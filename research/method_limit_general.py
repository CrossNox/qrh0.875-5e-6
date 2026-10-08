# /// script
# requires-python = ">=3.12"
# dependencies = ["sympy>=1.14"]
# ///

"""Optimize and certify the fixed-mass asymmetric balanced-row exponent family."""

import logging
from math import comb, isqrt

import sympy as sp


def enclose_algebraic_coefficient(value: sp.Expr) -> tuple[sp.Rational, sp.Rational]:
    """Bound a coefficient in the quadratic field using rational arithmetic."""
    root = sp.sqrt(921)
    coefficient = sp.collect(sp.radsimp(value), root)
    rational_part = coefficient.coeff(root, 0)
    root_part = coefficient.coeff(root, 1)
    if sp.simplify(coefficient - rational_part - root_part * root) != 0:
        raise ValueError(f"Coefficient is outside the expected field: {coefficient}")

    denominator = 10**18
    numerator = isqrt(921 * denominator**2)
    root_lower = sp.Rational(numerator, denominator)
    root_upper = sp.Rational(numerator + 1, denominator)
    if root_part >= 0:
        return rational_part + root_part * root_lower, rational_part + root_part * root_upper
    return rational_part + root_part * root_upper, rational_part + root_part * root_lower


def require_positive_coefficient(value: sp.Expr, description: str) -> None:
    """Reject a coefficient unless an exact rational lower bound is positive."""
    lower, _ = enclose_algebraic_coefficient(value)
    if lower <= 0:
        raise AssertionError(f"Nonpositive coefficient for {description}: {value}")


def find_bernstein_coefficients(
    polynomial: sp.Expr, first_variable: sp.Symbol, second_variable: sp.Symbol
) -> list[list[sp.Expr]]:
    """Express a polynomial in the Bernstein basis on the unit square."""
    expanded_polynomial = sp.Poly(sp.expand(polynomial), first_variable, second_variable)
    first_degree = expanded_polynomial.degree(first_variable)
    second_degree = expanded_polynomial.degree(second_variable)
    coefficients = []

    for first_index in range(first_degree + 1):
        coefficient_row = []
        for second_index in range(second_degree + 1):
            coefficient = sum(
                expanded_polynomial.coeff_monomial(first_variable**first_power * second_variable**second_power)
                * sp.Rational(comb(first_index, first_power), comb(first_degree, first_power))
                * sp.Rational(comb(second_index, second_power), comb(second_degree, second_power))
                for first_power in range(first_index + 1)
                for second_power in range(second_index + 1)
            )
            coefficient_row.append(sp.radsimp(coefficient))
        coefficients.append(coefficient_row)

    reconstructed_polynomial = sum(
        coefficients[first_index][second_index]
        * comb(first_degree, first_index)
        * first_variable**first_index
        * (1 - first_variable) ** (first_degree - first_index)
        * comb(second_degree, second_index)
        * second_variable**second_index
        * (1 - second_variable) ** (second_degree - second_index)
        for first_index in range(first_degree + 1)
        for second_index in range(second_degree + 1)
    )
    if sp.simplify(polynomial - reconstructed_polynomial) != 0:
        raise AssertionError("Bernstein reconstruction failed")
    return coefficients


def optimize_and_certify_geometry() -> None:
    """Solve the active equations and certify every bin and geometry constraint."""
    delta, amplitude_complement = sp.symbols("delta y", real=True)
    horizontal_shift, vertical_shift, boundary_reduction = sp.symbols("u v epsilon", real=True)
    prime_weight = (7 + 18 * amplitude_complement + 8 * amplitude_complement**2) / 9
    balance_denominator = (
        (sp.Rational(5, 6) - delta) * (37 + 34 * amplitude_complement) / 18
        + delta * prime_weight
    )
    balanced_row_exponent = (
        1 - delta
        + (sp.Rational(5, 6) - delta) * delta * prime_weight / (2 * balance_denominator)
    )
    prime_amplitude = delta * (sp.Rational(1, 2) - amplitude_complement)
    source_endpoint = (
        -sp.Rational(1, 48) + sp.Rational(2, 3) * delta + prime_amplitude / 6
        - sp.Rational(13, 16) * (1 - balanced_row_exponent)
    )
    perturbed_endpoint = (
        source_endpoint + boundary_reduction
        + horizontal_shift * (2 * balanced_row_exponent + delta + prime_amplitude - sp.Rational(5, 6))
        + vertical_shift * (balanced_row_exponent + delta + prime_amplitude - sp.Rational(1, 6))
    )
    frequency_length, physical_row_length = sp.symbols("frequency_length physical_row_length", real=True)
    x_length_symbolic = sp.Rational(17, 48) - horizontal_shift
    y_length_symbolic = sp.Rational(23, 48) - vertical_shift
    slot_length_symbolic = sp.Rational(1, 6) + horizontal_shift + vertical_shift
    row_length_symbolic = sp.Rational(13, 16) + 2 * horizontal_shift + vertical_shift
    zero_location = (1 + delta) / 2
    prime_contour = sp.Rational(17, 50)
    boundary_signal = (sp.Rational(3, 16) - boundary_reduction
                       + (vertical_shift - horizontal_shift) / 6)
    relative_source_exponent = (
        x_length_symbolic * (sp.Rational(1, 2) - prime_contour)
        + zero_location + prime_contour - 1 - zero_location * y_length_symbolic
        - frequency_length * prime_contour + physical_row_length * balanced_row_exponent
        + frequency_length * (zero_location - sp.Rational(1, 2))
        + slot_length_symbolic * (prime_contour - sp.Rational(1, 2) + prime_amplitude)
        - boundary_signal
    )
    if sp.simplify(relative_source_exponent.subs({
        frequency_length: row_length_symbolic, physical_row_length: row_length_symbolic
    }) - perturbed_endpoint) != 0:
        raise AssertionError("The physical source does not match the endpoint perturbation")

    critical_delta = (49 - sp.sqrt(921)) / 48
    optimum_reduction = (16 * sp.sqrt(921) - 485) / 13224
    optimum_total_shift = 4 * optimum_reduction
    critical_row_exponent = balanced_row_exponent.subs({delta: critical_delta, amplitude_complement: 0})
    if sp.simplify(critical_row_exponent - sp.Rational(2, 3)) != 0:
        raise AssertionError("The universal obstruction has the wrong row exponent")
    reduction_from_obstruction = (
        sp.Rational(7, 24) - 3 * critical_delta / 4
    ) / (3 + 6 * critical_delta)
    if sp.simplify(reduction_from_obstruction - optimum_reduction) != 0:
        raise AssertionError("The active-bin obstruction has the wrong boundary reduction")

    logging.info("Solving stationarity after the universal active-bin obstruction")
    endpoint_with_total_shift = perturbed_endpoint.subs(
        {boundary_reduction: optimum_reduction, vertical_shift: optimum_total_shift - horizontal_shift}
    )
    derivative_at_critical_bin = sp.diff(endpoint_with_total_shift, delta).subs(
        {delta: critical_delta, amplitude_complement: 0}
    )
    optimum_horizontal_shift = sp.radsimp(sp.solve(derivative_at_critical_bin, horizontal_shift)[0])
    optimum_vertical_shift = sp.radsimp(optimum_total_shift - optimum_horizontal_shift)
    optimum_endpoint = sp.simplify(endpoint_with_total_shift.subs(horizontal_shift, optimum_horizontal_shift))

    certificate_polynomial = sp.Poly(
        sp.expand(sp.cancel(-2 * balance_denominator * optimum_endpoint)), delta, amplitude_complement
    ).as_expr()
    boundary_polynomial = sp.expand(certificate_polynomial.subs(amplitude_complement, 0))
    square_coefficient = sp.radsimp(sp.Poly(boundary_polynomial, delta).coeff_monomial(delta**2))
    if sp.simplify(boundary_polynomial - square_coefficient * (delta - critical_delta) ** 2) != 0:
        raise AssertionError("The boundary polynomial is not the expected square")
    require_positive_coefficient(square_coefficient, "boundary square")

    endpoint_quadratic = sp.Poly(certificate_polynomial, delta)
    quadratic_coefficient = endpoint_quadratic.coeff_monomial(delta**2)
    linear_coefficient = endpoint_quadratic.coeff_monomial(delta)
    constant_coefficient = endpoint_quadratic.coeff_monomial(1)
    discriminant_certificate = sp.expand(
        (4 * quadratic_coefficient * constant_coefficient - linear_coefficient**2)
        / amplitude_complement
    )
    if sp.simplify(discriminant_certificate * amplitude_complement
                   - 4 * quadratic_coefficient * constant_coefficient
                   + linear_coefficient**2) != 0:
        raise AssertionError("Discriminant reconstruction failed")
    for power, coefficient in enumerate(sp.Poly(quadratic_coefficient, amplitude_complement).all_coeffs()):
        require_positive_coefficient(coefficient, f"quadratic coefficient {power}")
    for power, coefficient in enumerate(sp.Poly(discriminant_certificate, amplitude_complement).all_coeffs()):
        require_positive_coefficient(coefficient, f"discriminant coefficient {power}")
    print(f"Quadratic coefficients = {endpoint_quadratic.all_coeffs()}")
    print(f"Discriminant divided by y = {sp.collect(discriminant_certificate, amplitude_complement)}")
    remainder_polynomial = discriminant_certificate
    first_unit_coordinate, second_unit_coordinate = sp.symbols("s z", real=True)
    unit_remainder = remainder_polynomial.subs(
        {delta: 3 * first_unit_coordinate / 4, amplitude_complement: second_unit_coordinate / 2}
    )
    bernstein_coefficients = find_bernstein_coefficients(
        unit_remainder, first_unit_coordinate, second_unit_coordinate
    )
    for first_index, coefficient_row in enumerate(bernstein_coefficients):
        for second_index, coefficient in enumerate(coefficient_row):
            require_positive_coefficient(coefficient, f"Bernstein {first_index},{second_index}")

    total_shift = optimum_total_shift
    x_length = sp.Rational(17, 48) - optimum_horizontal_shift
    y_length = sp.Rational(23, 48) - optimum_vertical_shift
    slot_length = sp.Rational(1, 6) + total_shift
    row_length = sp.Rational(13, 16) + 2 * optimum_horizontal_shift + optimum_vertical_shift
    additive_length = y_length - x_length
    margins = {
        "slot positivity": slot_length,
        "additive positivity": additive_length,
        "compensated Gram cap": 2 * x_length - y_length - slot_length,
        "remaining x": x_length - slot_length,
        "remaining y": y_length - slot_length,
        "remaining row": x_length + y_length - 2 * slot_length,
        "fractional Gram tail": y_length - slot_length - sp.Rational(11, 6) * additive_length,
        "reflected empty subset": sp.Rational(1, 6) - 5 * total_shift,
        "row conductor cap": sp.Rational(7, 8) - row_length,
        "inverse selected-prime supply": slot_length - sp.Rational(7, 37) * row_length,
        "current selected-prime supply": slot_length - sp.Rational(8, 39) * row_length,
        "buffered selected-prime supply": 5 * slot_length - row_length - sp.Rational(1, 48),
        "floor at a=.51": sp.Rational(7, 1200) - optimum_reduction
        - sp.Rational(359, 300) * optimum_horizontal_shift
        - sp.Rational(259, 300) * optimum_vertical_shift,
        "principal w": y_length / 20,
        "principal z": row_length / 600,
        "principal fixed w": y_length / 20 - optimum_reduction,
        "principal fixed z": row_length / 600 - optimum_reduction,
        "small row": sp.Rational(63, 800) - sp.Rational(26, 75) * optimum_horizontal_shift
        - sp.Rational(101, 150) * optimum_vertical_shift,
        "small first Euler": sp.Rational(7, 8) - optimum_reduction - sp.Rational(87, 100),
        "principal strong Euler tail": sp.Rational(1, 400) - optimum_reduction,
        "global Euler product": sp.Rational(31, 40) - optimum_reduction + sp.Rational(24, 25) - sp.Rational(5, 3),
    }
    intermediate_exponent = (
        -sp.Rational(529, 2400) + sp.Rational(25, 96) * delta + optimum_reduction
        + optimum_horizontal_shift * (delta / 2 - sp.Rational(23, 150))
        + optimum_vertical_shift * (sp.Rational(1, 2) + delta - sp.Rational(49, 150))
    )
    margins["intermediate delta=0"] = -intermediate_exponent.subs(delta, 0)
    margins["intermediate delta=.75"] = -intermediate_exponent.subs(delta, sp.Rational(3, 4))
    for description, margin in margins.items():
        require_positive_coefficient(sp.radsimp(margin), description)

    print(f"critical delta = {critical_delta} = {sp.N(critical_delta, 18)}")
    print(f"optimum reduction = {optimum_reduction} = {sp.N(optimum_reduction, 18)}")
    print(f"boundary infimum = {sp.N(sp.Rational(7, 8) - optimum_reduction, 18)}")
    print(f"horizontal shift = {optimum_horizontal_shift} = {sp.N(optimum_horizontal_shift, 18)}")
    print(f"vertical shift = {optimum_vertical_shift} = {sp.N(optimum_vertical_shift, 18)}")
    print(f"square coefficient = {square_coefficient}")
    for first_index, coefficient_row in enumerate(bernstein_coefficients):
        for second_index, coefficient in enumerate(coefficient_row):
            print(f"Bernstein coefficient {first_index},{second_index} = {coefficient}")
    for description, margin in margins.items():
        print(f"{description}: {sp.N(margin, 18)}")
    logging.info("Certified the exact optimum of the fixed-mass numerical family with kappa=3/4")


if __name__ == "__main__":
    logging.basicConfig(level=logging.INFO, format="%(message)s")
    optimize_and_certify_geometry()
