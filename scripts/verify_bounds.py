# /// script
# requires-python = ">=3.11"
# dependencies = []
# ///

"""Verify the rational margins used in the perturbation note."""

from fractions import Fraction
from math import gcd, lcm

LENGTH_CHANGE = Fraction(42930200831, 250000000000000)
SKEW = Fraction(12457523527, 15625000000000)
BOUNDARY_CHANGE = Fraction(214651, 5000000000)
HIGH_MARGIN = Fraction(1, 1250000000000)


def verify_geometry_and_low_margin() -> None:
    """Check the changed lengths and direct-bound saving."""
    length_change = LENGTH_CHANGE
    boundary = Fraction(7, 8) - BOUNDARY_CHANGE
    slot_length = Fraction(1, 6) + length_change
    x_length = Fraction(17, 48) + SKEW - length_change / 2
    y_length = Fraction(23, 48) - SKEW - length_change / 2
    row_length = Fraction(13, 16) - SKEW + 3 * length_change / 2
    averaging_length = x_length + y_length
    additive_scale = Fraction(1, 8) - 2 * SKEW

    if boundary != Fraction(4374785349, 5000000000):
        raise AssertionError("The proposed boundary is inconsistent")
    if averaging_length + slot_length != 1:
        raise AssertionError("The physical scales do not balance")
    if row_length != 1 - x_length + slot_length:
        raise AssertionError("The row scale does not balance")
    if y_length - x_length != additive_scale:
        raise AssertionError("The additive scale changed")

    gram_gap = y_length - slot_length - 11 * additive_scale / 6
    if gram_gap != Fraction(1, 12) + 8 * SKEW / 3 - 3 * length_change / 2:
        raise AssertionError("The Gram gap formula is inconsistent")
    if min(x_length - slot_length, y_length - slot_length,
           averaging_length - 2 * slot_length, gram_gap) <= 0:
        raise AssertionError("A low-side length condition fails")
    if Fraction(1, 6) - 5 * length_change <= 0:
        raise AssertionError("The reflected row bound needs review")

    low_exponent = x_length / 2 + additive_scale / 12
    signal_exponent = boundary - Fraction(11, 16) + SKEW / 3
    low_margin = signal_exponent - low_exponent
    if low_margin != Fraction(831, 1000000000000000):
        raise AssertionError("The low margin is inconsistent")
    print(f"Low margin: {low_margin}")


def add_polynomials(left: list[Fraction], right: list[Fraction]) -> list[Fraction]:
    return [
        (left[index] if index < len(left) else Fraction(0))
        + (right[index] if index < len(right) else Fraction(0))
        for index in range(max(len(left), len(right)))
    ]


def multiply_polynomials(left: list[Fraction], right: list[Fraction]) -> list[Fraction]:
    coefficients = [Fraction(0)] * (len(left) + len(right) - 1)
    for left_degree, left_coefficient in enumerate(left):
        for right_degree, right_coefficient in enumerate(right):
            coefficients[left_degree + right_degree] += left_coefficient * right_coefficient
    return coefficients


def scale_polynomial(coefficients: list[Fraction], scale: Fraction) -> list[Fraction]:
    return [scale * coefficient for coefficient in coefficients]


def verify_high_endpoint_margin() -> None:
    """Check the exact endpoint polynomial and its positive discriminant complement."""
    length_change = LENGTH_CHANGE
    boundary_change = BOUNDARY_CHANGE
    high_margin = HIGH_MARGIN

    denominator_constant = [Fraction(185, 108), Fraction(170, 108)]
    denominator_linear = [Fraction(-138, 108), Fraction(12, 108), Fraction(96, 108)]
    prime_weight = [Fraction(7, 9), Fraction(18, 9), Fraction(8, 9)]
    endpoint_constant = Fraction(1, 48) - boundary_change - high_margin - length_change + SKEW / 3
    endpoint_linear = [Fraction(3, 48) - SKEW, Fraction(8, 48) + length_change]
    row_correction_coefficient = (Fraction(13, 16) + 3 * length_change / 2 - SKEW) / 2

    quadratic_coefficients = (
        add_polynomials(
            multiply_polynomials(denominator_linear, endpoint_linear),
            scale_polynomial(prime_weight, row_correction_coefficient),
        )
    )
    linear_coefficients = (
        add_polynomials(
            add_polynomials(
                scale_polynomial(denominator_linear, endpoint_constant),
                multiply_polynomials(denominator_constant, endpoint_linear),
            ),
            scale_polynomial(prime_weight, -Fraction(5, 6) * row_correction_coefficient),
        )
    )
    constant_coefficients = scale_polynomial(
        denominator_constant, endpoint_constant,
    )
    clearing_factor = lcm(*(coefficient.denominator for coefficient in
        quadratic_coefficients + linear_coefficients + constant_coefficients))
    integer_coefficients = [int(coefficient * clearing_factor) for coefficient in
        quadratic_coefficients + linear_coefficients + constant_coefficients]
    common_divisor = gcd(*integer_coefficients)
    clearing_factor = Fraction(clearing_factor, common_divisor)
    quadratic_coefficients = scale_polynomial(quadratic_coefficients, clearing_factor)
    linear_coefficients = scale_polynomial(linear_coefficients, clearing_factor)
    constant_coefficients = scale_polynomial(constant_coefficients, clearing_factor)

    discriminant_complement = add_polynomials(
        scale_polynomial(multiply_polynomials(quadratic_coefficients, constant_coefficients), Fraction(4)),
        scale_polynomial(multiply_polynomials(linear_coefficients, linear_coefficients), Fraction(-1)),
    )
    if min(quadratic_coefficients + discriminant_complement) <= 0:
        raise AssertionError("The endpoint square identity does not certify positivity")
    print(f"Endpoint clearing factor: {clearing_factor}")
    print(f"Quadratic coefficients: {[str(value) for value in quadratic_coefficients]}")
    print(f"Linear coefficients: {[str(value) for value in linear_coefficients]}")
    print(f"Constant coefficients: {[str(value) for value in constant_coefficients]}")
    print(f"Discriminant complement: {[str(value) for value in discriminant_complement]}")
    denominator_lower_bound = Fraction(185, 108) - Fraction(138, 108) * Fraction(5, 6)
    if denominator_lower_bound != Fraction(35, 54) or denominator_lower_bound <= 0:
        raise AssertionError("The endpoint denominator is not positive in the bin range")

    floor_cost = boundary_change + length_change * Fraction(121, 40) + SKEW * Fraction(67, 100)
    small_row_cost = length_change * Fraction(51, 100) + SKEW * Fraction(49, 150)
    if floor_cost >= min(Fraction(7, 1200), Fraction(49, 14400)):
        raise AssertionError("A secondary high-side margin fails")
    if small_row_cost >= Fraction(63, 800):
        raise AssertionError("The small-row margin fails")
    print(f"High endpoint margin: {high_margin}")


def verify_analytic_margins() -> None:
    """Check the widened Euler region and prime supply inequalities."""
    length_change = LENGTH_CHANGE
    boundary_change = BOUNDARY_CHANGE
    slot_length = Fraction(1, 6) + length_change
    row_length = Fraction(13, 16) - SKEW + 3 * length_change / 2
    boundary = Fraction(7, 8) - boundary_change
    euler_deterioration = 6 * boundary_change

    if -Fraction(363, 200) + euler_deterioration >= -1:
        raise AssertionError("The unramified Euler product may diverge")
    if -Fraction(33, 40) + euler_deterioration >= 0:
        raise AssertionError("The ramified Euler factors may grow")
    if -Fraction(363, 200) + euler_deterioration >= -Fraction(9, 5):
        raise AssertionError("The principal Euler tail lost its cutoff margin")
    if boundary - Fraction(1, 2) <= Fraction(37, 100):
        raise AssertionError("The small-row first Euler region is unavailable")
    if slot_length / row_length <= Fraction(8, 39):
        raise AssertionError("The prime supply did not increase")
    if 5 * slot_length - row_length <= Fraction(1, 48):
        raise AssertionError("The buffered supply did not increase")

    print("Euler and prime-supply margins: positive")


def main() -> None:
    """Run the exact arithmetic checks and report their margins."""
    verify_geometry_and_low_margin()
    verify_high_endpoint_margin()
    verify_analytic_margins()


if __name__ == "__main__":
    main()
