# /// script
# requires-python = ">=3.11"
# dependencies = []
# ///

"""Verify the rational margins used in the perturbation note."""

from fractions import Fraction


def verify_geometry_and_low_margin() -> None:
    """Check the changed lengths and direct-bound saving."""
    length_change = Fraction(169, 1000000)
    boundary = Fraction(7, 8) - Fraction(21, 500000)
    slot_length = Fraction(1, 6) + length_change
    x_length = Fraction(17, 48) - length_change / 2
    y_length = Fraction(23, 48) - length_change / 2
    row_length = Fraction(13, 16) + 3 * length_change / 2
    averaging_length = x_length + y_length
    additive_scale = Fraction(1, 8)

    if boundary != Fraction(437479, 500000):
        raise AssertionError("The proposed boundary is inconsistent")
    if averaging_length + slot_length != 1:
        raise AssertionError("The physical scales do not balance")
    if row_length != 1 - x_length + slot_length:
        raise AssertionError("The row scale does not balance")
    if y_length - x_length != additive_scale:
        raise AssertionError("The additive scale changed")

    gram_gap = y_length - slot_length - 11 * additive_scale / 6
    if gram_gap != Fraction(1, 12) - 3 * length_change / 2:
        raise AssertionError("The Gram gap formula is inconsistent")
    if min(x_length - slot_length, y_length - slot_length,
           averaging_length - 2 * slot_length, gram_gap) <= 0:
        raise AssertionError("A low-side length condition fails")
    if Fraction(1, 6) - 5 * length_change <= 0:
        raise AssertionError("The reflected row bound needs review")

    low_exponent = x_length / 2 + additive_scale / 12
    signal_exponent = boundary - Fraction(11, 16)
    low_margin = signal_exponent - low_exponent
    if low_margin != Fraction(1, 4000000):
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
    length_change = Fraction(169, 1000000)
    boundary_change = Fraction(21, 500000)
    high_margin = Fraction(1, 500000)
    clearing_factor = Fraction(648000000)

    denominator_constant = [Fraction(185, 108), Fraction(170, 108)]
    denominator_linear = [Fraction(-138, 108), Fraction(12, 108), Fraction(96, 108)]
    prime_weight = [Fraction(7, 9), Fraction(18, 9), Fraction(8, 9)]
    endpoint_constant = Fraction(1, 48) - boundary_change - high_margin - length_change
    endpoint_linear = [Fraction(3, 48), Fraction(8, 48) + length_change]
    row_correction_coefficient = (Fraction(13, 16) + 3 * length_change / 2) / 2

    quadratic_coefficients = scale_polynomial(
        add_polynomials(
            multiply_polynomials(denominator_linear, endpoint_linear),
            scale_polynomial(prime_weight, row_correction_coefficient),
        ),
        clearing_factor,
    )
    linear_coefficients = scale_polynomial(
        add_polynomials(
            add_polynomials(
                scale_polynomial(denominator_linear, endpoint_constant),
                multiply_polynomials(denominator_constant, endpoint_linear),
            ),
            scale_polynomial(prime_weight, -Fraction(5, 6) * row_correction_coefficient),
        ),
        clearing_factor,
    )
    constant_coefficients = scale_polynomial(
        denominator_constant, clearing_factor * endpoint_constant,
    )

    if quadratic_coefficients != [153063882, 393024336, 282085176, 96097344]:
        raise AssertionError("The quadratic endpoint coefficients are inconsistent")
    if linear_coefficients != [-118376871, -188464636, -13011148]:
        raise AssertionError("The linear endpoint coefficients are inconsistent")
    if constant_coefficients != [22888570, 21032740]:
        raise AssertionError("The constant endpoint coefficients are inconsistent")

    discriminant_complement = add_polynomials(
        scale_polynomial(multiply_polynomials(quadratic_coefficients, constant_coefficients), Fraction(4)),
        scale_polynomial(multiply_polynomials(linear_coefficients, linear_coefficients), Fraction(-1)),
    )
    if discriminant_complement != [
        569922764319, 4240763631276888, 20292262879067528,
        27625937254957024, 7915471831892336,
    ]:
        raise AssertionError("The endpoint square identity is inconsistent")
    if min(quadratic_coefficients + discriminant_complement) <= 0:
        raise AssertionError("The endpoint square identity does not certify positivity")
    denominator_lower_bound = Fraction(185, 108) - Fraction(138, 108) * Fraction(5, 6)
    if denominator_lower_bound != Fraction(35, 54) or denominator_lower_bound <= 0:
        raise AssertionError("The endpoint denominator is not positive in the bin range")

    floor_cost = length_change * Fraction(121, 40)
    small_row_cost = length_change * Fraction(51, 100)
    if floor_cost >= min(Fraction(7, 1200), Fraction(49, 14400)):
        raise AssertionError("A secondary high-side margin fails")
    if small_row_cost >= Fraction(63, 800):
        raise AssertionError("The small-row margin fails")
    print(f"High endpoint margin: {high_margin}")


def verify_analytic_margins() -> None:
    """Check the widened Euler region and prime supply inequalities."""
    length_change = Fraction(169, 1000000)
    boundary_change = Fraction(21, 500000)
    slot_length = Fraction(1, 6) + length_change
    row_length = Fraction(13, 16) + 3 * length_change / 2
    boundary = Fraction(7, 8) - boundary_change
    euler_deterioration = 6 * boundary_change

    if euler_deterioration != Fraction(63, 250000):
        raise AssertionError("The Euler deterioration is inconsistent")
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
