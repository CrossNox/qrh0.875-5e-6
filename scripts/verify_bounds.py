# /// script
# requires-python = ">=3.11"
# dependencies = []
# ///

"""Verify the rational margins used in the perturbation note."""

from fractions import Fraction


def verify_geometry_and_low_margin() -> None:
    """Check the changed lengths and direct-bound saving."""
    length_change = Fraction(3, 100000)
    boundary = Fraction(7, 8) - Fraction(1, 200000)
    slot_length = Fraction(1, 6) + length_change
    x_length = Fraction(17, 48) - length_change / 2
    y_length = Fraction(23, 48) - length_change / 2
    row_length = Fraction(13, 16) + 3 * length_change / 2
    averaging_length = x_length + y_length
    additive_scale = Fraction(1, 8)

    if boundary != Fraction(174999, 200000):
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
    if low_margin != Fraction(1, 400000):
        raise AssertionError("The low margin is inconsistent")
    print(f"Low margin: {low_margin}")


def verify_high_endpoint_margin() -> None:
    """Check that the endpoint certificate covers the perturbation."""
    length_change = Fraction(3, 100000)
    boundary_change = Fraction(1, 200000)
    maximum_bin_parameter = Fraction(3, 4)
    maximum_amplitude = maximum_bin_parameter / 2
    maximum_row_exponent = Fraction(17, 12)

    maximum_derivative = (
        -Fraction(1, 2)
        + maximum_bin_parameter
        + maximum_amplitude
        + 3 * maximum_row_exponent / 2
    )
    if maximum_derivative != Fraction(11, 4):
        raise AssertionError("The high-exponent derivative is inconsistent")

    perturbation_cost = boundary_change + length_change * maximum_derivative
    source_certificate = Fraction(49, 440640)
    high_margin = source_certificate - perturbation_cost
    if perturbation_cost != Fraction(7, 80000):
        raise AssertionError("The endpoint perturbation is inconsistent")
    if high_margin <= 0:
        raise AssertionError("The high endpoint has no saving")
    if perturbation_cost >= min(Fraction(7, 1200), Fraction(49, 14400)):
        raise AssertionError("A secondary high-side margin fails")
    print(f"High endpoint margin: {high_margin}")


def verify_analytic_margins() -> None:
    """Check the widened Euler region and prime supply inequalities."""
    length_change = Fraction(3, 100000)
    boundary_change = Fraction(1, 200000)
    slot_length = Fraction(1, 6) + length_change
    row_length = Fraction(13, 16) + 3 * length_change / 2
    boundary = Fraction(7, 8) - boundary_change

    if -Fraction(363, 200) + 6 * boundary_change >= -1:
        raise AssertionError("The unramified Euler product may diverge")
    if -Fraction(33, 40) + 6 * boundary_change >= 0:
        raise AssertionError("The ramified Euler factors may grow")
    if -Fraction(363, 200) + 6 * boundary_change >= -Fraction(9, 5):
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
