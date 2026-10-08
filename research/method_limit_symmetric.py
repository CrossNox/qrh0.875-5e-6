# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///

"""Compute the exact arithmetic limit for symmetric probe geometry."""

import json
import logging
from decimal import Decimal, localcontext
from fractions import Fraction


def multiply_polynomials(left, right):
    coefficients = [Fraction(0)] * (len(left) + len(right) - 1)

    for left_degree, left_coefficient in enumerate(left):
        for right_degree, right_coefficient in enumerate(right):
            coefficients[left_degree + right_degree] += (
                left_coefficient * right_coefficient
            )

    return coefficients


def evaluate_polynomial(coefficients, parameter):
    value = Fraction(0)

    for coefficient in reversed(coefficients):
        value = value * parameter + coefficient

    return value


def calculate_discriminant_coefficients():
    quadratic_coefficients = [
        [1224, 12096], [3144, 4608], [2256, 16128], [768, 18432]
    ]
    linear_coefficients = [[-948, 23040], [-1508, 6720], [-104, -1920]]
    constant_coefficients = [[185, -44400], [170, -40800]]
    discriminant_coefficients = [[Fraction(0)] * 3 for _ in range(5)]

    for quadratic_degree, quadratic_coefficient in enumerate(quadratic_coefficients):
        for constant_degree, constant_coefficient in enumerate(constant_coefficients):
            product = multiply_polynomials(quadratic_coefficient, constant_coefficient)

            for parameter_degree, coefficient in enumerate(product):
                discriminant_coefficients[quadratic_degree + constant_degree][parameter_degree] += 4 * coefficient

    for first_degree, first_coefficient in enumerate(linear_coefficients):
        for second_degree, second_coefficient in enumerate(linear_coefficients):
            product = multiply_polynomials(first_coefficient, second_coefficient)

            for parameter_degree, coefficient in enumerate(product):
                discriminant_coefficients[first_degree + second_degree][parameter_degree] -= coefficient

    return discriminant_coefficients


def calculate_limit_checkpoint():
    logging.info("Deriving the exact discriminant certificate")
    discriminant_coefficients = calculate_discriminant_coefficients()
    parameter_cap = Fraction(1, 20000)
    positive_coefficient_bounds = []

    for coefficients in discriminant_coefficients[1:]:
        lower_bound = coefficients[0]

        for degree, coefficient in enumerate(coefficients[1:], start=1):
            if coefficient < 0:
                lower_bound += coefficient * parameter_cap**degree

        if lower_bound <= 0:
            raise ArithmeticError("The positive-y discriminant certificate failed")

        positive_coefficient_bounds.append(lower_bound)

    with localcontext() as decimal_context:
        decimal_context.prec = 70
        linear_coefficient = Decimal(1144080)
        quadratic_coefficient = Decimal(18604800)
        square_root = (linear_coefficient**2 + 196 * quadratic_coefficient).sqrt()
        epsilon_limit = Decimal(98) / (linear_coefficient + square_root)
        checkpoint_denominator = 10**18
        enclosure_numerator = int(epsilon_limit * checkpoint_denominator)
        lower_epsilon = Fraction(enclosure_numerator, checkpoint_denominator)
        upper_epsilon = Fraction(enclosure_numerator + 1, checkpoint_denominator)
        worst_delta = (Decimal(948) - 23040 * epsilon_limit) / (
            Decimal(2448) + 24192 * epsilon_limit
        )
        boundary_limit = Decimal(7) / 8 - epsilon_limit

    root_polynomial = [49, -1144080, -18604800]
    lower_root_value = evaluate_polynomial(root_polynomial, lower_epsilon)
    upper_root_value = evaluate_polynomial(root_polynomial, upper_epsilon)

    if lower_root_value <= 0 or upper_root_value >= 0:
        raise ArithmeticError("The exact rational root enclosure failed")

    logging.info("Verified the rational enclosure and all positive-y coefficients")

    return {
        "epsilon_limit_decimal": str(epsilon_limit),
        "boundary_limit_decimal": str(boundary_limit),
        "worst_delta_decimal": str(worst_delta),
        "epsilon_lower": str(lower_epsilon),
        "epsilon_upper": str(upper_epsilon),
        "root_at_lower": str(lower_root_value),
        "root_at_upper": str(upper_root_value),
        "discriminant_coefficients_by_y_degree": [
            [str(coefficient) for coefficient in coefficients]
            for coefficients in discriminant_coefficients
        ],
        "positive_y_coefficient_lower_bounds": [
            str(lower_bound) for lower_bound in positive_coefficient_bounds
        ],
    }


if __name__ == "__main__":
    logging.basicConfig(level=logging.INFO, format="%(message)s")
    print(json.dumps(calculate_limit_checkpoint(), indent=2))
