# /// script
# requires-python = ">=3.12"
# dependencies = ["sympy>=1.14"]
# ///

"""Check exact local means for the mixed additive and completed rows."""

import argparse
import json
import logging
from collections import Counter
from pathlib import Path

from sympy import Poly, cyclotomic_poly, symbols


def find_primitive_root_for_prime(prime: int) -> int:
    for candidate in range(2, prime):
        residues = {pow(candidate, exponent, prime) for exponent in range(prime - 1)}
        if len(residues) == prime - 1:
            return candidate
    raise ValueError(f"No primitive root found for {prime}")


def find_sextic_exponents_for_prime(prime: int) -> dict[int, int]:
    primitive_root = find_primitive_root_for_prime(prime)
    return {pow(primitive_root, exponent, prime): exponent % 6 for exponent in range(prime - 1)}


def reduce_root_coefficients(coefficients: Counter[int], root_order: int) -> list[int]:
    variable = symbols("x")
    polynomial = Poly.from_dict(
        {(exponent % root_order,): coefficient for exponent, coefficient in coefficients.items()},
        variable,
        domain="ZZ",
    )
    remainder = polynomial.rem(Poly(cyclotomic_poly(root_order, variable), variable, domain="ZZ"))
    return [int(coefficient) for coefficient in remainder.all_coeffs()]


def sum_mixed_local_coefficients(
    prime: int, source_power: int, row_power: int, frequency: int = 0
) -> Counter[int]:
    modulus = prime**source_power
    root_order = 6 * modulus
    sextic_exponents = find_sextic_exponents_for_prime(prime)
    coefficients: Counter[int] = Counter()
    for row_residue in range(modulus):
        if row_power > 0 and row_residue % prime == 0:
            continue
        row_exponent = 0 if row_power == 0 else row_power * sextic_exponents[row_residue % prime]
        for gauss_residue in range(modulus):
            if gauss_residue % prime == 0:
                continue
            source_exponent = source_power * sextic_exponents[gauss_residue % prime]
            root_exponent = (
                modulus * (row_exponent + source_exponent)
                - 6 * row_residue * gauss_residue
                + 6 * frequency * row_residue
            )
            coefficients[root_exponent % root_order] += 1
    return coefficients


def sum_expected_principal_coefficients(prime: int) -> Counter[int]:
    sextic_exponents = find_sextic_exponents_for_prime(prime)
    coefficients: Counter[int] = Counter()
    for gauss_residue in range(1, prime):
        exponent = prime * (sextic_exponents[gauss_residue] - sextic_exponents[prime - 1]) + 6 * gauss_residue
        coefficients[exponent % (6 * prime)] += prime - 1
    return coefficients


def sum_expected_mixed_frequency_coefficients(prime: int, row_power: int, frequency: int) -> Counter[int]:
    sextic_exponents = find_sextic_exponents_for_prime(prime)
    coefficients: Counter[int] = Counter()
    if row_power == 0:
        if frequency != 0:
            coefficients[prime * sextic_exponents[frequency]] = prime
        return coefficients

    for gauss_residue in range(1, prime):
        for quotient_residue in range(1, prime):
            exponent = (
                prime
                * (
                    sextic_exponents[gauss_residue]
                    - sextic_exponents[prime - 1]
                    + (row_power - 1) * sextic_exponents[quotient_residue]
                )
                + 6 * gauss_residue
                + 6 * frequency * quotient_residue
            )
            coefficients[exponent % (6 * prime)] += 1
    return coefficients


def verify_exact_mixed_means() -> dict[str, object]:
    checkpoints: list[dict[str, int]] = []
    for prime in (7, 13, 19):
        logging.info("Checking mixed prime mean at p=%s", prime)
        expected_principal = reduce_root_coefficients(sum_expected_principal_coefficients(prime), 6 * prime)
        for row_power in range(13):
            observed = reduce_root_coefficients(sum_mixed_local_coefficients(prime, 1, row_power), 6 * prime)
            expected = expected_principal if row_power % 6 == 1 else [0]
            if observed != expected:
                raise AssertionError((prime, 1, row_power, observed, expected))
            checkpoints.append({"prime": prime, "source_power": 1, "row_power": row_power})

        for row_power in range(13):
            for frequency in range(1, prime):
                observed = reduce_root_coefficients(
                    sum_mixed_local_coefficients(prime, 1, row_power, frequency), 6 * prime
                )
                expected = reduce_root_coefficients(
                    sum_expected_mixed_frequency_coefficients(prime, row_power, frequency), 6 * prime
                )
                if observed != expected:
                    raise AssertionError((prime, row_power, frequency, observed, expected))
                checkpoints.append(
                    {"prime": prime, "source_power": 1, "row_power": row_power, "frequency": frequency}
                )

    for source_power in (2, 3):
        logging.info("Checking higher source power at p=7, exponent=%s", source_power)
        for row_power in (0, 1, 3, 6, 7):
            observed = reduce_root_coefficients(
                sum_mixed_local_coefficients(7, source_power, row_power), 6 * 7**source_power
            )
            if observed != [0]:
                raise AssertionError((7, source_power, row_power, observed))
            checkpoints.append({"prime": 7, "source_power": source_power, "row_power": row_power})

    for source_exponent in range(2):
        for column_exponent in range(2):
            for cubic_exponent in range(100):
                resonance = (column_exponent + 3 * cubic_exponent) % 6 == source_exponent
                classification = column_exponent == source_exponent and cubic_exponent % 2 == 0
                if resonance != classification:
                    raise AssertionError((source_exponent, column_exponent, cubic_exponent))

    return {
        "status": "passed",
        "local_checks": checkpoints,
        "squarefree_valuation_checks": 400,
        "scope": "Exact finite prime and prime power models. This does not prove the incomplete mixed row bound.",
    }


def check_mixed_arithmetic() -> None:
    arguments = argparse.ArgumentParser(description=__doc__)
    arguments.add_argument("--checkpoint", type=Path)
    options = arguments.parse_args()
    results = verify_exact_mixed_means()
    if options.checkpoint is not None:
        options.checkpoint.write_text(json.dumps(results, indent=2) + "\n")
        logging.info("Saved checkpoint to %s", options.checkpoint)
    logging.info("Passed %s exact local checks and 400 valuation checks", len(results["local_checks"]))


if __name__ == "__main__":
    logging.basicConfig(level=logging.INFO, format="%(message)s")
    check_mixed_arithmetic()
