# /// script
# requires-python = ">=3.11"
# dependencies = []
# ///

"""Check the good-prime Gram means with exact sixth roots of unity."""

from argparse import ArgumentParser
from fractions import Fraction
import importlib.util
import json
import logging
from pathlib import Path


Eisenstein = tuple[int, int]


def add_eisenstein(left: Eisenstein, right: Eisenstein) -> Eisenstein:
    return left[0] + right[0], left[1] + right[1]


def multiply_eisenstein(left: Eisenstein, right: Eisenstein) -> Eisenstein:
    return (
        left[0] * right[0] - left[1] * right[1],
        left[0] * right[1] + left[1] * right[0] - left[1] * right[1],
    )


def conjugate_eisenstein(value: Eisenstein) -> Eisenstein:
    return value[0] - value[1], -value[1]


def find_primitive_root(prime: int) -> int:
    for candidate in range(2, prime):
        if len({pow(candidate, exponent, prime) for exponent in range(prime - 1)}) == prime - 1:
            return candidate
    raise ValueError(f"No primitive root found modulo {prime}")


def construct_sextic_character(prime: int) -> list[Eisenstein]:
    generator = find_primitive_root(prime)
    character = [(0, 0)] * prime
    root: Eisenstein = (1, 1)
    root_power: Eisenstein = (1, 0)
    for exponent in range(prime - 1):
        character[pow(generator, exponent, prime)] = root_power
        root_power = multiply_eisenstein(root_power, root)
    return character


def raise_character_value(value: Eisenstein, exponent: int) -> Eisenstein:
    if value == (0, 0):
        return (0, 0)
    result: Eisenstein = (1, 0)
    for _ in range(exponent % 6):
        result = multiply_eisenstein(result, value)
    return result


def compute_local_correlation_table(
    prime: int, common_exponent: int, frequency_residue: int, character: list[Eisenstein]
) -> list[list[Eisenstein]]:
    correlation = [[(0, 0) for _ in range(prime)] for _ in range(prime)]
    powered_character = [raise_character_value(value, common_exponent) for value in character]
    for first_column in range(prime):
        for second_column in range(prime):
            if first_column == 0 and second_column == 0:
                continue
            local_sum: Eisenstein = (0, 0)
            for first_gauss_residue in range(prime):
                for second_gauss_residue in range(prime):
                    if (second_column * first_gauss_residue - first_column * second_gauss_residue) % prime == frequency_residue:
                        summand = multiply_eisenstein(
                            powered_character[first_gauss_residue],
                            conjugate_eisenstein(powered_character[second_gauss_residue]),
                        )
                        local_sum = add_eisenstein(local_sum, summand)
            factor = prime ** (common_exponent - 1)
            correlation[first_column][second_column] = factor * local_sum[0], factor * local_sum[1]
    return correlation


def predict_local_mean(prime: int, common_exponent: int, frequency_exponent: int, dilation: int) -> Fraction:
    if dilation % prime == 0 and common_exponent + frequency_exponent > 0:
        return Fraction(0)
    if (common_exponent + frequency_exponent) % 6 != 0:
        return Fraction(0)
    unit_density = Fraction(prime - 1, prime)
    if common_exponent == 0:
        return Fraction(1) if frequency_exponent == 0 else unit_density**2
    if frequency_exponent == 0:
        return prime**common_exponent * unit_density**2
    return prime**common_exponent * unit_density**3


def check_local_means(prime: int) -> dict[str, object]:
    character = construct_sextic_character(prime)
    checked_cases = 0
    nonzero_cases = []
    for common_exponent in range(7):
        correlation_tables = {}
        if common_exponent > 0:
            for frequency_residue in (0, 1):
                correlation_tables[frequency_residue] = compute_local_correlation_table(
                    prime, common_exponent, frequency_residue, character
                )
        for frequency_exponent in range(7):
            numerator_character = (
                [(1, 0)] * prime
                if frequency_exponent == 0
                else [raise_character_value(value, frequency_exponent) for value in character]
            )
            for dilation in (0, 1, 2):
                total: Eisenstein = (0, 0)
                for first_column in range(prime):
                    for second_column in range(prime):
                        first_residue = dilation * first_column % prime
                        second_residue = dilation * second_column % prime
                        local_extension = (
                            (1, 0)
                            if common_exponent == 0
                            else correlation_tables[int(frequency_exponent == 0)][first_residue][second_residue]
                        )
                        numerator = multiply_eisenstein(
                            numerator_character[first_residue],
                            conjugate_eisenstein(numerator_character[second_residue]),
                        )
                        total = add_eisenstein(total, multiply_eisenstein(local_extension, numerator))
                predicted_mean = predict_local_mean(prime, common_exponent, frequency_exponent, dilation)
                if total[1] != 0 or Fraction(total[0], prime**2) != predicted_mean:
                    raise AssertionError(
                        f"Mean mismatch q={prime}, c={common_exponent}, e={frequency_exponent}, "
                        f"d={dilation}: exact={total}/{prime**2}, predicted={predicted_mean}"
                    )
                checked_cases += 1
                if dilation == 1 and predicted_mean != 0:
                    nonzero_cases.append({"c": common_exponent, "e": frequency_exponent, "mean": str(predicted_mean)})
    for total_exponent in (6, 12, 18):
        weighted_mean = sum(
            Fraction(1, prime ** (2 * common_exponent))
            * predict_local_mean(prime, common_exponent, total_exponent - common_exponent, 1)
            for common_exponent in range(total_exponent + 1)
        )
        predicted_weight = (1 - Fraction(1, prime)) * (1 - Fraction(1, prime**2))
        if weighted_mean != predicted_weight:
            raise AssertionError(f"Common-divisor sum mismatch q={prime}, h={total_exponent}")
    return {"prime": prime, "checked_cases": checked_cases, "nonzero_cases": nonzero_cases}


def compile_gram_bulk_checkpoint() -> None:
    repository = Path(__file__).resolve().parents[1]
    verifier_path = repository / "scripts" / "verify_oai.py"
    specification = importlib.util.spec_from_file_location("verify_oai", verifier_path)
    if specification is None or specification.loader is None:
        raise ImportError(f"Cannot load the Lean verifier at {verifier_path}")
    verifier = importlib.util.module_from_spec(specification)
    specification.loader.exec_module(verifier)
    verifier.compile_local_oai_module(
        repository.parent / "rh-upstream", repository / "lean", "GramBulkClassification"
    )


def main() -> None:
    parser = ArgumentParser()
    parser.add_argument("--primes", type=int, nargs="+", default=[7, 13, 19])
    parser.add_argument("--check-lean", action="store_true")
    parser.add_argument("--show-cases", action="store_true")
    arguments = parser.parse_args()
    logging.basicConfig(level=logging.INFO, format="%(levelname)s %(message)s")
    results = []
    for prime in arguments.primes:
        if prime < 7 or prime % 6 != 1 or any(prime % divisor == 0 for divisor in range(2, int(prime**0.5) + 1)):
            raise ValueError(f"Expected a prime congruent to 1 modulo 6, received {prime}")
        logging.info("Checking exact local means modulo %s", prime)
        results.append(check_local_means(prime))
    displayed_results = (
        results
        if arguments.show_cases
        else [
            {"prime": result["prime"], "checked_cases": result["checked_cases"], "common_sum_checks": 3}
            for result in results
        ]
    )
    print(json.dumps(displayed_results, indent=2), flush=True)
    if arguments.check_lean:
        compile_gram_bulk_checkpoint()


if __name__ == "__main__":
    main()
