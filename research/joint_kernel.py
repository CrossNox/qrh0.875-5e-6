# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///

"""Check the canonical Eisenstein sextic joint kernel with exact arithmetic."""

import argparse
import hashlib
import json
import logging
from dataclasses import dataclass
from math import isqrt
from pathlib import Path


UPSTREAM_REVISION = "adc7f1241b42e322a6451854ab7e4b4c146bf78a"
SIXTH_ROOTS = ((1, 0), (0, 1), (-1, 1), (-1, 0), (0, -1), (1, -1))


def multiply_sixth_root_integers(left: tuple[int, int], right: tuple[int, int]) -> tuple[int, int]:
    a, b = left
    c, d = right
    return a * c - b * d, a * d + b * c + b * d


def multiply_ideal_factorizations(left: tuple, right: tuple) -> tuple:
    exponents = dict(left)
    for prime_index, exponent in right:
        exponents[prime_index] = exponents.get(prime_index, 0) + exponent
    return tuple(sorted(exponents.items()))


def list_supported_eisenstein_ideals(maximum_norm: int) -> tuple[list, list]:
    """Enumerate actual Eisenstein prime ideal factorizations away from two and three."""
    prime_ideals = []
    for rational_prime in range(5, maximum_norm + 1):
        if any(rational_prime % divisor == 0 for divisor in range(2, isqrt(rational_prime) + 1)):
            continue
        if rational_prime % 3 == 1:
            roots = [root for root in range(rational_prime)
                     if (root * root + root + 1) % rational_prime == 0]
            prime_ideals.extend(EisensteinResidueField(rational_prime, root) for root in roots)
        elif rational_prime**2 <= maximum_norm:
            prime_ideals.append(EisensteinResidueField(rational_prime))
    prime_ideals.sort(key=lambda field: (
        field.cardinality, field.omega_residue if field.omega_residue is not None else 0))
    ideals = [((), 1, 1)]
    for prime_index, prime_ideal in enumerate(prime_ideals):
        previous_ideals = ideals.copy()
        for factors, norm, moebius in previous_ideals:
            exponent = 1
            product_norm = norm * prime_ideal.cardinality
            while product_norm <= maximum_norm:
                ideals.append((factors + ((prime_index, exponent),), product_norm,
                               -moebius if exponent == 1 else 0))
                exponent += 1
                product_norm *= prime_ideal.cardinality
    return prime_ideals, ideals


def verify_dyadic_coefficient_conductor_groups(inverse_length: int, plain_length: int) -> dict:
    """Check coefficient grouping on actual ideals with indicator dyadic profiles."""
    if inverse_length <= 2 * plain_length:
        raise ValueError("The prime-pair check requires disjoint inverse and plain annuli")
    prime_ideals, ideals = list_supported_eisenstein_ideals(2 * inverse_length)
    inverse_ideals = [ideal for ideal in ideals if inverse_length <= ideal[1] < 2 * inverse_length]
    plain_ideals = [ideal for ideal in ideals if plain_length <= ideal[1] < 2 * plain_length]
    coefficients = {}
    for inverse_factors, _, moebius in inverse_ideals:
        if moebius == 0:
            continue
        for plain_factors, _, _ in plain_ideals:
            product_factors = multiply_ideal_factorizations(inverse_factors, plain_factors)
            coefficients[product_factors] = coefficients.get(product_factors, 0) + moebius

    grouped_coefficients = {}
    grouped_products = {}
    for product_factors, coefficient in coefficients.items():
        reduced_factors = tuple((prime_index, exponent % 6)
                                for prime_index, exponent in product_factors if exponent % 6 != 0)
        extra_zero_mask = tuple(prime_index for prime_index, exponent in product_factors if exponent % 6 == 0)
        label = reduced_factors, extra_zero_mask
        grouped_coefficients[label] = grouped_coefficients.get(label, 0) + coefficient
        grouped_products.setdefault(label, []).append(product_factors)

    inverse_primes = [ideal for ideal in inverse_ideals if len(ideal[0]) == 1 and ideal[0][0][1] == 1]
    plain_primes = [ideal for ideal in plain_ideals if len(ideal[0]) == 1 and ideal[0][0][1] == 1]
    prime_product_count = 0
    for inverse_factors, _, _ in inverse_primes:
        for plain_factors, _, _ in plain_primes:
            product_factors = multiply_ideal_factorizations(inverse_factors, plain_factors)
            if coefficients[product_factors] != -1:
                raise ArithmeticError("A separated prime pair did not have its exact coefficient -1")
            label = product_factors, ()
            if grouped_products[label] != [product_factors]:
                raise ArithmeticError("A full-norm squarefree prime product failed singleton grouping")
            prime_product_count += 1

    return {
        "inverse_length": inverse_length,
        "plain_length": plain_length,
        "profile_kind": "indicator annuli, coefficient arithmetic only",
        "prime_ideal_count": len(prime_ideals),
        "inverse_ideal_count": len(inverse_ideals),
        "plain_ideal_count": len(plain_ideals),
        "inverse_prime_ideal_count": len(inverse_primes),
        "plain_prime_ideal_count": len(plain_primes),
        "nonzero_product_coefficient_count": sum(coefficient != 0 for coefficient in coefficients.values()),
        "coefficient_square_sum": sum(coefficient**2 for coefficient in coefficients.values()),
        "masked_group_coefficient_square_sum": sum(coefficient**2 for coefficient in grouped_coefficients.values()),
        "maximum_masked_group_size": max(len(products) for products in grouped_products.values()),
        "exact_prime_product_coefficients_minus_one": prime_product_count,
        "normalized_prime_product_square_mass": [prime_product_count, inverse_length * plain_length],
    }


@dataclass(frozen=True)
class EisensteinResidueField:
    prime: int
    omega_residue: int | None = None

    @property
    def cardinality(self) -> int:
        return self.prime if self.omega_residue is not None else self.prime**2

    def list_elements(self) -> list[tuple[int, int]]:
        return [(a, b) for a in range(self.prime)
                for b in range(1 if self.omega_residue is not None else self.prime)]

    def multiply_elements(self, left: tuple[int, int], right: tuple[int, int]) -> tuple[int, int]:
        a, b = left
        c, d = right
        p = self.prime
        return (a * c - b * d) % p, (a * d + b * c - b * d) % p

    def raise_element(self, element: tuple[int, int], exponent: int) -> tuple[int, int]:
        product = (1, 0)
        while exponent != 0:
            if exponent % 2 == 1:
                product = self.multiply_elements(product, element)
            element = self.multiply_elements(element, element)
            exponent //= 2
        return product

    def add_elements(self, left: tuple[int, int], right: tuple[int, int]) -> tuple[int, int]:
        return (left[0] + right[0]) % self.prime, (left[1] + right[1]) % self.prime

    def compute_trace(self, element: tuple[int, int]) -> int:
        a, b = element
        return (a if self.omega_residue is not None else 2 * a - b) % self.prime

    def find_canonical_sextic_exponent(self, element: tuple[int, int]) -> int | None:
        """Evaluate cubicChar squared times quadraticChar in the pinned definition."""
        if element == (0, 0):
            return None
        omega = (self.omega_residue, 0) if self.omega_residue is not None else (0, 1)
        cubic_residue = self.raise_element(element, (self.cardinality - 1) // 3)
        cubic_roots = [self.raise_element(omega, exponent) for exponent in range(3)]
        cubic_exponent = cubic_roots.index(cubic_residue)
        quadratic_residue = self.raise_element(element, (self.cardinality - 1) // 2)
        if quadratic_residue not in ((1, 0), (self.prime - 1, 0)):
            raise ArithmeticError(f"Invalid quadratic residue {quadratic_residue}")
        quadratic_exponent = 0 if quadratic_residue == (1, 0) else 1
        return (4 * cubic_exponent + 3 * quadratic_exponent) % 6

    def compute_fourier_kernel(self, exponent: int, frequency: tuple[int, int]) -> list[tuple[int, int]]:
        """Return coefficients in Z[zeta_6,zeta_p] with both cyclotomic relations imposed."""
        coefficients = [[0, 0] for _ in range(self.prime)]
        for element in self.list_elements():
            sextic_exponent = self.find_canonical_sextic_exponent(element)
            if sextic_exponent is None:
                continue
            additive_exponent = self.compute_trace(self.multiply_elements(frequency, element))
            root_a, root_b = SIXTH_ROOTS[(exponent * sextic_exponent) % 6]
            coefficients[additive_exponent][0] += root_a
            coefficients[additive_exponent][1] += root_b
        last_a, last_b = coefficients[-1]
        return [(a - last_a, b - last_b) for a, b in coefficients[:-1]]

    def compute_squared_complex_norm(self, coefficients: list[tuple[int, int]]) -> list[tuple[int, int]]:
        product = [[0, 0] for _ in range(self.prime)]
        for left_index, left in enumerate(coefficients):
            for right_index, (a, b) in enumerate(coefficients):
                root_a, root_b = multiply_sixth_root_integers(left, (a + b, -b))
                additive_exponent = (left_index - right_index) % self.prime
                product[additive_exponent][0] += root_a
                product[additive_exponent][1] += root_b
        last_a, last_b = product[-1]
        return [(a - last_a, b - last_b) for a, b in product[:-1]]

    def verify_all_local_kernels(self) -> dict:
        expected_zero = [(0, 0)] * (self.prime - 1)
        kernel_digest = hashlib.sha256()
        for exponent in range(6):
            for frequency in self.list_elements():
                kernel = self.compute_fourier_kernel(exponent, frequency)
                kernel_digest.update(json.dumps(kernel).encode())
                if frequency == (0, 0):
                    expected = expected_zero.copy()
                    expected[0] = (self.cardinality - 1 if exponent == 0 else 0, 0)
                    if kernel != expected:
                        raise ArithmeticError(f"Zero frequency failure: {self}, {exponent}")
                else:
                    expected_norm = expected_zero.copy()
                    expected_norm[0] = (1 if exponent == 0 else self.cardinality, 0)
                    if self.compute_squared_complex_norm(kernel) != expected_norm:
                        raise ArithmeticError(f"Gauss norm failure: {self}, {exponent}, {frequency}")
                    if exponent == 0:
                        expected_principal = expected_zero.copy()
                        expected_principal[0] = (-1, 0)
                        if kernel != expected_principal:
                            raise ArithmeticError(f"Principal mask failure: {self}, {frequency}")
                    else:
                        frequency_sextic_exponent = self.find_canonical_sextic_exponent(frequency)
                        if frequency_sextic_exponent is None:
                            raise ArithmeticError("A nonzero frequency has zero character value")
                        inverse_phase = SIXTH_ROOTS[(-exponent * frequency_sextic_exponent) % 6]
                        gauss_kernel = self.compute_fourier_kernel(exponent, (1, 0))
                        expected_scaled = [multiply_sixth_root_integers(inverse_phase, coefficient)
                                           for coefficient in gauss_kernel]
                        if kernel != expected_scaled:
                            raise ArithmeticError(f"Canonical Gauss phase failure: {self}, {exponent}, {frequency}")

        pair_tests = 0
        for left_exponent in range(1, 13):
            for right_exponent in range(1, 13):
                joint_sum_a = 0
                joint_sum_b = 0
                for element in self.list_elements():
                    character_exponent = self.find_canonical_sextic_exponent(element)
                    if character_exponent is None:
                        continue
                    left_value = SIXTH_ROOTS[(left_exponent * character_exponent) % 6]
                    right_a, right_b = SIXTH_ROOTS[(right_exponent * character_exponent) % 6]
                    root_a, root_b = multiply_sixth_root_integers(left_value, (right_a + right_b, -right_b))
                    joint_sum_a += root_a
                    joint_sum_b += root_b
                expected_sum = (self.cardinality - 1 if (left_exponent - right_exponent) % 6 == 0 else 0, 0)
                if (joint_sum_a, joint_sum_b) != expected_sum:
                    raise ArithmeticError(f"Joint exponent failure: {self}")
                pair_tests += 1

        return {
            "prime": self.prime,
            "omega_residue": self.omega_residue,
            "field_cardinality": self.cardinality,
            "fourier_cases_checked": 6 * self.cardinality,
            "joint_exponent_cases_checked": pair_tests,
            "kernel_sha256": kernel_digest.hexdigest(),
            "exceptional_example_exponents": [1, 7],
            "exceptional_example_complete_sum": self.cardinality - 1,
            "selected_unit_character_one_count": sum(
                self.find_canonical_sextic_exponent(element) == 0 for element in self.list_elements()),
            "four_shift_correlations": self.verify_reduced_four_shift_correlations(),
        }

    def verify_reduced_four_shift_correlations(self) -> dict:
        """Check all translation and scaling classes of four shifts in the actual field."""
        elements = self.list_elements()
        character_exponents = {element: self.find_canonical_sextic_exponent(element)
                               for element in elements}
        shifted_exponents = {
            shift: [character_exponents[self.add_elements(element, shift)] for element in elements]
            for shift in elements
        }

        def compute_four_shift_correlation(shifts: tuple[tuple[int, int], ...], character_power: int) -> tuple[int, int]:
            correlation_a = 0
            correlation_b = 0
            for exponents in zip(*(shifted_exponents[shift] for shift in shifts), strict=True):
                if any(exponent is None for exponent in exponents):
                    continue
                exponent = character_power * (exponents[0] + exponents[1] - exponents[2] - exponents[3]) % 6
                root_a, root_b = SIXTH_ROOTS[exponent]
                correlation_a += root_a
                correlation_b += root_b
            return correlation_a, correlation_b

        maximum_nonexceptional_norm_squared = 0
        maximum_witness = None
        maximum_correlation = None
        exceptional_count = 0
        checked_count = 0
        collision_count = 0
        jacobi_sums = {}
        for character_power in range(1, 6):
            jacobi_a = 0
            jacobi_b = 0
            for element in elements:
                complement = self.add_elements((1, 0), ((-element[0]) % self.prime, (-element[1]) % self.prime))
                left_exponent = character_exponents[element]
                right_exponent = character_exponents[complement]
                if left_exponent is None or right_exponent is None:
                    continue
                root_a, root_b = SIXTH_ROOTS[character_power * (2 * left_exponent - right_exponent) % 6]
                jacobi_a += root_a
                jacobi_b += root_b
            jacobi_sums[character_power] = (jacobi_a, jacobi_b)
            norm_squared = jacobi_a**2 + jacobi_a * jacobi_b + jacobi_b**2
            if norm_squared != (1 if character_power == 3 else self.cardinality):
                raise ArithmeticError(f"Jacobi collision norm failure: {self}, {character_power}")
        reduced_shifts = [((0, 0), (1, 0), c, d) for c in elements for d in elements]
        reduced_shifts.extend(((0, 0), (0, 0), (1, 0), d) for d in elements)
        reduced_shifts.append(((0, 0),) * 4)
        for shifts, character_power in ((shifts, power) for shifts in reduced_shifts for power in range(1, 6)):
            correlation_a, correlation_b = compute_four_shift_correlation(shifts, character_power)
            if shifts[0] == shifts[1] == (0, 0) and shifts[2] == (1, 0) and shifts[3] not in ((0, 0), (1, 0)):
                t = shifts[3]
                t_minus_one = self.add_elements(t, (self.prime - 1, 0))
                phase_argument = self.multiply_elements(t, self.raise_element(t_minus_one, 2 * (self.cardinality - 2)))
                phase_exponent = character_exponents[phase_argument]
                if phase_exponent is None:
                    raise ArithmeticError("A three-root Jacobi phase vanished")
                expected_a, expected_b = multiply_sixth_root_integers(
                    SIXTH_ROOTS[character_power * phase_exponent % 6], jacobi_sums[character_power])
                if (correlation_a, correlation_b) != (expected_a - 1, expected_b):
                    raise ArithmeticError(f"Three-root Jacobi identity failure: {self}, {character_power}, {t}")
            norm_squared = correlation_a**2 + correlation_a * correlation_b + correlation_b**2
            numerator_shifts = sorted(shifts[:2])
            denominator_shifts = sorted(shifts[2:])
            exceptional = all(
                character_power * (numerator_shifts.count(shift) - denominator_shifts.count(shift)) % 6 == 0
                for shift in set(shifts)
            )
            if exceptional:
                exceptional_count += 1
                expected_sum = self.cardinality - len(set(shifts))
                if (correlation_a, correlation_b) != (expected_sum, 0):
                    raise ArithmeticError(f"Exceptional four-shift kernel failure: {self}, {shifts}")
            else:
                if norm_squared > 9 * self.cardinality:
                    raise ArithmeticError(f"Observed four-shift sum exceeds 3sqrt(q): {self}, {shifts}")
                if norm_squared > maximum_nonexceptional_norm_squared:
                    maximum_nonexceptional_norm_squared = norm_squared
                    maximum_witness = {"character_power": character_power,
                                       "shifts": [list(shift) for shift in shifts]}
                    maximum_correlation = [correlation_a, correlation_b]
                if len(set(shifts)) < 4:
                    collision_count += 1
                excess = norm_squared - 4 * self.cardinality - 1
                if excess > 0 and excess**2 > 16 * self.cardinality:
                    raise ArithmeticError(f"Observed four-shift sum exceeds 2sqrt(q)+1: {self}, {shifts}")
            checked_count += 1

        return {
            "normalized_shift_cases_checked": checked_count,
            "exceptional_cases": exceptional_count,
            "nonexceptional_collision_cases": collision_count,
            "maximum_nonexceptional_norm_squared": maximum_nonexceptional_norm_squared,
            "maximum_witness_shifts": maximum_witness,
            "maximum_correlation_in_zeta6_basis": maximum_correlation,
            "uniform_bound_status": "observed only, not a proof for all fields",
            "three_root_jacobi_sums": {str(power): list(value) for power, value in jacobi_sums.items()},
        }


def verify_canonical_joint_kernels() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--checkpoint", type=Path, required=True)
    parser.add_argument("--resume", action="store_true")
    arguments = parser.parse_args()
    script_digest = hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
    checkpoint = {"upstream_revision": UPSTREAM_REVISION, "script_sha256": script_digest, "fields": []}
    if arguments.resume and arguments.checkpoint.exists():
        checkpoint = json.loads(arguments.checkpoint.read_text())
        if checkpoint["script_sha256"] != script_digest:
            raise ValueError("Checkpoint belongs to a different script. Rerun without --resume.")

    fields = []
    for prime in (5, 7, 11, 13, 19, 31):
        roots = [root for root in range(prime) if (root * root + root + 1) % prime == 0]
        if prime % 3 == 1:
            if len(roots) != 2:
                raise ArithmeticError(f"Expected two split primes above {prime}")
            fields.extend(EisensteinResidueField(prime, root) for root in roots)
        else:
            if len(roots) != 0:
                raise ArithmeticError(f"Expected an inert prime above {prime}")
            fields.append(EisensteinResidueField(prime))

    completed_fields = {(item["prime"], item["omega_residue"]) for item in checkpoint["fields"]}
    for field in fields:
        if (field.prime, field.omega_residue) in completed_fields:
            logging.info("Resuming after verified field %s", field)
            continue
        logging.info("Checking actual residue field %s with q=%s", field, field.cardinality)
        checkpoint["fields"].append(field.verify_all_local_kernels())
        arguments.checkpoint.parent.mkdir(parents=True, exist_ok=True)
        arguments.checkpoint.write_text(json.dumps(checkpoint, indent=2) + "\n")
        logging.info("Saved verified field checkpoint to %s", arguments.checkpoint)
    if "coefficient_conductor_groups" not in checkpoint:
        checkpoint["coefficient_conductor_groups"] = []
    completed_cases = {(case["inverse_length"], case["plain_length"])
                       for case in checkpoint["coefficient_conductor_groups"]}
    for inverse_length, plain_length in ((32, 8), (128, 16), (256, 32), (512, 64), (1024, 64)):
        if (inverse_length, plain_length) in completed_cases:
            continue
        logging.info("Checking exact ideal coefficients D=%s N=%s", inverse_length, plain_length)
        checkpoint["coefficient_conductor_groups"].append(
            verify_dyadic_coefficient_conductor_groups(inverse_length, plain_length))
        arguments.checkpoint.write_text(json.dumps(checkpoint, indent=2) + "\n")
        logging.info("Saved coefficient conductor checkpoint to %s", arguments.checkpoint)
    logging.info("Verified %s canonical residue fields with integer arithmetic", len(fields))


if __name__ == "__main__":
    logging.basicConfig(level=logging.INFO, format="%(message)s")
    verify_canonical_joint_kernels()
