# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///

"""Count sixth-equivalent ideal pairs in Eisenstein norm annuli."""

import argparse
import json
import logging
import math
from dataclasses import dataclass


@dataclass(frozen=True)
class EisensteinIdealCounts:
    all_ideals: list[int]
    sixth_power_free_ideals: list[int]

    @classmethod
    def count_ideals_by_norm(cls, maximum_norm: int) -> "EisensteinIdealCounts":
        smallest_prime = list(range(maximum_norm + 1))
        for prime in range(2, maximum_norm + 1):
            if smallest_prime[prime] != prime:
                continue
            for multiple in range(prime * prime, maximum_norm + 1, prime):
                if smallest_prime[multiple] == multiple:
                    smallest_prime[multiple] = prime

        all_ideals = [0] * (maximum_norm + 1)
        sixth_power_free_ideals = [0] * (maximum_norm + 1)
        all_ideals[1] = 1
        sixth_power_free_ideals[1] = 1

        for norm in range(2, maximum_norm + 1):
            prime = smallest_prime[norm]
            exponent = 0
            remaining_norm = norm
            while remaining_norm % prime == 0:
                exponent += 1
                remaining_norm //= prime

            if prime == 3:
                unrestricted_factor = 1
                sixth_power_free_factor = int(exponent <= 5)
            elif prime % 3 == 1:
                unrestricted_factor = exponent + 1
                sixth_power_free_factor = max(
                    0, min(5, exponent) - max(0, exponent - 5) + 1,
                )
            else:
                unrestricted_factor = int(exponent % 2 == 0)
                sixth_power_free_factor = int(
                    exponent % 2 == 0 and exponent // 2 <= 5,
                )

            all_ideals[norm] = (
                all_ideals[remaining_norm] * unrestricted_factor
            )
            sixth_power_free_ideals[norm] = (
                sixth_power_free_ideals[remaining_norm] * sixth_power_free_factor
            )

        return cls(all_ideals, sixth_power_free_ideals)

    def count_sixth_equivalent_pairs_in_annulus(self, lower_norm: int) -> int:
        upper_norm = 2 * lower_norm
        sixth_root_choices = [0] * upper_norm
        norm_of_root = 1
        while norm_of_root**6 < upper_norm:
            sixth_power = norm_of_root**6
            minimum_core_norm = (lower_norm + sixth_power - 1) // sixth_power
            maximum_core_norm = (upper_norm - 1) // sixth_power
            for core_norm in range(minimum_core_norm, maximum_core_norm + 1):
                sixth_root_choices[core_norm] += self.all_ideals[norm_of_root]
            norm_of_root += 1

        return sum(
            self.sixth_power_free_ideals[core_norm] * root_count**2
            for core_norm, root_count in enumerate(sixth_root_choices)
        )

    def verify_ideal_counts_and_sixth_power_decomposition(self) -> None:
        expected_counts = {1: 1, 2: 0, 3: 1, 4: 1, 7: 2, 9: 1, 13: 2, 49: 3}
        for norm, expected_count in expected_counts.items():
            actual_count = self.all_ideals[norm]
            if actual_count != expected_count:
                raise AssertionError(
                    f"Ideal count at norm {norm}: {actual_count}, "
                    f"expected {expected_count}"
                )

        for norm in range(1, len(self.all_ideals)):
            recovered_count = 0
            norm_of_root = 1
            while norm_of_root**6 <= norm:
                sixth_power = norm_of_root**6
                if norm % sixth_power == 0:
                    recovered_count += (
                        self.all_ideals[norm_of_root]
                        * self.sixth_power_free_ideals[norm // sixth_power]
                    )
                norm_of_root += 1
            if recovered_count != self.all_ideals[norm]:
                raise AssertionError(
                    f"Sixth-power decomposition failed at norm {norm}: "
                    f"{recovered_count} versus {self.all_ideals[norm]}"
                )


def diagnose_four_shift_cauchy_exponents_at_balanced_crossing(
    delta: float, amplitude: float,
) -> dict[str, float]:
    inverse_slope = 5 / 6 - delta
    crossing_denominator = 3 - 17 * amplitude / 9
    plain_capacity = (2 - 8 * amplitude / 9) * (1 - amplitude)
    total_length = 1 + delta * plain_capacity / (
        2 * (inverse_slope * crossing_denominator + delta * plain_capacity)
    )
    inverse_length = (
        (2 - 8 * amplitude / 9) * total_length - 5 * amplitude / 9
    ) / crossing_denominator
    plain_length = total_length - inverse_length
    target_energy_exponent = 1 + 5 * (total_length - 1) / 6
    return {
        "delta": delta,
        "amplitude": amplitude,
        "inverse_length": inverse_length,
        "plain_length": plain_length,
        "total_length": total_length,
        "target_energy_exponent_without_saving": target_energy_exponent,
        "direct_four_ideal_kernel_bound_term": 3 / 4 + total_length / 4,
        "short_row_pair_kernel_bound_term": 3 * plain_length / 4 + 1 / 4,
        "long_row_pair_kernel_bound_term": 3 * inverse_length / 4 + 1 / 4,
        "energy_bound_with_optimistic_square_root_row_pairs": 1 + plain_length / 2,
        "additional_signed_saving_needed_after_pairwise_square_root": (
            total_length / 6 + 1 / 3
        ),
    }


def run_resonant_pair_experiment() -> None:
    argument_parser = argparse.ArgumentParser(description=__doc__)
    argument_parser.add_argument("--minimum-exponent", type=int, default=8)
    argument_parser.add_argument("--maximum-exponent", type=int, default=18)
    arguments = argument_parser.parse_args()
    if not 6 <= arguments.minimum_exponent <= arguments.maximum_exponent:
        raise ValueError("Require 6 ≤ minimum exponent ≤ maximum exponent")

    maximum_norm = 2 ** (arguments.maximum_exponent + 1) - 1
    logging.info("Counting Eisenstein ideals through norm %s", maximum_norm)
    ideal_counts = EisensteinIdealCounts.count_ideals_by_norm(maximum_norm)
    ideal_counts.verify_ideal_counts_and_sixth_power_decomposition()
    logging.info("Verified the exact sixth-power decomposition at every norm")

    measurements = []
    for exponent in range(arguments.minimum_exponent, arguments.maximum_exponent + 1):
        lower_norm = 2**exponent
        resonant_pair_count = ideal_counts.count_sixth_equivalent_pairs_in_annulus(
            lower_norm,
        )
        diagonal_pair_count = sum(ideal_counts.all_ideals[lower_norm:2 * lower_norm])
        measurements.append({
            "lower_norm": lower_norm,
            "resonant_pairs": resonant_pair_count,
            "diagonal_pairs": diagonal_pair_count,
            "resonant_pairs_per_lower_norm": resonant_pair_count / lower_norm,
            "off_diagonal_resonant_pairs": resonant_pair_count - diagonal_pair_count,
        })

    print(json.dumps({
        "status": "Exact ideal counting only. No incomplete kernel bound is tested.",
        "annulus": "[X, 2X)",
        "resonance": "Equal prime ideal valuations modulo six at every prime",
        "measurements": measurements,
        "conditional_exponent_diagnostics": [
            diagnose_four_shift_cauchy_exponents_at_balanced_crossing(0.3867, 0.5),
            diagnose_four_shift_cauchy_exponents_at_balanced_crossing(
                (49 - math.sqrt(921)) / 48, 0.5,
            ),
        ],
    }, indent=2))


if __name__ == "__main__":
    logging.basicConfig(level=logging.INFO, format="%(message)s")
    run_resonant_pair_experiment()
