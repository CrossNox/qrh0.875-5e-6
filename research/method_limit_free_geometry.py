# /// script
# requires-python = ">=3.12"
# dependencies = []
# ///

"""Check the reflected mass obstruction for independent probe lengths."""

import json
import logging
from fractions import Fraction


def evaluate_reflected_width_witness(row_mass, slot_mass):
    dual_width = 2 * row_mass + slot_mass - 1
    hybrid_saving = min(dual_width, slot_mass, (dual_width + slot_mass) / 3)
    reflected_exponent = max(row_mass, dual_width) + slot_mass - hybrid_saving
    reflected_mass_penalty = max(Fraction(0), row_mass + slot_mass - 1)

    if dual_width < 0:
        raise ArithmeticError("The witness does not satisfy the nonnegative dual gate")

    if reflected_exponent < row_mass + reflected_mass_penalty:
        raise ArithmeticError("The reflected mass lower bound failed")

    return {
        "row_mass": str(row_mass),
        "slot_mass": str(slot_mass),
        "dual_width": str(dual_width),
        "hybrid_saving": str(hybrid_saving),
        "reflected_exponent": str(reflected_exponent),
        "mass_penalty": str(reflected_mass_penalty),
        "empty_positive_part": str(max(Fraction(0), (1 + 3 * slot_mass - 2 * row_mass) / 4)),
    }


def calculate_free_geometry_checkpoint():
    logging.info("Checking exact reflected witnesses for independent lengths")
    slot_shift = Fraction(1, 1000)
    x_length = Fraction(17, 48)
    y_length = Fraction(23, 48)
    slot_mass = Fraction(1, 6) + slot_shift
    slot_only_witness = evaluate_reflected_width_witness(x_length + y_length, slot_mass)
    gram_cap_gap = 2 * x_length - y_length - slot_mass
    principal_exponent_gain = slot_shift / 6
    reflected_low_exponent_cost = Fraction(slot_only_witness["mass_penalty"]) / 2

    if gram_cap_gap <= 0:
        raise ArithmeticError("The slot-only example violates the Gram cap")

    logging.info("The Gram cap holds, but the reflected mass penalty exceeds the signal gain")

    return {
        "source_audit_scope": "Scalar retained-width estimates, not actual arithmetic energy lower bounds",
        "slot_only_example": slot_only_witness,
        "gram_cap_gap": str(gram_cap_gap),
        "principal_exponent_gain": str(principal_exponent_gain),
        "reflected_low_exponent_cost": str(reflected_low_exponent_cost),
        "net_low_gain": str(principal_exponent_gain - reflected_low_exponent_cost),
        "independent_review_counterexample": evaluate_reflected_width_witness(
            Fraction(21, 25), Fraction(17, 100)
        ),
        "central_cost_penalty_below_mass_one": "(total_shift-slot_shift)/3",
        "central_cost_penalty_above_mass_one": "(slot_shift-total_shift)*(2/3+3*delta)",
    }


if __name__ == "__main__":
    logging.basicConfig(level=logging.INFO, format="%(message)s")
    print(json.dumps(calculate_free_geometry_checkpoint(), indent=2))
