import Std

namespace PerturbedZeroFreeBound

theorem verify_boundary :
    7 * 25000 = 174999 + 1 := by
  decide

theorem verify_geometry :
    212491 + 287491 + 100018 = 600000 ∧
    287491 - 212491 = 75000 ∧
    487527 = 600000 - 212491 + 100018 := by
  decide

theorem verify_signal_and_gram_gap :
    3 * 212491 + 487527 = 1125000 ∧
    16 * 2475000 = 11 * 3600000 ∧
    287491 - 100018 - 137500 = 49973 ∧
    49973 > 0 := by
  decide

theorem verify_low_margin :
    6 * 174999 - 825000 = 224994 ∧
    212491 + 12500 = 224991 ∧
    224994 - 224991 = 3 := by
  decide

theorem verify_high_margin :
    2 + 11 * 3 = 7 * 5 ∧
    49 * 250 - 7 * 1377 = 2611 ∧
    2611 > 0 := by
  decide

theorem bound_high_derivative (delta q rowExponent : Int)
    (hdelta : delta ≤ 18) (hq : 2 * q ≤ delta)
    (hrow : rowExponent ≤ 34) :
    -24 + 2 * delta + 2 * q + 3 * rowExponent ≤ 132 := by
  omega

theorem bound_reflected_row_loss (scaledSubsetLength : Int)
    (hsubset : 0 ≤ scaledSubsetLength) :
    0 ≤ 8 * scaledSubsetLength ∧
    scaledSubsetLength - 99910 ≤ 8 * scaledSubsetLength := by
  omega

theorem verify_euler_margins :
    -363 * 500 + 3 < -100000 ∧
    -33 * 2500 + 3 < 0 ∧
    174999 - 100000 > 74000 := by
  decide

theorem verify_prime_supply :
    39 * 100018 > 8 * 487527 ∧
    48 * (5 * 100018 - 487527) > 600000 := by
  decide

end PerturbedZeroFreeBound
