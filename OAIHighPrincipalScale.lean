import OAI.NumberTheory.DirichletL.Detector.PrincipalRemainderBounds

namespace OAI

noncomputable section
open scoped BigOperators
namespace SevenEighths.ProbePrincipalRemainderBounds

lemma perturbed_source_scale_identity {ι : Type*} (J : Finset ι)
    (ell : ι → ℝ) (t Z a ξ υ : ℝ)
    (hell : ∑ j ∈ J, ell j = 1 / 6 + t) (hZ : 0 < Z) :
    scalePower (Z ^ (17 / 48 - t / 2 : ℝ))
        (Z ^ (23 / 48 - t / 2 : ℝ)) Z a ξ υ *
      (∏ j ∈ J, (Z ^ (ell j)) ^ ξ) =
        Z ^ (a - 11 / 16 + (13 / 16) * (ξ - 1 / 6) +
          (23 / 48) * (υ - 1) + t * (1 / 4 + 3 * ξ / 2 - υ / 2)) := by
  have hp : (∏ j ∈ J, (Z ^ (ell j)) ^ ξ) = Z ^ ((1 / 6 + t) * ξ) := by
    simp only [← Real.rpow_mul hZ.le]
    rw [← Real.rpow_sum_of_pos hZ, ← Finset.sum_mul, hell]
  rw [hp, scalePower, ← Real.rpow_mul hZ.le, ← Real.rpow_mul hZ.le]
  rw [← Real.rpow_add hZ, ← Real.rpow_add hZ, ← Real.rpow_add hZ]
  congr 1
  ring

lemma perturbed_source_w_scale_identity {ι : Type*} (J : Finset ι)
    (ell : ι → ℝ) (t Z a e : ℝ)
    (hell : ∑ j ∈ J, ell j = 1 / 6 + t) (hZ : 0 < Z) :
    scalePower (Z ^ (17 / 48 - t / 2 : ℝ))
        (Z ^ (23 / 48 - t / 2 : ℝ)) Z a (1 / 6 + e) (19 / 20) *
      (∏ j ∈ J, (Z ^ (ell j)) ^ (1 / 6 + e)) =
        Z ^ (a - 11 / 16 + (13 / 16) * e - 23 / 960 +
          t * (1 / 40 + 3 * e / 2)) := by
  rw [perturbed_source_scale_identity J ell t Z a (1 / 6 + e) (19 / 20) hell hZ]
  congr 1
  ring

lemma perturbed_source_z_scale_identity {ι : Type*} (J : Finset ι)
    (ell : ι → ℝ) (t Z a : ℝ)
    (hell : ∑ j ∈ J, ell j = 1 / 6 + t) (hZ : 0 < Z) :
    scalePower (Z ^ (17 / 48 - t / 2 : ℝ))
        (Z ^ (23 / 48 - t / 2 : ℝ)) Z a (33 / 200) 1 *
      (∏ j ∈ J, (Z ^ (ell j)) ^ (33 / 200 : ℝ)) =
        Z ^ (a - 11 / 16 - 13 / 9600 - t / 400) := by
  rw [perturbed_source_scale_identity J ell t Z a (33 / 200) 1 hell hZ]
  congr 1
  ring

lemma perturbed_source_w_strict_exponent (β e t : ℝ)
    (he' : e ≤ 1 / 1000)
    (ht : 0 ≤ t) (ht' : t ≤ 3 / 100000) :
    (β + e) - 11 / 16 + (13 / 16) * e - 23 / 960 +
      t * (1 / 40 + 3 * e / 2) ≤ β - 11 / 16 - 17 / 48000 := by
  have heprod := mul_le_mul_of_nonneg_left he' ht
  nlinarith

lemma perturbed_source_z_strict_exponent (β e t : ℝ)
    (he : e ≤ 1 / 1000) (ht : 0 ≤ t) :
    (β + e) - 11 / 16 - 13 / 9600 - t / 400 ≤
      β - 11 / 16 - 17 / 48000 := by
  linarith

end SevenEighths.ProbePrincipalRemainderBounds

end

end OAI
