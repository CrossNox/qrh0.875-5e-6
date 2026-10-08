import OAI.NumberTheory.DirichletL.Detector.CentralMixedMargins
import OAI.NumberTheory.DirichletL.Hecke.DetectorRowCountEndpoint
import OAI.NumberTheory.DirichletL.PrimeRows.NonfloorExponent

namespace OAI

noncomputable section
open scoped BigOperators
namespace SevenEighths.ProbeHighRowFamily
open HeckeDetectorRowCount ProbeCentralExponent

def mixedSourceExponentWithPerturbedLengths
    (t a v d R q : ℝ) : ℝ :=
  (17 / 48 - t / 2) * (1 / 2 - 17 / 50) + a + 17 / 50 - 1 -
    a * (23 / 48 - t / 2) - v * (17 / 50) + v * R +
    v * (a - 1 / 2) + (1 / 6 + t) * (17 / 50 - 1 / 2 + q) +
    (d - v) * R

lemma mixed_source_perturbation_identity
    (t a v d R q : ℝ) :
    mixedSourceExponentWithPerturbedLengths t a v d R q =
      mixedSourceExponent a (v - 3 * t / 2) (d - 3 * t / 2) R q +
        t * (-1 / 2 + (2 * a - 1) + q + 3 * R / 2) := by
  unfold mixedSourceExponentWithPerturbedLengths mixedSourceExponent
    ProbeCentralExponent.sourceExponent
  ring

lemma physical_scale_identity_with_perturbed_lengths
    (Z a e t : ℝ) (hZ : 0 < Z) :
    (Z ^ (17 / 48 - t / 2 : ℝ)) ^ (4 / 25 : ℝ) *
      Z ^ (a + 16 * e - 33 / 50) *
      (Z ^ (23 / 48 - t / 2 : ℝ)) ^ (-a - 6 * e) =
      Z ^ ((25 / 48) * a - 181 / 300 + (105 / 8) * e +
        t * (a / 2 + 3 * e - 2 / 25)) := by
  rw [← Real.rpow_mul hZ.le, ← Real.rpow_mul hZ.le,
    ← Real.rpow_add hZ, ← Real.rpow_add hZ]
  congr 1
  ring

lemma balanced_row_count_le_seventeen_twelfths
    (δ x : ℝ) (hδ : 0 ≤ δ) (hδ' : δ ≤ 3 / 4)
    (hx : 0 ≤ x) (hx' : x ≤ 1 / 2) :
    Endpoint.balancedRowCount δ (1 / 2 - x) ≤ 17 / 12 := by
  have hcut := balanced_cutoff_bounds hδ (by linarith : δ ≤ 5 / 6) hx hx'
  have hmul := mul_le_mul_of_nonneg_left hcut.2
    (show 0 ≤ (5 / 6 : ℝ) - δ by linarith)
  unfold Endpoint.balancedRowCount
  nlinarith

lemma balanced_perturbation_cost
    (δ x loss t : ℝ) (hδ : 0 ≤ δ) (hδ' : δ ≤ 3 / 4)
    (hx : 0 ≤ x) (hx' : x ≤ 1 / 2) (ht : 0 ≤ t) :
    t * (-1 / 2 + δ + δ * x +
      3 * (Endpoint.balancedRowCount δ (1 / 2 - x) + loss) / 2) ≤
      t * (11 / 4 + 3 * loss / 2) := by
  have hrow := balanced_row_count_le_seventeen_twelfths δ x hδ hδ' hx hx'
  have hq := mul_le_mul_of_nonneg_left hx' hδ
  apply mul_le_mul_of_nonneg_left _ ht
  nlinarith

lemma balanced_mixed_saving_with_perturbed_lengths
    (δ x loss ζ μ v d t other saving : ℝ)
    (hδ : 0 ≤ δ) (hδ' : δ ≤ 3 / 4)
    (hx : 0 ≤ x) (hx' : x ≤ 1 / 2)
    (hl : 0 ≤ loss) (hl' : loss ≤ 1 / 32)
    (hζ : 0 ≤ ζ) (hv : v ≤ 13 / 16 + 3 * t / 2 + ζ)
    (hμ : 0 ≤ μ) (hdv : d - v ≤ μ) (ht : 0 ≤ t)
    (hbudget : (13 / 16) * loss + 2 * ζ + (3 / 2) * μ + other +
      saving + t * (11 / 4 + 3 * loss / 2) + 1 / 200000 ≤ 49 / 440640) :
    mixedSourceExponentWithPerturbedLengths t ((1 + δ) / 2) v d
      (Endpoint.balancedRowCount δ (1 / 2 - x) + loss) (δ * x) +
      other ≤ 3 / 16 - 1 / 200000 - saving := by
  let R := Endpoint.balancedRowCount δ (1 / 2 - x) + loss
  have hm := balanced_mixed_margin δ x 0 loss ζ μ
    (v - 3 * t / 2) (d - 3 * t / 2)
    hδ (by linarith) hx hx' (by norm_num) (by norm_num)
    hl hl' hζ (by linarith) hμ (by linarith)
  have hc := balanced_perturbation_cost δ x loss t hδ hδ' hx hx' ht
  have hid := mixed_source_perturbation_identity t ((1 + δ) / 2) v d R (δ * x)
  have hdelta : 2 * ((1 + δ) / 2) - 1 = δ := by ring
  rw [hdelta] at hid
  simp only [zero_div, add_zero, mul_zero] at hm
  rw [hid]
  dsimp [R] at hm hc ⊢
  linarith

lemma perturbed_class_exponent_identity (N : ℕ)
    (a v d R q e eps loss mesh overhead t : ℝ) :
    ((25 / 48) * a - 181 / 300 + (105 / 8) * e +
      t * (a / 2 + 3 * e - 2 / 25)) +
      (overhead + d * R + v * (a - 1 / 2 + 12 * e + eps * (N + 8) - 17 / 50) +
        loss + (1 / 6 + t) * (-(4 / 25 : ℝ) + q + mesh)) =
    mixedSourceExponentWithPerturbedLengths t a v d R q +
      ProbeCentralExponent.realLoss N v e eps loss mesh + overhead +
        t * (3 * e + mesh) := by
  unfold mixedSourceExponentWithPerturbedLengths ProbeCentralExponent.realLoss
  ring

lemma balanced_adaptive_saving_with_perturbed_lengths (N : ℕ)
    (a q ε εm slotMesh ν ζ μ v d e eps loss mesh overhead t saving : ℝ)
    (ha : 1 / 2 < a) (ha' : a ≤ 7 / 8)
    (hq : 0 ≤ q) (hq' : q ≤ (2 * a - 1) / 2)
    (hε : 0 ≤ ε) (hεm : 0 ≤ εm)
    (hslot : 0 ≤ slotMesh) (hν : 0 ≤ ν)
    (hcount : 159 * ε + εm + slotMesh + 7 * ν ≤ 1 / 32)
    (hζ : 0 ≤ ζ) (hv : v ≤ 13 / 16 + 3 * t / 2 + ζ)
    (hv1 : v ≤ 1)
    (hμ : 0 ≤ μ) (hdv : d - v ≤ μ) (ht : 0 ≤ t)
    (he : 0 ≤ e) (heps : 0 ≤ eps)
    (hbudget : (13 / 16) * (159 * ε + εm + slotMesh + 7 * ν) +
      2 * ζ + (3 / 2) * μ +
      (26 * e + (N + 8) * eps + loss + mesh / 6) + overhead + saving +
      t * (11 / 4 + 3 * (159 * ε + εm + slotMesh + 7 * ν) / 2 + 3 * e + mesh) +
      1 / 200000 ≤ 49 / 440640) :
    mixedSourceExponentWithPerturbedLengths t a v d
      (adaptiveRowExponent (2 * a - 1) q 0 ε εm slotMesh ν) q +
      ProbeCentralExponent.realLoss N v e eps loss mesh + overhead +
        t * (3 * e + mesh) ≤ 3 / 16 - 1 / 200000 - saving := by
  have hδ : 0 < 2 * a - 1 := by linarith
  have hδ' : 2 * a - 1 ≤ 3 / 4 := by linarith
  have hx : 0 ≤ q / (2 * a - 1) := div_nonneg hq hδ.le
  have hx' : q / (2 * a - 1) ≤ 1 / 2 :=
    (div_le_iff₀ hδ).mpr (by linarith)
  have hl : 0 ≤ 159 * ε + εm + slotMesh + 7 * ν := by positivity
  have haeq : (1 + (2 * a - 1)) / 2 = a := by ring
  have hqeq : (2 * a - 1) * (q / (2 * a - 1)) = q :=
    mul_div_cancel₀ q hδ.ne'
  have hr := ProbeCentralExponent.realLoss_bound N v e eps loss mesh
    hv1 he heps
  have hb := balanced_mixed_saving_with_perturbed_lengths
    (2 * a - 1) (q / (2 * a - 1))
    (159 * ε + εm + slotMesh + 7 * ν) ζ μ v d t
    (ProbeCentralExponent.realLoss N v e eps loss mesh + overhead +
      t * (3 * e + mesh)) saving
    hδ.le hδ' hx hx' hl hcount hζ hv hμ hdv ht (by linarith)
  rw [haeq, hqeq] at hb
  simp only [adaptiveRowExponent,
    ite_eq_left (show 2 * a - 1 ≤ 5 / 6 by linarith), zero_div, add_zero]
  simp only [add_assoc] at hb ⊢
  exact hb

end SevenEighths.ProbeHighRowFamily

end

end OAI
