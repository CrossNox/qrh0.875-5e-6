import OAI.NumberTheory.DirichletL.Endpoint
import Mathlib.Analysis.Real.Sqrt
import ProofAudit

namespace MethodLimitGeneral

noncomputable section

open OAI.SevenEighths.Endpoint

def criticalDelta : ℝ := (49 - Real.sqrt 921) / 48

def maximumBoundaryReduction : ℝ :=
  (7 / 24 - 3 * criticalDelta / 4) / (3 + 6 * criticalDelta)

def evaluateAsymmetricEndpoint (ε u v δ y : ℝ) : ℝ :=
  balancedExponent δ y + ε +
    u * (2 * balancedRowCount δ y + δ + δ * (1 / 2 - y) - 5 / 6) +
    v * (balancedRowCount δ y + δ + δ * (1 / 2 - y) - 1 / 6)

def evaluateIndependentSlotEndpoint (ε u v w δ y : ℝ) : ℝ :=
  balancedExponent δ y + ε +
    u * (balancedRowCount δ y + δ / 2 - 1 / 6) +
    v * ((1 + δ) / 2) +
    w * (balancedRowCount δ y + δ / 2 + δ * (1 / 2 - y) - 2 / 3)

theorem bound_critical_delta : 0 ≤ criticalDelta ∧ criticalDelta ≤ 3 / 4 := by
  have hsqrt := Real.sq_sqrt (show (0 : ℝ) ≤ 921 by norm_num)
  have hnonneg := Real.sqrt_nonneg (921 : ℝ)
  have hlower : (30 : ℝ) ≤ Real.sqrt 921 := by nlinarith
  have hupper : Real.sqrt (921 : ℝ) ≤ 31 := by nlinarith
  unfold criticalDelta
  constructor <;> linarith

theorem verify_critical_delta_equation :
    288 * criticalDelta ^ 2 - 588 * criticalDelta + 185 = 0 := by
  have hsqrt := Real.sq_sqrt (show (0 : ℝ) ≤ 921 by norm_num)
  unfold criticalDelta
  nlinarith

theorem verify_row_count_equation (δ : ℝ)
    (hJ : balanceDenominator δ 0 ≠ 0) :
    324 * balanceDenominator δ 0 * (balancedRowCount δ 0 - 2 / 3) =
      288 * δ ^ 2 - 588 * δ + 185 := by
  unfold balancedRowCount balancedCutoff
  field_simp
  simp only [balanceDenominator, denominator, primeWeight]
  ring

theorem evaluate_critical_row_count : balancedRowCount criticalDelta 0 = 2 / 3 := by
  obtain ⟨hδ, hδ'⟩ := bound_critical_delta
  have hbounds := balanceDenominator_bounds (y := 0) hδ (by linarith)
    (by norm_num) (by norm_num)
  have hJ : 0 < balanceDenominator criticalDelta 0 := by linarith [hbounds.1]
  have hequation := verify_row_count_equation criticalDelta hJ.ne'
  have hroot := verify_critical_delta_equation
  have hfactor : 0 < 324 * balanceDenominator criticalDelta 0 := by positivity
  nlinarith

theorem evaluate_critical_asymmetric_endpoint (ε u v : ℝ) :
    evaluateAsymmetricEndpoint ε u v criticalDelta 0 =
      3 * criticalDelta / 4 - 7 / 24 + ε +
        (u + v) * (1 / 2 + 3 * criticalDelta / 2) := by
  unfold evaluateAsymmetricEndpoint balancedExponent
  rw [evaluate_critical_row_count]
  ring

theorem bound_asymmetric_boundary_reduction (ε u v : ℝ)
    (hlow : 4 * ε ≤ u + v)
    (hhigh : evaluateAsymmetricEndpoint ε u v criticalDelta 0 ≤ 0) :
    ε ≤ maximumBoundaryReduction := by
  have hδ := bound_critical_delta.1
  have hslope : 0 ≤ 1 / 2 + 3 * criticalDelta / 2 := by positivity
  have hcost := mul_le_mul_of_nonneg_right hlow hslope
  rw [evaluate_critical_asymmetric_endpoint] at hhigh
  unfold maximumBoundaryReduction
  apply (le_div_iff₀ (show 0 < 3 + 6 * criticalDelta by positivity)).mpr
  nlinarith

theorem bound_asymmetric_boundary_reduction_strict (ε u v : ℝ)
    (hlow : 4 * ε < u + v)
    (hhigh : evaluateAsymmetricEndpoint ε u v criticalDelta 0 ≤ 0) :
    ε < maximumBoundaryReduction := by
  have hδ := bound_critical_delta.1
  have hslope : 0 < 1 / 2 + 3 * criticalDelta / 2 := by positivity
  have hcost := mul_lt_mul_of_pos_right hlow hslope
  rw [evaluate_critical_asymmetric_endpoint] at hhigh
  unfold maximumBoundaryReduction
  apply (lt_div_iff₀ (show 0 < 3 + 6 * criticalDelta by positivity)).mpr
  nlinarith

theorem evaluate_maximum_boundary_reduction :
    maximumBoundaryReduction = (16 * Real.sqrt 921 - 485) / 13224 := by
  have hδ := bound_critical_delta.1
  have hden : 3 + 6 * criticalDelta ≠ 0 := by positivity
  have hsqrt := Real.sq_sqrt (show (0 : ℝ) ≤ 921 by norm_num)
  unfold maximumBoundaryReduction
  apply (div_eq_iff hden).mpr
  unfold criticalDelta
  nlinarith

theorem bound_maximum_boundary_reduction :
    maximumBoundaryReduction < 43 / 1000000 := by
  have hsqrt := Real.sq_sqrt (show (0 : ℝ) ≤ 921 by norm_num)
  have hnonneg := Real.sqrt_nonneg (921 : ℝ)
  have hupper : Real.sqrt (921 : ℝ) < 30348 / 1000 := by nlinarith
  rw [evaluate_maximum_boundary_reduction]
  linarith

theorem bound_independent_slot_cost (δ T w ε : ℝ) (hδ : 0 ≤ δ)
    (hlow : 12 * ε ≤ T + 2 * w - 6 * max (w - T) 0) :
    (2 + 6 * δ) * ε ≤ ((1 + δ) / 2) * T + δ * w := by
  have hfactor : 0 ≤ (1 + 3 * δ) / 6 := by positivity
  by_cases hmass : w ≤ T
  · have hmax : max (w - T) 0 = 0 := max_eq_right (by linarith)
    rw [hmax] at hlow
    have hscaled := mul_le_mul_of_nonneg_right hlow hfactor
    nlinarith
  · have hmax : max (w - T) 0 = w - T := max_eq_left (by linarith)
    rw [hmax] at hlow
    have hscaled := mul_le_mul_of_nonneg_right hlow hfactor
    have hremaining : 0 ≤ (2 / 3 + 3 * δ) * (w - T) :=
      mul_nonneg (by positivity) (by linarith)
    nlinarith

theorem bound_independent_slot_boundary_reduction (ε u v w : ℝ)
    (hlow : 12 * ε ≤ u + v + 2 * w - 6 * max (w - (u + v)) 0)
    (hhigh : evaluateIndependentSlotEndpoint ε u v w criticalDelta 0 ≤ 0) :
    ε ≤ maximumBoundaryReduction := by
  have hδ := bound_critical_delta.1
  have hcost := bound_independent_slot_cost criticalDelta (u + v) w ε hδ hlow
  have hevaluation : evaluateIndependentSlotEndpoint ε u v w criticalDelta 0 =
      3 * criticalDelta / 4 - 7 / 24 + ε +
        ((1 + criticalDelta) / 2) * (u + v) + criticalDelta * w := by
    unfold evaluateIndependentSlotEndpoint balancedExponent
    rw [evaluate_critical_row_count]
    ring
  rw [hevaluation] at hhigh
  unfold maximumBoundaryReduction
  apply (le_div_iff₀ (show 0 < 3 + 6 * criticalDelta by positivity)).mpr
  nlinarith

theorem verify_asymmetric_signal (s u v : ℝ) :
    (17 / 48 - u) / 2 + s - 1 + (13 / 16 + 2 * u + v) / 6 =
      s - 11 / 16 + (v - u) / 6 := by ring

theorem verify_asymmetric_low_gap (ε u v : ℝ) :
    (7 / 8 - ε - 11 / 16 + (v - u) / 6) -
      ((17 / 48 - u) / 2 + ((23 / 48 - v) - (17 / 48 - u)) / 12) =
      (u + v) / 4 - ε := by ring

#assert_standard_axioms bound_asymmetric_boundary_reduction
#assert_standard_axioms bound_asymmetric_boundary_reduction_strict
#assert_standard_axioms evaluate_maximum_boundary_reduction
#assert_standard_axioms bound_maximum_boundary_reduction
#assert_standard_axioms bound_independent_slot_cost
#assert_standard_axioms bound_independent_slot_boundary_reduction
#assert_standard_axioms verify_asymmetric_signal
#assert_standard_axioms verify_asymmetric_low_gap

end

end MethodLimitGeneral
