import OAIHighEulerRegion
import OAI.NumberTheory.DirichletL.Detector.PrincipalProduct

namespace PerturbedZeroFreeBound

noncomputable section

open scoped BigOperators Classical
open OAI
open OAI.SevenEighths.ProbeEuler
open ActualEisensteinCubic CompletedGauss SmoothMobiusCorrection

local notation "O" => ActualEisensteinCubic.O

def perturbedPrimeDefectBound (P : PrimeIdeal) : ℝ :=
  240 * (Ideal.absNorm P.val : ℝ) ^ (-(9 / 5 : ℝ))

theorem perturbed_prime_defect_bound_nonnegative (P : PrimeIdeal) :
    0 ≤ perturbedPrimeDefectBound P := by
  unfold perturbedPrimeDefectBound
  positivity

theorem sum_perturbed_prime_defects : Summable perturbedPrimeDefectBound := by
  have h : Summable
      (fun P : PrimeIdeal => ‖CubicEisenstein.fullIdealWeight
        ((9 / 5 : ℝ) : ℂ) P.val‖) :=
    (CubicEisenstein.fullIdealWeight_summable_norm
      ((9 / 5 : ℝ) : ℂ) (by norm_num)).comp_injective Subtype.val_injective
  apply (h.mul_left 240).congr
  intro P
  unfold perturbedPrimeDefectBound CubicEisenstein.fullIdealWeight
  simp only [P.property.ne_zero, ite_false]
  rw [Complex.norm_natCast_cpow_of_pos
    (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr P.property.ne_zero))]
  norm_num

theorem bound_principal_local_on_perturbed_region
    (eta : OAI.SevenEighths.HeckeFamily.Character) (P : PrimeIdeal)
    (hP : 4 ≤ Ideal.absNorm P.val) (s : ℂ)
    (hs : 7 / 8 - 1 / 200000 < s.re) :
    ‖principalLocal eta P s - 1‖ ≤ perturbedPrimeDefectBound P := by
  have hlocal := bound_unramified_closed_on_perturbed_region
    (Ideal.absNorm P.val) (actualAPhase eta (primaryGenerator P.val))
    (OAI.SevenEighths.HeckeFamily.elementCoeff eta (primaryGenerator P.val))
    1 s 1 (1 / 6)
    (by exact_mod_cast hP) (actualAPhase_norm_le_one eta _)
    (OAI.SevenEighths.ProbeRow.targetMonoid_norm_le_one eta _) (by simp)
    hs.le (by norm_num) (by norm_num)
  apply hlocal.trans
  unfold perturbedPrimeDefectBound
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast (show 1 ≤ Ideal.absNorm P.val by omega))
  norm_num

theorem principal_local_analytic_on_perturbed_region
    (eta : OAI.SevenEighths.HeckeFamily.Character) (P : PrimeIdeal)
    (hP : 4 ≤ Ideal.absNorm P.val) :
    AnalyticOnNhd ℂ (principalLocal eta P)
      {s : ℂ | 7 / 8 - 1 / 200000 < s.re} := by
  have hQ0 : 0 < (Ideal.absNorm P.val : ℝ) := by exact_mod_cast (by omega : 0 < Ideal.absNorm P.val)
  have hV : 1 - coordV (Ideal.absNorm P.val) (1 / 6) ≠ 0 := by
    apply OAI.SevenEighths.ProbeLocal.one_sub_ne_zero_of_norm_le_half
    rw [coordV_norm _ hQ0]
    apply rpow_le_half _ _ (by exact_mod_cast hP)
    norm_num
  have hdif : DifferentiableOn ℂ (principalLocal eta P)
      {s : ℂ | 7 / 8 - 1 / 200000 < s.re} := by
    intro s hs
    apply (unramifiedClosed_differentiableAt _ hQ0 _ _ 1 s 1 (1 / 6) ?_ hV ?_).differentiableWithinAt
    · apply OAI.SevenEighths.ProbeLocal.one_sub_ne_zero_of_norm_le_half
      apply (coordR_norm_le _ hQ0 _ s (1 / 6) (actualAPhase_norm_le_one eta _)).trans
      apply rpow_le_half _ _ (by exact_mod_cast hP)
      norm_num
      change (7 / 8 - 1 / 200000 : ℝ) < s.re at hs
      linarith
    · apply OAI.SevenEighths.ProbeLocal.one_sub_ne_zero_of_norm_le_half
      apply (coordD_norm_le _ hQ0 _ 1 s
        (OAI.SevenEighths.ProbeRow.targetMonoid_norm_le_one eta _) (by simp)).trans
      apply rpow_le_half _ _ (by exact_mod_cast hP)
      change (7 / 8 - 1 / 200000 : ℝ) < s.re at hs
      linarith
  exact hdif.analyticOnNhd (isOpen_lt continuous_const Complex.continuous_re)

theorem exists_uniform_perturbed_principal_cutoff :
    ∃ N : ℕ, 4 ≤ N ∧ ∀ (S : Finset (Ideal O)),
      (∀ P : PrimeIdeal, Ideal.absNorm P.val ≤ N → P.val ∈ S) →
      ∀ eta : OAI.SevenEighths.HeckeFamily.Character,
        AnalyticOnNhd ℂ (principalCorrection eta S)
          {s : ℂ | 7 / 8 - 1 / 200000 < s.re} ∧
        ∀ s : ℂ, 7 / 8 - 1 / 200000 < s.re →
          ‖principalCorrection eta S s - 1‖ ≤ 1 / 2 := by
  have ht := (tendsto_order.1
    (tendsto_tsum_compl_atTop_zero perturbedPrimeDefectBound)).2 (1 / 6) (by norm_num)
  obtain ⟨F, hF⟩ := ht.exists
  let N := max 4 (F.sup (fun P => Ideal.absNorm P.val))
  refine ⟨N, le_max_left _ _, ?_⟩
  intro S hS eta
  let T := {P : PrimeIdeal // P.val ∉ S}
  have hnot (P : T) : P.val ∉ F := by
    intro hm
    apply P.property
    apply hS P.val
    exact (Finset.le_sup (f := fun Q : PrimeIdeal => Ideal.absNorm Q.val) hm).trans (le_max_right _ _)
  let inc : T → {P : PrimeIdeal // P ∉ F} := fun P => ⟨P.val, hnot P⟩
  have hi : Function.Injective inc := by
    intro P Q h
    apply Subtype.ext
    exact congrArg (fun t : {P : PrimeIdeal // P ∉ F} => t.val) h
  have hnorm (P : T) : 4 ≤ Ideal.absNorm P.val.val := by
    have hh : ¬ Ideal.absNorm P.val.val ≤ N := fun h => P.property (hS P.val h)
    exact (le_max_left _ _).trans (Nat.le_of_lt (Nat.lt_of_not_ge hh))
  have hsum : Summable (fun P : T => perturbedPrimeDefectBound P.val) :=
    sum_perturbed_prime_defects.subtype _
  have hsmall : (∑' P : T, perturbedPrimeDefectBound P.val) ≤ 1 / 6 := by
    apply le_trans ?_ hF.le
    exact Summable.tsum_le_tsum_of_inj inc hi
      (fun P _ => perturbed_prime_defect_bound_nonnegative P.val) (fun _ => le_rfl)
      hsum (sum_perturbed_prime_defects.subtype _)
  have hhalf (P : T) : perturbedPrimeDefectBound P.val ≤ 1 / 2 := by
    have hterm := Summable.le_tsum hsum P
      (fun Q _ => perturbed_prime_defect_bound_nonnegative Q.val)
    linarith
  constructor
  · exact normalProduct_analytic (fun P : T => principalLocal eta P.val)
      (fun P : T => perturbedPrimeDefectBound P.val) _ (Complex.isOpen_re_gt _) hsum
      (fun P => principal_local_analytic_on_perturbed_region eta P.val (hnorm P))
      (fun P s hs => bound_principal_local_on_perturbed_region eta P.val (hnorm P) s hs) hhalf
  · intro s hs
    exact product_defect_le (fun P : T => principalLocal eta P.val s)
      (fun P : T => perturbedPrimeDefectBound P.val) hsum
      (fun P => bound_principal_local_on_perturbed_region eta P.val (hnorm P) s hs)
      hhalf hsmall

theorem exists_perturbed_principal_correction (S₀ : Finset (Ideal O)) :
    ∃ S : Finset (Ideal O), S₀ ⊆ S ∧
      ∀ eta : OAI.SevenEighths.HeckeFamily.Character,
        AnalyticOnNhd ℂ (principalCorrection eta S)
          {s : ℂ | 7 / 8 - 1 / 200000 < s.re} ∧
        ∀ s : ℂ, 7 / 8 - 1 / 200000 < s.re →
          ‖principalCorrection eta S s - 1‖ ≤ 1 / 2 := by
  obtain ⟨N, hN, hcut⟩ := exists_uniform_perturbed_principal_cutoff
  refine ⟨S₀ ∪ smallPrimeSet N, Finset.subset_union_left, ?_⟩
  apply hcut
  intro P hP
  exact Finset.mem_union_right _ ((mem_smallPrimeSet N P).mpr hP)

end

end PerturbedZeroFreeBound
