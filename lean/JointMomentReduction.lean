import OAI.NumberTheory.DirichletL.Hecke.DetectorWitnessArithmetic

namespace PerturbedBounds.JointMomentReduction

noncomputable section

open scoped Classical
open OAI.SevenEighths.HeckeFamily UniqueFactorizationMonoid OAI.CompletedGauss
open OAI.SevenEighths.HeckeDetectorWitnessArithmetic

local notation "O" => OAI.SevenEighths.HeckeFamily.O

/-- Express a nonunit cutoff coefficient using the complementary cutoff. -/
theorem express_cutoff_coefficient_by_complement
    (V : ℝ → ℂ) (D : ℝ) (I : Ideal O) (hI0 : I ≠ 0) (hI1 : I ≠ 1) :
    cutoffCoefficient V D I =
      -(∑' p : MulFiber I,
        (moebius p.val.1 : ℂ) * (1 - V ((Ideal.absNorm p.val.1 : ℝ) / D))) := by
  let e := mulFiberDivisorEquiv I hI0
  let : Finite (MulFiber I) := Finite.of_equiv _ e.symm
  let : Fintype (MulFiber I) := Fintype.ofFinite _
  have hsum := mulFiber_moebius_sum I hI0
  rw [tsum_fintype, ite_eq_right hI1] at hsum
  rw [cutoffCoefficient, ite_eq_right hI0, tsum_fintype, tsum_fintype]
  calc
    _ = (∑ p : MulFiber I, (moebius p.val.1 : ℂ)) -
        ∑ p : MulFiber I,
          (moebius p.val.1 : ℂ) *
            (1 - V ((Ideal.absNorm p.val.1 : ℝ) / D)) := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro p _
      ring
    _ = _ := by rw [hsum, zero_sub]

/-- Expand a finite row energy through its exact pair kernel. -/
theorem expand_finite_row_energy_through_pair_kernel
    {Row Index : Type*} (rows : Finset Row) (indices : Finset Index)
    (coefficient : Index → ℂ) (character : Row → Index → ℂ) :
    (∑ row ∈ rows,
      (∑ index ∈ indices, coefficient index * character row index) *
        star (∑ index ∈ indices, coefficient index * character row index)) =
    ∑ left ∈ indices, ∑ right ∈ indices,
      coefficient left * star (coefficient right) *
        ∑ row ∈ rows, character row left * star (character row right) := by
  simp only [star_sum, star_mul, Finset.sum_mul, Finset.mul_sum]
  conv_rhs => rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro left _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro right _
  apply Finset.sum_congr rfl
  intro row _
  ring

/-- Bound one diagonal strip by the remaining factor's row energy. -/
theorem bound_diagonal_strip_by_remaining_row_energy
    {Row Index : Type*} (rows : Finset Row) (indices : Finset Index)
    (weight : Row → Index → ℂ) (remainingFactor : Row → ℂ) (C : ℝ)
    (hweight : ∀ row ∈ rows, ∑ index ∈ indices, ‖weight row index‖ ^ 2 ≤ C) :
    (∑ row ∈ rows, ∑ index ∈ indices,
      ‖weight row index * remainingFactor row‖ ^ 2) ≤
      C * ∑ row ∈ rows, ‖remainingFactor row‖ ^ 2 := by
  calc
    _ = ∑ row ∈ rows,
        (∑ index ∈ indices, ‖weight row index‖ ^ 2) *
          ‖remainingFactor row‖ ^ 2 := by
      simp only [norm_mul, mul_pow, Finset.sum_mul]
    _ ≤ ∑ row ∈ rows, C * ‖remainingFactor row‖ ^ 2 := by
      apply Finset.sum_le_sum
      intro row hrow
      exact mul_le_mul_of_nonneg_right (hweight row hrow) (sq_nonneg _)
    _ = _ := by rw [Finset.mul_sum]

/-- Subtract both diagonal strips as a product of centered row values. -/
theorem express_double_strip_subtraction_as_centered_row_product
    {Row : Type*} (rows : Finset Row)
    (inverseEnergy plainEnergy inverseDiagonal plainDiagonal : Row → ℝ) :
    (∑ row ∈ rows,
      (inverseEnergy row - inverseDiagonal row) *
        (plainEnergy row - plainDiagonal row)) =
      (∑ row ∈ rows, inverseEnergy row * plainEnergy row) -
        (∑ row ∈ rows, inverseDiagonal row * plainEnergy row) -
        (∑ row ∈ rows, inverseEnergy row * plainDiagonal row) +
        ∑ row ∈ rows, inverseDiagonal row * plainDiagonal row := by
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
    ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro row _
  ring

#print axioms express_cutoff_coefficient_by_complement
#print axioms expand_finite_row_energy_through_pair_kernel
#print axioms bound_diagonal_strip_by_remaining_row_energy
#print axioms express_double_strip_subtraction_as_centered_row_product

end

end PerturbedBounds.JointMomentReduction
