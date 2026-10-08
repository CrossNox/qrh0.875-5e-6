import OAI.NumberTheory.DirichletL.Arithmetic.EisensteinEmbedding
import OAI.NumberTheory.DirichletL.Eisenstein.CompactEnergyFamilies
import OAI.NumberTheory.DirichletL.ChineseRemainder.PrimaryCompletions
import OAI.NumberTheory.DirichletL.ChineseRemainder.FrequencyLifts
import OAI.NumberTheory.DirichletL.Moments.Correlation

namespace OAI.SevenEighths.JointKernelArithmetic

open scoped BigOperators Classical
open ActualEisensteinCubic CanonicalRowCompletion
open CanonicalQuadraticSieve hiding O
local notation "O" => ActualEisensteinCubic.O

noncomputable section

theorem evaluate_sixth_twisted_ideal_row (u : O) (K A : Ideal O)
    (hA : Supported A) :
    idealRowHom u (K * A ^ 6) =
      idealRowHom u K * if IsCoprime A (Ideal.span {u}) then 1 else 0 := by
  rw [map_mul, map_pow, ← idealRowHom_argument_pow u 6 A hA,
    idealRowHom_sixth_mask u A hA]

theorem evaluate_sixth_twisted_ideal_row_coprime (u : O) (K A : Ideal O)
    (hA : Supported A) (hcop : IsCoprime A (Ideal.span {u})) :
    idealRowHom u (K * A ^ 6) = idealRowHom u K := by
  rw [evaluate_sixth_twisted_ideal_row u K A hA, ite_eq_left hcop, mul_one]

theorem evaluate_sixth_equivalent_joint_row (u : O) (K A B : Ideal O)
    (hA : Supported A) (hB : Supported B)
    (hcopA : IsCoprime A (Ideal.span {u})) (hcopB : IsCoprime B (Ideal.span {u})) :
    idealRowHom u (K * A ^ 6) * star (idealRowHom u (K * B ^ 6)) =
      idealRowHom u K * star (idealRowHom u K) := by
  rw [evaluate_sixth_twisted_ideal_row_coprime u K A hA hcopA,
    evaluate_sixth_twisted_ideal_row_coprime u K B hB hcopB]

theorem evaluate_active_local_zero_frequency (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) (hchar : ringChar (O ⧸ P) ≠ 2)
    [Fintype (O ⧸ P)] {j : ℕ} (hj0 : j ≠ 0) (hj6 : j < 6) :
    (∑ u : O ⧸ P, (canonicalSextic P hgood ^ j) u) = 0 := by
  exact MulChar.sum_eq_zero_of_ne_one
    (canonicalSextic_pow_ne_one P hgood hchar hj0 hj6)

theorem evaluate_masked_local_zero_frequency (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) [Fintype (O ⧸ P)] :
    (∑ u : O ⧸ P, (canonicalSextic P hgood ^ 0) u) =
      (Fintype.card (O ⧸ P)ˣ : ℂ) := by
  rw [pow_zero, MulChar.sum_one_eq_card_units]

section FourShift

variable {F : Type*} [Field F] [Fintype F]
open CenteredMomentCorrelation

def sumFourShiftCorrelation (χ : MulChar F ℂ) (a b c d : F) : ℂ :=
  ∑ x : F, χ (x + a) * χ (x + b) * star (χ (x + c)) * star (χ (x + d))

theorem evaluate_translated_two_factor_correlation (χ : MulChar F ℂ) (b d : F) :
    (∑ x : F, χ (x + b) * star (χ (x + d))) = shiftCorrelation χ (b - d) := by
  unfold shiftCorrelation
  rw [← (Equiv.addRight (-b)).sum_comp]
  swap
  · simp
  apply Finset.sum_congr rfl
  intro x _
  change χ (x + -b + b) * star (χ (x + -b + d)) =
    χ x * star (χ (x - (b - d)))
  congr 2 <;> ring

theorem evaluate_common_root_four_shift_correlation (χ : MulChar F ℂ)
    (hχ : χ ≠ 1) (b d : F) (hbd : b ≠ d) :
    sumFourShiftCorrelation χ 0 b 0 d = -1 - χ b * star (χ d) := by
  classical
  have hpoint (x : F) :
      χ x * χ (x + b) * star (χ x) * star (χ (x + d)) =
        χ (x + b) * star (χ (x + d)) -
          if x = 0 then χ b * star (χ d) else 0 := by
    by_cases hx : x = 0
    · simp [hx, MulChar.map_zero]
    · rw [show χ x * χ (x + b) * star (χ x) * star (χ (x + d)) =
        (χ x * star (χ x)) * (χ (x + b) * star (χ (x + d))) by ring,
        character_mul_star χ hx, one_mul, ite_eq_right hx, sub_zero]
  unfold sumFourShiftCorrelation
  simp only [add_zero, hpoint, Finset.sum_sub_distrib,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [evaluate_translated_two_factor_correlation,
    shiftCorrelation_nonprincipal χ hχ (sub_ne_zero.mpr hbd)]

theorem evaluate_double_root_four_shift_correlation (χ : MulChar F ℂ) (a c : F) :
    sumFourShiftCorrelation χ a a c c = shiftCorrelation (χ ^ 2) (a - c) := by
  rw [← evaluate_translated_two_factor_correlation (χ ^ 2) a c]
  unfold sumFourShiftCorrelation
  apply Finset.sum_congr rfl
  intro x _
  rw [MulChar.pow_apply' χ (by decide : (2 : ℕ) ≠ 0),
    MulChar.pow_apply' χ (by decide : (2 : ℕ) ≠ 0), star_pow]
  ring

theorem evaluate_quadratic_double_root_exception (χ : MulChar F ℂ)
    (hχ : χ ^ 2 = 1) (a c : F) (hac : a ≠ c) :
    sumFourShiftCorrelation χ a a c c = (Fintype.card F : ℂ) - 2 := by
  rw [evaluate_double_root_four_shift_correlation, hχ,
    shiftCorrelation_principal (sub_ne_zero.mpr hac)]

theorem evaluate_nonquadratic_double_root_correlation (χ : MulChar F ℂ)
    (hχ : χ ^ 2 ≠ 1) (a c : F) (hac : a ≠ c) :
    sumFourShiftCorrelation χ a a c c = -1 := by
  rw [evaluate_double_root_four_shift_correlation,
    shiftCorrelation_nonprincipal (χ ^ 2) hχ (sub_ne_zero.mpr hac)]

theorem evaluate_jacobi_squared_norm (χ φ : MulChar F ℂ)
    (hchar : ringChar ℂ ≠ ringChar F)
    (hχ : χ ≠ 1) (hφ : φ ≠ 1) (hχφ : χ * φ ≠ 1) :
    ‖jacobiSum χ φ‖ ^ 2 = (Fintype.card F : ℝ) := by
  have hstar : star (jacobiSum χ φ) = jacobiSum χ⁻¹ φ⁻¹ := by
    simp only [jacobiSum, star_sum, star_mul, MulChar.star_apply', mul_comm]
  have hproduct := jacobiSum_mul_jacobiSum_inv hchar hχ hφ hχφ
  rw [← hstar] at hproduct
  have hnorm : jacobiSum χ φ * star (jacobiSum χ φ) =
      ((‖jacobiSum χ φ‖ ^ 2 : ℝ) : ℂ) := by
    simpa only [Complex.ofReal_pow, ← starRingEnd_apply] using
      Complex.mul_conj' (jacobiSum χ φ)
  rw [hnorm] at hproduct
  exact_mod_cast hproduct

end FourShift

theorem evaluate_canonical_quadratic_double_root_exception (P : Ideal O) [P.IsMaximal]
    (hgood : lambda ∉ P) [Fintype (O ⧸ P)] (a c : O ⧸ P) (hac : a ≠ c) :
    letI : Field (O ⧸ P) := Ideal.Quotient.field P
    sumFourShiftCorrelation (canonicalSextic P hgood ^ 3) a a c c =
      (Fintype.card (O ⧸ P) : ℂ) - 2 := by
  letI : Field (O ⧸ P) := Ideal.Quotient.field P
  apply evaluate_quadratic_double_root_exception _ _ a c hac
  rw [← pow_mul, show 3 * 2 = 6 by norm_num, canonicalSextic_pow_six P hgood]

theorem compute_square_root_pair_energy_exponent_gap (r m : ℝ) :
    r + m + 1 / 2 - (1 + 5 / 6 * (r + m - 1)) = (r + m) / 6 + 1 / 3 := by
  ring

theorem bound_square_root_pair_energy_exponent_gap (r m : ℝ) (hsum : 0 ≤ r + m) :
    1 / 3 ≤ r + m + 1 / 2 - (1 + 5 / 6 * (r + m - 1)) := by
  rw [compute_square_root_pair_energy_exponent_gap]
  linarith

theorem compute_crossing_square_root_pair_energy_exponent_gap :
    let r : ℝ := 71499156 / 100000000
    let m : ℝ := 40839014 / 100000000
    r + m + 1 / 2 - (1 + 5 / 6 * (r + m - 1)) = 31233817 / 60000000 := by
  norm_num

theorem group_finite_ideal_rows_by_reduced_label_with_sixth_mask
    (ideals : Finset (Ideal O)) (reduced sixthPart : Ideal O → Ideal O)
    (coefficient : Ideal O → ℂ) (u : O)
    (hfactor : ∀ K ∈ ideals, K = reduced K * sixthPart K ^ 6)
    (hsupported : ∀ K ∈ ideals, Supported (sixthPart K)) :
    (∑ K ∈ ideals, coefficient K * idealRowHom u K) =
      ∑ A ∈ ideals.image reduced, ∑ K ∈ ideals with reduced K = A,
        coefficient K * idealRowHom u A *
          if IsCoprime (sixthPart K) (Ideal.span {u}) then 1 else 0 := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to
    (fun K hK => Finset.mem_image_of_mem reduced hK)
    (fun K => coefficient K * idealRowHom u K)]
  apply Finset.sum_congr rfl
  intro A hA
  apply Finset.sum_congr rfl
  intro K hK
  obtain ⟨hK, hlabel⟩ := Finset.mem_filter.mp hK
  rw [show idealRowHom u K = idealRowHom u (reduced K * sixthPart K ^ 6) by
    rw [← hfactor K hK],
    evaluate_sixth_twisted_ideal_row u (reduced K) (sixthPart K) (hsupported K hK), hlabel]
  ring

theorem exclude_nontrivial_sixth_part_from_full_norm_annulus (X : ℝ) (A B : Ideal O)
    (hX : 0 < X) (hA : X ≤ (Ideal.absNorm A : ℝ)) (hB0 : B ≠ 0)
    (hupper : (Ideal.absNorm (A * B ^ 6) : ℝ) < 4 * X) : B = 1 := by
  by_contra hB1
  have hBN0 : Ideal.absNorm B ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr hB0
  have hBN1 : Ideal.absNorm B ≠ 1 := by
    intro h
    exact hB1 (by simpa only [Ideal.one_eq_top] using Ideal.absNorm_eq_one_iff.mp h)
  have hBnorm : (2 : ℝ) ≤ Ideal.absNorm B := by
    exact_mod_cast (show 2 ≤ Ideal.absNorm B by omega)
  have hBpower : (64 : ℝ) ≤ (Ideal.absNorm B : ℝ) ^ 6 := by
    calc
      (64 : ℝ) = (2 : ℝ) ^ 6 := by norm_num
      _ ≤ (Ideal.absNorm B : ℝ) ^ 6 := by gcongr
  have hproduct : (Ideal.absNorm (A * B ^ 6) : ℝ) =
      (Ideal.absNorm A : ℝ) * (Ideal.absNorm B : ℝ) ^ 6 := by
    simp only [map_mul, map_pow, Nat.cast_mul, Nat.cast_pow]
  rw [hproduct] at hupper
  have hlower : 64 * X ≤ (Ideal.absNorm A : ℝ) * (Ideal.absNorm B : ℝ) ^ 6 := by
    calc
      64 * X = X * 64 := by ring
      _ ≤ (Ideal.absNorm A : ℝ) * (Ideal.absNorm B : ℝ) ^ 6 := by
        exact mul_le_mul hA hBpower (by norm_num) (hX.le.trans hA)
  linarith

theorem classify_prime_product_factor_pair (P Q d n : Ideal O)
    (hP : Prime P) (hQ : Prime Q) (hproduct : d * n = P * Q) :
    (d = 1 ∧ n = P * Q) ∨ (d = P ∧ n = Q) ∨
      (d = Q ∧ n = P) ∨ (d = P * Q ∧ n = 1) := by
  have hPd : P ∣ d * n := by rw [hproduct] <;> exact dvd_mul_right P Q
  rcases hP.dvd_or_dvd hPd with hd | hn
  · obtain ⟨a, rfl⟩ := hd
    have han : a * n = Q := by
      apply mul_left_cancel₀ hP.ne_zero
      simpa only [mul_assoc] using hproduct
    rcases hQ.irreducible.isUnit_or_isUnit han.symm with ha | hn
    · have ha1 : a = 1 := isUnit_iff_eq_one.mp ha
      rw [ha1, one_mul] at han
      exact Or.inr (Or.inl ⟨by simp [ha1], han⟩)
    · have hn1 : n = 1 := isUnit_iff_eq_one.mp hn
      rw [hn1, mul_one] at han
      exact Or.inr (Or.inr (Or.inr ⟨by rw [han], hn1⟩))
  · obtain ⟨a, rfl⟩ := hn
    have hda : d * a = Q := by
      apply mul_left_cancel₀ hP.ne_zero
      calc
        P * (d * a) = d * (P * a) := by ring
        _ = P * Q := hproduct
    rcases hQ.irreducible.isUnit_or_isUnit hda.symm with hd | ha
    · have hd1 : d = 1 := isUnit_iff_eq_one.mp hd
      rw [hd1, one_mul] at hda
      exact Or.inl ⟨hd1, by rw [hda]⟩
    · have ha1 : a = 1 := isUnit_iff_eq_one.mp ha
      rw [ha1, mul_one] at hda
      exact Or.inr (Or.inr (Or.inl ⟨hda, by simp [ha1]⟩))

def sumFiniteDyadicProductCoefficient (pairs : Finset (Ideal O × Ideal O))
    (inverseWeight plainWeight : Ideal O → ℂ) (K : Ideal O) : ℂ :=
  ∑ pair ∈ pairs with pair.1 * pair.2 = K,
    (UniqueFactorizationMonoid.moebius pair.1 : ℂ) * inverseWeight pair.1 * plainWeight pair.2

theorem evaluate_separated_prime_product_coefficient
    (pairs : Finset (Ideal O × Ideal O)) (inverseWeight plainWeight : Ideal O → ℂ)
    (P Q : Ideal O) (hP : Prime P) (hQ : Prime Q) (hmem : (P, Q) ∈ pairs)
    (hunit : inverseWeight 1 = 0) (hshort : inverseWeight Q = 0)
    (hfull : inverseWeight (P * Q) = 0) :
    sumFiniteDyadicProductCoefficient pairs inverseWeight plainWeight (P * Q) =
      -inverseWeight P * plainWeight Q := by
  classical
  unfold sumFiniteDyadicProductCoefficient
  rw [Finset.sum_eq_single (P, Q)]
  · rw [hP.irreducible.moebius_eq]
    simp
  · intro pair hpair hne
    have hproduct := (Finset.mem_filter.mp hpair).2
    rcases classify_prime_product_factor_pair P Q pair.1 pair.2 hP hQ hproduct with
      h | h | h | h
    · rw [h.1, hunit, mul_zero, zero_mul]
    · exact (hne (Prod.ext h.1 h.2)).elim
    · simp [h.1, hshort]
    · simp [h.1, hfull]
  · intro hnot
    exact (hnot (Finset.mem_filter.mpr ⟨hmem, rfl⟩)).elim

#print axioms evaluate_sixth_twisted_ideal_row
#print axioms evaluate_sixth_equivalent_joint_row
#print axioms evaluate_active_local_zero_frequency
#print axioms evaluate_masked_local_zero_frequency
#print axioms evaluate_common_root_four_shift_correlation
#print axioms evaluate_quadratic_double_root_exception
#print axioms evaluate_nonquadratic_double_root_correlation
#print axioms evaluate_jacobi_squared_norm
#print axioms evaluate_canonical_quadratic_double_root_exception
#print axioms compute_crossing_square_root_pair_energy_exponent_gap
#print axioms group_finite_ideal_rows_by_reduced_label_with_sixth_mask
#print axioms exclude_nontrivial_sixth_part_from_full_norm_annulus
#print axioms evaluate_separated_prime_product_coefficient

end

end OAI.SevenEighths.JointKernelArithmetic
