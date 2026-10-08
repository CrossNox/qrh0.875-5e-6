import OAI.NumberTheory.DirichletL.Detector.LowSelectedSum
import OAI.NumberTheory.DirichletL.Detector.LowGramProfile
import OAI.NumberTheory.DirichletL.Detector.LocalPhysical
import OAI.NumberTheory.DirichletL.Detector.CalibrationCRT

namespace OAI.SevenEighths.GramMixedArithmetic

noncomputable section
open scoped BigOperators Classical SchwartzMap FourierTransform RealInnerProductSpace
open ProbeGauss ProbePrimePower ProbePhysical
open EisensteinSchwartzPoisson

theorem factor_completed_summand_at_its_index
    (coefficient : ActualEisensteinCubic.O →* ℂ) (window : ℝ → ℂ) (scale : ℝ)
    (column cubicDivisor : Ideal ActualEisensteinCubic.O) :
    CompletedGauss.summand coefficient window scale column cubicDivisor =
      coefficient (ProbeCompleted.completedIndex column cubicDivisor) *
        CompletedGauss.summand 1 window scale column cubicDivisor := by
  simpa only [mul_one, ProbeCompleted.completedIndex] using
    CanonicalRowCompletion.summand_mul_fixed_twist coefficient 1 window scale column cubicDivisor

theorem factor_physical_completed_summand
    (target : HeckeFamily.Character) (calibration : CalibrationData)
    (source : ActualEisensteinCubic.O)
    (hsource : CanonicalQuadraticSieve.Supported (Ideal.span {source}))
    (row : ActualEisensteinCubic.O) (window : ℝ → ℂ) (scale : ℝ)
    (column cubicDivisor : Ideal ActualEisensteinCubic.O) :
    CompletedGauss.summand (ProbeRow.rowCoefficient target calibration.Xi source hsource row)
        window scale column cubicDivisor =
      (HeckeFamily.elementCoeff target (ProbeCompleted.completedIndex column cubicDivisor) *
        star (calibration.Xi (ProbeCompleted.completedIndex column cubicDivisor)) *
        CanonicalRowCompletion.sexticReciprocityPhase source (ProbeCompleted.completedIndex column cubicDivisor) *
        CanonicalRowCompletion.idealRowHom row
          (Ideal.span {ProbeCompleted.completedIndex column cubicDivisor})) *
        CompletedGauss.summand 1 window scale column cubicDivisor := by
  rw [factor_completed_summand_at_its_index, ProbeRow.rowCoefficient_apply]

theorem transform_mixed_gauss_at_frequency {F : Type*} [Field F] [Fintype F]
    (rowCharacter sourceCharacter : MulChar F ℂ) (phase : AddChar F ℂ) (frequency : F) :
    (∑ residue : F, rowCharacter residue * frequencyGauss sourceCharacter phase (-residue) *
        phase (frequency * residue)) =
      sourceCharacter⁻¹ (-1) * gaussSum sourceCharacter phase *
        frequencyGauss (rowCharacter * sourceCharacter⁻¹) phase frequency := by
  have hswap :
      (∑ residue : F, rowCharacter residue * frequencyGauss sourceCharacter phase (-residue) *
          phase (frequency * residue)) =
      ∑ sourceResidue : F, sourceCharacter sourceResidue *
        frequencyGauss rowCharacter phase (frequency - sourceResidue) := by
    unfold frequencyGauss
    simp_rw [Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro sourceResidue _
    apply Finset.sum_congr rfl
    intro residue _
    rw [show (frequency - sourceResidue) * residue =
      (-residue) * sourceResidue + frequency * residue by ring, phase.map_add_eq_mul]
    ring
  rw [hswap]
  exact finite_gauss_convolution sourceCharacter rowCharacter phase frequency

theorem cancel_matching_gauss_character_pointwise {F : Type*} [Field F] [Fintype F]
    (character : MulChar F ℂ) (phase : AddChar F ℂ) (hnonprincipal : character ≠ 1)
    (residue : F) :
    character residue * frequencyGauss character phase (-residue) =
      character⁻¹ (-1) * gaussSum character phase * (if residue = 0 then 0 else 1) := by
  rw [frequencyGauss_nonprincipal character phase hnonprincipal]
  by_cases hzero : residue = 0
  · simp [hzero, MulChar.map_zero]
  · have hunit : IsUnit residue := isUnit_iff_ne_zero.mpr hzero
    have hcancel := congrArg (fun coefficient : MulChar F ℂ => coefficient residue)
      (mul_inv_cancel character)
    simp only [MulChar.mul_apply, MulChar.one_apply hunit] at hcancel
    rw [show -residue = (-1) * residue by ring, map_mul, ite_eq_right hzero]
    calc
      _ = character⁻¹ (-1) * gaussSum character phase *
          (character residue * character⁻¹ residue) := by ring
      _ = _ := by rw [hcancel, mul_one]

theorem sum_mixed_gauss_eq_principal {F : Type*} [Field F] [Fintype F]
    (rowCharacter sourceCharacter : MulChar F ℂ) (phase : AddChar F ℂ) :
    (∑ residue : F, rowCharacter residue * frequencyGauss sourceCharacter phase (-residue)) =
      if sourceCharacter = rowCharacter then
        rowCharacter⁻¹ (-1) * gaussSum rowCharacter phase * (Nat.card Fˣ : ℂ)
      else 0 := by
  have hconvolution := finite_gauss_convolution rowCharacter sourceCharacter phase 0
  simp only [zero_sub] at hconvolution
  rw [hconvolution]
  by_cases hcharacters : sourceCharacter = rowCharacter
  · subst sourceCharacter
    rw [mul_inv_cancel, ite_eq_left rfl]
    have hprincipal : frequencyGauss (1 : MulChar F ℂ) phase 0 = (Nat.card Fˣ : ℂ) := by
      simpa [frequencyGauss, Nat.card_eq_fintype_card] using
        (MulChar.sum_one_eq_card_units (R := F) (R' := ℂ))
    rw [hprincipal]
  · rw [ite_eq_right hcharacters, frequencyGauss_zero_nonprincipal]
    · simp
    · intro hprincipal
      apply hcharacters
      have hequality := congrArg (fun character : MulChar F ℂ => character * rowCharacter) hprincipal
      simpa only [mul_assoc, inv_mul_cancel, mul_one, one_mul] using hequality

theorem classify_squarefree_mixed_resonance (sourceExponent columnExponent cubicExponent : ℕ)
    (hsource : sourceExponent ≤ 1) (hcolumn : columnExponent ≤ 1) :
    (columnExponent + 3 * cubicExponent) % 6 = sourceExponent ↔
      columnExponent = sourceExponent ∧ cubicExponent % 2 = 0 := by
  omega

theorem cancel_higher_source_power_with_row_mask
    (prime : ActualEisensteinCubic.O) (hprime : Prime prime)
    [(Ideal.span {prime} : Ideal ActualEisensteinCubic.O).IsMaximal]
    (hgood : ConcretePrimeRowBridge.goodLambda ∉ Ideal.span {prime})
    (rowCharacter : MulChar (ActualEisensteinCubic.O ⧸ Ideal.span {prime}) ℂ)
    (sourceExponent : ℕ) (hsource : 0 < sourceExponent) (row : ActualEisensteinCubic.O) :
    rowCharacter (Ideal.Quotient.mk (Ideal.span {prime}) row) *
      sexticGauss (prime ^ (sourceExponent + 1)) (pow_ne_zero _ hprime.ne_zero) (-row) = 0 := by
  rw [sexticGauss_prime_power prime hprime hgood]
  exact higher_outer_lift_annihilated prime hprime.ne_zero
    (CompletedGauss.actualSextic (Ideal.span {prime}) hgood ^ (sourceExponent + 1))
    rowCharacter hsource row

theorem cancel_calibrated_mixed_complete_mean
    (excluded : Finset (Ideal ActualEisensteinCubic.O))
    (hmaximal : ∀ prime ∈ excluded, prime.IsMaximal) (hnonempty : excluded.Nonempty)
    (movingModulus : ActualEisensteinCubic.O) (hmodulus : movingModulus ≠ 0)
    (hcoprime : IsCoprime (calibrationForSet excluded hmaximal).generator movingModulus)
    (movingCoefficient : CenteredMomentCommonSupport.Residue movingModulus → ℂ) :
    let calibration := calibrationForSet excluded hmaximal
    (∑' residue : CenteredMomentCommonSupport.Residue (calibration.generator * movingModulus),
      calibration.residue
        (CenteredMomentFourier.frequencyReduction calibration.generator
          (calibration.generator * movingModulus) (dvd_mul_right _ _) residue) *
        movingCoefficient
          (CenteredMomentFourier.frequencyReduction movingModulus
            (calibration.generator * movingModulus) (dvd_mul_left _ _) residue)) = 0 := by
  have hzero : ¬IsCoprime (calibrationForSet excluded hmaximal).generator
      (0 : ActualEisensteinCubic.O) := by
    intro hcoprimeZero
    obtain ⟨prime, hprime⟩ := hnonempty
    have hnotMem := (calibrationForSet_coprime_iff excluded hmaximal 0).mp hcoprimeZero
      prime hprime
    exact hnotMem (Ideal.zero_mem prime)
  have hmean := calibration_mixed_fourier_zero excluded hmaximal movingModulus hmodulus
    hcoprime movingCoefficient 0 hzero
  simpa only [map_zero, zero_mul, AddChar.map_zero_eq_one, mul_one] using hmean

def sum_periodic_fourier_coefficient
    (modulus : ActualEisensteinCubic.O) (hmodulus : modulus ≠ 0)
    (coefficient : ActualEisensteinCubic.O ⧸ Ideal.span {modulus} → ℂ)
    (frequency : ℤ × ℤ) : ℂ :=
  letI : Finite (ActualEisensteinCubic.O ⧸ Ideal.span {modulus}) :=
    ConcreteTraceCRT.finite_quotient_span hmodulus
  letI : Fintype (ActualEisensteinCubic.O ⧸ Ideal.span {modulus}) := Fintype.ofFinite _
  ∑ residue : ActualEisensteinCubic.O ⧸ Ideal.span {modulus}, coefficient residue *
    (Real.fourierChar (inner ℝ
      (ConcreteTraceCRT.eisEmbedding (GaussianShiftedPartition.representative modulus residue))
      (eisensteinDualFrequency (ConcreteTraceCRT.eisEmbedding modulus)
        (ConcreteTraceCRT.eisEmbedding_ne_zero hmodulus) frequency)) : ℂ)

theorem bound_periodic_zero_mean_by_nonzero_dual_tail
    (window : 𝓢(ℂ, ℂ)) (modulus : ActualEisensteinCubic.O) (hmodulus : modulus ≠ 0)
    (coefficient : ActualEisensteinCubic.O ⧸ Ideal.span {modulus} → ℂ)
    (bound : ℝ) (hbound : ∀ residue, ‖coefficient residue‖ ≤ bound)
    (hmean : (∑' residue, coefficient residue) = 0) :
    ‖∑' row : ActualEisensteinCubic.O, coefficient (Ideal.Quotient.mk _ row) *
        window (ConcreteTraceCRT.eisEmbedding row)‖ ≤
      (2 / Real.sqrt 3) * bound *
        ∑' frequency : {frequency : ℤ × ℤ // frequency ≠ 0},
          ‖(𝓕 window) (eisensteinDualFrequency (ConcreteTraceCRT.eisEmbedding modulus)
            (ConcreteTraceCRT.eisEmbedding_ne_zero hmodulus) frequency.val)‖ := by
  letI : Finite (ActualEisensteinCubic.O ⧸ Ideal.span {modulus}) :=
    ConcreteTraceCRT.finite_quotient_span hmodulus
  letI : Fintype (ActualEisensteinCubic.O ⧸ Ideal.span {modulus}) := Fintype.ofFinite _
  let modulusNorm : ℝ := Ideal.absNorm (Ideal.span {modulus})
  let dualFrequency := eisensteinDualFrequency (ConcreteTraceCRT.eisEmbedding modulus)
    (ConcreteTraceCRT.eisEmbedding_ne_zero hmodulus)
  let dualTerm := fun frequency : ℤ × ℤ =>
    sum_periodic_fourier_coefficient modulus hmodulus coefficient frequency *
      (𝓕 window) (dualFrequency frequency)
  have hzero : dualTerm 0 = 0 := by
    have hpoint : complexPoint (0 : ℝ) 0 = 0 := by apply Complex.ext <;> rfl
    rw [tsum_fintype] at hmean
    simp [dualTerm, sum_periodic_fourier_coefficient, dualFrequency, eisensteinDualFrequency,
      hpoint, hmean]
  have hcoefficient (frequency : ℤ × ℤ) :
      ‖sum_periodic_fourier_coefficient modulus hmodulus coefficient frequency‖ ≤ modulusNorm * bound := by
    unfold sum_periodic_fourier_coefficient
    calc
      _ ≤ ∑ residue : ActualEisensteinCubic.O ⧸ Ideal.span {modulus}, ‖coefficient residue‖ := by
        apply (norm_sum_le _ _).trans
        apply Finset.sum_le_sum
        intro residue _
        simp only [norm_mul, Circle.norm_coe, mul_one, le_refl]
      _ ≤ ∑ _residue : ActualEisensteinCubic.O ⧸ Ideal.span {modulus}, bound :=
        Finset.sum_le_sum (fun residue _ => hbound residue)
      _ = _ := by
        simp [modulusNorm, Ideal.absNorm_apply, Submodule.cardQuot_apply, Nat.card_eq_fintype_card]
  have hnorm (frequency : ℤ × ℤ) : ‖dualTerm frequency‖ ≤
      modulusNorm * bound * ‖(𝓕 window) (dualFrequency frequency)‖ := by
    dsimp only [dualTerm]
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (hcoefficient frequency) (norm_nonneg _)
  have hsFourier : Summable (fun frequency : ℤ × ℤ => ‖(𝓕 window) (dualFrequency frequency)‖) :=
    dual_lattice_summable_norm window
      (eisensteinLatticeMap (ConcreteTraceCRT.eisEmbedding modulus)
        (ConcreteTraceCRT.eisEmbedding_ne_zero hmodulus))
  have hsTerm : Summable (fun frequency : ℤ × ℤ => ‖dualTerm frequency‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hnorm (hsFourier.mul_left _)
  have hremoveZero : (∑' frequency : {frequency : ℤ × ℤ // frequency ≠ 0}, dualTerm frequency.val) =
      ∑' frequency : ℤ × ℤ, dualTerm frequency := by
    apply tsum_subtype_eq_of_support_subset
    intro frequency hsupport
    change dualTerm frequency ≠ 0 at hsupport
    exact fun hfrequency => hsupport (hfrequency ▸ hzero)
  have hsum : ‖∑' frequency : ℤ × ℤ, dualTerm frequency‖ ≤ modulusNorm * bound *
      ∑' frequency : {frequency : ℤ × ℤ // frequency ≠ 0},
        ‖(𝓕 window) (dualFrequency frequency.val)‖ := by
    rw [← hremoveZero]
    have hsTermNonzero := hsTerm.subtype (fun frequency => frequency ≠ 0)
    have hsFourierNonzero := hsFourier.subtype (fun frequency => frequency ≠ 0)
    apply (norm_tsum_le_tsum_norm hsTermNonzero).trans
    simpa only [tsum_mul_left] using Summable.tsum_le_tsum
      (fun frequency : {frequency : ℤ × ℤ // frequency ≠ 0} => hnorm frequency.val)
      hsTermNonzero (hsFourierNonzero.mul_left (modulusNorm * bound))
  rw [actual_eisenstein_periodic_fourier window modulus hmodulus coefficient,
    norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  change (2 / (Real.sqrt 3 * ‖ConcreteTraceCRT.eisEmbedding modulus‖ ^ 2)) *
    ‖∑' frequency : ℤ × ℤ, dualTerm frequency‖ ≤ _
  apply (mul_le_mul_of_nonneg_left hsum (by positivity)).trans_eq
  rw [ActualEisensteinCubic.eisEmbedding_norm_sq_eq_absNorm_span]
  have hnormPositive : 0 < modulusNorm := by
    dsimp only [modulusNorm]
    exact_mod_cast Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.mpr
      (Ideal.span_singleton_eq_bot.not.mpr hmodulus))
  dsimp only [dualFrequency]
  change (2 / (Real.sqrt 3 * modulusNorm)) * (modulusNorm * bound * _) = _
  field_simp

#print axioms factor_completed_summand_at_its_index
#print axioms factor_physical_completed_summand
#print axioms transform_mixed_gauss_at_frequency
#print axioms cancel_matching_gauss_character_pointwise
#print axioms sum_mixed_gauss_eq_principal
#print axioms classify_squarefree_mixed_resonance
#print axioms cancel_higher_source_power_with_row_mask
#print axioms cancel_calibrated_mixed_complete_mean
#print axioms bound_periodic_zero_mean_by_nonzero_dual_tail

end
end OAI.SevenEighths.GramMixedArithmetic
