import OAI.NumberTheory.DirichletL.Detector.GramPeriodicPoisson
import OAI.NumberTheory.DirichletL.Detector.GramIdealSummation

namespace PerturbedZeroFreeBound.GramCenteredRemainder

set_option maxHeartbeats 1000000

noncomputable section
open MeasureTheory
open scoped BigOperators Classical FourierTransform SchwartzMap
open OAI

def averageResidueCoefficient {R : Type*} (a : R → ℂ) : ℂ :=
  (Nat.card R : ℂ)⁻¹ * ∑' v, a v

def centerResidueCoefficient {R : Type*} (a : R → ℂ) (v : R) : ℂ :=
  a v - averageResidueCoefficient a

theorem sum_centered_residue_coefficient {R : Type*} [Finite R] [Nonempty R]
    (a : R → ℂ) : (∑' v, centerResidueCoefficient a v) = 0 := by
  classical
  let : Fintype R := Fintype.ofFinite R
  have hcard : (Fintype.card R : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  simp [centerResidueCoefficient, averageResidueCoefficient, tsum_fintype,
    Finset.sum_sub_distrib, Nat.card_eq_fintype_card, hcard]

theorem norm_average_residue_coefficient {R : Type*} [Finite R] [Nonempty R]
    (a : R → ℂ) (B : ℝ) (hB : ∀ v, ‖a v‖ ≤ B) :
    ‖averageResidueCoefficient a‖ ≤ B := by
  classical
  let : Fintype R := Fintype.ofFinite R
  have hcard : (0 : ℝ) < Fintype.card R := by
    exact_mod_cast Fintype.card_pos
  unfold averageResidueCoefficient
  rw [norm_mul, norm_inv, Complex.norm_natCast, Nat.card_eq_fintype_card,
    tsum_fintype]
  calc
    _ ≤ (Fintype.card R : ℝ)⁻¹ * (∑ v, ‖a v‖) :=
      mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
    _ ≤ (Fintype.card R : ℝ)⁻¹ * (∑ _v : R, B) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun v _ => hB v)) (by positivity)
    _ = B := by simp [hcard.ne']

theorem norm_centered_residue_coefficient {R : Type*} [Finite R] [Nonempty R]
    (a : R → ℂ) (B : ℝ) (hB : ∀ v, ‖a v‖ ≤ B) (v : R) :
    ‖centerResidueCoefficient a v‖ ≤ 2 * B := by
  exact (norm_sub_le _ _).trans (by
    have havg := norm_average_residue_coefficient a B hB
    have hv := hB v
    change ‖a v‖ + ‖averageResidueCoefficient a‖ ≤ 2 * B
    linarith)

open ProbeGramPeriodicPoisson ActualEisensteinCubic ConcreteTraceCRT

theorem principal_residue_cardinality (c : ActualEisensteinCubic.O) (_hc : c ≠ 0) :
    Nat.card (Residue c × Residue c) = (Ideal.absNorm (Ideal.span {c}))^2 := by
  simp [Nat.card_prod, Residue, Ideal.absNorm_apply, Submodule.cardQuot_apply, pow_two]

theorem average_ideal_residue_coefficient_eq (r : Ideal ActualEisensteinCubic.O)
    (a : (ActualEisensteinCubic.O ⧸ r) × (ActualEisensteinCubic.O ⧸ r) → ℂ) :
    averageResidueCoefficient a =
      ((Ideal.absNorm r : ℂ)^2)⁻¹ * ∑' v, a v := by
  simp [averageResidueCoefficient, Nat.card_prod, Ideal.absNorm_apply,
    Submodule.cardQuot_apply, pow_two, Nat.cast_mul]

theorem principal_zero_mode_eq_average (W : 𝓢(Joint, ℂ))
    (c : ActualEisensteinCubic.O) (hc : c ≠ 0)
    (a : Residue c × Residue c → ℂ) :
    (2 / (Real.sqrt 3 * ‖eisEmbedding c‖^2))^2 •
      (residueFourier c hc a 0 * (𝓕 W) 0) =
        (4/3 : ℂ) * averageResidueCoefficient a * (𝓕 W) 0 := by
  have hcov : (2 / (Real.sqrt 3 * ‖eisEmbedding c‖^2))^2 *
      (Nat.card (Residue c × Residue c) : ℝ) = 4/3 := by
    rw [principal_residue_cardinality c hc, Nat.cast_pow]
    exact principal_joint_inverse_covolume c hc
  have hcovC : (((2 / (Real.sqrt 3 * ‖eisEmbedding c‖^2))^2 : ℝ) : ℂ) *
      (Nat.card (Residue c × Residue c) : ℂ) = 4/3 := by
    simpa using congrArg (fun x : ℝ => (x : ℂ)) hcov
  have hcard : (Nat.card (Residue c × Residue c) : ℂ) ≠ 0 := by
    have hfinite : Finite (Residue c) := finite_quotient_span hc
    let := hfinite
    exact_mod_cast Nat.card_pos.ne'
  rw [residueFourier_zero, averageResidueCoefficient, ← hcovC,
    Algebra.smul_def]
  simp only [mul_assoc, mul_inv_cancel_left₀ hcard]
  rfl

theorem split_principal_periodic_bulk (W : 𝓢(Joint, ℂ))
    (c : ActualEisensteinCubic.O) (hc : c ≠ 0)
    (a : Residue c × Residue c → ℂ) (B : ℝ) (hB : ∀ v, ‖a v‖ ≤ B) :
    (∑' m : ActualEisensteinCubic.O × ActualEisensteinCubic.O,
      a (quotientPair c m) * W (embeddingPair m)) =
      (4/3 : ℂ) * averageResidueCoefficient a * (𝓕 W) 0 +
        (2 / (Real.sqrt 3 * ‖eisEmbedding c‖^2))^2 •
          ∑' p : {p : (ℤ × ℤ) × (ℤ × ℤ) // p ≠ 0},
            residueFourier c hc a p.val *
              (𝓕 W) (jointFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p.val) := by
  classical
  let F (p : (ℤ × ℤ) × (ℤ × ℤ)) := residueFourier c hc a p *
    (𝓕 W) (jointFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p)
  have hnorm (p) : ‖F p‖ ≤ (Ideal.absNorm (Ideal.span {c}) : ℝ)^2 * B *
      ‖(𝓕 W) (jointFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p)‖ := by
    dsimp only [F]
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (residueFourier_norm_le c hc a B hB p)
      (norm_nonneg _)
  have hsF : Summable F := Summable.of_norm
    (Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hnorm
      ((jointFrequency_summable_norm W (eisEmbedding c)
        (eisEmbedding_ne_zero hc)).mul_left _))
  have hsplit : (∑' p, F p) = F 0 +
      ∑' p : {p : (ℤ × ℤ) × (ℤ × ℤ) // p ≠ 0}, F p.val := by
    have h := (hsF.sum_add_tsum_subtype_compl
      ({0} : Finset ((ℤ × ℤ) × (ℤ × ℤ)))).symm
    simp only [Finset.sum_singleton] at h
    have hcompl : (fun p : (ℤ × ℤ) × (ℤ × ℤ) => p ∉
        ({0} : Finset ((ℤ × ℤ) × (ℤ × ℤ)))) = (fun p => p ≠ 0) := by
      funext p
      simp
    rw [hcompl] at h
    exact h
  rw [actual_joint_periodic_fourier W c hc a, hsplit, smul_add]
  congr 1
  simpa only [F, jointFrequency_zero] using principal_zero_mode_eq_average W c hc a

theorem split_principal_physical_bulk (W : 𝓢(Joint, ℂ))
    (c : ActualEisensteinCubic.O) (hc : c ≠ 0)
    (a : Residue c × Residue c → ℂ) (B : ℝ) (hB : ∀ v, ‖a v‖ ≤ B)
    (N : ℝ) (hN : 0 < N) :
    (∑' m : ActualEisensteinCubic.O × ActualEisensteinCubic.O,
      a (quotientPair c m) * W (ProbeGramLatticeDecay.physicalPoint N m)) =
      (4/3 : ℂ) * averageResidueCoefficient a * (N^2 : ℝ) *
        (∫ z : Joint, W z) +
        (2 / (Real.sqrt 3 * ‖eisEmbedding c‖^2))^2 •
          ∑' p : {p : (ℤ × ℤ) × (ℤ × ℤ) // p ≠ 0},
            residueFourier c hc a p.val *
              (𝓕 (scaledSource W (Real.sqrt N) (Real.sqrt_pos.mpr hN)))
                (jointFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p.val) := by
  have hsplit := split_principal_periodic_bulk
    (scaledSource W (Real.sqrt N) (Real.sqrt_pos.mpr hN)) c hc a B hB
  have ht4 : (Real.sqrt N)^4 = N^2 := by
    rw [show (4 : ℕ) = 2*2 by norm_num, pow_mul, Real.sq_sqrt hN.le]
  simp_rw [scaledSource_physicalPoint W N hN] at hsplit
  rw [fourier_scaledSource, smul_zero, ht4] at hsplit
  have hf0 : (𝓕 W) 0 = ∫ z : Joint, W z := by
    change (𝓕 (W : Joint → ℂ)) 0 = _
    simp [Real.fourier_eq]
  rw [hf0] at hsplit
  simpa [Algebra.smul_def, mul_assoc] using hsplit

theorem norm_principal_periodic_bulk_remainder_le (W : 𝓢(Joint, ℂ))
    (c : ActualEisensteinCubic.O) (hc : c ≠ 0)
    (a : Residue c × Residue c → ℂ) (B : ℝ) (hB : ∀ v, ‖a v‖ ≤ B) :
    ‖(∑' m : ActualEisensteinCubic.O × ActualEisensteinCubic.O,
      a (quotientPair c m) * W (embeddingPair m)) -
      (4/3 : ℂ) * averageResidueCoefficient a * (𝓕 W) 0‖ ≤
      (4/3 : ℝ) * B *
        ∑' p : {p : (ℤ × ℤ) × (ℤ × ℤ) // p ≠ 0},
          ‖(𝓕 W) (jointFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p.val)‖ := by
  let q : ℝ := Ideal.absNorm (Ideal.span {c})
  let F (p : (ℤ × ℤ) × (ℤ × ℤ)) := residueFourier c hc a p *
    (𝓕 W) (jointFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p)
  have hnorm (p) : ‖F p‖ ≤ q^2 * B *
      ‖(𝓕 W) (jointFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p)‖ := by
    dsimp only [F]
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_right (residueFourier_norm_le c hc a B hB p)
      (norm_nonneg _)
  have hsD : Summable (fun p : {p : (ℤ × ℤ) × (ℤ × ℤ) // p ≠ 0} =>
      ‖(𝓕 W) (jointFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p.val)‖) :=
    (jointFrequency_summable_norm W (eisEmbedding c)
      (eisEmbedding_ne_zero hc)).subtype (fun p => p ≠ 0)
  have hsF : Summable (fun p : {p : (ℤ × ℤ) × (ℤ × ℤ) // p ≠ 0} => ‖F p.val‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun p => hnorm p.val)
      (hsD.mul_left (q^2 * B))
  have hb : ‖∑' p : {p : (ℤ × ℤ) × (ℤ × ℤ) // p ≠ 0}, F p.val‖ ≤
      q^2 * B * ∑' p : {p : (ℤ × ℤ) × (ℤ × ℤ) // p ≠ 0},
        ‖(𝓕 W) (jointFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p.val)‖ := by
    have hnormsum : ‖∑' p : {p : (ℤ × ℤ) × (ℤ × ℤ) // p ≠ 0}, F p.val‖ ≤
        ∑' p : {p : (ℤ × ℤ) × (ℤ × ℤ) // p ≠ 0}, ‖F p.val‖ :=
      norm_tsum_le_tsum_norm hsF
    have htermbound : (∑' p : {p : (ℤ × ℤ) × (ℤ × ℤ) // p ≠ 0}, ‖F p.val‖) ≤
        ∑' p : {p : (ℤ × ℤ) × (ℤ × ℤ) // p ≠ 0}, q^2 * B *
          ‖(𝓕 W) (jointFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p.val)‖ :=
      Summable.tsum_le_tsum
        (fun p : {p : (ℤ × ℤ) × (ℤ × ℤ) // p ≠ 0} => hnorm p.val) hsF
        (hsD.mul_left (q^2 * B))
    exact hnormsum.trans (by simpa only [tsum_mul_left] using htermbound)
  rw [split_principal_periodic_bulk W c hc a B hB, add_sub_cancel_left,
    norm_smul, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  calc
    _ ≤ (2 / (Real.sqrt 3 * ‖eisEmbedding c‖^2))^2 *
        (q^2 * B * ∑' p : {p : (ℤ × ℤ) × (ℤ × ℤ) // p ≠ 0},
          ‖(𝓕 W) (jointFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p.val)‖) :=
      mul_le_mul_of_nonneg_left hb (sq_nonneg _)
    _ = _ := by
      rw [← mul_assoc, ← mul_assoc, principal_joint_inverse_covolume c hc]

def calculatePrincipalPhysicalBulk (W : 𝓢(Joint, ℂ))
    {c : ActualEisensteinCubic.O} (a : Residue c × Residue c → ℂ) (N : ℝ) : ℂ :=
  (4/3 : ℂ) * averageResidueCoefficient a * (N^2 : ℝ) * (𝓕 W) 0

theorem principal_physical_bulk_remainder_high_bound (A : ℕ) (hA : 2 < A) :
    ∃ (S : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(Joint, ℂ)) (c : ActualEisensteinCubic.O) (_hc : c ≠ 0)
        (a : Residue c × Residue c → ℂ) (B : ℝ), 0 ≤ B →
        (∀ v, ‖a v‖ ≤ B) → ∀ (N : ℝ), 0 < N →
        (Ideal.absNorm (Ideal.span {c}) : ℝ) ≤ N →
        ‖(∑' m : ActualEisensteinCubic.O × ActualEisensteinCubic.O,
          a (quotientPair c m) * W (ProbeGramLatticeDecay.physicalPoint N m)) -
          calculatePrincipalPhysicalBulk W a N‖ ≤
          C * ProbeGramLatticeDecay.sourceControl S W * B * N^2 *
            ((Ideal.absNorm (Ideal.span {c}) : ℝ) / N)^A := by
  obtain ⟨S, C, hC, hhigh⟩ := ProbeGramLatticeDecay.dual_fourier_lattice_bound A hA
  refine ⟨S, (4/3) * C, by positivity, ?_⟩
  intro W c hc a B hB0 hB N hN hscale
  let q : ℝ := Ideal.absNorm (Ideal.span {c})
  have hq : 0 < q := by
    dsimp only [q]
    rw [← eisEmbedding_norm_sq_eq_absNorm_span]
    exact sq_pos_of_pos (norm_pos_iff.mpr (eisEmbedding_ne_zero hc))
  have hL : 1 ≤ Real.sqrt (N/q) := by
    apply Real.le_sqrt_of_sq_le
    norm_num only [one_pow]
    exact (le_div_iff₀ hq).mpr (by simpa only [one_mul] using hscale)
  let u : ℂ := generatorRotation (eisEmbedding c)
  have hu : ‖u‖ = 1 := norm_generatorRotation _ (eisEmbedding_ne_zero hc)
  have ht4 : (Real.sqrt N)^4 = N^2 := by
    rw [show (4 : ℕ) = 2*2 by norm_num, pow_mul, Real.sq_sqrt hN.le]
  have hf (p : (ℤ × ℤ) × (ℤ × ℤ)) :
      ‖(𝓕 (scaledSource W (Real.sqrt N) (Real.sqrt_pos.mpr hN)))
        (jointFrequency (eisEmbedding c) (eisEmbedding_ne_zero hc) p)‖ =
      N^2 * ‖(𝓕 W) (ProbeGramLatticeDecay.scaledDualPoint (Real.sqrt (N/q)) u p)‖ := by
    rw [fourier_scaledSource, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (pow_nonneg (Real.sqrt_nonneg _) _), ht4,
      scaled_jointFrequency_eq _ _ N hN, eisEmbedding_norm_sq_eq_absNorm_span]
  have h := norm_principal_periodic_bulk_remainder_le
    (scaledSource W (Real.sqrt N) (Real.sqrt_pos.mpr hN)) c hc a B hB
  simp_rw [scaledSource_physicalPoint W N hN, hf, tsum_mul_left] at h
  rw [fourier_scaledSource, smul_zero, ht4] at h
  have hD := hhigh W (Real.sqrt (N/q)) hL u hu
  rw [sqrt_ratio_decay N q hN hq A] at hD
  have hbulk : (4/3 : ℂ) * averageResidueCoefficient a *
      (N^2 • (𝓕 W) 0) = calculatePrincipalPhysicalBulk W a N := by
    simp [calculatePrincipalPhysicalBulk, Algebra.smul_def, mul_assoc]
  rw [hbulk] at h
  calc
    _ ≤ (4/3 : ℝ) * B * (N^2 *
        ∑' p : {p : (ℤ × ℤ) × (ℤ × ℤ) // p ≠ 0},
          ‖(𝓕 W) (ProbeGramLatticeDecay.scaledDualPoint (Real.sqrt (N/q)) u p.val)‖) := h
    _ ≤ (4/3 : ℝ) * B * (N^2 *
        (C * ProbeGramLatticeDecay.sourceControl S W * (q/N)^A)) := by gcongr
    _ = _ := by ring

theorem principal_annular_bulk_remainder_bound (A : ℕ) (hA : 2 < A)
    (a₀ b₀ : ℝ) (ha₀ : 0 < a₀) (hab : a₀ < b₀) :
    ∃ (S : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(Joint, ℂ)), ProbeGramAnnularLattice.AnnularSupport a₀ b₀ W →
      ∀ (c : ActualEisensteinCubic.O), c ≠ 0 →
      ∀ (a : Residue c × Residue c → ℂ) (B : ℝ), 0 ≤ B →
        (∀ v, ‖a v‖ ≤ B) → ∀ (N : ℝ), 0 < N →
        ‖(∑' m : ActualEisensteinCubic.O × ActualEisensteinCubic.O,
          a (quotientPair c m) * W (ProbeGramLatticeDecay.physicalPoint N m)) -
          calculatePrincipalPhysicalBulk W a N‖ ≤
          C * ProbeGramLatticeDecay.sourceControl S W * B * N^2 *
            min 1 (((Ideal.absNorm (Ideal.span {c}) : ℝ) / N)^A) := by
  obtain ⟨Sl, Cl, hCl, hl⟩ :=
    ProbeGramAnnularLattice.annular_lattice_bound a₀ b₀ ha₀ hab
  obtain ⟨Sf, Cf, hCf, hf⟩ := ProbeGramLatticeDecay.fourier_seminorm_control 0
  obtain ⟨Sh, Ch, hCh, hh⟩ := principal_physical_bulk_remainder_high_bound A hA
  let S := (Sl ∪ Sf) ∪ Sh
  let C := Cl + (4/3) * Cf + Ch
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨S, C, hC, ?_⟩
  intro W hW c hc a B hB0 hB N hN
  have hSl : ProbeGramLatticeDecay.sourceControl Sl W ≤
      ProbeGramLatticeDecay.sourceControl S W :=
    ProbeGramLatticeDecay.sourceControl_mono
      (Finset.subset_union_left.trans Finset.subset_union_left) W
  have hSf : ProbeGramLatticeDecay.sourceControl Sf W ≤
      ProbeGramLatticeDecay.sourceControl S W :=
    ProbeGramLatticeDecay.sourceControl_mono
      (Finset.subset_union_right.trans Finset.subset_union_left) W
  have hSh : ProbeGramLatticeDecay.sourceControl Sh W ≤
      ProbeGramLatticeDecay.sourceControl S W :=
    ProbeGramLatticeDecay.sourceControl_mono Finset.subset_union_right W
  have hSl0 := ProbeGramLatticeDecay.sourceControl_nonneg Sl W
  have hSf0 := ProbeGramLatticeDecay.sourceControl_nonneg Sf W
  have hSh0 := ProbeGramLatticeDecay.sourceControl_nonneg Sh W
  have hS0 := ProbeGramLatticeDecay.sourceControl_nonneg S W
  have hratio : 0 ≤ (Ideal.absNorm (Ideal.span {c}) : ℝ) / N := by positivity
  by_cases hscale : (Ideal.absNorm (Ideal.span {c}) : ℝ) ≤ N
  · have hp : ((Ideal.absNorm (Ideal.span {c}) : ℝ) / N)^A ≤ 1 :=
      pow_le_one₀ hratio ((div_le_one hN).mpr hscale)
    rw [min_eq_right hp]
    apply (hh W c hc a B hB0 hB N hN hscale).trans
    have hChC : Ch ≤ C := by dsimp [C]; linarith
    gcongr
  · have hp : 1 ≤ ((Ideal.absNorm (Ideal.span {c}) : ℝ) / N)^A :=
      one_le_pow₀ ((le_div_iff₀ hN).mpr (by linarith))
    rw [min_eq_left hp, mul_one]
    let : Finite (Residue c) := finite_quotient_span hc
    have havg := norm_average_residue_coefficient a B hB
    have hF0 : ‖(𝓕 W) 0‖ ≤ Cf * ProbeGramLatticeDecay.sourceControl Sf W :=
      (SchwartzMap.norm_le_seminorm ℝ (𝓕 W) 0).trans (hf W)
    have hbulk : ‖calculatePrincipalPhysicalBulk W a N‖ ≤
        (4/3 : ℝ) * B * N^2 * (Cf * ProbeGramLatticeDecay.sourceControl Sf W) := by
      unfold calculatePrincipalPhysicalBulk
      simp only [norm_mul, Complex.norm_ofNat, Complex.norm_div, Complex.norm_real,
        Real.norm_eq_abs, abs_of_nonneg (sq_nonneg N)]
      gcongr
    have hraw : ‖∑' m : ActualEisensteinCubic.O × ActualEisensteinCubic.O,
        a (quotientPair c m) * W (ProbeGramLatticeDecay.physicalPoint N m)‖ ≤
        B * (Cl * ProbeGramLatticeDecay.sourceControl Sl W * N^2) :=
      (norm_physical_weighted_le W N hN _ B (fun m => hB _)).trans
        (mul_le_mul_of_nonneg_left (hl W hW N hN) hB0)
    calc
      _ ≤ ‖∑' m : ActualEisensteinCubic.O × ActualEisensteinCubic.O,
          a (quotientPair c m) * W (ProbeGramLatticeDecay.physicalPoint N m)‖ +
          ‖calculatePrincipalPhysicalBulk W a N‖ := norm_sub_le _ _
      _ ≤ B * (Cl * ProbeGramLatticeDecay.sourceControl Sl W * N^2) +
          (4/3 : ℝ) * B * N^2 * (Cf * ProbeGramLatticeDecay.sourceControl Sf W) :=
        add_le_add hraw hbulk
      _ ≤ B * (Cl * ProbeGramLatticeDecay.sourceControl S W * N^2) +
          (4/3 : ℝ) * B * N^2 * (Cf * ProbeGramLatticeDecay.sourceControl S W) := by
        gcongr
      _ = (Cl + (4/3) * Cf) * ProbeGramLatticeDecay.sourceControl S W * B * N^2 := by ring
      _ ≤ C * ProbeGramLatticeDecay.sourceControl S W * B * N^2 := by
        have hlowC : Cl + (4/3) * Cf ≤ C := by dsimp [C]; linarith
        gcongr

theorem ideal_annular_bulk_remainder_bound (A : ℕ) (hA : 2 < A)
    (a₀ b₀ : ℝ) (ha₀ : 0 < a₀) (hab : a₀ < b₀) :
    ∃ (S : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(Joint, ℂ)), ProbeGramAnnularLattice.AnnularSupport a₀ b₀ W →
      ∀ (r : Ideal ActualEisensteinCubic.O), r ≠ 0 →
      ∀ (a : (ActualEisensteinCubic.O ⧸ r) × (ActualEisensteinCubic.O ⧸ r) → ℂ)
        (B : ℝ), 0 ≤ B → (∀ v, ‖a v‖ ≤ B) → ∀ (N : ℝ), 0 < N →
        ‖(∑' m : ActualEisensteinCubic.O × ActualEisensteinCubic.O,
          a (idealQuotientPair r m) * W (ProbeGramLatticeDecay.physicalPoint N m)) -
          (4/3 : ℂ) * averageResidueCoefficient a * (N^2 : ℝ) * (𝓕 W) 0‖ ≤
          C * ProbeGramLatticeDecay.sourceControl S W * B * N^2 *
            min 1 (((Ideal.absNorm r : ℝ) / N)^A) := by
  obtain ⟨S, C, hC, hbound⟩ := principal_annular_bulk_remainder_bound A hA a₀ b₀ ha₀ hab
  refine ⟨S, C, hC, ?_⟩
  intro W hW r hr a B hB0 hB N hN
  obtain ⟨c, hc, hspan⟩ : ∃ c : ActualEisensteinCubic.O,
      c ≠ 0 ∧ Ideal.span {c} = r :=
    ⟨ConcretePrimeRowBridge.idealGenerator r,
      ConcretePrimeRowBridge.idealGenerator_ne_zero r hr,
      ConcretePrimeRowBridge.span_idealGenerator r⟩
  subst r
  exact hbound W hW c hc a B hB0 hB N hN

theorem centered_ideal_annular_bound (A : ℕ) (hA : 2 < A)
    (a b : ℝ) (ha : 0 < a) (hab : a < b) :
    ∃ (S : Finset (ℕ × ℕ)) (C : ℝ), 0 < C ∧
      ∀ (W : 𝓢(ProbeGramPeriodicPoisson.Joint, ℂ)),
        ProbeGramAnnularLattice.AnnularSupport a b W →
      ∀ (r : Ideal ActualEisensteinCubic.O), r ≠ 0 →
      ∀ (d : (ActualEisensteinCubic.O ⧸ r) × (ActualEisensteinCubic.O ⧸ r) → ℂ)
        (B : ℝ), 0 ≤ B → (∀ v, ‖d v‖ ≤ B) → ∀ (N : ℝ), 0 < N →
        Summable (fun m : ActualEisensteinCubic.O × ActualEisensteinCubic.O =>
          centerResidueCoefficient d (ProbeGramPeriodicPoisson.idealQuotientPair r m) *
            W (ProbeGramLatticeDecay.physicalPoint N m)) ∧
        ‖∑' m : ActualEisensteinCubic.O × ActualEisensteinCubic.O,
          centerResidueCoefficient d (ProbeGramPeriodicPoisson.idealQuotientPair r m) *
            W (ProbeGramLatticeDecay.physicalPoint N m)‖ ≤
          C * ProbeGramLatticeDecay.sourceControl S W * B * N^2 *
            min 1 (((Ideal.absNorm r : ℝ) / N)^A) := by
  obtain ⟨S, C, hC, hbound⟩ :=
    ProbeGramPeriodicPoisson.ideal_annular_periodic_bound A hA a b ha hab
  refine ⟨S, 2 * C, by positivity, ?_⟩
  intro W hW r hr d B hB hd N hN
  obtain ⟨c, hc, hspan⟩ : ∃ c : ActualEisensteinCubic.O,
      c ≠ 0 ∧ Ideal.span {c} = r :=
    ⟨ConcretePrimeRowBridge.idealGenerator r,
      ConcretePrimeRowBridge.idealGenerator_ne_zero r hr,
      ConcretePrimeRowBridge.span_idealGenerator r⟩
  have hfinite : Finite (ActualEisensteinCubic.O ⧸ r) := by
    rw [← hspan]
    exact ConcreteTraceCRT.finite_quotient_span hc
  let := hfinite
  have hresult := hbound W hW r hr (centerResidueCoefficient d) (2 * B)
    (by positivity) (norm_centered_residue_coefficient d B hd)
    (sum_centered_residue_coefficient d) N hN
  refine ⟨hresult.1, hresult.2.trans_eq ?_⟩
  ring

open SevenEighths.ProbeGramCommon ActualEisensteinCubic CanonicalQuadraticSieve
local notation "SupportedIdeal" => {I : Ideal ActualEisensteinCubic.O // Supported I}

theorem centered_exceptional_ideal_term_bound (ε Λ : ℝ) (hε : 0 < ε)
    (hεsmall : ε < 1 / 12) (hΛ : 0 < Λ) (A : ℕ) (hA : 1 ≤ A)
    (I J : SupportedIdeal) :
    gramIdealNorm I^(-7/6+ε : ℝ) * gramIdealNorm J^(-2 : ℝ) *
      min 1 ((gramIdealNorm I * gramIdealNorm J / Λ)^A) ≤
    Λ^(-1/6+2*ε : ℝ) *
      (gramIdealNorm I^(-1-ε : ℝ) * gramIdealNorm J^(-11/6-2*ε : ℝ)) := by
  have hi := gramIdealNorm_pos I
  have hj := gramIdealNorm_pos J
  have hAnat : (1 : ℝ) ≤ A := by exact_mod_cast hA
  have hθ : 0 ≤ (1/6-2*ε : ℝ) := by linarith
  have hθA : (1/6-2*ε : ℝ) ≤ A := by linarith
  have hmin := ideal_sum_min_power_bound (gramIdealNorm I * gramIdealNorm J / Λ)
    (by positivity) A (1/6-2*ε) hθ hθA
  apply (mul_le_mul_of_nonneg_left hmin (by positivity)).trans_eq
  rw [Real.div_rpow (by positivity) hΛ.le, Real.mul_rpow hi.le hj.le]
  rw [show (gramIdealNorm I^(1/6-2*ε : ℝ) * gramIdealNorm J^(1/6-2*ε : ℝ)) /
      Λ^(1/6-2*ε : ℝ) =
      (gramIdealNorm I^(1/6-2*ε : ℝ) * gramIdealNorm J^(1/6-2*ε : ℝ)) *
      (Λ^(1/6-2*ε : ℝ))⁻¹ by exact div_eq_mul_inv _ _]
  rw [← Real.rpow_neg hΛ.le]
  have hI : gramIdealNorm I^(-7/6+ε : ℝ) * gramIdealNorm I^(1/6-2*ε : ℝ) =
      gramIdealNorm I^(-1-ε : ℝ) := by
    rw [← Real.rpow_add hi]
    congr 1
    ring
  have hJ : gramIdealNorm J^(-2 : ℝ) * gramIdealNorm J^(1/6-2*ε : ℝ) =
      gramIdealNorm J^(-11/6-2*ε : ℝ) := by
    rw [← Real.rpow_add hj]
    congr 1
    ring
  rw [show -(1/6-2*ε : ℝ) = -1/6+2*ε by ring]
  calc
    _ = Λ^(-1/6+2*ε : ℝ) *
      ((gramIdealNorm I^(-7/6+ε : ℝ) * gramIdealNorm I^(1/6-2*ε : ℝ)) *
        (gramIdealNorm J^(-2 : ℝ) * gramIdealNorm J^(1/6-2*ε : ℝ))) := by ring
    _ = _ := by rw [hI, hJ]

theorem centered_exceptional_supported_double_sum (ε : ℝ) (hε : 0 < ε)
    (hεsmall : ε < 1 / 12) :
    ∃ K : ℝ, 0 < K ∧ ∀ (A : ℕ), 1 ≤ A → ∀ (Λ : ℝ), 0 < Λ →
      ∀ (F G : Finset SupportedIdeal),
      (∑ I ∈ F, ∑ J ∈ G,
        gramIdealNorm I^(-7/6+ε : ℝ) * gramIdealNorm J^(-2 : ℝ) *
          min 1 ((gramIdealNorm I * gramIdealNorm J / Λ)^A)) ≤
        K * Λ^(-1/6+2*ε : ℝ) := by
  obtain ⟨C, hC, hFbound⟩ :=
    supportedIdeal_rpow_finite_bound (-1-ε) (by linarith)
  obtain ⟨D, hD, hGbound⟩ :=
    supportedIdeal_rpow_finite_bound (-11/6-2*ε) (by linarith)
  refine ⟨C * D, by positivity, ?_⟩
  intro A hA Λ hΛ F G
  have hGn : 0 ≤ ∑ J ∈ G, gramIdealNorm J^(-11/6-2*ε : ℝ) :=
    Finset.sum_nonneg (fun J _ => Real.rpow_nonneg (gramIdealNorm_pos J).le _)
  calc
    _ ≤ ∑ I ∈ F, ∑ J ∈ G, Λ^(-1/6+2*ε : ℝ) *
        (gramIdealNorm I^(-1-ε : ℝ) * gramIdealNorm J^(-11/6-2*ε : ℝ)) :=
      Finset.sum_le_sum (fun I _ => Finset.sum_le_sum
        (fun J _ => centered_exceptional_ideal_term_bound ε Λ hε hεsmall hΛ A hA I J))
    _ = Λ^(-1/6+2*ε : ℝ) *
        ((∑ I ∈ F, gramIdealNorm I^(-1-ε : ℝ)) *
          (∑ J ∈ G, gramIdealNorm J^(-11/6-2*ε : ℝ))) := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
    _ ≤ Λ^(-1/6+2*ε : ℝ) * (C * D) :=
      mul_le_mul_of_nonneg_left (mul_le_mul (hFbound F) (hGbound G) hGn hC.le)
        (by positivity)
    _ = _ := by ring

theorem bound_finite_exceptional_blocks (ε : ℝ) (hε : 0 < ε)
    (hεsmall : ε < 1 / 12) :
    ∃ K : ℝ, 0 < K ∧ ∀ (A : ℕ), 1 ≤ A → ∀ (Λ H : ℝ), 0 < Λ → 0 ≤ H →
      ∀ (F G : Finset SupportedIdeal) (block : SupportedIdeal → SupportedIdeal → ℂ),
      (∀ I ∈ F, ∀ J ∈ G, ‖block I J‖ ≤
        H * (gramIdealNorm I^(-7/6+ε : ℝ) * gramIdealNorm J^(-2 : ℝ) *
          min 1 ((gramIdealNorm I * gramIdealNorm J / Λ)^A))) →
      ‖∑ I ∈ F, ∑ J ∈ G, block I J‖ ≤ H * K * Λ^(-1/6+2*ε : ℝ) := by
  obtain ⟨K, hK, hsum⟩ := centered_exceptional_supported_double_sum ε hε hεsmall
  refine ⟨K, hK, ?_⟩
  intro A hA Λ H hΛ hH F G block hblock
  calc
    _ ≤ ∑ I ∈ F, ‖∑ J ∈ G, block I J‖ := norm_sum_le _ _
    _ ≤ ∑ I ∈ F, ∑ J ∈ G, ‖block I J‖ :=
      Finset.sum_le_sum (fun I _ => norm_sum_le _ _)
    _ ≤ ∑ I ∈ F, ∑ J ∈ G,
        H * (gramIdealNorm I^(-7/6+ε : ℝ) * gramIdealNorm J^(-2 : ℝ) *
          min 1 ((gramIdealNorm I * gramIdealNorm J / Λ)^A)) :=
      Finset.sum_le_sum (fun I hI => Finset.sum_le_sum (fun J hJ => hblock I hI J hJ))
    _ = H * (∑ I ∈ F, ∑ J ∈ G,
        gramIdealNorm I^(-7/6+ε : ℝ) * gramIdealNorm J^(-2 : ℝ) *
          min 1 ((gramIdealNorm I * gramIdealNorm J / Λ)^A)) := by
      simp only [Finset.mul_sum]
    _ ≤ H * (K * Λ^(-1/6+2*ε : ℝ)) :=
      mul_le_mul_of_nonneg_left (hsum A hA Λ hΛ F G) hH
    _ = _ := by ring

theorem remainder_gain_le_one (P Y : ℝ) (hP : 0 < P) (hY : 0 < Y)
    (hscale : P^2 ≤ Y) : P^(1/3 : ℝ) * Y^(-1/6 : ℝ) ≤ 1 := by
  have hpower : P^(1/3 : ℝ) = (P^2)^(1/6 : ℝ) := by
    rw [← Real.rpow_two, ← Real.rpow_mul hP.le]
    norm_num
  have hbound : P^(1/3 : ℝ) ≤ Y^(1/6 : ℝ) := by
    rw [hpower]
    exact Real.rpow_le_rpow (sq_nonneg _) hscale (by norm_num)
  calc
    _ ≤ Y^(1/6 : ℝ) * Y^(-1/6 : ℝ) :=
      mul_le_mul_of_nonneg_right hbound (Real.rpow_nonneg hY.le _)
    _ = 1 := by rw [← Real.rpow_add hY]; norm_num

end
end PerturbedZeroFreeBound.GramCenteredRemainder

#print axioms PerturbedZeroFreeBound.GramCenteredRemainder.split_principal_physical_bulk
#print axioms PerturbedZeroFreeBound.GramCenteredRemainder.ideal_annular_bulk_remainder_bound
#print axioms PerturbedZeroFreeBound.GramCenteredRemainder.centered_exceptional_supported_double_sum
#print axioms PerturbedZeroFreeBound.GramCenteredRemainder.bound_finite_exceptional_blocks
#print axioms PerturbedZeroFreeBound.GramCenteredRemainder.remainder_gain_le_one
