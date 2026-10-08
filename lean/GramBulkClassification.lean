import OAI.NumberTheory.DirichletL.Detector.GramCanonical
import OAI.NumberTheory.DirichletL.Detector.PrimePhase

namespace OAI

noncomputable section

open scoped Classical

namespace SevenEighths.ProbeGramCommon

open CanonicalQuadraticSieve CanonicalRowCompletion CompletedGauss
open ConcretePrimeRowBridge RayFourExpansion
open CenteredMomentCorrelation
open ConcreteTraceCRT CubicJacobiGlobal QuadraticAllOddCRT
open ActualEisensteinCubic ActualEisensteinCoordinates
open CanonicalUnitEuler
open CenteredMomentSupportedCorrelation

local notation "O" => ActualEisensteinCubic.O

theorem sum_pair_unit_pullback
    {R : Type*} [CommRing R] [Fintype R]
    (u : Rˣ) (f : R → R → ℂ) :
    (∑ x : R, ∑ y : R, f (u.val * x) (u.val * y)) =
      ∑ x : R, ∑ y : R, f x y := by
  let e : R × R ≃ R × R :=
    { toFun := fun p => (u.val * p.1, u.val * p.2)
      invFun := fun p => ((u⁻¹).val * p.1, (u⁻¹).val * p.2)
      left_inv := by
        intro p
        simp
      right_inv := by
        intro p
        simp }
  have h := e.sum_comp (fun p => f p.1 p.2)
  change (∑ p : R × R, f (u.val * p.1) (u.val * p.2)) =
    (∑ p : R × R, f p.1 p.2) at h
  simpa only [Fintype.sum_prod_type] using h

theorem sum_character_pair_of_order_six
    {F : Type*} [Field F] [Fintype F]
    (χ : MulChar F ℂ) (hχ : orderOf χ = 6) (n : ℕ) :
    (∑ u : F, ∑ v : F, (χ ^ n) u * star ((χ ^ n) v)) =
      if 6 ∣ n then ((Fintype.card F : ℂ) - 1) ^ 2 else 0 := by
  have hfactor :
      (∑ u : F, ∑ v : F, (χ ^ n) u * star ((χ ^ n) v)) =
        (∑ u : F, (χ ^ n) u) * star (∑ v : F, (χ ^ n) v) := by
    simp only [star_sum, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
  have hprincipal : χ ^ n = 1 ↔ 6 ∣ n := by
    rw [← orderOf_dvd_iff_pow_eq_one, hχ]
  rw [hfactor, character_sum]
  by_cases hn : 6 ∣ n
  · simp [hprincipal, hn, pow_two]
  · simp [hprincipal, hn]

theorem globalExtension_dilation_zero_of_common_prime
    {ι : Type*} [Fintype ι]
    (P : ι → Ideal O) [∀ i, (P i).IsMaximal]
    (hg : ∀ i, goodLambda ∉ P i) (c : ι → ℕ)
    (i : ι) (d n m k : O) (hd : d ∈ P i) :
    globalExtension P hg c (d * n) (d * m) k = 0 := by
  unfold globalExtension
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  exact localExtension_both_zero (P i) (hg i) (c i) (d * n) (d * m) k
    ((P i).mul_mem_right n hd) ((P i).mul_mem_right m hd)

theorem canonicalJoint_dilation_zero_of_common_prime
    (S : Finset (Ideal O)) (hS : ∀ p ∈ S, p.IsMaximal) (σ : RayRing)
    (C : SupportedIdeal) (k : GramFrequency) (p : GramPrime C)
    (d n m : O) (hd : d ∈ gramPrime C p) :
    canonicalJoint S hS σ C k (d * n) (d * m) = 0 := by
  unfold canonicalJoint jointExtension
  rw [globalExtension_dilation_zero_of_common_prime
    (gramPrime C) (gramPrime_good C) (gramExponent C) p d n m k.val hd]
  simp

theorem sexticReciprocityPhase_self_mul
    (a b : O) (ha : Supported (Ideal.span {a})) (hb : Supported (Ideal.span {b})) :
    sexticReciprocityPhase (a * b) (a * b) =
      sexticReciprocityPhase a a * sexticReciprocityPhase b b := by
  have hsym : sexticReciprocityPhase b a = sexticReciprocityPhase a b := by
    simp only [sexticReciprocityPhase, quadraticRaySign_symm]
  have hcross : sexticReciprocityPhase a b * sexticReciprocityPhase b a = 1 := by
    rw [hsym, ← pow_two]
    change (quadraticRaySign (residue a) (residue b) : ℂ) ^ 2 = 1
    exact_mod_cast quadraticRaySign_sq (residue a)
      (residue b) (supported_residue_odd a ha) (supported_residue_odd b hb)
  rw [sexticReciprocityPhase_mul_left, sexticReciprocityPhase_mul_right,
    sexticReciprocityPhase_mul_right]
  calc
    _ = (sexticReciprocityPhase a a * sexticReciprocityPhase b b) *
        (sexticReciprocityPhase a b * sexticReciprocityPhase b a) := by ring
    _ = _ := by rw [hcross, mul_one]

theorem sexticReciprocityPhase_self_eq_neg_one_row
    (n : O) (hn : Supported (Ideal.span {n})) (hprimary : goodLambda ^ 2 ∣ n - 1) :
    sexticReciprocityPhase n n = idealRowHom (-1) (Ideal.span {n}) := by
  obtain ⟨factors, hproduct, hprimes⟩ := exists_primary_prime_factorization n
    (supported_element_ne_zero n hn) hprimary
  rw [← hproduct] at hn ⊢
  clear hproduct n hprimary
  induction factors using Multiset.induction_on with
  | empty =>
      change sexticReciprocityPhase 1 1 = idealRowHom (-1) (Ideal.span {(1 : O)})
      rw [sexticReciprocityPhase_one_right 1 hn]
      rw [Ideal.span_singleton_one, ← Ideal.one_eq_top, map_one]
  | @cons p factors ih =>
      rw [Multiset.prod_cons] at hn ⊢
      rw [← Ideal.span_singleton_mul_span_singleton, supported_mul_iff] at hn
      have hp := hprimes p (Multiset.mem_cons_self _ _)
      have hrest : ∀ q ∈ factors, Prime q ∧ goodLambda ^ 2 ∣ q - 1 :=
        fun q hq => hprimes q (Multiset.mem_cons_of_mem hq)
      let : (Ideal.span {p} : Ideal O).IsMaximal :=
        PrincipalIdealRing.isMaximal_of_irreducible hp.1.irreducible
      obtain ⟨hgood, hchar⟩ := supported_prime_data p hp.1 hn.1
      have hphase : sexticReciprocityPhase p p = idealRowHom (-1) (Ideal.span {p}) := by
        rw [idealRowHom_prime (-1) (Ideal.span {p}) hgood]
        simpa only [ProbePhase.reciprocitySign, sexticReciprocityPhase, map_neg, map_one] using
          ProbePhase.reciprocitySign_self_eq_sextic_neg_one p hp.1.ne_zero hgood hchar
            (supported_residue_odd p hn.1)
      rw [sexticReciprocityPhase_self_mul p factors.prod hn.1 hn.2, hphase,
        ih hn.2 hrest, ← Ideal.span_singleton_mul_span_singleton, map_mul]

theorem jointFixed_eq_rank_one_on_common_ray
    (S : Finset (Ideal O)) (hS : ∀ p ∈ S, p.IsMaximal) (σ : RayRing)
    (C : O) (u : Oˣ) (a b : ℕ) (r : O) (hr : Supported (Ideal.span {r}))
    (n m : O) (hm : Supported (Ideal.span {m})) (hprimary : goodLambda ^ 2 ∣ m - 1)
    (hray : (4 : O) ∣ n - m) :
    jointFixed S hS σ C u a b r hr n m =
      (primaryCoefficient S hS σ (C * n) * numeratorBadTwist u a b r hr n) *
        star (primaryCoefficient S hS σ (C * m) * numeratorBadTwist u a b r hr m) := by
  have hresidue := QuadraticGaussRay.residue_eq_of_four_dvd_sub n m hray
  have hself := sexticReciprocityPhase_self_eq_neg_one_row m hm hprimary
  have hphase : sexticReciprocityPhase n m = idealRowHom (-1) (Ideal.span {m}) := by
    change (quadraticRaySign (residue n) (residue m) : ℂ) = _
    rw [hresidue]
    exact hself
  have hunit : unitSupplement (-u) m =
      idealRowHom (-1) (Ideal.span {m}) * unitSupplement u m := by
    change (if Supported (Ideal.span {m}) then idealRowHom (-u.val) (Ideal.span {m}) else 0) =
      idealRowHom (-1) (Ideal.span {m}) *
        (if Supported (Ideal.span {m}) then idealRowHom u.val (Ideal.span {m}) else 0)
    rw [ite_eq_left hm, ite_eq_left hm]
    rw [← idealRowHom_argument_mul]
    congr 1
    simp only [neg_one_mul]
  have hnegative : numeratorBadTwist (-u) a b r hr m =
      idealRowHom (-1) (Ideal.span {m}) * numeratorBadTwist u a b r hr m := by
    unfold numeratorBadTwist
    simp only [MonoidHom.mul_apply, hunit]
    ring
  have hcancel : idealRowHom (-1) (Ideal.span {m}) *
      star (idealRowHom (-1) (Ideal.span {m})) = 1 := by
    rw [← hself]
    have hstar : star (sexticReciprocityPhase m m) = sexticReciprocityPhase m m := by
      simp [sexticReciprocityPhase]
    rw [hstar, ← pow_two]
    change (quadraticRaySign (residue m) (residue m) : ℂ) ^ 2 = 1
    exact_mod_cast quadraticRaySign_sq (residue m) (residue m)
      (supported_residue_odd m hm) (supported_residue_odd m hm)
  unfold jointFixed
  rw [hnegative, star_mul, hphase]
  calc
    _ = ((primaryCoefficient S hS σ (C * n) * numeratorBadTwist u a b r hr n) *
        star (primaryCoefficient S hS σ (C * m) * numeratorBadTwist u a b r hr m)) *
          (idealRowHom (-1) (Ideal.span {m}) *
            star (idealRowHom (-1) (Ideal.span {m}))) := by
        simp only [star_mul]
        ring
    _ = _ := by rw [hcancel, mul_one]

#print axioms sum_pair_unit_pullback
#print axioms sum_character_pair_of_order_six
#print axioms globalExtension_dilation_zero_of_common_prime
#print axioms canonicalJoint_dilation_zero_of_common_prime
#print axioms sexticReciprocityPhase_self_mul
#print axioms sexticReciprocityPhase_self_eq_neg_one_row
#print axioms jointFixed_eq_rank_one_on_common_ray

end SevenEighths.ProbeGramCommon

end

end OAI
