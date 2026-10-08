import OAIHighPrincipalRemainder
import OAI.NumberTheory.DirichletL.Detector.PrincipalPhysicalRemainder

namespace OAI

noncomputable section
open scoped Classical BigOperators
open Complex MeasureTheory
namespace SevenEighths.ProbePrincipalPhysical
open HeckeFamily ProbePhysical CompletedGauss ProbeFiniteProductBounds
open PrincipalMellinResidues PrincipalSignalComparison ProbeMellinBoundary ProbePrincipalContours
local notation "Id" => Ideal HeckeFamily.O

theorem physical_principal_residue_remainder_with_perturbed_lengths {K : ℕ}
    (η : Character) (S : Finset Id) (hS : SourceExclusions S)
    (c d B : ℝ) (hc : 0<c) (hd : c≤d) (hB : 0≤B)
    (W0 W1 : SchwartzMap ℝ ℂ) (a0 b0 a1 b1 : ℝ) (ha0 : 0<a0) (ha1 : 0<a1)
    (hW0 : Function.support W0⊆Set.Icc a0 b0) (hW1 : Function.support W1⊆Set.Icc a1 b1)
    (e lengthShift : ℝ) (he : 0<e) (hehi : e≤1/1000)
    (hβlo : (AsymmetricGeometry.boundary : ℝ) ≤ HeckeZeroSupremum.beta)
    (hβhi : HeckeZeroSupremum.beta ≤ 7/8)
    (ht : 0 ≤ lengthShift) (ht' : lengthShift ≤ 1/1000) :
    letI : NeZero (∏p∈S,p) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
    ∃C : ℝ,0<C ∧ ∀ell : Fin K→ℝ,(∑j,ell j)=1/6+lengthShift →
    ∀W : Fin K→ℝ→ℝ,
    (∀j x,0≤W j x ∧ W j x≤B) → (∀j,Function.support (W j)⊆Set.Icc c d) →
    ∀T : Fin K→Finset PrimeIdeal,(∀j p,p∈T j→p.val∉S) →
    (∀P:(∀j,T j),Function.Injective (fun j=>(P j).val)) →
    ∀Z : ℝ,1≤Z → (∀j,480≤c*Z^(ell j)) →
    (∀j,(Ideal.absNorm η.modulus:ℝ)<c*Z^(ell j)) →
    ‖(∑P:(∀j,T j),(∏j,(W j ((Ideal.absNorm (P j).val.val:ℝ)/Z^(ell j)):ℂ))*
        principalRowIntegral η S (fun j=>primaryGenerator (P j).val.val)
          W0 W1 (Z^(AsymmetricGeometry.xBase-lengthShift/2:ℝ))
          (Z^(AsymmetricGeometry.yBase-lengthShift/2:ℝ)) Z)-
      sourceResidueIntegral W0 W1 (∏p∈S,p) (η.excludePrimes S hS.prime)
        (7/8+e) (Z^(AsymmetricGeometry.xBase-lengthShift/2:ℝ))
        (Z^(AsymmetricGeometry.yBase-lengthShift/2:ℝ)) Z
        (globalClosedCorrection η S)
        (windowMultiplier η Finset.univ T (fun j x=>(W j x:ℂ))
          (fun j=>Z^(ell j)))‖≤
      C/e*Z^(HeckeZeroSupremum.beta+AsymmetricGeometry.signalOffset-1/4000) := by
  let : NeZero (∏p∈S,p) := ⟨fixedPrimeProduct_ne_zero S hS.prime⟩
  obtain ⟨C,hC,hbound⟩ :=
    ProbePrincipalRemainderBounds.source_remainders_fixed_contour_saving η S hS
      (Finset.univ : Finset (Fin K)) c d B hc hd hB W0 W1 a0 b0 a1 b1
      ha0 ha1 hW0 hW1 HeckeZeroSupremum.beta e lengthShift hβlo hβhi rfl
      he hehi ht ht'
  refine ⟨2*C,by positivity,?_⟩
  intro ell hell W hW hsupp T hT hdis Z hZ hthreshold hmod
  have hZ0 : 0<Z := by linarith
  have hb := hbound ell hell W (fun j _=>hW j) (fun j _=>hsupp j) T
    (fun j _ p hp=>hT j p hp) Z hZ (fun j _=>hthreshold j)
    (fun j _=>hmod j)
  dsimp only at hb
  have heq := principal_physical_pool_ordered η S hS T hT hdis
    (fun j p=>(W j ((Ideal.absNorm p.val:ℝ)/Z^(ell j)):ℂ))
    W0 W1 a0 b0 a1 b1 ha0 ha1 hW0 hW1
    (Z^(AsymmetricGeometry.xBase-lengthShift/2:ℝ)) (Z^(AsymmetricGeometry.yBase-lengthShift/2:ℝ)) Z
    (7/8+e) e
    (Real.rpow_pos_of_pos hZ0 _) (Real.rpow_pos_of_pos hZ0 _) hZ0
    (by linarith) (by linarith) (by linarith) he (by linarith)
  dsimp only at heq
  have hres (F : ℂ→ℂ) :
      (HeckeReciprocal.regularizedL (fixedSourcePrincipal S hS.prime) 1)^2/6*
        verticalIntegral (7/8+e) F=
      verticalIntegral (7/8+e) (fun s=>fixedPrincipalResidue (∏p∈S,p)^2/6*F s) := by
    rw [verticalIntegral,verticalIntegral,integral_const_mul]
    dsimp only [fixedPrincipalResidue,fixedPrincipal,fixedSourcePrincipal]
    ring
  rw [heq]
  unfold sourceResidueIntegral windowMultiplier
  rw [hres,add_sub_cancel_right]
  have hn := (norm_add_le _ _).trans (add_le_add hb.1 hb.2)
  change _≤(2*C)/e*Z^(HeckeZeroSupremum.beta+AsymmetricGeometry.signalOffset-1/4000)
  apply hn.trans
  have hCe : C≤C/e := (le_div_iff₀ he).mpr (by nlinarith)
  have hzpow : 0≤Z^(HeckeZeroSupremum.beta+AsymmetricGeometry.signalOffset-1/4000) :=
    Real.rpow_nonneg hZ0.le _
  have htwo : (2*C)/e=2*(C/e) := by ring
  rw [htwo]
  nlinarith

end SevenEighths.ProbePrincipalPhysical
end

end OAI
