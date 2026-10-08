import OAIHighAssemblyMomentInput
import OAI.NumberTheory.DirichletL.Energy.CertifiedExistence

namespace OAI

noncomputable section
open scoped Classical BigOperators SchwartzMap ContDiff ComplexConjugate

namespace SevenEighths.ProbeFinalAssembly
open CenteredMomentEnergyCertifiedExistence
open CenteredMomentEnergyCappedWidthInduction CenteredMomentEnergyWidthSchedule

theorem perturbed_detector_certified_band
    {gap : ℝ} (D : Parameters.PerturbedHighData gap)
    (F : PerturbedSourceData D)
    (hβ : (7 / 8 - 21 / 500000 : ℝ) < HeckeZeroSupremum.beta)
    (hβhi : HeckeZeroSupremum.beta ≤ 7 / 8)
    (bΦ : ℝ) (hbΦ : 0 < bΦ) :
    CertifiedBand (α := Fin D.N) F.modulus ⊤ le_top
      (fun x => conj (F.W x)) 2 (1 / 4) (9 / 4) bΦ
      0 1 (33 / 50) (33 / 50) 2 (3 / 4) (D.small / 4)
      (count 2 (D.small / 4)) := by
  apply terminal_certificate (α := Fin D.N) F.modulus ⊤ le_top
    (fun x => conj (F.W x)) 1 2 (1 / 4) (9 / 4) bΦ
    0 1 (33 / 50) (33 / 50) 2 (3 / 4) (D.small / 4)
  · norm_num
  · intro x hx
    exact F.complex_support (by simpa using hx)
  · exact Complex.conjCLE.contDiff.comp (F.W.smooth ⊤)
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · exact hbΦ
  · norm_num
  · norm_num
  · norm_num
  · exact div_pos D.small_pos (by norm_num)
  · linarith
  · linarith [hβ]

end SevenEighths.ProbeFinalAssembly

end

end OAI
