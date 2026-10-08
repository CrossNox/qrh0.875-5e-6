import OAIHighUnconditional
import OAI.NumberTheory.DirichletL.Hecke.Nonvanishing

namespace OAI.SevenEighths

theorem HeckeFamily.LFunction_ne_zero_of_perturbed_boundary_lt_re
    (χ : HeckeFamily.Character) {s : ℂ} (hs : (174999 / 200000 : ℝ) < s.re)
    (hpole : ¬ (χ.residue = 1 ∧ s = 1)) : HeckeFamily.LFunction χ s ≠ 0 := by
  apply PerturbedZeroFree.prove_hecke_nonvanishing χ s hs
  by_cases hs_one : s = 1
  · exact Or.inr fun hresidue => hpole ⟨hresidue, hs_one⟩
  · exact Or.inl hs_one

theorem PerturbedZeroFree.riemannZeta_ne_zero_of_perturbed_boundary_lt_re
    {s : ℂ} (hs : (174999 / 200000 : ℝ) < s.re) : _root_.riemannZeta s ≠ 0 :=
  PerturbedZeroFree.prove_zeta_nonvanishing s hs

theorem PerturbedZeroFree.dirichletLFunction_ne_zero_of_perturbed_boundary_lt_re
    {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) {s : ℂ}
    (hs : (174999 / 200000 : ℝ) < s.re) (hpole : ¬ (χ = 1 ∧ s = 1)) :
    χ.LFunction s ≠ 0 :=
  PerturbedZeroFree.prove_dirichlet_nonvanishing q (NeZero.ne q) χ s hs hpole

end OAI.SevenEighths
