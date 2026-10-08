import OAI.NumberTheory.DirichletL.ParametersCentralBudget

namespace OAI

noncomputable section
namespace SevenEighths.Parameters

def perturbedSlotLengthShift : ℝ := 3 / 100000

theorem exists_perturbed_central_budget (gap : ℝ) (hgap : 0 < gap) :
    ∃ small : ℝ, 0 < small ∧ small < gap / 4 ∧
      small ≤ 1 / 100000000 ∧
      13 / 16 + 3 * perturbedSlotLengthShift / 2 + 3 * small ≤ 7 / 8 ∧
      ∀ N : ℕ, ∃ allowance : ℝ, 0 < allowance ∧
        allowance ≤ small / ((N : ℝ) + 2000) ∧
        ∀ ε e eps : ℝ,
          0 ≤ ε → ε ≤ allowance →
          0 ≤ e → e ≤ allowance →
          0 ≤ eps → eps ≤ allowance →
          159 * ε + small +
              (1 + 6 * perturbedSlotLengthShift) * small + 7 * small ≤ 1 / 32 ∧
          (13 / 16) * (159 * ε + small +
              (1 + 6 * perturbedSlotLengthShift) * small + 7 * small) +
            2 * small + (3 / 2) * (2 * small) +
            (26 * e + (N + 8) * eps + small + small / 6) +
            (small + small + small) + small +
            perturbedSlotLengthShift *
              (11 / 4 + 3 * (159 * ε + small +
                (1 + 6 * perturbedSlotLengthShift) * small + 7 * small) / 2 +
                3 * e + small) + 1 / 200000 ≤ 49 / 440640 := by
  let small := min (gap / 8) (1 / 100000000)
  have hsmall : 0 < small := lt_min (by positivity) (by norm_num)
  have hsmall_gap : small ≤ gap / 8 := min_le_left _ _
  have hsmall_cap : small ≤ 1 / 100000000 := min_le_right _ _
  refine ⟨small, hsmall, by linarith, hsmall_cap, ?_, ?_⟩
  · dsimp [perturbedSlotLengthShift]
    linarith
  intro N
  let allowance := small / ((N : ℝ) + 2000)
  have hden : 0 < (N : ℝ) + 2000 := by positivity
  have hallowance : 0 < allowance := div_pos hsmall hden
  have hallowance_cap : allowance ≤ small / 2000 :=
    div_le_div_of_nonneg_left hsmall.le (by norm_num)
      (by linarith [Nat.cast_nonneg (α := ℝ) N])
  have hallowance_product : allowance * ((N : ℝ) + 2000) = small := by
    dsimp [allowance]
    field_simp
  refine ⟨allowance, hallowance, le_refl _, ?_⟩
  intro ε e eps hε hεa he hea heps hepsa
  have hεsmall : 2000 * ε ≤ small := by linarith
  have hesmall : 2000 * e ≤ small := by linarith
  have hepsN : ((N : ℝ) + 2000) * eps ≤ small := by
    have h := mul_le_mul_of_nonneg_left hepsa hden.le
    nlinarith
  have heps8 : ((N : ℝ) + 8) * eps ≤ small := by
    nlinarith [Nat.cast_nonneg (α := ℝ) N]
  dsimp [perturbedSlotLengthShift]
  constructor <;> nlinarith

end SevenEighths.Parameters

end

end OAI
