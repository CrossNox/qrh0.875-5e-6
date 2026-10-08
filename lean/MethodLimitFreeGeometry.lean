import Mathlib
import OAI.NumberTheory.DirichletL.Detector.LowReflectedExponent

namespace OAI.SevenEighths.ProbeFreeGeometry

noncomputable section
open InverseTerminalWidths ProbeLowReflected

def evaluateFreeLowGain (totalShift slotShift : ℝ) : ℝ :=
  (totalShift + 2 * slotShift) / 12 - max 0 (slotShift - totalShift) / 2

def evaluateWitnessCentralCost (ε δ totalShift slotShift : ℝ) : ℝ :=
  ε + (1 + δ) / 2 * totalShift + δ * slotShift

theorem bound_source_row_mass_away_from_one_half (x y slotMass h : ℝ)
    (hphysical : h = 1 - x + slotMass) (horder : x ≤ y)
    (hfloor : h < 7 / 8) (hsupply : 8 / 39 * h < slotMass) :
    95 / 156 < x + y ∧ 1 / 2 < x + y := by
  have hx : 95 / 312 < x := by linarith
  constructor <;> linarith

theorem verify_reflected_empty_witness_nonnegative_dual (rowMass slotMass : ℝ)
    (hrow : 1 / 2 ≤ rowMass) (hslot : 0 ≤ slotMass) :
    0 ≤ 2 * rowMass + slotMass - 1 := by
  linarith

theorem bound_free_reflected_exponent_with_mass_penalty
    (rowMass slotMass d ell₀ O₀ H A₀ N₀ S₀ B₀ za v ell el θ ε : ℝ)
    (hd : 0 ≤ d) (hε : 0 ≤ ε)
    (hO : -ε ≤ O₀)
    (hH : H ≤ rowMass - 2 * d - O₀ + ε)
    (hA : 2 * A₀ ≤ O₀ + ε) (hN : 0 ≤ N₀) (hNA : N₀ ≤ A₀)
    (hS : 0 ≤ S₀) (hB : 0 ≤ B₀)
    (hslot : ell₀ ≤ slotMass - d + ε) (hz : za ≤ ell₀ + ε)
    (hv : -ε ≤ v) (hl : -ε ≤ ell) (he : -ε ≤ el)
    (hθ : |θ| ≤ ε)
    (hret : v + 3 * ell + el ≤
      2 * H + 2 * A₀ + 2 * za - 1 - ell₀ - θ - N₀ - 3 * B₀ + ε) :
    reflectedExponent O₀ H S₀ B₀ za v ell el
      (2 * H + 2 * A₀ + 2 * za - 1 - ell₀ - θ - N₀ - 3 * B₀) ≤
      rowMass - 2 * d + max 0 (rowMass + slotMass - 1) +
        max 0 ((d + 1 + 3 * slotMass - 2 * rowMass) / 4) +
        40 * ε := by
  let dualWidth := 2 * H + 2 * A₀ + 2 * za - 1 - ell₀ - θ - N₀ - 3 * B₀
  have hθLower : -ε ≤ θ := (abs_le.mp hθ).1
  have hθUpper : θ ≤ ε := (abs_le.mp hθ).2
  have hmassUpper : rowMass + slotMass - 1 ≤ max 0 (rowMass + slotMass - 1) :=
    le_max_right _ _
  have hmassNonneg : 0 ≤ max 0 (rowMass + slotMass - 1) := le_max_left _ _
  have hdualWidth : dualWidth ≤ H + max 0 (rowMass + slotMass - 1) - 3 * d + 6 * ε := by
    dsimp [dualWidth]
    linarith
  have hcolumn : v + ell ≤ H + max 0 (rowMass + slotMass - 1) + 10 * ε := by
    dsimp [dualWidth] at hdualWidth
    linarith
  have hmax : max H (v + ell) ≤ H + max 0 (rowMass + slotMass - 1) + 10 * ε :=
    max_le (by linarith) hcolumn
  have hpositivePart : 0 ≤ max 0 ((d + 1 + 3 * slotMass - 2 * rowMass) / 4) :=
    le_max_left _ _
  have hpositivePartUpper : (d + 1 + 3 * slotMass - 2 * rowMass) / 4 ≤
      max 0 ((d + 1 + 3 * slotMass - 2 * rowMass) / 4) := le_max_right _ _
  by_cases hmode : hybridSaving v za = za
  · unfold reflectedExponent
    rw [hmode]
    change O₀ / 2 + max H (v + ell) - S₀ - B₀ + za - za - ell -
      2 * el / 3 - max 0 (dualWidth - v - 3 * ell - el) / 2 ≤ _
    have hkernel : 0 ≤ max 0 (dualWidth - v - 3 * ell - el) := le_max_left _ _
    linarith
  · have hhalf := hybrid_half_with_error hv hε hmode
    have hquarter := retained_kernel_quarter dualWidth (v + 3 * ell + el)
    have hcharge : dualWidth / 4 - 17 * ε / 12 ≤
        hybridSaving v za + ell + 2 * el / 3 +
          max 0 (dualWidth - v - 3 * ell - el) / 2 := by
      have hidentity : dualWidth - (v + 3 * ell + el) =
          dualWidth - v - 3 * ell - el := by ring
      rw [hidentity] at hquarter
      linarith
    have hbound : reflectedExponent O₀ H S₀ B₀ za v ell el dualWidth ≤
        O₀ / 2 + H + max 0 (rowMass + slotMass - 1) - S₀ - B₀ + za - dualWidth / 4 +
          (10 + 17 / 12) * ε := by
      unfold reflectedExponent
      linarith
    change reflectedExponent O₀ H S₀ B₀ za v ell el dualWidth ≤ _
    apply hbound.trans
    dsimp [dualWidth]
    linarith

theorem bound_free_reflected_exponent_with_mass_cap
    (rowMass slotMass d ell₀ O₀ H A₀ N₀ S₀ B₀ za v ell el θ ε : ℝ)
    (hmass : rowMass + slotMass ≤ 1) (hd : 0 ≤ d) (hε : 0 ≤ ε)
    (hO : -ε ≤ O₀)
    (hH : H ≤ rowMass - 2 * d - O₀ + ε)
    (hA : 2 * A₀ ≤ O₀ + ε) (hN : 0 ≤ N₀) (hNA : N₀ ≤ A₀)
    (hS : 0 ≤ S₀) (hB : 0 ≤ B₀)
    (hslot : ell₀ ≤ slotMass - d + ε) (hz : za ≤ ell₀ + ε)
    (hv : -ε ≤ v) (hl : -ε ≤ ell) (he : -ε ≤ el)
    (hθ : |θ| ≤ ε)
    (hret : v + 3 * ell + el ≤
      2 * H + 2 * A₀ + 2 * za - 1 - ell₀ - θ - N₀ - 3 * B₀ + ε) :
    reflectedExponent O₀ H S₀ B₀ za v ell el
      (2 * H + 2 * A₀ + 2 * za - 1 - ell₀ - θ - N₀ - 3 * B₀) ≤
      rowMass - 2 * d + max 0 ((d + 1 + 3 * slotMass - 2 * rowMass) / 4) +
        40 * ε := by
  have hbound := bound_free_reflected_exponent_with_mass_penalty
    rowMass slotMass d ell₀ O₀ H A₀ N₀ S₀ B₀ za v ell el θ ε
    hd hε hO hH hA hN hNA hS hB hslot hz hv hl he hθ hret
  simpa only [max_eq_left (show rowMass + slotMass - 1 ≤ 0 by linarith), add_zero] using hbound

theorem verify_reflected_mass_excess_witness (rowMass slotMass : ℝ)
    (hslot : 0 ≤ slotMass) (hdual : slotMass ≤ 2 * rowMass - 1) :
    reflectedExponent 0 rowMass 0 0 slotMass (2 * rowMass + slotMass - 1) 0 0
      (2 * rowMass + slotMass - 1) =
      rowMass + max 0 (rowMass + slotMass - 1) := by
  have hhybrid : hybridSaving (2 * rowMass + slotMass - 1) slotMass = slotMass := by
    unfold hybridSaving
    rw [min_eq_left (show slotMass ≤ ((2 * rowMass + slotMass - 1) + slotMass) / 3 by
      linarith)]
    rw [min_eq_right (show slotMass ≤ 2 * rowMass + slotMass - 1 by linarith)]
  unfold reflectedExponent
  rw [hhybrid]
  simp only [zero_div, add_zero, sub_zero, mul_zero, sub_self, max_self]
  rcases le_total (rowMass + slotMass - 1) 0 with h | h
  · rw [max_eq_left (by linarith), max_eq_left h]
    ring
  · rw [max_eq_right (by linarith), max_eq_right h]
    ring

theorem bound_reflected_mass_excess_witness (rowMass slotMass : ℝ) :
    rowMass + max 0 (rowMass + slotMass - 1) ≤
      reflectedExponent 0 rowMass 0 0 slotMass (2 * rowMass + slotMass - 1) 0 0
        (2 * rowMass + slotMass - 1) := by
  have hhybrid : hybridSaving (2 * rowMass + slotMass - 1) slotMass ≤ slotMass := by
    unfold hybridSaving
    exact (min_le_right _ _).trans (min_le_left _ _)
  unfold reflectedExponent
  simp only [zero_div, add_zero, sub_zero, mul_zero, sub_self, max_self]
  rcases le_total (rowMass + slotMass - 1) 0 with h | h
  · have hrow : 2 * rowMass + slotMass - 1 ≤ rowMass := by linarith
    rw [max_eq_left h, max_eq_left hrow]
    linarith
  · have hrow : rowMass ≤ 2 * rowMass + slotMass - 1 := by linarith
    rw [max_eq_right h, max_eq_right hrow]
    linarith

theorem verify_reflected_mass_excess_witness_in_source_scale (rowMass slotMass : ℝ)
    (hslot : 0 ≤ slotMass) (hrow : 2 * slotMass ≤ rowMass)
    (hmass : 1 ≤ rowMass + slotMass) :
    0 ≤ 2 * rowMass + slotMass - 1 ∧
      reflectedExponent 0 rowMass 0 0 slotMass (2 * rowMass + slotMass - 1) 0 0
        (2 * rowMass + slotMass - 1) = 2 * rowMass + slotMass - 1 := by
  have hdual : slotMass ≤ 2 * rowMass - 1 := by linarith
  constructor
  · linarith
  · rw [verify_reflected_mass_excess_witness rowMass slotMass hslot hdual]
    rw [max_eq_right (show 0 ≤ rowMass + slotMass - 1 by linarith)]
    ring

theorem disprove_unpenalized_free_reflected_bound :
    1 + 3 * (17 / 100 : ℝ) - 2 * (21 / 25) ≤ 0 ∧
      reflectedExponent 0 (21 / 25) 0 0 (17 / 100) (17 / 20) 0 0 (17 / 20) >
        21 / 25 + max 0 ((1 + 3 * (17 / 100) - 2 * (21 / 25)) / 4) := by
  norm_num [reflectedExponent, hybridSaving]

theorem bound_free_central_cost_with_mass_deficit (ε δ totalShift slotShift : ℝ)
    (hδ : 0 ≤ δ) (hlow : ε ≤ (totalShift + 2 * slotShift) / 12) :
    ε * (3 + 6 * δ) + (totalShift - slotShift) / 3 ≤
      evaluateWitnessCentralCost ε δ totalShift slotShift := by
  have hslack := mul_nonneg
    (show 0 ≤ totalShift + 2 * slotShift - 12 * ε by linarith)
    (show 0 ≤ 1 + 3 * δ by linarith)
  unfold evaluateWitnessCentralCost
  nlinarith

theorem bound_free_central_cost_with_mass_excess (ε δ totalShift slotShift : ℝ)
    (hδ : 0 ≤ δ) (hlow : ε ≤ (7 * totalShift - 4 * slotShift) / 12) :
    ε * (3 + 6 * δ) + (slotShift - totalShift) * (2 / 3 + 3 * δ) ≤
      evaluateWitnessCentralCost ε δ totalShift slotShift := by
  have hslack := mul_nonneg
    (show 0 ≤ 7 * totalShift - 4 * slotShift - 12 * ε by linarith)
    (show 0 ≤ 1 + 3 * δ by linarith)
  unfold evaluateWitnessCentralCost
  nlinarith

theorem bound_free_central_cost_with_reflected_mass_penalty (ε δ totalShift slotShift : ℝ)
    (hδ : 0 ≤ δ) (hlow : ε ≤ evaluateFreeLowGain totalShift slotShift) :
    ε * (3 + 6 * δ) + max 0 (totalShift - slotShift) / 3 +
      max 0 (slotShift - totalShift) * (2 / 3 + 3 * δ) ≤
      evaluateWitnessCentralCost ε δ totalShift slotShift := by
  rcases le_total slotShift totalShift with hmass | hmass
  · have hlow' : ε ≤ (totalShift + 2 * slotShift) / 12 := by
      simpa [evaluateFreeLowGain, max_eq_left (show slotShift - totalShift ≤ 0 by linarith)]
        using hlow
    have hcost := bound_free_central_cost_with_mass_deficit ε δ totalShift slotShift hδ hlow'
    rw [max_eq_right (by linarith), max_eq_left (by linarith)]
    simpa using hcost
  · have hlow' : ε ≤ (7 * totalShift - 4 * slotShift) / 12 := by
      unfold evaluateFreeLowGain at hlow
      rw [max_eq_right (by linarith)] at hlow
      linarith
    have hcost := bound_free_central_cost_with_mass_excess ε δ totalShift slotShift hδ hlow'
    rw [max_eq_left (by linarith), max_eq_right (by linarith)]
    simpa using hcost

end

end OAI.SevenEighths.ProbeFreeGeometry
