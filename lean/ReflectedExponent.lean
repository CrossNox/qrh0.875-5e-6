import BoundsReal

namespace PerturbedZeroFreeBound

noncomputable section

private def totalSlotLength : ℝ := 1 / 6 + lengthChange
private def totalRowLength : ℝ := 5 / 6 - lengthChange
private def adjustedRowLength (d : ℝ) : ℝ := totalRowLength - 2 * d
private def remainingSlotLength (d : ℝ) : ℝ := totalSlotLength - d
private def reflectedLoss (d : ℝ) : ℝ :=
  max 0 ((d - 1 / 6 + 5 * lengthChange) / 4)

private def hybridSaving (v slotWeight : ℝ) : ℝ :=
  min v (min slotWeight ((v + slotWeight) / 3))

private def reflectedExponent
    (powerfulLength rowLength sourceLength gcdLength slotWeight
      dualLength cubeLength fourthLength FourierLength : ℝ) : ℝ :=
  powerfulLength / 2 + max rowLength (dualLength + cubeLength) -
    sourceLength - gcdLength + slotWeight - hybridSaving dualLength slotWeight -
    cubeLength - 2 * fourthLength / 3 -
    max 0 (FourierLength - dualLength - 3 * cubeLength - fourthLength) / 2

private theorem bound_hybrid_saving {dualLength slotWeight loss : ℝ}
    (hdual : -loss ≤ dualLength) (hloss : 0 ≤ loss)
    (hmode : hybridSaving dualLength slotWeight ≠ slotWeight) :
    dualLength / 2 - loss / 2 ≤ hybridSaving dualLength slotWeight := by
  unfold hybridSaving at *
  rcases le_total dualLength (min slotWeight ((dualLength + slotWeight) / 3)) with h | h
  · rw [min_eq_left h]
    linarith
  · rw [min_eq_right h] at *
    rcases le_total slotWeight ((dualLength + slotWeight) / 3) with hs | hs
    · exact (hmode (min_eq_left hs)).elim
    · rw [min_eq_right hs]
      have hslot := min_le_left slotWeight ((dualLength + slotWeight) / 3)
      rw [min_eq_right hs] at hslot
      linarith

private theorem bound_retained_kernel (FourierLength usedLength : ℝ) :
    FourierLength / 4 ≤
      usedLength / 4 + max 0 (FourierLength - usedLength) / 2 := by
  have hzero := le_max_left 0 (FourierLength - usedLength)
  have hpositive := le_max_right 0 (FourierLength - usedLength)
  linarith

theorem bound_perturbed_reflected_exponent
    (d powerfulLength rowLength additiveLength numeratorLength
      sourceLength gcdLength slotWeight dualLength cubeLength
      fourthLength phaseError error : ℝ)
    (hd : 0 ≤ d) (_hdmax : d ≤ totalSlotLength) (herror : 0 ≤ error)
    (hpowerful : -error ≤ powerfulLength)
    (hrow : rowLength ≤ adjustedRowLength d - powerfulLength + error)
    (hadditive : 2 * additiveLength ≤ powerfulLength + error)
    (hnumerator : 0 ≤ numeratorLength)
    (hnumeratorAdditive : numeratorLength ≤ additiveLength)
    (hsource : 0 ≤ sourceLength) (hgcd : 0 ≤ gcdLength)
    (hslot : slotWeight ≤ remainingSlotLength d)
    (hdual : -error ≤ dualLength)
    (hcube : -error ≤ cubeLength)
    (hfourth : -error ≤ fourthLength)
    (hphase : |phaseError| ≤ error)
    (hretained : dualLength + 3 * cubeLength + fourthLength ≤
      2 * rowLength + 2 * additiveLength + 2 * slotWeight - 1 -
        remainingSlotLength d - phaseError - numeratorLength -
        3 * gcdLength + error) :
    reflectedExponent powerfulLength rowLength sourceLength gcdLength
      slotWeight dualLength cubeLength fourthLength
      (2 * rowLength + 2 * additiveLength + 2 * slotWeight - 1 -
        remainingSlotLength d - phaseError - numeratorLength -
        3 * gcdLength) ≤
      adjustedRowLength d + reflectedLoss d + 20 * error := by
  let FourierLength := 2 * rowLength + 2 * additiveLength + 2 * slotWeight - 1 -
    remainingSlotLength d - phaseError - numeratorLength - 3 * gcdLength
  have hphaseLower : -error ≤ phaseError := (abs_le.mp hphase).1
  have hphaseUpper : phaseError ≤ error := (abs_le.mp hphase).2
  have hFourier : FourierLength ≤ rowLength - 3 * d + 3 * error := by
    dsimp [FourierLength, adjustedRowLength, remainingSlotLength,
      totalRowLength, totalSlotLength] at *
    linarith
  have hcolumn : dualLength + cubeLength ≤ rowLength + 7 * error := by
    dsimp [FourierLength] at hFourier
    linarith
  have hmax : max rowLength (dualLength + cubeLength) ≤
      rowLength + 7 * error := max_le (by linarith) hcolumn
  have hkernel := le_max_left 0
    (FourierLength - dualLength - 3 * cubeLength - fourthLength)
  have hlossNonnegative : 0 ≤ reflectedLoss d := by
    unfold reflectedLoss
    exact le_max_left _ _
  by_cases hmode : hybridSaving dualLength slotWeight = slotWeight
  · unfold reflectedExponent
    rw [hmode]
    change powerfulLength / 2 + max rowLength (dualLength + cubeLength) -
      sourceLength - gcdLength + slotWeight - slotWeight - cubeLength -
      2 * fourthLength / 3 -
      max 0 (FourierLength - dualLength - 3 * cubeLength - fourthLength) / 2 ≤ _
    linarith
  · have hhalf := bound_hybrid_saving hdual herror hmode
    have hquarter := bound_retained_kernel FourierLength
      (dualLength + 3 * cubeLength + fourthLength)
    have hcharge : FourierLength / 4 - 17 * error / 12 ≤
        hybridSaving dualLength slotWeight + cubeLength +
        2 * fourthLength / 3 +
        max 0 (FourierLength - dualLength - 3 * cubeLength - fourthLength) / 2 := by
      have heq : FourierLength -
          (dualLength + 3 * cubeLength + fourthLength) =
          FourierLength - dualLength - 3 * cubeLength - fourthLength := by ring
      rw [heq] at hquarter
      linarith
    have hbound : reflectedExponent powerfulLength rowLength sourceLength
        gcdLength slotWeight dualLength cubeLength fourthLength FourierLength ≤
        powerfulLength / 2 + rowLength - sourceLength - gcdLength +
          slotWeight - FourierLength / 4 + (7 + 17 / 12) * error := by
      unfold reflectedExponent
      linarith
    change reflectedExponent powerfulLength rowLength sourceLength
      gcdLength slotWeight dualLength cubeLength fourthLength FourierLength ≤ _
    apply hbound.trans
    have hlossUpper : (d - 1 / 6 + 5 * lengthChange) / 4 ≤
        reflectedLoss d := by
      unfold reflectedLoss
      exact le_max_right _ _
    have hrowExplicit : rowLength ≤
        (5 / 6 - lengthChange - 2 * d) - powerfulLength + error := by
      simpa [adjustedRowLength, totalRowLength] using hrow
    have hslotExplicit : slotWeight ≤ 1 / 6 + lengthChange - d := by
      simpa [remainingSlotLength, totalSlotLength] using hslot
    dsimp [FourierLength, adjustedRowLength, remainingSlotLength,
      totalRowLength, totalSlotLength]
    linarith

end

end PerturbedZeroFreeBound
