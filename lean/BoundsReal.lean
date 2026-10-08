import EndpointCertificate

namespace PerturbedZeroFreeBound

noncomputable section

def skew : ℝ := 12457523527 / 15625000000000
def lengthChange : ℝ := 42930200831 / 250000000000000
def boundaryReduction : ℝ := 214651 / 5000000000
def boundary : ℝ := 7 / 8 - boundaryReduction
def highMargin : ℝ := 1 / 1250000000000
def ratioExponent : ℝ := 1 / 8 - 2 * skew
def lowBase : ℝ := 3 / 16 + skew / 3
def signalOffset : ℝ := -11 / 16 + skew / 3
def compensatedCap : ℝ := 11 / 48 + 3 * skew
def slotLength : ℝ := 1 / 6 + lengthChange
def xLength : ℝ := 17 / 48 + skew - lengthChange / 2
def yLength : ℝ := 23 / 48 - skew - lengthChange / 2
def rowLength : ℝ := 13 / 16 - skew + 3 * lengthChange / 2
def averagingLength : ℝ := xLength + yLength

theorem verify_geometry :
    xLength + yLength + slotLength = 1 ∧
    yLength - xLength = ratioExponent ∧
    rowLength = 1 - xLength + slotLength := by
  norm_num [xLength, yLength, slotLength, rowLength, lengthChange, skew, ratioExponent]

theorem verify_signal_exponent (sigma : ℝ) :
    xLength / 2 + sigma - 1 + rowLength / 6 = sigma + signalOffset := by
  norm_num [xLength, rowLength, lengthChange, skew, signalOffset]
  ring

theorem verify_low_margin :
    (boundary + signalOffset) - (xLength / 2 + ratioExponent / 12) =
      831 / 1000000000000000 := by
  norm_num [boundary, xLength, lengthChange, boundaryReduction, signalOffset, skew, ratioExponent]

theorem verify_low_scale_conditions (d : ℝ) (hd : d ≤ slotLength) :
    0 < xLength - d ∧
    0 < yLength - d ∧
    0 < averagingLength - 2 * d ∧
    0 < yLength - d - 11 * ratioExponent / 6 := by
  norm_num [slotLength, xLength, yLength, averagingLength, lengthChange, skew, ratioExponent] at *
  constructor
  · linarith
  constructor
  · linarith
  constructor
  · linarith
  · linarith

theorem bound_reflected_row_loss (d : ℝ) (hd : 0 ≤ d) :
    -d + max 0 ((d - 1 / 6 + 5 * lengthChange) / 8) ≤ 0 := by
  rcases le_total 0 ((d - 1 / 6 + 5 * lengthChange) / 8) with h | h
  · rw [max_eq_right h]
    norm_num [lengthChange] at *
    linarith
  · rw [max_eq_left h]
    linarith

private def highExponent (sigma ell ly h a delta q rowExponent : ℝ) : ℝ :=
  a - sigma + h * (17 / 50 - 1 / 6) - a * ly - ell / 2 + q * ell +
    h * (rowExponent + delta / 2 - 17 / 50)

theorem bound_high_derivative (delta q rowExponent : ℝ)
    (hdelta : delta ≤ 3 / 4) (hq : q ≤ delta / 2)
    (hrow : rowExponent ≤ 17 / 12) :
    -(1 / 2) + delta + q + 3 * rowExponent / 2 ≤ 11 / 4 := by
  linarith

theorem verify_high_perturbation (a delta q rowExponent : ℝ)
    (ha : 2 * a = 1 + delta) :
    highExponent boundary slotLength yLength rowLength a delta q rowExponent =
      highExponent (7 / 8) (1 / 6) (23 / 48) (13 / 16)
        a delta q rowExponent +
      boundaryReduction +
      lengthChange * (-(1 / 2) + delta + q + 3 * rowExponent / 2) +
      skew * (2 / 3 - rowExponent) := by
  rw [show a = (1 + delta) / 2 by linarith]
  unfold highExponent boundary slotLength yLength rowLength lengthChange boundaryReduction skew
  ring

theorem bound_high_endpoint (delta y : ℝ)
    (hdelta : 0 ≤ delta) (hdelta' : delta ≤ 3 / 4)
    (hy : 0 ≤ y) (hy' : y ≤ 1 / 2) :
    highExponent boundary slotLength yLength rowLength ((1 + delta) / 2)
      delta ((1 / 2 - y) * delta) (sourceRowExponent delta y) ≤
      -highMargin := by
  convert bound_perturbed_high_endpoint delta y hdelta hdelta' hy hy' using 1 <;>
    norm_num [highExponent, sourceHighExponent, boundary, slotLength, yLength,
    rowLength, lengthChange, boundaryReduction, skew, highMargin]

theorem verify_analytic_margins :
    -(363 / 200 : ℝ) + 6 * boundaryReduction < -1 ∧
    -(33 / 40 : ℝ) + 6 * boundaryReduction < 0 ∧
    boundary - 1 / 2 > 37 / 100 ∧
    slotLength / rowLength > 8 / 39 ∧
    5 * slotLength - rowLength > 1 / 48 := by
  norm_num [boundary, slotLength, rowLength, lengthChange, boundaryReduction, skew]

end

end PerturbedZeroFreeBound
