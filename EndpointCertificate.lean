import Mathlib

namespace PerturbedZeroFreeBound

noncomputable section

def sourceV (y : ℝ) : ℝ := 51 + 41 * y
def sourceP (y : ℝ) : ℝ := (7 + 18 * y + 8 * y ^ 2) / 9
def sourceJ (delta y : ℝ) : ℝ :=
  (185 + 170 * y + (-138 + 12 * y + 96 * y ^ 2) * delta) / 108

def sourceNegativeExponent (delta y : ℝ) : ℝ :=
  (1 + (3 + 8 * y) * delta) / 48 -
    (13 / 32) * ((5 / 6 - delta) * delta * sourceP y / sourceJ delta y)

private def certificateRhs (delta y : ℝ) : ℝ :=
  (3 + 5 * y) * ((4 * sourceV y * delta - 79) ^ 2 + 49) +
    4 * y * (4 * sourceV y * delta *
      ((1 + 3 * y) * (15 + 32 * y) * delta + 9 - 13 * y) + 265 + 3485 * y)

private def certificateLhs (delta y : ℝ) : ℝ :=
  10368 * sourceV y *
    (sourceJ delta y * ((1 + (3 + 8 * y) * delta) / 48) -
      (13 / 32) * ((5 / 6 - delta) * delta * sourceP y))

theorem verify_endpoint_polynomial_identity (delta y : ℝ) :
    certificateLhs delta y = certificateRhs delta y := by
  unfold certificateLhs certificateRhs sourceV sourceJ sourceP
  ring

theorem bound_source_j (delta y : ℝ) (hdelta0 : 0 ≤ delta)
    (hdelta1 : delta ≤ 5 / 6) (hy0 : 0 ≤ y) (hy1 : y ≤ 1 / 2) :
    35 / 54 ≤ sourceJ delta y ∧ sourceJ delta y ≤ 5 / 2 := by
  have hy2 : y ^ 2 ≤ 1 / 4 := by
    nlinarith [mul_nonneg hy0 (sub_nonneg.mpr hy1)]
  have hpositive : 0 ≤ (12 * y + 96 * y ^ 2) * delta := by positivity
  have hnegative : (-138 + 12 * y + 96 * y ^ 2) * delta ≤ 0 := by
    have hcoefficient : -138 + 12 * y + 96 * y ^ 2 ≤ 0 := by nlinarith
    exact mul_nonpos_of_nonpos_of_nonneg hcoefficient hdelta0
  unfold sourceJ
  constructor <;> nlinarith

theorem bound_endpoint_certificate_rhs (delta y : ℝ)
    (hdelta : 0 ≤ delta) (hy0 : 0 ≤ y) (hy1 : y ≤ 1 / 2) :
    49 * (3 + 5 * y) ≤ certificateRhs delta y := by
  have hv : 0 ≤ sourceV y := by unfold sourceV; positivity
  have hinner : 0 ≤ (1 + 3 * y) * (15 + 32 * y) * delta + 9 - 13 * y := by
    have hbase : 0 ≤ (1 + 3 * y) * (15 + 32 * y) * delta := by positivity
    linarith
  have hterm : 0 ≤ 4 * sourceV y * delta *
      ((1 + 3 * y) * (15 + 32 * y) * delta + 9 - 13 * y) +
      265 + 3485 * y := by positivity
  have hsquare : 0 ≤ (4 * sourceV y * delta - 79) ^ 2 := sq_nonneg _
  unfold certificateRhs
  have hfirst : 0 ≤ (3 + 5 * y) *
      (4 * sourceV y * delta - 79) ^ 2 := by positivity
  have hsecond : 0 ≤ 4 * y *
      (4 * sourceV y * delta *
      ((1 + 3 * y) * (15 + 32 * y) * delta + 9 - 13 * y) +
      265 + 3485 * y) := by positivity
  nlinarith

theorem bound_source_endpoint (delta y : ℝ)
    (hdelta0 : 0 ≤ delta) (hdelta1 : delta ≤ 5 / 6)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1 / 2) :
    49 / 440640 ≤ sourceNegativeExponent delta y := by
  have hJ := bound_source_j delta y hdelta0 hdelta1 hy0 hy1
  have hJpos : 0 < sourceJ delta y := by linarith [hJ.1]
  have hvpos : 0 < sourceV y := by unfold sourceV; linarith
  have hvbound : sourceV y ≤ 17 * (3 + 5 * y) := by
    unfold sourceV
    linarith
  have hproduct : sourceV y * sourceJ delta y ≤
      17 * (3 + 5 * y) * (5 / 2) := by
    calc
      sourceV y * sourceJ delta y ≤
          (17 * (3 + 5 * y)) * sourceJ delta y := by gcongr
      _ ≤ 17 * (3 + 5 * y) * (5 / 2) := by
        exact mul_le_mul_of_nonneg_left hJ.2 (by positivity)
  have hscaled : 49 * (3 + 5 * y) ≤
      10368 * sourceV y * sourceJ delta y *
        sourceNegativeExponent delta y := by
    have hidentity := verify_endpoint_polynomial_identity delta y
    have hlower := bound_endpoint_certificate_rhs delta y hdelta0 hy0 hy1
    have hconnect : certificateLhs delta y =
        10368 * sourceV y * sourceJ delta y *
          sourceNegativeExponent delta y := by
      unfold certificateLhs sourceNegativeExponent
      field_simp
    linarith
  have hupper : 10368 * sourceV y * sourceJ delta y * (49 / 440640) ≤
      49 * (3 + 5 * y) := by
    nlinarith [hproduct]
  by_contra h
  have hstrict : sourceNegativeExponent delta y < 49 / 440640 := lt_of_not_ge h
  have hfactor : 0 < 10368 * sourceV y * sourceJ delta y := by positivity
  have hless := mul_lt_mul_of_pos_left hstrict hfactor
  nlinarith

def sourceRowExponent (delta y : ℝ) : ℝ :=
  1 - delta + (5 / 6 - delta) * delta * sourceP y / (2 * sourceJ delta y)

def sourceHighExponent (sigma ell ly h delta y : ℝ) : ℝ :=
  (1 + delta) / 2 - sigma + h * (17 / 50 - 1 / 6) -
    (1 + delta) / 2 * ly - ell / 2 + (1 / 2 - y) * delta * ell +
    h * (sourceRowExponent delta y + delta / 2 - 17 / 50)

theorem bound_source_row_exponent (delta y : ℝ)
    (hdelta0 : 0 ≤ delta) (hdelta1 : delta ≤ 3 / 4)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1 / 2) :
    sourceRowExponent delta y ≤ 1 := by
  have hJ := bound_source_j delta y hdelta0 (by linarith) hy0 hy1
  have hJpos : 0 < sourceJ delta y := by linarith [hJ.1]
  have hy2 : y ^ 2 ≤ 1 / 4 := by
    nlinarith [mul_nonneg hy0 (sub_nonneg.mpr hy1)]
  have hP : 0 ≤ sourceP y := by unfold sourceP; positivity
  have hhalfD : sourceP y ≤ 2 * (37 + 34 * y) / 18 := by
    unfold sourceP
    nlinarith
  have hJformula : sourceJ delta y =
      (5 / 6 - delta) * (37 + 34 * y) / 18 + delta * sourceP y := by
    unfold sourceJ sourceP
    ring
  have hfactor : 0 ≤ 5 / 6 - delta := by linarith
  have hcap : (5 / 6 - delta) * sourceP y ≤ 2 * sourceJ delta y := by
    rw [hJformula]
    nlinarith [mul_nonneg hfactor (sub_nonneg.mpr hhalfD),
      mul_nonneg hdelta0 hP]
  have hscaled : (5 / 6 - delta) * delta * sourceP y ≤
      2 * sourceJ delta y * delta := by
    nlinarith [mul_nonneg hdelta0 (sub_nonneg.mpr hcap)]
  have hratio : (5 / 6 - delta) * delta * sourceP y /
      (2 * sourceJ delta y) ≤ delta := by
    exact (div_le_iff₀ (by positivity : 0 < 2 * sourceJ delta y)).mpr
      (by nlinarith [hscaled])
  unfold sourceRowExponent
  linarith

theorem verify_source_high_exponent (delta y : ℝ)
    (hdelta0 : 0 ≤ delta) (hdelta1 : delta ≤ 5 / 6)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1 / 2) :
    sourceHighExponent (7 / 8) (1 / 6) (23 / 48) (13 / 16) delta y =
      -sourceNegativeExponent delta y := by
  have hJpos : 0 < sourceJ delta y := by
    have hJ := bound_source_j delta y hdelta0 hdelta1 hy0 hy1
    linarith [hJ.1]
  unfold sourceHighExponent sourceRowExponent sourceNegativeExponent
  field_simp
  ring

theorem bound_perturbed_high_endpoint (delta y : ℝ)
    (hdelta0 : 0 ≤ delta) (hdelta1 : delta ≤ 3 / 4)
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1 / 2) :
    sourceHighExponent (7 / 8 - 1 / 200000)
      (1 / 6 + 3 / 100000) (23 / 48 - 3 / 200000)
      (13 / 16 + 9 / 200000) delta y ≤ -(2611 / 110160000) := by
  have hsource : sourceHighExponent (7 / 8) (1 / 6) (23 / 48)
      (13 / 16) delta y ≤ -(49 / 440640) := by
    rw [verify_source_high_exponent delta y hdelta0 (by linarith) hy0 hy1]
    linarith [bound_source_endpoint delta y hdelta0 (by linarith) hy0 hy1]
  have hrow := bound_source_row_exponent delta y hdelta0 hdelta1 hy0 hy1
  have hq : (1 / 2 - y) * delta ≤ delta / 2 := by
    nlinarith [mul_nonneg hy0 hdelta0]
  have hderivative : -(1 / 2) + delta + (1 / 2 - y) * delta +
      3 * sourceRowExponent delta y / 2 ≤ 11 / 4 := by
    linarith
  have hperturb :
      sourceHighExponent (7 / 8 - 1 / 200000)
        (1 / 6 + 3 / 100000) (23 / 48 - 3 / 200000)
        (13 / 16 + 9 / 200000) delta y =
      sourceHighExponent (7 / 8) (1 / 6) (23 / 48) (13 / 16) delta y +
        1 / 200000 + 3 / 100000 *
        (-(1 / 2) + delta + (1 / 2 - y) * delta +
          3 * sourceRowExponent delta y / 2) := by
    unfold sourceHighExponent
    ring
  rw [hperturb]
  linarith

end

end PerturbedZeroFreeBound
