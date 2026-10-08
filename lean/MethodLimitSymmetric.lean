import Mathlib
import OAI.NumberTheory.DirichletL.Endpoint

namespace OAI.SevenEighths.Endpoint

noncomputable section

def evaluateSymmetricPerturbationSlope (δ y : ℝ) : ℝ :=
  -1 / 2 + δ + δ * (1 / 2 - y) + 3 * balancedRowCount δ y / 2

def evaluateSymmetricLimitPolynomial (ε : ℝ) : ℝ :=
  49 - 1144080 * ε - 18604800 * ε ^ 2

def locateSymmetricWorstDelta (ε : ℝ) : ℝ :=
  (948 - 23040 * ε) / (2448 + 24192 * ε)

private def evaluateQuadraticCoefficient (ε y : ℝ) : ℝ :=
  1224 + 12096 * ε + (3144 + 4608 * ε) * y +
    (2256 + 16128 * ε) * y ^ 2 + (768 + 18432 * ε) * y ^ 3

private def evaluateLinearCoefficient (ε y : ℝ) : ℝ :=
  -948 + 23040 * ε + (-1508 + 6720 * ε) * y + (-104 - 1920 * ε) * y ^ 2

private def evaluateConstantCoefficient (ε y : ℝ) : ℝ :=
  185 - 44400 * ε + (170 - 40800 * ε) * y

private def evaluateClearedMargin (ε δ y : ℝ) : ℝ :=
  evaluateQuadraticCoefficient ε y * δ ^ 2 +
    evaluateLinearCoefficient ε y * δ + evaluateConstantCoefficient ε y

private def evaluateDiscriminant (ε y : ℝ) : ℝ :=
  144 * evaluateSymmetricLimitPolynomial ε +
    (299712 - 664266240 * ε - 3102105600 * ε ^ 2) * y +
    (1336112 - 877278720 * ε - 3573043200 * ε ^ 2) * y ^ 2 +
    (1788736 - 484362240 * ε - 5879808000 * ε ^ 2) * y ^ 3 +
    (511424 - 113203200 * ε - 3011788800 * ε ^ 2) * y ^ 4

theorem verify_symmetric_margin_identity (ε δ y : ℝ)
    (hJ : balanceDenominator δ y ≠ 0) :
    5184 * balanceDenominator δ y *
      (-balancedExponent δ y - ε * (1 + 4 * evaluateSymmetricPerturbationSlope δ y)) =
      evaluateClearedMargin ε δ y := by
  unfold balancedExponent evaluateSymmetricPerturbationSlope balancedRowCount
    balancedCutoff evaluateClearedMargin evaluateQuadraticCoefficient
    evaluateLinearCoefficient evaluateConstantCoefficient
  field_simp
  simp only [balanceDenominator, denominator, primeWeight]
  ring

theorem verify_symmetric_square_identity (ε δ y : ℝ) :
    4 * evaluateQuadraticCoefficient ε y * evaluateClearedMargin ε δ y =
      (2 * evaluateQuadraticCoefficient ε y * δ + evaluateLinearCoefficient ε y) ^ 2 +
        evaluateDiscriminant ε y := by
  unfold evaluateClearedMargin evaluateQuadraticCoefficient evaluateLinearCoefficient
    evaluateConstantCoefficient evaluateDiscriminant
    evaluateSymmetricLimitPolynomial
  ring

theorem bound_symmetric_discriminant (ε y : ℝ)
    (hε : 0 ≤ ε) (hε' : ε ≤ 1 / 20000) (hy : 0 ≤ y)
    (hroot : 0 ≤ evaluateSymmetricLimitPolynomial ε) :
    260000 * y ≤ evaluateDiscriminant ε y := by
  have hεsq : ε ^ 2 ≤ (1 / 20000 : ℝ) ^ 2 := by
    nlinarith [mul_nonneg hε (sub_nonneg.mpr hε')]
  have h1 : 0 ≤ 299712 - 664266240 * ε - 3102105600 * ε ^ 2 - 260000 := by
    nlinarith
  have h2 : 0 ≤ 1336112 - 877278720 * ε - 3573043200 * ε ^ 2 := by
    nlinarith
  have h3 : 0 ≤ 1788736 - 484362240 * ε - 5879808000 * ε ^ 2 := by
    nlinarith
  have h4 : 0 ≤ 511424 - 113203200 * ε - 3011788800 * ε ^ 2 := by
    nlinarith
  have hrest : 0 ≤ 144 * evaluateSymmetricLimitPolynomial ε +
      (299712 - 664266240 * ε - 3102105600 * ε ^ 2 - 260000) * y +
      (1336112 - 877278720 * ε - 3573043200 * ε ^ 2) * y ^ 2 +
      (1788736 - 484362240 * ε - 5879808000 * ε ^ 2) * y ^ 3 +
      (511424 - 113203200 * ε - 3011788800 * ε ^ 2) * y ^ 4 := by
    positivity
  unfold evaluateDiscriminant
  nlinarith

theorem bound_symmetric_cleared_margin (ε δ y : ℝ)
    (hε : 0 ≤ ε) (hε' : ε ≤ 1 / 20000) (hy : 0 ≤ y)
    (hroot : 0 ≤ evaluateSymmetricLimitPolynomial ε) :
    0 ≤ evaluateClearedMargin ε δ y := by
  have hcoefficient : 0 < evaluateQuadraticCoefficient ε y := by
    unfold evaluateQuadraticCoefficient
    positivity
  have hdiscriminant := bound_symmetric_discriminant ε y hε hε' hy hroot
  have hidentity := verify_symmetric_square_identity ε δ y
  have hsquare := sq_nonneg
    (2 * evaluateQuadraticCoefficient ε y * δ + evaluateLinearCoefficient ε y)
  nlinarith

theorem bound_symmetric_perturbation_slope (δ y : ℝ)
    (hδ : 0 ≤ δ) (hδ' : δ ≤ 3 / 4) (hy : 0 ≤ y) (hy' : y ≤ 1 / 2) :
    5 / 8 ≤ evaluateSymmetricPerturbationSlope δ y ∧
      evaluateSymmetricPerturbationSlope δ y ≤ 11 / 4 := by
  have hJbounds := balanceDenominator_bounds hδ (by linarith) hy hy'
  have hJ : 0 < balanceDenominator δ y := by linarith [hJbounds.1]
  have hP : 0 ≤ primeWeight y := by unfold primeWeight; positivity
  have hfactor : 0 ≤ (5 / 6 : ℝ) - δ := by linarith
  have hbase : 0 ≤ (5 / 6 - δ) * denominator y := by
    unfold denominator
    positivity
  have hratio : 0 ≤ δ * primeWeight y / (2 * balanceDenominator δ y) := by
    positivity
  have hratio' : δ * primeWeight y / (2 * balanceDenominator δ y) ≤ 1 / 2 := by
    apply (div_le_iff₀ (by positivity)).mpr
    unfold balanceDenominator
    nlinarith
  have hcutoff : 1 ≤ balancedCutoff δ y ∧ balancedCutoff δ y ≤ 3 / 2 := by
    unfold balancedCutoff
    constructor <;> linarith
  have hrow : 1 - δ ≤ balancedRowCount δ y ∧ balancedRowCount δ y ≤ 17 / 12 := by
    have hlo := mul_le_mul_of_nonneg_left hcutoff.1 hfactor
    have hhi := mul_le_mul_of_nonneg_left hcutoff.2 hfactor
    unfold balancedRowCount
    constructor <;> nlinarith
  have hq : 0 ≤ δ * (1 / 2 - y) := mul_nonneg hδ (sub_nonneg.mpr hy')
  have hq' : δ * (1 / 2 - y) ≤ δ / 2 := by
    nlinarith [mul_nonneg hδ hy]
  unfold evaluateSymmetricPerturbationSlope
  constructor <;> linarith

theorem certify_symmetric_global_margin (ε δ y : ℝ)
    (hε : 0 ≤ ε) (hε' : ε ≤ 1 / 20000)
    (hroot : 0 ≤ evaluateSymmetricLimitPolynomial ε)
    (hδ : 0 ≤ δ) (hδ' : δ ≤ 3 / 4) (hy : 0 ≤ y) (hy' : y ≤ 1 / 2) :
    ε * (1 + 4 * evaluateSymmetricPerturbationSlope δ y) ≤ -balancedExponent δ y := by
  have hJbounds := balanceDenominator_bounds hδ (by linarith) hy hy'
  have hJ : 0 < balanceDenominator δ y := by linarith [hJbounds.1]
  have hidentity := verify_symmetric_margin_identity ε δ y hJ.ne'
  have hmargin := bound_symmetric_cleared_margin ε δ y hε hε' hy hroot
  have hfactor : 0 < 5184 * balanceDenominator δ y := by positivity
  nlinarith

theorem locate_symmetric_worst_bin (ε : ℝ)
    (hε : 0 ≤ ε) (hε' : ε ≤ 1 / 20000)
    (hroot : evaluateSymmetricLimitPolynomial ε = 0) :
    0 ≤ locateSymmetricWorstDelta ε ∧ locateSymmetricWorstDelta ε ≤ 3 / 4 ∧
      ε * (1 + 4 * evaluateSymmetricPerturbationSlope (locateSymmetricWorstDelta ε) 0) =
        -balancedExponent (locateSymmetricWorstDelta ε) 0 := by
  have hden : 0 < 2448 + 24192 * ε := by positivity
  have hδ : 0 ≤ locateSymmetricWorstDelta ε := by
    unfold locateSymmetricWorstDelta
    apply div_nonneg _ hden.le
    linarith
  have hδ' : locateSymmetricWorstDelta ε ≤ 3 / 4 := by
    unfold locateSymmetricWorstDelta
    apply (div_le_iff₀ hden).mpr
    linarith
  refine ⟨hδ, hδ', ?_⟩
  have hvertex :
      2 * evaluateQuadraticCoefficient ε 0 * locateSymmetricWorstDelta ε +
        evaluateLinearCoefficient ε 0 = 0 := by
    unfold evaluateQuadraticCoefficient evaluateLinearCoefficient locateSymmetricWorstDelta
    field_simp
    ring
  have hdiscriminant : evaluateDiscriminant ε 0 = 0 := by
    simp [evaluateDiscriminant, hroot]
  have hcoefficient : 0 < evaluateQuadraticCoefficient ε 0 := by
    unfold evaluateQuadraticCoefficient
    positivity
  have hsquare := verify_symmetric_square_identity ε (locateSymmetricWorstDelta ε) 0
  rw [hvertex, hdiscriminant] at hsquare
  have hmargin : evaluateClearedMargin ε (locateSymmetricWorstDelta ε) 0 = 0 := by
    nlinarith
  have hJbounds := balanceDenominator_bounds (y := (0 : ℝ))
    hδ (by linarith) (by norm_num) (by norm_num)
  have hJ : 0 < balanceDenominator (locateSymmetricWorstDelta ε) 0 := by
    linarith [hJbounds.1]
  have hidentity := verify_symmetric_margin_identity ε (locateSymmetricWorstDelta ε) 0 hJ.ne'
  rw [hmargin] at hidentity
  have hfactor : 0 < 5184 * balanceDenominator (locateSymmetricWorstDelta ε) 0 := by
    positivity
  nlinarith

theorem identify_symmetric_worst_bin (ε δ y : ℝ)
    (hε : 0 ≤ ε) (hε' : ε ≤ 1 / 20000)
    (hroot : evaluateSymmetricLimitPolynomial ε = 0)
    (hδ : 0 ≤ δ) (hδ' : δ ≤ 3 / 4) (hy : 0 ≤ y) (hy' : y ≤ 1 / 2)
    (hequality : ε * (1 + 4 * evaluateSymmetricPerturbationSlope δ y) =
      -balancedExponent δ y) :
    y = 0 ∧ δ = locateSymmetricWorstDelta ε := by
  have hJbounds := balanceDenominator_bounds hδ (by linarith) hy hy'
  have hJ : 0 < balanceDenominator δ y := by linarith [hJbounds.1]
  have hidentity := verify_symmetric_margin_identity ε δ y hJ.ne'
  have hzero : -balancedExponent δ y -
      ε * (1 + 4 * evaluateSymmetricPerturbationSlope δ y) = 0 := by linarith
  rw [hzero, mul_zero] at hidentity
  have hsquare := verify_symmetric_square_identity ε δ y
  rw [← hidentity, mul_zero] at hsquare
  have hdiscriminant := bound_symmetric_discriminant ε y hε hε' hy (by rw [hroot])
  have hsquare_nonneg := sq_nonneg
    (2 * evaluateQuadraticCoefficient ε y * δ + evaluateLinearCoefficient ε y)
  have hyzero : y = 0 := by nlinarith
  refine ⟨hyzero, ?_⟩
  rw [hyzero] at hsquare
  have hdiscriminant_zero : evaluateDiscriminant ε 0 = 0 := by
    simp [evaluateDiscriminant, hroot]
  rw [hdiscriminant_zero] at hsquare
  have hvertex : 2 * evaluateQuadraticCoefficient ε 0 * δ +
      evaluateLinearCoefficient ε 0 = 0 := by nlinarith
  unfold evaluateQuadraticCoefficient evaluateLinearCoefficient at hvertex
  have hden : 2448 + 24192 * ε ≠ 0 := ne_of_gt (by positivity)
  unfold locateSymmetricWorstDelta
  apply (eq_div_iff hden).mpr
  nlinarith

def symmetricGeometryIsFeasible (ε : ℝ) : Prop :=
  ∃ t : ℝ, 0 ≤ t ∧ ε < t / 4 ∧
    ∀ δ y : ℝ, 0 ≤ δ → δ ≤ 3 / 4 → 0 ≤ y → y ≤ 1 / 2 →
      balancedExponent δ y + ε + t * evaluateSymmetricPerturbationSlope δ y < 0

theorem characterize_symmetric_feasibility (limit ε : ℝ)
    (hlimit : 0 ≤ limit) (hlimit' : limit ≤ 1 / 20000)
    (hroot : evaluateSymmetricLimitPolynomial limit = 0) (hε : 0 ≤ ε) :
    symmetricGeometryIsFeasible ε ↔ ε < limit := by
  constructor
  · rintro ⟨t, ht, hlow, hhigh⟩
    by_contra hnot
    have hεlimit : limit ≤ ε := le_of_not_gt hnot
    obtain ⟨hδ, hδ', hequality⟩ := locate_symmetric_worst_bin limit hlimit hlimit' hroot
    have hslope := bound_symmetric_perturbation_slope
      (locateSymmetricWorstDelta limit) 0 hδ hδ' (by norm_num) (by norm_num)
    have hcost : 0 < (t - 4 * ε) *
        evaluateSymmetricPerturbationSlope (locateSymmetricWorstDelta limit) 0 := by
      apply mul_pos <;> linarith
    have hgap := mul_nonneg (sub_nonneg.mpr hεlimit)
      (show 0 ≤ 1 + 4 * evaluateSymmetricPerturbationSlope
        (locateSymmetricWorstDelta limit) 0 by linarith)
    have hbad := hhigh (locateSymmetricWorstDelta limit) 0 hδ hδ'
      (by norm_num) (by norm_num)
    nlinarith
  · intro hεlimit
    let t := 4 * ε + (limit - ε) / 4
    refine ⟨t, by dsimp [t]; linarith, by dsimp [t]; linarith, ?_⟩
    intro δ y hδ hδ' hy hy'
    have hmargin := certify_symmetric_global_margin limit δ y hlimit hlimit'
      (by rw [hroot]) hδ hδ' hy hy'
    have hslope := bound_symmetric_perturbation_slope δ y hδ hδ' hy hy'
    have hcost := mul_le_mul_of_nonneg_left hslope.2
      (show 0 ≤ (limit - ε) / 4 by linarith)
    have hgap := mul_nonneg (show 0 ≤ limit - ε by linarith)
      (show 0 ≤ evaluateSymmetricPerturbationSlope δ y by linarith)
    dsimp [t]
    nlinarith

theorem enclose_symmetric_limit_root :
    ∃ limit : ℝ,
      21399692313119 / 500000000000000000 ≤ limit ∧
      limit ≤ 42799384626239 / 1000000000000000000 ∧
      evaluateSymmetricLimitPolynomial limit = 0 := by
  have hbounds : (21399692313119 / 500000000000000000 : ℝ) ≤
      42799384626239 / 1000000000000000000 := by norm_num
  have hcontinuous : ContinuousOn evaluateSymmetricLimitPolynomial
      (Set.Icc (21399692313119 / 500000000000000000)
        (42799384626239 / 1000000000000000000)) := by
    unfold evaluateSymmetricLimitPolynomial
    fun_prop
  have hvalues : (0 : ℝ) ∈ Set.Icc
      (evaluateSymmetricLimitPolynomial (42799384626239 / 1000000000000000000))
      (evaluateSymmetricLimitPolynomial (21399692313119 / 500000000000000000)) := by
    norm_num [evaluateSymmetricLimitPolynomial, Set.mem_Icc]
  obtain ⟨limit, hinterval, hroot⟩ := intermediate_value_Icc' hbounds hcontinuous hvalues
  exact ⟨limit, hinterval.1, hinterval.2, hroot⟩

theorem certify_symmetric_least_upper_bound (limit : ℝ)
    (hlimit : 0 < limit) (hlimit' : limit ≤ 1 / 20000)
    (hroot : evaluateSymmetricLimitPolynomial limit = 0) :
    IsLUB {ε : ℝ | 0 ≤ ε ∧ symmetricGeometryIsFeasible ε} limit := by
  constructor
  · intro ε hε
    exact ((characterize_symmetric_feasibility limit ε hlimit.le hlimit'
      hroot hε.1).mp hε.2).le
  · intro bound hbound
    have hzero : symmetricGeometryIsFeasible 0 :=
      (characterize_symmetric_feasibility limit 0 hlimit.le hlimit'
        hroot (by norm_num)).mpr hlimit
    have hbound0 : 0 ≤ bound := hbound ⟨by norm_num, hzero⟩
    by_contra hnot
    have hbound' : bound < limit := lt_of_not_ge hnot
    have hmidpoint : 0 ≤ (bound + limit) / 2 := by positivity
    have hfeasible : symmetricGeometryIsFeasible ((bound + limit) / 2) :=
      (characterize_symmetric_feasibility limit ((bound + limit) / 2)
        hlimit.le hlimit' hroot hmidpoint).mpr (by linarith)
    have hupper : (bound + limit) / 2 ≤ bound := hbound ⟨hmidpoint, hfeasible⟩
    linarith

theorem certify_symmetric_method_limit :
    ∃ limit : ℝ,
      21399692313119 / 500000000000000000 ≤ limit ∧
      limit ≤ 42799384626239 / 1000000000000000000 ∧
      evaluateSymmetricLimitPolynomial limit = 0 ∧
      IsLUB {ε : ℝ | 0 ≤ ε ∧ symmetricGeometryIsFeasible ε} limit := by
  obtain ⟨limit, hlow, hhigh, hroot⟩ := enclose_symmetric_limit_root
  have hlimit : 0 < limit := by linarith
  have hlimit' : limit ≤ 1 / 20000 := by linarith
  exact ⟨limit, hlow, hhigh, hroot,
    certify_symmetric_least_upper_bound limit hlimit hlimit' hroot⟩

end

end OAI.SevenEighths.Endpoint
