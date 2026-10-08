import BoundsReal

namespace PerturbedZeroFreeBound

noncomputable section

def compensatedGramFactor (q X Y L delta : ℝ) : ℝ :=
  (q * (X / L) * (Y / L) / (Y / L)) *
    (1 + ((Y / L)^2 / (q * (X / L) * (Y / L)))^(1 / 6 : ℝ) +
      ((Y / L)^2 / (q * (X / L) * (Y / L)))^2 / (Y / L)) *
    (Y / L)^delta

private theorem bound_gram_factor (q X Y L delta : ℝ)
    (hq : 0 < q) (hX : 0 < X) (hY : 0 < Y)
    (hL : 1 ≤ L) (hdelta : 0 ≤ delta)
    (hprime : q * X ≤ Y) (htail : L * Y ≤ q^2 * X^2) :
    compensatedGramFactor q X Y L delta ≤
      3 * (q * X / L) * (Y / (q * X))^(1 / 6 : ℝ) * Y^delta := by
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hratio : 1 ≤ Y / (q * X) :=
    (le_div_iff₀ (mul_pos hq hX)).mpr (by simpa using hprime)
  have hroot : 1 ≤ (Y / (q * X))^(1 / 6 : ℝ) :=
    Real.one_le_rpow hratio (by norm_num)
  have htailRatio : (Y / (q * X))^2 / (Y / L) ≤ 1 := by
    have heq : (Y / (q * X))^2 / (Y / L) = L * Y / (q^2 * X^2) := by
      field_simp
    rw [heq]
    exact (div_le_one (by positivity)).mpr htail
  have hYpower : (Y / L)^delta ≤ Y^delta :=
    Real.rpow_le_rpow (by positivity) (div_le_self hY.le hL) hdelta
  have hratioEq : (Y / L)^2 / (q * (X / L) * (Y / L)) = Y / (q * X) := by
    field_simp
  have hfront : q * (X / L) * (Y / L) / (Y / L) = q * X / L := by
    field_simp
  unfold compensatedGramFactor
  rw [hratioEq, hfront]
  calc
    _ ≤ (q * X / L) * (3 * (Y / (q * X))^(1 / 6 : ℝ)) * Y^delta :=
      mul_le_mul
        (mul_le_mul_of_nonneg_left (by linarith) (by positivity))
        hYpower (by positivity) (by positivity)
    _ = _ := by ring

theorem verify_perturbed_gram_scale (q Z L delta : ℝ)
    (hq : 1 ≤ q) (hZ : 1 ≤ Z) (hL : 1 ≤ L)
    (hqCap : q ≤ Z^ratioExponent)
    (hLCap : L ≤ Z^(2 * xLength - yLength))
    (hdelta : 0 ≤ delta) :
    compensatedGramFactor q (Z^xLength) (Z^yLength) L delta ≤
      (3 * q / L) * Z^(2 * lowBase - lengthChange / 2 + yLength * delta) := by
  have hz : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hx : 0 < Z^xLength := Real.rpow_pos_of_pos hz _
  have hy : 0 < Z^yLength := Real.rpow_pos_of_pos hz _
  have hprime : q * Z^xLength ≤ Z^yLength := by
    calc
      q * Z^xLength ≤ Z^ratioExponent * Z^xLength :=
        mul_le_mul_of_nonneg_right hqCap (by positivity)
      _ = Z^yLength := by
        rw [←Real.rpow_add hz]
        congr 1
        dsimp only [xLength, yLength, ratioExponent]
        ring
  have htail : L * Z^yLength ≤ q^2 * (Z^xLength)^2 := by
    calc
      L * Z^yLength ≤ Z^(2 * xLength - yLength) * Z^yLength :=
        mul_le_mul_of_nonneg_right hLCap (by positivity)
      _ = (Z^xLength)^2 := by
        rw [←Real.rpow_add hz, ←Real.rpow_natCast, ←Real.rpow_mul hz.le]
        congr 1
        ring
      _ ≤ q^2 * (Z^xLength)^2 :=
        le_mul_of_one_le_left (by positivity) (one_le_pow₀ hq)
  apply (bound_gram_factor q (Z^xLength) (Z^yLength) L delta
    hqpos hx hy hL hdelta hprime htail).trans
  have hratio : Z^yLength / (q * Z^xLength) ≤ Z^ratioExponent := by
    have heq : Z^yLength / Z^xLength = Z^ratioExponent := by
      rw [←Real.rpow_sub hz]
      congr 1
      dsimp only [xLength, yLength, ratioExponent]
      ring
    rw [←heq]
    exact div_le_div_of_nonneg_left (by positivity) (by positivity)
      (le_mul_of_one_le_left (by positivity) hq)
  have hroot := Real.rpow_le_rpow (by positivity) hratio
    (show 0 ≤ (1 / 6 : ℝ) by norm_num)
  calc
    3 * (q * Z^xLength / L) *
        (Z^yLength / (q * Z^xLength))^(1 / 6 : ℝ) *
        (Z^yLength)^delta ≤
      3 * (q * Z^xLength / L) * (Z^ratioExponent)^(1 / 6 : ℝ) *
        (Z^yLength)^delta := by gcongr
    _ = (3 * q / L) * Z^(2 * lowBase - lengthChange / 2 + yLength * delta) := by
      have hexponent : xLength + ratioExponent * (1 / 6 : ℝ) + yLength * delta =
          2 * lowBase - lengthChange / 2 + yLength * delta := by
        dsimp only [xLength, ratioExponent, lowBase]
        ring
      rw [←Real.rpow_mul hz.le, ←Real.rpow_mul hz.le, ←hexponent]
      rw [Real.rpow_add hz, Real.rpow_add hz]
      ring

theorem verify_perturbed_gram_sqrt (q Z L delta : ℝ)
    (hq : 1 ≤ q) (hZ : 1 ≤ Z) (hL : 1 ≤ L)
    (hqCap : q ≤ Z^ratioExponent)
    (hLCap : L ≤ Z^(2 * xLength - yLength))
    (hdelta : 0 ≤ delta) :
    Real.sqrt (compensatedGramFactor q (Z^xLength) (Z^yLength) L delta) ≤
      Real.sqrt (3 * q / L) *
        Z^(lowBase - lengthChange / 4 + yLength * delta / 2) := by
  have hz : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  have hsqrtPower :
      Real.sqrt (Z^(2 * lowBase - lengthChange / 2 + yLength * delta)) =
        Z^(lowBase - lengthChange / 4 + yLength * delta / 2) := by
    rw [Real.sqrt_eq_rpow, ←Real.rpow_mul hz.le]
    congr 1
    ring
  apply (Real.sqrt_le_sqrt
    (verify_perturbed_gram_scale q Z L delta hq hZ hL hqCap hLCap hdelta)).trans_eq
  rw [Real.sqrt_mul (by positivity), hsqrtPower]

theorem eventually_perturbed_gram_cap (B : ℝ) :
    ∀ᶠ Z : ℝ in Filter.atTop, 1 ≤ Z ∧
      ∀ L : ℝ, L ≤ B * Z^slotLength → L ≤ Z^(2 * xLength - yLength) := by
  have hgap : 0 < 2 * xLength - yLength - slotLength := by
    norm_num [xLength, yLength, slotLength, lengthChange, skew]
  have hB := (tendsto_rpow_atTop hgap).eventually
    (Filter.eventually_ge_atTop B)
  filter_upwards [Filter.eventually_ge_atTop (1 : ℝ), hB] with Z hZ hB
  refine ⟨hZ, ?_⟩
  intro L hL
  have hz : 0 < Z := lt_of_lt_of_le zero_lt_one hZ
  calc
    L ≤ B * Z^slotLength := hL
    _ ≤ Z^(2 * xLength - yLength - slotLength) * Z^slotLength :=
      mul_le_mul_of_nonneg_right hB (by positivity)
    _ = Z^(2 * xLength - yLength) := by
      rw [←Real.rpow_add hz]
      congr 1
      ring

end

end PerturbedZeroFreeBound
