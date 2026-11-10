module

public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Sarkozy.PartV.UpperReference

/-!
# Section 25 certificates: the printed tables, checked in exact arithmetic

`paper/sections/25_upper_reference.tex`. The certificates `cert:record:direct-star`,
`cert:upper-root-caps`, `cert:upper-completed-root` and `cert:upper-band-inputs` rest on exact
rational Schur and `LDLᵀ` tests whose matrices are in the research records, not in the paper; those
tests are not reproduced here. What the paper does print is checked:

* **`cert:upper-root-caps`, the block inflation** (`rootCaps_P3`, `rootCaps_2_48`, …,
  `rootCaps_2_51`, `rootCaps_127_64`): for LL20 and LL22 at the six printed band starts
  `P₃ = 167·2⁴⁰`, `2⁴⁸`, `2⁴⁹`, `2⁵⁰`, `2⁵¹`, `(127/64)·2⁵¹`, the printed block cap `d`
  satisfies `d ≥ g exp(B_top L_band/(X log X))` with the printed `g`, `B_top` (an upper bound)
  and `L_band`, i.e. the caps are valid upper bounds of the formula of
  `lem:record:monotone-endpoint` (`inflation_le`, with `exp y ≤ 1 + y + y²/2 + (2/9)y³` for
  `0 ≤ y ≤ 1`, `log 2 > 0.6931471803`, `log(167/128) > 0.265963`, `log(128/127) ≤ 1/127`).
  **At `P₃` this holds only up to `10⁻⁶`** (`rootCaps_P3`): the printed `B_top` there is not
  precise enough to reproduce the printed caps to their last digit.
* **`cert:upper-completed-root`, the integer caps** (`completedRoot_ceil`): for the nine band
  starts `2⁵², …, 2⁶⁴` and both cuts, the printed integer is the least integer above
  `g + 1.2·10⁻⁵`, as claimed (`d < g + 1.2·10⁻⁵` and `⌈d⌉` recorded); the `2⁶⁴` entries `113`, `45`
  are the tail datum's `d_L` and `k_LL` (`completedRoot_tail`, against V1's `tailOrdinary`,
  `tailFieldCap`). `routeA_not_used`: the Route A caps `3458, 1123` (at `2⁵⁰`) and `723, 543`
  (at `2⁵¹`) exceed the Route B caps of `cert:upper-root-caps`, so they are rightly not used.
* **`prop:observed-caps` / `cert:upper-band-inputs`(b), the observed caps**
  (`observedCaps_P3`, `observedCaps_2_48`): `k_G = 2.26882`, `k_C = 0.079762` at `P₃`
  (`L_band = 559`) and `k_G = 2.245406`, `k_C = 0.056394` for every band from `2⁴⁸` on
  (`X ≥ 2⁴⁸`, `L_band ≤ 886`) bound `g exp(B_top L/(X log X))`.
-/

@[expose] public section

namespace Sarkozy.UpperReference.Cert

/-- `exp y ≤ 1 + y + y²/2 + (2/9) y³` for `0 ≤ y ≤ 1` (`Real.exp_bound` with three terms). -/
theorem exp_le_cubic {y : ℝ} (h0 : 0 ≤ y) (h1 : y ≤ 1) :
    Real.exp y ≤ 1 + y + y ^ 2 / 2 + 2 / 9 * y ^ 3 := by
  have h := Real.exp_bound (x := y) (by rw [abs_of_nonneg h0]; exact h1) (n := 3) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  rw [abs_le, abs_of_nonneg h0] at h
  norm_num at h
  linarith [h.2]

/-- **The block inflation bound** (`lem:record:monotone-endpoint`, `lem:majorant`(c)): if
`log X ≥ λ > 0` and `y₀ = B L/(X λ) ≤ 1`, then
`g exp(B L/(X log X)) ≤ g(1 + y₀ + y₀²/2 + (2/9) y₀³)`. -/
theorem inflation_le {g B L X lam d : ℝ} (hg : 0 ≤ g) (hB : 0 ≤ B) (hL : 0 ≤ L) (hX : 0 < X)
    (hlam : 0 < lam) (hlog : lam ≤ Real.log X) (hy1 : B * L / (X * lam) ≤ 1)
    (hd : g * (1 + B * L / (X * lam) + (B * L / (X * lam)) ^ 2 / 2 +
      2 / 9 * (B * L / (X * lam)) ^ 3) ≤ d) :
    g * Real.exp (B * L / (X * Real.log X)) ≤ d := by
  have hy : B * L / (X * Real.log X) ≤ B * L / (X * lam) :=
    div_le_div_of_nonneg_left (mul_nonneg hB hL) (mul_pos hX hlam)
      (mul_le_mul_of_nonneg_left hlog hX.le)
  have hy0 : 0 ≤ B * L / (X * lam) := div_nonneg (mul_nonneg hB hL) (mul_pos hX hlam).le
  calc g * Real.exp (B * L / (X * Real.log X)) ≤ g * Real.exp (B * L / (X * lam)) :=
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hy) hg
    _ ≤ g * (1 + B * L / (X * lam) + (B * L / (X * lam)) ^ 2 / 2 +
          2 / 9 * (B * L / (X * lam)) ^ 3) :=
        mul_le_mul_of_nonneg_left (exp_le_cubic hy0 hy1) hg
    _ ≤ d := hd

/-- `log 2^k ≥ k · 0.6931471803`. -/
theorem log_two_pow_ge (k : ℕ) : (k : ℝ) * 0.6931471803 ≤ Real.log (2 ^ k) := by
  rw [Real.log_pow]
  exact mul_le_mul_of_nonneg_left Real.log_two_gt_d9.le (Nat.cast_nonneg k)

/-- `log(167/128) > 0.265963` (`Real.exp_bound` with eight terms). -/
theorem log_167_div_128_gt : (265963 / 1000000 : ℝ) < Real.log (167 / 128) := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have h := Real.exp_bound (x := 265963 / 1000000) (by rw [abs_of_nonneg (by norm_num)]; norm_num)
    (n := 8) (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  rw [abs_le] at h
  norm_num at h
  linarith [h.2]

/-- `log P₃ = log(167·2⁴⁰) ≥ 0.265963 + 47 · 0.6931471803`. -/
theorem log_P3_ge : (265963 / 1000000 : ℝ) + 47 * 0.6931471803 ≤ Real.log (167 * 2 ^ 40) := by
  have e : (167 * 2 ^ 40 : ℝ) = 167 / 128 * 2 ^ 47 := by norm_num
  rw [e, Real.log_mul (by norm_num) (by norm_num)]
  have h1 := log_167_div_128_gt
  have h2 := log_two_pow_ge 47
  push_cast at h2
  linarith

/-! ## `cert:upper-root-caps`: the inflation of the Route B root caps -/

/-- **`cert:upper-root-caps`, the row `P₃`** (`L_band = 559`), **to within `10⁻⁶`**: the printed
upper bounds `B_top < 2.52265·10⁸` (LL20) and `< 1.10946·10⁸` (LL22), rounded to six digits,
give `g exp(B_top L_band/(X log X)) ≈ 12847.18793146` and `≈ 9381.13747854`, which exceed the
printed `d_L = 12847.187931` and `k_LL = 9381.137478` by `4.6·10⁻⁷` and `5.4·10⁻⁷`; the printed
caps correspond to `B_top ≈ 2.522646·10⁸` and `1.109454·10⁸` (below the printed bounds). So from
the printed data the caps are valid up to one unit in the last place: `d + 10⁻⁶` bounds the
formula. (A precision limit of the printed `B_top`, not an error.) -/
theorem rootCaps_P3 :
    (1284688753069 / 10 ^ 8 : ℝ) * Real.exp (252265 * 10 ^ 3 * 559 /
      ((167 * 2 ^ 40) * Real.log (167 * 2 ^ 40))) ≤ 12847187931 / 10 ^ 6 + 1 / 10 ^ 6 ∧
    (938104100550 / 10 ^ 8 : ℝ) * Real.exp (110946 * 10 ^ 3 * 559 /
      ((167 * 2 ^ 40) * Real.log (167 * 2 ^ 40))) ≤ 9381137478 / 10 ^ 6 + 1 / 10 ^ 6 := by
  constructor <;>
    exact inflation_le (lam := 265963 / 1000000 + 47 * 0.6931471803) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) log_P3_ge (by norm_num) (by norm_num)

/-- **`cert:upper-root-caps`, the row `2⁴⁸`** (`L_band = 566`). -/
theorem rootCaps_2_48 :
    (656889967376 / 10 ^ 8 : ℝ) * Real.exp (859331 * 10 ^ 2 * 566 /
      (2 ^ 48 * Real.log (2 ^ 48))) ≤ 6568933791 / 10 ^ 6 ∧
    (507200168224 / 10 ^ 8 : ℝ) * Real.exp (371450 * 10 ^ 2 * 566 /
      (2 ^ 48 * Real.log (2 ^ 48))) ≤ 5072013069 / 10 ^ 6 := by
  have hlog : (48 : ℝ) * 0.6931471803 ≤ Real.log (2 ^ 48) := by
    have := log_two_pow_ge 48
    push_cast at this
    exact this
  constructor <;>
    exact inflation_le (lam := 48 * 0.6931471803) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) hlog (by norm_num) (by norm_num)

/-- **`cert:upper-root-caps`, the row `2⁴⁹`** (`L_band = 578`). -/
theorem rootCaps_2_49 :
    (255655783215 / 10 ^ 8 : ℝ) * Real.exp (230412 * 10 ^ 2 * 578 /
      (2 ^ 49 * Real.log (2 ^ 49))) ≤ 2556559613 / 10 ^ 6 ∧
    (207082814422 / 10 ^ 8 : ℝ) * Real.exp (851920 * 10 * 578 /
      (2 ^ 49 * Real.log (2 ^ 49))) ≤ 2070828678 / 10 ^ 6 := by
  have hlog : (49 : ℝ) * 0.6931471803 ≤ Real.log (2 ^ 49) := by
    have := log_two_pow_ge 49
    push_cast at this
    exact this
  constructor <;>
    exact inflation_le (lam := 49 * 0.6931471803) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) hlog (by norm_num) (by norm_num)

/-- **`cert:upper-root-caps`, the row `2⁵⁰`** (`L_band = 555`). -/
theorem rootCaps_2_50 :
    (116555594825 / 10 ^ 8 : ℝ) * Real.exp (920408 * 10 * 555 /
      (2 ^ 50 * Real.log (2 ^ 50))) ≤ 1165556101 / 10 ^ 6 ∧
    (94250581374 / 10 ^ 8 : ℝ) * Real.exp (271889 * 10 * 555 /
      (2 ^ 50 * Real.log (2 ^ 50))) ≤ 942505851 / 10 ^ 6 := by
  have hlog : (50 : ℝ) * 0.6931471803 ≤ Real.log (2 ^ 50) := by
    have := log_two_pow_ge 50
    push_cast at this
    exact this
  constructor <;>
    exact inflation_le (lam := 50 * 0.6931471803) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) hlog (by norm_num) (by norm_num)

/-- **`cert:upper-root-caps`, the row `2⁵¹`** (`L_band = 566`). -/
theorem rootCaps_2_51 :
    (61294721642 / 10 ^ 8 : ℝ) * Real.exp (471877 * 10 * 566 /
      (2 ^ 51 * Real.log (2 ^ 51))) ≤ 612947237 / 10 ^ 6 ∧
    (47287513870 / 10 ^ 8 : ℝ) * Real.exp (113250 * 10 * 566 /
      (2 ^ 51 * Real.log (2 ^ 51))) ≤ 472875143 / 10 ^ 6 := by
  have hlog : (51 : ℝ) * 0.6931471803 ≤ Real.log (2 ^ 51) := by
    have := log_two_pow_ge 51
    push_cast at this
    exact this
  constructor <;>
    exact inflation_le (lam := 51 * 0.6931471803) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) hlog (by norm_num) (by norm_num)

/-- `log((127/64)·2⁵¹) = log(127·2⁴⁵) ≥ 52 · 0.6931471803 - 1/127` (`log(128/127) ≤ 1/127`). -/
theorem log_127_ge : (52 : ℝ) * 0.6931471803 - 1 / 127 ≤ Real.log (127 * 2 ^ 45) := by
  have e : (127 * 2 ^ 45 : ℝ) = (128 / 127)⁻¹ * 2 ^ 52 := by norm_num
  rw [e, Real.log_mul (by norm_num) (by norm_num), Real.log_inv]
  have h1 : Real.log (128 / 127) ≤ 128 / 127 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
  have h2 := log_two_pow_ge 52
  push_cast at h2
  linarith

/-- **`cert:upper-root-caps`, the row `(127/64)·2⁵¹`** (`L_band = 577`). -/
theorem rootCaps_127_64 :
    (37009363192 / 10 ^ 8 : ℝ) * Real.exp (281352 * 10 * 577 /
      ((127 * 2 ^ 45) * Real.log (127 * 2 ^ 45))) ≤ 370093636 / 10 ^ 6 ∧
    (26247992391 / 10 ^ 8 : ℝ) * Real.exp (579331 * 577 /
      ((127 * 2 ^ 45) * Real.log (127 * 2 ^ 45))) ≤ 262479925 / 10 ^ 6 := by
  constructor <;>
    exact inflation_le (lam := 52 * 0.6931471803 - 1 / 127) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) log_127_ge (by norm_num) (by norm_num)

/-! ## `cert:upper-completed-root`: the integer caps from `2⁵²` on -/

/-- The table of `cert:upper-completed-root`: `(g(LL20), ⌈d⌉, g(LL22), ⌈d⌉)` at
`X = 2⁵², …, 2⁵⁸, 2⁶⁰, 2⁶⁴`. -/
def completedRootTable : List (ℚ × ℚ × ℚ × ℚ) :=
  [(36642727119 / 10 ^ 8, 367, 26084850454 / 10 ^ 8, 261),
   (24923718696 / 10 ^ 8, 250, 15702296656 / 10 ^ 8, 158),
   (18671731661 / 10 ^ 8, 187, 10154007395 / 10 ^ 8, 102),
   (15747650343 / 10 ^ 8, 158, 7679680847 / 10 ^ 8, 77),
   (14027191683 / 10 ^ 8, 141, 6335956145 / 10 ^ 8, 64),
   (13028930487 / 10 ^ 8, 131, 5617027922 / 10 ^ 8, 57),
   (12391150306 / 10 ^ 8, 124, 5186566728 / 10 ^ 8, 52),
   (11704430410 / 10 ^ 8, 118, 4752728217 / 10 ^ 8, 48),
   (11238975257 / 10 ^ 8, 113, 4477917248 / 10 ^ 8, 45)]

/-- **`cert:upper-completed-root`, the integer caps**: in every row and for both cuts, the printed
integer `D` is the least integer above every `d ∈ [g, g + 1.2·10⁻⁵)`: `g + 12/10⁶ ≤ D` and
`D - 1 < g` (and `D` is an integer). -/
theorem completedRoot_ceil : ∀ x ∈ completedRootTable,
    x.1 + 12 / 10 ^ 6 ≤ x.2.1 ∧ x.2.1 - 1 < x.1 ∧ x.2.2.1 + 12 / 10 ^ 6 ≤ x.2.2.2 ∧
      x.2.2.2 - 1 < x.2.2.1 ∧ x.2.1 = ⌈x.2.1⌉ ∧ x.2.2.2 = ⌈x.2.2.2⌉ := by
  decide +kernel

/-- **The `2⁶⁴` row is the tail datum's root entries**: `⌈d(LL20)⌉ = 113 = d_L` and
`⌈d(LL22)⌉ = 45 = k_LL` of `def:record:upper-bands`(e) (V1's `tailOrdinary`, `tailFieldCap`). -/
theorem completedRoot_tail :
    (completedRootTable.getLast?.map fun x => (x.2.1, x.2.2.2)) =
      some ((PartV.tailOrdinary .L).d, PartV.tailFieldCap .L .L) := by
  decide +kernel

/-- **The Route A caps below `2⁵²` are not used**: `3458 > d_L(2⁵⁰) = 1165.556101`,
`1123 > k_LL(2⁵⁰) = 942.505851`, `723 > d_L(2⁵¹) = 612.947237` and
`543 > k_LL(2⁵¹) = 472.875143` (`cert:upper-completed-root` against `cert:upper-root-caps`). -/
theorem routeA_not_used :
    (1165556101 / 10 ^ 6 : ℚ) < 3458 ∧ (942505851 / 10 ^ 6 : ℚ) < 1123 ∧
      (612947237 / 10 ^ 6 : ℚ) < 723 ∧ (472875143 / 10 ^ 6 : ℚ) < 543 := by
  norm_num

/-! ## `prop:observed-caps`: the rounded block caps -/

/-- **The observed caps at `P₃`** (`p₀ = 2⁴⁷`, `L_band = 559`): `k_G = 2.26882` and
`k_C = 0.079762` bound `g exp(B_top L/(X log X))` with `g_G = 2.268819655`, `g_C = 0.079761731`,
`B_top < 39236.89926`. -/
theorem observedCaps_P3 :
    (2268819655 / 10 ^ 9 : ℝ) * Real.exp (3923689926 / 10 ^ 5 * 559 /
      ((167 * 2 ^ 40) * Real.log (167 * 2 ^ 40))) ≤ 226882 / 10 ^ 5 ∧
    (79761731 / 10 ^ 9 : ℝ) * Real.exp (3923689926 / 10 ^ 5 * 559 /
      ((167 * 2 ^ 40) * Real.log (167 * 2 ^ 40))) ≤ 79762 / 10 ^ 6 := by
  constructor <;>
    exact inflation_le (lam := 265963 / 1000000 + 47 * 0.6931471803) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) log_P3_ge (by norm_num) (by norm_num)

/-- **The observed caps from `2⁴⁸` on** (`p₀ = 2⁴⁸`): for every band start `X ≥ 2⁴⁸` and budget
`L ≤ 886`, `k_G = 2.245406` and `k_C = 0.056394` bound `g exp(B_top L/(X log X))` with
`g_G = 2.245405779`, `g_C = 0.056393528`, `B_top < 39227.259341`. -/
theorem observedCaps_2_48 {X L : ℝ} (hX : 2 ^ 48 ≤ X) (hL : L ≤ 886) :
    (2245405779 / 10 ^ 9 : ℝ) * Real.exp (39227259341 / 10 ^ 6 * L / (X * Real.log X)) ≤
      2245406 / 10 ^ 6 ∧
    (56393528 / 10 ^ 9 : ℝ) * Real.exp (39227259341 / 10 ^ 6 * L / (X * Real.log X)) ≤
      56394 / 10 ^ 6 := by
  have hX0 : (0 : ℝ) < 2 ^ 48 := by norm_num
  have hXpos : 0 < X := lt_of_lt_of_le hX0 hX
  have hlog48 : (48 : ℝ) * 0.6931471803 ≤ Real.log (2 ^ 48) := by
    have := log_two_pow_ge 48
    push_cast at this
    exact this
  have hlogX : (48 : ℝ) * 0.6931471803 ≤ Real.log X :=
    hlog48.trans (Real.log_le_log hX0 hX)
  -- the exponent is at most its value at `X = 2⁴⁸`, `L = 886`
  have hy : 39227259341 / 10 ^ 6 * L / (X * Real.log X) ≤
      39227259341 / 10 ^ 6 * 886 / (2 ^ 48 * (48 * 0.6931471803)) := by
    apply div_le_div₀ (by norm_num) (by nlinarith) (by norm_num)
    exact mul_le_mul hX hlogX (by norm_num) hXpos.le
  have hexp : Real.exp (39227259341 / 10 ^ 6 * L / (X * Real.log X)) ≤
      1 + 39227259341 / 10 ^ 6 * 886 / (2 ^ 48 * (48 * 0.6931471803)) +
        (39227259341 / 10 ^ 6 * 886 / (2 ^ 48 * (48 * 0.6931471803))) ^ 2 / 2 +
        2 / 9 * (39227259341 / 10 ^ 6 * 886 / (2 ^ 48 * (48 * 0.6931471803))) ^ 3 :=
    (Real.exp_le_exp.mpr hy).trans (exp_le_cubic (by norm_num) (by norm_num))
  constructor
  · calc (2245405779 / 10 ^ 9 : ℝ) * Real.exp (39227259341 / 10 ^ 6 * L / (X * Real.log X)) ≤
          (2245405779 / 10 ^ 9 : ℝ) * (1 + 39227259341 / 10 ^ 6 * 886 /
            (2 ^ 48 * (48 * 0.6931471803)) + (39227259341 / 10 ^ 6 * 886 /
              (2 ^ 48 * (48 * 0.6931471803))) ^ 2 / 2 + 2 / 9 * (39227259341 / 10 ^ 6 * 886 /
              (2 ^ 48 * (48 * 0.6931471803))) ^ 3) :=
          mul_le_mul_of_nonneg_left hexp (by norm_num)
      _ ≤ 2245406 / 10 ^ 6 := by norm_num
  · calc (56393528 / 10 ^ 9 : ℝ) * Real.exp (39227259341 / 10 ^ 6 * L / (X * Real.log X)) ≤
          (56393528 / 10 ^ 9 : ℝ) * (1 + 39227259341 / 10 ^ 6 * 886 /
            (2 ^ 48 * (48 * 0.6931471803)) + (39227259341 / 10 ^ 6 * 886 /
              (2 ^ 48 * (48 * 0.6931471803))) ^ 2 / 2 + 2 / 9 * (39227259341 / 10 ^ 6 * 886 /
              (2 ^ 48 * (48 * 0.6931471803))) ^ 3) :=
          mul_le_mul_of_nonneg_left hexp (by norm_num)
      _ ≤ 56394 / 10 ^ 6 := by norm_num

end Sarkozy.UpperReference.Cert
