module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-!
# The numerical step of the component bound, sharpened (C38)

`paper/sections/21_middle_records.tex`, `prop:signed-bounds`(c), Step 1 ("every centred component
`Π_⊥ T[P_{uv,p}] Π_⊥` has norm at most `c_+ r`").

SD2's separable Paley + Schur argument (`Sarkozy.SignedDecomp.comp_form`) bounds the form of a
repaired component on the `m₀`-centred functions by `X₁ + X₂` times the norms, with `s = √p`,
`e = e₀(p) ≤ 3/p`, `H = p(p - 1)(p - 2)/2 = |H_F|`, `T = (15s + 8)p²`, `Z ≥ H² - TH`:
`X₁ = (e²H + T)(H/(1 - e))/Z` (the `W/Z` part) and
`X₂ = 2 p/(p - 1)(s + 1)p²(1 + e)/H` (the `J_C` part).
SD2's `comp_numeric` shows `X₁ + X₂ ≤ 38/s` and states `80/s`.

Here **`CompNumeric δ`** is the statement `X₁ + X₂ ≤ δ(s)` for all `s ≥ 4096`, and:
* **`compNumeric_34`**: `X₁ + X₂ ≤ 34/s + 1000/s²`, i.e. `34 r + 1000 q`. The leading `34 = 30 + 4`
  is what the argument gives (`T/H ~ 30/s`, `X₂ ~ 4/s`); the remainder is `≈ 945 q`.
* **`compNumeric_35`**, **`compNumeric_38`**: `35/s`, `38/s` (from the above, `s ≥ 4096`).
-/

namespace Sarkozy.CompSharp

/-- **The numerical step at constant `δ(s)`**: for `s ≥ 4096`, `0 ≤ e ≤ 3/s²` and every
`Z ≥ H² - TH` (`H = s²(s² - 1)(s² - 2)/2`, `T = (15s + 8)s⁴`), `X₁ + X₂ ≤ δ(s)` (module
docstring). -/
def CompNumeric (δ : ℝ → ℝ) : Prop :=
  ∀ s e Z : ℝ, 4096 ≤ s → 0 ≤ e → e ≤ 3 / s ^ 2 →
    (s ^ 2 * (s ^ 2 - 1) * (s ^ 2 - 2) / 2) ^ 2 -
      (15 * s + 8) * (s ^ 2) ^ 2 * (s ^ 2 * (s ^ 2 - 1) * (s ^ 2 - 2) / 2) ≤ Z →
    (e ^ 2 * (s ^ 2 * (s ^ 2 - 1) * (s ^ 2 - 2) / 2) + (15 * s + 8) * (s ^ 2) ^ 2) *
        ((s ^ 2 * (s ^ 2 - 1) * (s ^ 2 - 2) / 2) / (1 - e)) / Z +
      2 * (s ^ 2 / (s ^ 2 - 1) * ((s + 1) * (s ^ 2) ^ 2)) * (1 + e) /
        (s ^ 2 * (s ^ 2 - 1) * (s ^ 2 - 2) / 2) ≤ δ s

theorem CompNumeric.mono {δ δ' : ℝ → ℝ} (h : CompNumeric δ) (hδ : ∀ s, 4096 ≤ s → δ s ≤ δ' s) :
    CompNumeric δ' := fun s e Z hs he0 he hZ => (h s e Z hs he0 he hZ).trans (hδ s hs)

/-- `(15s + 8)s⁴ ≤ (15s + 10)(s² - 1)(s² - 2)` for `s ≥ 4096` (so `T/H ≤ 30/s + 20/s²`). -/
theorem poly_T {s : ℝ} (hs : 4096 ≤ s) :
    (15 * s + 8) * s ^ 4 ≤ (15 * s + 10) * ((s ^ 2 - 1) * (s ^ 2 - 2)) := by
  have hs0 : 0 < s := by linarith
  have h0 : 45 * s + 30 ≤ 2 * s ^ 2 := by nlinarith
  have h1 : (45 * s + 30) * s ^ 2 ≤ 2 * s ^ 2 * s ^ 2 :=
    mul_le_mul_of_nonneg_right h0 (by positivity)
  have e1 : (15 * s + 10) * ((s ^ 2 - 1) * (s ^ 2 - 2)) - (15 * s + 8) * s ^ 4 =
      (2 * s ^ 2 * s ^ 2 - (45 * s + 30) * s ^ 2) + (30 * s + 20) := by ring
  have h2 : 0 ≤ 30 * s + 20 := by positivity
  linarith

/-- `4(s + 1)s⁴(s² + 3) ≤ (4s + 5)(s² - 1)²(s² - 2)` for `s ≥ 4096` (so `X₂ ≤ 4/s + 5/s²`). -/
theorem poly_X2 {s : ℝ} (hs : 4096 ≤ s) :
    4 * (s + 1) * s ^ 4 * (s ^ 2 + 3) ≤ (4 * s + 5) * ((s ^ 2 - 1) ^ 2 * (s ^ 2 - 2)) := by
  have hs0 : 0 < s := by linarith
  have h1 : 1 ≤ s ^ 2 - 28 * s - 32 := by nlinarith
  have h4 : 0 ≤ s ^ 4 := by positivity
  have h2 : s ^ 4 ≤ s ^ 4 * (s ^ 2 - 28 * s - 32) := le_mul_of_one_le_right h4 h1
  have h3 : 8 * s + 10 ≤ s ^ 4 := by
    have : 8 * s + 10 ≤ s * s := by nlinarith
    have hss : s * s ≤ s ^ 4 := by
      have : 1 ≤ s * s := by nlinarith
      calc s * s = s * s * 1 := by ring
        _ ≤ s * s * (s * s) := mul_le_mul_of_nonneg_left this (by positivity)
        _ = s ^ 4 := by ring
    linarith
  have h5 : 0 ≤ 20 * s ^ 3 + 25 * s ^ 2 := by positivity
  have e1 : (4 * s + 5) * ((s ^ 2 - 1) ^ 2 * (s ^ 2 - 2)) - 4 * (s + 1) * s ^ 4 * (s ^ 2 + 3) =
      s ^ 4 * (s ^ 2 - 28 * s - 32) + (20 * s ^ 3 + 25 * s ^ 2) - 8 * s - 10 := by ring
  linarith

/-- `(30s + 21)s² ≤ (30s + 940)(s² - 30s - 23)` for `s ≥ 4096`. -/
theorem poly_X1 {s : ℝ} (hs : 4096 ≤ s) :
    (30 * s + 21) * s ^ 2 ≤ (30 * s + 940) * (s ^ 2 - 30 * s - 23) := by
  have : 28890 * s + 21620 ≤ 19 * s ^ 2 := by nlinarith
  have e1 : (30 * s + 940) * (s ^ 2 - 30 * s - 23) - (30 * s + 21) * s ^ 2 =
      19 * s ^ 2 - (28890 * s + 21620) := by ring
  linarith

/-- **The `W/Z` term**: `X₁ ≤ (30s + 940)/s²` (`s ≥ 4096`, `0 ≤ e ≤ 3/s²`, `Z ≥ H² - TH`). -/
theorem x1_bound {s e Z H T : ℝ} (hs : 4096 ≤ s) (he0 : 0 ≤ e) (he : e ≤ 3 / s ^ 2)
    (hHdef : H = s ^ 2 * (s ^ 2 - 1) * (s ^ 2 - 2) / 2) (hTdef : T = (15 * s + 8) * (s ^ 2) ^ 2)
    (hZ : H ^ 2 - T * H ≤ Z) :
    (e ^ 2 * H + T) * (H / (1 - e)) / Z ≤ (30 * s + 940) / s ^ 2 := by
  have hs0 : 0 < s := by linarith
  have hS0 : 0 < s ^ 2 := by positivity
  have hs2 : 4096 ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ (by norm_num) hs 2
  have hp1 : 0 < s ^ 2 - 1 := by nlinarith
  have hp2 : 0 < s ^ 2 - 2 := by nlinarith
  have hH0 : 0 < H := by rw [hHdef]; positivity
  have hT0 : 0 ≤ T := by rw [hTdef]; positivity
  have hT : T * s ^ 2 ≤ (30 * s + 20) * H := by
    have e1 : T * s ^ 2 = s ^ 2 * ((15 * s + 8) * s ^ 4) := by rw [hTdef]; ring
    have e2 : (30 * s + 20) * H = s ^ 2 * ((15 * s + 10) * ((s ^ 2 - 1) * (s ^ 2 - 2))) := by
      rw [hHdef]; ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_left (poly_T hs) hS0.le
  have h1 : e * s ^ 2 ≤ 3 := by rwa [le_div_iff₀ hS0] at he
  have he2 : e ^ 2 * s ^ 2 ≤ 1 := by
    have h2 : e ≤ 1 / 4096 := by
      refine le_trans he ?_
      rw [div_le_div_iff₀ hS0 (by norm_num)]; nlinarith
    have : e ^ 2 * s ^ 2 = e * (e * s ^ 2) := by ring
    rw [this]
    calc e * (e * s ^ 2) ≤ 1 / 4096 * 3 := mul_le_mul h2 h1 (by positivity) (by norm_num)
      _ ≤ 1 := by norm_num
  have he1 : e < 1 := by
    have : e * s ^ 2 < 1 * s ^ 2 := by nlinarith
    exact lt_of_mul_lt_mul_right this hS0.le
  have hes : s ^ 2 - 3 ≤ (1 - e) * s ^ 2 := by
    have : (1 - e) * s ^ 2 = s ^ 2 - e * s ^ 2 := by ring
    linarith
  have hHT : 0 < H - T := by
    have h30 : 30 * s + 20 < s ^ 2 := by nlinarith
    have : T * s ^ 2 < H * s ^ 2 := by
      refine lt_of_le_of_lt hT ?_
      exact mul_lt_mul_of_pos_right h30 hH0 |>.trans_eq (by ring)
    exact sub_pos.mpr (lt_of_mul_lt_mul_right this hS0.le)
  have hZ' : H * (H - T) ≤ Z := by
    have : H * (H - T) = H ^ 2 - T * H := by ring
    linarith
  have hZ0 : 0 < Z := lt_of_lt_of_le (mul_pos hH0 hHT) hZ'
  have h1e : 0 < 1 - e := by linarith
  have hden : 0 < (1 - e) * (H - T) := mul_pos h1e hHT
  have hnum0 : 0 ≤ e ^ 2 * H + T := by positivity
  have step1 : (e ^ 2 * H + T) * (H / (1 - e)) / Z ≤ (e ^ 2 * H + T) / ((1 - e) * (H - T)) := by
    rw [div_le_div_iff₀ hZ0 hden]
    have e1 : (e ^ 2 * H + T) * (H / (1 - e)) * ((1 - e) * (H - T)) =
        (e ^ 2 * H + T) * (H * (H - T)) := by
      have h1e' : (1 - e) ≠ 0 := h1e.ne'
      have e0 : H / (1 - e) * ((1 - e) * (H - T)) = H * (H - T) := by
        field_simp
      rw [mul_assoc, e0]
    rw [e1]
    exact mul_le_mul_of_nonneg_left hZ' hnum0
  refine step1.trans ?_
  rw [div_le_div_iff₀ hden hS0]
  have hnum : (e ^ 2 * H + T) * s ^ 2 ≤ (30 * s + 21) * H := by
    have : e ^ 2 * H * s ^ 2 ≤ 1 * H := by
      have := mul_le_mul_of_nonneg_left he2 hH0.le
      linarith [show e ^ 2 * H * s ^ 2 = H * (e ^ 2 * s ^ 2) by ring]
    have e1 : (e ^ 2 * H + T) * s ^ 2 = e ^ 2 * H * s ^ 2 + T * s ^ 2 := by ring
    have e2 : (30 * s + 21) * H = 1 * H + (30 * s + 20) * H := by ring
    linarith
  have hA : (s ^ 2 - 30 * s - 20) * H ≤ (H - T) * s ^ 2 := by
    have : (H - T) * s ^ 2 = H * s ^ 2 - T * s ^ 2 := by ring
    have : (s ^ 2 - 30 * s - 20) * H = H * s ^ 2 - (30 * s + 20) * H := by ring
    linarith
  have hB : (s ^ 2 - 3) * (H - T) ≤ (1 - e) * (H - T) * s ^ 2 := by
    have := mul_le_mul_of_nonneg_right hes hHT.le
    linarith [show (1 - e) * s ^ 2 * (H - T) = (1 - e) * (H - T) * s ^ 2 by ring]
  have hC : (s ^ 2 - 30 * s - 23) * H ≤ (s ^ 2 - 3) * (H - T) := by
    have : (s ^ 2 - 3) * (H - T) = (H - T) * s ^ 2 - 3 * (H - T) := by ring
    have : (s ^ 2 - 30 * s - 23) * H = (s ^ 2 - 30 * s - 20) * H - 3 * H := by ring
    linarith
  have hden2 : (s ^ 2 - 30 * s - 23) * H ≤ (1 - e) * (H - T) * s ^ 2 := hC.trans hB
  have hpos : 0 ≤ 30 * s + 940 := by positivity
  refine le_of_mul_le_mul_right ?_ hS0
  calc (e ^ 2 * H + T) * s ^ 2 * s ^ 2 ≤ (30 * s + 21) * H * s ^ 2 :=
        mul_le_mul_of_nonneg_right hnum hS0.le
    _ = (30 * s + 21) * s ^ 2 * H := by ring
    _ ≤ (30 * s + 940) * (s ^ 2 - 30 * s - 23) * H := mul_le_mul_of_nonneg_right (poly_X1 hs) hH0.le
    _ = (30 * s + 940) * ((s ^ 2 - 30 * s - 23) * H) := by ring
    _ ≤ (30 * s + 940) * ((1 - e) * (H - T) * s ^ 2) := mul_le_mul_of_nonneg_left hden2 hpos
    _ = (30 * s + 940) * ((1 - e) * (H - T)) * s ^ 2 := by ring

/-- **The `J_C` term**: `X₂ ≤ (4s + 5)/s²` (`s ≥ 4096`, `0 ≤ e ≤ 3/s²`). -/
theorem x2_bound {s e H : ℝ} (hs : 4096 ≤ s) (he : e ≤ 3 / s ^ 2)
    (hHdef : H = s ^ 2 * (s ^ 2 - 1) * (s ^ 2 - 2) / 2) :
    2 * (s ^ 2 / (s ^ 2 - 1) * ((s + 1) * (s ^ 2) ^ 2)) * (1 + e) / H ≤ (4 * s + 5) / s ^ 2 := by
  have hs0 : 0 < s := by linarith
  have hS0 : 0 < s ^ 2 := by positivity
  have hs2 : 4096 ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ (by norm_num) hs 2
  have hp1 : 0 < s ^ 2 - 1 := by nlinarith
  have hp2 : 0 < s ^ 2 - 2 := by nlinarith
  have hH0 : 0 < H := by rw [hHdef]; positivity
  have hes3 : (1 + e) * s ^ 2 ≤ s ^ 2 + 3 := by
    have h1 : e * s ^ 2 ≤ 3 := by rwa [le_div_iff₀ hS0] at he
    have : (1 + e) * s ^ 2 = s ^ 2 + e * s ^ 2 := by ring
    linarith
  have hw : s ^ 2 / (s ^ 2 - 1) * (s ^ 2 - 1) = s ^ 2 := div_mul_cancel₀ _ hp1.ne'
  rw [div_le_div_iff₀ hH0 hS0]
  refine le_of_mul_le_mul_right ?_ hp1
  have hc : 0 ≤ s ^ 2 / 2 * (4 * (s + 1) * s ^ 4) := by positivity
  calc 2 * (s ^ 2 / (s ^ 2 - 1) * ((s + 1) * (s ^ 2) ^ 2)) * (1 + e) * s ^ 2 * (s ^ 2 - 1)
      = (s ^ 2 / (s ^ 2 - 1) * (s ^ 2 - 1)) * (2 * ((s + 1) * (s ^ 2) ^ 2) * (1 + e) * s ^ 2) := by
        ring
    _ = s ^ 2 / 2 * (4 * (s + 1) * s ^ 4) * ((1 + e) * s ^ 2) := by rw [hw]; ring
    _ ≤ s ^ 2 / 2 * (4 * (s + 1) * s ^ 4) * (s ^ 2 + 3) := mul_le_mul_of_nonneg_left hes3 hc
    _ = s ^ 2 / 2 * (4 * (s + 1) * s ^ 4 * (s ^ 2 + 3)) := by ring
    _ ≤ s ^ 2 / 2 * ((4 * s + 5) * ((s ^ 2 - 1) ^ 2 * (s ^ 2 - 2))) :=
        mul_le_mul_of_nonneg_left (poly_X2 hs) (by positivity)
    _ = (4 * s + 5) * H * (s ^ 2 - 1) := by rw [hHdef]; ring

/-- **The sharp numerical step**: `X₁ + X₂ ≤ 34/s + 1000/s²` for `s ≥ 4096` (in fact
`≤ (34s + 945)/s²`). -/
theorem compNumeric_34 : CompNumeric (fun s => 34 / s + 1000 / s ^ 2) := by
  intro s e Z hs he0 he hZ
  have hs0 : 0 < s := by linarith
  have hS0 : 0 < s ^ 2 := by positivity
  have h1 := x1_bound (Z := Z) hs he0 he rfl rfl hZ
  have h2 := x2_bound (e := e) hs he rfl
  have hsum : (30 * s + 940) / s ^ 2 + (4 * s + 5) / s ^ 2 ≤ 34 / s + 1000 / s ^ 2 := by
    have e1 : 34 / s = 34 * s / s ^ 2 := by
      rw [eq_div_iff hS0.ne']; field_simp
    rw [← add_div, e1, ← add_div]
    exact div_le_div_of_nonneg_right (by linarith) hS0.le
  exact (add_le_add h1 h2).trans hsum

/-- **`35 r`**: `X₁ + X₂ ≤ 35/s` for `s ≥ 4096`. -/
theorem compNumeric_35 : CompNumeric (fun s => 35 / s) := by
  refine compNumeric_34.mono fun s hs => ?_
  have hs0 : 0 < s := by linarith
  have : 1000 / s ^ 2 ≤ 1 / s := by
    rw [div_le_div_iff₀ (by positivity) hs0]; nlinarith
  have e : 35 / s = 34 / s + 1 / s := by rw [← add_div]; norm_num
  rw [e]; linarith

/-- **`38 r`**: `X₁ + X₂ ≤ 38/s` for `s ≥ 4096` (the constant SD2's proof gives). -/
theorem compNumeric_38 : CompNumeric (fun s => 38 / s) := by
  refine compNumeric_35.mono fun s hs => ?_
  exact div_le_div_of_nonneg_right (by norm_num) (by linarith)

end Sarkozy.CompSharp
