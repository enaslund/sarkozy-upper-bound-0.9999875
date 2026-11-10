module

public import Sarkozy.SignedDecompCrude.RecordPaper

@[expose] public section

/-!
# A uniform crude constant: `e_sg′(p) ≤ 21` for every `p ≥ 2²⁴` (ND)

`paper/sections/21_middle_records.tex`, `prop:signed-bounds`(c), `eq:signed-constants`.

* **`esgCrude_le`**: `esgCrude κRec nT p ≤ 21` for every `p ≥ 2²⁴`. The terms are bounded
  crudely: `κRec p ≤ 11/10`, `c_g/q ≤ 1/1000`, `6(D_g/q)Γ_A r ≤ 1/50`, `(nT + kRQ)/(1 - e₀) ≤ 96/5`.
  (The value at `Q₃` is about `19.62`, an untrusted float evaluation.)
* **`pieceGate_mono`**: the gate for a larger `e_sg` implies the gate for a smaller one.
* **`signedDecompInputs_of_gate21`**: PG's `SignedDecompInputsC C` for every `C`, from the gates
  `PieceGate (fun _ => 21) 38 k` at the 33 pieces, i.e. PG's `GateAt` with `e_o = eoP` at
  `c_col = 73`, `e_sg = 21`, `c_+ = 38`.
-/

open Finset

namespace Sarkozy.SignedDecompCrude

open Sarkozy.PrimeGram Sarkozy.SignedGram Sarkozy.SignedComponents Sarkozy.SignedDecomp
open Sarkozy.MainFinal2 (tPaper tPaper_nonneg tPaper_le_one)
open Sarkozy.MainFinalF1 (bOf Blk)
open Sarkozy.MainFinalF1c (ComparisonPartsTC)
open Sarkozy.AnalyticCells (f1Cell)
open Sarkozy.MiddleRefinement (paperSide)
open Sarkozy.MiddleRecords (GammaA)

section Bounds

variable {x : ℝ} (hx : 16777216 ≤ x)

include hx in
theorem e0_le3 : Sarkozy.SignedEstimates.e0 x ≤ 3 / x := by
  unfold Sarkozy.SignedEstimates.e0
  have h3 : 0 < x - 3 := by linarith
  have h4 : 0 < x - 4 := by linarith
  rw [div_le_div_iff₀ (by positivity) (by linarith)]
  nlinarith

include hx in
theorem e0_nonneg' : 0 ≤ Sarkozy.SignedEstimates.e0 x := by
  unfold Sarkozy.SignedEstimates.e0
  have h3 : 0 < x - 3 := by linarith
  have h4 : 0 < x - 4 := by linarith
  have : 0 ≤ x := by linarith
  positivity

include hx in
theorem sqrt_ge4096 : 4096 ≤ √x := by
  rw [show (4096 : ℝ) = √(4096 ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
  exact Real.sqrt_le_sqrt (by linarith)

include hx in
/-- `M̄ ≤ 27/x`. -/
theorem Mbar_le : Mc (10 / x) (Sarkozy.SignedEstimates.e0 x) ≤ 27 / x := by
  have he := e0_le3 hx
  have he0 := e0_nonneg' hx
  set e := Sarkozy.SignedEstimates.e0 x
  have hx0 : 0 < x := by linarith
  unfold Mc
  have h1 : 0 < 1 - 10 / x := by rw [sub_pos, div_lt_one hx0]; linarith
  have hq : 10 / x ≤ 1 / 1000000 := by rw [div_le_iff₀ hx0]; linarith
  have he' : e ≤ 1 / 1000000 := he.trans (by rw [div_le_iff₀ hx0]; linarith)
  have h2 : 0 < 1 - e := by linarith
  rw [div_le_div_iff₀ (mul_pos h1 h2) hx0]
  have hxq : 10 / x * x = 10 := by field_simp
  have hxe : e * x ≤ 3 := by rw [le_div_iff₀ hx0] at he; linarith
  nlinarith [mul_nonneg (div_nonneg (by norm_num : (0 : ℝ) ≤ 10) hx0.le) he0]

include hx in
/-- `δ(10/x, M) ≤ 65/x` for `0 ≤ M ≤ 27/x`. -/
theorem delta_le {M : ℝ} (hM : M ≤ 27 / x) : deltaC (10 / x) M ≤ 65 / x := by
  have hx0 : 0 < x := by linarith
  unfold deltaC
  have h1 : 0 < 1 - 10 / x := by rw [sub_pos, div_lt_one hx0]; linarith
  have hq : 10 / x ≤ 1 / 1000000 := by rw [div_le_iff₀ hx0]; linarith
  have hq0 : 0 ≤ 10 / x := by positivity
  rw [div_le_div_iff₀ h1 hx0]
  have hxq : 10 / x * x = 10 := by field_simp
  have hMx : M * x ≤ 27 := by rw [le_div_iff₀ hx0] at hM; linarith
  nlinarith [mul_le_mul_of_nonneg_left hMx hq0]

include hx in
/-- `|H_F|(1 - e₀) ≥ (x³ - 6x²)/2`. -/
theorem H_lower {e : ℝ} (he : e ≤ 3 / x) :
    (x ^ 3 - 6 * x ^ 2) / 2 ≤ x * (x - 1) * (x - 2) / 2 * (1 - e) := by
  have hx0 : 0 < x := by linarith
  have hex : e * x ≤ 3 := by rw [le_div_iff₀ hx0] at he; linarith
  have hH : 0 ≤ x * (x - 1) * (x - 2) / 2 := by
    have : 0 ≤ x - 1 := by linarith
    have : 0 ≤ x - 2 := by linarith
    positivity
  -- `H e ≤ 3H/x = 3(x - 1)(x - 2)/2`
  have h1 : x * (x - 1) * (x - 2) / 2 * e ≤ 3 * ((x - 1) * (x - 2)) / 2 := by
    have : x * (x - 1) * (x - 2) / 2 * e = (e * x) * ((x - 1) * (x - 2)) / 2 := by ring
    rw [this]
    have h12 : 0 ≤ (x - 1) * (x - 2) := by nlinarith
    nlinarith
  nlinarith

include hx in
/-- `X₁ ≤ 32 √x/x`. -/
theorem X1_le : X1C x (Sarkozy.SignedEstimates.e0 x) (x * (x - 1) * (x - 2) / 2) ≤ 32 * √x / x := by
  have he := e0_le3 hx
  have he0 := e0_nonneg' hx
  have hs := sqrt_ge4096 hx
  set e := Sarkozy.SignedEstimates.e0 x
  set s := √x with hsdef
  have hx0 : 0 < x := by linarith
  have hs2 : s * s = x := Real.mul_self_sqrt hx0.le
  have hex : e * x ≤ 3 := by rw [le_div_iff₀ hx0] at he; linarith
  have he1 : e ≤ 1 / 1000000 := he.trans (by rw [div_le_iff₀ hx0]; linarith)
  have hHl := H_lower hx he
  set H := x * (x - 1) * (x - 2) / 2 with hHdef
  have hD : 0 < H * (1 - e) := by
    have h6 : 0 < x ^ 2 * (x - 6) := mul_pos (by positivity) (by linarith)
    have : 0 < (x ^ 3 - 6 * x ^ 2) / 2 := by nlinarith
    linarith
  have hH0 : 0 < H := by
    have : 0 < 1 - e := by linarith
    exact pos_of_mul_pos_left hD this.le
  unfold X1C
  rw [add_div]
  have t1 : e ^ 2 * H / (H * (1 - e)) ≤ s / x := by
    rw [div_le_div_iff₀ hD hx0]
    have : e ^ 2 * H * x = (e * x) * e * H := by ring
    rw [this]
    have hb : (e * x) * e * H ≤ 3 * (1 / 1000000) * H := by
      have := mul_le_mul hex he1 he0 (by norm_num)
      nlinarith
    have hc : 3 * (1 / 1000000) * H ≤ s * (H * (1 - e)) := by nlinarith
    linarith
  have t2 : (15 * √x + 8) * x ^ 2 / (H * (1 - e)) ≤ 31 * s / x := by
    rw [div_le_div_iff₀ hD hx0, ← hsdef]
    have key : (15 * s + 8) * x ^ 2 * x ≤ 31 * s * ((x ^ 3 - 6 * x ^ 2) / 2) := by
      have hx3 : x ^ 3 = s * s * x ^ 2 := by rw [hs2]; ring
      have h8 : 8 * x + 93 * s ≤ s * x / 2 := by nlinarith
      have hx2 : 0 ≤ x ^ 2 := sq_nonneg x
      nlinarith [mul_le_mul_of_nonneg_right h8 hx2]
    have := mul_le_mul_of_nonneg_left hHl (by positivity : (0 : ℝ) ≤ 31 * s)
    linarith
  have : s / x + 31 * s / x = 32 * s / x := by ring
  linarith

include hx in
/-- `X₂ ≤ 3 √x/x`. -/
theorem X2_le : X2C x (Sarkozy.SignedEstimates.e0 x) (x * (x - 1) * (x - 2) / 2) ≤ 3 * √x / x := by
  have he := e0_le3 hx
  have he0 := e0_nonneg' hx
  have hs := sqrt_ge4096 hx
  set e := Sarkozy.SignedEstimates.e0 x
  set s := √x with hsdef
  have hx0 : 0 < x := by linarith
  have hs2 : s * s = x := Real.mul_self_sqrt hx0.le
  have he1 : e ≤ 1 / 1000000 := he.trans (by rw [div_le_iff₀ hx0]; linarith)
  have hx1 : 0 < x - 1 := by linarith
  have hx2 : 0 < x - 2 := by linarith
  unfold X2C
  have hH : 0 < x * (x - 1) * (x - 2) / 2 := by positivity
  rw [← hsdef]
  have e1 : x / (x - 1) * ((s + 1) * x ^ 2) * ((1 + e) / (x * (x - 1) * (x - 2) / 2)) =
      2 * x ^ 2 * (s + 1) * (1 + e) / ((x - 1) ^ 2 * (x - 2)) := by
    field_simp
  rw [e1, div_le_div_iff₀ (by positivity) hx0]
  -- `2x³(s + 1)(1 + e) ≤ 3s(x - 1)²(x - 2)`
  have hA : 2 * x ^ 2 * (s + 1) * (1 + e) * x ≤ 2 * x ^ 3 * (s + 1) * (1 + 1 / 1000000) := by
    have : 2 * x ^ 2 * (s + 1) * (1 + e) * x = 2 * x ^ 3 * (s + 1) * (1 + e) := by ring
    rw [this]
    have h0 : 0 ≤ 2 * x ^ 3 * (s + 1) := by positivity
    nlinarith
  have hB : 2 * x ^ 3 * (s + 1) * (1 + 1 / 1000000) ≤ 3 * s * ((x - 1) ^ 2 * (x - 2)) := by
    have hx3 : (x - 1) ^ 2 * (x - 2) ≥ x ^ 3 - 4 * x ^ 2 := by nlinarith
    have h1 : 2 * (s + 1) * (1 + 1 / 1000000) ≤ 3 * s - 12 * s / x * 1 := by
      have : 12 * s / x ≤ 1 := by rw [div_le_iff₀ hx0]; nlinarith
      nlinarith
    have hx30 : 0 ≤ x ^ 3 := by positivity
    have e2 : 3 * s * (x ^ 3 - 4 * x ^ 2) = (3 * s - 12 * s / x * 1) * x ^ 3 := by
      field_simp
      ring
    have := mul_le_mul_of_nonneg_right h1 hx30
    have h3s : 0 ≤ 3 * s := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hx3 h3s]
  linarith

end Bounds

/-! ## The four terms of `e_sg′` -/

theorem gamQ_le_two : gamQ 16777216 4096 ≤ 2 := by decide +kernel

theorem GammaA_le_two {x : ℝ} (hx : 16777216 ≤ x) : GammaA (1 / x) (√(1 / x)) ≤ 2 := by
  have h := GammaA_le (n := x) (X := 16777216) (s := 4096) (by norm_num) (by exact_mod_cast hx)
    (by norm_num) (by norm_num)
  rw [one_div, Real.sqrt_inv]
  refine h.trans ?_
  exact_mod_cast gamQ_le_two

/-- **`κRec p ≤ 11/10`** for `p ≥ 2²⁴`. -/
theorem κRec_le {p : ℕ} (hp : 2 ^ 24 ≤ p) : κRec p ≤ 11 / 10 := by
  have hx : (16777216 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  set x := (p : ℝ) with hxdef
  have hx0 : 0 < x := by linarith
  have hs := sqrt_ge4096 hx
  set s := √x with hsdef
  have hs2 : s * s = x := Real.mul_self_sqrt hx0.le
  have he := e0_le3 hx
  have he0 := e0_nonneg' hx
  have hM := Mbar_le hx
  have hη0 : 0 ≤ 10 / x := by positivity
  have hη1 : 10 / x < 1 := by rw [div_lt_one hx0]; linarith
  have he1 : Sarkozy.SignedEstimates.e0 x < 1 := he.trans_lt (by rw [div_lt_one hx0]; linarith)
  have hM0 : 0 ≤ Mc (10 / x) (Sarkozy.SignedEstimates.e0 x) := Mc_nonneg hη0 hη1 he0 he1
  have hδ := delta_le hx hM
  have hδ0 : 0 ≤ deltaC (10 / x) (Mc (10 / x) (Sarkozy.SignedEstimates.e0 x)) := by
    unfold deltaC; have : 0 < 1 - 10 / x := by linarith
    positivity
  have hX1 := X1_le hx
  have hX2 := X2_le hx
  rw [← hsdef] at hX1 hX2
  have hX10 : 0 ≤ X1C x (Sarkozy.SignedEstimates.e0 x) (x * (x - 1) * (x - 2) / 2) := by
    unfold X1C
    have : 0 < 1 - Sarkozy.SignedEstimates.e0 x := by linarith
    have : 0 ≤ x - 1 := by linarith
    have : 0 ≤ x - 2 := by linarith
    positivity
  have hX20 : 0 ≤ X2C x (Sarkozy.SignedEstimates.e0 x) (x * (x - 1) * (x - 2) / 2) := by
    unfold X2C
    have : 0 < x - 1 := by linarith
    have : 0 ≤ x - 2 := by linarith
    positivity
  unfold κRec Mbar Hp
  rw [← hxdef]
  set δ := deltaC (10 / x) (Mc (10 / x) (Sarkozy.SignedEstimates.e0 x))
  set M := Mc (10 / x) (Sarkozy.SignedEstimates.e0 x)
  set X1 := X1C x (Sarkozy.SignedEstimates.e0 x) (x * (x - 1) * (x - 2) / 2)
  set X2 := X2C x (Sarkozy.SignedEstimates.e0 x) (x * (x - 1) * (x - 2) / 2)
  have hA : δ * X1 ≤ 65 / x * (32 * s / x) := mul_le_mul hδ hX1 hX10 (by positivity)
  have hB : 4 * M * X2 ≤ 4 * (27 / x) * (3 * s / x) :=
    mul_le_mul (by linarith) hX2 hX20 (by positivity)
  have hAB : (δ * X1 + 4 * M * X2) * x ≤ 2404 * s / x := by
    have e1 : (65 / x * (32 * s / x) + 4 * (27 / x) * (3 * s / x)) * x = 2404 * s / x := by
      field_simp
      ring
    have := mul_le_mul_of_nonneg_right (add_le_add hA hB) hx0.le
    linarith
  have hsx : 2404 * s / x ≤ 2404 / 4096 := by
    rw [div_le_div_iff₀ hx0 (by norm_num)]
    nlinarith
  have ht : (1 + tPaper) = 627 / 500 := by norm_num [tPaper]
  rw [ht]
  have h0 : 0 ≤ δ * X1 + 4 * M * X2 := by positivity
  calc 627 / 500 * (δ * X1 + 4 * M * X2) * x = 627 / 500 * ((δ * X1 + 4 * M * X2) * x) := by
        ring
    _ ≤ 627 / 500 * (2404 / 4096) := by
        apply mul_le_mul_of_nonneg_left (hAB.trans hsx) (by norm_num)
    _ ≤ 11 / 10 := by norm_num

/-- `c_g/q ≤ 1/1000`. -/
theorem cg_le {x : ℝ} (hx : 16777216 ≤ x) :
    cgC (Sarkozy.SignedEstimates.e0 x) / x⁻¹ ≤ 1 / 1000 := by
  have he := e0_le3 hx
  have he0 := e0_nonneg' hx
  set e := Sarkozy.SignedEstimates.e0 x
  have hx0 : 0 < x := by linarith
  have he1 : e ≤ 1 / 1000000 := he.trans (by rw [div_le_iff₀ hx0]; linarith)
  have h1e : 0 < 1 - e := by linarith
  have hk : e / (1 - e) ≤ 6 / x := by
    rw [div_le_iff₀ h1e]
    calc e ≤ 3 / x := he
      _ = 6 / x * (1 / 2) := by ring
      _ ≤ 6 / x * (1 - e) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have hk0 : 0 ≤ e / (1 - e) := div_nonneg he0 h1e.le
  unfold cgC
  rw [div_inv_eq_mul]
  have h2 : (e / (1 - e)) ^ 2 ≤ (6 / x) ^ 2 := pow_le_pow_left₀ hk0 hk 2
  have e3 : (6 / x) ^ 2 * x = 36 / x := by field_simp; norm_num
  have h4 : 36 / x ≤ 1 / 1000 := by rw [div_le_div_iff₀ hx0 (by norm_num)]; linarith
  nlinarith

/-- `6 (D_g/q) Γ_A r ≤ 1/40`. -/
theorem dg_le {x : ℝ} (hx : 16777216 ≤ x) :
    6 * (DgC (Sarkozy.SignedEstimates.e0 x) / x⁻¹) * GammaA (1 / x) (√(1 / x)) * (√x)⁻¹ ≤
      1 / 40 := by
  have he := e0_le3 hx
  have he0 := e0_nonneg' hx
  have hs := sqrt_ge4096 hx
  have hΓ := GammaA_le_two hx
  set e := Sarkozy.SignedEstimates.e0 x
  have hx0 : 0 < x := by linarith
  have hex : e * x ≤ 3 := by rw [le_div_iff₀ hx0] at he; linarith
  have he1 : e ≤ 1 / 1000000 := he.trans (by rw [div_le_iff₀ hx0]; linarith)
  have h1e : 0 < 1 - e := by linarith
  have hD : DgC e / x⁻¹ ≤ 7 := by
    unfold DgC
    rw [div_inv_eq_mul, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [mul_le_mul hex he1 he0 (by norm_num)]
  have hD0 : 0 ≤ DgC e / x⁻¹ := by
    unfold DgC
    have : 0 ≤ x⁻¹ := by positivity
    positivity
  have hΓ0 : 0 ≤ GammaA (1 / x) (√(1 / x)) := by
    have h7 : (7 : ℝ) ≤ x := by linarith
    -- `Γ_A ≥ 1 - (small)`: its first term is `1` and the others are nonnegative
    unfold GammaA
    have hq : 1 / x ≤ 1 / 1000 := by rw [div_le_div_iff₀ hx0 (by norm_num)]; linarith
    have hq0 : 0 ≤ 1 / x := by positivity
    have h1 : 0 < 1 - 1 / x := by linarith
    have h4 : 0 < 1 - 4 * (1 / x) := by linarith
    have : 0 ≤ √(1 / x) := Real.sqrt_nonneg _
    positivity
  have hr : (√x)⁻¹ ≤ 1 / 4096 := by
    rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) hs
  have hr0 : 0 ≤ (√x)⁻¹ := by positivity
  calc 6 * (DgC e / x⁻¹) * GammaA (1 / x) (√(1 / x)) * (√x)⁻¹ ≤ 6 * 7 * 2 * (1 / 4096) := by
        gcongr
    _ ≤ 1 / 40 := by norm_num

/-- `(nT p + kRQ p)/(1 - e₀) ≤ 96/5`. -/
theorem nk_le {p : ℕ} (hp : 2 ^ 24 ≤ p) :
    (nT p + kRQ p) / (1 - Sarkozy.SignedEstimates.e0 (p : ℝ)) ≤ 96 / 5 := by
  have hx : (16777216 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  set x := (p : ℝ) with hxdef
  have hx0 : 0 < x := by linarith
  have he := e0_le3 hx
  have he1 : Sarkozy.SignedEstimates.e0 x ≤ 1 / 1000000 :=
    he.trans (by rw [div_le_iff₀ hx0]; linarith)
  have hq : x⁻¹ ≤ 1 / 16777216 := by
    rw [inv_eq_one_div]; exact one_div_le_one_div_of_le (by norm_num) hx
  have hq0 : 0 ≤ x⁻¹ := by positivity
  have hZ : 9999 / 10000 ≤ (1 - x⁻¹) * (1 - 2 * x⁻¹) := by nlinarith
  have hab : √(1 + 2 * (1 - tPaper) ^ 2) * √(1 + (1 + tPaper) ^ 2 + (1 - tPaper) ^ 2) ≤
      258 / 100 := by
    rw [← Real.sqrt_mul (by positivity)]
    rw [show (258 / 100 : ℝ) = √((258 / 100) ^ 2) by rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num [tPaper])
  have hn : nT p ≤ 2 * (258 / 100) / (9999 / 10000) := by
    unfold nT
    rw [← hxdef]
    exact div_le_div₀ (by norm_num) (by linarith) (by norm_num) hZ
  have hk : kRQ p ≤ 2 * (4 * (2 - tPaper)) / (9999 / 10000) := by
    unfold kRQ
    rw [← hxdef]
    have : 0 ≤ 2 * (4 * (2 - tPaper)) := by norm_num [tPaper]
    exact div_le_div₀ this le_rfl (by norm_num) hZ
  have ht : 2 * (4 * (2 - tPaper)) = 6984 / 500 := by norm_num [tPaper]
  rw [ht] at hk
  have h1e : (999999 / 1000000 : ℝ) ≤ 1 - Sarkozy.SignedEstimates.e0 x := by linarith
  have hsum : nT p + kRQ p ≤ 2 * (258 / 100) / (9999 / 10000) + 6984 / 500 / (9999 / 10000) := by
    linarith
  have hsum0 : 0 ≤ nT p + kRQ p := by
    have := nT_nonneg p (le_trans (by norm_num) hp)
    have : 0 ≤ kRQ p := by
      unfold kRQ
      have : 0 < 1 - x⁻¹ := by linarith
      have : 0 < 1 - 2 * x⁻¹ := by linarith
      have : 0 ≤ 2 * (4 * (2 - tPaper)) := by norm_num [tPaper]
      positivity
    linarith
  calc (nT p + kRQ p) / (1 - Sarkozy.SignedEstimates.e0 x)
      ≤ (2 * (258 / 100) / (9999 / 10000) + 6984 / 500 / (9999 / 10000)) / (999999 / 1000000) :=
        div_le_div₀ (by norm_num) hsum (by norm_num) h1e
    _ ≤ 96 / 5 := by norm_num

/-- **`e_sg′(p) ≤ 21` for every `p ≥ 2²⁴`** (`esgCrude κRec nT`). -/
theorem esgCrude_le {p : ℕ} (hp : 2 ^ 24 ≤ p) : esgCrude κRec nT p ≤ 21 := by
  have hx : (16777216 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have h1 := κRec_le hp
  have h2 := cg_le hx
  have h3 := dg_le hx
  have h4 := nk_le hp
  unfold esgCrude esgND
  linarith

/-! ## The gates -/

/-- **The gate is monotone in `e_sg`**: `PieceGate esgF c_B k` and `esgF′ ≤ esgF` on `p ≥ 2²⁴`
give `PieceGate esgF′ c_B k`. -/
theorem pieceGate_mono {esgF esgF' : ℕ → ℝ} {cB : ℝ} {k : Fin 33} (G : PieceGate esgF cB k)
    (h : ∀ p : ℕ, 2 ^ 24 ≤ p → esgF' p ≤ esgF p) : PieceGate esgF' cB k := by
  intro ι _ _ pr _ hXp hcard r hr0 hrp hrX
  obtain ⟨g1, rest⟩ := G pr hXp hcard r hr0 hrp hrX
  obtain ⟨hX24, -, -, -⟩ := table_check k
  refine ⟨fun i => le_trans ?_ (g1 i), rest⟩
  have hr : 0 ≤ rP pr i := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hle := h (pr i) (hX24.trans (hXp i))
  have : (eoP pr (fun _ => 73) i + esgF' (pr i)) * rP pr i ≤
      (eoP pr (fun _ => 73) i + esgF (pr i)) * rP pr i :=
    mul_le_mul_of_nonneg_right (by linarith) hr
  exact mul_le_mul_of_nonneg_right (by linarith) hr

end Sarkozy.SignedDecompCrude
