module

public import Sarkozy.NormBoundsPaper3.TripleLaws

@[expose] public section

/-!
# The exact-marginal matching law `K₁` at one prime (`lem:record:e-law`(a); NB3)

`paper/sections/21_middle_records.tex`, `lem:record:e-law`(a): `K₁` "is `4/z₁` times the indicator
of the strict edges `x₁ → y₀` and `x₀ → y₁` … whose two half marginals both equal `ν_E`"; proof:
"Fix a half `x`. Under `ν_E` the pair `(y₀, y₁)` is uniform on ordered distinct pairs, and the
pairs with `x₁ → y₀` and `x₀ → y₁` number `((p − 1)/2)² − k_p = (p² − 3p + 4)/4`, the coincident
ones being the `k_p` common out-neighbours of `x₀` and `x₁` (`lem:paley-triple`(a)) … the column
sums are one by the same count with common in-neighbours."

`MiddleComparison.eLaw` is the uniform law on `eSet` (two layers of three labels, injective in each
layer, with the strict edges `x₁ → y₀`, `x₀ → y₁`). Read at the two layers it is the matrix `P3`:

* `asm x y`: the labelling with layers `x`, `y`; `rd_asm_iff`; **`P3_weight`**: `P3 x y` is the
  weight of `asm x y`;
* `sq1 d = [χ(d) = 1]`, `good x y = [x, y injective][x₁ → y₀][x₀ → y₁]`; **`P3_eq`**:
  `P3 x y = good x y / |eSet|`;
* `sum_off_mul`; **`row_count`**, **`col_count`**: for `x₀ ≠ x₁` (resp. `y₀ ≠ y₁`) the fibre has
  `(p − 2)(p² − 3p + 4)/4` points (`card_out`, `card_common_out`, `card_in`, `card_common_in`);
* **`eSet_card`**: `|eSet| = p(p − 1)(p − 2) · (p − 2)(p² − 3p + 4)/4`;
* **`P3_row`**, **`P3_col`**: both half marginals of `K₁` are `ν_E` (`m3`).
-/

open Finset Matrix
open scoped BigOperators

namespace Sarkozy.NormBoundsPaper3

open Sarkozy.PartV Sarkozy.Labellings Sarkozy.PartVRecords Sarkozy.MiddleComparison
open Sarkozy.NormBoundsPaper2 (off sum_off)
open Sarkozy.TraceMixing (card_out card_in card_common_out card_common_in)

section Assemble

variable {F : Type}

/-- The two-layer labelling with layer `0` equal to `x` and layer `1` equal to `y`. -/
def asm (x y : (F × F) × F) : Fin 3 × Fin 2 → F :=
  fun w => if w.2 = 0 then ![x.1.1, x.1.2, x.2] w.1 else ![y.1.1, y.1.2, y.2] w.1

theorem rd_asm_iff (z : Fin 3 × Fin 2 → F) (x y : (F × F) × F) :
    rd z (lay 0) = x ∧ rd z (lay 1) = y ↔ z = asm x y := by
  constructor
  · rintro ⟨rfl, rfl⟩
    funext w
    rcases w with ⟨k, ℓ⟩
    fin_cases k <;> fin_cases ℓ <;> rfl
  · rintro rfl
    exact ⟨rfl, rfl⟩

theorem vec3_inj_iff {a b c : F} :
    Function.Injective (![a, b, c] : Fin 3 → F) ↔ a ≠ b ∧ c ≠ a ∧ c ≠ b := by
  constructor
  · intro h
    refine ⟨fun e => ?_, fun e => ?_, fun e => ?_⟩
    · exact absurd (h (show (![a, b, c] : Fin 3 → F) 0 = ![a, b, c] 1 from e)) (by decide)
    · exact absurd (h (show (![a, b, c] : Fin 3 → F) 2 = ![a, b, c] 0 from e)) (by decide)
    · exact absurd (h (show (![a, b, c] : Fin 3 → F) 2 = ![a, b, c] 1 from e)) (by decide)
  · exact vec3_inj

end Assemble

section Prime

variable {p : ℕ} [Fact p.Prime]

/-- `[χ(d) = 1]`. -/
noncomputable def sq1 (d : ZMod p) : ℝ := if quadraticChar (ZMod p) d = 1 then 1 else 0

theorem sq1_nonneg (d : ZMod p) : 0 ≤ sq1 d := by unfold sq1; split_ifs <;> norm_num

/-- `[x, y injective][x₁ → y₀][x₀ → y₁]`. -/
noncomputable def good (x y : (ZMod p × ZMod p) × ZMod p) : ℝ :=
  ind3 x * ind3 y * sq1 (y.1.1 - x.1.2) * sq1 (y.1.2 - x.1.1)

theorem good_nonneg (x y : (ZMod p × ZMod p) × ZMod p) : 0 ≤ good x y := by
  unfold good
  have := ind3_nonneg x
  have := ind3_nonneg y
  have := sq1_nonneg (y.1.1 - x.1.2)
  have := sq1_nonneg (y.1.2 - x.1.1)
  positivity

theorem eGood_asm (x y : (ZMod p × ZMod p) × ZMod p) :
    EGood (asm x y) ↔ Inj3 x ∧ Inj3 y ∧ quadraticChar (ZMod p) (y.1.1 - x.1.2) = 1 ∧
      quadraticChar (ZMod p) (y.1.2 - x.1.1) = 1 := by
  have e0 : (fun o : Fin 3 => asm x y (o, 0)) = ![x.1.1, x.1.2, x.2] := by
    funext o; fin_cases o <;> rfl
  have e1 : (fun o : Fin 3 => asm x y (o, 1)) = ![y.1.1, y.1.2, y.2] := by
    funext o; fin_cases o <;> rfl
  have a01 : asm x y (0, 1) = y.1.1 := rfl
  have a10 : asm x y (1, 0) = x.1.2 := rfl
  have a11 : asm x y (1, 1) = y.1.2 := rfl
  have a00 : asm x y (0, 0) = x.1.1 := rfl
  unfold EGood
  rw [Fin.forall_fin_two, e0, e1, vec3_inj_iff, vec3_inj_iff, a01, a10, a11, a00]
  unfold Inj3
  exact and_assoc

theorem good_eq (x y : (ZMod p × ZMod p) × ZMod p) :
    good x y = if EGood (asm x y) then 1 else 0 := by
  have key := eGood_asm x y
  by_cases hg : EGood (asm x y)
  · obtain ⟨h1, h2, h3, h4⟩ := key.mp hg
    simp only [good, ind3, sq1, h1, h2, h3, h4, hg, ↓reduceIte, mul_one]
  · have hz : ¬(Inj3 x ∧ Inj3 y ∧ quadraticChar (ZMod p) (y.1.1 - x.1.2) = 1 ∧
        quadraticChar (ZMod p) (y.1.2 - x.1.1) = 1) := fun h => hg (key.mpr h)
    simp only [hg, ↓reduceIte]
    unfold good ind3 sq1
    by_cases h1 : Inj3 x
    · by_cases h2 : Inj3 y
      · by_cases h3 : quadraticChar (ZMod p) (y.1.1 - x.1.2) = 1
        · have h4 : ¬quadraticChar (ZMod p) (y.1.2 - x.1.1) = 1 := fun h4 => hz ⟨h1, h2, h3, h4⟩
          simp only [h4, ↓reduceIte, mul_zero]
        · simp only [h3, ↓reduceIte, mul_zero, zero_mul]
      · simp only [h2, ↓reduceIte, mul_zero, zero_mul]
    · simp only [h1, ↓reduceIte, zero_mul]

/-- **`K₁` read at the two layers.** -/
noncomputable def P3 (hE : (eSet (F := ZMod p)).Nonempty) :
    Matrix ((ZMod p × ZMod p) × ZMod p) ((ZMod p × ZMod p) × ZMod p) ℝ :=
  cmT (eLaw hE) (lay 0) (lay 1)

theorem P3_weight (hE : (eSet (F := ZMod p)).Nonempty) (x y : (ZMod p × ZMod p) × ZMod p) :
    P3 hE x y = (eLaw hE).weight (asm x y) := by
  unfold P3 cmT
  rw [sum_eq_single (asm x y)]
  · rw [ite_eq_left_iff.mpr (fun h => absurd ((rd_asm_iff _ x y).mpr rfl) h), mul_one]
  · intro z _ hz
    rw [ite_eq_right_iff.mpr (fun h => absurd ((rd_asm_iff z x y).mp h) hz), mul_zero]
  · exact fun h => absurd (mem_univ _) h

/-- `|eSet|`, as a real number. -/
noncomputable def Nk : ℝ := ((eSet (F := ZMod p)).card : ℝ)

theorem Nk_pos (hE : (eSet (F := ZMod p)).Nonempty) : 0 < Nk (p := p) := by
  unfold Nk
  exact_mod_cast card_pos.mpr hE

/-- **`P3 x y = good x y / |eSet|`.** -/
theorem P3_eq (hE : (eSet (F := ZMod p)).Nonempty) (x y : (ZMod p × ZMod p) × ZMod p) :
    P3 hE x y = good x y / Nk (p := p) := by
  rw [P3_weight, good_eq]
  change (if asm x y ∈ eSet then 1 / ((eSet (F := ZMod p)).card : ℝ) else 0) = _
  have hm : asm x y ∈ eSet ↔ EGood (asm x y) := by
    simp only [eSet, mem_filter, mem_univ, true_and]
  unfold Nk
  by_cases hg : EGood (asm x y)
  · simp [hm.mpr hg, hg]
  · simp [mt hm.mp hg, hg]

theorem P3_nonneg (hE : (eSet (F := ZMod p)).Nonempty) (x y : (ZMod p × ZMod p) × ZMod p) :
    0 ≤ P3 hE x y :=
  cmT_nonneg _ _ _ x y

theorem sum_good (hE : (eSet (F := ZMod p)).Nonempty) :
    ∑ x, ∑ y, good (p := p) x y = Nk (p := p) := by
  have h1 : ∑ x, ∑ y, P3 hE x y = 1 := by
    unfold P3
    simp only [cmT_row]
    exact sum_tw _ _
  simp only [P3_eq, ← sum_div] at h1
  rw [div_eq_one_iff_eq (Nk_pos hE).ne'] at h1
  exact h1

/-! ### The fibre counts -/

/-- `∑_b [b₀ ≠ b₁] f(b₀) g(b₁) = (∑ f)(∑ g) − ∑ f g`. -/
theorem sum_off_mul (f g : ZMod p → ℝ) :
    ∑ b : ZMod p × ZMod p, off b * (f b.1 * g b.2) = (∑ a, f a) * (∑ a, g a) - ∑ a, f a * g a := by
  have e : ∀ b : ZMod p × ZMod p, off b * (f b.1 * g b.2) =
      f b.1 * g b.2 - (if b.1 = b.2 then f b.1 * g b.2 else 0) := by
    intro b
    unfold off
    split_ifs <;> ring
  simp only [e, sum_sub_distrib, Fintype.sum_prod_type, sum_mul_sum]
  congr 1
  refine sum_congr rfl fun a _ => ?_
  rw [sum_ite_eq]
  simp

theorem sum_sq1 (hp2 : p ≠ 2) (a : ZMod p) :
    2 * ∑ c, sq1 (c - a) = (p : ℝ) - 1 := by
  have hF : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  have h := card_out hF a
  rw [ZMod.card] at h
  unfold sq1
  rw [sum_boole]
  have h' : (2 : ℝ) * ((univ.filter fun b : ZMod p => quadraticChar (ZMod p) (b - a) = 1).card : ℝ)
      = ((2 * ((univ.filter fun b : ZMod p => quadraticChar (ZMod p) (b - a) = 1).card : ℤ) : ℤ)
        : ℝ) := by push_cast; ring
  rw [h', h]
  push_cast
  ring

theorem sum_sq1_in (hp2 : p ≠ 2) (h3 : p % 4 = 3) (a : ZMod p) :
    2 * ∑ c, sq1 (a - c) = (p : ℝ) - 1 := by
  have hF : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  have h := card_in hF (by rw [ZMod.card]; exact h3) a
  rw [ZMod.card] at h
  unfold sq1
  rw [sum_boole]
  have h' : (2 : ℝ) * ((univ.filter fun b : ZMod p => quadraticChar (ZMod p) (a - b) = 1).card : ℝ)
      = ((2 * ((univ.filter fun b : ZMod p => quadraticChar (ZMod p) (a - b) = 1).card : ℤ) : ℤ)
        : ℝ) := by push_cast; ring
  rw [h', h]
  push_cast
  ring

theorem sq1_mul (d e : ZMod p) :
    sq1 d * sq1 e =
      if quadraticChar (ZMod p) d = 1 ∧ quadraticChar (ZMod p) e = 1 then 1 else 0 := by
  unfold sq1
  split_ifs <;> simp_all

theorem sum_sq1_common (hp2 : p ≠ 2) (h3 : p % 4 = 3) {a a' : ZMod p} (haa : a ≠ a') :
    4 * ∑ c, sq1 (c - a) * sq1 (c - a') = (p : ℝ) - 3 := by
  have hF : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  have h := card_common_out hF (by rw [ZMod.card]; exact h3) haa
  rw [ZMod.card] at h
  simp only [sq1_mul]
  rw [sum_boole]
  have h' : (4 : ℝ) * ((univ.filter fun c : ZMod p => quadraticChar (ZMod p) (c - a) = 1 ∧
      quadraticChar (ZMod p) (c - a') = 1).card : ℝ) =
      ((4 * ((univ.filter fun c : ZMod p => quadraticChar (ZMod p) (c - a) = 1 ∧
      quadraticChar (ZMod p) (c - a') = 1).card : ℤ) : ℤ) : ℝ) := by push_cast; ring
  rw [h', h]
  push_cast
  ring

theorem sum_sq1_common_in (hp2 : p ≠ 2) (h3 : p % 4 = 3) {a a' : ZMod p} (haa : a ≠ a') :
    4 * ∑ c, sq1 (a - c) * sq1 (a' - c) = (p : ℝ) - 3 := by
  have hF : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  have h := card_common_in hF (by rw [ZMod.card]; exact h3) haa
  rw [ZMod.card] at h
  simp only [sq1_mul]
  rw [sum_boole]
  have h' : (4 : ℝ) * ((univ.filter fun c : ZMod p => quadraticChar (ZMod p) (a - c) = 1 ∧
      quadraticChar (ZMod p) (a' - c) = 1).card : ℝ) =
      ((4 * ((univ.filter fun c : ZMod p => quadraticChar (ZMod p) (a - c) = 1 ∧
      quadraticChar (ZMod p) (a' - c) = 1).card : ℤ) : ℤ) : ℝ) := by push_cast; ring
  rw [h', h]
  push_cast
  ring

/-- The fibre size `(p − 2)(p² − 3p + 4)/4`. -/
noncomputable def Rf (p : ℕ) : ℝ := ((p : ℝ) - 2) * ((p : ℝ) ^ 2 - 3 * p + 4) / 4

/-- **The row count**: given `x₀ ≠ x₁`, the halves `y` with `x₁ → y₀`, `x₀ → y₁`. -/
theorem row_count (hp2 : p ≠ 2) (h3 : p % 4 = 3) {a₀ a₁ : ZMod p} (ha : a₀ ≠ a₁) :
    ∑ y : (ZMod p × ZMod p) × ZMod p, ind3 y * sq1 (y.1.1 - a₁) * sq1 (y.1.2 - a₀) = Rf p := by
  rw [Fintype.sum_prod_type]
  have e : ∀ b : ZMod p × ZMod p, ∑ c, ind3 (b, c) * sq1 (b.1 - a₁) * sq1 (b.2 - a₀) =
      ((p : ℝ) - 2) * (off b * (sq1 (b.1 - a₁) * sq1 (b.2 - a₀))) := by
    intro b
    rw [← sum_mul, ← sum_mul, sum_ind3_fib, ZMod.card]
    ring
  have hs := sum_off_mul (fun c => sq1 (c - a₁)) (fun c => sq1 (c - a₀))
  simp only [e, ← mul_sum, hs]
  have h1 := sum_sq1 hp2 a₁
  have h2 := sum_sq1 hp2 a₀
  have h4 := sum_sq1_common hp2 h3 (Ne.symm ha)
  have e1 : ∑ c, sq1 (c - a₁) = ((p : ℝ) - 1) / 2 := by linarith
  have e2 : ∑ c, sq1 (c - a₀) = ((p : ℝ) - 1) / 2 := by linarith
  have e4 : ∑ c, sq1 (c - a₁) * sq1 (c - a₀) = ((p : ℝ) - 3) / 4 := by linarith
  rw [e1, e2, e4]
  unfold Rf
  ring

/-- **The column count**: given `y₀ ≠ y₁`, the halves `x` with `x₁ → y₀`, `x₀ → y₁`. -/
theorem col_count (hp2 : p ≠ 2) (h3 : p % 4 = 3) {b₀ b₁ : ZMod p} (hb : b₀ ≠ b₁) :
    ∑ x : (ZMod p × ZMod p) × ZMod p, ind3 x * sq1 (b₀ - x.1.2) * sq1 (b₁ - x.1.1) = Rf p := by
  rw [Fintype.sum_prod_type]
  have e : ∀ a : ZMod p × ZMod p, ∑ c, ind3 (a, c) * sq1 (b₀ - a.2) * sq1 (b₁ - a.1) =
      ((p : ℝ) - 2) * (off a * (sq1 (b₁ - a.1) * sq1 (b₀ - a.2))) := by
    intro a
    rw [← sum_mul, ← sum_mul, sum_ind3_fib, ZMod.card]
    ring
  have hs := sum_off_mul (fun c => sq1 (b₁ - c)) (fun c => sq1 (b₀ - c))
  simp only [e, ← mul_sum, hs]
  have h1 := sum_sq1_in hp2 h3 b₁
  have h2 := sum_sq1_in hp2 h3 b₀
  have h4 := sum_sq1_common_in hp2 h3 (Ne.symm hb)
  have e1 : ∑ c, sq1 (b₁ - c) = ((p : ℝ) - 1) / 2 := by linarith
  have e2 : ∑ c, sq1 (b₀ - c) = ((p : ℝ) - 1) / 2 := by linarith
  have e4 : ∑ c, sq1 (b₁ - c) * sq1 (b₀ - c) = ((p : ℝ) - 3) / 4 := by linarith
  rw [e1, e2, e4]
  unfold Rf
  ring

theorem row_good (hp2 : p ≠ 2) (h3 : p % 4 = 3) (x : (ZMod p × ZMod p) × ZMod p) :
    ∑ y, good x y = ind3 x * Rf p := by
  by_cases hx : Inj3 x
  · have e : ∀ y, good x y = ind3 x * (ind3 y * sq1 (y.1.1 - x.1.2) * sq1 (y.1.2 - x.1.1)) :=
      fun y => by unfold good; ring
    simp only [e, ← mul_sum, row_count hp2 h3 hx.1]
  · have h0 : ind3 x = 0 := by unfold ind3; simp [hx]
    simp [good, h0]

theorem col_good (hp2 : p ≠ 2) (h3 : p % 4 = 3) (y : (ZMod p × ZMod p) × ZMod p) :
    ∑ x, good x y = ind3 y * Rf p := by
  by_cases hy : Inj3 y
  · have e : ∀ x, good x y = ind3 y * (ind3 x * sq1 (y.1.1 - x.1.2) * sq1 (y.1.2 - x.1.1)) :=
      fun x => by unfold good; ring
    simp only [e, ← mul_sum, col_count hp2 h3 hy.1]
  · have h0 : ind3 y = 0 := by unfold ind3; simp [hy]
    simp [good, h0]

/-- **`|eSet| = p(p − 1)(p − 2) (p − 2)(p² − 3p + 4)/4`.** -/
theorem eSet_card (hE : (eSet (F := ZMod p)).Nonempty) (hp2 : p ≠ 2) (h3 : p % 4 = 3) :
    Nk (p := p) = (p : ℝ) * ((p : ℝ) - 1) * ((p : ℝ) - 2) * Rf p := by
  rw [← sum_good hE]
  simp only [row_good hp2 h3, ← sum_mul, sum_ind3]

omit [Fact p.Prime] in
theorem Rf_pos (hp : 7 ≤ p) : 0 < Rf p := by
  have : (7 : ℝ) ≤ p := by exact_mod_cast hp
  unfold Rf
  have h1 : (0 : ℝ) < (p : ℝ) - 2 := by linarith
  have h2 : (0 : ℝ) < (p : ℝ) ^ 2 - 3 * p + 4 := by nlinarith
  positivity

/-- **Both half marginals of `K₁` are `ν_E`** (rows). -/
theorem P3_row (hE : (eSet (F := ZMod p)).Nonempty) (hp : 7 ≤ p) (h3 : p % 4 = 3)
    (x : (ZMod p × ZMod p) × ZMod p) :
    ∑ y, P3 hE x y = m3 p x := by
  have hp2 : p ≠ 2 := by omega
  simp only [P3_eq, ← sum_div, row_good hp2 h3, eSet_card hE hp2 h3]
  have hR := Rf_pos hp
  unfold m3
  field_simp

/-- **Both half marginals of `K₁` are `ν_E`** (columns). -/
theorem P3_col (hE : (eSet (F := ZMod p)).Nonempty) (hp : 7 ≤ p) (h3 : p % 4 = 3)
    (y : (ZMod p × ZMod p) × ZMod p) :
    ∑ x, P3 hE x y = m3 p y := by
  have hp2 : p ≠ 2 := by omega
  simp only [P3_eq, ← sum_div, col_good hp2 h3, eSet_card hE hp2 h3]
  have hR := Rf_pos hp
  unfold m3
  field_simp

end Prime

end Sarkozy.NormBoundsPaper3
