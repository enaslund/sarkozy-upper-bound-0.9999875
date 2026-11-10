module

public import Sarkozy.Misc.LowerStartSums
public import Sarkozy.PartVLaws.PieceCaps

@[expose] public section

/-!
# Block charges over the exact blocks (`lem:record:block-charge`(ii))

`paper/sections/20_middle_reference.tex`, `lem:record:block-charge`(ii). For an exact block `𝔅` of
`def:record:exact-blocks`(c) (V1's greedy blocks `Sarkozy.PartV.greedyBlocks`), with
`𝔲(𝔅) = ∑_{p ∈ 𝔅} 𝔲(p)`, the bin `k_𝔅 = ⌈2¹⁶ 𝔲(𝔅)/𝔲_*⌉` (`Sarkozy.PartVLaws.blockBin`, from
`PartVLaws/PieceCaps.lean`) and the rounded weights
`w₂(𝔅) = ⌈2⁹⁵/b_𝔅⌉`, `w₃(𝔅) = ⌈2¹²⁷/(b_𝔅 ⌊(2⁶⁴ b_𝔅)^{1/2}⌋)⌉`, `w₄(𝔅) = ⌈2⁹⁵/b_𝔅²⌉`:

* `1 ≤ k_𝔅 ≤ 2¹⁶` (`bin_bounds`, from V1's `one_le_blockBin`, `blockBin_le`);
* `q_𝔅^{2a} ≤ exp(2a 𝔲_* k_𝔅/2⁵⁶) ≤ e^{2aL}` (`exact_price_le`);
* `b_𝔅^{-d/2} ≤ w_d(𝔅)/2⁹⁵` for `d = 2, 3, 4` (`rpow_le_wd`);
* consequently, for the blocks of a part,
  `∑_𝔅 q_𝔅^{2a} b_𝔅^{-d/2} ≤ ∑_{k=1}^{2¹⁶} exp(2a 𝔲_* k/2⁵⁶) w_d(𝔭, k)/2⁹⁵` with
  `w_d(𝔭, k) = ∑_{k_𝔅 = k} w_d(𝔅)` (`block_charge_exact`, for any list of blocks satisfying the
  stated per-block facts, and `block_charge_greedy` for V1's greedy blocks of a list of primes).

`⌊(2⁶⁴ b)^{1/2}⌋` is `Nat.sqrt (2⁶⁴ b)`. The first prime of a block is `B.headD 0`. The histogram
values themselves (`cert:record:middle-price`) are data and are not entered here.
-/

open Finset

namespace Sarkozy.Misc

open Sarkozy.PartV Sarkozy.PartVLaws

/-! ## The rounded weights -/

/-- `w₃(𝔅) = ⌈2¹²⁷ / (b ⌊(2⁶⁴ b)^{1/2}⌋)⌉`. -/
noncomputable def w3 (b : ℕ) : ℕ := ⌈(2 : ℝ) ^ 127 / ((b : ℝ) * (Nat.sqrt (2 ^ 64 * b) : ℕ))⌉₊

/-- `w₃` as written in the paper, with `⌊(2⁶⁴ b)^{1/2}⌋` the floor of the real square root. -/
theorem w3_eq (b : ℕ) :
    w3 b = ⌈(2 : ℝ) ^ 127 / ((b : ℝ) * (⌊Real.sqrt ((2 ^ 64 * b : ℕ) : ℝ)⌋₊ : ℕ))⌉₊ := by
  rw [Real.nat_floor_real_sqrt_eq_nat_sqrt]
  rfl

/-- `w₄(𝔅) = ⌈2⁹⁵ / b²⌉`. -/
noncomputable def w4 (b : ℕ) : ℕ := ⌈(2 : ℝ) ^ 95 / (b : ℝ) ^ 2⌉₊

/-- `w_d` for `d ∈ {2, 3, 4}`. -/
noncomputable def wd (d b : ℕ) : ℕ := if d = 2 then w2 b else if d = 3 then w3 b else w4 b

theorem rpow_le_w2 {b : ℕ} (hb : 0 < b) : (b : ℝ) ^ (-(2 : ℝ) / 2) ≤ (w2 b : ℝ) / 2 ^ 95 := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have he : -(2 : ℝ) / 2 = -1 := by norm_num
  rw [he, Real.rpow_neg_one, le_div_iff₀ (by positivity)]
  have h := Nat.le_ceil ((2 : ℝ) ^ 95 / b)
  unfold w2
  calc (b : ℝ)⁻¹ * 2 ^ 95 = 2 ^ 95 / b := by field_simp
    _ ≤ _ := h

theorem rpow_le_w4 {b : ℕ} (hb : 0 < b) : (b : ℝ) ^ (-(4 : ℝ) / 2) ≤ (w4 b : ℝ) / 2 ^ 95 := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have he : -(4 : ℝ) / 2 = -((2 : ℕ) : ℝ) := by norm_num
  rw [he, Real.rpow_neg hbR.le, Real.rpow_natCast, le_div_iff₀ (by positivity)]
  have h := Nat.le_ceil ((2 : ℝ) ^ 95 / (b : ℝ) ^ 2)
  unfold w4
  calc ((b : ℝ) ^ 2)⁻¹ * 2 ^ 95 = 2 ^ 95 / (b : ℝ) ^ 2 := by field_simp
    _ ≤ _ := h

theorem rpow_le_w3 {b : ℕ} (hb : 0 < b) : (b : ℝ) ^ (-(3 : ℝ) / 2) ≤ (w3 b : ℝ) / 2 ^ 95 := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  set s0 : ℕ := Nat.sqrt (2 ^ 64 * b) with hs0
  have hs0pos : (0 : ℝ) < s0 := by
    have : 0 < s0 := Nat.sqrt_pos.mpr (by positivity)
    exact_mod_cast this
  -- `s₀ ≤ 2³² √b`
  have hs0le : (s0 : ℝ) ≤ 2 ^ 32 * Real.sqrt b := by
    have h1 : (s0 : ℝ) ≤ Real.sqrt ((2 ^ 64 * b : ℕ) : ℝ) := Real.nat_sqrt_le_real_sqrt
    have h2 : Real.sqrt ((2 ^ 64 * b : ℕ) : ℝ) = 2 ^ 32 * Real.sqrt b := by
      have hc : ((2 ^ 64 * b : ℕ) : ℝ) = (2 ^ 32) ^ 2 * (b : ℝ) := by push_cast; ring
      rw [hc, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    rw [h2] at h1
    exact h1
  have hsqrt : 0 < Real.sqrt b := Real.sqrt_pos.mpr hbR
  -- `b^{-3/2} = 1/(b √b)`
  have he : (b : ℝ) ^ (-(3 : ℝ) / 2) = ((b : ℝ) * Real.sqrt b)⁻¹ := by
    have : -(3 : ℝ) / 2 = -(1 + 1 / 2) := by norm_num
    rw [this, Real.rpow_neg hbR.le, Real.rpow_add hbR, Real.rpow_one, ← Real.sqrt_eq_rpow]
  rw [he, le_div_iff₀ (by positivity)]
  have hc := Nat.le_ceil ((2 : ℝ) ^ 127 / ((b : ℝ) * (s0 : ℝ)))
  unfold w3
  rw [← hs0]
  refine le_trans ?_ hc
  rw [le_div_iff₀ (by positivity)]
  have hprod : (b : ℝ) * s0 ≤ (b : ℝ) * (2 ^ 32 * Real.sqrt b) :=
    mul_le_mul_of_nonneg_left hs0le hbR.le
  have hinv : ((b : ℝ) * Real.sqrt b)⁻¹ * ((b : ℝ) * Real.sqrt b) = 1 :=
    inv_mul_cancel₀ (by positivity)
  calc ((b : ℝ) * Real.sqrt b)⁻¹ * 2 ^ 95 * ((b : ℝ) * s0)
      ≤ ((b : ℝ) * Real.sqrt b)⁻¹ * 2 ^ 95 * ((b : ℝ) * (2 ^ 32 * Real.sqrt b)) :=
        mul_le_mul_of_nonneg_left hprod (by positivity)
    _ = 2 ^ 127 * (((b : ℝ) * Real.sqrt b)⁻¹ * ((b : ℝ) * Real.sqrt b)) := by ring
    _ = 2 ^ 127 := by rw [hinv, mul_one]

/-- **`b_𝔅^{-d/2} ≤ w_d(𝔅)/2⁹⁵`** for `d = 2, 3, 4` (`lem:record:block-charge`(ii)). -/
theorem rpow_le_wd {d b : ℕ} (hd : d = 2 ∨ d = 3 ∨ d = 4) (hb : 0 < b) :
    (b : ℝ) ^ (-(d : ℝ) / 2) ≤ (wd d b : ℝ) / 2 ^ 95 := by
  rcases hd with rfl | rfl | rfl
  · simpa [wd] using rpow_le_w2 hb
  · simpa [wd] using rpow_le_w3 hb
  · simpa [wd] using rpow_le_w4 hb

/-! ## The price of an exact block -/

/-- `log q_𝔅 = ∑_{p ∈ 𝔅} log p` for positive integers. -/
theorem log_prod_eq (B : List ℕ) (hpos : ∀ p ∈ B, 0 < p) :
    Real.log ((B.prod : ℕ) : ℝ) = (B.map fun p : ℕ => Real.log (p : ℝ)).sum := by
  induction B with
  | nil => simp
  | cons p B ih =>
    have hp : (0 : ℝ) < p := by exact_mod_cast hpos p List.mem_cons_self
    have hB : (0 : ℝ) < (B.prod : ℕ) := by
      have : 0 < B.prod := List.prod_pos fun q hq => hpos q (List.mem_cons_of_mem p hq)
      exact_mod_cast this
    rw [List.prod_cons, Nat.cast_mul, Real.log_mul hp.ne' hB.ne', List.map_cons, List.sum_cons,
      ih fun q hq => hpos q (List.mem_cons_of_mem p hq)]

/-- **`1 ≤ k_𝔅 ≤ 2¹⁶`** when `0 < 𝔲(𝔅) ≤ 𝔲_*`. -/
theorem bin_bounds {u : ℕ → ℕ} {B : List ℕ} (h0 : 0 < blockU u B)
    (hU : blockU u B ≤ integerBudget) : 1 ≤ blockBin u B ∧ blockBin u B ≤ 2 ^ 16 :=
  ⟨one_le_blockBin h0, blockBin_le hU⟩

/-- **The price of an exact block** (`lem:record:block-charge`(ii)):
`q_𝔅^{2a} ≤ exp(2a 𝔲_* k_𝔅/2⁵⁶) ≤ e^{2aL}`, for `a ≥ 0`, positive primes with `log p < 𝔲(p)/2⁴⁰`
and `𝔲(𝔅) ≤ 𝔲_*`. -/
theorem exact_price_le (u : ℕ → ℕ) (B : List ℕ) {a : ℝ} (ha : 0 ≤ a) (hpos : ∀ p ∈ B, 0 < p)
    (hlog : ∀ p ∈ B, Real.log p < (u p : ℝ) / 2 ^ 40) (hU : blockU u B ≤ integerBudget) :
    ((B.prod : ℕ) : ℝ) ^ (2 * a) ≤ Real.exp (2 * a * integerBudget * blockBin u B / 2 ^ 56) ∧
      Real.exp (2 * a * integerBudget * blockBin u B / 2 ^ 56) ≤
        Real.exp (2 * a * middleBudget) := by
  have hq : (0 : ℝ) < (B.prod : ℕ) := by
    have : 0 < B.prod := List.prod_pos hpos
    exact_mod_cast this
  have hlogq : Real.log ((B.prod : ℕ) : ℝ) ≤ (blockBin u B : ℝ) * middleBudget / 2 ^ 16 := by
    rw [log_prod_eq B hpos]
    exact exactBlock_log_le_bin u B hlog
  have hbud : (integerBudget : ℝ) / 2 ^ 56 = middleBudget / 2 ^ 16 := by
    rw [integerBudget_eq_real]
    ring
  have hexp : 2 * a * integerBudget * blockBin u B / 2 ^ 56 =
      2 * a * ((blockBin u B : ℝ) * middleBudget / 2 ^ 16) := by
    have : 2 * a * (integerBudget : ℝ) * blockBin u B / 2 ^ 56 =
        2 * a * blockBin u B * ((integerBudget : ℝ) / 2 ^ 56) := by ring
    rw [this, hbud]
    ring
  constructor
  · rw [Real.rpow_def_of_pos hq, hexp]
    apply Real.exp_le_exp.mpr
    nlinarith
  · rw [hexp]
    apply Real.exp_le_exp.mpr
    have := bin_cap_le hU
    nlinarith

/-! ## Grouping the blocks by their bin -/

/-- Regrouping a sum over a list by the values of `g` in `K`. -/
theorem list_sum_regroup {α : Type*} (l : List α) (g : α → ℕ) (K : Finset ℕ)
    (hK : ∀ B ∈ l, g B ∈ K) (F : ℕ → ℝ) (w : α → ℝ) :
    (l.map fun B => F (g B) * w B).sum =
      ∑ k ∈ K, F k * ((l.filter fun B => g B = k).map w).sum := by
  induction l with
  | nil => simp
  | cons B l ih =>
    rw [List.map_cons, List.sum_cons, ih fun B' hB' => hK B' (List.mem_cons_of_mem _ hB')]
    have hstep : ∀ k ∈ K, F k * (((B :: l).filter fun B => g B = k).map w).sum =
        F k * ((l.filter fun B => g B = k).map w).sum + if k = g B then F k * w B else 0 := by
      intro k _
      by_cases h : g B = k
      · subst h
        simp only [List.filter_cons, decide_true, ↓reduceIte, List.map_cons, List.sum_cons]
        ring
      · have h' : ¬ k = g B := fun e => h e.symm
        simp only [List.filter_cons, h, decide_false, Bool.false_eq_true, ↓reduceIte, h', add_zero]
    rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib, Finset.sum_ite_eq' K (g B)]
    simp only [hK B List.mem_cons_self, ↓reduceIte]
    ring

/-- **`lem:record:block-charge`(ii), the consequence**: for a list of blocks (nonempty, of positive
primes with `log p < 𝔲(p)/2⁴⁰`, with `0 < 𝔲(𝔅) ≤ 𝔲_*`), `a ≥ 0` and `d ∈ {2, 3, 4}`,
`∑_𝔅 q_𝔅^{2a} b_𝔅^{-d/2} ≤ ∑_{k=1}^{2¹⁶} exp(2a 𝔲_* k/2⁵⁶) w_d(𝔭, k)/2⁹⁵`,
`w_d(𝔭, k) = ∑_{k_𝔅 = k} w_d(𝔅)`. -/
theorem block_charge_exact (u : ℕ → ℕ) (blocks : List (List ℕ)) {a : ℝ} (ha : 0 ≤ a) {d : ℕ}
    (hd : d = 2 ∨ d = 3 ∨ d = 4) (hne : ∀ B ∈ blocks, B ≠ [])
    (hpos : ∀ B ∈ blocks, ∀ p ∈ B, 0 < p)
    (hlog : ∀ B ∈ blocks, ∀ p ∈ B, Real.log p < (u p : ℝ) / 2 ^ 40)
    (hU : ∀ B ∈ blocks, blockU u B ≤ integerBudget) (hU0 : ∀ B ∈ blocks, 0 < blockU u B) :
    (blocks.map fun B =>
        ((B.prod : ℕ) : ℝ) ^ (2 * a) * ((B.headD 0 : ℕ) : ℝ) ^ (-(d : ℝ) / 2)).sum ≤
      ∑ k ∈ Icc (1 : ℕ) (2 ^ 16), Real.exp (2 * a * integerBudget * (k : ℝ) / 2 ^ 56) *
        (((blocks.filter fun B => blockBin u B = k).map fun B => (wd d (B.headD 0) : ℝ)).sum /
          2 ^ 95) := by
  have hhead : ∀ B ∈ blocks, 0 < B.headD 0 := by
    intro B hB
    obtain ⟨b, B', rfl⟩ := List.exists_cons_of_ne_nil (hne B hB)
    simpa using hpos _ hB b List.mem_cons_self
  have hterm : ∀ B ∈ blocks, ((B.prod : ℕ) : ℝ) ^ (2 * a) * ((B.headD 0 : ℕ) : ℝ) ^ (-(d : ℝ) / 2) ≤
      Real.exp (2 * a * integerBudget * (blockBin u B : ℕ) / 2 ^ 56) *
        ((wd d (B.headD 0) : ℝ) / 2 ^ 95) := by
    intro B hB
    have h1 := (exact_price_le u B ha (hpos B hB) (hlog B hB) (hU B hB)).1
    have h2 := rpow_le_wd hd (hhead B hB)
    exact mul_le_mul h1 h2 (Real.rpow_nonneg (Nat.cast_nonneg _) _) (Real.exp_pos _).le
  have hK : ∀ B ∈ blocks, blockBin u B ∈ Icc 1 (2 ^ 16) := by
    intro B hB
    obtain ⟨h1, h2⟩ := bin_bounds (hU0 B hB) (hU B hB)
    exact mem_Icc.mpr ⟨h1, h2⟩
  have hregroup := list_sum_regroup blocks (blockBin u) (Icc 1 (2 ^ 16)) hK
    (fun k => Real.exp (2 * a * integerBudget * (k : ℝ) / 2 ^ 56))
    (fun B => (wd d (B.headD 0) : ℝ) / 2 ^ 95)
  refine (List.sum_le_sum hterm).trans (le_of_eq ?_)
  rw [hregroup]
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  induction (blocks.filter fun B => blockBin u B = k) with
  | nil => simp
  | cons B l ih => simp only [List.map_cons, List.sum_cons, ih, add_div]

/-! ## V1's greedy blocks -/

/-- **`lem:record:block-charge`(ii) for the exact blocks of a part**: V1's greedy blocks of a
nonempty list `ps` of primes with `log p < 𝔲(p)/2⁴⁰` and `1 ≤ 𝔲(p) ≤ 𝔲_*` (the paper: a single prime
has `𝔲(p) ≤ ⌈2⁴⁰ log X_Ch⌉ < 𝔲_*`). -/
theorem block_charge_greedy (u : ℕ → ℕ) (hu : ∀ p, u p ≤ integerBudget) (ps : List ℕ)
    (hps : ps ≠ []) (hpos : ∀ p ∈ ps, 0 < p) (hu1 : ∀ p ∈ ps, 1 ≤ u p)
    (hlog : ∀ p ∈ ps, Real.log p < (u p : ℝ) / 2 ^ 40) {a : ℝ} (ha : 0 ≤ a) {d : ℕ}
    (hd : d = 2 ∨ d = 3 ∨ d = 4) :
    ((greedyBlocks u integerBudget ps).map fun B =>
        ((B.prod : ℕ) : ℝ) ^ (2 * a) * ((B.headD 0 : ℕ) : ℝ) ^ (-(d : ℝ) / 2)).sum ≤
      ∑ k ∈ Icc (1 : ℕ) (2 ^ 16), Real.exp (2 * a * integerBudget * (k : ℝ) / 2 ^ 56) *
        ((((greedyBlocks u integerBudget ps).filter fun B => blockBin u B = k).map
          fun B => (wd d (B.headD 0) : ℝ)).sum / 2 ^ 95) := by
  have hsub : ∀ B ∈ greedyBlocks u integerBudget ps, ∀ p ∈ B, p ∈ ps := by
    intro B hB p hp
    rw [← greedyBlocks_flatten u integerBudget ps]
    exact List.mem_flatten.mpr ⟨B, hB, hp⟩
  have hne := greedyBlocks_ne_nil u integerBudget hu hps
  apply block_charge_exact u _ ha hd hne
  · exact fun B hB p hp => hpos p (hsub B hB p hp)
  · exact fun B hB p hp => hlog p (hsub B hB p hp)
  · exact greedyBlocks_budget u integerBudget hu ps
  · intro B hB
    obtain ⟨b, B', rfl⟩ := List.exists_cons_of_ne_nil (hne B hB)
    unfold blockU
    simp only [List.map_cons, List.sum_cons]
    have := hu1 b (hsub _ hB b List.mem_cons_self)
    omega

end Sarkozy.Misc
