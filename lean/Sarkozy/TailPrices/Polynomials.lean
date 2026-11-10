module

public import Sarkozy.TailPrices.Sums
public import Sarkozy.PartV.UpperReference

@[expose] public section

/-!
# The tail price polynomials and the per-prime bound (`lem:tail-prices`(ii),(iii))

`paper/sections/27_tail_index.tex`, `eq:tail-polynomials` and `lem:tail-prices`. At a tail prime
`p ≥ P₄`, `r = p^{-1/2}`, the tail comparison law has prices
`s_p ≤ (Π^{rep} + Π^{del})(r) p^{2a}` and `a_p ≤ Π^{rep}(r) p^{2a}` (`lem:tail-prices`(ii)), with

* `Π^{rep}(r) = c^{rep}_3 r³ + c^{rep}_4 r⁴`, `c^{rep}_3 = 73056854152246473/12500000000`,
  `c^{rep}_4 = 149151332035400049/68359375`;
* `Π^{del}(r) = ∑_{d=3}^7 c^{del}_d r^d`, `c^{del}_3 = 81606792/25` and `c^{del}_d = c_d`
  (`def:tail-law`) for `4 ≤ d ≤ 7`.

This file proves (`lem:tail-prices`(iii) in a sharpened, split form):

* `tailR_le`: `r = p^{-1/2} ≤ 2^{-256}` at `p ≥ P₄`;
* `piS_le`, `piA_le`: `(Π^{rep} + Π^{del})(r) ≤ k_S r³` and `Π^{rep}(r) ≤ k_A r³` for
  `0 ≤ r ≤ 2^{-256}`, with `k_S = 9108821`, `k_A = 5844549` (`c^{rep}_3 + c^{del}_3 = 9108820.012…`,
  `c^{rep}_3 = 5844548.332…`);
* `cube_mul_rpow`: `r³ p^{2a} = p^{-(3/2 - 2a)}`;
* **`price_le_of_poly`**: a price whose unpriced total is at most `Π(r)` is at most
  `k p^{-(3/2 - 2a)}` after the factor `p^{2a}`. With `k_S + k_A = 14953370`, this is
  `η_p ≤ C_tail p^{-3/2+2a}` of (iii) (`C_tail = 1.4953…·10⁷`).
-/

open Finset
open scoped BigOperators

namespace Sarkozy.TailPrices

/-- `c^{rep}_3` (`eq:tail-polynomials`). -/
noncomputable def cRep3 : ℝ := 73056854152246473 / 12500000000
/-- `c^{rep}_4` (`eq:tail-polynomials`). -/
noncomputable def cRep4 : ℝ := 149151332035400049 / 68359375
/-- `c^{del}_3` (`eq:tail-polynomials`). -/
noncomputable def cDel3 : ℝ := 81606792 / 25
/-- `c^{del}_4 = c_4` (`def:tail-law`; every record of degree at least four is deleted). -/
noncomputable def cDel4 : ℝ := 50638290432 / 5
/-- `c^{del}_5 = c_5` (`def:tail-law`). -/
noncomputable def cDel5 : ℝ := 621170191872 / 5
/-- `c^{del}_6 = c_6` (`def:tail-law`). -/
noncomputable def cDel6 : ℝ := 1877429977088 / 7
/-- `c^{del}_7 = c_7` (`def:tail-law`). -/
noncomputable def cDel7 : ℝ := 970455252992 / 7

/-- **`Π^{rep}(r) = c^{rep}_3 r³ + c^{rep}_4 r⁴`** (`eq:tail-polynomials`). -/
noncomputable def piRep (r : ℝ) : ℝ := cRep3 * r ^ 3 + cRep4 * r ^ 4

/-- **`Π^{del}(r) = ∑_{d=3}^7 c^{del}_d r^d`** (`eq:tail-polynomials`). -/
noncomputable def piDel (r : ℝ) : ℝ :=
  cDel3 * r ^ 3 + cDel4 * r ^ 4 + cDel5 * r ^ 5 + cDel6 * r ^ 6 + cDel7 * r ^ 7

/-- The constant `k_S` of the symmetric tail price, `k_S ≥ c^{rep}_3 + c^{del}_3 + O(2^{-256})`. -/
noncomputable def kS : ℝ := 9108821

/-- The constant `k_A` of the skew tail price, `k_A ≥ c^{rep}_3 + O(2^{-256})`. -/
noncomputable def kA : ℝ := 5844549

theorem kS_nonneg : 0 ≤ kS := by unfold kS; norm_num

theorem kA_nonneg : 0 ≤ kA := by unfold kA; norm_num

theorem P4_pos : 0 < PartV.P4 := by
  unfold PartV.P4
  exact pow_pos (by norm_num) _

/-- `r = p^{-1/2} ≤ 2^{-256}` at every `p ≥ P₄ = 2^{512}`. -/
theorem tailR_le {q : ℕ} (hq : PartV.P4 ≤ q) : PartV.tailR q ≤ 1 / 2 ^ 256 := by
  have hP : (0 : ℝ) < PartV.P4 := Nat.cast_pos.mpr P4_pos
  have h := Real.rpow_le_rpow_of_nonpos hP (Nat.cast_le.mpr hq) (by norm_num : -(1 / 2 : ℝ) ≤ 0)
  unfold PartV.tailR
  refine h.trans (le_of_eq ?_)
  rw [P4_rpow, show (512 * (1 / 2 : ℝ)) = ((256 : ℕ) : ℝ) by norm_num, two_rpow_neg_nat]

/-- `r^k ≤ r` for `0 ≤ r ≤ 1`, `k ≥ 1`, in the form used below. -/
theorem pow_le_self' {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1) {k : ℕ} (hk : k ≠ 0) : r ^ k ≤ r :=
  pow_le_of_le_one h0 h1 hk

/-- **`(Π^{rep} + Π^{del})(r) ≤ k_S r³`** for `0 ≤ r ≤ 2^{-256}`. -/
theorem piS_le {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1 / 2 ^ 256) : piRep r + piDel r ≤ kS * r ^ 3 := by
  have hr1 : r ≤ 1 := h1.trans (by norm_num)
  have e : piRep r + piDel r = r ^ 3 * ((cRep3 + cDel3) +
      ((cRep4 + cDel4) * r + cDel5 * r ^ 2 + cDel6 * r ^ 3 + cDel7 * r ^ 4)) := by
    unfold piRep piDel
    ring
  have hb : (cRep4 + cDel4) * r + cDel5 * r ^ 2 + cDel6 * r ^ 3 + cDel7 * r ^ 4 ≤
      (cRep4 + cDel4 + cDel5 + cDel6 + cDel7) * (1 / 2 ^ 256) := by
    have h2 := pow_le_self' h0 hr1 (k := 2) (by norm_num)
    have h3 := pow_le_self' h0 hr1 (k := 3) (by norm_num)
    have h4 := pow_le_self' h0 hr1 (k := 4) (by norm_num)
    unfold cRep4 cDel4 cDel5 cDel6 cDel7
    nlinarith
  have hc : (cRep3 + cDel3) + (cRep4 + cDel4 + cDel5 + cDel6 + cDel7) * (1 / 2 ^ 256) ≤ kS := by
    unfold cRep3 cDel3 cRep4 cDel4 cDel5 cDel6 cDel7 kS
    norm_num
  rw [e, mul_comm kS]
  exact mul_le_mul_of_nonneg_left (by linarith) (pow_nonneg h0 3)

/-- **`Π^{rep}(r) ≤ k_A r³`** for `0 ≤ r ≤ 2^{-256}`. -/
theorem piA_le {r : ℝ} (h0 : 0 ≤ r) (h1 : r ≤ 1 / 2 ^ 256) : piRep r ≤ kA * r ^ 3 := by
  have hr1 : r ≤ 1 := h1.trans (by norm_num)
  have e : piRep r = r ^ 3 * (cRep3 + cRep4 * r) := by
    unfold piRep
    ring
  have hb : cRep4 * r ≤ cRep4 * (1 / 2 ^ 256) := by
    unfold cRep4
    nlinarith
  have hc : cRep3 + cRep4 * (1 / 2 ^ 256) ≤ kA := by
    unfold cRep3 cRep4 kA
    norm_num
  rw [e, mul_comm kA]
  exact mul_le_mul_of_nonneg_left (by linarith) (pow_nonneg h0 3)

/-- `r³ p^{2a} = p^{-(3/2 - 2a)}` with `r = p^{-1/2}`, written `p^{-((1/2 - 2a) + 1)}`. -/
theorem cube_mul_rpow {q : ℕ} (hq : 0 < q) (a : ℝ) :
    PartV.tailR q ^ 3 * (q : ℝ) ^ (2 * a) = (q : ℝ) ^ (-((1 / 2 - 2 * a) + 1)) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  unfold PartV.tailR
  rw [← Real.rpow_mul_natCast hq0.le, ← Real.rpow_add hq0]
  congr 1
  push_cast
  ring

/-- **The per-prime price bound** (`lem:tail-prices`(iii), split): at `p ≥ P₄`, if the unpriced
total `S` is at most `Π(r)` and `Π(r) ≤ k r³` for `0 ≤ r ≤ 2^{-256}`, then
`S p^{2a} ≤ k p^{-(3/2 - 2a)}`. -/
theorem price_le_of_poly {q : ℕ} (hq : PartV.P4 ≤ q) (a : ℝ) {S k : ℝ} (F : ℝ → ℝ)
    (hF : ∀ r, 0 ≤ r → r ≤ 1 / 2 ^ 256 → F r ≤ k * r ^ 3) (hS : S ≤ F (PartV.tailR q)) :
    S * (q : ℝ) ^ (2 * a) ≤ k * (q : ℝ) ^ (-((1 / 2 - 2 * a) + 1)) := by
  have hq0 : 0 < q := lt_of_lt_of_le P4_pos hq
  have hpos : 0 ≤ (q : ℝ) ^ (2 * a) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  rw [← cube_mul_rpow hq0, ← mul_assoc]
  exact mul_le_mul_of_nonneg_right
    (hS.trans (hF _ (PartV.tailR_nonneg q) (tailR_le hq))) hpos

/-- **`s_p ≤ k_S p^{-(3/2-2a)}`** from `lem:tail-prices`(ii)'s symmetric bound. -/
theorem sym_price_le {q : ℕ} (hq : PartV.P4 ≤ q) (a : ℝ) {S : ℝ}
    (hS : S ≤ piRep (PartV.tailR q) + piDel (PartV.tailR q)) :
    S * (q : ℝ) ^ (2 * a) ≤ kS * (q : ℝ) ^ (-((1 / 2 - 2 * a) + 1)) :=
  price_le_of_poly hq a (fun r => piRep r + piDel r) (fun _ h0 h1 => piS_le h0 h1) hS

/-- **`a_p ≤ k_A p^{-(3/2-2a)}`** from `lem:tail-prices`(ii)'s skew bound. -/
theorem skew_price_le {q : ℕ} (hq : PartV.P4 ≤ q) (a : ℝ) {S : ℝ}
    (hS : S ≤ piRep (PartV.tailR q)) :
    S * (q : ℝ) ^ (2 * a) ≤ kA * (q : ℝ) ^ (-((1 / 2 - 2 * a) + 1)) :=
  price_le_of_poly hq a piRep (fun _ h0 h1 => piA_le h0 h1) hS

/-- **`lem:tail-prices`(iii)**: `η_p = s_p + a_p ≤ C p^{-3/2+2a}` with `C = k_S + k_A = 14953370`
(the paper's `C_tail = 1.4953…·10⁷`). -/
theorem eta_le {q : ℕ} (hq : PartV.P4 ≤ q) (a : ℝ) {S A : ℝ}
    (hS : S ≤ piRep (PartV.tailR q) + piDel (PartV.tailR q)) (hA : A ≤ piRep (PartV.tailR q)) :
    S * (q : ℝ) ^ (2 * a) + A * (q : ℝ) ^ (2 * a) ≤
      (kS + kA) * (q : ℝ) ^ (-((1 / 2 - 2 * a) + 1)) := by
  have h1 := sym_price_le hq a hS
  have h2 := skew_price_le hq a hA
  linarith

theorem kS_add_kA : kS + kA = 14953370 := by unfold kS kA; norm_num

end Sarkozy.TailPrices
