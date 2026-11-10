module

public import Sarkozy.TraceMixing.Slot
public import Sarkozy.Labellings.TargetBridge

/-!
# Seventy-two vertices of degree at most twenty (`lem:trace-mixing`(d), slot part; (R4))

`paper/sections/12_labellings.tex`, `lem:trace-mixing`(d), the bound for one slot: if
`n = 72` and every degree is at most `20`, then for `q ≥ 2^512` the squared norm of the
conditional operator from one slot on the mean-zero functions is at most `2^22/q`
(`trace_mixing_slot_72`).

The paper takes `w = w_20(p, 72)` and checks the final inequality at `p = 2^512` with a
certificate (`cert:trace-mixing-72`). Here `w = 2^{-22}` is used instead: for `q ≥ 2^512` and
`t ≤ 20` the graded error `e^-_t(71)` is below `2^{-22}` (`lowerErr_72_le`), and the bound
`2/(q-1) · (2^20/(1 - 2^{-22}) - 1) ≤ 2^22/q` is elementary. No certificate is needed.

`isGammaMixing_graphLaw_slot` is the slot half of the mixing hypothesis (R4)
(`it:record:R4`) for graph laws: at every prime `p ≥ 2^512`, assuming Weil's bound
(`Sarkozy.Target.Weil`), the graph law of a graph with `72` vertices and degrees at most `20` is
`(255/1024, v)`-mixing at every slot `v` (`IsGammaMixing`, `def:mixing`).
-/

@[expose] public section

open Finset
open scoped BigOperators Matrix

namespace Sarkozy.TraceMixing

open Sarkozy.Mixing Sarkozy.Labellings

/-- `a_t ≤ (t + 2) 2^t`. -/
theorem gradedA_le (t : ℕ) : gradedA t ≤ (t + 2) * 2 ^ t := by
  unfold gradedA
  split_ifs with ht
  · positivity
  · have h1 : (2 : ℝ) ^ (t - 1) ≤ 2 ^ t := pow_le_pow_right₀ (by norm_num) (Nat.sub_le t 1)
    have h0 : (0 : ℝ) ≤ 2 ^ (t - 1) := by positivity
    have h2 : (1 : ℝ) ≤ 2 ^ t := one_le_pow₀ (by norm_num)
    have ht0 : (0 : ℝ) ≤ t := Nat.cast_nonneg t
    nlinarith

/-- `b_t ≤ 2^t`. -/
theorem gradedB_le (t : ℕ) : gradedB t ≤ 2 ^ t := by
  unfold gradedB
  split_ifs with ht
  · positivity
  · have h1 : (2 : ℝ) ^ (t - 1) ≤ 2 ^ t := pow_le_pow_right₀ (by norm_num) (Nat.sub_le t 1)
    linarith

/-- For `q ≥ 2^512` and `t ≤ 20`, `e^-_t(71) ≤ 2^{-22}`. -/
theorem lowerErr_72_le {q : ℝ} (hq : 2 ^ 512 ≤ q) {t : ℕ} (ht : t ≤ 20) :
    lowerErr q t 71 ≤ 1 / 2 ^ 22 := by
  have hq0 : 0 < q := lt_of_lt_of_le (by positivity) hq
  set s := Real.sqrt q with hs
  have hss : s * s = q := Real.mul_self_sqrt hq0.le
  have hs256 : (2 : ℝ) ^ 256 ≤ s := by
    rw [hs, Real.le_sqrt (by positivity) hq0.le]
    calc ((2 : ℝ) ^ 256) ^ 2 = 2 ^ 512 := by rw [← pow_mul]
      _ ≤ q := hq
  have hs0 : 0 ≤ s := Real.sqrt_nonneg q
  have hpow : (2 : ℝ) ^ t ≤ 2 ^ 20 := pow_le_pow_right₀ (by norm_num) ht
  have htR : (t : ℝ) ≤ 20 := by exact_mod_cast ht
  have hA : gradedA t ≤ 22 * 2 ^ 20 := by
    have := gradedA_le t
    have h2 : (0 : ℝ) ≤ 2 ^ t := by positivity
    nlinarith only [this, h2, hpow, htR]
  have hB : gradedB t ≤ 2 ^ 20 := (gradedB_le t).trans hpow
  have hA0 : 0 ≤ gradedA t := gradedA_nonneg t
  unfold lowerErr softError
  rw [div_le_iff₀ hq0, ← hs, ← hss]
  have hnum : gradedA t * s + gradedB t + 2 ^ t * ((71 : ℕ) : ℝ) ≤
      22 * 2 ^ 20 * s + 72 * 2 ^ 20 := by
    push_cast
    nlinarith only [hA, hB, hpow, hs0, hA0]
  have hs60 : (2 : ℝ) ^ 60 ≤ s := le_trans (pow_le_pow_right₀ (by norm_num) (by norm_num)) hs256
  clear hs256 hq
  have hs1 : (1 : ℝ) ≤ s := le_trans (one_le_pow₀ (by norm_num)) hs60
  have h1 : (2 : ℝ) ^ 60 * s ≤ s * s := mul_le_mul_of_nonneg_right hs60 hs0
  have hbig : 22 * 2 ^ 20 * s + 72 * 2 ^ 20 ≤ 1 / 2 ^ 22 * (s * s) := by
    have h2 : 1 / 2 ^ 22 * ((2 : ℝ) ^ 60 * s) ≤ 1 / 2 ^ 22 * (s * s) :=
      mul_le_mul_of_nonneg_left h1 (by norm_num)
    have h3 : 1 / 2 ^ 22 * ((2 : ℝ) ^ 60 * s) = 2 ^ 38 * s := by ring
    have h4 : 22 * 2 ^ 20 * s + 72 * 2 ^ 20 ≤ (2 : ℝ) ^ 38 * s := by
      linarith only [hs1]
    linarith only [h2, h3, h4]
  exact hnum.trans hbig

/-- **`lem:trace-mixing`(d), one slot.** For a graph with `72` vertices, a vertex `v` of degree
at most `20` and `q ≥ 2^512`: `‖T f‖² ≤ (2^22/q) ‖f‖²` for every `f` with `E f = 0`. -/
theorem trace_mixing_slot_72 {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    {W : Type*} [Fintype W] [DecidableEq W] (hW : WeilBound F) (hF : ringChar F ≠ 2)
    (G : OrientedGraph W) (hne : (injLabellings F G).Nonempty) (hn : Fintype.card W = 72)
    (v : W) (hdeg : degree G v ≤ 20) (hq : (2 : ℝ) ^ 512 ≤ Fintype.card F)
    (f : F → ℝ) (hf : ∑ x, f x = 0) :
    ∑ b, tgtWeight (slotJoint (graphLaw G hne) v) b *
        condOp (slotJoint (graphLaw G hne) v) f b ^ 2 ≤
      2 ^ 22 / (Fintype.card F : ℝ) * (FiniteLaw.uniform F).expect (fun x => f x ^ 2) := by
  have hw : lowerErr (Fintype.card F) (degree G v) (Fintype.card W - 1) ≤ 1 / 2 ^ 22 := by
    rw [hn]
    exact lowerErr_72_le hq hdeg
  have h := trace_mixing_slot_graded hW hF G hne v (by norm_num) hw f hf
  have hE : 0 ≤ (FiniteLaw.uniform F).expect (fun x => f x ^ 2) :=
    (FiniteLaw.uniform F).expect_nonneg (fun x => sq_nonneg _)
  refine h.trans (mul_le_mul_of_nonneg_right ?_ hE)
  have h2512 : (2 : ℝ) ≤ 2 ^ 512 := le_self_pow₀ (by norm_num) (by norm_num)
  have hq1 : (2 : ℝ) ≤ Fintype.card F := le_trans h2512 hq
  clear h2512 hq hw h
  have hpow : (2 : ℝ) ^ degree G v ≤ 2 ^ 20 := pow_le_pow_right₀ (by norm_num) hdeg
  have hfrac : (2 : ℝ) ^ degree G v / (1 - 1 / 2 ^ 22) - 1 ≤ 2 ^ 20 := by
    have h1 : (2 : ℝ) ^ degree G v / (1 - 1 / 2 ^ 22) ≤ 2 ^ 20 / (1 - 1 / 2 ^ 22) :=
      div_le_div_of_nonneg_right hpow (by norm_num)
    have h2 : (2 : ℝ) ^ 20 / (1 - 1 / 2 ^ 22) - 1 ≤ 2 ^ 20 := by norm_num
    linarith
  have hq0 : (0 : ℝ) < (Fintype.card F : ℝ) - 1 := by linarith
  have hcoef : 0 ≤ 2 / ((Fintype.card F : ℝ) - 1) := div_nonneg (by norm_num) hq0.le
  calc 2 / ((Fintype.card F : ℝ) - 1) * ((2 : ℝ) ^ degree G v / (1 - 1 / 2 ^ 22) - 1)
      ≤ 2 / ((Fintype.card F : ℝ) - 1) * 2 ^ 20 := mul_le_mul_of_nonneg_left hfrac hcoef
    _ ≤ 2 ^ 22 / (Fintype.card F : ℝ) := by
        rw [div_mul_eq_mul_div, div_le_div_iff₀ hq0 (by linarith)]
        nlinarith

/-- **(R4) for graph laws, one slot.** Assume Weil's bound (`Sarkozy.Target.Weil`). For a
prime `p ≥ 2^512` and a graph with `72` vertices and all degrees at most `20`, the graph law
`λ_p(G)` is `(255/1024, v)`-mixing at every slot `v` (`def:mixing`). -/
theorem isGammaMixing_graphLaw_slot (hWeil : Target.Weil) (p : ℕ) [Fact p.Prime]
    (hp : (2 : ℝ) ^ 512 ≤ p) {W : Type*} [Fintype W] [DecidableEq W] (G : OrientedGraph W)
    (hn : Fintype.card W = 72) (hdeg : ∀ v, degree G v ≤ 20)
    (hne : (injLabellings (ZMod p) G).Nonempty) (v : W) :
    IsGammaMixing p (255 / 1024) (graphLaw G hne) {v} := by
  have h2512 : (2 : ℝ) < 2 ^ 512 := lt_self_pow₀ (by norm_num) (by norm_num)
  have hp2R : (2 : ℝ) < p := lt_of_lt_of_le h2512 hp
  have hp2 : p ≠ 2 := by
    intro h
    rw [h] at hp2R
    push_cast at hp2R
    exact lt_irrefl _ hp2R
  have hW := weilBound_of_target hWeil p hp2
  have hF : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  have hcard : (Fintype.card (ZMod p) : ℝ) = p := by rw [ZMod.card]
  have hp0 : (0 : ℝ) < p := by linarith only [hp2R]
  have hp1 : (1 : ℝ) ≤ p := by linarith only [hp2R]
  have hsqrt : (2 : ℝ) ^ 256 ≤ Real.sqrt p := by
    rw [Real.le_sqrt (by positivity) hp0.le]
    calc ((2 : ℝ) ^ 256) ^ 2 = (2 : ℝ) ^ 512 := by rw [← pow_mul]
      _ ≤ (p : ℝ) := hp
  have hlow : lowerErr (Fintype.card (ZMod p)) (degree G v) (Fintype.card W - 1) ≤ 1 / 2 ^ 22 := by
    rw [hn, hcard]
    exact lowerErr_72_le hp (hdeg v)
  have h22 : (2 : ℝ) ^ 22 ≤ Real.sqrt p :=
    le_trans (pow_le_pow_right₀ (by norm_num) (by norm_num)) hsqrt
  clear hsqrt hp h2512
  unfold IsGammaMixing
  apply isMixing_graphLaw_slot hW hF G hne v (w := 1 / 2 ^ 22) (by norm_num) hlow
  -- `2/(p-1) (2^d/(1 - 2^{-22}) - 1) ≤ 2^22/p ≤ p^{-255/512}`
  have hpow : (2 : ℝ) ^ degree G v ≤ 2 ^ 20 := pow_le_pow_right₀ (by norm_num) (hdeg v)
  have hfrac : (2 : ℝ) ^ degree G v / (1 - 1 / 2 ^ 22) - 1 ≤ 2 ^ 20 := by
    have h1 : (2 : ℝ) ^ degree G v / (1 - 1 / 2 ^ 22) ≤ 2 ^ 20 / (1 - 1 / 2 ^ 22) :=
      div_le_div_of_nonneg_right hpow (by norm_num)
    have h2 : (2 : ℝ) ^ 20 / (1 - 1 / 2 ^ 22) - 1 ≤ 2 ^ 20 := by norm_num
    linarith only [h1, h2]
  rw [hcard]
  have hq0 : (0 : ℝ) < (p : ℝ) - 1 := by linarith only [hp2R]
  have hcoef : 0 ≤ 2 / ((p : ℝ) - 1) := div_nonneg (by norm_num) hq0.le
  have hstep1 : 2 / ((p : ℝ) - 1) * ((2 : ℝ) ^ degree G v / (1 - 1 / 2 ^ 22) - 1) ≤
      2 ^ 22 / (p : ℝ) := by
    calc 2 / ((p : ℝ) - 1) * ((2 : ℝ) ^ degree G v / (1 - 1 / 2 ^ 22) - 1)
        ≤ 2 / ((p : ℝ) - 1) * 2 ^ 20 := mul_le_mul_of_nonneg_left hfrac hcoef
      _ ≤ 2 ^ 22 / (p : ℝ) := by
          rw [div_mul_eq_mul_div, div_le_div_iff₀ hq0 hp0]
          nlinarith only [hp2R]
  -- `(p^{-255/1024})² = p^{-255/512} ≥ 2^22/p`
  have hsq : ((p : ℝ) ^ (-(255 / 1024 : ℝ))) ^ 2 = (p : ℝ) ^ (-(255 / 512 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hp0.le]
    norm_num
  have hhalf : Real.sqrt p ≤ (p : ℝ) ^ (257 / 512 : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hp1 (by norm_num)
  have hsplit : (p : ℝ) ^ (-(255 / 512 : ℝ)) = (p : ℝ) ^ (257 / 512 : ℝ) / p := by
    rw [show (-(255 / 512 : ℝ)) = (257 / 512 : ℝ) - 1 by norm_num, Real.rpow_sub hp0,
      Real.rpow_one]
  have hstep2 : 2 ^ 22 / (p : ℝ) ≤ (p : ℝ) ^ (-(255 / 512 : ℝ)) := by
    rw [hsplit]
    exact div_le_div_of_nonneg_right (h22.trans hhalf) hp0.le
  rw [hsq]
  exact hstep1.trans hstep2

end Sarkozy.TraceMixing
