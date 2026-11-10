module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.SpecialFunctions.Pow.Real

@[expose] public section

/-!
# The invariant split of the outside law (`lem:oct24:invariant-background`(v))

`paper/sections/23_envelopes.tex`, `lem:oct24:invariant-background`(v), the "consequently" clause:
if `0 ≤ κ_b ≤ κ_H` and an outside polynomial has the coefficient `κ_b` on the monomials whose middle
factors are all `μ` or invariant tags and `κ_H` on all others, its completed value is at most
`κ_H e^{U_0} - (κ_H - κ_b) e^{t U_inv}` for every `U_0 ≥ t(U_inv + ∑_i u^G_i)`.

**Form.** After the expansion in the positive tags, the polynomial over the middle blocks `𝔅` is
`κ_H ∏_𝔅 (1 + v_𝔅 + w_𝔅) - (κ_H - κ_b) ∏_𝔅 (1 + v_𝔅)`, with `v_𝔅`, `w_𝔅` the prices of the
invariant and of the generic tag (`backgroundPoly`). The chosen upper prices `m_𝔅 ≥ v_𝔅`,
`n_𝔅 ≥ w_𝔅` (part (iii) of the record-expansion lemma of Part III) sum to `∑ m = t U_inv` and
`∑ (m + n) = t(U_inv + ∑ u^G) ≤ U_0`; they are hypotheses here, as is the identification of the
energy with the polynomial. Selected blocks are included with `v = w = 0` (the paper: "which only
increases when the selected blocks are included").

**Main results.**
* `prod_sub_prod_le_exp`: `∏(1 + v + w) - ∏(1 + v) ≤ e^{∑(m+n)} - e^{∑ m}` for
  `0 ≤ v ≤ m`, `0 ≤ w ≤ n` (the chosen-tag-price form of `rem:completion-subtraction`; this file
  proves the last paragraph of that remark, not its first two);
* `backgroundPoly_le`: the completed value bound at chosen upper prices;
* `backgroundPoly_le_of_sums`: the same from the price sums, the chosen prices being constructed;
* `backgroundCost_mono`: the bound is nondecreasing in `κ_H` and `κ_b` (`thm:envelopes`(iii)).
-/

namespace Sarkozy.Envelopes

open Finset

/-- The outside polynomial `κ_H ∏(1 + v + w) - (κ_H - κ_b) ∏(1 + v)`. -/
noncomputable def backgroundPoly {ι : Type*} (s : Finset ι) (κH κb : ℝ) (v w : ι → ℝ) : ℝ :=
  κH * ∏ i ∈ s, (1 + v i + w i) - (κH - κb) * ∏ i ∈ s, (1 + v i)

theorem prod_one_add_le_exp_sum {ι : Type*} (s : Finset ι) (x : ι → ℝ)
    (hx : ∀ i ∈ s, 0 ≤ x i) : ∏ i ∈ s, (1 + x i) ≤ Real.exp (∑ i ∈ s, x i) := by
  rw [Real.exp_sum]
  refine prod_le_prod₀ (fun i hi => by linarith [hx i hi]) fun i _ => ?_
  have := Real.add_one_le_exp (x i)
  linarith

/-- **The chosen-tag-price comparison** (`rem:completion-subtraction`, used in
`lem:oct24:invariant-background`(v) and `lem:orbit-coupon`): for `0 ≤ v ≤ m` and `0 ≤ w ≤ n`,
`∏(1 + v + w) - ∏(1 + v) ≤ e^{∑(m + n)} - e^{∑ m}`, together with the two product bounds. -/
theorem prod_sub_prod_le_exp {ι : Type*} [DecidableEq ι] (s : Finset ι) (v w m n : ι → ℝ)
    (hv : ∀ i ∈ s, 0 ≤ v i) (hw : ∀ i ∈ s, 0 ≤ w i) (hvm : ∀ i ∈ s, v i ≤ m i)
    (hwn : ∀ i ∈ s, w i ≤ n i) :
    ∏ i ∈ s, (1 + v i + w i) - ∏ i ∈ s, (1 + v i) ≤
        Real.exp (∑ i ∈ s, (m i + n i)) - Real.exp (∑ i ∈ s, m i) ∧
      ∏ i ∈ s, (1 + v i) ≤ ∏ i ∈ s, (1 + v i + w i) ∧
      ∏ i ∈ s, (1 + v i + w i) ≤ Real.exp (∑ i ∈ s, (m i + n i)) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hv' : ∀ i ∈ s, 0 ≤ v i := fun i hi => hv i (mem_insert_of_mem hi)
    have hw' : ∀ i ∈ s, 0 ≤ w i := fun i hi => hw i (mem_insert_of_mem hi)
    have hvm' : ∀ i ∈ s, v i ≤ m i := fun i hi => hvm i (mem_insert_of_mem hi)
    have hwn' : ∀ i ∈ s, w i ≤ n i := fun i hi => hwn i (mem_insert_of_mem hi)
    obtain ⟨h1, h2, h3⟩ := ih hv' hw' hvm' hwn'
    have hva := hv a (mem_insert_self a s)
    have hwa := hw a (mem_insert_self a s)
    have hvma := hvm a (mem_insert_self a s)
    have hwna := hwn a (mem_insert_self a s)
    rw [prod_insert ha, prod_insert ha, sum_insert ha, sum_insert ha,
      Real.exp_add (m a + n a), Real.exp_add (m a) (∑ i ∈ s, m i)]
    set A := ∏ i ∈ s, (1 + v i + w i)
    set B := ∏ i ∈ s, (1 + v i)
    set A' := Real.exp (∑ i ∈ s, (m i + n i))
    set B' := Real.exp (∑ i ∈ s, m i)
    have hB0 : 0 ≤ B := prod_nonneg fun i hi => by linarith [hv' i hi]
    have hAB : 0 ≤ A - B := by linarith
    have hem : 1 + m a ≤ Real.exp (m a) := by have := Real.add_one_le_exp (m a); linarith
    have hm0 : 0 ≤ m a := hva.trans hvma
    have hn0 : 0 ≤ n a := hwa.trans hwna
    have hen : 1 + n a ≤ Real.exp (n a) := by have := Real.add_one_le_exp (n a); linarith
    have hem1 : 1 ≤ Real.exp (m a) := Real.one_le_exp hm0
    have hemn : Real.exp (m a + n a) = Real.exp (m a) * Real.exp (n a) := Real.exp_add _ _
    refine ⟨?_, ?_, ?_⟩
    · -- `(1+v)(A - B) + w A ≤ e^m (A' - B') + (e^{m+n} - e^m) A'`
      have e1 : (1 + v a + w a) * A - (1 + v a) * B = (1 + v a) * (A - B) + w a * A := by ring
      have e2 : Real.exp (m a + n a) * A' - Real.exp (m a) * B' =
          Real.exp (m a) * (A' - B') + (Real.exp (m a + n a) - Real.exp (m a)) * A' := by ring
      rw [e1, e2]
      have k1 : (1 + v a) * (A - B) ≤ Real.exp (m a) * (A' - B') :=
        mul_le_mul (by linarith) h1 hAB (by positivity)
      have k2 : w a ≤ Real.exp (m a + n a) - Real.exp (m a) := by
        rw [hemn]
        nlinarith
      have k3 : w a * A ≤ (Real.exp (m a + n a) - Real.exp (m a)) * A' :=
        mul_le_mul k2 h3 (by linarith) (by linarith)
      linarith
    · exact mul_le_mul (by linarith) h2 hB0 (by linarith)
    · have : 1 + v a + w a ≤ Real.exp (m a + n a) := by
        rw [hemn]; nlinarith
      exact mul_le_mul this h3 (hB0.trans h2) (by positivity)

/-- **`lem:oct24:invariant-background`(v), the completed value.** Let `0 ≤ κ_b ≤ κ_H`, let
`0 ≤ v ≤ m` and `0 ≤ w ≤ n` be the actual and the chosen upper prices of the invariant and the
generic tags, with `∑ m = t U_inv` and `∑ (m + n) ≤ U_0`. Then
`κ_H ∏(1 + v + w) - (κ_H - κ_b) ∏(1 + v) ≤ κ_H e^{U_0} - (κ_H - κ_b) e^{t U_inv}`. -/
theorem backgroundPoly_le {ι : Type*} [DecidableEq ι] (s : Finset ι) {κH κb U0 tU : ℝ}
    (hκb : 0 ≤ κb) (hκ : κb ≤ κH) (v w m n : ι → ℝ)
    (hv : ∀ i ∈ s, 0 ≤ v i) (hw : ∀ i ∈ s, 0 ≤ w i) (hvm : ∀ i ∈ s, v i ≤ m i)
    (hwn : ∀ i ∈ s, w i ≤ n i) (hm : ∑ i ∈ s, m i = tU) (hU : ∑ i ∈ s, (m i + n i) ≤ U0) :
    backgroundPoly s κH κb v w ≤ κH * Real.exp U0 - (κH - κb) * Real.exp tU := by
  obtain ⟨h1, -, -⟩ := prod_sub_prod_le_exp s v w m n hv hw hvm hwn
  have h4 := prod_one_add_le_exp_sum s v hv
  have h5 : Real.exp (∑ i ∈ s, v i) ≤ Real.exp tU := by
    rw [Real.exp_le_exp, ← hm]
    exact sum_le_sum hvm
  have h6 : Real.exp (∑ i ∈ s, (m i + n i)) ≤ Real.exp U0 := Real.exp_le_exp.2 hU
  rw [hm] at h1
  have hκH : 0 ≤ κH := hκb.trans hκ
  unfold backgroundPoly
  have e : κH * ∏ i ∈ s, (1 + v i + w i) - (κH - κb) * ∏ i ∈ s, (1 + v i) =
      κH * (∏ i ∈ s, (1 + v i + w i) - ∏ i ∈ s, (1 + v i)) + κb * ∏ i ∈ s, (1 + v i) := by
    ring
  rw [e]
  have k1 : κH * (∏ i ∈ s, (1 + v i + w i) - ∏ i ∈ s, (1 + v i)) ≤
      κH * (Real.exp U0 - Real.exp tU) :=
    mul_le_mul_of_nonneg_left (by linarith) hκH
  have k2 : κb * ∏ i ∈ s, (1 + v i) ≤ κb * Real.exp tU :=
    mul_le_mul_of_nonneg_left (h4.trans h5) hκb
  linarith

/-- **`lem:oct24:invariant-background`(v), from the price sums.** The chosen upper prices exist:
on a nonempty set of blocks, if the actual prices satisfy `∑ v ≤ t U_inv` and
`t U_inv + ∑ w ≤ U_0` (in the paper `∑ w ≤ t ∑_i u^G_i` and `U_0 ≥ t(U_inv + ∑_i u^G_i)`), then
`κ_H ∏(1 + v + w) - (κ_H - κ_b) ∏(1 + v) ≤ κ_H e^{U_0} - (κ_H - κ_b) e^{t U_inv}`. The upper prices
are `m = v` plus the slack `t U_inv - ∑ v` at one block, and `n = w`. -/
theorem backgroundPoly_le_of_sums {ι : Type*} [DecidableEq ι] (s : Finset ι) (hs : s.Nonempty)
    {κH κb U0 tU : ℝ} (hκb : 0 ≤ κb) (hκ : κb ≤ κH) (v w : ι → ℝ)
    (hv : ∀ i ∈ s, 0 ≤ v i) (hw : ∀ i ∈ s, 0 ≤ w i) (hsv : ∑ i ∈ s, v i ≤ tU)
    (hsw : tU + ∑ i ∈ s, w i ≤ U0) :
    backgroundPoly s κH κb v w ≤ κH * Real.exp U0 - (κH - κb) * Real.exp tU := by
  obtain ⟨a, ha⟩ := hs
  set slack := tU - ∑ i ∈ s, v i
  have hslack : 0 ≤ slack := by simp only [slack]; linarith
  let m : ι → ℝ := fun i => v i + if i = a then slack else 0
  have hvm : ∀ i ∈ s, v i ≤ m i := by
    intro i _
    simp only [m]
    split_ifs <;> linarith
  have hm : ∑ i ∈ s, m i = tU := by
    simp only [m, sum_add_distrib, sum_ite_eq', ha, ↓reduceIte, slack]
    ring
  have hU : ∑ i ∈ s, (m i + w i) ≤ U0 := by
    rw [sum_add_distrib, hm]; exact hsw
  exact backgroundPoly_le s hκb hκ v w m w hv hw hvm (fun i _ => le_rfl) hm hU

/-- The outside cost `κ_H e^{U_0} - (κ_H - κ_b) e^{t U_inv}` (`eq:envelope-background`). -/
noncomputable def backgroundCost (κH κb U0 tU : ℝ) : ℝ :=
  κH * Real.exp U0 - (κH - κb) * Real.exp tU

/-- **`thm:envelopes`(iii), monotonicity of the background cost.** For `t U_inv ≤ U_0` the cost is
nondecreasing in `κ_H` (derivative `e^{U_0} - e^{t U_inv} ≥ 0`), in `κ_b` (derivative
`e^{t U_inv}`), and, for `κ_H ≥ 0`, in `U_0`; and it is at least `κ_b e^{t U_inv}`. -/
theorem backgroundCost_mono {κH κH' κb κb' U0 U0' tU : ℝ} (hU : tU ≤ U0) (hH : κH ≤ κH')
    (hb : κb ≤ κb') (hU' : U0 ≤ U0') (hκH : 0 ≤ κH) :
    backgroundCost κH κb U0 tU ≤ backgroundCost κH' κb' U0' tU ∧
      κb * Real.exp tU ≤ backgroundCost κH κb U0 tU := by
  unfold backgroundCost
  have e1 : Real.exp tU ≤ Real.exp U0 := Real.exp_le_exp.2 hU
  have e2 : Real.exp U0 ≤ Real.exp U0' := Real.exp_le_exp.2 hU'
  have hpos : 0 < Real.exp tU := Real.exp_pos _
  refine ⟨?_, ?_⟩
  · have k1 : κH * Real.exp U0 ≤ κH * Real.exp U0' := mul_le_mul_of_nonneg_left e2 hκH
    have k2 : (κH' - κH) * Real.exp tU ≤ (κH' - κH) * Real.exp U0' :=
      mul_le_mul_of_nonneg_left (e1.trans e2) (by linarith)
    have k3 : κb * Real.exp tU ≤ κb' * Real.exp tU := mul_le_mul_of_nonneg_right hb hpos.le
    nlinarith
  · have : κH * Real.exp tU ≤ κH * Real.exp U0 := mul_le_mul_of_nonneg_left e1 hκH
    nlinarith

end Sarkozy.Envelopes
