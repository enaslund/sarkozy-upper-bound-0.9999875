module

public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Algebra.BigOperators.Ring.Finset

@[expose] public section

/-!
# The background polynomial of Step 4 (i) (OPS-S)

`paper/sections/23_envelopes.tex`, proof of `thm:envelopes`, "(iii) and (i)": "the main terms are at
most `|𝒞| π̃ C_X (1 + o(1)) Y` times `κ_H ∏_𝔅 (1 + v_𝔅 + w_𝔅) − (κ_H − κ_b) ∏_𝔅 (1 + v_𝔅)`, and
`lem:oct24:invariant-background`(v) bounds this by `κ_H e^{U₀} − (κ_H − κ_b) e^{tU}`";
`lem:oct24:invariant-background`(v), proof ("the polynomial being nondecreasing in every variable
… the chosen-tag-price form of `rem:completion-subtraction` then bounds the polynomial by
`κ_H e^{U₀} − (κ_H − κ_b) e^{∑ m_𝔅}`").

The finite part of the evaluation of the background, for the input `heval` of `Step4.step4_of_caps`:

* `sum_subsets_eq`: `∑_Z ∏_{𝔅 ∈ Z} w_𝔅 ∏_{𝔅 ∉ Z} (1 + v_𝔅) = ∏ (1 + v + w)` (the expansion
  `Ñ₀ = Ñ^inv + G` priced per atom);
* **`background_poly_eq`**: with the cap `b` on `Z = ∅` and `κ` elsewhere, the weighted sum is
  `κ ∏(1 + v + w) − (κ − b) ∏(1 + v)`;
* **`completion_sub_le`** (`rem:completion-subtraction`): `∏(1 + x + y) − ∏(1 + x) ≤
  e^{∑(x+y)} − e^{∑x}` for `x, y ≥ 0`;
* **`poly_mono`**: `κ ∏(1 + v + w) − (κ − κ_b) ∏(1 + v)` is nondecreasing in `v`, `w` for
  `0 ≤ κ_b ≤ κ`;
* **`heval_of_finer`**: the evaluation input `heval` of `Step4.step4_of_caps` in form (i), from the
  finer (E1) per outside set `Z` (the remaining input) and the upper prices;
* **`background_le`**: with upper prices `m ≥ v`, `n ≥ w`, `∑ m = tU` and `∑ (m + n) ≤ U₀`, the
  polynomial is at most `κ e^{U₀} − (κ − κ_b) e^{tU}` (`lem:oct24:invariant-background`(v)).
-/

open Finset
open scoped BigOperators

namespace Sarkozy.OpsSteps

variable {ι : Type*} [DecidableEq ι]

/-- **The per-atom expansion of the background**: choosing at every atom the generic tag `G`
(price `w`) or the invariant background (`1 + v`) gives `∏ (1 + v + w)`. -/
theorem sum_subsets_eq [Fintype ι] (v w : ι → ℝ) :
    ∑ f : ι → Bool, ∏ b, (if f b then w b else 1 + v b) = ∏ b, (1 + v b + w b) := by
  rw [← Fintype.prod_sum (fun b (y : Bool) => if y then w b else 1 + v b)]
  refine prod_congr rfl fun b _ => ?_
  rw [Fintype.sum_bool]
  simp only [↓reduceIte, Bool.false_eq_true]
  ring

/-- **The background polynomial** (`thm:envelopes`, (iii)): with the cap `b` on the invariant
monomials (`Z = ∅`) and `κ` on the others, `∑_Z cap_Z ∏_{Z} w ∏_{Zᶜ} (1 + v) =
κ ∏(1 + v + w) − (κ − b) ∏(1 + v)`. -/
theorem background_poly_eq [Fintype ι] (v w : ι → ℝ) (κ b : ℝ) :
    ∑ f : ι → Bool, (if f = (fun _ => false) then b else κ) *
        ∏ c, (if f c then w c else 1 + v c) =
      κ * ∏ c, (1 + v c + w c) - (κ - b) * ∏ c, (1 + v c) := by
  have h0 : ∏ c, (if (fun _ => false : ι → Bool) c then w c else 1 + v c) = ∏ c, (1 + v c) := by
    simp
  have hpt : ∀ f : ι → Bool, (if f = (fun _ => false) then b else κ) *
      ∏ c, (if f c then w c else 1 + v c) =
      κ * ∏ c, (if f c then w c else 1 + v c) +
        (if f = (fun _ => false) then (b - κ) * ∏ c, (if f c then w c else 1 + v c) else 0) := by
    intro f
    split_ifs <;> ring
  rw [sum_congr rfl fun f _ => hpt f, sum_add_distrib, ← mul_sum, sum_subsets_eq,
    sum_ite_eq' univ (fun _ => false : ι → Bool)
      (fun f => (b - κ) * ∏ c, (if f c then w c else 1 + v c))]
  simp only [mem_univ, ↓reduceIte]
  rw [h0]
  ring

/-- `e^t − 1 − t` is nondecreasing on `t ≥ 0`. -/
theorem exp_sub_one_sub_mono {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    Real.exp s - 1 - s ≤ Real.exp t - 1 - t := by
  have h := Real.add_one_le_exp (t - s)
  have hes : 1 ≤ Real.exp s := Real.one_le_exp hs
  have : Real.exp t = Real.exp s * Real.exp (t - s) := by rw [← Real.exp_add]; ring_nf
  nlinarith

/-- **`rem:completion-subtraction`**: for `x, y ≥ 0`,
`∏ (1 + x + y) − ∏ (1 + x) ≤ e^{∑(x + y)} − e^{∑ x}`. -/
theorem completion_sub_le (s : Finset ι) (x y : ι → ℝ) (hx : ∀ b, 0 ≤ x b) (hy : ∀ b, 0 ≤ y b) :
    ∏ b ∈ s, (1 + x b + y b) - ∏ b ∈ s, (1 + x b) ≤
      Real.exp (∑ b ∈ s, (x b + y b)) - Real.exp (∑ b ∈ s, x b) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert c s hc ih =>
    rw [prod_insert hc, prod_insert hc, sum_insert hc, sum_insert hc,
      show Real.exp (x c + y c + ∑ b ∈ s, (x b + y b)) =
        Real.exp (x c + y c) * Real.exp (∑ b ∈ s, (x b + y b)) from Real.exp_add _ _,
      show Real.exp (x c + ∑ b ∈ s, x b) = Real.exp (x c) * Real.exp (∑ b ∈ s, x b) from
        Real.exp_add _ _]
    set P := ∏ b ∈ s, (1 + x b + y b)
    set Q := ∏ b ∈ s, (1 + x b)
    set Exy := Real.exp (∑ b ∈ s, (x b + y b))
    set Ex := Real.exp (∑ b ∈ s, x b)
    have hP : P ≤ Exy := by
      refine le_trans (prod_le_prod₀ (g := fun b => Real.exp (x b + y b))
        (fun b _ => by linarith [hx b, hy b])
        fun b _ => by linarith [Real.add_one_le_exp (x b + y b)]) ?_
      exact (Real.exp_sum s (fun b => x b + y b)).symm.le
    have hQ0 : 0 ≤ Q := prod_nonneg fun b _ => by linarith [hx b]
    have hEx_le : Ex ≤ Exy :=
      Real.exp_le_exp.mpr (sum_le_sum fun b _ => by linarith [hy b])
    have hEx0 : 0 ≤ Ex := (Real.exp_pos _).le
    have hg := exp_sub_one_sub_mono (hx c) (show x c ≤ x c + y c by linarith [hy c])
    have hg0 : 0 ≤ Real.exp (x c) - 1 - x c := by linarith [Real.add_one_le_exp (x c)]
    have ha : 0 ≤ 1 + x c := by linarith [hx c]
    -- P (1 + x + y) − Q (1 + x) = (P − Q)(1 + x) + P y
    have step : P * (1 + x c + y c) - Q * (1 + x c) ≤ (Exy - Ex) * (1 + x c) + Exy * y c := by
      have h1 := mul_le_mul_of_nonneg_right ih ha
      have h2 := mul_le_mul_of_nonneg_right hP (hy c)
      nlinarith
    have hfin : (Exy - Ex) * (1 + x c) + Exy * y c ≤
        Exy * Real.exp (x c + y c) - Ex * Real.exp (x c) := by
      have e1 : Exy * Real.exp (x c + y c) - Ex * Real.exp (x c) -
          ((Exy - Ex) * (1 + x c) + Exy * y c) =
          Exy * (Real.exp (x c + y c) - 1 - (x c + y c)) -
            Ex * (Real.exp (x c) - 1 - x c) := by ring
      have h3 := mul_le_mul hEx_le hg hg0 (hEx0.trans hEx_le)
      linarith
    have hall := step.trans hfin
    nlinarith [hall]

/-- The background polynomial `κ ∏(1 + v + w) − c ∏(1 + v)` (`c = κ − κ_b`). -/
noncomputable def bgPoly (s : Finset ι) (κ c : ℝ) (v w : ι → ℝ) : ℝ :=
  κ * ∏ b ∈ s, (1 + v b + w b) - c * ∏ b ∈ s, (1 + v b)

/-- **The background polynomial is at most its completion** (`rem:completion-subtraction`):
`κ ∏(1 + v + w) − c ∏(1 + v) ≤ κ e^{∑(v + w)} − c e^{∑ v}` for `0 ≤ c ≤ κ` and `v, w ≥ 0`. -/
theorem bgPoly_le_exp (s : Finset ι) {κ c : ℝ} (hc : 0 ≤ c) (hcκ : c ≤ κ) (v w : ι → ℝ)
    (hv : ∀ b, 0 ≤ v b) (hw : ∀ b, 0 ≤ w b) :
    bgPoly s κ c v w ≤ κ * Real.exp (∑ b ∈ s, (v b + w b)) - c * Real.exp (∑ b ∈ s, v b) := by
  unfold bgPoly
  have h1 := completion_sub_le s v w hv hw
  have h2 : ∏ b ∈ s, (1 + v b + w b) ≤ Real.exp (∑ b ∈ s, (v b + w b)) := by
    refine le_trans (prod_le_prod₀ (g := fun b => Real.exp (v b + w b))
      (fun b _ => by linarith [hv b, hw b])
      fun b _ => by linarith [Real.add_one_le_exp (v b + w b)]) ?_
    exact (Real.exp_sum s (fun b => v b + w b)).symm.le
  have h3 := mul_le_mul_of_nonneg_left h1 hc
  have h4 := mul_le_mul_of_nonneg_left h2 (sub_nonneg.mpr hcκ)
  nlinarith

/-- **The background polynomial is nondecreasing in every variable** (for `0 ≤ c ≤ κ`): the proof of
`lem:oct24:invariant-background`(v). -/
theorem bgPoly_mono (s : Finset ι) {κ c : ℝ} (hc : 0 ≤ c) (hcκ : c ≤ κ) {v w v' w' : ι → ℝ}
    (hv : ∀ b, 0 ≤ v b) (hw : ∀ b, 0 ≤ w b) (hvv : ∀ b, v b ≤ v' b) (hww : ∀ b, w b ≤ w' b) :
    bgPoly s κ c v w ≤ bgPoly s κ c v' w' := by
  unfold bgPoly
  induction s using Finset.induction_on with
  | empty => simp
  | insert d s hd ih =>
    rw [prod_insert hd, prod_insert hd, prod_insert hd, prod_insert hd]
    set P := ∏ b ∈ s, (1 + v b + w b)
    set Q := ∏ b ∈ s, (1 + v b)
    set P' := ∏ b ∈ s, (1 + v' b + w' b)
    set Q' := ∏ b ∈ s, (1 + v' b)
    have hQ0 : 0 ≤ Q := prod_nonneg fun b _ => by linarith [hv b]
    have hQQ : Q ≤ P := prod_le_prod₀ (fun b _ => by linarith [hv b])
      fun b _ => by linarith [hw b]
    have hQQ' : Q ≤ Q' := prod_le_prod₀ (fun b _ => by linarith [hv b])
      fun b _ => by linarith [hvv b]
    have hPP' : P ≤ P' := prod_le_prod₀ (fun b _ => by linarith [hv b, hw b])
      fun b _ => by linarith [hvv b, hww b]
    have hQ'P' : Q' ≤ P' := prod_le_prod₀ (fun b _ => by linarith [hv b, hvv b])
      fun b _ => by linarith [hw b, hww b]
    -- F' − F = κ (P' a' − P a) − c (Q' b' − Q b) with a = 1 + v + w, b = 1 + v at `d`
    have ha : 1 + v d + w d ≤ 1 + v' d + w' d := by linarith [hvv d, hww d]
    have hb : 1 + v d ≤ 1 + v' d := by linarith [hvv d]
    have ha0 : 0 ≤ 1 + v d + w d := by linarith [hv d, hw d]
    have hb0 : 0 ≤ 1 + v d := by linarith [hv d]
    have hba : 1 + v' d ≤ 1 + v' d + w' d := by linarith [hw d, hww d]
    -- write the increments
    have key : κ * ((1 + v d + w d) * P) - c * ((1 + v d) * Q) ≤
        κ * ((1 + v' d + w' d) * P') - c * ((1 + v' d) * Q') := by
      have hih : κ * P - c * Q ≤ κ * P' - c * Q' := ih
      have hκ0 : 0 ≤ κ := hc.trans hcκ
      -- κ P' a' − c Q' b' − (κ P a − c Q b)
      --   = a (κ P' − c Q' − (κ P − c Q)) + κ P' (a' − a) − c Q' (b' − a) + c Q' (b − a)·0 …
      have e : κ * ((1 + v' d + w' d) * P') - c * ((1 + v' d) * Q') -
          (κ * ((1 + v d + w d) * P) - c * ((1 + v d) * Q)) =
          (1 + v d + w d) * ((κ * P' - c * Q') - (κ * P - c * Q)) +
            ((v' d + w' d) - (v d + w d)) * (κ * P' - c * Q') +
            c * Q' * ((v' d + w' d) - (v' d)) - c * Q * ((v d + w d) - v d) := by ring
      have t1 : 0 ≤ (1 + v d + w d) * ((κ * P' - c * Q') - (κ * P - c * Q)) :=
        mul_nonneg ha0 (by linarith)
      have hκP'cQ' : 0 ≤ κ * P' - c * Q' := by
        have := mul_le_mul hcκ hQ'P' (hQ0.trans hQQ') hκ0
        nlinarith [mul_nonneg hc (hQ0.trans hQQ')]
      have t2 : 0 ≤ ((v' d + w' d) - (v d + w d)) * (κ * P' - c * Q') :=
        mul_nonneg (by linarith [hvv d, hww d]) hκP'cQ'
      have t3 : c * Q * ((v d + w d) - v d) ≤ c * Q' * ((v' d + w' d) - v' d) := by
        have : (v d + w d) - v d ≤ (v' d + w' d) - v' d := by linarith [hww d]
        exact mul_le_mul (mul_le_mul_of_nonneg_left hQQ' hc) this (by linarith [hw d])
          (mul_nonneg hc (hQ0.trans hQQ'))
      linarith
    calc κ * ((1 + v d + w d) * P) - c * ((1 + v d) * Q) ≤
        κ * ((1 + v' d + w' d) * P') - c * ((1 + v' d) * Q') := key
      _ = _ := rfl

/-- **The background bound of `lem:oct24:invariant-background`(v)**: with upper prices `m ≥ v`,
`n ≥ w` such that `∑ m = tU` and `∑(m + n) ≤ U₀`, and `0 ≤ κ_b ≤ κ_H`,
`κ_H ∏(1 + v + w) − (κ_H − κ_b) ∏(1 + v) ≤ κ_H e^{U₀} − (κ_H − κ_b) e^{tU}`. -/
theorem background_le (s : Finset ι) {κH κb U₀ tU : ℝ} (hb : 0 ≤ κb) (hbH : κb ≤ κH)
    {v w m n : ι → ℝ} (hv : ∀ b, 0 ≤ v b) (hw : ∀ b, 0 ≤ w b) (hvm : ∀ b, v b ≤ m b)
    (hwn : ∀ b, w b ≤ n b) (hm : ∑ b ∈ s, m b = tU) (hU : ∑ b ∈ s, (m b + n b) ≤ U₀) :
    κH * ∏ b ∈ s, (1 + v b + w b) - (κH - κb) * ∏ b ∈ s, (1 + v b) ≤
      κH * Real.exp U₀ - (κH - κb) * Real.exp tU := by
  have hc : 0 ≤ κH - κb := by linarith
  have hcκ : κH - κb ≤ κH := by linarith
  have h1 := bgPoly_mono s hc hcκ hv hw hvm hwn
  have hm0 : ∀ b, 0 ≤ m b := fun b => (hv b).trans (hvm b)
  have hn0 : ∀ b, 0 ≤ n b := fun b => (hw b).trans (hwn b)
  have h2 := bgPoly_le_exp s hc hcκ m n hm0 hn0
  unfold bgPoly at h1 h2
  rw [hm] at h2
  have h3 : κH * Real.exp (∑ b ∈ s, (m b + n b)) ≤ κH * Real.exp U₀ :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hU) (hb.trans hbH)
  linarith

/-- **The evaluation input `heval` of `step4_of_caps` in form (i)**, from the finer (E1): if at
every selection `ω` of the class every outside set `Z` (`f`) has
`Y^{O_Z}[Diag_ω] ≤ (1 + ε) C_X Y ∏_{Z} w ∏_{Zᶜ} (1 + v) + r_{ω,Z}` (E1 with the tags of `G` and of
`E_add + H` priced separately: the remaining input), with the caps `κ_b(ω)` on `Z = ∅` and `κ_H(ω)`
elsewhere (`0 ≤ κ_b ≤ κ_H ≤ κ_M`), the upper prices `m ≥ v`, `n ≥ w` with `∑ m = tU`,
`∑(m + n) ≤ U₀`, and `ε κ_M e^{U₀} ≤ z`, then
`∑_ω π̃_ω ∑_Z cap_{ω,Z} Y^{O_Z}[Diag_ω] ≤ (∑_ω π̃ C_X (κ_H e^{U₀} − (κ_H − κ_b) e^{tU})) Y +
z (∑ π̃ C_X) Y + ∑_ω π̃ ∑_Z cap r`. -/
theorem heval_of_finer [Fintype ι] {Ω : Type*} (𝒞 : Finset Ω) (wt CX : Ω → ℝ) (κH κb : Ω → ℝ)
    (EO r : Ω → (ι → Bool) → ℝ) {v w m n : ι → ℝ} {ε Y U₀ tU z κM : ℝ}
    (hv : ∀ b, 0 ≤ v b) (hw : ∀ b, 0 ≤ w b) (hvm : ∀ b, v b ≤ m b) (hwn : ∀ b, w b ≤ n b)
    (hm : ∑ b, m b = tU) (hU : ∑ b, (m b + n b) ≤ U₀) (hε : 0 ≤ ε)
    (hwt : ∀ ω ∈ 𝒞, 0 ≤ wt ω) (hCY : ∀ ω ∈ 𝒞, 0 ≤ CX ω * Y)
    (hκb : ∀ ω ∈ 𝒞, 0 ≤ κb ω) (hκbH : ∀ ω ∈ 𝒞, κb ω ≤ κH ω) (hκM : ∀ ω ∈ 𝒞, κH ω ≤ κM)
    (hz : ε * κM * Real.exp U₀ ≤ z)
    (hfine : ∀ ω ∈ 𝒞, ∀ f, EO ω f ≤
      (1 + ε) * CX ω * Y * ∏ c, (if f c then w c else 1 + v c) + r ω f) :
    ∑ ω ∈ 𝒞, wt ω * ∑ f : ι → Bool, (if f = (fun _ => false) then κb ω else κH ω) * EO ω f ≤
      (∑ ω ∈ 𝒞, wt ω * CX ω * (κH ω * Real.exp U₀ - (κH ω - κb ω) * Real.exp tU)) * Y +
        z * (∑ ω ∈ 𝒞, wt ω * CX ω) * Y +
        ∑ ω ∈ 𝒞, wt ω * ∑ f : ι → Bool, (if f = (fun _ => false) then κb ω else κH ω) * r ω f := by
  have hper : ∀ ω ∈ 𝒞, wt ω * ∑ f : ι → Bool, (if f = (fun _ => false) then κb ω else κH ω) *
      EO ω f ≤ wt ω * CX ω * (κH ω * Real.exp U₀ - (κH ω - κb ω) * Real.exp tU) * Y +
        z * (wt ω * CX ω) * Y +
        wt ω * ∑ f : ι → Bool, (if f = (fun _ => false) then κb ω else κH ω) * r ω f := by
    intro ω hω
    have hcap0 : ∀ f : ι → Bool, 0 ≤ (if f = (fun _ => false) then κb ω else κH ω) := fun f => by
      split_ifs
      · exact hκb ω hω
      · exact (hκb ω hω).trans (hκbH ω hω)
    have h1 : ∑ f : ι → Bool, (if f = (fun _ => false) then κb ω else κH ω) * EO ω f ≤
        ∑ f : ι → Bool, (if f = (fun _ => false) then κb ω else κH ω) *
          ((1 + ε) * CX ω * Y * ∏ c, (if f c then w c else 1 + v c) + r ω f) :=
      sum_le_sum fun f _ => mul_le_mul_of_nonneg_left (hfine ω hω f) (hcap0 f)
    have h2 : ∑ f : ι → Bool, (if f = (fun _ => false) then κb ω else κH ω) *
          ((1 + ε) * CX ω * Y * ∏ c, (if f c then w c else 1 + v c) + r ω f) =
        (1 + ε) * (CX ω * Y) * (κH ω * ∏ c, (1 + v c + w c) - (κH ω - κb ω) * ∏ c, (1 + v c)) +
          ∑ f : ι → Bool, (if f = (fun _ => false) then κb ω else κH ω) * r ω f := by
      rw [← background_poly_eq v w (κH ω) (κb ω), mul_sum, ← sum_add_distrib]
      exact sum_congr rfl fun f _ => by ring
    have h3 := background_le univ (hκb ω hω) (hκbH ω hω) hv hw hvm hwn hm hU
    set X := κH ω * Real.exp U₀ - (κH ω - κb ω) * Real.exp tU
    have hXle : X ≤ κH ω * Real.exp U₀ := by
      have : 0 ≤ (κH ω - κb ω) * Real.exp tU :=
        mul_nonneg (by linarith [hκbH ω hω]) (Real.exp_pos _).le
      linarith
    have hCY0 := hCY ω hω
    have h4 : (1 + ε) * (CX ω * Y) * (κH ω * ∏ c, (1 + v c + w c) -
        (κH ω - κb ω) * ∏ c, (1 + v c)) ≤ (1 + ε) * (CX ω * Y) * X :=
      mul_le_mul_of_nonneg_left h3 (mul_nonneg (by linarith) hCY0)
    have h5 : (1 + ε) * (CX ω * Y) * X ≤ CX ω * Y * X + z * (CX ω * Y) := by
      have h6 : ε * X ≤ z := by
        have : ε * X ≤ ε * (κM * Real.exp U₀) := by
          refine mul_le_mul_of_nonneg_left (hXle.trans ?_) hε
          exact mul_le_mul_of_nonneg_right (hκM ω hω) (Real.exp_pos _).le
        linarith
      nlinarith [mul_le_mul_of_nonneg_left h6 hCY0]
    have h7 := h1.trans (h2.le.trans (add_le_add_left (h4.trans h5) _))
    have h8 := mul_le_mul_of_nonneg_left h7 (hwt ω hω)
    calc _ ≤ _ := h8
      _ = _ := by ring
  calc _ ≤ ∑ ω ∈ 𝒞, (wt ω * CX ω * (κH ω * Real.exp U₀ - (κH ω - κb ω) * Real.exp tU) * Y +
        z * (wt ω * CX ω) * Y +
        wt ω * ∑ f : ι → Bool, (if f = (fun _ => false) then κb ω else κH ω) * r ω f) :=
      sum_le_sum hper
    _ = _ := by
      rw [sum_add_distrib, sum_add_distrib, ← sum_mul, ← sum_mul, ← mul_sum]

end Sarkozy.OpsSteps
