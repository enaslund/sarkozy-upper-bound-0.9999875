module

public import Sarkozy.SpectralD.OverlapPair
public import Sarkozy.Peyre.Correlation

@[expose] public section

/-!
# From `def:prelim:maxcorr` to the hypotheses of `lem:general-star`(e)

`paper/sections/04_notation.tex`, `def:prelim:maxcorr`, defines the maximal correlation with
**real** functions; `Sarkozy.Peyre.maxCorr` and its inequality form `Sarkozy.Peyre.CorrLe`
formalize it (`Peyre.maxCorr_le_iff`). The proof of `lem:general-star`(e) applies it to the
complex functions `W_S h`. This file proves the standard complexification step and so derives the
hypotheses `CorrBound` and `CondCorrBound` of `OverlapDisjoint` and `OverlapPair` from the
paper's definition:

* `complex_corr_of_corrLe`: if `CorrLe ν X Y ρ` (`ρ ≥ 0`), then
  `|E \overline{F} G| ≤ ρ ‖F‖ ‖G‖` for complex mean-zero `F ∈ L²(X)`, `G ∈ L²(Y)`. Proof:
  `E[\overline{F} G] = E[\overline{F} H]` with `H = E[Re G | X] + i E[Im G | X]`, Cauchy–Schwarz,
  and `‖E[Re G | X]‖ ≤ ρ ‖Re G‖`, `‖E[Im G | X]‖ ≤ ρ ‖Im G‖` (`Peyre.sqrt_condExp_sq_le`).
* `corrBound_of_maxCorr_le`: `ρ(x_A; x_B) ≤ ρ` gives `CorrBound μ A B ρ`.
* `condCorrBound_of_maxCorr_le`: if, for every value `α` of `x_a` of positive probability, the
  maximal correlation of `x_b` and `x_{U∖{a,b}}` under `μ(· | x_a = α)` is at most `ρ`
  (`def:prelim:maxcorr`, conditional), then `CondCorrBound μ a b ρ`.
* `disjoint_star_bound_maxCorr`, `pair_overlap_maxCorr`: `lem:general-star`(e) with its two
  hypotheses exactly in the form of `def:prelim:maxcorr`.

New material for this paper.
-/

namespace Sarkozy.SpectralD.Overlap

open Finset Complex Sarkozy.Characters Sarkozy.SpectralC Sarkozy.Peyre
open scoped BigOperators ComplexConjugate

section Complexify

variable {Ω : Type*} [Fintype Ω] {α β : Type*}

/-- `CorrLe` is symmetric. -/
lemma corrLe_symm {ν : FiniteLaw Ω} {X : Ω → α} {Y : Ω → β} {ε : ℝ} (h : CorrLe ν X Y ε) :
    CorrLe ν Y X ε := by
  intro g f hg hf
  have h1 := h f g hf hg
  have e : ν.expect (fun ω => g (Y ω) * f (X ω)) = ν.expect (fun ω => f (X ω) * g (Y ω)) :=
    ν.expect_congr fun ω => mul_comm _ _
  rw [e]
  calc _ ≤ ε * √(ν.expect (fun ω => f (X ω) ^ 2)) * √(ν.expect (fun ω => g (Y ω) ^ 2)) := h1
    _ = _ := by ring

/-- For a real `f ∈ L²(X)` and complex `G`, with `H = E[Re G | X] + i E[Im G | X]`:
`E[f G] = E[f H]`. -/
lemma sum_real_mul_condExpC (ν : FiniteLaw Ω) (X : Ω → α) (f : Ω → ℝ) (hf : IsFunOf X f)
    (G : Ω → ℂ) :
    ∑ ω, (ν.weight ω : ℂ) * ((f ω : ℂ) * G ω) =
      ∑ ω, (ν.weight ω : ℂ) * ((f ω : ℂ) * ((condExp ν X (fun ω => (G ω).re) ω : ℂ) +
        (condExp ν X (fun ω => (G ω).im) ω : ℂ) * I)) := by
  have h1 := expect_mul_condExp ν X (fun ω => (G ω).re) f hf
  have h2 := expect_mul_condExp ν X (fun ω => (G ω).im) f hf
  unfold FiniteLaw.expect at h1 h2
  apply Complex.ext
  · simp only [re_sum, mul_re, ofReal_re, ofReal_im, add_re, add_im, mul_im, I_re, I_im,
      zero_mul, sub_zero, mul_zero, mul_one, zero_add, add_zero]
    rw [← h1]
  · simp only [im_sum, mul_im, ofReal_re, ofReal_im, add_re, add_im, mul_re, I_re, I_im,
      zero_mul, sub_zero, mul_zero, mul_one, zero_add, add_zero]
    rw [← h2]

/-- **Complexification of a real maximal-correlation bound** (`def:prelim:maxcorr`): if
`CorrLe ν X Y ρ` with `ρ ≥ 0`, then for complex `F` a function of `X` and `G` a function of `Y`,
both of mean zero, `|E \overline{F} G| ≤ ρ ‖F‖ ‖G‖`. -/
theorem complex_corr_of_corrLe {ν : FiniteLaw Ω} {X : Ω → α} {Y : Ω → β} {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (h : CorrLe ν X Y ρ) (F G : Ω → ℂ) (hF : ∀ ω ω', X ω = X ω' → F ω = F ω')
    (hG : ∀ ω ω', Y ω = Y ω' → G ω = G ω') (hG0 : ∑ ω, (ν.weight ω : ℂ) * G ω = 0) :
    ‖∑ ω, (ν.weight ω : ℂ) * (conj (F ω) * G ω)‖ ≤
      ρ * Real.sqrt (∑ ω, ν.weight ω * ‖F ω‖ ^ 2) *
        Real.sqrt (∑ ω, ν.weight ω * ‖G ω‖ ^ 2) := by
  set G1 : Ω → ℝ := fun ω => (G ω).re with hG1
  set G2 : Ω → ℝ := fun ω => (G ω).im with hG2
  set H1 := condExp ν X G1 with hH1
  set H2 := condExp ν X G2 with hH2
  set H : Ω → ℂ := fun ω => (H1 ω : ℂ) + (H2 ω : ℂ) * I with hH
  have hF1 : IsFunOf X (fun ω => (F ω).re) := fun ω ω' hx => by simp only [hF ω ω' hx]
  have hF2 : IsFunOf X (fun ω => (F ω).im) := fun ω ω' hx => by simp only [hF ω ω' hx]
  have hGG1 : IsFunOf Y G1 := fun ω ω' hy => by simp only [hG1, hG ω ω' hy]
  have hGG2 : IsFunOf Y G2 := fun ω ω' hy => by simp only [hG2, hG ω ω' hy]
  have hm1 : ν.expect G1 = 0 := by
    have := congrArg Complex.re hG0
    simp only [re_sum, mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero, zero_re] at this
    exact this
  have hm2 : ν.expect G2 = 0 := by
    have := congrArg Complex.im hG0
    simp only [im_sum, mul_im, ofReal_re, ofReal_im, zero_mul, add_zero, zero_im] at this
    exact this
  -- `E[\overline{F} G] = E[\overline{F} H]`
  have hconj : ∀ ω, conj (F ω) = (((F ω).re : ℝ) : ℂ) - (((F ω).im : ℝ) : ℂ) * I := by
    intro ω
    apply Complex.ext <;> simp
  have hid : ∑ ω, (ν.weight ω : ℂ) * (conj (F ω) * G ω) =
      ∑ ω, (ν.weight ω : ℂ) * (conj (F ω) * H ω) := by
    have a1 := sum_real_mul_condExpC ν X (fun ω => (F ω).re) hF1 G
    have a2 := sum_real_mul_condExpC ν X (fun ω => (F ω).im) hF2 G
    have e : ∀ K : Ω → ℂ, ∑ ω, (ν.weight ω : ℂ) * (conj (F ω) * K ω) =
        ∑ ω, (ν.weight ω : ℂ) * ((((F ω).re : ℝ) : ℂ) * K ω) -
          I * ∑ ω, (ν.weight ω : ℂ) * ((((F ω).im : ℝ) : ℂ) * K ω) := by
      intro K
      rw [mul_sum, ← sum_sub_distrib]
      refine sum_congr rfl fun ω _ => ?_
      rw [hconj ω]
      ring
    rw [e G, e H, a1, a2]
  rw [hid]
  refine (fiber_cs univ ν.weight ν.nonneg F H).trans ?_
  -- `‖H‖ ≤ ρ ‖G‖`
  have hsq : ∀ z : ℂ, ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := fun z => by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  have hHn : ∀ ω, ‖H ω‖ ^ 2 = H1 ω ^ 2 + H2 ω ^ 2 := fun ω => by
    rw [hsq]; simp [hH]
  have hGn : ∀ ω, ‖G ω‖ ^ 2 = G1 ω ^ 2 + G2 ω ^ 2 := fun ω => by rw [hsq]
  have hY := corrLe_symm h
  have b1 := sqrt_condExp_sq_le hY hρ0 hGG1 hm1
  have b2 := sqrt_condExp_sq_le hY hρ0 hGG2 hm2
  rw [← hH1] at b1
  rw [← hH2] at b2
  have sq1 : ν.expect (fun ω => H1 ω ^ 2) ≤ ρ ^ 2 * ν.expect (fun ω => G1 ω ^ 2) := by
    have h0 := Real.sqrt_nonneg (ν.expect (fun ω => H1 ω ^ 2))
    have := pow_le_pow_left₀ h0 b1 2
    rwa [Real.sq_sqrt (ν.second_moment_nonneg _), mul_pow,
      Real.sq_sqrt (ν.second_moment_nonneg _)] at this
  have sq2 : ν.expect (fun ω => H2 ω ^ 2) ≤ ρ ^ 2 * ν.expect (fun ω => G2 ω ^ 2) := by
    have h0 := Real.sqrt_nonneg (ν.expect (fun ω => H2 ω ^ 2))
    have := pow_le_pow_left₀ h0 b2 2
    rwa [Real.sq_sqrt (ν.second_moment_nonneg _), mul_pow,
      Real.sq_sqrt (ν.second_moment_nonneg _)] at this
  have hsumH : ∑ ω, ν.weight ω * ‖H ω‖ ^ 2 ≤ ρ ^ 2 * ∑ ω, ν.weight ω * ‖G ω‖ ^ 2 := by
    have e1 : ∑ ω, ν.weight ω * ‖H ω‖ ^ 2 =
        ν.expect (fun ω => H1 ω ^ 2) + ν.expect (fun ω => H2 ω ^ 2) := by
      unfold FiniteLaw.expect
      rw [← sum_add_distrib]
      exact sum_congr rfl fun ω _ => by rw [hHn]; ring
    have e2 : ∑ ω, ν.weight ω * ‖G ω‖ ^ 2 =
        ν.expect (fun ω => G1 ω ^ 2) + ν.expect (fun ω => G2 ω ^ 2) := by
      unfold FiniteLaw.expect
      rw [← sum_add_distrib]
      exact sum_congr rfl fun ω _ => by rw [hGn]; ring
    rw [e1, e2]
    linarith
  have hsH : Real.sqrt (∑ ω, ν.weight ω * ‖H ω‖ ^ 2) ≤
      ρ * Real.sqrt (∑ ω, ν.weight ω * ‖G ω‖ ^ 2) := by
    calc Real.sqrt (∑ ω, ν.weight ω * ‖H ω‖ ^ 2)
        ≤ Real.sqrt (ρ ^ 2 * ∑ ω, ν.weight ω * ‖G ω‖ ^ 2) := Real.sqrt_le_sqrt hsumH
      _ = ρ * Real.sqrt (∑ ω, ν.weight ω * ‖G ω‖ ^ 2) := by
          rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hρ0]
  calc Real.sqrt (∑ ω, ν.weight ω * ‖F ω‖ ^ 2) * Real.sqrt (∑ ω, ν.weight ω * ‖H ω‖ ^ 2)
      ≤ Real.sqrt (∑ ω, ν.weight ω * ‖F ω‖ ^ 2) *
          (ρ * Real.sqrt (∑ ω, ν.weight ω * ‖G ω‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left hsH (Real.sqrt_nonneg _)
    _ = _ := by ring

end Complexify

variable {p : ℕ} [Fact p.Prime] {U : Type*} [Fintype U] [DecidableEq U]

/-- The coordinates `x_A = (x_i)_{i ∈ A}`. -/
def restr (A : Finset U) (x : U → ZMod p) : A → ZMod p := fun i => x i

omit [Fact p.Prime] [Fintype U] [DecidableEq U] in
lemma restr_eq_iff {A : Finset U} {x x' : U → ZMod p} :
    restr A x = restr A x' ↔ ∀ i ∈ A, x i = x' i := by
  constructor
  · intro h i hi
    exact congrFun h ⟨i, hi⟩
  · intro h
    funext i
    exact h i i.2

/-- **The hypothesis of the disjoint-support bound from `def:prelim:maxcorr`**: if the maximal
correlation `ρ(x_A; x_B)` (`Peyre.maxCorr`) under the law `ν` is at most `ρ`, then
`CorrBound ν A B ρ`. -/
theorem corrBound_of_maxCorr_le (ν : FiniteLaw (U → ZMod p)) (A B : Finset U) {ρ : ℝ}
    (hρ0 : 0 ≤ ρ) (h : maxCorr ν (restr A) (restr B) ≤ ρ) : CorrBound ν.weight A B ρ := by
  have hc := (maxCorr_le_iff hρ0).mp h
  intro F G hF hG hF0 hG0
  exact complex_corr_of_corrLe hρ0 hc F G (fun x x' hx => hF x x' (restr_eq_iff.mp hx))
    (fun x x' hx => hG x x' (restr_eq_iff.mp hx)) hG0

/-- Sums against a conditional law are fibre sums: `E[k | x_a = α] = μ(x_a = α)⁻¹ ∑_{x_a = α} μ k`. -/
lemma sum_condLaw_fiber {M : Type*} [AddCommMonoid M] [Module ℝ M] (ν : FiniteLaw (U → ZMod p))
    (a : U) (α : ZMod p) (hα : 0 < prob ν (fun x => x a = α)) (k : (U → ZMod p) → M) :
    ∑ x, (condLaw ν (fun x => x a = α) hα).weight x • k x =
      (prob ν (fun x => x a = α))⁻¹ • ∑ x ∈ univ.filter (fun x : U → ZMod p => x a = α),
        ν.weight x • k x := by
  rw [smul_sum, sum_filter]
  refine sum_congr rfl fun x _ => ?_
  rw [cond_weight]
  by_cases hx : x a = α
  · rw [ind_of_pos (E := fun y : U → ZMod p => y a = α) (ω := x) hx, ite_eq_left hx, one_mul,
      div_eq_inv_mul, mul_smul]
  · rw [ind_of_neg (E := fun y : U → ZMod p => y a = α) (ω := x) hx, ite_eq_right hx, zero_mul,
      zero_div, zero_smul]

/-- **The hypothesis of `eq:pair-overlap` from `def:prelim:maxcorr`**: if for every value `α` of
`x_a` of positive probability the maximal correlation of `x_b` and `x_{U∖{a,b}}` under
`ν(· | x_a = α)` (`Peyre.maxCorr` of `Peyre.condLaw`) is at most `ρ`, then
`CondCorrBound ν a b ρ`. -/
theorem condCorrBound_of_maxCorr_le (ν : FiniteLaw (U → ZMod p)) (a b : U) {ρ : ℝ}
    (hρ0 : 0 ≤ ρ)
    (h : ∀ α : ZMod p, ∀ hα : 0 < prob ν (fun x => x a = α),
      maxCorr (condLaw ν (fun x => x a = α) hα) (fun x => x b) (restr (univ \ {a, b})) ≤ ρ) :
    CondCorrBound ν.weight a b ρ := by
  intro α f G hG hf0 hG0
  rcases (prob_nonneg ν (fun x => x a = α)).eq_or_lt with h0 | hα
  · -- a null fibre
    have hw : ∀ x ∈ univ.filter (fun x : U → ZMod p => x a = α), ν.weight x = 0 := by
      intro x hx
      exact le_antisymm (h0 ▸ weight_le_prob ν (mem_filter.mp hx).2) (ν.nonneg x)
    have hz : ∑ x ∈ univ.filter (fun x : U → ZMod p => x a = α),
        (ν.weight x : ℂ) * (conj (f (x b)) * G x) = 0 :=
      sum_eq_zero fun x hx => by rw [hw x hx]; simp
    rw [hz, norm_zero]
    positivity
  · set P := prob ν (fun x => x a = α) with hP
    set νc := condLaw ν (fun x => x a = α) hα
    have hc := (maxCorr_le_iff hρ0).mp (h α hα)
    have hcs : ∀ k : (U → ZMod p) → ℂ, ∑ x, (νc.weight x : ℂ) * k x =
        ((P⁻¹ : ℝ) : ℂ) * ∑ x ∈ univ.filter (fun x : U → ZMod p => x a = α),
          (ν.weight x : ℂ) * k x := by
      intro k
      have := sum_condLaw_fiber ν a α hα k
      simp only [Complex.real_smul] at this
      rw [this]
    have hcr : ∀ k : (U → ZMod p) → ℝ, ∑ x, νc.weight x * k x =
        P⁻¹ * ∑ x ∈ univ.filter (fun x : U → ZMod p => x a = α), ν.weight x * k x := by
      intro k
      have := sum_condLaw_fiber ν a α hα k
      simp only [smul_eq_mul] at this
      exact this
    have hPi : 0 < P⁻¹ := inv_pos.mpr hα
    have hf0' : ∑ x, (νc.weight x : ℂ) * f (x b) = 0 := by
      rw [hcs (fun x => f (x b)), hf0, mul_zero]
    have hG0' : ∑ x, (νc.weight x : ℂ) * G x = 0 := by
      rw [hcs G, hG0, mul_zero]
    have hb := complex_corr_of_corrLe hρ0 hc (fun x => f (x b)) G
      (fun x x' hx => by simp only [hx]) (fun x x' hx => hG x x' (restr_eq_iff.mp hx)) hG0'
    rw [hcs (fun x => conj (f (x b)) * G x), hcr (fun x => ‖f (x b)‖ ^ 2),
      hcr (fun x => ‖G x‖ ^ 2), norm_mul, Complex.norm_real, Real.norm_of_nonneg hPi.le,
      Real.sqrt_mul hPi.le, Real.sqrt_mul hPi.le] at hb
    have hPP : Real.sqrt P⁻¹ * Real.sqrt P⁻¹ = P⁻¹ := Real.mul_self_sqrt hPi.le
    have hb' : P⁻¹ * ‖∑ x ∈ univ.filter (fun x : U → ZMod p => x a = α),
        (ν.weight x : ℂ) * (conj (f (x b)) * G x)‖ ≤
        P⁻¹ * (ρ * Real.sqrt (∑ x ∈ univ.filter (fun x : U → ZMod p => x a = α),
          ν.weight x * ‖f (x b)‖ ^ 2) *
          Real.sqrt (∑ x ∈ univ.filter (fun x : U → ZMod p => x a = α), ν.weight x * ‖G x‖ ^ 2)) := by
      calc _ ≤ _ := hb
        _ = (Real.sqrt P⁻¹ * Real.sqrt P⁻¹) * (ρ *
            Real.sqrt (∑ x ∈ univ.filter (fun x : U → ZMod p => x a = α),
              ν.weight x * ‖f (x b)‖ ^ 2) *
            Real.sqrt (∑ x ∈ univ.filter (fun x : U → ZMod p => x a = α),
              ν.weight x * ‖G x‖ ^ 2)) := by ring
        _ = _ := by rw [hPP]
    exact le_of_mul_le_mul_left hb' hPi

/-- **`lem:general-star`(e), disjoint supports, with the hypothesis of `def:prelim:maxcorr`**
(`p ≡ 3 (mod 4)`): for the law `ν` (invariant, on injective labellings), `T ∩ S = ∅` and
`ρ(x_S; x_{U∖S}) ≤ ρ_S`: `|⟨W_S h, W_T h'⟩_ν| ≤ ρ_S q ‖h‖ ‖h'‖`, i.e.
`‖(W_S/r)^*(W_T/r)‖ ≤ ρ_S`. -/
theorem disjoint_star_bound_maxCorr (hp2 : p ≠ 2) (hp3 : p % 4 = 3)
    (ν : FiniteLaw (U → ZMod p))
    (hinv : ∀ (s c : ZMod p) (x : U → ZMod p), s ≠ 0 → IsSquare s →
      ν.weight (affLab s c x) = ν.weight x)
    (hinj : ∀ (x : U → ZMod p) (k l : U), ν.weight x ≠ 0 → k ≠ l → x k ≠ x l)
    {S T : Finset U} (hST : Disjoint S T) {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hρ : maxCorr ν (restr S) (restr (univ \ S)) ≤ ρ)
    (h h' : ZMod p → ℂ) (hh : meanC h = 0) (hh' : meanC h' = 0) :
    ‖∑ x, (ν.weight x : ℂ) * (conj (kerMap (starKer S) h x) * kerMap (starKer T) h' x)‖ ≤
      ρ * (p : ℝ)⁻¹ * Real.sqrt (l2sq h) * Real.sqrt (l2sq h') :=
  disjoint_star_bound hp2 hp3 ν.weight ν.nonneg ν.total hinv hinj hST hρ0
    (corrBound_of_maxCorr_le ν S (univ \ S) hρ0 hρ) h h' hh hh'

/-- **`lem:general-star`(e), `eq:pair-overlap`, with the hypothesis of `def:prelim:maxcorr`**
(`p ≡ 3 (mod 4)`): for `S = {a, b}`, `T = {a, b'}` (`a, b, b'` distinct) and conditional maximal
correlations of `x_b` and `x_{U∖{a,b}}` given `x_a = α` at most `ρ` for every `α` of positive
probability: `|⟨W_S h, W_T h'⟩_ν| ≤ q (2ρ/(1 − q) + q(q + r)²/(1 − q)²) ‖h‖ ‖h'‖`. -/
theorem pair_overlap_maxCorr (hp2 : p ≠ 2) (hp3 : p % 4 = 3) (ν : FiniteLaw (U → ZMod p))
    (hinv : ∀ (s c : ZMod p) (x : U → ZMod p), s ≠ 0 → IsSquare s →
      ν.weight (affLab s c x) = ν.weight x)
    (hinj : ∀ (x : U → ZMod p) (k l : U), ν.weight x ≠ 0 → k ≠ l → x k ≠ x l)
    {a b b' : U} (hab : a ≠ b) (hab' : a ≠ b') (hbb' : b ≠ b') {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hρ : ∀ α : ZMod p, ∀ hα : 0 < prob ν (fun x => x a = α),
      maxCorr (condLaw ν (fun x => x a = α) hα) (fun x => x b) (restr (univ \ {a, b})) ≤ ρ)
    (h h' : ZMod p → ℂ) (hh : meanC h = 0) (hh' : meanC h' = 0) :
    ‖∑ x, (ν.weight x : ℂ) * (conj (kerMap (starKer {a, b}) h x) * kerMap (starKer {a, b'}) h' x)‖ ≤
      pairOverlapConst p ρ * Real.sqrt (l2sq h) * Real.sqrt (l2sq h') :=
  pair_overlap hp2 hp3 ν.weight ν.nonneg ν.total hinv hinj hab hab' hbb' hρ0
    (condCorrBound_of_maxCorr_le ν a b hρ0 hρ) h h' hh hh'

end Sarkozy.SpectralD.Overlap
