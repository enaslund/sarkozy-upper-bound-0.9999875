module

public import Sarkozy.SpectralD.OverlapDisjoint

@[expose] public section

/-!
# Overlapping pair supports (`lem:general-star`(e), `eq:pair-overlap`)

`paper/sections/14_spectral.tex`, `lem:general-star`(e), second claim. Setting of
`subsec:spec:actual-stars`: `p ≡ 3 (mod 4)`, `μ` an `Aff_p`-invariant law on injective labellings
`x : U → 𝔽_p`, `W_S h = kerMap (starKer S) h`. Let `S = {a, b}`, `T = {a, b'}` with `a, b, b'`
distinct, and let `ρ ≥ 0` bound, for every value `α` of `x_a`, the conditional maximal correlation
of `x_b` and `x_{U∖{a,b}}` given `x_a = α` (hypothesis `CondCorrBound`, `def:prelim:maxcorr` in
inequality form). Then (`pair_overlap`), for mean-zero `h, h'`,
`|⟨W_S h, W_T h'⟩_μ| ≤ q (2ρ/(1 − q) + q(q + r)²/(1 − q)²) ‖h‖ ‖h'‖`,
that is `‖(W_S/r)^*(W_T/r)‖ ≤ 2ρ/(1 − q) + q(q + r)²/(1 − q)²` (`eq:pair-overlap`); in operator form
`pair_overlap_gram`.

The proof follows the paper:
* `pairLaw_eq` (`lem:spec:affpair`(b) for `(x_a, x_b)`, no diagonal mass): the pair law is
  `π(α, β) = (1 − [α = β] + s_ab χ(β − α))/(p(p − 1))`, `s_ab = E_μ χ(x_b − x_a)`;
* `(W_S h)(x) = F_{x_a}(x_b)` with `F_α(β) = E_t χ(t − α) χ(t − β) h(t)` (`pairF`);
* the conditional mean (`fiber_mean`): `E[F_α(x_b) | x_a = α] = (q h(α) + s_ab (Ch)(α))/(p − 1)`
  (`mF`), which is the paper's `(q² h(α) + q s_ab (Ch)(α))/(1 − q)`; it uses `χ(−1) = −1` and the
  two-root identity;
* the split into conditional means and fluctuations on each fibre `x_a = α` (`fiber_decomp`).

**A simplification relative to the paper.** The fluctuation part is bounded here by
`ρ q ‖h‖ ‖h'‖` (`pair_overlap_sharp`): Cauchy–Schwarz over the fibres together with
`‖W_S h‖²_μ ≤ q‖h‖²` (`lem:general-star`(a)) replaces the paper's pointwise conditional bound
`E[|F_α(x_b)|² | x_a = α] ≤ 2r²‖h‖²/(1 − q)`, which loses the factor `2/(1 − q)`. The paper's bound
`eq:pair-overlap` follows since `ρ ≤ 2ρ/(1 − q)`.

**The hypothesis.** `CondCorrBound μ a b ρ` is stated for complex functions and for the
unnormalised sums over the fibre `{x_a = α}` (equivalent to the normalised conditional statement,
since the inequality is homogeneous). It always holds with `ρ = 1` (`condCorrBound_one`), so it is
satisfiable. The passage from the real definition `def:prelim:maxcorr` (under the conditional laws
`μ(· | x_a = α)`) to this complex form is `condCorrBound_of_maxCorr_le` in `OverlapBridge`.

New material for this paper.
-/

namespace Sarkozy.SpectralD.Overlap

open Finset Complex Sarkozy.Characters Sarkozy.SpectralC
open scoped BigOperators ComplexConjugate

variable {p : ℕ} [Fact p.Prime] {U : Type*} [Fintype U] [DecidableEq U]

/-! ## Characters -/

lemma chiRe_cast (t : ZMod p) : ((chiRe t : ℝ) : ℂ) = chiC p t := by
  unfold chiRe; rw [chiC_apply, Complex.ofReal_intCast]

lemma chiRe_neg_one (hp2 : p ≠ 2) (hp3 : p % 4 = 3) : chiRe (-1 : ZMod p) = -1 := by
  have hF : ringChar (ZMod p) ≠ 2 := by rwa [ZMod.ringChar_zmod_n]
  unfold chiRe
  rw [quadraticChar_neg_one hF, ZMod.card, ZMod.χ₄_nat_three_mod_four hp3]
  norm_num

lemma chiRe_swap (hp2 : p ≠ 2) (hp3 : p % 4 = 3) (s t : ZMod p) :
    chiRe (s - t) = -chiRe (t - s) := by
  rw [show s - t = -1 * (t - s) by ring, chiRe_mul, chiRe_neg_one hp2 hp3, neg_one_mul]

lemma chiRe_of_not_isSquare {t : ZMod p} (ht : ¬ IsSquare t) : chiRe t = -1 := by
  unfold chiRe; rw [quadraticChar_neg_one_iff_not_isSquare.mpr ht]; norm_num

lemma sum_chiRe_sub_left (hp2 : p ≠ 2) (t : ZMod p) : ∑ β : ZMod p, chiRe (t - β) = 0 := by
  have e : ∑ β : ZMod p, chiRe (t - β) = ∑ u : ZMod p, chiRe u :=
    Fintype.sum_equiv (Equiv.subLeft t) _ _ (fun β => rfl)
  rw [e]
  have h := quadraticChar_sum_zero (F := ZMod p) (by rwa [ZMod.ringChar_zmod_n])
  unfold chiRe
  exact_mod_cast h

lemma sum_chiRe_sub_sq (α : ZMod p) :
    ∑ β : ZMod p, chiRe (β - α) * chiRe (β - α) = (p : ℝ) - 1 := by
  simp_rw [chiRe_sq_eq]
  rw [sum_sub_distrib, sum_const, card_univ, ZMod.card, nsmul_eq_mul, mul_one, sum_ite_eq']
  simp

/-! ## Weighted sums over a fibre -/

section Fibre

variable {X : Type*}

/-- The split into means and fluctuations: if `∑_s μ = M`, `∑_s μF = Mm`, `∑_s μG = Mm'`, then
`∑_s μ \overline{F} G = ∑_s μ \overline{(F − m)} (G − m') + M \overline{m} m'`. -/
lemma fiber_decomp (s : Finset X) (μ : X → ℝ) (F G : X → ℂ) (m m' : ℂ) (M : ℝ)
    (hM : ∑ x ∈ s, μ x = M) (hF : ∑ x ∈ s, (μ x : ℂ) * F x = (M : ℂ) * m)
    (hG : ∑ x ∈ s, (μ x : ℂ) * G x = (M : ℂ) * m') :
    ∑ x ∈ s, (μ x : ℂ) * (conj (F x) * G x) =
      ∑ x ∈ s, (μ x : ℂ) * (conj (F x - m) * (G x - m')) + (M : ℂ) * (conj m * m') := by
  have e1 : ∑ x ∈ s, (μ x : ℂ) * (conj (F x - m) * (G x - m')) =
      ∑ x ∈ s, (μ x : ℂ) * (conj (F x) * G x) - conj m * ∑ x ∈ s, (μ x : ℂ) * G x -
        m' * ∑ x ∈ s, (μ x : ℂ) * conj (F x) + conj m * m' * ∑ x ∈ s, (μ x : ℂ) := by
    simp only [mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun x _ => ?_
    rw [map_sub]
    ring
  have e2 : ∑ x ∈ s, (μ x : ℂ) * conj (F x) = (M : ℂ) * conj m := by
    have h := congrArg conj hF
    rw [map_sum, map_mul, Complex.conj_ofReal] at h
    rw [← h]
    exact sum_congr rfl fun x _ => by rw [map_mul, Complex.conj_ofReal]
  have e3 : ∑ x ∈ s, (μ x : ℂ) = (M : ℂ) := by rw [← hM]; push_cast; rfl
  rw [e1, hG, e2, e3]
  ring

/-- The variance is at most the second moment: `∑_s μ |F − m|² ≤ ∑_s μ |F|²` when `m` is the
`μ`-mean of `F` on `s`. -/
lemma fiber_var (s : Finset X) (μ : X → ℝ) (hμ0 : ∀ x, 0 ≤ μ x) (F : X → ℂ) (m : ℂ) (M : ℝ)
    (hM : ∑ x ∈ s, μ x = M) (hF : ∑ x ∈ s, (μ x : ℂ) * F x = (M : ℂ) * m) :
    ∑ x ∈ s, μ x * ‖F x - m‖ ^ 2 ≤ ∑ x ∈ s, μ x * ‖F x‖ ^ 2 := by
  have e := fiber_decomp s μ F F m m M hM hF hF
  simp only [Complex.conj_mul'] at e
  have e' : ∑ x ∈ s, μ x * ‖F x‖ ^ 2 = ∑ x ∈ s, μ x * ‖F x - m‖ ^ 2 + M * ‖m‖ ^ 2 := by
    have : ((∑ x ∈ s, μ x * ‖F x‖ ^ 2 : ℝ) : ℂ) =
        ((∑ x ∈ s, μ x * ‖F x - m‖ ^ 2 + M * ‖m‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      exact e
    exact_mod_cast this
  have hM0 : 0 ≤ M := by rw [← hM]; exact sum_nonneg fun x _ => hμ0 x
  rw [e']
  have : 0 ≤ M * ‖m‖ ^ 2 := by positivity
  linarith

/-- Cauchy–Schwarz for a weighted sum over a finite set. -/
lemma fiber_cs (s : Finset X) (μ : X → ℝ) (hμ0 : ∀ x, 0 ≤ μ x) (F G : X → ℂ) :
    ‖∑ x ∈ s, (μ x : ℂ) * (conj (F x) * G x)‖ ≤
      Real.sqrt (∑ x ∈ s, μ x * ‖F x‖ ^ 2) * Real.sqrt (∑ x ∈ s, μ x * ‖G x‖ ^ 2) := by
  calc ‖∑ x ∈ s, (μ x : ℂ) * (conj (F x) * G x)‖
      ≤ ∑ x ∈ s, (Real.sqrt (μ x) * ‖F x‖) * (Real.sqrt (μ x) * ‖G x‖) := by
        refine (norm_sum_le _ _).trans (le_of_eq (sum_congr rfl fun x _ => ?_))
        rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real,
          Real.norm_of_nonneg (hμ0 x)]
        rw [show Real.sqrt (μ x) * ‖F x‖ * (Real.sqrt (μ x) * ‖G x‖) =
          (Real.sqrt (μ x) * Real.sqrt (μ x)) * (‖F x‖ * ‖G x‖) by ring,
          Real.mul_self_sqrt (hμ0 x)]
    _ ≤ Real.sqrt (∑ x ∈ s, (Real.sqrt (μ x) * ‖F x‖) ^ 2) *
          Real.sqrt (∑ x ∈ s, (Real.sqrt (μ x) * ‖G x‖) ^ 2) :=
        Real.sum_mul_le_sqrt_mul_sqrt _ _ _
    _ = Real.sqrt (∑ x ∈ s, μ x * ‖F x‖ ^ 2) * Real.sqrt (∑ x ∈ s, μ x * ‖G x‖ ^ 2) := by
        congr 2 <;> refine sum_congr rfl fun x _ => ?_ <;>
          rw [mul_pow, Real.sq_sqrt (hμ0 x)]

end Fibre

/-! ## The hypothesis -/

/-- **Conditional maximal correlation, inequality form** (`def:prelim:maxcorr`): for every value
`α` of `x_a`, under `μ(· | x_a = α)`, `|E[\overline{f(x_b)} G]| ≤ ρ ‖f(x_b)‖ ‖G‖` for `f(x_b)` a
function of `x_b` and `G` a function of `x_{U∖{a,b}}`, both of conditional mean zero. Stated for
the unnormalised sums over the fibre `{x_a = α}`. -/
def CondCorrBound (μ : (U → ZMod p) → ℝ) (a b : U) (ρ : ℝ) : Prop :=
  ∀ (α : ZMod p) (f : ZMod p → ℂ) (G : (U → ZMod p) → ℂ), DependsOn (univ \ {a, b}) G →
    ∑ x ∈ univ.filter (fun x => x a = α), (μ x : ℂ) * f (x b) = 0 →
    ∑ x ∈ univ.filter (fun x => x a = α), (μ x : ℂ) * G x = 0 →
    ‖∑ x ∈ univ.filter (fun x => x a = α), (μ x : ℂ) * (conj (f (x b)) * G x)‖ ≤
      ρ * Real.sqrt (∑ x ∈ univ.filter (fun x => x a = α), μ x * ‖f (x b)‖ ^ 2) *
        Real.sqrt (∑ x ∈ univ.filter (fun x => x a = α), μ x * ‖G x‖ ^ 2)

/-- **Sanity check** (rule 9): `CondCorrBound` always holds with `ρ = 1`. -/
theorem condCorrBound_one (μ : (U → ZMod p) → ℝ) (hμ0 : ∀ x, 0 ≤ μ x) (a b : U) :
    CondCorrBound μ a b 1 := by
  intro α f G _ _ _
  rw [one_mul]
  exact fiber_cs _ μ hμ0 (fun x => f (x b)) G

/-! ## The pair law -/

/-- The pair marginal `π(α, β) = μ(x_a = α, x_b = β)`. -/
noncomputable def pairLaw (μ : (U → ZMod p) → ℝ) (a b : U) (α β : ZMod p) : ℝ :=
  ∑ x, if x a = α ∧ x b = β then μ x else 0

/-- `s_ab = E_μ χ(x_b − x_a)`. -/
noncomputable def pairCorr (μ : (U → ZMod p) → ℝ) (a b : U) : ℝ :=
  ∑ x, μ x * chiRe (x b - x a)

lemma pairLaw_affInv (μ : (U → ZMod p) → ℝ)
    (hinv : ∀ (s c : ZMod p) (x : U → ZMod p), s ≠ 0 → IsSquare s → μ (affLab s c x) = μ x)
    (a b : U) : IsAffInv (pairLaw μ a b) := by
  intro s c α β hs hsq
  unfold pairLaw
  rw [← (affLab_bijective (U := U) hs c).sum_comp]
  refine sum_congr rfl fun y _ => ?_
  have e : ∀ (i : U) (γ : ZMod p), (affLab s c y i = s * γ + c ↔ y i = γ) := by
    intro i γ
    unfold affLab
    constructor
    · intro h; exact mul_left_cancel₀ hs (by linear_combination h)
    · intro h; rw [h]
  simp only [e, hinv s c y hs hsq]

lemma pairLaw_diag (μ : (U → ZMod p) → ℝ)
    (hinj : ∀ (x : U → ZMod p) (k l : U), μ x ≠ 0 → k ≠ l → x k ≠ x l)
    {a b : U} (hab : a ≠ b) (α : ZMod p) : pairLaw μ a b α α = 0 := by
  unfold pairLaw
  refine sum_eq_zero fun x _ => ?_
  split_ifs with hx
  · by_contra h0
    exact hinj x a b h0 hab (hx.1.trans hx.2.symm)
  · rfl

/-- `∑_{α, β} π(α, β) f(α, β) = E_μ f(x_a, x_b)`. -/
lemma sum_pairLaw_mul (μ : (U → ZMod p) → ℝ) (a b : U) (f : ZMod p → ZMod p → ℝ) :
    ∑ α, ∑ β, pairLaw μ a b α β * f α β = ∑ x, μ x * f (x a) (x b) := by
  have hx : ∀ x : U → ZMod p, μ x * f (x a) (x b) =
      ∑ α, ∑ β, (if x a = α ∧ x b = β then μ x else 0) * f α β := by
    intro x
    rw [sum_eq_single (x a) (fun α _ hα => sum_eq_zero fun β _ => by
      rw [ite_eq_right (fun h => hα h.1.symm), zero_mul]) (fun h => absurd (mem_univ _) h)]
    rw [sum_eq_single (x b) (fun β _ hβ => by rw [ite_eq_right (fun h => hβ h.2.symm), zero_mul])
      (fun h => absurd (mem_univ _) h)]
    simp
  rw [sum_congr rfl fun x _ => hx x]
  unfold pairLaw
  simp_rw [sum_mul]
  calc ∑ α, ∑ β, ∑ x, (if x a = α ∧ x b = β then μ x else 0) * f α β
      = ∑ α, ∑ x, ∑ β, (if x a = α ∧ x b = β then μ x else 0) * f α β :=
        sum_congr rfl fun α _ => sum_comm
    _ = ∑ x, ∑ α, ∑ β, (if x a = α ∧ x b = β then μ x else 0) * f α β := sum_comm

/-- **The pair law** (`lem:spec:affpair`(b) for the pair `(x_a, x_b)`, which has no diagonal
mass): `π(α, β) = (1 − [α = β] + s_ab χ(β − α))/(p(p − 1))`. Any odd `p`. -/
theorem pairLaw_eq (hp2 : p ≠ 2) (μ : (U → ZMod p) → ℝ) (hμ1 : ∑ x, μ x = 1)
    (hinv : ∀ (s c : ZMod p) (x : U → ZMod p), s ≠ 0 → IsSquare s → μ (affLab s c x) = μ x)
    (hinj : ∀ (x : U → ZMod p) (k l : U), μ x ≠ 0 → k ≠ l → x k ≠ x l)
    {a b : U} (hab : a ≠ b) (α β : ZMod p) :
    pairLaw μ a b α β = (1 - (if α = β then 1 else 0) + pairCorr μ a b * chiRe (β - α)) /
      ((p : ℝ) * ((p : ℝ) - 1)) := by
  have hF : ringChar (ZMod p) ≠ 2 := by rwa [ZMod.ringChar_zmod_n]
  obtain ⟨n, hn⟩ := FiniteField.exists_nonsquare hF
  have hκ := pairLaw_affInv μ hinv a b
  set A := (pairLaw μ a b 0 1 + pairLaw μ a b 0 n) / 2 with hA
  set B := (pairLaw μ a b 0 1 - pairLaw μ a b 0 n) / 2 with hB
  have horb : ∀ α β, pairLaw μ a b α β =
      A * (1 - if α = β then 1 else 0) + B * chiRe (β - α) := by
    intro α β
    rw [affInv_orbit (pairLaw μ a b) hκ hn α β]
    by_cases hαβ : α = β
    · subst hαβ
      rw [ite_eq_left rfl, ite_eq_left rfl, pairLaw_diag μ hinj hab, sub_self]
      unfold chiRe
      simp
    · have hd : β - α ≠ 0 := sub_ne_zero.mpr (Ne.symm hαβ)
      rw [ite_eq_right hαβ, ite_eq_right hαβ]
      by_cases hs : IsSquare (β - α)
      · rw [ite_eq_left hs, chiRe_of_isSquare hd hs]; ring
      · rw [ite_eq_right hs, chiRe_of_not_isSquare hs]; ring
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hsum1 : ∀ α : ZMod p, ∑ β, (1 - if α = β then (1 : ℝ) else 0) = (p : ℝ) - 1 := by
    intro α
    rw [sum_sub_distrib, sum_const, card_univ, ZMod.card, nsmul_eq_mul, mul_one, sum_ite_eq]
    simp
  have hsum2 : ∀ α : ZMod p, ∑ β, chiRe (β - α) = 0 := fun α => sum_chiRe_shift hp2 α
  have e1 : ∑ α, ∑ β, pairLaw μ a b α β = A * ((p : ℝ) * ((p : ℝ) - 1)) := by
    simp_rw [horb]
    have : ∀ α : ZMod p, ∑ β, (A * (1 - if α = β then (1 : ℝ) else 0) + B * chiRe (β - α)) =
        A * ((p : ℝ) - 1) := by
      intro α
      rw [sum_add_distrib, ← mul_sum, ← mul_sum, hsum1 α, hsum2 α, mul_zero, add_zero]
    rw [sum_congr rfl fun α _ => this α, sum_const, card_univ, ZMod.card, nsmul_eq_mul]
    ring
  have e2 : ∑ α, ∑ β, pairLaw μ a b α β * chiRe (β - α) = B * ((p : ℝ) * ((p : ℝ) - 1)) := by
    simp_rw [horb]
    have : ∀ α : ZMod p, ∑ β, (A * (1 - if α = β then (1 : ℝ) else 0) + B * chiRe (β - α)) *
        chiRe (β - α) = B * ((p : ℝ) - 1) := by
      intro α
      have h3 : ∑ β, (1 - if α = β then (1 : ℝ) else 0) * chiRe (β - α) = 0 := by
        simp only [sub_mul, one_mul, ite_mul, zero_mul, sum_sub_distrib, sum_ite_eq, mem_univ,
          ite_true, hsum2 α, sub_self]
        unfold chiRe
        simp
      have h4 : ∑ β, (A * (1 - if α = β then (1 : ℝ) else 0) + B * chiRe (β - α)) *
          chiRe (β - α) = A * ∑ β, (1 - if α = β then (1 : ℝ) else 0) * chiRe (β - α) +
            B * ∑ β, chiRe (β - α) * chiRe (β - α) := by
        rw [mul_sum, mul_sum, ← sum_add_distrib]
        exact sum_congr rfl fun β _ => by ring
      rw [h4, h3, sum_chiRe_sub_sq, mul_zero, zero_add]
    rw [sum_congr rfl fun α _ => this α, sum_const, card_univ, ZMod.card, nsmul_eq_mul]
    ring
  have htot := sum_pairLaw_mul μ a b (fun _ _ => 1)
  simp only [mul_one] at htot
  rw [htot, hμ1] at e1
  have hchi := sum_pairLaw_mul μ a b (fun α β => chiRe (β - α))
  have hs : ∑ x, μ x * chiRe (x b - x a) = pairCorr μ a b := rfl
  rw [hchi, hs] at e2
  have hpp : (p : ℝ) * ((p : ℝ) - 1) ≠ 0 := by
    have : (0 : ℝ) < (p : ℝ) - 1 := by linarith
    positivity
  have hA' : A = 1 / ((p : ℝ) * ((p : ℝ) - 1)) := by
    rw [eq_div_iff hpp]; linarith
  have hB' : B = pairCorr μ a b / ((p : ℝ) * ((p : ℝ) - 1)) := by
    rw [eq_div_iff hpp]; linarith
  rw [horb α β, hA', hB']
  field_simp

/-! ## The star maps of the two pairs -/

/-- `F_α(β) = E_t χ(t − α) χ(t − β) h(t)`, so that `(W_{{a,b}} h)(x) = F_{x_a}(x_b)`. -/
noncomputable def pairF (h : ZMod p → ℂ) (α β : ZMod p) : ℂ :=
  ∑ t, (((p : ℝ)⁻¹ * (chiRe (t - α) * chiRe (t - β)) : ℝ) : ℂ) * h t

omit [Fintype U] in
lemma kerMap_starKer_pair {a b : U} (hab : a ≠ b) (h : ZMod p → ℂ) (x : U → ZMod p) :
    kerMap (starKer {a, b}) h x = pairF h (x a) (x b) := by
  unfold kerMap starKer pairF
  refine sum_congr rfl fun t _ => ?_
  rw [prod_pair hab]

lemma sum_pairF (hp2 : p ≠ 2) (h : ZMod p → ℂ) (α : ZMod p) : ∑ β, pairF h α β = 0 := by
  unfold pairF
  rw [sum_comm]
  refine sum_eq_zero fun t _ => ?_
  rw [← sum_mul]
  have e : ∑ β : ZMod p, ((p : ℝ)⁻¹ * (chiRe (t - α) * chiRe (t - β))) = 0 := by
    rw [← mul_sum, ← mul_sum, sum_chiRe_sub_left hp2 t, mul_zero, mul_zero]
  have e' : ∑ β : ZMod p, ((((p : ℝ)⁻¹ * (chiRe (t - α) * chiRe (t - β)) : ℝ)) : ℂ) = 0 := by
    exact_mod_cast e
  rw [e', zero_mul]

lemma pairF_diag (h : ZMod p → ℂ) (hh : ∑ t, h t = 0) (α : ZMod p) :
    pairF h α α = -((p : ℂ)⁻¹ * h α) := by
  unfold pairF
  have e : ∀ t, ((((p : ℝ)⁻¹ * (chiRe (t - α) * chiRe (t - α)) : ℝ)) : ℂ) * h t =
      (p : ℂ)⁻¹ * h t - (if t = α then (p : ℂ)⁻¹ * h t else 0) := by
    intro t
    rw [chiRe_sq_eq]
    split_ifs <;> push_cast <;> ring
  rw [sum_congr rfl fun t _ => e t, sum_sub_distrib, ← mul_sum, hh, mul_zero, sum_ite_eq']
  simp

lemma sum_chiRe_pairF (hp2 : p ≠ 2) (hp3 : p % 4 = 3) (h : ZMod p → ℂ) (α : ZMod p) :
    ∑ β, ((chiRe (β - α) : ℝ) : ℂ) * pairF h α β = gaussOp h α := by
  have hs : ∀ t : ZMod p, ∑ β : ZMod p, chiRe (β - α) * chiRe (t - β) =
      1 - if α = t then (p : ℝ) else 0 := by
    intro t
    simp_rw [chiRe_swap hp2 hp3 t, mul_neg, sum_neg_distrib, sum_chiRe_mul hp2]
    ring
  have key : ∀ t, ∑ β : ZMod p, ((chiRe (β - α) : ℝ) : ℂ) *
      (((((p : ℝ)⁻¹ * (chiRe (t - α) * chiRe (t - β)) : ℝ)) : ℂ) * h t) =
      (p : ℂ)⁻¹ * chiC p (t - α) * h t - (if α = t then chiC p (t - α) * h t else 0) := by
    intro t
    have e : ∀ β : ZMod p, ((chiRe (β - α) : ℝ) : ℂ) *
        (((((p : ℝ)⁻¹ * (chiRe (t - α) * chiRe (t - β)) : ℝ)) : ℂ) * h t) =
        (((chiRe (β - α) * chiRe (t - β) : ℝ)) : ℂ) * ((p : ℂ)⁻¹ * chiC p (t - α) * h t) := by
      intro β
      rw [← chiRe_cast]
      push_cast
      ring
    rw [sum_congr rfl fun β _ => e β, ← sum_mul]
    have e2 : ∑ β : ZMod p, (((chiRe (β - α) * chiRe (t - β) : ℝ)) : ℂ) =
        (((1 - if α = t then (p : ℝ) else 0) : ℝ) : ℂ) := by
      rw [← hs t]; push_cast; rfl
    rw [e2]
    have hpC := p_ne_zero_C (p := p)
    split_ifs with hαt
    · push_cast
      field_simp
    · push_cast
      ring
  unfold pairF gaussOp
  simp_rw [mul_sum]
  rw [sum_comm, sum_congr rfl fun t _ => key t, sum_sub_distrib, sum_ite_eq,
    ite_eq_left (mem_univ _), sub_self, chiC_zero, zero_mul, sub_zero]
  exact sum_congr rfl fun t _ => by ring

/-! ## The conditional means -/

/-- The conditional mean `m_F(α) = (q h(α) + s (Ch)(α))/(p − 1) = (q² h(α) + q s (Ch)(α))/(1 − q)`. -/
noncomputable def mF (s : ℝ) (h : ZMod p → ℂ) (α : ZMod p) : ℂ :=
  ((p : ℂ)⁻¹ * h α + (s : ℂ) * gaussOp h α) / ((p : ℂ) - 1)

lemma ofReal_pairLaw (μ : (U → ZMod p) → ℝ) (a b : U) (α β : ZMod p) :
    ((pairLaw μ a b α β : ℝ) : ℂ) = ∑ x, if x a = α ∧ x b = β then (μ x : ℂ) else 0 := by
  unfold pairLaw
  rw [Complex.ofReal_sum]
  refine sum_congr rfl fun x _ => ?_
  split_ifs <;> simp

/-- Sums over the fibre `x_a = α` of functions of `x_b` are sums against the pair law. -/
lemma sum_fiber_eq (μ : (U → ZMod p) → ℝ) (a b : U) (α : ZMod p) (f : ZMod p → ℂ) :
    ∑ x ∈ univ.filter (fun x => x a = α), (μ x : ℂ) * f (x b) =
      ∑ β, ((pairLaw μ a b α β : ℝ) : ℂ) * f β := by
  simp_rw [ofReal_pairLaw, sum_mul]
  rw [sum_comm, sum_filter]
  refine sum_congr rfl fun x _ => ?_
  by_cases hx : x a = α
  · rw [ite_eq_left hx, sum_eq_single (x b)]
    · simp [hx]
    · intro β _ hβ; simp [hx, Ne.symm hβ]
    · simp
  · rw [ite_eq_right hx]
    exact (sum_eq_zero fun β _ => by simp [hx]).symm

/-- The mass of a fibre: `μ(x_a = α) = q`. -/
lemma fiber_mass (hp2 : p ≠ 2) (μ : (U → ZMod p) → ℝ) (hμ1 : ∑ x, μ x = 1)
    (hinv : ∀ (s c : ZMod p) (x : U → ZMod p), s ≠ 0 → IsSquare s → μ (affLab s c x) = μ x)
    (hinj : ∀ (x : U → ZMod p) (k l : U), μ x ≠ 0 → k ≠ l → x k ≠ x l)
    {a b : U} (hab : a ≠ b) (α : ZMod p) :
    ∑ x ∈ univ.filter (fun x => x a = α), μ x = (p : ℝ)⁻¹ := by
  have h := sum_fiber_eq μ a b α (fun _ => 1)
  simp only [mul_one] at h
  have h2 : ∑ x ∈ univ.filter (fun x => x a = α), μ x = ∑ β, pairLaw μ a b α β := by
    have : ((∑ x ∈ univ.filter (fun x => x a = α), μ x : ℝ) : ℂ) =
        ((∑ β, pairLaw μ a b α β : ℝ) : ℂ) := by push_cast; exact h
    exact_mod_cast this
  rw [h2]
  simp_rw [pairLaw_eq hp2 μ hμ1 hinv hinj hab α]
  rw [← sum_div]
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hnum : ∑ β : ZMod p, (1 - (if α = β then (1 : ℝ) else 0) + pairCorr μ a b *
      chiRe (β - α)) = (p : ℝ) - 1 := by
    rw [sum_add_distrib, ← mul_sum, sum_chiRe_shift hp2 α, mul_zero, add_zero, sum_sub_distrib,
      sum_const, card_univ, ZMod.card, nsmul_eq_mul, mul_one, sum_ite_eq]
    simp
  rw [hnum]
  have : (p : ℝ) - 1 ≠ 0 := by linarith
  field_simp

/-- **The conditional mean** (proof of `lem:general-star`(e)): on the fibre `x_a = α`,
`∑_{x_a = α} μ F_α(x_b) = q m_F(α)`, `m_F(α) = (q h(α) + s_ab (Ch)(α))/(p − 1)`. -/
lemma fiber_mean (hp2 : p ≠ 2) (hp3 : p % 4 = 3) (μ : (U → ZMod p) → ℝ) (hμ1 : ∑ x, μ x = 1)
    (hinv : ∀ (s c : ZMod p) (x : U → ZMod p), s ≠ 0 → IsSquare s → μ (affLab s c x) = μ x)
    (hinj : ∀ (x : U → ZMod p) (k l : U), μ x ≠ 0 → k ≠ l → x k ≠ x l)
    {a b : U} (hab : a ≠ b) (h : ZMod p → ℂ) (hh : meanC h = 0) (α : ZMod p) :
    ∑ x ∈ univ.filter (fun x => x a = α), (μ x : ℂ) * pairF h α (x b) =
      (((p : ℝ)⁻¹ : ℝ) : ℂ) * mF (pairCorr μ a b) h α := by
  have hsum : ∑ t, h t = 0 := by
    unfold meanC at hh
    exact (mul_eq_zero.mp hh).resolve_left (inv_ne_zero p_ne_zero_C)
  rw [sum_fiber_eq μ a b α (pairF h α)]
  simp_rw [pairLaw_eq hp2 μ hμ1 hinv hinj hab α]
  set s := pairCorr μ a b
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hpC := p_ne_zero_C (p := p)
  have hp1C : (p : ℂ) - 1 ≠ 0 := by
    have : ((p : ℝ) - 1 : ℝ) ≠ 0 := by linarith
    exact_mod_cast this
  have e : ∀ β, (((1 - (if α = β then 1 else 0) + s * chiRe (β - α)) /
      ((p : ℝ) * ((p : ℝ) - 1)) : ℝ) : ℂ) * pairF h α β =
      ((p : ℂ) * ((p : ℂ) - 1))⁻¹ * (pairF h α β - (if α = β then pairF h α β else 0) +
        (s : ℂ) * (((chiRe (β - α) : ℝ) : ℂ) * pairF h α β)) := by
    intro β
    split_ifs
    · push_cast
      field_simp
    · push_cast
      field_simp
      ring
  rw [sum_congr rfl fun β _ => e β, ← mul_sum, sum_add_distrib, sum_sub_distrib, sum_ite_eq,
    ite_eq_left (mem_univ _), ← mul_sum, sum_pairF hp2, sum_chiRe_pairF hp2 hp3, pairF_diag h hsum]
  unfold mF
  push_cast
  field_simp
  ring

/-! ## The means part -/

lemma sqrt_l2sq_gaussOp_le (hp2 : p ≠ 2) (h : ZMod p → ℂ) :
    Real.sqrt (l2sq (gaussOp h)) ≤ rp p * Real.sqrt (l2sq h) := by
  have h1 := l2sq_gaussOp_le hp2 h
  have hr : 0 ≤ rp p := by unfold rp; positivity
  calc Real.sqrt (l2sq (gaussOp h)) ≤ Real.sqrt (rp p ^ 2 * l2sq h) := Real.sqrt_le_sqrt h1
    _ = rp p * Real.sqrt (l2sq h) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hr]

/-- Expansion of `⟨c₁f₁ + c₂f₂, d₁g₁ + d₂g₂⟩` and its bound. -/
lemma norm_ip_two_le (c₁ c₂ d₁ d₂ : ℂ) (f₁ f₂ g₁ g₂ : ZMod p → ℂ) :
    ‖ip (fun t => c₁ * f₁ t + c₂ * f₂ t) (fun t => d₁ * g₁ t + d₂ * g₂ t)‖ ≤
      (‖c₁‖ * Real.sqrt (l2sq f₁) + ‖c₂‖ * Real.sqrt (l2sq f₂)) *
        (‖d₁‖ * Real.sqrt (l2sq g₁) + ‖d₂‖ * Real.sqrt (l2sq g₂)) := by
  have e : ip (fun t => c₁ * f₁ t + c₂ * f₂ t) (fun t => d₁ * g₁ t + d₂ * g₂ t) =
      conj c₁ * d₁ * ip f₁ g₁ + conj c₁ * d₂ * ip f₁ g₂ + conj c₂ * d₁ * ip f₂ g₁ +
        conj c₂ * d₂ * ip f₂ g₂ := by
    unfold ip
    have e1 : ∀ t, conj (c₁ * f₁ t + c₂ * f₂ t) * (d₁ * g₁ t + d₂ * g₂ t) =
        conj c₁ * d₁ * (conj (f₁ t) * g₁ t) + conj c₁ * d₂ * (conj (f₁ t) * g₂ t) +
          conj c₂ * d₁ * (conj (f₂ t) * g₁ t) + conj c₂ * d₂ * (conj (f₂ t) * g₂ t) := by
      intro t
      rw [map_add, map_mul, map_mul]
      ring
    rw [sum_congr rfl fun t _ => e1 t]
    simp only [sum_add_distrib, ← mul_sum]
    ring
  rw [e]
  have b1 := norm_ip_le f₁ g₁
  have b2 := norm_ip_le f₁ g₂
  have b3 := norm_ip_le f₂ g₁
  have b4 := norm_ip_le f₂ g₂
  have n1 : ‖conj c₁ * d₁ * ip f₁ g₁‖ ≤ ‖c₁‖ * ‖d₁‖ * (Real.sqrt (l2sq f₁) * Real.sqrt (l2sq g₁)) := by
    rw [norm_mul, norm_mul, Complex.norm_conj]
    exact mul_le_mul_of_nonneg_left b1 (by positivity)
  have n2 : ‖conj c₁ * d₂ * ip f₁ g₂‖ ≤ ‖c₁‖ * ‖d₂‖ * (Real.sqrt (l2sq f₁) * Real.sqrt (l2sq g₂)) := by
    rw [norm_mul, norm_mul, Complex.norm_conj]
    exact mul_le_mul_of_nonneg_left b2 (by positivity)
  have n3 : ‖conj c₂ * d₁ * ip f₂ g₁‖ ≤ ‖c₂‖ * ‖d₁‖ * (Real.sqrt (l2sq f₂) * Real.sqrt (l2sq g₁)) := by
    rw [norm_mul, norm_mul, Complex.norm_conj]
    exact mul_le_mul_of_nonneg_left b3 (by positivity)
  have n4 : ‖conj c₂ * d₂ * ip f₂ g₂‖ ≤ ‖c₂‖ * ‖d₂‖ * (Real.sqrt (l2sq f₂) * Real.sqrt (l2sq g₂)) := by
    rw [norm_mul, norm_mul, Complex.norm_conj]
    exact mul_le_mul_of_nonneg_left b4 (by positivity)
  calc ‖conj c₁ * d₁ * ip f₁ g₁ + conj c₁ * d₂ * ip f₁ g₂ + conj c₂ * d₁ * ip f₂ g₁ +
        conj c₂ * d₂ * ip f₂ g₂‖
      ≤ ‖conj c₁ * d₁ * ip f₁ g₁‖ + ‖conj c₁ * d₂ * ip f₁ g₂‖ + ‖conj c₂ * d₁ * ip f₂ g₁‖ +
          ‖conj c₂ * d₂ * ip f₂ g₂‖ := norm_add₄_le
    _ ≤ _ := by nlinarith [n1, n2, n3, n4]

/-- **The means part** (proof of `lem:general-star`(e)): for `|s|, |s'| ≤ 1`,
`|⟨m_F, m_G⟩| ≤ ((q + r)/(p − 1))² ‖h‖ ‖h'‖ = (q(q + r)/(1 − q))² ‖h‖ ‖h'‖`. -/
lemma norm_ip_mF_le (hp2 : p ≠ 2) {s s' : ℝ} (hs : |s| ≤ 1) (hs' : |s'| ≤ 1)
    (h h' : ZMod p → ℂ) :
    ‖ip (mF s h) (mF s' h')‖ ≤ (((p : ℝ)⁻¹ + rp p) / ((p : ℝ) - 1)) ^ 2 *
      Real.sqrt (l2sq h) * Real.sqrt (l2sq h') := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp1' : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hp1C : (p : ℂ) - 1 = (((p : ℝ) - 1 : ℝ) : ℂ) := by push_cast; rfl
  have hmF : ∀ (σ : ℝ) (g : ZMod p → ℂ), mF σ g = fun t =>
      ((((p : ℝ)⁻¹ / ((p : ℝ) - 1) : ℝ)) : ℂ) * g t +
        (((σ / ((p : ℝ) - 1) : ℝ)) : ℂ) * gaussOp g t := by
    intro σ g
    funext t
    unfold mF
    rw [hp1C]
    have : ((p : ℝ) - 1 : ℝ) ≠ 0 := by linarith
    push_cast
    field_simp
  rw [hmF s h, hmF s' h']
  refine (norm_ip_two_le _ _ _ _ _ _ _ _).trans ?_
  have hr0 : 0 ≤ rp p := by unfold rp; positivity
  have hC := sqrt_l2sq_gaussOp_le hp2 h
  have hC' := sqrt_l2sq_gaussOp_le hp2 h'
  have n1 : ‖((((p : ℝ)⁻¹ / ((p : ℝ) - 1) : ℝ)) : ℂ)‖ = (p : ℝ)⁻¹ / ((p : ℝ) - 1) := by
    rw [Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have n2 : ∀ σ : ℝ, |σ| ≤ 1 → ‖(((σ / ((p : ℝ) - 1) : ℝ)) : ℂ)‖ ≤ 1 / ((p : ℝ) - 1) := by
    intro σ hσ
    rw [Complex.norm_real, Real.norm_eq_abs, abs_div, abs_of_pos hp1']
    exact div_le_div_of_nonneg_right hσ hp1'.le
  have hsh := Real.sqrt_nonneg (l2sq h)
  have hsh' := Real.sqrt_nonneg (l2sq h')
  have k1 : ‖((((p : ℝ)⁻¹ / ((p : ℝ) - 1) : ℝ)) : ℂ)‖ * Real.sqrt (l2sq h) +
      ‖(((s / ((p : ℝ) - 1) : ℝ)) : ℂ)‖ * Real.sqrt (l2sq (gaussOp h)) ≤
      ((p : ℝ)⁻¹ + rp p) / ((p : ℝ) - 1) * Real.sqrt (l2sq h) := by
    rw [n1]
    have := mul_le_mul (n2 s hs) hC (Real.sqrt_nonneg _) (by positivity)
    have e : ((p : ℝ)⁻¹ + rp p) / ((p : ℝ) - 1) * Real.sqrt (l2sq h) =
        (p : ℝ)⁻¹ / ((p : ℝ) - 1) * Real.sqrt (l2sq h) +
          1 / ((p : ℝ) - 1) * (rp p * Real.sqrt (l2sq h)) := by ring
    rw [e]
    linarith
  have k2 : ‖((((p : ℝ)⁻¹ / ((p : ℝ) - 1) : ℝ)) : ℂ)‖ * Real.sqrt (l2sq h') +
      ‖(((s' / ((p : ℝ) - 1) : ℝ)) : ℂ)‖ * Real.sqrt (l2sq (gaussOp h')) ≤
      ((p : ℝ)⁻¹ + rp p) / ((p : ℝ) - 1) * Real.sqrt (l2sq h') := by
    rw [n1]
    have := mul_le_mul (n2 s' hs') hC' (Real.sqrt_nonneg _) (by positivity)
    have e : ((p : ℝ)⁻¹ + rp p) / ((p : ℝ) - 1) * Real.sqrt (l2sq h') =
        (p : ℝ)⁻¹ / ((p : ℝ) - 1) * Real.sqrt (l2sq h') +
          1 / ((p : ℝ) - 1) * (rp p * Real.sqrt (l2sq h')) := by ring
    rw [e]
    linarith
  calc _ ≤ (((p : ℝ)⁻¹ + rp p) / ((p : ℝ) - 1) * Real.sqrt (l2sq h)) *
        (((p : ℝ)⁻¹ + rp p) / ((p : ℝ) - 1) * Real.sqrt (l2sq h')) :=
        mul_le_mul k1 k2 (by positivity) (by positivity)
    _ = (((p : ℝ)⁻¹ + rp p) / ((p : ℝ) - 1)) ^ 2 * Real.sqrt (l2sq h) *
          Real.sqrt (l2sq h') := by ring

lemma abs_pairCorr_le (μ : (U → ZMod p) → ℝ) (hμ0 : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1)
    (a b : U) : |pairCorr μ a b| ≤ 1 := by
  unfold pairCorr
  calc |∑ x, μ x * chiRe (x b - x a)| ≤ ∑ x, μ x * 1 := by
        refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun x _ => ?_)
        rw [abs_mul, abs_of_nonneg (hμ0 x)]
        exact mul_le_mul_of_nonneg_left (abs_chiRe_le _) (hμ0 x)
    _ = 1 := by rw [← sum_mul, hμ1, one_mul]

/-! ## The bound -/

lemma sqrt_mul_sqrt_le_of_le {A B l l' q : ℝ} (hq : 0 ≤ q) (hA : A ≤ q * l) (hB : B ≤ q * l') :
    Real.sqrt A * Real.sqrt B ≤ q * Real.sqrt l * Real.sqrt l' := by
  have h1 : Real.sqrt A ≤ Real.sqrt q * Real.sqrt l := by
    rw [← Real.sqrt_mul hq]; exact Real.sqrt_le_sqrt hA
  have h2 : Real.sqrt B ≤ Real.sqrt q * Real.sqrt l' := by
    rw [← Real.sqrt_mul hq]; exact Real.sqrt_le_sqrt hB
  have hqq : Real.sqrt q * Real.sqrt q = q := Real.mul_self_sqrt hq
  calc Real.sqrt A * Real.sqrt B ≤ (Real.sqrt q * Real.sqrt l) * (Real.sqrt q * Real.sqrt l') :=
        mul_le_mul h1 h2 (Real.sqrt_nonneg _) (by positivity)
    _ = (Real.sqrt q * Real.sqrt q) * Real.sqrt l * Real.sqrt l' := by ring
    _ = q * Real.sqrt l * Real.sqrt l' := by rw [hqq]

/-- **`lem:general-star`(e), overlapping pair supports, sharp form** (`p ≡ 3 (mod 4)`): for
`S = {a, b}`, `T = {a, b'}` with `a, b, b'` distinct and `ρ ≥ 0` bounding, for every value of
`x_a`, the conditional maximal correlation of `x_b` and `x_{U∖{a,b}}` given `x_a` (hypothesis
`hρ`), `|⟨W_S h, W_T h'⟩_μ| ≤ (ρ q + ((q + r)/(p − 1))²) ‖h‖ ‖h'‖` on `L²_0`. Here
`((q + r)/(p − 1))² = q²(q + r)²/(1 − q)²` is the means part and `ρ q` the fluctuation part. -/
theorem pair_overlap_sharp (hp2 : p ≠ 2) (hp3 : p % 4 = 3) (μ : (U → ZMod p) → ℝ)
    (hμ0 : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1)
    (hinv : ∀ (s c : ZMod p) (x : U → ZMod p), s ≠ 0 → IsSquare s → μ (affLab s c x) = μ x)
    (hinj : ∀ (x : U → ZMod p) (k l : U), μ x ≠ 0 → k ≠ l → x k ≠ x l)
    {a b b' : U} (hab : a ≠ b) (hab' : a ≠ b') (hbb' : b ≠ b') {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hρ : CondCorrBound μ a b ρ) (h h' : ZMod p → ℂ) (hh : meanC h = 0) (hh' : meanC h' = 0) :
    ‖∑ x, (μ x : ℂ) * (conj (kerMap (starKer {a, b}) h x) * kerMap (starKer {a, b'}) h' x)‖ ≤
      (ρ * (p : ℝ)⁻¹ + (((p : ℝ)⁻¹ + rp p) / ((p : ℝ) - 1)) ^ 2) *
        Real.sqrt (l2sq h) * Real.sqrt (l2sq h') := by
  set F : (U → ZMod p) → ℂ := kerMap (starKer {a, b}) h with hFdef
  set G : (U → ZMod p) → ℂ := kerMap (starKer {a, b'}) h' with hGdef
  set m : ZMod p → ℂ := mF (pairCorr μ a b) h with hmdef
  set m' : ZMod p → ℂ := mF (pairCorr μ a b') h' with hm'def
  have hFfib : ∀ α, ∀ x ∈ univ.filter (fun x : U → ZMod p => x a = α), F x = pairF h α (x b) :=
    fun α x hx => by rw [hFdef, kerMap_starKer_pair hab, (mem_filter.mp hx).2]
  have hGfib : ∀ α, ∀ x ∈ univ.filter (fun x : U → ZMod p => x a = α),
      G x = pairF h' α (x b') :=
    fun α x hx => by rw [hGdef, kerMap_starKer_pair hab', (mem_filter.mp hx).2]
  have hM : ∀ α, ∑ x ∈ univ.filter (fun x : U → ZMod p => x a = α), μ x = (p : ℝ)⁻¹ :=
    fiber_mass hp2 μ hμ1 hinv hinj hab
  have hMC : ∀ α, ∑ x ∈ univ.filter (fun x : U → ZMod p => x a = α), (μ x : ℂ) =
      (((p : ℝ)⁻¹ : ℝ) : ℂ) := fun α => by rw [← hM α]; push_cast; rfl
  have hmeanF : ∀ α, ∑ x ∈ univ.filter (fun x : U → ZMod p => x a = α), (μ x : ℂ) * F x =
      (((p : ℝ)⁻¹ : ℝ) : ℂ) * m α := by
    intro α
    rw [sum_congr rfl fun x hx => by rw [hFfib α x hx]]
    exact fiber_mean hp2 hp3 μ hμ1 hinv hinj hab h hh α
  have hmeanG : ∀ α, ∑ x ∈ univ.filter (fun x : U → ZMod p => x a = α), (μ x : ℂ) * G x =
      (((p : ℝ)⁻¹ : ℝ) : ℂ) * m' α := by
    intro α
    rw [sum_congr rfl fun x hx => by rw [hGfib α x hx]]
    exact fiber_mean hp2 hp3 μ hμ1 hinv hinj hab' h' hh' α
  -- the fluctuations on one fibre
  have hfluct : ∀ α, ‖∑ x ∈ univ.filter (fun x : U → ZMod p => x a = α),
      (μ x : ℂ) * (conj (F x - m α) * (G x - m' α))‖ ≤
      ρ * Real.sqrt (∑ x ∈ univ.filter (fun x : U → ZMod p => x a = α), μ x * ‖F x‖ ^ 2) *
        Real.sqrt (∑ x ∈ univ.filter (fun x : U → ZMod p => x a = α), μ x * ‖G x‖ ^ 2) := by
    intro α
    have hdep : DependsOn (univ \ {a, b}) (fun x : U → ZMod p => pairF h' α (x b') - m' α) := by
      intro x x' hxx'
      have hb' : b' ∈ univ \ {a, b} := by
        simp only [mem_sdiff, mem_univ, mem_insert, mem_singleton, true_and, not_or]
        exact ⟨Ne.symm hab', Ne.symm hbb'⟩
      simp only [hxx' b' hb']
    have hf0 : ∑ x ∈ univ.filter (fun x : U → ZMod p => x a = α),
        (μ x : ℂ) * (pairF h α (x b) - m α) = 0 := by
      have e : ∑ x ∈ univ.filter (fun x : U → ZMod p => x a = α),
          (μ x : ℂ) * (pairF h α (x b) - m α) =
          ∑ x ∈ univ.filter (fun x : U → ZMod p => x a = α), (μ x : ℂ) * F x -
            (∑ x ∈ univ.filter (fun x : U → ZMod p => x a = α), (μ x : ℂ)) * m α := by
        rw [sum_mul, ← sum_sub_distrib]
        exact sum_congr rfl fun x hx => by rw [hFfib α x hx]; ring
      rw [e, hmeanF α, hMC α, sub_self]
    have hg0 : ∑ x ∈ univ.filter (fun x : U → ZMod p => x a = α),
        (μ x : ℂ) * (pairF h' α (x b') - m' α) = 0 := by
      have e : ∑ x ∈ univ.filter (fun x : U → ZMod p => x a = α),
          (μ x : ℂ) * (pairF h' α (x b') - m' α) =
          ∑ x ∈ univ.filter (fun x : U → ZMod p => x a = α), (μ x : ℂ) * G x -
            (∑ x ∈ univ.filter (fun x : U → ZMod p => x a = α), (μ x : ℂ)) * m' α := by
        rw [sum_mul, ← sum_sub_distrib]
        exact sum_congr rfl fun x hx => by rw [hGfib α x hx]; ring
      rw [e, hmeanG α, hMC α, sub_self]
    have hb := hρ α (fun β => pairF h α β - m α) (fun x => pairF h' α (x b') - m' α) hdep hf0 hg0
    have e1 : ∑ x ∈ univ.filter (fun x : U → ZMod p => x a = α),
        (μ x : ℂ) * (conj (pairF h α (x b) - m α) * (pairF h' α (x b') - m' α)) =
        ∑ x ∈ univ.filter (fun x : U → ZMod p => x a = α),
          (μ x : ℂ) * (conj (F x - m α) * (G x - m' α)) :=
      sum_congr rfl fun x hx => by rw [hFfib α x hx, hGfib α x hx]
    have e2 : ∑ x ∈ univ.filter (fun x : U → ZMod p => x a = α),
        μ x * ‖pairF h α (x b) - m α‖ ^ 2 =
        ∑ x ∈ univ.filter (fun x : U → ZMod p => x a = α), μ x * ‖F x - m α‖ ^ 2 :=
      sum_congr rfl fun x hx => by rw [hFfib α x hx]
    have e3 : ∑ x ∈ univ.filter (fun x : U → ZMod p => x a = α),
        μ x * ‖pairF h' α (x b') - m' α‖ ^ 2 =
        ∑ x ∈ univ.filter (fun x : U → ZMod p => x a = α), μ x * ‖G x - m' α‖ ^ 2 :=
      sum_congr rfl fun x hx => by rw [hGfib α x hx]
    rw [e1, e2, e3] at hb
    refine hb.trans ?_
    have v1 := fiber_var _ μ hμ0 F (m α) _ (hM α) (hmeanF α)
    have v2 := fiber_var _ μ hμ0 G (m' α) _ (hM α) (hmeanG α)
    exact mul_le_mul (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt v1) hρ0)
      (Real.sqrt_le_sqrt v2) (Real.sqrt_nonneg _) (mul_nonneg hρ0 (Real.sqrt_nonneg _))
  -- the decomposition of the whole sum
  have htot : ∑ x, (μ x : ℂ) * (conj (F x) * G x) =
      ∑ α, ∑ x ∈ univ.filter (fun x : U → ZMod p => x a = α),
        (μ x : ℂ) * (conj (F x - m α) * (G x - m' α)) + ip m m' := by
    rw [← sum_fiberwise univ (fun x : U → ZMod p => x a)
      (fun x => (μ x : ℂ) * (conj (F x) * G x))]
    rw [sum_congr rfl fun α _ => fiber_decomp _ μ F G (m α) (m' α) _ (hM α) (hmeanF α)
      (hmeanG α), sum_add_distrib]
    congr 1
    unfold ip
    rw [mul_sum]
    push_cast
    rfl
  rw [htot]
  have hA : ∑ α, ∑ x ∈ univ.filter (fun x : U → ZMod p => x a = α), μ x * ‖F x‖ ^ 2 =
      ∑ x, μ x * ‖F x‖ ^ 2 := sum_fiberwise univ (fun x : U → ZMod p => x a) _
  have hB : ∑ α, ∑ x ∈ univ.filter (fun x : U → ZMod p => x a = α), μ x * ‖G x‖ ^ 2 =
      ∑ x, μ x * ‖G x‖ ^ 2 := sum_fiberwise univ (fun x : U → ZMod p => x a) _
  have hnF := norm_starMap_sq_le hp2 hp3 μ hμ0 hμ1 hinv hinj {a, b} h hh
  have hnG := norm_starMap_sq_le hp2 hp3 μ hμ0 hμ1 hinv hinj {a, b'} h' hh'
  have hfl : ‖∑ α, ∑ x ∈ univ.filter (fun x : U → ZMod p => x a = α),
      (μ x : ℂ) * (conj (F x - m α) * (G x - m' α))‖ ≤
      ρ * (p : ℝ)⁻¹ * Real.sqrt (l2sq h) * Real.sqrt (l2sq h') := by
    have hA0 : ∀ α, 0 ≤ ∑ x ∈ univ.filter (fun x : U → ZMod p => x a = α), μ x * ‖F x‖ ^ 2 :=
      fun α => sum_nonneg fun x _ => mul_nonneg (hμ0 x) (sq_nonneg _)
    have hB0 : ∀ α, 0 ≤ ∑ x ∈ univ.filter (fun x : U → ZMod p => x a = α), μ x * ‖G x‖ ^ 2 :=
      fun α => sum_nonneg fun x _ => mul_nonneg (hμ0 x) (sq_nonneg _)
    calc _ ≤ ∑ α, ‖∑ x ∈ univ.filter (fun x : U → ZMod p => x a = α),
          (μ x : ℂ) * (conj (F x - m α) * (G x - m' α))‖ := norm_sum_le _ _
      _ ≤ ∑ α, ρ * Real.sqrt (∑ x ∈ univ.filter (fun x : U → ZMod p => x a = α),
            μ x * ‖F x‖ ^ 2) *
            Real.sqrt (∑ x ∈ univ.filter (fun x : U → ZMod p => x a = α), μ x * ‖G x‖ ^ 2) :=
          sum_le_sum fun α _ => hfluct α
      _ = ρ * ∑ α, Real.sqrt (∑ x ∈ univ.filter (fun x : U → ZMod p => x a = α),
            μ x * ‖F x‖ ^ 2) *
            Real.sqrt (∑ x ∈ univ.filter (fun x : U → ZMod p => x a = α), μ x * ‖G x‖ ^ 2) := by
          rw [mul_sum]; exact sum_congr rfl fun α _ => by ring
      _ ≤ ρ * (Real.sqrt (∑ α, ∑ x ∈ univ.filter (fun x : U → ZMod p => x a = α),
            μ x * ‖F x‖ ^ 2) *
            Real.sqrt (∑ α, ∑ x ∈ univ.filter (fun x : U → ZMod p => x a = α),
              μ x * ‖G x‖ ^ 2)) :=
          mul_le_mul_of_nonneg_left (Real.sum_sqrt_mul_sqrt_le _ hA0 hB0) hρ0
      _ = ρ * (Real.sqrt (∑ x, μ x * ‖F x‖ ^ 2) * Real.sqrt (∑ x, μ x * ‖G x‖ ^ 2)) := by
          rw [hA, hB]
      _ ≤ ρ * ((p : ℝ)⁻¹ * Real.sqrt (l2sq h) * Real.sqrt (l2sq h')) :=
          mul_le_mul_of_nonneg_left (sqrt_mul_sqrt_le_of_le (by positivity) hnF hnG) hρ0
      _ = ρ * (p : ℝ)⁻¹ * Real.sqrt (l2sq h) * Real.sqrt (l2sq h') := by ring
  have hmn := norm_ip_mF_le hp2 (abs_pairCorr_le μ hμ0 hμ1 a b) (abs_pairCorr_le μ hμ0 hμ1 a b')
    h h'
  calc _ ≤ ‖∑ α, ∑ x ∈ univ.filter (fun x : U → ZMod p => x a = α),
          (μ x : ℂ) * (conj (F x - m α) * (G x - m' α))‖ + ‖ip m m'‖ := norm_add_le _ _
    _ ≤ ρ * (p : ℝ)⁻¹ * Real.sqrt (l2sq h) * Real.sqrt (l2sq h') +
          (((p : ℝ)⁻¹ + rp p) / ((p : ℝ) - 1)) ^ 2 * Real.sqrt (l2sq h) * Real.sqrt (l2sq h') :=
        add_le_add hfl hmn
    _ = _ := by ring

/-- The constant of `eq:pair-overlap` times `q`: `q (2ρ/(1 − q) + q(q + r)²/(1 − q)²)`. -/
noncomputable def pairOverlapConst (p : ℕ) (ρ : ℝ) : ℝ :=
  (p : ℝ)⁻¹ * (2 * ρ / (1 - (p : ℝ)⁻¹) +
    (p : ℝ)⁻¹ * ((p : ℝ)⁻¹ + rp p) ^ 2 / (1 - (p : ℝ)⁻¹) ^ 2)

lemma sharp_le_pairOverlapConst {ρ : ℝ} (hρ0 : 0 ≤ ρ) :
    ρ * (p : ℝ)⁻¹ + (((p : ℝ)⁻¹ + rp p) / ((p : ℝ) - 1)) ^ 2 ≤ pairOverlapConst p ρ := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hq0 : 0 < (p : ℝ)⁻¹ := by positivity
  have hq1 : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp1
  have h1q : 0 < 1 - (p : ℝ)⁻¹ := by linarith
  have hp0 : (p : ℝ) ≠ 0 := by positivity
  have hp1' : (p : ℝ) - 1 ≠ 0 := by linarith
  have e : (((p : ℝ)⁻¹ + rp p) / ((p : ℝ) - 1)) ^ 2 =
      (p : ℝ)⁻¹ * ((p : ℝ)⁻¹ * ((p : ℝ)⁻¹ + rp p) ^ 2 / (1 - (p : ℝ)⁻¹) ^ 2) := by
    field_simp
  have hρ : ρ * (p : ℝ)⁻¹ ≤ (p : ℝ)⁻¹ * (2 * ρ / (1 - (p : ℝ)⁻¹)) := by
    rw [mul_comm]
    apply mul_le_mul_of_nonneg_left _ hq0.le
    rw [le_div_iff₀ h1q]
    nlinarith
  unfold pairOverlapConst
  rw [e, mul_add]
  linarith

/-- **`lem:general-star`(e), `eq:pair-overlap`** (`p ≡ 3 (mod 4)`): for `S = {a, b}`,
`T = {a, b'}` with `a, b, b'` distinct and `ρ ≥ 0` bounding, for every value of `x_a`, the
conditional maximal correlation of `x_b` and `x_{U∖{a,b}}` given `x_a` (hypothesis `hρ`),
`|⟨W_S h, W_T h'⟩_μ| ≤ q (2ρ/(1 − q) + q(q + r)²/(1 − q)²) ‖h‖ ‖h'‖` on `L²_0`, that is
`‖(W_S/r)^*(W_T/r)‖ ≤ 2ρ/(1 − q) + q(q + r)²/(1 − q)²`. -/
theorem pair_overlap (hp2 : p ≠ 2) (hp3 : p % 4 = 3) (μ : (U → ZMod p) → ℝ)
    (hμ0 : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1)
    (hinv : ∀ (s c : ZMod p) (x : U → ZMod p), s ≠ 0 → IsSquare s → μ (affLab s c x) = μ x)
    (hinj : ∀ (x : U → ZMod p) (k l : U), μ x ≠ 0 → k ≠ l → x k ≠ x l)
    {a b b' : U} (hab : a ≠ b) (hab' : a ≠ b') (hbb' : b ≠ b') {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hρ : CondCorrBound μ a b ρ) (h h' : ZMod p → ℂ) (hh : meanC h = 0) (hh' : meanC h' = 0) :
    ‖∑ x, (μ x : ℂ) * (conj (kerMap (starKer {a, b}) h x) * kerMap (starKer {a, b'}) h' x)‖ ≤
      pairOverlapConst p ρ * Real.sqrt (l2sq h) * Real.sqrt (l2sq h') := by
  refine (pair_overlap_sharp hp2 hp3 μ hμ0 hμ1 hinv hinj hab hab' hbb' hρ0 hρ h h' hh hh').trans ?_
  have hs := mul_nonneg (Real.sqrt_nonneg (l2sq h)) (Real.sqrt_nonneg (l2sq h'))
  have := mul_le_mul_of_nonneg_right (sharp_le_pairOverlapConst (p := p) hρ0) hs
  calc _ = (ρ * (p : ℝ)⁻¹ + (((p : ℝ)⁻¹ + rp p) / ((p : ℝ) - 1)) ^ 2) *
        (Real.sqrt (l2sq h) * Real.sqrt (l2sq h')) := by ring
    _ ≤ pairOverlapConst p ρ * (Real.sqrt (l2sq h) * Real.sqrt (l2sq h')) := this
    _ = _ := by ring

/-- **`lem:general-star`(e), `eq:pair-overlap`, operator form** (`p ≡ 3 (mod 4)`): under the
hypotheses of `pair_overlap`, `‖W_S^*W_T h'‖² ≤ (q (2ρ/(1 − q) + q(q + r)²/(1 − q)²))² ‖h'‖²`. -/
theorem pair_overlap_gram (hp2 : p ≠ 2) (hp3 : p % 4 = 3) (μ : (U → ZMod p) → ℝ)
    (hμ0 : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1)
    (hinv : ∀ (s c : ZMod p) (x : U → ZMod p), s ≠ 0 → IsSquare s → μ (affLab s c x) = μ x)
    (hinj : ∀ (x : U → ZMod p) (k l : U), μ x ≠ 0 → k ≠ l → x k ≠ x l)
    {a b b' : U} (hab : a ≠ b) (hab' : a ≠ b') (hbb' : b ≠ b') {ρ : ℝ} (hρ0 : 0 ≤ ρ)
    (hρ : CondCorrBound μ a b ρ) (h' : ZMod p → ℂ) (hh' : meanC h' = 0) :
    l2sq (gramOp μ (starKer {a, b}) (starKer {a, b'}) h') ≤
      pairOverlapConst p ρ ^ 2 * l2sq h' := by
  set u := gramOp μ (starKer {a, b}) (starKer {a, b'}) h' with hu
  have hu0 : meanC u = 0 := meanC_gramOp_star hp2 μ hinv {a, b} {a, b'} h' hh'
  apply l2sq_le_of_self_ip
  have e := ip_kerMap μ (starKer {a, b}) (starKer {a, b'}) u h'
  rw [← hu] at e
  rw [← e]
  exact pair_overlap hp2 hp3 μ hμ0 hμ1 hinv hinj hab hab' hbb' hρ0 hρ u h' hu0 hh'

end Sarkozy.SpectralD.Overlap
