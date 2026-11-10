module

public import Sarkozy.SpectralD.WeilStars

@[expose] public section

/-!
# Singleton–star entries (`lem:general-star`(d), `eq:singleton-star`): the Weil cases

`paper/sections/14_spectral.tex`, `lem:general-star`(d). Setting of `subsec:spec:actual-stars`:
`p ≡ 3 (mod 4)`, `μ` an `Aff_p`-invariant law on labellings `x : U → 𝔽_p`, supported on
injective labellings. For the singleton `V_i` (`vertKer i`) and the star `W_S` (`starKer S`),
WP-K's `gram_two_traces_le` bounds `‖V_i^*W_S‖` through the two traces
`tr(V_i^*W_S) = E_μ(ψ_S(x_i, x) − w_S)` and `β_i = tr(C^*V_i^*W_S) = E_μ E_z χ(z − x_i)ψ_S(z, x)`
(`vert_star_gtrace`, `vert_star_gtraceC`), and WP-K proved the case `i ∈ S`, `|S| = 2`
(`SpectralC.vert_star_pair_bound`). This file proves the other three cases of
`eq:singleton-star`, with `thm:weil` as the hypothesis `Labellings.WeilBound (ZMod p)`
(from `Target.Weil` by `Labellings.weilBound_of_target`):

* `vert_star_out_bound` (`i ∉ S`, `k = |S| ≥ 1`):
  `(1 − q)‖V_i^*W_S‖/r ≤ (r²(1 + (k − 1)r)² + k²q)^{1/2}`. Here `|ψ_S(x_i, x)| ≤ 1`,
  `|w_S| ≤ (k − 1)r` and `β_i = E_μ w_{S∪{i}}`, `|β_i| ≤ kr` (Weil).
* `vert_star_three_bound` (`i ∈ S`, `k = 3`): `(1 − q)‖V_i^*W_S‖/r ≤ 2√2 q`.
* `vert_star_large_bound` (`i ∈ S`, `k ≥ 4`):
  `(1 − q)‖V_i^*W_S‖/r ≤ ((k − 1)²q² + ((k − 2)r + q)²)^{1/2}`.

For `i ∈ S` the traces are `−E_μ w_S` and `β_i = E_μ(w_{S∖i} − qψ_{S∖i}(x_i, x))`
(`sum_chiRe_mul_starKer_mem`), so `|tr| ≤ (k − 1)r` and `|β_i| ≤ a_{k−1} + q`
(`vert_star_mem_bound`, with `aConst`: `w_{S∖i} = −q` for `k = 3`, Weil for `k ≥ 4`).

All norms are in squared form, `‖V_i^*W_S h‖² ≤ c ‖h‖²` on `L²_0`: the bound
`(1 − q)‖V_i^*W_S‖/r ≤ X^{1/2}` is `‖V_i^*W_S h‖² ≤ q X/(1 − q)² ‖h‖²`.

New material for this paper.
-/

namespace Sarkozy.SpectralD

open Finset Sarkozy.SpectralC
open scoped BigOperators

variable {p : ℕ} [Fact p.Prime] {U : Type*} [Fintype U] [DecidableEq U]

omit [Fact p.Prime] in
lemma rp_sq : rp p ^ 2 = (p : ℝ)⁻¹ := by
  unfold rp
  rw [inv_pow, Real.sq_sqrt (Nat.cast_nonneg p)]

omit [Fact p.Prime] in
lemma rp_nonneg : 0 ≤ rp p := by unfold rp; positivity

omit [Fintype U] [DecidableEq U] in
/-- `ψ_S(x_i, x) = 0` for `i ∈ S`. -/
lemma prod_chiRe_self_zero {S : Finset U} {i : U} (hi : i ∈ S) (x : U → ZMod p) :
    ∏ k ∈ S, chiRe (x i - x k) = 0 := by
  apply prod_eq_zero hi
  rw [sub_self]
  unfold chiRe
  simp

omit [Fintype U] in
/-- For `i ∉ S`: `χ(b − x_i) (p⁻¹ψ_S(b, x)) = p⁻¹ψ_{S∪{i}}(b, x)`. -/
lemma chiRe_mul_starKer_not_mem {S : Finset U} {i : U} (hi : i ∉ S) (x : U → ZMod p)
    (b : ZMod p) : chiRe (b - x i) * starKer S x b = starKer (insert i S) x b := by
  unfold starKer
  rw [prod_insert hi]
  ring

omit [Fintype U] in
/-- For `i ∈ S`: `∑_b χ(b − x_i)(p⁻¹ψ_S(b, x)) = w_{S∖i}(x) − q ψ_{S∖i}(x_i, x)`. -/
lemma sum_chiRe_mul_starKer_mem {S : Finset U} {i : U} (hi : i ∈ S) (x : U → ZMod p) :
    ∑ b, chiRe (b - x i) * starKer S x b =
      starMean (S.erase i) x - (p : ℝ)⁻¹ * psiRest S i x (x i) := by
  have h1 : ∀ b, chiRe (b - x i) * starKer S x b =
      starKer (S.erase i) x b - if b = x i then (p : ℝ)⁻¹ * psiRest S i x b else 0 := by
    intro b
    unfold starKer psiRest
    rw [← mul_prod_erase S _ hi]
    have e : chiRe (b - x i) * ((p : ℝ)⁻¹ * (chiRe (b - x i) * ∏ k ∈ S.erase i, chiRe (b - x k))) =
        (p : ℝ)⁻¹ * (chiRe (b - x i) * chiRe (b - x i)) * ∏ k ∈ S.erase i, chiRe (b - x k) := by
      ring
    rw [e, chiRe_sq_eq]
    split_ifs <;> ring
  rw [sum_congr rfl fun b _ => h1 b, sum_sub_distrib, sum_ite_eq']
  simp only [mem_univ, ↓reduceIte]
  rfl

/-- The two traces of `V_i^*W_S` for `i ∉ S`: `|tr| ≤ 1 + (k − 1)r`, `|β_i| ≤ kr`. -/
theorem vert_star_not_mem_traces (hW : Labellings.WeilBound (ZMod p)) (μ : (U → ZMod p) → ℝ)
    (hμ0 : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1)
    (hinj : ∀ (x : U → ZMod p) (k l : U), μ x ≠ 0 → k ≠ l → x k ≠ x l)
    {S : Finset U} (hS : S.Nonempty) {i : U} (hi : i ∉ S) :
    |gtrace μ (vertKer i) (starKer S)| ≤ 1 + ((S.card : ℝ) - 1) * rp p ∧
      |gtraceC μ (vertKer i) (starKer S)| ≤ (S.card : ℝ) * rp p := by
  have hinjOn : ∀ x, μ x ≠ 0 → ∀ R : Finset U, Set.InjOn x R := fun x hx R a _ b _ hab => by
    by_contra hne; exact hinj x a b hx hne hab
  constructor
  · rw [vert_star_gtrace]
    calc |∑ x, μ x * (∏ k ∈ S, chiRe (x i - x k) - starMean S x)|
        ≤ ∑ x, μ x * (1 + ((S.card : ℝ) - 1) * rp p) := by
          refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun x _ => ?_)
          rw [abs_mul, abs_of_nonneg (hμ0 x)]
          by_cases hx : μ x = 0
          · rw [hx, zero_mul, zero_mul]
          apply mul_le_mul_of_nonneg_left _ (hμ0 x)
          refine (abs_sub _ _).trans (add_le_add ?_ ?_)
          · exact abs_prod_chiRe_le S x (x i)
          · exact abs_starMean_le hW hS x (hinjOn x hx S)
      _ = 1 + ((S.card : ℝ) - 1) * rp p := by rw [← sum_mul, hμ1, one_mul]
  · rw [vert_star_gtraceC]
    calc |∑ x, μ x * ∑ b, chiRe (b - x i) * starKer S x b|
        ≤ ∑ x, μ x * ((S.card : ℝ) * rp p) := by
          refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun x _ => ?_)
          rw [abs_mul, abs_of_nonneg (hμ0 x)]
          by_cases hx : μ x = 0
          · rw [hx, zero_mul, zero_mul]
          apply mul_le_mul_of_nonneg_left _ (hμ0 x)
          rw [sum_congr rfl fun b _ => chiRe_mul_starKer_not_mem hi x b]
          have h := abs_starMean_le hW (insert_nonempty i S) x (hinjOn x hx _)
          rw [card_insert_of_notMem hi] at h
          change |starMean (insert i S) x| ≤ _
          refine h.trans (le_of_eq ?_)
          push_cast
          ring
      _ = (S.card : ℝ) * rp p := by rw [← sum_mul, hμ1, one_mul]

/-- The two traces of `V_i^*W_S` for `i ∈ S`, `|S| ≥ 2`: `|tr| ≤ (k − 1)r` and
`|β_i| ≤ a_{k−1} + q`. -/
theorem vert_star_mem_traces (hp2 : p ≠ 2) (hW : Labellings.WeilBound (ZMod p))
    (μ : (U → ZMod p) → ℝ) (hμ0 : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1)
    (hinj : ∀ (x : U → ZMod p) (k l : U), μ x ≠ 0 → k ≠ l → x k ≠ x l)
    {S : Finset U} (hS2 : 2 ≤ S.card) {i : U} (hi : i ∈ S) :
    |gtrace μ (vertKer i) (starKer S)| ≤ ((S.card : ℝ) - 1) * rp p ∧
      |gtraceC μ (vertKer i) (starKer S)| ≤ aConst p (S.card - 1) + (p : ℝ)⁻¹ := by
  have hinjOn : ∀ x, μ x ≠ 0 → ∀ R : Finset U, Set.InjOn x R := fun x hx R a _ b _ hab => by
    by_contra hne; exact hinj x a b hx hne hab
  have hS : S.Nonempty := ⟨i, hi⟩
  have hSe : (S.erase i).Nonempty := by
    rw [← card_pos, card_erase_of_mem hi]; omega
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  constructor
  · rw [vert_star_gtrace]
    calc |∑ x, μ x * (∏ k ∈ S, chiRe (x i - x k) - starMean S x)|
        ≤ ∑ x, μ x * (((S.card : ℝ) - 1) * rp p) := by
          refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun x _ => ?_)
          rw [abs_mul, abs_of_nonneg (hμ0 x)]
          by_cases hx : μ x = 0
          · rw [hx, zero_mul, zero_mul]
          apply mul_le_mul_of_nonneg_left _ (hμ0 x)
          rw [prod_chiRe_self_zero hi x, zero_sub, abs_neg]
          exact abs_starMean_le hW hS x (hinjOn x hx S)
      _ = ((S.card : ℝ) - 1) * rp p := by rw [← sum_mul, hμ1, one_mul]
  · rw [vert_star_gtraceC]
    calc |∑ x, μ x * ∑ b, chiRe (b - x i) * starKer S x b|
        ≤ ∑ x, μ x * (aConst p (S.card - 1) + (p : ℝ)⁻¹) := by
          refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun x _ => ?_)
          rw [abs_mul, abs_of_nonneg (hμ0 x)]
          by_cases hx : μ x = 0
          · rw [hx, zero_mul, zero_mul]
          apply mul_le_mul_of_nonneg_left _ (hμ0 x)
          rw [sum_chiRe_mul_starKer_mem hi x]
          refine (abs_sub _ _).trans (add_le_add ?_ ?_)
          · have h := abs_starMean_le_aConst hp2 hW hSe x (hinjOn x hx _)
            rwa [card_erase_of_mem hi] at h
          · rw [abs_mul, abs_of_pos (inv_pos.mpr hp0)]
            exact mul_le_of_le_one_right (inv_pos.mpr hp0).le (abs_psiRest_le S i x (x i))
      _ = aConst p (S.card - 1) + (p : ℝ)⁻¹ := by rw [← sum_mul, hμ1, one_mul]

/-- The norm in terms of the two trace bounds: `((T/(p−1))² + q(B/(1−q))²) = q(qT² + B²)/(1−q)²`. -/
lemma trace_bound_form (T B : ℝ) :
    (T / ((p : ℝ) - 1)) ^ 2 + (p : ℝ)⁻¹ * (B / (1 - (p : ℝ)⁻¹)) ^ 2 =
      (p : ℝ)⁻¹ * ((p : ℝ)⁻¹ * T ^ 2 + B ^ 2) / (1 - (p : ℝ)⁻¹) ^ 2 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hq1 : (1 : ℝ) - (p : ℝ)⁻¹ ≠ 0 := by
    have : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp1
    linarith
  have hp1' : (p : ℝ) - 1 ≠ 0 := by linarith
  have hp0 : (p : ℝ) ≠ 0 := by linarith
  field_simp

/-- **`lem:general-star`(d), `eq:singleton-star`, case `i ∉ S`** (`p ≡ 3 (mod 4)`, Weil): for
`k = |S| ≥ 1`, `‖V_i^*W_S h‖² ≤ q (r²(1 + (k − 1)r)² + k²q)/(1 − q)² ‖h‖²` on `L²_0`, that is
`(1 − q)‖V_i^*W_S‖/r ≤ (r²(1 + (k − 1)r)² + k²q)^{1/2}`. -/
theorem vert_star_out_bound (hp2 : p ≠ 2) (hp3 : p % 4 = 3) (hW : Labellings.WeilBound (ZMod p))
    (μ : (U → ZMod p) → ℝ) (hμ0 : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1)
    (hinv : ∀ (s c : ZMod p) (x : U → ZMod p), s ≠ 0 → IsSquare s → μ (affLab s c x) = μ x)
    (hinj : ∀ (x : U → ZMod p) (k l : U), μ x ≠ 0 → k ≠ l → x k ≠ x l)
    {S : Finset U} (hS : S.Nonempty) {i : U} (hi : i ∉ S) (h : ZMod p → ℂ) (hh : meanC h = 0) :
    l2sq (gramOp μ (vertKer i) (starKer S) h) ≤
      (p : ℝ)⁻¹ * (rp p ^ 2 * (1 + ((S.card : ℝ) - 1) * rp p) ^ 2 +
        (S.card : ℝ) ^ 2 * (p : ℝ)⁻¹) / (1 - (p : ℝ)⁻¹) ^ 2 * l2sq h := by
  obtain ⟨hT, hB⟩ := vert_star_not_mem_traces hW μ hμ0 hμ1 hinj hS hi
  have hb := gram_two_traces_le hp2 hp3 (labAction μ hinv) (vertKer i) (starKer S)
    (fun s c _ _ h' x => vertKer_cov i s c h' x)
    (fun s c hs hsq h' x => starKer_cov _ s c hs hsq h' x) hT hB h hh
  refine hb.trans (le_of_eq ?_)
  rw [trace_bound_form, mul_pow, rp_sq]

/-- **`lem:general-star`(d) for `i ∈ S`, `|S| ≥ 2`** (`p ≡ 3 (mod 4)`, Weil):
`‖V_i^*W_S h‖² ≤ q (q((k − 1)r)² + (a_{k−1} + q)²)/(1 − q)² ‖h‖²` on `L²_0`. -/
theorem vert_star_mem_bound (hp2 : p ≠ 2) (hp3 : p % 4 = 3) (hW : Labellings.WeilBound (ZMod p))
    (μ : (U → ZMod p) → ℝ) (hμ0 : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1)
    (hinv : ∀ (s c : ZMod p) (x : U → ZMod p), s ≠ 0 → IsSquare s → μ (affLab s c x) = μ x)
    (hinj : ∀ (x : U → ZMod p) (k l : U), μ x ≠ 0 → k ≠ l → x k ≠ x l)
    {S : Finset U} (hS2 : 2 ≤ S.card) {i : U} (hi : i ∈ S) (h : ZMod p → ℂ) (hh : meanC h = 0) :
    l2sq (gramOp μ (vertKer i) (starKer S) h) ≤
      (p : ℝ)⁻¹ * ((p : ℝ)⁻¹ * (((S.card : ℝ) - 1) * rp p) ^ 2 +
        (aConst p (S.card - 1) + (p : ℝ)⁻¹) ^ 2) / (1 - (p : ℝ)⁻¹) ^ 2 * l2sq h := by
  obtain ⟨hT, hB⟩ := vert_star_mem_traces hp2 hW μ hμ0 hμ1 hinj hS2 hi
  have hb := gram_two_traces_le hp2 hp3 (labAction μ hinv) (vertKer i) (starKer S)
    (fun s c _ _ h' x => vertKer_cov i s c h' x)
    (fun s c hs hsq h' x => starKer_cov _ s c hs hsq h' x) hT hB h hh
  exact hb.trans (le_of_eq (by rw [trace_bound_form]))

/-- **`lem:general-star`(d), `eq:singleton-star`, case `i ∈ S`, `|S| = 3`** (`p ≡ 3 (mod 4)`,
Weil): `‖V_i^*W_S h‖² ≤ q (2√2 q)²/(1 − q)² ‖h‖²`, that is `(1 − q)‖V_i^*W_S‖/r ≤ 2√2 q`. -/
theorem vert_star_three_bound (hp2 : p ≠ 2) (hp3 : p % 4 = 3)
    (hW : Labellings.WeilBound (ZMod p)) (μ : (U → ZMod p) → ℝ) (hμ0 : ∀ x, 0 ≤ μ x)
    (hμ1 : ∑ x, μ x = 1)
    (hinv : ∀ (s c : ZMod p) (x : U → ZMod p), s ≠ 0 → IsSquare s → μ (affLab s c x) = μ x)
    (hinj : ∀ (x : U → ZMod p) (k l : U), μ x ≠ 0 → k ≠ l → x k ≠ x l)
    {S : Finset U} (hS3 : S.card = 3) {i : U} (hi : i ∈ S) (h : ZMod p → ℂ) (hh : meanC h = 0) :
    l2sq (gramOp μ (vertKer i) (starKer S) h) ≤
      (p : ℝ)⁻¹ * (2 * Real.sqrt 2 * (p : ℝ)⁻¹) ^ 2 / (1 - (p : ℝ)⁻¹) ^ 2 * l2sq h := by
  have hb := vert_star_mem_bound hp2 hp3 hW μ hμ0 hμ1 hinv hinj (by omega) hi h hh
  refine hb.trans (le_of_eq ?_)
  have ha : aConst p (S.card - 1) = (p : ℝ)⁻¹ := by
    rw [hS3]; unfold aConst; norm_num
  rw [ha, hS3, mul_pow, rp_sq, mul_pow, mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  push_cast
  ring

/-- **`lem:general-star`(d), `eq:singleton-star`, case `i ∈ S`, `|S| ≥ 4`** (`p ≡ 3 (mod 4)`,
Weil): `‖V_i^*W_S h‖² ≤ q ((k − 1)²q² + ((k − 2)r + q)²)/(1 − q)² ‖h‖²`, that is
`(1 − q)‖V_i^*W_S‖/r ≤ ((k − 1)²q² + ((k − 2)r + q)²)^{1/2}`. -/
theorem vert_star_large_bound (hp2 : p ≠ 2) (hp3 : p % 4 = 3)
    (hW : Labellings.WeilBound (ZMod p)) (μ : (U → ZMod p) → ℝ) (hμ0 : ∀ x, 0 ≤ μ x)
    (hμ1 : ∑ x, μ x = 1)
    (hinv : ∀ (s c : ZMod p) (x : U → ZMod p), s ≠ 0 → IsSquare s → μ (affLab s c x) = μ x)
    (hinj : ∀ (x : U → ZMod p) (k l : U), μ x ≠ 0 → k ≠ l → x k ≠ x l)
    {S : Finset U} (hS4 : 4 ≤ S.card) {i : U} (hi : i ∈ S) (h : ZMod p → ℂ) (hh : meanC h = 0) :
    l2sq (gramOp μ (vertKer i) (starKer S) h) ≤
      (p : ℝ)⁻¹ * (((S.card : ℝ) - 1) ^ 2 * (p : ℝ)⁻¹ ^ 2 +
        (((S.card : ℝ) - 2) * rp p + (p : ℝ)⁻¹) ^ 2) / (1 - (p : ℝ)⁻¹) ^ 2 * l2sq h := by
  have hb := vert_star_mem_bound hp2 hp3 hW μ hμ0 hμ1 hinv hinj (by omega) hi h hh
  refine hb.trans (le_of_eq ?_)
  have ha : aConst p (S.card - 1) = ((S.card : ℝ) - 2) * rp p := by
    unfold aConst
    have h1 : ¬ (S.card - 1 ≤ 1) := by omega
    have h2 : ¬ (S.card - 1 = 2) := by omega
    simp only [h1, h2, ↓reduceIte]
    rw [Nat.cast_sub (by omega : 1 ≤ S.card)]
    push_cast
    ring
  rw [ha, mul_pow, rp_sq]
  ring

end Sarkozy.SpectralD
