module

public import Sarkozy.Peyre.Theorem

/-!
# Peyre's tensorization in finite form, VI: `thm:peyre-finite`

The statements of `thm:peyre-finite` (paper `04_notation.tex`, restated in Appendix B):

* `peyre_prefix` — the second (prefix) statement, for two finite families
  `X 0, …, X (N-1)` and `Y 0, …, Y (M-1)`: if
  `ρ(X_k; Y_l | X_{<k} = x, Y_{<l} = y) ≤ ε_{kl}` for all `k, l` and all values of positive
  probability, then `ρ((X_k)_k; (Y_l)_l) ≤ min(1, Λ)` for every `Λ ≥ 0` with
  `‖𝓔 x‖₂ ≤ Λ ‖x‖₂`.  `peyre_prefix_l2` takes `Λ = ‖𝓔‖`, mathlib's `ℓ²` operator norm
  (`Matrix.Norms.L2Operator`), i.e. the largest singular value.
* `peyre_finite_prefix` — the second statement for finite index sets `A, B ⊆ ι` with given
  enumerations; `peyre_finite_prefix_l2` with `Λ = ‖𝓔‖`.
* `peyre_finite` — the first statement, for disjoint finite index sets `A, B` and conditioning
  on all `S ⊆ (A ∪ B) \ {i, j}`; `peyre_finite_l2` with `Λ = ‖𝓔‖`.

The probability space is a finite type with a `FiniteLaw` (zero weights allowed); the paper's
reduction of a general probability space to the finite joint law of the variables
(`sec:peyre:conv`) is not formalized.  A value `s` of `X_S = (X_v)_{v ∈ S}` is represented by
any `s : ι → α` (only `s|_S` matters), and the event `{X_S = s}` by
`fun ω => ∀ v ∈ S, X v ω = s v`; similarly for prefixes.  All variables of a family take
values in one type `α` (`ρ` depends only on level sets, `maxCorr_congr`, so variables with
different value sets can be embedded in a common type).
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.Peyre

open Sarkozy

/-- The weights of the proof: from `‖𝓔 x‖ ≤ Λ ‖x‖` and `Λ² < λ`, a vector `a > 0` with
`𝓔𝓔ᵀ a ≤ λ a` (`lem:peyre:weights` applied to `K = 𝓔𝓔ᵀ`, `‖K‖ ≤ Λ²`). -/
theorem exists_peyre_weights {N M : ℕ} (ε : Fin N → Fin M → ℝ) (hε : ∀ k l, 0 ≤ ε k l)
    {Λ lam : ℝ} (hlam : Λ ^ 2 < lam)
    (hop : ∀ x : Fin M → ℝ, ∑ k, (∑ l, ε k l * x l) ^ 2 ≤ Λ ^ 2 * ∑ l, x l ^ 2) :
    ∃ a : Fin N → ℝ, (∀ k, 0 < a k) ∧ ∀ k, ∑ l, ε k l * ∑ i, ε i l * a i ≤ lam * a k := by
  set K : Fin N → Fin N → ℝ := fun i k => ∑ l, ε i l * ε k l with hK
  have hK0 : ∀ i k, 0 ≤ K i k :=
    fun i k => Finset.sum_nonneg (fun l _ => mul_nonneg (hε i l) (hε k l))
  have hKz : ∀ (x : Fin N → ℝ) i, ∑ k, K i k * x k = ∑ l, ε i l * ∑ k, ε k l * x k := by
    intro x i
    simp only [hK, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun l _ => Finset.sum_congr rfl (fun k _ => by ring))
  have hKnorm : ∀ x : Fin N → ℝ, ∑ i, (∑ k, K i k * x k) ^ 2 ≤ (Λ ^ 2) ^ 2 * ∑ i, x i ^ 2 := by
    intro x
    simp only [hKz]
    calc ∑ i, (∑ l, ε i l * ∑ k, ε k l * x k) ^ 2 ≤
        Λ ^ 2 * ∑ l, (∑ k, ε k l * x k) ^ 2 := hop _
      _ ≤ Λ ^ 2 * (Λ ^ 2 * ∑ k, x k ^ 2) :=
          mul_le_mul_of_nonneg_left (transpose_bound ε hop x) (sq_nonneg Λ)
      _ = _ := by ring
  obtain ⟨a, ha1, ha2⟩ := exists_weights K hK0 (sq_nonneg Λ) hlam hKnorm
  have hlam0 : 0 < lam := lt_of_le_of_lt (sq_nonneg Λ) hlam
  refine ⟨a, fun k => lt_of_lt_of_le (inv_pos.mpr hlam0) (ha1 k), fun k => ?_⟩
  have e : ∑ l, ε k l * ∑ i, ε i l * a i = ∑ i, K k i * a i := by
    simp only [hK, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun l _ => by ring))
  rw [e]
  exact ha2 k

variable {Ω : Type*} [Fintype Ω] {α β : Type*}

/-- `thm:peyre-finite`, prefix form, with the hypothesis in inequality form and the prefixes
encoded by `pre`. -/
theorem peyre_prefix_corrLe (μ : FiniteLaw Ω) {N M : ℕ} (X : Fin N → Ω → α)
    (Y : Fin M → Ω → β) (ε : Fin N → Fin M → ℝ) (hε : ∀ k l, 0 ≤ ε k l) {Λ : ℝ}
    (hΛ : 0 ≤ Λ) (hop : ∀ x : Fin M → ℝ, ∑ k, (∑ l, ε k l * x l) ^ 2 ≤ Λ ^ 2 * ∑ l, x l ^ 2)
    (hyp : ∀ (k : Fin N) (l : Fin M) (x : Fin N → Option α) (y : Fin M → Option β)
      (h : 0 < prob μ (fun ω => pre X k ω = x ∧ pre Y l ω = y)),
      CorrLe (condLaw μ (fun ω => pre X k ω = x ∧ pre Y l ω = y) h) (X k) (Y l) (ε k l)) :
    maxCorr μ (fun ω k => X k ω) (fun ω l => Y l ω) ≤ min 1 Λ := by
  rcases le_or_gt 1 Λ with h1 | h1
  · rw [min_eq_left h1]
    exact maxCorr_le_one μ _ _
  rw [min_eq_right h1.le]
  apply le_of_forall_gt_imp_ge_of_dense
  intro t ht
  rcases le_or_gt 1 t with ht1 | ht1
  · exact (maxCorr_le_one μ _ _).trans ht1
  have ht0 : 0 ≤ t := hΛ.trans ht.le
  have hlam : Λ ^ 2 < t ^ 2 := by nlinarith
  have hlam1 : t ^ 2 < 1 := by nlinarith
  obtain ⟨a, ha, hKa⟩ := exists_peyre_weights ε hε hlam hop
  have hmain : ∀ F : Ω → ℝ, IsFunOf (fun ω k => X k ω) F → μ.expect F = 0 →
      μ.expect (fun ω => condExp μ (fun ω l => Y l ω) F ω ^ 2) ≤
        t ^ 2 * μ.expect (fun ω => F ω ^ 2) := by
    intro F hF hF0
    have hF' : IsFunOf (pre X N) F := fun ω ω' h => hF ω ω' ((pre_full_eq_iff X ω ω').mp h)
    have hc : condExp μ (fun ω l => Y l ω) F = condExp μ (pre Y M) F :=
      condExp_congr_level μ (fun ω ω' => (pre_full_eq_iff Y ω ω').symm) F
    rw [hc]
    exact peyre_core μ X Y ε hε hyp a ha hlam1 hKa F hF' hF0
  have := maxCorr_le_of_condExp_sq_le μ _ _ (sq_nonneg t) hmain
  rwa [Real.sqrt_sq ht0] at this

/-- **`thm:peyre-finite`, second (prefix) statement.**  Let `X 0, …, X (N-1)` and
`Y 0, …, Y (M-1)` be random variables on a finite probability space and `ε_{kl} ≥ 0`.
Suppose that for all `k, l` and every value `(x, y)` of `(X_{<k}, Y_{<l})` of positive
probability, `ρ(X_k; Y_l | X_{<k} = x, Y_{<l} = y) ≤ ε_{kl}`.  Then
`ρ((X_k)_k; (Y_l)_l) ≤ min(1, Λ)` for every `Λ ≥ 0` with `‖𝓔 x‖₂ ≤ Λ ‖x‖₂` for all `x`.
(A value of `X_{<k}` is represented by `x : Fin N → α`, of which only `x k'`, `k' < k`,
matters.) -/
theorem peyre_prefix (μ : FiniteLaw Ω) {N M : ℕ} (X : Fin N → Ω → α) (Y : Fin M → Ω → β)
    (ε : Fin N → Fin M → ℝ) (hε : ∀ k l, 0 ≤ ε k l) {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hop : ∀ x : Fin M → ℝ, ∑ k, (∑ l, ε k l * x l) ^ 2 ≤ Λ ^ 2 * ∑ l, x l ^ 2)
    (hyp : ∀ (k : Fin N) (l : Fin M) (x : Fin N → α) (y : Fin M → β)
      (h : 0 < prob μ (fun ω => (∀ k' : Fin N, k' < k → X k' ω = x k') ∧
        (∀ l' : Fin M, l' < l → Y l' ω = y l'))),
      maxCorr (condLaw μ (fun ω => (∀ k' : Fin N, k' < k → X k' ω = x k') ∧
        (∀ l' : Fin M, l' < l → Y l' ω = y l')) h) (X k) (Y l) ≤ ε k l) :
    maxCorr μ (fun ω k => X k ω) (fun ω l => Y l ω) ≤ min 1 Λ := by
  apply peyre_prefix_corrLe μ X Y ε hε hΛ hop
  intro k l x y h
  obtain ⟨ω₀, hω₀, -⟩ := exists_of_prob_pos h
  have hx : pre X k ω₀ = x := hω₀.1
  have hy : pre Y l ω₀ = y := hω₀.2
  have hev : (fun ω => pre X k ω = x ∧ pre Y l ω = y) =
      (fun ω => (∀ k' : Fin N, k' < k → X k' ω = X k' ω₀) ∧
        (∀ l' : Fin M, l' < l → Y l' ω = Y l' ω₀)) := by
    funext ω
    apply propext
    rw [← hx, ← hy, pre_eq_iff, pre_eq_iff]
    simp only [Fin.lt_def]
  have h' : 0 < prob μ (fun ω => (∀ k' : Fin N, k' < k → X k' ω = X k' ω₀) ∧
      (∀ l' : Fin M, l' < l → Y l' ω = Y l' ω₀)) := hev ▸ h
  rw [cond_congr μ hev h h']
  exact corrLe_of_maxCorr_le (hyp k l _ _ h')

open scoped Matrix.Norms.L2Operator in
/-- **`thm:peyre-finite`, prefix statement, with `Λ = ‖𝓔‖`** (the `ℓ²(B) → ℓ²(A)` operator
norm, mathlib's `Matrix.Norms.L2Operator`). -/
theorem peyre_prefix_l2 (μ : FiniteLaw Ω) {N M : ℕ} (X : Fin N → Ω → α) (Y : Fin M → Ω → β)
    (ε : Fin N → Fin M → ℝ) (hε : ∀ k l, 0 ≤ ε k l)
    (hyp : ∀ (k : Fin N) (l : Fin M) (x : Fin N → α) (y : Fin M → β)
      (h : 0 < prob μ (fun ω => (∀ k' : Fin N, k' < k → X k' ω = x k') ∧
        (∀ l' : Fin M, l' < l → Y l' ω = y l'))),
      maxCorr (condLaw μ (fun ω => (∀ k' : Fin N, k' < k → X k' ω = x k') ∧
        (∀ l' : Fin M, l' < l → Y l' ω = y l')) h) (X k) (Y l) ≤ ε k l) :
    maxCorr μ (fun ω k => X k ω) (fun ω l => Y l ω) ≤
      min 1 ‖(Matrix.of ε : Matrix (Fin N) (Fin M) ℝ)‖ :=
  peyre_prefix μ X Y ε hε (norm_nonneg _) (fun x => opBound_of_l2 (Matrix.of ε) x) hyp

/-- **`thm:peyre-finite`, second (prefix) statement, for finite index sets.**  Let `A, B`
be finite index sets with enumerations `eA : Fin |A| ≃ A` and `eB : Fin |B| ≃ B` (the
paper's `a_1, …, a_N` and `b_1, …, b_M` are `eA 0, …, eA (N-1)` and `eB 0, …, eB (M-1)`),
and `ε_{ij} ≥ 0` for `i ∈ A`, `j ∈ B`.  Suppose that for all `k, l`, with
`S = {a_{k'} : k' < k} ∪ {b_{l'} : l' < l}`, and every value `s` of `X_S` with
`P(X_S = s) > 0`, `ρ(X_{a_k}; X_{b_l} | X_S = s) ≤ ε_{a_k b_l}`; here the event `{X_S = s}`
is written `(∀ k' < k, X_{a_{k'}} = s_{a_{k'}}) ∧ (∀ l' < l, X_{b_{l'}} = s_{b_{l'}})`.  Then
`ρ((X_a)_{a ∈ A}; (X_b)_{b ∈ B}) ≤ min(1, Λ)` for every `Λ ≥ 0` with `‖𝓔 x‖₂ ≤ Λ ‖x‖₂`
for all `x ∈ ℝ^B`, where `𝓔 = (ε_{ij})_{i ∈ A, j ∈ B}`. -/
theorem peyre_finite_prefix (μ : FiniteLaw Ω) {ι : Type*} (X : ι → Ω → α) (A B : Finset ι)
    (eA : Fin A.card ≃ A) (eB : Fin B.card ≃ B) (ε : ι → ι → ℝ)
    (hε : ∀ i ∈ A, ∀ j ∈ B, 0 ≤ ε i j) {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hop : ∀ x : B → ℝ, ∑ i : A, (∑ j : B, ε i j * x j) ^ 2 ≤ Λ ^ 2 * ∑ j : B, x j ^ 2)
    (hyp : ∀ (k : Fin A.card) (l : Fin B.card) (s : ι → α)
      (h : 0 < prob μ (fun ω => (∀ k' : Fin A.card, k' < k → X (eA k') ω = s (eA k')) ∧
        (∀ l' : Fin B.card, l' < l → X (eB l') ω = s (eB l')))),
      maxCorr (condLaw μ (fun ω => (∀ k' : Fin A.card, k' < k → X (eA k') ω = s (eA k')) ∧
        (∀ l' : Fin B.card, l' < l → X (eB l') ω = s (eB l'))) h) (X (eA k)) (X (eB l)) ≤
        ε (eA k) (eB l)) :
    maxCorr μ (fun ω (v : A) => X v ω) (fun ω (v : B) => X v ω) ≤ min 1 Λ := by
  set X' : Fin A.card → Ω → α := fun k => X (eA k) with hX'
  set Y' : Fin B.card → Ω → α := fun l => X (eB l) with hY'
  set ε' : Fin A.card → Fin B.card → ℝ := fun k l => ε (eA k) (eB l) with hε'_def
  have hε' : ∀ k l, 0 ≤ ε' k l := fun k l => hε _ (eA k).2 _ (eB l).2
  have hop' : ∀ x : Fin B.card → ℝ, ∑ k, (∑ l, ε' k l * x l) ^ 2 ≤ Λ ^ 2 * ∑ l, x l ^ 2 := by
    intro x
    have h := hop (fun j => x (eB.symm j))
    have e1 : ∀ i : A, ∑ j : B, ε i j * x (eB.symm j) = ∑ l, ε i (eB l) * x l := by
      intro i
      rw [← Equiv.sum_comp eB]
      simp only [Equiv.symm_apply_apply]
    have e2 : ∑ i : A, (∑ l, ε i (eB l) * x l) ^ 2 =
        ∑ k, (∑ l, ε (eA k) (eB l) * x l) ^ 2 :=
      (Equiv.sum_comp eA (fun i : A => (∑ l, ε i (eB l) * x l) ^ 2)).symm
    have e3 : ∑ j : B, x (eB.symm j) ^ 2 = ∑ l, x l ^ 2 := by
      rw [← Equiv.sum_comp eB]
      simp only [Equiv.symm_apply_apply]
    simp only [e1] at h
    rw [e2, e3] at h
    exact h
  have hyp' : ∀ (k : Fin A.card) (l : Fin B.card) (x : Fin A.card → α) (y : Fin B.card → α)
      (h : 0 < prob μ (fun ω => (∀ k' : Fin A.card, k' < k → X' k' ω = x k') ∧
        (∀ l' : Fin B.card, l' < l → Y' l' ω = y l'))),
      maxCorr (condLaw μ (fun ω => (∀ k' : Fin A.card, k' < k → X' k' ω = x k') ∧
        (∀ l' : Fin B.card, l' < l → Y' l' ω = y l')) h) (X' k) (Y' l) ≤ ε' k l := by
    intro k l x y h
    obtain ⟨ω₀, hω₀, -⟩ := exists_of_prob_pos h
    have hx : ∀ k' : Fin A.card, k' < k → X' k' ω₀ = x k' := hω₀.1
    have hy : ∀ l' : Fin B.card, l' < l → Y' l' ω₀ = y l' := hω₀.2
    have hev : (fun ω => (∀ k' : Fin A.card, k' < k → X' k' ω = x k') ∧
        (∀ l' : Fin B.card, l' < l → Y' l' ω = y l')) =
        (fun ω => (∀ k' : Fin A.card, k' < k → X (eA k') ω = X (eA k') ω₀) ∧
          (∀ l' : Fin B.card, l' < l → X (eB l') ω = X (eB l') ω₀)) := by
      funext ω
      apply propext
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨fun k' hk' => (h1 k' hk').trans (hx k' hk').symm,
          fun l' hl' => (h2 l' hl').trans (hy l' hl').symm⟩
      · rintro ⟨h1, h2⟩
        exact ⟨fun k' hk' => (h1 k' hk').trans (hx k' hk'),
          fun l' hl' => (h2 l' hl').trans (hy l' hl')⟩
    have h' : 0 < prob μ (fun ω => (∀ k' : Fin A.card, k' < k → X (eA k') ω = X (eA k') ω₀) ∧
        (∀ l' : Fin B.card, l' < l → X (eB l') ω = X (eB l') ω₀)) := hev ▸ h
    rw [cond_congr μ hev h h']
    exact hyp k l (fun v => X v ω₀) h'
  have hmain := peyre_prefix μ X' Y' ε' hε' hΛ hop' hyp'
  have hc : maxCorr μ (fun ω k => X' k ω) (fun ω l => Y' l ω) =
      maxCorr μ (fun ω (v : A) => X v ω) (fun ω (v : B) => X v ω) := by
    apply maxCorr_congr
    · intro ω ω'
      constructor
      · intro h
        funext v
        have := congrFun h (eA.symm v)
        simpa only [hX', Equiv.apply_symm_apply] using this
      · intro h
        funext k
        exact congrFun h (eA k)
    · intro ω ω'
      constructor
      · intro h
        funext v
        have := congrFun h (eB.symm v)
        simpa only [hY', Equiv.apply_symm_apply] using this
      · intro h
        funext l
        exact congrFun h (eB l)
  rw [← hc]
  exact hmain

/-- **`thm:peyre-finite`, first statement.**  Let `A, B` be disjoint finite index sets and
`(X_v)_{v ∈ A ∪ B}` random variables on a finite probability space, and `ε_{ij} ≥ 0`
(`i ∈ A`, `j ∈ B`).  Suppose that for all `i ∈ A`, `j ∈ B`, every
`S ⊆ (A ∪ B) \ {i, j}` (written `∀ v ∈ S, v ∈ A ∨ v ∈ B`, `i ∉ S`, `j ∉ S`) and every
value `s` of `X_S` with `P(X_S = s) > 0`,
`ρ(X_i; X_j | X_S = s) ≤ ε_{ij}`.  Then `ρ((X_a)_{a ∈ A}; (X_b)_{b ∈ B}) ≤ min(1, Λ)` for
every `Λ ≥ 0` with `‖𝓔 x‖₂ ≤ Λ ‖x‖₂` for all `x ∈ ℝ^B` (`𝓔 = (ε_{ij})_{i ∈ A, j ∈ B}`).
Derived from `peyre_finite_prefix` with the enumerations `Finset.equivFin`; disjointness
makes the prefix sets avoid `i` and `j`. -/
theorem peyre_finite (μ : FiniteLaw Ω) {ι : Type*} (X : ι → Ω → α) (A B : Finset ι)
    (hAB : Disjoint A B) (ε : ι → ι → ℝ) (hε : ∀ i ∈ A, ∀ j ∈ B, 0 ≤ ε i j) {Λ : ℝ}
    (hΛ : 0 ≤ Λ)
    (hop : ∀ x : B → ℝ, ∑ i : A, (∑ j : B, ε i j * x j) ^ 2 ≤ Λ ^ 2 * ∑ j : B, x j ^ 2)
    (hyp : ∀ i ∈ A, ∀ j ∈ B, ∀ S : Finset ι, (∀ v ∈ S, v ∈ A ∨ v ∈ B) → i ∉ S → j ∉ S →
      ∀ s : ι → α,
      ∀ h : 0 < prob μ (fun ω => ∀ v ∈ S, X v ω = s v),
        maxCorr (condLaw μ (fun ω => ∀ v ∈ S, X v ω = s v) h) (X i) (X j) ≤ ε i j) :
    maxCorr μ (fun ω (v : A) => X v ω) (fun ω (v : B) => X v ω) ≤ min 1 Λ := by
  classical
  set eA : Fin A.card ≃ A := A.equivFin.symm with heA
  set eB : Fin B.card ≃ B := B.equivFin.symm with heB
  apply peyre_finite_prefix μ X A B eA eB ε hε hΛ hop
  intro k l s h
  set S : Finset ι := (Finset.univ.filter (fun k' => k' < k)).image (fun k' => (eA k' : ι)) ∪
    (Finset.univ.filter (fun l' => l' < l)).image (fun l' => (eB l' : ι)) with hS
  have hmemA : ∀ k', k' < k → (eA k' : ι) ∈ S := fun k' hk' =>
    Finset.mem_union_left _ (Finset.mem_image.mpr
      ⟨k', Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk'⟩, rfl⟩)
  have hmemB : ∀ l', l' < l → (eB l' : ι) ∈ S := fun l' hl' =>
    Finset.mem_union_right _ (Finset.mem_image.mpr
      ⟨l', Finset.mem_filter.mpr ⟨Finset.mem_univ _, hl'⟩, rfl⟩)
  have hev : (fun ω => (∀ k' : Fin A.card, k' < k → X (eA k') ω = s (eA k')) ∧
      (∀ l' : Fin B.card, l' < l → X (eB l') ω = s (eB l'))) =
      (fun ω => ∀ v ∈ S, X v ω = s v) := by
    funext ω
    apply propext
    constructor
    · rintro ⟨h1, h2⟩ v hv
      rcases Finset.mem_union.mp hv with hv | hv
      · obtain ⟨k', hk', rfl⟩ := Finset.mem_image.mp hv
        exact h1 k' (Finset.mem_filter.mp hk').2
      · obtain ⟨l', hl', rfl⟩ := Finset.mem_image.mp hv
        exact h2 l' (Finset.mem_filter.mp hl').2
    · intro hSω
      exact ⟨fun k' hk' => hSω _ (hmemA k' hk'), fun l' hl' => hSω _ (hmemB l' hl')⟩
  have h' : 0 < prob μ (fun ω => ∀ v ∈ S, X v ω = s v) := hev ▸ h
  rw [cond_congr μ hev h h']
  have hiS : (eA k : ι) ∉ S := by
    intro hmem
    rcases Finset.mem_union.mp hmem with hv | hv
    · obtain ⟨k', hk', heq⟩ := Finset.mem_image.mp hv
      have hk'' := (Finset.mem_filter.mp hk').2
      have : k' = k := eA.injective (Subtype.ext heq)
      rw [this] at hk''
      exact lt_irrefl k hk''
    · obtain ⟨l', _, heq⟩ := Finset.mem_image.mp hv
      have hB' : (eB l' : ι) ∈ B := (eB l').2
      rw [heq] at hB'
      exact Finset.disjoint_left.mp hAB (eA k).2 hB'
  have hjS : (eB l : ι) ∉ S := by
    intro hmem
    rcases Finset.mem_union.mp hmem with hv | hv
    · obtain ⟨k', _, heq⟩ := Finset.mem_image.mp hv
      have hA' : (eA k' : ι) ∈ A := (eA k').2
      rw [heq] at hA'
      exact Finset.disjoint_left.mp hAB hA' (eB l).2
    · obtain ⟨l', hl', heq⟩ := Finset.mem_image.mp hv
      have hl'' := (Finset.mem_filter.mp hl').2
      have : l' = l := eB.injective (Subtype.ext heq)
      rw [this] at hl''
      exact lt_irrefl l hl''
  have hSsub : ∀ v ∈ S, v ∈ A ∨ v ∈ B := by
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · obtain ⟨k', _, rfl⟩ := Finset.mem_image.mp hv
      exact Or.inl (eA k').2
    · obtain ⟨l', _, rfl⟩ := Finset.mem_image.mp hv
      exact Or.inr (eB l').2
  exact hyp _ (eA k).2 _ (eB l).2 S hSsub hiS hjS s h'

/-- `thm:peyre-finite`, first statement, applied in a conditional law `μ(· | E)` (as in the
proof of `prop:middle-negative` (b), where `E` is a pinning event): the hypothesis is stated
under `μ`, given `{X_S = s} ∩ E`. -/
theorem peyre_finite_cond (μ : FiniteLaw Ω) {ι : Type*} (X : ι → Ω → α) (A B : Finset ι)
    (hAB : Disjoint A B) (E : Ω → Prop) (hE : 0 < prob μ E) (ε : ι → ι → ℝ)
    (hε : ∀ i ∈ A, ∀ j ∈ B, 0 ≤ ε i j) {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (hop : ∀ x : B → ℝ, ∑ i : A, (∑ j : B, ε i j * x j) ^ 2 ≤ Λ ^ 2 * ∑ j : B, x j ^ 2)
    (hyp : ∀ i ∈ A, ∀ j ∈ B, ∀ S : Finset ι, (∀ v ∈ S, v ∈ A ∨ v ∈ B) → i ∉ S → j ∉ S →
      ∀ s : ι → α,
      ∀ h : 0 < prob μ (fun ω => (∀ v ∈ S, X v ω = s v) ∧ E ω),
        maxCorr (condLaw μ (fun ω => (∀ v ∈ S, X v ω = s v) ∧ E ω) h) (X i) (X j) ≤ ε i j) :
    maxCorr (condLaw μ E hE) (fun ω (v : A) => X v ω) (fun ω (v : B) => X v ω) ≤ min 1 Λ := by
  apply peyre_finite (condLaw μ E hE) X A B hAB ε hε hΛ hop
  intro i hi j hj S hS hiS hjS s h
  have h' := prob_and_pos_of_cond μ E hE _ h
  rw [cond_cond μ E hE _ h h']
  exact hyp i hi j hj S hS hiS hjS s h'

open scoped Matrix.Norms.L2Operator in
/-- **`thm:peyre-finite`, first statement, with `Λ = ‖𝓔‖`**, the `ℓ²(B) → ℓ²(A)` operator
norm of `𝓔 = (ε_{ij})_{i ∈ A, j ∈ B}` (mathlib's `Matrix.Norms.L2Operator`). -/
theorem peyre_finite_l2 (μ : FiniteLaw Ω) {ι : Type*} [DecidableEq ι] (X : ι → Ω → α)
    (A B : Finset ι) (hAB : Disjoint A B) (ε : ι → ι → ℝ) (hε : ∀ i ∈ A, ∀ j ∈ B, 0 ≤ ε i j)
    (hyp : ∀ i ∈ A, ∀ j ∈ B, ∀ S : Finset ι, (∀ v ∈ S, v ∈ A ∨ v ∈ B) → i ∉ S → j ∉ S →
      ∀ s : ι → α,
      ∀ h : 0 < prob μ (fun ω => ∀ v ∈ S, X v ω = s v),
        maxCorr (condLaw μ (fun ω => ∀ v ∈ S, X v ω = s v) h) (X i) (X j) ≤ ε i j) :
    maxCorr μ (fun ω (v : A) => X v ω) (fun ω (v : B) => X v ω) ≤
      min 1 ‖(Matrix.of fun (i : A) (j : B) => ε i j : Matrix A B ℝ)‖ :=
  peyre_finite μ X A B hAB ε hε (norm_nonneg _)
    (fun x => opBound_of_l2 (Matrix.of fun (i : A) (j : B) => ε i j) x) hyp

open scoped Matrix.Norms.L2Operator in
/-- `peyre_finite_prefix` with `Λ = ‖𝓔‖` (mathlib's `ℓ²` operator norm). -/
theorem peyre_finite_prefix_l2 (μ : FiniteLaw Ω) {ι : Type*} [DecidableEq ι] (X : ι → Ω → α)
    (A B : Finset ι) (eA : Fin A.card ≃ A) (eB : Fin B.card ≃ B) (ε : ι → ι → ℝ)
    (hε : ∀ i ∈ A, ∀ j ∈ B, 0 ≤ ε i j)
    (hyp : ∀ (k : Fin A.card) (l : Fin B.card) (s : ι → α)
      (h : 0 < prob μ (fun ω => (∀ k' : Fin A.card, k' < k → X (eA k') ω = s (eA k')) ∧
        (∀ l' : Fin B.card, l' < l → X (eB l') ω = s (eB l')))),
      maxCorr (condLaw μ (fun ω => (∀ k' : Fin A.card, k' < k → X (eA k') ω = s (eA k')) ∧
        (∀ l' : Fin B.card, l' < l → X (eB l') ω = s (eB l'))) h) (X (eA k)) (X (eB l)) ≤
        ε (eA k) (eB l)) :
    maxCorr μ (fun ω (v : A) => X v ω) (fun ω (v : B) => X v ω) ≤
      min 1 ‖(Matrix.of fun (i : A) (j : B) => ε i j : Matrix A B ℝ)‖ :=
  peyre_finite_prefix μ X A B eA eB ε hε (norm_nonneg _)
    (fun x => opBound_of_l2 (Matrix.of fun (i : A) (j : B) => ε i j) x) hyp

end Sarkozy.Peyre
