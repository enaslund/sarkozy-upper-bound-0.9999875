module

public import Sarkozy.Peyre.Main

/-!
# Peyre's tensorization in finite form, VII: independent pairs

`cor:peyre-independent` (paper `04_notation.tex`, Section 4.6; `rem:peyre:sharp` (i) of
Appendix B): if the pairs `(X_k, Y_k)` are independent of each other, then
`ρ((X_k)_k; (Y_k)_k) = max_k ρ(X_k; Y_k)`, and the same holds conditionally on
`(Z_k)_k = z` when the triples `(X_k, Y_k, Z_k)` are independent across `k`.

* `IndepFamily μ T`: mutual independence of `T 0, …, T (n-1)`, in event form
  (`P(∀ k, T_k ∈ E_k) = ∏_k P(T_k ∈ E_k)` for all events `E_k` of the values).
  `IndepFamily.expect_prod` derives the expectation form.
* The maximum over `k` is written `⨆ k, …` (`iSup` over `Fin n`; it is `0` for `n = 0`,
  in which case both families are constant and `ρ = 0`).
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.Peyre

open Sarkozy

variable {Ω : Type*} {α β γ : Type*}

theorem ind_forall {n : ℕ} (E : Fin n → Ω → Prop) (ω : Ω) :
    ind (fun ω => ∀ k, E k ω) ω = ∏ k, ind (E k) ω := by
  by_cases h : ∀ k, E k ω
  · rw [ind_of_pos h]
    exact (Finset.prod_eq_one (fun k _ => ind_of_pos (h k))).symm
  · obtain ⟨k, hk⟩ := not_forall.mp h
    rw [ind_of_neg h]
    exact (Finset.prod_eq_zero (Finset.mem_univ k) (ind_of_neg hk)).symm

variable [Fintype Ω]

/-- Mutual independence of the random variables `T 0, …, T (n-1)` (event form). -/
def IndepFamily (μ : FiniteLaw Ω) {n : ℕ} (T : Fin n → Ω → γ) : Prop :=
  ∀ E : Fin n → γ → Prop,
    prob μ (fun ω => ∀ k, E k (T k ω)) = ∏ k, prob μ (fun ω => E k (T k ω))

theorem prob_mono (μ : FiniteLaw Ω) {E F : Ω → Prop} (h : ∀ ω, E ω → F ω) :
    prob μ E ≤ prob μ F := by
  unfold prob
  refine μ.expect_mono (fun ω => ?_)
  by_cases hE : E ω
  · rw [ind_of_pos hE, ind_of_pos (h ω hE)]
  · rw [ind_of_neg hE]
    exact ind_nonneg F ω

theorem prob_pos_of_forall {μ : FiniteLaw Ω} {n : ℕ} {E : Fin n → Ω → Prop}
    (h : 0 < prob μ (fun ω => ∀ k, E k ω)) (k : Fin n) : 0 < prob μ (E k) :=
  lt_of_lt_of_le h (prob_mono μ (fun _ hω => hω k))

theorem fun_eq_sum_ind [DecidableEq γ] (T : Ω → γ) (φ : γ → ℝ) (ω : Ω) :
    φ (T ω) = ∑ c ∈ Finset.univ.image T, φ c * ind (fun ω => T ω = c) ω := by
  rw [Finset.sum_eq_single (T ω)]
  · rw [ind_of_pos (E := fun ω' => T ω' = T ω) rfl, mul_one]
  · intro c _ hc
    rw [ind_of_neg (fun h => hc h.symm), mul_zero]
  · intro h
    exact absurd (Finset.mem_image_of_mem T (Finset.mem_univ ω)) h

/-- Independence in expectation form: `E[∏_k φ_k(T_k)] = ∏_k E[φ_k(T_k)]`. -/
theorem IndepFamily.expect_prod {μ : FiniteLaw Ω} {n : ℕ} {T : Fin n → Ω → γ}
    (hI : IndepFamily μ T) (φ : Fin n → γ → ℝ) :
    μ.expect (fun ω => ∏ k, φ k (T k ω)) = ∏ k, μ.expect (fun ω => φ k (T k ω)) := by
  classical
  have hexp : (fun ω => ∏ k, φ k (T k ω)) = fun ω =>
      ∑ p ∈ Fintype.piFinset (fun k => Finset.univ.image (T k)),
        ∏ k, (φ k (p k) * ind (fun ω => T k ω = p k) ω) := by
    funext ω
    rw [Finset.prod_congr rfl (fun k _ => fun_eq_sum_ind (T k) (φ k) ω),
      Finset.prod_univ_sum]
  have hexp1 : ∀ k, μ.expect (fun ω => φ k (T k ω)) =
      ∑ c ∈ Finset.univ.image (T k), φ k c * prob μ (fun ω => T k ω = c) := by
    intro k
    have e : (fun ω => φ k (T k ω)) =
        fun ω => ∑ c ∈ Finset.univ.image (T k), φ k c * ind (fun ω => T k ω = c) ω :=
      funext (fun ω => fun_eq_sum_ind (T k) (φ k) ω)
    rw [e, expect_sum]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [FiniteLaw.expect_const_mul]
    rfl
  rw [hexp, expect_sum]
  simp_rw [hexp1]
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  have hind : μ.expect (fun ω => ∏ k, ind (fun ω => T k ω = p k) ω) =
      ∏ k, prob μ (fun ω => T k ω = p k) := by
    rw [← hI (fun k c => c = p k)]
    unfold prob
    exact μ.expect_congr (fun ω => (ind_forall (fun k ω => T k ω = p k) ω).symm)
  simp_rw [Finset.prod_mul_distrib]
  rw [FiniteLaw.expect_const_mul, hind]

/-- Conditioning an independent family on a product event: the expectation of a product
under `μ(· | ∀ k, T_k ∈ F_k)` is the product of the expectations under `μ(· | T_k ∈ F_k)`. -/
theorem IndepFamily.cond_expect_prod {μ : FiniteLaw Ω} {n : ℕ} {T : Fin n → Ω → γ}
    (hI : IndepFamily μ T) (F : Fin n → γ → Prop) (hF : 0 < prob μ (fun ω => ∀ k, F k (T k ω)))
    (φ : Fin n → γ → ℝ) :
    (condLaw μ (fun ω => ∀ k, F k (T k ω)) hF).expect (fun ω => ∏ k, φ k (T k ω)) =
      ∏ k, (μ.expect (fun ω => ind (F k) (T k ω) * φ k (T k ω)) /
        prob μ (fun ω => F k (T k ω))) := by
  rw [cond_expect, Finset.prod_div_distrib, ← hI F]
  congr 1
  have e : (fun ω => ind (fun ω => ∀ k, F k (T k ω)) ω * ∏ k, φ k (T k ω)) =
      fun ω => ∏ k, (ind (F k) (T k ω) * φ k (T k ω)) := by
    funext ω
    rw [ind_forall (fun k ω => F k (T k ω)) ω, ← Finset.prod_mul_distrib]
    rfl
  rw [e]
  exact hI.expect_prod (fun k c => ind (F k) c * φ k c)

theorem IndepFamily.prob_ne_zero {μ : FiniteLaw Ω} {n : ℕ} {T : Fin n → Ω → γ}
    (hI : IndepFamily μ T) (F : Fin n → γ → Prop) (hF : 0 < prob μ (fun ω => ∀ k, F k (T k ω)))
    (k : Fin n) : prob μ (fun ω => F k (T k ω)) ≠ 0 := by
  have h := hF.ne'
  rw [hI F] at h
  exact Finset.prod_ne_zero_iff.mp h k (Finset.mem_univ k)

/-- The law of one variable `T_k` under `μ(· | ∀ j, T_j ∈ F_j)` is its law under
`μ(· | T_k ∈ F_k)`. -/
theorem IndepFamily.cond_expect_single {μ : FiniteLaw Ω} {n : ℕ} {T : Fin n → Ω → γ}
    (hI : IndepFamily μ T) (F : Fin n → γ → Prop) (hF : 0 < prob μ (fun ω => ∀ k, F k (T k ω)))
    (k : Fin n) (φ : γ → ℝ) :
    (condLaw μ (fun ω => ∀ j, F j (T j ω)) hF).expect (fun ω => φ (T k ω)) =
      μ.expect (fun ω => ind (F k) (T k ω) * φ (T k ω)) / prob μ (fun ω => F k (T k ω)) := by
  classical
  set ψ : Fin n → γ → ℝ := fun j c => if j = k then φ c else 1 with hψ
  have e1 : (fun ω => φ (T k ω)) = fun ω => ∏ j, ψ j (T j ω) := by
    funext ω
    simp only [hψ]
    rw [Finset.prod_ite_eq' Finset.univ k (fun j => φ (T j ω)),
      ite_eq_left (Finset.mem_univ k)]
  rw [e1, hI.cond_expect_prod F hF ψ]
  have e2 : ∀ j, μ.expect (fun ω => ind (F j) (T j ω) * ψ j (T j ω)) /
      prob μ (fun ω => F j (T j ω)) = if j = k then
        μ.expect (fun ω => ind (F k) (T k ω) * φ (T k ω)) / prob μ (fun ω => F k (T k ω))
      else 1 := by
    intro j
    by_cases hj : j = k
    · subst hj
      simp only [hψ, ite_true]
    · rw [ite_eq_right hj]
      simp only [hψ, hj, ite_false, mul_one]
      exact div_self (hI.prob_ne_zero F hF j)
  simp_rw [e2]
  rw [Finset.prod_ite_eq' Finset.univ k, ite_eq_left (Finset.mem_univ k)]

theorem prod_ite_two {n : ℕ} {k l : Fin n} (hkl : k ≠ l) (a b : Fin n → ℝ) :
    ∏ j, (if j = k then a j else if j = l then b j else 1) = a k * b l := by
  classical
  have e : ∀ j, (if j = k then a j else if j = l then b j else 1) =
      (if j = k then a j else 1) * (if j = l then b j else 1) := by
    intro j
    by_cases hj : j = k
    · subst hj
      rw [ite_eq_left rfl, ite_eq_left rfl, ite_eq_right hkl, mul_one]
    · rw [ite_eq_right hj, ite_eq_right hj, one_mul]
  simp_rw [e]
  rw [Finset.prod_mul_distrib, Finset.prod_ite_eq' Finset.univ k,
    Finset.prod_ite_eq' Finset.univ l, ite_eq_left (Finset.mem_univ k),
    ite_eq_left (Finset.mem_univ l)]

/-- Under `μ(· | ∀ j, T_j ∈ F_j)`, two variables `T_k`, `T_l` with `k ≠ l` are independent. -/
theorem IndepFamily.cond_expect_mul {μ : FiniteLaw Ω} {n : ℕ} {T : Fin n → Ω → γ}
    (hI : IndepFamily μ T) (F : Fin n → γ → Prop) (hF : 0 < prob μ (fun ω => ∀ k, F k (T k ω)))
    {k l : Fin n} (hkl : k ≠ l) (u v : γ → ℝ) :
    (condLaw μ (fun ω => ∀ j, F j (T j ω)) hF).expect (fun ω => u (T k ω) * v (T l ω)) =
      (condLaw μ (fun ω => ∀ j, F j (T j ω)) hF).expect (fun ω => u (T k ω)) *
        (condLaw μ (fun ω => ∀ j, F j (T j ω)) hF).expect (fun ω => v (T l ω)) := by
  classical
  set ψ : Fin n → γ → ℝ := fun j c => if j = k then u c else if j = l then v c else 1 with hψ
  have e1 : (fun ω => u (T k ω) * v (T l ω)) = fun ω => ∏ j, ψ j (T j ω) := by
    funext ω
    simp only [hψ]
    exact (prod_ite_two hkl (fun j => u (T j ω)) (fun j => v (T j ω))).symm
  rw [e1, hI.cond_expect_prod F hF ψ, hI.cond_expect_single F hF k u,
    hI.cond_expect_single F hF l v]
  have e2 : ∀ j, μ.expect (fun ω => ind (F j) (T j ω) * ψ j (T j ω)) /
      prob μ (fun ω => F j (T j ω)) =
      if j = k then μ.expect (fun ω => ind (F j) (T j ω) * u (T j ω)) /
        prob μ (fun ω => F j (T j ω))
      else if j = l then μ.expect (fun ω => ind (F j) (T j ω) * v (T j ω)) /
        prob μ (fun ω => F j (T j ω))
      else 1 := by
    intro j
    by_cases hj : j = k
    · subst hj
      simp only [hψ, ite_true]
    · by_cases hj' : j = l
      · subst hj'
        simp only [hψ, hj, ite_true, ite_false]
      · simp only [hψ, hj, hj', ite_false, mul_one]
        exact div_self (hI.prob_ne_zero F hF j)
  simp_rw [e2]
  exact prod_ite_two hkl _ _

/-- `ρ(X;Y)` depends only on the joint law of `(X, Y)`. -/
theorem maxCorr_congr_law {μ ν : FiniteLaw Ω} {X : Ω → α} {Y : Ω → β}
    (h : ∀ φ : α → β → ℝ, ν.expect (fun ω => φ (X ω) (Y ω)) = μ.expect (fun ω => φ (X ω) (Y ω))) :
    maxCorr ν X Y = maxCorr μ X Y := by
  unfold maxCorr
  congr 1
  ext c
  constructor
  · rintro ⟨f, g, h1, h2, h3, h4, rfl⟩
    refine ⟨f, g, ?_, ?_, ?_, ?_, ?_⟩
    · rw [← h1]; exact (h (fun a _ => f a)).symm
    · rw [← h2]; exact (h (fun _ b => g b)).symm
    · rw [← h3]; exact (h (fun a _ => f a ^ 2)).symm
    · rw [← h4]; exact (h (fun _ b => g b ^ 2)).symm
    · rw [h (fun a b => f a * g b)]
  · rintro ⟨f, g, h1, h2, h3, h4, rfl⟩
    refine ⟨f, g, ?_, ?_, ?_, ?_, ?_⟩
    · rw [← h1]; exact h (fun a _ => f a)
    · rw [← h2]; exact h (fun _ b => g b)
    · rw [← h3]; exact h (fun a _ => f a ^ 2)
    · rw [← h4]; exact h (fun _ b => g b ^ 2)
    · rw [h (fun a b => f a * g b)]

/-- Functions of `X_k` alone and of `Y_k` alone are admissible: `ρ(X_k; Y_k) ≤ ρ(X; Y)`. -/
theorem maxCorr_le_family (μ : FiniteLaw Ω) {n : ℕ} (X : Fin n → Ω → α) (Y : Fin n → Ω → β)
    (k : Fin n) : maxCorr μ (X k) (Y k) ≤ maxCorr μ (fun ω k => X k ω) (fun ω k => Y k ω) :=
  maxCorr_mono μ (fun _ _ h => congrFun h k) (fun _ _ h => congrFun h k)

/-- `cor:peyre-independent`, upper bound: if the pairs `(X_k, Y_k)` are independent of each
other and `ρ(X_k; Y_k) ≤ Λ` for all `k`, then `ρ((X_k)_k; (Y_k)_k) ≤ Λ`.  Proof as in the
paper: `thm:peyre-finite` (prefix form) with the diagonal matrix `diag(ρ(X_k; Y_k))`. -/
theorem peyre_independent_le (μ : FiniteLaw Ω) {n : ℕ} (X : Fin n → Ω → α)
    (Y : Fin n → Ω → β) (hI : IndepFamily μ (fun k ω => (X k ω, Y k ω))) {Λ : ℝ}
    (hΛ0 : 0 ≤ Λ) (hΛ : ∀ k, maxCorr μ (X k) (Y k) ≤ Λ) :
    maxCorr μ (fun ω k => X k ω) (fun ω k => Y k ω) ≤ Λ := by
  classical
  set ε : Fin n → Fin n → ℝ := fun k l => if k = l then maxCorr μ (X k) (Y k) else 0 with hεd
  have hε : ∀ k l, 0 ≤ ε k l := by
    intro k l
    simp only [hεd]
    split_ifs
    · exact maxCorr_nonneg μ _ _
    · exact le_refl 0
  have hop : ∀ x : Fin n → ℝ, ∑ k, (∑ l, ε k l * x l) ^ 2 ≤ Λ ^ 2 * ∑ l, x l ^ 2 := by
    intro x
    have hrow : ∀ k, ∑ l, ε k l * x l = maxCorr μ (X k) (Y k) * x k := by
      intro k
      simp only [hεd, ite_mul, zero_mul]
      rw [Finset.sum_ite_eq Finset.univ k, ite_eq_left (Finset.mem_univ k)]
    simp only [hrow]
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum (fun k _ => ?_)
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_right
      (pow_le_pow_left₀ (maxCorr_nonneg μ _ _) (hΛ k) 2) (sq_nonneg _)
  have hmain := peyre_prefix μ X Y ε hε hΛ0 hop (by
    intro k l x y h
    set F : Fin n → α × β → Prop :=
      fun j c => (j < k → c.1 = x j) ∧ (j < l → c.2 = y j) with hF
    have hev : (fun ω => (∀ k' : Fin n, k' < k → X k' ω = x k') ∧
        (∀ l' : Fin n, l' < l → Y l' ω = y l')) =
        (fun ω => ∀ j, F j ((fun k ω => (X k ω, Y k ω)) j ω)) := by
      funext ω
      apply propext
      simp only [hF]
      constructor
      · rintro ⟨h1, h2⟩ j
        exact ⟨h1 j, h2 j⟩
      · intro h
        exact ⟨fun k' hk' => (h k').1 hk', fun l' hl' => (h l').2 hl'⟩
    have h' : 0 < prob μ (fun ω => ∀ j, F j ((fun k ω => (X k ω, Y k ω)) j ω)) := hev ▸ h
    rw [cond_congr μ hev h h']
    by_cases hkl : k = l
    · subst hkl
      simp only [hεd, ite_true]
      apply le_of_eq
      apply maxCorr_congr_law
      intro φ
      have hs := hI.cond_expect_single F h' k (fun c => φ c.1 c.2)
      have hFk : ∀ c, F k c := fun c =>
        ⟨fun hc => absurd hc (lt_irrefl k), fun hc => absurd hc (lt_irrefl k)⟩
      have hind : ∀ ω, ind (F k) (X k ω, Y k ω) = 1 := fun ω => ind_of_pos (hFk _)
      have hprob : prob μ (fun ω => F k (X k ω, Y k ω)) = 1 := by
        unfold prob
        rw [show ind (fun ω => F k (X k ω, Y k ω)) = fun _ => 1 from
          funext fun ω => ind_of_pos (hFk _), FiniteLaw.expect_const]
      simp only [hind, one_mul, hprob, div_one] at hs
      exact hs
    · simp only [hεd, hkl, ite_false]
      apply maxCorr_le_of_corrLe le_rfl
      intro f g hf _
      have hm := hI.cond_expect_mul F h' hkl (fun c => f c.1) (fun c => g c.2)
      simp only at hm
      rw [hm, hf, zero_mul, abs_zero, zero_mul, zero_mul])
  exact hmain.trans (min_le_right _ _)

/-- **`cor:peyre-independent`**: if the pairs `(X_k, Y_k)`, `k < n`, are independent of each
other, then `ρ((X_k)_k; (Y_k)_k) = max_k ρ(X_k; Y_k)`. -/
theorem peyre_independent (μ : FiniteLaw Ω) {n : ℕ} (X : Fin n → Ω → α) (Y : Fin n → Ω → β)
    (hI : IndepFamily μ (fun k ω => (X k ω, Y k ω))) :
    maxCorr μ (fun ω k => X k ω) (fun ω k => Y k ω) = ⨆ k, maxCorr μ (X k) (Y k) := by
  apply le_antisymm
  · exact peyre_independent_le μ X Y hI (Real.iSup_nonneg (fun k => maxCorr_nonneg μ _ _))
      (fun k => le_ciSup (f := fun j => maxCorr μ (X j) (Y j))
        (Finite.bddAbove_range (fun j => maxCorr μ (X j) (Y j))) k)
  · exact Real.iSup_le (fun k => maxCorr_le_family μ X Y k) (maxCorr_nonneg μ _ _)

/-- Conditioning independent triples on `(Z_k)_k = z` keeps the pairs `(X_k, Y_k)`
independent. -/
theorem indep_pairs_cond (μ : FiniteLaw Ω) {n : ℕ} (X : Fin n → Ω → α) (Y : Fin n → Ω → β)
    (Z : Fin n → Ω → γ) (hI : IndepFamily μ (fun k ω => (X k ω, Y k ω, Z k ω)))
    (z : Fin n → γ) (hz : 0 < prob μ (fun ω => ∀ k, Z k ω = z k)) :
    IndepFamily (condLaw μ (fun ω => ∀ k, Z k ω = z k) hz) (fun k ω => (X k ω, Y k ω)) := by
  set F : Fin n → α × β × γ → Prop := fun k c => c.2.2 = z k with hF
  have hz' : 0 < prob μ (fun ω => ∀ k, F k ((fun k ω => (X k ω, Y k ω, Z k ω)) k ω)) := hz
  intro E
  have hcond : condLaw μ (fun ω => ∀ k, Z k ω = z k) hz =
      condLaw μ (fun ω => ∀ k, F k ((fun k ω => (X k ω, Y k ω, Z k ω)) k ω)) hz' := rfl
  rw [hcond]
  unfold prob
  have e1 : ind (fun ω => ∀ k, E k (X k ω, Y k ω)) =
      fun ω => ∏ k, ind (E k) (X k ω, Y k ω) := by
    funext ω
    exact ind_forall (fun k ω => E k (X k ω, Y k ω)) ω
  rw [e1]
  have h1 := hI.cond_expect_prod F hz' (fun k c => ind (E k) (c.1, c.2.1))
  simp only at h1
  rw [h1]
  refine Finset.prod_congr rfl (fun k _ => ?_)
  have h2 := hI.cond_expect_single F hz' k (fun c => ind (E k) (c.1, c.2.1))
  simp only at h2
  rw [← h2]
  rfl

/-- **`cor:peyre-independent`, conditional form**: if the triples `(X_k, Y_k, Z_k)` are
independent across `k` and `z` is a value of `(Z_k)_k` of positive probability, then
`ρ((X_k)_k; (Y_k)_k | (Z_k)_k = z) = max_k ρ(X_k; Y_k | Z_k = z_k)`. -/
theorem peyre_independent_cond (μ : FiniteLaw Ω) {n : ℕ} (X : Fin n → Ω → α)
    (Y : Fin n → Ω → β) (Z : Fin n → Ω → γ)
    (hI : IndepFamily μ (fun k ω => (X k ω, Y k ω, Z k ω))) (z : Fin n → γ)
    (hz : 0 < prob μ (fun ω => ∀ k, Z k ω = z k)) :
    maxCorr (condLaw μ (fun ω => ∀ k, Z k ω = z k) hz) (fun ω k => X k ω) (fun ω k => Y k ω) =
      ⨆ k, maxCorr (condLaw μ (fun ω => Z k ω = z k)
        (prob_pos_of_forall (E := fun k ω => Z k ω = z k) hz k)) (X k) (Y k) := by
  rw [peyre_independent _ X Y (indep_pairs_cond μ X Y Z hI z hz)]
  congr 1
  funext k
  apply maxCorr_congr_law
  intro φ
  set F : Fin n → α × β × γ → Prop := fun k c => c.2.2 = z k with hF
  have hz' : 0 < prob μ (fun ω => ∀ k, F k ((fun k ω => (X k ω, Y k ω, Z k ω)) k ω)) := hz
  have hcond : condLaw μ (fun ω => ∀ k, Z k ω = z k) hz =
      condLaw μ (fun ω => ∀ k, F k ((fun k ω => (X k ω, Y k ω, Z k ω)) k ω)) hz' := rfl
  rw [hcond]
  have h2 := hI.cond_expect_single F hz' k (fun c => φ c.1 c.2.1)
  simp only at h2
  rw [h2, cond_expect]
  rfl

end Sarkozy.Peyre
