module

public import Sarkozy.Peyre.Independent
public import Sarkozy.ProbabilityProducts

/-!
# Peyre's tensorization in finite form, X: product laws

Under a product law `FiniteLaw.pi μs` on `∀ k, Ωs k` (from `Sarkozy.ProbabilityProducts`),
functions of distinct coordinates form an independent family (`indepFamily_pi`).  Hence
`cor:peyre-independent` applies to product laws (`peyre_independent_pi`).
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.Peyre

open Sarkozy

variable {γ : Type*}

theorem pi_prob_forall {n : ℕ} {Ωs : Fin n → Type*} [∀ k, Fintype (Ωs k)]
    (μs : ∀ k, FiniteLaw (Ωs k)) (h : ∀ k, Ωs k → γ) (E : Fin n → γ → Prop) :
    prob (FiniteLaw.pi μs) (fun x => ∀ k, E k (h k (x k))) =
      ∏ k, (μs k).expect (fun y => ind (E k) (h k y)) := by
  unfold prob
  have e : ind (fun x : (∀ k, Ωs k) => ∀ k, E k (h k (x k))) =
      fun x => ∏ k, ind (E k) (h k (x k)) := by
    funext x
    exact ind_forall (fun k x => E k (h k (x k))) x
  rw [e]
  exact FiniteLaw.expect_pi_product μs (fun k y => ind (E k) (h k y))

/-- Functions of distinct coordinates of a product law are independent. -/
theorem indepFamily_pi {n : ℕ} {Ωs : Fin n → Type*} [∀ k, Fintype (Ωs k)]
    (μs : ∀ k, FiniteLaw (Ωs k)) (h : ∀ k, Ωs k → γ) :
    IndepFamily (FiniteLaw.pi μs) (fun k x => h k (x k)) := by
  classical
  intro E
  rw [pi_prob_forall μs h E]
  refine Finset.prod_congr rfl (fun k _ => ?_)
  set E' : Fin n → γ → Prop := fun j c => if j = k then E k c else True with hE'
  have hev : (fun x : (∀ k, Ωs k) => E k (h k (x k))) =
      (fun x => ∀ j, E' j (h j (x j))) := by
    funext x
    apply propext
    constructor
    · intro hx j
      by_cases hj : j = k
      · subst hj
        simp only [hE', ite_true]
        exact hx
      · simp only [hE', hj, ite_false]
    · intro hx
      have := hx k
      simp only [hE', ite_true] at this
      exact this
  show _ = prob (FiniteLaw.pi μs) (fun x => E k (h k (x k)))
  rw [hev, pi_prob_forall μs h E']
  have e : ∀ j, (μs j).expect (fun y => ind (E' j) (h j y)) =
      if j = k then (μs k).expect (fun y => ind (E k) (h k y)) else 1 := by
    intro j
    by_cases hj : j = k
    · subst hj
      simp only [hE', ite_true]
    · rw [ite_eq_right hj]
      have hone : ∀ y, ind (E' j) (h j y) = 1 := fun y => ind_of_pos (by
        simp only [hE', hj, ite_false])
      simp only [hone, FiniteLaw.expect_const]
  simp_rw [e]
  rw [Finset.prod_ite_eq' Finset.univ k, ite_eq_left (Finset.mem_univ k)]

/-- `cor:peyre-independent` for a product law: if `X_k, Y_k` are functions of the `k`-th
coordinate only, then `ρ((X_k)_k; (Y_k)_k) = max_k ρ(X_k; Y_k)`. -/
theorem peyre_independent_pi {α β : Type*} {n : ℕ} {Ωs : Fin n → Type*}
    [∀ k, Fintype (Ωs k)] (μs : ∀ k, FiniteLaw (Ωs k)) (f : ∀ k, Ωs k → α)
    (g : ∀ k, Ωs k → β) :
    maxCorr (FiniteLaw.pi μs) (fun x k => f k (x k)) (fun x k => g k (x k)) =
      ⨆ k, maxCorr (FiniteLaw.pi μs) (fun x => f k (x k)) (fun x => g k (x k)) :=
  peyre_independent (FiniteLaw.pi μs) (fun k x => f k (x k)) (fun k x => g k (x k))
    (indepFamily_pi μs (fun k y => (f k y, g k y)))

end Sarkozy.Peyre
