module

public import Sarkozy.Cuts.RowProducts
public import Sarkozy.Peyre.Product

/-!
# Cuts, II″: maximal correlation of product couplings (`lem:row-comparison` (c))

`13_cuts_correlations.tex`, `lem:row-comparison` (c), last remaining clause:
`ρ_π = max_p ρ_{π_p}` for `π = ⊗_p π_p` (`maxCorr_prodCoupling`). The proof combines Peyre's
theorem for independent pairs (`Sarkozy.Peyre.peyre_independent_pi`) with two invariance facts:
* `maxCorr_eq_of_pairLaw`: `ρ(X; Y)` depends only on the law of `(X, Y)`;
* `expect_pi_eval`: a coordinate of a product law has the factor law.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.Cuts

open Sarkozy Sarkozy.Peyre

/-- `ρ(X; Y)` depends only on the joint law of `(X, Y)`. -/
theorem maxCorr_eq_of_pairLaw {Ω Ω' α β : Type*} [Fintype Ω] [Fintype Ω'] (μ : FiniteLaw Ω)
    (ν : FiniteLaw Ω') (X : Ω → α) (Y : Ω → β) (X' : Ω' → α) (Y' : Ω' → β)
    (h : ∀ Φ : α → β → ℝ, μ.expect (fun ω => Φ (X ω) (Y ω)) = ν.expect (fun ω => Φ (X' ω) (Y' ω))) :
    maxCorr μ X Y = maxCorr ν X' Y' := by
  unfold maxCorr
  congr 1
  ext c
  simp only [corrSet, Set.mem_ofPred_eq]
  have h1 : ∀ f : α → ℝ, μ.expect (fun ω => f (X ω)) = ν.expect (fun ω => f (X' ω)) :=
    fun f => h (fun a _ => f a)
  have h2 : ∀ g : β → ℝ, μ.expect (fun ω => g (Y ω)) = ν.expect (fun ω => g (Y' ω)) :=
    fun g => h (fun _ b => g b)
  have h3 : ∀ (f : α → ℝ) (g : β → ℝ), μ.expect (fun ω => f (X ω) * g (Y ω)) =
      ν.expect (fun ω => f (X' ω) * g (Y' ω)) := fun f g => h (fun a b => f a * g b)
  constructor
  · rintro ⟨f, g, hf, hg, hf2, hg2, rfl⟩
    refine ⟨f, g, ?_, ?_, ?_, ?_, ?_⟩
    · rw [← h1]; exact hf
    · rw [← h2]; exact hg
    · rw [← h1 (fun a => f a ^ 2)]; exact hf2
    · rw [← h2 (fun b => g b ^ 2)]; exact hg2
    · rw [h3]
  · rintro ⟨f, g, hf, hg, hf2, hg2, rfl⟩
    refine ⟨f, g, ?_, ?_, ?_, ?_, ?_⟩
    · rw [h1]; exact hf
    · rw [h2]; exact hg
    · rw [h1 (fun a => f a ^ 2)]; exact hf2
    · rw [h2 (fun b => g b ^ 2)]; exact hg2
    · rw [h3]

/-- A coordinate of a product law has the factor law. -/
theorem expect_pi_eval {ι : Type*} [Fintype ι] [DecidableEq ι] {Ω : ι → Type*}
    [∀ i, Fintype (Ω i)] (μ : ∀ i, FiniteLaw (Ω i)) (k : ι) (f : Ω k → ℝ) :
    (FiniteLaw.pi μ).expect (fun x => f (x k)) = (μ k).expect f := by
  set g : ∀ i, Ω i → ℝ := Function.update (fun i (_ : Ω i) => (1 : ℝ)) k f with hg
  have h := FiniteLaw.expect_pi_product μ g
  have e1 : ∀ x : ∀ i, Ω i, ∏ i, g i (x i) = f (x k) := by
    intro x
    rw [Finset.prod_eq_single k (fun j _ hj => by rw [hg, Function.update_of_ne hj])
      (fun hk => absurd (Finset.mem_univ k) hk), hg, Function.update_self]
  have e2 : ∏ i, (μ i).expect (g i) = (μ k).expect f := by
    rw [Finset.prod_eq_single k (fun j _ hj => by
        rw [hg, Function.update_of_ne hj]
        exact FiniteLaw.expect_const _ 1)
      (fun hk => absurd (Finset.mem_univ k) hk), hg, Function.update_self]
  simp only [e1] at h
  rw [h, e2]

/-- **`lem:row-comparison` (c).** The maximal correlation of a product coupling is the maximum of
the maximal correlations of the factors: `ρ_π = max_p ρ_{π_p}`. -/
theorem maxCorr_prodCoupling {n : ℕ} {X : Fin n → Type*} [∀ i, Fintype (X i)]
    [∀ i, DecidableEq (X i)] (π : ∀ i, FiniteLaw (X i × X i)) :
    maxCorr (prodCoupling π) Prod.fst Prod.snd = ⨆ k, maxCorr (π k) Prod.fst Prod.snd := by
  -- the coupling is the image of the product law
  have h1 : maxCorr (prodCoupling π) Prod.fst Prod.snd =
      maxCorr (FiniteLaw.pi π) (fun x i => (x i).1) (fun x i => (x i).2) := by
    refine maxCorr_eq_of_pairLaw _ _ _ _ _ _ (fun Φ => ?_)
    unfold prodCoupling
    rw [FiniteLaw.expect_map]
    rfl
  -- encode the coordinates in a common type
  have h2 : maxCorr (FiniteLaw.pi π) (fun x i => (x i).1) (fun x i => (x i).2) =
      maxCorr (FiniteLaw.pi π) (fun x k => (⟨k, (x k).1⟩ : Σ k, X k))
        (fun x k => (⟨k, (x k).2⟩ : Σ k, X k)) := by
    refine maxCorr_congr _ (fun x x' => ?_) (fun x x' => ?_)
    · constructor
      · intro h
        funext k
        rw [show (x k).1 = (x' k).1 from congrFun h k]
      · intro h
        funext k
        have := congrFun h k
        simp only [Sigma.mk.inj_iff, heq_eq_eq, true_and] at this
        exact this
    · constructor
      · intro h
        funext k
        rw [show (x k).2 = (x' k).2 from congrFun h k]
      · intro h
        funext k
        have := congrFun h k
        simp only [Sigma.mk.inj_iff, heq_eq_eq, true_and] at this
        exact this
  have h3 := peyre_independent_pi (α := Σ k, X k) (β := Σ k, X k) π
    (fun k c => ⟨k, c.1⟩) (fun k c => ⟨k, c.2⟩)
  have h4 : ∀ k, maxCorr (FiniteLaw.pi π) (fun x => (⟨k, (x k).1⟩ : Σ k, X k))
      (fun x => (⟨k, (x k).2⟩ : Σ k, X k)) = maxCorr (π k) Prod.fst Prod.snd := by
    intro k
    have hc : maxCorr (FiniteLaw.pi π) (fun x => (⟨k, (x k).1⟩ : Σ k, X k))
        (fun x => (⟨k, (x k).2⟩ : Σ k, X k)) =
        maxCorr (FiniteLaw.pi π) (fun x => (x k).1) (fun x => (x k).2) := by
      refine maxCorr_congr _ (fun x x' => ?_) (fun x x' => ?_)
      · simp only [Sigma.mk.inj_iff, heq_eq_eq, true_and]
      · simp only [Sigma.mk.inj_iff, heq_eq_eq, true_and]
    rw [hc]
    exact maxCorr_eq_of_pairLaw _ _ _ _ _ _ (fun Φ =>
      expect_pi_eval π k (fun c => Φ c.1 c.2))
  rw [h1, h2, h3]
  exact congrArg (fun F => ⨆ k, F k) (funext h4)

end Sarkozy.Cuts
