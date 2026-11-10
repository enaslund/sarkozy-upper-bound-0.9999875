module

public import Sarkozy.SignedGram.Kernel

@[expose] public section

/-!
# The reflected transpose: the Gram of `F₂` from that of `F₁` (SGA)

`paper/sections/24_matching_mean.tex`, `lem:record:asymmetric-gram`(c); `def:record:mixture`(d).

With `ς(x₀, x₁, x₂) = (-x₂, -x₁, -x₀)` and `Φ(x, y) = (ς y, ς x)` (`rT` on two-layer labellings):

* **`opGram_refl`**: if `K₀ ∘ Φ = K₀`, `K₀` is layer-swap invariant, and `K₂ = K₁ ∘ Φ` (the
  record of `F₂` is the reflected transpose of that of `F₁`), then the block Gram of `K₁` with
  the shifts `(σ_L, σ_R)` gives that of `K₂` with the shifts interchanged. The proof is the
  paper's: exchange the two copies and conjugate by `𝒰φ = φ ∘ ς`
  (`G₂(φ, ψ) = G₁(ψ ∘ ς, φ ∘ ς)`).

The argument is uniform in the label set: it is stated for any finite `X` with an involutive
negation, in particular for the block labels `∏_p ℤ/p`.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.SignedGram

section Generic

variable {X : Type} [Fintype X] [DecidableEq X] [InvolutiveNeg X]

/-- The reflection `ς(x₀, x₁, x₂) = (-x₂, -x₁, -x₀)` of a triple. -/
def rf (x : Fin 3 → X) : Fin 3 → X := fun o => -x (Fin.rev o)

/-- The reflected transpose `Φ(y)_{o, ℓ} = -y_{rev o, 1 - ℓ}` of a two-layer labelling:
`Φ(x, y) = (ς y, ς x)`. -/
def rT (y : Fin 3 × Fin 2 → X) : Fin 3 × Fin 2 → X := fun w => -y (Fin.rev w.1, 1 - w.2)

omit [Fintype X] [DecidableEq X] in
theorem rT_rT (y : Fin 3 × Fin 2 → X) : rT (rT y) = y := by
  funext ⟨o, l⟩
  simp only [rT, neg_neg, Fin.rev_rev]
  congr 2
  fin_cases l <;> rfl

omit [Fintype X] [DecidableEq X] in
theorem lay2_rT_zero (y : Fin 3 × Fin 2 → X) : lay2 (rT y) 0 = rf (lay2 y 1) := rfl

omit [Fintype X] [DecidableEq X] in
theorem lay2_rT_one (y : Fin 3 × Fin 2 → X) : lay2 (rT y) 1 = rf (lay2 y 0) := by
  funext o
  simp only [lay2, rT, rf]
  rfl

/-- The reflected transpose as an equivalence. -/
def rTE : (Fin 3 × Fin 2 → X) ≃ (Fin 3 × Fin 2 → X) := ⟨rT, rT, rT_rT, rT_rT⟩

omit [DecidableEq X] in
theorem kform_refl_eq {K₀ : (Fin 3 × Fin 2 → X) → ℝ} (hr : ∀ y, K₀ (rT y) = K₀ y)
    (φ : (Fin 3 → X) → ℝ) : kform K₀ (fun x => φ (rf x)) (fun x => φ (rf x)) = kform K₀ φ φ := by
  unfold kform
  refine Fintype.sum_equiv rTE _ _ fun y => ?_
  change _ = K₀ (rT y) * (φ (lay2 (rT y) 0) * φ (lay2 (rT y) 1))
  rw [hr, lay2_rT_zero, lay2_rT_one]
  ring

omit [DecidableEq X] in
theorem mform_refl_eq {K₀ : (Fin 3 × Fin 2 → X) → ℝ} (hr : ∀ y, K₀ (rT y) = K₀ y)
    (hs : ∀ y, K₀ (y ∘ Labellings.layerSwapMap (Fin 3)) = K₀ y) (φ : (Fin 3 → X) → ℝ) :
    mform K₀ (fun x => φ (rf x)) = mform K₀ φ := by
  have h1 : mform K₀ (fun x => φ (rf x)) = ∑ y, K₀ y * (φ (lay2 y 1) * φ (lay2 y 1)) := by
    unfold mform
    refine Fintype.sum_equiv rTE _ _ fun y => ?_
    change _ = K₀ (rT y) * (φ (lay2 (rT y) 1) * φ (lay2 (rT y) 1))
    rw [hr, lay2_rT_one]
  have h2 : ∑ y, K₀ y * (φ (lay2 y 1) * φ (lay2 y 1)) = mform K₀ φ := by
    unfold mform
    refine Fintype.sum_equiv swapE _ _ fun y => ?_
    change _ = K₀ (y ∘ Labellings.layerSwapMap (Fin 3)) *
      (φ (lay2 (swapE y) 0) * φ (lay2 (swapE y) 0))
    rw [hs, (lay2_swapE y).1]
  rw [h1, h2]

omit [DecidableEq X] in
theorem kform_reflT {K₁ K₂ : (Fin 3 × Fin 2 → X) → ℝ} (h : ∀ y, K₂ y = K₁ (rT y))
    (φ ψ : (Fin 3 → X) → ℝ) :
    kform K₁ (fun x => ψ (rf x)) (fun x => φ (rf x)) = kform K₂ φ ψ := by
  unfold kform
  refine Fintype.sum_equiv rTE _ _ fun y => ?_
  change _ = K₂ (rT y) * (φ (lay2 (rT y) 0) * ψ (lay2 (rT y) 1))
  rw [h, rT_rT, lay2_rT_zero, lay2_rT_one]
  ring

omit [DecidableEq X] in
/-- **`lem:record:asymmetric-gram`(c)** on `L²(m₀)²`: if `Φ` preserves `K₀`, `K₀` is layer-swap
invariant, and the record of `F₂` is the reflected transpose of that of `F₁` (`K₂ = K₁ ∘ Φ`),
the block Gram of `K₁` with the shifts `(σ_L, σ_R)` gives that of `K₂` with `σ_L, σ_R`
interchanged. -/
theorem opGram_refl {K₀ K₁ K₂ : (Fin 3 × Fin 2 → X) → ℝ} (hr : ∀ y, K₀ (rT y) = K₀ y)
    (hs : ∀ y, K₀ (y ∘ Labellings.layerSwapMap (Fin 3)) = K₀ y) (h : ∀ y, K₂ y = K₁ (rT y))
    {σL σR : ℝ} (hG : OpGram K₀ K₁ σL σR) : OpGram K₀ K₂ σR σL := by
  intro φ ψ
  have h1 := hG (fun x => ψ (rf x)) (fun x => φ (rf x))
  rw [kform_refl_eq hr, kform_refl_eq hr, mform_refl_eq hr hs, mform_refl_eq hr hs,
    kform_reflT h] at h1
  linarith

end Generic

end Sarkozy.SignedGram
