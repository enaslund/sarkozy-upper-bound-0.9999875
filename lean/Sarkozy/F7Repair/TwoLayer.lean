module

public import Sarkozy.F7Repair.Law
public import Sarkozy.UpperComparison.Densities

@[expose] public section

/-!
# The one-way repair of a two-layer record ((F7), generic in the labels)

`paper/sections/26_upper_comparison.tex`, (F7) and "the repair": a nonaccepting two-layer record
has the old law `π^old = λ_p(G)` on the labellings `y : O₀ × O₁ × Fin 2 → Z` of its two layers
`X = U × {0}`, `Y = U × {1}`; its half law is `λ_H`, and its actual half marginal is `μ^old`
(`oldHalf`). The new law `π^new = λ_p(G^new)` keeps the halves, drops the cross edges and imposes
the projected queries. The one-way repair is `π^rep = (1 + f(x) + g(y))π^new` with both half
marginals `μ^old`.

This file is generic in `O₀`, `O₁`, `Z` and in the laws, so the tail atoms (`Tail.lean`) and the
upper blocks both instantiate it.

* **`F7Record lamO lamH`**: the inputs of (F7) for one record: `π^new` with its support, the
  `OneWayData` of `π^new` with targets `μ^old` (`U`, `ρ_new`, `K_∞`, the gate `2F < 1`), and the
  bound `ρ_old` of `ρ(π^old)`. *Hypotheses*: these are the conclusions of (F1), (F2), (F6) and
  `lem:recentering`(b) at the prime, which the paper evaluates per record.
* **`F7Record.lam`**: the repaired two-layer law; `supp` (both layers where `λ_H` is),
  `support` (inside the support of `π^new`, so every imposed query is accepted), `half0`, `half1`
  (both half marginals are `μ^old`), `centred` (centred norm `≤ ρ'`);
* **`F7Record.change_bound`**: the conclusion of (F7): the change of centred pair forms relative to
  `μ^old`, `𝒞_{π^rep} − 𝒞_{π^old}`, has norm at most `C = ρ_old + ρ'` (`lem:tr:repair`(f));
* **`F7Record.invariant`**: invariance of the repair under every symmetry of `π^new` and `π^old`
  acting by one map on both halves (square-affine invariance in (F7)).
-/

open Finset
open scoped BigOperators

namespace Sarkozy.F7Repair

open Sarkozy.Recentering Sarkozy.Structured Sarkozy.UpperComparison

variable {O₀ O₁ Z : Type*} [Fintype O₀] [DecidableEq O₀] [Fintype O₁] [DecidableEq O₁]
  [Fintype Z] [DecidableEq Z]

/-- The layer-`0` half of a two-layer labelling. -/
abbrev lay0 (y : O₀ × O₁ × Fin 2 → Z) : O₀ × O₁ → Z := layerOf y 0

/-- The layer-`1` half of a two-layer labelling. -/
abbrev lay1 (y : O₀ × O₁ × Fin 2 → Z) : O₀ × O₁ → Z := layerOf y 1

/-- **The actual half marginal `μ^old`** of a two-layer law (its layer-`0` law). -/
noncomputable def oldHalf (lamO : FiniteLaw (O₀ × O₁ × Fin 2 → Z)) : FiniteLaw (O₀ × O₁ → Z) :=
  lamO.map lay0

theorem oldHalf_expect (lamO : FiniteLaw (O₀ × O₁ × Fin 2 → Z)) (φ : (O₀ × O₁ → Z) → ℝ) :
    (oldHalf lamO).expect φ = lamO.expect (fun y => φ (lay0 y)) := by
  unfold oldHalf
  rw [FiniteLaw.expect_map]
  rfl

/-- **The inputs of (F7) for one record** at one prime (`lem:tr:repair`(d),(f), (F7)).
*Hypotheses*: `π^new` with its support, the one-way data of `π^new` with targets `μ^old`, and
the bound `ρ_old` on the centred norm of the replaced record relative to `μ^old`. -/
structure F7Record (lamO : FiniteLaw (O₀ × O₁ × Fin 2 → Z)) (lamH : FiniteLaw (O₀ × O₁ → Z)) where
  /-- The new law `π^new = λ_p(G^new)`. -/
  lamN : FiniteLaw (O₀ × O₁ × Fin 2 → Z)
  /-- Both layers of `π^new` lie where `λ_H` is (the new graph keeps the old halves). -/
  suppN : LayersSupported lamN lamH
  /-- The one-way data: `U`, `ρ_new`, `K_∞`, the gate `2F < 1`, with targets `μ^old`. -/
  D : OneWayData (pairLaw lamN lay0 lay1) (oldHalf lamO) (oldHalf lamO)
  /-- `ρ_old`, a bound for the centred norm `ρ(π^old)`. -/
  ρold : ℝ
  ρold_nonneg : 0 ≤ ρold
  /-- `ρ(π^old) ≤ ρ_old`, relative to `μ^old` on both halves. -/
  old_corr : ∀ h k, (oldHalf lamO).expect h = 0 → (oldHalf lamO).expect k = 0 →
    |lamO.expect (fun y => h (lay0 y) * k (lay1 y))| ≤
      ρold * nrm (oldHalf lamO) h * nrm (oldHalf lamO) k

namespace F7Record

variable {lamO : FiniteLaw (O₀ × O₁ × Fin 2 → Z)} {lamH : FiniteLaw (O₀ × O₁ → Z)}
  (R : F7Record lamO lamH)

/-- **The one-way repair `π^rep`** of the record. -/
noncomputable def lam : FiniteLaw (O₀ × O₁ × Fin 2 → Z) := repLaw R.D

/-- **The (F7) coefficient times `r`**: `C = ρ_old + ρ'`. -/
noncomputable def C : ℝ := R.ρold + R.D.ρ'

theorem C_nonneg : 0 ≤ R.C := add_nonneg R.ρold_nonneg R.D.ρ'_nonneg

/-- The repair lives on the support of `π^new` (`lem:tr:repair`(c)). -/
theorem support {y : O₀ × O₁ × Fin 2 → Z} (h : R.lam.weight y ≠ 0) : R.lamN.weight y ≠ 0 :=
  repLaw_support R.D h

/-- Both layers of the repair lie where `λ_H` is. -/
theorem supp : LayersSupported R.lam lamH := fun y hy => R.suppN y (R.support hy)

/-- The layer-`0` marginal of the repair is `μ^old`. -/
theorem half0 (φ : (O₀ × O₁ → Z) → ℝ) :
    R.lam.expect (fun y => φ (lay0 y)) = (oldHalf lamO).expect φ := repLaw_fst R.D φ

/-- The layer-`1` marginal of the repair is `μ^old`. -/
theorem half1 (φ : (O₀ × O₁ → Z) → ℝ) :
    R.lam.expect (fun y => φ (lay1 y)) = (oldHalf lamO).expect φ := repLaw_snd R.D φ

/-- The centred norm of the repair relative to `μ^old` is at most `ρ'`. -/
theorem centred (h k : (O₀ × O₁ → Z) → ℝ) (hh : (oldHalf lamO).expect h = 0)
    (hk : (oldHalf lamO).expect k = 0) :
    |R.lam.expect (fun y => h (lay0 y) * k (lay1 y))| ≤
      R.D.ρ' * nrm (oldHalf lamO) h * nrm (oldHalf lamO) k :=
  repLaw_centred R.D h k hh hk

/-- `‖χ‖_{μ^old}` is W8's `mnrm λ_H u₀`. -/
theorem mnrm_eq (hsO : LayersSupported lamO lamH) (χ : (O₀ × O₁ → Z) → ℝ) :
    mnrm lamH (halfDensity lamO lamH) χ = nrm (oldHalf lamO) χ := by
  have h1 := half_density_eq lamO lamH hsO χ
  have h2 : nrm (oldHalf lamO) χ =
      Real.sqrt (lamO.expect (fun y => χ (layerOf y 0) * χ (layerOf y 0))) := by
    unfold nrm ip
    rw [oldHalf_expect]
  rw [h2, h1]
  exact (Real.sqrt_sq (Real.sqrt_nonneg _)).symm

/-- **The conclusion of (F7)** (`lem:tr:repair`(f)): if `π^old` lies where `λ_H` is and its two
layers have the same law (the layer swap is an automorphism of `G`), the change of centred pair
forms `𝒞_{π^rep} − 𝒞_{π^old}` relative to `μ^old = (1 + u₀)λ_H` has norm at most
`C = ρ_old + ρ'`. This is the hypothesis `hB` of T2's `TailRepair.ofChangeBound`. -/
theorem change_bound (hsO : LayersSupported lamO lamH)
    (hsym : ∀ φ : (O₀ × O₁ → Z) → ℝ,
      lamO.expect (fun y => φ (lay1 y)) = lamO.expect (fun y => φ (lay0 y)))
    (φ ψ : (O₀ × O₁ → Z) → ℝ) :
    |centredForm lamH (halfDensity lamO lamH) (pairDensity R.lam lamH) φ ψ -
        centredForm lamH (halfDensity lamO lamH) (pairDensity lamO lamH) φ ψ| ≤
      R.C * mnrm lamH (halfDensity lamO lamH) φ * mnrm lamH (halfDensity lamO lamH) ψ := by
  unfold centredForm
  rw [← pair_density_eq R.lam lamH R.supp φ ψ, ← pair_density_eq lamO lamH hsO φ ψ,
    mnrm_eq hsO, mnrm_eq hsO]
  have hQ1 : ∀ φ : (O₀ × O₁ → Z) → ℝ,
      lamO.expect (fun y => φ (lay0 y)) = (oldHalf lamO).expect φ :=
    fun φ => (oldHalf_expect lamO φ).symm
  have hQ2 : ∀ φ : (O₀ × O₁ → Z) → ℝ,
      lamO.expect (fun y => φ (lay1 y)) = (oldHalf lamO).expect φ :=
    fun φ => (hsym φ).trans (hQ1 φ)
  have h := coupling_change R.lam lamO lay0 lay1 lay0 lay1 R.half0 R.half1 hQ1 hQ2
    R.D.ρ'_nonneg R.ρold_nonneg R.centred R.old_corr φ ψ
  have e : ∀ A B c : ℝ, (A - c) - (B - c) = A - B := fun _ _ _ => by ring
  rw [e]
  unfold C
  rw [add_comm R.ρold]
  exact h

/-- **Invariance of the repair** (`lem:tr:repair`(a); "the data are square-affine invariant, so
it is invariant"): a bijection `σ` of the two-layer labellings preserving `π^new` and `π^old`
and acting on both halves by one map `τ` preserves `π^rep`. -/
theorem invariant (σ : (O₀ × O₁ × Fin 2 → Z) ≃ (O₀ × O₁ × Fin 2 → Z))
    (τ : (O₀ × O₁ → Z) ≃ (O₀ × O₁ → Z)) (hσN : ∀ y, R.lamN.weight (σ y) = R.lamN.weight y)
    (hσO : ∀ y, lamO.weight (σ y) = lamO.weight y) (h0 : ∀ y, lay0 (σ y) = τ (lay0 y))
    (h1 : ∀ y, lay1 (σ y) = τ (lay1 y)) (y : O₀ × O₁ × Fin 2 → Z) :
    R.lam.weight (σ y) = R.lam.weight y := by
  have hμ : ∀ x, (oldHalf lamO).weight (τ x) = (oldHalf lamO).weight x :=
    map_weight_equivariant lamO lay0 σ τ hσO h0
  exact repLaw_invariant R.D σ τ τ hσN h0 h1 hμ hμ y

end F7Record

end Sarkozy.F7Repair
