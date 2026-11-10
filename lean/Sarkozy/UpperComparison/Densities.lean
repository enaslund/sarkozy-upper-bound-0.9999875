module

public import Sarkozy.UpperComparison.Emission

@[expose] public section

/-!
# The kernels of a two-layer record relative to its half law

`paper/sections/26_upper_comparison.tex`, `def:dense-comparison` ("`K_{D₀}`, the density of
`π^old` relative to `μ ⊗ μ`") and the proof of (F7) ("Densities"): a two-layer record is described
by the density of the pair law of its two layers relative to `ν ⊗ ν`, `ν = λ_H` the common half
law, and by the density `1 + u₀` of its actual half marginal relative to `ν`. On a finite space
these densities exist as soon as the layers are supported where `ν` is.

* `pairDensity`, `pair_density_eq`: the pair law of the two layers is `pairDensity · (ν ⊗ ν)`;
* `halfDensity`, `half_density_eq`, `one_add_halfDensity_nonneg`: the layer-`0` law is
  `(1 + halfDensity)ν`;
* `upRecord_sym_bracket_of_support`, `upRecord_skew_bracket_of_support`: `Emission`'s brackets
  with these kernels, so that the identification hypotheses `hN`, `hO`, `hm₀` are discharged and
  only the support condition and the analytic bound remain.
-/

open Finset

namespace Sarkozy.UpperComparison

open Sarkozy.RecordExpansion Sarkozy.Recentering Sarkozy.Structured Sarkozy.PartV

variable {O₀ O₁ X : Type*} [Fintype O₀] [DecidableEq O₀] [Fintype O₁] [DecidableEq O₁]
  [Fintype X] [DecidableEq X]

/-- The weight of the pair `(x, x')` of layers under a two-layer law. -/
noncomputable def pairWeight (lam : FiniteLaw (O₀ × O₁ × Fin 2 → X))
    (p : (O₀ × O₁ → X) × (O₀ × O₁ → X)) : ℝ :=
  ∑ y, if layerOf y 0 = p.1 ∧ layerOf y 1 = p.2 then lam.weight y else 0

/-- **The pair density** of the two layers relative to `ν ⊗ ν`. -/
noncomputable def pairDensity (lam : FiniteLaw (O₀ × O₁ × Fin 2 → X))
    (ν : FiniteLaw (O₀ × O₁ → X)) (p : (O₀ × O₁ → X) × (O₀ × O₁ → X)) : ℝ :=
  pairWeight lam p / (ν.weight p.1 * ν.weight p.2)

/-- Both layers of the law are supported where `ν` is. -/
def LayersSupported (lam : FiniteLaw (O₀ × O₁ × Fin 2 → X)) (ν : FiniteLaw (O₀ × O₁ → X)) :
    Prop :=
  ∀ y, lam.weight y ≠ 0 → ν.weight (layerOf y 0) ≠ 0 ∧ ν.weight (layerOf y 1) ≠ 0

theorem pairWeight_eq_zero {lam : FiniteLaw (O₀ × O₁ × Fin 2 → X)} {ν : FiniteLaw (O₀ × O₁ → X)}
    (hs : LayersSupported lam ν) {p : (O₀ × O₁ → X) × (O₀ × O₁ → X)}
    (hp : ν.weight p.1 * ν.weight p.2 = 0) : pairWeight lam p = 0 := by
  unfold pairWeight
  refine Finset.sum_eq_zero fun y _ => ?_
  split_ifs with h
  · by_contra hy
    obtain ⟨h0, h1⟩ := hs y hy
    rw [h.1] at h0
    rw [h.2] at h1
    exact mul_ne_zero h0 h1 hp
  · rfl

/-- **The pair law has the density `pairDensity` relative to `ν ⊗ ν`.** -/
theorem pair_density_eq (lam : FiniteLaw (O₀ × O₁ × Fin 2 → X)) (ν : FiniteLaw (O₀ × O₁ → X))
    (hs : LayersSupported lam ν) (φ ψ : (O₀ × O₁ → X) → ℝ) :
    lam.expect (fun y => φ (layerOf y 0) * ψ (layerOf y 1)) =
      kform ν ν (pairDensity lam ν) φ ψ := by
  have hterm : ∀ x x' : O₀ × O₁ → X, ν.weight x * (ν.weight x' *
      (φ x * ψ x' * pairDensity lam ν (x, x'))) = φ x * ψ x' * pairWeight lam (x, x') := by
    intro x x'
    unfold pairDensity
    by_cases h : ν.weight x * ν.weight x' = 0
    · rw [pairWeight_eq_zero hs (p := (x, x')) h]
      rcases mul_eq_zero.mp h with h0 | h0 <;> simp [h0]
    · have ha : ν.weight x ≠ 0 := left_ne_zero_of_mul h
      have hb : ν.weight x' ≠ 0 := right_ne_zero_of_mul h
      field_simp
  symm
  unfold kform FiniteLaw.expect
  calc ∑ x, ν.weight x * ∑ x', ν.weight x' * (φ x * ψ x' * pairDensity lam ν (x, x'))
      = ∑ x, ∑ x', φ x * ψ x' * pairWeight lam (x, x') := by
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun x' _ => hterm x x'
    _ = ∑ x, ∑ x', ∑ y, (if x = layerOf y 0 then (if x' = layerOf y 1 then
          lam.weight y * (φ (layerOf y 0) * ψ (layerOf y 1)) else 0) else 0) := by
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun x' _ => ?_
        unfold pairWeight
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun y _ => ?_
        by_cases h0 : x = layerOf y 0
        · subst h0
          by_cases h1 : x' = layerOf y 1
          · subst h1
            simp only [and_self, ↓reduceIte]
            ring
          · simp [h1, Ne.symm h1]
        · simp [h0, Ne.symm h0]
    _ = ∑ y, lam.weight y * (φ (layerOf y 0) * ψ (layerOf y 1)) := by
        rw [Finset.sum_congr rfl fun x _ => Finset.sum_comm]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun y _ => ?_
        simp

/-- **The half density** `u₀` of the layer-`0` law relative to `ν`: `1 + u₀ = dm₀/dν` on the
support of `ν`, and `u₀ = 0` off it. -/
noncomputable def halfDensity (lam : FiniteLaw (O₀ × O₁ × Fin 2 → X))
    (ν : FiniteLaw (O₀ × O₁ → X)) (x : O₀ × O₁ → X) : ℝ :=
  if ν.weight x = 0 then 0
  else (∑ y, if layerOf y 0 = x then lam.weight y else 0) / ν.weight x - 1

theorem one_add_halfDensity_nonneg (lam : FiniteLaw (O₀ × O₁ × Fin 2 → X))
    (ν : FiniteLaw (O₀ × O₁ → X)) (x : O₀ × O₁ → X) : 0 ≤ 1 + halfDensity lam ν x := by
  unfold halfDensity
  split_ifs with h
  · norm_num
  · have hs : 0 ≤ ∑ y, if layerOf y 0 = x then lam.weight y else 0 :=
      Finset.sum_nonneg fun y _ => by split_ifs <;> simp [lam.nonneg y]
    have := div_nonneg hs (ν.nonneg x)
    linarith

/-- **The layer-`0` law is `(1 + u₀)ν`** with `u₀ = halfDensity`, as the norm identity of
`Emission`. -/
theorem half_density_eq (lam : FiniteLaw (O₀ × O₁ × Fin 2 → X)) (ν : FiniteLaw (O₀ × O₁ → X))
    (hs : LayersSupported lam ν) (φ : (O₀ × O₁ → X) → ℝ) :
    lam.expect (fun y => φ (layerOf y 0) * φ (layerOf y 0)) =
      mnrm ν (halfDensity lam ν) φ ^ 2 := by
  have hnn : 0 ≤ ν.expect (fun x => (1 + halfDensity lam ν x) * φ x ^ 2) :=
    ν.expect_nonneg fun x => mul_nonneg (one_add_halfDensity_nonneg lam ν x) (sq_nonneg _)
  have hm : mnrm ν (halfDensity lam ν) φ ^ 2 =
      ν.expect (fun x => (1 + halfDensity lam ν x) * φ x ^ 2) := by
    unfold mnrm
    exact Real.sq_sqrt hnn
  rw [hm]
  have hterm : ∀ x : O₀ × O₁ → X, ν.weight x * ((1 + halfDensity lam ν x) * φ x ^ 2) =
      (∑ y, if layerOf y 0 = x then lam.weight y else 0) * (φ x * φ x) := by
    intro x
    unfold halfDensity
    split_ifs with h
    · have hz : (∑ y, if layerOf y 0 = x then lam.weight y else 0) = 0 := by
        refine Finset.sum_eq_zero fun y _ => ?_
        split_ifs with hy
        · by_contra hw
          have := (hs y hw).1
          rw [hy] at this
          exact this h
        · rfl
      rw [h, hz]
      ring
    · field_simp
      ring
  unfold FiniteLaw.expect
  rw [Finset.sum_congr rfl fun x _ => hterm x]
  rw [sum_marginal_mul (fun y => layerOf y 0) lam.weight (fun x => φ x * φ x)]

/-- **`Emission.upRecord_sym_bracket` with the kernels of the records.** If both layers of the new
and of the old two-layer laws are supported where `ν` is, the kernels `K' = pairDensity lamN ν`,
`O = pairDensity lamO ν` and the half density `u₀ = halfDensity lamO ν` satisfy the identification
hypotheses, and a bound `C` on the symmetric part of `𝒞_{K'} - 𝒞_O` relative to `(1 + u₀)ν` gives
the bracket of the symmetric part of the emitted change at `ι`. -/
theorem upRecord_sym_bracket_of_support (lamN lamO : FiniteLaw (O₀ × O₁ × Fin 2 → X))
    (φ₀ : ZMod 6 → O₀) (φ₁ : ZMod 6 → O₁) (ν : FiniteLaw (O₀ × O₁ → X))
    (hsN : LayersSupported lamN ν) (hsO : LayersSupported lamO ν) {C : ℝ} (hC : 0 ≤ C)
    (hB : ∀ φ ψ, |((centredForm ν (halfDensity lamO ν) (pairDensity lamN ν) φ ψ -
          centredForm ν (halfDensity lamO ν) (pairDensity lamO ν) φ ψ) +
        (centredForm ν (halfDensity lamO ν) (pairDensity lamN ν) ψ φ -
          centredForm ν (halfDensity lamO ν) (pairDensity lamO ν) ψ φ)) / 2| ≤
      C * mnrm ν (halfDensity lamO ν) φ * mnrm ν (halfDensity lamO ν) ψ) :
    reservedCut.Bracket
      (C • reservedCut.diagonalLaw (plusMarginal reservedCut (emit lamO (upEmission φ₀ φ₁)).weight))
      (symPart reservedCut (signedIntegral (emit lamN (upEmission φ₀ φ₁)).weight -
        signedIntegral (emit lamO (upEmission φ₀ φ₁)).weight))
      (C • reservedCut.diagonalLaw
        (plusMarginal reservedCut (emit lamO (upEmission φ₀ φ₁)).weight)) :=
  upRecord_sym_bracket lamN lamO φ₀ φ₁ ν (halfDensity lamO ν) (pairDensity lamN ν)
    (pairDensity lamO ν) (pair_density_eq lamN ν hsN) (pair_density_eq lamO ν hsO)
    (half_density_eq lamO ν hsO) hC hB

/-- The skew counterpart of `upRecord_sym_bracket_of_support`. -/
theorem upRecord_skew_bracket_of_support (lamN lamO : FiniteLaw (O₀ × O₁ × Fin 2 → X))
    (φ₀ : ZMod 6 → O₀) (φ₁ : ZMod 6 → O₁) (ν : FiniteLaw (O₀ × O₁ → X))
    (hsN : LayersSupported lamN ν) (hsO : LayersSupported lamO ν) {C : ℝ} (hC : 0 ≤ C)
    (hB : ∀ φ ψ, |((centredForm ν (halfDensity lamO ν) (pairDensity lamN ν) φ ψ -
          centredForm ν (halfDensity lamO ν) (pairDensity lamO ν) φ ψ) -
        (centredForm ν (halfDensity lamO ν) (pairDensity lamN ν) ψ φ -
          centredForm ν (halfDensity lamO ν) (pairDensity lamO ν) ψ φ)) / 2| ≤
      C * mnrm ν (halfDensity lamO ν) φ * mnrm ν (halfDensity lamO ν) ψ) :
    reservedCut.Bracket
      (C • reservedCut.diagonalLaw (plusMarginal reservedCut (emit lamO (upEmission φ₀ φ₁)).weight))
      (skewPart reservedCut (signedIntegral (emit lamN (upEmission φ₀ φ₁)).weight -
        signedIntegral (emit lamO (upEmission φ₀ φ₁)).weight))
      (C • reservedCut.diagonalLaw
        (plusMarginal reservedCut (emit lamO (upEmission φ₀ φ₁)).weight)) :=
  upRecord_skew_bracket lamN lamO φ₀ φ₁ ν (halfDensity lamO ν) (pairDensity lamN ν)
    (pairDensity lamO ν) (pair_density_eq lamN ν hsN) (pair_density_eq lamO ν hsO)
    (half_density_eq lamO ν hsO) hC hB

end Sarkozy.UpperComparison
