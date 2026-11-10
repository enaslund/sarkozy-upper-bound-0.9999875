module

public import Sarkozy.UpperComparison.Transfer
public import Sarkozy.PartV.Acceptance

@[expose] public section

/-!
# The emission of a two-layer upper record at the reserved cut

`paper/sections/26_upper_comparison.tex`, paragraph "The repair": "The emission acts within each
layer, so a test function of an emitted half is a test function of the field half". This file
proves that statement for V1's two-layer upper emission `upEmission φ₀ φ₁` at the reserved cut
`ι`, and with `Transfer` turns the field-level bounds of `ForestRecords`, `DenseLaws` and
`LEMixture` into the brackets of `(CP4)(b)` for the emitted change.

* `reserved_half_layer`: the slots of the plus half of `ι` are those of layer `0`;
* `upHalf`: the emission of a half, `x ↦ (v ↦ x(φ₀ v₀, φ₁ v₁))`;
* `upEmission_form`: the cut form at `ι` of an emitted two-layer law is the pair form of its two
  layers read through `upHalf`;
* `upEmission_halfNorm`: the half marginal at `ι` of the emitted law is the image of the law of
  layer `0`, as a norm identity;
* `upRecord_sym_bracket`, `upRecord_skew_bracket`: for a changed two-layer record whose new and old
  two-layer laws have pair laws `K'(ν ⊗ ν)` and `O(ν ⊗ ν)` (the kernels of the analytic
  propositions) and whose old layer-`0` law is `m₀ = (1 + u₀)ν`, a bound `C` on the symmetric
  (skew) part of `𝒞_{K'} - 𝒞_O` relative to `m₀` gives the bracket of the symmetric (skew) part of
  the emitted change at `ι`, with the half marginal of the emitted old record as envelope.
-/

open Finset

namespace Sarkozy.UpperComparison

open Sarkozy.RecordExpansion Sarkozy.Recentering Sarkozy.Structured Sarkozy.PartV

/-- The plus half of the reserved cut is layer `0`. -/
theorem reserved_half_layer (v : reservedCut.Half) : v.1.2.2 = 0 := by
  have h := v.2
  change v.1 ∈ (Finset.univ ×ˢ (Finset.univ ×ˢ ({0} : Finset Layer))) at h
  rw [Finset.mem_product, Finset.mem_product, Finset.mem_singleton] at h
  exact h.2.2

variable {O₀ O₁ X : Type*} [Fintype O₀] [DecidableEq O₀] [Fintype O₁] [DecidableEq O₁]
  [Fintype X] [DecidableEq X]

/-- The emission of a half: a field half configuration `x : O₀ × O₁ → X` read on the plus half of
`ι`. -/
def upHalf (φ₀ : ZMod 6 → O₀) (φ₁ : ZMod 6 → O₁) (x : O₀ × O₁ → X) : reservedCut.Half → X :=
  fun v => x (φ₀ v.1.1, φ₁ v.1.2.1)

/-- The layer `k` of a two-layer field labelling. -/
def layerOf (y : O₀ × O₁ × Fin 2 → X) (k : Fin 2) : O₀ × O₁ → X := fun o => y (o.1, o.2, k)

/-- **The cut form of an emitted two-layer law at `ι`** is the pair form of its two layers read
through the half emission. -/
theorem upEmission_form (lam : FiniteLaw (O₀ × O₁ × Fin 2 → X)) (φ₀ : ZMod 6 → O₀)
    (φ₁ : ZMod 6 → O₁) (F G : (reservedCut.Half → X) → ℝ) :
    reservedCut.form (signedIntegral (emit lam (upEmission φ₀ φ₁)).weight) F G =
      lam.expect (fun y => F (upHalf φ₀ φ₁ (layerOf y 0)) * G (upHalf φ₀ φ₁ (layerOf y 1))) := by
  unfold ReflectionCut.form
  rw [← FiniteLaw.expect_eq_signedIntegral, expect_emit]
  apply FiniteLaw.expect_congr
  intro y
  have h0 : (fun v : reservedCut.Half => (y ∘ upEmission φ₀ φ₁) v.1) =
      upHalf φ₀ φ₁ (layerOf y 0) := by
    funext v
    change y (φ₀ v.1.1, φ₁ v.1.2.1, layerFin v.1.2.2) = y (φ₀ v.1.1, φ₁ v.1.2.1, 0)
    rw [reserved_half_layer v, layerFin_zero]
  have h1 : (fun v : reservedCut.Half => (y ∘ upEmission φ₀ φ₁) (reservedCut.flip v.1)) =
      upHalf φ₀ φ₁ (layerOf y 1) := by
    funext v
    change y (φ₀ v.1.1, φ₁ v.1.2.1, layerFin (1 - v.1.2.2)) = y (φ₀ v.1.1, φ₁ v.1.2.1, 1)
    have h10 : layerFin (1 - 0 : Layer) = 1 := by decide
    rw [reserved_half_layer v, h10]
  rw [h0, h1]

/-- **The half marginal at `ι` of an emitted two-layer law** is the image of its layer-`0` law:
`∑_x m_+(x) F(x)² = E[F(e(y₀))²]`. -/
theorem upEmission_halfNorm (lam : FiniteLaw (O₀ × O₁ × Fin 2 → X)) (φ₀ : ZMod 6 → O₀)
    (φ₁ : ZMod 6 → O₁) (F : (reservedCut.Half → X) → ℝ) :
    ∑ x, plusMarginal reservedCut (emit lam (upEmission φ₀ φ₁)).weight x * (F x * F x) =
      lam.expect (fun y => F (upHalf φ₀ φ₁ (layerOf y 0)) * F (upHalf φ₀ φ₁ (layerOf y 0))) := by
  unfold plusMarginal
  rw [sum_marginal_mul (fun z : Slot → X => fun v : reservedCut.Half => z v.1)
    (emit lam (upEmission φ₀ φ₁)).weight (fun x => F x * F x)]
  change (emit lam (upEmission φ₀ φ₁)).expect
      (fun z => F (fun v : reservedCut.Half => z v.1) * F (fun v : reservedCut.Half => z v.1)) = _
  rw [expect_emit]
  apply FiniteLaw.expect_congr
  intro y
  have h0 : (fun v : reservedCut.Half => (y ∘ upEmission φ₀ φ₁) v.1) =
      upHalf φ₀ φ₁ (layerOf y 0) := by
    funext v
    change y (φ₀ v.1.1, φ₁ v.1.2.1, layerFin v.1.2.2) = y (φ₀ v.1.1, φ₁ v.1.2.1, 0)
    rw [reserved_half_layer v, layerFin_zero]
  rw [h0]

/-- **The bracket of the symmetric part of an emitted change** (`prop:record:upper`(i),
"Records repaired", "Records replaced"). Let the new and the old two-layer laws `lamN`, `lamO` of a
changed record have pair laws with densities `K'` and `O` relative to `ν ⊗ ν` on the field halves
(`hN`, `hO`: the kernels of `ForestRecords`, `DenseLaws`, `LEMixture`), and let the layer-`0` law of
the old record be `m₀ = (1 + u₀)ν` (`hm₀`). If the symmetric part of `𝒞_{K'} - 𝒞_O` has norm at
most `C` relative to `m₀`, then the symmetric part at `ι` of the emitted change
`Π_new - Π_old` has the bracket with coefficient `C` and envelope `Diag(m_+)`, `m_+` the half
marginal of the emitted old record. -/
theorem upRecord_sym_bracket (lamN lamO : FiniteLaw (O₀ × O₁ × Fin 2 → X)) (φ₀ : ZMod 6 → O₀)
    (φ₁ : ZMod 6 → O₁) (ν : FiniteLaw (O₀ × O₁ → X)) (u0 : (O₀ × O₁ → X) → ℝ)
    (K' O : (O₀ × O₁ → X) × (O₀ × O₁ → X) → ℝ)
    (hN : ∀ φ ψ : (O₀ × O₁ → X) → ℝ,
      lamN.expect (fun y => φ (layerOf y 0) * ψ (layerOf y 1)) = kform ν ν K' φ ψ)
    (hO : ∀ φ ψ : (O₀ × O₁ → X) → ℝ,
      lamO.expect (fun y => φ (layerOf y 0) * ψ (layerOf y 1)) = kform ν ν O φ ψ)
    (hm₀ : ∀ φ : (O₀ × O₁ → X) → ℝ,
      lamO.expect (fun y => φ (layerOf y 0) * φ (layerOf y 0)) = mnrm ν u0 φ ^ 2)
    {C : ℝ} (hC : 0 ≤ C)
    (hB : ∀ φ ψ, |((centredForm ν u0 K' φ ψ - centredForm ν u0 O φ ψ) +
        (centredForm ν u0 K' ψ φ - centredForm ν u0 O ψ φ)) / 2| ≤
      C * mnrm ν u0 φ * mnrm ν u0 ψ) :
    reservedCut.Bracket
      (C • reservedCut.diagonalLaw (plusMarginal reservedCut (emit lamO (upEmission φ₀ φ₁)).weight))
      (symPart reservedCut (signedIntegral (emit lamN (upEmission φ₀ φ₁)).weight -
        signedIntegral (emit lamO (upEmission φ₀ φ₁)).weight))
      (C • reservedCut.diagonalLaw
        (plusMarginal reservedCut (emit lamO (upEmission φ₀ φ₁)).weight)) := by
  refine sym_bracket_of_field_bound reservedCut
    (plusMarginal_nonneg reservedCut (emit lamO (upEmission φ₀ φ₁)).nonneg) ν u0
    (upHalf φ₀ φ₁) _ (fun φ ψ => centredForm ν u0 K' φ ψ - centredForm ν u0 O φ ψ) ?_ ?_ hC hB
  · intro F G
    have hsub : reservedCut.form (signedIntegral (emit lamN (upEmission φ₀ φ₁)).weight -
        signedIntegral (emit lamO (upEmission φ₀ φ₁)).weight) F G =
        reservedCut.form (signedIntegral (emit lamN (upEmission φ₀ φ₁)).weight) F G -
          reservedCut.form (signedIntegral (emit lamO (upEmission φ₀ φ₁)).weight) F G := by
      unfold ReflectionCut.form
      rw [LinearMap.sub_apply]
    rw [hsub, upEmission_form, upEmission_form]
    have e1 := hN (F ∘ upHalf φ₀ φ₁) (G ∘ upHalf φ₀ φ₁)
    have e2 := hO (F ∘ upHalf φ₀ φ₁) (G ∘ upHalf φ₀ φ₁)
    simp only [Function.comp_apply] at e1 e2
    rw [e1, e2]
    unfold centredForm
    ring
  · intro F
    rw [upEmission_halfNorm]
    have h := hm₀ (F ∘ upHalf φ₀ φ₁)
    simp only [Function.comp_apply] at h
    rw [h]
    exact Real.sqrt_sq (by unfold mnrm; exact Real.sqrt_nonneg _)

/-- **The bracket of the skew part of an emitted change**, as `upRecord_sym_bracket` with the skew
parts. -/
theorem upRecord_skew_bracket (lamN lamO : FiniteLaw (O₀ × O₁ × Fin 2 → X)) (φ₀ : ZMod 6 → O₀)
    (φ₁ : ZMod 6 → O₁) (ν : FiniteLaw (O₀ × O₁ → X)) (u0 : (O₀ × O₁ → X) → ℝ)
    (K' O : (O₀ × O₁ → X) × (O₀ × O₁ → X) → ℝ)
    (hN : ∀ φ ψ : (O₀ × O₁ → X) → ℝ,
      lamN.expect (fun y => φ (layerOf y 0) * ψ (layerOf y 1)) = kform ν ν K' φ ψ)
    (hO : ∀ φ ψ : (O₀ × O₁ → X) → ℝ,
      lamO.expect (fun y => φ (layerOf y 0) * ψ (layerOf y 1)) = kform ν ν O φ ψ)
    (hm₀ : ∀ φ : (O₀ × O₁ → X) → ℝ,
      lamO.expect (fun y => φ (layerOf y 0) * φ (layerOf y 0)) = mnrm ν u0 φ ^ 2)
    {C : ℝ} (hC : 0 ≤ C)
    (hB : ∀ φ ψ, |((centredForm ν u0 K' φ ψ - centredForm ν u0 O φ ψ) -
        (centredForm ν u0 K' ψ φ - centredForm ν u0 O ψ φ)) / 2| ≤
      C * mnrm ν u0 φ * mnrm ν u0 ψ) :
    reservedCut.Bracket
      (C • reservedCut.diagonalLaw (plusMarginal reservedCut (emit lamO (upEmission φ₀ φ₁)).weight))
      (skewPart reservedCut (signedIntegral (emit lamN (upEmission φ₀ φ₁)).weight -
        signedIntegral (emit lamO (upEmission φ₀ φ₁)).weight))
      (C • reservedCut.diagonalLaw
        (plusMarginal reservedCut (emit lamO (upEmission φ₀ φ₁)).weight)) := by
  refine skew_bracket_of_field_bound reservedCut
    (plusMarginal_nonneg reservedCut (emit lamO (upEmission φ₀ φ₁)).nonneg) ν u0
    (upHalf φ₀ φ₁) _ (fun φ ψ => centredForm ν u0 K' φ ψ - centredForm ν u0 O φ ψ) ?_ ?_ hC hB
  · intro F G
    have hsub : reservedCut.form (signedIntegral (emit lamN (upEmission φ₀ φ₁)).weight -
        signedIntegral (emit lamO (upEmission φ₀ φ₁)).weight) F G =
        reservedCut.form (signedIntegral (emit lamN (upEmission φ₀ φ₁)).weight) F G -
          reservedCut.form (signedIntegral (emit lamO (upEmission φ₀ φ₁)).weight) F G := by
      unfold ReflectionCut.form
      rw [LinearMap.sub_apply]
    rw [hsub, upEmission_form, upEmission_form]
    have e1 := hN (F ∘ upHalf φ₀ φ₁) (G ∘ upHalf φ₀ φ₁)
    have e2 := hO (F ∘ upHalf φ₀ φ₁) (G ∘ upHalf φ₀ φ₁)
    simp only [Function.comp_apply] at e1 e2
    rw [e1, e2]
    unfold centredForm
    ring
  · intro F
    rw [upEmission_halfNorm]
    have h := hm₀ (F ∘ upHalf φ₀ φ₁)
    simp only [Function.comp_apply] at h
    rw [h]
    exact Real.sqrt_sq (by unfold mnrm; exact Real.sqrt_nonneg _)

end Sarkozy.UpperComparison
