module

public import Sarkozy.Variance.RestorationBlocks
public import Sarkozy.Variance.NonrootMass

/-!
# Restoration for V1's middle reference (`lem:record:restoration`, steps (C), (B) and the
pointwise branch)

`paper/sections/22_variance.tex`, `lem:record:restoration`, for the selected blocks of `X` each
carrying V1's middle reference law `μ_𝔅 = middleReference F_𝔅 W_𝔅 r_𝔅`
(`PartV.middleReference`, on the 72 slots), and positive outside factors. The decomposition
`μ_𝔅 = (1 + h_𝔅)⁻¹(Π^rt_𝔅 + 𝓜_𝔅)` of step (C) is proved (`middleReference_split`), with
`h_𝔅 = P(r_𝔅) - 1 = (3w_D + 2w_S + v_L) r + …` (`eq:record:nonroot-mass`). The root `Π^rt_𝔅` is
the two-layer root component of type `L`.

The remaining hypotheses are those of `restoration_pointwise_blocks` other than `hmix`:
* (E1) for the nonroot part of the product;
* the root's half marginals `ν_𝔅` at the fold chamber, from `lem:record:fold-identification`;
* hypothesis (A), `ν_𝔅 ≤ M_𝔅 λ_𝔅`.
-/

@[expose] public section

open Finset
open scoped BigOperators
open Sarkozy.RecordExpansion Sarkozy.PartV

namespace Sarkozy.Variance

variable {J : Type*} [Fintype J] [DecidableEq J] {X : J → Type} [∀ b, Fintype (X b)]
  [∀ b, DecidableEq (X b)]

/-- **`lem:record:restoration`, (C), (B) and the pointwise branch, for V1's middle reference**:
`(1 + h - (1 + z) h C_X) Y ≤ ∏ M_𝔅 · Y[⊗_X Diag(λ) ⊗ O]`, with
`h = ∏ P(r_𝔅) - 1` (the product of the masses of `μ̃_𝔅`, minus one). -/
theorem restoration_pointwise_middle (c : ReflectionCut Slot)
    (O : ∀ j, ((Slot → X j) → ℝ) →ₗ[ℝ] ℝ) (Xs : Finset J) (hO : ∀ j, j ∉ Xs → c.Positive (O j))
    (F : (∀ b, X b) → ℝ) {Yμ : ℝ} (hYdef : diagonalIntegral (tensorLaw O) F = Yμ)
    (Fl : ∀ j, MiddleFieldLaws (X j)) (W : J → MiddleWeights) (r : J → ℝ) (hr : ∀ j, 0 ≤ r j)
    (hOX : ∀ j ∈ Xs, O j = signedIntegral (middleReference (Fl j) (W j) (hr j)).weight)
    {CX z : ℝ}
    (hE1M : diagonalIntegral (tensorLaw (onBlocks Xs
          (fun j => signedIntegral (midComponent (Fl j) rootIdx).weight +
            middleNonroot (Fl j) (W j) (r j)) O)) F -
        diagonalIntegral (tensorLaw (onBlocks Xs
          (fun j => signedIntegral (midComponent (Fl j) rootIdx).weight) O)) F ≤
      (1 + z) * (∏ j ∈ Xs, (1 + (midPoly (W j) (r j) - 1)) - 1) * CX * Yμ)
    (ν lam : ∀ j, (c.Half → X j) → ℝ)
    (hplus : ∀ j ∈ Xs, plusMarginal c (midComponent (Fl j) rootIdx).weight = ν j)
    (hminus : ∀ j ∈ Xs, minusMarginal c (midComponent (Fl j) rootIdx).weight = ν j)
    (M : J → ℝ) (hA : ∀ j ∈ Xs, ∀ x, ν j x ≤ M j * lam j x) :
    (1 + (∏ j ∈ Xs, (1 + (midPoly (W j) (r j) - 1)) - 1) -
        (1 + z) * (∏ j ∈ Xs, (1 + (midPoly (W j) (r j) - 1)) - 1) * CX) * Yμ ≤
      (∏ j ∈ Xs, M j) *
        diagonalIntegral (tensorLaw (onBlocks Xs (fun j => c.diagonalLaw (lam j)) O)) F :=
  restoration_pointwise_blocks c O Xs hO F hYdef
    (fun j => (midComponent (Fl j) rootIdx).weight)
    (fun j _ z => (midComponent (Fl j) rootIdx).nonneg z)
    (fun j => middleNonroot (Fl j) (W j) (r j)) (fun j => midPoly (W j) (r j) - 1)
    (fun j _ => (middleReference_split (Fl j) (W j) (hr j)).2)
    (fun j hj => (hOX j hj).trans (middleReference_split (Fl j) (W j) (hr j)).1)
    hE1M ν lam hplus hminus M hA

end Sarkozy.Variance
