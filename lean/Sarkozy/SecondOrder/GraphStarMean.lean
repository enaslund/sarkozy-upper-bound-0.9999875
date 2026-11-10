module

public import Sarkozy.SecondOrder.StarMean
public import Sarkozy.SecondOrder.GraphPinned

/-!
# The complete-star mean for graph laws (`lem:star-mean` at `μ = λ_p(G⁺)`)

`paper/sections/15_second_order.tex`: `lem:star-mean` is stated for `μ = λ_p(G⁺)`, a pinned half
law with count errors `e_i`. With `graphPinned` (`GraphPinned.lean`) the ordered-star bound and
the star mean hold for every oriented graph `G⁺` on `U` with `Inj_p(G⁺) ≠ ∅` whose count errors
`e_i = (𝔈_{d_i} + 2^{d_i}(n - 1))/p` are below one. The only literature inputs are Weil (H1) and
the moving-root moments (H5).
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace Sarkozy.SecondOrder

open Sarkozy.Target Sarkozy.Labellings

variable {p : ℕ} [hp : Fact p.Prime] {U K : Type*} [Fintype U] [DecidableEq U] [LinearOrder U]
  [Fintype K]

/-- **`prop:advance:ordered-star` for graph laws**, from Weil and H5. -/
theorem ordered_star_graph (hW : Target.Weil) (hM : Target.MovingRoot) (hp2 : p ≠ 2)
    (G : OrientedGraph U) (hne : (injLabellings (ZMod p) G).Nonempty)
    (he : ∀ i, graphCountError (p := p) G i < 1) (𝒯 : Finset (Finset U))
    (h𝒯 : ∀ T ∈ 𝒯, 3 ≤ T.card) (a : Finset U → ℝ) :
    let L := graphPinned (weilBound_of_target hW p hp2) G hne he
    ∑ x, L.μ x * (∑ i, pivotF 𝒯 a i x) ^ 2 ≤
        (1 / Real.sqrt p) ^ 2 * (∑ i, pivotD2 L 𝒯 a i + 2 * (1 / Real.sqrt p) *
          ∑ i, pivotK L 𝒯 a i * ∑ j ∈ univ.filter (· < i), Real.sqrt (pivotD2 L 𝒯 a j)) ∧
      ∀ i, |∑ x, L.μ x * pivotF 𝒯 a i x| ≤ (1 / Real.sqrt p) ^ 2 * pivotK L 𝒯 a i :=
  ordered_star hW hM hp2 _ 𝒯 h𝒯 a

/-- **`lem:star-mean` for graph laws**, from Weil and H5: `Var_λ h_⋆ ≤ M_⋆²` and
`|E_λ h_⋆| ≤ z_⋆ = r²(∑_i K_i + |B_even|)`. -/
theorem star_mean_graph (hW : Target.Weil) (hM : Target.MovingRoot) (hp2 : p ≠ 2)
    (G : OrientedGraph U) (hne : (injLabellings (ZMod p) G).Nonempty)
    (he : ∀ i, graphCountError (p := p) G i < 1) (N : K → Finset U) (c : K → Finset U → ℝ) :
    let L := graphPinned (weilBound_of_target hW p hp2) G hne he
    ∑ x, L.μ x * (Spectral.starFunction (F := ZMod p) N c x -
        ∑ y, L.μ y * Spectral.starFunction (F := ZMod p) N c y) ^ 2 ≤
        (1 / Real.sqrt p) ^ 2 * (∑ i, pivotD2 L supports3 (starCoeff N c) i +
          2 * (1 / Real.sqrt p) * ∑ i, pivotK L supports3 (starCoeff N c) i *
            ∑ j ∈ univ.filter (· < i), Real.sqrt (pivotD2 L supports3 (starCoeff N c) j)) ∧
      |∑ x, L.μ x * Spectral.starFunction (F := ZMod p) N c x| ≤
        (1 / Real.sqrt p) ^ 2 * (∑ i, pivotK L supports3 (starCoeff N c) i +
          |starBEven N c|) :=
  star_mean hW hM hp2 _ N c

end Sarkozy.SecondOrder
