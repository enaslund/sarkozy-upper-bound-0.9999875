module

public import Sarkozy.Spectral.GlueStars





@[expose] public section

open scoped BigOperators InnerProductSpace
open Finset

namespace Sarkozy.SecondOrder

open Sarkozy Sarkozy.InfluenceGlue Sarkozy.Spectral

variable {p : ℕ} [Fact p.Prime] {U K : Type*} [Fintype U] [DecidableEq U] [Fintype K]

/-- **`lem:record:direct-star-inputs` (i), (ii)**: the graph law of `G` is the pinned half law
`graphPinned`, with the count errors of `lem:extension`. In `L²(λ_p(G))`, the centred star
function has norm at most `M_⋆` (`prop:advance:ordered-star`), and its mean is at most `z_⋆`
(`lem:star-mean`); these are the inputs (H3) of the direct star route. -/
theorem direct_star_inputs [LinearOrder U] (hW : Target.Weil) (hMR : Target.MovingRoot)
    (hp2 : p ≠ 2) (G : Labellings.OrientedGraph U)
    (hne : (Labellings.injLabellings (ZMod p) G).Nonempty)
    (he : ∀ i, graphCountError (p := p) G i < 1) (N : K → Finset U)
    (c : K → Finset U → ℝ) :
    let L := graphPinned (Labellings.weilBound_of_target hW p hp2) G hne he
    (pinnedLaw L).weight = (Labellings.graphLaw G hne).weight ∧
    ‖l2Map (pinnedLaw L) (starFunction N c) -
        ⟪l2Map (pinnedLaw L) (fun _ => 1), l2Map (pinnedLaw L) (starFunction N c)⟫_ℝ •
          l2Map (pinnedLaw L) (fun _ => 1)‖ ≤ starMstar L N c ∧
    ‖⟪l2Map (pinnedLaw L) (fun _ => 1), l2Map (pinnedLaw L) (starFunction N c)⟫_ℝ‖ ≤
      starZstar L N c :=
  glue_star_inputs_graph hW hMR hp2 G hne he N c

end Sarkozy.SecondOrder
