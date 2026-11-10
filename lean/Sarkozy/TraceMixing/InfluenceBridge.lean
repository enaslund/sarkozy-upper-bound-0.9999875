module

public import Sarkozy.TraceMixing.Slot
public import Sarkozy.Influence.Bridge

/-!
# Degrees of the two oriented-graph types

`Sarkozy.Influence.ofLabellings` (WP-P, `Influence/Bridge.lean`) reads a `Labellings` oriented
graph as an `Influence` oriented graph, with the same `Inj_p(G)` and graph law. The degree
`Sarkozy.TraceMixing.degree` used in `lem:trace-mixing` agrees with WP-P's
`Influence.OrientedGraph.deg` (`deg_ofLabellings`), so the degree hypotheses of the two
developments transfer. This file is not imported by `Sarkozy.TraceMixing.Main`.
-/

@[expose] public section

open Finset

namespace Sarkozy.TraceMixing

open Sarkozy.Labellings

variable {W : Type*} [Fintype W] [DecidableEq W]

theorem deg_ofLabellings (G : OrientedGraph W) (u : W) :
    (Influence.ofLabellings G).deg u = degree G u := by
  classical
  unfold Influence.OrientedGraph.deg degree nbrCount
  apply Finset.card_bij (fun a _ => a)
  · intro a ha
    rw [Finset.mem_filter] at ha
    rw [Finset.mem_filter, Finset.mem_erase]
    have hadj : (u, a) ∈ G.E ∨ (a, u) ∈ G.E := ha.2
    refine ⟨⟨?_, mem_univ _⟩, hadj.symm⟩
    rintro rfl
    rcases hadj with h | h <;> exact G.loopless _ h
  · intro a _ b _ h
    exact h
  · intro b hb
    rw [Finset.mem_filter, Finset.mem_erase] at hb
    refine ⟨b, ?_, rfl⟩
    rw [Finset.mem_filter]
    exact ⟨mem_univ _, (hb.2.symm : (u, b) ∈ G.E ∨ (b, u) ∈ G.E)⟩

end Sarkozy.TraceMixing
