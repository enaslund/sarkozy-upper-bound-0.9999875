module

public import Sarkozy.PartV.SixQuery
public import Sarkozy.PartV.ChamberCut

@[expose] public section

/-!
# (R5) for the kept records of an upper block (`prop:record:upper`(i))

`paper/sections/26_upper_comparison.tex`, `prop:record:upper`(i), "Acceptance and
admissibility": every retained record accepts `𝓔₆`, so under it each query pair has a nonzero
square difference at every prime of the block, which is (R5).

For the records that are **kept**, this follows from the edge acceptance of
`lem:six-query-retention` (V1's `TwoLayerEdgeAccepts`, `FoldedEdgeAccepts`): the block field laws
`λ_𝔅(G)` are tensor products over the primes of the uniform laws on the injective strict-square
labellings, so every labelling they charge satisfies every edge of the field graph at every prime.
V1 proves this at one prime for the tail field laws (`PartV.tail_record_accepts`); here it is
proved for the block field laws of an upper block, at every prime of the block:
* `blockGraphLaw_support`: a block labelling charged by `λ_𝔅(G)` is, prime by prime, an injective
  strict-square labelling;
* `kept_two_layer_accepts`: a kept (edge-accepting) two-layer record accepts every query of `𝓔₆`
  at every prime of the block;
* `kept_folded_accepts`: the same for a kept folded record.

For the **changed** records, acceptance is a property of the replacing laws (their support lies
where the required queries hold: (F7), `prop:dense-comparison`(a), `prop:le-mixture`; V3's
`PartVRecords.Hdense_support_req` for the softened kernels) and is not repeated here.
-/

open Finset

namespace Sarkozy.UpperComparison

open Sarkozy.Labellings Sarkozy.PartV

variable {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]

/-- **The support of a block law**: a block labelling charged by `λ_𝔅(G) = ⊗_p λ_p(G)` is, at every
prime of the block, an injective strict-square labelling of `G`. -/
theorem blockGraphLaw_support {W : Type} [Fintype W] [DecidableEq W] (G : OrientedGraph W)
    (hne : ∀ i, (injLabellings (ZMod (pr i)) G).Nonempty) {y : W → BlockLabel pr}
    (hy : (blockGraphLaw pr G hne).weight y ≠ 0) (i : ι) :
    (fun w => y w i) ∈ injLabellings (ZMod (pr i)) G := by
  unfold blockGraphLaw at hy
  rw [tensor_weight, Finset.prod_ne_zero_iff] at hy
  exact (graphLaw_weight_ne_zero _ _ _).mp (hy i (mem_univ i))

/-- **(R5) for a kept two-layer record of an upper block** (`prop:record:upper`(i)): if the record
edge-accepts `𝓔₆` (`lem:six-query-retention`), every labelling `z` it charges has
`χ_p(z_{target} - z_{source}) = 1` for every query and every prime `p` of the block. -/
theorem kept_two_layer_accepts (hne : UpperNonempty pr) (t : PType × PType)
    (φ : t.1.Pat × t.2.Pat) (hacc : TwoLayerEdgeAccepts t φ) {z : Slot → BlockLabel pr}
    (hz : (upComponent (upperBlockFieldLaws pr hne) (true, ⟨t, φ⟩)).weight z ≠ 0) (j : Chamber)
    (i : ι) : quadraticChar (ZMod (pr i)) (z (queryTarget j) i - z (querySource j) i) = 1 := by
  change (emit (blockGraphLaw pr (fieldGraph t.1.field t.2.field (Fin 2)) (hne.two _ _))
    (upEmission (t.1.pat φ.1) (t.2.pat φ.2))).weight z ≠ 0 at hz
  obtain ⟨y, hy, rfl⟩ := emit_support _ _ hz
  have hfeas := blockGraphLaw_support pr _ _ hy i
  rw [mem_injLabellings_iff_feasible] at hfeas
  obtain ⟨-, hedge⟩ := hfeas
  simp only [fieldGraph, mem_twoLayerGraph, mem_univ, forall_const] at hedge
  have h := hedge ((t.1.pat φ.1 0, t.2.pat φ.2 j, 0), (t.1.pat φ.1 2, t.2.pat φ.2 (rot j), 1))
    (hacc j)
  have h1 : upEmission (t.1.pat φ.1) (t.2.pat φ.2) (queryTarget j) =
      (t.1.pat φ.1 2, t.2.pat φ.2 (rot j), 1) := by
    change (t.1.pat φ.1 2, t.2.pat φ.2 (chamberRotation j), layerFin 1) = _
    rw [layerFin_one, rot_eq_chamberRotation]
  have h2 : upEmission (t.1.pat φ.1) (t.2.pat φ.2) (querySource j) =
      (t.1.pat φ.1 0, t.2.pat φ.2 j, 0) := by
    change (t.1.pat φ.1 0, t.2.pat φ.2 j, layerFin 0) = _
    rw [layerFin_zero]
  rw [Function.comp_apply, Function.comp_apply, h1, h2]
  exact h

/-- **(R5) for a kept folded record of an upper block**: the same for a folded record that
edge-accepts `𝓔₆`, read on its one-layer field graph copied onto both layers. -/
theorem kept_folded_accepts (hne : UpperNonempty pr) (t : PType × PType)
    (φ : t.1.Pat × t.2.Pat) (hacc : FoldedEdgeAccepts t φ) {z : Slot → BlockLabel pr}
    (hz : (upComponent (upperBlockFieldLaws pr hne) (false, ⟨t, φ⟩)).weight z ≠ 0) (j : Chamber)
    (i : ι) : quadraticChar (ZMod (pr i)) (z (queryTarget j) i - z (querySource j) i) = 1 := by
  change (emit (blockGraphLaw pr (fieldGraph t.1.field t.2.field (Fin 1)) (hne.one _ _))
    (upDiagEmission (t.1.pat φ.1) (t.2.pat φ.2))).weight z ≠ 0 at hz
  obtain ⟨y, hy, rfl⟩ := emit_support _ _ hz
  have hfeas := blockGraphLaw_support pr _ _ hy i
  rw [mem_injLabellings_iff_feasible] at hfeas
  obtain ⟨-, hedge⟩ := hfeas
  simp only [fieldGraph, mem_twoLayerGraph, mem_univ, forall_const] at hedge
  have h := hedge ((t.1.pat φ.1 0, t.2.pat φ.2 j, 0), (t.1.pat φ.1 2, t.2.pat φ.2 (rot j), 0))
    (hacc j)
  have h1 : upDiagEmission (t.1.pat φ.1) (t.2.pat φ.2) (queryTarget j) =
      (t.1.pat φ.1 2, t.2.pat φ.2 (rot j), 0) := by
    change (t.1.pat φ.1 2, t.2.pat φ.2 (chamberRotation j), 0) = _
    rw [rot_eq_chamberRotation]
  have h2 : upDiagEmission (t.1.pat φ.1) (t.2.pat φ.2) (querySource j) =
      (t.1.pat φ.1 0, t.2.pat φ.2 j, 0) := rfl
  rw [Function.comp_apply, Function.comp_apply, h1, h2]
  exact h

end Sarkozy.UpperComparison
