module

public import Sarkozy.PartV.Acceptance

@[expose] public section

/-!
# Which upper records accept the six queries (`lem:six-query-retention`)

`paper/sections/26_upper_comparison.tex`, `lem:six-query-retention`.

A record (a pattern summand `Π_{𝔱,φ}` of the upper reference, two-layer or folded) **edge-accepts**
`𝓔₆` if every query `(0, j, 0) → (2, rot j, 1)` is read by its emission as an edge of its field
graph (`TwoLayerEdgeAccepts`, `FoldedEdgeAccepts`). This is the test of the paper's enumeration
(`six_query_geometry.py`), and it implies acceptance on the support (`tail_record_accepts`, at one
prime). The enumeration over the `2 · 196` records, by `decide +kernel`:
* every record of formal degree at most one accepts, two-layer and folded
  (`accepts_deg_le_one`);
* of the 37 two-layer records of degree two exactly 9 accept (`count_deg2`,
  `count_accept_deg2`), and of the 37 folded records of total degree three exactly 9 accept
  (`count_accept_folded_deg2`);
* the non-accepting two-layer records of degree two have the state multiplicities
  `LR 6, RL 2, DD 6, DS 4, SD 6, SS 4` (`nonaccepting_deg2_by_state`);
* `G₀₁L`, `G₁₀L` and their folded companions accept (`G01L_G10L_accept`);
* no record of degree at least three accepts (`not_accepts_deg_ge_three`), and there are 64
  two-layer records of degree three (`count_deg3`).

The paper's "does not accept" is the failure of this test: such a record charges labellings
that violate the query condition, which for the full-support graph laws holds at large `p`
(not formalized). Whether the seven accepting degree-two records are those of the twelve-query
ledger is not checked here.
-/

namespace Sarkozy.PartV

open Finset Sarkozy.Labellings

/-- **Edge acceptance of a two-layer upper record**: every query `(0, j, 0) → (2, rot j, 1)` of
`𝓔₆` is read, under the emission of the record, as an edge of its field graph. -/
def TwoLayerEdgeAccepts (t : PType × PType) (φ : t.1.Pat × t.2.Pat) : Prop :=
  ∀ j : ZMod 6, twoLayerEdge (Λ := Fin 2) t.1.field.rel t.2.field.rel
    (t.1.pat φ.1 0, t.2.pat φ.2 j, 0) (t.1.pat φ.1 2, t.2.pat φ.2 (rot j), 1) = true

/-- **Edge acceptance of a folded (one-layer) upper record**, copied onto both layers. -/
def FoldedEdgeAccepts (t : PType × PType) (φ : t.1.Pat × t.2.Pat) : Prop :=
  ∀ j : ZMod 6, twoLayerEdge (Λ := Fin 1) t.1.field.rel t.2.field.rel
    (t.1.pat φ.1 0, t.2.pat φ.2 j, 0) (t.1.pat φ.1 2, t.2.pat φ.2 (rot j), 0) = true

instance (t : PType × PType) (φ : t.1.Pat × t.2.Pat) : Decidable (TwoLayerEdgeAccepts t φ) := by
  unfold TwoLayerEdgeAccepts; infer_instance

instance (t : PType × PType) (φ : t.1.Pat × t.2.Pat) : Decidable (FoldedEdgeAccepts t φ) := by
  unfold FoldedEdgeAccepts; infer_instance

/-- The degree of a state. -/
def stateDeg (t : PType × PType) : ℕ := t.1.deg + t.2.deg

/-- The two-layer records of degree `d`. -/
def twoLayerRecords (d : ℕ) : Finset (Σ t : PType × PType, t.1.Pat × t.2.Pat) :=
  univ.filter fun i => stateDeg i.1 = d

theorem count_deg2 : (twoLayerRecords 2).card = 37 := by decide

theorem count_accept_deg2 :
    ((twoLayerRecords 2).filter fun i => TwoLayerEdgeAccepts i.1 i.2).card = 9 := by decide +kernel

theorem count_accept_folded_deg2 :
    ((twoLayerRecords 2).filter fun i => FoldedEdgeAccepts i.1 i.2).card = 9 := by decide +kernel

/-- Every record of formal degree at most one accepts, two-layer and folded. -/
theorem accepts_deg_le_one :
    ∀ i : Σ t : PType × PType, t.1.Pat × t.2.Pat, stateDeg i.1 ≤ 1 →
      TwoLayerEdgeAccepts i.1 i.2 ∧ FoldedEdgeAccepts i.1 i.2 := by decide +kernel

/-- No record of degree at least three accepts, two-layer or folded. -/
theorem not_accepts_deg_ge_three :
    ∀ i : Σ t : PType × PType, t.1.Pat × t.2.Pat, 3 ≤ stateDeg i.1 →
      ¬ TwoLayerEdgeAccepts i.1 i.2 ∧ ¬ FoldedEdgeAccepts i.1 i.2 := by decide +kernel

theorem count_deg3 : (twoLayerRecords 3).card = 64 := by decide

/-- The non-accepting two-layer records of degree two, by state:
`LR 6, RL 2, DD 6, DS 4, SD 6, SS 4`. -/
theorem nonaccepting_deg2_by_state :
    ((twoLayerRecords 2).filter fun i => ¬ TwoLayerEdgeAccepts i.1 i.2 ∧ i.1 = (.L, .R)).card = 6 ∧
    ((twoLayerRecords 2).filter fun i => ¬ TwoLayerEdgeAccepts i.1 i.2 ∧ i.1 = (.R, .L)).card = 2 ∧
    ((twoLayerRecords 2).filter fun i => ¬ TwoLayerEdgeAccepts i.1 i.2 ∧ i.1 = (.D, .D)).card = 6 ∧
    ((twoLayerRecords 2).filter fun i => ¬ TwoLayerEdgeAccepts i.1 i.2 ∧ i.1 = (.D, .S)).card = 4 ∧
    ((twoLayerRecords 2).filter fun i => ¬ TwoLayerEdgeAccepts i.1 i.2 ∧ i.1 = (.S, .D)).card = 6 ∧
    ((twoLayerRecords 2).filter fun i => ¬ TwoLayerEdgeAccepts i.1 i.2 ∧ i.1 = (.S, .S)).card =
      4 := by
  decide +kernel

/-- The two EL records `G₀₁L`, `G₁₀L` of state `RL` accept, with their folded companions. -/
theorem G01L_G10L_accept :
    TwoLayerEdgeAccepts (.R, .L) ((0, 1), ()) ∧ TwoLayerEdgeAccepts (.R, .L) ((1, 0), ()) ∧
      FoldedEdgeAccepts (.R, .L) ((0, 1), ()) ∧ FoldedEdgeAccepts (.R, .L) ((1, 0), ()) := by
  decide +kernel

/-- **Edge acceptance implies acceptance on the support** (at one prime, for the field laws of the
tail law): every labelling charged by an edge-accepting two-layer record has nonzero square
query differences. -/
theorem tail_record_accepts (p : ℕ) [Fact p.Prime] (hne : TailNonempty p) (t : PType × PType)
    (φ : t.1.Pat × t.2.Pat) (hacc : TwoLayerEdgeAccepts t φ) {z : Slot → ZMod p}
    (hz : (upComponent (tailFieldLaws p hne) (true, ⟨t, φ⟩)).weight z ≠ 0) (j : Chamber) :
    quadraticChar (ZMod p) (z (queryTarget j) - z (querySource j)) = 1 := by
  change (emit (graphLaw (fieldGraph t.1.field t.2.field (Fin 2)) (hne.two _ _))
    (upEmission (t.1.pat φ.1) (t.2.pat φ.2))).weight z ≠ 0 at hz
  obtain ⟨y, hy, rfl⟩ := emit_support _ _ hz
  have hfeas := graphLaw_support _ _ hy
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

end Sarkozy.PartV
