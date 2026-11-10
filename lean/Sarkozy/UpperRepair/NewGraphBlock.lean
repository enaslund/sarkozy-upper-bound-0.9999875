module

public import Sarkozy.UpperRepair.OneWay
public import Sarkozy.F7Repair.NewGraph

@[expose] public section

/-!
# The repaired graph `G^new` at an upper block (`prop:record:upper`(i), "The repair")

`paper/sections/26_upper_comparison.tex`, paragraph "The repair": "The new graph `G^new` keeps the
two induced halves, drops the old cross edges and imposes the projected queries;
`π^new = λ_p(G^new)`."
FR's `newGraph` (`Sarkozy/F7Repair/NewGraph.lean`) proves this at one prime. At an upper block the
law is the block law `λ_𝔅(G^new) = ⊗_p λ_p(G^new)` (V1's `blockGraphLaw`). Here, at every block:

* **`newBlock_layersSupported`**: both layers of `λ_𝔅(G^new)` lie where the half law `λ_H` of the
  record is (each layer of a labelling of `G^new` is a labelling of `H` at every prime);
* **`newBlock_accepts`**: `λ_𝔅(G^new)` accepts `𝓔₆` at every prime of the block, when the cross
  edges `Q` contain the projected `𝓔₆` queries (`queryPairs`; the paper's twelve, `twelvePairs`,
  contain them, FR's `queryPairs_subset_twelve`);
* `newBlockLaw`; `OneWayGraphInput pr hne t φ`: the (F7) inputs with `π^new = λ_𝔅(G^new)`: the
  cross edges `Q`, the nonemptiness of `Inj_p(G^new)` at every prime of the block, and FR's
  `F7Record` with new law `λ_𝔅(G^new)`; `OneWayGraphInput.ofData` builds it from the one-way data
  of `λ_𝔅(G^new)` with targets `μ^old` and `ρ_old` alone; **`OneWayGraphInput.toOneWay`**,
  `toRepl`.

So for a one-way record the support and the acceptance are proved; what is left is analytic: `U`,
`ρ_new`, `K_∞`, the gate (the `OneWayData`) and `ρ_old`, at the block.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.UpperRepair

open Sarkozy.TheoremC Sarkozy.RecordExpansion Sarkozy.PartV Sarkozy.PartVRecords
  Sarkozy.UpperComparison Sarkozy.Structured Sarkozy.Recentering Sarkozy.F7Repair
  Sarkozy.Labellings

variable {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]

/-- **Both layers of `λ_𝔅(G^new)` lie where `λ_H` is** (the new graph keeps the old halves). -/
theorem newBlock_layersSupported (hne : UpperNonempty pr) (t : PType × PType)
    (Q : Finset ((t.1.field.Obj × t.2.field.Obj) × (t.1.field.Obj × t.2.field.Obj)))
    (hN : ∀ i, (injLabellings (ZMod (pr i)) (newGraph t.1.field t.2.field Q)).Nonempty) :
    LayersSupported (blockGraphLaw pr (newGraph t.1.field t.2.field Q) hN) (recHalf pr hne t) := by
  intro y hy
  have hfeas : ∀ i, (fun w => y w i) ∈
      injLabellings (ZMod (pr i)) (newGraph t.1.field t.2.field Q) :=
    fun i => blockGraphLaw_support pr _ _ hy i
  have key : ∀ k : Fin 2, (recHalf pr hne t).weight (layerOf y k) ≠ 0 := by
    intro k
    set y' : t.1.field.Obj × t.2.field.Obj × Fin 1 → BlockLabel pr := fun o => y (o.1, o.2.1, k)
      with hy'
    have hw : (blockGraphLaw pr (fieldGraph t.1.field t.2.field (Fin 1))
        (hne.one t.1.field t.2.field)).weight y' ≠ 0 :=
      blockGraphLaw_weight_ne_zero_of pr _ _ fun i =>
        newLayer_feasible t.1.field t.2.field Q k _ (hfeas i)
    have hpos : 0 < (blockGraphLaw pr (fieldGraph t.1.field t.2.field (Fin 1))
        (hne.one t.1.field t.2.field)).weight y' :=
      lt_of_le_of_ne ((blockGraphLaw pr _ (hne.one t.1.field t.2.field)).nonneg y') (Ne.symm hw)
    have hmap : (fun o : t.1.field.Obj × t.2.field.Obj => y' (o.1, o.2, 0)) = layerOf y k := rfl
    change (∑ y'', if (fun o : t.1.field.Obj × t.2.field.Obj => y'' (o.1, o.2, 0)) = layerOf y k
      then (blockGraphLaw pr (fieldGraph t.1.field t.2.field (Fin 1))
        (hne.one t.1.field t.2.field)).weight y'' else 0) ≠ 0
    apply ne_of_gt
    refine Finset.sum_pos' (fun y'' _ => ?_) ⟨y', mem_univ _, ?_⟩
    · split_ifs
      · exact (blockGraphLaw pr _ (hne.one t.1.field t.2.field)).nonneg y''
      · exact le_rfl
    · simp only [hmap, ↓reduceIte]
      exact hpos
  exact ⟨key 0, key 1⟩

/-- **`λ_𝔅(G^new)` accepts `𝓔₆` at every prime of the block** when `Q` contains the projected
`𝓔₆` queries. -/
theorem newBlock_accepts (t : PType × PType) (φ : t.1.Pat × t.2.Pat)
    (Q : Finset ((t.1.field.Obj × t.2.field.Obj) × (t.1.field.Obj × t.2.field.Obj)))
    (hQ : ∀ j : Chamber,
      ((t.1.pat φ.1 0, t.2.pat φ.2 j), (t.1.pat φ.1 2, t.2.pat φ.2 (chamberRotation j))) ∈ Q)
    (hN : ∀ i, (injLabellings (ZMod (pr i)) (newGraph t.1.field t.2.field Q)).Nonempty)
    (y : t.1.field.Obj × t.2.field.Obj × Fin 2 → BlockLabel pr)
    (hy : (blockGraphLaw pr (newGraph t.1.field t.2.field Q) hN).weight y ≠ 0) (j : Chamber)
    (i : ι) :
    quadraticChar (ZMod (pr i))
      (y (recEm t φ (queryTarget j)) i - y (recEm t φ (querySource j)) i) = 1 := by
  have hfeas := (mem_injLabellings_iff_feasible _ _).mp (blockGraphLaw_support pr _ _ hy i)
  have hedge : crossEdge ((t.1.pat φ.1 0, t.2.pat φ.2 j),
      (t.1.pat φ.1 2, t.2.pat φ.2 (chamberRotation j))) ∈ (newGraph t.1.field t.2.field Q).E :=
    (mem_newEdges t.1.field t.2.field Q _).mpr (Or.inr ⟨_, hQ j, rfl⟩)
  exact hfeas.2 _ hedge (mem_univ _) (mem_univ _)

/-- The block law `λ_𝔅(G^new)` of the repaired graph. -/
noncomputable def newBlockLaw (t : PType × PType)
    (Q : Finset ((t.1.field.Obj × t.2.field.Obj) × (t.1.field.Obj × t.2.field.Obj)))
    (hN : ∀ i, (injLabellings (ZMod (pr i)) (newGraph t.1.field t.2.field Q)).Nonempty) :
    FiniteLaw (t.1.field.Obj × t.2.field.Obj × Fin 2 → BlockLabel pr) :=
  blockGraphLaw pr (newGraph t.1.field t.2.field Q) hN

/-- **The (F7) inputs of a one-way repaired upper record with `π^new = λ_𝔅(G^new)`**
(`it:record:upper-F7`, "The repair"). *Hypotheses*: the cross edges `Q` (containing the projected
`𝓔₆` queries), `Inj_p(G^new) ≠ ∅` at every prime of the block, and FR's `F7Record` whose new law is
`λ_𝔅(G^new)` (`hlam`): the one-way data with targets `μ^old` (`U`, `ρ_new`, `K_∞`, the gate
`2F < 1`: (F1), (F2) and the density bounds of the proof of (F7)), and `ρ_old` ((F6) with
`lem:recentering`(b), or (F2) for `G`). The support field of the record is
`newBlock_layersSupported` (`OneWayGraphInput.ofData` builds the record from the analytic data
alone). -/
structure OneWayGraphInput (hne : UpperNonempty pr) (t : PType × PType)
    (φ : t.1.Pat × t.2.Pat) where
  /-- The imposed cross pairs. -/
  Q : Finset ((t.1.field.Obj × t.2.field.Obj) × (t.1.field.Obj × t.2.field.Obj))
  /-- `Q` contains the projected `𝓔₆` queries. -/
  hQ : ∀ j : Chamber,
    ((t.1.pat φ.1 0, t.2.pat φ.2 j), (t.1.pat φ.1 2, t.2.pat φ.2 (chamberRotation j))) ∈ Q
  /-- `Inj_p(G^new) ≠ ∅` at every prime of the block. -/
  hN : ∀ i, (injLabellings (ZMod (pr i)) (newGraph t.1.field t.2.field Q)).Nonempty
  /-- The (F7) record. -/
  R : F7Record (recOld pr hne t) (recHalf pr hne t)
  /-- Its new law is `λ_𝔅(G^new)`. -/
  hlam : R.lamN = newBlockLaw pr t Q hN

namespace OneWayGraphInput

variable {pr} {hne : UpperNonempty pr} {t : PType × PType} {φ : t.1.Pat × t.2.Pat}

/-- **The input from the analytic data alone**: the support of `λ_𝔅(G^new)` is
`newBlock_layersSupported`. -/
noncomputable def ofData
    (Q : Finset ((t.1.field.Obj × t.2.field.Obj) × (t.1.field.Obj × t.2.field.Obj)))
    (hQ : ∀ j : Chamber,
      ((t.1.pat φ.1 0, t.2.pat φ.2 j), (t.1.pat φ.1 2, t.2.pat φ.2 (chamberRotation j))) ∈ Q)
    (hN : ∀ i, (injLabellings (ZMod (pr i)) (newGraph t.1.field t.2.field Q)).Nonempty)
    (D : OneWayData (pairLaw (newBlockLaw pr t Q hN) lay0 lay1) (oldHalf (recOld pr hne t))
      (oldHalf (recOld pr hne t)))
    (ρold : ℝ) (hρ : 0 ≤ ρold)
    (old_corr : ∀ h k, (oldHalf (recOld pr hne t)).expect h = 0 →
      (oldHalf (recOld pr hne t)).expect k = 0 →
      |(recOld pr hne t).expect (fun y => h (lay0 y) * k (lay1 y))| ≤
        ρold * nrm (oldHalf (recOld pr hne t)) h * nrm (oldHalf (recOld pr hne t)) k) :
    OneWayGraphInput pr hne t φ where
  Q := Q
  hQ := hQ
  hN := hN
  R := ⟨newBlockLaw pr t Q hN, newBlock_layersSupported pr hne t Q hN, D, ρold, hρ, old_corr⟩
  hlam := rfl

/-- The `OneWayInput`: the acceptance is `newBlock_accepts`. -/
noncomputable def toOneWay (I : OneWayGraphInput pr hne t φ) : OneWayInput pr hne t φ where
  R := I.R
  accepts y hy j i := by
    rw [I.hlam] at hy
    exact newBlock_accepts pr t φ I.Q I.hQ I.hN y hy j i

/-- **The replacing law of the record**: `π^rep` of `λ_𝔅(G^new)`, `C^s = ρ_old + ρ'`, `C^a = ρ'`. -/
noncomputable def toRepl (I : OneWayGraphInput pr hne t φ) : ReplRecord pr hne t φ :=
  I.toOneWay.toRepl

theorem toRepl_Cs (I : OneWayGraphInput pr hne t φ) : I.toRepl.Cs = I.R.ρold + I.R.D.ρ' := rfl

theorem toRepl_Ca (I : OneWayGraphInput pr hne t φ) : I.toRepl.Ca = I.R.D.ρ' := rfl

end OneWayGraphInput

end Sarkozy.UpperRepair
