module

public import Sarkozy.TailCorr.Core
public import Sarkozy.Cuts.CutKernel

@[expose] public section

/-!
# The two coordinates of the tail datum have the same row data

`paper/sections/25_upper_reference.tex`, `def:record:upper-bands`(e) and
`subsec:upper-reference-rp`: the inputs of the tail datum are recorded per field type, the same
for the coordinates `0` and `1`; `paper/sections/27_tail_index.tex`, `lem:tail-law`(i).

The graph `G_{φ₀φ₁,ℓ}` has the edge relation `twoLayerEdge`, which is symmetric in the two
coordinates: `(a, b, λ) → (a', b', λ')` is an edge of `G_{φ₀φ₁}` iff `(b, a, λ) → (b', a', λ')` is
an edge of `G_{φ₁φ₀}` (`twoLayerEdge_swap`). So the coordinate swap carries `Inj_p(G_{φ₀φ₁})` onto
`Inj_p(G_{φ₁φ₀})` (`mem_inj_swap`) and the graph law of `G_{φ₁φ₀}` is the image of that of
`G_{φ₀φ₁}` (`graphLaw_swap`). The rows of the coordinate `0` of `λ_{𝔱𝔣'}` are therefore the rows of
the coordinate `1` of `λ_{𝔣'𝔱}`, as laws (`rows_swap_one`, `rows_swap_two`), and

* **`rowD1_eq_rowD0_one`**, **`rowD1_eq_rowD0_two`**: V2's row datum of the coordinate `1` at
  `𝔣'` *is* the row datum of the coordinate `0` at `𝔣'`, for the one-layer and the two-layer
  tail laws at every prime.

Consequently the coordinate-`1` fields of HC's `TailSpectralCore` (`root21`, `root11`, `fold21`,
`fold11`, `match21`, `match11`) are the coordinate-`0` fields: **`TailSpectralCore0`** keeps only
the latter and the layer caps, and `tailSpectralCore_of_core0` recovers `TailSpectralCore`;
**`tailInputsCorr_of_core0`** is the plug-in for `hC`.

New material for this paper.
-/

namespace Sarkozy.TailCorrCore

open Finset Sarkozy.Labellings Sarkozy.FiveType Sarkozy.PartV Sarkozy.FiveType.TwoCoord
  Sarkozy.PartVLaws

/-! ## The coordinate swap -/

section Swap

variable {A B Λ : Type*}

/-- The coordinate swap `(b, a, λ) ↦ (a, b, λ)`. -/
def swap3 (w : B × A × Λ) : A × B × Λ := (w.2.1, w.1, w.2.2)

/-- **The edge relation of `G_{φ₀φ₁}` is symmetric in the two coordinates.** -/
lemma twoLayerEdge_swap (c₀ : FieldType A) (c₁ : FieldType B) (u v : B × A × Λ) :
    twoLayerEdge c₁ c₀ u v = twoLayerEdge c₀ c₁ (swap3 u) (swap3 v) := by
  simp only [twoLayerEdge, swap3]
  generalize c₀.rel u.2.1 v.2.1 = a
  generalize c₁.rel u.1 v.1 = b
  generalize c₀.fwd u.2.1 v.2.1 = c
  generalize c₁.fwd u.1 v.1 = d
  revert a b c d
  decide

end Swap

section Laws

variable {p : ℕ} [Fact p.Prime]

lemma mem_fieldGraph (f₀ f₁ : FType) (Λ : Type) [Fintype Λ]
    (e : (f₀.Obj × f₁.Obj × Λ) × (f₀.Obj × f₁.Obj × Λ)) :
    e ∈ (fieldGraph f₀ f₁ Λ).E ↔ twoLayerEdge f₀.rel f₁.rel e.1 e.2 = true := by
  unfold fieldGraph
  exact mem_twoLayerGraph _ _ _ _ e

/-- **The swap carries `Inj_p(G_{φ₀φ₁})` onto `Inj_p(G_{φ₁φ₀})`.** -/
theorem mem_inj_swap (f₀ f₁ : FType) (Λ : Type) [Fintype Λ] [DecidableEq Λ]
    (y : f₀.Obj × f₁.Obj × Λ → ZMod p) :
    (fun w => y (swap3 w)) ∈ injLabellings (ZMod p) (fieldGraph f₁ f₀ Λ) ↔
      y ∈ injLabellings (ZMod p) (fieldGraph f₀ f₁ Λ) := by
  rw [mem_injLabellings_iff_feasible, mem_injLabellings_iff_feasible]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨fun a _ b _ hab => ?_, fun e he _ _ => ?_⟩
    · have := h1 (swap3 a) (mem_univ _) (swap3 b) (mem_univ _) hab
      exact congrArg swap3 this
    · have he' : (swap3 e.1, swap3 e.2) ∈ (fieldGraph f₁ f₀ Λ).E := by
        rw [mem_fieldGraph, twoLayerEdge_swap]
        exact (mem_fieldGraph f₀ f₁ Λ e).mp he
      exact h2 _ he' (mem_univ _) (mem_univ _)
  · rintro ⟨h1, h2⟩
    refine ⟨fun a _ b _ hab => ?_, fun e he _ _ => ?_⟩
    · have := h1 (swap3 a) (mem_univ _) (swap3 b) (mem_univ _) hab
      exact congrArg swap3 this
    · have he' : (swap3 e.1, swap3 e.2) ∈ (fieldGraph f₀ f₁ Λ).E := by
        rw [mem_fieldGraph, ← twoLayerEdge_swap]
        exact (mem_fieldGraph f₁ f₀ Λ e).mp he
      exact h2 _ he' (mem_univ _) (mem_univ _)

/-- **The graph law of `G_{φ₁φ₀}` is the image of that of `G_{φ₀φ₁}` under the swap.** -/
theorem graphLaw_swap (f₀ f₁ : FType) (Λ : Type) [Fintype Λ] [DecidableEq Λ]
    (h01 : (injLabellings (ZMod p) (fieldGraph f₀ f₁ Λ)).Nonempty)
    (h10 : (injLabellings (ZMod p) (fieldGraph f₁ f₀ Λ)).Nonempty)
    (Φ : (f₁.Obj × f₀.Obj × Λ → ZMod p) → ℝ) :
    (graphLaw (fieldGraph f₁ f₀ Λ) h10).expect Φ =
      (graphLaw (fieldGraph f₀ f₁ Λ) h01).expect (fun y => Φ (fun w => y (swap3 w))) := by
  rw [Cuts.SpecData.graphLaw_expect', Cuts.SpecData.graphLaw_expect']
  have hsum : ∑ z ∈ injLabellings (ZMod p) (fieldGraph f₁ f₀ Λ), Φ z =
      ∑ y ∈ injLabellings (ZMod p) (fieldGraph f₀ f₁ Λ), Φ (fun w => y (swap3 w)) := by
    refine (sum_nbij' (fun z => fun w => z (swap3 w)) (fun y => fun w => y (swap3 w)) ?_ ?_
      ?_ ?_ ?_).symm
    · intro y hy
      exact (mem_inj_swap f₀ f₁ Λ y).mpr hy
    · intro z hz
      exact (mem_inj_swap f₁ f₀ Λ z).mpr hz
    · intro y _; rfl
    · intro z _; rfl
    · intro y _; rfl
  have hcard : (injLabellings (ZMod p) (fieldGraph f₁ f₀ Λ)).card =
      (injLabellings (ZMod p) (fieldGraph f₀ f₁ Λ)).card := by
    refine (card_nbij' (fun y => fun w => y (swap3 w)) (fun z => fun w => z (swap3 w)) ?_ ?_
      ?_ ?_).symm
    · intro y hy
      exact (mem_inj_swap f₀ f₁ Λ y).mpr (mem_coe.mp hy)
    · intro z hz
      exact (mem_inj_swap f₁ f₀ Λ z).mpr (mem_coe.mp hz)
    · intro y _; rfl
    · intro z _; rfl
  rw [hsum, hcard]

/-- **One-layer rows**: the rows of the coordinate `0` of `λ^{(1)}_{𝔱𝔣'}` are the rows of the
coordinate `1` of `λ^{(1)}_{𝔣'𝔱}`, as laws. -/
theorem rows_swap_one (hne : TailNonempty p) (t f' : FieldTy) :
    ((lam1 (tailFieldLaws p hne) t f').map fun y => (rows0 y : t.Obj → f'.Obj × Unit → ZMod p)) =
      ((lam1 (tailFieldLaws p hne) f' t).map fun y =>
        (rows1 y : t.Obj → f'.Obj × Unit → ZMod p)) := by
  refine law_eq_of_expect fun h => ?_
  simp only [lam1, FiniteLaw.expect_map]
  change (graphLaw (fieldGraph (toFType t) (toFType f') (Fin 1)) (hne.one _ _)).expect _ =
    (graphLaw (fieldGraph (toFType f') (toFType t) (Fin 1)) (hne.one _ _)).expect _
  rw [graphLaw_swap (toFType t) (toFType f') (Fin 1) (hne.one _ _) (hne.one _ _)]
  rfl

/-- **Two-layer rows**: the same for `λ_{𝔱𝔣'}`. -/
theorem rows_swap_two (hne : TailNonempty p) (t f' : FieldTy) :
    ((lam2 (tailFieldLaws p hne) t f').map fun y =>
        (rows0 y : t.Obj → f'.Obj × ZMod 2 → ZMod p)) =
      ((lam2 (tailFieldLaws p hne) f' t).map fun y =>
        (rows1 y : t.Obj → f'.Obj × ZMod 2 → ZMod p)) := by
  refine law_eq_of_expect fun h => ?_
  simp only [lam2, FiniteLaw.expect_map]
  change (graphLaw (fieldGraph (toFType t) (toFType f') (Fin 2)) (hne.two _ _)).expect _ =
    (graphLaw (fieldGraph (toFType f') (toFType t) (Fin 2)) (hne.two _ _)).expect _
  rw [graphLaw_swap (toFType t) (toFType f') (Fin 2) (hne.two _ _) (hne.two _ _)]
  rfl

end Laws

end Sarkozy.TailCorrCore
