module

public import Sarkozy.MiddleComparison.Atom
public import Sarkozy.PartVRecords.OneStageBlock
public import Sarkozy.UpperComparison.Acceptance

@[expose] public section

/-!
# The frame facts on the paper's middle blocks (`subsec:middle-comparison`)

`paper/sections/21_middle_records.tex`, `subsec:middle-comparison`: "the retained records of
`ν_𝔅` are the two-layer root and `F₀`, the folded root and the folded `F₀`, the record `E_new` of
the first stage, and the replacements; each accepts the six queries: the root and `F₀` contain the
edge `0 → 2` of the first coordinate in both layers, and so do their diagonal copies (on the pieces
from `2³⁰` the root is the positive root …, which has the support of the uniform root …);
`E_new` by `lem:record:one-stage-folded-e`".

For V3's frame of a middle block (`middleFrame`: V1's block field laws with a root, and
`κnew = blockPlusLaw`), with acceptance "`y_p - x_p` is a nonzero square at every prime of the
block" (`blockSquareAccepted`) and the six queries `MainAnchor.paperQueries`:

* `emit_edge_accepts`: a law supported on the injective strict-square labellings of a graph `G`,
  emitted so that every query reads an edge of `G`, accepts every query at every prime;
* `RootSupported root`: the root is supported where the uniform root is (at every prime, the
  injective strict-square labellings of `G_{L,2}`); **proved** for the uniform root
  (`uniformRoot_supported`), the individual-square positive root (`individualRoot_supported`,
  `lem:positive-root-properties`(a)) and the coherent root (`coherentRoot_supported`);
* **`middleFrame_facts`**: `FrameFacts` of the frame for any supported root with uniform vertex
  marginals: the uniform marginals of the field laws and of `κnew`, and the acceptance of the
  four kept records (the query edges `(0,ℓ) → (2,ℓ')` of `G_{L}` and of `F₀` in `G_F`, by
  `decide`) and of `E_new` (V3's `newRec_accepts`).
-/

open Finset
open scoped BigOperators

namespace Sarkozy.MiddleComparison

open Sarkozy.TheoremC Sarkozy.PartV Sarkozy.PartVRecords Sarkozy.RecordExpansion
open Sarkozy.ComparisonLawPaper Sarkozy.UpperComparison Sarkozy.Labellings

variable {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]

/-- **Acceptance through an emission reading edges**: if a law `lam` of labellings of the vertices
of `G` is supported, at every prime, on the injective strict-square labellings of `G`, and the
emission `π` reads every query as an edge of `G`, then every labelling charged by the emitted law
has `χ_p(z_{target} - z_{source}) = 1` at every prime. -/
theorem emit_edge_accepts {W : Type} [Fintype W] [DecidableEq W] (G : OrientedGraph W)
    (lam : FiniteLaw (W → BlockLabel pr))
    (hsupp : ∀ y, lam.weight y ≠ 0 → ∀ i, (fun w => y w i) ∈ injLabellings (ZMod (pr i)) G)
    (π : Slot → W) (hπ : ∀ j : Chamber, (π (querySource j), π (queryTarget j)) ∈ G.E)
    {z : Slot → BlockLabel pr} (hz : (emit lam π).weight z ≠ 0) (j : Chamber) (i : ι) :
    quadraticChar (ZMod (pr i)) (z (queryTarget j) i - z (querySource j) i) = 1 := by
  obtain ⟨y, hy, rfl⟩ := emit_support _ _ hz
  have hfeas := hsupp y hy i
  rw [mem_injLabellings_iff_feasible] at hfeas
  exact hfeas.2 _ (hπ j) (mem_univ _) (mem_univ _)

/-- The block graph laws are supported on the injective strict-square labellings. -/
theorem blockGraphLaw_supported {W : Type} [Fintype W] [DecidableEq W] (G : OrientedGraph W)
    (hne : ∀ i, (injLabellings (ZMod (pr i)) G).Nonempty) :
    ∀ y, (blockGraphLaw pr G hne).weight y ≠ 0 → ∀ i,
      (fun w => y w i) ∈ injLabellings (ZMod (pr i)) G :=
  fun _ hy i => blockGraphLaw_support pr G hne hy i

/-- **A root supported where the uniform root is**: at every prime of the block, the injective
strict-square labellings of the twelve-label root `G_{L,2}`. -/
def RootSupported (root : FiniteLaw (ZMod 6 × Fin 2 → BlockLabel pr)) : Prop :=
  ∀ y, root.weight y ≠ 0 → ∀ i, (fun w => y w i) ∈ injLabellings (ZMod (pr i)) (recordGraph (Fin 2))

theorem uniformRoot_supported (hne : MiddleNonempty pr) : RootSupported pr (uniformRoot pr hne) :=
  fun _ hy i => blockGraphLaw_support pr _ hne.L2 hy i

/-- **The individual-square positive root has the support of the uniform root**
(`lem:positive-root-properties`(a), prime by prime). -/
theorem individualRoot_supported (u : ℚ)
    (hne : ∀ i, (injLabellings (ZMod (pr i)) (recordGraph (Fin 2))).Nonempty) :
    RootSupported pr (individualBlockRoot pr u hne) := by
  intro y hy i
  unfold individualBlockRoot at hy
  rw [tensor_weight, Finset.prod_ne_zero_iff] at hy
  have h1 := hy i (mem_univ i)
  rw [individualRoot_support] at h1
  exact (graphLaw_weight_ne_zero _ _ _).mp h1

/-- The coherent root has the support of the uniform root. -/
theorem coherentRoot_supported (D : Dictionary) (u : ℚ) {η : ℚ} (hη : 0 < η)
    (hne : ∀ i, (injLabellings (ZMod (pr i)) (recordGraph (Fin 2))).Nonempty) :
    RootSupported pr (coherentBlockRoot pr D u hη hne) := by
  intro y hy i
  unfold coherentBlockRoot at hy
  rw [tensor_weight, Finset.prod_ne_zero_iff] at hy
  have h1 := hy i (mem_univ i)
  rw [coherentRoot_support] at h1
  exact (graphLaw_weight_ne_zero _ _ _).mp h1

/-! ## The query edges of the kept records -/

theorem root_query_edge (j : Chamber) :
    (midEmission (fun u : ZMod 6 => u) (querySource j),
      midEmission (fun u : ZMod 6 => u) (queryTarget j)) ∈
      (recordGraph (Fin 2)).E := by
  rw [mem_recordGraph]
  revert j
  decide

theorem rootDiag_query_edge (j : Chamber) :
    (midDiagEmission (fun u : ZMod 6 => u) (querySource j),
      midDiagEmission (fun u : ZMod 6 => u) (queryTarget j)) ∈ (recordGraph (Fin 1)).E := by
  rw [mem_recordGraph]
  revert j
  decide

theorem fold0_query_edge (j : Chamber) :
    (midEmission (fold 0) (querySource j),
      midEmission (fold 0) (queryTarget j)) ∈ (foldGraph (Fin 2)).E := by
  rw [mem_foldGraph]
  revert j
  decide

theorem fold0Diag_query_edge (j : Chamber) :
    (midDiagEmission (fold 0) (querySource j),
      midDiagEmission (fold 0) (queryTarget j)) ∈ (foldGraph (Fin 1)).E := by
  rw [mem_foldGraph]
  revert j
  decide

/-! ## The facts -/

omit [Fintype ι] [DecidableEq ι] in
/-- `quadraticChar = 1` at every prime gives `blockSquareAccepted`. -/
theorem blockSquareAccepted_of {x y : BlockLabel pr}
    (h : ∀ i, quadraticChar (ZMod (pr i)) (y i - x i) = 1) : blockSquareAccepted pr x y :=
  fun i => (quadraticChar_eq_one_iff _).mp (h i)

variable (hne : MiddleNonempty pr) (root : FiniteLaw (ZMod 6 × Fin 2 → BlockLabel pr))
  (W : MiddleWeights) (I : MiddleInputs) {r : ℝ} (hr : 0 ≤ r) (b : ℝ) (h : ClassThreeBlock pr)

/-- **The frame facts of a middle block** (`subsec:middle-comparison`): for a root supported where
the uniform root is, with uniform vertex marginals. -/
theorem middleFrame_facts (hsupp : RootSupported pr root)
    (hunif : ∀ (o : ZMod 6 × Fin 2) (g : BlockLabel pr → ℝ),
      root.expect (fun y => g (y o)) = (FiniteLaw.uniform (BlockLabel pr)).expect g) :
    FrameFacts (middleFrame pr hne root W I hr b h) (blockSquareAccepted pr)
      MainAnchor.paperQueries where
  two_unif f o g := by
    cases f
    · exact hunif o g
    · exact blockGraphLaw_vertex_uniform pr _ hne.F2 o g
    · exact blockGraphLaw_vertex_uniform pr _ hne.E2 o g
  one_unif f o g := middleFrame_one_uniform pr hne root W I hr b h f o g
  new_unif o g := blockPlusLaw_vertex_uniform pr h o g
  kept_accept k z hz e := by
    rw [paperQueries_source_eq, paperQueries_target_eq]
    refine blockSquareAccepted_of pr fun i => ?_
    fin_cases k
    · exact emit_edge_accepts pr _ root hsupp _ root_query_edge hz e i
    · exact emit_edge_accepts pr _ _ (blockGraphLaw_supported pr _ hne.L1) _ rootDiag_query_edge
        hz e i
    · exact emit_edge_accepts pr _ _ (blockGraphLaw_supported pr _ hne.F2) _ fold0_query_edge
        hz e i
    · exact emit_edge_accepts pr _ _ (blockGraphLaw_supported pr _ hne.F1) _ fold0Diag_query_edge
        hz e i
  new_accept s z hz e := by
    rw [paperQueries_source_eq, paperQueries_target_eq]
    exact blockSquareAccepted_of pr fun i => newRec_accepts pr h s hz e i

end Sarkozy.MiddleComparison
