module

public import Sarkozy.UpperRepair.NewGraphBlock
public import Sarkozy.UpperRepair.OldKernel
public import Sarkozy.UpperComparison.Sanity

@[expose] public section

/-!
# Non-vacuity of `ReplRecord` at the actual block laws

`ReplRecord` (`Replacement.lean`) asks for a two-layer law with both half marginals `μ^old`, living
where `λ_H` is, accepting `𝓔₆` at every prime of the block, with bounds on its change. These are
the conventions of B2's `UpperAtomInputs` (acceptance read through the emission `e_φ` at the six
query pairs, uniform one-slot marginals), so a mismatch between them (as on 1 November, when a
field asked query pairs to be uniform on `𝔽_p × 𝔽_p`) would make the structure empty. Here:

* **`keptRepl`**: for a record that accepts (`TwoLayerEdgeAccepts`), the old law itself is a
  `ReplRecord` with `C^s = C^a = 0`, at the actual block laws of every upper block, with no
  hypothesis. So all the fields can hold together, with the acceptance convention of
  `UpperAtomInputs`;
* `rootRepl`: the instance at V1's root record `(LL, φ)`, which is kept (`root_kept`);
  `rootRepl_uniform`: its emitted law has uniform one-slot marginals (`new_uniform`);
* **`keptKernel`**: for an accepting record, the old kernel `recK` (W8's form of
  `pairDensity π^old λ_H`) is a `KernelInput` with `C^s = C^a = 0`: its marginals are `1 + u₀`
  with the actual `u₀` (the convention of W8's `hm1`, `hm2`, `hO1`, `hO2`), so `KernelInput` is
  satisfiable as well; `keptKernel_C`;
* for a changed record, `λ_𝔅(G^new)` satisfies the support and acceptance fields
  (`newBlock_layersSupported`, `newBlock_accepts`, `NewGraphBlock.lean`); its marginals are
  corrected by the one-way repair (`OneWayInput.toRepl`). What `UpperRepairData` still asks is the
  analytic and numerical content: the (F7) data at the block and the constants against the band
  coefficients.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.UpperRepair

open Sarkozy.TheoremC Sarkozy.RecordExpansion Sarkozy.PartV Sarkozy.PartVRecords
  Sarkozy.UpperComparison Sarkozy.Structured

variable {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]

/-- A labelling charged by a law has its image charged by the emitted law. -/
theorem emit_weight_ne_zero {I X : Type*} [Fintype I] [DecidableEq I] [Fintype X] [DecidableEq X]
    (lam : FiniteLaw (I → X)) (π : Slot → I) {y : I → X} (hy : lam.weight y ≠ 0) :
    (emit lam π).weight (y ∘ π) ≠ 0 := by
  change (∑ y', if (fun y => y ∘ π) y' = y ∘ π then lam.weight y' else 0) ≠ 0
  have hpos : 0 < lam.weight y := lt_of_le_of_ne (lam.nonneg y) (Ne.symm hy)
  apply ne_of_gt
  refine Finset.sum_pos' (fun y' _ => ?_) ⟨y, mem_univ _, ?_⟩
  · split_ifs
    · exact lam.nonneg y'
    · exact le_rfl
  · simp only [↓reduceIte]
    exact hpos

/-- **An accepting record is its own replacing law** (`C^s = C^a = 0`), at the actual block laws:
`ReplRecord` is satisfiable with the conventions of `UpperAtomInputs`. -/
noncomputable def keptRepl (hne : UpperNonempty pr) (t : PType × PType) (φ : t.1.Pat × t.2.Pat)
    (hacc : TwoLayerEdgeAccepts t φ) : ReplRecord pr hne t φ where
  lamN := recOld pr hne t
  supp := upper_layersSupported pr hne _ _
  half0 _ := rfl
  half1 g := F7Repair.recOld_symm pr hne t g
  accepts y hy j i :=
    kept_two_layer_accepts pr hne t φ hacc (emit_weight_ne_zero _ (recEm t φ) hy) j i
  Cs := 0
  Ca := 0
  Cs_nonneg := le_rfl
  Ca_nonneg := le_rfl
  sym φ' ψ' := by simp [recChangeForm]
  skew φ' ψ' := by simp [recChangeForm]

/-- V1's root record `(LL, φ)` accepts. -/
theorem root_accepts : TwoLayerEdgeAccepts (PType.L, PType.L) ((), ()) := by
  by_contra h
  have hk := root_kept
  simp only [UpperComparison.rootIdx, upperFate, h, ↓reduceIte] at hk
  split_ifs at hk

/-- The instance at V1's root record, at every upper block. -/
noncomputable def rootRepl (hne : UpperNonempty pr) :
    ReplRecord pr hne (PType.L, PType.L) ((), ()) :=
  keptRepl pr hne _ _ root_accepts

/-- Its emitted law has uniform one-slot marginals. -/
theorem rootRepl_uniform (hne : UpperNonempty pr) : HasUniformMarginals (rootRepl pr hne).new :=
  (rootRepl pr hne).new_uniform

/-- **An accepting record's old kernel is a `KernelInput`** (`C^s = C^a = 0`). -/
noncomputable def keptKernel (hne : UpperNonempty pr) (t : PType × PType) (φ : t.1.Pat × t.2.Pat)
    (hacc : TwoLayerEdgeAccepts t φ) : KernelInput pr hne t φ where
  K := recK pr hne t
  K_nonneg p := by
    unfold recK modK pairDensity pairWeight
    split_ifs
    · exact zero_le_one
    · exact div_nonneg (Finset.sum_nonneg fun y _ => by
        split_ifs
        · exact (recOld pr hne t).nonneg y
        · exact le_rfl) (mul_nonneg ((recHalf pr hne t).nonneg _) ((recHalf pr hne t).nonneg _))
  row x _ := recK_row pr hne t x
  col y _ := recK_col pr hne t y
  accepts x x' hx hx' hK j i := by
    have hK' : pairDensity (recOld pr hne t) (recHalf pr hne t) (x, x') ≠ 0 := by
      have : ¬((recHalf pr hne t).weight x = 0 ∨ (recHalf pr hne t).weight x' = 0) := by
        rintro (h | h)
        · exact hx h
        · exact hx' h
      simpa [recK, modK, this] using hK
    have hW : pairWeight (recOld pr hne t) (x, x') ≠ 0 := by
      intro h0
      apply hK'
      unfold pairDensity
      rw [h0, zero_div]
    unfold pairWeight at hW
    obtain ⟨y, _, hy⟩ := Finset.exists_ne_zero_of_sum_ne_zero hW
    have hl : layerOf y 0 = x ∧ layerOf y 1 = x' := by
      by_contra hn
      simp only [hn, ↓reduceIte] at hy
      exact hy rfl
    simp only [hl, and_self, ↓reduceIte] at hy
    have h := kept_two_layer_accepts pr hne t φ hacc (emit_weight_ne_zero _ (recEm t φ) hy) j i
    have h1 : recEm t φ (queryTarget j) =
        (t.1.pat φ.1 2, t.2.pat φ.2 (chamberRotation j), 1) := by
      change (t.1.pat φ.1 2, t.2.pat φ.2 (chamberRotation j), layerFin 1) = _
      rw [layerFin_one]
    have h2 : recEm t φ (querySource j) = (t.1.pat φ.1 0, t.2.pat φ.2 j, 0) := by
      change (t.1.pat φ.1 0, t.2.pat φ.2 j, layerFin 0) = _
      rw [layerFin_zero]
    rw [Function.comp_apply, Function.comp_apply, h1, h2] at h
    rw [← hl.1, ← hl.2]
    exact h
  Cs := 0
  Ca := 0
  Cs_nonneg := le_rfl
  Ca_nonneg := le_rfl
  sym φ' ψ' := by simp [recK_centredForm]
  skew φ' ψ' := by simp [recK_centredForm]

/-- Its replacing law has the bounds `0`. -/
theorem keptKernel_C (hne : UpperNonempty pr) (t : PType × PType) (φ : t.1.Pat × t.2.Pat)
    (hacc : TwoLayerEdgeAccepts t φ) :
    (keptKernel pr hne t φ hacc).toRepl.Cs = 0 ∧ (keptKernel pr hne t φ hacc).toRepl.Ca = 0 :=
  ⟨rfl, rfl⟩

end Sarkozy.UpperRepair
