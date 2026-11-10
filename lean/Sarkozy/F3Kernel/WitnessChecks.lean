module

public import Sarkozy.F3Kernel.BitSets
public import Sarkozy.F3Kernel.Rectangle
public import Sarkozy.ExtractionK.KernelBridge

/-!
# The bit-level witness and cover checks imply the paper's conditions

The two accepted vertex lists give an injective witness. Its decided rectangle and cover
conditions follow from the checker's mask tests, interpreted using the carry-free arithmetic
lemmas. These are the `witness` and `cover` fields of `LeafRecordData.Valid`.
-/

@[expose] public section

namespace Sarkozy.F3Kernel

open Finset Sarkozy.Extraction Sarkozy.ExtractionK

def witnessOf {k xs ys V W : ℕ} (hx : vmask k xs 0 = some V)
    (hy : vmask k ys 0 = some W) (i : Fin k) : Fin 36 × Fin 36 :=
  (witnessVertex hx i, witnessVertex hy i)

def rectangleMask (G : Consts) (V W : ℕ) : ℕ := Nat.land (spread V * W) G.EM

def coverMask (G : Consts) (V W cx cy : ℕ) : ℕ :=
  Nat.lor (rectangleMask G V W)
    (Nat.lor (spread cx * FULL64) (cy * LANE0))

theorem rectangleMask_dec (G : Consts) {V W : ℕ} (hV : V < 2 ^ 36) (hW : W < 2 ^ 36) :
    decM (rectangleMask G V W) = (decV V ×ˢ decV W) ∩ decM G.EM := by
  rw [rectangleMask, decM_land, decM_spread_mul hV (hW.trans_le (by norm_num))]

theorem coverMask_dec (G : Consts) (V W cx cy : ℕ) (hx : cx < 2 ^ 36)
    (hy : cy < 2 ^ 36) :
    decM (coverMask G V W cx cy) = decM (rectangleMask G V W) ∪
      ((decV cx ×ˢ univ) ∪ (univ ×ˢ decV cy)) := by
  rw [coverMask, decM_lor, decM_lor, decM_cover_rows hx,
    decM_cover_cols (hy.trans_le (by norm_num))]

theorem witnessOf_fst_mem {k xs ys V W : ℕ} (hx : vmask k xs 0 = some V)
    (hy : vmask k ys 0 = some W) (v : Fin 36) :
    v ∈ decV V ↔ ∃ i, (witnessOf hx hy i).1 = v := by
  rw [mem_decV, vmask_zero_mem hx]
  rfl

theorem witnessOf_snd_mem {k xs ys V W : ℕ} (hx : vmask k xs 0 = some V)
    (hy : vmask k ys 0 = some W) (v : Fin 36) :
    v ∈ decV W ↔ ∃ i, (witnessOf hx hy i).2 = v := by
  rw [mem_decV, vmask_zero_mem hy]
  rfl

/-- The exact witness condition `(W_k)` follows from the list, rectangle, and free-mask checks. -/
theorem isWitness_of_checks (G : Consts) (c : Cyl) {k xs ys V W pat : ℕ}
    (hclass : IsClassDatum (decM G.EM) (decM c.pm, decM c.am))
    (hx : vmask k xs 0 = some V) (hy : vmask k ys 0 = some W)
    (hfree : Nat.land (rectangleMask G V W) (Nat.xor G.EM (Nat.lor c.pm c.am)) = 0)
    (hpat : rectPat (Nat.land (rectangleMask G V W) c.pm) xs ys k (k * k) 0 = some pat) :
    IsWitness (decM G.EM) (decM c.pm) (decM c.am) (witnessOf hx hy) := by
  have hV := vmask_zero_lt hx
  have hW := vmask_zero_lt hy
  refine ⟨?_, witnessVertex_injective hx, witnessVertex_injective hy, ?_⟩
  · intro i
    have hdiag : (i, i) ∈ Components.rectangle k pat := by
      simp only [Components.rectangle, mem_filter, mem_univ, true_or, and_self]
    have hb := (rectPat_rectangle hpat i i).mp hdiag
    rw [← witnessVertex_val hx i, ← witnessVertex_val hy i] at hb
    have hm : witnessOf hx hy i ∈ decM (Nat.land (rectangleMask G V W) c.pm) :=
      (mem_decM _ _).mpr hb
    rw [decM_land] at hm
    exact (mem_inter.mp hm).2
  · intro e he hx' hy'
    have hr : e ∈ decM (rectangleMask G V W) := by
      rw [rectangleMask_dec G hV hW, mem_inter, mem_product,
        witnessOf_fst_mem hx hy, witnessOf_snd_mem hx hy]
      exact ⟨⟨hx', hy'⟩, he⟩
    have hsub : decM (Nat.lor c.pm c.am) ⊆ decM G.EM := by
      rw [decM_lor]
      exact union_subset hclass.1 hclass.2.1
    have hf := disjoint_left.mp (decM_disjoint hfree) hr
    rw [decM_xor hsub, decM_lor] at hf
    have hu : e ∈ decM c.pm ∪ decM c.am := by
      by_contra hn
      exact hf (mem_sdiff.mpr ⟨he, hn⟩)
    exact mem_union.mp hu

/-- The checker's cover test implies `(VC_k)`, including disjointness from the witness. -/
theorem isCover_of_checks (G : Consts) (c : Cyl) {k xs ys V W cx cy : ℕ}
    (hclass : IsClassDatum (decM G.EM) (decM c.pm, decM c.am))
    (hx : vmask k xs 0 = some V) (hy : vmask k ys 0 = some W)
    (hcx : cx < 2 ^ 36) (hcy : cy < 2 ^ 36)
    (hdx : Nat.land cx V = 0) (hdy : Nat.land cy W = 0)
    (hcover : Nat.land (Nat.xor G.EM c.am) (coverMask G V W cx cy) = Nat.xor G.EM c.am) :
    IsCover (decM G.EM) (decM c.pm) (decM c.am) (witnessOf hx hy) (decV cx) (decV cy) := by
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    exact disjoint_left.mp (decV_disjoint hdx) hi
      ((witnessOf_fst_mem hx hy _).mpr ⟨i, rfl⟩)
  · intro i hi
    exact disjoint_left.mp (decV_disjoint hdy) hi
      ((witnessOf_snd_mem hx hy _).mpr ⟨i, rfl⟩)
  · intro e he hn
    have hna : e ∈ decM G.EM \ decM c.am := by
      rcases mem_union.mp he with hp | hf
      · exact mem_sdiff.mpr ⟨hclass.1 hp, disjoint_left.mp hclass.2.2 hp⟩
      · obtain ⟨he, hfree⟩ := mem_sdiff.mp hf
        exact mem_sdiff.mpr ⟨he, fun ha => hfree (mem_union_right _ ha)⟩
    have hs := decM_subset hcover
    rw [decM_xor hclass.2.1, coverMask_dec G V W cx cy hcx hcy] at hs
    rcases mem_union.mp (hs hna) with hr | hc
    · rw [rectangleMask_dec G (vmask_zero_lt hx) (vmask_zero_lt hy)] at hr
      obtain ⟨⟨hV, hW⟩, _⟩ := (mem_inter.mp hr).imp_left mem_product.mp
      exact False.elim (hn ⟨(witnessOf_fst_mem hx hy _).mp hV,
        (witnessOf_snd_mem hx hy _).mp hW⟩)
    · simpa only [mem_union, mem_product, mem_univ, and_true, true_and] using hc

/-- The restored presence pattern is the mathematical witness-index set of the tested rectangle. -/
theorem witnessIdx_of_rectPat {k xs ys V W PR pat : ℕ}
    (hx : vmask k xs 0 = some V) (hy : vmask k ys 0 = some W)
    (hpat : rectPat PR xs ys k (k * k) 0 = some pat) :
    witnessIdx (decM PR) (witnessOf hx hy) = Components.rectangle k pat := by
  ext ⟨i, j⟩
  rw [mem_witnessIdx, mem_decM, rectPat_rectangle hpat]
  simp only [witnessOf, witnessVertex_val]

/-- Intersecting with the witness rectangle does not change its witness-index set. -/
theorem witnessIdx_rectangleMask (G : Consts) (P : ℕ) {k xs ys V W : ℕ}
    (hx : vmask k xs 0 = some V) (hy : vmask k ys 0 = some W)
    (hP : decM P ⊆ decM G.EM) :
    witnessIdx (decM (Nat.land (rectangleMask G V W) P)) (witnessOf hx hy) =
      witnessIdx (decM P) (witnessOf hx hy) := by
  ext ⟨i, j⟩
  rw [mem_witnessIdx, mem_witnessIdx, decM_land, mem_inter]
  refine and_iff_right_of_imp ?_
  intro hp
  rw [rectangleMask_dec G (vmask_zero_lt hx) (vmask_zero_lt hy), mem_inter, mem_product,
    witnessOf_fst_mem hx hy, witnessOf_snd_mem hx hy]
  exact ⟨⟨⟨i, rfl⟩, ⟨j, rfl⟩⟩, hP hp⟩

end Sarkozy.F3Kernel
