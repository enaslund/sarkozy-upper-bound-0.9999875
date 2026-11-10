module

public import Sarkozy.SpectralD.RootOneFast.Count
public import Sarkozy.SpectralD.RootOneGeometry
public import Sarkozy.SpectralD.RootOneData

/-!
# Fast kernel checks for LL20's class-one tables

The cross neighbourhoods and the adjacency of `LL20.cut.Half` are tabulated on the codes
`slotCode` (`LL20_nbrCodes`, `LL20_adjMasks`) by small checks over the half
(`LL20_nbr_codes`, `LL20_nbr_onto`, `LL20_nbr_nodup`, `LL20_adj_masks`). The lemmas of
`RootOneFast.Count` turn `(N k ∩ N l).card` and `coverCount` into computations on these codes
(`LL20_card_common`, `LL20_coverCount_common`), and the table entries are checked on codes
(`LL20_gram_codes`, `LL20_cover_codes`). The data are generated, but they are checked here
and not trusted.
-/

@[expose] public section

namespace Sarkozy.SpectralD.Root

open Finset

/-- The cross neighbour codes of each code of `LL20.cut.Half`, in increasing order. -/
def LL20_nbrCodes : List (List ℕ) :=
  [
    [4, 5, 8, 9, 14, 15, 20, 21, 22, 23],
    [4, 5, 8, 9, 14, 15, 20, 21, 22, 23],
    [6, 7, 10, 11, 12, 13, 16, 17, 18, 19],
    [6, 7, 10, 11, 12, 13, 16, 17, 18, 19],
    [0, 1, 8, 9, 12, 13, 14, 15, 18, 19],
    [0, 1, 8, 9, 12, 13, 14, 15, 18, 19],
    [2, 3, 10, 11, 16, 17, 20, 21, 22, 23],
    [2, 3, 10, 11, 16, 17, 20, 21, 22, 23],
    [0, 1, 4, 5, 16, 17, 18, 19, 22, 23],
    [0, 1, 4, 5, 16, 17, 18, 19, 22, 23],
    [2, 3, 6, 7, 12, 13, 14, 15, 20, 21],
    [2, 3, 6, 7, 12, 13, 14, 15, 20, 21],
    [2, 3, 4, 5, 10, 11, 26, 27, 32, 33, 34, 35],
    [2, 3, 4, 5, 10, 11, 26, 27, 32, 33, 34, 35],
    [0, 1, 4, 5, 10, 11, 24, 25, 28, 29, 30, 31],
    [0, 1, 4, 5, 10, 11, 24, 25, 28, 29, 30, 31],
    [2, 3, 6, 7, 8, 9, 24, 25, 26, 27, 30, 31],
    [2, 3, 6, 7, 8, 9, 24, 25, 26, 27, 30, 31],
    [2, 3, 4, 5, 8, 9, 28, 29, 32, 33, 34, 35],
    [2, 3, 4, 5, 8, 9, 28, 29, 32, 33, 34, 35],
    [0, 1, 6, 7, 10, 11, 28, 29, 30, 31, 34, 35],
    [0, 1, 6, 7, 10, 11, 28, 29, 30, 31, 34, 35],
    [0, 1, 6, 7, 8, 9, 24, 25, 26, 27, 32, 33],
    [0, 1, 6, 7, 8, 9, 24, 25, 26, 27, 32, 33],
    [14, 15, 16, 17, 22, 23, 28, 29, 32, 33],
    [14, 15, 16, 17, 22, 23, 28, 29, 32, 33],
    [12, 13, 16, 17, 22, 23, 30, 31, 34, 35],
    [12, 13, 16, 17, 22, 23, 30, 31, 34, 35],
    [14, 15, 18, 19, 20, 21, 24, 25, 32, 33],
    [14, 15, 18, 19, 20, 21, 24, 25, 32, 33],
    [14, 15, 16, 17, 20, 21, 26, 27, 34, 35],
    [14, 15, 16, 17, 20, 21, 26, 27, 34, 35],
    [12, 13, 18, 19, 22, 23, 24, 25, 28, 29],
    [12, 13, 18, 19, 22, 23, 24, 25, 28, 29],
    [12, 13, 18, 19, 20, 21, 26, 27, 30, 31],
    [12, 13, 18, 19, 20, 21, 26, 27, 30, 31]
  ]

/-- The neighbours in `G⁺` of each code of `LL20.cut.Half`, as bit masks of codes. -/
def LL20_adjMasks : List ℕ :=
  [
    52549582848, 52549582848, 52408614912, 52408614912,
    16310611968, 16310611968, 13904166912, 13904166912,
    54811373568, 54811373568, 16157294592, 16157294592,
    13690209072, 13690209072, 54760836288, 54760836288,
    12935234307, 12935234307, 51740937228, 51740937228,
    855638067, 855638067, 3422552268, 3422552268,
    3346188, 3346188, 13369587, 13369587,
    3158223, 3158223, 12635952, 12635952,
    212208, 212208, 836367, 836367
  ]

/-- The cross neighbour codes of the code `x`. -/
def LL20_nbr (x : ℕ) : List ℕ := codeTable LL20_nbrCodes x

/-- The mask of the neighbours in `G⁺` of the code `x`. -/
def LL20_adj (x : ℕ) : ℕ := maskTable LL20_adjMasks x

/-- The common cross neighbour codes of the codes `x` and `y`. -/
def LL20_common (x y : ℕ) : List ℕ := commonR (LL20_nbr x) (LL20_nbr y)

theorem LL20_code_injective : Function.Injective (fun k : LL20.cut.Half => slotCode k.1) :=
  slotCode_injective.comp Subtype.val_injective

theorem LL20_nbr_codes : ∀ k j : LL20.cut.Half,
    (sgnB LL20.cut.flip j.1 k.1 ≠ 0 ↔
      memR (slotCode j.1) (LL20_nbr (slotCode k.1)) = true) := by
  decide +kernel

theorem LL20_nbr_onto : ∀ k : LL20.cut.Half, ∀ x ∈ LL20_nbr (slotCode k.1),
    ∃ j : LL20.cut.Half, slotCode j.1 = x := by
  decide +kernel

theorem LL20_nbr_nodup : ∀ k : LL20.cut.Half, (LL20_nbr (slotCode k.1)).Nodup := by
  decide +kernel

theorem LL20_adj_masks : ∀ i j : LL20.cut.Half,
    (i ≠ j ∧ halfAdjB i j ↔
      (LL20_adj (slotCode i.1) >>> (slotCode j.1)) % 2 = 1) := by
  decide +kernel

theorem LL20_mem_neighboursB (k j : LL20.cut.Half) :
    j ∈ neighboursB LL20.cut k ↔ (slotCode j.1) ∈ LL20_nbr (slotCode k.1) := by
  rw [← memR_iff, ← LL20_nbr_codes k j]
  simp only [neighboursB, mem_filter, mem_univ, true_and]

theorem LL20_card_common (k l : LL20.cut.Half) :
    (neighboursB LL20.cut k ∩ neighboursB LL20.cut l).card =
      (LL20_common (slotCode k.1) (slotCode l.1)).length :=
  card_inter_eq_commonR _ _ _ LL20_code_injective LL20_mem_neighboursB LL20_nbr_onto
    LL20_nbr_nodup k l

theorem LL20_coverCount_common (k l : LL20.cut.Half) :
    coverCount (neighboursB LL20.cut) halfAdjB k l =
      coverMaskCount LL20_adj (LL20_common (slotCode k.1) (slotCode l.1)) 0 0 :=
  coverCount_eq_coverMaskCount _ _ _ LL20_code_injective LL20_mem_neighboursB LL20_nbr_onto
    LL20_nbr_nodup _ _ LL20_adj_masks k l

theorem LL20_gram_codes : ∀ x, x < 36 → ∀ y, y < 36 →
    (2 : ℤ) ^ (LL20_common x y).length - 1 = oneEntry LL20_HOneTable x y := by
  decide +kernel

theorem LL20_cover_codes : ∀ x, x < 36 → ∀ y, y < 36 →
    (coverMaskCount LL20_adj (LL20_common x y) 0 0 : ℤ) =
      oneEntry LL20_HplusOneTable x y - oneEntry LL20_HOneTable x y := by
  decide +kernel

end Sarkozy.SpectralD.Root
