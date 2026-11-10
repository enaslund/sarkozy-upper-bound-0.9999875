module

public import Sarkozy.SpectralD.RootOneFast.Count
public import Sarkozy.SpectralD.RootOneGeometry
public import Sarkozy.SpectralD.RootOneData

/-!
# Fast kernel checks for LL22's class-one tables

The cross neighbourhoods and the adjacency of `LL22.cut.Half` are tabulated on the codes
`slotCode / 2` (`LL22_nbrCodes`, `LL22_adjMasks`) by small checks over the half
(`LL22_nbr_codes`, `LL22_nbr_onto`, `LL22_nbr_nodup`, `LL22_adj_masks`). The lemmas of
`RootOneFast.Count` turn `(N k ∩ N l).card` and `coverCount` into computations on these codes
(`LL22_card_common`, `LL22_coverCount_common`), and the table entries are checked on codes
(`LL22_gram_codes`, `LL22_cover_codes`). The data are generated, but they are checked here
and not trusted.
-/

@[expose] public section

namespace Sarkozy.SpectralD.Root

open Finset

/-- The cross neighbour codes of each code of `LL22.cut.Half`, in increasing order. -/
def LL22_nbrCodes : List (List ℕ) :=
  [
    [8, 10, 13, 14, 17, 25, 28, 29, 32, 34],
    [9, 11, 12, 14, 17, 24, 26, 27, 33, 35],
    [6, 10, 13, 15, 16, 24, 25, 27, 30, 34],
    [7, 11, 13, 14, 16, 26, 28, 29, 31, 35],
    [6, 8, 12, 15, 17, 26, 27, 29, 30, 32],
    [7, 9, 12, 15, 16, 24, 25, 28, 31, 33],
    [2, 4, 14, 16, 19, 22, 23, 31, 32, 35],
    [3, 5, 15, 17, 18, 20, 21, 30, 32, 35],
    [0, 4, 12, 16, 18, 19, 21, 31, 33, 34],
    [1, 5, 13, 17, 20, 22, 23, 31, 32, 34],
    [0, 2, 12, 14, 20, 21, 23, 30, 33, 35],
    [1, 3, 13, 15, 18, 19, 22, 30, 33, 34],
    [1, 4, 5, 8, 10, 20, 22, 25, 26, 29],
    [0, 2, 3, 9, 11, 21, 23, 24, 26, 29],
    [0, 1, 3, 6, 10, 18, 22, 25, 27, 28],
    [2, 4, 5, 7, 11, 19, 23, 25, 26, 28],
    [2, 3, 5, 6, 8, 18, 20, 24, 27, 29],
    [0, 1, 4, 7, 9, 19, 21, 24, 27, 28],
    [7, 8, 11, 14, 16, 26, 28, 31, 34, 35],
    [6, 8, 11, 15, 17, 27, 29, 30, 32, 33],
    [7, 9, 10, 12, 16, 24, 28, 30, 31, 33],
    [7, 8, 10, 13, 17, 25, 29, 32, 34, 35],
    [6, 9, 11, 12, 14, 24, 26, 32, 33, 35],
    [6, 9, 10, 13, 15, 25, 27, 30, 31, 34],
    [1, 2, 5, 13, 16, 17, 20, 22, 32, 34],
    [0, 2, 5, 12, 14, 15, 21, 23, 33, 35],
    [1, 3, 4, 12, 13, 15, 18, 22, 30, 34],
    [1, 2, 4, 14, 16, 17, 19, 23, 31, 35],
    [0, 3, 5, 14, 15, 17, 18, 20, 30, 32],
    [0, 3, 4, 12, 13, 16, 19, 21, 31, 33],
    [2, 4, 7, 10, 11, 19, 20, 23, 26, 28],
    [3, 5, 6, 8, 9, 18, 20, 23, 27, 29],
    [0, 4, 6, 7, 9, 19, 21, 22, 24, 28],
    [1, 5, 8, 10, 11, 19, 20, 22, 25, 29],
    [0, 2, 8, 9, 11, 18, 21, 23, 24, 26],
    [1, 3, 6, 7, 10, 18, 21, 22, 25, 27]
  ]

/-- The neighbours in `G⁺` of each code of `LL22.cut.Half`, as bit masks of codes. -/
def LL22_adjMasks : List ℕ :=
  [
    22313854208, 43167930880, 18438267968, 37379729536,
    6107074880, 11056288384, 40815378452, 39732019240,
    27920240657, 23636090914, 44034969605, 26848567306,
    642778418, 631245325, 440665163, 378013876,
    689176940, 422052499, 54022719872, 14629898560,
    12096444032, 56405140864, 47328549440, 20568909376,
    21480284198, 42960212005, 18258112538, 36516347926,
    5370200105, 10740117529, 345509012, 680788840,
    292029137, 576195874, 94636805, 174326986
  ]

/-- The cross neighbour codes of the code `x`. -/
def LL22_nbr (x : ℕ) : List ℕ := codeTable LL22_nbrCodes x

/-- The mask of the neighbours in `G⁺` of the code `x`. -/
def LL22_adj (x : ℕ) : ℕ := maskTable LL22_adjMasks x

/-- The common cross neighbour codes of the codes `x` and `y`. -/
def LL22_common (x y : ℕ) : List ℕ := commonR (LL22_nbr x) (LL22_nbr y)

theorem LL22_code_injective : Function.Injective (fun k : LL22.cut.Half => slotCode k.1 / 2) := by
  have h : ∀ a b : LL22.cut.Half, slotCode a.1 / 2 = slotCode b.1 / 2 → a = b := by
    decide +kernel
  exact fun a b => h a b

theorem LL22_nbr_codes : ∀ k j : LL22.cut.Half,
    (sgnB LL22.cut.flip j.1 k.1 ≠ 0 ↔
      memR (slotCode j.1 / 2) (LL22_nbr (slotCode k.1 / 2)) = true) := by
  decide +kernel

theorem LL22_nbr_onto : ∀ k : LL22.cut.Half, ∀ x ∈ LL22_nbr (slotCode k.1 / 2),
    ∃ j : LL22.cut.Half, slotCode j.1 / 2 = x := by
  decide +kernel

theorem LL22_nbr_nodup : ∀ k : LL22.cut.Half, (LL22_nbr (slotCode k.1 / 2)).Nodup := by
  decide +kernel

theorem LL22_adj_masks : ∀ i j : LL22.cut.Half,
    (i ≠ j ∧ halfAdjB i j ↔
      (LL22_adj (slotCode i.1 / 2) >>> (slotCode j.1 / 2)) % 2 = 1) := by
  decide +kernel

theorem LL22_mem_neighboursB (k j : LL22.cut.Half) :
    j ∈ neighboursB LL22.cut k ↔ (slotCode j.1 / 2) ∈ LL22_nbr (slotCode k.1 / 2) := by
  rw [← memR_iff, ← LL22_nbr_codes k j]
  simp only [neighboursB, mem_filter, mem_univ, true_and]

theorem LL22_card_common (k l : LL22.cut.Half) :
    (neighboursB LL22.cut k ∩ neighboursB LL22.cut l).card =
      (LL22_common (slotCode k.1 / 2) (slotCode l.1 / 2)).length :=
  card_inter_eq_commonR _ _ _ LL22_code_injective LL22_mem_neighboursB LL22_nbr_onto
    LL22_nbr_nodup k l

theorem LL22_coverCount_common (k l : LL22.cut.Half) :
    coverCount (neighboursB LL22.cut) halfAdjB k l =
      coverMaskCount LL22_adj (LL22_common (slotCode k.1 / 2) (slotCode l.1 / 2)) 0 0 :=
  coverCount_eq_coverMaskCount _ _ _ LL22_code_injective LL22_mem_neighboursB LL22_nbr_onto
    LL22_nbr_nodup _ _ LL22_adj_masks k l

theorem LL22_gram_codes : ∀ x, x < 36 → ∀ y, y < 36 →
    (2 : ℤ) ^ (LL22_common x y).length - 1 = oneEntry LL22_HOneTable x y := by
  decide +kernel

theorem LL22_cover_codes : ∀ x, x < 36 → ∀ y, y < 36 →
    (coverMaskCount LL22_adj (LL22_common x y) 0 0 : ℤ) =
      oneEntry LL22_HplusOneTable x y - oneEntry LL22_HOneTable x y := by
  decide +kernel

end Sarkozy.SpectralD.Root
