module

public import Sarkozy.FirstStagePaper.Paper
public import Sarkozy.PartV.LocalDomain
public import Mathlib.Tactic.NormNum.Prime

@[expose] public section

/-!
# The paper's block assignment and the first-stage constants (`def:construction`(b))

`paper/sections/20_middle_reference.tex`, `def:record:exact-blocks`;
`paper/sections/25_upper_reference.tex`, `def:record:upper-bands`.

**Sites.** A class-three prime `p ∈ [Q₃, P₄)` lies in exactly one *site*: one of the 33 middle
pieces `[X_i, X_{i+1})` of `def:record:exact-blocks`(a) (below `P₃`) or one of the 310 upper bands
of `def:record:upper-bands`(a) (from `P₃`). `siteOf p` is that site and `siteOf_mem` proves
`siteStart ≤ p < siteStop` (from the tiling of `[Q₃, P₃)` by the pieces and of `[P₃, P₄)` by the
bands, checked by `decide +kernel`).

**Blocks.** Inside a site the paper groups the primes `≡ 3 (mod 4)` into consecutive blocks: the
greedy exact blocks below `X_Ch` (`def:record:exact-blocks`(c), from the 5668 recorded count bins),
the fixed-cardinality cells above `X_Ch` (`def:record:exact-blocks`(d), with the recorded `n_j`),
and the cells of the bands (`def:record:upper-bands`(b), with the recorded `n_j`). This
within-site rule is the parameter `cell : ℕ → ℕ` (the index of the block of `p` inside its site);
the recorded integers it needs (bins, `n_j`) are not entered here. The block of a class-three
coordinate is its label `(siteOf p, cell p)`, and the block type `PaperBlock cell` is the finite set
of the labels that occur. **Every block therefore lies in one site, for every `cell`**, which is
all that the block specification, the Gram gate and the first-stage constants use. The price and
ledger obligations (`hB`, `hL₀`, …) depend on the actual `cell` of the paper.

* `paperBlockOf cell : PaperJ0 → PaperBlock cell`: the block assignment (the square-clique primes
  `p ≡ 1 (4)` are sent to a fixed block; `paperAtomMap` makes them atoms `{p}` of their own, so this
  value is never used);
* `blockSite b`, `blockLeast b` (the least prime `b_𝔅`), `mem_site`, `blockLeast_le`,
  `siteStart_le_blockLeast`;
* **`paperIn cell`**: A1's `FirstStageInputs` with `X` the start of the block's site and `bmin` the
  least prime of the block (`lem:record:middle-prices`: `r = b_𝔅^{-1/2}`).
-/

open Finset

namespace Sarkozy.BlockSpecPaper

open Sarkozy.PartV Sarkozy.CancellationSteps Sarkozy.PartVLaws Sarkozy.FirstStagePaper

/-! ## Sites -/

/-- **A site**: a middle piece (`def:record:exact-blocks`(a)) or an upper band
(`def:record:upper-bands`(a)). -/
abbrev Site : Type := Fin 33 ⊕ Fin 310

/-- The start of a site. -/
def siteStart : Site → ℕ
  | .inl i => pieceStart i
  | .inr k => (bandOf k).1

/-- The end of a site. -/
def siteStop : Site → ℕ
  | .inl i => pieceStop i
  | .inr k => (bandOf k).2

/-- If `e 0 ≤ p < e n`, then `p` lies in one of the intervals `[e i, e (i+1))`, `i < n`. -/
theorem exists_interval (e : ℕ → ℕ) {p : ℕ} (h0 : e 0 ≤ p) :
    ∀ n, p < e n → ∃ i < n, e i ≤ p ∧ p < e (i + 1)
  | 0, h => absurd h0 (not_le.mpr h)
  | n + 1, h => by
      by_cases hn : p < e n
      · obtain ⟨i, hi, h1, h2⟩ := exists_interval e h0 n hn
        exact ⟨i, by omega, h1, h2⟩
      · exact ⟨n, by omega, not_lt.mp hn, h⟩

/-- The piece endpoints `X₁, …, X₃₄` as a function. -/
def pieceE (i : ℕ) : ℕ := pieceEnds.getD i 0

theorem pieceE_zero : pieceE 0 = Q3 := by decide +kernel

theorem pieceE_33 : pieceE 33 = P3 := by decide +kernel

/-- **The pieces tile `[Q₃, P₃)`** (`def:record:exact-blocks`(a)). -/
theorem exists_piece {p : ℕ} (h1 : Q3 ≤ p) (h2 : p < P3) :
    ∃ i : Fin 33, pieceStart i ≤ p ∧ p < pieceStop i := by
  obtain ⟨i, hi, h3, h4⟩ := exists_interval pieceE (pieceE_zero ▸ h1) 33 (pieceE_33 ▸ h2)
  exact ⟨⟨i, hi⟩, h3, h4⟩

/-- The band endpoints as a function: the band starts, then `P₄`. -/
def bandE (i : ℕ) : ℕ := ((upperBands.map Prod.fst) ++ [P4]).getD i 0

theorem bandOf_eq_bandE : ∀ k : Fin 310,
    (bandOf k).1 = bandE k.val ∧ (bandOf k).2 = bandE (k.val + 1) := by
  decide +kernel

theorem bandE_zero : bandE 0 = P3 := by decide +kernel

theorem bandE_310 : bandE 310 = P4 := by decide +kernel

/-- **The bands tile `[P₃, P₄)`** (`def:record:upper-bands`(a)). -/
theorem exists_band {p : ℕ} (h1 : P3 ≤ p) (h2 : p < P4) :
    ∃ k : Fin 310, (bandOf k).1 ≤ p ∧ p < (bandOf k).2 := by
  obtain ⟨i, hi, h3, h4⟩ := exists_interval bandE (bandE_zero ▸ h1) 310 (bandE_310 ▸ h2)
  refine ⟨⟨i, hi⟩, ?_, ?_⟩
  · rw [(bandOf_eq_bandE ⟨i, hi⟩).1]
    exact h3
  · rw [(bandOf_eq_bandE ⟨i, hi⟩).2]
    exact h4

/-- Every band starts at `P₃` or later. -/
theorem P3_le_bandStart : ∀ k : Fin 310, P3 ≤ (bandOf k).1 := by decide +kernel

/-- **The site of a prime** `p ∈ [Q₃, P₄)`: its piece below `P₃`, its band from `P₃` (a junk value
outside `[Q₃, P₄)`). -/
noncomputable def siteOf (p : ℕ) : Site :=
  if h : Q3 ≤ p ∧ p < P3 then .inl (exists_piece h.1 h.2).choose
  else if h' : P3 ≤ p ∧ p < P4 then .inr (exists_band h'.1 h'.2).choose
  else .inl 0

/-- **A prime of `[Q₃, P₄)` lies in its site.** -/
theorem siteOf_mem {p : ℕ} (h1 : Q3 ≤ p) (h2 : p < P4) :
    siteStart (siteOf p) ≤ p ∧ p < siteStop (siteOf p) := by
  unfold siteOf
  split_ifs with h h'
  · exact (exists_piece h.1 h.2).choose_spec
  · exact (exists_band h'.1 h'.2).choose_spec
  · exfalso
    rcases lt_or_ge p P3 with h3 | h3
    · exact h ⟨h1, h3⟩
    · exact h' ⟨h3, h2⟩

/-- Every site starts at `Q₃ > 2²⁴` or later. -/
theorem two_pow_24_le_siteStart : ∀ s : Site, 2 ^ 24 ≤ siteStart s
  | .inl i => le_trans (by norm_num [Q3]) (pieceStart_ge_Q3 i)
  | .inr k => le_trans (by norm_num [P3]) (P3_le_bandStart k)

/-! ## The block assignment -/

/-- The class-three coordinates `p ≡ 3 (mod 4)`, `Q₃ ≤ p < P₄` (`𝒫₃`). -/
def classThreeCoords : Finset PaperJ0 := univ.filter fun j => j.1 % 4 ≠ 1

/-- A fixed class-three coordinate, the prime `19 951 627 ≡ 3 (mod 4)` (the least above `Q₃`). -/
def baseCoord : PaperJ0 :=
  ⟨19951627, mem_filter.mpr ⟨mem_range.mpr ((by norm_num [P3] : 19951627 < P3).trans P3_lt_P4),
    by norm_num,
    Or.inr ⟨by norm_num, by norm_num [Q3]⟩⟩⟩

theorem baseCoord_mem : baseCoord ∈ classThreeCoords :=
  mem_filter.mpr ⟨mem_univ _, by decide⟩

variable (cell : ℕ → ℕ)

/-- **The label of a block** (`def:record:exact-blocks`, `def:record:upper-bands`(b)): the site of
the prime and its block index inside the site (`cell`, the paper's within-site rule). -/
noncomputable def blockLabel (p : ℕ) : Site × ℕ := (siteOf p, cell p)

/-- The labels of the blocks that occur. -/
noncomputable def paperBlocks : Finset (Site × ℕ) :=
  classThreeCoords.image fun j => blockLabel cell j.1

/-- **A block of the paper's partition** of the class-three coordinates: a label that occurs. (A
structure rather than the subtype `↥(paperBlocks cell)`, so that instance synthesis and
unification never unfold the label set, a filter over the primes below `P₄ = 2⁵¹²`.) -/
@[ext] structure PaperBlock where
  /-- The label `(site, index)` of the block. -/
  val : Site × ℕ
  mem : val ∈ paperBlocks cell

instance : DecidableEq (PaperBlock cell) := fun a b =>
  decidable_of_iff (a.val = b.val) ⟨PaperBlock.ext, fun h => h ▸ rfl⟩

/-- The blocks are the labels that occur. -/
def PaperBlock.equiv : PaperBlock cell ≃ {x // x ∈ paperBlocks cell} where
  toFun b := ⟨b.val, b.mem⟩
  invFun x := ⟨x.1, x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

noncomputable instance : Fintype (PaperBlock cell) :=
  Fintype.ofEquiv _ (PaperBlock.equiv cell).symm

/-- **The paper's block assignment** (`def:construction`(b)): a class-three coordinate goes to the
block of its label; a square-clique coordinate (an atom `{p}` of its own under `paperAtomMap`) to a
fixed block. -/
noncomputable def paperBlockOf (j : PaperJ0) : PaperBlock cell :=
  if h : j.1 % 4 = 1 then ⟨blockLabel cell baseCoord.1, mem_image_of_mem _ baseCoord_mem⟩
  else ⟨blockLabel cell j.1, mem_image_of_mem _ (mem_filter.mpr ⟨mem_univ _, h⟩)⟩

variable {cell}

/-- The site of a block. -/
def blockSite (b : PaperBlock cell) : Site := b.1.1

theorem paperBlockOf_val {j : PaperJ0} (h : j.1 % 4 ≠ 1) :
    (paperBlockOf cell j).1 = blockLabel cell j.1 := by
  unfold paperBlockOf
  simp only [h, ↓reduceDIte]

theorem paperAtomMap_class3 {j : PaperJ0} (h : j.1 % 4 ≠ 1) :
    paperAtomMap (paperBlockOf cell) j = .inr (paperBlockOf cell j) := by
  unfold paperAtomMap
  simp only [h, ↓reduceDIte]

/-- A coordinate of a block has the block's label. -/
theorem blockOf_of_coord {b : PaperBlock cell}
    (j : {j : PaperJ0 // paperAtomMap (paperBlockOf cell) j = .inr b}) :
    j.1.1 % 4 ≠ 1 ∧ b.1 = blockLabel cell j.1.1 := by
  have hj : j.1.1 % 4 ≠ 1 := paperAtomMap_inr (paperBlockOf cell) j.2
  have h := j.2
  rw [paperAtomMap_class3 hj] at h
  have hb : paperBlockOf cell j.1 = b := Sum.inr_injective h
  refine ⟨hj, ?_⟩
  calc b.1 = (paperBlockOf cell j.1).1 := by rw [hb]
    _ = blockLabel cell j.1.1 := paperBlockOf_val hj

/-- **Every coordinate of a block lies in the block's site.** -/
theorem mem_site {b : PaperBlock cell}
    (j : {j : PaperJ0 // paperAtomMap (paperBlockOf cell) j = .inr b}) :
    siteStart (blockSite b) ≤ blockPrimes (paperBlockOf cell) b j ∧
      blockPrimes (paperBlockOf cell) b j < siteStop (blockSite b) := by
  obtain ⟨hj, hb⟩ := blockOf_of_coord j
  have hm : blockPrimes (paperBlockOf cell) b j = j.1.1 := paperM0_cls3 hj
  have hge := (blockPrimes_mod_ge b j).2
  rw [hm] at hge ⊢
  have hs : blockSite b = siteOf j.1.1 := by
    unfold blockSite
    rw [hb]
    rfl
  rw [hs]
  exact siteOf_mem hge (paperJ0_lt_P4 j.1)

/-- **Every block has a coordinate.** -/
theorem blockIdx_nonempty (b : PaperBlock cell) :
    Nonempty {j : PaperJ0 // paperAtomMap (paperBlockOf cell) j = .inr b} := by
  obtain ⟨j, hj, hl⟩ := mem_image.mp b.2
  have h3 : j.1 % 4 ≠ 1 := (mem_filter.mp hj).2
  refine ⟨⟨j, ?_⟩⟩
  rw [paperAtomMap_class3 h3]
  congr 1
  exact PaperBlock.ext ((paperBlockOf_val h3).trans hl)

/-! ## The least prime of a block -/

/-- **The least prime `b_𝔅` of a block** (`lem:record:middle-prices`). -/
noncomputable def blockLeast (b : PaperBlock cell) : ℕ :=
  (univ.image (blockPrimes (paperBlockOf cell) b)).min'
    (image_nonempty.mpr (univ_nonempty_iff.mpr (blockIdx_nonempty b)))

theorem blockLeast_le (b : PaperBlock cell)
    (j : {j : PaperJ0 // paperAtomMap (paperBlockOf cell) j = .inr b}) :
    blockLeast b ≤ blockPrimes (paperBlockOf cell) b j :=
  min'_le _ _ (mem_image_of_mem _ (mem_univ j))

theorem blockLeast_mem (b : PaperBlock cell) :
    ∃ j : {j : PaperJ0 // paperAtomMap (paperBlockOf cell) j = .inr b},
      blockPrimes (paperBlockOf cell) b j = blockLeast b := by
  obtain ⟨j, -, hj⟩ := mem_image.mp (min'_mem (univ.image (blockPrimes (paperBlockOf cell) b))
    (image_nonempty.mpr (univ_nonempty_iff.mpr (blockIdx_nonempty b))))
  exact ⟨j, hj⟩

theorem siteStart_le_blockLeast (b : PaperBlock cell) : siteStart (blockSite b) ≤ blockLeast b := by
  obtain ⟨j, hj⟩ := blockLeast_mem b
  rw [← hj]
  exact (mem_site j).1

theorem two_pow_24_le_blockLeast (b : PaperBlock cell) : 2 ^ 24 ≤ blockLeast b :=
  (two_pow_24_le_siteStart _).trans (siteStart_le_blockLeast b)

/-! ## The first-stage constants -/

variable (cell) in
/-- **A1's `FirstStageInputs` for the paper's partition**: `X` is the start of the block's site
(the piece start `X_i`, or the band start), `bmin` the least prime `b_𝔅` of the block. -/
noncomputable def paperIn : FirstStageInputs (paperBlockOf cell) where
  X b := siteStart (blockSite b)
  bmin b := blockLeast b
  hX b := by exact_mod_cast two_pow_24_le_siteStart _
  hXb b := by exact_mod_cast siteStart_le_blockLeast b
  hbp b j := by exact_mod_cast blockLeast_le b j

end Sarkozy.BlockSpecPaper
