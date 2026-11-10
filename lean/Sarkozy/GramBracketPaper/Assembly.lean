module

public import Sarkozy.FirstStagePaper.Assembly
public import Sarkozy.PartVRecords.Frame
public import Sarkozy.Reflection.Coordinates

@[expose] public section

/-!
# (CP3) from per-atom data (`def:cp3`)

`paper/sections/09_comparison_theorem.tex`, `def:cp3`. The Gram bracket of Theorem C is a family of
per-atom data over the first stage (`def:cp2`); its total `U₀` is a sum over the atoms. On the block
atoms `BlockAtom Bk J L = Bk ⊕ J L`, with the first stage of A1's `firstStageOfAtoms` (one
`AtomStage` per prefix atom, the trivial data at the tail atoms), the bracket is assembled here from
one `AtomGram` per prefix atom; at the tail atoms it is `Ñ = μ`, which needs only `μ ⪰_ι 0`.

* `AtomGram A`: the data of `def:cp3` at one atom whose first-stage data is `A` (an `AtomStage`):
  positive reserved-diagonal records `κu_i`, `Ñ₀` with `Ñ₀ - μ = ∑_i κu_i` (and `Ñ₀ = μ` off the
  first stage), `λ = ρ + δ_E` symmetric at `ι`, `Ñ = Ñ₀ + δ_E` nonnegative, and the bracket
  `(Ñ λ; λ Ñ) ⪰_ι 0`.
* `AtomGram.ofTrivial`: the data at an atom with trivial first stage (`ρ = μ`, no records), from
  `μ ⪰_ι 0` alone: `Ñ₀ = μ`, no records; `λ = μ` is symmetric at `ι` because a measure that is
  positive at a cut is invariant under its reflection (`Positive.reflection_invariant`), and
  `(μ μ; μ μ) ⪰_ι 0` (`Positive.bracket_self`).
* **`gramBracketOfAtoms`**: the structure `TheoremCBlock.GramBracket` over
  `firstStageOfAtoms … A` from one `AtomGram` per prefix atom and `μ_p ⪰_ι 0` at the tail
  atoms, with `U₀ = ∑_β u_β` (scale-independent, as the atoms of a block are).
-/

open Filter Finset Function
open scoped BigOperators

namespace Sarkozy.GramBracketPaper

open Sarkozy.TheoremC Sarkozy.TheoremCBlock Sarkozy.BlockFrame Sarkozy.RecordExpansion
open Sarkozy.FirstStagePaper

/-! ## The data at one atom -/

/-- **The (CP3) data of one atom** (`def:cp3`), relative to its first-stage data `A` (reference
`μ`): positive reserved-diagonal records `κu_i`, the measure `Ñ₀` with `Ñ₀ - μ = ∑_i κu_i` (`Ñ₀ = μ`
off the first stage), the first stage `λ = ρ + ∑_i (κ'_i - κ_i)` symmetric at `ι`, the bracket law
`Ñ = Ñ₀ + ∑_i (κ'_i - κ_i)` nonnegative, and `(Ñ λ; λ Ñ) ⪰_ι 0`. -/
structure AtomGram {X : Type} [Fintype X] [DecidableEq X] {μ : SlotMeasure X} {Tag : Type}
    {cut : Tag → ReflectionCut Slot} {ϑ₀ : ReflectionCut Slot} (A : AtomStage μ Tag cut ϑ₀) where
  Iu : Type
  [IuFintype : Fintype Iu]
  κu : Iu → SlotMeasure X
  /-- Positive records. -/
  κu_pos : ∀ i, IsPositiveRecord (κu i)
  /-- Reserved diagonal. -/
  κu_diag : ∀ i, TheoremC.IsDiagonalAt reservedCut (κu i)
  N₀ : SlotMeasure X
  /-- `Ñ₀ - μ = ∑_i κu_i`. -/
  N₀_sub : N₀ - μ = ∑ i, κu i
  /-- `Ñ₀ = μ` off the first stage. -/
  N₀_off : A.first = false → N₀ = μ
  /-- `λ` is symmetric at `ι`. -/
  lam_sym : IsSymmetricAt reservedCut (A.ρ + ∑ i, (A.κ' i - A.κ i))
  /-- `Ñ` is nonnegative. -/
  N_nonneg : IsNonneg (N₀ + ∑ i, (A.κ' i - A.κ i))
  /-- `(Ñ λ; λ Ñ) ⪰_ι 0`. -/
  bracket : reservedCut.Bracket (N₀ + ∑ i, (A.κ' i - A.κ i)) (A.ρ + ∑ i, (A.κ' i - A.κ i))
    (N₀ + ∑ i, (A.κ' i - A.κ i))

attribute [instance] AtomGram.IuFintype

namespace AtomGram

variable {X : Type} [Fintype X] [DecidableEq X] {μ : SlotMeasure X} {Tag : Type}
  {cut : Tag → ReflectionCut Slot} {ϑ₀ : ReflectionCut Slot} {A : AtomStage μ Tag cut ϑ₀}

/-- The price `u_𝔟 = ∑_i κu_i(1) q_𝔟^{2a}` at the selection factor `sel`. -/
noncomputable def uprice (G : AtomGram A) (sel : ℝ) : ℝ := ∑ i, mass (G.κu i) * sel

theorem uprice_nonneg (G : AtomGram A) {sel : ℝ} (hsel : 0 ≤ sel) : 0 ≤ G.uprice sel :=
  sum_nonneg fun i _ => mul_nonneg (AtomStage.mass_nonneg_of_positive (G.κu_pos i)) hsel

/-- A measure positive at `ι` is symmetric at `ι` (`Positive.reflection_invariant`). -/
theorem isSymmetricAt_of_positive {κ : SlotMeasure X} (h : reservedCut.Positive κ) :
    IsSymmetricAt reservedCut κ :=
  h.reflection_invariant

/-- **The (CP3) data of an atom with trivial first stage** (`def:cp3` off the first-stage atoms):
`Ñ₀ = μ`, no records, from `μ ⪰_ι 0`. -/
noncomputable def ofTrivial (μ : FiniteLaw (Slot → X))
    (hμ : reservedCut.Positive (signedIntegral μ.weight)) :
    AtomGram (AtomStage.trivial (signedIntegral μ.weight) Tag cut ϑ₀) where
  Iu := Empty
  κu := fun i => i.elim
  κu_pos := fun i => i.elim
  κu_diag := fun i => i.elim
  N₀ := signedIntegral μ.weight
  N₀_sub := by simp
  N₀_off := fun _ => rfl
  lam_sym := by
    change IsSymmetricAt reservedCut (signedIntegral μ.weight + ∑ i : Empty, _)
    rw [Finset.univ_eq_empty, sum_empty, add_zero]
    exact isSymmetricAt_of_positive hμ
  N_nonneg := by
    change IsNonneg (signedIntegral μ.weight + ∑ i : Empty, _)
    rw [Finset.univ_eq_empty, sum_empty, add_zero]
    exact PartVRecords.isNonneg_law μ
  bracket := by
    change reservedCut.Bracket (signedIntegral μ.weight + ∑ i : Empty, _)
      (signedIntegral μ.weight + ∑ i : Empty, _) (signedIntegral μ.weight + ∑ i : Empty, _)
    rw [Finset.univ_eq_empty, sum_empty, add_zero]
    exact hμ.bracket_self

theorem ofTrivial_uprice (μ : FiniteLaw (Slot → X))
    (hμ : reservedCut.Positive (signedIntegral μ.weight)) (sel : ℝ) :
    (ofTrivial (Tag := Tag) (cut := cut) (ϑ₀ := ϑ₀) μ hμ).uprice sel = 0 := by
  exact Finset.sum_eq_zero fun i _ => Empty.elim i

end AtomGram

/-! ## The assembly -/

variable {a : ℝ}
variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] (m₀ : J₀ → ℕ) [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] (blk : J₀ → Bk)
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] (p : ∀ L, J L → ℕ)
  [∀ L j, NeZero (p L j)]

section Tail

variable {selPre : Bk → ℝ} {R : Reference m₀ blk} {Tag : Type} [Fintype Tag] [DecidableEq Tag]
  {cut : Tag → ReflectionCut Slot} {hcut : ∀ j, IsFamilyCut (cut j)} {ϑ₀ : ReflectionCut Slot}
  {hϑ₀ : IsFamilyCut ϑ₀} {A : ∀ β, AtomStage (signedIntegral (R.μ₀ β).weight) Tag cut ϑ₀}

omit [∀ L, DecidableEq (J L)] in
/-- At a tail atom the first stage has no differences. -/
theorem fsOfAtoms_delta_inr (L : ℕ) (j : J L) :
    ∑ i, ((firstStageOfAtoms a m₀ blk p selPre R Tag cut hcut ϑ₀ hϑ₀ A).κ' L (.inr j) i -
      (firstStageOfAtoms a m₀ blk p selPre R Tag cut hcut ϑ₀ hϑ₀ A).κ L (.inr j) i) = 0 :=
  Finset.sum_eq_zero fun i _ => Empty.elim i

omit [∀ L, DecidableEq (J L)] in
/-- At a tail atom the first stage is the reference: `λ_p = μ_p`. -/
theorem fsOfAtoms_lam_inr (L : ℕ) (j : J L) :
    (firstStageOfAtoms a m₀ blk p selPre R Tag cut hcut ϑ₀ hϑ₀ A).lam L (.inr j) =
      R.law p L (.inr j) := by
  unfold TheoremCBlock.FirstStage.lam
  rw [fsOfAtoms_delta_inr, add_zero]
  rfl

omit [∀ L, DecidableEq (J L)] in
/-- At a prefix atom the first stage is `ρ + δ_E` of its `AtomStage`. -/
theorem fsOfAtoms_lam_inl (L : ℕ) (β : Bk) :
    (firstStageOfAtoms a m₀ blk p selPre R Tag cut hcut ϑ₀ hϑ₀ A).lam L (.inl β) =
      (A β).ρ + ∑ i, ((A β).κ' i - (A β).κ i) := rfl

omit [∀ L, DecidableEq (J L)] in
theorem fsOfAtoms_first_of_not_mem {L : ℕ} {β : Bk}
    (hb : (.inl β : BlockAtom Bk J L) ∉
      (firstStageOfAtoms a m₀ blk p selPre R Tag cut hcut ϑ₀ hϑ₀ A).fs L) :
    (A β).first = false := by
  have hb' : (Sum.inl β : BlockAtom Bk J L) ∉ univ.filter (fun b : BlockAtom Bk J L =>
      Sum.elim (fun β => (A β).first) (fun _ => false) b) := hb
  simpa using hb'

end Tail

variable (a) in
/-- **(CP3) from per-atom data** (`def:cp3`), over the first stage `firstStageOfAtoms … A` of A1. At
the prefix atoms the data are the `AtomGram`s `G β`; at the tail atoms `Ñ₀ = μ_p` with no records,
which needs `μ_p ⪰_ι 0` (`htail`). The total is `U₀ = ∑_β u_β` over the prefix atoms. -/
noncomputable def gramBracketOfAtoms (selPre : Bk → ℝ) (R : Reference m₀ blk) (Tag : Type)
    [Fintype Tag] [DecidableEq Tag] (cut : Tag → ReflectionCut Slot)
    (hcut : ∀ j, IsFamilyCut (cut j)) (ϑ₀ : ReflectionCut Slot) (hϑ₀ : IsFamilyCut ϑ₀)
    (A : ∀ β, AtomStage (signedIntegral (R.μ₀ β).weight) Tag cut ϑ₀)
    (G : ∀ β, AtomGram (A β))
    (htail : ∀ L (j : J L), reservedCut.Positive (R.law p L (.inr j))) :
    GramBracket a m₀ blk p selPre
      (firstStageOfAtoms a m₀ blk p selPre R Tag cut hcut ϑ₀ hϑ₀ A) where
  Iu L b := match b with
    | .inl β => (G β).Iu
    | .inr _ => Empty
  IuFintype L b := match b with
    | .inl β => (G β).IuFintype
    | .inr _ => inferInstanceAs (Fintype Empty)
  κu L b := match b with
    | .inl β => (G β).κu
    | .inr _ => fun i => i.elim
  κu_pos L b := match b with
    | .inl β => (G β).κu_pos
    | .inr _ => fun i => i.elim
  κu_diag L b := match b with
    | .inl β => (G β).κu_diag
    | .inr _ => fun i => i.elim
  N₀ L b := match b with
    | .inl β => (G β).N₀
    | .inr j => R.law p L (.inr j)
  N₀_sub L b := match b with
    | .inl β => (G β).N₀_sub
    | .inr _ => by simp
  N₀_off L b hb := match b with
    | .inl β => (G β).N₀_off (fsOfAtoms_first_of_not_mem m₀ blk p hb)
    | .inr _ => rfl
  lam_sym L b := match b with
    | .inl β => (G β).lam_sym
    | .inr j => by
        rw [fsOfAtoms_lam_inr]
        exact AtomGram.isSymmetricAt_of_positive (htail L j)
  N_nonneg L b := match b with
    | .inl β => (G β).N_nonneg
    | .inr j => by
        rw [fsOfAtoms_delta_inr, add_zero]
        exact PartVRecords.isNonneg_law (R.μp (p L j))
  bracket L b := match b with
    | .inl β => (G β).bracket
    | .inr j => by
        rw [fsOfAtoms_delta_inr, add_zero, fsOfAtoms_lam_inr]
        exact (htail L j).bracket_self
  U₀ := ∑ β, (G β).uprice (selPre β)
  U₀_total L := by
    rw [Fintype.sum_sum_type]
    simp only [Finset.univ_eq_empty, sum_empty, sum_const_zero, add_zero]
    rfl

section Totals

variable {selPre : Bk → ℝ} {R : Reference m₀ blk} {Tag : Type} [Fintype Tag] [DecidableEq Tag]
  {cut : Tag → ReflectionCut Slot} {hcut : ∀ j, IsFamilyCut (cut j)} {ϑ₀ : ReflectionCut Slot}
  {hϑ₀ : IsFamilyCut ϑ₀} {A : ∀ β, AtomStage (signedIntegral (R.μ₀ β).weight) Tag cut ϑ₀}
  {G : ∀ β, AtomGram (A β)} {htail : ∀ L (j : J L), reservedCut.Positive (R.law p L (.inr j))}

omit [∀ L, DecidableEq (J L)] in
/-- The total `U₀` of the assembled bracket is the sum of the prices of the prefix atoms. -/
theorem gramBracketOfAtoms_U₀ :
    (gramBracketOfAtoms a m₀ blk p selPre R Tag cut hcut ϑ₀ hϑ₀ A G htail).U₀ =
      ∑ β, (G β).uprice (selPre β) := rfl

omit [∀ L, DecidableEq (J L)] in
/-- The bracket law of a prefix atom is `Ñ₀ + δ_E` of its `AtomGram`. -/
theorem gramBracketOfAtoms_N₀ (L : ℕ) (β : Bk) :
    (gramBracketOfAtoms a m₀ blk p selPre R Tag cut hcut ϑ₀ hϑ₀ A G htail).N₀ L (.inl β) =
      (G β).N₀ := rfl

end Totals

end Sarkozy.GramBracketPaper
