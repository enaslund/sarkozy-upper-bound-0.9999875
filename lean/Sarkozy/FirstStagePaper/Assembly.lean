module

public import Sarkozy.TheoremCBlock.Data

@[expose] public section

/-!
# (CP2) from per-atom data (`def:cp2`)

`paper/sections/09_comparison_theorem.tex`, `def:cp2`. The first stage of Theorem C is a family of
per-atom data; its totals `P`, `d_j`, `v_j` are sums over the atoms. On the block atoms
`BlockAtom Bk J L = Bk ⊕ J L` the first-stage atoms are prefix atoms (in the paper: the middle
blocks), and the atoms of a block do not depend on the scale; so the totals are sums over the prefix
atoms, the same at every scale.

* `AtomStage μ Tag cut ϑ₀`: the data of `def:cp2` at one atom with reference `μ`: a flag `first`
  (the atom is a first-stage atom), `ρ` with `ρ - μ = ∑ c_i κ_i` (positive records `κ_i`),
  `ρ ⪰_{ϑ₀} μ` on a first-stage atom and `ρ = μ` off them, and the tagged differences `κ'_i - κ_i`
  (positive records of equal mass), each with a sharp bound `d_i` at the cut of its tag
  (`def:price`(b)); none off the first-stage atoms.
* `AtomStage.trivial μ`: the data of an atom that is not a first-stage atom (`ρ = μ`, no records).
* `AtomStage.pvar`, `AtomStage.dTag`, `AtomStage.vTag`: the atom's variation price
  `p_𝔟 = ∑_i |c_i| κ_i(1) q^{2a}`, and its sharp and variation prices of tag `j`.
* **`firstStageOfAtoms`**: the structure `TheoremCBlock.FirstStage` from one `AtomStage` per prefix
  atom (the tail atoms carry the trivial data), with the totals `P = ∑_β p_β`,
  `d_j = ∑_β d_{β,j}`, `v_j = ∑_β v_{β,j}`; every field of `def:cp2` is checked here
  (`firstStageOfAtoms_P`, `_dT`, `_vT`, `_fs`, `_ρ` record the definitions).
-/

open Filter Finset Function
open scoped BigOperators

namespace Sarkozy.FirstStagePaper

open Sarkozy.TheoremC Sarkozy.TheoremCBlock Sarkozy.BlockFrame Sarkozy.RecordExpansion

/-! ## The data at one atom -/

/-- **The first-stage data of one atom** (`def:cp2`), relative to the atom's reference `μ`, for a
set of tags `Tag` with cuts `cut` and the polarization cut `ϑ₀`. -/
structure AtomStage {X : Type} [Fintype X] [DecidableEq X] (μ : SlotMeasure X) (Tag : Type)
    (cut : Tag → ReflectionCut Slot) (ϑ₀ : ReflectionCut Slot) where
  /-- The atom is a first-stage atom. -/
  first : Bool
  ρ : SlotMeasure X
  Ia : Type
  [IaFintype : Fintype Ia]
  ca : Ia → ℝ
  κa : Ia → SlotMeasure X
  /-- (CP2)(a): positive records. -/
  κa_pos : ∀ i, IsPositiveRecord (κa i)
  /-- (CP2)(a): `ρ - μ = ∑_i c_i κ_i`. -/
  ρ_sub : ρ - μ = ∑ i, ca i • κa i
  /-- (CP2)(a): `ρ ⪰_{ϑ₀} μ` on a first-stage atom. -/
  ρ_ge : first = true → ϑ₀.Below μ ρ
  /-- `ρ = μ` off the first-stage atoms. -/
  ρ_off : first = false → ρ = μ
  Ib : Type
  [IbFintype : Fintype Ib]
  [IbDecEq : DecidableEq Ib]
  κ : Ib → SlotMeasure X
  κ' : Ib → SlotMeasure X
  /-- (CP2)(b): differences of positive records of equal mass. -/
  κ_pos : ∀ i, IsPositiveRecord (κ i)
  κ'_pos : ∀ i, IsPositiveRecord (κ' i)
  mass_eq : ∀ i, mass (κ' i) = mass (κ i)
  tag : Ib → Tag
  dconst : Ib → ℝ
  dconst_nonneg : ∀ i, 0 ≤ dconst i
  /-- (CP2)(b): the sharp bound at the cut of the tag (`def:price`(b)). -/
  sharp : ∀ i, HasSharpBound (cut (tag i)) (κ i) (κ' i - κ i) (dconst i)
  /-- No differences off the first-stage atoms. -/
  off : first = false → IsEmpty Ib

attribute [instance] AtomStage.IaFintype AtomStage.IbFintype AtomStage.IbDecEq

namespace AtomStage

variable {X : Type} [Fintype X] [DecidableEq X] {μ : SlotMeasure X} {Tag : Type}
  {cut : Tag → ReflectionCut Slot} {ϑ₀ : ReflectionCut Slot}

/-- **The data of an atom that is not a first-stage atom**: `ρ = μ`, no records. -/
def trivial (μ : SlotMeasure X) (Tag : Type) (cut : Tag → ReflectionCut Slot)
    (ϑ₀ : ReflectionCut Slot) : AtomStage μ Tag cut ϑ₀ where
  first := false
  ρ := μ
  Ia := Empty
  ca := fun i => i.elim
  κa := fun i => i.elim
  κa_pos := fun i => i.elim
  ρ_sub := by simp
  ρ_ge := fun h => absurd h Bool.false_ne_true
  ρ_off := fun _ => rfl
  Ib := Empty
  κ := fun i => i.elim
  κ' := fun i => i.elim
  κ_pos := fun i => i.elim
  κ'_pos := fun i => i.elim
  mass_eq := fun i => i.elim
  tag := fun i => i.elim
  dconst := fun i => i.elim
  dconst_nonneg := fun i => i.elim
  sharp := fun i => i.elim
  off := fun _ => inferInstance

variable (A : AtomStage μ Tag cut ϑ₀)

/-- The variation price `p_𝔟 = ∑_i |c_i| κ_i(1) q_𝔟^{2a}` at the selection factor `sel`. -/
noncomputable def pvar (sel : ℝ) : ℝ := ∑ i, |A.ca i| * mass (A.κa i) * sel

/-- The sharp prices of tag `j` at the atom. -/
noncomputable def dTag [DecidableEq Tag] (sel : ℝ) (j : Tag) : ℝ :=
  ∑ i, if A.tag i = j then sharpPrice sel (A.κ i) (A.dconst i) else 0

/-- The variation prices of tag `j` at the atom. -/
noncomputable def vTag [DecidableEq Tag] (sel : ℝ) (j : Tag) : ℝ :=
  ∑ i, if A.tag i = j then (mass (A.κ i) + mass (A.κ' i)) * sel else 0

omit [DecidableEq X] in
theorem mass_nonneg_of_positive {κ : SlotMeasure X} (h : IsPositiveRecord κ) : 0 ≤ mass κ :=
  h.1 _ fun _ => zero_le_one

theorem pvar_nonneg {sel : ℝ} (hsel : 0 ≤ sel) : 0 ≤ A.pvar sel :=
  sum_nonneg fun i _ => mul_nonneg (mul_nonneg (abs_nonneg _)
    (mass_nonneg_of_positive (A.κa_pos i))) hsel

theorem dTag_nonneg [DecidableEq Tag] {sel : ℝ} (hsel : 0 ≤ sel) (j : Tag) : 0 ≤ A.dTag sel j := by
  refine sum_nonneg fun i _ => ?_
  split_ifs
  · exact mul_nonneg (mul_nonneg (mass_nonneg_of_positive (A.κ_pos i)) (A.dconst_nonneg i)) hsel
  · exact le_refl 0

theorem vTag_nonneg [DecidableEq Tag] {sel : ℝ} (hsel : 0 ≤ sel) (j : Tag) : 0 ≤ A.vTag sel j := by
  refine sum_nonneg fun i _ => ?_
  split_ifs
  · exact mul_nonneg (add_nonneg (mass_nonneg_of_positive (A.κ_pos i))
      (mass_nonneg_of_positive (A.κ'_pos i))) hsel
  · exact le_refl 0

end AtomStage

/-! ## The assembly -/

variable {a : ℝ}
variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] (m₀ : J₀ → ℕ) [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] (blk : J₀ → Bk)
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] (p : ∀ L, J L → ℕ)
  [∀ L j, NeZero (p L j)]

variable (a) in
/-- **(CP2) from per-atom data** (`def:cp2`). The first-stage atoms are the prefix atoms `β` with
`(A β).first`; the tail atoms carry the trivial data. The totals are the sums over the prefix atoms:
`P = ∑_β p_β`, `d_j = ∑_β d_{β,j}`, `v_j = ∑_β v_{β,j}` (scale-independent, as the atoms of a block
are). -/
noncomputable def firstStageOfAtoms (selPre : Bk → ℝ) (R : Reference m₀ blk) (Tag : Type)
    [Fintype Tag] [DecidableEq Tag] (cut : Tag → ReflectionCut Slot)
    (hcut : ∀ j, IsFamilyCut (cut j)) (ϑ₀ : ReflectionCut Slot) (hϑ₀ : IsFamilyCut ϑ₀)
    (A : ∀ β, AtomStage (signedIntegral (R.μ₀ β).weight) Tag cut ϑ₀) :
    FirstStage a m₀ blk p selPre R where
  fs L := univ.filter (fun b : BlockAtom Bk J L =>
    Sum.elim (fun β => (A β).first) (fun _ => false) b)
  Tag := Tag
  cut := cut
  cut_family := hcut
  ϑ₀ := ϑ₀
  ϑ₀_family := hϑ₀
  ρ L b := match b with
    | .inl β => (A β).ρ
    | .inr j => R.law p L (.inr j)
  Ia L b := match b with
    | .inl β => (A β).Ia
    | .inr _ => Empty
  IaFintype L b := match b with
    | .inl β => (A β).IaFintype
    | .inr _ => inferInstanceAs (Fintype Empty)
  ca L b := match b with
    | .inl β => (A β).ca
    | .inr _ => fun i => i.elim
  κa L b := match b with
    | .inl β => (A β).κa
    | .inr _ => fun i => i.elim
  κa_pos L b := match b with
    | .inl β => (A β).κa_pos
    | .inr _ => fun i => i.elim
  ρ_sub L b := match b with
    | .inl β => (A β).ρ_sub
    | .inr _ => by simp
  ρ_ge L b hb := match b with
    | .inl β => (A β).ρ_ge (by simpa using hb)
    | .inr _ => absurd hb (by simp)
  ρ_off L b hb := match b with
    | .inl β => (A β).ρ_off (by simpa using hb)
    | .inr _ => rfl
  Ib L b := match b with
    | .inl β => (A β).Ib
    | .inr _ => Empty
  IbFintype L b := match b with
    | .inl β => (A β).IbFintype
    | .inr _ => inferInstanceAs (Fintype Empty)
  IbDecEq L b := match b with
    | .inl β => (A β).IbDecEq
    | .inr _ => inferInstanceAs (DecidableEq Empty)
  κ L b := match b with
    | .inl β => (A β).κ
    | .inr _ => fun i => i.elim
  κ' L b := match b with
    | .inl β => (A β).κ'
    | .inr _ => fun i => i.elim
  κ_pos L b := match b with
    | .inl β => (A β).κ_pos
    | .inr _ => fun i => i.elim
  κ'_pos L b := match b with
    | .inl β => (A β).κ'_pos
    | .inr _ => fun i => i.elim
  mass_eq L b := match b with
    | .inl β => (A β).mass_eq
    | .inr _ => fun i => i.elim
  tag L b := match b with
    | .inl β => (A β).tag
    | .inr _ => fun i => i.elim
  dconst L b := match b with
    | .inl β => (A β).dconst
    | .inr _ => fun i => i.elim
  dconst_nonneg L b := match b with
    | .inl β => (A β).dconst_nonneg
    | .inr _ => fun i => i.elim
  sharp L b := match b with
    | .inl β => (A β).sharp
    | .inr _ => fun i => i.elim
  off L b hb := match b with
    | .inl β => (A β).off (by simpa using hb)
    | .inr _ => inferInstanceAs (IsEmpty Empty)
  P := ∑ β, (A β).pvar (selPre β)
  dT j := ∑ β, (A β).dTag (selPre β) j
  vT j := ∑ β, (A β).vTag (selPre β) j
  P_total L := by
    rw [Fintype.sum_sum_type]
    simp only [Finset.univ_eq_empty, sum_empty, sum_const_zero, add_zero]
    rfl
  dT_total L j := by
    rw [Fintype.sum_sum_type]
    simp only [Finset.univ_eq_empty, sum_empty, sum_const_zero, add_zero]
    rfl
  vT_total L j := by
    rw [Fintype.sum_sum_type]
    simp only [Finset.univ_eq_empty, sum_empty, sum_const_zero, add_zero]
    rfl

section Totals

variable {selPre : Bk → ℝ} {R : Reference m₀ blk} {Tag : Type} [Fintype Tag] [DecidableEq Tag]
  {cut : Tag → ReflectionCut Slot} {hcut : ∀ j, IsFamilyCut (cut j)} {ϑ₀ : ReflectionCut Slot}
  {hϑ₀ : IsFamilyCut ϑ₀} {A : ∀ β, AtomStage (signedIntegral (R.μ₀ β).weight) Tag cut ϑ₀}

omit [∀ L, DecidableEq (J L)] in
theorem firstStageOfAtoms_P :
    (firstStageOfAtoms a m₀ blk p selPre R Tag cut hcut ϑ₀ hϑ₀ A).P =
      ∑ β, (A β).pvar (selPre β) := rfl

omit [∀ L, DecidableEq (J L)] in
theorem firstStageOfAtoms_dT (j : Tag) :
    (firstStageOfAtoms a m₀ blk p selPre R Tag cut hcut ϑ₀ hϑ₀ A).dT j =
      ∑ β, (A β).dTag (selPre β) j := rfl

omit [∀ L, DecidableEq (J L)] in
theorem firstStageOfAtoms_vT (j : Tag) :
    (firstStageOfAtoms a m₀ blk p selPre R Tag cut hcut ϑ₀ hϑ₀ A).vT j =
      ∑ β, (A β).vTag (selPre β) j := rfl

end Totals

end Sarkozy.FirstStagePaper
