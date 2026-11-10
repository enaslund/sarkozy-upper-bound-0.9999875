module

public import Mathlib.Data.Finset.Interval
public import Mathlib.Data.Finset.Max
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.Ring
public import Mathlib.Logic.Relation
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases

@[expose] public section

/-!
# The compressed partition (`lem:advance:compressed-partition`(a), (b), (c))

`paper/sections/16_extraction.tex`, the paragraph *Classes*, `def:extraction:witness` and
`lem:advance:compressed-partition`. All three parts (a), (b), (c) are proved, with no hypotheses
beyond those of the paper.

**Setting.** Types `X`, `Z` with decidable equality and a finite set `Ex : Finset (X × Z)` of
pairs (the paper's `E_×`, symmetric or not). Two pairs are *disjoint* (`PairDisj`) if their
`x`-endpoints differ and their `x'`-endpoints differ. As in `subsec:spec:perp`, a nonempty set of
pairs is a *row star* if its set `J(S)` of `x`-endpoints has one element (`IsRowStar`), a
*column star* if its set `K(S)` of `x'`-endpoints has one element (`IsColStar`), and a
*nonstar* otherwise (`IsNonstar`; the empty set is neither). `rowDeg Ex j = r^X_j` and
`colDeg Ex k = r^Z_k`. The class `𝒞(P, A) = {S : P ⊆ S ⊆ Ex \ A}` is `cls Ex P A`; its free pairs
are `F = Ex \ (P ∪ A)` and its mass is `2^{|F|}`. A *class datum* is a pair `(P, A)` of disjoint
subsets of `Ex` (`IsClassDatum`), and an *exact partition* of a family `𝓕` is a finite set of
class data whose classes are pairwise disjoint with union `𝓕` (`IsExactPartition`).

**(a)** `noPairDisj_iff`: a set contains no two disjoint pairs iff it is empty or a star
(`isNonstar_iff`: a nonstar is a set with two disjoint pairs). `card_emptyOrStar` (and
`card_noPairDisj`, `card_emptyOrStar_int` with integer subtractions): the empty set and the
stars inside `Ex` are `1 + m_× + ∑_j (2^{r^X_j} − 1 − r^X_j) + ∑_k (2^{r^Z_k} − 1 − r^Z_k)`
subsets. `card_cls`: `|𝒞(P, A)| = 2^{|F|}`. `sum_mass_eq` (any finite family of pairwise
disjoint classes with union the nonstar subsets) and `IsExactPartition.sum_mass`: the masses add
up to `2^{m_×}` minus that number (`sum_mass_add`: the additive form).

**(b)** The total order `≺` on `Ex` is given by a rank function `ρ : X × Z → ℕ` injective on
`Ex`, `g ≺ h ↔ ρ g < ρ h` (every total order on the finite set `Ex` is of this form, e.g. with
`ρ g` the number of predecessors of `g`). `IsCompressedDatum ρ Ex S (P, A)` says that `e` is the
first pair of `S` (`IsFirst`) and that either (case (A)) `f` is the first pair of `S` disjoint
from `e` and `(P, A) = datumA ρ Ex S e f`, or (case (B)) no pair of `S` is disjoint from `e`,
`g₁`, `g₂` are the first arms (`rowArms`, `colArms`) and `(P, A) = datumB ρ Ex e g₁ g₂`; these
are the paper's formulas. `arms_nonempty`, `exists_isCompressedDatum` and
`IsCompressedDatum.unique`: every nonstar has exactly one datum. `IsCompressedDatum.self_mem_cls`
(`S ∈ 𝒞(S)`), `IsCompressedDatum.of_mem_cls` and `compressedDatum_of_mem_cls`: every element
of `𝒞(S)` is a nonstar with the same class. `isExactPartition_compressedPartition`: the distinct
classes `𝒞(S)` form an exact partition of the nonstar subsets (`sum_mass_compressedPartition`:
its masses). `isWitness_datumA`, `witnessArc_datumA` (case (A): `e, f` are a witness of size
two, with the arc `1 → 2` iff `(a, b') ∈ S` and the arc `2 → 1` iff `(a', b) ∈ S`),
`isWitness_datumB`, `witnessArc_datumB` (case (B): `g₁, g₂` are a witness of size two with the
arc `1 → 2` only), `IsCompressedDatum.exists_witness_twoCycle_iff` (the digraph is a two-cycle
iff case (A) with both connectors present, and acyclic otherwise).

**(c)** `cls_children_disjoint`, `cls_children_union`: the children `𝒞(P ∪ {g}, A)` and
`𝒞(P, A ∪ {g})` partition `𝒞(P, A)` (for every pair `g`); `IsClassDatum.children`: for a free
`g` they are class data. `IsExactPartition.refineStep`, `IsExactPartition.refine`: replacing a
class of an exact partition by its children, any number of times, gives an exact partition.
`IsWitness.child_present`, `IsWitness.child_absent`, `IsCover.child_present`,
`IsCover.child_absent`, `IsWitness.refine`, `IsCover.refine`: a witness (with its witness
digraph, `ClassWitnessArc`) and a cover of a class are a witness and a cover of each child and of
every class obtained by deciding free pairs one at a time (`IsChild`). `isWitness_of_refine`:
`k` pairs of `P` with distinct `x`-endpoints and distinct `x'`-endpoints are a witness of size
`k` of every such class in which their rectangle is decided.

**Formal conventions.** A witness of size `k` is a map `w : Fin k → X × Z` (`IsWitness`, the
condition (W_k); the standing assumption `k ≥ 1` is not needed and not imposed); the rectangle
`E_{VW}` is the set of pairs of `Ex` whose `x`-endpoint is some `(w i).1` and whose
`x'`-endpoint is some `(w l).2` (pairs outside `Ex` count as absent). A cover is `IsCover`, the
condition (VC_k), with `C_x ∩ V = ∅`, `C_z ∩ W = ∅`. The class `𝒞(S)` of a nonstar is
`compressedDatum ρ Ex S`, a choice among the data of `S`, which is unique by
`IsCompressedDatum.unique`.
-/

open Finset

namespace Sarkozy.Extraction

variable {X Z : Type*} [DecidableEq X] [DecidableEq Z]

/-! ### Stars and nonstars -/

/-- Two pairs are *disjoint* if their `x`-endpoints differ and their `x'`-endpoints differ. -/
def PairDisj (e f : X × Z) : Prop := e.1 ≠ f.1 ∧ e.2 ≠ f.2

instance (e f : X × Z) : Decidable (PairDisj e f) :=
  inferInstanceAs (Decidable (e.1 ≠ f.1 ∧ e.2 ≠ f.2))

/-- A *row star*: a set `S` of pairs whose set `J(S)` of `x`-endpoints has one element
(so `S` is nonempty). -/
def IsRowStar (S : Finset (X × Z)) : Prop := #(S.image Prod.fst) = 1

/-- A *column star*: a set `S` of pairs whose set `K(S)` of `x'`-endpoints has one element. -/
def IsColStar (S : Finset (X × Z)) : Prop := #(S.image Prod.snd) = 1

/-- A *star*: a row star or a column star. -/
def IsStar (S : Finset (X × Z)) : Prop := IsRowStar S ∨ IsColStar S

/-- A *nonstar*: a nonempty set that is not a star (`subsec:spec:perp`). -/
def IsNonstar (S : Finset (X × Z)) : Prop := S.Nonempty ∧ ¬ IsStar S

instance (S : Finset (X × Z)) : Decidable (IsRowStar S) :=
  inferInstanceAs (Decidable (_ = _))

instance (S : Finset (X × Z)) : Decidable (IsColStar S) :=
  inferInstanceAs (Decidable (_ = _))

instance (S : Finset (X × Z)) : Decidable (IsStar S) :=
  inferInstanceAs (Decidable (_ ∨ _))

instance (S : Finset (X × Z)) : Decidable (IsNonstar S) :=
  inferInstanceAs (Decidable (_ ∧ _))

omit [DecidableEq Z] in
theorem isRowStar_iff {S : Finset (X × Z)} :
    IsRowStar S ↔ S.Nonempty ∧ ∃ j, ∀ e ∈ S, e.1 = j := by
  unfold IsRowStar
  rw [card_eq_one]
  constructor
  · rintro ⟨j, hj⟩
    refine ⟨?_, j, fun e he => ?_⟩
    · have : j ∈ S.image Prod.fst := by rw [hj]; exact mem_singleton_self j
      obtain ⟨e, he, -⟩ := mem_image.1 this
      exact ⟨e, he⟩
    · have : e.1 ∈ S.image Prod.fst := mem_image_of_mem _ he
      rw [hj] at this
      exact mem_singleton.1 this
  · rintro ⟨⟨e₀, he₀⟩, j, hj⟩
    refine ⟨j, ?_⟩
    ext x
    simp only [mem_image, mem_singleton]
    constructor
    · rintro ⟨e, he, rfl⟩; exact hj e he
    · rintro rfl; exact ⟨e₀, he₀, hj e₀ he₀⟩

omit [DecidableEq X] in
theorem isColStar_iff {S : Finset (X × Z)} :
    IsColStar S ↔ S.Nonempty ∧ ∃ k, ∀ e ∈ S, e.2 = k := by
  unfold IsColStar
  rw [card_eq_one]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨?_, k, fun e he => ?_⟩
    · have : k ∈ S.image Prod.snd := by rw [hk]; exact mem_singleton_self k
      obtain ⟨e, he, -⟩ := mem_image.1 this
      exact ⟨e, he⟩
    · have : e.2 ∈ S.image Prod.snd := mem_image_of_mem _ he
      rw [hk] at this
      exact mem_singleton.1 this
  · rintro ⟨⟨e₀, he₀⟩, k, hk⟩
    refine ⟨k, ?_⟩
    ext x
    simp only [mem_image, mem_singleton]
    constructor
    · rintro ⟨e, he, rfl⟩; exact hk e he
    · rintro rfl; exact ⟨e₀, he₀, hk e₀ he₀⟩

/-- **`lem:advance:compressed-partition`(a), first assertion.** A set of pairs contains no two
disjoint pairs if and only if it is empty or a star. -/
theorem noPairDisj_iff {S : Finset (X × Z)} :
    (∀ e ∈ S, ∀ f ∈ S, ¬ PairDisj e f) ↔ S = ∅ ∨ IsStar S := by
  constructor
  · intro h
    rcases S.eq_empty_or_nonempty with hS | ⟨e, he⟩
    · exact Or.inl hS
    right
    by_contra hns
    have hg : ∃ g ∈ S, g.1 ≠ e.1 := by
      by_contra hcon
      push Not at hcon
      exact hns (Or.inl (isRowStar_iff.2 ⟨⟨e, he⟩, e.1, hcon⟩))
    have hg' : ∃ g ∈ S, g.2 ≠ e.2 := by
      by_contra hcon
      push Not at hcon
      exact hns (Or.inr (isColStar_iff.2 ⟨⟨e, he⟩, e.2, hcon⟩))
    obtain ⟨g, hgS, hg1⟩ := hg
    obtain ⟨g', hg'S, hg2⟩ := hg'
    have h1 : g.2 = e.2 := by
      by_contra hne
      exact h e he g hgS ⟨Ne.symm hg1, Ne.symm hne⟩
    have h2 : g'.1 = e.1 := by
      by_contra hne
      exact h e he g' hg'S ⟨Ne.symm hne, Ne.symm hg2⟩
    exact h g hgS g' hg'S ⟨by rw [h2]; exact hg1, by rw [h1]; exact Ne.symm hg2⟩
  · rintro (rfl | hst) e he f hf hd
    · simp at he
    · rcases hst with hr | hc
      · obtain ⟨-, j, hj⟩ := isRowStar_iff.1 hr
        exact hd.1 (by rw [hj e he, hj f hf])
      · obtain ⟨-, k, hk⟩ := isColStar_iff.1 hc
        exact hd.2 (by rw [hk e he, hk f hf])

/-- A nonstar is a set containing two disjoint pairs. -/
theorem isNonstar_iff {S : Finset (X × Z)} :
    IsNonstar S ↔ ∃ e ∈ S, ∃ f ∈ S, PairDisj e f := by
  rw [IsNonstar]
  constructor
  · rintro ⟨hne, hst⟩
    by_contra h
    push Not at h
    rcases noPairDisj_iff.1 h with h0 | h1
    · exact hne.ne_empty h0
    · exact hst h1
  · rintro ⟨e, he, f, hf, hd⟩
    exact ⟨⟨e, he⟩, fun hst => noPairDisj_iff.2 (Or.inr hst) e he f hf hd⟩

theorem isNonstar_iff_not {S : Finset (X × Z)} : IsNonstar S ↔ ¬ (S = ∅ ∨ IsStar S) := by
  rw [IsNonstar, not_or, nonempty_iff_ne_empty]

theorem isStar_of_card_eq_one {S : Finset (X × Z)} (h : #S = 1) : IsStar S := by
  obtain ⟨e, rfl⟩ := card_eq_one.1 h
  left
  simp [IsRowStar]

/-! ### Counting the empty set and the stars -/

/-- `r^X_j`: the number of pairs of `Ex` with `x`-endpoint `j`. -/
def rowDeg (Ex : Finset (X × Z)) (j : X) : ℕ := #(Ex.filter fun e => e.1 = j)

/-- `r^Z_k`: the number of pairs of `Ex` with `x'`-endpoint `k`. -/
def colDeg (Ex : Finset (X × Z)) (k : Z) : ℕ := #(Ex.filter fun e => e.2 = k)

/-- The nonstar subsets of `Ex`. -/
def nonstars (Ex : Finset (X × Z)) : Finset (Finset (X × Z)) := Ex.powerset.filter IsNonstar

theorem card_powerset_filter_card_lt_two {α : Type*} [DecidableEq α] (T : Finset α) :
    #(T.powerset.filter fun U => #U < 2) = 1 + #T := by
  have h : (T.powerset.filter fun U => #U < 2) = powersetCard 0 T ∪ powersetCard 1 T := by
    ext U
    simp only [mem_filter, mem_powerset, mem_union, mem_powersetCard]
    constructor
    · rintro ⟨hU, h2⟩
      have : #U = 0 ∨ #U = 1 := by omega
      rcases this with h | h
      · exact Or.inl ⟨hU, h⟩
      · exact Or.inr ⟨hU, h⟩
    · rintro (⟨hU, h⟩ | ⟨hU, h⟩) <;> exact ⟨hU, by omega⟩
  have hd : Disjoint (powersetCard 0 T) (powersetCard 1 T) := by
    rw [disjoint_left]
    intro U h0 h1
    rw [mem_powersetCard] at h0 h1
    omega
  rw [h, card_union_of_disjoint hd, card_powersetCard, card_powersetCard, Nat.choose_zero_right,
    Nat.choose_one_right]

theorem card_powerset_filter_two_le {α : Type*} [DecidableEq α] (T : Finset α) :
    #(T.powerset.filter fun U => 2 ≤ #U) = 2 ^ #T - 1 - #T := by
  have h := card_filter_add_card_filter_not (s := T.powerset) (fun U => 2 ≤ #U)
  have h' : (T.powerset.filter fun U => ¬ 2 ≤ #U) = T.powerset.filter fun U => #U < 2 := by
    ext U
    simp only [mem_filter, not_le]
  rw [h', card_powerset_filter_card_lt_two, card_powerset] at h
  omega

theorem filter_rowStar_eq [Fintype X] (Ex : Finset (X × Z)) :
    (Ex.powerset.filter fun S => 2 ≤ #S ∧ IsRowStar S) =
      univ.biUnion fun j => (Ex.filter fun e => e.1 = j).powerset.filter fun U => 2 ≤ #U := by
  ext S
  simp only [mem_filter, mem_powerset, mem_biUnion, mem_univ, true_and]
  constructor
  · rintro ⟨hS, h2, hr⟩
    obtain ⟨-, j, hj⟩ := isRowStar_iff.1 hr
    exact ⟨j, fun e he => mem_filter.2 ⟨hS he, hj e he⟩, h2⟩
  · rintro ⟨j, hS, h2⟩
    refine ⟨hS.trans (filter_subset _ _), h2,
      isRowStar_iff.2 ⟨card_pos.1 (by omega), j, fun e he => (mem_filter.1 (hS he)).2⟩⟩

theorem filter_colStar_eq [Fintype Z] (Ex : Finset (X × Z)) :
    (Ex.powerset.filter fun S => 2 ≤ #S ∧ IsColStar S) =
      univ.biUnion fun k => (Ex.filter fun e => e.2 = k).powerset.filter fun U => 2 ≤ #U := by
  ext S
  simp only [mem_filter, mem_powerset, mem_biUnion, mem_univ, true_and]
  constructor
  · rintro ⟨hS, h2, hc⟩
    obtain ⟨-, k, hk⟩ := isColStar_iff.1 hc
    exact ⟨k, fun e he => mem_filter.2 ⟨hS he, hk e he⟩, h2⟩
  · rintro ⟨k, hS, h2⟩
    refine ⟨hS.trans (filter_subset _ _), h2,
      isColStar_iff.2 ⟨card_pos.1 (by omega), k, fun e he => (mem_filter.1 (hS he)).2⟩⟩

theorem card_filter_rowStar [Fintype X] (Ex : Finset (X × Z)) :
    #(Ex.powerset.filter fun S => 2 ≤ #S ∧ IsRowStar S) =
      ∑ j : X, (2 ^ rowDeg Ex j - 1 - rowDeg Ex j) := by
  rw [filter_rowStar_eq, card_biUnion]
  · simp only [card_powerset_filter_two_le, rowDeg]
  · intro j _ j' _ hjj'
    simp only [Function.onFun]
    rw [disjoint_left]
    intro U hU hU'
    simp only [mem_filter, mem_powerset] at hU hU'
    obtain ⟨e, he⟩ := card_pos.1 (by omega : 0 < #U)
    exact hjj' ((mem_filter.1 (hU.1 he)).2.symm.trans (mem_filter.1 (hU'.1 he)).2)

theorem card_filter_colStar [Fintype Z] (Ex : Finset (X × Z)) :
    #(Ex.powerset.filter fun S => 2 ≤ #S ∧ IsColStar S) =
      ∑ k : Z, (2 ^ colDeg Ex k - 1 - colDeg Ex k) := by
  rw [filter_colStar_eq, card_biUnion]
  · simp only [card_powerset_filter_two_le, colDeg]
  · intro k _ k' _ hkk'
    simp only [Function.onFun]
    rw [disjoint_left]
    intro U hU hU'
    simp only [mem_filter, mem_powerset] at hU hU'
    obtain ⟨e, he⟩ := card_pos.1 (by omega : 0 < #U)
    exact hkk' ((mem_filter.1 (hU.1 he)).2.symm.trans (mem_filter.1 (hU'.1 he)).2)

/-- **`lem:advance:compressed-partition`(a), the count.** The empty set and the stars inside
`Ex` are `1 + m_× + ∑_j (2^{r^X_j} − 1 − r^X_j) + ∑_k (2^{r^Z_k} − 1 − r^Z_k)` subsets
(the natural-number subtractions are exact, since `1 + r ≤ 2^r`). -/
theorem card_emptyOrStar [Fintype X] [Fintype Z] (Ex : Finset (X × Z)) :
    #(Ex.powerset.filter fun S => S = ∅ ∨ IsStar S) =
      1 + #Ex + ∑ j : X, (2 ^ rowDeg Ex j - 1 - rowDeg Ex j) +
        ∑ k : Z, (2 ^ colDeg Ex k - 1 - colDeg Ex k) := by
  have hsplit : (Ex.powerset.filter fun S => S = ∅ ∨ IsStar S) =
      (Ex.powerset.filter fun S => #S < 2) ∪
        ((Ex.powerset.filter fun S => 2 ≤ #S ∧ IsRowStar S) ∪
          (Ex.powerset.filter fun S => 2 ≤ #S ∧ IsColStar S)) := by
    ext S
    simp only [mem_filter, mem_powerset, mem_union]
    constructor
    · rintro ⟨hS, h⟩
      by_cases h2 : #S < 2
      · exact Or.inl ⟨hS, h2⟩
      · rcases h with h0 | hr | hc
        · subst h0; simp at h2
        · exact Or.inr (Or.inl ⟨hS, by omega, hr⟩)
        · exact Or.inr (Or.inr ⟨hS, by omega, hc⟩)
    · rintro (⟨hS, h2⟩ | ⟨hS, -, hr⟩ | ⟨hS, -, hc⟩)
      · refine ⟨hS, ?_⟩
        have : #S = 0 ∨ #S = 1 := by omega
        rcases this with h | h
        · exact Or.inl (card_eq_zero.1 h)
        · exact Or.inr (isStar_of_card_eq_one h)
      · exact ⟨hS, Or.inr (Or.inl hr)⟩
      · exact ⟨hS, Or.inr (Or.inr hc)⟩
  have hd1 : Disjoint (Ex.powerset.filter fun S => 2 ≤ #S ∧ IsRowStar S)
      (Ex.powerset.filter fun S => 2 ≤ #S ∧ IsColStar S) := by
    rw [disjoint_filter]
    rintro S - ⟨h2, hr⟩ ⟨-, hc⟩
    obtain ⟨-, j, hj⟩ := isRowStar_iff.1 hr
    obtain ⟨-, k, hk⟩ := isColStar_iff.1 hc
    have : #S ≤ 1 := card_le_one.2 fun a ha b hb =>
      Prod.ext (by rw [hj a ha, hj b hb]) (by rw [hk a ha, hk b hb])
    omega
  have hd2 : Disjoint (Ex.powerset.filter fun S => #S < 2)
      ((Ex.powerset.filter fun S => 2 ≤ #S ∧ IsRowStar S) ∪
        (Ex.powerset.filter fun S => 2 ≤ #S ∧ IsColStar S)) := by
    rw [disjoint_union_right]
    constructor
    · rw [disjoint_filter]
      rintro S - h ⟨h2, -⟩
      omega
    · rw [disjoint_filter]
      rintro S - h ⟨h2, -⟩
      omega
  rw [hsplit, card_union_of_disjoint hd2, card_union_of_disjoint hd1,
    card_powerset_filter_card_lt_two, card_filter_rowStar, card_filter_colStar]
  omega

/-- `lem:advance:compressed-partition`(a), the count, in the form "subsets containing no two
disjoint pairs". -/
theorem card_noPairDisj [Fintype X] [Fintype Z] (Ex : Finset (X × Z)) :
    #(Ex.powerset.filter fun S => ∀ e ∈ S, ∀ f ∈ S, ¬ PairDisj e f) =
      1 + #Ex + ∑ j : X, (2 ^ rowDeg Ex j - 1 - rowDeg Ex j) +
        ∑ k : Z, (2 ^ colDeg Ex k - 1 - colDeg Ex k) := by
  rw [← card_emptyOrStar]
  congr 1
  exact filter_congr fun S _ => noPairDisj_iff

omit [DecidableEq X] [DecidableEq Z] in
theorem cast_two_pow_sub_one_sub (r : ℕ) : ((2 ^ r - 1 - r : ℕ) : ℤ) = 2 ^ r - 1 - r := by
  have h := Nat.lt_two_pow_self (n := r)
  have h1 : 1 ≤ 2 ^ r := Nat.one_le_two_pow
  rw [Nat.cast_sub (by omega), Nat.cast_sub h1]
  push_cast
  ring

/-- `card_emptyOrStar` with integer subtractions. -/
theorem card_emptyOrStar_int [Fintype X] [Fintype Z] (Ex : Finset (X × Z)) :
    (#(Ex.powerset.filter fun S => S = ∅ ∨ IsStar S) : ℤ) =
      1 + #Ex + ∑ j : X, ((2 : ℤ) ^ rowDeg Ex j - 1 - rowDeg Ex j) +
        ∑ k : Z, ((2 : ℤ) ^ colDeg Ex k - 1 - colDeg Ex k) := by
  rw [card_emptyOrStar]
  push_cast [cast_two_pow_sub_one_sub]
  ring

/-- The nonstar subsets of `Ex` and the empty set and stars together are all `2^{m_×}`
subsets. -/
theorem card_nonstars_add [Fintype X] [Fintype Z] (Ex : Finset (X × Z)) :
    #(nonstars Ex) + (1 + #Ex + ∑ j : X, (2 ^ rowDeg Ex j - 1 - rowDeg Ex j) +
        ∑ k : Z, (2 ^ colDeg Ex k - 1 - colDeg Ex k)) = 2 ^ #Ex := by
  have h := card_filter_add_card_filter_not (s := Ex.powerset) (fun S => S = ∅ ∨ IsStar S)
  have h' : (Ex.powerset.filter fun S => ¬ (S = ∅ ∨ IsStar S)) = nonstars Ex := by
    ext S
    simp only [nonstars, mem_filter, isNonstar_iff_not]
  rw [h', card_emptyOrStar, card_powerset] at h
  omega

/-! ### Classes -/

/-- The class `𝒞(P, A) = {S : P ⊆ S ⊆ Ex \ A}`. -/
def cls (Ex P A : Finset (X × Z)) : Finset (Finset (X × Z)) :=
  (Ex \ A).powerset.filter fun S => P ⊆ S

@[simp]
theorem mem_cls {Ex P A S : Finset (X × Z)} : S ∈ cls Ex P A ↔ P ⊆ S ∧ S ⊆ Ex \ A := by
  rw [cls, mem_filter, mem_powerset, and_comm]

/-- The size of a class is its mass `2^{|F|}`, `F = Ex \ (P ∪ A)`. -/
theorem card_cls {Ex P A : Finset (X × Z)} (hP : P ⊆ Ex) (hPA : Disjoint P A) :
    #(cls Ex P A) = 2 ^ #(Ex \ (P ∪ A)) := by
  have hsub : P ⊆ Ex \ A := fun x hx => mem_sdiff.2 ⟨hP hx, disjoint_left.1 hPA hx⟩
  have h1 : cls Ex P A = Icc P (Ex \ A) := by rw [Icc_eq_filter_powerset]; rfl
  have h2 : Ex \ (P ∪ A) = (Ex \ A) \ P := by
    ext x
    simp only [mem_sdiff, mem_union]
    tauto
  rw [h1, card_Icc_finset hsub, h2, card_sdiff_of_subset hsub]

/-- `lem:advance:compressed-partition`(a), the masses, additive form: for a finite family of
pairwise disjoint classes `𝒞(P_i, A_i)` (`P_i ⊆ Ex`, `P_i ∩ A_i = ∅`) whose union is the set of
nonstar subsets of `Ex`, the masses `2^{|F_i|}` and the number of empty and star subsets add up
to `2^{m_×}`. -/
theorem sum_mass_add [Fintype X] [Fintype Z] {ι : Type*} {Ex : Finset (X × Z)} {I : Finset ι}
    {P A : ι → Finset (X × Z)} (hP : ∀ i ∈ I, P i ⊆ Ex) (hPA : ∀ i ∈ I, Disjoint (P i) (A i))
    (hdisj : (I : Set ι).PairwiseDisjoint fun i => cls Ex (P i) (A i))
    (hunion : I.biUnion (fun i => cls Ex (P i) (A i)) = nonstars Ex) :
    ∑ i ∈ I, 2 ^ #(Ex \ (P i ∪ A i)) + (1 + #Ex + ∑ j : X, (2 ^ rowDeg Ex j - 1 - rowDeg Ex j) +
        ∑ k : Z, (2 ^ colDeg Ex k - 1 - colDeg Ex k)) = 2 ^ #Ex := by
  have h1 : ∑ i ∈ I, 2 ^ #(Ex \ (P i ∪ A i)) = #(nonstars Ex) := by
    rw [← hunion, card_biUnion hdisj]
    exact sum_congr rfl fun i hi => (card_cls (hP i hi) (hPA i hi)).symm
  rw [h1]
  exact card_nonstars_add Ex

/-- **`lem:advance:compressed-partition`(a), the masses.** If a finite family of classes
`𝒞(P_i, A_i)` (`P_i ⊆ Ex`, `P_i ∩ A_i = ∅`) is pairwise disjoint and its union is the set of
nonstar subsets of `Ex`, the masses `2^{|F_i|}` add up to `2^{m_×}` minus the number of
`card_emptyOrStar` (the subtraction is exact by `sum_mass_add`). -/
theorem sum_mass_eq [Fintype X] [Fintype Z] {ι : Type*} {Ex : Finset (X × Z)} {I : Finset ι}
    {P A : ι → Finset (X × Z)} (hP : ∀ i ∈ I, P i ⊆ Ex) (hPA : ∀ i ∈ I, Disjoint (P i) (A i))
    (hdisj : (I : Set ι).PairwiseDisjoint fun i => cls Ex (P i) (A i))
    (hunion : I.biUnion (fun i => cls Ex (P i) (A i)) = nonstars Ex) :
    ∑ i ∈ I, 2 ^ #(Ex \ (P i ∪ A i)) =
      2 ^ #Ex - (1 + #Ex + ∑ j : X, (2 ^ rowDeg Ex j - 1 - rowDeg Ex j) +
        ∑ k : Z, (2 ^ colDeg Ex k - 1 - colDeg Ex k)) := by
  have h := sum_mass_add hP hPA hdisj hunion
  omega

/-- A *class datum* `(P, A)`: disjoint `P, A ⊆ Ex`. -/
def IsClassDatum (Ex : Finset (X × Z)) (c : Finset (X × Z) × Finset (X × Z)) : Prop :=
  c.1 ⊆ Ex ∧ c.2 ⊆ Ex ∧ Disjoint c.1 c.2

/-- An *exact partition* of a family `𝓕` of subsets of `Ex`: a set of class data whose classes
are pairwise disjoint and have union `𝓕`. -/
def IsExactPartition (Ex : Finset (X × Z)) (𝓟 : Finset (Finset (X × Z) × Finset (X × Z)))
    (𝓕 : Finset (Finset (X × Z))) : Prop :=
  (∀ c ∈ 𝓟, IsClassDatum Ex c) ∧
    (↑𝓟 : Set (Finset (X × Z) × Finset (X × Z))).PairwiseDisjoint (fun c => cls Ex c.1 c.2) ∧
    𝓟.biUnion (fun c => cls Ex c.1 c.2) = 𝓕

/-- `lem:advance:compressed-partition`(a), the masses, for an exact partition. -/
theorem IsExactPartition.sum_mass [Fintype X] [Fintype Z] {Ex : Finset (X × Z)}
    {𝓟 : Finset (Finset (X × Z) × Finset (X × Z))} (h : IsExactPartition Ex 𝓟 (nonstars Ex)) :
    ∑ c ∈ 𝓟, 2 ^ #(Ex \ (c.1 ∪ c.2)) =
      2 ^ #Ex - (1 + #Ex + ∑ j : X, (2 ^ rowDeg Ex j - 1 - rowDeg Ex j) +
        ∑ k : Z, (2 ^ colDeg Ex k - 1 - colDeg Ex k)) :=
  sum_mass_eq (fun c hc => (h.1 c hc).1) (fun c hc => (h.1 c hc).2.2) h.2.1 h.2.2

/-! ### Children (`lem:advance:compressed-partition`(c)) -/

theorem cls_present_subset (Ex P A : Finset (X × Z)) (g : X × Z) :
    cls Ex (insert g P) A ⊆ cls Ex P A := by
  intro S hS
  rw [mem_cls] at hS ⊢
  exact ⟨(subset_insert g P).trans hS.1, hS.2⟩

theorem cls_absent_subset (Ex P A : Finset (X × Z)) (g : X × Z) :
    cls Ex P (insert g A) ⊆ cls Ex P A := by
  intro S hS
  rw [mem_cls] at hS ⊢
  exact ⟨hS.1, hS.2.trans (sdiff_subset_sdiff subset_rfl (subset_insert g A))⟩

/-- **`lem:advance:compressed-partition`(c).** The children `𝒞(P ∪ {g}, A)` and
`𝒞(P, A ∪ {g})` of a class are disjoint. -/
theorem cls_children_disjoint (Ex P A : Finset (X × Z)) (g : X × Z) :
    Disjoint (cls Ex (insert g P) A) (cls Ex P (insert g A)) := by
  rw [disjoint_left]
  intro S h1 h2
  rw [mem_cls] at h1 h2
  have hg : g ∈ S := h1.1 (mem_insert_self g P)
  have := h2.2 hg
  simp at this

/-- **`lem:advance:compressed-partition`(c).** The union of the children `𝒞(P ∪ {g}, A)` and
`𝒞(P, A ∪ {g})` of a class is the class. -/
theorem cls_children_union (Ex P A : Finset (X × Z)) (g : X × Z) :
    cls Ex (insert g P) A ∪ cls Ex P (insert g A) = cls Ex P A := by
  ext S
  simp only [mem_union, mem_cls, insert_subset_iff, subset_sdiff, disjoint_insert_right]
  tauto

/-- The children of a class datum at a free pair `g ∈ F = Ex \ (P ∪ A)` are class data. -/
theorem IsClassDatum.children {Ex : Finset (X × Z)} {c : Finset (X × Z) × Finset (X × Z)}
    (hc : IsClassDatum Ex c) {g : X × Z} (hg : g ∈ Ex \ (c.1 ∪ c.2)) :
    IsClassDatum Ex (insert g c.1, c.2) ∧ IsClassDatum Ex (c.1, insert g c.2) := by
  obtain ⟨hgE, hgPA⟩ := mem_sdiff.1 hg
  rw [mem_union, not_or] at hgPA
  refine ⟨⟨insert_subset hgE hc.1, hc.2.1, ?_⟩, ⟨hc.1, insert_subset hgE hc.2.1, ?_⟩⟩
  · exact disjoint_insert_left.2 ⟨hgPA.2, hc.2.2⟩
  · exact disjoint_insert_right.2 ⟨hgPA.1, hc.2.2⟩

/-- One refinement step: a class of an exact partition is replaced by its two children at a
free pair. -/
def RefineStep (Ex : Finset (X × Z)) (𝓟 𝓟' : Finset (Finset (X × Z) × Finset (X × Z))) :
    Prop :=
  ∃ c ∈ 𝓟, ∃ g ∈ Ex \ (c.1 ∪ c.2),
    𝓟' = insert (insert g c.1, c.2) (insert (c.1, insert g c.2) (𝓟.erase c))

/-- **`lem:advance:compressed-partition`(c).** Replacing a class of an exact partition by its
children gives an exact partition. -/
theorem IsExactPartition.refineStep {Ex : Finset (X × Z)}
    {𝓟 𝓟' : Finset (Finset (X × Z) × Finset (X × Z))} {𝓕 : Finset (Finset (X × Z))}
    (h : IsExactPartition Ex 𝓟 𝓕) (hstep : RefineStep Ex 𝓟 𝓟') : IsExactPartition Ex 𝓟' 𝓕 := by
  obtain ⟨c, hc, g, hg, rfl⟩ := hstep
  obtain ⟨hdat, hdisj, hunion⟩ := h
  have hch := (hdat c hc).children hg
  have hsub : ∀ d ∈ 𝓟.erase c, Disjoint (cls Ex c.1 c.2) (cls Ex d.1 d.2) := by
    intro d hd
    obtain ⟨hdc, hd𝓟⟩ := mem_erase.1 hd
    exact hdisj hc hd𝓟 (Ne.symm hdc)
  refine ⟨?_, ?_, ?_⟩
  · intro d hd
    rcases mem_insert.1 hd with rfl | hd
    · exact hch.1
    rcases mem_insert.1 hd with rfl | hd
    · exact hch.2
    exact hdat d (mem_of_mem_erase hd)
  · rw [coe_insert, coe_insert]
    refine Set.PairwiseDisjoint.insert (Set.PairwiseDisjoint.insert ?_ ?_) ?_
    · exact hdisj.subset (by rw [coe_erase]; exact Set.sdiff_subset)
    · intro d hd _
      exact (hsub d (mem_coe.1 hd)).mono_left (cls_absent_subset Ex c.1 c.2 g)
    · intro d hd _
      rcases Set.mem_insert_iff.1 hd with rfl | hd
      · exact cls_children_disjoint Ex c.1 c.2 g
      · exact (hsub d (mem_coe.1 hd)).mono_left (cls_present_subset Ex c.1 c.2 g)
  · rw [← hunion]
    conv_rhs => rw [← insert_erase hc]
    simp only [biUnion_insert]
    rw [← union_assoc, cls_children_union]

/-- **`lem:advance:compressed-partition`(c).** Replacing classes by their children any number
of times gives an exact partition. -/
theorem IsExactPartition.refine {Ex : Finset (X × Z)}
    {𝓟 𝓟' : Finset (Finset (X × Z) × Finset (X × Z))} {𝓕 : Finset (Finset (X × Z))}
    (h : IsExactPartition Ex 𝓟 𝓕) (hr : Relation.ReflTransGen (RefineStep Ex) 𝓟 𝓟') :
    IsExactPartition Ex 𝓟' 𝓕 := by
  induction hr with
  | refl => exact h
  | tail _ hstep ih => exact ih.refineStep hstep

/-! ### Witnesses and covers (`def:extraction:witness`) -/

/-- **(W_k)** of `def:extraction:witness`(a): the pairs `w 0, …, w (k-1)` of `P` have distinct
`x`-endpoints `V` and distinct `x'`-endpoints `W`, and every pair of the rectangle
`E_{VW} = (V × W) ∩ Ex` is decided (present or absent). -/
structure IsWitness (Ex P A : Finset (X × Z)) {k : ℕ} (w : Fin k → X × Z) : Prop where
  mem : ∀ i, w i ∈ P
  injective_fst : Function.Injective fun i => (w i).1
  injective_snd : Function.Injective fun i => (w i).2
  decided : ∀ e ∈ Ex, (∃ i, (w i).1 = e.1) → (∃ l, (w l).2 = e.2) → e ∈ P ∨ e ∈ A

/-- **(VC_k)** of `def:extraction:witness`(c): `C_x ⊆ X \ V`, `C_z ⊆ Z \ W`, and every pair of
`P ∪ F` outside `V × W` has its `x`-endpoint in `C_x` or its `x'`-endpoint in `C_z`. -/
structure IsCover (Ex P A : Finset (X × Z)) {k : ℕ} (w : Fin k → X × Z) (Cx : Finset X)
    (Cz : Finset Z) : Prop where
  fst_not_mem : ∀ i, (w i).1 ∉ Cx
  snd_not_mem : ∀ i, (w i).2 ∉ Cz
  cover : ∀ e ∈ P ∪ (Ex \ (P ∪ A)), ¬ ((∃ i, (w i).1 = e.1) ∧ (∃ l, (w l).2 = e.2)) →
    e.1 ∈ Cx ∨ e.2 ∈ Cz

omit [DecidableEq X] [DecidableEq Z] in
/-- A witness stays a witness when more pairs are decided. -/
theorem IsWitness.mono {Ex P A P' A' : Finset (X × Z)} {k : ℕ} {w : Fin k → X × Z}
    (hw : IsWitness Ex P A w) (hP : P ⊆ P') (hA : A ⊆ A') : IsWitness Ex P' A' w where
  mem i := hP (hw.mem i)
  injective_fst := hw.injective_fst
  injective_snd := hw.injective_snd
  decided e he h1 h2 := (hw.decided e he h1 h2).imp (fun h => hP h) (fun h => hA h)

/-- A free pair `g ∈ F` does not lie in the rectangle of a witness. -/
theorem IsWitness.ne_of_free {Ex P A : Finset (X × Z)} {k : ℕ} {w : Fin k → X × Z}
    (hw : IsWitness Ex P A w) {g : X × Z} (hg : g ∈ Ex \ (P ∪ A)) (i l : Fin k) :
    ((w i).1, (w l).2) ≠ g := by
  rintro rfl
  obtain ⟨hgE, hgPA⟩ := mem_sdiff.1 hg
  exact hgPA (mem_union.2 (hw.decided _ hgE ⟨i, rfl⟩ ⟨l, rfl⟩))

/-- The arcs `i → l` (`i ≠ l`, `(j_i, k_l) ∈ P`) of the witness digraph `D_𝒞`
(`def:extraction:witness`(b)). -/
def ClassWitnessArc (P : Finset (X × Z)) {k : ℕ} (w : Fin k → X × Z) (i l : Fin k) : Prop :=
  i ≠ l ∧ ((w i).1, (w l).2) ∈ P

/-- **`lem:advance:compressed-partition`(c).** A witness of `𝒞(P, A)` is a witness of the child
`𝒞(P ∪ {g}, A)` (`g` free), with the same witness digraph. -/
theorem IsWitness.child_present {Ex P A : Finset (X × Z)} {k : ℕ} {w : Fin k → X × Z}
    (hw : IsWitness Ex P A w) {g : X × Z} (hg : g ∈ Ex \ (P ∪ A)) :
    IsWitness Ex (insert g P) A w ∧
      ∀ i l, ClassWitnessArc (insert g P) w i l ↔ ClassWitnessArc P w i l := by
  refine ⟨hw.mono (subset_insert g P) subset_rfl, fun i l => ?_⟩
  unfold ClassWitnessArc
  rw [mem_insert]
  have := hw.ne_of_free hg i l
  tauto

/-- **`lem:advance:compressed-partition`(c).** A witness of `𝒞(P, A)` is a witness of the child
`𝒞(P, A ∪ {g})`, with the same witness digraph (the present pairs do not change). -/
theorem IsWitness.child_absent {Ex P A : Finset (X × Z)} {k : ℕ} {w : Fin k → X × Z}
    (hw : IsWitness Ex P A w) (g : X × Z) : IsWitness Ex P (insert g A) w :=
  hw.mono subset_rfl (subset_insert g A)

/-- **`lem:advance:compressed-partition`(c).** A cover of `𝒞(P, A)` is a cover of the child
`𝒞(P ∪ {g}, A)` (`g` free). -/
theorem IsCover.child_present {Ex P A : Finset (X × Z)} {k : ℕ} {w : Fin k → X × Z}
    {Cx : Finset X} {Cz : Finset Z} (hc : IsCover Ex P A w Cx Cz) {g : X × Z}
    (hg : g ∈ Ex \ (P ∪ A)) : IsCover Ex (insert g P) A w Cx Cz where
  fst_not_mem := hc.fst_not_mem
  snd_not_mem := hc.snd_not_mem
  cover e he hout := by
    refine hc.cover e ?_ hout
    obtain ⟨hgE, hgPA⟩ := mem_sdiff.1 hg
    simp only [mem_union, mem_insert, mem_sdiff] at he hgPA ⊢
    rcases he with (rfl | he) | ⟨heE, he⟩
    · exact Or.inr ⟨hgE, hgPA⟩
    · exact Or.inl he
    · exact Or.inr ⟨heE, by tauto⟩

/-- **`lem:advance:compressed-partition`(c).** A cover of `𝒞(P, A)` is a cover of the child
`𝒞(P, A ∪ {g})`. -/
theorem IsCover.child_absent {Ex P A : Finset (X × Z)} {k : ℕ} {w : Fin k → X × Z}
    {Cx : Finset X} {Cz : Finset Z} (hc : IsCover Ex P A w Cx Cz) (g : X × Z) :
    IsCover Ex P (insert g A) w Cx Cz where
  fst_not_mem := hc.fst_not_mem
  snd_not_mem := hc.snd_not_mem
  cover e he hout := by
    refine hc.cover e ?_ hout
    simp only [mem_union, mem_insert, mem_sdiff] at he ⊢
    tauto

/-- `def:extraction:witness`(c): `(X \ V, Z \ W)` is always a cover. -/
theorem isCover_compl [Fintype X] [Fintype Z] (Ex P A : Finset (X × Z)) {k : ℕ}
    (w : Fin k → X × Z) :
    IsCover Ex P A w (univ.filter fun j => ∀ i, (w i).1 ≠ j)
      (univ.filter fun k' => ∀ i, (w i).2 ≠ k') where
  fst_not_mem i := by simp
  snd_not_mem i := by simp
  cover e _ hout := by
    simp only [mem_filter, mem_univ, true_and]
    by_contra h
    push Not at h
    obtain ⟨⟨i, hi⟩, ⟨l, hl⟩⟩ := h
    exact hout ⟨⟨i, hi⟩, ⟨l, hl⟩⟩

/-- A class is a *child* of another if it is obtained by deciding one free pair. -/
def IsChild (Ex : Finset (X × Z)) (c c' : Finset (X × Z) × Finset (X × Z)) : Prop :=
  ∃ g ∈ Ex \ (c.1 ∪ c.2), c' = (insert g c.1, c.2) ∨ c' = (c.1, insert g c.2)

/-- **`lem:advance:compressed-partition`(c).** A witness and a cover of a class are a witness
and a cover of every class obtained from it by deciding free pairs one at a time, with the same
witness digraph. -/
theorem IsWitness.refine {Ex : Finset (X × Z)} {c c' : Finset (X × Z) × Finset (X × Z)}
    {k : ℕ} {w : Fin k → X × Z} (hw : IsWitness Ex c.1 c.2 w)
    (hr : Relation.ReflTransGen (IsChild Ex) c c') :
    IsWitness Ex c'.1 c'.2 w ∧ ∀ i l, ClassWitnessArc c'.1 w i l ↔ ClassWitnessArc c.1 w i l := by
  induction hr with
  | refl => exact ⟨hw, fun _ _ => Iff.rfl⟩
  | tail _ hstep ih =>
    obtain ⟨hw', harc⟩ := ih
    obtain ⟨g, hg, rfl | rfl⟩ := hstep
    · obtain ⟨h1, h2⟩ := hw'.child_present hg
      exact ⟨h1, fun i l => (h2 i l).trans (harc i l)⟩
    · exact ⟨hw'.child_absent g, harc⟩

theorem IsCover.refine {Ex : Finset (X × Z)} {c c' : Finset (X × Z) × Finset (X × Z)}
    {k : ℕ} {w : Fin k → X × Z} {Cx : Finset X} {Cz : Finset Z}
    (hc : IsCover Ex c.1 c.2 w Cx Cz) (hr : Relation.ReflTransGen (IsChild Ex) c c') :
    IsCover Ex c'.1 c'.2 w Cx Cz := by
  induction hr with
  | refl => exact hc
  | tail _ hstep ih =>
    obtain ⟨g, hg, rfl | rfl⟩ := hstep
    · exact ih.child_present hg
    · exact ih.child_absent g

/-- Deciding pairs only enlarges `P` and `A`. -/
theorem IsChild.reflTransGen_subset {Ex : Finset (X × Z)}
    {c c' : Finset (X × Z) × Finset (X × Z)} (hr : Relation.ReflTransGen (IsChild Ex) c c') :
    c.1 ⊆ c'.1 ∧ c.2 ⊆ c'.2 := by
  induction hr with
  | refl => exact ⟨subset_rfl, subset_rfl⟩
  | tail _ hstep ih =>
    obtain ⟨g, -, rfl | rfl⟩ := hstep
    · exact ⟨ih.1.trans (subset_insert _ _), ih.2⟩
    · exact ⟨ih.1, ih.2.trans (subset_insert _ _)⟩

/-- **`lem:advance:compressed-partition`(c), last assertion.** If `k` pairs of `P` have distinct
`x`-endpoints and distinct `x'`-endpoints, they form a witness of size `k` of every class
obtained from `𝒞(P, A)` by deciding pairs one at a time once their rectangle is decided. -/
theorem isWitness_of_refine {Ex : Finset (X × Z)} {c c' : Finset (X × Z) × Finset (X × Z)}
    {k : ℕ} {w : Fin k → X × Z} (hmem : ∀ i, w i ∈ c.1)
    (hfst : Function.Injective fun i => (w i).1) (hsnd : Function.Injective fun i => (w i).2)
    (hr : Relation.ReflTransGen (IsChild Ex) c c')
    (hdec : ∀ e ∈ Ex, (∃ i, (w i).1 = e.1) → (∃ l, (w l).2 = e.2) → e ∈ c'.1 ∨ e ∈ c'.2) :
    IsWitness Ex c'.1 c'.2 w where
  mem i := (IsChild.reflTransGen_subset hr).1 (hmem i)
  injective_fst := hfst
  injective_snd := hsnd
  decided := hdec

/-! ### The compressed partition (`lem:advance:compressed-partition`(b)) -/

section Compressed

variable (ρ : X × Z → ℕ)

theorem mem_nonstars {Ex S : Finset (X × Z)} : S ∈ nonstars Ex ↔ S ⊆ Ex ∧ IsNonstar S := by
  rw [nonstars, mem_filter, mem_powerset]

omit [DecidableEq X] [DecidableEq Z] in
/-- `e` is the *first* pair of `T` for the order `g ≺ h ↔ ρ g < ρ h`. -/
def IsFirst (T : Finset (X × Z)) (e : X × Z) : Prop := e ∈ T ∧ ∀ g ∈ T, ρ e ≤ ρ g

omit [DecidableEq X] [DecidableEq Z] in
theorem exists_isFirst {T : Finset (X × Z)} (hT : T.Nonempty) : ∃ e, IsFirst ρ T e := by
  obtain ⟨e, he, hmin⟩ := T.exists_min_image ρ hT
  exact ⟨e, he, hmin⟩

omit [DecidableEq X] [DecidableEq Z] in
/-- The first pair is unique when `ρ` is injective on `Ex ⊇ T`. -/
theorem IsFirst.unique {Ex T : Finset (X × Z)} (hρ : Set.InjOn ρ ↑Ex) (hT : T ⊆ Ex)
    {e e' : X × Z} (h : IsFirst ρ T e) (h' : IsFirst ρ T e') : e = e' :=
  hρ (mem_coe.2 (hT h.1)) (mem_coe.2 (hT h'.1)) (le_antisymm (h.2 e' h'.1) (h'.2 e h.1))

/-- The *connectors* `Con = {(a, b'), (a', b)} ∩ Ex` of `e = (a, b)` and `f = (a', b')`. -/
def con (Ex : Finset (X × Z)) (e f : X × Z) : Finset (X × Z) :=
  Ex.filter fun g => g = (e.1, f.2) ∨ g = (f.1, e.2)

/-- The pairs `g ≠ e` of `T` with `x`-endpoint `e.1`. -/
def rowArms (T : Finset (X × Z)) (e : X × Z) : Finset (X × Z) :=
  T.filter fun g => g ≠ e ∧ g.1 = e.1

/-- The pairs `g ≠ e` of `T` with `x'`-endpoint `e.2`. -/
def colArms (T : Finset (X × Z)) (e : X × Z) : Finset (X × Z) :=
  T.filter fun g => g ≠ e ∧ g.2 = e.2

/-- The class datum `(P, A)` of case (A): `P = {e, f} ∪ (S ∩ Con)`,
`A = {g ≺ e} ∪ {g ≺ f : g disjoint from e} ∪ (Con \ S)` (pairs of `Ex`). -/
def datumA (Ex S : Finset (X × Z)) (e f : X × Z) : Finset (X × Z) × Finset (X × Z) :=
  ({e, f} ∪ (S ∩ con Ex e f),
    (Ex.filter fun g => ρ g < ρ e) ∪ (Ex.filter fun g => PairDisj e g ∧ ρ g < ρ f) ∪
      (con Ex e f \ S))

/-- The class datum `(P, A)` of case (B): `P = {e, g₁, g₂}`,
`A = {g ≺ e} ∪ A₁ ∪ A₂ ∪ {g : g disjoint from e}` (pairs of `Ex`). -/
def datumB (Ex : Finset (X × Z)) (e g₁ g₂ : X × Z) : Finset (X × Z) × Finset (X × Z) :=
  ({e, g₁, g₂},
    (Ex.filter fun g => ρ g < ρ e) ∪ ((rowArms Ex e).filter fun g => ρ g < ρ g₁) ∪
      ((colArms Ex e).filter fun g => ρ g < ρ g₂) ∪ (Ex.filter fun g => PairDisj e g))

/-- `c` is the compressed class datum of `S`: `e` is the first pair of `S`; in case (A) `f` is
the first pair of `S` disjoint from `e`; in case (B) (no pair of `S` is disjoint from `e`)
`g₁`, `g₂` are the first arms of the two kinds. -/
def IsCompressedDatum (Ex S : Finset (X × Z)) (c : Finset (X × Z) × Finset (X × Z)) : Prop :=
  ∃ e, IsFirst ρ S e ∧
    ((∃ f, IsFirst ρ (S.filter fun g => PairDisj e g) f ∧ c = datumA ρ Ex S e f) ∨
      ((∀ f ∈ S, ¬ PairDisj e f) ∧ ∃ g₁ g₂, IsFirst ρ (rowArms S e) g₁ ∧
        IsFirst ρ (colArms S e) g₂ ∧ c = datumB ρ Ex e g₁ g₂))

/-- **`lem:advance:compressed-partition`(b), case (B).** If no pair of the nonstar `S` is
disjoint from `e ∈ S`, then `S` contains, besides `e`, a pair with `x`-endpoint `e.1` and a pair
with `x'`-endpoint `e.2` (the arms of `e`). -/
theorem arms_nonempty {S : Finset (X × Z)} (hns : IsNonstar S) {e : X × Z}
    (hB : ∀ f ∈ S, ¬ PairDisj e f) : (rowArms S e).Nonempty ∧ (colArms S e).Nonempty := by
  constructor
  · have : ∃ g ∈ S, g.2 ≠ e.2 := by
      by_contra hcon
      push Not at hcon
      exact hns.2 (Or.inr (isColStar_iff.2 ⟨hns.1, e.2, hcon⟩))
    obtain ⟨g, hg, hg2⟩ := this
    have hg1 : g.1 = e.1 := by
      by_contra hne
      exact hB g hg ⟨Ne.symm hne, Ne.symm hg2⟩
    exact ⟨g, mem_filter.2 ⟨hg, fun h => hg2 (by rw [h]), hg1⟩⟩
  · have : ∃ g ∈ S, g.1 ≠ e.1 := by
      by_contra hcon
      push Not at hcon
      exact hns.2 (Or.inl (isRowStar_iff.2 ⟨hns.1, e.1, hcon⟩))
    obtain ⟨g, hg, hg1⟩ := this
    have hg2 : g.2 = e.2 := by
      by_contra hne
      exact hB g hg ⟨Ne.symm hg1, Ne.symm hne⟩
    exact ⟨g, mem_filter.2 ⟨hg, fun h => hg1 (by rw [h]), hg2⟩⟩

/-- **`lem:advance:compressed-partition`(b).** Every nonstar `S` has a compressed class datum:
it has a first pair `e`, and either case (A) or case (B) applies. -/
theorem exists_isCompressedDatum (Ex : Finset (X × Z)) {S : Finset (X × Z)}
    (hns : IsNonstar S) : ∃ c, IsCompressedDatum ρ Ex S c := by
  obtain ⟨e, he⟩ := exists_isFirst ρ hns.1
  by_cases hA : ∃ f ∈ S, PairDisj e f
  · obtain ⟨f, hf, hd⟩ := hA
    obtain ⟨f', hf'⟩ := exists_isFirst ρ (T := S.filter fun g => PairDisj e g)
      ⟨f, mem_filter.2 ⟨hf, hd⟩⟩
    exact ⟨_, e, he, Or.inl ⟨f', hf', rfl⟩⟩
  · push Not at hA
    obtain ⟨h1, h2⟩ := arms_nonempty hns hA
    obtain ⟨g₁, hg₁⟩ := exists_isFirst ρ h1
    obtain ⟨g₂, hg₂⟩ := exists_isFirst ρ h2
    exact ⟨_, e, he, Or.inr ⟨hA, g₁, g₂, hg₁, hg₂, rfl⟩⟩

/-- The compressed class datum is unique ("exactly one of (A), (B) holds, and it defines a
class"). -/
theorem IsCompressedDatum.unique {Ex S : Finset (X × Z)} (hρ : Set.InjOn ρ ↑Ex) (hS : S ⊆ Ex)
    {c c' : Finset (X × Z) × Finset (X × Z)} (h : IsCompressedDatum ρ Ex S c)
    (h' : IsCompressedDatum ρ Ex S c') : c = c' := by
  obtain ⟨e, he, hc⟩ := h
  obtain ⟨e', he', hc'⟩ := h'
  obtain rfl := IsFirst.unique ρ hρ hS he he'
  rcases hc with ⟨f, hf, rfl⟩ | ⟨hB, g₁, g₂, hg₁, hg₂, rfl⟩ <;>
    rcases hc' with ⟨f', hf', rfl⟩ | ⟨hB', g₁', g₂', hg₁', hg₂', rfl⟩
  · rw [IsFirst.unique ρ hρ ((filter_subset _ _).trans hS) hf hf']
  · exact absurd (mem_filter.1 hf.1).2 (hB' f (mem_filter.1 hf.1).1)
  · exact absurd (mem_filter.1 hf'.1).2 (hB f' (mem_filter.1 hf'.1).1)
  · rw [IsFirst.unique ρ hρ ((filter_subset _ _).trans hS) hg₁ hg₁',
      IsFirst.unique ρ hρ ((filter_subset _ _).trans hS) hg₂ hg₂']

/-- `S ∈ 𝒞(S)`. -/
theorem IsCompressedDatum.self_mem_cls {Ex S : Finset (X × Z)} (hS : S ⊆ Ex)
    {c : Finset (X × Z) × Finset (X × Z)} (h : IsCompressedDatum ρ Ex S c) :
    S ∈ cls Ex c.1 c.2 := by
  obtain ⟨e, he, ⟨f, hf, rfl⟩ | ⟨hB, g₁, g₂, hg₁, hg₂, rfl⟩⟩ := h
  · rw [mem_cls, subset_sdiff]
    dsimp only [datumA]
    refine ⟨?_, hS, disjoint_left.2 fun g hg hgA => ?_⟩
    · exact union_subset (insert_subset he.1 (singleton_subset_iff.2 (mem_filter.1 hf.1).1))
        inter_subset_left
    · simp only [mem_union, mem_filter, mem_sdiff] at hgA
      rcases hgA with (⟨-, hlt⟩ | ⟨-, hd, hlt⟩) | ⟨-, hgS⟩
      · exact absurd (he.2 g hg) (not_le.2 hlt)
      · exact absurd (hf.2 g (mem_filter.2 ⟨hg, hd⟩)) (not_le.2 hlt)
      · exact hgS hg
  · rw [mem_cls, subset_sdiff]
    dsimp only [datumB]
    refine ⟨?_, hS, disjoint_left.2 fun g hg hgA => ?_⟩
    · exact insert_subset he.1 (insert_subset (mem_filter.1 hg₁.1).1
        (singleton_subset_iff.2 (mem_filter.1 hg₂.1).1))
    · simp only [rowArms, colArms, mem_union, mem_filter] at hgA
      rcases hgA with ((⟨-, hlt⟩ | ⟨⟨-, hne, h1⟩, hlt⟩) | ⟨⟨-, hne, h2⟩, hlt⟩) | ⟨-, hd⟩
      · exact absurd (he.2 g hg) (not_le.2 hlt)
      · exact absurd (hg₁.2 g (mem_filter.2 ⟨hg, hne, h1⟩)) (not_le.2 hlt)
      · exact absurd (hg₂.2 g (mem_filter.2 ⟨hg, hne, h2⟩)) (not_le.2 hlt)
      · exact hB g hg hd

/-- **`lem:advance:compressed-partition`(b).** Every element `S'` of `𝒞(S)` is a nonstar whose
class datum is that of `S`. -/
theorem IsCompressedDatum.of_mem_cls {Ex S S' : Finset (X × Z)}
    {c : Finset (X × Z) × Finset (X × Z)} (h : IsCompressedDatum ρ Ex S c)
    (hS' : S' ∈ cls Ex c.1 c.2) : IsNonstar S' ∧ IsCompressedDatum ρ Ex S' c := by
  rw [mem_cls, subset_sdiff] at hS'
  obtain ⟨hP, hS'E, hdis⟩ := hS'
  have hnot : ∀ g ∈ S', g ∉ c.2 := fun g hg hgA => disjoint_left.1 hdis hg hgA
  obtain ⟨e, he, ⟨f, hf, rfl⟩ | ⟨hB, g₁, g₂, hg₁, hg₂, rfl⟩⟩ := h
  · dsimp only [datumA] at hP hnot
    have heS' : e ∈ S' := hP (mem_union_left _ (mem_insert_self e {f}))
    have hfS' : f ∈ S' := hP (mem_union_left _ (mem_insert_of_mem (mem_singleton_self f)))
    have hd : PairDisj e f := (mem_filter.1 hf.1).2
    have he' : IsFirst ρ S' e := ⟨heS', fun g hg => by
      by_contra hlt
      push Not at hlt
      exact hnot g hg (mem_union_left _ (mem_union_left _ (mem_filter.2 ⟨hS'E hg, hlt⟩)))⟩
    have hf' : IsFirst ρ (S'.filter fun g => PairDisj e g) f :=
      ⟨mem_filter.2 ⟨hfS', hd⟩, fun g hg => by
        obtain ⟨hgS', hdg⟩ := mem_filter.1 hg
        by_contra hlt
        push Not at hlt
        exact hnot g hgS'
          (mem_union_left _ (mem_union_right _ (mem_filter.2 ⟨hS'E hgS', hdg, hlt⟩)))⟩
    have hcon : ∀ x ∈ con Ex e f, (x ∈ S' ↔ x ∈ S) := by
      intro x hxc
      constructor
      · intro hxS'
        by_contra hxS
        exact hnot x hxS' (mem_union_right _ (mem_sdiff.2 ⟨hxc, hxS⟩))
      · intro hxS
        exact hP (mem_union_right _ (mem_inter.2 ⟨hxS, hxc⟩))
    have h1 : S' ∩ con Ex e f = S ∩ con Ex e f := by
      ext x
      simp only [mem_inter]
      constructor
      · rintro ⟨hx, hxc⟩; exact ⟨(hcon x hxc).1 hx, hxc⟩
      · rintro ⟨hx, hxc⟩; exact ⟨(hcon x hxc).2 hx, hxc⟩
    have h2 : con Ex e f \ S' = con Ex e f \ S := by
      ext x
      simp only [mem_sdiff]
      constructor
      · rintro ⟨hxc, hx⟩; exact ⟨hxc, fun h => hx ((hcon x hxc).2 h)⟩
      · rintro ⟨hxc, hx⟩; exact ⟨hxc, fun h => hx ((hcon x hxc).1 h)⟩
    refine ⟨isNonstar_iff.2 ⟨e, heS', f, hfS', hd⟩, e, he', Or.inl ⟨f, hf', ?_⟩⟩
    simp only [datumA, h1, h2]
  · dsimp only [datumB] at hP hnot
    have heS' : e ∈ S' := hP (mem_insert_self _ _)
    have hg₁S' : g₁ ∈ S' := hP (mem_insert_of_mem (mem_insert_self _ _))
    have hg₂S' : g₂ ∈ S' := hP (mem_insert_of_mem (mem_insert_of_mem (mem_singleton_self _)))
    obtain ⟨-, hg₁e, hg₁1⟩ := mem_filter.1 hg₁.1
    obtain ⟨-, hg₂e, hg₂2⟩ := mem_filter.1 hg₂.1
    have he' : IsFirst ρ S' e := ⟨heS', fun g hg => by
      by_contra hlt
      push Not at hlt
      exact hnot g hg (mem_union_left _ (mem_union_left _ (mem_union_left _
        (mem_filter.2 ⟨hS'E hg, hlt⟩))))⟩
    have hB' : ∀ f ∈ S', ¬ PairDisj e f := fun f hf hd =>
      hnot f hf (mem_union_right _ (mem_filter.2 ⟨hS'E hf, hd⟩))
    have hg₁' : IsFirst ρ (rowArms S' e) g₁ := ⟨mem_filter.2 ⟨hg₁S', hg₁e, hg₁1⟩, fun g hg => by
      obtain ⟨hgS', hge, hg1⟩ := mem_filter.1 hg
      by_contra hlt
      push Not at hlt
      exact hnot g hgS' (mem_union_left _ (mem_union_left _ (mem_union_right _
        (mem_filter.2 ⟨mem_filter.2 ⟨hS'E hgS', hge, hg1⟩, hlt⟩))))⟩
    have hg₂' : IsFirst ρ (colArms S' e) g₂ := ⟨mem_filter.2 ⟨hg₂S', hg₂e, hg₂2⟩, fun g hg => by
      obtain ⟨hgS', hge, hg2⟩ := mem_filter.1 hg
      by_contra hlt
      push Not at hlt
      exact hnot g hgS' (mem_union_left _ (mem_union_right _
        (mem_filter.2 ⟨mem_filter.2 ⟨hS'E hgS', hge, hg2⟩, hlt⟩)))⟩
    have hd : PairDisj g₁ g₂ := by
      refine ⟨fun h => hg₂e (Prod.ext ?_ hg₂2), fun h => hg₁e (Prod.ext hg₁1 ?_)⟩
      · rw [← h, hg₁1]
      · rw [h, hg₂2]
    exact ⟨isNonstar_iff.2 ⟨g₁, hg₁S', g₂, hg₂S', hd⟩, e, he', Or.inr ⟨hB', g₁, g₂, hg₁', hg₂', rfl⟩⟩

/-- The compressed class datum is a class datum (`P, A ⊆ Ex` disjoint). -/
theorem IsCompressedDatum.isClassDatum {Ex S : Finset (X × Z)} (hS : S ⊆ Ex)
    {c : Finset (X × Z) × Finset (X × Z)} (h : IsCompressedDatum ρ Ex S c) :
    IsClassDatum Ex c := by
  have hmem := IsCompressedDatum.self_mem_cls ρ hS h
  rw [mem_cls, subset_sdiff] at hmem
  refine ⟨hmem.1.trans hS, ?_, disjoint_of_subset_left hmem.1 hmem.2.2⟩
  obtain ⟨e, -, ⟨f, -, rfl⟩ | ⟨-, g₁, g₂, -, -, rfl⟩⟩ := h
  · intro x hx
    simp only [datumA, con, mem_union, mem_filter, mem_sdiff] at hx
    rcases hx with (⟨hx, -⟩ | ⟨hx, -⟩) | ⟨⟨hx, -⟩, -⟩ <;> exact hx
  · intro x hx
    simp only [datumB, rowArms, colArms, mem_union, mem_filter] at hx
    rcases hx with ((⟨hx, -⟩ | ⟨⟨hx, -⟩, -⟩) | ⟨⟨hx, -⟩, -⟩) | ⟨hx, -⟩ <;> exact hx

/-- The compressed class datum `𝒞(S)` of a nonstar `S` (a fixed choice; it is unique by
`IsCompressedDatum.unique`), and `(∅, ∅)` for other sets. -/
noncomputable def compressedDatum (Ex S : Finset (X × Z)) : Finset (X × Z) × Finset (X × Z) :=
  if h : IsNonstar S then Classical.choose (exists_isCompressedDatum ρ Ex h) else (∅, ∅)

theorem compressedDatum_spec (Ex : Finset (X × Z)) {S : Finset (X × Z)} (h : IsNonstar S) :
    IsCompressedDatum ρ Ex S (compressedDatum ρ Ex S) := by
  rw [compressedDatum, dite_eq_left h]
  exact Classical.choose_spec (exists_isCompressedDatum ρ Ex h)

/-- **`lem:advance:compressed-partition`(b).** Every element of `𝒞(S)` is a nonstar whose class
is `𝒞(S)`. -/
theorem compressedDatum_of_mem_cls {Ex S S' : Finset (X × Z)} (hρ : Set.InjOn ρ ↑Ex)
    (hS : IsNonstar S)
    (hS' : S' ∈ cls Ex (compressedDatum ρ Ex S).1 (compressedDatum ρ Ex S).2) :
    IsNonstar S' ∧ compressedDatum ρ Ex S' = compressedDatum ρ Ex S := by
  obtain ⟨hns', hc'⟩ := IsCompressedDatum.of_mem_cls ρ (compressedDatum_spec ρ Ex hS) hS'
  exact ⟨hns', IsCompressedDatum.unique ρ hρ ((mem_cls.1 hS').2.trans sdiff_subset)
    (compressedDatum_spec ρ Ex hns') hc'⟩

/-- The compressed partition: the distinct class data `𝒞(S)` of the nonstar subsets of `Ex`. -/
noncomputable def compressedPartition (Ex : Finset (X × Z)) :
    Finset (Finset (X × Z) × Finset (X × Z)) :=
  (nonstars Ex).image (compressedDatum ρ Ex)

/-- **`lem:advance:compressed-partition`(b).** The distinct classes `𝒞(S)` form an exact
partition of the nonstar subsets (for a total order on `Ex`, given by `ρ` injective on
`Ex`). -/
theorem isExactPartition_compressedPartition {Ex : Finset (X × Z)} (hρ : Set.InjOn ρ ↑Ex) :
    IsExactPartition Ex (compressedPartition ρ Ex) (nonstars Ex) := by
  refine ⟨?_, ?_, ?_⟩
  · intro c hc
    obtain ⟨S, hS, rfl⟩ := mem_image.1 hc
    obtain ⟨hSE, hns⟩ := mem_nonstars.1 hS
    exact IsCompressedDatum.isClassDatum ρ hSE (compressedDatum_spec ρ Ex hns)
  · intro c hc c' hc' hne
    obtain ⟨S₁, hS₁, rfl⟩ := mem_image.1 (mem_coe.1 hc)
    obtain ⟨S₂, hS₂, rfl⟩ := mem_image.1 (mem_coe.1 hc')
    simp only [Function.onFun]
    rw [disjoint_left]
    intro S' h1 h2
    obtain ⟨-, e1⟩ := compressedDatum_of_mem_cls ρ hρ (mem_nonstars.1 hS₁).2 h1
    obtain ⟨-, e2⟩ := compressedDatum_of_mem_cls ρ hρ (mem_nonstars.1 hS₂).2 h2
    exact hne (e1.symm.trans e2)
  · ext S'
    simp only [mem_biUnion, compressedPartition, mem_image]
    constructor
    · rintro ⟨c, ⟨S, hS, rfl⟩, hS'⟩
      obtain ⟨hns', -⟩ := compressedDatum_of_mem_cls ρ hρ (mem_nonstars.1 hS).2 hS'
      exact mem_nonstars.2 ⟨(mem_cls.1 hS').2.trans sdiff_subset, hns'⟩
    · intro hS'
      refine ⟨_, ⟨S', hS', rfl⟩, ?_⟩
      exact IsCompressedDatum.self_mem_cls ρ (mem_nonstars.1 hS').1
        (compressedDatum_spec ρ Ex (mem_nonstars.1 hS').2)

/-- `lem:advance:compressed-partition`(a) for the compressed partition: the masses of its
classes add up to `2^{m_×}` minus the number of empty and star subsets. -/
theorem sum_mass_compressedPartition [Fintype X] [Fintype Z] {Ex : Finset (X × Z)}
    (hρ : Set.InjOn ρ ↑Ex) :
    ∑ c ∈ compressedPartition ρ Ex, 2 ^ #(Ex \ (c.1 ∪ c.2)) =
      2 ^ #Ex - (1 + #Ex + ∑ j : X, (2 ^ rowDeg Ex j - 1 - rowDeg Ex j) +
        ∑ k : Z, (2 ^ colDeg Ex k - 1 - colDeg Ex k)) :=
  (isExactPartition_compressedPartition ρ hρ).sum_mass

/-! ### The witnesses of size two of the compressed classes -/

omit [DecidableEq X] [DecidableEq Z] in
theorem injective_fin_two {β : Type*} {u : Fin 2 → β} (h : u 0 ≠ u 1) :
    Function.Injective u := by
  intro i j hij
  fin_cases i <;> fin_cases j
  · rfl
  · exact absurd hij h
  · exact absurd hij.symm h
  · rfl

/-- **`lem:advance:compressed-partition`(b), case (A).** The pairs `e, f` form a witness of size
two of `𝒞(S)`. -/
theorem isWitness_datumA (Ex S : Finset (X × Z)) {e f : X × Z} (hd : PairDisj e f) :
    IsWitness Ex (datumA ρ Ex S e f).1 (datumA ρ Ex S e f).2 ![e, f] where
  mem i := by
    fin_cases i <;> simp [datumA]
  injective_fst := injective_fin_two (by simpa using hd.1)
  injective_snd := injective_fin_two (by simpa using hd.2)
  decided x hx h1 h2 := by
    rw [Fin.exists_fin_two] at h1 h2
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h1 h2
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · have : x = e := Prod.ext h1.symm h2.symm
      subst this
      left
      simp [datumA]
    · have : x = (e.1, f.2) := Prod.ext h1.symm h2.symm
      subst this
      by_cases hxS : (e.1, f.2) ∈ S
      · left; simp [datumA, con, hxS, hx]
      · right; simp [datumA, con, hxS, hx]
    · have : x = (f.1, e.2) := Prod.ext h1.symm h2.symm
      subst this
      by_cases hxS : (f.1, e.2) ∈ S
      · left; simp [datumA, con, hxS, hx]
      · right; simp [datumA, con, hxS, hx]
    · have : x = f := Prod.ext h1.symm h2.symm
      subst this
      left
      simp [datumA]

/-- **`lem:advance:compressed-partition`(b), case (A).** The witness digraph of `(e, f)` has the
arc `1 → 2` iff the connector `(a, b')` is present and the arc `2 → 1` iff `(a', b)` is
present; so it is a two-cycle iff both connectors are present, and acyclic otherwise. -/
theorem witnessArc_datumA {Ex S : Finset (X × Z)} (hS : S ⊆ Ex) {e f : X × Z}
    (hd : PairDisj e f) :
    (ClassWitnessArc (datumA ρ Ex S e f).1 ![e, f] 0 1 ↔ (e.1, f.2) ∈ S) ∧
      (ClassWitnessArc (datumA ρ Ex S e f).1 ![e, f] 1 0 ↔ (f.1, e.2) ∈ S) := by
  have key : ∀ x, x ≠ e → x ≠ f →
      (x ∈ (datumA ρ Ex S e f).1 ↔ x ∈ S ∧ x ∈ con Ex e f) := by
    intro x hxe hxf
    simp only [datumA, mem_union, mem_insert, mem_singleton, mem_inter, hxe, hxf, false_or]
  have h1 : (e.1, f.2) ≠ e := fun h => hd.2 (congrArg Prod.snd h).symm
  have h2 : (e.1, f.2) ≠ f := fun h => hd.1 (Prod.ext_iff.1 h).1
  have h3 : (f.1, e.2) ≠ e := fun h => hd.1 (congrArg Prod.fst h).symm
  have h4 : (f.1, e.2) ≠ f := fun h => hd.2 (Prod.ext_iff.1 h).2
  have h01 : (0 : Fin 2) ≠ 1 := by decide
  unfold ClassWitnessArc
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  rw [key _ h1 h2, key _ h3 h4]
  constructor
  · constructor
    · rintro ⟨-, h, -⟩; exact h
    · intro h; exact ⟨h01, h, mem_filter.2 ⟨hS h, Or.inl rfl⟩⟩
  · constructor
    · rintro ⟨-, h, -⟩; exact h
    · intro h; exact ⟨h01.symm, h, mem_filter.2 ⟨hS h, Or.inr rfl⟩⟩

/-- **`lem:advance:compressed-partition`(b), case (B).** The arms `g₁, g₂` form a witness of
size two of `𝒞(S)`. -/
theorem isWitness_datumB (Ex : Finset (X × Z)) {S : Finset (X × Z)} {e g₁ g₂ : X × Z}
    (hg₁ : g₁ ∈ rowArms S e) (hg₂ : g₂ ∈ colArms S e) :
    IsWitness Ex (datumB ρ Ex e g₁ g₂).1 (datumB ρ Ex e g₁ g₂).2 ![g₁, g₂] := by
  obtain ⟨-, hg₁e, hg₁1⟩ := mem_filter.1 hg₁
  obtain ⟨-, hg₂e, hg₂2⟩ := mem_filter.1 hg₂
  have hg₁2 : g₁.2 ≠ e.2 := fun h => hg₁e (Prod.ext hg₁1 h)
  have hg₂1 : g₂.1 ≠ e.1 := fun h => hg₂e (Prod.ext h hg₂2)
  refine ⟨fun i => ?_, injective_fin_two ?_, injective_fin_two ?_, fun x hx h1 h2 => ?_⟩
  · fin_cases i <;> simp [datumB]
  · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [hg₁1]
    exact Ne.symm hg₂1
  · simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [hg₂2]
    exact hg₁2
  · rw [Fin.exists_fin_two] at h1 h2
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at h1 h2
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · have : x = g₁ := Prod.ext h1.symm h2.symm
      subst this
      left
      simp [datumB]
    · have : x = e := Prod.ext (h1.symm.trans hg₁1) (h2.symm.trans hg₂2)
      subst this
      left
      simp [datumB]
    · have hdx : PairDisj e x := ⟨fun h => hg₂1 (h1.trans h.symm), fun h => hg₁2 (h2.trans h.symm)⟩
      right
      simp only [datumB, mem_union, mem_filter]
      exact Or.inr ⟨hx, hdx⟩
    · have : x = g₂ := Prod.ext h1.symm h2.symm
      subst this
      left
      simp [datumB]

/-- **`lem:advance:compressed-partition`(b), case (B).** The witness digraph of `(g₁, g₂)` has
the arc `1 → 2` (the present pair `e`) and not the arc `2 → 1`; it is acyclic. -/
theorem witnessArc_datumB (Ex : Finset (X × Z)) {S : Finset (X × Z)} {e g₁ g₂ : X × Z}
    (hg₁ : g₁ ∈ rowArms S e) (hg₂ : g₂ ∈ colArms S e) :
    ClassWitnessArc (datumB ρ Ex e g₁ g₂).1 ![g₁, g₂] 0 1 ∧
      ¬ ClassWitnessArc (datumB ρ Ex e g₁ g₂).1 ![g₁, g₂] 1 0 := by
  obtain ⟨-, hg₁e, hg₁1⟩ := mem_filter.1 hg₁
  obtain ⟨-, hg₂e, hg₂2⟩ := mem_filter.1 hg₂
  have hg₁2 : g₁.2 ≠ e.2 := fun h => hg₁e (Prod.ext hg₁1 h)
  have hg₂1 : g₂.1 ≠ e.1 := fun h => hg₂e (Prod.ext h hg₂2)
  unfold ClassWitnessArc
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
  refine ⟨⟨by decide, ?_⟩, ?_⟩
  · have : (g₁.1, g₂.2) = e := Prod.ext hg₁1 hg₂2
    rw [this]
    simp [datumB]
  · rintro ⟨-, h⟩
    simp only [datumB, mem_insert, mem_singleton] at h
    rcases h with h | h | h
    · exact hg₂1 (Prod.ext_iff.1 h).1
    · exact hg₂1 ((congrArg Prod.fst h).trans hg₁1)
    · exact hg₁2 ((Prod.ext_iff.1 h).2.trans hg₂2)

/-- **`lem:advance:compressed-partition`(b).** Every compressed class has a witness of size
two: `(e, f)` in case (A), `(g₁, g₂)` in case (B). -/
theorem IsCompressedDatum.exists_witness {Ex S : Finset (X × Z)}
    {c : Finset (X × Z) × Finset (X × Z)} (h : IsCompressedDatum ρ Ex S c) :
    ∃ w : Fin 2 → X × Z, IsWitness Ex c.1 c.2 w := by
  obtain ⟨e, -, ⟨f, hf, rfl⟩ | ⟨-, g₁, g₂, hg₁, hg₂, rfl⟩⟩ := h
  · exact ⟨_, isWitness_datumA ρ Ex S (mem_filter.1 hf.1).2⟩
  · exact ⟨_, isWitness_datumB ρ Ex hg₁.1 hg₂.1⟩

/-- **`lem:advance:compressed-partition`(b), the witness digraph.** A compressed class `𝒞(S)`
has a witness `w` of size two (`(e, f)` in case (A), `(g₁, g₂)` in case (B)) whose digraph is a
two-cycle (both arcs) iff `S` is in case (A) with both connectors present; otherwise the digraph
is acyclic (on two vertices: not both arcs). -/
theorem IsCompressedDatum.exists_witness_twoCycle_iff {Ex S : Finset (X × Z)}
    (hρ : Set.InjOn ρ ↑Ex) (hS : S ⊆ Ex) {c : Finset (X × Z) × Finset (X × Z)}
    (h : IsCompressedDatum ρ Ex S c) :
    ∃ w : Fin 2 → X × Z, IsWitness Ex c.1 c.2 w ∧
      ((ClassWitnessArc c.1 w 0 1 ∧ ClassWitnessArc c.1 w 1 0) ↔
        ∃ e f, IsFirst ρ S e ∧ IsFirst ρ (S.filter fun g => PairDisj e g) f ∧
          (e.1, f.2) ∈ S ∧ (f.1, e.2) ∈ S) := by
  obtain ⟨e, he, ⟨f, hf, rfl⟩ | ⟨hB, g₁, g₂, hg₁, hg₂, rfl⟩⟩ := h
  · have hd : PairDisj e f := (mem_filter.1 hf.1).2
    refine ⟨![e, f], isWitness_datumA ρ Ex S hd, ?_⟩
    obtain ⟨h01, h10⟩ := witnessArc_datumA ρ hS hd
    rw [h01, h10]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨e, f, he, hf, h1, h2⟩
    · rintro ⟨e', f', he', hf', h1, h2⟩
      obtain rfl := IsFirst.unique ρ hρ hS he he'
      obtain rfl := IsFirst.unique ρ hρ ((filter_subset _ _).trans hS) hf hf'
      exact ⟨h1, h2⟩
  · refine ⟨![g₁, g₂], isWitness_datumB ρ Ex hg₁.1 hg₂.1, ?_⟩
    have harc := witnessArc_datumB ρ Ex hg₁.1 hg₂.1
    constructor
    · rintro ⟨-, h⟩
      exact absurd h harc.2
    · rintro ⟨e', f', he', hf', -, -⟩
      obtain rfl := IsFirst.unique ρ hρ hS he he'
      exact absurd (mem_filter.1 hf'.1).2 (hB f' (mem_filter.1 hf'.1).1)

/-- The class `𝒞(S)` of a nonstar `S ⊆ Ex` in the compressed partition has a witness of size
two. -/
theorem compressedDatum_exists_witness (Ex : Finset (X × Z)) {S : Finset (X × Z)}
    (hS : IsNonstar S) :
    ∃ w : Fin 2 → X × Z, IsWitness Ex (compressedDatum ρ Ex S).1 (compressedDatum ρ Ex S).2 w :=
  IsCompressedDatum.exists_witness ρ (compressedDatum_spec ρ Ex hS)

end Compressed

end Sarkozy.Extraction
