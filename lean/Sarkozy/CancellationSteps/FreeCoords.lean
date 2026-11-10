module

public import Sarkozy.CancellationSteps.Reindex
public import Sarkozy.Cancellation.PaperEncoding
public import Sarkozy.Cancellation.FibreRestriction

/-!
# The free coordinates of Step 3 inside the joined group

`paper/sections/08_scale_comparison.tex`, `lem:record:density-can`, Step 3. At a low support
`U` of the tail primes `p ≥ P₅`, the conditioned atoms are the prefix, the tail primes below `P₅`
and the primes of `U`; the free coordinates are the tail primes `p ≥ P₅` outside `U`. WP-K's
`FibreData` indexes them by `{k : TailIdx // U k = false}`; the fibre formula
(`Cancellation.groupCoeff_input_free`, from WP-FI's `groupCoeff_input_freeze`) is stated on the
free coordinates `{c // c ∉ E}` of the joined group `G_N = ResidueSpace (joinModuli m₀ (p L))`.

* `frozenCoords`, `freeEquiv`: the frozen set `E` and `{k // U k = false} ≃ {c // c ∉ E}`;
* `atomGroupEquiv_mergeAt_freeze`: the encoded label `mergeAt x (mergeFree U y x')` of
  `PaperEncoding` is the frozen label `coordinateFreeze E z (extendFree (reindex x'))`, with
  `z` the label of `mergeAt x y`.

New material for this paper.
-/

@[expose] public section

namespace Sarkozy.CancellationSteps

open Finset Complex
open scoped BigOperators ComplexConjugate
open Sarkozy.Cancellation Sarkozy.Mixing Sarkozy.PaperFrame Sarkozy.FourierArithmetic
  Sarkozy.Functional

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] (m₀ : J₀ → ℕ) [∀ i, NeZero (m₀ i)]
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] (p : ∀ L, J L → ℕ)
  [∀ L j, NeZero (p L j)]

/-- A free coordinate of Step 3 at the low support `U`: a tail prime `p ≥ P₅` outside `U`. -/
def IsFreeCoord (L P5 : ℕ) (U : TailIdx p L P5 → Bool) : J₀ ⊕ J L → Prop
  | Sum.inl _ => False
  | Sum.inr j => ∃ h : P5 ≤ p L j, U ⟨j, h⟩ = false

instance (L P5 : ℕ) (U : TailIdx p L P5 → Bool) :
    DecidablePred (IsFreeCoord (J₀ := J₀) p L P5 U) := fun c => by
  cases c <;> unfold IsFreeCoord <;> infer_instance

/-- The frozen coordinates of Step 3: the prefix, the tail primes below `P₅` and those of `U`. -/
def frozenCoords (L P5 : ℕ) (U : TailIdx p L P5 → Bool) : Finset (J₀ ⊕ J L) :=
  univ.filter (fun c => ¬ IsFreeCoord (J₀ := J₀) p L P5 U c)

omit [DecidableEq J₀] [∀ L, DecidableEq (J L)] [∀ L j, NeZero (p L j)] in
lemma not_mem_frozenCoords (L P5 : ℕ) (U : TailIdx p L P5 → Bool) (c : J₀ ⊕ J L) :
    c ∉ frozenCoords (J₀ := J₀) p L P5 U ↔ IsFreeCoord (J₀ := J₀) p L P5 U c := by
  simp [frozenCoords]

/-- The free tail primes as the free coordinates of the joined group. -/
def freeEquiv (L P5 : ℕ) (U : TailIdx p L P5 → Bool) :
    {k : TailIdx p L P5 // U k = false} ≃
      {c : J₀ ⊕ J L // c ∉ frozenCoords (J₀ := J₀) p L P5 U} where
  toFun k := ⟨Sum.inr k.1.1, (not_mem_frozenCoords p L P5 U _).mpr ⟨k.1.2, k.2⟩⟩
  invFun c := match c with
    | ⟨Sum.inl _, hc⟩ => absurd ((not_mem_frozenCoords p L P5 U _).mp hc) id
    | ⟨Sum.inr j, hc⟩ =>
      ⟨⟨j, ((not_mem_frozenCoords p L P5 U _).mp hc).fst⟩,
        ((not_mem_frozenCoords p L P5 U _).mp hc).snd⟩
  left_inv k := rfl
  right_inv c := by
    match c with
    | ⟨Sum.inl _, hc⟩ => exact absurd ((not_mem_frozenCoords p L P5 U _).mp hc) id
    | ⟨Sum.inr j, hc⟩ => rfl

/-- The moduli of the free coordinates of the joined group. -/
abbrev freeJoinModuli (L P5 : ℕ) (U : TailIdx p L P5 → Bool) :
    {c : J₀ ⊕ J L // c ∉ frozenCoords (J₀ := J₀) p L P5 U} → ℕ :=
  Cancellation.freeModuli (joinModuli m₀ (p L)) (frozenCoords (J₀ := J₀) p L P5 U)

/-- The free labels of `FibreData` as free labels of the joined group. -/
noncomputable def freeLabel (L P5 : ℕ) (U : TailIdx p L P5 → Bool) :
    ResidueSpace (fun k : {k : TailIdx p L P5 // U k = false} => tailQ p L P5 k.1) ≃
      ResidueSpace (freeJoinModuli m₀ p L P5 U) :=
  reindexLabel (freeEquiv (J₀ := J₀) p L P5 U) (freeJoinModuli m₀ p L P5 U)

omit [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] [∀ L j, NeZero (p L j)] in
lemma isLow_none (L P5 : ℕ) : IsLow p L P5 (none : PaperAtom J L) := fun j h => by cases h

omit [Fintype J₀] [DecidableEq J₀] [∀ i, NeZero (m₀ i)] [∀ L j, NeZero (p L j)] in
lemma mergeAt_low (L P5 : ℕ)
    (xw : ∀ i : {b : PaperAtom J L // IsLow p L P5 b}, AtomLabel m₀ p L i.1)
    (a : ∀ k : TailIdx p L P5, ZMod (tailQ p L P5 k)) (b : PaperAtom J L) (hb : IsLow p L P5 b) :
    mergeAt m₀ p L P5 xw a b = xw ⟨b, hb⟩ := by
  unfold mergeAt
  rw [Equiv.piEquivPiSubtypeProd_symm_apply]
  simp only [hb, ↓reduceDIte]

omit [Fintype J₀] [DecidableEq J₀] [∀ i, NeZero (m₀ i)] [∀ L j, NeZero (p L j)] in
lemma mergeAt_tail (L P5 : ℕ)
    (xw : ∀ i : {b : PaperAtom J L // IsLow p L P5 b}, AtomLabel m₀ p L i.1)
    (a : ∀ k : TailIdx p L P5, ZMod (tailQ p L P5 k)) (k : TailIdx p L P5) :
    mergeAt m₀ p L P5 xw a (some k.1) = a k := by
  unfold mergeAt
  rw [Equiv.piEquivPiSubtypeProd_symm_apply]
  have hb : ¬ IsLow p L P5 (some k.1) := fun h => absurd (h k.1 rfl) (not_lt.mpr k.2)
  simp only [hb, ↓reduceDIte]
  exact Equiv.piCongrLeft_apply_apply
    (fun i : {b // ¬ IsLow p L P5 b} => AtomLabel m₀ p L i.1) (tailEquiv p L P5) a k

omit [∀ i, NeZero (m₀ i)] [∀ L j, NeZero (p L j)] in
/-- **The encoded label is a frozen label**: `mergeAt x (mergeFree U y x')`, read in `G_N`, is the
label of `mergeAt x y` with the free coordinates replaced by `x'`. -/
theorem atomGroupEquiv_mergeAt_freeze (L P5 : ℕ) (U : TailIdx p L P5 → Bool)
    (xw : ∀ i : {b : PaperAtom J L // IsLow p L P5 b}, AtomLabel m₀ p L i.1)
    (y₀ : ∀ k : TailIdx p L P5, ZMod (tailQ p L P5 k))
    (x' : ResidueSpace (fun k : {k : TailIdx p L P5 // U k = false} => tailQ p L P5 k.1)) :
    atomGroupEquiv m₀ p L (mergeAt m₀ p L P5 xw (mergeFree U y₀ x')) =
      coordinateFreeze (joinModuli m₀ (p L)) (frozenCoords (J₀ := J₀) p L P5 U)
        (atomGroupEquiv m₀ p L (mergeAt m₀ p L P5 xw y₀))
        (Cancellation.extendFree (joinModuli m₀ (p L)) (frozenCoords (J₀ := J₀) p L P5 U)
          (freeLabel m₀ p L P5 U x')) := by
  funext c
  unfold coordinateFreeze
  rcases c with i | j
  · have hmem : (Sum.inl i : J₀ ⊕ J L) ∈ frozenCoords (J₀ := J₀) p L P5 U := by
      by_contra h
      exact (not_mem_frozenCoords p L P5 U _).mp h
    simp only [hmem, ↓reduceIte, atomGroupEquiv_apply, atomEquiv]
    show mergeAt m₀ p L P5 xw (mergeFree U y₀ x') none i = mergeAt m₀ p L P5 xw y₀ none i
    rw [mergeAt_low m₀ p L P5 xw _ none (isLow_none p L P5),
      mergeAt_low m₀ p L P5 xw _ none (isLow_none p L P5)]
  · by_cases hj : P5 ≤ p L j
    · set k : TailIdx p L P5 := ⟨j, hj⟩ with hk
      show mergeAt m₀ p L P5 xw (mergeFree U y₀ x') (some k.1) = _
      rw [mergeAt_tail]
      by_cases hU : U k = false
      · have hfree : (Sum.inr j : J₀ ⊕ J L) ∉ frozenCoords (J₀ := J₀) p L P5 U :=
          (not_mem_frozenCoords p L P5 U _).mpr ⟨hj, hU⟩
        simp only [hfree, ↓reduceIte]
        rw [mergeFree_free U y₀ x' ⟨k, hU⟩]
        unfold Cancellation.extendFree
        simp only [hfree, ↓reduceDIte]
        exact (reindexLabel_apply (freeEquiv (J₀ := J₀) p L P5 U) (freeJoinModuli m₀ p L P5 U) x'
          ⟨k, hU⟩).symm
      · have hUt : U k = true := by simpa using hU
        have hmem : (Sum.inr j : J₀ ⊕ J L) ∈ frozenCoords (J₀ := J₀) p L P5 U := by
          by_contra h
          obtain ⟨h1, h2⟩ := (not_mem_frozenCoords p L P5 U _).mp h
          exact hU h2
        simp only [hmem, ↓reduceIte]
        rw [mergeFree_fixed U y₀ x' hUt]
        show y₀ k = mergeAt m₀ p L P5 xw y₀ (some k.1)
        rw [mergeAt_tail]
    · have hlow : IsLow p L P5 (some j) := fun j' h => by
        cases h
        exact lt_of_not_ge hj
      have hmem : (Sum.inr j : J₀ ⊕ J L) ∈ frozenCoords (J₀ := J₀) p L P5 U := by
        by_contra h
        obtain ⟨h1, _⟩ := (not_mem_frozenCoords p L P5 U _).mp h
        exact hj h1
      simp only [hmem, ↓reduceIte]
      show mergeAt m₀ p L P5 xw (mergeFree U y₀ x') (some j) = mergeAt m₀ p L P5 xw y₀ (some j)
      rw [mergeAt_low m₀ p L P5 xw _ _ hlow, mergeAt_low m₀ p L P5 xw _ _ hlow]

end Sarkozy.CancellationSteps
