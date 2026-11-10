module

public import Sarkozy.PaperFrame.Atoms
public import Sarkozy.Functional.FibreRestoration

@[expose] public section

/-!
# Two scales: the lift at a smaller scale inside `G_N` (`lem:record:fibre-scale`(c))

The comparison worker's paper model (`Comparison/PaperMain.lean`) has a fixed prefix and a
tail of primes at every scale. Here the tail at the scale `L` is the set `T L` of primes,
`J L = ↥(T L)`, `p L j = j` (`tailModuli`). For a smaller scale `ℓ` with `T ℓ ⊆ T L`, the
coordinates of `G_n` (scale `ℓ`) are a subset of those of `G_N` (scale `L`), and

* `restrictScale`: `G_N → G_n` forgets the tail primes of `T L \ T ℓ`;
* `extendScale`: a character label of `G_n` extended by `0` is a label of `G_N`;
* `lift_restrictScale`: if every prime of `T L \ T ℓ` exceeds the cutoff `Q`, the lift
  with cutoff `Q` on `G_N` is the lift with the same cutoff on `G_n`, read on the
  `G_n`-coordinates (the paper's "a character with `q ≤ n^β` involves only primes at most
  `n^β`" in the proof of `lem:record:fibre-scale`(c)).

The `restrictScale`/`extendScale` maps act definitionally on the coordinate types (the
modulus of a tail coordinate is the prime itself at both scales), so no casts are needed.
-/

open Finset Function
open scoped BigOperators ComplexConjugate

namespace Sarkozy.PaperFrame

open Sarkozy.FourierArithmetic Sarkozy.Functional

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] (m₀ : J₀ → ℕ) [∀ i, NeZero (m₀ i)]
  (T : ℕ → Finset ℕ) [∀ L (j : ↥(T L)), NeZero (j : ℕ)]

/-- The tail moduli at the scale `L`: the primes of `T L`. -/
abbrev tailModuli (L : ℕ) : ↥(T L) → ℕ := fun j => (j : ℕ)

/-- The group `G_N` at the scale `L` (prefix ⊕ tail coordinates). -/
abbrev ScaleGroup (L : ℕ) : Type := ResidueSpace (joinModuli m₀ (tailModuli T L))

/-- The tail coordinate of `ℓ` inside the tail of `L`. -/
def tailEmbed {ℓ L : ℕ} (hT : T ℓ ⊆ T L) (j : ↥(T ℓ)) : ↥(T L) := ⟨j.1, hT j.2⟩

omit [∀ L (j : ↥(T L)), NeZero (j : ℕ)] in
theorem tailEmbed_injective {ℓ L : ℕ} (hT : T ℓ ⊆ T L) : Injective (tailEmbed T hT) := by
  intro a b h
  apply Subtype.ext
  have := congrArg Subtype.val h
  exact this

/-- Forgetting the tail primes of `T L \ T ℓ`: `G_N → G_n`. -/
def restrictScale {ℓ L : ℕ} (hT : T ℓ ⊆ T L) (y : ScaleGroup m₀ T L) : ScaleGroup m₀ T ℓ :=
  fun k => match k with
    | Sum.inl i => y (Sum.inl i)
    | Sum.inr j => y (Sum.inr (tailEmbed T hT j))

/-- Extending a label of `G_n` by zero on the tail primes of `T L \ T ℓ`. -/
noncomputable def extendScale (ℓ L : ℕ) (a : ScaleGroup m₀ T ℓ) : ScaleGroup m₀ T L :=
  fun k => match k with
    | Sum.inl i => a (Sum.inl i)
    | Sum.inr j => if h : (j : ℕ) ∈ T ℓ then a (Sum.inr ⟨j.1, h⟩) else 0

omit [DecidableEq J₀] [Fintype J₀] [∀ i, NeZero (m₀ i)] [∀ L (j : ↥(T L)), NeZero (j : ℕ)] in
theorem restrictScale_extendScale {ℓ L : ℕ} (hT : T ℓ ⊆ T L) (a : ScaleGroup m₀ T ℓ) :
    restrictScale m₀ T hT (extendScale m₀ T ℓ L a) = a := by
  funext k
  match k with
  | Sum.inl i => rfl
  | Sum.inr j =>
    change (if h : (j : ℕ) ∈ T ℓ then a (Sum.inr ⟨j.1, h⟩) else 0) = a (Sum.inr j)
    rw [dite_eq_left j.2]

omit [DecidableEq J₀] [Fintype J₀] [∀ i, NeZero (m₀ i)] [∀ L (j : ↥(T L)), NeZero (j : ℕ)] in
theorem extendScale_restrictScale {ℓ L : ℕ} (hT : T ℓ ⊆ T L) {b : ScaleGroup m₀ T L}
    (hb : ∀ j : ↥(T L), (j : ℕ) ∉ T ℓ → b (Sum.inr j) = 0) :
    extendScale m₀ T ℓ L (restrictScale m₀ T hT b) = b := by
  funext k
  match k with
  | Sum.inl i => rfl
  | Sum.inr j =>
    change (if h : (j : ℕ) ∈ T ℓ then b (Sum.inr ⟨j.1, hT h⟩) else 0) = b (Sum.inr j)
    by_cases h : (j : ℕ) ∈ T ℓ
    · rw [dite_eq_left h]
    · rw [dite_eq_right h, hb j h]

omit [Fintype J₀] [DecidableEq J₀] [∀ i, NeZero (m₀ i)] [∀ L (j : ↥(T L)), NeZero (j : ℕ)] in
theorem restrictScale_integerResidue {ℓ L : ℕ} (hT : T ℓ ⊆ T L) (n : ℤ) :
    restrictScale m₀ T hT (integerResidue (joinModuli m₀ (tailModuli T L)) n) =
      integerResidue (joinModuli m₀ (tailModuli T ℓ)) n := by
  funext k
  match k with
  | Sum.inl i => rfl
  | Sum.inr j => rfl

omit [Fintype J₀] [DecidableEq J₀] [∀ i, NeZero (m₀ i)] [∀ L (j : ↥(T L)), NeZero (j : ℕ)] in
theorem extendScale_inl (ℓ L : ℕ) (a : ScaleGroup m₀ T ℓ) (i : J₀) :
    extendScale m₀ T ℓ L a (Sum.inl i) = a (Sum.inl i) := rfl

omit [Fintype J₀] [DecidableEq J₀] [∀ i, NeZero (m₀ i)] [∀ L (j : ↥(T L)), NeZero (j : ℕ)] in
theorem extendScale_inr_embed {ℓ L : ℕ} (hT : T ℓ ⊆ T L) (a : ScaleGroup m₀ T ℓ)
    (j : ↥(T ℓ)) : extendScale m₀ T ℓ L a (Sum.inr (tailEmbed T hT j)) = a (Sum.inr j) := by
  show (if h : (j : ℕ) ∈ T ℓ then a (Sum.inr ⟨j.1, h⟩) else 0) = a (Sum.inr j)
  rw [dite_eq_left j.2]

omit [Fintype J₀] [DecidableEq J₀] [∀ i, NeZero (m₀ i)] [∀ L (j : ↥(T L)), NeZero (j : ℕ)] in
theorem extendScale_inr_of_not_mem (ℓ L : ℕ) (a : ScaleGroup m₀ T ℓ) (j : ↥(T L))
    (hj : (j : ℕ) ∉ T ℓ) : extendScale m₀ T ℓ L a (Sum.inr j) = 0 := by
  show (if h : (j : ℕ) ∈ T ℓ then a (Sum.inr ⟨j.1, h⟩) else (0 : ZMod (j : ℕ))) =
    (0 : ZMod (j : ℕ))
  exact dite_eq_right hj

omit [Fintype J₀] [DecidableEq J₀] [∀ i, NeZero (m₀ i)] [∀ L (j : ↥(T L)), NeZero (j : ℕ)] in
theorem not_mem_range_tailEmbed {ℓ L : ℕ} (hT : T ℓ ⊆ T L) (j' : ↥(T L))
    (hj' : j' ∉ Set.range (tailEmbed T hT)) : (j' : ℕ) ∉ T ℓ := by
  intro h
  exact hj' ⟨⟨j'.1, h⟩, rfl⟩

omit [DecidableEq J₀] in
/-- The characters: `e(y·ext(a)) = e(restrict(y)·a)`. -/
theorem prodChar_extendScale {ℓ L : ℕ} (hT : T ℓ ⊆ T L) (a : ScaleGroup m₀ T ℓ)
    (y : ScaleGroup m₀ T L) :
    prodChar (joinModuli m₀ (tailModuli T L)) (extendScale m₀ T ℓ L a) y =
      prodChar (joinModuli m₀ (tailModuli T ℓ)) a (restrictScale m₀ T hT y) := by
  unfold prodChar
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
  refine congrArg₂ (· * ·) rfl ?_
  symm
  refine Fintype.prod_of_injective (tailEmbed T hT) (tailEmbed_injective T hT) _ _ ?_ ?_
  · intro j' hj'
    rw [extendScale_inr_of_not_mem m₀ T ℓ L a j' (not_mem_range_tailEmbed T hT j' hj'),
      zero_mul, AddChar.map_zero_eq_one]
  · intro j
    rw [extendScale_inr_embed m₀ T hT a j]
    rfl

omit [DecidableEq J₀] [∀ i, NeZero (m₀ i)] [∀ L (j : ↥(T L)), NeZero (j : ℕ)] in
/-- Extension by zero preserves the conductor. -/
theorem conductor_extendScale (ℓ L : ℕ) (hT : T ℓ ⊆ T L) (a : ScaleGroup m₀ T ℓ) :
    Functional.conductor (joinModuli m₀ (tailModuli T L)) (extendScale m₀ T ℓ L a) =
      Functional.conductor (joinModuli m₀ (tailModuli T ℓ)) a := by
  unfold Functional.conductor
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type]
  refine congrArg₂ (· * ·) rfl ?_
  symm
  refine Fintype.prod_of_injective (tailEmbed T hT) (tailEmbed_injective T hT) _ _ ?_ ?_
  · intro j' hj'
    rw [extendScale_inr_of_not_mem m₀ T ℓ L a j' (not_mem_range_tailEmbed T hT j' hj'),
      addOrderOf_zero]
  · intro j
    rw [extendScale_inr_embed m₀ T hT a j]
    rfl

omit [DecidableEq J₀] in
/-- A label of `G_N` of conductor `≤ Q` vanishes at the tail primes `> Q`. -/
theorem vanish_of_conductor_le {L : ℕ} (hprime : ∀ q ∈ T L, q.Prime) {Q : ℝ}
    {b : ScaleGroup m₀ T L} (hb : (Functional.conductor (joinModuli m₀ (tailModuli T L)) b : ℝ) ≤ Q)
    (j : ↥(T L)) (hj : Q < (j : ℕ)) : b (Sum.inr j) = 0 := by
  by_contra hne
  have hord : addOrderOf (b (Sum.inr j)) = (j : ℕ) := by
    have h := addOrderOf_zmod_prime (hprime j.1 j.2) (b (Sum.inr j))
    split_ifs at h with h0
    · exact absurd h0 hne
    · exact h
  have hle : addOrderOf (b (Sum.inr j)) ≤
      Functional.conductor (joinModuli m₀ (tailModuli T L)) b := by
    unfold Functional.conductor
    exact Finset.single_le_prod (fun k _ => Nat.one_le_iff_ne_zero.mpr
      (addOrderOf_pos (b k)).ne') (mem_univ (Sum.inr j))
  rw [hord] at hle
  have : ((j : ℕ) : ℝ) ≤ Q := (by exact_mod_cast hle : ((j : ℕ) : ℝ) ≤ _).trans hb
  linarith

/-- **The lift at the smaller scale.** If `T ℓ ⊆ T L` and every prime of `T L \ T ℓ`
exceeds the cutoff `Q`, the lift with cutoff `Q` on `G_N` is the lift with cutoff `Q` on
`G_n` read on the `G_n`-coordinates. -/
theorem lift_restrictScale {ℓ L : ℕ} (hT : T ℓ ⊆ T L) (hprime : ∀ q ∈ T L, q.Prime) {Q : ℝ}
    (hlarge : ∀ q ∈ T L, q ∉ T ℓ → Q < q) (I : Finset ℤ) (f : ℤ → ℂ) (y : ScaleGroup m₀ T L) :
    Functional.lift (joinModuli m₀ (tailModuli T L)) Q I f y =
      Functional.lift (joinModuli m₀ (tailModuli T ℓ)) Q I f (restrictScale m₀ T hT y) := by
  have hvan : ∀ b ∈ retained (joinModuli m₀ (tailModuli T L)) Q,
      ∀ j : ↥(T L), (j : ℕ) ∉ T ℓ → b (Sum.inr j) = 0 := by
    intro b hb j hj
    exact vanish_of_conductor_le m₀ T hprime ((mem_retained _).mp hb) j (hlarge j.1 j.2 hj)
  unfold Functional.lift liftOn
  symm
  apply sum_nbij' (extendScale m₀ T ℓ L) (restrictScale m₀ T hT)
  · intro a ha
    rw [mem_retained, conductor_extendScale m₀ T ℓ L hT]
    exact (mem_retained _).mp ha
  · intro b hb
    rw [mem_retained, ← conductor_extendScale m₀ T ℓ L hT,
      extendScale_restrictScale m₀ T hT (hvan b hb)]
    exact (mem_retained _).mp hb
  · intro a _
    exact restrictScale_extendScale m₀ T hT a
  · intro b hb
    exact extendScale_restrictScale m₀ T hT (hvan b hb)
  · intro a _
    rw [prodChar_extendScale m₀ T hT a y]
    congr 1
    unfold intervalCoeff
    congr 1
    apply sum_congr rfl
    intro n _
    rw [prodChar_extendScale m₀ T hT a, restrictScale_integerResidue]

end Sarkozy.PaperFrame
