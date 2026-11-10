module

public import Sarkozy.CancellationSteps.Final
public import Sarkozy.CancellationSteps.SquareLocal

/-!
# The square class of `𝔞₂ − 𝔞₁` from the local conditions (b)

`paper/sections/08_scale_comparison.tex`, `lem:record:density-can`, Step 3: "The difference
`𝔞₂ − 𝔞₁` is `r` modulo `M₀`, a nonzero square at the primes of `U` and at the primes below `P₅`
with `e_p = 1`, and at the clique primes nonzero of even valuation below `e_p` with square unit
part, by (b)." Here, for the encoded data of a query (`FibreCore`):

* `squareClass_step`: for every choice of fibre classes `𝔞₁`, `𝔞₂` and every `ω = (x, a)` with
  `μ(x) ≠ 0`, `𝔞₂(ω) − 𝔞₁(ω)` is a nonvanishing square class modulo `D = M₀ ∏_{c ∈ E} m_c`. The
  inputs are the acceptance (b) at the low atoms (`TheoremC.AcceptedPair`), the strict-square
  pairs at the primes of `U` (`PairAlphabet`), `r` a nonvanishing square class modulo `M₀`, and
  the structure of the prefix (`m₀ i = pp_i^{ep_i}`, `pp_i` prime, `ep_i ≥ 1`).

New material for this paper.
-/

@[expose] public section

namespace Sarkozy.CancellationSteps

open Finset
open scoped BigOperators
open Sarkozy.Cancellation Sarkozy.Mixing Sarkozy.PaperFrame Sarkozy.FourierArithmetic
  Sarkozy.Functional

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] (m₀ : J₀ → ℕ) [∀ i, NeZero (m₀ i)]
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] (p : ∀ L, J L → ℕ)
  [∀ L j, NeZero (p L j)]

/-- The prime of an atom coordinate: `pp_i` at a prefix coordinate, `p_j` at a tail prime. -/
def coordPrime (pp : J₀ → ℕ) (L : ℕ) : J₀ ⊕ J L → ℕ
  | Sum.inl i => pp i
  | Sum.inr j => p L j

/-- The exponent of an atom coordinate: `ep_i` at a prefix coordinate, `1` at a tail prime. -/
def coordExp (ep : J₀ → ℕ) (L : ℕ) : J₀ ⊕ J L → ℕ
  | Sum.inl i => ep i
  | Sum.inr _ => 1

omit [Fintype J₀] [DecidableEq J₀] [∀ i, NeZero (m₀ i)] [∀ L j, NeZero (p L j)] in
lemma frozenAt_inl (L P5 : ℕ) (w : Slot) (x : LowLabels m₀ p L P5)
    (y : ∀ k : TailIdx p L P5, ZMod (tailQ p L P5 k)) (i : J₀) :
    frozenAt m₀ p L P5 w x y (Sum.inl i) = x ⟨none, isLow_none p L P5⟩ w i := by
  unfold frozenAt
  rw [atomGroupEquiv_apply]
  show mergeAt m₀ p L P5 (fun i => x i w) y none i = _
  rw [mergeAt_low m₀ p L P5 _ _ none (isLow_none p L P5)]

omit [Fintype J₀] [DecidableEq J₀] [∀ i, NeZero (m₀ i)] [∀ L j, NeZero (p L j)] in
lemma frozenAt_low (L P5 : ℕ) (w : Slot) (x : LowLabels m₀ p L P5)
    (y : ∀ k : TailIdx p L P5, ZMod (tailQ p L P5 k)) (j : J L) (hj : IsLow p L P5 (some j)) :
    frozenAt m₀ p L P5 w x y (Sum.inr j) = x ⟨some j, hj⟩ w := by
  unfold frozenAt
  rw [atomGroupEquiv_apply]
  show mergeAt m₀ p L P5 (fun i => x i w) y (some j) = _
  rw [mergeAt_low m₀ p L P5 _ _ (some j) hj]

omit [Fintype J₀] [DecidableEq J₀] [∀ i, NeZero (m₀ i)] [∀ L j, NeZero (p L j)] in
lemma frozenAt_tail (L P5 : ℕ) (w : Slot) (x : LowLabels m₀ p L P5)
    (y : ∀ k : TailIdx p L P5, ZMod (tailQ p L P5 k)) (k : TailIdx p L P5) :
    frozenAt m₀ p L P5 w x y (Sum.inr k.1) = y k := by
  unfold frozenAt
  rw [atomGroupEquiv_apply]
  show mergeAt m₀ p L P5 (fun i => x i w) y (some k.1) = _
  rw [mergeAt_tail]

/-- **The square class of Step 3**: for fibre classes `𝔞₁`, `𝔞₂` of the frozen labels of `u`
(residue `s`) and `v` (residue `s + r`), and `ω = (x, a)` with `μ(x) ≠ 0`, the acceptance (b) at
the low atoms, the strict-square pairs at the primes of `U` and `r` a nonvanishing square class
modulo `M` make `𝔞₂(ω) − 𝔞₁(ω)` a nonvanishing square class modulo `D = M ∏_{c ∈ E} m_c`. -/
theorem squareClass_step [∀ L j, Fact (p L j).Prime] (pp ep : J₀ → ℕ)
    (hpre : ∀ i, (pp i).Prime ∧ 1 ≤ ep i ∧ m₀ i = pp i ^ ep i) (L P5 : ℕ)
    (U : TailIdx p L P5 → Bool) {M : ℕ} [NeZero M]
    (hcop0 : ∀ c : J₀ ⊕ J L, Nat.Coprime M (joinModuli m₀ (p L) c))
    (hcopE : ∀ i j : J₀ ⊕ J L, i ≠ j →
      Nat.Coprime (joinModuli m₀ (p L) i) (joinModuli m₀ (p L) j))
    (s r : ZMod M) (hr : Functional.IsNonvanishingSquareClass M r) (u v : Slot)
    (ϱ : ∀ b : PaperAtom J L, FiniteLaw (Slot → AtomLabel m₀ p L b))
    (hb : ∀ b : PaperAtom J L, (∀ j, b = some j → p L j < P5) → ∀ z, (ϱ b).weight z ≠ 0 →
      Sarkozy.TheoremC.AcceptedPair m₀ p pp ep L b (z u) (z v))
    (𝔞₁ 𝔞₂ : LowLabels m₀ p L P5 × (∀ k, PairAlphabet (tailQ p L P5) k) → ℤ)
    (c₁ : ∀ ω n, InFibre (joinModuli m₀ (p L)) (frozenCoords (J₀ := J₀) p L P5 U)
        (frozenAt m₀ p L P5 u ω.1 (pairsToVectors (tailQ p L P5) ω.2).1) s n ↔
        n ≡ 𝔞₁ ω [ZMOD ((fibreModulus m₀ p L P5 U M : ℕ) : ℤ)])
    (c₂ : ∀ ω n, InFibre (joinModuli m₀ (p L)) (frozenCoords (J₀ := J₀) p L P5 U)
        (frozenAt m₀ p L P5 v ω.1 (pairsToVectors (tailQ p L P5) ω.2).2) (s + r) n ↔
        n ≡ 𝔞₂ ω [ZMOD ((fibreModulus m₀ p L P5 U M : ℕ) : ℤ)])
    (ω : LowLabels m₀ p L P5 × (∀ k, PairAlphabet (tailQ p L P5) k))
    (hω : (FiniteLaw.pi (fun i : {b : PaperAtom J L // IsLow p L P5 b} => ϱ i.1)).weight ω.1 ≠ 0) :
    Kernel.IsNonvanishingSquareClass (fibreModulus m₀ p L P5 U M) (𝔞₂ ω - 𝔞₁ ω) := by
  set E := frozenCoords (J₀ := J₀) p L P5 U with hE
  -- the fibre conditions of the classes themselves
  obtain ⟨h1s, h1E⟩ := (c₁ ω (𝔞₁ ω)).mpr (Int.ModEq.refl _)
  obtain ⟨h2s, h2E⟩ := (c₂ ω (𝔞₂ ω)).mpr (Int.ModEq.refl _)
  -- the weights of the low atoms
  have hw : ∀ i : {b : PaperAtom J L // IsLow p L P5 b}, (ϱ i.1).weight (ω.1 i) ≠ 0 := by
    intro i
    have := hω
    unfold FiniteLaw.pi at this
    exact (prod_ne_zero_iff.mp this) i (mem_univ _)
  have hmod : ∀ c, joinModuli m₀ (p L) c = coordPrime p pp L c ^ coordExp (J := J) ep L c := by
    intro c
    cases c with
    | inl i => exact (hpre i).2.2
    | inr j => exact (pow_one _).symm
  have hPprime : ∀ c, (coordPrime p pp L c).Prime := by
    intro c
    cases c with
    | inl i => exact (hpre i).1
    | inr j => exact (Fact.out : (p L j).Prime)
  have hexp : ∀ c, 1 ≤ coordExp (J := J) ep L c := by
    intro c
    cases c with
    | inl i => exact (hpre i).2.1
    | inr j => exact le_rfl
  have hPdvd : ∀ c, coordPrime p pp L c ∣ joinModuli m₀ (p L) c := by
    intro c
    rw [hmod c]
    exact dvd_pow_self _ (by have := hexp c; omega)
  have hDeq : fibreModulus m₀ p L P5 U M =
      M * ∏ c ∈ E, coordPrime p pp L c ^ coordExp (J := J) ep L c := by
    unfold fibreModulus
    rw [prod_congr rfl fun c _ => hmod c]
  rw [hDeq]
  -- the residue of `𝔞₂ − 𝔞₁` at a frozen coordinate
  have hres : ∀ c ∈ E, (((𝔞₂ ω - 𝔞₁ ω : ℤ)) : ZMod (joinModuli m₀ (p L) c)) =
      frozenAt m₀ p L P5 v ω.1 (pairsToVectors (tailQ p L P5) ω.2).2 c -
        frozenAt m₀ p L P5 u ω.1 (pairsToVectors (tailQ p L P5) ω.2).1 c := by
    intro c hc
    push_cast
    rw [h1E c hc, h2E c hc]
  apply squareClass_difference E (coordPrime p pp L) (coordExp ep L)
    (fun c _ => hPprime c) ?_ (NeZero.ne M)
    (fun c _ => Nat.Coprime.coprime_dvd_right (hPdvd c) (hcop0 c))
    (kernel_of_functional_squareClass (NeZero.ne M) hr) ?_ ?_
  · -- distinct primes
    intro c hc c' hc' hcc
    by_contra hne
    have hcop := hcopE c c' hne
    have h1 := hPdvd c
    have h2 := hPdvd c'
    rw [hcc] at h1
    have := Nat.eq_one_of_dvd_coprimes hcop h1 h2
    exact (hPprime c').one_lt.ne' this
  · -- the congruence modulo `M`
    rw [← ZMod.intCast_eq_intCast_iff]
    push_cast
    rw [h1s, h2s, ZMod.natCast_zmod_val]
    ring
  · -- the local conditions
    intro c hc
    cases c with
    | inl i =>
      have hacc := hb none (fun j h => by cases h) (ω.1 ⟨none, isLow_none p L P5⟩)
        (hw ⟨none, isLow_none p L P5⟩) i
      have hδ := hres (Sum.inl i) hc
      rw [frozenAt_inl, frozenAt_inl] at hδ
      exact oddLocalSquare_of_prefix (hpre i).2.2 (hpre i).1 (hpre i).2.1 hacc.2 hδ
    | inr j =>
      by_cases hj : p L j < P5
      · have hlow : IsLow p L P5 (some j) := fun j' h => by cases h; exact hj
        have hacc := hb (some j) (fun j' h => by cases h; exact hj) (ω.1 ⟨some j, hlow⟩)
          (hw ⟨some j, hlow⟩)
        have hδ := hres (Sum.inr j) hc
        rw [frozenAt_low m₀ p L P5 v ω.1 _ j hlow, frozenAt_low m₀ p L P5 u ω.1 _ j hlow] at hδ
        exact oddLocalSquare_of_square hacc.1 hacc.2 hδ
      · have hj' : P5 ≤ p L j := not_lt.mp hj
        have hδ := hres (Sum.inr j) hc
        have e1 := frozenAt_tail m₀ p L P5 v ω.1 (pairsToVectors (tailQ p L P5) ω.2).2 ⟨j, hj'⟩
        have e2 := frozenAt_tail m₀ p L P5 u ω.1 (pairsToVectors (tailQ p L P5) ω.2).1 ⟨j, hj'⟩
        rw [e1, e2] at hδ
        have hmem : (ω.2 (⟨j, hj'⟩ : TailIdx p L P5)).1.2 - (ω.2 (⟨j, hj'⟩ : TailIdx p L P5)).1.1 ∈
            sqSet (tailQ p L P5) (⟨j, hj'⟩ : TailIdx p L P5) := (ω.2 (⟨j, hj'⟩ : TailIdx p L P5)).2
        unfold sqSet at hmem
        rw [mem_filter] at hmem
        exact oddLocalSquare_of_square hmem.2.1 hmem.2.2 hδ

end Sarkozy.CancellationSteps
