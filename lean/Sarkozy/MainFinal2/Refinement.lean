module

public import Sarkozy.EnvelopesPaper.Prefix

@[expose] public section

/-!
# The prefix refinement from its middle-block atoms (K2)

`prop:record:matching`(i): the paper replaces records only on the middle blocks. B3's
`PrefixRefinement` asks its data and its bracket `bracket_pre` at **every** prefix atom. Here:

* `AtomRefinement GB CL L β`: the refinement at one prefix atom `β` and scale `L` (the replaced
  records, the added positive diagonals with their coefficients, and the refined bracket);
* `AtomRefinement.trivial`: nothing replaced, nothing added; the bracket is (CP3)'s
  (**proved**, from `GB.bracket`);
* `MidRefinement GB CL mid`: the refinement on the atoms with `mid β` only, with per-atom bounds
  of the added prices; **`MidRefinement.toPrefix`** is B3's `PrefixRefinement`, trivial off `mid`.
-/

open Finset Function
open scoped BigOperators

namespace Sarkozy.MainFinal2

open Sarkozy.TheoremC Sarkozy.TheoremCBlock Sarkozy.BlockFrame
open Sarkozy.EnvelopesPaper (PrefixRefinement)

variable {a : ℝ}
  {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {S₀ : Bk → ℝ} {pp ep : J₀ → ℕ} {E : Type} {Q : Queries E} {R : Reference m₀ blk}
  {FS : FirstStage a m₀ blk p S₀ R}

/-- **The refinement at one prefix atom** (`prop:record:matching`(i), `prop:signed-sides`): the
replaced records `repl`, the added positive diagonals `κK` with coefficients `kL`, `kR`, and the
refined bracket `Ñ + ∑ kL κK ⪯ λ + ∑_{repl} Δ ⪯ Ñ + ∑ kR κK`. -/
structure AtomRefinement (GB : GramBracket a m₀ blk p S₀ FS)
    (CL : ComparisonLaw a m₀ blk p S₀ pp ep Q FS) (L : ℕ) (β : Bk) where
  repl : Finset (CL.T L (.inl β))
  IK : Type
  [IKFintype : Fintype IK]
  kL : IK → ℝ
  kR : IK → ℝ
  kL_nonneg : ∀ i, 0 ≤ kL i
  kR_nonneg : ∀ i, 0 ≤ kR i
  κK : IK → AtomMeasure m₀ blk p L (.inl β)
  κK_pos : ∀ i, IsPositiveRecord (κK i)
  κK_diag : ∀ i, TheoremC.IsDiagonalAt reservedCut (κK i)
  /-- The refined bracket at the atom. *Hypothesis.* -/
  bracket : reservedCut.Bracket (GB.N L (.inl β) + ∑ i, kL i • κK i)
    (FS.lam L (.inl β) + ∑ t ∈ repl, CL.Δ L (.inl β) t) (GB.N L (.inl β) + ∑ i, kR i • κK i)

attribute [instance] AtomRefinement.IKFintype

/-- **The trivial refinement at a prefix atom**: nothing replaced or added; the bracket is (CP3)'s
(`GB.bracket`). -/
noncomputable def AtomRefinement.trivial (GB : GramBracket a m₀ blk p S₀ FS)
    (CL : ComparisonLaw a m₀ blk p S₀ pp ep Q FS) (L : ℕ) (β : Bk) :
    AtomRefinement GB CL L β where
  repl := ∅
  IK := Empty
  kL := Empty.elim
  kR := Empty.elim
  kL_nonneg i := i.elim
  kR_nonneg i := i.elim
  κK := Empty.elim
  κK_pos i := i.elim
  κK_diag i := i.elim
  bracket := by
    rw [sum_empty, add_zero]
    simp only [univ_eq_empty, sum_empty, add_zero]
    exact GB.bracket L (.inl β)

/-- **The refinement on the atoms `mid β`** (the middle blocks), with per-atom bounds of the
prices of the added diagonals, uniform in the scale. -/
structure MidRefinement (GB : GramBracket a m₀ blk p S₀ FS)
    (CL : ComparisonLaw a m₀ blk p S₀ pp ep Q FS) (mid : Bk → Prop) [DecidablePred mid] where
  /-- The refinement at each atom of `mid` and each scale. *Hypothesis* (its bracket). -/
  R : ∀ L β, mid β → AtomRefinement GB CL L β
  /-- The per-atom bounds. Data. -/
  KL : Bk → ℝ
  KR : Bk → ℝ
  KL_bound : ∀ L β (h : mid β), ∑ i, (R L β h).kL i * mass ((R L β h).κK i) * S₀ β ≤ KL β
  KR_bound : ∀ L β (h : mid β), ∑ i, (R L β h).kR i * mass ((R L β h).κK i) * S₀ β ≤ KR β

namespace MidRefinement

variable {GB : GramBracket a m₀ blk p S₀ FS} {CL : ComparisonLaw a m₀ blk p S₀ pp ep Q FS}
  {mid : Bk → Prop} [DecidablePred mid]

/-- The refinement at every prefix atom: `R` on `mid`, trivial elsewhere. -/
noncomputable def atom (M : MidRefinement GB CL mid) (L : ℕ) (β : Bk) : AtomRefinement GB CL L β :=
  if h : mid β then M.R L β h else AtomRefinement.trivial GB CL L β

/-- **B3's `PrefixRefinement` from the refinement on `mid`** (trivial off `mid`, nothing at a
tail atom); the bounds are `KL β`, `KR β` on `mid` and `0` elsewhere. -/
noncomputable def toPrefix (M : MidRefinement GB CL mid) : PrefixRefinement GB CL where
  repl L b := match b with
    | .inl β => (M.atom L β).repl
    | .inr _ => ∅
  IK L b := match b with
    | .inl β => (M.atom L β).IK
    | .inr _ => Empty
  IKFintype L b := match b with
    | .inl β => (M.atom L β).IKFintype
    | .inr _ => inferInstanceAs (Fintype Empty)
  kL L b := match b with
    | .inl β => (M.atom L β).kL
    | .inr _ => Empty.elim
  kR L b := match b with
    | .inl β => (M.atom L β).kR
    | .inr _ => Empty.elim
  kL_nonneg L b := match b with
    | .inl β => (M.atom L β).kL_nonneg
    | .inr _ => fun i => i.elim
  kR_nonneg L b := match b with
    | .inl β => (M.atom L β).kR_nonneg
    | .inr _ => fun i => i.elim
  κK L b := match b with
    | .inl β => (M.atom L β).κK
    | .inr _ => Empty.elim
  κK_pos L b := match b with
    | .inl β => (M.atom L β).κK_pos
    | .inr _ => fun i => i.elim
  κK_diag L b := match b with
    | .inl β => (M.atom L β).κK_diag
    | .inr _ => fun i => i.elim
  repl_tail _ _ := rfl
  kL_tail _ _ i := i.elim
  kR_tail _ _ i := i.elim
  bracket_pre L β := (M.atom L β).bracket
  KL β := if mid β then M.KL β else 0
  KR β := if mid β then M.KR β else 0
  KL_bound L β := by
    show ∑ i, (M.atom L β).kL i * mass ((M.atom L β).κK i) * S₀ β ≤ (if mid β then M.KL β else 0)
    by_cases h : mid β
    · rw [show M.atom L β = M.R L β h by unfold atom; simp only [h, ↓reduceDIte]]
      simp only [h, ↓reduceIte]
      exact M.KL_bound L β h
    · rw [show M.atom L β = AtomRefinement.trivial GB CL L β by
        unfold atom; simp only [h, ↓reduceDIte]]
      simp only [h, ↓reduceIte]
      exact le_of_eq (sum_eq_zero fun i _ => Empty.elim i)
  KR_bound L β := by
    show ∑ i, (M.atom L β).kR i * mass ((M.atom L β).κK i) * S₀ β ≤ (if mid β then M.KR β else 0)
    by_cases h : mid β
    · rw [show M.atom L β = M.R L β h by unfold atom; simp only [h, ↓reduceDIte]]
      simp only [h, ↓reduceIte]
      exact M.KR_bound L β h
    · rw [show M.atom L β = AtomRefinement.trivial GB CL L β by
        unfold atom; simp only [h, ↓reduceDIte]]
      simp only [h, ↓reduceIte]
      exact le_of_eq (sum_eq_zero fun i _ => Empty.elim i)

/-- The replaced records of `toPrefix` at a prefix atom off `mid`: none. -/
theorem toPrefix_repl_off (M : MidRefinement GB CL mid) (L : ℕ) (β : Bk) (h : ¬ mid β) :
    M.toPrefix.repl L (.inl β) = ∅ := by
  show (M.atom L β).repl = ∅
  rw [show M.atom L β = AtomRefinement.trivial GB CL L β by
        unfold atom; simp only [h, ↓reduceDIte]]
  rfl

end MidRefinement

end Sarkozy.MainFinal2
