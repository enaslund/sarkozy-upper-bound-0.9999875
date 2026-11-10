module

public import Sarkozy.TheoremCParam.Defs
public import Sarkozy.BlockFrame.Wrap

@[expose] public section



open Filter Finset Function
open scoped Topology BigOperators Matrix

namespace Sarkozy.TheoremCBlock

open Sarkozy.TheoremC
open Sarkozy.Param (Params)
open Sarkozy.BlockFrame

variable {a : ℝ}

open Sarkozy.FourierArithmetic Sarkozy.Functional Sarkozy.IndexSupport Sarkozy.Comparison
  Sarkozy.PaperFrame Sarkozy.RecordExpansion

/-! ## Measures, records and prices (`def:cp:records`, `def:price`) -/

/-! ## The cuts, the queries and the index law (CP0) -/

section Standing

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] (m₀ : J₀ → ℕ) [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] (blk : J₀ → Bk)
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] (p : ∀ L, J L → ℕ)
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] (pr h : P → ℕ) [∀ q, NeZero (pr q ^ h q)]

/-- **(CP0) Standing data** (`def:cp0`), over the objects of `Sarkozy.PaperFrame`.
(a) The slots `V = Slot` (`d = 72`) and the cut family `IsFamilyCut`, which contains the
sorting sequence (`isFamilyCut_of_sorting`), are fixed. (b) `K = blockScale`; at every
scale `L ≥ 1`, `N = KL`, the group `G_N = ResidueSpace (joinModuli m₀ (p L))`, its atoms
`PaperAtom J L` (the prefix and the tail primes `p L j`), the lift `F_A = atomLift` and the
inputs `g^{I,D_0,s}` (`atomInput`) are those of `def:record:functional`; the prefix
coordinates are `ℤ/p^{e_p}ℤ` with the fixed prefix exponents `e_p` (`pp`, `ep`); the
density exponent is `θ = densityExponent` and the price exponent `a = decay`. (c) The
queries. (d) The index law. -/
structure StandingData (E : Type) [Fintype E] [DecidableEq E] where
  /-- The prefix primes and exponents: `m₀ i = pp i ^ ep i`. -/
  pp : J₀ → ℕ
  ep : J₀ → ℕ
  pp_prime : ∀ i, (pp i).Prime
  ep_pos : ∀ i, 1 ≤ ep i
  m₀_eq : ∀ i, m₀ i = pp i ^ ep i
  /-- The tail coordinates are distinct primes. -/
  p_prime : ∀ L j, (p L j).Prime
  p_inj : ∀ L, Function.Injective (p L)
  /-- The selection factors `q_𝔟^{2a}` of the prefix blocks (`def:price`). -/
  selPre : Bk → ℝ
  one_le_selPre : ∀ β, 1 ≤ selPre β
  /-- (c) The queries. -/
  Q : Queries E
  /-- (d) The index law; `M₀ = ∏_p p^{h_p}` with `h_2 ≥ 3`, coprime to every prime of
  `G_N`. -/
  index : IndexLaw pr h E
  pr_prime : ∀ q, (pr q).Prime
  pr_inj : Function.Injective pr
  h_two : ∃ q, pr q = 2 ∧ 3 ≤ h q
  modulus_coprime : ∀ L k, Nat.Coprime (modulus pr h) (joinModuli m₀ (p L) k)

variable (a) in
/-- The selection factor `q_𝔟^{2a}` of an atom (`def:price`): `p^{2a}` at a tail prime
`p`, the given factor `selPre β` at the prefix block `β` (the paper's values are
`Sarkozy.BlockAnchor.paperSel`). -/
noncomputable def selectionFactor (selPre : Bk → ℝ) (L : ℕ) : BlockAtom Bk J L → ℝ
  | .inl β => selPre β
  | .inr j => ((p L j : ℕ) : ℝ) ^ (2 * a)

/-- The product of the primes of an atom with `e_p = 1` (the weight `q_𝔟` of (CP8)(c)). -/
noncomputable def oneWeight (pp ep : J₀ → ℕ) (L : ℕ) : BlockAtom Bk J L → ℝ
  | .inl β => ∏ i ∈ univ.filter (fun i : BlockIdx blk β => ep i.1 = 1), (pp i.1 : ℝ)
  | .inr j => (p L j : ℝ)

/-- The law of an atom at the scale `L`. -/
abbrev AtomMeasure (L : ℕ) (b : BlockAtom Bk J L) : Type := SlotMeasure (BlockLabel m₀ blk p L b)

/-- Acceptance of a query pair at an atom (`(CP4)(a)`, `(R5)`): the difference
`y - x = z_{v_e} - z_{u_e}` is a nonzero square at a tail prime (`e_p = 1`), and at every
prefix prime it is nonzero, of even valuation `2j < e_p`, with a square unit part (for
`e_p = 1` this is a nonzero square). -/
def AcceptedPair (pp ep : J₀ → ℕ) (L : ℕ) : ∀ b : BlockAtom Bk J L,
    BlockLabel m₀ blk p L b → BlockLabel m₀ blk p L b → Prop
  | .inl β => fun x y => ∀ i : BlockIdx blk β, y i - x i ≠ 0 ∧ ∃ jj : ℕ, 2 * jj < ep i.1 ∧
      ∃ r : ZMod (m₀ i.1), IsUnit r ∧ IsSquare r ∧
        y i - x i = ((pp i.1 : ℕ) : ZMod (m₀ i.1)) ^ (2 * jj) * r
  | .inr _ => fun x y => y - x ≠ 0 ∧ IsSquare (y - x)

end Standing

/-! ## Robust bounds (`def:robust`) -/

end Sarkozy.TheoremCBlock
