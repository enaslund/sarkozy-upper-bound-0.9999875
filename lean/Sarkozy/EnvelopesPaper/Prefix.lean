module

public import Sarkozy.EnvelopesPaper.Summability

@[expose] public section

/-!
# A refinement supported on the prefix atoms: `SI` and `hTs` reduced to per-block sums

`prop:record:matching`(i),(ii); `def:cp8`(c). In the paper the refinement (the fold and matching
records replaced by `K_{s,𝔅}`, `Q_{E,𝔅}`) lives on the middle blocks only: at a tail atom nothing is
replaced and nothing is added. `PrefixRefinement GB CL` records exactly this:

* the data of `EnvelopeRefinement`, with `repl = ∅` and `kL = kR = 0` at every tail atom
  (`repl_tail`, `kL_tail`, `kR_tail`), and the refined bracket required **at the prefix atoms
  only** (`bracket_pre`); at a tail atom it is (CP3)'s bracket (`toRefinement`, proved);
* per-block constants `KL β`, `KR β` bounding the prices of the added diagonals at every scale (in
  the paper the prices `(k_{L,i} + k_{R,i}) r_𝔅² q_𝔅^{2a}` do not depend on the scale).

Proved from it:
* `PrefixRefinement.summabilityInputs`: `SummabilityInputs` with `σ_K = W_pre ∑_β (KL β + KR β)`;
  only the weighted (CP4) bound `σ_CL` of the comparison law remains;
* `PrefixRefinement.hTs`: the side sums `∑_𝔟 priceL, ∑_𝔟 priceR ≤ T` from the explicit per-block
  sums `∑_β KL β ≤ T_K`, `∑_β KR β ≤ T_K` and the named property `hrepl` of the comparison law: at
  every scale, its replaced records carry at least `∑_𝔟(s_𝔟 + a_𝔟) − (T − T_K)` of its (CP4) price.
-/

open Finset Function
open scoped BigOperators

namespace Sarkozy.EnvelopesPaper

open Sarkozy.TheoremC Sarkozy.TheoremCBlock Sarkozy.BlockFrame
open Sarkozy.RecordExpansion (ChangeType symTotal skewTotal)

variable {a : ℝ}
  {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {S₀ : Bk → ℝ} {pp ep : J₀ → ℕ} {E : Type} {Q : Queries E} {R : Reference m₀ blk}
  {FS : FirstStage a m₀ blk p S₀ R} {GB : GramBracket a m₀ blk p S₀ FS}
  {CL : ComparisonLaw a m₀ blk p S₀ pp ep Q FS}

/-- **A refinement supported on the prefix atoms** (`prop:record:matching`(i): the replacement
happens on the middle blocks only), with per-block bounds of the prices of its added diagonals.
The bracket `bracket_pre` at the prefix atoms is the paper's middle-block computation; it is the
remaining hypothesis. -/
structure PrefixRefinement (GB : GramBracket a m₀ blk p S₀ FS)
    (CL : ComparisonLaw a m₀ blk p S₀ pp ep Q FS) where
  repl : ∀ L b, Finset (CL.T L b)
  IK : ∀ L, BlockAtom Bk J L → Type
  [IKFintype : ∀ L b, Fintype (IK L b)]
  kL : ∀ L b, IK L b → ℝ
  kR : ∀ L b, IK L b → ℝ
  kL_nonneg : ∀ L b i, 0 ≤ kL L b i
  kR_nonneg : ∀ L b i, 0 ≤ kR L b i
  κK : ∀ L b, IK L b → AtomMeasure m₀ blk p L b
  κK_pos : ∀ L b i, IsPositiveRecord (κK L b i)
  κK_diag : ∀ L b i, TheoremC.IsDiagonalAt reservedCut (κK L b i)
  /-- Nothing is replaced or added at a tail atom. -/
  repl_tail : ∀ L j, repl L (.inr j) = ∅
  kL_tail : ∀ L j i, kL L (.inr j) i = 0
  kR_tail : ∀ L j i, kR L (.inr j) i = 0
  /-- **The refined bracket at the prefix atoms** (`prop:record:matching`(i), middle-block step;
  trivially (CP3)'s bracket at a prefix atom with nothing replaced). *Hypothesis.* -/
  bracket_pre : ∀ L β, reservedCut.Bracket
    (GB.N L (.inl β) + ∑ i, kL L (.inl β) i • κK L (.inl β) i)
    (FS.lam L (.inl β) + ∑ t ∈ repl L (.inl β), CL.Δ L (.inl β) t)
    (GB.N L (.inl β) + ∑ i, kR L (.inl β) i • κK L (.inl β) i)
  /-- Per-block bounds of the prices of the added diagonals, uniform in the scale. -/
  KL : Bk → ℝ
  KR : Bk → ℝ
  KL_bound : ∀ L β, ∑ i, kL L (.inl β) i * mass (κK L (.inl β) i) * S₀ β ≤ KL β
  KR_bound : ∀ L β, ∑ i, kR L (.inl β) i * mass (κK L (.inl β) i) * S₀ β ≤ KR β

attribute [instance] PrefixRefinement.IKFintype

namespace PrefixRefinement

variable (PR : PrefixRefinement GB CL)

/-- **The refinement**: the bracket at a tail atom is (CP3)'s. -/
noncomputable def toRefinement : EnvelopeRefinement GB CL where
  repl := PR.repl
  IK := PR.IK
  IKFintype := PR.IKFintype
  kL := PR.kL
  kR := PR.kR
  kL_nonneg := PR.kL_nonneg
  kR_nonneg := PR.kR_nonneg
  κK := PR.κK
  κK_pos := PR.κK_pos
  κK_diag := PR.κK_diag
  bracket L b := by
    cases b with
    | inl β => exact PR.bracket_pre L β
    | inr j =>
      rw [PR.repl_tail L j, sum_empty, add_zero]
      simp only [PR.kL_tail, PR.kR_tail, zero_smul, sum_const_zero, add_zero]
      exact GB.bracket L (.inr j)

theorem KpriceL_tail (L : ℕ) (j : J L) : PR.toRefinement.KpriceL L (.inr j) = 0 := by
  have h : ∑ i : PR.IK L (.inr j), PR.kL L (.inr j) i * mass (PR.κK L (.inr j) i) *
      selectionFactor a p S₀ L (.inr j) = 0 :=
    sum_eq_zero fun i _ => by rw [PR.kL_tail, zero_mul, zero_mul]
  exact h

theorem KpriceR_tail (L : ℕ) (j : J L) : PR.toRefinement.KpriceR L (.inr j) = 0 := by
  have h : ∑ i : PR.IK L (.inr j), PR.kR L (.inr j) i * mass (PR.κK L (.inr j) i) *
      selectionFactor a p S₀ L (.inr j) = 0 :=
    sum_eq_zero fun i _ => by rw [PR.kR_tail, zero_mul, zero_mul]
  exact h

theorem KpriceL_inl_le (L : ℕ) (β : Bk) : PR.toRefinement.KpriceL L (.inl β) ≤ PR.KL β :=
  PR.KL_bound L β

theorem KpriceR_inl_le (L : ℕ) (β : Bk) : PR.toRefinement.KpriceR L (.inl β) ≤ PR.KR β :=
  PR.KR_bound L β

theorem KpriceL_nonneg (hS₀ : ∀ β, 0 ≤ S₀ β) (L : ℕ) (β : Bk) :
    0 ≤ PR.toRefinement.KpriceL L (.inl β) :=
  sum_nonneg fun i _ => mul_nonneg (mul_nonneg (PR.kL_nonneg L _ i)
    (mass_nonneg_of (PR.κK_pos L _ i).1)) (hS₀ β)

theorem KpriceR_nonneg (hS₀ : ∀ β, 0 ≤ S₀ β) (L : ℕ) (β : Bk) :
    0 ≤ PR.toRefinement.KpriceR L (.inl β) :=
  sum_nonneg fun i _ => mul_nonneg (mul_nonneg (PR.kR_nonneg L _ i)
    (mass_nonneg_of (PR.κK_pos L _ i).1)) (hS₀ β)

variable (pp ep) in
/-- **`SummabilityInputs` for a prefix refinement** (`def:cp8`(c)): `σ_K = W_pre ∑_β (KL β + KR β)`
is proved; only the weighted (CP4) bound `σ_CL` of the comparison law is an input. -/
noncomputable def summabilityInputs (hS₀ : ∀ β, 0 ≤ S₀ β) (σCL : ℝ)
    (hCL : ∀ L, ∑ b, oneWeight blk p pp ep L b ^ ((1 : ℝ) / 4) *
      (symTotal (CL.π L) b + skewTotal (CL.π L) b) ≤ σCL) :
    SummabilityInputs pp ep PR.toRefinement where
  σCL := σCL
  hCL := hCL
  σK := prefixWeight blk p pp ep (J := J) * ∑ β, (PR.KL β + PR.KR β)
  hK L := by
    rw [Fintype.sum_sum_type]
    simp only [PR.KpriceL_tail, PR.KpriceR_tail, add_zero, mul_zero, sum_const_zero]
    rw [mul_sum]
    apply sum_le_sum
    intro β _
    have hw := weight_inl_le (pp := pp) (ep := ep) (blk := blk) (p := p) L β
    have hw0 : 0 ≤ oneWeight blk p pp ep L (.inl β : BlockAtom Bk J L) ^ ((1 : ℝ) / 4) :=
      weight_nonneg L _
    have h1 := PR.KpriceL_inl_le L β
    have h2 := PR.KpriceR_inl_le L β
    have h3 := PR.KpriceL_nonneg hS₀ L β
    have h4 := PR.KpriceR_nonneg hS₀ L β
    calc oneWeight blk p pp ep L (.inl β : BlockAtom Bk J L) ^ ((1 : ℝ) / 4) *
          (PR.toRefinement.KpriceL L (.inl β) + PR.toRefinement.KpriceR L (.inl β))
        ≤ oneWeight blk p pp ep L (.inl β : BlockAtom Bk J L) ^ ((1 : ℝ) / 4) *
          (PR.KL β + PR.KR β) := mul_le_mul_of_nonneg_left (by linarith) hw0
      _ ≤ _ := mul_le_mul_of_nonneg_right hw (by linarith)

/-- **The side sums from per-block sums** (`prop:record:matching`(ii)): if `∑_β KL β ≤ T_K`,
`∑_β KR β ≤ T_K`, and at every scale the replaced records of the comparison law carry at least
`∑_𝔟 (s_𝔟 + a_𝔟) − (T − T_K)` of its (CP4) price at that scale (`hrepl`), then `∑_𝔟 priceL ≤ T` and `∑_𝔟 priceR ≤ T`. -/
theorem hTs {T TK : ℝ} (hKL : ∑ β, PR.KL β ≤ TK) (hKR : ∑ β, PR.KR β ≤ TK)
    (hrepl : ∀ L, ∑ b, (symTotal (CL.π L) b + skewTotal (CL.π L) b) - (T - TK) ≤
      ∑ b, ∑ t ∈ PR.repl L b, (CL.π L b t .sym + CL.π L b t .skew)) (L : ℕ) :
    ∑ b, PR.toRefinement.priceL L b ≤ T ∧ ∑ b, PR.toRefinement.priceR L b ≤ T := by
  have hoth : ∑ b, PR.toRefinement.otherPrice L b ≤ T - TK := by
    simp only [EnvelopeRefinement.otherPrice_eq, sum_sub_distrib]
    have h2 := hrepl L
    change _ - ∑ b, ∑ t ∈ PR.repl L b, _ ≤ _
    linarith
  have hsplit : ∀ g : BlockAtom Bk J L → ℝ, (∀ j, g (.inr j) = 0) →
      ∑ b, g b = ∑ β, g (.inl β) := fun g hg => by
    rw [Fintype.sum_sum_type]
    simp [hg]
  have hKLs : ∑ b, PR.toRefinement.KpriceL L b ≤ TK := by
    rw [hsplit _ (PR.KpriceL_tail L)]
    exact (sum_le_sum fun β _ => PR.KpriceL_inl_le L β).trans hKL
  have hKRs : ∑ b, PR.toRefinement.KpriceR L b ≤ TK := by
    rw [hsplit _ (PR.KpriceR_tail L)]
    exact (sum_le_sum fun β _ => PR.KpriceR_inl_le L β).trans hKR
  have eL : ∑ b, PR.toRefinement.priceL L b =
      ∑ b, PR.toRefinement.KpriceL L b + ∑ b, PR.toRefinement.otherPrice L b := by
    rw [← sum_add_distrib]
    rfl
  have eR : ∑ b, PR.toRefinement.priceR L b =
      ∑ b, PR.toRefinement.KpriceR L b + ∑ b, PR.toRefinement.otherPrice L b := by
    rw [← sum_add_distrib]
    rfl
  rw [eL, eR]
  constructor <;> linarith

end PrefixRefinement

/-- **The trivial prefix refinement** (non-vacuity): nothing replaced, nothing added, `KL = KR = 0`;
its prefix bracket is (CP3)'s. -/
noncomputable def trivialPrefixRefinement (GB : GramBracket a m₀ blk p S₀ FS)
    (CL : ComparisonLaw a m₀ blk p S₀ pp ep Q FS) : PrefixRefinement GB CL where
  repl _ _ := ∅
  IK _ _ := Empty
  IKFintype _ _ := inferInstanceAs (Fintype Empty)
  kL _ _ i := i.elim
  kR _ _ i := i.elim
  kL_nonneg _ _ i := i.elim
  kR_nonneg _ _ i := i.elim
  κK _ _ i := i.elim
  κK_pos _ _ i := i.elim
  κK_diag _ _ i := i.elim
  repl_tail _ _ := rfl
  kL_tail _ _ i := i.elim
  kR_tail _ _ i := i.elim
  bracket_pre L β := by
    simp only [Finset.univ_eq_empty, sum_empty, add_zero]
    exact GB.bracket L (.inl β)
  KL _ := 0
  KR _ := 0
  KL_bound _ _ := by simp
  KR_bound _ _ := by simp

end Sarkozy.EnvelopesPaper
