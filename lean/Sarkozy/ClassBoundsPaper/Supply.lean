module

public import Sarkozy.ClassBoundsPaper.Inputs
public import Sarkozy.ClassBoundsPaper.Families

@[expose] public section

/-!
# `ClassInputs` from the envelope and variance families

`ClassInputs.ofFamilies` builds `ClassInputs CL` from its data fields and two robust class bounds,
one per family of the paper, each uniformly within the family with nonnegative relative errors and
remainders (`robust_of_families`):

* `EnvelopeFamilyRobust`: the degree classes `𝒞_n` (`thm:envelopes`(i), `cor:envelope-costs`),
  with the class bound `C_n π^arm_ω + B'(∏(π^lead + π^rem) − ∏ π^lead)` (on a degree class
  `replacedBound` is this bound);
* `VarianceFamilyRobust`: the variance classes (`cor:var-classes`, `lem:var-gain`,
  `cor:variance:final`(i), (iii)), with the class cost `vcost(ω) π_ω`.

Both are *hypotheses*: the analytic content of Sections 22–23 for the comparison law `CL`.
-/

open Finset Filter
open scoped Topology BigOperators

namespace Sarkozy.ClassBoundsPaper

open Sarkozy.RecordExpansion Sarkozy.RecordExpansion.Choice Sarkozy.TheoremCBlock
open Sarkozy.TheoremC Sarkozy.BlockFrame
open Sarkozy.Param (Params)
open Sarkozy.FourierArithmetic Sarkozy.Functional Sarkozy.IndexSupport Sarkozy.Comparison
  Sarkozy.PaperFrame

variable {a : ℝ} {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {S₀ : Bk → ℝ} {pp ep : J₀ → ℕ} {E : Type} {Q : Queries E} {R : Reference m₀ blk}
  {FS : FirstStage a m₀ blk p S₀ R}

variable (CL : ComparisonLaw a m₀ blk p S₀ pp ep Q FS)

/-- **The robust class bounds of the envelope classes** (`thm:envelopes`(i), `cor:envelope-costs`;
`def:robust`), uniformly in the degree classes, for the class data `N`, `kind`, `vcls` and the
class bound `replacedBound` (on `𝒞_n`: `C_n π^arm_ω + B'(∏(π^lead + π^rem) − ∏ π^lead)`). -/
def EnvelopeFamilyRobust (N : Finset (Fin 3 → ℕ)) (C : (Fin 3 → ℕ) → ℝ) (Bp : ℝ)
    (kind : ∀ L, PriceVar (CL.T L) → Option (Fin 3)) (yarm ylead yrem : ∀ L, PriceVar (CL.T L) → ℝ)
    (V : ℕ → Type) [∀ L, DecidableEq (V L)] (vcls : ∀ L, Choice (CL.T L) → Option (V L))
    (vcost : ∀ L, Choice (CL.T L) → ℝ) : Prop :=
  ∃ ε : ℕ → ℝ, (∀ L, 0 ≤ ε L) ∧ Tendsto ε atTop (𝓝 0) ∧ ∃ c : ℝ, 0 ≤ c ∧
    ∃ r : ∀ L, Finset ℤ → Choice (CL.T L) → ℝ, (∀ L A ω, 0 ≤ r L A ω) ∧
    Param.AtCounterexamples (Params.ofDecay a) (energyFirst (R.law p) (blockLift m₀ blk p))
      fun L A =>
        (∀ i, ∑ ω ∈ (univ.filter fun ω : Choice (CL.T L) => IsSelection ω).filter
            (fun ω => paperCls N (kind L) (vcls L) ω = some (Sum.inl i)),
              |term (FS.lam L) (CL.ζ L) (blockLift m₀ blk p L A) ω| ≤
          ∑ ω ∈ (univ.filter fun ω : Choice (CL.T L) => IsSelection ω).filter
              (fun ω => paperCls N (kind L) (vcls L) ω = some (Sum.inl i)),
            ((replacedBound (kind L) N C Bp (yarm L) (ylead L) (yrem L) (vcost L) (CL.π L) ω +
                ε L * monomial (CL.π L) ω) *
                energyFirst (R.law p) (blockLift m₀ blk p) L A + r L A ω)) ∧
        ∑ ω ∈ univ.filter (fun ω : Choice (CL.T L) => IsSelection ω), r L A ω ≤ remainder c L A

/-- **The robust class bounds of the variance classes** (`cor:var-classes`, `lem:var-gain`;
`def:robust`), uniformly in the variance classes (on them `replacedBound` is `vcost(ω) π_ω`). -/
def VarianceFamilyRobust (N : Finset (Fin 3 → ℕ)) (C : (Fin 3 → ℕ) → ℝ) (Bp : ℝ)
    (kind : ∀ L, PriceVar (CL.T L) → Option (Fin 3)) (yarm ylead yrem : ∀ L, PriceVar (CL.T L) → ℝ)
    (V : ℕ → Type) [∀ L, DecidableEq (V L)] (vcls : ∀ L, Choice (CL.T L) → Option (V L))
    (vcost : ∀ L, Choice (CL.T L) → ℝ) : Prop :=
  ∃ ε : ℕ → ℝ, (∀ L, 0 ≤ ε L) ∧ Tendsto ε atTop (𝓝 0) ∧ ∃ c : ℝ, 0 ≤ c ∧
    ∃ r : ∀ L, Finset ℤ → Choice (CL.T L) → ℝ, (∀ L A ω, 0 ≤ r L A ω) ∧
    Param.AtCounterexamples (Params.ofDecay a) (energyFirst (R.law p) (blockLift m₀ blk p))
      fun L A =>
        (∀ i, ∑ ω ∈ (univ.filter fun ω : Choice (CL.T L) => IsSelection ω).filter
            (fun ω => paperCls N (kind L) (vcls L) ω = some (Sum.inr i)),
              |term (FS.lam L) (CL.ζ L) (blockLift m₀ blk p L A) ω| ≤
          ∑ ω ∈ (univ.filter fun ω : Choice (CL.T L) => IsSelection ω).filter
              (fun ω => paperCls N (kind L) (vcls L) ω = some (Sum.inr i)),
            ((replacedBound (kind L) N C Bp (yarm L) (ylead L) (yrem L) (vcost L) (CL.π L) ω +
                ε L * monomial (CL.π L) ω) *
                energyFirst (R.law p) (blockLift m₀ blk p) L A + r L A ω)) ∧
        ∑ ω ∈ univ.filter (fun ω : Choice (CL.T L) => IsSelection ω), r L A ω ≤ remainder c L A

/-- **`ClassInputs` from the two families**: the data fields and the robust bounds of the envelope
and variance classes; `robust` is `robust_of_families`. The bound `n_max` is asked of the variance
classes only: a selection of a degree class `𝒞_n` has `|n|` atoms
(`card_support_of_mem_kindMonos`). -/
noncomputable def ClassInputs.ofFamilies (N : Finset (Fin 3 → ℕ))
    (hN : ∀ n ∈ N, n ≠ 0 ∧ Even (∑ l, n l)) (C : (Fin 3 → ℕ) → ℝ) (C_nonneg : ∀ n ∈ N, 0 ≤ C n)
    (Bp : ℝ) (Bp_nonneg : 0 ≤ Bp) (π_nonneg : ∀ L b t e, 0 ≤ CL.π L b t e)
    (kind : ∀ L, PriceVar (CL.T L) → Option (Fin 3))
    (kind_skew : ∀ L v l, kind L v = some l → v.2.2 = .skew)
    (yarm ylead yrem : ∀ L, PriceVar (CL.T L) → ℝ) (yarm_nonneg : ∀ L v, 0 ≤ yarm L v)
    (ylead_nonneg : ∀ L v, 0 ≤ ylead L v) (yrem_nonneg : ∀ L v, 0 ≤ yrem L v)
    (V : ℕ → Type) [∀ L, Fintype (V L)] [∀ L, DecidableEq (V L)]
    (vcls : ∀ L, Choice (CL.T L) → Option (V L)) (vcost : ∀ L, Choice (CL.T L) → ℝ)
    (vcost_nonneg : ∀ L ω, 0 ≤ vcost L ω) (nmax : ℕ) (nmax_deg : ∀ n ∈ N, ∑ l, n l ≤ nmax)
    (nmax_var : ∀ L (ω : Choice (CL.T L)), IsSelection ω → vcls L ω ≠ none →
      (Choice.support ω).card ≤ nmax)
    (henv : EnvelopeFamilyRobust CL N C Bp kind yarm ylead yrem V vcls vcost)
    (hvar : VarianceFamilyRobust CL N C Bp kind yarm ylead yrem V vcls vcost) :
    ClassInputs CL where
  N := N
  hN := hN
  C := C
  C_nonneg := C_nonneg
  Bp := Bp
  Bp_nonneg := Bp_nonneg
  π_nonneg := π_nonneg
  kind := kind
  kind_skew := kind_skew
  yarm := yarm
  ylead := ylead
  yrem := yrem
  yarm_nonneg := yarm_nonneg
  ylead_nonneg := ylead_nonneg
  yrem_nonneg := yrem_nonneg
  V := V
  vcls := vcls
  vcost := vcost
  vcost_nonneg := vcost_nonneg
  nmax := nmax
  nmax_bound L ω hω h := by
    rcases h with h | h
    · obtain ⟨n, hn, hm⟩ := mem_biUnion.mp h
      rw [card_support_of_mem_kindMonos hm]
      exact nmax_deg n hn
    · exact nmax_var L ω hω h
  robust := robust_of_families (fun L => paperCls N (kind L) (vcls L))
    (fun L => univ.filter fun ω : Choice (CL.T L) => IsSelection ω)
    (fun L A ω => |term (FS.lam L) (CL.ζ L) (blockLift m₀ blk p L A) ω|)
    (fun L ω => replacedBound (kind L) N C Bp (yarm L) (ylead L) (yrem L) (vcost L) (CL.π L) ω)
    (fun L ω => monomial (CL.π L) ω) (fun L ω => monomial_nonneg (π_nonneg L) ω) henv hvar

end Sarkozy.ClassBoundsPaper
