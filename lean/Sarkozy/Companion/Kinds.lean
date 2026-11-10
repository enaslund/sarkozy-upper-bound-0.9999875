module

public import Sarkozy.MainFinalF1b.E1
public import Sarkozy.ThetaOne.Inputs

@[expose] public section

/-!
# The open fields of (E1) and of `SF`, one definition per field (FC)

F1P's `MainFinalF1b.E1InputsAgg` and TH's `ThetaOne.SharpFirstBaseInputs` each mix fields of two
kinds (`TRUST_MAP.md` §3): a routine analytic lemma **(R)** (`hsub`, resp. `hfold`) and novel
core **(C)** (`hcoup`, `hrem`, resp. `hrem`). So that the companion statement can list them in
their groups, each field type is given a name here. The bodies are verbatim copies of the field
types; `E1InputsAgg.ofFields` and `SharpFirstBaseInputs.ofFields` rebuild the original structures
(definitionally), so Lean checks that the copies are exact.

* (E1): `E1R0`, `E1R` (the remainder types), **`E1Sub`** (R, `lem:bracket-energy`),
  **`E1Coup`** (C, `lem:sharp-first`, `lem:density:coupled`), **`E1Rem`** (C,
  `lem:record:density-lp`, `def:robust`), `E1InputsAgg.ofFields`;
* `SF`: `SFR` (the remainder type), `SFData` (the free data), **`SFFold`** (R,
  `prop:record:density-structured` on the folded energies of `lem:record:folded-energy`),
  **`SFRem`** (C, `lem:sharp-first`, the error terms), `SharpFirstBaseInputs.ofFields`.
-/

open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.Companion

open Sarkozy.EnvelopeInputsBlock Sarkozy.EnvelopeInputs
open Sarkozy.Param (Params)
open Sarkozy.BlockFrame
open Sarkozy.TheoremC Sarkozy.Comparison Sarkozy.PaperFrame Sarkozy.RecordExpansion
  Sarkozy.RecordExpansion.Choice Sarkozy.Structured ReflectionCut
open Sarkozy.MainFinalF1b Sarkozy.ThetaOne
open Sarkozy.MainFinal Sarkozy.MainFinal2

variable {a : ℝ}
  {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

/-! ## (E1) off the classes (`E1InputsAgg`) -/

/-- The type of the per-term remainders `r0` of the subset terms (`E1InputsAgg.r0`). -/
abbrev E1R0 (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) :=
  ∀ L, Finset ℤ → Choice (D.CL.T L) → (BlockAtom Bk J L → Bool) → ℝ

/-- The type of the per-term remainders `r` of the coupled pieces (`E1InputsAgg.r`). -/
abbrev E1R (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) :=
  ∀ L, Finset ℤ → (ω : Choice (D.CL.T L)) → (∀ b, Option (D.FS.Ib L b)) → D.FS.Tag →
    (∀ b, CEPiece D L b) → ℝ

/-- **(R) `E1.hsub`** (`lem:bracket-energy`, "`μ` off a selected set";
`prop:record:density-structured`): per selection and atom set, the subset-term energy is at most
the relative main term plus the free remainder `r0`. *Open*; alone trivially satisfiable, its
content is joint with `E1Rem`. -/
def E1Sub (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (εE : ℕ → ℝ) (r0 : E1R0 D) :
    Prop :=
  Param.AtCounterexamples (Params.ofDecay a) D.Y
    (fun L A => ∀ ω : Choice (D.CL.T L), IsSelection ω →
    ∀ f : BlockAtom Bk J L → Bool,
    |diagonalIntegral (tensorLaw fun b => if f b then
    (if (ω b).isSome then 0 else ∑ i, D.GB.κu L b i)
    else entryFactor (D.R.law p L b) (D.CL.D L b) (ω b)) (blockLift m₀ blk p L A)| ≤
    ((1 + εE L) * (∏ b ∈ Choice.support ω, TheoremCBlock.selectionFactor a p D.S.selPre L b) *
    D.Y L A) * ∏ b, (if f b then (if (ω b).isSome then 0 else D.GB.uprice L b) else 1) +
    r0 L A ω f)

/-- **(C) `E1.hcoup`** (`lem:sharp-first`, `lem:density:coupled`, `prop:density:production`): the
coupled envelope pieces, with the free remainder `r`. *Open*; alone trivially satisfiable, its
content is joint with `E1Rem`. -/
def E1Coup (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (εE : ℕ → ℝ) (r : E1R D) :
    Prop :=
  Param.AtCounterexamples (Params.ofDecay a) D.Y
    (fun L A => ∀ ω : Choice (D.CL.T L), IsSelection ω →
    ∀ σ : (∀ b, Option (D.FS.Ib L b)), σ ≠ (fun _ => none) → ∀ j,
    1 ≤ countVec (D.FS.tag L) σ j → ∀ f : (∀ b, CEPiece D L b),
    (∀ b, ecpieceCoef D L ω σ j b (f b) ≠ 0) →
    |diagonalIntegral (tensorLaw fun b => ecpieceK D L ω b (f b)) (blockLift m₀ blk p L A)| ≤
    (∏ b, ecpieceG D L ω b (f b)) * ((1 + εE L) * D.Y L A) + r L A ω σ j f)

/-- **(C) `E1.hrem`** (`lem:record:density-lp`, `def:robust`; `10_comparison_lemmas.tex`
ll. 126–140): the price-weighted sum of the remainders `r0`, `r` over the selections is at most
`c_E L^{-σ} α`. *Open*. -/
def E1Rem (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (cE : ℝ) (r0 : E1R0 D)
    (r : E1R D) : Prop :=
  Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
    ∑ ω ∈ univ.filter (fun ω : Choice (D.CL.T L) => IsSelection ω),
      monomial (D.CL.πt L) ω *
        (∑ f, r0 L A ω f +
          ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
            ∑ j, ∑ f, (∏ b, |ecpieceCoef D L ω σ j b (f b)|) * r L A ω σ j f) ≤
        remainder cE L A)

/-- `E1InputsAgg` from its fields, with the three open fields stated by `E1Sub`, `E1Coup`,
`E1Rem` (definitional). -/
def E1InputsAgg.ofFields (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (εE : ℕ → ℝ)
    (hε0 : ∀ L, 0 ≤ εE L) (hεt : Tendsto εE atTop (𝓝 0)) (cE : ℝ) (hcE : 0 ≤ cE)
    (r0 : E1R0 D) (r : E1R D) (hsub : E1Sub D εE r0) (hcoup : E1Coup D εE r)
    (hrem : E1Rem D cE r0 r) (hr0 : ∀ L A ω σ j f, 0 ≤ r L A ω σ j f)
    (hs0 : ∀ L A ω f, 0 ≤ r0 L A ω f) : E1InputsAgg D where
  εE := εE
  hε0 := hε0
  hεt := hεt
  cE := cE
  hcE := hcE
  r0 := r0
  r := r
  hsub := hsub
  hcoup := hcoup
  hrem := hrem
  hr0 := hr0
  hs0 := hs0

/-! ## `SF` on the baseline route (`SharpFirstBaseInputs`) -/

/-- The type of the remainders `rp`, `rm` of the two folded energies. -/
abbrev SFR (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) :=
  ∀ L, Finset ℤ → (∀ b, Option (D.FS.Ib L b)) → D.FS.Tag → (∀ b, WPiece D L b) → ℝ

/-- **The free data of `SF`** (`SharpFirstBaseInputs` without its side conditions and its two
open fields): the sharp decompositions `dec` of the differences (`lem:sharp-first`), the
relative error `ε`, the constant `c` and the remainders `rp`, `rm` of the folded energies. -/
structure SFData (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) : Type 1 where
  dec : ∀ L, DecFamily D L
  ε : ℕ → ℝ
  c : ℝ
  rp : SFR D
  rm : SFR D

/-- **(R) `SF.hfold`** (`prop:record:density-structured` on the folded energies of
`lem:record:folded-energy`, per piece of the whole-difference expansion of `lem:sharp-first`):
the two folded energies are at most `(∏ g)(1 + ε)Y` plus the free remainders `rp`, `rm`. *Open*;
alone trivially satisfiable (`hfold_satisfiable`), its content is joint with `SFRem`. -/
def SFFold (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (dec : ∀ L, DecFamily D L)
    (ε : ℕ → ℝ) (rp rm : SFR D) : Prop :=
  Param.AtCounterexamples (Params.ofDecay a) D.Y
      (fun L A => ∀ σ : (∀ b, Option (D.FS.Ib L b)),
    σ ≠ (fun _ => none) → ∀ j, 1 ≤ countVec (D.FS.tag L) σ j → ∀ f,
    foldedPlus (D.FS.cut j) (wpieceLp (dec L) j) (fun _ => blockLift m₀ blk p L A) f ≤
        (∏ b, wpieceG D L b (f b)) * ((1 + ε L) * D.Y L A) + rp L A σ j f ∧
      foldedMinus (D.FS.cut j) (wpieceLm (dec L) j) (fun _ => blockLift m₀ blk p L A) f ≤
        (∏ b, wpieceG D L b (f b)) * ((1 + ε L) * D.Y L A) + rm L A σ j f)

/-- **(C) `SF.hrem`** (`lem:sharp-first`, "the error terms are density-linear"): the weighted
remainders `rp`, `rm` sum to at most `c L^{-σ} α`. *Open*. -/
def SFRem (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (c : ℝ) (rp rm : SFR D) : Prop :=
  Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
    ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
      ∑ j, ∑ f, choiceWeight (wpieceCoef σ j) (wpieceD D L) f *
        ((rp L A σ j f + rm L A σ j f) / 2) ≤ remainder c L A)

/-- `SharpFirstBaseInputs` from its fields, with the two open fields stated by `SFFold`, `SFRem`
(definitional). -/
def SharpFirstBaseInputs.ofFields (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)
    (dec : ∀ L, DecFamily D L) (ε : ℕ → ℝ) (hε0 : ∀ L, 0 ≤ ε L) (hεt : Tendsto ε atTop (𝓝 0))
    (c : ℝ) (hc : 0 ≤ c) (rp rm : SFR D) (hr0 : ∀ L A σ j f, 0 ≤ rp L A σ j f ∧ 0 ≤ rm L A σ j f)
    (hfold : SFFold D dec ε rp rm) (hrem : SFRem D c rp rm) : SharpFirstBaseInputs D where
  dec := dec
  ε := ε
  hε0 := hε0
  hεt := hεt
  c := c
  hc := hc
  rp := rp
  rm := rm
  hr0 := hr0
  hfold := hfold
  hrem := hrem

end Sarkozy.Companion
