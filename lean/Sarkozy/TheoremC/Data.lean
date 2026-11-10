module

public import Sarkozy.TheoremC.Defs
public import Sarkozy.TheoremC.FirstStage
public import Sarkozy.TheoremC.Wrap
public import Sarkozy.PaperFrame.StepInvariance

@[expose] public section

/-!
# Hypotheses (CP1)–(CP8) on the three laws (`def:cp1` … `def:cp8`)

`paper/sections/09_comparison_theorem.tex`, `subsec:cp:hypotheses`. The structures are
stated over the standing data (CP0) of `Sarkozy.TheoremC.Defs`, at every scale `L`, with
the paper's atoms `PaperAtom J L` and alphabets `AtomLabel m₀ p L b`. Each structure takes
the previous ones as parameters: the reference `μ` (CP1), the first stage `λ` (CP2), the
bracket `Ñ` (CP3), the comparison law `ν` (CP4), the optional class bounds (CP5), the
matching envelopes `M_L, M_R` (CP6), the mean credit `m` (CP7), summability (CP8)(c).
Totals are numbers bounding the corresponding sums over the atoms of every scale (see
the module docstring of `Defs`).
-/

open Filter Finset Function
open scoped Topology BigOperators Matrix

namespace Sarkozy.TheoremC

open Sarkozy.FourierArithmetic Sarkozy.Functional Sarkozy.IndexSupport Sarkozy.Comparison
  Sarkozy.PaperFrame Sarkozy.RecordExpansion Sarkozy.RecordExpansion.Choice

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] (m₀ : J₀ → ℕ) [∀ i, NeZero (m₀ i)]
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] (p : ∀ L, J L → ℕ)
  [∀ L j, NeZero (p L j)]

/-! ## (CP1) Reference -/

/-- **(CP1) Reference** (`def:cp1`). The reference at scale `N` is the product
`μ = ⊗_𝔟 μ_𝔟` of the prefix law `μ₀` and the tail laws `μ_p` (`refLaws`, whose tensor is
`paperLaw`). It satisfies (R1)–(R3) of `hyp:record:reference`, with (R2) at every cut of
`𝔉`, and the part of (R4) that concerns `μ`: at every tail prime `p ≥ P₅`, `μ_p` is
`(γ, v)`-mixing for every slot `v`. (R1) is built in: the laws are probability laws
(`FiniteLaw`) indexed by the atom (the prefix, or the prime `q`), hence independent of the
scale. -/
structure Reference where
  μ₀ : FiniteLaw (Slot → ResidueSpace m₀)
  μp : ∀ (q : ℕ) [NeZero q], FiniteLaw (Slot → ZMod q)
  /-- (R2) at every cut of the family. -/
  rp₀ : FamilyReflectionPositive (signedIntegral μ₀.weight)
  rpp : ∀ (q : ℕ) [NeZero q], q.Prime → FamilyReflectionPositive (signedIntegral (μp q).weight)
  /-- (R3) square-affine invariance: `z_{v,p} ↦ r_p z_{v,p} + c_p` with square units `r_p`,
  independently at the prefix coordinates. -/
  inv₀ : ∀ (a : ∀ i, (ZMod (m₀ i))ˣ) (b : ResidueSpace m₀),
    (∀ i, IsSquare ((a i : ZMod (m₀ i)))) → ∀ F : (Slot → ResidueSpace m₀) → ℝ,
      μ₀.expect (fun z => F (fun v => piAffineEquiv m₀ a b (z v))) = μ₀.expect F
  invp : ∀ (q : ℕ) [NeZero q] (a : (ZMod q)ˣ) (b : ZMod q), IsSquare (a : ZMod q) →
    ∀ F : (Slot → ZMod q) → ℝ,
      (μp q).expect (fun z => F (fun v => affineEquiv a b (z v))) = (μp q).expect F
  /-- (R3): every one-slot marginal is uniform. -/
  unif₀ : HasUniformMarginals μ₀
  unifp : ∀ (q : ℕ) [NeZero q], q.Prime → HasUniformMarginals (μp q)
  /-- The threshold `P₅` of (R4). -/
  P5 : ℕ
  /-- (R4), the part that concerns `μ`. -/
  mixing : ∀ (q : ℕ) [NeZero q], q.Prime → P5 ≤ q → ∀ v : Slot,
    Sarkozy.Mixing.IsGammaMixing q Sarkozy.AnalyticStage.γ (μp q) {v}

/-- The reference law of the atom `b` at the scale `L`. -/
noncomputable abbrev Reference.law {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)] (R : Reference m₀) :
    ∀ L (b : PaperAtom J L), AtomMeasure m₀ p L b :=
  refLaws m₀ p R.μ₀ R.μp

/-! ## (CP2) First stage -/

/-- **(CP2) First stage** (`def:cp2`). First-stage atoms `𝒜^fs` (at each scale), a finite
set `𝔗` of tags with cuts `c_j ∈ 𝔉`, and on the first-stage atoms signed measures `ρ_𝔟`
and `δ_{E,𝔟}` such that
(a) `ρ_𝔟 - μ_𝔟 = ∑_i c_i κ_i` is a finite real combination of positive records, with
variation price `p_𝔟 = ∑_i |c_i| κ_i(1) q_𝔟^{2a}`, and `ρ_𝔟 ⪰_{ϑ₀} μ_𝔟` at one cut
`ϑ₀ ∈ 𝔉`, the same for all first-stage atoms;
(b) `δ_{E,𝔟} = ∑_i (κ'_{𝔟,i} - κ_{𝔟,i})` is a finite sum of differences of positive records
of equal mass; each difference carries a tag `j(𝔟,i)` and has a sharp bound relative to
`κ_{𝔟,i}` at the cut of its tag (`def:price`(b)), with sharp price `d_{𝔟,i}` and variation
price `v_{𝔟,i} = (κ_{𝔟,i}(1) + κ'_{𝔟,i}(1)) q_𝔟^{2a}`.
Off the first-stage atoms `ρ_𝔟 = μ_𝔟` and there are no differences. The totals `P`, `d_j`,
`v_j` bound the sums over the atoms of every scale. -/
structure FirstStage (selPre : ℝ) (R : Reference m₀) where
  fs : ∀ L, Finset (PaperAtom J L)
  Tag : Type
  [tagFintype : Fintype Tag]
  [tagDecEq : DecidableEq Tag]
  cut : Tag → ReflectionCut Slot
  cut_family : ∀ j, IsFamilyCut (cut j)
  ϑ₀ : ReflectionCut Slot
  ϑ₀_family : IsFamilyCut ϑ₀
  ρ : ∀ L b, AtomMeasure m₀ p L b
  Ia : ∀ L, PaperAtom J L → Type
  [IaFintype : ∀ L b, Fintype (Ia L b)]
  ca : ∀ L b, Ia L b → ℝ
  κa : ∀ L b, Ia L b → AtomMeasure m₀ p L b
  κa_pos : ∀ L b i, IsPositiveRecord (κa L b i)
  ρ_sub : ∀ L b, ρ L b - R.law p L b = ∑ i, ca L b i • κa L b i
  ρ_ge : ∀ L b, b ∈ fs L → ϑ₀.Below (R.law p L b) (ρ L b)
  ρ_off : ∀ L b, b ∉ fs L → ρ L b = R.law p L b
  Ib : ∀ L, PaperAtom J L → Type
  [IbFintype : ∀ L b, Fintype (Ib L b)]
  [IbDecEq : ∀ L b, DecidableEq (Ib L b)]
  κ : ∀ L b, Ib L b → AtomMeasure m₀ p L b
  κ' : ∀ L b, Ib L b → AtomMeasure m₀ p L b
  κ_pos : ∀ L b i, IsPositiveRecord (κ L b i)
  κ'_pos : ∀ L b i, IsPositiveRecord (κ' L b i)
  mass_eq : ∀ L b i, mass (κ' L b i) = mass (κ L b i)
  tag : ∀ L b, Ib L b → Tag
  /-- The sharp constant of the difference `κ' - κ` at the cut of its tag. -/
  dconst : ∀ L b, Ib L b → ℝ
  dconst_nonneg : ∀ L b i, 0 ≤ dconst L b i
  sharp : ∀ L b i, HasSharpBound (cut (tag L b i)) (κ L b i) (κ' L b i - κ L b i) (dconst L b i)
  off : ∀ L b, b ∉ fs L → IsEmpty (Ib L b)
  /-- The total variation price `P`. -/
  P : ℝ
  /-- The tag totals `d_j`, `v_j`. -/
  dT : Tag → ℝ
  vT : Tag → ℝ
  P_total : ∀ L, ∑ b, ∑ i, |ca L b i| * mass (κa L b i) * selectionFactor p selPre L b ≤ P
  dT_total : ∀ L j, ∑ b, ∑ i, (if tag L b i = j then
    sharpPrice (selectionFactor p selPre L b) (κ L b i) (dconst L b i) else 0) ≤ dT j
  vT_total : ∀ L j, ∑ b, ∑ i, (if tag L b i = j then
    (mass (κ L b i) + mass (κ' L b i)) * selectionFactor p selPre L b else 0) ≤ vT j

attribute [instance] FirstStage.tagFintype FirstStage.tagDecEq FirstStage.IaFintype
  FirstStage.IbFintype FirstStage.IbDecEq

namespace FirstStage

variable {m₀ p} {selPre : ℝ} {R : Reference m₀} (FS : FirstStage m₀ p selPre R)

/-- The first stage `λ_𝔟 = ρ_𝔟 + δ_{E,𝔟}` (`λ_𝔟 = μ_𝔟` off the first-stage atoms). -/
noncomputable def lam (L : ℕ) (b : PaperAtom J L) : AtomMeasure m₀ p L b :=
  FS.ρ L b + ∑ i, (FS.κ' L b i - FS.κ L b i)

/-- The variation price `p_𝔟`. -/
noncomputable def pvar (L : ℕ) (b : PaperAtom J L) : ℝ :=
  ∑ i, |FS.ca L b i| * mass (FS.κa L b i) * selectionFactor p selPre L b

/-- The sharp price `d_{𝔟,i}`. -/
noncomputable def dprice (L : ℕ) (b : PaperAtom J L) (i : FS.Ib L b) : ℝ :=
  sharpPrice (selectionFactor p selPre L b) (FS.κ L b i) (FS.dconst L b i)

/-- The variation price `v_{𝔟,i}`. -/
noncomputable def vprice (L : ℕ) (b : PaperAtom J L) (i : FS.Ib L b) : ℝ :=
  (mass (FS.κ L b i) + mass (FS.κ' L b i)) * selectionFactor p selPre L b

/-- The cost `L₀ = e^P 𝔗(d, v)` of the first stage. -/
noncomputable def L₀ : ℝ := firstStageCost FS.P FS.dT FS.vT

end FirstStage

/-! ## (CP3) Gram bracket -/

/-- **(CP3) Gram bracket** (`def:cp3`). The bracket `Ñ = ⊗_𝔟 Ñ_𝔟` with `Ñ_𝔟 = μ_𝔟` off the
first-stage atoms and `Ñ_𝔟 = Ñ_{0,𝔟} + δ_{E,𝔟}` on them, where `Ñ_{0,𝔟} - μ_𝔟` is a finite
sum of positive reserved-diagonal records, of total price `u_𝔟`, such that for every atom
`λ_𝔟` is symmetric at `ι`, `Ñ_𝔟` is nonnegative, and `(Ñ_𝔟 λ_𝔟; λ_𝔟 Ñ_𝔟) ⪰_ι 0`
(equivalently `Ñ_𝔟 ± λ_𝔟 ⪰_ι 0`, `lem:record:block-gram`(d)). `U₀` bounds `∑_𝔟 u_𝔟`. -/
structure GramBracket (selPre : ℝ) {R : Reference m₀} (FS : FirstStage m₀ p selPre R) where
  Iu : ∀ L, PaperAtom J L → Type
  [IuFintype : ∀ L b, Fintype (Iu L b)]
  κu : ∀ L b, Iu L b → AtomMeasure m₀ p L b
  κu_pos : ∀ L b i, IsPositiveRecord (κu L b i)
  κu_diag : ∀ L b i, IsDiagonalAt reservedCut (κu L b i)
  N₀ : ∀ L b, AtomMeasure m₀ p L b
  N₀_sub : ∀ L b, N₀ L b - R.law p L b = ∑ i, κu L b i
  N₀_off : ∀ L b, b ∉ FS.fs L → N₀ L b = R.law p L b
  lam_sym : ∀ L b, IsSymmetricAt reservedCut (FS.lam L b)
  N_nonneg : ∀ L b, IsNonneg (N₀ L b + ∑ i, (FS.κ' L b i - FS.κ L b i))
  bracket : ∀ L b, reservedCut.Bracket (N₀ L b + ∑ i, (FS.κ' L b i - FS.κ L b i))
    (FS.lam L b) (N₀ L b + ∑ i, (FS.κ' L b i - FS.κ L b i))
  U₀ : ℝ
  U₀_total : ∀ L, ∑ b, ∑ i, mass (κu L b i) * selectionFactor p selPre L b ≤ U₀

attribute [instance] GramBracket.IuFintype

namespace GramBracket

variable {m₀ p} {selPre : ℝ} {R : Reference m₀} {FS : FirstStage m₀ p selPre R}
  (GB : GramBracket m₀ p selPre FS)

/-- The bracket law `Ñ_𝔟 = Ñ_{0,𝔟} + δ_{E,𝔟}`. -/
noncomputable def N (L : ℕ) (b : PaperAtom J L) : AtomMeasure m₀ p L b :=
  GB.N₀ L b + ∑ i, (FS.κ' L b i - FS.κ L b i)

/-- The price `u_𝔟` of `Ñ_{0,𝔟} - μ_𝔟`. -/
noncomputable def uprice (L : ℕ) (b : PaperAtom J L) : ℝ :=
  ∑ i, mass (GB.κu L b i) * selectionFactor p selPre L b

/-- `R_err = e^{U₀} 𝔗(d, v)`. -/
noncomputable def Rerr : ℝ := Real.exp GB.U₀ * tagSeries FS.dT FS.vT

/-- The energy factor `B = e^{U₀} + R_err` of the bracket. -/
noncomputable def B : ℝ := Real.exp GB.U₀ + GB.Rerr

end GramBracket

/-! ## (CP4) Comparison law -/

/-- The symmetric (`ζ^s`) or skew (`ζ^a`) part at `ι` of a change. -/
noncomputable def changePart {X : Type} [Fintype X] : ChangeType → SlotMeasure X → SlotMeasure X
  | .sym => symPart reservedCut
  | .skew => skewPart reservedCut

/-- **(CP4) Comparison law** (`def:record:comparison-law`). A product `ν = ⊗_𝔟 ν_𝔟` of
finite signed measures, each a finite real combination `ν_𝔟 = ∑_i c_{𝔟,i} ν_{𝔟,i}` of
nonnegative measures (its components; `ν_{𝔟,i} = w_{𝔟,i} ν̄_{𝔟,i}` with mass `w > 0` and
normalized component `ν̄_{𝔟,i}`), with `ν_𝔟(1) > 0`, and with the number of product
components bounded by `n_ν` at every scale (the paper: `|I_𝔟| = 1`, `c = 1` at all but
finitely many atoms), such that
(a) *acceptance*: every query is accepted by every component (`AcceptedPair`
`ν̄`-almost surely), all one-slot marginals of every component are uniform, and the part of
(R4) that concerns `ν̄` holds at the tail primes `p ≥ P₅` for the queries ((R5) is the
acceptance itself);
(b) *records and brackets*: `ν_𝔟 - λ_𝔟 = ∑_t (ζ^s_{𝔟,t} + ζ^a_{𝔟,t})`, where `ζ^s, ζ^a` are the
symmetric and skew parts at `ι` of the change `Δ_{𝔟,t}` of the record `t`, and there are
reserved-diagonal probability laws `D^ε_{𝔟,t}` with uniform one-slot marginals and numbers
`π̃^ε_{𝔟,t} ≥ 0` with `(π̃ D  ζ; ζ*  π̃ D) ⪰_ι 0`; the prices are `π^ε = π̃^ε q_𝔟^{2a}`, with
totals `S` (symmetric) and `A` (skew);
(c) *selections* are the `Choice`s of `Sarkozy.RecordExpansion` with `IsSelection` (a
nonempty set of atoms with a record and a type at each, an even number of skew types);
their measure, monomial and term are `choiceLaw`, `monomial`, `term`.
The variation factor `𝔳_ν = ∏_𝔟 |ν|_𝔟/ν_𝔟(1)` is bounded by `vfac` at every scale. -/
structure ComparisonLaw (S₀ : ℝ) (pp ep : J₀ → ℕ) {E : Type} (Q : Queries E)
    {R : Reference m₀} (FS : FirstStage m₀ p S₀ R) where
  Ic : ∀ L, PaperAtom J L → Type
  [IcFintype : ∀ L b, Fintype (Ic L b)]
  cc : ∀ L b, Ic L b → ℝ
  cmass : ∀ L b, Ic L b → ℝ
  claw : ∀ L b, Ic L b → FiniteLaw (Slot → AtomLabel m₀ p L b)
  cmass_pos : ∀ L b i, 0 < cmass L b i
  mass_pos : ∀ L b, 0 < ∑ i, cc L b i * cmass L b i
  nν : ℕ
  nν_bound : ∀ L, ∏ b, Fintype.card (Ic L b) ≤ nν
  accept : ∀ L b i (z : Slot → AtomLabel m₀ p L b), (claw L b i).weight z ≠ 0 →
    ∀ e, AcceptedPair m₀ p pp ep L b (z (Q.source e)) (z (Q.target e))
  unif : ∀ L b i, HasUniformMarginals (claw L b i)
  mixing : ∀ L (j : J L) i, R.P5 ≤ p L j →
    (∀ v : Slot, Sarkozy.Mixing.IsGammaMixing (p L j) Sarkozy.AnalyticStage.γ (claw L (some j) i) {v}) ∧
    ∀ e, PairUniformOmega (q := p L j) (claw L (some j) i) (Q.source e) (Q.target e) ∧
      Sarkozy.Mixing.IsGammaMixing (p L j) Sarkozy.AnalyticStage.γ (claw L (some j) i) {Q.source e, Q.target e}
  T : ∀ L, PaperAtom J L → Type
  [TFintype : ∀ L b, Fintype (T L b)]
  [TDecEq : ∀ L b, DecidableEq (T L b)]
  Δ : ∀ L b, T L b → AtomMeasure m₀ p L b
  change : ∀ L b, (∑ i, (cc L b i * cmass L b i) • signedIntegral (claw L b i).weight) -
    FS.lam L b = ∑ t, Δ L b t
  D : ∀ L b, T L b → ChangeType → AtomMeasure m₀ p L b
  D_prob : ∀ L b t e, IsProbability (D L b t e)
  D_diag : ∀ L b t e, IsDiagonalAt reservedCut (D L b t e)
  D_unif : ∀ L b t e, HasUniformSlotMarginals (D L b t e)
  πt : ∀ L b, T L b → ChangeType → ℝ
  πt_nonneg : ∀ L b t e, 0 ≤ πt L b t e
  bracket : ∀ L b t e, reservedCut.Bracket (πt L b t e • D L b t e)
    (changePart e (Δ L b t)) (πt L b t e • D L b t e)
  S : ℝ
  A : ℝ
  S_total : ∀ L, ∑ b, symTotal (fun b t e => πt L b t e * selectionFactor p S₀ L b) b ≤ S
  A_total : ∀ L, ∑ b, skewTotal (fun b t e => πt L b t e * selectionFactor p S₀ L b) b ≤ A
  vfac : ℝ
  vfac_bound : ∀ L, ∏ b, (∑ i, |cc L b i| * cmass L b i) / (∑ i, cc L b i * cmass L b i) ≤ vfac

attribute [instance] ComparisonLaw.IcFintype ComparisonLaw.TFintype ComparisonLaw.TDecEq

namespace ComparisonLaw

variable {m₀ p} {S₀ : ℝ} {pp ep : J₀ → ℕ} {E : Type} {Q : Queries E} {R : Reference m₀}
  {FS : FirstStage m₀ p S₀ R} (CL : ComparisonLaw m₀ p S₀ pp ep Q FS)

/-- The comparison law `ν_𝔟 = ∑_i c_{𝔟,i} ν_{𝔟,i}`. -/
noncomputable def ν (L : ℕ) (b : PaperAtom J L) : AtomMeasure m₀ p L b :=
  ∑ i, (CL.cc L b i * CL.cmass L b i) • signedIntegral (CL.claw L b i).weight

/-- The symmetric and skew parts `ζ^ε_{𝔟,t}` of the changes. -/
noncomputable def ζ (L : ℕ) (b : PaperAtom J L) (t : CL.T L b) (e : ChangeType) :
    AtomMeasure m₀ p L b :=
  changePart e (CL.Δ L b t)

/-- The prices `π^ε_{𝔟,t} = π̃^ε_{𝔟,t} q_𝔟^{2a}`. -/
noncomputable def π (L : ℕ) (b : PaperAtom J L) (t : CL.T L b) (e : ChangeType) : ℝ :=
  CL.πt L b t e * selectionFactor p S₀ L b

end ComparisonLaw

/-! ## (CP5) Class bounds (optional) -/

/-- **(CP5) Class bounds** (`def:cp5`, optional). For every atom finitely many auxiliary
prices `y_{𝔟,j} ≥ 0`, each attached to one record `t` and one type `ε`; pairwise disjoint
classes of selections (the fibres of `cls`), each selection of a class having at most
`n_max` atoms; and for every selection `ω` of a class a class bound `φ_ω`, a polynomial
with nonnegative coefficients in the auxiliary prices each of whose monomials is a product,
over the atoms of `ω`, of one auxiliary price attached to the record and type of `ω` there
(`coeff_support`); such that robustly and uniformly in the class
`∑_{ω∈𝒞} |I_ω| ≤ ∑_{ω∈𝒞} (φ_ω + o(1) π_ω) Y`. A class cost `c_𝒞` is the case
`φ_ω = c_𝒞 π_ω`, with the prices of the selected records as auxiliary prices. -/
structure ClassBounds {S₀ : ℝ} {pp ep : J₀ → ℕ} {E : Type} {Q : Queries E}
    {R : Reference m₀} {FS : FirstStage m₀ p S₀ R} (CL : ComparisonLaw m₀ p S₀ pp ep Q FS) where
  ι : ℕ → Type
  [ιFintype : ∀ L, Fintype (ι L)]
  [ιDecEq : ∀ L, DecidableEq (ι L)]
  cls : ∀ L, Choice (CL.T L) → Option (ι L)
  nmax : ℕ
  nmax_bound : ∀ L ω i, cls L ω = some i → (Choice.support ω).card ≤ nmax
  Jaux : ∀ L, PaperAtom J L → Type
  [JauxFintype : ∀ L b, Fintype (Jaux L b)]
  [JauxDecEq : ∀ L b, DecidableEq (Jaux L b)]
  y : ∀ L b, Jaux L b → ℝ
  y_nonneg : ∀ L b j, 0 ≤ y L b j
  attach : ∀ L b, Jaux L b → CL.T L b × ChangeType
  coeff : ∀ L, Choice (CL.T L) → (∀ b, Option (Jaux L b)) → ℝ
  coeff_nonneg : ∀ L ω m, 0 ≤ coeff L ω m
  coeff_support : ∀ L ω m, coeff L ω m ≠ 0 → ∀ b, (m b).map (attach L b) = ω b
  /-- The robust class bounds, uniformly in the classes: one relative error `ε`, one
  remainder constant `c` for the aggregated remainders `r`. -/
  robust : ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∃ c : ℝ, 0 ≤ c ∧
    ∃ r : ∀ L, Finset ℤ → Choice (CL.T L) → ℝ,
    AtCounterexamples (energyFirst (R.law p) (atomLift m₀ p)) fun L A =>
      (∀ i, ∑ ω ∈ (univ.filter fun ω : Choice (CL.T L) => IsSelection ω).filter
          (fun ω => cls L ω = some i), |term (FS.lam L) (CL.ζ L) (atomLift m₀ p L A) ω| ≤
        ∑ ω ∈ (univ.filter fun ω : Choice (CL.T L) => IsSelection ω).filter
            (fun ω => cls L ω = some i),
          ((∑ m, coeff L ω m * ∏ b, (m b).elim 1 (y L b) + ε L * monomial (CL.π L) ω) *
              energyFirst (R.law p) (atomLift m₀ p) L A + r L A ω)) ∧
      ∑ ω ∈ univ.filter (fun ω : Choice (CL.T L) => IsSelection ω), r L A ω ≤ remainder c L A

/-! ## (CP6) Matching envelopes -/

/-- **(CP6) Matching envelopes** (`def:cp6`). For `s ∈ {L, R}` and every atom, nonnegative
measures `M_{s,𝔟}` such that `M_{s,𝔟} - Ñ_𝔟` is a finite nonnegative combination of positive
reserved-diagonal records, of price `T_{s,𝔟}`, and `(M_{L,𝔟} ν_𝔟; ν_𝔟* M_{R,𝔟}) ⪰_ι 0` for
every atom. The matching exponent `T` bounds `∑_𝔟 T_{s,𝔟}` for both sides. -/
structure MatchingEnvelopes {S₀ : ℝ} {pp ep : J₀ → ℕ} {E : Type} {Q : Queries E}
    {R : Reference m₀} {FS : FirstStage m₀ p S₀ R} (GB : GramBracket m₀ p S₀ FS)
    (CL : ComparisonLaw m₀ p S₀ pp ep Q FS) where
  IL : ∀ L, PaperAtom J L → Type
  [ILFintype : ∀ L b, Fintype (IL L b)]
  IR : ∀ L, PaperAtom J L → Type
  [IRFintype : ∀ L b, Fintype (IR L b)]
  cL : ∀ L b, IL L b → ℝ
  cR : ∀ L b, IR L b → ℝ
  cL_nonneg : ∀ L b i, 0 ≤ cL L b i
  cR_nonneg : ∀ L b i, 0 ≤ cR L b i
  κL : ∀ L b, IL L b → AtomMeasure m₀ p L b
  κR : ∀ L b, IR L b → AtomMeasure m₀ p L b
  κL_pos : ∀ L b i, IsPositiveRecord (κL L b i)
  κR_pos : ∀ L b i, IsPositiveRecord (κR L b i)
  κL_diag : ∀ L b i, IsDiagonalAt reservedCut (κL L b i)
  κR_diag : ∀ L b i, IsDiagonalAt reservedCut (κR L b i)
  bracket : ∀ L b, reservedCut.Bracket (GB.N L b + ∑ i, cL L b i • κL L b i) (CL.ν L b)
    (GB.N L b + ∑ i, cR L b i • κR L b i)
  T : ℝ
  TL_total : ∀ L, ∑ b, ∑ i, cL L b i * mass (κL L b i) * selectionFactor p S₀ L b ≤ T
  TR_total : ∀ L, ∑ b, ∑ i, cR L b i * mass (κR L b i) * selectionFactor p S₀ L b ≤ T

attribute [instance] MatchingEnvelopes.ILFintype MatchingEnvelopes.IRFintype

namespace MatchingEnvelopes

variable {m₀ p} {S₀ : ℝ} {pp ep : J₀ → ℕ} {E : Type} {Q : Queries E} {R : Reference m₀}
  {FS : FirstStage m₀ p S₀ R} {GB : GramBracket m₀ p S₀ FS}
  {CL : ComparisonLaw m₀ p S₀ pp ep Q FS} (ME : MatchingEnvelopes m₀ p GB CL)

/-- The left envelope `M_{L,𝔟}`. -/
noncomputable def ML (L : ℕ) (b : PaperAtom J L) : AtomMeasure m₀ p L b :=
  GB.N L b + ∑ i, ME.cL L b i • ME.κL L b i

/-- The right envelope `M_{R,𝔟}`. -/
noncomputable def MR (L : ℕ) (b : PaperAtom J L) : AtomMeasure m₀ p L b :=
  GB.N L b + ∑ i, ME.cR L b i • ME.κR L b i

end MatchingEnvelopes

/-! ## (CP7) Mean energies -/

/-- **(CP7) Mean energies** (`def:cp7`). A number `m`, the mean credit, such that robustly
`½(e_L + e_R) ≥ (m - o(1)) Y`, with `e_s = Q_{⊗_𝔟 M_{s,𝔟}}(X̄, X̄)` the mean energy of the
envelope of the side `s` and `Y` the reference energy. -/
structure MeanCredit {S₀ : ℝ} {pp ep : J₀ → ℕ} {E : Type} {Q : Queries E}
    {R : Reference m₀} {FS : FirstStage m₀ p S₀ R} {GB : GramBracket m₀ p S₀ FS}
    {CL : ComparisonLaw m₀ p S₀ pp ep Q FS} (ME : MatchingEnvelopes m₀ p GB CL) where
  m : ℝ
  bound : RobustLower (energyFirst (R.law p) (atomLift m₀ p))
    (fun L A => (energyMean (atomLift m₀ p) ME.ML L A + energyMean (atomLift m₀ p) ME.MR L A) / 2) m

/-! ## (CP8) Admissibility, robustness, summability -/

/-- **(CP8) Summability** (`def:cp8`(c)), with `q_𝔟` the product of the primes of `𝔟` with
`e_p = 1` (`oneWeight`): `∑_𝔟 q_𝔟^{1/4}(p_𝔟 + v_𝔟 + d_𝔟 + u_𝔟 + s_𝔟 + a_𝔟 + T_{L,𝔟} + T_{R,𝔟})`
is finite (bounded at every scale); the auxiliary prices of (CP5) are added when (CP5) is
used. (CP8)(a): (O1) is imposed on every named law in the structures above; (O2)–(O4)
concern the reductions inside the analytic inputs. (CP8)(b): the bounds of (CP5) and (CP7)
are robust by their statement (`RobustLower`, `ClassBounds.robust`). -/
structure Summability {S₀ : ℝ} {pp ep : J₀ → ℕ} {E : Type} {Q : Queries E}
    {R : Reference m₀} {FS : FirstStage m₀ p S₀ R} {GB : GramBracket m₀ p S₀ FS}
    {CL : ComparisonLaw m₀ p S₀ pp ep Q FS} (ME : MatchingEnvelopes m₀ p GB CL) where
  bound : ℝ
  summable : ∀ L, ∑ b, oneWeight p pp ep L b ^ ((1 : ℝ) / 4) *
    (FS.pvar L b + ∑ i, FS.vprice L b i + ∑ i, FS.dprice L b i + GB.uprice L b +
      symTotal (CL.π L) b + skewTotal (CL.π L) b +
      ∑ i, ME.cL L b i * mass (ME.κL L b i) * selectionFactor p S₀ L b +
      ∑ i, ME.cR L b i * mass (ME.κR L b i) * selectionFactor p S₀ L b) ≤ bound

end Sarkozy.TheoremC
