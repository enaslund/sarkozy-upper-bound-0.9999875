module

public import Sarkozy.BracketEnergy.All
public import Sarkozy.ClassInputsPaper.All
public import Sarkozy.EnvelopeSteps.Constructor
public import Sarkozy.SignedComponents.All
public import Sarkozy.MainFinal.All
public import Sarkozy.EnvelopeInputsBlock.EnvelopeCoupledNonneg

@[expose] public section

/-!
# Generic bundles for the combined main statement (K2)

Three bundles of the newer reductions, stated generically so that the paper's data slot in:

* **`normSizes_of_bounds`** (B8, `lem:middle-comparison-prices`): the twelve norm bounds
  `NormBounds` of `prop:signed-bounds`(a),(b),(e), `lem:record:exact-marginal-e`(ii), the table of
  `lem:merge-repair` and `lem:record:accepting-c2`, stated for the concrete changes of B8's
  `ofFold`, give K1's `NormSizes` of the optimal norms of `ofFold` (proved: `ofFold_N_le`).
* **`EnvMeansInputs`, `FixMeansInputs`** (B9, `lem:envelope-energy`, `lem:bracket-energy`): the
  arguments of `EnvelopeBracketInputs.ofMeans` and `FixedBracketInputs.ofMeans`, as structures,
  with `.toCRT` to B5's bundles `EnvelopeEnergyInputsCRT`, `FixedIntervalInputsCRT`. The bracket
  of `lem:bracket-energy` is removed (B9's layer 1, **proved**); what remains per side is the
  sharp-first difference `hdiff` (`lem:sharp-first`, used as hypothesis) and the residue-averaged
  first bounds `hm` (`EnvMeanBound`, `FixMeanBound`: `lem:envelope-energy` after the average over
  the residues, used as hypothesis).
* **`ClassEnergySteps`** (B10, `thm:envelopes`(i), `cor:envelope-costs`, `cor:var-classes`): the
  arguments of `ClassEnergyData.ofSteps`, i.e. B10's `ClassEnergyData` with the class bounds at
  energy level replaced by the steps `StepsFamily` (Steps 1–4 of `thm:envelopes`(i) on a degree
  class, the class-cost step of `prop:background-variance`(a) on a variance class), given in
  B11's operator form (`ClassStepsOps`, `stepsFamily_of_ops`; Steps 1–2 proved from operator
  inequalities); `.toED`.
-/

open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.MainFinal2

/-! ## B8: the norm sizes of `ofFold` from the twelve norm bounds -/

section Norms

open Sarkozy.TheoremC Sarkozy.PartV Sarkozy.PartVRecords Sarkozy.RecordExpansion
open Sarkozy.Labellings Sarkozy.MiddleComparison Sarkozy.ComparisonLawPaper Sarkozy.MiddleRecords
open Sarkozy.SignedComponents

variable {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]
  (h : ClassThreeBlock pr) (hne : MiddleNonempty pr)
  (root : FiniteLaw (ZMod 6 × Fin 2 → BlockLabel pr)) (W : MiddleWeights) (I : MiddleInputs)
  {r : ℝ} (hr : 0 ≤ r) (b : ℝ)

/-- **K1's `NormSizes` for B8's `ofFold` from the paper's twelve norm bounds**
(`lem:middle-comparison-prices`, proof; `prop:signed-bounds`(a),(b),(e),
`lem:record:exact-marginal-e`(ii), `lem:merge-repair`, `lem:record:accepting-c2` are the
hypotheses `NB`): the norms of `ofFold` are the optimal constants, so each `FormBound` with the
paper's constant bounds the norm (`ofFold_N_le`). -/
theorem normSizes_of_bounds (C : FoldComponents pr hne) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    {b' sF aF ℓ sE aE : ℝ} (NB : NormBounds pr h hne root W I hr b C t b' sF aF ℓ sE aE) :
    MainFinal.NormSizes (ofFold pr h hne root W I hr b C t ht0 ht1).N ⟨sF, aF, ℓ, sE, aE⟩ b' r := by
  have hN : ∀ {t' : Chg} {e : ChangeType} {K : ℝ},
      FormBound reservedCut (mOf (middleFrame pr hne root W I hr b h) t')
        (foldChange pr h hne root W I hr b C t t' e) K →
        (ofFold pr h hne root W I hr b C t ht0 ht1).N t' e ≤ K :=
    fun hK => ofFold_N_le pr h hne root W I hr b C ht0 ht1 hK
  exact ⟨fun i => hN (NB.Fs i), fun i => hN (NB.Fa i), fun i => hN (NB.Es i),
    fun i => hN (NB.Ea i),
    { sym_nonneg := fun _ => (ofFold pr h hne root W I hr b C t ht0 ht1).N_nonneg _ _
      skew_nonneg := fun _ => (ofFold pr h hne root W I hr b C t ht0 ht1).N_nonneg _ _
      sym_mirror := fun s k hk => hN (NB.Ms s k hk)
      skew_mirror := fun s k hk => hN (NB.Ma s k hk)
      sym_first := fun s => hN (NB.Ms₂ s)
      skew_first := fun s => hN (NB.Ma₂ s) },
    fun k => hN (NB.Cs k), fun k => hN (NB.Ca k)⟩

end Norms

/-! ## B9: the mean-bound forms of `envC` and `fixC` -/

section Means

open Sarkozy.BracketEnergy
open Sarkozy.EnvelopeInputs Sarkozy.EnvelopeEnergiesPaper
open Sarkozy.Param (Params)
open Sarkozy.BlockFrame
open Sarkozy.IndexSupport Sarkozy.Functional Sarkozy.TheoremC Sarkozy.Structured
  Sarkozy.PaperFrame Sarkozy.Comparison Sarkozy.FourierArithmetic

variable {a : ℝ}
variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]
  (hcop : Pairwise (Nat.Coprime on fun q => pr q ^ h q))

/-- **The inputs of `envC` in B9's mean-bound form** (`lem:envelope-energy`, `lem:bracket-energy`,
`lem:hyb:moment`): the arguments of `EnvelopeBracketInputs.ofMeans`. Per side: the sharp-first
difference `hdiff` (`lem:sharp-first` with revealed inputs; *hypothesis*, analytic) and the
residue-averaged first bound with its summation `hm` (`EnvMeanBound`; the chain-covered terms by
`env_first_mean_le`; *hypothesis*, analytic). `z`, `c`, `r2L`, `r2R` are data. 13 fields. -/
structure EnvMeansInputs (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (p L) i).Coprime (joinModuli m₀ (p L) j))
    where
  z : ℕ → ℝ
  hz0 : ∀ L, 0 ≤ z L
  hzt : Tendsto z atTop (𝓝 0)
  c : ℝ
  hc : 0 ≤ c
  r2L : ∀ L, Finset ℤ → (∀ (e : E) (j : Option P), Fin ((D.index.C e j).depth + 1)) →
    (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j) → (BlockAtom Bk J L → Bool) → ℝ
  r2R : ∀ L, Finset ℤ → (∀ (e : E) (j : Option P), Fin ((D.index.C e j).depth + 1)) →
    (∀ (_e : E) (j : Option P), CoordSpace blockScale pr h j) → (BlockAtom Bk J L → Bool) → ℝ
  hdiffL : Param.AtCounterexamples (Params.ofDecay a) D.Y
    (fun L A => ∀ Jq ω (f : BlockAtom Bk J L → Bool),
    |multilinearIntegral (tensorLaw (crtLaws blk (prefix_pairwise (hpair L)) L fun b =>
    if f b then TheoremCBlock.Structured.envIncL D L b else D.GB.N L b))
    (pairInputs D.index.u D.index.u (revealedInputCRT blk hcop D L A Jq)
    (revealedInputCRT blk hcop D L A Jq)
    (unchangedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A L) ω ω) -
    multilinearIntegral (tensorLaw (crtLaws blk (prefix_pairwise (hpair L)) L fun b =>
    if f b then TheoremCBlock.Structured.envIncL D L b else D.GB.N₀ L b))
    (pairInputs D.index.u D.index.u (revealedInputCRT blk hcop D L A Jq)
    (revealedInputCRT blk hcop D L A Jq)
    (unchangedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A L) ω ω)| ≤
    (D.GB.Rerr + z L) * (conductorPrice pr h (EnvelopeInputsBlock.priceExponent a) Jq *
    D.Y L A * ∏ b, (if f b then TheoremCBlock.Structured.envPriceL D L b else 1)) +
    r2L L A Jq ω f)
  hdiffR : Param.AtCounterexamples (Params.ofDecay a) D.Y
    (fun L A => ∀ Jq ω (f : BlockAtom Bk J L → Bool),
    |multilinearIntegral (tensorLaw (crtLaws blk (prefix_pairwise (hpair L)) L fun b =>
    if f b then TheoremCBlock.Structured.envIncR D L b else D.GB.N L b))
    (pairInputs D.index.w D.index.w (revealedInputCRT blk hcop D L A Jq)
    (revealedInputCRT blk hcop D L A Jq)
    (unchangedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A L) ω ω) -
    multilinearIntegral (tensorLaw (crtLaws blk (prefix_pairwise (hpair L)) L fun b =>
    if f b then TheoremCBlock.Structured.envIncR D L b else D.GB.N₀ L b))
    (pairInputs D.index.w D.index.w (revealedInputCRT blk hcop D L A Jq)
    (revealedInputCRT blk hcop D L A Jq)
    (unchangedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A L) ω ω)| ≤
    (D.GB.Rerr + z L) * (conductorPrice pr h (EnvelopeInputsBlock.priceExponent a) Jq *
    D.Y L A * ∏ b, (if f b then TheoremCBlock.Structured.envPriceR D L b else 1)) +
    r2R L A Jq ω f)
  hmL : EnvMeanBound hcop D hpair z c (fun L => TheoremCBlock.Structured.envIncL D L)
    (fun L => TheoremCBlock.Structured.envPriceL D L) D.index.u r2L
  hmR : EnvMeanBound hcop D hpair z c (fun L => TheoremCBlock.Structured.envIncR D L)
    (fun L => TheoremCBlock.Structured.envPriceR D L) D.index.w r2R

/-- B5's `envC` from the mean-bound form (B9's `ofMeans`, then `toCRT`). -/
noncomputable def EnvMeansInputs.toCRT {D : TheoremCBlock.ComparisonData a m₀ blk p pr h E}
    {hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (p L) i).Coprime (joinModuli m₀ (p L) j)}
    (M : EnvMeansInputs hcop D hpair) : EnvelopeEnergyInputsCRT hcop D hpair :=
  (EnvelopeBracketInputs.ofMeans hcop D hpair M.z M.hz0 M.hzt M.c M.hc M.r2L M.r2R M.hdiffL
    M.hdiffR M.hmL M.hmR).toCRT

/-- **The inputs of `fixC` in B9's mean-bound form** (`lem:envelope-energy`, `lem:twointerval`(ii),
`lem:bracket-energy`): the arguments of `FixedBracketInputs.ofMeans`. Per side: `hdiff`
(`lem:sharp-first`; *hypothesis*) and `hm` (`FixMeanBound`, the fixed-interval price; the
chain-covered terms by `fix_first_mean_le`; *hypothesis*). 13 fields. -/
structure FixMeansInputs (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)
    (hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (p L) i).Coprime (joinModuli m₀ (p L) j))
    where
  z : ℕ → ℝ
  hz0 : ∀ L, 0 ≤ z L
  hzt : Tendsto z atTop (𝓝 0)
  c : ℝ
  hc : 0 ≤ c
  r2L : ∀ L, Finset ℤ → Finset E →
    (∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1)) →
    (E → ∀ j : Option P, CoordSpace blockScale pr h j) → (BlockAtom Bk J L → Bool) → ℝ
  r2R : ∀ L, Finset ℤ → Finset E →
    (∀ (_e : E) (j : Option P), Fin ((coordChain blockScale pr h j).depth + 1)) →
    (E → ∀ j : Option P, CoordSpace blockScale pr h j) → (BlockAtom Bk J L → Bool) → ℝ
  hdiffL : Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A => ∀ S : Finset E, S ≠ ∅ →
    ∀ Jq ω (f : BlockAtom Bk J L → Bool),
    |multilinearIntegral (tensorLaw (crtLaws blk (prefix_pairwise (hpair L)) L fun b =>
    if f b then TheoremCBlock.Structured.wrapInc D L b else D.GB.N L b))
    (pairInputs D.S.Q.u D.S.Q.u (revealedSlot Jq (wrapInputCRT blk hcop L A S 0))
    (revealedSlot Jq (wrapInputCRT blk hcop L A S 0))
    (unchangedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A L) ω ω) -
    multilinearIntegral (tensorLaw (crtLaws blk (prefix_pairwise (hpair L)) L fun b =>
    if f b then TheoremCBlock.Structured.wrapInc D L b else D.GB.N₀ L b))
    (pairInputs D.S.Q.u D.S.Q.u (revealedSlot Jq (wrapInputCRT blk hcop L A S 0))
    (revealedSlot Jq (wrapInputCRT blk hcop L A S 0))
    (unchangedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A L) ω ω)| ≤
    (D.GB.Rerr + z L) * (fixedPrice pr h (EnvelopeInputsBlock.priceExponent a) S Jq *
    D.Y L A * ∏ b, (if f b then TheoremCBlock.Structured.wrapPrice D L b else 1)) +
    r2L L A S Jq ω f)
  hdiffR : Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A => ∀ S : Finset E, S ≠ ∅ →
    ∀ Jq ω (f : BlockAtom Bk J L → Bool),
    |multilinearIntegral (tensorLaw (crtLaws blk (prefix_pairwise (hpair L)) L fun b =>
    if f b then TheoremCBlock.Structured.wrapInc D L b else D.GB.N L b))
    (pairInputs D.S.Q.w D.S.Q.w (revealedSlot Jq (wrapInputCRT blk hcop L A S 1))
    (revealedSlot Jq (wrapInputCRT blk hcop L A S 1))
    (unchangedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A L) ω ω) -
    multilinearIntegral (tensorLaw (crtLaws blk (prefix_pairwise (hpair L)) L fun b =>
    if f b then TheoremCBlock.Structured.wrapInc D L b else D.GB.N₀ L b))
    (pairInputs D.S.Q.w D.S.Q.w (revealedSlot Jq (wrapInputCRT blk hcop L A S 1))
    (revealedSlot Jq (wrapInputCRT blk hcop L A S 1))
    (unchangedInput (crtModuli m₀ blk p L) (paperCutoff (blockScale * L)) A L) ω ω)| ≤
    (D.GB.Rerr + z L) * (fixedPrice pr h (EnvelopeInputsBlock.priceExponent a) S Jq *
    D.Y L A * ∏ b, (if f b then TheoremCBlock.Structured.wrapPrice D L b else 1)) +
    r2R L A S Jq ω f)
  hmL : FixMeanBound hcop D hpair z c D.S.Q.u 0 r2L
  hmR : FixMeanBound hcop D hpair z c D.S.Q.w 1 r2R

/-- B5's `fixC` from the mean-bound form (B9's `ofMeans`, then `toCRT`). -/
noncomputable def FixMeansInputs.toCRT {D : TheoremCBlock.ComparisonData a m₀ blk p pr h E}
    {hpair : ∀ L, Pairwise fun i j => (joinModuli m₀ (p L) i).Coprime (joinModuli m₀ (p L) j)}
    (M : FixMeansInputs hcop D hpair) : FixedIntervalInputsCRT hcop D hpair :=
  (FixedBracketInputs.ofMeans hcop D hpair M.z M.hz0 M.hzt M.c M.hc M.r2L M.r2R M.hdiffL
    M.hdiffR M.hmL M.hmR).toCRT

end Means

/-! ## B10: the class energies from the steps -/

section Steps

open Sarkozy.ClassInputsPaper Sarkozy.ClassBoundsPaper
open Sarkozy.TheoremC Sarkozy.TheoremCBlock
open Sarkozy.Param (Params)
open Sarkozy.BlockFrame
open Sarkozy.FourierArithmetic Sarkozy.Functional Sarkozy.IndexSupport Sarkozy.Comparison
  Sarkozy.PaperFrame Sarkozy.RecordExpansion Sarkozy.RecordExpansion.Choice

variable {a : ℝ}
  {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

/-- **The steps of every class bound in B11's operator form** (`thm:envelopes`(i) Steps 1–4 on a
degree class with Steps 1–2 as operator inequalities on the actual half spaces, B11's `DegreeOps`
at the cut `ι`; the class-cost step of `prop:background-variance`(a)/`lem:var-gain`(b) on a
variance class, B10's `VarStepsAt`), with one `z_L → 0`, one `K` and remainders
`rr ≥ 0`, `∑ rr ≤ c₀ L^{-σ} α`: the arguments of B11's `stepsFamily_of_ops`. The per-class operator
data are built by B11's `paperDegreeOps` from the objects and marginals, the record operators
(N4), the domination, `‖Υ‖`, (E1) for `Diag_ω`, Step 3 and Step 4. 9 fields; `H` is *open*
(analytic). -/
structure ClassStepsOps {D : TheoremCBlock.ComparisonData a m₀ blk p pr h E} (cd : ClassData D.CL)
    (Θ : ℕ → Type) [∀ L, Fintype (Θ L)] (Z : ∀ L, Finset ℤ → Θ L → ℝ)
    (wc : ∀ L, cd.ι L → Θ L → ℝ) (ρ : ∀ L, Choice (D.CL.T L) → ℝ) where
  z : ℕ → ℝ
  hz0 : ∀ L, 0 ≤ z L
  hz : Tendsto z atTop (𝓝 0)
  K : ℝ
  c₀ : ℝ
  hc₀ : 0 ≤ c₀
  rr : ∀ L, Finset ℤ → Choice (D.CL.T L) → ℝ
  hrr0 : ∀ L A ω, 0 ≤ rr L A ω
  /-- Per counterexample: the operator data of every degree class, the variance steps of every
  variance class, and the summed remainders. *Open* (analytic). -/
  H : Param.AtCounterexamples (Param.Params.ofDecay a) D.Y fun L A =>
    (∀ n : {n // n ∈ cd.N}, Nonempty (EnvelopeSteps.DegreeOps reservedCut (cd.clsSel L (.inl n))
      (EnvelopeSteps.termAt (D := D) L A) (fun ω => monomial (D.CL.π L) ω) (ρ L) (rr L A)
      (∑ j, wc L (.inl n) j * Z L A j) (D.Y L A) (z L) K)) ∧
    (∀ v : cd.V L, Nonempty (VarStepsAt (cd.clsSel L (.inr v)) (EnvelopeSteps.termAt (D := D) L A)
      (fun ω => monomial (D.CL.π L) ω) (ρ L) (rr L A) (∑ j, wc L (.inr v) j * Z L A j)
      (D.Y L A) (z L) K)) ∧
    ∑ ω ∈ cd.sel L, rr L A ω ≤ Comparison.remainder c₀ L A

omit [DecidableEq P] in
/-- B10's `StepsFamily` from B11's operator form (`stepsFamily_of_ops`). -/
theorem ClassStepsOps.toSteps {D : TheoremCBlock.ComparisonData a m₀ blk p pr h E}
    {cd : ClassData D.CL} {Θ : ℕ → Type} [∀ L, Fintype (Θ L)] {Z : ∀ L, Finset ℤ → Θ L → ℝ}
    {wc : ∀ L, cd.ι L → Θ L → ℝ} {ρ : ∀ L, Choice (D.CL.T L) → ℝ}
    (O : ClassStepsOps cd Θ Z wc ρ) : StepsFamily cd Θ Z wc ρ :=
  EnvelopeSteps.stepsFamily_of_ops cd reservedCut Θ Z wc ρ O.z O.hz0 O.hz O.K O.c₀ O.hc₀ O.rr
    O.hrr0 O.H

/-- **B10's class energies with the energy-level class bounds given by their steps**
(`thm:envelopes`(i) Steps 1–4 on a degree class, `prop:background-variance`(a)/`lem:var-gain`(b)
on a variance class, in B11's operator form `ops`: *hypothesis*, analytic), the consistency with the
class polynomial (`consistent`, evaluation), the error weights (`errw`, numerical) and the upper
prices of the diagonals (`upper`, `lem:bracket-energy`; *hypothesis*, analytic): the arguments of
`ClassEnergyData.ofSteps`. 13 fields. -/
structure ClassEnergySteps (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)
    (cd : ClassData D.CL) where
  /-- The labelled positive diagonals of the envelopes. Data. -/
  Θ : ℕ → Type
  [ΘFintype : ∀ L, Fintype (Θ L)]
  /-- Their energies and upper prices. Data. -/
  Z : ∀ L, Finset ℤ → Θ L → ℝ
  u : ∀ L, Θ L → ℝ
  /-- The class weights on the diagonals. Data. -/
  wc : ∀ L, cd.ι L → Θ L → ℝ
  wc_nonneg : ∀ L i j, 0 ≤ wc L i j
  /-- The evaluated residuals. Data. -/
  ρ : ∀ L, Choice (D.CL.T L) → ℝ
  /-- **The steps of every class bound** in B11's operator form (`ClassStepsOps`, giving
  `StepsFamily` by `stepsFamily_of_ops`). *Open* (analytic). -/
  ops : ClassStepsOps cd Θ Z wc ρ
  /-- The evaluation at the upper prices is at most the class bound. *Open* (evaluation). -/
  consistent : ∀ L i, ∑ j, wc L i j * u L j + ∑ ω ∈ cd.clsSel L i, ρ L ω ≤
    ∑ ω ∈ cd.clsSel L i, cd.φ L ω
  /-- The error weights. Data. -/
  v : ∀ L, Θ L → ℝ
  errK : ℝ
  /-- The error weights are dominated by the class prices. *Open* (numerical). -/
  errw : ∀ L i, ∑ j, wc L i j * v L j ≤ errK * ∑ ω ∈ cd.clsSel L i, monomial (D.CL.π L) ω
  /-- **The upper prices of the diagonals** (`lem:bracket-energy`, (E1)). *Open* (analytic). -/
  upper : ∃ ε₃ : ℕ → ℝ, (∀ L, 0 ≤ ε₃ L) ∧ Tendsto ε₃ atTop (𝓝 0) ∧ ∃ c₃ : ℝ, 0 ≤ c₃ ∧
    ∃ r : ∀ L, Finset ℤ → Θ L → ℝ, (∀ L A j, 0 ≤ r L A j) ∧
    Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
      ∀ j, Z L A j ≤ (u L j + ε₃ L * v L j) * D.Y L A + r L A j) ∧
    Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
      ∑ j, (∑ i, wc L i j) * r L A j ≤ remainder c₃ L A)

attribute [instance] ClassEnergySteps.ΘFintype

/-- B10's `ClassEnergyData` from the steps (`ClassEnergyData.ofSteps`, i.e. `energy_of_steps`). -/
noncomputable def ClassEnergySteps.toED {D : TheoremCBlock.ComparisonData a m₀ blk p pr h E}
    {cd : ClassData D.CL} (S : ClassEnergySteps D cd) : ClassEnergyData D cd :=
  ClassEnergyData.ofSteps cd S.Θ S.Z S.u S.wc S.wc_nonneg S.ρ S.ops.toSteps S.consistent S.v
    S.errK S.errw S.upper

end Steps

/-! ## (E1) off the classes: G1's coupled pieces -/

section E1

open Sarkozy.EnvelopeInputsBlock Sarkozy.EnvelopeInputs
open Sarkozy.Param (Params)
open Sarkozy.BlockFrame
open Sarkozy.TheoremC Sarkozy.Comparison Sarkozy.PaperFrame Sarkozy.RecordExpansion
  Sarkozy.RecordExpansion.Choice Sarkozy.Structured ReflectionCut

variable {a : ℝ}
  {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

/-- **The inputs of (E1) off the classes** (`def:robust`; G1's
`envelopeBoundNonneg_of_coupledPieces_uniform`): the subset terms `hsub` (`lem:bracket-energy`,
"`μ` off a selected set"; *hypothesis*, analytic) and the coupled envelope pieces `hcoup`
(`lem:sharp-first`, `lem:density:coupled`; *hypothesis*, analytic), with one relative error
`εE → 0` and one remainder constant `c₁ ≥ 0`. 7 fields. -/
structure E1Inputs (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) where
  εE : ℕ → ℝ
  hε0 : ∀ L, 0 ≤ εE L
  hεt : Tendsto εE atTop (𝓝 0)
  c₁ : ℝ
  hc₁ : 0 ≤ c₁
  hsub : Param.AtCounterexamples (Params.ofDecay a) D.Y
    (fun L A => ∀ ω : Choice (D.CL.T L), IsSelection ω →
    ∀ f : BlockAtom Bk J L → Bool,
    |diagonalIntegral (tensorLaw fun b => if f b then
    (if (ω b).isSome then 0 else ∑ i, D.GB.κu L b i)
    else entryFactor (D.R.law p L b) (D.CL.D L b) (ω b)) (blockLift m₀ blk p L A)| ≤
    ((1 + εE L) * (∏ b ∈ Choice.support ω, TheoremCBlock.selectionFactor a p D.S.selPre L b) *
    D.Y L A) * ∏ b, (if f b then (if (ω b).isSome then 0 else D.GB.uprice L b) else 1) +
    (∏ b, (if f b then (if (ω b).isSome then 0 else mass (∑ i, D.GB.κu L b i)) else 1)) *
    remainder c₁ L A)
  hcoup : Param.AtCounterexamples (Params.ofDecay a) D.Y
    (fun L A => ∀ ω : Choice (D.CL.T L), IsSelection ω →
    ∀ σ : (∀ b, Option (D.FS.Ib L b)), σ ≠ (fun _ => none) → ∀ j,
    1 ≤ countVec (D.FS.tag L) σ j → ∀ f : (∀ b, CEPiece D L b),
    (∀ b, ecpieceCoef D L ω σ j b (f b) ≠ 0) →
    |diagonalIntegral (tensorLaw fun b => ecpieceK D L ω b (f b)) (blockLift m₀ blk p L A)| ≤
    (∏ b, ecpieceG D L ω b (f b)) * ((1 + εE L) * D.Y L A) +
    (∏ b, ecpieceM D L b (f b)) * remainder c₁ L A)


omit [DecidableEq P] in
/-- (E1) off the classes from G1's per-term inputs. -/
theorem E1Inputs.toE1 {D : TheoremCBlock.ComparisonData a m₀ blk p pr h E} (ha : 0 ≤ a)
    (I : E1Inputs D) : D.EnvelopeBoundNonneg :=
  envelopeBoundNonneg_of_coupledPieces_uniform D ha I.εE I.hε0 I.hεt I.hc₁ I.hsub I.hcoup

end E1

end Sarkozy.MainFinal2
