module

public import Sarkozy.Companion.Front
public import Sarkozy.Companion.Kinds
public import Sarkozy.Companion.ClassFields
public import Sarkozy.MeanCredit2.Classes
public import Sarkozy.SharpBase2.Parts

@[expose] public section

/-!
# The companion statement: all reductions of 7 November at once (`main_goal_companion`)

`MainCombined2.main_goal_theta1k` takes `O : MainFinalObligationsKT1` (`F : FrontK`, `Cls`, `Sh`).
Five packages reduced it in parallel, each in its own variant of the statement. Here they are
applied together, and the result is mapped down to `main_goal_theta1k` through their own maps:

* **SD2** (`SignedDecomp`): `F.SD` from `SDB` (`SignedDecompAnalytic2.toSD`);
* **NB3** (`NormBoundsPaper3`): `F.hNr2` from `hEs`, `hNr4` (`FrontN3.toK`);
* **FD** (`NormBoundsPaper4`): `hEs` proved (`eOrthPaperInput`); `hNr4` from `SDB` (C38's
  component norms, FS's `sym`, `skew`, RG's side conditions at the rebased table:
  `Rebase.hNr4_paperKappa`; FD's `hFold` is dropped);
* **SH2** (`SharpBase2`): `Sh` from SF and the four per-term summations
  (`SharpBaseInputsPT.toSharpPartsBase`, which supersedes SH2's `sh2` route);
* **CM** (`MeanCredit`, `MeanCredit2`): `Cls` from `MeanCredit2.classPartsPaper`, i.e. the
  class group at the paper's coefficients, with CM's single comparison hypothesis (`hC`, `hCv`).
  Its split form `classPartsPaperSplit` is a special case of it (`τ = 10⁻²⁸`, through
  `harnessE_formula`), so the single form gives the stronger statement with fewer fields.
* UC's split `PCu`, `UpT`, `UpB` and PG's prime Gram, already in `FrontK`.

**The structure `CompanionObligations` lists the open hypotheses by kind** (`TRUST_MAP.md` §3):
* the front `F : CompanionFront` (6 fields, ordered by their types; kinds marked: C + F, C, C,
  F + R, F + R, C);
* **(D)** the free data of the class and sharp groups, and **(S)** their sign, limit and
  uniformity side conditions (choices, no content of their own);
* **(F)** finite numerical claims: CM's residual gates and comparison series;
* **(R)** routine analytic lemmas: `lem:bracket-energy` (twice) and
  `prop:record:density-structured` on the folded energies;
* **(C)** novel core still open.

The literature hypotheses **(L)** (H1 `Weil`, H2 `BMOR`, H5 `MovingRoot`,
H6 `FourCycle` = `thm:dl:K`, H2″ `ThetaSmallRR`) and the finite record table `UpT` (F) are
parameters of `main_goal_companion`, as of `main_goal_theta1k`.

* **`CompanionObligations`**, **`CompanionObligations.Cls`** (CM), **`.ShPT`** (SH2),
  **`.toKT1`**;
* **`main_goal_companion`**: `s(N) ≤ C·N^{0.99999}`, through `main_goal_theta1k`.
-/

open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.Companion

open Sarkozy.PartV Sarkozy.BlockSpecPaper Sarkozy.MainCombined Sarkozy.MainCombined2
open Sarkozy.ClassBoundsPaper Sarkozy.ClassInputsPaper Sarkozy.ClassData Sarkozy.MainFinal2
open Sarkozy.MainFinalF1b Sarkozy.MeanCredit Sarkozy.MeanCredit2
open Sarkozy.TheoremC Sarkozy.TheoremCBlock Sarkozy.JointClosing
open Sarkozy.RecordExpansion Sarkozy.RecordExpansion.Choice
open Sarkozy.ThetaOne Sarkozy.SharpBase2
open Sarkozy.EnvelopeEnergiesPaper (paper_pairwise)
open Sarkozy.AnalyticCells (f1Cell)
open Sarkozy.UpperCapsPaper (UpperRecordTables)

/-- **The obligations of the companion statement**, grouped by kind (`TRUST_MAP.md` §3). The
front `F` comes first, since the class and sharp groups are typed at its joint block data
`F.X hB hRR`; then the free data (D), their side conditions (S), and the hypotheses with content:
(F) finite numerical claims, (R) routine analytic lemmas, (C) novel core. Every field is a
verbatim copy of a field of SD2's, FD's, SH2's or CM's inputs (Lean checks this in `toKT1`), with
three exceptions: `UpB` is split into `F.rep`, `F.hs`, `F.ha`; `hwPaper`, `hwW`, `hvV` are stated
on `wc`, `agg π` directly (definitionally CM's `aggED … .w`, `.v`); (E1) and `SF` are flattened
(`E1InputsAgg.ofFields`, `SharpFirstBaseInputs.ofFields`). -/
structure CompanionObligations (hW : Target.Weil) (hMR : Target.MovingRoot)
    (hFour : Target.FourCycle) (hB : Target.BMOR) (hRR : Target.ThetaSmallRR)
    (UpT : UpperRecordTables) : Type 1 where
  /-- **The front** (6 fields, kinds marked in `CompanionFront`): `PCu` (C + F), `BA` (C),
  `rep` (C), `hs`, `ha` (F + R), `SDB` (C; RG: the signed decomposition only). -/
  F : CompanionFront hW hMR hFour UpT
  -- (D) The free data of the class group (CM's route)
  /-- (D) The classes `ι`, `cls` of `def:cp5` (B10's `ClassData`). -/
  cd : ClassData (F.X hB hRR).data.CL
  /-- (D) The labels of the aggregated diagonals (e.g. `PaperDiag × Fin 4`, one per family). -/
  K : Type
  [instFK : Fintype K]
  [instDK : DecidableEq K]
  /-- (D) The letters of the record expansion other than CM's mean letters `F`, `E`, `I`, `G`. -/
  Lt : Type
  [instFLt : Fintype Lt]
  [instDLt : DecidableEq Lt]
  /-- (D) The label of each selection (`none`: unlabelled). -/
  labS : ∀ L, Choice ((F.X hB hRR).data.CL.T L) → Option K
  /-- (D) The paper type of each label. -/
  labK : K → PaperDiag
  /-- (D) The family coefficient of each label (`prop:joint-middle-mean`, families (i)–(iv)). -/
  μK : K → ℝ
  /-- (D) The per-selection diagonal energies. -/
  Zs : ∀ L, Finset ℤ → Choice ((F.X hB hRR).data.CL.T L) → ℝ
  /-- (D) The class weights on the labels. -/
  wc : ∀ L, cd.ι L → K → ℝ
  /-- (D) The evaluated residuals of the selections (`cor:envelope-costs`). -/
  ρ : ∀ L, Choice ((F.X hB hRR).data.CL.T L) → ℝ
  /-- (D) The per-selection residual coefficients (the residual table). -/
  r : ∀ L, Choice ((F.X hB hRR).data.CL.T L) → ℝ
  /-- (D) The uniform bound of the label prices. -/
  Vv : ℝ
  /-- (D) The lettering of the record expansion (one letter per entry). -/
  ℓ : ∀ L, Entry ((F.X hB hRR).data.CL.T L) → MLetter ⊕ Lt
  /-- (D) The comparison coefficient of a letter degree. -/
  c : (MLetter ⊕ Lt → ℕ) → ℝ
  /-- (D) The letter totals. -/
  X : MLetter ⊕ Lt → ℝ
  /-- (D) The completed comparison series and its slack. -/
  Cv : ℝ
  τ : ℝ
  -- (D) The free data of (E1) and of `SF`
  /-- (D) (E1): the relative error, the constant and the remainders. -/
  εE : ℕ → ℝ
  cE : ℝ
  r0 : E1R0 (F.X hB hRR).data
  rE : E1R (F.X hB hRR).data
  /-- (D) `SF`: the sharp decompositions `dec` of the differences (`lem:sharp-first`), the
  relative error `ε`, the constant `c` and the remainders `rp`, `rm` of the folded energies. -/
  sf : SFData (F.X hB hRR).toJoint.data
  /-- (D) The constant of the four `rch` summations. -/
  c₂ : ℝ
  -- (S) Side conditions on the data
  /-- (S) The family coefficients: `0 ≤ μ_k ≤ diagB`, zero exactly when `diagB` is. -/
  hμ0 : ∀ k, 0 ≤ μK k
  hμle : ∀ k, μK k ≤ diagB (labK k)
  hz : ∀ k, (diagB (labK k) : ℝ) = 0 → μK k = 0
  hnz : ∀ k, (diagB (labK k) : ℝ) ≠ 0 → μK k ≠ 0
  /-- (S) The class weights are nonnegative. -/
  wc_nonneg : ∀ L i j, 0 ≤ wc L i j
  /-- (S) **`hwPaper`**: the aggregated class weight of a label is the paper's
  `63(κ_b − var)/63 = diagW` per unit of the exact weight `wtOf` (the residual table of
  `prop:joint-middle-mean`, aggregated). It pins `wc`; the content is then in `ops`. -/
  hwPaper : WeightsPaper (F.X hB hRR).data cd labK μK wc
  /-- (S) The aggregated label prices are uniformly bounded. -/
  hVv : 0 ≤ Vv
  hvV : PriceBound (F.X hB hRR).data cd labS labK μK Vv
  /-- (S) The per-selection energies are nonnegative. -/
  hZs : ∀ L A ω, 0 ≤ Zs L A ω
  /-- (S) The letter totals are nonnegative, and on the mean letters they are E3's v2 totals
  `x`, `V`, `U − V` (rounded up to `10⁻³⁰`). -/
  hX0 : ∀ l, 0 ≤ X l
  hXm : ∀ l, X (.inl l) = mTot xq 0 0 Vq (Uq - Vq) l
  /-- (S) The slack of the comparison series is at most `3·10⁻²` (RG: the AllocJ spare at the
  rebased ledger is about `2.51`, so `63 τ ≤ 12/5`; it was `2·10⁻³` before). -/
  hτ : τ ≤ 3 / 100
  /-- (S) (E1): `0 ≤ ε_E → 0`, `c_E ≥ 0`, nonnegative remainders. -/
  hεE0 : ∀ L, 0 ≤ εE L
  hεEt : Tendsto εE atTop (𝓝 0)
  hcE : 0 ≤ cE
  hrE0 : ∀ L A ω σ j f, 0 ≤ rE L A ω σ j f
  hr00 : ∀ L A ω f, 0 ≤ r0 L A ω f
  /-- (S) `SF`: `0 ≤ ε → 0`, `c ≥ 0`, nonnegative remainders; `c₂ ≥ 0`. -/
  hεS0 : ∀ L, 0 ≤ sf.ε L
  hεSt : Tendsto sf.ε atTop (𝓝 0)
  hcS : 0 ≤ sf.c
  hrpm0 : ∀ L A σ j f, 0 ≤ sf.rp L A σ j f ∧ 0 ≤ sf.rm L A σ j f
  hc₂ : 0 ≤ c₂
  -- (F) Finite numerical claims
  /-- **(F)** The residual gates on every letter degree, `63 c − mLift ≥ 0`
  (`prop:joint-middle-mean`, the residual table; `eq:final-joint-closing`). On the degrees of
  labelled class selections they follow from `hcomp`, `hmean` and E4's 192 gates
  (`hres_of_ids`). *Open*. -/
  hres : ∀ d, 0 ≤ 63 * c d - mLift d
  /-- **(F)** The comparison side of `eq:final-joint-closing`: the completed comparison series
  `C_v = ∑_d c(d) ∏_l X_l^{d_l}/d_l!` … -/
  hC : HasSum (fun d => c d * ∏ l, X l ^ d l / (d l).factorial) Cv
  /-- **(F)** … is at most the harness's `𝓔` plus `τ` (`harnessE`, E3's v2 value). The class
  costs enter the gate here. *Open*. -/
  hCv : Cv ≤ harnessE + τ
  -- (R) Routine analytic lemmas
  /-- **(R)** `ES.upper` per selection (`lem:bracket-energy`, first display;
  `prop:record:density-structured`, `def:robust`): the labelled selection energies satisfy
  `Z_ω ≤ (1 + ε₃)π_ω Y + r_ω`, with the remainders summed against the class weights
  (`SelUpper`). *Open*. -/
  hup : SelUpper (F.X hB hRR).data cd labS (wtOf labK μK) Zs wc
  /-- **(R)** `E1.hsub` (`lem:bracket-energy`, `prop:record:density-structured`): `E1Sub`.
  *Open*. -/
  hsub : E1Sub (F.X hB hRR).data εE r0
  /-- **(R)** `SF.hfold` (`prop:record:density-structured` on the folded energies of
  `lem:record:folded-energy`): `SFFold`. *Open*. -/
  hfold : SFFold (F.X hB hRR).toJoint.data sf.dec sf.ε sf.rp sf.rm
  -- (C) Novel core still open
  /-- **(C)** `ES.ops` (`thm:envelopes`(i) Steps 1–4, `lem:oct24:mask-schur`(a),
  `lem:oct24:feature-block`(a), `prop:background-variance`(a), `lem:var-gain`(b),
  `lem:record:restoration`): B11's operator steps for the aggregated diagonals. *Open*. -/
  ops : ClassStepsOps cd (fun _ => K)
    (fun L A => agg (cd.sel L) (labS L) (wtOf labK μK) (Zs L A)) wc ρ
  /-- **(C)** `MD.mean` per selection (`prop:record:mean-credit`, `prop:joint-middle-mean`,
  (CP7) `def:cp7`): the mean energies retain `(m₁ − o(1))Y + ∑_ω μ_ω Z_ω` with
  `μ_ω = μK(label ω)` (`SelMean`). *Open*. -/
  hm : SelMean (F.X hB hRR).data cd (fun L ω => (labS L ω).elim 0 μK) Zs
  /-- **(C)** The residual of a class selection is `r_ω` times its monomial
  (`cor:envelope-costs`). *Open*. -/
  hρ : ResidualId (F.X hB hRR).data cd ρ r
  /-- **(C)** `hcomp`: the comparison coefficient of a selection's letter degree dominates its
  class bound (`thm:envelopes`(i), `cor:envelope-costs`): `B` off the classes, `r_ω` on them,
  plus `diagW` on its label. *Open*. -/
  hcomp : CompId (F.X hB hRR).data cd labS labK ℓ c r
  /-- **(C)** `hmean`: a selection's letter degree carries at most its label's family credit
  (`prop:joint-middle-mean`, families (i)–(iv), per selection). *Open*. -/
  hmean : MeanId (F.X hB hRR).data cd labS μK ℓ
  /-- **(C)** `hX`: the formal letter totals are at most `X` (the price bounds of
  `lem:four-routes-normalized`; with `hXm`, the formal raw arms and outside prices are at most
  the harness's). CM's finding §11.7(3): one lettering with all of the harness's totals is the
  part of `eq:final-joint-closing` asserted without detail; its content is joint with `hXm`,
  `hC`, `hcomp`. *Open*. -/
  hX : TotalsLe (F.X hB hRR).data ℓ X
  /-- **(C)** `E1.hcoup` (`lem:sharp-first`, `lem:density:coupled`): `E1Coup`. *Open*. -/
  hcoup : E1Coup (F.X hB hRR).data εE rE
  /-- **(C)** `E1.hrem` (`lem:record:density-lp`, `def:robust`): `E1Rem`. *Open*. -/
  hremE : E1Rem (F.X hB hRR).data cE r0 rE
  /-- **(C)** `SF.hrem` (`lem:sharp-first`, the error terms): `SFRem`. *Open*. -/
  hremS : SFRem (F.X hB hRR).toJoint.data sf.c sf.rp sf.rm
  /-- **(C)** SH2: the summation of the per-term remainders `rchFixL` (`Sh.fixM.hr2L`;
  `lem:sharp-first`, `lem:record:density-dc`, `lem:record:density-lp`). *Open*. -/
  fixL : RchSumPTFixL (BlockAnchor.index_coprime_block (F.X hB hRR).toJoint.data)
    (F.X hB hRR).toJoint.data paper_pairwise sf.dec c₂
  /-- **(C)** SH2: the same for `rchFixR` (`Sh.fixM.hr2R`). *Open*. -/
  fixR : RchSumPTFixR (BlockAnchor.index_coprime_block (F.X hB hRR).toJoint.data)
    (F.X hB hRR).toJoint.data paper_pairwise sf.dec c₂
  /-- **(C)** SH2: the same for `rchEnvL` (`Sh.envM.hr2L`). *Open*. -/
  envL : RchSumPTEnvL (BlockAnchor.index_coprime_block (F.X hB hRR).toJoint.data)
    (F.X hB hRR).toJoint.data paper_pairwise sf.dec c₂
  /-- **(C)** SH2: the same for `rchEnvR` (`Sh.envM.hr2R`). *Open*. -/
  envR : RchSumPTEnvR (BlockAnchor.index_coprime_block (F.X hB hRR).toJoint.data)
    (F.X hB hRR).toJoint.data paper_pairwise sf.dec c₂

attribute [instance] CompanionObligations.instFK CompanionObligations.instDK
  CompanionObligations.instFLt CompanionObligations.instDLt

namespace CompanionObligations

variable {hW : Target.Weil} {hMR : Target.MovingRoot} {hFour : Target.FourCycle}
  {hB : Target.BMOR} {hRR : Target.ThetaSmallRR} {UpT : UpperRecordTables}

/-- The uniform bound of the aggregated class weights, `∑_k diagW(k)/wtOf(k)` (CM's `W`; `hwW`
follows from `hwPaper`). -/
noncomputable def W (O : CompanionObligations hW hMR hFour hB hRR UpT) : ℝ :=
  ∑ k, (diagW (O.labK k) : ℝ) / wtOf O.labK O.μK k

theorem weight_nonneg (O : CompanionObligations hW hMR hFour hB hRR UpT) (k : O.K) :
    0 ≤ (diagW (O.labK k) : ℝ) / wtOf O.labK O.μK k :=
  div_nonneg (le_of_lt (by exact_mod_cast diagW_pos (O.labK k)))
    (le_of_lt (wtOf_pos O.labK O.μK O.hμ0 O.hnz k))

theorem W_nonneg (O : CompanionObligations hW hMR hFour hB hRR UpT) : 0 ≤ O.W :=
  Finset.sum_nonneg fun k _ => O.weight_nonneg k

theorem hwW (O : CompanionObligations hW hMR hFour hB hRR UpT) (L : ℕ) (k : O.K) :
    ∑ i, O.wc L i k ≤ O.W := by
  rw [O.hwPaper L k]
  exact Finset.single_le_sum (fun k _ => O.weight_nonneg k) (Finset.mem_univ k)

/-- **(E1)** from the flattened fields (`E1InputsAgg.ofFields`). -/
noncomputable def E1 (O : CompanionObligations hW hMR hFour hB hRR UpT) :
    E1InputsAgg (O.F.X hB hRR).data :=
  E1InputsAgg.ofFields _ O.εE O.hεE0 O.hεEt O.cE O.hcE O.r0 O.rE O.hsub O.hcoup O.hremE O.hrE0
    O.hr00

/-- **The class group, CM's constructor at the paper's coefficients**
(`MeanCredit2.classPartsPaper`; `cor:joint-closing`, `prop:joint-middle-mean`,
`eq:final-joint-closing`), at the joint block data of the front: the same data `D` as the field
`Cls` of `MainFinalObligationsKT1` at `F := O.F.toK`. -/
noncomputable def Cls (O : CompanionObligations hW hMR hFour hB hRR UpT) :
    ClassPartsE4B (O.F.X hB hRR).data :=
  classPartsPaper (D := (O.F.X hB hRR).data) (cd := O.cd) (K := O.K) (C := O.Lt)
    O.labS O.labK O.μK O.hμ0 O.hμle O.hz O.hnz O.Zs O.wc O.wc_nonneg O.ρ O.ops O.hup O.hwPaper
    O.W O.Vv O.W_nonneg O.hVv O.hwW
    (PriceBound.toAggED O.hμ0 O.Zs O.wc O.wc_nonneg O.ρ O.ops O.hup O.hvV) O.hZs O.hm O.ℓ O.c O.X
    O.hX0 O.hXm O.hX O.hres O.Cv O.τ O.hτ O.hC O.hCv O.r O.hρ O.hcomp O.hmean O.E1

/-- **The sharp inputs, SH2's per-term route** (`SharpBaseInputsPT`), with `SF` rebuilt from the
flattened fields (`SharpFirstBaseInputs.ofFields`). -/
noncomputable def ShPT (O : CompanionObligations hW hMR hFour hB hRR UpT) :
    SharpBaseInputsPT (O.F.X hB hRR).toJoint where
  SF := SharpFirstBaseInputs.ofFields _ O.sf.dec O.sf.ε O.hεS0 O.hεSt O.sf.c O.hcS O.sf.rp O.sf.rm
    O.hrpm0 O.hfold O.hremS
  c₂ := O.c₂
  hc₂ := O.hc₂
  fixL := O.fixL
  fixR := O.fixR
  envL := O.envL
  envR := O.envR

/-- **`MainFinalObligationsKT1` from the companion obligations**: `F := F.toK` (SD2, FD, NB3),
`Cls := O.Cls` (CM), `Sh := O.ShPT.toSharpPartsBase …` (SH2). -/
noncomputable def toKT1 (O : CompanionObligations hW hMR hFour hB hRR UpT) :
    MainFinalObligationsKT1 hW hMR hFour hB hRR UpT where
  F := O.F.toK
  Cls := O.Cls
  Sh := O.ShPT.toSharpPartsBase (ThetaOne.paperAtomMap_paperBlockOf_surjective f1Cell)

end CompanionObligations

/-- **The companion statement** (`thm:main` at `ε = 10⁻⁵`; `thm:density:induction` at `ϑ = 1`
with the four-routes closing at `a_T`): `s(N) ≤ C·N^{0.99999}` from
* **(L)** H1 `Weil`, H2 `BMOR`, H5 `MovingRoot`, H6 `FourCycle` (`thm:dl:K`),
  H2″ `ThetaSmallRR`;
* **(F)** the finite record table `UpT` (`def:upper-comparison`, `lem:record:domain`(ii));
* the obligations `O : CompanionObligations`, grouped by kind.

It is `main_goal_theta1k` at `O.toKT1`, with all of SD2's, NB3's, FD's, SH2's and CM's
reductions. -/
theorem main_goal_companion (hWeil : Target.Weil) (hBMOR : Target.BMOR)
    (hMovingRoot : Target.MovingRoot)
    (hFourCycle : Target.FourCycle) (hThetaSmallRR : Target.ThetaSmallRR)
    (UpT : UpperRecordTables)
    (O : CompanionObligations hWeil hMovingRoot hFourCycle hBMOR hThetaSmallRR UpT) :
    Target.SarkozyBound TargetGoal.epsGoal :=
  main_goal_theta1k hWeil hBMOR hMovingRoot hFourCycle hThetaSmallRR UpT O.toKT1

end Sarkozy.Companion
