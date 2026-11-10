module

public import Sarkozy.CompanionND.Main
public import Sarkozy.ClassSlack.NoMean

@[expose] public section

/-!
# The rebased companion statement without the middle mean credit (`main_goal_rebased_cg`)

CG, 7 November 2026. `CompanionND.main_goal_rebased_nd` takes CM's class route
(`MeanCredit2.classPartsPaper`), which books the middle mean credit of `prop:joint-middle-mean`
(families (i)–(iv), `64 Δ_mid = 1.0873` in the 63-scaled gate) through labelled diagonals. At the
rebased ledger the AllocJ spare (`12/5` stated, about `2.51`) pays for that credit, so the class
group closes without it (`ClassSlack.classPartsNoMean`, `noMean_room`).

* **`CompanionObligationsCG`**: `CompanionND.CompanionObligationsND` with
  - removed: the family coefficients `μK` and their side conditions `hμ0`, `hμle`, `hz`, `hnz`;
    the mean letters' totals `hXm`; the residual gates `hres` (F); the identification `hmean`
    (`MeanId`, C);
  - weakened: `hm` (`SelMean` at `μ = μK(label)`) becomes `hm₁` (`SelMean` at `μ = 0`: the
    one-block credit `m₁` only);
  - restated: the weights at `1/2` (`hwHalf`, `hvV`, and the `wt` of `ops`, `hup`; the effective
    weight per selection `diagW` is unchanged); `hc0 : c ≥ 0`;
  - tightened: `hτ : τ ≤ 1/50` (it was `3/100`).

  Every other field is a verbatim copy of `CompanionObligationsND`'s.
* `W`, `hwW` (proved), `E1`, **`Cls`** (`classPartsNoMean`), **`ShPT`**, **`toKT1`**;
* **`main_goal_rebased_cg`**: `Target.SarkozyBound TargetGoal.epsGoal`, by the same endgame as
  `main_goal_rebased_nd`.
-/

open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.ClassSlack

open Sarkozy.PartV Sarkozy.BlockSpecPaper Sarkozy.MainCombined Sarkozy.MainCombined2
open Sarkozy.ClassBoundsPaper Sarkozy.ClassInputsPaper Sarkozy.ClassData Sarkozy.MainFinal2
open Sarkozy.MainFinalF1b Sarkozy.MeanCredit Sarkozy.MeanCredit2
open Sarkozy.TheoremC Sarkozy.TheoremCBlock Sarkozy.JointClosing
open Sarkozy.RecordExpansion Sarkozy.RecordExpansion.Choice
open Sarkozy.ThetaOne Sarkozy.SharpBase2
open Sarkozy.EnvelopeEnergiesPaper (paper_pairwise)
open Sarkozy.AnalyticCells (f1Cell)
open Sarkozy.UpperCapsPaper (UpperRecordTables)
open Sarkozy.CompanionND (CompanionFrontND)
open Sarkozy.Companion (E1R0 E1R E1Sub E1Coup E1Rem E1InputsAgg.ofFields SFData SFFold SFRem
  SharpFirstBaseInputs.ofFields ResidualId CompId TotalsLe)

/-- **The obligations of `main_goal_rebased_cg`**: `CompanionND.CompanionObligationsND` without the
middle mean credit (module docstring): no `μK`, `hμ0`, `hμle`, `hz`, `hnz`, `hXm`, `hres`,
`hmean`; `hm₁` (`SelMean` at `μ = 0`) for `hm`; the weights at `1/2`; `hc0`;
`τ ≤ 13/625 = 0.0208`. Grouped by kind (`TRUST_MAP.md` §3): the front, the free data (D),
their side conditions (S), and the hypotheses with content: (F) finite numerical claims,
(R) routine analytic lemmas, (C) novel core. -/
structure CompanionObligationsCG (hW : Target.Weil) (hMR : Target.MovingRoot)
    (hFour : Target.FourCycle) (hB : Target.BMOR) (hRR : Target.ThetaSmallRR)
    (UpT : UpperRecordTables) : Type 1 where
  /-- **The front** (5 fields, kinds marked in `CompanionFrontND`): `PCu` (C + F), `BA` (C),
  `rep` (C), `hs`, `ha` (F + R). The signed decomposition is proved below the front (ND). -/
  F : CompanionFrontND hW hMR hFour UpT
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
  /-- (S) The class weights are nonnegative. -/
  wc_nonneg : ∀ L i j, 0 ≤ wc L i j
  /-- (S) **`hwHalf`**: the aggregated class weight of a label is twice the paper's
  `κ_b − var = diagW` of its type (the residual table of `prop:joint-middle-mean`, aggregated at
  the weight `1/2`, so that the effective weight per selection is `diagW`). It pins `wc`; the
  content is then in `ops`. -/
  hwHalf : WeightsHalf (F.X hB hRR).data cd labK wc
  /-- (S) The aggregated label prices are uniformly bounded. -/
  hVv : 0 ≤ Vv
  hvV : PriceBoundHalf (F.X hB hRR).data cd labS Vv
  /-- (S) The per-selection energies are nonnegative. -/
  hZs : ∀ L A ω, 0 ≤ Zs L A ω
  /-- (S) The letter totals are nonnegative. The mean letters are not pinned (no `hXm`): no mean
  is retained, so they are ordinary letters. -/
  hX0 : ∀ l, 0 ≤ X l
  /-- (S) The comparison coefficient is nonnegative (it replaces the residual gates `hres`). -/
  hc0 : ∀ d, 0 ≤ c d
  /-- (S) The slack of the comparison series is at most `13/625 = 0.0208`
  (CG: `63 τ + 64 Δ_mid ≤ 12/5`,
  `noMean_room`; CM's route with the mean credit allows `3/100`). -/
  hτ : τ ≤ 13 / 625
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
  hup : SelUpper (F.X hB hRR).data cd labS (wtHalf K) Zs wc
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
    (fun L A => agg (cd.sel L) (labS L) (wtHalf K) (Zs L A)) wc ρ
  /-- **(C)** `MD.mean` with no retained diagonal (`prop:record:mean-credit` Steps 1–3, the
  one-block credit `m₁` only): the mean energies retain `(m₁ − o(1))Y` (`SelMean` at `μ = 0`).
  The families (i)–(iv) of `prop:joint-middle-mean` are not used. *Open*. -/
  hm₁ : SelMean (F.X hB hRR).data cd (fun _ _ => 0) Zs
  /-- **(C)** The residual of a class selection is `r_ω` times its monomial
  (`cor:envelope-costs`). *Open*. -/
  hρ : ResidualId (F.X hB hRR).data cd ρ r
  /-- **(C)** `hcomp`: the comparison coefficient of a selection's letter degree dominates its
  class bound (`thm:envelopes`(i), `cor:envelope-costs`): `B` off the classes, `r_ω` on them,
  plus `diagW` on its label. *Open*. -/
  hcomp : CompId (F.X hB hRR).data cd labS labK ℓ c r
  /-- **(C)** `hX`: the formal letter totals are at most `X` (the price bounds of
  `lem:four-routes-normalized`). Without `hXm`, its content is joint with `hC`, `hcomp` only.
  *Open*. -/
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

attribute [instance] CompanionObligationsCG.instFK CompanionObligationsCG.instDK
  CompanionObligationsCG.instFLt CompanionObligationsCG.instDLt

namespace CompanionObligationsCG

variable {hW : Target.Weil} {hMR : Target.MovingRoot} {hFour : Target.FourCycle}
  {hB : Target.BMOR} {hRR : Target.ThetaSmallRR} {UpT : UpperRecordTables}

/-- The uniform bound of the aggregated class weights, `∑_k 2 diagW(k)`. -/
noncomputable def W (O : CompanionObligationsCG hW hMR hFour hB hRR UpT) : ℝ :=
  ∑ k, 2 * (diagW (O.labK k) : ℝ)

theorem weight_nonneg (O : CompanionObligationsCG hW hMR hFour hB hRR UpT) (k : O.K) :
    0 ≤ 2 * (diagW (O.labK k) : ℝ) := by
  have h := diagW_pos (O.labK k)
  have h' : (0 : ℝ) < diagW (O.labK k) := by exact_mod_cast h
  linarith

theorem W_nonneg (O : CompanionObligationsCG hW hMR hFour hB hRR UpT) : 0 ≤ O.W :=
  Finset.sum_nonneg fun k _ => O.weight_nonneg k

theorem hwW (O : CompanionObligationsCG hW hMR hFour hB hRR UpT) (L : ℕ) (k : O.K) :
    ∑ i, O.wc L i k ≤ O.W := by
  rw [O.hwHalf L k]
  exact Finset.single_le_sum (f := fun k => 2 * (diagW (O.labK k) : ℝ))
    (fun k _ => O.weight_nonneg k) (Finset.mem_univ k)

/-- **(E1)** from the flattened fields (`E1InputsAgg.ofFields`). -/
noncomputable def E1 (O : CompanionObligationsCG hW hMR hFour hB hRR UpT) :
    E1InputsAgg (O.F.X hB hRR).data :=
  E1InputsAgg.ofFields _ O.εE O.hεE0 O.hεEt O.cE O.hcE O.r0 O.rE O.hsub O.hcoup O.hremE O.hrE0
    O.hr00

/-- **The class group without the middle mean credit** (`ClassSlack.classPartsNoMean`;
`cor:joint-closing`, `prop:record:mean-credit`, `eq:final-joint-closing`), at the joint block data
of the front: the same data `D` as the field `Cls` of `MainFinalObligationsKT1` at
`F := O.F.toK`. -/
noncomputable def Cls (O : CompanionObligationsCG hW hMR hFour hB hRR UpT) :
    ClassPartsE4B (O.F.X hB hRR).data :=
  classPartsNoMean (D := (O.F.X hB hRR).data) (cd := O.cd) (K := O.K) (C := O.Lt)
    O.labS O.labK O.Zs O.wc O.wc_nonneg O.ρ O.ops O.hup
    (WeightsHalf.toAggED O.Zs O.wc O.wc_nonneg O.ρ O.ops O.hup O.hwHalf) O.W O.Vv O.W_nonneg O.hVv
    (weightsBound_toAggED O.Zs O.wc O.wc_nonneg O.ρ O.ops O.hup O.hwW)
    (PriceBoundHalf.toAggED O.Zs O.wc O.wc_nonneg O.ρ O.ops O.hup O.hvV) O.hZs O.hm₁ O.ℓ O.c O.hc0
    O.X O.hX0 O.hX O.Cv O.τ O.hτ O.hC O.hCv O.r O.hρ O.hcomp O.E1

/-- **The sharp inputs, SH2's per-term route** (`SharpBaseInputsPT`), as in
`CompanionObligationsND.ShPT`. -/
noncomputable def ShPT (O : CompanionObligationsCG hW hMR hFour hB hRR UpT) :
    SharpBaseInputsPT (O.F.X hB hRR).toJoint where
  SF := SharpFirstBaseInputs.ofFields _ O.sf.dec O.sf.ε O.hεS0 O.hεSt O.sf.c O.hcS O.sf.rp O.sf.rm
    O.hrpm0 O.hfold O.hremS
  c₂ := O.c₂
  hc₂ := O.hc₂
  fixL := O.fixL
  fixR := O.fixR
  envL := O.envL
  envR := O.envR

/-- **`MainFinalObligationsKT1` from the CG obligations**: `F := F.toK` (ND, FD, NB3),
`Cls := O.Cls` (CG), `Sh := O.ShPT.toSharpPartsBase …` (SH2). -/
noncomputable def toKT1 (O : CompanionObligationsCG hW hMR hFour hB hRR UpT) :
    MainFinalObligationsKT1 hW hMR hFour hB hRR UpT where
  F := O.F.toK
  Cls := O.Cls
  Sh := O.ShPT.toSharpPartsBase (ThetaOne.paperAtomMap_paperBlockOf_surjective f1Cell)

end CompanionObligationsCG

/-- **The rebased companion statement without the middle mean credit** (`thm:main` at
`ε = 10⁻⁵`; `thm:density:induction` at `ϑ = 1` with the four-routes closing at the rebased ledger
`a_G = 71/10⁵`): `s(N) ≤ C·N^{0.99999}` from
* **(L)** H1 `Weil`, H2 `BMOR`, H5 `MovingRoot`, H6 `FourCycle` (`thm:dl:K`),
  H2″ `ThetaSmallRR`;
* **(F)** the finite record table `UpT` (`def:upper-comparison`, `lem:record:domain`(ii));
* the obligations `O : CompanionObligationsCG` (no `hmean`, `hres`, `hXm`, `μK`; `hm₁` for `hm`;
  `τ ≤ 13/625 = 0.0208`).

As `CompanionND.main_goal_rebased_nd`: the endgame at `O.toKT1.toT1.toGP.toG`, whose saving is
`epsGoal` (`Rebase.targetSaving_eq_epsGoal`). -/
theorem main_goal_rebased_cg (hWeil : Target.Weil) (hBMOR : Target.BMOR)
    (hMovingRoot : Target.MovingRoot)
    (hFourCycle : Target.FourCycle) (hThetaSmallRR : Target.ThetaSmallRR)
    (UpT : UpperRecordTables)
    (O : CompanionObligationsCG hWeil hMovingRoot hFourCycle hBMOR hThetaSmallRR UpT) :
    Target.SarkozyBound TargetGoal.epsGoal := by
  have h := MainCombined.main_target_f1_final3gc hWeil hBMOR hMovingRoot hFourCycle
    hThetaSmallRR O.toKT1.toT1.toGP.toG
  rwa [Rebase.targetSaving_eq_epsGoal] at h

end Sarkozy.ClassSlack
