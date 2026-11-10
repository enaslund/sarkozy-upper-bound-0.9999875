module

public import Sarkozy.OpsCore.Data
public import Sarkozy.E1Closure.Main

@[expose] public section

/-!
# The companion statement without the links `hρ` and `hup` (`main_goal_rebased_bl`)

BL, 10 November 2026. `CompanionObligationsEC` has two free data, the residuals `ρ` and the
per-selection energies `Zs`, whose only roles are to link `ops` to the prices:

* `hρ : ResidualId ρ r` (kind C) says `ρ_ω ≤ r_ω π_ω` on the class selections;
* `hup : SelUpper Zs` (kind R) says `Zs_ω ≤ (1 + ε₃) π_ω Y + rs_ω` on the labelled selections,
  with `ε₃ → 0` and the remainders `rs` summed against the class weights; with `hZs : 0 ≤ Zs`.

`ops` is monotone in both (`OpsCore.ClassStepsOps.mono`), so nothing is lost by evaluating it at
the largest values these links allow. This file does that:

* **`UpperSlack`**: the data `ε₃`, `c₃`, `rs` of `hup` and their side conditions, which are
  satisfied by `UpperSlack.zero`, so the field asserts nothing;
* **`UpperSlack.zs`**: `(1 + ε₃) π_ω Y⁺ + rs_ω`; `zs_nonneg` and `selUpper` (`hZs`, `hup` hold);
  `exists_slack`: every `Zs` satisfying `hup` lies below some `S.zs` at the counterexamples;
* **`CompanionObligationsBL`**: EC's obligations without `Zs`, `ρ`, `hZs`, `hup`, `hρ`, with the
  slack `up`, and with `ops` stated at `Zs = up.zs`, `ρ = r π`. Every other field is verbatim;
* **`toEC`**, **`ofEC`**, **`nonempty_iff`**: the two sets of obligations are equivalent;
* **`main_goal_rebased_bl`**: `Target.SarkozyBound TargetGoal.epsGoal`.

This is bookkeeping: no analytic statement is proved here. The content of `hρ` and `hup` moves
into `ops`, which must now reach the budgets `r π` and `(1 + ε₃) π Y⁺ + rs` directly, as
`thm:envelopes`(i) does (it ends at `∑ (φ_ω + o(1) π_ω) Y`). The kinds become: novel core 8 → 7,
routine 1 → 0.
-/

open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.BudgetLinks

open Sarkozy.ClassSlack Sarkozy.ClassInputsPaper Sarkozy.ClassData Sarkozy.MainFinal2
open Sarkozy.MeanCredit Sarkozy.RecordExpansion Sarkozy.RecordExpansion.Choice
open Sarkozy.UpperCapsPaper (UpperRecordTables)
open Sarkozy.CompanionND (CompanionFrontND)
open Sarkozy.Companion (CompId TotalsLe ResidualId)
open Sarkozy.E1Closure (CompanionObligationsEC main_goal_rebased_ec)
open Sarkozy.MeanCredit2
open Sarkozy.OpsCore (rhoOf residualId_rhoOf sum_le_rhoOf)
open Sarkozy.CancellationSteps (PaperJ0)

section Slack

variable {B : Type} [Fintype B] [DecidableEq B] {blockOf : PaperJ0 → B}
  {D : CD blockOf} {cd : ClassData D.CL} {K : Type} [Fintype K]
  {labS : ∀ L, Choice (D.CL.T L) → Option K} {wt : K → ℝ} {wc : ∀ L, cd.ι L → K → ℝ}

/-- **The slack of the upper prices**: the data `ε₃ → 0`, `c₃`, `rs` of `SelUpper`, with their
side conditions. `UpperSlack.zero` satisfies them, so this asserts nothing about the paper. -/
structure UpperSlack (D : CD blockOf) (cd : ClassData D.CL) {K : Type} [Fintype K]
    (labS : ∀ L, Choice (D.CL.T L) → Option K) (wt : K → ℝ) (wc : ∀ L, cd.ι L → K → ℝ) where
  /-- The relative slack. -/
  ε₃ : ℕ → ℝ
  ε₃_nonneg : ∀ L, 0 ≤ ε₃ L
  ε₃_tendsto : Tendsto ε₃ atTop (𝓝 0)
  /-- The constant of the summed remainders. -/
  c₃ : ℝ
  c₃_nonneg : 0 ≤ c₃
  /-- The per-selection remainders. -/
  rs : ∀ L, Finset ℤ → Choice (D.CL.T L) → ℝ
  rs_nonneg : ∀ L A ω, 0 ≤ rs L A ω
  rs_sum : Param.AtCounterexamples (Param.Params.ofDecay TargetLedger.targetDecay) D.Y
    (fun L A => ∑ ω ∈ cd.sel L, coefOf (fun j => ∑ i, wc L i j) wt (labS L ω) * rs L A ω ≤
      Comparison.remainder c₃ L A)

/-- **Non-vacuity**: the zero slack. -/
noncomputable def UpperSlack.zero (labS : ∀ L, Choice (D.CL.T L) → Option K) (wt : K → ℝ)
    (wc : ∀ L, cd.ι L → K → ℝ) : UpperSlack D cd labS wt wc where
  ε₃ := fun _ => 0
  ε₃_nonneg := fun _ => le_rfl
  ε₃_tendsto := tendsto_const_nhds
  c₃ := 0
  c₃_nonneg := le_rfl
  rs := fun _ _ _ => 0
  rs_nonneg := fun _ _ _ => le_rfl
  rs_sum := Eventually.of_forall fun L _ _ _ A _ _ => by
    simp only [mul_zero, sum_const_zero]
    unfold Comparison.remainder
    simp

/-- **The energies at their largest admissible values**: `(1 + ε₃) π_ω Y⁺ + rs_ω`. -/
noncomputable def UpperSlack.zs (S : UpperSlack D cd labS wt wc) (L : ℕ) (A : Finset ℤ)
    (ω : Choice (D.CL.T L)) : ℝ :=
  (monomial (D.CL.π L) ω + S.ε₃ L * monomial (D.CL.π L) ω) * max (D.Y L A) 0 + S.rs L A ω

/-- `hZs` at `S.zs`. -/
theorem UpperSlack.zs_nonneg (S : UpperSlack D cd labS wt wc) (L : ℕ) (A : Finset ℤ)
    (ω : Choice (D.CL.T L)) : 0 ≤ S.zs L A ω := by
  have h := monomial_nonneg (cd.π_nonneg L) ω
  exact add_nonneg (mul_nonneg (add_nonneg h (mul_nonneg (S.ε₃_nonneg L) h))
    (le_max_right _ _)) (S.rs_nonneg L A ω)

/-- `hup` at `S.zs`. -/
theorem UpperSlack.selUpper (S : UpperSlack D cd labS wt wc) :
    SelUpper D cd labS wt S.zs wc := by
  refine ⟨S.ε₃, S.ε₃_nonneg, S.ε₃_tendsto, S.c₃, S.c₃_nonneg, S.rs, S.rs_nonneg, ?_, S.rs_sum⟩
  refine Eventually.of_forall fun L C hC _ A _ hcount ω _ _ => ?_
  have hY := (Param.counterexample_pos (Param.Params.ofDecay TargetLedger.targetDecay) hC
    hcount).le
  refine le_of_eq ?_
  unfold UpperSlack.zs
  rw [max_eq_left hY]

/-- **Every `Zs` satisfying `hup` lies below some `S.zs`** at the counterexamples, on the labelled
selections. -/
theorem exists_slack {Zs : ∀ L, Finset ℤ → Choice (D.CL.T L) → ℝ}
    (h : SelUpper D cd labS wt Zs wc) :
    ∃ S : UpperSlack D cd labS wt wc,
      Param.AtCounterexamples (Param.Params.ofDecay TargetLedger.targetDecay) D.Y (fun L A =>
        ∀ ω ∈ cd.sel L, labS L ω ≠ none → Zs L A ω ≤ S.zs L A ω) := by
  obtain ⟨ε₃, h0, ht, c₃, hc, rs, hrs, hle, hsum⟩ := h
  refine ⟨⟨ε₃, h0, ht, c₃, hc, rs, hrs, hsum⟩, ?_⟩
  filter_upwards [hle] with L hL C hC hind A hA hcount ω hω hl
  refine (hL C hC hind A hA hcount ω hω hl).trans ?_
  have hπ := monomial_nonneg (cd.π_nonneg L) ω
  have hnn : 0 ≤ monomial (D.CL.π L) ω + ε₃ L * monomial (D.CL.π L) ω :=
    add_nonneg hπ (mul_nonneg (h0 L) hπ)
  have hm := mul_le_mul_of_nonneg_left (le_max_left (D.Y L A) 0) hnn
  simp only [UpperSlack.zs]
  linarith

/-- **`ops` transfers to the largest admissible budgets.** -/
theorem ops_transfer [DecidableEq K] {Zs : ∀ L, Finset ℤ → Choice (D.CL.T L) → ℝ}
    {ρ r : ∀ L, Choice (D.CL.T L) → ℝ}
    (O : ClassStepsOps cd (fun _ => K)
      (fun L A => agg (cd.sel L) (labS L) (wtHalf K) (Zs L A)) wc ρ)
    (hwc : ∀ L i j, 0 ≤ wc L i j) (hρ : ResidualId D cd ρ r)
    (S : UpperSlack D cd labS (wtHalf K) wc)
    (hS : Param.AtCounterexamples (Param.Params.ofDecay TargetLedger.targetDecay) D.Y (fun L A =>
      ∀ ω ∈ cd.sel L, labS L ω ≠ none → Zs L A ω ≤ S.zs L A ω)) :
    Nonempty (ClassStepsOps cd (fun _ => K)
      (fun L A => agg (cd.sel L) (labS L) (wtHalf K) (S.zs L A)) wc (rhoOf r)) := by
  refine OpsCore.ClassStepsOps.mono O ?_ (sum_le_rhoOf hρ)
  filter_upwards [hS] with L hL C hC hind A hA hcount
  have hle := hL C hC hind A hA hcount
  have hagg : ∀ j, agg (cd.sel L) (labS L) (wtHalf K) (Zs L A) j ≤
      agg (cd.sel L) (labS L) (wtHalf K) (S.zs L A) j := fun j =>
    sum_le_sum fun ω hω => by
      have hm := mem_filter.mp hω
      exact mul_le_mul_of_nonneg_left
        (hle ω hm.1 (by rw [hm.2]; exact Option.some_ne_none j)) (wtHalf_nonneg K j)
  have hagg0 : ∀ j, 0 ≤ agg (cd.sel L) (labS L) (wtHalf K) (S.zs L A) j := fun j =>
    sum_nonneg fun ω _ => mul_nonneg (wtHalf_nonneg K j) (S.zs_nonneg L A ω)
  exact ⟨fun n => sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (hagg j) (hwc _ _ _),
    fun v => sum_nonneg fun j _ => mul_nonneg (hwc _ _ _) (hagg0 j)⟩

end Slack

/-- **The obligations of `main_goal_rebased_bl`**: EC's `CompanionObligationsEC` without the data
`Zs`, `ρ` and the fields `hZs`, `hup`, `hρ`, with the slack `up` (data and side conditions only)
and with `ops` at `Zs = up.zs`, `ρ = r π`. Every other field is a verbatim copy of EC's.
Equivalent to EC's (`toEC`, `ofEC`). 31 fields. -/
structure CompanionObligationsBL (hW : Target.Weil) (hMR : Target.MovingRoot)
    (hFour : Target.FourCycle) (hB : Target.BMOR) (hRR : Target.ThetaSmallRR)
    (UpT : UpperRecordTables) : Type 1 where
  /-- **The front** (as EC's). -/
  F : CompanionFrontND hW hMR hFour UpT
  /-- (D) The classes (as EC's). -/
  cd : ClassData (F.X hB hRR).data.CL
  /-- (D) The labels of the aggregated diagonals (as EC's). -/
  K : Type
  [instFK : Fintype K]
  [instDK : DecidableEq K]
  /-- (D) The letters other than the mean letters (as EC's). -/
  Lt : Type
  [instFLt : Fintype Lt]
  [instDLt : DecidableEq Lt]
  /-- (D) The label of each selection (as EC's). -/
  labS : ∀ L, Choice ((F.X hB hRR).data.CL.T L) → Option K
  /-- (D) The paper type of each label (as EC's). -/
  labK : K → PaperDiag
  /-- (D) The class weights on the labels (as EC's). -/
  wc : ∀ L, cd.ι L → K → ℝ
  /-- (D, S) The slack of the upper prices. Replaces `Zs`, `hZs`, `hup`. Asserts nothing about the
  paper (`UpperSlack.zero`). -/
  up : UpperSlack (F.X hB hRR).data cd labS (wtHalf K) wc
  /-- (D) The per-selection residual coefficients (as EC's). -/
  r : ∀ L, Choice ((F.X hB hRR).data.CL.T L) → ℝ
  /-- (D) The uniform bound of the label prices (as EC's). -/
  Vv : ℝ
  /-- (D) The lettering of the record expansion (as EC's). -/
  ℓ : ∀ L, Entry ((F.X hB hRR).data.CL.T L) → MLetter ⊕ Lt
  /-- (D) The comparison coefficient of a letter degree (as EC's). -/
  c : (MLetter ⊕ Lt → ℕ) → ℝ
  /-- (D) The letter totals (as EC's). -/
  X : MLetter ⊕ Lt → ℝ
  /-- (D) The completed comparison series and its slack (as EC's). -/
  Cv : ℝ
  τ : ℝ
  /-- (S) As EC's. -/
  wc_nonneg : ∀ L i j, 0 ≤ wc L i j
  /-- (S) As EC's. -/
  hwHalf : WeightsHalf (F.X hB hRR).data cd labK wc
  /-- (S) As EC's. -/
  hVv : 0 ≤ Vv
  hvV : PriceBoundHalf (F.X hB hRR).data cd labS Vv
  /-- (S) As EC's. -/
  hX0 : ∀ l, 0 ≤ X l
  /-- (S) As EC's. -/
  hc0 : ∀ d, 0 ≤ c d
  /-- (S) As EC's. -/
  hτ : τ ≤ 13 / 625
  /-- **(F)** As EC's. -/
  hC : HasSum (fun d => c d * ∏ l, X l ^ d l / (d l).factorial) Cv
  /-- **(F)** As EC's. -/
  hCv : Cv ≤ harnessE + τ
  /-- **(C)** EC's `ops`, at the budgets `Zs = up.zs` and `ρ = r π`. *Open*. -/
  ops : ClassStepsOps cd (fun _ => K)
    (fun L A => agg (cd.sel L) (labS L) (wtHalf K) (up.zs L A)) wc (rhoOf r)
  /-- **(C)** As EC's. *Open*. -/
  hcomp : CompId (F.X hB hRR).data cd labS labK ℓ c r
  /-- **(C)** As EC's. *Open*. -/
  hX : TotalsLe (F.X hB hRR).data ℓ X

attribute [instance] CompanionObligationsBL.instFK CompanionObligationsBL.instDK
  CompanionObligationsBL.instFLt CompanionObligationsBL.instDLt

namespace CompanionObligationsBL

variable {hW : Target.Weil} {hMR : Target.MovingRoot} {hFour : Target.FourCycle}
  {hB : Target.BMOR} {hRR : Target.ThetaSmallRR} {UpT : UpperRecordTables}

/-- **The EC obligations**: `Zs := up.zs`, `ρ := r π`; `hZs`, `hup`, `hρ` are theorems there. -/
noncomputable def toEC (O : CompanionObligationsBL hW hMR hFour hB hRR UpT) :
    CompanionObligationsEC hW hMR hFour hB hRR UpT where
  F := O.F
  cd := O.cd
  K := O.K
  Lt := O.Lt
  labS := O.labS
  labK := O.labK
  Zs := O.up.zs
  wc := O.wc
  ρ := rhoOf O.r
  r := O.r
  Vv := O.Vv
  ℓ := O.ℓ
  c := O.c
  X := O.X
  Cv := O.Cv
  τ := O.τ
  wc_nonneg := O.wc_nonneg
  hwHalf := O.hwHalf
  hVv := O.hVv
  hvV := O.hvV
  hZs := O.up.zs_nonneg
  hX0 := O.hX0
  hc0 := O.hc0
  hτ := O.hτ
  hC := O.hC
  hCv := O.hCv
  hup := O.up.selUpper
  ops := O.ops
  hρ := residualId_rhoOf O.r
  hcomp := O.hcomp
  hX := O.hX

/-- **Losslessness**: every `CompanionObligationsEC` gives a `CompanionObligationsBL`. The slack
is `hup`'s, and `ops` moves to the larger budgets (`ops_transfer`). -/
noncomputable def ofEC (O : CompanionObligationsEC hW hMR hFour hB hRR UpT) :
    CompanionObligationsBL hW hMR hFour hB hRR UpT where
  F := O.F
  cd := O.cd
  K := O.K
  Lt := O.Lt
  labS := O.labS
  labK := O.labK
  wc := O.wc
  up := Classical.choose (exists_slack O.hup)
  r := O.r
  Vv := O.Vv
  ℓ := O.ℓ
  c := O.c
  X := O.X
  Cv := O.Cv
  τ := O.τ
  wc_nonneg := O.wc_nonneg
  hwHalf := O.hwHalf
  hVv := O.hVv
  hvV := O.hvV
  hX0 := O.hX0
  hc0 := O.hc0
  hτ := O.hτ
  hC := O.hC
  hCv := O.hCv
  ops := Classical.choice (ops_transfer O.ops O.wc_nonneg O.hρ _
    (Classical.choose_spec (exists_slack O.hup)))
  hcomp := O.hcomp
  hX := O.hX

/-- **The two sets of obligations are equivalent.** -/
theorem nonempty_iff :
    Nonempty (CompanionObligationsBL hW hMR hFour hB hRR UpT) ↔
      Nonempty (CompanionObligationsEC hW hMR hFour hB hRR UpT) :=
  ⟨fun ⟨O⟩ => ⟨O.toEC⟩, fun ⟨O⟩ => ⟨ofEC O⟩⟩

end CompanionObligationsBL

/-- **The companion statement without the links `hρ` and `hup`** (`thm:main` at `ε = 10⁻⁵`):
`s(N) ≤ C·N^{0.99999}` from the literature (L), the record table `UpT` (F) and the obligations
`O : CompanionObligationsBL`, which are equivalent to EC's. -/
theorem main_goal_rebased_bl (hWeil : Target.Weil) (hBMOR : Target.BMOR)
    (hMovingRoot : Target.MovingRoot)
    (hFourCycle : Target.FourCycle) (hThetaSmallRR : Target.ThetaSmallRR)
    (UpT : UpperRecordTables)
    (O : CompanionObligationsBL hWeil hMovingRoot hFourCycle hBMOR hThetaSmallRR UpT) :
    Target.SarkozyBound TargetGoal.epsGoal :=
  main_goal_rebased_ec hWeil hBMOR hMovingRoot hFourCycle hThetaSmallRR UpT O.toEC

end Sarkozy.BudgetLinks
