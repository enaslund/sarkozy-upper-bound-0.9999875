module

public import Sarkozy.ClassSlack.Main

@[expose] public section

/-!
# Non-vacuity of the mean-free class group (CG)

**`ofND`**: every `CompanionND.CompanionObligationsND` with `τ ≤ 13/625 = 0.0208` gives a
`CompanionObligationsCG` at the same front, classes, labels, letters, comparison coefficient,
totals and series. So the CG obligations are satisfiable whenever ND's are (at that
`τ`), and the removed fields (`μK`, `hμ0`, `hμle`, `hz`, `hnz`, `hXm`, `hres`, `hmean`) are not
hidden elsewhere.
The weights are rescaled from CM's exact weights `wtOf` to `1/2` (`wc' = wc · 2 wtOf`), which
leaves every product `w · wt` unchanged (`opsHalf`, `selUpperHalf`); `hm₁` follows from ND's `hm`
because the retained mean `∑ μ_ω Z_ω` is nonnegative (`selMean_zero`).

`c ≥ 0` follows from ND's `hres : 63 c − mLift ≥ 0`, since `mLift ≥ 0` (`mLift_nonneg`: every
family coefficient of `mPaper` is a nonnegative constant times a power of `r ≥ 0`).

**`main_goal_of_nd`**: `main_goal_rebased_cg` applied to `ofND O`.

**`numerics_satisfiable_cg`**: the numerical side conditions and claims of CG (`hc0`, `hX0`,
`hτ`, `hC`, `hCv`) hold together (trivially, at `c = 0`; their content is joint with `hcomp`).
-/

open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.ClassSlack

open Sarkozy.ClassBoundsPaper Sarkozy.ClassInputsPaper Sarkozy.ClassData Sarkozy.MainFinal2
open Sarkozy.MainFinalF1b Sarkozy.MeanCredit Sarkozy.MeanCredit2
open Sarkozy.TheoremC Sarkozy.TheoremCBlock Sarkozy.JointClosing
open Sarkozy.RecordExpansion Sarkozy.RecordExpansion.Choice
open Sarkozy.CancellationSteps (PaperJ0)
open Sarkozy.UpperCapsPaper (UpperRecordTables)
open Sarkozy.Companion (WeightsPaper PriceBound)

section Generic

variable {B : Type} [Fintype B] [DecidableEq B] {blockOf : PaperJ0 → B}
  {D : CD blockOf} {cd : ClassData D.CL} {K : Type} [Fintype K] [DecidableEq K]

/-- The rescaled class weights: `wc' = wc · 2 wtOf`. -/
noncomputable def wcHalf (labK : K → PaperDiag) (μK : K → ℝ) (wc : ∀ L, cd.ι L → K → ℝ) :
    ∀ L, cd.ι L → K → ℝ :=
  fun L i k => wc L i k * (2 * wtOf labK μK k)

omit [Fintype K] in
theorem agg_half_eq (labS : ∀ L, Choice (D.CL.T L) → Option K) (labK : K → PaperDiag)
    (μK : K → ℝ) (L : ℕ) (f : Choice (D.CL.T L) → ℝ) (k : K) :
    2 * wtOf labK μK k * agg (cd.sel L) (labS L) (wtHalf K) f k =
      agg (cd.sel L) (labS L) (wtOf labK μK) f k := by
  unfold agg wtHalf
  rw [mul_sum]
  exact sum_congr rfl fun ω _ => by ring

/-- The class-weighted diagonal energies are unchanged by the rescaling. -/
theorem wcHalf_sum (labS : ∀ L, Choice (D.CL.T L) → Option K) (labK : K → PaperDiag)
    (μK : K → ℝ) (wc : ∀ L, cd.ι L → K → ℝ) (L : ℕ) (f : Choice (D.CL.T L) → ℝ) (i : cd.ι L) :
    ∑ j, wcHalf labK μK wc L i j * agg (cd.sel L) (labS L) (wtHalf K) f j =
      ∑ j, wc L i j * agg (cd.sel L) (labS L) (wtOf labK μK) f j := by
  refine sum_congr rfl fun j _ => ?_
  rw [← agg_half_eq labS labK μK L f j]
  unfold wcHalf
  ring

/-- **`ops` at the weights `1/2`**: B11's operator steps for CM's aggregation at `wtOf` are the
operator steps for the aggregation at `1/2` with the rescaled weights (the class-weighted diagonal
energies agree, `wcHalf_sum`). -/
def opsHalf (labS : ∀ L, Choice (D.CL.T L) → Option K) (labK : K → PaperDiag) (μK : K → ℝ)
    (Zs : ∀ L, Finset ℤ → Choice (D.CL.T L) → ℝ) (wc : ∀ L, cd.ι L → K → ℝ)
    (ρ : ∀ L, Choice (D.CL.T L) → ℝ)
    (ops : ClassStepsOps cd (fun _ => K)
      (fun L A => agg (cd.sel L) (labS L) (wtOf labK μK) (Zs L A)) wc ρ) :
    ClassStepsOps cd (fun _ => K) (fun L A => agg (cd.sel L) (labS L) (wtHalf K) (Zs L A))
      (wcHalf labK μK wc) ρ where
  z := ops.z
  hz0 := ops.hz0
  hz := ops.hz
  K := ops.K
  c₀ := ops.c₀
  hc₀ := ops.hc₀
  rr := ops.rr
  hrr0 := ops.hrr0
  H := by
    have h := ops.H
    filter_upwards [h] with L hL
    intro C hC hind A hA hcount
    obtain ⟨h1, h2, h3⟩ := hL C hC hind A hA hcount
    refine ⟨fun n => ?_, fun v => ?_, h3⟩
    · have e := wcHalf_sum labS labK μK wc L (Zs L A) (.inl n)
      rw [e]
      exact h1 n
    · have e := wcHalf_sum labS labK μK wc L (Zs L A) (.inr v)
      rw [e]
      exact h2 v

omit [Fintype K] [DecidableEq K] in
theorem coefOf_wcHalf (labK : K → PaperDiag) (μK : K → ℝ) (wc : ∀ L, cd.ι L → K → ℝ) (L : ℕ)
    (o : Option K) :
    coefOf (fun j => ∑ i, wcHalf labK μK wc L i j) (wtHalf K) o =
      coefOf (fun j => ∑ i, wc L i j) (wtOf labK μK) o := by
  rcases o with _ | k
  · rfl
  · simp only [coefOf, Option.elim, wcHalf, wtHalf, ← sum_mul]
    ring

omit [DecidableEq K] in
/-- **`SelUpper` at the weights `1/2`**: the remainders are summed against the same effective
weights. -/
theorem selUpperHalf (labS : ∀ L, Choice (D.CL.T L) → Option K) (labK : K → PaperDiag)
    (μK : K → ℝ) (Zs : ∀ L, Finset ℤ → Choice (D.CL.T L) → ℝ) (wc : ∀ L, cd.ι L → K → ℝ)
    (hup : SelUpper D cd labS (wtOf labK μK) Zs wc) :
    SelUpper D cd labS (wtHalf K) Zs (wcHalf labK μK wc) := by
  obtain ⟨ε₃, hε0, hε, c₃, hc₃, rs, hrs0, h1, h2⟩ := hup
  refine ⟨ε₃, hε0, hε, c₃, hc₃, rs, hrs0, h1, ?_⟩
  filter_upwards [h2] with L hL
  intro C hC hind A hA hcount
  have h := hL C hC hind A hA hcount
  simp only [coefOf_wcHalf labK μK wc L]
  exact h

omit [Fintype K] [DecidableEq K] in
/-- **`hwHalf` from CM's `hwPaper`.** -/
theorem weightsHalf_of_paper (labK : K → PaperDiag) (μK : K → ℝ) (hμ0 : ∀ k, 0 ≤ μK k)
    (hnz : ∀ k, (diagB (labK k) : ℝ) ≠ 0 → μK k ≠ 0) (wc : ∀ L, cd.ι L → K → ℝ)
    (h : WeightsPaper D cd labK μK wc) : WeightsHalf D cd labK (wcHalf labK μK wc) := by
  intro L k
  have hp := wtOf_pos labK μK hμ0 hnz k
  simp only [wcHalf]
  rw [← sum_mul, h L k]
  field_simp

/-- The price bound at the weights `1/2`: `Vv ∑_k 1/(2 wtOf k)`. -/
noncomputable def vvHalf (labK : K → PaperDiag) (μK : K → ℝ) (Vv : ℝ) : ℝ :=
  Vv * ∑ k, 1 / (2 * wtOf labK μK k)

omit [DecidableEq K] in
theorem vvHalf_nonneg (labK : K → PaperDiag) (μK : K → ℝ) (hμ0 : ∀ k, 0 ≤ μK k) (Vv : ℝ)
    (hVv : 0 ≤ Vv) : 0 ≤ vvHalf labK μK Vv :=
  mul_nonneg hVv (sum_nonneg fun k _ => by
    have := wtOf_nonneg labK hμ0 k
    positivity)

/-- **`hvV` at the weights `1/2`** from CM's `PriceBound`. -/
theorem priceBoundHalf_of_paper (labS : ∀ L, Choice (D.CL.T L) → Option K)
    (labK : K → PaperDiag) (μK : K → ℝ) (hμ0 : ∀ k, 0 ≤ μK k)
    (hnz : ∀ k, (diagB (labK k) : ℝ) ≠ 0 → μK k ≠ 0) (Vv : ℝ) (hVv : 0 ≤ Vv)
    (h : PriceBound D cd labS labK μK Vv) : PriceBoundHalf D cd labS (vvHalf labK μK Vv) := by
  intro L k
  have hp := wtOf_pos labK μK hμ0 hnz k
  have e := agg_half_eq (cd := cd) labS labK μK L (monomial (D.CL.π L)) k
  have h1 : agg (cd.sel L) (labS L) (wtHalf K) (monomial (D.CL.π L)) k ≤
      Vv * (1 / (2 * wtOf labK μK k)) := by
    rw [mul_one_div, le_div_iff₀ (by positivity), mul_comm, e]
    exact h L k
  have h2 : 1 / (2 * wtOf labK μK k) ≤ ∑ k, 1 / (2 * wtOf labK μK k) :=
    single_le_sum (f := fun k => 1 / (2 * wtOf labK μK k))
      (fun k _ => by have := wtOf_nonneg labK hμ0 k; positivity) (mem_univ k)
  unfold vvHalf
  nlinarith

/-- **`hm₁` from a retained mean with nonnegative coefficients** (`prop:record:mean-credit`): the
retained `∑ μ_ω Z_ω` is nonnegative, so `SelMean` at `μ` gives `SelMean` at `0`. -/
theorem selMean_zero (μ : ∀ L, Choice (D.CL.T L) → ℝ) (hμ : ∀ L ω, 0 ≤ μ L ω)
    (Zs : ∀ L, Finset ℤ → Choice (D.CL.T L) → ℝ) (hZs : ∀ L A ω, 0 ≤ Zs L A ω)
    (hm : SelMean D cd μ Zs) : SelMean D cd (fun _ _ => 0) Zs := by
  obtain ⟨ε₂, hε, c₂, hc₂, h⟩ := hm
  refine ⟨ε₂, hε, c₂, hc₂, ?_⟩
  filter_upwards [h] with L hL
  intro C hC hind A hA hcount
  have h1 := hL C hC hind A hA hcount
  have h2 : 0 ≤ ∑ ω ∈ cd.sel L, μ L ω * Zs L A ω :=
    sum_nonneg fun ω _ => mul_nonneg (hμ L ω) (hZs L A ω)
  simp only [zero_mul, sum_const_zero, add_zero]
  linarith

end Generic

/-! ## The paper's middle mean coefficient is nonnegative -/

section MLift

theorem bg_nonneg (a : ℕ → ℝ) (a0 : ℝ) (J j k : ℕ) (ha : ∀ j ≤ J, 0 ≤ a j) (ha0 : 0 ≤ a0) :
    0 ≤ bg a a0 J j k := by
  unfold bg
  split_ifs with h
  · exact ha j h.2
  · exact ha0

theorem famCoef_nonneg (f o e k : ℕ) (a : ℕ → ℝ) (a0 : ℝ) (J : ℕ) (d : MLetter → ℕ)
    (ha : ∀ j ≤ J, 0 ≤ a j) (ha0 : 0 ≤ a0) : 0 ≤ famCoef f o e k a a0 J d := by
  unfold famCoef
  split_ifs
  · exact bg_nonneg a a0 J _ _ ha ha0
  · exact le_rfl

theorem famI_nonneg (r : ℝ) (hr : 0 ≤ r) (d : MLetter → ℕ) : 0 ≤ famI r d := by
  unfold famI
  split_ifs
  · have hH : (0 : ℝ) < hStar := by norm_num [hStar]
    positivity
  · exact le_rfl

theorem aEta_nonneg (j : ℕ) (hj : j ≤ 8) : 0 ≤ aEta j := by
  have h := eta_ge (n := j + 2) (by omega) (by omega)
  have h' : ((eta0 : ℚ) : ℝ) ≤ ((etaQ (j + 2) : ℚ) : ℝ) := by exact_mod_cast h
  have h0 : (0 : ℝ) ≤ (eta0 : ℝ) := by norm_num [eta0]
  unfold aEta
  linarith

theorem aZeta_nonneg (j : ℕ) (hj : j ≤ 8) : 0 ≤ aZeta j := by
  have h := zeta_ge (n := j + 1) (by omega) (by omega)
  have h' : ((zeta0 : ℚ) : ℝ) ≤ ((zetaQ (j + 1) : ℚ) : ℝ) := by exact_mod_cast h
  have h0 : (0 : ℝ) ≤ (zeta0 : ℝ) := by norm_num [zeta0]
  unfold aZeta
  linarith

theorem aRho_nonneg (j : ℕ) : 0 ≤ aRho j := by
  have h : (0 : ℝ) ≤ (rhoQ : ℝ) := by norm_num [rhoQ, ratioR]
  unfold aRho
  positivity

/-- **The paper's middle mean coefficient is nonnegative** (`prop:joint-middle-mean`, families
(i)–(iv)): every coefficient of `mPaper r` is a nonnegative constant times a power of `r ≥ 0`
(`η_n ≥ 211/80`, `ζ_n ≥ 9/4` by `eta_ge`, `zeta_ge`). -/
theorem mPaper_nonneg (r : ℝ) (hr : 0 ≤ r) (d : MLetter → ℕ) : 0 ≤ mPaper r d := by
  have hσ : (0 : ℝ) ≤ (sigmaQ : ℝ) := by norm_num [sigmaQ]
  have he0 : (0 : ℝ) ≤ (eta0 : ℝ) := by norm_num [eta0]
  have hz0 : (0 : ℝ) ≤ (zeta0 : ℝ) := by norm_num [zeta0]
  have hZ : ∀ n : ℕ, ∀ j ≤ 8, 0 ≤ (sigmaQ : ℝ) ^ n * aZeta j := fun n j hj =>
    mul_nonneg (pow_nonneg hσ n) (aZeta_nonneg j hj)
  have hR : ∀ n : ℕ, ∀ j ≤ 10, 0 ≤ (sigmaQ : ℝ) ^ n * aRho j := fun n j _ =>
    mul_nonneg (pow_nonneg hσ n) (aRho_nonneg j)
  unfold mPaper
  have h1 := famI_nonneg r hr d
  have h2 := famCoef_nonneg 0 0 2 0 aEta (eta0 : ℝ) 8 d aEta_nonneg he0
  have h3 := famCoef_nonneg 1 0 1 0 (fun j => (sigmaQ : ℝ) * aZeta j) ((sigmaQ : ℝ) * zeta0) 8 d
    (fun j hj => by simpa using hZ 1 j hj) (mul_nonneg hσ hz0)
  have h4 := famCoef_nonneg 3 0 1 0 (fun j => (sigmaQ : ℝ) ^ 3 * aZeta j)
    ((sigmaQ : ℝ) ^ 3 * zeta0) 8 d (hZ 3) (mul_nonneg (pow_nonneg hσ 3) hz0)
  have h5 := famCoef_nonneg 5 0 1 0 (fun j => (sigmaQ : ℝ) ^ 5 * aZeta j)
    ((sigmaQ : ℝ) ^ 5 * zeta0) 8 d (hZ 5) (mul_nonneg (pow_nonneg hσ 5) hz0)
  have h6 := famCoef_nonneg 2 0 0 0 (fun j => (sigmaQ : ℝ) ^ 2 * aRho j) ((sigmaQ : ℝ) ^ 2 * 1)
    10 d (hR 2) (by positivity)
  have h7 := famCoef_nonneg 4 0 0 0 (fun j => (sigmaQ : ℝ) ^ 4 * aRho j) ((sigmaQ : ℝ) ^ 4 * 1)
    10 d (hR 4) (by positivity)
  have h8 := famCoef_nonneg 6 0 0 0 (fun j => (sigmaQ : ℝ) ^ 6 * aRho j) ((sigmaQ : ℝ) ^ 6 * 1)
    10 d (hR 6) (by positivity)
  linarith

/-- **`mLift ≥ 0`**, hence ND's residual gates `63 c − mLift ≥ 0` give `c ≥ 0`. -/
theorem mLift_nonneg {C : Type} [Fintype C] (d : MLetter ⊕ C → ℕ) : 0 ≤ mLift d := by
  have hr : 0 ≤ rH := by unfold rH; norm_num [rhoHq]
  unfold mLift
  split_ifs
  · exact mPaper_nonneg rH hr _
  · exact le_rfl

end MLift

namespace CompanionObligationsCG

open Sarkozy.CompanionND (CompanionObligationsND)

variable {hW : Target.Weil} {hMR : Target.MovingRoot} {hFour : Target.FourCycle}
  {hB : Target.BMOR} {hRR : Target.ThetaSmallRR} {UpT : UpperRecordTables}

/-- **The CG obligations from the ND obligations** at `τ ≤ 13/625 = 0.0208`: the
same front, classes, labels, letters, comparison coefficient, totals, series, residuals and
(E1)/`SF` data; the weights rescaled to `1/2` (`wcHalf`, `vvHalf`); `ops`, `hup` transported
(`opsHalf`, `selUpperHalf`); `hm₁` from `hm` (`selMean_zero`). -/
noncomputable def ofND (O : CompanionObligationsND hW hMR hFour hB hRR UpT)
    (hτ : O.τ ≤ 13 / 625) :
    CompanionObligationsCG hW hMR hFour hB hRR UpT where
  F := O.F
  cd := O.cd
  K := O.K
  Lt := O.Lt
  labS := O.labS
  labK := O.labK
  Zs := O.Zs
  wc := wcHalf O.labK O.μK O.wc
  ρ := O.ρ
  r := O.r
  Vv := vvHalf O.labK O.μK O.Vv
  ℓ := O.ℓ
  c := O.c
  X := O.X
  Cv := O.Cv
  τ := O.τ
  εE := O.εE
  cE := O.cE
  r0 := O.r0
  rE := O.rE
  sf := O.sf
  c₂ := O.c₂
  wc_nonneg L i k := mul_nonneg (O.wc_nonneg L i k)
    (mul_nonneg zero_le_two (wtOf_nonneg O.labK O.hμ0 k))
  hwHalf := weightsHalf_of_paper O.labK O.μK O.hμ0 O.hnz O.wc O.hwPaper
  hVv := vvHalf_nonneg O.labK O.μK O.hμ0 O.Vv O.hVv
  hvV := priceBoundHalf_of_paper O.labS O.labK O.μK O.hμ0 O.hnz O.Vv O.hVv O.hvV
  hZs := O.hZs
  hX0 := O.hX0
  hc0 d := by
    have h1 := O.hres d
    have h2 := mLift_nonneg (C := O.Lt) d
    linarith
  hτ := hτ
  hεE0 := O.hεE0
  hεEt := O.hεEt
  hcE := O.hcE
  hrE0 := O.hrE0
  hr00 := O.hr00
  hεS0 := O.hεS0
  hεSt := O.hεSt
  hcS := O.hcS
  hrpm0 := O.hrpm0
  hc₂ := O.hc₂
  hC := O.hC
  hCv := O.hCv
  hup := selUpperHalf O.labS O.labK O.μK O.Zs O.wc O.hup
  hsub := O.hsub
  hfold := O.hfold
  ops := opsHalf O.labS O.labK O.μK O.Zs O.wc O.ρ O.ops
  hm₁ := selMean_zero _ (fun L ω => by
    rcases O.labS L ω with _ | k
    · exact le_rfl
    · exact O.hμ0 k) O.Zs O.hZs O.hm
  hρ := O.hρ
  hcomp := O.hcomp
  hX := O.hX
  hcoup := O.hcoup
  hremE := O.hremE
  hremS := O.hremS
  fixL := O.fixL
  fixR := O.fixR
  envL := O.envL
  envR := O.envR

end CompanionObligationsCG

/-- **`main_goal_rebased_cg` covers ND's obligations at `τ ≤ 13/625 = 0.0208`**
(non-vacuity). -/
theorem main_goal_of_nd (hWeil : Target.Weil) (hBMOR : Target.BMOR)
    (hMovingRoot : Target.MovingRoot)
    (hFourCycle : Target.FourCycle) (hThetaSmallRR : Target.ThetaSmallRR)
    (UpT : UpperRecordTables)
    (O : CompanionND.CompanionObligationsND hWeil hMovingRoot hFourCycle hBMOR hThetaSmallRR UpT)
    (hτ : O.τ ≤ 13 / 625) :
    Target.SarkozyBound TargetGoal.epsGoal :=
  main_goal_rebased_cg hWeil hBMOR hMovingRoot hFourCycle hThetaSmallRR UpT
    (CompanionObligationsCG.ofND O hτ)

/-- **The numerical fields of CG hold together** (`c = 0`, `X = 0`, `C_v = 0`, `τ = 0`). Their
content is joint with `hcomp`, which forces `c ≥ B` on the degrees of the selections in no class. -/
theorem numerics_satisfiable_cg (Λ : Type) [Fintype Λ] :
    ∃ (c : (Λ → ℕ) → ℝ) (X : Λ → ℝ) (Cv τ : ℝ), (∀ d, 0 ≤ c d) ∧ (∀ l, 0 ≤ X l) ∧
      τ ≤ 13 / 625 ∧ HasSum (fun d => c d * ∏ l, X l ^ d l / (d l).factorial) Cv ∧
      Cv ≤ harnessE + τ := by
  refine ⟨fun _ => 0, fun _ => 0, 0, 0, fun _ => le_rfl, fun _ => le_rfl, by norm_num, ?_, ?_⟩
  · simp only [zero_mul]
    exact hasSum_zero
  · have : (0 : ℝ) ≤ harnessE := by unfold harnessE; norm_num
    linarith

end Sarkozy.ClassSlack
