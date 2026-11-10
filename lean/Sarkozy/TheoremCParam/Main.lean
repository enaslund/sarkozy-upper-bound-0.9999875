module

public import Sarkozy.TheoremC.Main
public import Sarkozy.TheoremCParam.Data
public import Sarkozy.TheoremCParam.RecordComparison

@[expose] public section



open Filter Finset Function
open scoped Topology BigOperators Matrix

namespace Sarkozy.TheoremCParam

open Sarkozy.TheoremC
open Sarkozy.Param (Params)

variable {a : ℝ}

open Sarkozy.FourierArithmetic Sarkozy.Functional Sarkozy.IndexSupport Sarkozy.Comparison
  Sarkozy.PaperFrame Sarkozy.RecordExpansion Sarkozy.RecordExpansion.Choice

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] (m₀ : J₀ → ℕ) [∀ i, NeZero (m₀ i)]
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] (p : ∀ L, J L → ℕ)
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] (pr h : P → ℕ) [∀ q, NeZero (pr q ^ h q)]
  (E : Type) [Fintype E] [DecidableEq E]

variable (a) in
/-- **Comparison data** (`thm:comparison`): the standing data (CP0) and laws satisfying
(CP1)–(CP4) and (CP6)–(CP8). -/
structure ComparisonData where
  S : StandingData m₀ p pr h E
  R : Reference m₀
  FS : FirstStage a m₀ p S.selPre R
  GB : GramBracket a m₀ p S.selPre FS
  CL : ComparisonLaw a m₀ p S.selPre S.pp S.ep S.Q FS
  ME : MatchingEnvelopes a m₀ p GB CL
  MC : MeanCredit a m₀ p ME
  SM : Summability a m₀ p ME

namespace ComparisonData

variable {m₀ p pr h E} (D : ComparisonData a m₀ p pr h E)

/-! ## The closing number -/

/-- The reference energy `Y = Y_μ = 𝒴(L, A)` (`energyFirst_refLaws`). -/
noncomputable abbrev Y : ℕ → Finset ℤ → ℝ := energyFirst (D.R.law p) (atomLift m₀ p)

/-- The cost `L₀ = e^P 𝔗(d, v)` of the first stage (CP2). -/
noncomputable abbrev L₀ : ℝ := D.FS.L₀

/-- The energy factor `B = e^{U₀} + R_err` of the bracket (CP3). -/
noncomputable abbrev B : ℝ := D.GB.B

/-- The coupled index term `J = B e^T (R_I/2)^k`. -/
noncomputable def Jc : ℝ := D.B * Real.exp D.ME.T * (D.S.index.R_I / 2) ^ Fintype.card E

/-- The ratio `R_I K^{2θ/d − 1}` of the wrapping terms (`d = 72`). -/
noncomputable def wrapRatio : ℝ :=
  D.S.index.R_I * (blockScale : ℝ) ^ (2 * densityExponent / 72 - 1)

/-- The wrapping term `W = B e^{S+A}[(1 + R_I/(2K^{1−2θ/d}))^k − 1]`. -/
noncomputable def W : ℝ := wrapNumber D.B (D.CL.S + D.CL.A) D.wrapRatio (Fintype.card E)

/-- The complete polynomial without (CP5) families at the totals: `Ψ = B(e^S cosh A − 1)`. -/
noncomputable def Ψ : ℝ := D.B * (Real.exp D.CL.S * Real.cosh D.CL.A - 1)

/-- **The closing number of Theorem C**,
`Θ = (1 − 2^{-k})(L₀ + 𝓔) + J + W + (1 − m)/2^k`. -/
noncomputable def Theta (𝓔 : ℝ) : ℝ :=
  (1 - ((2 : ℝ) ^ Fintype.card E)⁻¹) * (D.L₀ + 𝓔) + D.Jc + D.W +
    (1 - D.MC.m) / 2 ^ Fintype.card E

omit [DecidableEq P] in
theorem jointTheta_eq_Theta (𝓔 : ℝ) :
    jointTheta (Fintype.card E) D.L₀ D.Jc D.W (jointConstantC (Fintype.card E) 𝓔 D.MC.m) =
      D.Theta 𝓔 :=
  jointTheta_jointConstantC _ _ _ _ _ _

omit [DecidableEq P] in
theorem two_pow_mul_Jc :
    (2 : ℝ) ^ Fintype.card E * D.Jc =
      D.B * Real.exp D.ME.T * D.S.index.R_I ^ Fintype.card E := by
  unfold Jc
  rw [div_pow]
  field_simp

/-- The coupled index of (CP0)(d) (`paperCoupledIndex`). -/
noncomputable abbrev index :
    CoupledIndex E (fun _ => Option P) (fun _ => CoordSpace blockScale pr h) :=
  paperCoupledIndex pr h D.S.index.μ D.S.index.hμ D.S.index.hμ1 D.S.index.t D.S.index.hnorm
    D.S.Q.u D.S.Q.w D.S.Q.hu D.S.Q.hw

/-! ## The hypotheses that remain (conclusions of Section 10 lemmas) -/

/-- **(E1) for the envelopes of the selections** (`lem:energy-toolkit` (E1) with outside
law `Ñ`, i.e. `lem:bracket-energy` for `κ = ⊗_{𝔟∈X} D^{ε_𝔟}_{𝔟,t_𝔟}`), robustly: at every
least counterexample, every selection `ω` with selected set `X` has
`Y_{(⊗_X D) ⊗ Ñ_{−X}} ≤ (B + o(1)) C_X Y + r_ω`, `C_X = ∏_{𝔟∈X} q_𝔟^{2a}`, where the
remainders `r_ω` (the large selections, `lem:record:density-lp`) add up, with the
weights `π̃_ω`, to a density-linear remainder. -/
def EnvelopeBound : Prop :=
  ∃ εE : ℕ → ℝ, (∀ L, 0 ≤ εE L) ∧ Tendsto εE atTop (𝓝 0) ∧ ∃ cE : ℝ, 0 ≤ cE ∧
    ∃ rE : ∀ L, Finset ℤ → Choice (D.CL.T L) → ℝ,
      Param.AtCounterexamples (Params.ofDecay a) D.Y
          (fun L A => ∀ ω : Choice (D.CL.T L), IsSelection ω →
        diagonalIntegral (envelopeLaw (D.GB.N L) (D.CL.D L) ω) (atomLift m₀ p L A) ≤
          (D.B + εE L) * (∏ b ∈ Choice.support ω, selectionFactor a p D.S.selPre L b) *
            D.Y L A + rE L A ω) ∧
      Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
        ∑ ω ∈ univ.filter (fun ω : Choice (D.CL.T L) => IsSelection ω),
          monomial (D.CL.πt L) ω * rE L A ω ≤ remainder cE L A)

/-- **The terms of the tagged sharp-first expansion** (`lem:sharp-first`, used for Step 2
of `lem:record:first-stage`), robustly: for every nonempty choice `σ` of record
differences and every tag `j` present in `σ`,
`|Y_σ| ≤ (1 + o(1)) Y wt_j(σ) + r_σ` (the folded-energy bound,
`lem:record:folded-energy`, with `prop:record:density-structured` for the two folded
energies), the remainders adding up to a density-linear remainder. -/
def SharpFirstTerms : Prop :=
  ∃ ε : ℕ → ℝ, (∀ L, 0 ≤ ε L) ∧ Tendsto ε atTop (𝓝 0) ∧ ∃ c : ℝ, 0 ≤ c ∧
    ∃ r : ∀ L, Finset ℤ → (∀ b, Option (D.FS.Ib L b)) → ℝ,
      Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A => ∀ σ, σ ≠ (fun _ => none) → ∀ j,
        1 ≤ countVec (D.FS.tag L) σ j →
        |diagonalIntegral (tensorLaw (fun b => (σ b).elim (D.FS.ρ L b)
            (fun i => D.FS.κ' L b i - D.FS.κ L b i))) (atomLift m₀ p L A)| ≤
          (1 + ε L) * D.Y L A *
            tagWeight (D.FS.tag L) (D.FS.dprice L) (D.FS.vprice L) (D.FS.pvar L) j σ +
            r L A σ) ∧
      Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
        ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
          r L A σ ≤ remainder c L A)

variable (hcop : Pairwise (Nat.Coprime on fun q => pr q ^ h q))

/-- **Cancellation of the nonwrapping terms** (`lem:record:wrap-expansion`, nonwrapping
terms): every coupled form `I_{ν,𝒮,𝒲}` with a nonwrapping active query (`𝒲 ⊊ 𝒮`) is a
density-linear remainder. In the paper this is `lem:record:density-can` applied to each
product component of `ν`, with coefficients at most `2^k 𝔳_ν e^{P+S}`. -/
def NonwrappingCancellation : Prop :=
  ∃ cn : ℝ, 0 ≤ cn ∧ Param.AtCounterexamples (Params.ofDecay a) D.Y
      (fun L A => ∀ S W : Finset E, W ⊆ S → W ≠ S →
    |wrapForm m₀ p pr h hcop D.S.index.μ D.S.Q.u D.S.Q.w D.CL.ν L A S W| ≤ remainder cn L A)

/-- **The fully wrapping terms** (`lem:record:wrap-expansion`, wrapping terms):
`|I_{ν,𝒮,𝒮}| ≤ (B e^{S+A} (R_I K^{2θ/d−1})^{|𝒮|} + o(1)) Y`, robustly. In the paper:
`lem:record:common-mean`(b) for the residue coupling with the brackets of (CP3), (CP4)
added up, and `lem:envelope-energy` with `T_Q = S + A` and fixed intervals. -/
def WrappingTerms : Prop :=
  ∃ εw : ℕ → ℝ, (∀ L, 0 ≤ εw L) ∧ Tendsto εw atTop (𝓝 0) ∧ ∃ cw : ℝ, 0 ≤ cw ∧
    Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A => ∀ S : Finset E, S ≠ ∅ →
      |wrapForm m₀ p pr h hcop D.S.index.μ D.S.Q.u D.S.Q.w D.CL.ν L A S S| ≤
        (D.B * Real.exp (D.CL.S + D.CL.A) * D.wrapRatio ^ S.card + εw L) * D.Y L A +
          remainder cw L A)

/-- **The envelope energies** (`lem:envelope-energy` with `𝒮 = ℰ_k`, uniform intervals and
`Q_𝔟 = M_{s,𝔟} − Ñ_𝔟` of (CP6)): `V_L, V_R ≤ (B e^T R_I^k + o(1)) Y`, robustly. -/
def EnvelopeEnergies : Prop :=
  ∃ εenv : ℕ → ℝ, Tendsto εenv atTop (𝓝 0) ∧ ∃ cenv : ℝ, 0 ≤ cenv ∧
    Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
      inclusionEnergyL D.index D.ME.ML (fun L A e => atomInput m₀ p pr h hcop L A e)
          (atomLift m₀ p) L A ≤
        (D.B * Real.exp D.ME.T * D.S.index.R_I ^ Fintype.card E + εenv L) * D.Y L A +
          remainder cenv L A) ∧
    Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
      inclusionEnergyR D.index D.ME.MR (fun L A e => atomInput m₀ p pr h hcop L A e)
          (atomLift m₀ p) L A ≤
        (D.B * Real.exp D.ME.T * D.S.index.R_I ^ Fintype.card E + εenv L) * D.Y L A +
          remainder cenv L A)

/-! ## Auxiliary facts about the data -/

omit [DecidableEq P] in
theorem selectionFactor_nonneg (L : ℕ) (b : PaperAtom J L) :
    0 ≤ selectionFactor a p D.S.selPre L b := by
  cases b with
  | none => exact le_trans zero_le_one D.S.one_le_selPre
  | some j => exact Real.rpow_nonneg (Nat.cast_nonneg _) _

theorem mass_nonneg_of_nonneg {X : Type} [Fintype X] {κ : SlotMeasure X} (hκ : IsNonneg κ) :
    0 ≤ mass κ :=
  hκ _ fun _ => zero_le_one

omit [DecidableEq P] in
theorem law_positive {c : ReflectionCut Slot} (hc : IsFamilyCut c) (L : ℕ) (b : PaperAtom J L) :
    c.Positive (D.R.law p L b) := by
  cases b with
  | none => exact D.R.rp₀ c hc
  | some j => exact D.R.rpp (p L j) (D.S.p_prime L j) c hc

omit [DecidableEq P] in
theorem rho_below (L : ℕ) (b : PaperAtom J L) : D.FS.ϑ₀.Below (D.R.law p L b) (D.FS.ρ L b) := by
  by_cases hb : b ∈ D.FS.fs L
  · exact D.FS.ρ_ge L b hb
  · rw [D.FS.ρ_off L b hb]
    exact below_refl _ _

omit [DecidableEq P] in
theorem dprice_nonneg (L : ℕ) (b : PaperAtom J L) (i : D.FS.Ib L b) : 0 ≤ D.FS.dprice L b i :=
  mul_nonneg (mul_nonneg (mass_nonneg_of_nonneg (D.FS.κ_pos L b i).1) (D.FS.dconst_nonneg L b i))
    (D.selectionFactor_nonneg L b)

omit [DecidableEq P] in
theorem vprice_nonneg (L : ℕ) (b : PaperAtom J L) (i : D.FS.Ib L b) : 0 ≤ D.FS.vprice L b i :=
  mul_nonneg (add_nonneg (mass_nonneg_of_nonneg (D.FS.κ_pos L b i).1)
    (mass_nonneg_of_nonneg (D.FS.κ'_pos L b i).1)) (D.selectionFactor_nonneg L b)

omit [DecidableEq P] in
theorem pvar_nonneg (L : ℕ) (b : PaperAtom J L) : 0 ≤ D.FS.pvar L b :=
  sum_nonneg fun i _ => mul_nonneg (mul_nonneg (abs_nonneg _)
    (mass_nonneg_of_nonneg (D.FS.κa_pos L b i).1)) (D.selectionFactor_nonneg L b)

omit [DecidableEq P] in
theorem dT_nonneg (j : D.FS.Tag) : 0 ≤ D.FS.dT j :=
  le_trans (sum_nonneg fun b _ => sum_nonneg fun i _ => by
    split_ifs
    · exact D.dprice_nonneg 0 b i
    · exact le_refl 0) (D.FS.dT_total 0 j)

omit [DecidableEq P] in
theorem vT_nonneg (j : D.FS.Tag) : 0 ≤ D.FS.vT j :=
  le_trans (sum_nonneg fun b _ => sum_nonneg fun i _ => by
    split_ifs
    · exact D.vprice_nonneg 0 b i
    · exact le_refl 0) (D.FS.vT_total 0 j)

omit [DecidableEq P] in
theorem B_nonneg : 0 ≤ D.B :=
  add_nonneg (Real.exp_pos _).le (mul_nonneg (Real.exp_pos _).le
    (tagSeries_nonneg D.dT_nonneg D.vT_nonneg))

omit [DecidableEq P] in
theorem L₀_nonneg : 0 ≤ D.L₀ := firstStageCost_nonneg _ D.dT_nonneg D.vT_nonneg

omit [DecidableEq P] in
/-- `ν_𝔟 = λ_𝔟 + ∑_t (ζ^s_{𝔟,t} + ζ^a_{𝔟,t})` ((CP4)(b)). -/
theorem nu_eq (L : ℕ) (b : PaperAtom J L) :
    D.CL.ν L b = D.FS.lam L b + ∑ t, (D.CL.ζ L b t .sym + D.CL.ζ L b t .skew) := by
  have h1 := D.CL.change L b
  have h2 : ∀ t, D.CL.ζ L b t .sym + D.CL.ζ L b t .skew = D.CL.Δ L b t := fun t =>
    symPart_add_skewPart reservedCut (D.CL.Δ L b t)
  simp only [h2]
  rw [← h1]
  unfold ComparisonLaw.ν
  abel

/-! ## Theorem C -/

/-- **The five robust closing estimates of Theorem C** (`thm:record:criterion`,
`cor:joint-closing`): from the comparison data, the bound `𝓔 ≥ Ψ = B(e^S cosh A − 1)`
(no (CP5) families) and the five Section 10 inputs still taken as hypotheses, the closing
estimates of `Sarkozy.Comparison.Criterion` hold for the reference energy `Y`, with
`k = |E|`, `L₀`, `J`, `W` as above and joint constant `(1 − 2^{-k})𝓔 + (1 − m)/2^k`. -/
theorem closingEstimates {𝓔 : ℝ} (h𝓔 : D.Ψ ≤ 𝓔) (hE1 : D.EnvelopeBound)
    (hSF : D.SharpFirstTerms) (hcan : D.NonwrappingCancellation hcop)
    (hwr : D.WrappingTerms hcop) (henv : D.EnvelopeEnergies hcop) :
    Nonempty (Param.ClosingEstimates (Params.ofDecay a) D.Y (Fintype.card E) D.L₀ D.Jc D.W
      (jointConstantC (Fintype.card E) 𝓔 D.MC.m)) := by
  obtain ⟨εE, hεE0, hεE, cE, hcE, rE, hE1a, hE1b⟩ := hE1
  obtain ⟨εs, hεs0, hεs, cs, hcs, rs, htermS, hrS⟩ := hSF
  obtain ⟨cn, hcn, hnon⟩ := hcan
  obtain ⟨εw, hεw0, hεw, cw, hcw, hwrapT⟩ := hwr
  obtain ⟨εenv, hεenv, cenv, hcenv, henvL, henvR⟩ := henv
  obtain ⟨ε₂, hε₂, c₂, hc₂, hmean⟩ := D.MC.bound
  -- first stage
  have hfirst := firstStage_estimate (Atom := PaperAtom J) (Xb := AtomLabel m₀ p) D.FS.ϑ₀
    (D.R.law p) D.FS.ρ D.FS.lam (atomLift m₀ p) (fun L b => D.law_positive D.FS.ϑ₀_family L b)
    (fun L b => D.rho_below L b) (fun L b i => D.FS.κ' L b i - D.FS.κ L b i) (fun L b => rfl)
    D.FS.tag D.FS.dprice D.FS.vprice (fun L b i => D.dprice_nonneg L b i)
    (fun L b i => D.vprice_nonneg L b i) D.FS.pvar (fun L b => D.pvar_nonneg L b)
    D.FS.P_total D.FS.dT_total D.FS.vT_total εs hεs0 rs cs htermS hrS
  -- joint
  have hjoint := joint_estimate (Atom := PaperAtom J) (Xb := AtomLabel m₀ p) (D.R.law p)
    D.FS.lam D.GB.N D.CL.ν D.ME.ML D.ME.MR (atomLift m₀ p) D.CL.ζ D.CL.D (fun L b => D.nu_eq L b)
    D.GB.lam_sym (fun L b t => isSymmetricAt_symPart _ _) (fun L b t => isSkewAt_skewPart _ _)
    D.CL.πt D.CL.πt_nonneg D.GB.bracket D.CL.bracket (selectionFactor a p D.S.selPre)
    (fun L b => D.selectionFactor_nonneg L b) D.CL.S_total D.CL.A_total D.B_nonneg h𝓔 εE hεE0
    rE hE1a hE1b hmean (Fintype.card E)
  -- wrap
  have hwrap := wrap_estimate m₀ p pr h hcop D.Y D.S.index.μ D.S.index.hμ D.S.index.hμ1
    D.S.index.t D.S.index.hnorm D.S.Q.u D.S.Q.w D.S.Q.hu D.S.Q.hw D.CL.ν
    (Bf := D.B) (SA := D.CL.S + D.CL.A) (x := D.wrapRatio) εw hεw0 hcn hcw hnon hwrapT
  -- envelopes
  have hJ := D.two_pow_mul_Jc
  have henvL' : Param.AtCounterexamples (Params.ofDecay a) D.Y fun L A =>
      inclusionEnergyL D.index D.ME.ML (fun L A e => atomInput m₀ p pr h hcop L A e)
          (atomLift m₀ p) L A ≤
        (2 ^ Fintype.card E * D.Jc + εenv L) * D.Y L A + remainder cenv L A := by
    rw [hJ]
    exact henvL
  have henvR' : Param.AtCounterexamples (Params.ofDecay a) D.Y fun L A =>
      inclusionEnergyR D.index D.ME.MR (fun L A e => atomInput m₀ p pr h hcop L A e)
          (atomLift m₀ p) L A ≤
        (2 ^ Fintype.card E * D.Jc + εenv L) * D.Y L A + remainder cenv L A := by
    rw [hJ]
    exact henvR
  have hk : (1 : ℝ) ≤ 2 ^ Fintype.card E := one_le_pow₀ (by norm_num)
  exact ⟨Param.ClosingEstimates.ofConcrete
      (Params.ofDecay a) D.index D.FS.lam D.ME.ML D.CL.ν D.ME.MR
    (fun L A e => atomInput m₀ p pr h hcop L A e) (fun L A e => atomInput m₀ p pr h hcop L A e)
    (atomLift m₀ p) D.ME.bracket (fun L A e y => expect_atomInput m₀ p pr h hcop L A e y)
    (fun L A e y => expect_atomInput m₀ p pr h hcop L A e y)
    (fun L => 3 ^ Fintype.card E * εw L) εenv (fun L => εs L * D.L₀)
    (fun L => ((2 : ℝ) ^ Fintype.card E - 1) *
      (εE L * (Real.exp D.CL.S * Real.cosh D.CL.A - 1)) + ε₂ L)
    (4 ^ Fintype.card E * cn + 3 ^ Fintype.card E * cw) cenv cs
    (((2 : ℝ) ^ Fintype.card E - 1) * cE + c₂)
    (by simpa only [mul_zero] using hεw.const_mul ((3 : ℝ) ^ Fintype.card E)) hεenv
    (firstStage_error_tendsto _ _ _ hεs)
    (tendsto_joint_error hεE hε₂ _ _)
    (by positivity) hcenv hcs (by nlinarith) hwrap henvL' henvR' hfirst hjoint⟩

/-- **The recurrence of Theorem C** (`lem:record:rec`(iii)): under the hypotheses of
`closingEstimates`, the raw comparison recurrence holds with a coefficient tending to `Θ`. -/
theorem rawComparison {𝓔 : ℝ} (h𝓔 : D.Ψ ≤ 𝓔) (hE1 : D.EnvelopeBound)
    (hSF : D.SharpFirstTerms) (hcan : D.NonwrappingCancellation hcop)
    (hwr : D.WrappingTerms hcop) (henv : D.EnvelopeEnergies hcop) :
    ∃ (q : ℕ → ℝ) (c : ℝ), 0 ≤ c ∧ Param.RawComparison (Params.ofDecay a) D.Y q c ∧
      Tendsto q atTop (𝓝 (D.Theta 𝓔)) := by
  obtain ⟨e⟩ := D.closingEstimates hcop h𝓔 hE1 hSF hcan hwr henv
  refine ⟨e.coefficient, e.remainderConstant, e.remainderConstant_nonneg, e.rawComparison, ?_⟩
  rw [← D.jointTheta_eq_Theta]
  exact e.coefficient_tendsto

/-- **Theorem C** (`thm:comparison`, closing-criterion form). Let comparison data satisfy
(CP0)–(CP4), (CP6)–(CP8), let `𝓔 ≥ Ψ = B(e^S cosh A − 1)` and
`Θ = (1 − 2^{-k})(L₀ + 𝓔) + J + W + (1 − m)/2^k < 1`. Given the five Section 10 inputs that
are not yet derived (`EnvelopeBound`, `SharpFirstTerms`, `NonwrappingCancellation`,
`WrappingTerms`, `EnvelopeEnergies`) and the unit mixed `L³⁶` bound of the large-prime
reference laws, `s(N) ≤ C N^{1 − ε}` (`PowerSavingBound`). -/
theorem theoremC (hP : (Params.ofDecay a).Valid) {𝓔 : ℝ} (h𝓔 : D.Ψ ≤ 𝓔) (hΘ : D.Theta 𝓔 < 1)
    (hE1 : D.EnvelopeBound)
    (hSF : D.SharpFirstTerms) (hcan : D.NonwrappingCancellation hcop)
    (hwr : D.WrappingTerms hcop) (henv : D.EnvelopeEnergies hcop)
    (hunit : ∃ p₀ : ℕ, ∀ (q : ℕ) [NeZero q], q.Prime → p₀ ≤ q → MixedLpBound (D.R.μp q) 36 1) :
    Param.PowerSavingBound (Params.ofDecay a) := by
  obtain ⟨e⟩ := D.closingEstimates hcop h𝓔 hE1 hSF hcan hwr henv
  exact Param.paperMain_powerSavingBound_theta_ref m₀ p hP D.S.p_prime D.S.p_inj D.R.μ₀ D.R.μp
    D.R.unif₀ D.R.rp₀.slot D.R.unifp (fun q _ hq => (D.R.rpp q hq).slot) hunit
    (by rw [D.jointTheta_eq_Theta]; exact hΘ) e

end ComparisonData

end Sarkozy.TheoremCParam
