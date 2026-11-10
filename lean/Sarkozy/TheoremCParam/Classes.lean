module

public import Sarkozy.TheoremC.Classes
public import Sarkozy.TheoremCParam.Main

@[expose] public section



open Filter Finset Function
open scoped Topology BigOperators Matrix

namespace Sarkozy.TheoremCParam

open Sarkozy.TheoremC
open Sarkozy.Param (Params)

variable {a : ℝ}

open Sarkozy.FourierArithmetic Sarkozy.Functional Sarkozy.IndexSupport Sarkozy.Comparison
  Sarkozy.PaperFrame Sarkozy.RecordExpansion Sarkozy.RecordExpansion.Choice

attribute [local instance] ClassBounds.ιFintype ClassBounds.ιDecEq ClassBounds.JauxFintype
  ClassBounds.JauxDecEq

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]

namespace ClassBounds

variable {S₀ : ℝ} {pp ep : J₀ → ℕ} {E : Type} {Q : Queries E} {R : Reference m₀}
  {FS : FirstStage a m₀ p S₀ R} {CL : ComparisonLaw a m₀ p S₀ pp ep Q FS}
  (CB : ClassBounds a m₀ p CL)

/-- The class bound `φ_ω = ∑_m coeff(ω, m) ∏_{𝔟} y_{𝔟, m_𝔟}` of a selection (`def:cp5`):
a polynomial with nonnegative coefficients in the auxiliary prices, each of whose
monomials takes one auxiliary price at each atom of `ω` (`coeff_support`). -/
noncomputable def phi (L : ℕ) (ω : Choice (CL.T L)) : ℝ :=
  ∑ m, CB.coeff L ω m * ∏ b, (m b).elim 1 (CB.y L b)

/-- The robust class bounds of (CP5) with nonnegative remainders (`def:robust`: the
remainders are absolute values). -/
def RobustNonneg : Prop :=
  ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∃ c : ℝ, 0 ≤ c ∧
    ∃ r : ∀ L, Finset ℤ → Choice (CL.T L) → ℝ, (∀ L A ω, 0 ≤ r L A ω) ∧
    Param.AtCounterexamples (Params.ofDecay a) (energyFirst (R.law p) (atomLift m₀ p)) fun L A =>
      (∀ i, ∑ ω ∈ (univ.filter fun ω : Choice (CL.T L) => IsSelection ω).filter
          (fun ω => CB.cls L ω = some i), |term (FS.lam L) (CL.ζ L) (atomLift m₀ p L A) ω| ≤
        ∑ ω ∈ (univ.filter fun ω : Choice (CL.T L) => IsSelection ω).filter
            (fun ω => CB.cls L ω = some i),
          ((CB.phi L ω + ε L * monomial (CL.π L) ω) *
              energyFirst (R.law p) (atomLift m₀ p) L A + r L A ω)) ∧
      ∑ ω ∈ univ.filter (fun ω : Choice (CL.T L) => IsSelection ω), r L A ω ≤ remainder c L A

/-- `RobustNonneg` is the robust bound of (CP5) with nonnegative remainders. -/
theorem RobustNonneg.robust {CB : ClassBounds a m₀ p CL} (h : CB.RobustNonneg) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∃ c : ℝ, 0 ≤ c ∧
      ∃ r : ∀ L, Finset ℤ → Choice (CL.T L) → ℝ,
      Param.AtCounterexamples (Params.ofDecay a) (energyFirst (R.law p) (atomLift m₀ p)) fun L A =>
        (∀ i, ∑ ω ∈ (univ.filter fun ω : Choice (CL.T L) => IsSelection ω).filter
            (fun ω => CB.cls L ω = some i), |term (FS.lam L) (CL.ζ L) (atomLift m₀ p L A) ω| ≤
          ∑ ω ∈ (univ.filter fun ω : Choice (CL.T L) => IsSelection ω).filter
              (fun ω => CB.cls L ω = some i),
            ((CB.phi L ω + ε L * monomial (CL.π L) ω) *
                energyFirst (R.law p) (atomLift m₀ p) L A + r L A ω)) ∧
        ∑ ω ∈ univ.filter (fun ω : Choice (CL.T L) => IsSelection ω), r L A ω ≤
          remainder c L A := by
  obtain ⟨ε, hε, c, hc, r, -, hb⟩ := h
  exact ⟨ε, hε, c, hc, r, hb⟩

end ClassBounds

namespace ComparisonData

variable {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E] (D : ComparisonData a m₀ p pr h E)

/-- `EnvelopeBound` with nonnegative remainders (`def:robust`: the remainders, the
large-union terms of `lem:record:density-lp`, are absolute values). -/
def EnvelopeBoundNonneg : Prop :=
  ∃ εE : ℕ → ℝ, (∀ L, 0 ≤ εE L) ∧ Tendsto εE atTop (𝓝 0) ∧ ∃ cE : ℝ, 0 ≤ cE ∧
    ∃ rE : ∀ L, Finset ℤ → Choice (D.CL.T L) → ℝ, (∀ L A ω, 0 ≤ rE L A ω) ∧
      Param.AtCounterexamples (Params.ofDecay a) D.Y
          (fun L A => ∀ ω : Choice (D.CL.T L), IsSelection ω →
        diagonalIntegral (envelopeLaw (D.GB.N L) (D.CL.D L) ω) (atomLift m₀ p L A) ≤
          (D.B + εE L) * (∏ b ∈ Choice.support ω, selectionFactor a p D.S.selPre L b) *
            D.Y L A + rE L A ω) ∧
      Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
        ∑ ω ∈ univ.filter (fun ω : Choice (D.CL.T L) => IsSelection ω),
          monomial (D.CL.πt L) ω * rE L A ω ≤ remainder cE L A)

omit [DecidableEq P] in
theorem EnvelopeBoundNonneg.envelopeBound {D : ComparisonData a m₀ p pr h E}
    (hE : D.EnvelopeBoundNonneg) : D.EnvelopeBound := by
  obtain ⟨εE, hεE0, hεE, cE, hcE, rE, -, h1, h2⟩ := hE
  exact ⟨εE, hεE0, hεE, cE, hcE, rE, h1, h2⟩

omit [DecidableEq P] in
/-- The bound `b_ω` of `lem:record:record-expansion` (ii) (`classBound`) as an `if`. -/
theorem classBound_eq_ite (CB : ClassBounds a m₀ p D.CL) (L : ℕ) (ω : Choice (D.CL.T L)) :
    classBound (CB.cls L) (CB.phi L) D.B (D.CL.π L) ω =
      if CB.cls L ω = none then D.B * monomial (D.CL.π L) ω else CB.phi L ω := by
  unfold classBound
  cases CB.cls L ω <;> simp

omit [DecidableEq P] in
/-- **Hypothesis (i) of `thm:record:criterion` with the class bounds of (CP5)**
(`lem:record:record-expansion` (ii), evaluated form): `|Y_ν − Y_λ| ≤ (𝓔 + o(1)) Y`, where
`𝓔` bounds `∑_ω b_ω` at every scale (`hΨ`; `b_ω = B π_ω` for a selection in no class and
the class bound `φ_ω` for a selection of a class). The selections in no class are bounded
through the brackets of (CP3), (CP4)(b) and the envelope bound (E1)
(`EnvelopeBoundNonneg`), those of the classes by the robust class bounds of (CP5)
(`ClassBounds.RobustNonneg`). -/
theorem comparison_estimate_classes (CB : ClassBounds a m₀ p D.CL) {𝓔 : ℝ}
    (hΨ : ∀ L, ∑ ω ∈ univ.filter (fun ω : Choice (D.CL.T L) => IsSelection ω),
      (if CB.cls L ω = none then D.B * monomial (D.CL.π L) ω else CB.phi L ω) ≤ 𝓔)
    (hE1 : D.EnvelopeBoundNonneg) (hCB : CB.RobustNonneg) :
    ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∃ c : ℝ, 0 ≤ c ∧
      Param.AtCounterexamples (Params.ofDecay a) D.Y fun L A =>
        |energyComparison D.CL.ν (atomLift m₀ p) L A - energyFirst D.FS.lam (atomLift m₀ p) L A| ≤
          (𝓔 + ε L) * D.Y L A + remainder c L A := by
  obtain ⟨εE, hεE0, hεE, cE, hcE, rE, hrE0, hE1a, hE1b⟩ := hE1
  obtain ⟨ε, hε, c, hc, r, hr0, hcb⟩ := hCB
  set X : ℝ := Real.exp D.CL.S * Real.cosh D.CL.A - 1 with hX
  refine ⟨fun L => (εE L + |ε L|) * X, ?_, cE + c, add_nonneg hcE hc, ?_⟩
  · have h := (hεE.add hε.abs).mul_const X
    simpa only [abs_zero, add_zero, zero_mul] using h
  filter_upwards [hE1a, hE1b, hcb] with L h1 h2 h3
  intro C hC hind A hA hcount
  have hE := h1 C hC hind A hA hcount
  have hrsum := h2 C hC hind A hA hcount
  obtain ⟨hcls, hrcls⟩ := h3 C hC hind A hA hcount
  have hY : 0 < D.Y L A := counterexample_pos hC hcount
  set z : ℝ := εE L + |ε L| with hz
  have hz0 : 0 ≤ z := add_nonneg (hεE0 L) (abs_nonneg _)
  have hπ : ∀ b t e, 0 ≤ D.CL.π L b t e := fun b t e =>
    mul_nonneg (D.CL.πt_nonneg L b t e) (D.selectionFactor_nonneg L b)
  -- the combined remainders
  set rc : Choice (D.CL.T L) → ℝ := fun ω =>
    if CB.cls L ω = none then monomial (D.CL.πt L) ω * rE L A ω else r L A ω with hrc
  -- selections in no class
  have hfree : ∀ ω : Choice (D.CL.T L), IsSelection ω → CB.cls L ω = none →
      |term (D.FS.lam L) (D.CL.ζ L) (atomLift m₀ p L A) ω| ≤
        (D.B + z) * monomial (D.CL.π L) ω * D.Y L A + rc ω := by
    intro ω hω hnone
    have h1' : |term (D.FS.lam L) (D.CL.ζ L) (atomLift m₀ p L A) ω| ≤
        monomial (D.CL.πt L) ω *
          diagonalIntegral (envelopeLaw (D.GB.N L) (D.CL.D L) ω) (atomLift m₀ p L A) :=
      abs_term_le_envelope (c := reservedCut) (N := D.GB.N L) (D := D.CL.D L)
        (D.GB.bracket L) (D.CL.bracket L) (atomLift m₀ p L A) ω
    have hm : 0 ≤ monomial (D.CL.πt L) ω := monomial_nonneg (D.CL.πt_nonneg L) ω
    have h2' := mul_le_mul_of_nonneg_left (hE ω hω) hm
    have hmono : monomial (D.CL.π L) ω =
        monomial (D.CL.πt L) ω * ∏ b ∈ Choice.support ω, selectionFactor a p D.S.selPre L b :=
      monomial_mul_selectionFactor _ _ ω
    have hπω : 0 ≤ monomial (D.CL.π L) ω := monomial_nonneg hπ ω
    have hrcω : rc ω = monomial (D.CL.πt L) ω * rE L A ω := by
      simp only [hrc, hnone, ite_true]
    have hzE : (D.B + εE L) * monomial (D.CL.π L) ω * D.Y L A ≤
        (D.B + z) * monomial (D.CL.π L) ω * D.Y L A := by
      apply mul_le_mul_of_nonneg_right _ hY.le
      apply mul_le_mul_of_nonneg_right _ hπω
      linarith [abs_nonneg (ε L)]
    rw [hrcω]
    calc |term (D.FS.lam L) (D.CL.ζ L) (atomLift m₀ p L A) ω|
        ≤ monomial (D.CL.πt L) ω *
            diagonalIntegral (envelopeLaw (D.GB.N L) (D.CL.D L) ω) (atomLift m₀ p L A) := h1'
      _ ≤ monomial (D.CL.πt L) ω * ((D.B + εE L) *
            (∏ b ∈ Choice.support ω, selectionFactor a p D.S.selPre L b) * D.Y L A +
              rE L A ω) := h2'
      _ = (D.B + εE L) * monomial (D.CL.π L) ω * D.Y L A +
            monomial (D.CL.πt L) ω * rE L A ω := by rw [hmono]; ring
      _ ≤ (D.B + z) * monomial (D.CL.π L) ω * D.Y L A +
            monomial (D.CL.πt L) ω * rE L A ω := by linarith
  -- the classes
  have hclass : ∀ i, ∑ ω ∈ (univ.filter fun ω : Choice (D.CL.T L) => IsSelection ω).filter
        (fun ω => CB.cls L ω = some i), |term (D.FS.lam L) (D.CL.ζ L) (atomLift m₀ p L A) ω| ≤
      ∑ ω ∈ (univ.filter fun ω : Choice (D.CL.T L) => IsSelection ω).filter
          (fun ω => CB.cls L ω = some i),
        ((CB.phi L ω + z * monomial (D.CL.π L) ω) * D.Y L A + rc ω) := by
    intro i
    refine (hcls i).trans (sum_le_sum fun ω hω => ?_)
    have hsome : CB.cls L ω = some i := (mem_filter.mp hω).2
    have hrcω : rc ω = r L A ω := by
      simp only [hrc, hsome, reduceCtorEq, ite_false]
    have hπω : 0 ≤ monomial (D.CL.π L) ω := monomial_nonneg hπ ω
    have hεz : ε L ≤ z := by linarith [le_abs_self (ε L), hεE0 L]
    have : ε L * monomial (D.CL.π L) ω * D.Y L A ≤ z * monomial (D.CL.π L) ω * D.Y L A :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hεz hπω) hY.le
    rw [hrcω]
    nlinarith
  have hsum := sum_abs_le_of_classes (CB.cls L)
    (fun ω => term (D.FS.lam L) (D.CL.ζ L) (atomLift m₀ p L A) ω) (CB.phi L)
    (π := D.CL.π L) (Bf := D.B) (z := z) (Y := D.Y L A) rc hfree hclass
  -- the evaluated complete polynomial
  have hΨL : ∑ ω ∈ univ.filter (fun ω : Choice (D.CL.T L) => IsSelection ω),
      classBound (CB.cls L) (CB.phi L) D.B (D.CL.π L) ω ≤ 𝓔 := by
    refine le_of_eq_of_le (sum_congr rfl fun ω _ => ?_) (hΨ L)
    exact D.classBound_eq_ite CB L ω
  have hmain := abs_energy_sub_le_of_complete reservedCut (D.nu_eq L) (D.GB.lam_sym L)
    (fun b t => isSymmetricAt_symPart _ _) (fun b t => isSkewAt_skewPart _ _)
    (atomLift m₀ p L A) hπ hz0 hY.le (classBound (CB.cls L) (CB.phi L) D.B (D.CL.π L)) rc
    hsum hΨL
  -- the totals and the remainders
  have hS : ∑ b, symTotal (D.CL.π L) b ≤ D.CL.S := D.CL.S_total L
  have hA' : ∑ b, skewTotal (D.CL.π L) b ≤ D.CL.A := D.CL.A_total L
  have hA0 : 0 ≤ ∑ b, skewTotal (D.CL.π L) b :=
    sum_nonneg fun b _ => sum_nonneg fun t _ => hπ b t _
  have hmono := exp_mul_cosh_le_of_le hS hA0 hA'
  have hstep : z * (Real.exp (∑ b, symTotal (D.CL.π L) b) *
      Real.cosh (∑ b, skewTotal (D.CL.π L) b) - 1) * D.Y L A ≤ z * X * D.Y L A := by
    apply mul_le_mul_of_nonneg_right _ hY.le
    apply mul_le_mul_of_nonneg_left _ hz0
    rw [hX]
    linarith
  have hrcle : ∑ ω ∈ univ.filter (fun ω : Choice (D.CL.T L) => IsSelection ω), rc ω ≤
      remainder cE L A + remainder c L A := by
    have hle : ∀ ω ∈ univ.filter (fun ω : Choice (D.CL.T L) => IsSelection ω),
        rc ω ≤ monomial (D.CL.πt L) ω * rE L A ω + r L A ω := by
      intro ω _
      have hm : 0 ≤ monomial (D.CL.πt L) ω * rE L A ω :=
        mul_nonneg (monomial_nonneg (D.CL.πt_nonneg L) ω) (hrE0 L A ω)
      simp only [hrc]
      split_ifs
      · linarith [hr0 L A ω]
      · linarith
    calc ∑ ω ∈ univ.filter (fun ω : Choice (D.CL.T L) => IsSelection ω), rc ω
        ≤ ∑ ω ∈ univ.filter (fun ω : Choice (D.CL.T L) => IsSelection ω),
            (monomial (D.CL.πt L) ω * rE L A ω + r L A ω) := sum_le_sum hle
      _ = ∑ ω ∈ univ.filter (fun ω : Choice (D.CL.T L) => IsSelection ω),
            monomial (D.CL.πt L) ω * rE L A ω +
          ∑ ω ∈ univ.filter (fun ω : Choice (D.CL.T L) => IsSelection ω), r L A ω :=
            sum_add_distrib
      _ ≤ remainder cE L A + remainder c L A := add_le_add hrsum hrcls
  have hnueq : energyComparison D.CL.ν (atomLift m₀ p) L A =
      diagonalIntegral (tensorLaw (D.CL.ν L)) (atomLift m₀ p L A) :=
    Sarkozy.PaperFrame.form_barHalf_eq_diagonal _ _
  have hlameq : energyFirst D.FS.lam (atomLift m₀ p) L A =
      diagonalIntegral (tensorLaw (D.FS.lam L)) (atomLift m₀ p L A) :=
    Sarkozy.PaperFrame.form_barHalf_eq_diagonal _ _
  rw [hnueq, hlameq, remainder_add]
  have hfin : (𝓔 + z * (Real.exp (∑ b, symTotal (D.CL.π L) b) *
      Real.cosh (∑ b, skewTotal (D.CL.π L) b) - 1)) * D.Y L A ≤
      (𝓔 + z * X) * D.Y L A := by nlinarith [hstep]
  linarith [hmain, hfin, hrcle]

/-- **The five robust closing estimates of Theorem C with the class bounds of (CP5)**:
`closingEstimates` of `Sarkozy.TheoremC.Main`, with the comparison bound (i) of
`thm:record:criterion` from `comparison_estimate_classes` (the evaluated complete
polynomial `hΨ` replaces `𝓔 ≥ B(e^S cosh A − 1)`). -/
theorem closingEstimates_classes (hcop : Pairwise (Nat.Coprime on fun q => pr q ^ h q))
    (CB : ClassBounds a m₀ p D.CL) {𝓔 : ℝ}
    (hΨ : ∀ L, ∑ ω ∈ univ.filter (fun ω : Choice (D.CL.T L) => IsSelection ω),
      (if CB.cls L ω = none then D.B * monomial (D.CL.π L) ω else CB.phi L ω) ≤ 𝓔)
    (hE1 : D.EnvelopeBoundNonneg) (hCB : CB.RobustNonneg)
    (hSF : D.SharpFirstTerms) (hcan : D.NonwrappingCancellation hcop)
    (hwr : D.WrappingTerms hcop) (henv : D.EnvelopeEnergies hcop) :
    Nonempty (Param.ClosingEstimates (Params.ofDecay a) D.Y (Fintype.card E) D.L₀ D.Jc D.W
      (jointConstantC (Fintype.card E) 𝓔 D.MC.m)) := by
  obtain ⟨ε₁, hε₁, c₁, hc₁, hcomp⟩ := D.comparison_estimate_classes CB hΨ hE1 hCB
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
  -- joint: (i) with classes and (ii) = (CP7)
  have hjoint := joint_of_comparison_mean (Atom := PaperAtom J) (Xb := AtomLabel m₀ p)
    (D.R.law p) D.FS.lam D.CL.ν D.ME.ML D.ME.MR (atomLift m₀ p) hcomp hmean (Fintype.card E)
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
  have hεj : Tendsto (fun L => ((2 : ℝ) ^ Fintype.card E - 1) * ε₁ L + ε₂ L) atTop (𝓝 0) := by
    simpa only [mul_zero, add_zero] using
      (hε₁.const_mul ((2 : ℝ) ^ Fintype.card E - 1)).add hε₂
  exact ⟨Param.ClosingEstimates.ofConcrete
      (Params.ofDecay a) D.index D.FS.lam D.ME.ML D.CL.ν D.ME.MR
    (fun L A e => atomInput m₀ p pr h hcop L A e) (fun L A e => atomInput m₀ p pr h hcop L A e)
    (atomLift m₀ p) D.ME.bracket (fun L A e y => expect_atomInput m₀ p pr h hcop L A e y)
    (fun L A e y => expect_atomInput m₀ p pr h hcop L A e y)
    (fun L => 3 ^ Fintype.card E * εw L) εenv (fun L => εs L * D.L₀)
    (fun L => ((2 : ℝ) ^ Fintype.card E - 1) * ε₁ L + ε₂ L)
    (4 ^ Fintype.card E * cn + 3 ^ Fintype.card E * cw) cenv cs
    (((2 : ℝ) ^ Fintype.card E - 1) * c₁ + c₂)
    (by simpa only [mul_zero] using hεw.const_mul ((3 : ℝ) ^ Fintype.card E)) hεenv
    (firstStage_error_tendsto _ _ _ hεs) hεj
    (by positivity) hcenv hcs (by nlinarith) hwrap henvL' henvR' hfirst hjoint⟩

/-- **Theorem C** (`thm:comparison`) **with the classes and class bounds of (CP5)**: as
`theoremC`, with `𝓔` bounding the evaluated complete polynomial `∑_ω b_ω` at every scale
(`hΨ`, `rem:cp:monotone`). If `Θ = (1 − 2^{-k})(L₀ + 𝓔) + J + W + (1 − m)/2^k < 1`, then
`PowerSavingBound`. -/
theorem theoremC_classes (hcop : Pairwise (Nat.Coprime on fun q => pr q ^ h q))
    (hP : (Params.ofDecay a).Valid)
    (CB : ClassBounds a m₀ p D.CL) {𝓔 : ℝ}
    (hΨ : ∀ L, ∑ ω ∈ univ.filter (fun ω : Choice (D.CL.T L) => IsSelection ω),
      (if CB.cls L ω = none then D.B * monomial (D.CL.π L) ω else CB.phi L ω) ≤ 𝓔)
    (hΘ : D.Theta 𝓔 < 1) (hE1 : D.EnvelopeBoundNonneg) (hCB : CB.RobustNonneg)
    (hSF : D.SharpFirstTerms) (hcan : D.NonwrappingCancellation hcop)
    (hwr : D.WrappingTerms hcop) (henv : D.EnvelopeEnergies hcop)
    (hunit : ∃ p₀ : ℕ, ∀ (q : ℕ) [NeZero q], q.Prime → p₀ ≤ q → MixedLpBound (D.R.μp q) 36 1) :
    Param.PowerSavingBound (Params.ofDecay a) := by
  obtain ⟨e⟩ := D.closingEstimates_classes hcop CB hΨ hE1 hCB hSF hcan hwr henv
  exact Param.paperMain_powerSavingBound_theta_ref m₀ p hP D.S.p_prime D.S.p_inj D.R.μ₀ D.R.μp
    D.R.unif₀ D.R.rp₀.slot D.R.unifp (fun q _ hq => (D.R.rpp q hq).slot) hunit
    (by rw [D.jointTheta_eq_Theta]; exact hΘ) e

end ComparisonData

end Sarkozy.TheoremCParam
