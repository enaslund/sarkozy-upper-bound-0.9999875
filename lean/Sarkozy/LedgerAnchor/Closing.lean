module

public import Sarkozy.LedgerAnchor.Numerics
public import Sarkozy.Param.All
public import Sarkozy.TheoremCParam.Anchor

@[expose] public section

/-!
# The closing condition at `a₀` from the ledger

The closing hypotheses of the endgame at the formal exponent, discharged from the outward
bounds `AnchorBounds l` on the primitive totals at `a₀` (`Sarkozy.LedgerAnchor.Numerics`), which
come from Part V:

* `sarkozyBound_epsAnchor_of_anchorLedger`, `sarkozyBound_epsAnchor_of_prefixedModel_ledger`:
  the endgame of `Sarkozy.Param.Anchor` with the closing number of the six-query joint closing
  `jointTheta 6 l.L₀ l.J l.W l.jointConstant < 1` supplied by `AnchorBounds.jointTheta_lt_one`;
  the same hypothesis is the `hθ` of `Sarkozy.Param.sarkozyBound_epsAnchor_canonical` (with
  `Lc, Jc, Wc, Hc := l.L₀, l.J, l.W, l.jointConstant`).
* `ComparisonData.Theta_le_of_anchorLedger`, `ComparisonData.Theta_lt_one_of_anchorLedger`: for
  comparison data `D` at `a₀` (`Sarkozy.TheoremCParam`) whose totals are bounded by the ledger,
  `D.Theta 𝓔 ≤ l.theta < 1`, the hypothesis `hΘ` of `theoremC_reduced_anchor` and
  `theoremC_classes_reduced_anchor`.
* `ComparisonData.theoremC_classes_reduced_anchor_of_ledger`: Theorem C with the (CP5) class
  bounds at `a₀`, with the closing condition discharged from the ledger.

**Which form can close.** The ledger's `E = B(e^S cosh A − 1) − D` subtracts the certified
savings `D` (16 class savings `D_{n,m}`, together `0.459227`, and the variance credit
`D_var = 0.009894` at `a₀`). In `theoremC_reduced` the energy constant must satisfy
`𝓔 ≥ Ψ = B(e^S cosh A − 1)`, without savings; with the `a₀` totals that gives `Θ ≈ 1.42`. The
savings enter through the class bounds of `theoremC_classes_reduced` (`hΨ`), so the closing at
`a₀` goes through the classes form (or through the joint-closing endgame of `Sarkozy.Param`).
-/

open Filter Finset Function
open scoped Topology BigOperators Matrix

namespace Sarkozy.LedgerAnchor

open Sarkozy.Comparison (jointTheta PrimitiveLedger)
open Sarkozy.Param (Params)

/-! ## The endgame of `Sarkozy.Param` at `a₀` -/

/-- **The endgame at the formal exponent, closing discharged from the `a₀` ledger.** For any
functional `Y` with the reflection lower bound, the global moment bound and the five robust
closing estimates at the anchor exponents with the ledger's six-query closing data, the outward
ledger bounds at `a₀` give `s(N) ≤ C N^{1−ε′}`. -/
theorem sarkozyBound_epsAnchor_of_anchorLedger
    {Y : ℕ → Finset ℤ → ℝ} {M : ℝ} {l : PrimitiveLedger} (hledger : AnchorBounds l) (hM : 0 < M)
    (hreflection : ∀ L : ℕ, 1 ≤ L → ∀ A : Finset ℤ,
      Admissible (blockScale * L) A → density (blockScale * L) A ^ slots ≤ Y L A)
    (hglobal : Param.GlobalMomentBound Params.anchor Y M)
    (e : Param.ClosingEstimates Params.anchor Y 6 l.L₀ l.J l.W l.jointConstant) :
    Target.SarkozyBound Param.anchorSaving :=
  Param.sarkozyBound_epsAnchor_of_closingEstimates hledger.jointTheta_lt_one hM hreflection
    hglobal e

/-- The endgame at `a₀` for the prefixed residue model, closing discharged from the ledger. -/
theorem sarkozyBound_epsAnchor_of_prefixedModel_ledger
    {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)]
    {p : ∀ L, J L → ℕ} [∀ L j, NeZero (p L j)]
    {X₀ : Type} [AddCommGroup X₀] [Fintype X₀]
    (model : Sarkozy.PrefixedResidueModel p X₀) (ha : model.Arithmetic p X₀)
    (hprefix : 1 ∈ model.prefixSet)
    (hzero : ∀ L : ℕ, 1 ≤ L → ∅ ∈ model.supports L 1)
    (hm : ∀ L : ℕ, 1 ≤ L → HasUniformMarginals (model.law L))
    (hp : ∀ L : ℕ, 1 ≤ L → SlotReflectionPositive (signedIntegral (model.law L).weight))
    {C : ℝ} (hC : 0 < C)
    (hmixed : ∀ L : ℕ, 1 ≤ L → MixedLpBound (model.law L) 36 C)
    {l : PrimitiveLedger} (hledger : AnchorBounds l)
    (e : Param.ClosingEstimates Params.anchor (model.toFourierModel p X₀).energy 6 l.L₀ l.J l.W
      l.jointConstant) :
    Target.SarkozyBound Param.anchorSaving :=
  Param.sarkozyBound_epsAnchor_of_prefixedModel model ha hprefix hzero hm hp hC hmixed
    hledger.jointTheta_lt_one e

/-! ## Theorem C at `a₀` -/

namespace ComparisonData

open Sarkozy.TheoremC Sarkozy.TheoremCParam Sarkozy.RecordExpansion Sarkozy.RecordExpansion.Choice

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]
  (D : TheoremCParam.ComparisonData Params.anchorDecay m₀ p pr h E)

omit [DecidableEq P] in
/-- The two forms of the wrap exponent agree: `2ϑ/72 − 1 = −1 + ϑ/36`. -/
theorem wrapRatio_eq : D.wrapRatio = D.S.index.R_I * PrimitiveLedger.wrapFactor := by
  unfold TheoremCParam.ComparisonData.wrapRatio PrimitiveLedger.wrapFactor
  congr 2
  ring

omit [DecidableEq P] in
/-- **Theorem C's closing number is at most the ledger's closing number**, when the data's
totals are bounded by the ledger: `B`, `L₀`, `T`, `R_I` and `S + A` from above, the energy
constant `𝓔` by the ledger's `E`, and the mean credit `m` from below by `m₁` plus `2^6` times the
joint-closing allocations `Δ_α + Δ_M + Δ_O + Δ_K + Δ_u − R_u` (`cor:joint-closing`). -/
theorem Theta_le_of_anchorLedger {l : PrimitiveLedger} (hcard : Fintype.card E = 6)
    (hB0 : 0 ≤ D.B) (hB : D.B ≤ l.B) (hL₀ : D.L₀ ≤ l.L₀) (hT : D.ME.T ≤ l.T)
    (hR0 : 0 ≤ D.S.index.R_I) (hR : D.S.index.R_I ≤ l.R_I)
    (hSA : D.CL.S + D.CL.A ≤ l.S + l.A) {𝓔 : ℝ} (h𝓔 : 𝓔 ≤ l.E)
    (hm : l.m₁ + 64 * ((l.deltaAlpha + l.deltaMatching + l.deltaOdd + l.deltaEven) +
      l.deltaUpper - l.upperError) ≤ D.MC.m) :
    D.Theta 𝓔 ≤ l.theta := by
  have hw0 := PrimitiveLedger.wrapFactor_pos
  have hJ : D.Jc ≤ l.J := by
    unfold TheoremCParam.ComparisonData.Jc PrimitiveLedger.J
    rw [hcard]
    have hR6 : (D.S.index.R_I / 2) ^ 6 ≤ (l.R_I / 2) ^ 6 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 6
    have h1 : D.B * Real.exp D.ME.T ≤ l.B * Real.exp l.T :=
      mul_le_mul hB (Real.exp_le_exp.mpr hT) (Real.exp_pos _).le (le_trans hB0 hB)
    exact mul_le_mul h1 hR6 (pow_nonneg (by linarith) 6)
      (mul_nonneg (le_trans hB0 hB) (Real.exp_pos _).le)
  have hW : D.W ≤ l.W := by
    unfold TheoremCParam.ComparisonData.W PrimitiveLedger.W wrapNumber
    rw [hcard, wrapRatio_eq]
    have hx : D.S.index.R_I * PrimitiveLedger.wrapFactor / 2 ≤
        l.R_I / 2 * PrimitiveLedger.wrapFactor := by
      have := mul_le_mul_of_nonneg_right hR hw0.le
      linarith
    have hx0 : 0 ≤ D.S.index.R_I * PrimitiveLedger.wrapFactor / 2 :=
      div_nonneg (mul_nonneg hR0 hw0.le) (by norm_num)
    have hpow : (1 + D.S.index.R_I * PrimitiveLedger.wrapFactor / 2) ^ 6 - 1 ≤
        (1 + l.R_I / 2 * PrimitiveLedger.wrapFactor) ^ 6 - 1 :=
      sub_le_sub_right (pow_le_pow_left₀ (by linarith) (by linarith) 6) 1
    have hpow0 : 0 ≤ (1 + D.S.index.R_I * PrimitiveLedger.wrapFactor / 2) ^ 6 - 1 := by
      have := one_le_pow₀ (n := 6)
        (show (1 : ℝ) ≤ 1 + D.S.index.R_I * PrimitiveLedger.wrapFactor / 2 by linarith)
      linarith
    have h1 : D.B * Real.exp (D.CL.S + D.CL.A) ≤ l.B * Real.exp (l.S + l.A) :=
      mul_le_mul hB (Real.exp_le_exp.mpr hSA) (Real.exp_pos _).le (le_trans hB0 hB)
    exact mul_le_mul h1 hpow hpow0 (mul_nonneg (le_trans hB0 hB) (Real.exp_pos _).le)
  unfold TheoremCParam.ComparisonData.Theta PrimitiveLedger.theta
  rw [hcard]
  have hE := h𝓔
  unfold PrimitiveLedger.E at hE
  norm_num
  linarith

omit [DecidableEq P] in
/-- **The closing condition `Θ(𝓔) < 1` of Theorem C at `a₀`, from the ledger**: the hypothesis
`hΘ` of `theoremC_reduced_anchor` and `theoremC_classes_reduced_anchor`. -/
theorem Theta_lt_one_of_anchorLedger {l : PrimitiveLedger} (hl : AnchorBounds l)
    (hcard : Fintype.card E = 6)
    (hB0 : 0 ≤ D.B) (hB : D.B ≤ l.B) (hL₀ : D.L₀ ≤ l.L₀) (hT : D.ME.T ≤ l.T)
    (hR0 : 0 ≤ D.S.index.R_I) (hR : D.S.index.R_I ≤ l.R_I)
    (hSA : D.CL.S + D.CL.A ≤ l.S + l.A) {𝓔 : ℝ} (h𝓔 : 𝓔 ≤ l.E)
    (hm : l.m₁ + 64 * ((l.deltaAlpha + l.deltaMatching + l.deltaOdd + l.deltaEven) +
      l.deltaUpper - l.upperError) ≤ D.MC.m) :
    D.Theta 𝓔 < 1 :=
  (Theta_le_of_anchorLedger D hcard hB0 hB hL₀ hT hR0 hR hSA h𝓔 hm).trans_lt
    hl.theta_lt_one

variable (hcop : Pairwise (Nat.Coprime on fun q => pr q ^ h q))

/-- **Theorem C with the (CP5) class bounds at the formal exponent, closing discharged from
the `a₀` ledger** (`thm:comparison` in the form used by `thm:density:induction`, at `a = a₀`).
The hypotheses are those of `theoremC_classes_reduced_anchor` with `hΘ` replaced by the ledger
bounds `AnchorBounds l` (Part V) and the comparison of the data's totals with the ledger. -/
theorem theoremC_classes_reduced_anchor_of_ledger {l : PrimitiveLedger} (hl : AnchorBounds l)
    (hcard : Fintype.card E = 6)
    (hB0 : 0 ≤ D.B) (hB : D.B ≤ l.B) (hL₀ : D.L₀ ≤ l.L₀) (hT : D.ME.T ≤ l.T)
    (hR0 : 0 ≤ D.S.index.R_I) (hR : D.S.index.R_I ≤ l.R_I)
    (hSA : D.CL.S + D.CL.A ≤ l.S + l.A)
    (hm : l.m₁ + 64 * ((l.deltaAlpha + l.deltaMatching + l.deltaOdd + l.deltaEven) +
      l.deltaUpper - l.upperError) ≤ D.MC.m)
    (CB : TheoremCParam.ClassBounds Params.anchorDecay m₀ p D.CL) {𝓔 : ℝ} (h𝓔 : 𝓔 ≤ l.E)
    (hΨ : ∀ L, ∑ ω ∈ univ.filter (fun ω : Choice (D.CL.T L) => IsSelection ω),
      (if CB.cls L ω = none then D.B * monomial (D.CL.π L) ω else CB.phi L ω) ≤ 𝓔)
    (hE1 : D.EnvelopeBoundNonneg) (hCB : CB.RobustNonneg)
    (hSF : D.SharpFirstTerms) (hDC : DensityCancellation m₀ p pr h D.R.P5 D.S.pp D.S.ep)
    (hfix : D.FixedIntervalEnvelopeEnergies hcop) (henv : D.EnvelopeEnergies hcop)
    (hunit : ∃ p₀ : ℕ, ∀ (q : ℕ) [NeZero q], q.Prime → p₀ ≤ q → MixedLpBound (D.R.μp q) 36 1) :
    Target.SarkozyBound Param.anchorSaving :=
  D.theoremC_classes_reduced_anchor hcop CB hΨ
    (Theta_lt_one_of_anchorLedger D hl hcard hB0 hB hL₀ hT hR0 hR hSA h𝓔 hm) hE1 hCB hSF hDC
    hfix henv hunit

end ComparisonData

end Sarkozy.LedgerAnchor
