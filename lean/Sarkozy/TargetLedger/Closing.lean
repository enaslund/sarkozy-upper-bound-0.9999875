module

public import Sarkozy.TargetLedger.Numerics
public import Sarkozy.TargetLedger.Exponent
public import Sarkozy.TheoremCBlock.MainEnvelope
public import Sarkozy.Param.All

@[expose] public section

/-!
# The closing condition from a ledger, on the block atoms, at a free exponent and at `a_T`

K0's `TheoremCBlock.Ledger` (the `a₀` endgame on the block atoms) at a **free price exponent
`a`**, and its instance at the ledger's exponent `TargetLedger.targetDecay`
(`a_T = 212956239/250000000000` until RG's rebase of 7 November 2026, `a_G = 71/10⁵` since):

* `Theta_le_of_ledger`, `Theta_lt_one_of_ledger`: for comparison data `D` on the block atoms at
  any exponent `a` whose totals are bounded by a ledger `l`, `D.Theta 𝓔 ≤ l.theta`, hence
  `D.Theta 𝓔 < 1` when `l.theta < 1`. The proof is K0's (P1's): the closing number does not see
  `a`, only the totals.
* **`theoremC_classes_reduced_of_ledger`**: `thm:comparison` with the (CP5) class bounds in the
  form used by `thm:density:induction`, at any `a` with `(Params.ofDecay a).Valid` and `0 ≤ a`,
  the closing condition discharged from a ledger with `l.theta < 1`; the conclusion is
  `Target.SarkozyBound (a/(72 − ϑ))`.
* **`theoremC_classes_reduced_target_of_ledger`**: the same at `a = a_T`, with the closing
  condition discharged by the target ledger bounds `TargetBounds l` (`Θ < 0.72` at `a_G`); the
  conclusion is `Target.SarkozyBound TargetLedger.targetSaving`, the bound `N^{1 − a_T/71}`. This
  is the
  `a_T` analogue of `TheoremCBlock.Ledger.ComparisonData.theoremC_classes_reduced_anchor_of_ledger`.

* `sarkozyBound_epsTarget_of_targetLedger`: P1's
  `LedgerAnchor.sarkozyBound_epsAnchor_of_anchorLedger` at `a_T`, i.e. the endgame of
  `Sarkozy.Param` (`thm:density:induction`, joint form of `cor:joint-closing`) with the
  six-query closing number discharged by `TargetBounds l`.

All analytic inputs (`EnvelopeBoundNonneg`, `SharpFirstTerms`, `DensityCancellation`,
`FixedIntervalEnvelopeEnergies`, `EnvelopeEnergies`, the unit `L³⁶` bound) are hypotheses, as in
K0's version.
-/

open Filter Finset Function
open scoped Topology BigOperators Matrix

namespace Sarkozy.TargetLedger

open Sarkozy.Comparison (jointTheta PrimitiveLedger)
open Sarkozy.Param (Params)

/-! ## The endgame of `Sarkozy.Param` at `a_T` -/

/-- **The endgame at the target exponent, closing discharged from the target ledger**
(`thm:density:induction` at `a = a_T`, joint form of `cor:joint-closing`). For any functional `Y`
with the reflection lower bound, the global moment bound and the five robust closing estimates
at `a_T` with the ledger's six-query closing data, the outward ledger bounds at `a_T` give
`s(N) ≤ C N^{1 − a_T/71}`. P1's `sarkozyBound_epsAnchor_of_anchorLedger` at `a_T`. -/
theorem sarkozyBound_epsTarget_of_targetLedger
    {Y : ℕ → Finset ℤ → ℝ} {M : ℝ} {l : PrimitiveLedger} (hledger : TargetBounds l) (hM : 0 < M)
    (hreflection : ∀ L : ℕ, 1 ≤ L → ∀ A : Finset ℤ,
      Admissible (blockScale * L) A → density (blockScale * L) A ^ slots ≤ Y L A)
    (hglobal : Param.GlobalMomentBound (Params.ofDecay targetDecay) Y M)
    (e : Param.ClosingEstimates (Params.ofDecay targetDecay) Y 6 l.L₀ l.J l.W l.jointConstant) :
    Target.SarkozyBound TargetLedger.targetSaving := by
  rw [← target_saving]
  exact Param.sarkozyBound_of_closingEstimates target_valid hledger.jointTheta_lt_one hM
    hreflection hglobal e

namespace ComparisonData

open Sarkozy.TheoremC Sarkozy.TheoremCBlock Sarkozy.RecordExpansion Sarkozy.RecordExpansion.Choice

variable {a : ℝ}
  {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]
  (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)

omit [DecidableEq P] in
/-- The two forms of the wrap exponent agree: `2ϑ/72 − 1 = −1 + ϑ/36`. -/
theorem wrapRatio_eq : D.wrapRatio = D.S.index.R_I * PrimitiveLedger.wrapFactor := by
  unfold TheoremCBlock.ComparisonData.wrapRatio PrimitiveLedger.wrapFactor
  congr 2
  ring

omit [DecidableEq P] in
/-- **Theorem C's closing number is at most the ledger's closing number** at any exponent `a`,
when the data's totals are bounded by the ledger: `B`, `L₀`, `T`, `R_I` and `S + A` from above,
the energy constant `𝓔` by the ledger's `E`, and the mean credit `m` from below by `m₁` plus
`2^6` times the joint-closing allocations `Δ_α + Δ_M + Δ_O + Δ_K + Δ_u − R_u`
(`cor:joint-closing`). K0's `Theta_le_of_anchorLedger` with `a` free. -/
theorem Theta_le_of_ledger {l : PrimitiveLedger} (hcard : Fintype.card E = 6)
    (hB0 : 0 ≤ D.B) (hB : D.B ≤ l.B) (hL₀ : D.L₀ ≤ l.L₀) (hT : D.ME.T ≤ l.T)
    (hR0 : 0 ≤ D.S.index.R_I) (hR : D.S.index.R_I ≤ l.R_I)
    (hSA : D.CL.S + D.CL.A ≤ l.S + l.A) {𝓔 : ℝ} (h𝓔 : 𝓔 ≤ l.E)
    (hm : l.m₁ + 64 * ((l.deltaAlpha + l.deltaMatching + l.deltaOdd + l.deltaEven) +
      l.deltaUpper - l.upperError) ≤ D.MC.m) :
    D.Theta 𝓔 ≤ l.theta := by
  have hw0 := PrimitiveLedger.wrapFactor_pos
  have hJ : D.Jc ≤ l.J := by
    unfold TheoremCBlock.ComparisonData.Jc PrimitiveLedger.J
    rw [hcard]
    have hR6 : (D.S.index.R_I / 2) ^ 6 ≤ (l.R_I / 2) ^ 6 :=
      pow_le_pow_left₀ (by linarith) (by linarith) 6
    have h1 : D.B * Real.exp D.ME.T ≤ l.B * Real.exp l.T :=
      mul_le_mul hB (Real.exp_le_exp.mpr hT) (Real.exp_pos _).le (le_trans hB0 hB)
    exact mul_le_mul h1 hR6 (pow_nonneg (by linarith) 6)
      (mul_nonneg (le_trans hB0 hB) (Real.exp_pos _).le)
  have hW : D.W ≤ l.W := by
    unfold TheoremCBlock.ComparisonData.W PrimitiveLedger.W wrapNumber
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
  unfold TheoremCBlock.ComparisonData.Theta PrimitiveLedger.theta
  rw [hcard]
  have hE := h𝓔
  unfold PrimitiveLedger.E at hE
  norm_num
  linarith

omit [DecidableEq P] in
/-- **The closing condition `Θ(𝓔) < 1` of Theorem C at any exponent, from a ledger with
`l.theta < 1`.** -/
theorem Theta_lt_one_of_ledger {l : PrimitiveLedger} (hl : l.theta < 1)
    (hcard : Fintype.card E = 6)
    (hB0 : 0 ≤ D.B) (hB : D.B ≤ l.B) (hL₀ : D.L₀ ≤ l.L₀) (hT : D.ME.T ≤ l.T)
    (hR0 : 0 ≤ D.S.index.R_I) (hR : D.S.index.R_I ≤ l.R_I)
    (hSA : D.CL.S + D.CL.A ≤ l.S + l.A) {𝓔 : ℝ} (h𝓔 : 𝓔 ≤ l.E)
    (hm : l.m₁ + 64 * ((l.deltaAlpha + l.deltaMatching + l.deltaOdd + l.deltaEven) +
      l.deltaUpper - l.upperError) ≤ D.MC.m) :
    D.Theta 𝓔 < 1 :=
  (Theta_le_of_ledger D hcard hB0 hB hL₀ hT hR0 hR hSA h𝓔 hm).trans_lt hl

section General

variable (hcop : Pairwise (Nat.Coprime on fun q => pr q ^ h q))

/-- **Theorem C with the (CP5) class bounds at a free exponent `a`, closing discharged from a
ledger** (`thm:comparison` in the form used by `thm:density:induction`). The hypotheses are
those of `TheoremCBlock.ComparisonData.theoremC_classes_reduced` with `hΘ` replaced by
`l.theta < 1` and the comparison of the data's totals with the ledger; the conclusion is the
target's statement at the exponent `a/(72 − ϑ)`. -/
theorem theoremC_classes_reduced_of_ledger (hP : (Params.ofDecay a).Valid) (ha : 0 ≤ a)
    {l : PrimitiveLedger} (hl : l.theta < 1)
    (hcard : Fintype.card E = 6)
    (hB0 : 0 ≤ D.B) (hB : D.B ≤ l.B) (hL₀ : D.L₀ ≤ l.L₀) (hT : D.ME.T ≤ l.T)
    (hR0 : 0 ≤ D.S.index.R_I) (hR : D.S.index.R_I ≤ l.R_I)
    (hSA : D.CL.S + D.CL.A ≤ l.S + l.A)
    (hm : l.m₁ + 64 * ((l.deltaAlpha + l.deltaMatching + l.deltaOdd + l.deltaEven) +
      l.deltaUpper - l.upperError) ≤ D.MC.m)
    (CB : TheoremCBlock.ClassBounds a m₀ blk p D.CL) {𝓔 : ℝ} (h𝓔 : 𝓔 ≤ l.E)
    (hΨ : ∀ L, ∑ ω ∈ univ.filter (fun ω : Choice (D.CL.T L) => IsSelection ω),
      (if CB.cls L ω = none then D.B * monomial (D.CL.π L) ω else CB.phi L ω) ≤ 𝓔)
    (hE1 : D.EnvelopeBoundNonneg) (hCB : CB.RobustNonneg)
    (hSF : D.SharpFirstTerms)
    (hDC : TheoremCBlock.DensityCancellation m₀ blk p pr h D.R.P5 D.S.pp D.S.ep)
    (hfix : D.FixedIntervalEnvelopeEnergies hcop) (henv : D.EnvelopeEnergies hcop)
    (hunit : ∃ p₀ : ℕ, ∀ (q : ℕ) [NeZero q], q.Prime → p₀ ≤ q → MixedLpBound (D.R.μp q) 36 1) :
    Target.SarkozyBound (Params.ofDecay a).saving :=
  (Param.sarkozyBound_iff _).mp
    (D.theoremC_classes_reduced hcop hP ha CB hΨ
      (Theta_lt_one_of_ledger D hl hcard hB0 hB hL₀ hT hR0 hR hSA h𝓔 hm) hE1 hCB hSF hDC
      hfix henv hunit)

end General

/-- **Theorem C with the (CP5) class bounds at the target `a_T`, closing discharged from the
target ledger** (`thm:comparison` in the form used by `thm:density:induction`, at
`a = a_T = TargetLedger.targetDecay`, `71/10⁵` since RG's rebase). The `a_T` analogue of K0's
`theoremC_classes_reduced_anchor_of_ledger`: `hΘ` is replaced by the ledger bounds
`TargetBounds l` (Part V certificates at the ledger's exponent, `Θ < 0.72`) and the comparison of
the data's totals with the ledger. The conclusion is `N^{1 − a_T/71}`. -/
theorem theoremC_classes_reduced_target_of_ledger
    (D : TheoremCBlock.ComparisonData targetDecay m₀ blk p pr h E)
    (hcop : Pairwise (Nat.Coprime on fun q => pr q ^ h q))
    {l : PrimitiveLedger} (hl : TargetBounds l)
    (hcard : Fintype.card E = 6)
    (hB0 : 0 ≤ D.B) (hB : D.B ≤ l.B) (hL₀ : D.L₀ ≤ l.L₀) (hT : D.ME.T ≤ l.T)
    (hR0 : 0 ≤ D.S.index.R_I) (hR : D.S.index.R_I ≤ l.R_I)
    (hSA : D.CL.S + D.CL.A ≤ l.S + l.A)
    (hm : l.m₁ + 64 * ((l.deltaAlpha + l.deltaMatching + l.deltaOdd + l.deltaEven) +
      l.deltaUpper - l.upperError) ≤ D.MC.m)
    (CB : TheoremCBlock.ClassBounds targetDecay m₀ blk p D.CL) {𝓔 : ℝ} (h𝓔 : 𝓔 ≤ l.E)
    (hΨ : ∀ L, ∑ ω ∈ univ.filter (fun ω : Choice (D.CL.T L) => IsSelection ω),
      (if CB.cls L ω = none then D.B * monomial (D.CL.π L) ω else CB.phi L ω) ≤ 𝓔)
    (hE1 : D.EnvelopeBoundNonneg) (hCB : CB.RobustNonneg)
    (hSF : D.SharpFirstTerms)
    (hDC : TheoremCBlock.DensityCancellation m₀ blk p pr h D.R.P5 D.S.pp D.S.ep)
    (hfix : D.FixedIntervalEnvelopeEnergies hcop) (henv : D.EnvelopeEnergies hcop)
    (hunit : ∃ p₀ : ℕ, ∀ (q : ℕ) [NeZero q], q.Prime → p₀ ≤ q → MixedLpBound (D.R.μp q) 36 1) :
    Target.SarkozyBound TargetLedger.targetSaving := by
  rw [← target_saving]
  exact theoremC_classes_reduced_of_ledger D hcop target_valid targetDecay_nonneg
    hl.theta_lt_one hcard hB0 hB hL₀ hT hR0 hR hSA hm CB h𝓔 hΨ hE1 hCB hSF hDC hfix henv hunit

end ComparisonData

end Sarkozy.TargetLedger
