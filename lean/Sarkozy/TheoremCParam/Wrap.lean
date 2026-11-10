module

public import Sarkozy.TheoremC.Wrap
public import Sarkozy.TheoremCParam.Defs

@[expose] public section



open Filter Finset Function
open scoped Topology BigOperators Matrix

namespace Sarkozy.TheoremCParam

open Sarkozy.TheoremC
open Sarkozy.Param (Params)

variable {a : ℝ}

open Sarkozy.FourierArithmetic Sarkozy.Functional Sarkozy.IndexSupport Sarkozy.Comparison
  Sarkozy.PaperFrame

/-- At a least normalized counterexample the functional is nonnegative (it exceeds
`C L^{-a} α^θ ≥ 0`). -/
theorem nonneg_of_counterexample {Y : ℕ → Finset ℤ → ℝ} {C : ℝ} (hC : 1 ≤ C) {L : ℕ}
    {A : Finset ℤ}
    (hcounter : C * (L : ℝ) ^ (-a) * density (blockScale * L) A ^ densityExponent <
      Y L A) : 0 ≤ Y L A := by
  have h0 : 0 ≤ C * (L : ℝ) ^ (-a) * density (blockScale * L) A ^ densityExponent :=
    mul_nonneg (mul_nonneg (by linarith) (Real.rpow_nonneg (Nat.cast_nonneg L) _))
      (Real.rpow_nonneg (density_nonneg _ A) _)
  exact h0.trans hcounter.le

section Paper

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] (m₀ : J₀ → ℕ) [∀ i, NeZero (m₀ i)]
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] (p : ∀ L, J L → ℕ)
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] (pr h : P → ℕ) [∀ q, NeZero (pr q ^ h q)]
  (hcop : Pairwise (Nat.Coprime on fun q => pr q ^ h q))
  {E : Type} [Fintype E] [DecidableEq E]

/-- **The wrap estimate** (`lem:record:wrap-expansion`, in the robust form of the field
`wrap` of `ClosingEstimates`, for the paper's coupled index, inputs and lift). If at every
least normalized counterexample of every large scale the nonwrapping coupled forms
`I_{ν,𝒮,𝒲}` (`𝒲 ⊊ 𝒮`) are remainders `c_n L^{-σ} α` (`hnon`) and the fully wrapping ones are
at most `(B e^{S+A} x^{|𝒮|} + ε(L)) Y + c_w L^{-σ} α` (`hwrapT`), then
`2^k Y_ν ≤ J_ν + (2^k W + 3^k ε(L)) Y + (4^k c_n + 3^k c_w) L^{-σ} α`, `k = |E|`,
`W = wrapNumber B (S + A) x k`. No sign condition on `B` or `x` is needed for this step. -/
theorem wrap_estimate (Y : ℕ → Finset ℤ → ℝ) (μ : E → ∀ q, ZMod (pr q ^ h q) → ℝ)
    (hμ : ∀ e q r, 0 ≤ μ e q r) (hμ1 : ∀ e q, ∑ r, μ e q r = 1)
    (t : E → ∀ q, Tails (Chain.residues (pr q) (h q)).depth)
    (hnorm : ∀ e q (l : Fin ((Chain.residues (pr q) (h q)).depth + 1)) f,
      (Chain.residues (pr q) (h q)).diff l *ᵥ f = f →
      (convMatrix (μ e q) *ᵥ f) ⬝ᵥ (convMatrix (μ e q) *ᵥ f) ≤ (t e q).tail l ^ 2 * (f ⬝ᵥ f))
    (u w : E → reservedCut.Half) (hu : Function.Injective u) (hw : Function.Injective w)
    (ν : ∀ L b, ((Slot → AtomLabel m₀ p L b) → ℝ) →ₗ[ℝ] ℝ)
    {Bf SA x : ℝ} (εw : ℕ → ℝ) (hεw0 : ∀ L, 0 ≤ εw L)
    {cn cw : ℝ} (hcn : 0 ≤ cn) (hcw : 0 ≤ cw)
    (hnon : Param.AtCounterexamples (Params.ofDecay a) Y
        fun L A => ∀ S W : Finset E, W ⊆ S → W ≠ S →
      |wrapForm m₀ p pr h hcop μ u w ν L A S W| ≤ remainder cn L A)
    (hwrapT : Param.AtCounterexamples (Params.ofDecay a) Y fun L A => ∀ S : Finset E, S ≠ ∅ →
      |wrapForm m₀ p pr h hcop μ u w ν L A S S| ≤
        (Bf * Real.exp SA * x ^ S.card + εw L) * Y L A + remainder cw L A) :
    Param.AtCounterexamples (Params.ofDecay a) Y fun L A =>
      2 ^ Fintype.card E * energyComparison ν (atomLift m₀ p) L A ≤
        signedIndexForm (paperCoupledIndex pr h μ hμ hμ1 t hnorm u w hu hw) ν
            (fun L A e => atomInput m₀ p pr h hcop L A e)
            (fun L A e => atomInput m₀ p pr h hcop L A e) (atomLift m₀ p) L A +
          (2 ^ Fintype.card E * wrapNumber Bf SA x (Fintype.card E) +
              3 ^ Fintype.card E * εw L) * Y L A +
          remainder (4 ^ Fintype.card E * cn + 3 ^ Fintype.card E * cw) L A := by
  filter_upwards [hnon, hwrapT] with L hn hwr
  intro C hC hind A hA hcounter
  have hY : 0 ≤ Y L A := nonneg_of_counterexample hC hcounter
  have hb := paper_wrap_bound m₀ p pr h hcop μ hμ hμ1 t hnorm u w hu hw ν L A
    (Y := Y L A) (B' := Bf * Real.exp SA) (x := x) (ε := εw L) (r := remainder cn L A)
    (r' := remainder cw L A) hY (hεw0 L) (remainder_nonneg' hcn L A)
    (remainder_nonneg' hcw L A) (hn C hC hind A hA hcounter) (hwr C hC hind A hA hcounter)
  have hW : 2 ^ Fintype.card E * wrapNumber Bf SA x (Fintype.card E) * Y L A =
      Bf * Real.exp SA * ((2 + x) ^ Fintype.card E - 2 ^ Fintype.card E) * Y L A := by
    rw [two_pow_mul_wrapNumber]
  have hrem : remainder (4 ^ Fintype.card E * cn + 3 ^ Fintype.card E * cw) L A =
      4 ^ Fintype.card E * remainder cn L A + 3 ^ Fintype.card E * remainder cw L A := by
    unfold remainder
    ring
  have h1 := neg_abs_le (signedIndexForm (paperCoupledIndex pr h μ hμ hμ1 t hnorm u w hu hw) ν
      (fun L A e => atomInput m₀ p pr h hcop L A e)
      (fun L A e => atomInput m₀ p pr h hcop L A e) (atomLift m₀ p) L A -
      2 ^ Fintype.card E * energyComparison ν (atomLift m₀ p) L A)
  rw [hrem]
  have hexp : (2 ^ Fintype.card E * wrapNumber Bf SA x (Fintype.card E) +
        3 ^ Fintype.card E * εw L) * Y L A =
      2 ^ Fintype.card E * wrapNumber Bf SA x (Fintype.card E) * Y L A +
        3 ^ Fintype.card E * εw L * Y L A := by ring
  rw [hexp, hW]
  linarith

end Paper

end Sarkozy.TheoremCParam
