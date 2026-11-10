module

public import Sarkozy.TheoremCParam.StructuredTheoremCGlue
public import Sarkozy.TheoremCParam.Classes

@[expose] public section

/-!
# `EnvelopeBoundNonneg` from the per-term bounds with nonnegative remainders

The classes form of Theorem C (`theoremC_classes_reduced`) takes (E1) as
`ComparisonData.EnvelopeBoundNonneg`. Its only difference from `ComparisonData.EnvelopeBound` is
the extra field `∀ L A ω, 0 ≤ rE L A ω`: the remainders of the selections are nonnegative.
`def:robust` makes them absolute values, the large-union terms of `lem:record:density-lp`.

**Why `EnvelopeBound` alone does not give it.** The first condition survives replacing `rE` by
its positive part `max rE 0`. The second one, `∑_ω π̃_ω rE_ω ≤ c L^{-σ} α`, does not, because the
weights `π̃_ω ≥ 0` multiply the positive parts, and these can exceed the signed sum. So the
reduction has to keep track of how the remainders are built.

**The reduction.** WP-R's `envelopeBound_of_terms` builds `rE_ω = ∑_f r⁰_{ω,f} + ∑_σ r_{ω,σ}`
from the per-term bounds of `lem:bracket-energy` and `prop:record:density-structured`.
`envelopeBoundNonneg_of_terms` takes the same per-term hypotheses, now at a free exponent `a`
(`Sarkozy.TheoremCParam.Structured`), together with `r⁰ ≥ 0` and `r ≥ 0`, and concludes
`EnvelopeBoundNonneg`. In the paper the per-term remainders are absolute values, so the two
nonnegativity hypotheses are part of the paper's statement. The proof is WP-R's, with the extra
field.

**Not covered.** I1's folded route `EnvelopeInputs.envelopeBound_of_foldedPieces`, at the
record exponent, uses `r_{ω,σ} = ∑_j ∑_f w · (r⁺ + r⁻)/2`, where `w` is a `choiceWeight`; its
`r⁺, r⁻ ≥ 0` are hypotheses there. It also needs `r⁰ ≥ 0`, and `w ≥ 0` for its coefficients.
Its `a₀` version waits for I1's files to settle.
-/

open Filter Finset
open scoped Topology BigOperators

namespace Sarkozy.TheoremCParam.Structured

open Sarkozy.TheoremC Sarkozy.Structured
open Sarkozy.Param (Params)
open Sarkozy.TheoremC Sarkozy.Comparison Sarkozy.PaperFrame Sarkozy.RecordExpansion
  Sarkozy.RecordExpansion.Choice

variable {a : ℝ}

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

omit [DecidableEq P] in
/-- **`EnvelopeBoundNonneg` from the per-term bounds with nonnegative remainders**
(`lem:bracket-energy` for the selection envelopes, `def:robust`; at a free price exponent `a`).
The hypotheses are those of `Sarkozy.TheoremCParam.Structured.envelopeBound_of_terms`, together
with `r⁰ ≥ 0` and `r ≥ 0`. -/
theorem envelopeBoundNonneg_of_terms (D : ComparisonData a m₀ p pr h E)
    (εE : ℕ → ℝ) (hε0 : ∀ L, 0 ≤ εE L) (hεt : Tendsto εE atTop (𝓝 0)) {cE : ℝ} (hcE : 0 ≤ cE)
    (r0 : ∀ L, Finset ℤ → Choice (D.CL.T L) → (PaperAtom J L → Bool) → ℝ)
    (r : ∀ L, Finset ℤ → Choice (D.CL.T L) → (∀ b, Option (D.FS.Ib L b)) → ℝ)
    (hr0 : ∀ L A ω f, 0 ≤ r0 L A ω f) (hr : ∀ L A ω σ, 0 ≤ r L A ω σ)
    (hterms : Param.AtCounterexamples (Params.ofDecay a) D.Y
        (fun L A => ∀ ω : Choice (D.CL.T L), IsSelection ω →
      (∀ f : PaperAtom J L → Bool,
        |diagonalIntegral (tensorLaw fun b => if f b then
            (if (ω b).isSome then 0 else ∑ i, D.GB.κu L b i)
          else entryFactor (D.R.law p L b) (D.CL.D L b) (ω b)) (atomLift m₀ p L A)| ≤
          ((1 + εE L) * (∏ b ∈ Choice.support ω, selectionFactor a p D.S.selPre L b) *
            D.Y L A) * ∏ b, (if f b then (if (ω b).isSome then 0 else D.GB.uprice L b) else 1) +
          r0 L A ω f) ∧
      (∀ σ : (∀ b, Option (D.FS.Ib L b)), σ ≠ (fun _ => none) → ∀ j,
        1 ≤ countVec (D.FS.tag L) σ j →
        |diagonalIntegral (tensorLaw (fun b => (σ b).elim
          (entryFactor (D.R.law p L b) (D.CL.D L b) (ω b) +
            (if (ω b).isSome then 0 else ∑ i, D.GB.κu L b i))
          (fun i => if (ω b).isSome then 0 else (D.FS.κ' L b i - D.FS.κ L b i))))
            (atomLift m₀ p L A)| ≤
          ((1 + εE L) * (∏ b ∈ Choice.support ω, selectionFactor a p D.S.selPre L b) *
            D.Y L A) * tagWeight (D.FS.tag L) (D.FS.dprice L) (D.FS.vprice L)
              (fun b => if (ω b).isSome then 0 else D.GB.uprice L b) j σ + r L A ω σ)))
    (hrem : Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
      ∑ ω ∈ univ.filter (fun ω : Choice (D.CL.T L) => IsSelection ω),
        monomial (D.CL.πt L) ω *
          (∑ f, r0 L A ω f +
            ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
              r L A ω σ) ≤ remainder cE L A)) :
    D.EnvelopeBoundNonneg := by
  refine ⟨fun L => εE L * D.B, fun L => mul_nonneg (hε0 L) (B_nonneg D), ?_, cE, hcE,
    fun L A ω => ∑ f, r0 L A ω f +
      ∑ σ ∈ univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none),
        r L A ω σ, ?_, ?_, hrem⟩
  · simpa using hεt.mul_const D.B
  · intro L A ω
    exact add_nonneg (sum_nonneg fun f _ => hr0 L A ω f) (sum_nonneg fun σ _ => hr L A ω σ)
  · filter_upwards [hterms] with L hL
    intro C hC hk A hA hY ω hω
    obtain ⟨h0, h1⟩ := hL C hC hk A hA hY ω hω
    have hY0 : 0 ≤ D.Y L A := by
      have : 0 ≤ C * (L : ℝ) ^ (-(Params.ofDecay a).decay) *
        density ((Params.ofDecay a).blockScale * L) A ^ (Params.ofDecay a).densityExponent :=
        mul_nonneg (mul_nonneg (by linarith) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
          (Real.rpow_nonneg (density_nonneg _ _) _)
      linarith
    have hCX : 0 ≤ ∏ b ∈ Choice.support ω, selectionFactor a p D.S.selPre L b :=
      prod_nonneg fun b _ => D.selectionFactor_nonneg L b
    have hK : 0 ≤ (1 + εE L) * (∏ b ∈ Choice.support ω, selectionFactor a p D.S.selPre L b) *
        D.Y L A := mul_nonneg (mul_nonneg (by linarith [hε0 L]) hCX) hY0
    refine (envelope_energy_le_B D L A ω hK (r0 L A ω) (r L A ω) h0 h1).trans (le_of_eq ?_)
    ring

end Sarkozy.TheoremCParam.Structured
