module

public import Sarkozy.ClassSlack.NoMean
public import Sarkozy.JointClosing.Main

@[expose] public section

/-!
# The one-block credit at `m₁ = 0` is a theorem (CG; evidence for a ledger option)

After `classPartsNoMean`, the only mean input of the class group is `hm₁`: `SelMean` at `μ = 0`,
i.e. `(m₁ − o(1)) Y − c₂ L^{-σ} α ≤ (E_L + E_R)/2` with the ledger's one-block credit
`m₁ = targetLedger.m₁ ≥ 1.5309` (`prop:record:mean-credit`, Steps 1–3). The ledger's `Θ` reads
`m₁` only through `(1 − m₁)/64` (`TargetLedger.Numerics`), so `m₁ = 0` would cost
`1.5309/64 = 0.0239` in `Θ` (`0.6943 → 0.7182`), over RG's cap `0.7` (margin `0.0057`) but far
below `1`.

**`selMeanAt_zero`** (proved): the statement of `SelMean` at `μ = 0`, with the one-block credit
`m` in place of `targetLedger.m₁`, holds at `m = 0` for every class datum and every family of
selection energies, because the mean energies of the matching envelopes are nonnegative
(`JointClosing.ML_positive`, `MR_positive`, `EnvelopesPaper.energyMean_nonneg`). So with the
ledger entry `m₁` lowered to `0` (a change to `TargetLedger/Numerics.lean`, not made here),
`hm₁` would be closed and the class group would carry no mean input at all. `selMeanAt_ledger`
records that `SelMeanAt targetLedger.m₁` is `SelMean` at `μ = 0` (`rfl`).
-/

open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.ClassSlack

open Sarkozy.ClassBoundsPaper Sarkozy.ClassInputsPaper Sarkozy.ClassData
open Sarkozy.MeanCredit Sarkozy.TheoremCBlock
open Sarkozy.RecordExpansion Sarkozy.RecordExpansion.Choice
open Sarkozy.CancellationSteps (PaperJ0 paperM0 paperTail)
open Sarkozy.Comparison (remainder energyMean)
open Sarkozy.BlockFrame
open Sarkozy.Param (Params)
open Sarkozy.PartVLaws (paperAtomMap)
open Sarkozy.TargetLedger (targetDecay targetLedger)

variable {B : Type} [Fintype B] [DecidableEq B] {blockOf : PaperJ0 → B}

/-- **`SelMean` with the one-block credit `m` as a parameter** (`prop:record:mean-credit`): the
mean energies retain `(m − o(1)) Y + ∑_ω μ_ω Z_ω`. -/
def SelMeanAt (m : ℝ) (D : CD blockOf) (cd : ClassData D.CL)
    (μ : ∀ L, Choice (D.CL.T L) → ℝ) (Zs : ∀ L, Finset ℤ → Choice (D.CL.T L) → ℝ) : Prop :=
  ∃ ε₂ : ℕ → ℝ, Tendsto ε₂ atTop (𝓝 0) ∧ ∃ c₂ : ℝ, 0 ≤ c₂ ∧
    Param.AtCounterexamples (Params.ofDecay targetDecay) D.Y fun L A =>
      (m - ε₂ L) * D.Y L A + ∑ ω ∈ cd.sel L, μ L ω * Zs L A ω - remainder c₂ L A ≤
        (energyMean (blockLift paperM0 (paperAtomMap blockOf) paperTail) D.ME.ML L A +
          energyMean (blockLift paperM0 (paperAtomMap blockOf) paperTail) D.ME.MR L A) / 2

/-- At the ledger's `m₁`, `SelMeanAt` is CM's `SelMean`. -/
theorem selMeanAt_ledger (D : CD blockOf) (cd : ClassData D.CL)
    (μ : ∀ L, Choice (D.CL.T L) → ℝ) (Zs : ∀ L, Finset ℤ → Choice (D.CL.T L) → ℝ) :
    SelMeanAt targetLedger.m₁ D cd μ Zs ↔ SelMean D cd μ Zs := Iff.rfl

/-- **The mean input of the mean-free class group at `m₁ = 0` is a theorem**: the mean energies
of the matching envelopes are nonnegative (`def:cp7` with credit `0`, as
`JointClosing.zeroMeanCredit`). -/
theorem selMeanAt_zero (D : CD blockOf) (cd : ClassData D.CL)
    (Zs : ∀ L, Finset ℤ → Choice (D.CL.T L) → ℝ) :
    SelMeanAt 0 D cd (fun _ _ => 0) Zs := by
  refine ⟨fun _ => 0, tendsto_const_nhds, 0, le_refl 0, ?_⟩
  unfold Param.AtCounterexamples
  filter_upwards with L
  intro _ _ _ A _ _
  have h1 := EnvelopesPaper.energyMean_nonneg (blockLift paperM0 (paperAtomMap blockOf) paperTail)
    D.ME.ML (JointClosing.ML_positive D.ME) L A
  have h2 := EnvelopesPaper.energyMean_nonneg (blockLift paperM0 (paperAtomMap blockOf) paperTail)
    D.ME.MR (JointClosing.MR_positive D.ME) L A
  have h0 : remainder 0 L A = 0 := by
    unfold remainder
    ring
  rw [h0]
  simp only [zero_mul, sum_const_zero, sub_zero, add_zero]
  linarith

end Sarkozy.ClassSlack
