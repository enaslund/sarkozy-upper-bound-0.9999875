module

public import Sarkozy.EnvelopeEnergiesPaper.SharpFirstCoupled
public import Sarkozy.Moments.Mixed

@[expose] public section

/-!
# Non-vacuity checks for B5's new input structures

* `recordMoment_uniform`: the per-record moment input `RecordMoment` holds for the independent
  uniform law on `Slot → X` (a positive record of mass `1`) at every `θ ≤ 72`;
* `recordMoment_of_mass_zero`: it holds trivially for a record of mass `0` (such terms vanish,
  `SharpFirstCoupledInputs.term_bound`);
* the fibre-moment input is the weakest fibre input of the coupled lemma
  (`coupledFibreMoment_of_price`, with `coupledFibrePrice_of_moment` the converse), so it asks
  nothing beyond `lem:density:coupled`'s own hypothesis;
* `SharpFoldData.hasSharpBound`: the sharp-fold data contain a witness of K0's `FirstStage.sharp`;
* the CRT bundles are equivalent to G1's term by term (`env_term_crt`, `fix_term_crt_source`,
  `fix_term_crt_target`).
-/

open Finset

namespace Sarkozy.EnvelopeEnergiesPaper

open Sarkozy.TheoremC Sarkozy.Structured

variable {X : Type} [Fintype X] [DecidableEq X] [Nonempty X]

/-- **A toy positive record satisfies the record-moment input**: the independent uniform law
`Unif(X)^{⊗72}` has unit mixed `L^1`, hence unit mixed `L^{72/θ}` for `0 < θ ≤ 72`. -/
theorem recordMoment_uniform {θ : ℝ} (hθ : 0 < θ) (hθ72 : θ ≤ 72) :
    RecordMoment
      (signedIntegral (FiniteLaw.pi (fun _ : Slot => FiniteLaw.uniform X)).weight) θ := by
  intro _
  refine ⟨FiniteLaw.pi (fun _ : Slot => FiniteLaw.uniform X), fun z => ?_, ?_⟩
  · rw [lawDensity_signedIntegral_eq]
    have hm : mass (signedIntegral (FiniteLaw.pi (fun _ : Slot => FiniteLaw.uniform X)).weight) =
        1 := (FiniteLaw.pi (fun _ : Slot => FiniteLaw.uniform X)).expect_const 1
    rw [hm, div_one]
  · exact MixedLpBound.mono_exponent mixedLpBound_independent zero_le_one one_pos
      (by rw [le_div_iff₀ hθ]; linarith)

/-- A record of mass `0` satisfies the record-moment input trivially. -/
theorem recordMoment_of_mass_zero {κ : SlotMeasure X} (h0 : mass κ = 0) (θ : ℝ) :
    RecordMoment κ θ := fun h => absurd h (by rw [h0]; exact lt_irrefl 0)

end Sarkozy.EnvelopeEnergiesPaper
