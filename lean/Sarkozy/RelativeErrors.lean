module

public import Sarkozy.Initialization
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Uniform relative errors at a least counterexample

The global second-density moment estimate prevents the density at a
counterexample from being too small. This turns a density-linear analytic
error into a negative power of the scale, uniformly in every induction
constant C ≥ 1. The power is positive at the selected parameters.
-/

@[expose] public section

namespace Sarkozy

open Filter
open scoped Topology

/-- The inverse density factor forced by the global moment bound. -/
theorem inverse_density_bound {δ M L : ℝ}
    (hδ : 0 < δ) (hM : 0 < M) (hL : 0 < L)
    (h : L ^ (-decay) * δ ^ densityExponent ≤ M * L ^ momentSlack * δ ^ 2) :
    δ ^ (1 - densityExponent) ≤
      M ^ densityRatio * L ^ ((decay + momentSlack) * densityRatio) := by
  have hleft : Real.log (L ^ (-decay) * δ ^ densityExponent) =
      -decay * Real.log L + densityExponent * Real.log δ := by
    rw [Real.log_mul (Real.rpow_pos_of_pos hL _).ne' (Real.rpow_pos_of_pos hδ _).ne',
      Real.log_rpow hL, Real.log_rpow hδ]
  have hright : Real.log (M * L ^ momentSlack * δ ^ 2) =
      Real.log M + momentSlack * Real.log L + 2 * Real.log δ := by
    rw [Real.log_mul (mul_pos hM (Real.rpow_pos_of_pos hL _)).ne' (pow_pos hδ 2).ne',
      Real.log_mul hM.ne' (Real.rpow_pos_of_pos hL _).ne', Real.log_rpow hL,
      Real.log_pow]
    norm_num
  have hlog := Real.log_le_log
    (mul_pos (Real.rpow_pos_of_pos hL _) (Real.rpow_pos_of_pos hδ _)) h
  rw [hleft, hright] at hlog
  apply (Real.log_le_log_iff (Real.rpow_pos_of_pos hδ _)
    (mul_pos (Real.rpow_pos_of_pos hM _) (Real.rpow_pos_of_pos hL _))).mp
  rw [Real.log_rpow hδ,
    Real.log_mul (Real.rpow_pos_of_pos hM _).ne' (Real.rpow_pos_of_pos hL _).ne',
    Real.log_rpow hM, Real.log_rpow hL]
  norm_num [decay, momentSlack, densityExponent, densityRatio] at hlog ⊢

/-- Explicit relative-error bound, with no density or induction constant in
the resulting coefficient. -/
theorem relative_error_bound {δ M L C E Y : ℝ}
    (hδ : 0 < δ) (hM : 0 < M) (hL : 0 < L) (hC : 1 ≤ C) (hE : 0 ≤ E)
    (hcounter : C * L ^ (-decay) * δ ^ densityExponent < Y)
    (hglobal : Y ≤ M * L ^ momentSlack * δ ^ 2) :
    E * L ^ (-cancellationDecay) * δ ≤
      (E * M ^ densityRatio * L ^ (-relativeErrorDecay)) * Y := by
  have hweight : 0 < L ^ (-decay) * δ ^ densityExponent :=
    mul_pos (Real.rpow_pos_of_pos hL _) (Real.rpow_pos_of_pos hδ _)
  have hbase : L ^ (-decay) * δ ^ densityExponent ≤ Y := by
    have hmul := mul_le_mul_of_nonneg_right hC hweight.le
    simp only [one_mul] at hmul
    exact hmul.trans (by simpa only [mul_assoc] using hcounter.le)
  have hY : 0 < Y := hweight.trans_le hbase
  have hinverse := inverse_density_bound hδ hM hL (hbase.trans hglobal)
  have hfactor : 0 ≤ E * L ^ (decay - cancellationDecay) :=
    mul_nonneg hE (Real.rpow_nonneg hL.le _)
  have hstep := mul_le_mul_of_nonneg_left hbase
    (mul_nonneg hfactor (Real.rpow_nonneg hδ.le (1 - densityExponent)))
  have hid : (E * L ^ (decay - cancellationDecay) * δ ^ (1 - densityExponent)) *
      (L ^ (-decay) * δ ^ densityExponent) = E * L ^ (-cancellationDecay) * δ := by
    calc
      _ = E * (L ^ (decay - cancellationDecay) * L ^ (-decay)) *
          (δ ^ (1 - densityExponent) * δ ^ densityExponent) := by ring
      _ = _ := by
        rw [← Real.rpow_add hL, ← Real.rpow_add hδ]
        have he : decay - cancellationDecay + -decay = -cancellationDecay := by ring
        have hd : 1 - densityExponent + densityExponent = 1 := by ring
        rw [he, hd, Real.rpow_one]
  rw [hid] at hstep
  apply hstep.trans
  have hmul := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hinverse hfactor) hY.le
  convert hmul using 1
  congr 1
  calc
    E * M ^ densityRatio * L ^ (-relativeErrorDecay) =
        E * M ^ densityRatio * L ^ ((decay - cancellationDecay) +
          (decay + momentSlack) * densityRatio) := by
      congr 2
      unfold relativeErrorDecay
      ring
    _ = _ := by rw [Real.rpow_add hL]; ring

/-- The global moment input after absorbing the fixed factor K^η into M. -/
def GlobalMomentBound (Y : ℕ → Finset ℤ → ℝ) (M : ℝ) : Prop :=
  ∀ L : ℕ, 1 ≤ L → ∀ A : Finset ℤ, Admissible (blockScale * L) A →
    Y L A ≤ M * (L : ℝ) ^ momentSlack * density (blockScale * L) A ^ 2

/-- The analytic comparison before absorbing its density-linear error.

The constant C is universally quantified: the eventual scale must be uniform
in C. This is essential for choosing the finite initialization constant later.
-/
def RawComparison (Y : ℕ → Finset ℤ → ℝ) (q : ℕ → ℝ) (E : ℝ) : Prop :=
  ∀ᶠ L : ℕ in atTop, ∀ C : ℝ, 1 ≤ C →
    (∀ k : ℕ, 1 ≤ k → k < L → EnergyUpperBoundAt Y C k) →
    ∀ A : Finset ℤ, Admissible (blockScale * L) A →
      C * (L : ℝ) ^ (-decay) * density (blockScale * L) A ^ densityExponent < Y L A →
      Y L A ≤ q L * Y L A +
        E * (L : ℝ) ^ (-cancellationDecay) * density (blockScale * L) A

/-- Finite initialization and uniform error absorption are both discharged.

Only reflection, the global moment estimate, and the raw comparison remain
as mathematical inputs; convergence supplies the eventual scalar margin.
-/
theorem scaledEnergyEstimate_of_rawComparison
    {Y : ℕ → Finset ℤ → ℝ} {M E θ : ℝ} {q : ℕ → ℝ}
    (hM : 0 < M) (hE : 0 ≤ E) (hθ : θ < 1)
    (hreflection : ∀ L : ℕ, 1 ≤ L → ∀ A : Finset ℤ,
      Admissible (blockScale * L) A → density (blockScale * L) A ^ slots ≤ Y L A)
    (hglobal : GlobalMomentBound Y M) (hrec : RawComparison Y q E)
    (hq : Tendsto q atTop (𝓝 θ)) : ScaledEnergyEstimate Y := by
  let coefficient : ℕ → ℝ := fun L =>
    E * M ^ densityRatio * (L : ℝ) ^ (-relativeErrorDecay)
  have hvanish : Tendsto coefficient atTop (𝓝 0) := by
    have hp := (tendsto_rpow_neg_atTop relativeErrorDecay_pos).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa only [coefficient, Function.comp_def, mul_zero] using
      hp.const_mul (E * M ^ densityRatio)
  have hlimit : Tendsto (fun L => q L + coefficient L) atTop (𝓝 θ) := by
    simpa only [add_zero] using hq.add hvanish
  obtain ⟨L₀, hL₀⟩ := eventually_atTop.mp (hrec.and (hlimit.eventually_lt_const hθ))
  have hzero : ∀ L : ℕ, 1 ≤ L → Y L ∅ ≤ 0 := by
    intro L hL
    simpa only [density_empty, zero_pow (by decide : 2 ≠ 0), mul_zero] using
      hglobal L hL ∅ (admissible_empty _)
  apply scaledEnergyEstimate_of_uniform_contraction (q := θ) (L₀ := L₀)
    (error := fun L _ => q L - θ + coefficient L) hzero hreflection
  · intro C hC L hL hlarge ih A hA hcounter
    have hδ : 0 < density (blockScale * L) A := by
      by_contra! hnonpos
      have hz := le_antisymm hnonpos (density_nonneg _ _)
      have hy : Y L A ≤ 0 := by
        simpa only [hz, zero_pow (by decide : 2 ≠ 0), mul_zero] using hglobal L hL A hA
      have hb : 0 ≤ C * (L : ℝ) ^ (-decay) *
          density (blockScale * L) A ^ densityExponent :=
        mul_nonneg (mul_nonneg (zero_le_one.trans hC)
          (Real.rpow_nonneg (Nat.cast_nonneg _) _))
          (Real.rpow_nonneg (density_nonneg _ _) _)
      linarith
    have hLpos : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
    have herr := relative_error_bound hδ hM hLpos hC hE hcounter (hglobal L hL A hA)
    have hraw := (hL₀ L hlarge).1 C hC ih A hA hcounter
    calc
      Y L A ≤ q L * Y L A + E * (L : ℝ) ^ (-cancellationDecay) *
          density (blockScale * L) A := hraw
      _ ≤ q L * Y L A + coefficient L * Y L A := add_le_add le_rfl herr
      _ = _ := by ring
  · intro L _ hlarge A _
    have h := (hL₀ L hlarge).2
    linarith

/-- Selected closing arithmetic plus the raw analytic inputs imply the exact
paper exponent. No finite initialization or relative-error hypothesis remains. -/
theorem powerSavingBound_of_rawComparison
    {l : ClosingLedger} (hledger : l.Bounds)
    {Y : ℕ → Finset ℤ → ℝ} {M E : ℝ} {q : ℕ → ℝ}
    (hM : 0 < M) (hE : 0 ≤ E)
    (hreflection : ∀ L : ℕ, 1 ≤ L → ∀ A : Finset ℤ,
      Admissible (blockScale * L) A → density (blockScale * L) A ^ slots ≤ Y L A)
    (hglobal : GlobalMomentBound Y M) (hrec : RawComparison Y q E)
    (hq : Tendsto q atTop (𝓝 l.theta)) : PowerSavingBound :=
  powerSavingBound_of_scaledEnergyEstimate
    (scaledEnergyEstimate_of_rawComparison hM hE (ClosingLedger.theta_lt_one hledger)
      hreflection hglobal hrec hq)

end Sarkozy
