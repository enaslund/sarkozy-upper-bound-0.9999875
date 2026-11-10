module

public import Sarkozy.Param.Induction
public import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

@[expose] public section

/-!
# Uniform relative errors at a least counterexample, for general exponents

Parametrized copy of `Sarkozy/RelativeErrors.lean`. In the proof of `thm:density:induction`
(`paper/sections/31_density_induction_upgrade.tex`), the global moment bound
`lem:density:global-moment`, `Y ≤ C_η L^η α²`, at a least counterexample
`Y > C₀ L^{-a} α^ϑ` gives `α ≥ c C₀^{1/(2−ϑ)} L^{−(a+η)/(2−ϑ)}`. A density-linear error
`O(L^{-σ} α)` divided by `Y` is then `O(L^{−(σ − a − (a+η)(ϑ−1)/(2−ϑ))})`, uniformly in
`C₀ ≥ 1`, and this tends to zero by the error gate of `Params.Valid`.

The hard-coded file closes the logarithmic inequality of `inverse_density_bound` with
`norm_num` at the record values; here it is closed for every `1 ≤ ϑ < 2`.
-/

namespace Sarkozy.Param

open Filter
open scoped Topology

variable {P : Params}

/-- **The inverse density factor forced by the global moment bound** (proof of
`thm:density:induction`): from `L^{-a} δ^ϑ ≤ M L^η δ²`,
`δ^{1−ϑ} ≤ M^ρ L^{(a+η)ρ}` with `ρ = (ϑ − 1)/(2 − ϑ)`. Needs `1 ≤ ϑ < 2`. -/
theorem inverse_density_bound (hP : P.Valid) {δ M L : ℝ}
    (hδ : 0 < δ) (hM : 0 < M) (hL : 0 < L)
    (h : L ^ (-P.decay) * δ ^ P.densityExponent ≤ M * L ^ P.momentSlack * δ ^ 2) :
    δ ^ (1 - P.densityExponent) ≤
      M ^ P.densityRatio * L ^ ((P.decay + P.momentSlack) * P.densityRatio) := by
  have hleft : Real.log (L ^ (-P.decay) * δ ^ P.densityExponent) =
      -P.decay * Real.log L + P.densityExponent * Real.log δ := by
    rw [Real.log_mul (Real.rpow_pos_of_pos hL _).ne' (Real.rpow_pos_of_pos hδ _).ne',
      Real.log_rpow hL, Real.log_rpow hδ]
  have hright : Real.log (M * L ^ P.momentSlack * δ ^ 2) =
      Real.log M + P.momentSlack * Real.log L + 2 * Real.log δ := by
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
  -- `(ϑ − 2) log δ ≤ log M + (a + η) log L`, so `−log δ ≤ (log M + (a + η) log L)/(2 − ϑ)`.
  have h2 := hP.two_sub_pos
  have hθ1 : 0 ≤ P.densityExponent - 1 := by linarith [hP.one_le_densityExponent]
  have hx : -Real.log δ ≤
      (Real.log M + (P.decay + P.momentSlack) * Real.log L) / (2 - P.densityExponent) := by
    rw [le_div_iff₀ h2]
    linarith
  have hmul := mul_le_mul_of_nonneg_left hx hθ1
  have hrhs : (P.densityExponent - 1) *
      ((Real.log M + (P.decay + P.momentSlack) * Real.log L) / (2 - P.densityExponent)) =
      P.densityRatio * Real.log M +
        (P.decay + P.momentSlack) * P.densityRatio * Real.log L := by
    unfold Params.densityRatio
    field_simp
  rw [hrhs] at hmul
  linarith

/-- **Explicit relative-error bound** at a counterexample, with no density or induction
constant in the coefficient (`Sarkozy.relative_error_bound` in general):
`E L^{-σ} δ ≤ E M^ρ L^{−(σ − a − (a+η)ρ)} Y`. -/
theorem relative_error_bound (hP : P.Valid) {δ M L C E Y : ℝ}
    (hδ : 0 < δ) (hM : 0 < M) (hL : 0 < L) (hC : 1 ≤ C) (hE : 0 ≤ E)
    (hcounter : C * L ^ (-P.decay) * δ ^ P.densityExponent < Y)
    (hglobal : Y ≤ M * L ^ P.momentSlack * δ ^ 2) :
    E * L ^ (-P.cancellationDecay) * δ ≤
      (E * M ^ P.densityRatio * L ^ (-P.relativeErrorDecay)) * Y := by
  have hweight : 0 < L ^ (-P.decay) * δ ^ P.densityExponent :=
    mul_pos (Real.rpow_pos_of_pos hL _) (Real.rpow_pos_of_pos hδ _)
  have hbase : L ^ (-P.decay) * δ ^ P.densityExponent ≤ Y := by
    have hmul := mul_le_mul_of_nonneg_right hC hweight.le
    simp only [one_mul] at hmul
    exact hmul.trans (by simpa only [mul_assoc] using hcounter.le)
  have hY : 0 < Y := hweight.trans_le hbase
  have hinverse := inverse_density_bound hP hδ hM hL (hbase.trans hglobal)
  have hfactor : 0 ≤ E * L ^ (P.decay - P.cancellationDecay) :=
    mul_nonneg hE (Real.rpow_nonneg hL.le _)
  have hstep := mul_le_mul_of_nonneg_left hbase
    (mul_nonneg hfactor (Real.rpow_nonneg hδ.le (1 - P.densityExponent)))
  have hid : (E * L ^ (P.decay - P.cancellationDecay) * δ ^ (1 - P.densityExponent)) *
      (L ^ (-P.decay) * δ ^ P.densityExponent) = E * L ^ (-P.cancellationDecay) * δ := by
    calc
      _ = E * (L ^ (P.decay - P.cancellationDecay) * L ^ (-P.decay)) *
          (δ ^ (1 - P.densityExponent) * δ ^ P.densityExponent) := by ring
      _ = _ := by
        rw [← Real.rpow_add hL, ← Real.rpow_add hδ]
        have he : P.decay - P.cancellationDecay + -P.decay = -P.cancellationDecay := by ring
        have hd : 1 - P.densityExponent + P.densityExponent = 1 := by ring
        rw [he, hd, Real.rpow_one]
  rw [hid] at hstep
  apply hstep.trans
  have hmul := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hinverse hfactor) hY.le
  convert hmul using 1
  congr 1
  calc
    E * M ^ P.densityRatio * L ^ (-P.relativeErrorDecay) =
        E * M ^ P.densityRatio * L ^ ((P.decay - P.cancellationDecay) +
          (P.decay + P.momentSlack) * P.densityRatio) := by
      congr 2
      unfold Params.relativeErrorDecay
      ring
    _ = _ := by rw [Real.rpow_add hL]; ring

variable (P)

/-- **`lem:density:global-moment`** in the form used by the induction, at the exponents `P`:
`Y(L, A) ≤ M L^η α²` for every square-difference-free `A ⊆ [1, K L]`
(`Sarkozy.GlobalMomentBound` in general). Used as a hypothesis here. -/
def GlobalMomentBound (Y : ℕ → Finset ℤ → ℝ) (M : ℝ) : Prop :=
  ∀ L : ℕ, 1 ≤ L → ∀ A : Finset ℤ, Admissible (P.blockScale * L) A →
    Y L A ≤ M * (L : ℝ) ^ P.momentSlack * density (P.blockScale * L) A ^ 2

/-- The analytic comparison before absorbing its density-linear error, at the exponents `P`
(`Sarkozy.RawComparison` in general). The induction constant `C ≥ 1` is universally
quantified after the eventual scale, as in the proof of `thm:density:induction`. -/
def RawComparison (Y : ℕ → Finset ℤ → ℝ) (q : ℕ → ℝ) (E : ℝ) : Prop :=
  ∀ᶠ L : ℕ in atTop, ∀ C : ℝ, 1 ≤ C →
    (∀ k : ℕ, 1 ≤ k → k < L → EnergyUpperBoundAt P Y C k) →
    ∀ A : Finset ℤ, Admissible (P.blockScale * L) A →
      C * (L : ℝ) ^ (-P.decay) * density (P.blockScale * L) A ^ P.densityExponent < Y L A →
      Y L A ≤ q L * Y L A +
        E * (L : ℝ) ^ (-P.cancellationDecay) * density (P.blockScale * L) A

variable {P}

/-- **The induction of `thm:density:induction`, scalar form**, at the exponents `P`: reflection,
the global moment bound and a raw comparison whose coefficient tends to `θ < 1` give the energy
bounds (`Sarkozy.scaledEnergyEstimate_of_rawComparison` in general). Finite initialization
and the absorption of the density-linear errors are proved. -/
theorem scaledEnergyEstimate_of_rawComparison (hP : P.Valid)
    {Y : ℕ → Finset ℤ → ℝ} {M E θ : ℝ} {q : ℕ → ℝ}
    (hM : 0 < M) (hE : 0 ≤ E) (hθ : θ < 1)
    (hreflection : ∀ L : ℕ, 1 ≤ L → ∀ A : Finset ℤ,
      Admissible (P.blockScale * L) A → density (P.blockScale * L) A ^ slots ≤ Y L A)
    (hglobal : GlobalMomentBound P Y M) (hrec : RawComparison P Y q E)
    (hq : Tendsto q atTop (𝓝 θ)) : ScaledEnergyEstimate P Y := by
  let coefficient : ℕ → ℝ := fun L =>
    E * M ^ P.densityRatio * (L : ℝ) ^ (-P.relativeErrorDecay)
  have hvanish : Tendsto coefficient atTop (𝓝 0) := by
    have hp := (tendsto_rpow_neg_atTop hP.relativeErrorDecay_pos).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
    simpa only [coefficient, Function.comp_def, mul_zero] using
      hp.const_mul (E * M ^ P.densityRatio)
  have hlimit : Tendsto (fun L => q L + coefficient L) atTop (𝓝 θ) := by
    simpa only [add_zero] using hq.add hvanish
  obtain ⟨L₀, hL₀⟩ := eventually_atTop.mp (hrec.and (hlimit.eventually_lt_const hθ))
  have hzero : ∀ L : ℕ, 1 ≤ L → Y L ∅ ≤ 0 := by
    intro L hL
    simpa only [density_empty, zero_pow (by decide : 2 ≠ 0), mul_zero] using
      hglobal L hL ∅ (admissible_empty _)
  apply scaledEnergyEstimate_of_uniform_contraction hP (q := θ) (L₀ := L₀)
    (error := fun L _ => q L - θ + coefficient L) hzero hreflection
  · intro C hC L hL hlarge ih A hA hcounter
    have hδ : 0 < density (P.blockScale * L) A := by
      by_contra! hnonpos
      have hz := le_antisymm hnonpos (density_nonneg _ _)
      have hy : Y L A ≤ 0 := by
        simpa only [hz, zero_pow (by decide : 2 ≠ 0), mul_zero] using hglobal L hL A hA
      have hb : 0 ≤ C * (L : ℝ) ^ (-P.decay) *
          density (P.blockScale * L) A ^ P.densityExponent :=
        mul_nonneg (mul_nonneg (zero_le_one.trans hC)
          (Real.rpow_nonneg (Nat.cast_nonneg _) _))
          (Real.rpow_nonneg (density_nonneg _ _) _)
      linarith
    have hLpos : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
    have herr := relative_error_bound hP hδ hM hLpos hC hE hcounter (hglobal L hL A hA)
    have hraw := (hL₀ L hlarge).1 C hC ih A hA hcounter
    calc
      Y L A ≤ q L * Y L A + E * (L : ℝ) ^ (-P.cancellationDecay) *
          density (P.blockScale * L) A := hraw
      _ ≤ q L * Y L A + coefficient L * Y L A := add_le_add le_rfl herr
      _ = _ := by ring
  · intro L _ hlarge A _
    have h := (hL₀ L hlarge).2
    linarith

/-- The raw-comparison endgame at the exponents `P`: `s(N) ≤ C N^{1 − a/(72 − ϑ)}` from
reflection, the global moment bound and a raw comparison with limit coefficient `θ < 1`. -/
theorem powerSavingBound_of_rawComparison (hP : P.Valid)
    {Y : ℕ → Finset ℤ → ℝ} {M E θ : ℝ} {q : ℕ → ℝ}
    (hM : 0 < M) (hE : 0 ≤ E) (hθ : θ < 1)
    (hreflection : ∀ L : ℕ, 1 ≤ L → ∀ A : Finset ℤ,
      Admissible (P.blockScale * L) A → density (P.blockScale * L) A ^ slots ≤ Y L A)
    (hglobal : GlobalMomentBound P Y M) (hrec : RawComparison P Y q E)
    (hq : Tendsto q atTop (𝓝 θ)) : PowerSavingBound P :=
  powerSavingBound_of_scaledEnergyEstimate hP
    (scaledEnergyEstimate_of_rawComparison hP hM hE hθ hreflection hglobal hrec hq)

end Sarkozy.Param
