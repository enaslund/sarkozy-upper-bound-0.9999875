module

public import Sarkozy.Envelopes.Theorem

@[expose] public section

/-!
# The class bounds at energy level from the steps of their proofs (real-number form)

`paper/sections/23_envelopes.tex`, `thm:envelopes`(i) (Steps 1–4 of its proof),
`cor:envelope-costs`, `lem:oct24:invariant-background`(v), `lem:orbit-coupon`;
`paper/sections/22_variance.tex`, `prop:background-variance`(a), `lem:var-gain`(b),
`cor:var-classes`, `cor:variance:final`(i).

W2's `Envelopes.envelope_class_sum` assembles Steps 1–4 of `thm:envelopes` for a class whose
selections share one raw-arm product `π̃` and one `C_X`, with no remainders, in evaluated form.
W1's `Variance.class_cost_scalar` is the class-cost step of `prop:background-variance`(a) for a
class with one `γ` and one `C_X`, with no remainders. The class bounds of the construction need
both **per selection** (the prices `π̃^arm_ω`, `C_X`, `γ_ω` vary over a class), **with the
remainders** of `def:robust`, and, for the joint closing, **at energy level**: Step 4 ends at the
energies `∑_j w_j Z_j` of the labelled positive diagonals of the background expansion, not at
their upper prices. This file proves these forms (the arguments are W2's and W1's).

* `envelope_class_energy`: Steps 1–4 with weights `π̃_ω`, `C_X(ω)`, remainders, and Step 4 at
  energy level: `∑ |I_ω| ≤ W_Z + (M R_err − M^inv e^{tU} tδ) (∑ π̃ C_X) Y + B (∑ π̃ υ C_X) Y
  + z (∑ π̃ (2 + υ) C_X) Y + rem`. With `π̃`, `C_X` constant, no remainders and Step 4 evaluated
  (`W_Z = |𝒞|(κ_H e^{U_0} − (κ_H − κ_b) e^{tU}) π̃ C_X Y`) this is W2's `envelope_class_sum`.
* `variance_class_energy`: W1's class-cost step with weights and remainders:
  `∑ |I_s| ≤ (B − [b̃ − R_*]_+ + 3z)(∑ γ C_X) Y + rem`.
* `EnvStepsAt`, `VarStepsAt`: the data of these steps for one class at one counterexample, with
  the identification of the residual `ρ` and of the error weights; `EnvStepsAt.bound`,
  `VarStepsAt.bound` give the class bound in the form of `ClassEnergyData.energy`.
* `consistent_degree`: the consistency of a degree class with its class bound
  `C_n π^arm + B'(π^{lead+rem} − π^lead)`, from the background gate
  (`lem:oct24:invariant-background`(v): `∑_j w_j u_j ≤ (κ_H e^{U_0} − (κ_H − κ_b) e^{tU}) ∑ π^arm`),
  `π̃ C_X = π^arm`, `π̃ υ C_X ≤ π^{lead+rem} − π^lead` (B4's finding 2) and
  `classCost ≤ C_n`.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.ClassInputsPaper

open Sarkozy.Envelopes

/-! ## The envelope classes -/

/-- **`thm:envelopes`(i) at energy level, per selection, with remainders** (the assembly of Steps
1–4 of its proof; W2's `envelope_class_sum` with weights). For a class `𝒞` with raw-arm products
`π̃_ω ≥ 0` and `C_X(ω) ≥ 0`:
* (N4) `I_ω = π̃_ω (Lead_ω + Rem_ω)`;
* Step 1 (`(P5)`, `(E1)`, `eq:oct24:star-tensor-error`): `|Rem_ω| ≤ υ_ω (B + z) C_X Y + r₁`;
* Step 2 (`lem:oct24:mask-schur`(a), `(P5)`): `|Lead_ω| ≤ Y^Ñ[[D_ω]]`;
* Step 3 (`lem:orbit-coupon`): `Y^Ñ ≤ Y^{Ñ₀} + (M_ω R_err − M_{h,ω} e^{tU} tδ + z) C_X Y + r₃`;
* Step 4 (`lem:reflection-averaging`(d), the background expansion of (iii)), at energy level:
  `∑ π̃ Y^{Ñ₀}[[D_ω]] ≤ W_Z + z (∑ π̃ C_X) Y + r₄`, `W_Z = ∑_j w_j Z_j`;
* the class averages: `∑ π̃ C_X M_ω ≤ M ∑ π̃ C_X`, `M^inv ∑ π̃ C_X ≤ ∑ π̃ C_X M_{h,ω}`. -/
theorem envelope_class_energy {Ω : Type*} (𝒞 : Finset Ω)
    (I Lead Rem YN YN0 υ Mω Mh wt CX r₁ r₃ : Ω → ℝ)
    {Y B z M Minv Rerr tU tδ WZ r₄ : ℝ}
    (hwt : ∀ ω ∈ 𝒞, 0 ≤ wt ω) (hY : 0 ≤ Y) (hR : 0 ≤ Rerr) (htδ : 0 ≤ tδ)
    (hI : ∀ ω ∈ 𝒞, I ω = wt ω * (Lead ω + Rem ω))
    (hstep1 : ∀ ω ∈ 𝒞, |Rem ω| ≤ υ ω * (B + z) * CX ω * Y + r₁ ω)
    (hstep2 : ∀ ω ∈ 𝒞, |Lead ω| ≤ YN ω)
    (hstep3 : ∀ ω ∈ 𝒞,
      YN ω ≤ YN0 ω + (Mω ω * Rerr - Mh ω * Real.exp tU * tδ + z) * CX ω * Y + r₃ ω)
    (hstep4 : ∑ ω ∈ 𝒞, wt ω * YN0 ω ≤ WZ + z * (∑ ω ∈ 𝒞, wt ω * CX ω) * Y + r₄)
    (hM : ∑ ω ∈ 𝒞, wt ω * CX ω * Mω ω ≤ M * ∑ ω ∈ 𝒞, wt ω * CX ω)
    (hMinv : Minv * ∑ ω ∈ 𝒞, wt ω * CX ω ≤ ∑ ω ∈ 𝒞, wt ω * CX ω * Mh ω) :
    ∑ ω ∈ 𝒞, |I ω| ≤ WZ + (M * Rerr - Minv * Real.exp tU * tδ) * (∑ ω ∈ 𝒞, wt ω * CX ω) * Y +
      B * (∑ ω ∈ 𝒞, wt ω * υ ω * CX ω) * Y + z * (∑ ω ∈ 𝒞, wt ω * (2 + υ ω) * CX ω) * Y +
      (∑ ω ∈ 𝒞, wt ω * (r₁ ω + r₃ ω) + r₄) := by
  set e := Real.exp tU * tδ with he
  have he0 : 0 ≤ e := mul_nonneg (Real.exp_pos _).le htδ
  -- per selection
  have hper : ∀ ω ∈ 𝒞, |I ω| ≤ wt ω * YN0 ω + (Rerr * Y) * (wt ω * CX ω * Mω ω) -
      (e * Y) * (wt ω * CX ω * Mh ω) + (z * Y) * (wt ω * CX ω) +
      (B * Y) * (wt ω * υ ω * CX ω) + (z * Y) * (wt ω * υ ω * CX ω) +
      wt ω * (r₁ ω + r₃ ω) := by
    intro ω hω
    have h0 := hwt ω hω
    have hb : |Lead ω + Rem ω| ≤ YN0 ω + (Mω ω * Rerr - Mh ω * e + z) * CX ω * Y + r₃ ω +
        (υ ω * (B + z) * CX ω * Y + r₁ ω) := by
      have := abs_add_le (Lead ω) (Rem ω)
      have h3 := hstep3 ω hω
      rw [show Mh ω * Real.exp tU * tδ = Mh ω * e by rw [he]; ring] at h3
      linarith [hstep1 ω hω, hstep2 ω hω]
    rw [hI ω hω, abs_mul, abs_of_nonneg h0]
    calc wt ω * |Lead ω + Rem ω|
        ≤ wt ω * (YN0 ω + (Mω ω * Rerr - Mh ω * e + z) * CX ω * Y + r₃ ω +
          (υ ω * (B + z) * CX ω * Y + r₁ ω)) := mul_le_mul_of_nonneg_left hb h0
      _ = _ := by ring
  have hsum := sum_le_sum hper
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at hsum
  have h2 : ∑ ω ∈ 𝒞, wt ω * (2 + υ ω) * CX ω =
      2 * ∑ ω ∈ 𝒞, wt ω * CX ω + ∑ ω ∈ 𝒞, wt ω * υ ω * CX ω := by
    rw [mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun ω _ => by ring
  have hRY : 0 ≤ Rerr * Y := mul_nonneg hR hY
  have heY : 0 ≤ e * Y := mul_nonneg he0 hY
  have h5 := mul_le_mul_of_nonneg_left hM hRY
  have h6 := mul_le_mul_of_nonneg_left hMinv heY
  rw [h2]
  nlinarith [hstep4, h5, h6, hsum]

/-- **The data of Steps 1–4 for one degree class at one counterexample**, with the residual
`ρ` (`∑ ρ ≥ (M R_err − M^inv e^{tU} tδ) ∑ π̃ C_X + B ∑ π̃ υ C_X`, the coupling and remainder
parts of the class bound), the error weights (`π̃ (2 + υ) C_X ≤ K π_ω`, `thm:envelopes`(i):
the raw-arm, leading and total prices are at most `2^{|X|} π_ω`) and the remainders (`≤ ∑ rr`). -/
structure EnvStepsAt {Ω : Type*} (𝒞 : Finset Ω) (I π ρ rr : Ω → ℝ) (WZ Y z K : ℝ) where
  Lead : Ω → ℝ
  Rem : Ω → ℝ
  YN : Ω → ℝ
  YN0 : Ω → ℝ
  υ : Ω → ℝ
  Mω : Ω → ℝ
  Mh : Ω → ℝ
  wt : Ω → ℝ
  CX : Ω → ℝ
  r₁ : Ω → ℝ
  r₃ : Ω → ℝ
  r₄ : ℝ
  B : ℝ
  M : ℝ
  Minv : ℝ
  Rerr : ℝ
  tU : ℝ
  tδ : ℝ
  hwt : ∀ ω ∈ 𝒞, 0 ≤ wt ω
  hR : 0 ≤ Rerr
  htδ : 0 ≤ tδ
  /-- (N4): `ζ_ω = π̃^arm_ω [L_ω + Υ_ω]_ω`. -/
  hI : ∀ ω ∈ 𝒞, I ω = wt ω * (Lead ω + Rem ω)
  /-- Step 1: `(P5)`, `(E1)`, `eq:oct24:star-tensor-error`. -/
  step1 : ∀ ω ∈ 𝒞, |Rem ω| ≤ υ ω * (B + z) * CX ω * Y + r₁ ω
  /-- Step 2: `lem:oct24:mask-schur`(a), `(P5)`. -/
  step2 : ∀ ω ∈ 𝒞, |Lead ω| ≤ YN ω
  /-- Step 3: `lem:orbit-coupon`. -/
  step3 : ∀ ω ∈ 𝒞,
    YN ω ≤ YN0 ω + (Mω ω * Rerr - Mh ω * Real.exp tU * tδ + z) * CX ω * Y + r₃ ω
  /-- Step 4: `lem:reflection-averaging`(d) and the background expansion, at energy level. -/
  step4 : ∑ ω ∈ 𝒞, wt ω * YN0 ω ≤ WZ + z * (∑ ω ∈ 𝒞, wt ω * CX ω) * Y + r₄
  /-- The class averages of the coupling masses (`lem:orbit-coupon`). -/
  hM : ∑ ω ∈ 𝒞, wt ω * CX ω * Mω ω ≤ M * ∑ ω ∈ 𝒞, wt ω * CX ω
  hMinv : Minv * ∑ ω ∈ 𝒞, wt ω * CX ω ≤ ∑ ω ∈ 𝒞, wt ω * CX ω * Mh ω
  /-- The residual carries the coupling and remainder parts of the class bound. -/
  hρ : (M * Rerr - Minv * Real.exp tU * tδ) * (∑ ω ∈ 𝒞, wt ω * CX ω) +
    B * (∑ ω ∈ 𝒞, wt ω * υ ω * CX ω) ≤ ∑ ω ∈ 𝒞, ρ ω
  /-- The error weights are dominated by the prices. -/
  hπ : ∀ ω ∈ 𝒞, wt ω * (2 + υ ω) * CX ω ≤ K * π ω
  /-- The remainders. -/
  hrr : ∑ ω ∈ 𝒞, wt ω * (r₁ ω + r₃ ω) + r₄ ≤ ∑ ω ∈ 𝒞, rr ω

/-- **The class bound at energy level of a degree class from its steps**:
`∑ |I_ω| ≤ W_Z + ∑ ((ρ_ω + zK π_ω) Y + rr_ω)`. -/
theorem EnvStepsAt.bound {Ω : Type*} {𝒞 : Finset Ω} {I π ρ rr : Ω → ℝ} {WZ Y z K : ℝ}
    (S : EnvStepsAt 𝒞 I π ρ rr WZ Y z K) (hY : 0 ≤ Y) (hz : 0 ≤ z) :
    ∑ ω ∈ 𝒞, |I ω| ≤ WZ + ∑ ω ∈ 𝒞, ((ρ ω + z * K * π ω) * Y + rr ω) := by
  have h := envelope_class_energy 𝒞 I S.Lead S.Rem S.YN S.YN0 S.υ S.Mω S.Mh S.wt S.CX S.r₁ S.r₃
    S.hwt hY S.hR S.htδ S.hI S.step1 S.step2 S.step3 S.step4 S.hM S.hMinv
  have hπs : z * (∑ ω ∈ 𝒞, S.wt ω * (2 + S.υ ω) * S.CX ω) * Y ≤
      z * K * (∑ ω ∈ 𝒞, π ω) * Y := by
    have h1 : ∑ ω ∈ 𝒞, S.wt ω * (2 + S.υ ω) * S.CX ω ≤ K * ∑ ω ∈ 𝒞, π ω := by
      rw [mul_sum]
      exact sum_le_sum S.hπ
    have := mul_le_mul_of_nonneg_left h1 hz
    have := mul_le_mul_of_nonneg_right this hY
    linarith
  have hρY := mul_le_mul_of_nonneg_right S.hρ hY
  have e : ∑ ω ∈ 𝒞, ((ρ ω + z * K * π ω) * Y + rr ω) =
      (∑ ω ∈ 𝒞, ρ ω) * Y + z * K * (∑ ω ∈ 𝒞, π ω) * Y + ∑ ω ∈ 𝒞, rr ω := by
    have e1 : ∀ ω, (ρ ω + z * K * π ω) * Y + rr ω = ρ ω * Y + (z * K * Y) * π ω + rr ω :=
      fun ω => by ring
    rw [sum_congr rfl fun ω _ => e1 ω, sum_add_distrib, sum_add_distrib, ← sum_mul, ← mul_sum]
    ring
  rw [e]
  nlinarith [h, hπs, hρY, S.hrr]

/-- **The consistency of a degree class with its class bound** (`thm:envelopes`(i),
`cor:envelope-costs`, `lem:oct24:invariant-background`(v)): if the diagonals of the class,
evaluated at their upper prices, are at most the background part
`(κ_H e^{U_0} − (κ_H − κ_b) e^{tU}) ∑ π^arm` (`hbg`), the residual is at most the coupling and
remainder parts (`hρ`), `π̃ C_X = π^arm` and `0 ≤ π̃ υ C_X ≤ π^{lead+rem} − π^lead`, `B ≤ B'` and
`classCost ≤ C_n`, then `W_u + ∑ ρ ≤ ∑ (C_n π^arm + B'(π^{lead+rem} − π^lead))`. -/
theorem consistent_degree {Ω : Type*} (𝒞 : Finset Ω) (ρ parm plr pl wt CX υ : Ω → ℝ)
    {WU κH κb M Minv U0 tU Rerr tδ B B' Cn : ℝ}
    (hbg : WU ≤ (κH * Real.exp U0 - (κH - κb) * Real.exp tU) * ∑ ω ∈ 𝒞, parm ω)
    (hρ : ∑ ω ∈ 𝒞, ρ ω ≤ (M * Rerr - Minv * Real.exp tU * tδ) * (∑ ω ∈ 𝒞, wt ω * CX ω) +
      B * (∑ ω ∈ 𝒞, wt ω * υ ω * CX ω))
    (harm : ∀ ω ∈ 𝒞, wt ω * CX ω = parm ω) (hparm : ∀ ω ∈ 𝒞, 0 ≤ parm ω)
    (hυ0 : ∀ ω ∈ 𝒞, 0 ≤ wt ω * υ ω * CX ω) (hυ : ∀ ω ∈ 𝒞, wt ω * υ ω * CX ω ≤ plr ω - pl ω)
    (hB : B ≤ B') (hB0 : 0 ≤ B) (hC : classCost κH κb M Minv U0 tU Rerr tδ ≤ Cn) :
    WU + ∑ ω ∈ 𝒞, ρ ω ≤ ∑ ω ∈ 𝒞, (Cn * parm ω + B' * (plr ω - pl ω)) := by
  have hsarm : ∑ ω ∈ 𝒞, wt ω * CX ω = ∑ ω ∈ 𝒞, parm ω := sum_congr rfl harm
  rw [hsarm] at hρ
  have hp0 : 0 ≤ ∑ ω ∈ 𝒞, parm ω := sum_nonneg hparm
  have hυs : ∑ ω ∈ 𝒞, wt ω * υ ω * CX ω ≤ ∑ ω ∈ 𝒞, (plr ω - pl ω) := sum_le_sum hυ
  have hυs0 : 0 ≤ ∑ ω ∈ 𝒞, wt ω * υ ω * CX ω := sum_nonneg hυ0
  have h1 : B * ∑ ω ∈ 𝒞, wt ω * υ ω * CX ω ≤ B' * ∑ ω ∈ 𝒞, (plr ω - pl ω) :=
    mul_le_mul hB hυs hυs0 (hB0.trans hB)
  have h2 : classCost κH κb M Minv U0 tU Rerr tδ * ∑ ω ∈ 𝒞, parm ω ≤
      Cn * ∑ ω ∈ 𝒞, parm ω := mul_le_mul_of_nonneg_right hC hp0
  rw [sum_add_distrib, ← mul_sum, ← mul_sum]
  unfold classCost at h2
  nlinarith [hbg, hρ, h1, h2]

/-! ## The variance classes -/

/-- **The class-cost step of `prop:background-variance`(a) and `lem:var-gain`(b), per selection,
with remainders** (W1's `class_cost_scalar` with weights `γ_s`, `C_X(s)` and remainders). For each
selection `s` of a class `R`: `|I_s| ≤ γ_s (DN_s − JN_s)` (`lem:record:variance-interface`(i)),
`JN_s ≥ 0` ((E2)), `DN_s ≤ (B + z) C_X Y + r_D` ((E1)), `JO_s − (R_err + z) C_X Y − r_J ≤ JN_s`
(`lem:oct24:invariant-background`), and the restoration bound
`∑ γ JO ≥ (b̃ − z) (∑ γ C_X) Y − r₀` (`lem:record:restoration`, `lem:var-gain`(a)). Then
`∑ |I_s| ≤ (B − [b̃ − R_*]_+ + 3z)(∑ γ C_X) Y + ∑ γ (r_D + r_J) + r₀` for `R_err ≤ R_*`. -/
theorem variance_class_energy {Ω : Type*} (R : Finset Ω) (I DN JN JO γ CX rD rJ : Ω → ℝ)
    {Y Bf Rerr Rstar bt z r₀ : ℝ} (hγ : ∀ s ∈ R, 0 ≤ γ s) (hCX : ∀ s ∈ R, 0 ≤ CX s)
    (hY : 0 ≤ Y) (hz : 0 ≤ z) (hr₀ : 0 ≤ r₀) (hrJ : ∀ s ∈ R, 0 ≤ rJ s) (hRs : Rerr ≤ Rstar)
    (hI : ∀ s ∈ R, |I s| ≤ γ s * (DN s - JN s)) (hJN0 : ∀ s ∈ R, 0 ≤ JN s)
    (hDN : ∀ s ∈ R, DN s ≤ (Bf + z) * CX s * Y + rD s)
    (hJN : ∀ s ∈ R, JO s - (Rerr + z) * CX s * Y - rJ s ≤ JN s)
    (hres : (bt - z) * (∑ s ∈ R, γ s * CX s) * Y - r₀ ≤ ∑ s ∈ R, γ s * JO s) :
    ∑ s ∈ R, |I s| ≤ (Bf - max 0 (bt - Rstar) + 3 * z) * (∑ s ∈ R, γ s * CX s) * Y +
      (∑ s ∈ R, γ s * (rD s + rJ s) + r₀) := by
  have hS0 : 0 ≤ ∑ s ∈ R, γ s * CX s := sum_nonneg fun s hs => mul_nonneg (hγ s hs) (hCX s hs)
  have hSY : 0 ≤ (∑ s ∈ R, γ s * CX s) * Y := mul_nonneg hS0 hY
  have hγrJ : 0 ≤ ∑ s ∈ R, γ s * rJ s := sum_nonneg fun s hs => mul_nonneg (hγ s hs) (hrJ s hs)
  have esplit : ∑ s ∈ R, γ s * (rD s + rJ s) = ∑ s ∈ R, γ s * rD s + ∑ s ∈ R, γ s * rJ s := by
    rw [← sum_add_distrib]
    exact sum_congr rfl fun s _ => by ring
  by_cases hg : 0 ≤ bt - Rstar
  · rw [max_eq_right hg]
    have hper : ∀ s ∈ R, |I s| ≤ (Bf + Rerr + 2 * z) * Y * (γ s * CX s) - γ s * JO s +
        (γ s * rD s + γ s * rJ s) := by
      intro s hs
      have h1 := hI s hs
      have h2 : DN s - JN s ≤ (Bf + z) * CX s * Y + rD s - (JO s - (Rerr + z) * CX s * Y - rJ s) :=
        by linarith [hDN s hs, hJN s hs]
      have := mul_le_mul_of_nonneg_left h2 (hγ s hs)
      nlinarith
    have hsum := sum_le_sum hper
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum] at hsum
    rw [esplit]
    nlinarith [hres, hsum, hSY]
  · rw [max_eq_left (by linarith)]
    have hper : ∀ s ∈ R, |I s| ≤ (Bf + z) * Y * (γ s * CX s) + γ s * rD s := by
      intro s hs
      have h1 := hI s hs
      have h2 : DN s - JN s ≤ (Bf + z) * CX s * Y + rD s := by linarith [hDN s hs, hJN0 s hs]
      have := mul_le_mul_of_nonneg_left h2 (hγ s hs)
      nlinarith
    have hsum := sum_le_sum hper
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
    rw [esplit]
    nlinarith [hsum, hSY, hγrJ]

/-- **The data of the class-cost step for one variance class at one counterexample**, with the
residual (`(B − [b̃ − R_*]_+) ∑ γ C_X ≤ ∑ ρ`: the class cost `B − g` of `cor:variance:final`(i)),
the error weights (`3 γ C_X ≤ K π_ω`) and the remainders. -/
structure VarStepsAt {Ω : Type*} (R : Finset Ω) (I π ρ rr : Ω → ℝ) (WZ Y z K : ℝ) where
  DN : Ω → ℝ
  JN : Ω → ℝ
  JO : Ω → ℝ
  γ : Ω → ℝ
  CX : Ω → ℝ
  rD : Ω → ℝ
  rJ : Ω → ℝ
  r₀ : ℝ
  Bf : ℝ
  Rerr : ℝ
  Rstar : ℝ
  bt : ℝ
  hγ : ∀ s ∈ R, 0 ≤ γ s
  hCX : ∀ s ∈ R, 0 ≤ CX s
  hr₀ : 0 ≤ r₀
  hrJ : ∀ s ∈ R, 0 ≤ rJ s
  hRs : Rerr ≤ Rstar
  /-- `lem:record:variance-interface`(i). -/
  hI : ∀ s ∈ R, |I s| ≤ γ s * (DN s - JN s)
  /-- (E2). -/
  hJN0 : ∀ s ∈ R, 0 ≤ JN s
  /-- (E1) for the diagonals. -/
  hDN : ∀ s ∈ R, DN s ≤ (Bf + z) * CX s * Y + rD s
  /-- `lem:oct24:invariant-background`: the bracket `Ñ` against `Ñ₀`. -/
  hJN : ∀ s ∈ R, JO s - (Rerr + z) * CX s * Y - rJ s ≤ JN s
  /-- The restoration bound (`lem:record:restoration`, `lem:var-gain`(a), `cor:var-classes`). -/
  hres : (bt - z) * (∑ s ∈ R, γ s * CX s) * Y - r₀ ≤ ∑ s ∈ R, γ s * JO s
  /-- The variance class has no part on the diagonals beyond a nonnegative one. -/
  hWZ : 0 ≤ WZ
  /-- The residual carries the class cost `B − g`. -/
  hρ : (Bf - max 0 (bt - Rstar)) * (∑ s ∈ R, γ s * CX s) ≤ ∑ s ∈ R, ρ s
  /-- The error weights are dominated by the prices. -/
  hπ : ∀ s ∈ R, 3 * (γ s * CX s) ≤ K * π s
  /-- The remainders. -/
  hrr : ∑ s ∈ R, γ s * (rD s + rJ s) + r₀ ≤ ∑ s ∈ R, rr s

/-- **The class bound at energy level of a variance class from its class-cost step**. -/
theorem VarStepsAt.bound {Ω : Type*} {R : Finset Ω} {I π ρ rr : Ω → ℝ} {WZ Y z K : ℝ}
    (S : VarStepsAt R I π ρ rr WZ Y z K) (hY : 0 ≤ Y) (hz : 0 ≤ z) :
    ∑ ω ∈ R, |I ω| ≤ WZ + ∑ ω ∈ R, ((ρ ω + z * K * π ω) * Y + rr ω) := by
  have h := variance_class_energy R I S.DN S.JN S.JO S.γ S.CX S.rD S.rJ S.hγ S.hCX hY hz S.hr₀
    S.hrJ S.hRs S.hI S.hJN0 S.hDN S.hJN S.hres
  have hπs : 3 * z * (∑ s ∈ R, S.γ s * S.CX s) * Y ≤ z * K * (∑ s ∈ R, π s) * Y := by
    have h1 : 3 * ∑ s ∈ R, S.γ s * S.CX s ≤ K * ∑ s ∈ R, π s := by
      rw [mul_sum, mul_sum]
      exact sum_le_sum S.hπ
    have := mul_le_mul_of_nonneg_left h1 hz
    have := mul_le_mul_of_nonneg_right this hY
    linarith
  have hρY := mul_le_mul_of_nonneg_right S.hρ hY
  have e : ∑ ω ∈ R, ((ρ ω + z * K * π ω) * Y + rr ω) =
      (∑ ω ∈ R, ρ ω) * Y + z * K * (∑ ω ∈ R, π ω) * Y + ∑ ω ∈ R, rr ω := by
    have e1 : ∀ ω, (ρ ω + z * K * π ω) * Y + rr ω = ρ ω * Y + (z * K * Y) * π ω + rr ω :=
      fun ω => by ring
    rw [sum_congr rfl fun ω _ => e1 ω, sum_add_distrib, sum_add_distrib, ← sum_mul, ← mul_sum]
    ring
  rw [e]
  nlinarith [h, hπs, hρY, S.hrr, S.hWZ]

end Sarkozy.ClassInputsPaper
