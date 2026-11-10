module

public import Sarkozy.Envelopes.Background
public import Sarkozy.Envelopes.OrbitCoupon

@[expose] public section

/-!
# Positive joint envelopes: the class bound (`thm:envelopes`)

`paper/sections/23_envelopes.tex`, `thm:envelopes` (i)–(iii), the assembly of the proof (Steps 1–4)
and the properties of the class bound `eq:envelope-class-bound`.

**Form (abstract, with the paper's hypotheses).** The energies of the proof enter as real numbers,
one family per selection `ω` of the class `𝒞`:
* `I ω`, the term `I_ω` of the record expansion, equal to `π̃ (Lead ω + Rem ω)` with `π̃` the common
  product of the raw-arm coefficients (`(N4)`) and `Lead ω`, `Rem ω` the energies of the leading
  star tensor and of the remainder (`ζ_ω = π̃^arm_ω [L_ω + Υ_ω]_ω`);
* Step 1 (`(P5)`, `(E1)` and `eq:oct24:star-tensor-error`): `|Rem ω| ≤ υ_ω (B + z) C_X Y`;
* Step 2 (`lem:oct24:mask-schur`(a), `(P5)`): `|Lead ω| ≤ Y^Ñ[[D_ω]]`;
* Step 3 (`lem:orbit-coupon`):
  `Y^Ñ[[D_ω]] ≤ Y^{Ñ₀}[[D_ω]] + (M_ω R_err - M_{h,ω} e^{tU} tδ + z) C_X Y`;
* Step 4 (`lem:reflection-averaging`(d), and (iii) with `lem:oct24:invariant-background`(v)):
  `∑ Y^{Ñ₀}[[D_ω]] = ∑ Y^{Ñ₀}[[D̄_ω]] ≤ |𝒞| (κ_H e^{U_0} - (κ_H - κ_b) e^{tU} + z) C_X Y`.
Here `z ≥ 0` is the uniform `o(1)` and `M`, `M^inv` are the class averages of `M_ω`, `M_{h,ω}`.

**Main results.**
* `envelope_class_sum`: (i), `∑_𝒞 |I_ω| ≤ ∑_𝒞 (φ_ω + error_ω)`, with
  `φ_ω = C_{n,m} π^arm_ω + B(π^tot_ω - π^lead_ω)`, `π^arm_ω = π̃ C_X` and
  `π^tot_ω - π^lead_ω = π̃ υ_ω C_X` (`remainder_monomial` in `StarTensor`);
* `classCost_ge`: the bracket is nonnegative, indeed at least `κ_b e^{tU}`;
* `classCost_uniform`: (ii), the case `κ_b = κ_H`, `M^inv = 0`;
* `classCost_mono`, `classBound_mono`: (iii), monotonicity in `κ_H, κ_b, M, R_err, U_0` and `B`.
-/

namespace Sarkozy.Envelopes

open Finset

/-- The base cost `C_{n,m} = κ_H e^{U_0} - (κ_H - κ_b) e^{tU_inv} + M R_err - M^inv e^{tU_inv} tδ_s`
per raw-arm monomial (`eq:envelope-class-bound`, `cor:envelope-costs`). -/
noncomputable def classCost (κH κb M Minv U0 tU Rerr tδ : ℝ) : ℝ :=
  κH * Real.exp U0 - (κH - κb) * Real.exp tU + M * Rerr - Minv * Real.exp tU * tδ

/-- The class bound `φ_ω = C_{n,m} π^arm_ω + B (π^tot_ω - π^lead_ω)` (`eq:envelope-class-bound`). -/
noncomputable def classBound (cost B πarm πtot πlead : ℝ) : ℝ := cost * πarm + B * (πtot - πlead)

/-- **`thm:envelopes`(i), the bracket is nonnegative.** Under the gates `0 ≤ κ_b ≤ κ_H`,
`tU ≤ U_0` and `M^inv e^{tU} tδ ≤ M R_err` (`lem:orbit-coupon`(iv)), `C_{n,m} ≥ κ_b e^{tU} ≥ 0`. -/
theorem classCost_ge {κH κb M Minv U0 tU Rerr tδ : ℝ} (hκb : 0 ≤ κb) (hκ : κb ≤ κH)
    (hU : tU ≤ U0) (hcoup : Minv * Real.exp tU * tδ ≤ M * Rerr) :
    κb * Real.exp tU ≤ classCost κH κb M Minv U0 tU Rerr tδ ∧
      0 ≤ classCost κH κb M Minv U0 tU Rerr tδ := by
  have h := (backgroundCost_mono (κH := κH) (κH' := κH) (κb := κb) (κb' := κb) (U0 := U0)
    (U0' := U0) hU le_rfl le_rfl le_rfl (hκb.trans hκ)).2
  unfold backgroundCost at h
  unfold classCost
  have : 0 ≤ κb * Real.exp tU := mul_nonneg hκb (Real.exp_pos _).le
  constructor <;> linarith

/-- **`thm:envelopes`(ii), the uniform cost** (`eq:oct24:envelope-cost`): without the invariant
split and the coupon, `C = κ_H e^{U_0} + M R_err`. -/
theorem classCost_uniform (κH M U0 tU Rerr tδ : ℝ) :
    classCost κH κH M 0 U0 tU Rerr tδ = κH * Real.exp U0 + M * Rerr := by
  unfold classCost; ring

/-- **`thm:envelopes`(iii), monotonicity of the cost.** For `tU ≤ U_0`, `κ_H ≥ 0`, `M ≥ 0` and
`R_err ≥ 0`, the cost is nondecreasing in `κ_H`, `κ_b`, `M`, `R_err` and `U_0`. -/
theorem classCost_mono {κH κH' κb κb' M M' Minv U0 U0' tU Rerr Rerr' tδ : ℝ} (hU : tU ≤ U0)
    (hH : κH ≤ κH') (hb : κb ≤ κb') (hM : M ≤ M') (hR : Rerr ≤ Rerr') (hU' : U0 ≤ U0')
    (hκH : 0 ≤ κH) (hM0 : 0 ≤ M) (hR0 : 0 ≤ Rerr) :
    classCost κH κb M Minv U0 tU Rerr tδ ≤ classCost κH' κb' M' Minv U0' tU Rerr' tδ := by
  have h := (backgroundCost_mono (κb := κb) (κb' := κb') hU hH hb hU' hκH).1
  unfold backgroundCost at h
  unfold classCost
  have : M * Rerr ≤ M' * Rerr' := mul_le_mul hM hR hR0 (hM0.trans hM)
  linarith

/-- **`thm:envelopes`(iii), monotonicity of the class bound** in the cost and in `B`, for
`π^arm ≥ 0` and `π^lead ≤ π^tot`. -/
theorem classBound_mono {cost cost' B B' πarm πtot πlead : ℝ} (hc : cost ≤ cost') (hB : B ≤ B')
    (harm : 0 ≤ πarm) (hrem : πlead ≤ πtot) :
    classBound cost B πarm πtot πlead ≤ classBound cost' B' πarm πtot πlead := by
  unfold classBound
  have h1 : cost * πarm ≤ cost' * πarm := mul_le_mul_of_nonneg_right hc harm
  have h2 : B * (πtot - πlead) ≤ B' * (πtot - πlead) :=
    mul_le_mul_of_nonneg_right hB (by linarith)
  linarith

/-- **`thm:envelopes`(i), the reduction (abstract assembly of Steps 1–4).** Let `𝒞` be a finite
class of selections with the common raw-arm product `π̃ ≥ 0` (`(N4)`), and suppose the energies of
the proof satisfy Steps 1–4 (see the module docstring), with the class averages
`|𝒞| M = ∑ M_ω` and `|𝒞| M^inv = ∑ M_{h,ω}`. Then
`∑_𝒞 |I_ω| ≤ ∑_𝒞 [classBound C_{n,m} B (π̃ C_X) (π̃ C_X (ℓ + υ_ω)) (π̃ C_X ℓ)] Y`
`+ ∑_𝒞 π̃ (2 + υ_ω) z C_X Y`
for any `ℓ` (the leading part cancels in `π^tot - π^lead`); the last sum is the `o(1)` term. -/
theorem envelope_class_sum {Ω : Type*} (𝒞 : Finset Ω) (I Lead Rem YN YN0 YN0bar υ Mω Mh : Ω → ℝ)
    {π CX Y B z κH κb M Minv U0 tU Rerr tδ ℓ : ℝ} (hπ : 0 ≤ π)
    (hI : ∀ ω ∈ 𝒞, I ω = π * (Lead ω + Rem ω))
    (hstep1 : ∀ ω ∈ 𝒞, |Rem ω| ≤ υ ω * (B + z) * CX * Y)
    (hstep2 : ∀ ω ∈ 𝒞, |Lead ω| ≤ YN ω)
    (hstep3 : ∀ ω ∈ 𝒞, YN ω ≤ YN0 ω + (Mω ω * Rerr - Mh ω * Real.exp tU * tδ + z) * CX * Y)
    (hstep4a : ∑ ω ∈ 𝒞, YN0 ω = ∑ ω ∈ 𝒞, YN0bar ω)
    (hstep4b : ∑ ω ∈ 𝒞, YN0bar ω ≤
      (𝒞.card : ℝ) * (κH * Real.exp U0 - (κH - κb) * Real.exp tU + z) * CX * Y)
    (hM : ∑ ω ∈ 𝒞, Mω ω = (𝒞.card : ℝ) * M) (hMinv : ∑ ω ∈ 𝒞, Mh ω = (𝒞.card : ℝ) * Minv) :
    ∑ ω ∈ 𝒞, |I ω| ≤
      ∑ ω ∈ 𝒞, classBound (classCost κH κb M Minv U0 tU Rerr tδ) B (π * CX)
          (π * CX * (ℓ + υ ω)) (π * CX * ℓ) * Y +
        ∑ ω ∈ 𝒞, π * (2 + υ ω) * z * CX * Y := by
  -- per selection
  have hper : ∀ ω ∈ 𝒞, |I ω| ≤ π * (YN0 ω + (Mω ω * Rerr - Mh ω * Real.exp tU * tδ + z) * CX * Y
      + υ ω * (B + z) * CX * Y) := by
    intro ω hω
    rw [hI ω hω, abs_mul, abs_of_nonneg hπ]
    refine mul_le_mul_of_nonneg_left ?_ hπ
    calc |Lead ω + Rem ω| ≤ |Lead ω| + |Rem ω| := abs_add_le _ _
      _ ≤ _ := by linarith [hstep2 ω hω, hstep3 ω hω, hstep1 ω hω]
  have hsum := sum_le_sum hper
  have e1 : ∑ ω ∈ 𝒞, (Mω ω * Rerr - Mh ω * Real.exp tU * tδ) =
      (𝒞.card : ℝ) * (M * Rerr - Minv * Real.exp tU * tδ) := by
    rw [sum_sub_distrib, ← sum_mul, ← sum_mul, ← sum_mul, hM, hMinv]; ring
  have e2 : ∑ ω ∈ 𝒞, π * (YN0 ω + (Mω ω * Rerr - Mh ω * Real.exp tU * tδ + z) * CX * Y +
      υ ω * (B + z) * CX * Y) = π * ∑ ω ∈ 𝒞, YN0 ω +
        π * ((∑ ω ∈ 𝒞, (Mω ω * Rerr - Mh ω * Real.exp tU * tδ)) * CX * Y) +
        ∑ ω ∈ 𝒞, π * (z * CX * Y + υ ω * (B + z) * CX * Y) := by
    rw [sum_mul, sum_mul, mul_sum, mul_sum, ← sum_add_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun ω _ => ?_
    ring
  rw [e2, e1, hstep4a] at hsum
  have hmain : π * ∑ ω ∈ 𝒞, YN0bar ω ≤
      π * ((𝒞.card : ℝ) * (κH * Real.exp U0 - (κH - κb) * Real.exp tU + z) * CX * Y) :=
    mul_le_mul_of_nonneg_left hstep4b hπ
  have e3 : ∑ ω ∈ 𝒞, classBound (classCost κH κb M Minv U0 tU Rerr tδ) B (π * CX)
        (π * CX * (ℓ + υ ω)) (π * CX * ℓ) * Y + ∑ ω ∈ 𝒞, π * (2 + υ ω) * z * CX * Y =
      π * ((𝒞.card : ℝ) * (κH * Real.exp U0 - (κH - κb) * Real.exp tU + z) * CX * Y) +
        π * ((𝒞.card : ℝ) * (M * Rerr - Minv * Real.exp tU * tδ) * CX * Y) +
        ∑ ω ∈ 𝒞, π * (z * CX * Y + υ ω * (B + z) * CX * Y) := by
    simp only [classBound, classCost]
    rw [← sum_add_distrib]
    have hc : ∀ ω ∈ 𝒞, ((κH * Real.exp U0 - (κH - κb) * Real.exp tU + M * Rerr -
          Minv * Real.exp tU * tδ) * (π * CX) + B * (π * CX * (ℓ + υ ω) - π * CX * ℓ)) * Y +
          π * (2 + υ ω) * z * CX * Y =
        (π * (κH * Real.exp U0 - (κH - κb) * Real.exp tU + z) * CX * Y) +
          (π * (M * Rerr - Minv * Real.exp tU * tδ) * CX * Y) +
          π * (z * CX * Y + υ ω * (B + z) * CX * Y) := by
      intro ω _; ring
    rw [sum_congr rfl hc, sum_add_distrib, sum_add_distrib, sum_const, sum_const,
      nsmul_eq_mul, nsmul_eq_mul]
    ring
  rw [e3]
  linarith

/-- **`cor:envelope-costs`, the gates** (partial: the class list, the savings `D_{n,m}` and their
positivity, certified by the closing, are not formalized). For every class, if `0 < κ_b ≤ κ_H`,
`0 ≤ t U_inv ≤ U_0`, `0 ≤ M^inv ≤ M`, `0 ≤ tδ_s ≤ d`, `R_err ≥ 2 e^{U_0} d` and the gain is
below `1`, then `C_{n,m} ≥ κ_b e^{tU_inv} > 0`, every coupon is at most `M R_err`, and the credit
`κ_b g` is below `C_{n,m}`. -/
theorem envelope_costs_gates {κH κb M Minv U0 tU Rerr tδ d g : ℝ} (hκb : 0 < κb)
    (hκ : κb ≤ κH) (htU : 0 ≤ tU) (hU : tU ≤ U0) (hMinv0 : 0 ≤ Minv) (hMinv : Minv ≤ M)
    (htd0 : 0 ≤ tδ) (htd : tδ ≤ d) (hR : 2 * Real.exp U0 * d ≤ Rerr) (hg : g < 1) :
    0 < κb * Real.exp tU ∧ κb * Real.exp tU ≤ classCost κH κb M Minv U0 tU Rerr tδ ∧
      Minv * Real.exp tU * tδ ≤ M * Rerr ∧ κb * g < classCost κH κb M Minv U0 tU Rerr tδ := by
  have hX : Real.exp tU ≤ Real.exp U0 := Real.exp_le_exp.2 hU
  have hcoup := (orbit_coupon_gate hMinv0 hMinv (Real.exp_pos tU).le hX htd0 htd hR).2
  have hc : Minv * Real.exp tU * tδ ≤ M * Rerr := by linarith
  have hge := (classCost_ge hκb.le hκ hU hc).1
  have h1 : 1 ≤ Real.exp tU := Real.one_le_exp htU
  have hpos : 0 < κb * Real.exp tU := mul_pos hκb (Real.exp_pos _)
  have hgk : κb * g < κb * Real.exp tU := by nlinarith
  exact ⟨hpos, hge, hc, hgk.trans_le hge⟩

end Sarkozy.Envelopes
