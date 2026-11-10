module

public import Sarkozy.Cuts.Rows
public import Sarkozy.Peyre.Basic

/-!
# Cuts, III: restriction to an injectivity event (`lem:restriction`)

`13_cuts_correlations.tex`, `subsec:cuts:restriction`. Finite probability spaces `λ_X`, `λ_Y`.
Events `I_X`, `I_Y` have probabilities `P_X, P_Y > 0`, and `μ_X = λ_X(· | I_X)`,
`μ_Y = λ_Y(· | I_Y)` (`Sarkozy.Peyre.condLaw`). A kernel `S` on `X × Y` gives the forms
`⟨f, T_S h⟩ = kernelForm λ_X λ_Y S f h` and `⟨f, S_μ h⟩ = kernelForm μ_X μ_Y S f h`.
The embedding is `ι_X f = 1_{I_X} f / √P_X`.

* (a) `nrm_iota`, `expect_iota`, `ip_iota`, `iota_one`, `nrm_vX`, `expect_vX`, and
  `kernelForm_cond` (`S_μ = ι_X^* T_S ι_Y / √(P_X P_Y)`).
* (b) `restriction_full`, `restriction_centred`, `restriction_const_image`,
  `restriction_mass`.
* (c) `restriction_centred_I0`, `restriction_const_image_I0`.

The full-support hypotheses of the paper are not needed.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.Cuts

open Sarkozy Sarkozy.Recentering Sarkozy.Peyre

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- `ι f = 1_I f / √P`. -/
noncomputable def iota (lamX : FiniteLaw X) (I : X → Prop) (f : X → ℝ) : X → ℝ :=
  fun x => ind I x * f x / √(prob lamX I)

theorem expect_condLaw (lamX : FiniteLaw X) (I : X → Prop) (hP : 0 < prob lamX I) (u : X → ℝ) :
    (condLaw lamX I hP).expect u = lamX.expect (fun x => ind I x * u x) / prob lamX I :=
  cond_expect lamX I hP u

omit [Fintype X] in
theorem ind_sq (I : X → Prop) (x : X) : ind I x * ind I x = ind I x := by
  by_cases h : I x
  · rw [ind_of_pos h]; ring
  · rw [ind_of_neg h]; ring

/-- (a) `ι` is an isometry `L²(μ) → L²(λ)`. -/
theorem nrm_iota (lamX : FiniteLaw X) (I : X → Prop) (hP : 0 < prob lamX I) (f : X → ℝ) :
    nrm lamX (iota lamX I f) = nrm (condLaw lamX I hP) f := by
  unfold nrm ip
  congr 1
  rw [expect_condLaw]
  have hs : √(prob lamX I) * √(prob lamX I) = prob lamX I := Real.mul_self_sqrt hP.le
  have hs0 : √(prob lamX I) ≠ 0 := (Real.sqrt_pos.mpr hP).ne'
  unfold iota
  rw [eq_div_iff hP.ne', ← FiniteLaw.expect_mul_const]
  refine lamX.expect_congr (fun x => ?_)
  have hi := ind_sq I x
  set s := √(prob lamX I)
  rw [← hs]
  field_simp
  linear_combination (f x * f x) * hi

/-- (a) `E_λ ι f = √P E_μ f`; so `ι` maps `μ`-centred functions to `λ`-centred functions. -/
theorem expect_iota (lamX : FiniteLaw X) (I : X → Prop) (hP : 0 < prob lamX I) (f : X → ℝ) :
    lamX.expect (iota lamX I f) = √(prob lamX I) * (condLaw lamX I hP).expect f := by
  rw [expect_condLaw]
  unfold iota
  have hs : √(prob lamX I) * √(prob lamX I) = prob lamX I := Real.mul_self_sqrt hP.le
  have hs0 : √(prob lamX I) ≠ 0 := (Real.sqrt_pos.mpr hP).ne'
  rw [expect_div_const lamX (fun x => ind I x * f x)]
  set s := √(prob lamX I)
  rw [← hs]
  field_simp

/-- (a) The adjoint: `⟨ι f, g⟩_λ = √P ⟨f, g⟩_μ`, i.e. `ι^* g = √P g|_I`. -/
theorem ip_iota (lamX : FiniteLaw X) (I : X → Prop) (hP : 0 < prob lamX I) (f g : X → ℝ) :
    ip lamX (iota lamX I f) g = √(prob lamX I) * ip (condLaw lamX I hP) f g := by
  unfold ip
  have := expect_iota lamX I hP (fun x => f x * g x)
  rw [← this]
  unfold iota
  exact lamX.expect_congr (fun x => by ring)

/-- `v = ι 1 - √P`. -/
noncomputable def vEv (lamX : FiniteLaw X) (I : X → Prop) : X → ℝ :=
  fun x => iota lamX I (fun _ => 1) x - √(prob lamX I)

/-- (a) `ι 1 = √P 1 + v`. -/
theorem iota_one_eq (lamX : FiniteLaw X) (I : X → Prop) :
    iota lamX I (fun _ => 1) = √(prob lamX I) • (fun _ : X => (1 : ℝ)) + vEv lamX I := by
  funext x
  simp only [vEv, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_one]
  ring

/-- (a) `v` is centred. -/
theorem expect_vX (lamX : FiniteLaw X) (I : X → Prop) (hP : 0 < prob lamX I) :
    lamX.expect (vEv lamX I) = 0 := by
  unfold vEv
  rw [FiniteLaw.expect_sub, FiniteLaw.expect_const, expect_iota lamX I hP, expect_one, mul_one,
    sub_self]

/-- (a) `‖v‖ = √(1 - P)`. -/
theorem nrm_vX (lamX : FiniteLaw X) (I : X → Prop) (hP : 0 < prob lamX I) :
    nrm lamX (vEv lamX I) = √(1 - prob lamX I) := by
  unfold nrm ip
  congr 1
  have hs : √(prob lamX I) * √(prob lamX I) = prob lamX I := Real.mul_self_sqrt hP.le
  have hs0 : √(prob lamX I) ≠ 0 := (Real.sqrt_pos.mpr hP).ne'
  have hP0 : prob lamX I ≠ 0 := hP.ne'
  have e : (fun x => vEv lamX I x * vEv lamX I x) =
      fun x => (ind I x * (1 / prob lamX I - 2)) + prob lamX I := by
    funext x
    unfold vEv iota
    have hi := ind_sq I x
    set s := √(prob lamX I)
    rw [← hs]
    field_simp
    linear_combination hi
  rw [e, FiniteLaw.expect_add, FiniteLaw.expect_mul_const, FiniteLaw.expect_const]
  change prob lamX I * (1 / prob lamX I - 2) + prob lamX I = 1 - prob lamX I
  field_simp
  ring

/-- (a) `S_μ = ι_X^* T_S ι_Y / √(P_X P_Y)`. -/
theorem kernelForm_cond (lamX : FiniteLaw X) (lamY : FiniteLaw Y) (IX : X → Prop) (IY : Y → Prop)
    (hPX : 0 < prob lamX IX) (hPY : 0 < prob lamY IY) (S : X → Y → ℝ) (f : X → ℝ) (h : Y → ℝ) :
    kernelForm (condLaw lamX IX hPX) (condLaw lamY IY hPY) S f h =
      kernelForm lamX lamY S (iota lamX IX f) (iota lamY IY h) / √(prob lamX IX * prob lamY IY) := by
  rw [Real.sqrt_mul hPX.le]
  have hsX : √(prob lamX IX) * √(prob lamX IX) = prob lamX IX := Real.mul_self_sqrt hPX.le
  have hsY : √(prob lamY IY) * √(prob lamY IY) = prob lamY IY := Real.mul_self_sqrt hPY.le
  have hsX0 : √(prob lamX IX) ≠ 0 := (Real.sqrt_pos.mpr hPX).ne'
  have hsY0 : √(prob lamY IY) ≠ 0 := (Real.sqrt_pos.mpr hPY).ne'
  simp only [kernelForm, LinearMap.mk₂_apply, cond_weight, iota]
  rw [eq_div_iff (mul_ne_zero hsX0 hsY0), Finset.sum_mul]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  set sX := √(prob lamX IX)
  set sY := √(prob lamY IY)
  rw [← hsX, ← hsY]
  field_simp

/-- (b) `‖S_μ‖ ≤ ‖T_S‖ / √(P_X P_Y)`. -/
theorem restriction_full (lamX : FiniteLaw X) (lamY : FiniteLaw Y) (IX : X → Prop) (IY : Y → Prop)
    (hPX : 0 < prob lamX IX) (hPY : 0 < prob lamY IY) (S : X → Y → ℝ) {c : ℝ}
    (hT : ∀ f h, |kernelForm lamX lamY S f h| ≤ c * nrm lamX f * nrm lamY h) (f : X → ℝ) (h : Y → ℝ) :
    |kernelForm (condLaw lamX IX hPX) (condLaw lamY IY hPY) S f h| ≤
      c / √(prob lamX IX * prob lamY IY) * nrm (condLaw lamX IX hPX) f * nrm (condLaw lamY IY hPY) h := by
  rw [kernelForm_cond, abs_div, abs_of_pos (Real.sqrt_pos.mpr (mul_pos hPX hPY)),
    ← nrm_iota lamX IX hPX f, ← nrm_iota lamY IY hPY h]
  have := hT (iota lamX IX f) (iota lamY IY h)
  have hs := Real.sqrt_pos.mpr (mul_pos hPX hPY)
  rw [div_le_iff₀ hs]
  calc |kernelForm lamX lamY S (iota lamX IX f) (iota lamY IY h)|
      ≤ c * nrm lamX (iota lamX IX f) * nrm lamY (iota lamY IY h) := this
    _ = c / √(prob lamX IX * prob lamY IY) * nrm lamX (iota lamX IX f) * nrm lamY (iota lamY IY h) *
          √(prob lamX IX * prob lamY IY) := by field_simp

/-- (b) `‖P₀ S_μ P₀‖ ≤ ‖P₀ T_S P₀‖ / √(P_X P_Y)`. -/
theorem restriction_centred (lamX : FiniteLaw X) (lamY : FiniteLaw Y) (IX : X → Prop)
    (IY : Y → Prop) (hPX : 0 < prob lamX IX) (hPY : 0 < prob lamY IY) (S : X → Y → ℝ) {c : ℝ}
    (hT : ∀ f h, lamX.expect f = 0 → lamY.expect h = 0 →
      |kernelForm lamX lamY S f h| ≤ c * nrm lamX f * nrm lamY h)
    (f : X → ℝ) (h : Y → ℝ) (hf : (condLaw lamX IX hPX).expect f = 0)
    (hh : (condLaw lamY IY hPY).expect h = 0) :
    |kernelForm (condLaw lamX IX hPX) (condLaw lamY IY hPY) S f h| ≤
      c / √(prob lamX IX * prob lamY IY) * nrm (condLaw lamX IX hPX) f * nrm (condLaw lamY IY hPY) h := by
  rw [kernelForm_cond, abs_div, abs_of_pos (Real.sqrt_pos.mpr (mul_pos hPX hPY)),
    ← nrm_iota lamX IX hPX f, ← nrm_iota lamY IY hPY h]
  have hf' : lamX.expect (iota lamX IX f) = 0 := by rw [expect_iota lamX IX hPX, hf, mul_zero]
  have hh' : lamY.expect (iota lamY IY h) = 0 := by rw [expect_iota lamY IY hPY, hh, mul_zero]
  have := hT (iota lamX IX f) (iota lamY IY h) hf' hh'
  have hs := Real.sqrt_pos.mpr (mul_pos hPX hPY)
  rw [div_le_iff₀ hs]
  calc |kernelForm lamX lamY S (iota lamX IX f) (iota lamY IY h)|
      ≤ c * nrm lamX (iota lamX IX f) * nrm lamY (iota lamY IY h) := this
    _ = c / √(prob lamX IX * prob lamY IY) * nrm lamX (iota lamX IX f) * nrm lamY (iota lamY IY h) *
          √(prob lamX IX * prob lamY IY) := by field_simp

/-- (b) The constant image: for `μ_X`-centred `f`,
`|⟨f, S_μ 1⟩| ≤ (M'_X / √P_X + ‖P₀ T_S P₀‖ √((1 - P_Y)/(P_X P_Y))) ‖f‖_{μ_X}`. Here `M'_X`
bounds `|⟨ι_X f, T_S 1⟩|` over `μ_X`-centred `f`. -/
theorem restriction_const_image (lamX : FiniteLaw X) (lamY : FiniteLaw Y) (IX : X → Prop)
    (IY : Y → Prop) (hPX : 0 < prob lamX IX) (hPY : 0 < prob lamY IY) (S : X → Y → ℝ) {c M : ℝ}
    (hT : ∀ f h, lamX.expect f = 0 → lamY.expect h = 0 →
      |kernelForm lamX lamY S f h| ≤ c * nrm lamX f * nrm lamY h)
    (hM : ∀ f, (condLaw lamX IX hPX).expect f = 0 →
      |kernelForm lamX lamY S (iota lamX IX f) (fun _ => 1)| ≤ M * nrm (condLaw lamX IX hPX) f)
    (f : X → ℝ) (hf : (condLaw lamX IX hPX).expect f = 0) :
    |kernelForm (condLaw lamX IX hPX) (condLaw lamY IY hPY) S f (fun _ => 1)| ≤
      (M / √(prob lamX IX) + c * √((1 - prob lamY IY) / (prob lamX IX * prob lamY IY))) *
        nrm (condLaw lamX IX hPX) f := by
  set PX := prob lamX IX
  set PY := prob lamY IY
  have hsX := Real.sqrt_pos.mpr hPX
  have hsY := Real.sqrt_pos.mpr hPY
  rw [kernelForm_cond, iota_one_eq lamY IY, map_add, map_smul, smul_eq_mul]
  have hf' : lamX.expect (iota lamX IX f) = 0 := by rw [expect_iota lamX IX hPX, hf, mul_zero]
  have h1 := hM f hf
  have h2 := hT (iota lamX IX f) (vEv lamY IY) hf' (expect_vX lamY IY hPY)
  rw [nrm_iota lamX IX hPX, nrm_vX lamY IY hPY] at h2
  have hn0 : 0 ≤ nrm (condLaw lamX IX hPX) f := Real.sqrt_nonneg _
  rw [Real.sqrt_mul hPX.le, abs_div, abs_of_pos (mul_pos hsX hsY), div_le_iff₀ (mul_pos hsX hsY)]
  have e2 : √((1 - PY) / (PX * PY)) = √(1 - PY) / (√PX * √PY) := by
    rw [Real.sqrt_div' _ (mul_pos hPX hPY).le, Real.sqrt_mul hPX.le]
  rw [e2]
  calc |√PY * kernelForm lamX lamY S (iota lamX IX f) (fun _ => 1) +
        kernelForm lamX lamY S (iota lamX IX f) (vEv lamY IY)|
      ≤ √PY * |kernelForm lamX lamY S (iota lamX IX f) (fun _ => 1)| +
          |kernelForm lamX lamY S (iota lamX IX f) (vEv lamY IY)| := by
        rw [← abs_of_pos hsY, ← abs_mul, abs_of_pos hsY]; exact abs_add_le _ _
    _ ≤ √PY * (M * nrm (condLaw lamX IX hPX) f) +
          c * nrm (condLaw lamX IX hPX) f * √(1 - PY) :=
        add_le_add (mul_le_mul_of_nonneg_left h1 hsY.le) h2
    _ = (M / √PX + c * (√(1 - PY) / (√PX * √PY))) * nrm (condLaw lamX IX hPX) f *
          (√PX * √PY) := by
        field_simp

/-- (b) The total mass: `|⟨1, S_μ 1⟩ - ⟨1, T_S 1⟩| ≤ ‖P₀ T_S^* 1‖ √((1-P_Y)/P_Y)
+ ‖P₀ T_S 1‖ √((1-P_X)/P_X) + ‖P₀ T_S P₀‖ √((1-P_X)(1-P_Y)/(P_X P_Y))`. -/
theorem restriction_mass (lamX : FiniteLaw X) (lamY : FiniteLaw Y) (IX : X → Prop) (IY : Y → Prop)
    (hPX : 0 < prob lamX IX) (hPY : 0 < prob lamY IY) (S : X → Y → ℝ) {c cL cR : ℝ}
    (hT : ∀ f h, lamX.expect f = 0 → lamY.expect h = 0 →
      |kernelForm lamX lamY S f h| ≤ c * nrm lamX f * nrm lamY h)
    (hL : ∀ h, lamY.expect h = 0 → |kernelForm lamX lamY S (fun _ => 1) h| ≤ cL * nrm lamY h)
    (hR : ∀ f, lamX.expect f = 0 → |kernelForm lamX lamY S f (fun _ => 1)| ≤ cR * nrm lamX f) :
    |kernelForm (condLaw lamX IX hPX) (condLaw lamY IY hPY) S (fun _ => 1) (fun _ => 1) -
        kernelForm lamX lamY S (fun _ => 1) (fun _ => 1)| ≤
      cL * √((1 - prob lamY IY) / prob lamY IY) + cR * √((1 - prob lamX IX) / prob lamX IX) +
        c * √((1 - prob lamX IX) * (1 - prob lamY IY) / (prob lamX IX * prob lamY IY)) := by
  rw [kernelForm_cond, iota_one_eq lamX IX, iota_one_eq lamY IY]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
  set PX := prob lamX IX
  set PY := prob lamY IY
  have hsX := Real.sqrt_pos.mpr hPX
  have hsY := Real.sqrt_pos.mpr hPY
  set A := kernelForm lamX lamY S (fun _ => 1) (fun _ => 1)
  set B := kernelForm lamX lamY S (fun _ => 1) (vEv lamY IY)
  set Cc := kernelForm lamX lamY S (vEv lamX IX) (fun _ => 1)
  set D := kernelForm lamX lamY S (vEv lamX IX) (vEv lamY IY)
  have hB : |B| ≤ cL * √(1 - PY) := by
    have := hL (vEv lamY IY) (expect_vX lamY IY hPY)
    rwa [nrm_vX lamY IY hPY] at this
  have hC : |Cc| ≤ cR * √(1 - PX) := by
    have := hR (vEv lamX IX) (expect_vX lamX IX hPX)
    rwa [nrm_vX lamX IX hPX] at this
  have hD : |D| ≤ c * √(1 - PX) * √(1 - PY) := by
    have := hT (vEv lamX IX) (vEv lamY IY) (expect_vX lamX IX hPX) (expect_vX lamY IY hPY)
    rwa [nrm_vX lamX IX hPX, nrm_vX lamY IY hPY] at this
  have hsXY : √(PX * PY) = √PX * √PY := Real.sqrt_mul hPX.le _
  have e : (√PY * (√PX * A + Cc) + (√PX * B + D)) / √(PX * PY) - A =
      B / √PY + Cc / √PX + D / (√PX * √PY) := by
    rw [hsXY]
    field_simp
    ring
  rw [e]
  have h1PX : 0 ≤ 1 - PX := by
    have : PX ≤ 1 := by
      unfold PX prob
      exact lamX.expect_le_const (fun x => ind_le_one IX x)
    linarith
  have h1PY : 0 ≤ 1 - PY := by
    have : PY ≤ 1 := by
      unfold PY prob
      exact lamY.expect_le_const (fun y => ind_le_one IY y)
    linarith
  have r1 : √((1 - PY) / PY) = √(1 - PY) / √PY := Real.sqrt_div' _ hPY.le
  have r2 : √((1 - PX) / PX) = √(1 - PX) / √PX := Real.sqrt_div' _ hPX.le
  have r3 : √((1 - PX) * (1 - PY) / (PX * PY)) = √(1 - PX) * √(1 - PY) / (√PX * √PY) := by
    rw [Real.sqrt_div' _ (mul_pos hPX hPY).le, Real.sqrt_mul h1PX, hsXY]
  rw [r1, r2, r3]
  calc |B / √PY + Cc / √PX + D / (√PX * √PY)|
      ≤ |B| / √PY + |Cc| / √PX + |D| / (√PX * √PY) := by
        have h1 : |B / √PY| = |B| / √PY := by rw [abs_div, abs_of_pos hsY]
        have h2 : |Cc / √PX| = |Cc| / √PX := by rw [abs_div, abs_of_pos hsX]
        have h3 : |D / (√PX * √PY)| = |D| / (√PX * √PY) := by
          rw [abs_div, abs_of_pos (mul_pos hsX hsY)]
        rw [← h1, ← h2, ← h3]
        exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
    _ ≤ cL * √(1 - PY) / √PY + cR * √(1 - PX) / √PX + c * √(1 - PX) * √(1 - PY) / (√PX * √PY) := by
        gcongr
    _ = cL * (√(1 - PY) / √PY) + cR * (√(1 - PX) / √PX) +
          c * (√(1 - PX) * √(1 - PY) / (√PX * √PY)) := by ring

/-- (c) If `P_X, P_Y ≥ I₀ > 0`: `‖P₀ S_μ P₀‖ ≤ ‖P₀ T_S P₀‖ / I₀`. -/
theorem restriction_centred_I0 (lamX : FiniteLaw X) (lamY : FiniteLaw Y) (IX : X → Prop)
    (IY : Y → Prop) (hPX : 0 < prob lamX IX) (hPY : 0 < prob lamY IY) {I₀ : ℝ} (hI0 : 0 < I₀)
    (hIX : I₀ ≤ prob lamX IX) (hIY : I₀ ≤ prob lamY IY) (S : X → Y → ℝ) {c : ℝ} (hc0 : 0 ≤ c)
    (hT : ∀ f h, lamX.expect f = 0 → lamY.expect h = 0 →
      |kernelForm lamX lamY S f h| ≤ c * nrm lamX f * nrm lamY h)
    (f : X → ℝ) (h : Y → ℝ) (hf : (condLaw lamX IX hPX).expect f = 0)
    (hh : (condLaw lamY IY hPY).expect h = 0) :
    |kernelForm (condLaw lamX IX hPX) (condLaw lamY IY hPY) S f h| ≤
      c / I₀ * nrm (condLaw lamX IX hPX) f * nrm (condLaw lamY IY hPY) h := by
  refine (restriction_centred lamX lamY IX IY hPX hPY S hT f h hf hh).trans ?_
  have hn : 0 ≤ nrm (condLaw lamX IX hPX) f * nrm (condLaw lamY IY hPY) h :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hsq : I₀ ≤ √(prob lamX IX * prob lamY IY) := by
    rw [show I₀ = √(I₀ * I₀) from (Real.sqrt_mul_self hI0.le).symm]
    exact Real.sqrt_le_sqrt (mul_le_mul hIX hIY hI0.le (le_trans hI0.le hIX))
  have : c / √(prob lamX IX * prob lamY IY) ≤ c / I₀ := div_le_div_of_nonneg_left hc0 hI0 hsq
  rw [mul_assoc, mul_assoc]
  exact mul_le_mul_of_nonneg_right this hn

theorem prob_le_one' (lamX : FiniteLaw X) (I : X → Prop) : prob lamX I ≤ 1 := by
  unfold prob
  exact lamX.expect_le_const (fun x => ind_le_one I x)

/-- `I₀ ≤ P ≤ 1` gives `√((1 - P)/P) ≤ √(1 - I₀)/√I₀`. -/
theorem sqrt_ratio_le {P I₀ : ℝ} (hI0 : 0 < I₀) (hIP : I₀ ≤ P) :
    √((1 - P) / P) ≤ √(1 - I₀) / √I₀ := by
  rw [← Real.sqrt_div' _ hI0.le]
  apply Real.sqrt_le_sqrt
  have hP : 0 < P := lt_of_lt_of_le hI0 hIP
  rw [div_le_div_iff₀ hP hI0]
  nlinarith

/-- (c) The constant image with `P_X, P_Y ≥ I₀`:
`‖P₀ S_μ 1‖ ≤ M/√I₀ + C √(1 - I₀)/I₀ ≤ (M + C √(1 - I₀))/I₀`. -/
theorem restriction_const_image_I0 (lamX : FiniteLaw X) (lamY : FiniteLaw Y) (IX : X → Prop)
    (IY : Y → Prop) (hPX : 0 < prob lamX IX) (hPY : 0 < prob lamY IY) {I₀ : ℝ} (hI0 : 0 < I₀)
    (hIX : I₀ ≤ prob lamX IX) (hIY : I₀ ≤ prob lamY IY) (S : X → Y → ℝ) {c M : ℝ}
    (hc0 : 0 ≤ c) (hM0 : 0 ≤ M)
    (hT : ∀ f h, lamX.expect f = 0 → lamY.expect h = 0 →
      |kernelForm lamX lamY S f h| ≤ c * nrm lamX f * nrm lamY h)
    (hM : ∀ f, (condLaw lamX IX hPX).expect f = 0 →
      |kernelForm lamX lamY S (iota lamX IX f) (fun _ => 1)| ≤ M * nrm (condLaw lamX IX hPX) f)
    (f : X → ℝ) (hf : (condLaw lamX IX hPX).expect f = 0) :
    |kernelForm (condLaw lamX IX hPX) (condLaw lamY IY hPY) S f (fun _ => 1)| ≤
      (M / √I₀ + c * √(1 - I₀) / I₀) * nrm (condLaw lamX IX hPX) f ∧
    |kernelForm (condLaw lamX IX hPX) (condLaw lamY IY hPY) S f (fun _ => 1)| ≤
      (M + c * √(1 - I₀)) / I₀ * nrm (condLaw lamX IX hPX) f := by
  have hb := restriction_const_image lamX lamY IX IY hPX hPY S hT hM f hf
  have hn0 : 0 ≤ nrm (condLaw lamX IX hPX) f := Real.sqrt_nonneg _
  have hI1 : I₀ ≤ 1 := hIX.trans (prob_le_one' lamX IX)
  have hsI : 0 < √I₀ := Real.sqrt_pos.mpr hI0
  have hsIle : I₀ ≤ √I₀ := by
    have := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hI1 hI0.le)
    rwa [mul_one, Real.sqrt_mul_self hI0.le] at this
  have h1 : M / √(prob lamX IX) ≤ M / √I₀ :=
    div_le_div_of_nonneg_left hM0 hsI (Real.sqrt_le_sqrt hIX)
  have h2 : √((1 - prob lamY IY) / (prob lamX IX * prob lamY IY)) ≤ √(1 - I₀) / I₀ := by
    have e : √(1 - I₀) / I₀ = √((1 - I₀) / (I₀ * I₀)) := by
      rw [Real.sqrt_div' _ (mul_self_nonneg I₀), Real.sqrt_mul_self hI0.le]
    rw [e]
    apply Real.sqrt_le_sqrt
    have hXY : I₀ * I₀ ≤ prob lamX IX * prob lamY IY := mul_le_mul hIX hIY hI0.le hPX.le
    exact div_le_div₀ (by linarith) (by linarith) (mul_pos hI0 hI0) hXY
  have hfirst : M / √(prob lamX IX) + c * √((1 - prob lamY IY) / (prob lamX IX * prob lamY IY)) ≤
      M / √I₀ + c * √(1 - I₀) / I₀ := by
    rw [mul_div_assoc]
    exact add_le_add h1 (mul_le_mul_of_nonneg_left h2 hc0)
  have hA := hb.trans (mul_le_mul_of_nonneg_right hfirst hn0)
  refine ⟨hA, hA.trans (mul_le_mul_of_nonneg_right ?_ hn0)⟩
  have h3 : M / √I₀ ≤ M / I₀ := div_le_div_of_nonneg_left hM0 hI0 hsIle
  have e : (M + c * √(1 - I₀)) / I₀ = M / I₀ + c * √(1 - I₀) / I₀ := by rw [add_div]
  rw [e]
  linarith

/-- (c) The total mass with `P_X, P_Y ≥ I₀` and one constant `C` bounding the three
compressions: `|⟨1, S_μ 1⟩ - a₀| ≤ (Z + C(2√(1 - I₀) + 1 - I₀))/I₀` whenever
`|⟨1, T_S 1⟩ - a₀| ≤ Z`. -/
theorem restriction_mass_I0 (lamX : FiniteLaw X) (lamY : FiniteLaw Y) (IX : X → Prop)
    (IY : Y → Prop) (hPX : 0 < prob lamX IX) (hPY : 0 < prob lamY IY) {I₀ : ℝ} (hI0 : 0 < I₀)
    (hIX : I₀ ≤ prob lamX IX) (hIY : I₀ ≤ prob lamY IY) (S : X → Y → ℝ) {C a₀ Z : ℝ}
    (hC0 : 0 ≤ C)
    (hT : ∀ f h, lamX.expect f = 0 → lamY.expect h = 0 →
      |kernelForm lamX lamY S f h| ≤ C * nrm lamX f * nrm lamY h)
    (hL : ∀ h, lamY.expect h = 0 → |kernelForm lamX lamY S (fun _ => 1) h| ≤ C * nrm lamY h)
    (hR : ∀ f, lamX.expect f = 0 → |kernelForm lamX lamY S f (fun _ => 1)| ≤ C * nrm lamX f)
    (hZ : |kernelForm lamX lamY S (fun _ => 1) (fun _ => 1) - a₀| ≤ Z) :
    |kernelForm (condLaw lamX IX hPX) (condLaw lamY IY hPY) S (fun _ => 1) (fun _ => 1) - a₀| ≤
      (Z + C * (2 * √(1 - I₀) + 1 - I₀)) / I₀ := by
  have hb := restriction_mass lamX lamY IX IY hPX hPY S hT hL hR
  have hI1 : I₀ ≤ 1 := hIX.trans (prob_le_one' lamX IX)
  have hsI : 0 < √I₀ := Real.sqrt_pos.mpr hI0
  have hsIle : I₀ ≤ √I₀ := by
    have := Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hI1 hI0.le)
    rwa [mul_one, Real.sqrt_mul_self hI0.le] at this
  have hZ0 : 0 ≤ Z := le_trans (abs_nonneg _) hZ
  have hs1 : 0 ≤ √(1 - I₀) := Real.sqrt_nonneg _
  have hY : √((1 - prob lamY IY) / prob lamY IY) ≤ √(1 - I₀) / I₀ :=
    (sqrt_ratio_le hI0 hIY).trans (div_le_div_of_nonneg_left hs1 hI0 hsIle)
  have hX : √((1 - prob lamX IX) / prob lamX IX) ≤ √(1 - I₀) / I₀ :=
    (sqrt_ratio_le hI0 hIX).trans (div_le_div_of_nonneg_left hs1 hI0 hsIle)
  have hXY : √((1 - prob lamX IX) * (1 - prob lamY IY) / (prob lamX IX * prob lamY IY)) ≤
      (1 - I₀) / I₀ := by
    have hsq : (1 - I₀) / I₀ = √(((1 - I₀) / I₀) * ((1 - I₀) / I₀)) :=
      (Real.sqrt_mul_self (div_nonneg (by linarith) hI0.le)).symm
    rw [hsq]
    apply Real.sqrt_le_sqrt
    rw [div_mul_div_comm]
    have hPXY : I₀ * I₀ ≤ prob lamX IX * prob lamY IY := mul_le_mul hIX hIY hI0.le hPX.le
    have hnum : (1 - prob lamX IX) * (1 - prob lamY IY) ≤ (1 - I₀) * (1 - I₀) :=
      mul_le_mul (by linarith) (by linarith) (by linarith [prob_le_one' lamY IY])
        (by linarith)
    exact div_le_div₀ (mul_nonneg (by linarith) (by linarith)) hnum (mul_pos hI0 hI0) hPXY
  have hZI : Z ≤ Z / I₀ := by
    rw [le_div_iff₀ hI0]
    nlinarith
  calc |kernelForm (condLaw lamX IX hPX) (condLaw lamY IY hPY) S (fun _ => 1) (fun _ => 1) - a₀|
      ≤ |kernelForm (condLaw lamX IX hPX) (condLaw lamY IY hPY) S (fun _ => 1) (fun _ => 1) -
          kernelForm lamX lamY S (fun _ => 1) (fun _ => 1)| +
        |kernelForm lamX lamY S (fun _ => 1) (fun _ => 1) - a₀| := abs_sub_le _ _ _
    _ ≤ (C * (√(1 - I₀) / I₀) + C * (√(1 - I₀) / I₀) + C * ((1 - I₀) / I₀)) + Z / I₀ := by
        refine add_le_add (hb.trans ?_) (hZ.trans hZI)
        exact add_le_add (add_le_add (mul_le_mul_of_nonneg_left hY hC0)
          (mul_le_mul_of_nonneg_left hX hC0)) (mul_le_mul_of_nonneg_left hXY hC0)
    _ = (Z + C * (2 * √(1 - I₀) + 1 - I₀)) / I₀ := by
        field_simp
        ring

/-- (c) Adding a constant kernel `a` changes the form by `a E f E h`; so the centred
compression and the two constant images are unchanged. -/
theorem kernelForm_sub_const (lamX : FiniteLaw X) (lamY : FiniteLaw Y) (S : X → Y → ℝ) (a : ℝ)
    (f : X → ℝ) (h : Y → ℝ) :
    kernelForm lamX lamY (fun x y => S x y - a) f h =
      kernelForm lamX lamY S f h - a * lamX.expect f * lamY.expect h := by
  simp only [kernelForm, LinearMap.mk₂_apply, FiniteLaw.expect]
  rw [mul_assoc, Finset.sum_mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  ring

end Sarkozy.Cuts
