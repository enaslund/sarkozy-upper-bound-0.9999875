module

public import Sarkozy.UpperComparison.Domain
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic
public import Mathlib.Analysis.Convex.Slope

@[expose] public section

/-!
# The displayed majorants of `lem:record:domain`, Step 2

`paper/sections/26_upper_comparison.tex`, proof of `lem:record:domain`, Step 2: "For instance
`f_Schur = H R_m ρ_F/r + (H + 50H²)(υ²/r²) r`, `ρ'/r = ((ρ_new/r)(1 + 2F) + U(U/r))/(1 - U)`, and
`F_N = 2NU + K_∞ ρ_I^{2N-1} e_I/(1 - ρ_I²)` with the number `N` of initial terms held fixed."

Each of the three is admissible (nonnegative and nondecreasing on the box) once its inputs are,
by the closure rules of `lem:majorant`(ii) (`Sarkozy.Majorant`):
* `fSchur_admissible`;
* `rhoPrime_div_admissible` (with `U < 1` on the box, gate (G5));
* `FN_admissible` (with `ρ_I < 1` on the box, the hypothesis of `prop:dense-comparison`);
* `expm1_div_admissible`: `U/r = ((e^{ℓ_U} - 1)/ℓ_U)(ℓ_U/r)` is admissible when `ℓ_U` and
  `ℓ_U/r` are, from the monotonicity of `(e^x - 1)/x` (`expm1_div_mono`, convexity of `exp`).

`nonroot_block_coef` is the block inflation of the nonroot coefficients in part (ii),
`d = g exp(B_top L'/(X log X))`.

`neumann_one_eq` is the scalar identity behind `lem:upper:neumann-refinement`: `F_N` at `N = 1`,
`ρ_I = ρ_new`, `e_I = (1 + ρ_new)U` is `2U + K_∞ ρ_new U/(1 - ρ_new)`.

So by `domain_coeffs` the values at the evaluation point bound the values at every larger prime
(`rhoPrime_at_prime`). The admissibility of the inputs (`ρ_new/r`, `U`, `U/r`, `F`, `K_∞`, `ρ_I`,
`e_I`, `H`, `R_m`, `ρ_F/r`, `υ²/r²`) is the rest of Step 2 and is a hypothesis here.
-/

open Finset

namespace Sarkozy.UpperComparison

open Sarkozy.Majorant

section Formulas

variable {Δ : Type*} [Preorder Δ]

/-- Natural powers of an admissible function are admissible. -/
theorem admissible_pow {φ : Δ → ℝ} (hφ : Admissible φ) (n : ℕ) :
    Admissible (fun x => φ x ^ n) :=
  ⟨fun _ _ hxy => pow_le_pow_left₀ (hφ.2 _) (hφ.1 hxy) n, fun x => pow_nonneg (hφ.2 x) n⟩

/-- A nonnegative multiple of an admissible function is admissible. -/
theorem admissible_const_mul {φ : Δ → ℝ} (hφ : Admissible φ) {c : ℝ} (hc : 0 ≤ c) :
    Admissible (fun x => c * φ x) :=
  admissible_mul (admissible_const hc) hφ

/-- **`f_Schur` is admissible**: `f_Schur = H R_m (ρ_F/r) + (H + 50H²)(υ²/r²) r`, for admissible
`H`, `R_m`, `ρ_F/r`, `υ²/r²` and `r`. -/
theorem fSchur_admissible {H Rm ρFr υr r : Δ → ℝ} (hH : Admissible H) (hRm : Admissible Rm)
    (hρF : Admissible ρFr) (hυ : Admissible υr) (hr : Admissible r) :
    Admissible (fun x => H x * Rm x * ρFr x + (H x + 50 * H x ^ 2) * υr x * r x) := by
  have h1 : Admissible (H * Rm * ρFr) := admissible_mul (admissible_mul hH hRm) hρF
  have h2 : Admissible (fun x => H x + 50 * H x ^ 2) :=
    admissible_add hH (admissible_const_mul (admissible_pow hH 2) (by norm_num))
  have h3 : Admissible ((fun x => H x + 50 * H x ^ 2) * υr * r) :=
    admissible_mul (admissible_mul h2 hυ) hr
  exact admissible_add h1 h3

/-- **`ρ'/r` is admissible** ((F7)): `ρ'/r = ((ρ_new/r)(1 + 2F) + U (U/r))/(1 - U)`, for
admissible `ρ_new/r`, `F`, `U`, `U/r`, with `U < 1` on the box (gate (G5)). -/
theorem rhoPrime_div_admissible {ρnr F U Ur : Δ → ℝ} (hρ : Admissible ρnr) (hF : Admissible F)
    (hU : Admissible U) (hUr : Admissible Ur) (hU1 : ∀ x, U x < 1) :
    Admissible (fun x => (ρnr x * (1 + 2 * F x) + U x * Ur x) / (1 - U x)) := by
  have h1 : Admissible (fun x => 1 + 2 * F x) :=
    admissible_add (admissible_const zero_le_one) (admissible_const_mul hF (by norm_num))
  have h2 : Admissible (ρnr * (fun x => 1 + 2 * F x) + U * Ur) :=
    admissible_add (admissible_mul hρ h1) (admissible_mul hU hUr)
  have h3 := admissible_mul h2 (admissible_one_div_one_sub hU hU1)
  refine ⟨fun a b hab => ?_, fun x => ?_⟩
  · have := h3.1 hab
    simp only [Pi.mul_apply, Pi.add_apply] at this
    rwa [mul_one_div, mul_one_div] at this
  · have := h3.2 x
    simp only [Pi.mul_apply, Pi.add_apply] at this
    rwa [mul_one_div] at this

/-- **`F_N` is admissible** (`prop:dense-comparison`): with `N` fixed,
`F_N = 2NU + K_∞ ρ_I^{2N-1} e_I/(1 - ρ_I²)`, for admissible `U`, `K_∞`, `ρ_I`, `e_I`, with
`ρ_I < 1` on the box. -/
theorem FN_admissible (N : ℕ) {U Kinf ρI eI : Δ → ℝ} (hU : Admissible U)
    (hK : Admissible Kinf) (hρ : Admissible ρI) (he : Admissible eI) (hρ1 : ∀ x, ρI x < 1) :
    Admissible (fun x => 2 * N * U x + Kinf x * ρI x ^ (2 * N - 1) * eI x / (1 - ρI x ^ 2)) := by
  have hsq : ∀ x, ρI x ^ 2 < 1 := fun x => by
    have h0 := hρ.2 x
    have h1 := hρ1 x
    nlinarith
  have h1 : Admissible (fun x => (2 * N : ℝ) * U x) :=
    admissible_const_mul hU (by positivity)
  have h2 : Admissible (Kinf * (fun x => ρI x ^ (2 * N - 1)) * eI) :=
    admissible_mul (admissible_mul hK (admissible_pow hρ _)) he
  have h3 := admissible_mul h2 (admissible_one_div_one_sub (admissible_pow hρ 2) hsq)
  have h4 := admissible_add h1 h3
  refine ⟨fun a b hab => ?_, fun x => ?_⟩
  · have := h4.1 hab
    simp only [Pi.mul_apply, Pi.add_apply] at this
    rwa [mul_one_div, mul_one_div] at this
  · have := h4.2 x
    simp only [Pi.mul_apply, Pi.add_apply] at this
    rwa [mul_one_div] at this

/-- `(e^x - 1)/x` is nondecreasing on `(0, ∞)`: secant slopes of the convex function `exp` from
`0`. -/
theorem expm1_div_mono {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) :
    (Real.exp x - 1) / x ≤ (Real.exp y - 1) / y := by
  have h := convexOn_exp.secant_mono (a := 0) (x := x) (y := y) (Set.mem_univ _)
    (Set.mem_univ _) (Set.mem_univ _) hx.ne' (by linarith : y ≠ 0) hxy
  simpa only [Real.exp_zero, sub_zero] using h

/-- **`U/r` is admissible** (`lem:record:domain`, Step 2: "`U/r = ((e^{ℓ_U} - 1)/ℓ_U)(ℓ_U/r)` is
admissible"): if the count logarithm `ℓ` and `ℓ/r` are admissible and `r > 0`, then
`(e^ℓ - 1)/r` is admissible. -/
theorem expm1_div_admissible {ℓ r : Δ → ℝ} (hℓ : Admissible ℓ)
    (hℓr : Admissible (fun x => ℓ x / r x)) (hr : ∀ x, 0 < r x) :
    Admissible (fun x => (Real.exp (ℓ x) - 1) / r x) := by
  have hnum : ∀ x, 0 ≤ Real.exp (ℓ x) - 1 := fun x => by
    linarith [Real.add_one_le_exp (ℓ x), hℓ.2 x]
  refine ⟨fun x y hxy => ?_, fun x => div_nonneg (hnum x) (hr x).le⟩
  rcases (hℓ.2 x).eq_or_lt with h0 | hpos
  · simp only
    rw [← h0, Real.exp_zero, sub_self, zero_div]
    exact div_nonneg (hnum y) (hr y).le
  · have hly : ℓ x ≤ ℓ y := hℓ.1 hxy
    have hpos' : 0 < ℓ y := lt_of_lt_of_le hpos hly
    have e1 : (Real.exp (ℓ x) - 1) / r x =
        ((Real.exp (ℓ x) - 1) / ℓ x) * (ℓ x / r x) := by
      field_simp [hpos.ne', (hr x).ne']
    have e2 : (Real.exp (ℓ y) - 1) / r y =
        ((Real.exp (ℓ y) - 1) / ℓ y) * (ℓ y / r y) := by
      field_simp [hpos'.ne', (hr y).ne']
    simp only
    rw [e1, e2]
    exact mul_le_mul (expm1_div_mono hpos hly) (hℓr.1 hxy) (hℓr.2 x)
      (div_nonneg (hnum y) hpos'.le)

end Formulas

/-- **`lem:upper:neumann-refinement`, the scalar identity**: the bound `F_N` of `lem:tr:repair`(g)
with `N = 1`, `ρ_I = ρ_new` and `e_I = (1 + ρ_new)U` is `2U + K_∞ ρ_new U/(1 - ρ_new)`, the
second term of `F_*`. -/
theorem neumann_one_eq {U K ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ : ρ < 1) :
    2 * ((1 : ℕ) : ℝ) * U + K * ρ ^ (2 * 1 - 1) * ((1 + ρ) * U) / (1 - ρ ^ 2) =
      2 * U + K * ρ * U / (1 - ρ) := by
  have h1 : (1 : ℝ) - ρ ≠ 0 := by linarith
  have h2 : (1 : ℝ) + ρ ≠ 0 := by linarith
  have h3 : (1 : ℝ) - ρ ^ 2 = (1 - ρ) * (1 + ρ) := by ring
  rw [h3]
  norm_num
  field_simp

/-- **The repair correlation at a larger prime** (`lem:record:domain`(i) for (F7)): if `ρ'` at the
point `x` of the box is `r · (ρ'/r)(x)` with admissible inputs, it is at most `r` times the value
of `ρ'/r` at the evaluation point. -/
theorem rhoPrime_at_prime {r₀ l₀ : ℝ} (hr : 0 ≤ r₀) (hl : 0 ≤ l₀) {ρnr F U Ur : UpperBox r₀ l₀ → ℝ}
    (hρ : Admissible ρnr) (hF : Admissible F) (hU : Admissible U) (hUr : Admissible Ur)
    (hU1 : ∀ x, U x < 1) (x : UpperBox r₀ l₀) :
    x.1.1 ^ 1 * ((ρnr x * (1 + 2 * F x) + U x * Ur x) / (1 - U x)) ≤
      x.1.1 ^ 1 * ((ρnr (UpperBox.top hr hl) * (1 + 2 * F (UpperBox.top hr hl)) +
          U (UpperBox.top hr hl) * Ur (UpperBox.top hr hl)) / (1 - U (UpperBox.top hr hl))) :=
  prime_coeff_le hr hl (rhoPrime_div_admissible hρ hF hU hUr hU1) x 1

/-- **The nonroot block coefficient** (`lem:record:domain`(ii)): if the block form of (F6)
(`lem:spec:tensorcomp`(b),(c), a hypothesis here) bounds the negative coefficient of a block by
`g ∏_{p ∈ 𝔅} (1 + B_top/p)`, and the primes of the block are at least `X > 1` with product at most
`e^{L'}`, then it is at most `d = g exp(B_top L'/(X log X))`, by `∑_{p ∈ 𝔅} 1/p ≤ L'/(X log X)`. -/
theorem nonroot_block_coef {s : Finset ℝ} {X L g B dB : ℝ} (hX : 1 < X) (hs : ∀ p ∈ s, X ≤ p)
    (hprod : ∏ p ∈ s, p ≤ Real.exp L) (hg : 0 ≤ g) (hB : 0 ≤ B)
    (hd : dB ≤ g * ∏ p ∈ s, (1 + B / p)) :
    dB ≤ g * Real.exp (B * L / (X * Real.log X)) :=
  hd.trans (mul_le_mul_of_nonneg_left (block_inflation_prod hX hs hprod hB) hg)

end Sarkozy.UpperComparison
