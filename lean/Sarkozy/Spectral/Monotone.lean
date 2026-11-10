module

public import Sarkozy.Certificates.Majorant

/-!
# `lem:spectral-monotone` (c) and the variance part of (d)

`paper/sections/14_spectral.tex`, `lem:spectral-monotone`, with the calculus of admissible
functions of `Sarkozy.Certificates.Majorant` (`def:majorant`, `lem:majorant`): every quantity
is a function on a box `Δ` (in the application `r ∈ (0, r₀]`), and *admissible* means
nonnegative and nondecreasing.

* `spectral_monotone_c` — (c): if `N_ns/r`, `D_col/r`, `M_⋆/r` and `ε_Z` are admissible and
  `ε_Z(r₀) < 1`, then `R_Z = 1/(1 - ε_Z)`, `ε_ϱ/r = R_Z (M_⋆/r + N_ns/r + D_col/r)`,
  `ε_ϱ = r (ε_ϱ/r)` and `c_⊥ = R_Z (N_ns/r + D_col/r) + r (ε_ϱ/r)²` are admissible. These give
  the uniformity hypotheses `c_⊥(r) ≤ c̄_⊥` and `ε_ϱ(r)/r ≤ ε_ϱ(r₀)/r₀` of
  `Sarkozy.Spectral.spectral_criterion_routeA` (by `Sarkozy.Majorant.endpoint_le`).
* `admissible_range_variance` — (d), the bound (a) of `lem:push:localvariance`:
  `δ'²/(4(1 + δ'))` is admissible when `δ'` is.
* `admissible_sq_div_antitone` — (d), the bound `(ε^loc/ℓ^loc)²` of `lem:push:localvariance`
  (b) is admissible when `ε^loc` is admissible and `ℓ^loc` is positive and nonincreasing.
* `beta_branch_identity`, `beta_branch_nonneg` — (a), the identity in its proof showing that the
  second branch of the maximum in `β_kl` (`eq:spec:beta`) never exceeds the first.
* `spectral_monotone_b` — (b): `ε_rem`, `ε_par`, `η_B` and `Λ_M` are admissible.
* `p_conversions` — the conversions `p/(p-1) = 1/(1 - r²)` etc. used in (a).
* `localvariance_monotone`, `admissible_kappa` — (d): `ℓ^loc > 0` on the box from its value at
  `r₀`, admissibility of `(ε^loc/ℓ^loc)²`, and of the denominators `κ = 2^t/(1 - ε⁻)`.
-/

@[expose] public section

namespace Sarkozy.Spectral

open Sarkozy.Majorant

variable {Δ : Type*} [Preorder Δ]

/-- **`lem:spectral-monotone` (c).** Here `nN = N_ns/r`, `nD = D_col/r`, `nM = M_⋆/r`, and `xp`
is the endpoint `r₀` of the box. -/
theorem spectral_monotone_c (r nN nD nM εZ : Δ → ℝ) (hr : Admissible r) (hN : Admissible nN)
    (hD : Admissible nD) (hM : Admissible nM) (hZ : Admissible εZ) (xp : Δ)
    (hxp : ∀ x, x ≤ xp) (hZ1 : εZ xp < 1) :
    Admissible (fun x => 1 / (1 - εZ x)) ∧
    Admissible (fun x => 1 / (1 - εZ x) * (nM x + nN x + nD x)) ∧
    Admissible (fun x => r x * (1 / (1 - εZ x) * (nM x + nN x + nD x))) ∧
    Admissible (fun x => 1 / (1 - εZ x) * (nN x + nD x) +
      r x * (1 / (1 - εZ x) * (nM x + nN x + nD x)) ^ 2) := by
  have hlt : ∀ x, εZ x < 1 := fun x => lt_of_le_of_lt (endpoint_le hZ (hxp x)) hZ1
  have hRZ : Admissible (fun x => 1 / (1 - εZ x)) := admissible_one_div_one_sub hZ hlt
  have hsum3 : Admissible (fun x => nM x + nN x + nD x) :=
    admissible_add (admissible_add hM hN) hD
  have hsum2 : Admissible (fun x => nN x + nD x) := admissible_add hN hD
  have hρr : Admissible (fun x => 1 / (1 - εZ x) * (nM x + nN x + nD x)) :=
    admissible_mul hRZ hsum3
  have hρ : Admissible (fun x => r x * (1 / (1 - εZ x) * (nM x + nN x + nD x))) :=
    admissible_mul hr hρr
  have hsq : Admissible (fun x => (1 / (1 - εZ x) * (nM x + nN x + nD x)) ^ 2) := by
    have := admissible_mul hρr hρr
    refine ⟨fun a b hab => ?_, fun x => sq_nonneg _⟩
    have h := this.1 hab
    simp only [Pi.mul_apply] at h
    simpa [sq] using h
  refine ⟨hRZ, hρr, hρ, admissible_add (admissible_mul hRZ hsum2) (admissible_mul hr hsq)⟩

/-- `y ↦ y²/(4(1 + y))` is nondecreasing on `[0, ∞)`. -/
theorem range_variance_mono {y y' : ℝ} (hy : 0 ≤ y) (hyy : y ≤ y') :
    y ^ 2 / (4 * (1 + y)) ≤ y' ^ 2 / (4 * (1 + y')) := by
  rw [div_le_div_iff₀ (by positivity) (by linarith)]
  nlinarith [mul_nonneg hy (sub_nonneg.mpr hyy), mul_nonneg (mul_nonneg hy hy)
    (sub_nonneg.mpr hyy)]

/-- **`lem:spectral-monotone` (d), the range bound**: if `δ'` is admissible, so is
`δ'²/(4(1 + δ'))` (`lem:push:localvariance` (a)). -/
theorem admissible_range_variance {δ : Δ → ℝ} (hδ : Admissible δ) :
    Admissible (fun x => δ x ^ 2 / (4 * (1 + δ x))) :=
  ⟨fun _ _ hab => range_variance_mono (hδ.2 _) (hδ.1 hab),
    fun x => div_nonneg (sq_nonneg _) (by linarith [hδ.2 x])⟩

/-- **`lem:spectral-monotone` (d), the local bound**: if `ε` is admissible and `ℓ` is positive
and nonincreasing, then `(ε/ℓ)²` is admissible (`lem:push:localvariance` (b)). -/
theorem admissible_sq_div_antitone {ε ℓ : Δ → ℝ} (hε : Admissible ε) (hℓ : Antitone ℓ)
    (hℓ0 : ∀ x, 0 < ℓ x) : Admissible (fun x => (ε x / ℓ x) ^ 2) := by
  refine ⟨fun a b hab => ?_, fun x => sq_nonneg _⟩
  have h1 : ε a / ℓ a ≤ ε b / ℓ b :=
    div_le_div₀ (hε.2 b) (hε.1 hab) (hℓ0 b) (hℓ hab)
  exact pow_le_pow_left₀ (div_nonneg (hε.2 a) (hℓ0 a).le) h1 2

/-- **The two branches of `β_kl`** (`eq:spec:beta`; proof of `lem:spectral-monotone` (a)): for
`0 ≤ a, b < 1`, `(1 + e)/((1 - a)(1 - b)) + (1 - e)/((1 + a)(1 + b)) - 2` equals
`2(a² + b² + ab - a²b² + e(a + b))/((1 - a²)(1 - b²))`. -/
theorem beta_branch_identity {a b e : ℝ} (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (ha : a < 1) (hb : b < 1) :
    (1 + e) / ((1 - a) * (1 - b)) + (1 - e) / ((1 + a) * (1 + b)) - 2 =
      2 * (a ^ 2 + b ^ 2 + a * b - a ^ 2 * b ^ 2 + e * (a + b)) /
        ((1 - a ^ 2) * (1 - b ^ 2)) := by
  have h1 : (1 - a) ≠ 0 := (sub_pos.mpr ha).ne'
  have h2 : (1 - b) ≠ 0 := (sub_pos.mpr hb).ne'
  have h3 : (1 + a) ≠ 0 := by positivity
  have h4 : (1 + b) ≠ 0 := by positivity
  have h5 : (1 - a ^ 2) ≠ 0 := (by nlinarith : (0 : ℝ) < 1 - a ^ 2).ne'
  have h6 : (1 - b ^ 2) ≠ 0 := (by nlinarith : (0 : ℝ) < 1 - b ^ 2).ne'
  field_simp
  ring

/-- **The second branch of `β_kl` never exceeds the first** (`lem:spectral-monotone` (a)):
for `0 ≤ a, b < 1` and `e ≥ 0` the difference of `beta_branch_identity` is nonnegative, with no
condition on `e` beyond `e ≥ 0`. -/
theorem beta_branch_nonneg {a b e : ℝ} (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (ha : a < 1) (hb : b < 1)
    (he : 0 ≤ e) :
    0 ≤ (1 + e) / ((1 - a) * (1 - b)) + (1 - e) / ((1 + a) * (1 + b)) - 2 := by
  rw [beta_branch_identity ha0 hb0 ha hb]
  have hab : a * b ≤ 1 := by nlinarith
  apply div_nonneg
  · nlinarith [sq_nonneg a, sq_nonneg b, mul_nonneg he (add_nonneg ha0 hb0),
      mul_nonneg (mul_nonneg ha0 hb0) (sub_nonneg.mpr hab)]
  · exact mul_nonneg (by nlinarith) (by nlinarith)

/-- Hence `β_kl = 2^{|N(k) ∩ N(l)|} ((1 + e_u)/((1 - ê_k)(1 - ê_l)) - 1)`: the maximum in
`eq:spec:beta` is its first branch. -/
theorem beta_max_eq_first {a b e : ℝ} (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (ha : a < 1) (hb : b < 1)
    (he : 0 ≤ e) :
    max ((1 + e) / ((1 - a) * (1 - b)) - 1) (1 - (1 - e) / ((1 + a) * (1 + b))) =
      (1 + e) / ((1 - a) * (1 - b)) - 1 :=
  max_eq_left (by linarith [beta_branch_nonneg ha0 hb0 ha hb he])

/-- `φ - 1` is admissible if `φ` is admissible and `φ ≥ 1`. -/
theorem admissible_sub_one {φ : Δ → ℝ} (hφ : Admissible φ) (h1 : ∀ x, 1 ≤ φ x) :
    Admissible (fun x => φ x - 1) :=
  ⟨fun _ _ hab => by simp only; linarith [hφ.1 hab], fun x => by simp only; linarith [h1 x]⟩

/-- **`lem:spectral-monotone` (b).** With `r` admissible and `r² < 1` (so `p/(p-1) = 1/(1 - r²)`),
if `Γ_E`, `ε_H`, `ζ̄` and `R₊ ≥ 1` are admissible, and so are `ε_≠`, `ε_V`, `η_Q` (by (a)),
then `ε_rem = 2(Γ_E(λ̄ + ε_H))^{1/2} + Γ_E` (`eq:spec:rem`), `ε_par = ζ̄ Λ_nc`,
`η_B = (R₊/(1 - r²) - 1)Λ₊ + R₊/(1 - r²) (ε_H + ε_≠ + ε_rem + ε_par) + ε_V Λ_D² + 2Λ_D η_Q`
(`eq:spec:etaB`) and `Λ_M = Λ₊ + ε_H + ε_≠ + ε_rem + ε_par` are admissible. -/
theorem spectral_monotone_b (r ΓE εH ζ Rp εne εV ηQ : Δ → ℝ) {lam Λnc Λp ΛD : ℝ}
    (hr : Admissible r) (hΓ : Admissible ΓE) (hεH : Admissible εH) (hζ : Admissible ζ)
    (hRp : Admissible Rp) (hεne : Admissible εne) (hεV : Admissible εV) (hηQ : Admissible ηQ)
    (hlam : 0 ≤ lam) (hΛnc : 0 ≤ Λnc) (hΛp : 0 ≤ Λp) (hΛD : 0 ≤ ΛD)
    (hRp1 : ∀ x, 1 ≤ Rp x) (hr1 : ∀ x, r x ^ 2 < 1) :
    Admissible (fun x => 2 * Real.sqrt (ΓE x * (lam + εH x)) + ΓE x) ∧
    Admissible (fun x => ζ x * Λnc) ∧
    Admissible (fun x => (Rp x / (1 - r x ^ 2) - 1) * Λp + Rp x / (1 - r x ^ 2) *
      (εH x + εne x + (2 * Real.sqrt (ΓE x * (lam + εH x)) + ΓE x) + ζ x * Λnc) +
      εV x * ΛD ^ 2 + 2 * ΛD * ηQ x) ∧
    Admissible (fun x => Λp + εH x + εne x + (2 * Real.sqrt (ΓE x * (lam + εH x)) + ΓE x) +
      ζ x * Λnc) := by
  have hc : ∀ {c : ℝ}, 0 ≤ c → Admissible (fun _ : Δ => c) := fun h => admissible_const h
  have hrem : Admissible (fun x => 2 * Real.sqrt (ΓE x * (lam + εH x)) + ΓE x) :=
    admissible_add (admissible_mul (hc zero_le_two)
      (admissible_sqrt (admissible_mul hΓ (admissible_add (hc hlam) hεH)))) hΓ
  have hpar : Admissible (fun x => ζ x * Λnc) := admissible_mul hζ (hc hΛnc)
  have hr2 : Admissible (fun x => r x ^ 2) := by
    have h := admissible_mul hr hr
    exact ⟨fun a b hab => by simpa [sq] using h.1 hab, fun x => sq_nonneg _⟩
  have hinv : Admissible (fun x => 1 / (1 - r x ^ 2)) := admissible_one_div_one_sub hr2 hr1
  have hq : Admissible (fun x => Rp x / (1 - r x ^ 2)) := by
    have h := admissible_mul hRp hinv
    refine ⟨fun a b hab => ?_, fun x => ?_⟩
    · have h' := h.1 hab
      simp only [Pi.mul_apply, mul_one_div] at h'
      exact h'
    · have h' := h.2 x
      simp only [Pi.mul_apply, mul_one_div] at h'
      exact h'
  have hq1 : ∀ x, 1 ≤ Rp x / (1 - r x ^ 2) := fun x => by
    have h0 : 0 < 1 - r x ^ 2 := by linarith [hr1 x]
    have h1 : 1 - r x ^ 2 ≤ 1 := by linarith [sq_nonneg (r x)]
    rw [le_div_iff₀ h0]
    nlinarith [hRp1 x]
  have hsum : Admissible (fun x => εH x + εne x + (2 * Real.sqrt (ΓE x * (lam + εH x)) + ΓE x) +
      ζ x * Λnc) := admissible_add (admissible_add (admissible_add hεH hεne) hrem) hpar
  refine ⟨hrem, hpar, ?_, ?_⟩
  · exact admissible_add (admissible_add (admissible_add
      (admissible_mul (admissible_sub_one hq hq1) (hc hΛp)) (admissible_mul hq hsum))
      (admissible_mul hεV (hc (sq_nonneg ΛD))))
      (admissible_mul (hc (by positivity : (0 : ℝ) ≤ 2 * ΛD)) hηQ)
  · exact admissible_add (admissible_add (admissible_add (admissible_add (hc hΛp) hεH) hεne)
      hrem) hpar

/-- **`lem:spectral-monotone` (d), the local bound**: if `ε^loc` is admissible, `∏_i α⁻_i` is
nonincreasing, and `ℓ^loc = ∏_i α⁻_i - ε^loc > 0` at the endpoint `r₀`, then `ℓ^loc > 0` on the
whole box and `(ε^loc/ℓ^loc)²` is admissible. -/
theorem localvariance_monotone (εloc αm : Δ → ℝ) (hε : Admissible εloc) (hα : Antitone αm)
    (xp : Δ) (hxp : ∀ x, x ≤ xp) (hℓ : 0 < αm xp - εloc xp) :
    (∀ x, 0 < αm x - εloc x) ∧
      Admissible (fun x => (εloc x / (αm x - εloc x)) ^ 2) := by
  have hanti : Antitone (fun x => αm x - εloc x) := fun a b hab => by
    simp only
    linarith [hα hab, hε.1 hab]
  have hpos : ∀ x, 0 < αm x - εloc x := fun x => lt_of_lt_of_le hℓ (hanti (hxp x))
  exact ⟨hpos, admissible_sq_div_antitone hε hanti hpos⟩

/-- The denominators `κ = 2^t/(1 - ε⁻)` of `lem:push:localvariance` (b) are admissible when `ε⁻`
is admissible and below one (`lem:spectral-monotone` (d)). -/
theorem admissible_kappa {e : Δ → ℝ} (he : Admissible e) (h1 : ∀ x, e x < 1) (t : ℕ) :
    Admissible (fun x => 2 ^ t / (1 - e x)) := by
  have h := admissible_mul (admissible_const (Δ := Δ) (by positivity : (0 : ℝ) ≤ 2 ^ t))
    (admissible_one_div_one_sub he h1)
  refine ⟨fun a b hab => ?_, fun x => ?_⟩
  · have h' := h.1 hab
    simp only [Pi.mul_apply, mul_one_div] at h'
    exact h'
  · have h' := h.2 x
    simp only [Pi.mul_apply, mul_one_div] at h'
    exact h'

/-- **The conversions** in the proof of `lem:spectral-monotone` (a), with `r = p^{-1/2}`:
`p/(p-1) = 1/(1 - r²)`, `1/(p-1) = r²/(1 - r²)`, `1/((p-1) r) = r/(1 - r²)`, and
`n/((p - n) r) = n r/(1 - n r²)` for `p > n`. -/
theorem p_conversions {p n : ℝ} (hp : 1 < p) (hpn : n < p) :
    p / (p - 1) = 1 / (1 - (1 / Real.sqrt p) ^ 2) ∧
    1 / (p - 1) = (1 / Real.sqrt p) ^ 2 / (1 - (1 / Real.sqrt p) ^ 2) ∧
    1 / ((p - 1) * (1 / Real.sqrt p)) = (1 / Real.sqrt p) / (1 - (1 / Real.sqrt p) ^ 2) ∧
    n / ((p - n) * (1 / Real.sqrt p)) =
      n * (1 / Real.sqrt p) / (1 - n * (1 / Real.sqrt p) ^ 2) := by
  have hp0 : 0 < p := by linarith
  have hs : Real.sqrt p ^ 2 = p := Real.sq_sqrt hp0.le
  have hs0 : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp0
  have hr2 : (1 / Real.sqrt p) ^ 2 = 1 / p := by rw [div_pow, one_pow, hs]
  have h1 : p - 1 ≠ 0 := by linarith
  have h2 : p - n ≠ 0 := by linarith
  have h3 : 1 - 1 / p ≠ 0 := (sub_pos.mpr ((div_lt_one hp0).mpr hp)).ne'
  have h4 : 1 - n * (1 / p) ≠ 0 := by
    have : n * (1 / p) < 1 := by rw [mul_one_div, div_lt_one hp0]; exact hpn
    linarith
  rw [hr2]
  refine ⟨?_, ?_, ?_, ?_⟩
  · field_simp
  · field_simp
  · have hs' : Real.sqrt p * Real.sqrt p = p := Real.mul_self_sqrt hp0.le
    field_simp
    nlinarith [hs']
  · have hs' : Real.sqrt p * Real.sqrt p = p := Real.mul_self_sqrt hp0.le
    field_simp
    nlinarith [hs']

end Sarkozy.Spectral
