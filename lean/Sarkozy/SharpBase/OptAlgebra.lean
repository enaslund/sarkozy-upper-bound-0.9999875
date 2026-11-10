module

public import Sarkozy.DensityChain2.HfoldAlgebra

@[expose] public section

/-!
# The optimal ratio in DC2's `hfold`: the remainder `√(A₊A₋) − W√(M₊M₋)`

SH2 (7 November 2026). DC2's per-choice hypothesis `hfold` (the AM–GM step of `lem:sharp-first`
after `lem:record:folded-energy`) asks for `t > 0`, `M_±`, `r_±` with `t M₊ + M₋/t ≤ R`,
`𝔈_±(φ) ≤ BG(φ) M_± + r_±(φ)` and a remainder `rch ≥ (t ∑ w r₊ + (∑ w r₋)/t)/2`.

DC3's witnesses (`HfoldAlgebra`) take `t = √(M₋/M₊)`. Then
`rch = (√(M₋/M₊) R₊ + √(M₊/M₋) R₋)/2`, where `R_± = ∑ w r_±` are the weighted remainders. The
ratio `M₋/M₊` is a ratio of local-density factors of the two halves of the tag cut, which is not
bounded in mean over the index `ω` (negative moments of local densities). So DC3's `rch` need
not be summable.

Here the ratio is re-optimized against the **whole** bounds `A_± = W M_± + R_±`
(`W = ∑ w BG`): `t' = √(A₋/A₊)`, `M'₊ = s/t'`, `M'₋ = s t'` with `s = √(M₊M₋)`. The main
condition still holds (`t' M'₊ + M'₋/t' = 2s ≤ t M₊ + M₋/t`, AM–GM), and the remainder becomes
`rchOptVal = (t'A₊ + A₋/t')/2 − W s`, which is `√(A₊A₋) − W√(M₊M₋)` when `A_± > 0`:
at most `√(W M₊ R₋) + √(W M₋ R₊) + √(R₊ R₋)`, the paper's cross terms (proof of
`lem:sharp-first`: "the error terms are density-linear"; their mean over `ω` is controlled by
Cauchy–Schwarz with the local-density means, at the cost of halving the dc exponent).

* `two_sqrt_le`: `2√(xy) ≤ t x + y/t`;
* `optT`, `rchOptVal`, `rchOptVal_nonneg`;
* **`hfold_reopt`**: new witnesses from any witnesses, with remainder `rchOptVal`;
* `rchOpt`: `rchOptVal` at DC3's explicit witnesses (`hfoldM`, `hfoldR`);
* **`hfold_choice_opt`**: DC3's `hfold_choice` with the remainder `rchOpt`; `rchOpt_nonneg`.
-/

namespace Sarkozy.SharpBase

open Finset
open scoped BigOperators
open Sarkozy.DensityChain2

theorem two_sqrt_mul_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    2 * Real.sqrt (x * y) ≤ x + y := by
  rw [Real.sqrt_mul hx]
  nlinarith [sq_nonneg (Real.sqrt x - Real.sqrt y), Real.sq_sqrt hx, Real.sq_sqrt hy]

/-- **AM–GM with a ratio**: `2√(xy) ≤ t x + y/t` for `x, y ≥ 0`, `t > 0`. -/
theorem two_sqrt_le {x y t : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) (ht : 0 < t) :
    2 * Real.sqrt (x * y) ≤ t * x + y / t := by
  have e : x * y = (t * x) * (y / t) := by
    field_simp
  rw [e]
  exact two_sqrt_mul_le (mul_nonneg ht.le hx) (div_nonneg hy ht.le)

open Classical in
/-- The optimal ratio `t' = √(A₋/A₊)` (or `1` if one of `A_±` is not positive). -/
noncomputable def optT (Ap Am : ℝ) : ℝ := if 0 < Ap ∧ 0 < Am then Real.sqrt (Am / Ap) else 1

theorem optT_pos (Ap Am : ℝ) : 0 < optT Ap Am := by
  unfold optT
  split_ifs with h
  · exact Real.sqrt_pos.mpr (div_pos h.2 h.1)
  · exact one_pos

/-- **The re-optimized remainder** `(t'A₊ + A₋/t')/2 − W√(M₊M₋)`, `A_± = W M_± + R_±`,
`t' = optT A₊ A₋`. -/
noncomputable def rchOptVal (W Mp Mm Rp Rm : ℝ) : ℝ :=
  (optT (W * Mp + Rp) (W * Mm + Rm) * (W * Mp + Rp) +
      (W * Mm + Rm) / optT (W * Mp + Rp) (W * Mm + Rm)) / 2 - W * Real.sqrt (Mp * Mm)

/-- In the nondegenerate case `rchOptVal = √(A₊A₋) − W√(M₊M₋)`. -/
theorem rchOptVal_eq {W Mp Mm Rp Rm : ℝ} (hp : 0 < W * Mp + Rp) (hm : 0 < W * Mm + Rm) :
    rchOptVal W Mp Mm Rp Rm =
      Real.sqrt ((W * Mp + Rp) * (W * Mm + Rm)) - W * Real.sqrt (Mp * Mm) := by
  unfold rchOptVal optT
  simp only [hp, hm, and_self, ↓reduceIte]
  have hq : 0 < (W * Mm + Rm) / (W * Mp + Rp) := div_pos hm hp
  have hs := Real.sqrt_pos.mpr hq
  have hsq := Real.sq_sqrt hq.le
  have h1 : Real.sqrt ((W * Mm + Rm) / (W * Mp + Rp)) * (W * Mp + Rp) =
      Real.sqrt ((W * Mp + Rp) * (W * Mm + Rm)) := by
    rw [show (W * Mp + Rp) * (W * Mm + Rm) =
        ((W * Mm + Rm) / (W * Mp + Rp)) * (W * Mp + Rp) ^ 2 by field_simp,
      Real.sqrt_mul hq.le, Real.sqrt_sq hp.le]
  have h2 : (W * Mm + Rm) / Real.sqrt ((W * Mm + Rm) / (W * Mp + Rp)) =
      Real.sqrt ((W * Mm + Rm) / (W * Mp + Rp)) * (W * Mp + Rp) := by
    rw [div_eq_iff hs.ne']
    have : Real.sqrt ((W * Mm + Rm) / (W * Mp + Rp)) * (W * Mp + Rp) *
        Real.sqrt ((W * Mm + Rm) / (W * Mp + Rp)) =
        Real.sqrt ((W * Mm + Rm) / (W * Mp + Rp)) ^ 2 * (W * Mp + Rp) := by ring
    rw [this, hsq]
    field_simp
  rw [h2, h1]
  ring

theorem rchOptVal_nonneg {W Mp Mm Rp Rm : ℝ} (hW : 0 ≤ W) (hMp : 0 ≤ Mp) (hMm : 0 ≤ Mm)
    (hRp : 0 ≤ Rp) (hRm : 0 ≤ Rm) : 0 ≤ rchOptVal W Mp Mm Rp Rm := by
  have hAp : 0 ≤ W * Mp + Rp := add_nonneg (mul_nonneg hW hMp) hRp
  have hAm : 0 ≤ W * Mm + Rm := add_nonneg (mul_nonneg hW hMm) hRm
  have h1 := two_sqrt_le hAp hAm (optT_pos (W * Mp + Rp) (W * Mm + Rm))
  have h2 : Real.sqrt ((W * Mp) * (W * Mm)) ≤ Real.sqrt ((W * Mp + Rp) * (W * Mm + Rm)) :=
    Real.sqrt_le_sqrt (mul_le_mul (by linarith) (by linarith) (mul_nonneg hW hMm) hAp)
  have h3 : Real.sqrt ((W * Mp) * (W * Mm)) = W * Real.sqrt (Mp * Mm) := by
    rw [show (W * Mp) * (W * Mm) = W ^ 2 * (Mp * Mm) by ring, Real.sqrt_mul (sq_nonneg W),
      Real.sqrt_sq hW]
  unfold rchOptVal
  linarith

variable {Φ : Type} [Fintype Φ]

/-- **Re-optimizing the ratio of `hfold`**: from any witnesses `t, M_± ≥ 0, r_±` of DC2's
per-choice conditions, the witnesses `t' = optT A₊ A₋`, `M'₊ = s/t'`, `M'₋ = s t'`,
`r'_±(φ) = r_±(φ) + BG(φ)(M_± − M'_±)` (`s = √(M₊M₋)`) satisfy them with the remainder
`rchOptVal W M₊ M₋ R₊ R₋`. -/
theorem hfold_reopt (adm : Φ → Prop) {t Mp Mm R : ℝ} (ht : 0 < t) (hMp : 0 ≤ Mp)
    (hMm : 0 ≤ Mm) (hR : t * Mp + Mm / t ≤ R) (w BG Fp Fm rp rm : Φ → ℝ)
    (hp : ∀ φ, adm φ → Fp φ ≤ BG φ * Mp + rp φ) (hm : ∀ φ, adm φ → Fm φ ≤ BG φ * Mm + rm φ) :
    ∃ (t' Mp' Mm' : ℝ) (rp' rm' : Φ → ℝ), 0 < t' ∧ t' * Mp' + Mm' / t' ≤ R ∧
      (∀ φ, adm φ → Fp φ ≤ BG φ * Mp' + rp' φ) ∧ (∀ φ, adm φ → Fm φ ≤ BG φ * Mm' + rm' φ) ∧
      (t' * ∑ φ, w φ * rp' φ + (∑ φ, w φ * rm' φ) / t') / 2 ≤
        rchOptVal (∑ φ, w φ * BG φ) Mp Mm (∑ φ, w φ * rp φ) (∑ φ, w φ * rm φ) := by
  set W := ∑ φ, w φ * BG φ with hW
  set Rp := ∑ φ, w φ * rp φ with hRp
  set Rm := ∑ φ, w φ * rm φ with hRm
  set t' := optT (W * Mp + Rp) (W * Mm + Rm) with ht'
  have ht'0 : 0 < t' := optT_pos _ _
  have ht'ne : t' ≠ 0 := ht'0.ne'
  set s := Real.sqrt (Mp * Mm) with hs
  refine ⟨t', s / t', s * t', fun φ => rp φ + BG φ * (Mp - s / t'),
    fun φ => rm φ + BG φ * (Mm - s * t'), ht'0, ?_, ?_, ?_, ?_⟩
  · have e : t' * (s / t') + s * t' / t' = 2 * s := by
      field_simp
      ring
    rw [e]
    exact (two_sqrt_le hMp hMm ht).trans hR
  · intro φ hφ
    have e : BG φ * (s / t') + (rp φ + BG φ * (Mp - s / t')) = BG φ * Mp + rp φ := by ring
    linarith [hp φ hφ]
  · intro φ hφ
    have e : BG φ * (s * t') + (rm φ + BG φ * (Mm - s * t')) = BG φ * Mm + rm φ := by ring
    linarith [hm φ hφ]
  · apply le_of_eq
    have e1 : ∑ φ, w φ * (rp φ + BG φ * (Mp - s / t')) = Rp + W * (Mp - s / t') := by
      rw [hRp, hW, Finset.sum_mul, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun φ _ => by ring
    have e2 : ∑ φ, w φ * (rm φ + BG φ * (Mm - s * t')) = Rm + W * (Mm - s * t') := by
      rw [hRm, hW, Finset.sum_mul, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun φ _ => by ring
    rw [e1, e2]
    unfold rchOptVal
    rw [← ht', ← hs]
    field_simp
    ring

/-- **The re-optimized remainder at DC3's explicit witnesses** (`HfoldAlgebra.hfoldM`,
`hfoldR`): `rchOptVal (∑ w BG) M₊ M₋ (∑ w r₊) (∑ w r₋)`. It replaces DC3's `rchVal`. -/
noncomputable def rchOpt (small : Φ → Prop) (K₀ Pp Pm Cr : ℝ) (w BG Gp Gm Fp Fm : Φ → ℝ) : ℝ :=
  rchOptVal (∑ φ, w φ * BG φ) (hfoldM K₀ Pp Pm Pp) (hfoldM K₀ Pp Pm Pm)
    (∑ φ, w φ * hfoldR small K₀ Pp Pm Pp Cr BG Gp Fp φ)
    (∑ φ, w φ * hfoldR small K₀ Pp Pm Pm Cr BG Gm Fm φ)

theorem hfoldM_nonneg {K₀ Pp Pm P : ℝ} (hK₀ : 0 ≤ K₀) (hP : 0 ≤ P) :
    0 ≤ hfoldM K₀ Pp Pm P := by
  unfold hfoldM
  split_ifs
  · exact mul_nonneg hK₀ hP
  · exact le_rfl

/-- **One choice of `hfold` with the re-optimized remainder** (DC3's `hfold_choice` followed by
`hfold_reopt`). Same hypotheses as `hfold_choice`. -/
theorem hfold_choice_opt (small adm : Φ → Prop) {K₀ Pp Pm P0 Cr R : ℝ} (hK₀ : 0 ≤ K₀)
    (hPp : 0 ≤ Pp) (hPm : 0 ≤ Pm) (hP0 : 0 ≤ P0) (hprod : Pp * Pm = P0 ^ 2)
    (hR : 2 * (K₀ * P0) ≤ R) (hR0 : 0 ≤ R)
    (w BG Gp Gm Fp Fm : Φ → ℝ) (hBG : ∀ φ, 0 ≤ BG φ)
    (hp : ∀ φ, adm φ → small φ → Fp φ ≤ BG φ * (K₀ * Pp) + Gp φ * Cr)
    (hm : ∀ φ, adm φ → small φ → Fm φ ≤ BG φ * (K₀ * Pm) + Gm φ * Cr) :
    ∃ (t Mp Mm : ℝ) (rp rm : Φ → ℝ), 0 < t ∧ t * Mp + Mm / t ≤ R ∧
      (∀ φ, adm φ → Fp φ ≤ BG φ * Mp + rp φ) ∧ (∀ φ, adm φ → Fm φ ≤ BG φ * Mm + rm φ) ∧
      (t * ∑ φ, w φ * rp φ + (∑ φ, w φ * rm φ) / t) / 2 ≤
        rchOpt small K₀ Pp Pm Cr w BG Gp Gm Fp Fm := by
  obtain ⟨h1, h2, h3, h4, -⟩ := hfold_choice small adm hK₀ hPp hPm hP0 hprod hR hR0 w BG Gp Gm
    Fp Fm hBG hp hm
  exact hfold_reopt adm h1 (hfoldM_nonneg hK₀ hPp) (hfoldM_nonneg hK₀ hPm) h2 w BG Fp Fm _ _ h3 h4

/-- **`rchOpt ≥ 0`**, so a sum of `rchOpt` over the tags dominates each of them. -/
theorem rchOpt_nonneg (small : Φ → Prop) {K₀ Pp Pm Cr : ℝ} (hK₀ : 0 ≤ K₀) (hPp : 0 ≤ Pp)
    (hPm : 0 ≤ Pm) (hCr : 0 ≤ Cr) (w BG Gp Gm Fp Fm : Φ → ℝ) (hw : ∀ φ, 0 ≤ w φ)
    (hBG : ∀ φ, 0 ≤ BG φ) (hGp : ∀ φ, 0 ≤ Gp φ) (hGm : ∀ φ, 0 ≤ Gm φ) :
    0 ≤ rchOpt small K₀ Pp Pm Cr w BG Gp Gm Fp Fm :=
  rchOptVal_nonneg (sum_nonneg fun φ _ => mul_nonneg (hw φ) (hBG φ))
    (hfoldM_nonneg hK₀ hPp) (hfoldM_nonneg hK₀ hPm)
    (sum_nonneg fun φ _ =>
      mul_nonneg (hw φ) (hfoldR_nonneg small hK₀ hPp hCr BG Gp Fp hBG hGp φ))
    (sum_nonneg fun φ _ =>
      mul_nonneg (hw φ) (hfoldR_nonneg small hK₀ hPm hCr BG Gm Fm hBG hGm φ))

/-- **The cross-term bound**: `√(A₊A₋) − W√(M₊M₋) ≤ √(W M₊ R₋) + √(W M₋ R₊) + √(R₊ R₋)`
(nondegenerate case), the form in which the paper sums the error terms of `lem:sharp-first`. -/
theorem rchOptVal_le_cross {W Mp Mm Rp Rm : ℝ} (hW : 0 ≤ W) (hMp : 0 ≤ Mp) (hMm : 0 ≤ Mm)
    (hRp : 0 ≤ Rp) (hRm : 0 ≤ Rm) (hp : 0 < W * Mp + Rp) (hm : 0 < W * Mm + Rm) :
    rchOptVal W Mp Mm Rp Rm ≤
      Real.sqrt (W * Mp * Rm) + Real.sqrt (W * Mm * Rp) + Real.sqrt (Rp * Rm) := by
  rw [rchOptVal_eq hp hm]
  have hx : 0 ≤ W * Mp := mul_nonneg hW hMp
  have hy : 0 ≤ W * Mm := mul_nonneg hW hMm
  -- √((x+a)(y+b)) ≤ √(xy) + √(xb) + √(ay) + √(ab), by squaring
  have hxy : Real.sqrt ((W * Mp) * (W * Mm)) = W * Real.sqrt (Mp * Mm) := by
    rw [show (W * Mp) * (W * Mm) = W ^ 2 * (Mp * Mm) by ring, Real.sqrt_mul (sq_nonneg W),
      Real.sqrt_sq hW]
  have key : Real.sqrt ((W * Mp + Rp) * (W * Mm + Rm)) ≤
      Real.sqrt ((W * Mp) * (W * Mm)) + Real.sqrt (W * Mp * Rm) + Real.sqrt (W * Mm * Rp) +
        Real.sqrt (Rp * Rm) := by
    rw [Real.sqrt_le_left (by positivity)]
    have s1 := Real.sq_sqrt (mul_nonneg hx hy)
    have s2 := Real.sq_sqrt (mul_nonneg hx hRm)
    have s3 := Real.sq_sqrt (mul_nonneg hy hRp)
    have s4 := Real.sq_sqrt (mul_nonneg hRp hRm)
    have e1 : Real.sqrt ((W * Mp) * (W * Mm)) * Real.sqrt (Rp * Rm) =
        Real.sqrt (W * Mp * Rm) * Real.sqrt (W * Mm * Rp) := by
      rw [← Real.sqrt_mul (mul_nonneg hx hy), ← Real.sqrt_mul (mul_nonneg hx hRm)]
      congr 1
      ring
    nlinarith [Real.sqrt_nonneg ((W * Mp) * (W * Mm)), Real.sqrt_nonneg (W * Mp * Rm),
      Real.sqrt_nonneg (W * Mm * Rp), Real.sqrt_nonneg (Rp * Rm),
      mul_nonneg (Real.sqrt_nonneg ((W * Mp) * (W * Mm))) (Real.sqrt_nonneg (W * Mp * Rm)),
      mul_nonneg (Real.sqrt_nonneg ((W * Mp) * (W * Mm))) (Real.sqrt_nonneg (W * Mm * Rp)),
      mul_nonneg (Real.sqrt_nonneg (W * Mp * Rm)) (Real.sqrt_nonneg (Rp * Rm)),
      mul_nonneg (Real.sqrt_nonneg (W * Mm * Rp)) (Real.sqrt_nonneg (Rp * Rm))]
  linarith

end Sarkozy.SharpBase
