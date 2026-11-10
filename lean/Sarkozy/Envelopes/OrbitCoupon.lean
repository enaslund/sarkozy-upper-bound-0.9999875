module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

@[expose] public section

/-!
# The orbit coupon (`lem:orbit-coupon`)

`paper/sections/23_envelopes.tex`, `lem:orbit-coupon` (i), (ii), (iv): the orbit decomposition of a
collected combination of couplings under a reflection, and the coupon it earns.

**Setting (abstract, with the paper's hypotheses).** The couplings `C` of the collected expansion
`K = ∑_C c(C) [C]_ω` form a finite type `ι`; the reflection `R_h` acts on them by an involution
`h : ι → ι` (`R_{h*}[C]_ω = [hC]_ω`). The placed couplings are vectors `e C` of a real vector space
(the signed measures), and the error `Y^{Ñ}[·] - Y^{Ñ₀}[·]` is a linear functional `Δ` on it. The
paper's analytic input, from the sharp first comparison of Part III and the category `e_s`
(proof of (i)), enters as two
hypotheses:
* every coupling has `|Δ [C]| ≤ R` (`R = R_err` up to the energy errors);
* every `R_h`-invariant coupling, in particular every orbit average `½([C] + [hC])`, has
  `|Δ| ≤ R - s` (`s = e^{t U_inv} t δ_s`, the symmetric-price saving).

**Main results.**
* `orbit_coupon`: `|Δ K| ≤ M R - M_h(K) s`, with `M = ∑ |c(C)|` and
  `M_h(K) = ∑_C 1[c(C) c(hC) > 0] min(|c(C)|, |c(hC)|)` (`orbitMass`), a fixed coupling counting
  with its full `|c(C)|`; this is (i).
* `orbit_coupon_split`: the form of (i) in which only one category `Δ_s` of the error improves and
  the other categories `Δ_rest` keep their bound ((iii)).
* `orbit_coupon_two`: (ii), two reflections on disjoint categories.
* `orbitMass_le`, `orbit_coupon_gate`, `orbit_coupon_gate_two`: the gate (iv).

**Proof.** Instead of listing the orbits, put `b(C) = sgn(c(C)) min(|c(C)|, |c(hC)|)` when
`c(C) c(hC) > 0` and `b(C) = 0` otherwise. Then `b(hC) = b(C)`, so
`∑ b(C)[C] = ∑ b(C) ½([C] + [hC])`, and `|c(C) - b(C)| = |c(C)| - |b(C)|`; this is the paper's
decomposition `c(C)C + c(hC)hC = 2b (C + hC)/2 + (c(C) - b)C + (c(hC) - b)hC` summed over the
orbits.
-/

namespace Sarkozy.Envelopes

open Finset

variable {ι : Type*} [Fintype ι]

/-- The matched part `b(C)` of the coefficient of `C` in the orbit decomposition. -/
noncomputable def orbitPart (h : ι → ι) (c : ι → ℝ) (C : ι) : ℝ :=
  if 0 < c C * c (h C) then
    (if 0 < c C then min |c C| |c (h C)| else -min |c C| |c (h C)|)
  else 0

/-- The orbit mass `M_h(K) = ∑_C 1[c(C) c(hC) > 0] min(|c(C)|, |c(hC)|)` (`lem:orbit-coupon`). -/
noncomputable def orbitMass (h : ι → ι) (c : ι → ℝ) : ℝ :=
  ∑ C, if 0 < c C * c (h C) then min |c C| |c (h C)| else 0

/-- The coupling mass `M = ∑_C |c(C)|` (`lem:oct24:mask-schur`(a)). -/
noncomputable def couplingMass (c : ι → ℝ) : ℝ := ∑ C, |c C|

omit [Fintype ι] in
theorem abs_orbitPart (h : ι → ι) (c : ι → ℝ) (C : ι) :
    |orbitPart h c C| = if 0 < c C * c (h C) then min |c C| |c (h C)| else 0 := by
  have h0 : 0 ≤ min |c C| |c (h C)| := le_min (abs_nonneg _) (abs_nonneg _)
  unfold orbitPart
  split_ifs <;> simp [abs_of_nonneg h0]

omit [Fintype ι] in
theorem orbitPart_comm {h : ι → ι} (hh : ∀ C, h (h C) = C) (c : ι → ℝ) (C : ι) :
    orbitPart h c (h C) = orbitPart h c C := by
  unfold orbitPart
  rw [hh C, mul_comm (c (h C)) (c C), min_comm |c (h C)| |c C|]
  by_cases hp : 0 < c C * c (h C)
  · simp only [hp, ↓reduceIte]
    have hiff : 0 < c (h C) ↔ 0 < c C := by
      constructor
      · intro h1; by_contra h2; push Not at h2
        nlinarith
      · intro h1; by_contra h2; push Not at h2
        nlinarith
    by_cases h1 : 0 < c C
    · simp only [h1, hiff.2 h1, ↓reduceIte]
    · have h1' : ¬ 0 < c (h C) := fun h2 => h1 (hiff.1 h2)
      simp only [h1, h1', ↓reduceIte]
  · simp only [hp, ↓reduceIte]

omit [Fintype ι] in
theorem abs_sub_orbitPart (h : ι → ι) (c : ι → ℝ) (C : ι) :
    |c C - orbitPart h c C| = |c C| - |orbitPart h c C| := by
  rw [abs_orbitPart]
  unfold orbitPart
  by_cases hp : 0 < c C * c (h C)
  · simp only [hp, ↓reduceIte]
    by_cases h1 : 0 < c C
    · simp only [h1, ↓reduceIte]
      have hm : min |c C| |c (h C)| ≤ |c C| := min_le_left _ _
      have hm0 : 0 ≤ min |c C| |c (h C)| := le_min (abs_nonneg _) (abs_nonneg _)
      rw [abs_of_pos h1] at hm ⊢
      rw [abs_of_nonneg (by linarith)]
    · simp only [h1, ↓reduceIte]
      have hneg : c C < 0 := by
        rcases lt_trichotomy (c C) 0 with hlt | heq | hgt
        · exact hlt
        · rw [heq, zero_mul] at hp; exact absurd hp (lt_irrefl 0)
        · exact absurd hgt h1
      have hm : min |c C| |c (h C)| ≤ |c C| := min_le_left _ _
      have hm0 : 0 ≤ min |c C| |c (h C)| := le_min (abs_nonneg _) (abs_nonneg _)
      rw [abs_of_neg hneg] at hm ⊢
      rw [abs_of_nonpos (by linarith)]
      ring
  · simp only [hp, ↓reduceIte, sub_zero]

theorem sum_abs_orbitPart (h : ι → ι) (c : ι → ℝ) :
    ∑ C, |orbitPart h c C| = orbitMass h c := by
  unfold orbitMass
  exact sum_congr rfl fun C _ => abs_orbitPart h c C

theorem orbitMass_nonneg (h : ι → ι) (c : ι → ℝ) : 0 ≤ orbitMass h c := by
  rw [← sum_abs_orbitPart]
  exact sum_nonneg fun C _ => abs_nonneg _

/-- **`lem:orbit-coupon`(iv), first claim.** `M_h ≤ M`. -/
theorem orbitMass_le (h : ι → ι) (c : ι → ℝ) : orbitMass h c ≤ couplingMass c := by
  unfold orbitMass couplingMass
  refine sum_le_sum fun C _ => ?_
  split_ifs
  · exact min_le_left _ _
  · exact abs_nonneg _

/-- The matched part may be spread over the orbit: `∑ b(C)[C] = ∑ b(C) ½([C] + [hC])`. -/
theorem sum_orbitPart_avg {V : Type*} [AddCommGroup V] [Module ℝ V] {h : ι → ι}
    (hh : ∀ C, h (h C) = C) (c : ι → ℝ) (e : ι → V) :
    ∑ C, orbitPart h c C • e C =
      ∑ C, orbitPart h c C • ((1 / 2 : ℝ) • (e C + e (h C))) := by
  have hinv : Function.Involutive h := hh
  have hswap : ∑ C, orbitPart h c C • e (h C) = ∑ C, orbitPart h c C • e C := by
    have e0 : ∑ C, orbitPart h c C • e (h C) = ∑ C, orbitPart h c (h C) • e (h C) :=
      sum_congr rfl fun C _ => by rw [orbitPart_comm hh]
    rw [e0]
    exact Equiv.sum_comp (hinv.toPerm h) (fun C => orbitPart h c C • e C)
  simp only [smul_add, smul_smul, sum_add_distrib]
  have e1 : ∑ C, (orbitPart h c C * (1 / 2 : ℝ)) • e C =
      (1 / 2 : ℝ) • ∑ C, orbitPart h c C • e C := by
    rw [smul_sum]; refine sum_congr rfl fun C _ => ?_; rw [smul_smul, mul_comm]
  have e2 : ∑ C, (orbitPart h c C * (1 / 2 : ℝ)) • e (h C) =
      (1 / 2 : ℝ) • ∑ C, orbitPart h c C • e C := by
    rw [← hswap, smul_sum]; refine sum_congr rfl fun C _ => ?_; rw [smul_smul, mul_comm]
  rw [e1, e2, ← add_smul]
  norm_num

/-- **`lem:orbit-coupon`(i).** Let `h` be an involution of the couplings, `Δ` linear, and suppose
`|Δ [C]| ≤ R` for every coupling and `|Δ (½([C] + [hC]))| ≤ R - s` for every orbit average (the
`R_h`-invariant couplings). Then for `K = ∑ c(C)[C]`,
`|Δ K| ≤ M R - M_h(K) s`. -/
theorem orbit_coupon {V : Type*} [AddCommGroup V] [Module ℝ V] {h : ι → ι}
    (hh : ∀ C, h (h C) = C) (c : ι → ℝ) (e : ι → V) (Δ : V →ₗ[ℝ] ℝ) {R s : ℝ}
    (hR : ∀ C, |Δ (e C)| ≤ R) (hs : ∀ C, |Δ ((1 / 2 : ℝ) • (e C + e (h C)))| ≤ R - s) :
    |Δ (∑ C, c C • e C)| ≤ couplingMass c * R - orbitMass h c * s := by
  set b := orbitPart h c
  have hsplit : ∑ C, c C • e C =
      ∑ C, b C • ((1 / 2 : ℝ) • (e C + e (h C))) + ∑ C, (c C - b C) • e C := by
    rw [← sum_orbitPart_avg hh c e, ← sum_add_distrib]
    refine sum_congr rfl fun C _ => ?_
    rw [← add_smul]; congr 1; ring
  rw [hsplit, map_add, map_sum, map_sum]
  have h1 : |∑ C, Δ (b C • ((1 / 2 : ℝ) • (e C + e (h C))))| ≤ ∑ C, |b C| * (R - s) := by
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun C _ => ?_)
    rw [map_smul, smul_eq_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (hs C) (abs_nonneg _)
  have h2 : |∑ C, Δ ((c C - b C) • e C)| ≤ ∑ C, (|c C| - |b C|) * R := by
    refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun C _ => ?_)
    rw [map_smul, smul_eq_mul, abs_mul, abs_sub_orbitPart]
    have : 0 ≤ |c C| - |b C| := by
      rw [← abs_sub_orbitPart]; exact abs_nonneg _
    exact mul_le_mul_of_nonneg_left (hR C) this
  have e3 : ∑ C, |b C| * (R - s) + ∑ C, (|c C| - |b C|) * R =
      couplingMass c * R - orbitMass h c * s := by
    have e4 : ∑ C, |b C| * (R - s) + ∑ C, (|c C| - |b C|) * R =
        ∑ C, (|c C| * R - |b C| * s) := by
      rw [← sum_add_distrib]; exact sum_congr rfl fun C _ => by ring
    rw [e4, sum_sub_distrib, ← sum_mul, ← sum_mul, sum_abs_orbitPart]
    rfl
  calc _ ≤ |∑ C, Δ (b C • ((1 / 2 : ℝ) • (e C + e (h C))))| +
        |∑ C, Δ ((c C - b C) • e C)| := abs_add_le _ _
    _ ≤ ∑ C, |b C| * (R - s) + ∑ C, (|c C| - |b C|) * R := add_le_add h1 h2
    _ = _ := e3

/-- A linear functional bounded by `R` on every coupling is bounded by `M R` on `K`. -/
theorem abs_le_couplingMass {V : Type*} [AddCommGroup V] [Module ℝ V] (c : ι → ℝ)
    (e : ι → V) (Δ : V →ₗ[ℝ] ℝ) {R : ℝ} (hR : ∀ C, |Δ (e C)| ≤ R) :
    |Δ (∑ C, c C • e C)| ≤ couplingMass c * R := by
  rw [map_sum]
  simp only [map_smul, smul_eq_mul]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  rw [couplingMass, sum_mul]
  refine sum_le_sum fun C _ => ?_
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_left (hR C) (abs_nonneg _)

/-- **`lem:orbit-coupon`(i) with (iii).** The error splits into the category `Δ_s` of exactly one
folded difference of tag `s`, which improves on the `R_h`-invariant couplings, and the other
categories `Δ_rest`, which keep their bound `R_rest`. Then
`|Δ_s K + Δ_rest K| ≤ M (R_s + R_rest) - M_h(K) s'`. -/
theorem orbit_coupon_split {V : Type*} [AddCommGroup V] [Module ℝ V] {h : ι → ι}
    (hh : ∀ C, h (h C) = C) (c : ι → ℝ) (e : ι → V) (Δs Δr : V →ₗ[ℝ] ℝ) {Rs Rr s : ℝ}
    (hRs : ∀ C, |Δs (e C)| ≤ Rs) (hs : ∀ C, |Δs ((1 / 2 : ℝ) • (e C + e (h C)))| ≤ Rs - s)
    (hRr : ∀ C, |Δr (e C)| ≤ Rr) :
    |(Δs + Δr) (∑ C, c C • e C)| ≤ couplingMass c * (Rs + Rr) - orbitMass h c * s := by
  have h1 := orbit_coupon hh c e Δs hRs hs
  have h2 := abs_le_couplingMass c e Δr hRr
  rw [LinearMap.add_apply]
  calc _ ≤ |Δs (∑ C, c C • e C)| + |Δr (∑ C, c C • e C)| := abs_add_le _ _
    _ ≤ (couplingMass c * Rs - orbitMass h c * s) + couplingMass c * Rr := add_le_add h1 h2
    _ = _ := by ring

/-- **`lem:orbit-coupon`(ii).** Two reflections `h₁, h₃` used at once on the disjoint categories
`Δ₀, Δ₁` (and the remaining categories `Δ_rest` unchanged):
`|ΔK| ≤ M (R₀ + R₁ + R_rest) - (M_{h₁} + M_{h₃}) s`. -/
theorem orbit_coupon_two {V : Type*} [AddCommGroup V] [Module ℝ V] {h₁ h₃ : ι → ι}
    (hh₁ : ∀ C, h₁ (h₁ C) = C) (hh₃ : ∀ C, h₃ (h₃ C) = C) (c : ι → ℝ) (e : ι → V)
    (Δ₀ Δ₁ Δr : V →ₗ[ℝ] ℝ) {R₀ R₁ Rr s : ℝ}
    (hR₀ : ∀ C, |Δ₀ (e C)| ≤ R₀) (hs₀ : ∀ C, |Δ₀ ((1 / 2 : ℝ) • (e C + e (h₁ C)))| ≤ R₀ - s)
    (hR₁ : ∀ C, |Δ₁ (e C)| ≤ R₁) (hs₁ : ∀ C, |Δ₁ ((1 / 2 : ℝ) • (e C + e (h₃ C)))| ≤ R₁ - s)
    (hRr : ∀ C, |Δr (e C)| ≤ Rr) :
    |(Δ₀ + Δ₁ + Δr) (∑ C, c C • e C)| ≤
      couplingMass c * (R₀ + R₁ + Rr) - (orbitMass h₁ c + orbitMass h₃ c) * s := by
  have h0 := orbit_coupon hh₁ c e Δ₀ hR₀ hs₀
  have h1 := orbit_coupon hh₃ c e Δ₁ hR₁ hs₁
  have h2 := abs_le_couplingMass c e Δr hRr
  rw [LinearMap.add_apply, LinearMap.add_apply]
  calc _ ≤ |Δ₀ (∑ C, c C • e C)| + |Δ₁ (∑ C, c C • e C)| + |Δr (∑ C, c C • e C)| :=
        (abs_add_le _ _).trans (add_le_add_left (abs_add_le _ _) _)
    _ ≤ (couplingMass c * R₀ - orbitMass h₁ c * s) + (couplingMass c * R₁ - orbitMass h₃ c * s)
        + couplingMass c * Rr := add_le_add (add_le_add h0 h1) h2
    _ = _ := by ring

/-- **`lem:orbit-coupon`(iv), the gate.** If `0 ≤ M_h ≤ M`, `0 ≤ e^{tU_inv} ≤ e^{U_0}`,
`0 ≤ tδ_s ≤ d` and `R_err ≥ 2 e^{U_0} d`, the coupon is at most `M R_err / 2`; in particular the
coefficient `M R_err - M_h e^{tU_inv} tδ_s` is nonnegative. -/
theorem orbit_coupon_gate {M Mh X eU td d Rerr : ℝ} (hMh0 : 0 ≤ Mh) (hMh : Mh ≤ M)
    (hX0 : 0 ≤ X) (hX : X ≤ eU) (htd0 : 0 ≤ td) (htd : td ≤ d) (hR : 2 * eU * d ≤ Rerr) :
    Mh * X * td ≤ M * Rerr / 2 ∧ 0 ≤ M * Rerr - Mh * X * td := by
  have hM0 : 0 ≤ M := hMh0.trans hMh
  have hd0 : 0 ≤ d := htd0.trans htd
  have hXtd : X * td ≤ eU * d := mul_le_mul hX htd htd0 (hX0.trans hX)
  have h1 : Mh * X * td ≤ M * (eU * d) := by
    rw [mul_assoc]
    exact mul_le_mul hMh hXtd (mul_nonneg hX0 htd0) hM0
  have h2 : M * (eU * d) ≤ M * Rerr / 2 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
    nlinarith [mul_le_mul_of_nonneg_left hR hM0]
  refine ⟨h1.trans h2, ?_⟩
  have : 0 ≤ M * Rerr := by
    have := mul_nonneg hM0 (mul_nonneg (hX0.trans hX) hd0)
    nlinarith [mul_le_mul_of_nonneg_left hR hM0]
  linarith

/-- **`lem:orbit-coupon`(iv), the gate of (ii).** With `M_{h₁} + M_{h₃} ≤ 2M` the doubled coupon
is at most `M R_err`. -/
theorem orbit_coupon_gate_two {M M₁ M₃ X eU td d Rerr : ℝ} (hM₁ : 0 ≤ M₁) (hM₃ : 0 ≤ M₃)
    (hM₁M : M₁ ≤ M) (hM₃M : M₃ ≤ M) (hX0 : 0 ≤ X) (hX : X ≤ eU) (htd0 : 0 ≤ td)
    (htd : td ≤ d) (hR : 2 * eU * d ≤ Rerr) :
    (M₁ + M₃) * X * td ≤ M * Rerr := by
  have a := (orbit_coupon_gate hM₁ hM₁M hX0 hX htd0 htd hR).1
  have b := (orbit_coupon_gate hM₃ hM₃M hX0 hX htd0 htd hR).1
  nlinarith

/-! ### A toy instance -/

/-- Toy check of the definitions: two couplings exchanged by the reflection, with coefficients
`1` and `2`, have `M = 3` and `M_h = 2` (each orbit member contributes `min(1, 2)`). -/
example :
    couplingMass ![(1 : ℝ), 2] = 3 ∧ orbitMass (Equiv.swap (0 : Fin 2) 1) ![(1 : ℝ), 2] = 2 := by
  constructor
  · simp [couplingMass, Fin.sum_univ_two]; norm_num
  · simp [orbitMass, Fin.sum_univ_two, Equiv.swap_apply_left, Equiv.swap_apply_right]
    norm_num

end Sarkozy.Envelopes
