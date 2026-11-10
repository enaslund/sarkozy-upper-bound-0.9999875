module

public import Sarkozy.PositiveRoots.Moments

@[expose] public section

/-!
# Square of a score on the rectangle (`lem:root-square`)

`paper/sections/20b_positive_roots.tex`, `lem:root-square` and its proof.

* **The diagonal split of the pair rows** (`cor:raw-pair-maps`(b) as used in the proof): in
  `L²(𝔽²)` with the uniform law, `Ψ_y(z, z') = ψ_y(z)ψ_y(z') = r(1 − 2q)d + ρ_y` with the unit
  vector `d = √n 𝟙_{z = z'}`; concretely `ρ_y(z, z') = ψ_y(z)ψ_y(z') − (1 − 2q)𝟙_{z = z'}`
  (`rhoP`), and `ρ_y ⊥ d` for a distinct pair (`rhoP_perp`: `∑_z ρ_y(z, z) = 0`).
* **The square of a score** (`pairScore_sq_split`): for distinct pairs `y, y'`,
  `H(y, y')² = (1 − 2q)² + q^{-1}⟨ρ_y, ρ_{y'}⟩`, i.e.
  `H² = (1 − 2q)² + n^{-1} ∑_{z,z'} ρ_y(z,z')ρ_{y'}(z,z')` (the cross terms vanish since
  `ρ ⊥ d`). This is the identity `H₀² = (1 − 2q)² + q^{-1}⟨ρ_a, ρ_{c'}⟩` of the proof.
* **The second bound from the first** (`root_square_second`): if `‖K_soft‖ ≤ 𝔯₂²` and
  `‖K_soft∘H_j² − (1 − 2q)²K_soft‖ ≤ c`, then `‖K_soft∘H_j² − K_soft‖ ≤ 4q𝔯₂² + c`, as
  `0 ≤ 1 − (1 − 2q)² ≤ 4q` (`one_sub_sq_le`).
* `rect_norm_sq_le`: the norm step `‖𝖱‖ ≤ max(‖𝔯‖₂, ‖𝖱_c‖) ≤ 𝔯₂` in its scalar form: if
  `𝖱f = (Ef)𝔯 + 𝖱_c P₀f` with `𝖱_cP₀f ⊥ 𝔯`, `‖𝔯‖ ≤ 𝔯₂`, `‖𝖱_c‖ ≤ c ≤ 𝔯₂`, then
  `‖𝖱f‖² ≤ 𝔯₂²‖f‖²`. With `‖K_soft‖ = ‖𝖱‖²` (`lem:swapped-rectangle`(a)) and
  `c = k₄r + N_A < 1 ≤ 𝔯₂`
  this is the input `‖K_soft‖ ≤ 𝔯₂²`.

The first bound `‖K_soft∘H_j² − (1 − 2q)²K_soft‖ ≤ 256c₀𝔯₊q` is `SquareSchur.root_square_first`
(the factorization of `lem:swapped-rectangle`(d) and the positive Schur order of
`lem:swapped-rectangle`(b), with the residual pair-map Gram bound of `cor:raw-pair-maps`(b) as a
hypothesis); it is the hypothesis `h1` of `root_square_second`.
-/

namespace Sarkozy.PositiveRoots

open Finset Sarkozy.L20Cap Sarkozy.Cuts

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The residual of a pair row**: `ρ_y(z, z') = ψ_y(z)ψ_y(z') − (1 − 2q)𝟙_{z = z'}`,
`q = 1/n`; it is `Ψ_y − r(1 − 2q)d` with `d = √n 𝟙_{z=z'}`. -/
noncomputable def rhoP (y : F × F) (z z' : F) : ℝ :=
  psiP y z * psiP y z' - (1 - 2 / (Fintype.card F : ℝ)) * (if z = z' then 1 else 0)

/-- `∑_z ψ_y(z)² = n − 2` for a distinct pair. -/
theorem sum_psiP_sq_z {y : F × F} (hy : y.1 ≠ y.2) :
    ∑ z, psiP y z ^ 2 = (Fintype.card F : ℝ) - 2 := by
  unfold psiP
  have e : ∀ z, (chi (z - y.1) * chi (z - y.2)) ^ 2 =
      1 - (if z = y.1 then 1 else 0) - (if z = y.2 then 1 else 0) := by
    intro z
    rw [mul_pow, chi_sub_sq, chi_sub_sq]
    by_cases h1 : y.1 = z
    · subst h1
      simp [hy]
    · by_cases h2 : y.2 = z
      · subst h2
        simp [h1, Ne.symm h1]
      · simp [h1, h2, Ne.symm h1, Ne.symm h2]
  rw [sum_congr rfl fun z _ => e z, sum_sub_distrib, sum_sub_distrib,
    sum_ite_eq' univ y.1 (fun _ => (1 : ℝ)), sum_ite_eq' univ y.2 (fun _ => (1 : ℝ))]
  simp only [mem_univ, ↓reduceIte, sum_const, card_univ, nsmul_eq_mul, mul_one]
  ring

/-- **`ρ_y ⊥ d`** for a distinct pair: `∑_z ρ_y(z, z) = 0`, i.e. `⟨Ψ_y, d⟩ = r(1 − 2q)`. -/
theorem rhoP_perp {y : F × F} (hy : y.1 ≠ y.2) : ∑ z, rhoP y z z = 0 := by
  have hn : (2 : ℝ) ≤ Fintype.card F := by
    have := Fintype.one_lt_card (α := F)
    exact_mod_cast this
  unfold rhoP
  simp only [↓reduceIte, mul_one, sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul]
  have e : ∑ z, psiP y z * psiP y z = (Fintype.card F : ℝ) - 2 := by
    rw [← sum_psiP_sq_z hy]
    simp only [sq]
  rw [e]
  field_simp
  ring

/-- **The square of a score** (`lem:root-square`, proof): for distinct pairs `y, y'`,
`H(y, y')² = (1 − 2q)² + q^{-1}⟨ρ_y, ρ_{y'}⟩ = (1 − 2q)² + n^{-1}∑_{z,z'} ρ_y ρ_{y'}`. -/
theorem pairScore_sq_split {y y' : F × F} (hy : y.1 ≠ y.2) (hy' : y'.1 ≠ y'.2) :
    pairScore y y' ^ 2 = (1 - 2 / (Fintype.card F : ℝ)) ^ 2 +
      (1 / (Fintype.card F : ℝ)) * ∑ z, ∑ z', rhoP y z z' * rhoP y' z z' := by
  set n : ℝ := (Fintype.card F : ℝ) with hn_def
  have hn : (2 : ℝ) ≤ n := by
    have := Fintype.one_lt_card (α := F)
    rw [hn_def]; exact_mod_cast this
  have hn0 : n ≠ 0 := by linarith
  -- expand the double sum of the residuals
  have hexp : ∑ z, ∑ z', rhoP y z z' * rhoP y' z z' =
      (∑ z, psiP y z * psiP y' z) ^ 2 - n * (1 - 2 / n) ^ 2 := by
    have e1 : ∀ z z', rhoP y z z' * rhoP y' z z' =
        psiP y z * psiP y' z * (psiP y z' * psiP y' z') -
          (1 - 2 / n) * ((if z = z' then 1 else 0) * (psiP y z * psiP y z')) -
          (1 - 2 / n) * ((if z = z' then 1 else 0) * (psiP y' z * psiP y' z')) +
          (1 - 2 / n) ^ 2 * (if z = z' then 1 else 0) := by
      intro z z'
      unfold rhoP
      rw [← hn_def]
      split_ifs <;> ring
    have t1 : ∑ z : F, ∑ z' : F, psiP y z * psiP y' z * (psiP y z' * psiP y' z') =
        (∑ z, psiP y z * psiP y' z) ^ 2 := by
      rw [sq, Finset.sum_mul_sum]
    simp only [e1, sum_add_distrib, sum_sub_distrib]
    rw [t1]
    simp only [← Finset.mul_sum]
    have d1 : ∀ (g : F → F → ℝ), ∑ z : F, ∑ z' : F, (if z = z' then (1 : ℝ) else 0) * g z z' =
        ∑ z : F, g z z := by
      intro g
      refine sum_congr rfl fun z _ => ?_
      rw [Finset.sum_eq_single z]
      · simp
      · intro b _ hb; simp [Ne.symm hb]
      · simp
    rw [d1 (fun z z' => psiP y z * psiP y z'), d1 (fun z z' => psiP y' z * psiP y' z')]
    have d2 : ∑ z : F, ∑ z' : F, (if z = z' then (1 : ℝ) else 0) = n := by
      have := d1 (fun _ _ => (1 : ℝ))
      simp only [mul_one] at this
      rw [this]
      simp [hn_def]
    rw [d2]
    have s1 : ∑ z, psiP y z * psiP y z = n - 2 := by
      rw [← sum_psiP_sq_z hy]; simp only [sq]
    have s2 : ∑ z, psiP y' z * psiP y' z = n - 2 := by
      rw [← sum_psiP_sq_z hy']; simp only [sq]
    rw [s1, s2]
    field_simp
    ring
  unfold pairScore
  rw [hexp, div_pow, Real.sq_sqrt (by linarith), ← hn_def]
  field_simp
  ring

/-! ## The second bound -/

theorem one_sub_sq_le {q : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    0 ≤ 1 - (1 - 2 * q) ^ 2 ∧ 1 - (1 - 2 * q) ^ 2 ≤ 4 * q := by
  constructor <;> nlinarith

section Second

variable {X : Type*} [Fintype X]

/-- **`lem:root-square`, the second bound from the first**: if `‖K‖ ≤ 𝔯₂²` and
`‖K∘H² − (1 − 2q)²K‖ ≤ c` (forms on `ν ⊗ ν`), then `‖K∘H² − K‖ ≤ 4q𝔯₂² + c`. -/
theorem root_square_second (ν : Sarkozy.FiniteLaw X) (K H : X → X → ℝ) {q c r2 : ℝ} (hq : 0 ≤ q)
    (hq1 : q ≤ 1)
    (hK : ∀ f g, |kernelForm ν ν K f g| ≤ r2 ^ 2 * Recentering.nrm ν f * Recentering.nrm ν g)
    (h1 : ∀ f g, |kernelForm ν ν (fun x y => K x y * H x y ^ 2 - (1 - 2 * q) ^ 2 * K x y) f g| ≤
      c * Recentering.nrm ν f * Recentering.nrm ν g)
    (f g : X → ℝ) :
    |kernelForm ν ν (fun x y => K x y * H x y ^ 2 - K x y) f g| ≤
      (4 * q * r2 ^ 2 + c) * Recentering.nrm ν f * Recentering.nrm ν g := by
  have e : kernelForm ν ν (fun x y => K x y * H x y ^ 2 - K x y) f g =
      kernelForm ν ν (fun x y => K x y * H x y ^ 2 - (1 - 2 * q) ^ 2 * K x y) f g -
        (1 - (1 - 2 * q) ^ 2) * kernelForm ν ν K f g := by
    simp only [kernelForm, LinearMap.mk₂_apply, Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact sum_congr rfl fun x _ => sum_congr rfl fun y _ => by ring
  rw [e]
  obtain ⟨h0, h4⟩ := one_sub_sq_le hq hq1
  have hn : 0 ≤ Recentering.nrm ν f * Recentering.nrm ν g :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have a1 := h1 f g
  have a2 := hK f g
  have a3 : |(1 - (1 - 2 * q) ^ 2) * kernelForm ν ν K f g| ≤
      4 * q * (r2 ^ 2 * Recentering.nrm ν f * Recentering.nrm ν g) := by
    rw [abs_mul, abs_of_nonneg h0]
    exact mul_le_mul h4 a2 (abs_nonneg _) (by linarith)
  have t := abs_sub _ _ |>.trans (add_le_add a1 a3)
  calc _ ≤ _ := t
    _ = _ := by ring

end Second

/-- **The norm of the rectangle** (proof of `lem:root-square`, second bound), scalar form: if
`‖𝖱f‖² = (Ef)²‖𝔯‖² + ‖𝖱_cP₀f‖²` (`𝖱1 = 𝔯`, `𝖱` maps `1^⊥` into `𝔯^⊥`), `‖f‖² = (Ef)² + ‖P₀f‖²`,
`‖𝔯‖ ≤ 𝔯₂` and `‖𝖱_cP₀f‖ ≤ c‖P₀f‖` with `0 ≤ c ≤ 𝔯₂`, then `‖𝖱f‖² ≤ 𝔯₂²‖f‖²`. -/
theorem rect_norm_sq_le {a nr g t c r2 Rf nf : ℝ} (hnr : 0 ≤ nr) (hnr2 : nr ≤ r2) (hg : 0 ≤ g)
    (ht : 0 ≤ t) (htc : t ≤ c * g) (hc : 0 ≤ c) (hcr : c ≤ r2)
    (hRf : Rf = a ^ 2 * nr ^ 2 + t ^ 2) (hnf : nf = a ^ 2 + g ^ 2) : Rf ≤ r2 ^ 2 * nf := by
  rw [hRf, hnf]
  have h1 : nr ^ 2 ≤ r2 ^ 2 := pow_le_pow_left₀ hnr hnr2 2
  have h2 : t ^ 2 ≤ (c * g) ^ 2 := pow_le_pow_left₀ ht htc 2
  have h3 : (c * g) ^ 2 ≤ (r2 * g) ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg hc hg) (mul_le_mul_of_nonneg_right hcr hg) 2
  nlinarith [sq_nonneg a]

end Sarkozy.PositiveRoots
