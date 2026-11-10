module

public import Sarkozy.SpectralC.DegreeOne

@[expose] public section

/-!
# Small pair constants (`lem:spec:small`)

`paper/sections/14_spectral.tex`, `lem:spec:small`. The proof conditions on all labels but one
(`x'_l`), under which `x'_l` is uniform on its admissible set `𝒜` (`lem:graphs:vertex`(dens)), and
counts `𝒜` and `𝒜⁺ = {a ∈ 𝒜 : a − x_k ∈ Q_p}` by `lem:extension`(coarse):
`|𝒜| ∈ c[1 − e, 1 + e]`, `2|𝒜⁺| ∈ c[1 − e', 1 + e']`, `c = p 2^{-d_l}`. Since `x_k ∉ 𝒜`, the
conditional mean of `χ(x'_l − x_k)` is `(2|𝒜⁺| − |𝒜|)/|𝒜|`, of modulus at most
`(e + e')/(1 − e)` (`cond_chi_mean`, `abs_cond_chi_mean_le`); averaging over the conditioning gives
`|E_λ χ(x'_l − x_k)| ≤ δ^×_l` (`small_pair_bound`, and `small_pair_deltaX` for `δ^×_kl` itself).
The conditional law and the two counts are the explicit hypotheses (they are
`lem:graphs:vertex`(dens) and `lem:extension`(coarse), outside this brief). The bound by
`min(δ^×_k, δ^×_l)` follows from the swap identity (`small_pair_min`). The same statement with
`μ`, `d^0_l` and `e(p, n)` is part (b).

The other claims of (a): on a cross pair `χ(x'_l − x_k) = χ(ς_kl)` almost surely (the cross
constraint), and `E_λ χ(x'_k − x_l) = χ(−1) E_λ χ(x'_l − x_k)` (`deltaX_swap`,
`Sarkozy.SpectralC.DegreeOne`).

New material for this paper.
-/

namespace Sarkozy.SpectralC

open Finset Complex Sarkozy.Characters
open scoped BigOperators ComplexConjugate

variable {p : ℕ} [Fact p.Prime]

/-- The mean of `χ(a − x)` over a set `𝒜 ∌ x`: `(2|𝒜⁺| − |𝒜|)/|𝒜|`, `𝒜⁺ = {a ∈ 𝒜 : a − x ∈ Q_p}`. -/
lemma cond_chi_mean (𝒜 : Finset (ZMod p)) (x : ZMod p) (hx : x ∉ 𝒜) :
    ∑ a ∈ 𝒜, chiC p (a - x) =
      2 * ((𝒜.filter (fun a => IsSquare (a - x))).card : ℂ) - 𝒜.card := by
  have h : ∀ a ∈ 𝒜, chiC p (a - x) = 2 * (if IsSquare (a - x) then 1 else 0) - 1 := by
    intro a ha
    have hne : a - x ≠ 0 := by
      intro h0; rw [sub_eq_zero] at h0; exact hx (h0 ▸ ha)
    split_ifs with hs
    · rw [chiC_of_isSquare hne hs]; ring
    · rw [chiC_of_not_isSquare hs]; ring
  rw [sum_congr rfl h, sum_sub_distrib, ← mul_sum, sum_const, nsmul_eq_mul, mul_one]
  rw [← sum_filter, sum_const, nsmul_eq_mul, mul_one]

/-- `|(2A⁺ − A)/A| ≤ (e + e')/(1 − e)` when `A ∈ c[1 − e, 1 + e]`, `2A⁺ ∈ c[1 − e', 1 + e']`. -/
lemma abs_cond_chi_mean_le {A Ap c e e' : ℝ} (hc : 0 < c) (he1 : e < 1)
    (hA1 : c * (1 - e) ≤ A) (hA2 : A ≤ c * (1 + e))
    (hAp1 : c * (1 - e') ≤ 2 * Ap) (hAp2 : 2 * Ap ≤ c * (1 + e')) :
    |(2 * Ap - A) / A| ≤ (e + e') / (1 - e) := by
  have hA : 0 < A := lt_of_lt_of_le (mul_pos hc (by linarith)) hA1
  rw [abs_div, abs_of_pos hA, div_le_div_iff₀ hA (by linarith)]
  have h1 : |2 * Ap - A| ≤ c * (e + e') := by
    rw [abs_le]; constructor <;> nlinarith
  calc |2 * Ap - A| * (1 - e) ≤ c * (e + e') * (1 - e) :=
        mul_le_mul_of_nonneg_right h1 (by linarith)
    _ = (e + e') * (c * (1 - e)) := by ring
    _ ≤ (e + e') * A := by
        apply mul_le_mul_of_nonneg_left hA1
        have : 0 ≤ c * (e + e') := (abs_nonneg _).trans h1
        exact (mul_nonneg_iff_of_pos_left hc).mp this

/-- **`lem:spec:small`(a), the bound for `ς_kl = 0`** (and (b), with `μ`): if, given the other
labels `z` (law `Λ'`), `x'_l` is uniform on `𝒜(z)` with `x_k(z) ∉ 𝒜(z)`,
`|𝒜(z)| ∈ c[1 − e, 1 + e]` and `2|𝒜⁺(z)| ∈ c[1 − e', 1 + e']`, then
`|E_λ χ(x'_l − x_k)| ≤ (e + e')/(1 − e)` (`= δ^×_l` with `c = p2^{-d_l}`, `e = e_{d_l}(p, 2n)`,
`e' = e_{d_l+1}(p, 2n)`). -/
theorem small_pair_bound {Z : Type*} [Fintype Z] (Λ' : Z → ℝ) (hΛ' : ∀ z, 0 ≤ Λ' z)
    (hΛ'1 : ∑ z, Λ' z = 1) (𝒜 : Z → Finset (ZMod p)) (xk : Z → ZMod p)
    (hx : ∀ z, xk z ∉ 𝒜 z) {c e e' : ℝ} (hc : 0 < c) (he1 : e < 1)
    (hA : ∀ z, c * (1 - e) ≤ (𝒜 z).card ∧ ((𝒜 z).card : ℝ) ≤ c * (1 + e))
    (hAp : ∀ z, c * (1 - e') ≤ 2 * ((𝒜 z).filter (fun a => IsSquare (a - xk z))).card ∧
      2 * (((𝒜 z).filter (fun a => IsSquare (a - xk z))).card : ℝ) ≤ c * (1 + e')) :
    ‖∑ z, (Λ' z : ℂ) * (((𝒜 z).card : ℂ)⁻¹ * ∑ a ∈ 𝒜 z, chiC p (a - xk z))‖ ≤
      (e + e') / (1 - e) := by
  have hz : ∀ z, ‖((𝒜 z).card : ℂ)⁻¹ * ∑ a ∈ 𝒜 z, chiC p (a - xk z)‖ ≤ (e + e') / (1 - e) := by
    intro z
    rw [cond_chi_mean (𝒜 z) (xk z) (hx z)]
    have hreal : ((𝒜 z).card : ℂ)⁻¹ *
        (2 * (((𝒜 z).filter (fun a => IsSquare (a - xk z))).card : ℂ) - (𝒜 z).card) =
        (((2 * ((((𝒜 z).filter (fun a => IsSquare (a - xk z))).card : ℝ)) -
          ((𝒜 z).card : ℝ)) / ((𝒜 z).card : ℝ) : ℝ) : ℂ) := by
      push_cast
      ring
    rw [hreal, Complex.norm_real, Real.norm_eq_abs]
    exact abs_cond_chi_mean_le hc he1 (hA z).1 (hA z).2 (hAp z).1 (hAp z).2
  calc ‖∑ z, (Λ' z : ℂ) * (((𝒜 z).card : ℂ)⁻¹ * ∑ a ∈ 𝒜 z, chiC p (a - xk z))‖
      ≤ ∑ z, Λ' z * ((e + e') / (1 - e)) := by
        refine (norm_sum_le _ _).trans (sum_le_sum fun z _ => ?_)
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hΛ' z)]
        exact mul_le_mul_of_nonneg_left (hz z) (hΛ' z)
    _ = (e + e') / (1 - e) := by rw [← sum_mul, hΛ'1, one_mul]

/-- **`lem:spec:small`(a), cross pairs** (and the edge cases of (b)): if
`σ(x'_l − x_k) ∈ Q_p` almost surely for a sign `σ = ±1` (the cross constraint, `σ = ς_kl`), then
`E χ(x'_l − x_k) = χ(σ)`. -/
theorem chi_mean_of_square {Ω : Type*} [Fintype Ω] (Λ : Ω → ℝ) (hΛ1 : ∑ ω, Λ ω = 1)
    (d : Ω → ZMod p) {σ : ZMod p} (hσ : σ = 1 ∨ σ = -1)
    (hsq : ∀ ω, Λ ω ≠ 0 → σ * d ω ≠ 0 ∧ IsSquare (σ * d ω)) :
    ∑ ω, (Λ ω : ℂ) * chiC p (d ω) = chiC p σ := by
  have hσσ : σ * σ = 1 := by rcases hσ with h | h <;> rw [h] <;> ring
  have hpt : ∀ ω, (Λ ω : ℂ) * chiC p (d ω) = (Λ ω : ℂ) * chiC p σ := by
    intro ω
    by_cases hω : Λ ω = 0
    · rw [hω]; simp
    · obtain ⟨hne, hs⟩ := hsq ω hω
      have h1 : chiC p (σ * d ω) = 1 := chiC_of_isSquare hne hs
      have h2 : d ω = σ * (σ * d ω) := by rw [← mul_assoc, hσσ, one_mul]
      rw [h2, map_mul, h1, mul_one]
  rw [sum_congr rfl fun ω _ => hpt ω, ← sum_mul]
  have : ∑ ω, (Λ ω : ℂ) = 1 := by exact_mod_cast hΛ1
  rw [this, one_mul]

variable {U : Type*} [Fintype U] [DecidableEq U]

/-- **`lem:spec:small`(a), the bound `δ^×_l` for `δ^×_kl = E_λ χ(x'_l − x_k)`**: the hypothesis
`hdis` is `lem:graphs:vertex`(dens) (given the labels `z` other than `x'_l`, of law `Λ'`, the
label `x'_l` is uniform on `𝒜(z)`); `hA`, `hAp` are `lem:extension`(coarse). -/
theorem small_pair_deltaX {Z : Type*} [Fintype Z] (Λ : (U → ZMod p) × (U → ZMod p) → ℝ)
    (k l : U) (Λ' : Z → ℝ) (hΛ' : ∀ z, 0 ≤ Λ' z) (hΛ'1 : ∑ z, Λ' z = 1)
    (𝒜 : Z → Finset (ZMod p)) (xk : Z → ZMod p)
    (hdis : deltaX Λ k l =
      ∑ z, (Λ' z : ℂ) * (((𝒜 z).card : ℂ)⁻¹ * ∑ a ∈ 𝒜 z, chiC p (a - xk z)))
    (hx : ∀ z, xk z ∉ 𝒜 z) {c e e' : ℝ} (hc : 0 < c) (he1 : e < 1)
    (hA : ∀ z, c * (1 - e) ≤ (𝒜 z).card ∧ ((𝒜 z).card : ℝ) ≤ c * (1 + e))
    (hAp : ∀ z, c * (1 - e') ≤ 2 * ((𝒜 z).filter (fun a => IsSquare (a - xk z))).card ∧
      2 * (((𝒜 z).filter (fun a => IsSquare (a - xk z))).card : ℝ) ≤ c * (1 + e')) :
    ‖deltaX Λ k l‖ ≤ (e + e') / (1 - e) := by
  rw [hdis]
  exact small_pair_bound Λ' hΛ' hΛ'1 𝒜 xk hx hc he1 hA hAp

/-- **`lem:spec:small`(a), the `min`**: from the bounds for the pairs `(k, l)` and `(l, k)` and the
swap invariance of `λ`, `|δ^×_kl| ≤ min(δ^×_k, δ^×_l)`. -/
theorem small_pair_min (Λ : (U → ZMod p) × (U → ZMod p) → ℝ)
    (hswap : ∀ z, Λ (z.2, z.1) = Λ z) (k l : U) {δk δl : ℝ}
    (hl : ‖deltaX Λ k l‖ ≤ δl) (hk : ‖deltaX Λ l k‖ ≤ δk) : ‖deltaX Λ k l‖ ≤ min δk δl := by
  have h1 : ‖chiC p (-1)‖ = 1 := norm_chiC (neg_ne_zero.mpr one_ne_zero)
  have h2 : ‖deltaX Λ l k‖ = ‖deltaX Λ k l‖ := by
    rw [deltaX_swap Λ hswap k l, norm_mul, h1, one_mul]
  exact le_min (h2 ▸ hk) hl

end Sarkozy.SpectralC
