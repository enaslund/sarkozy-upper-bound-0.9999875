module

public import Sarkozy.Envelopes.DirectGram

@[expose] public section

/-!
# The sides of the signed law (`prop:signed-sides`, partly)

`paper/sections/24_matching_mean.tex`, `prop:signed-sides`.

**Proved here.**
* (i), **the prime Gram** (`prime_gram_signed`): with the leading parts forming `G(u_t, v_t)` of
  `lem:record:direct-gram` (frame `Γ_A`) and the remainders `R_o`, `R^new` of norms at most
  `e_o q`, `e_sg q` (`remainder_block_form`), the prime Gram with the shifts `d r` is positive
  semidefinite on the centred functions for every `d ≥ s_t Γ_A + (e_o + e_sg) r = d_t`, `q = r²`;
  on the constants it is `[[1 + dr, 1], [1, 1 + dr]] ⪰ 0` (`constants_block`).
* (ii), **the chosen sides** (`chosen_side_ge`, `side_coefficient`): with
  `up(x) = 10⁻³⁰⌈10³⁰ x⌉` and an upper end `U ≥ H̄_X d_t`, the side
  `d_s = d^aux_s + up([U - d^aux_s]_+)` is at least `max(H̄_X d_t, d^aux_s)`, and
  `k_s = w_D d_s - v_D = k^aux_s + w_D δ⁺_s ≥ k^aux_s`.
* (iii), **the price** (`side_price_le`): `(k_L + k_R) Ī₂ ≤ up((k^aux_L + k^aux_R) Ī₂) +
  up(2 w_D up(½(δ⁺_L + δ⁺_R)) Ī₂)` for each piece; summing over the pieces gives `T'_K`.

**Not formalized:** the operator decomposition `T_old = O₀ + R_o`, `T'_p = O₀ + L^m + R^new` (from
`prop:signed-bounds`, here hypotheses through the forms), the block step through
`lem:record:asymmetric-gram`(b), and the gates of `cert:signed-local` (`c_{≥2}(X) r_X < d_t(X)`,
`n_X e₀(X) < 1`) at the 33 piece starts.
-/

namespace Sarkozy.Envelopes

open Finset

section PrimeGram

variable {H₀ 𝓗 : Type*} [NormedAddCommGroup H₀] [InnerProductSpace ℝ H₀] [CompleteSpace H₀]
  [NormedAddCommGroup 𝓗] [InnerProductSpace ℝ 𝓗] [CompleteSpace 𝓗]

omit [CompleteSpace 𝓗] in
/-- The form of the remainder block `[[R_o, R^new], [R^new*, R_o]]` at `(f, g)` is at least
`-(e_o + e_sg) q (‖f‖² + ‖g‖²)` when `‖R_o‖ ≤ e_o q` and `‖R^new‖ ≤ e_sg q`. -/
theorem remainder_block_form (Ro Rn : 𝓗 →L[ℝ] 𝓗) {eo esg q : ℝ} (hes : 0 ≤ esg)
    (hq : 0 ≤ q) (hRo : ∀ x, ‖Ro x‖ ≤ eo * q * ‖x‖) (hRn : ∀ x, ‖Rn x‖ ≤ esg * q * ‖x‖)
    (f g : 𝓗) :
    -((eo + esg) * q * (‖f‖ ^ 2 + ‖g‖ ^ 2)) ≤
      inner ℝ f (Ro f) + 2 * inner ℝ f (Rn g) + inner ℝ g (Ro g) := by
  have h1 : |inner ℝ f (Ro f)| ≤ eo * q * ‖f‖ ^ 2 := by
    calc |inner ℝ f (Ro f)| ≤ ‖f‖ * ‖Ro f‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖f‖ * (eo * q * ‖f‖) := mul_le_mul_of_nonneg_left (hRo f) (norm_nonneg _)
      _ = eo * q * ‖f‖ ^ 2 := by ring
  have h2 : |inner ℝ g (Ro g)| ≤ eo * q * ‖g‖ ^ 2 := by
    calc |inner ℝ g (Ro g)| ≤ ‖g‖ * ‖Ro g‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖g‖ * (eo * q * ‖g‖) := mul_le_mul_of_nonneg_left (hRo g) (norm_nonneg _)
      _ = eo * q * ‖g‖ ^ 2 := by ring
  have h3 : |inner ℝ f (Rn g)| ≤ esg * q * (‖f‖ * ‖g‖) := by
    calc |inner ℝ f (Rn g)| ≤ ‖f‖ * ‖Rn g‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖f‖ * (esg * q * ‖g‖) := mul_le_mul_of_nonneg_left (hRn g) (norm_nonneg _)
      _ = esg * q * (‖f‖ * ‖g‖) := by ring
  have h4 : 2 * (‖f‖ * ‖g‖) ≤ ‖f‖ ^ 2 + ‖g‖ ^ 2 := by
    nlinarith [sq_nonneg (‖f‖ - ‖g‖)]
  have hesq : 0 ≤ esg * q := mul_nonneg hes hq
  have h5 : 2 * (esg * q * (‖f‖ * ‖g‖)) ≤ esg * q * (‖f‖ ^ 2 + ‖g‖ ^ 2) := by
    nlinarith [mul_le_mul_of_nonneg_left h4 hesq]
  have a1 := neg_abs_le (inner ℝ f (Ro f))
  have a2 := neg_abs_le (inner ℝ g (Ro g))
  have a3 := neg_abs_le (inner ℝ f (Rn g))
  nlinarith

/-- **`prop:signed-sides`(i), the prime Gram on the centred functions.** Under the frame bound of
`lem:record:direct-gram` (`Γ ≥ 0`, `r > 0`), if the remainder form `Rem` satisfies
`Rem(f, g) ≥ -e r² (‖f‖² + ‖g‖²)` (`e = e_o + e_sg`, `q = r²`, `remainder_block_form`) and
`d ≥ s_t Γ + e r` (the coefficient `d_t` of `eq:signed-constants`), then the prime Gram form
`G(u_t, v_t)(f, g) + Rem(f, g) + d r (‖f‖² + ‖g‖²)` is nonnegative. -/
theorem prime_gram_signed (V : H₀ →L[ℝ] 𝓗) (A : Fin 3 → H₀ →L[ℝ] 𝓗) {r Γ e d : ℝ}
    (hr : 0 < r) (hΓ : 0 ≤ Γ)
    (hframe : ∀ (h₀ : H₀) (h : Fin 3 → H₀),
      ‖V h₀ + ∑ i, r⁻¹ • A i (h i)‖ ^ 2 ≤ Γ * (‖h₀‖ ^ 2 + ∑ i, ‖h i‖ ^ 2))
    (t : ℝ) (Rem : 𝓗 → 𝓗 → ℝ) (hRem : ∀ f g, -(e * r ^ 2 * (‖f‖ ^ 2 + ‖g‖ ^ 2)) ≤ Rem f g)
    (hd : sT t * Γ + e * r ≤ d) (f g : 𝓗) :
    0 ≤ gBlockForm V A (uT t) (vT t) f g + Rem f g + d * r * (‖f‖ ^ 2 + ‖g‖ ^ 2) := by
  have h1 := directGram_signed V A hr hΓ hframe t f g
  have h2 := hRem f g
  have hN : 0 ≤ ‖f‖ ^ 2 + ‖g‖ ^ 2 := by positivity
  have h3 : (sT t * Γ + e * r) * r * (‖f‖ ^ 2 + ‖g‖ ^ 2) ≤ d * r * (‖f‖ ^ 2 + ‖g‖ ^ 2) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hd hr.le) hN
  nlinarith

end PrimeGram

/-- **`prop:signed-sides`(i), the constants.** On the constants the prime Gram is
`[[1 + dr, 1], [1, 1 + dr]] ⪰ 0` for `d, r ≥ 0`. -/
theorem constants_block {d r : ℝ} (hd : 0 ≤ d) (hr : 0 ≤ r) (a b : ℝ) :
    0 ≤ (1 + d * r) * a ^ 2 + 2 * a * b + (1 + d * r) * b ^ 2 := by
  nlinarith [sq_nonneg (a + b), mul_nonneg hd hr, sq_nonneg a, sq_nonneg b]

/-! ### (ii), (iii): the chosen sides and their price -/

/-- The outward rounding `up(x) = 10⁻³⁰ ⌈10³⁰ x⌉` of `prop:signed-sides`. -/
noncomputable def up30 (x : ℝ) : ℝ := (⌈(10 : ℝ) ^ 30 * x⌉ : ℝ) / 10 ^ 30

theorem le_up30 (x : ℝ) : x ≤ up30 x := by
  unfold up30
  rw [le_div_iff₀ (by positivity), mul_comm]
  exact Int.le_ceil _

/-- **`prop:signed-sides`(ii), the chosen sides.** If `U ≥ H̄_X d_t` (the certified upper end),
the increment `δ⁺ = up([U - d^aux]_+)` is nonnegative and the chosen side
`d_s = d^aux + δ⁺` is at least `max(H̄_X d_t, d^aux)`. -/
theorem chosen_side_ge {Hd U daux : ℝ} (hU : Hd ≤ U) :
    0 ≤ up30 (max (U - daux) 0) ∧ max Hd daux ≤ daux + up30 (max (U - daux) 0) := by
  have h1 := le_up30 (max (U - daux) 0)
  have h2 : 0 ≤ max (U - daux) 0 := le_max_right _ _
  have h3 : U - daux ≤ max (U - daux) 0 := le_max_left _ _
  refine ⟨h2.trans h1, max_le ?_ ?_⟩ <;> linarith

/-- **`prop:signed-sides`(ii), the side coefficients.** `k_s = w_D d_s - v_D` equals
`k^aux_s + w_D δ⁺_s` with `k^aux_s = w_D d^aux_s - v_D`, and `k_s ≥ k^aux_s` for `w_D, δ⁺ ≥ 0`;
so the side gate `k^aux_s ≥ 0` gives `k_s ≥ 0`. -/
theorem side_coefficient {w v daux δ : ℝ} (hw : 0 ≤ w) (hδ : 0 ≤ δ) :
    w * (daux + δ) - v = (w * daux - v) + w * δ ∧ w * daux - v ≤ w * (daux + δ) - v := by
  refine ⟨by ring, ?_⟩
  nlinarith [mul_nonneg hw hδ]

/-- **`prop:signed-sides`(iii), the price of one piece.** With `w_D, Ī₂ ≥ 0` and the increments
`δ⁺_L, δ⁺_R`,
`(k_L + k_R) Ī₂ ≤ up((k^aux_L + k^aux_R) Ī₂) + up(2 w_D up(½(δ⁺_L + δ⁺_R)) Ī₂)`, where
`k_s = k^aux_s + w_D δ⁺_s`. Summed over the pieces this is `∑ (k_L + k_R) Ī₂ ≤ T'_K`. -/
theorem side_price_le {w I kauxL kauxR δL δR : ℝ} (hw : 0 ≤ w) (hI : 0 ≤ I) :
    ((kauxL + w * δL) + (kauxR + w * δR)) * I ≤
      up30 ((kauxL + kauxR) * I) + up30 (2 * w * up30 ((δL + δR) / 2) * I) := by
  have e : ((kauxL + w * δL) + (kauxR + w * δR)) * I =
      (kauxL + kauxR) * I + 2 * w * ((δL + δR) / 2) * I := by ring
  rw [e]
  have h1 := le_up30 ((kauxL + kauxR) * I)
  have h2 : 2 * w * ((δL + δR) / 2) * I ≤ 2 * w * up30 ((δL + δR) / 2) * I := by
    have := le_up30 ((δL + δR) / 2)
    have hw2 : 0 ≤ 2 * w := by linarith
    have := mul_le_mul_of_nonneg_left this hw2
    exact mul_le_mul_of_nonneg_right this hI
  have h3 := le_up30 (2 * w * up30 ((δL + δR) / 2) * I)
  linarith

/-- **`prop:signed-sides`(iii), the sum over the pieces.** -/
theorem side_price_sum {ι : Type*} (s : Finset ι) (w I kauxL kauxR δL δR : ι → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i) (hI : ∀ i ∈ s, 0 ≤ I i) :
    ∑ i ∈ s, ((kauxL i + w i * δL i) + (kauxR i + w i * δR i)) * I i ≤
      ∑ i ∈ s, up30 ((kauxL i + kauxR i) * I i) +
        ∑ i ∈ s, up30 (2 * w i * up30 ((δL i + δR i) / 2) * I i) := by
  rw [← sum_add_distrib]
  exact sum_le_sum fun i hi => side_price_le (hw i hi) (hI i hi)

end Sarkozy.Envelopes
