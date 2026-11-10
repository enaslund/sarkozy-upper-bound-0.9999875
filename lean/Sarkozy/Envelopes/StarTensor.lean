module

public import Mathlib.Analysis.Normed.Ring.Basic
public import Mathlib.Algebra.BigOperators.Fin

@[expose] public section

/-!
# The star-tensor error (`eq:oct24:star-tensor-error`)

`paper/sections/23_envelopes.tex`, `eq:oct24:star-tensor-error` (used in Step 1 of the proof of
`thm:envelopes`): if `‖L_𝔅‖ ≤ ℓ_𝔅` and `‖Υ_𝔅‖ ≤ ρ_𝔅`, then
`‖⊗_𝔅 (L_𝔅 + Υ_𝔅) - ⊗_𝔅 L_𝔅‖ ≤ ∏_𝔅 (ℓ_𝔅 + ρ_𝔅) - ∏_𝔅 ℓ_𝔅`.

**Form.** The tensor product of operators acting on distinct tensor factors is the ordered product
of the operators `T_𝔅 ⊗ I` in the algebra of operators on the whole tensor product, with
`‖T_𝔅 ⊗ I‖ = ‖T_𝔅‖`. So the statement is proved in any normed ring with `‖1‖ = 1` for ordered
products `∏_{i<n}` (`List.ofFn`), without commutativity: `norm_prod_add_sub_prod_le`. The paper
proves it by expanding the product by the set of remainder factors; the induction here gives the
same bound. `remainder_monomial` is the identity behind "multiplied by the raw-arm coefficients and
by `q_X^{2a}`, the right side becomes `π^tot_ω - π^lead_ω`".
-/

namespace Sarkozy.Envelopes

open Finset

/-- The norm of an ordered product is at most the product of the norm bounds. -/
theorem norm_ofFn_prod_le {A : Type*} [NormedRing A] [NormOneClass A] :
    ∀ (n : ℕ) (L : Fin n → A) (ℓ : Fin n → ℝ), (∀ i, ‖L i‖ ≤ ℓ i) →
      ‖(List.ofFn L).prod‖ ≤ ∏ i, ℓ i
  | 0, _, _, _ => by simp
  | n + 1, L, ℓ, hL => by
    rw [List.ofFn_succ, List.prod_cons, Fin.prod_univ_succ]
    have ih := norm_ofFn_prod_le n (fun i => L i.succ) (fun i => ℓ i.succ) (fun i => hL _)
    have h0 : 0 ≤ ℓ 0 := (norm_nonneg _).trans (hL 0)
    calc ‖L 0 * (List.ofFn fun i => L i.succ).prod‖
        ≤ ‖L 0‖ * ‖(List.ofFn fun i => L i.succ).prod‖ := norm_mul_le _ _
      _ ≤ ℓ 0 * ∏ i : Fin n, ℓ i.succ :=
          mul_le_mul (hL 0) ih (norm_nonneg _) h0

/-- **`eq:oct24:star-tensor-error`.** In a normed ring with `‖1‖ = 1`, if `‖L_i‖ ≤ ℓ_i` and
`‖Υ_i‖ ≤ ρ_i`, then `‖∏_i (L_i + Υ_i) - ∏_i L_i‖ ≤ ∏_i (ℓ_i + ρ_i) - ∏_i ℓ_i` for ordered
products. -/
theorem norm_prod_add_sub_prod_le {A : Type*} [NormedRing A] [NormOneClass A] :
    ∀ (n : ℕ) (L Υ : Fin n → A) (ℓ ρ : Fin n → ℝ), (∀ i, ‖L i‖ ≤ ℓ i) → (∀ i, ‖Υ i‖ ≤ ρ i) →
      ‖(List.ofFn fun i => L i + Υ i).prod - (List.ofFn L).prod‖ ≤
        ∏ i, (ℓ i + ρ i) - ∏ i, ℓ i
  | 0, _, _, _, _, _, _ => by simp
  | n + 1, L, Υ, ℓ, ρ, hL, hΥ => by
    rw [List.ofFn_succ, List.prod_cons, List.ofFn_succ, List.prod_cons, Fin.prod_univ_succ,
      Fin.prod_univ_succ]
    set P' := (List.ofFn fun i : Fin n => L i.succ + Υ i.succ).prod
    set P := (List.ofFn fun i : Fin n => L i.succ).prod
    have ih := norm_prod_add_sub_prod_le n (fun i => L i.succ) (fun i => Υ i.succ)
      (fun i => ℓ i.succ) (fun i => ρ i.succ) (fun i => hL _) (fun i => hΥ _)
    have hP := norm_ofFn_prod_le n (fun i => L i.succ) (fun i => ℓ i.succ) (fun i => hL _)
    have hℓ0 : 0 ≤ ℓ 0 := (norm_nonneg _).trans (hL 0)
    have hρ0 : 0 ≤ ρ 0 := (norm_nonneg _).trans (hΥ 0)
    have e : (L 0 + Υ 0) * P' - L 0 * P = (L 0 + Υ 0) * (P' - P) + Υ 0 * P := by
      simp only [mul_sub, add_mul]
      abel
    rw [e]
    have hLU : ‖L 0 + Υ 0‖ ≤ ℓ 0 + ρ 0 := (norm_add_le _ _).trans (add_le_add (hL 0) (hΥ 0))
    calc ‖(L 0 + Υ 0) * (P' - P) + Υ 0 * P‖
        ≤ ‖L 0 + Υ 0‖ * ‖P' - P‖ + ‖Υ 0‖ * ‖P‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_mul_le _ _) (norm_mul_le _ _))
      _ ≤ (ℓ 0 + ρ 0) * (∏ i : Fin n, (ℓ i.succ + ρ i.succ) - ∏ i : Fin n, ℓ i.succ) +
          ρ 0 * ∏ i : Fin n, ℓ i.succ :=
          add_le_add (mul_le_mul hLU ih (norm_nonneg _) (add_nonneg hℓ0 hρ0))
            (mul_le_mul (hΥ 0) hP (norm_nonneg _) hρ0)
      _ = (ℓ 0 + ρ 0) * ∏ i : Fin n, (ℓ i.succ + ρ i.succ) - ℓ 0 * ∏ i : Fin n, ℓ i.succ := by
          ring

/-- The remainder monomial: with raw-arm coefficients `c_i` (times `q_X^{2a}`),
`∏ c_i (ℓ_i + ρ_i) - ∏ c_i ℓ_i = (∏ c_i)(∏ (ℓ_i + ρ_i) - ∏ ℓ_i)`, i.e.
`π^tot_ω - π^lead_ω = π̃^arm_ω C_X υ_ω`. -/
theorem remainder_monomial {ι : Type*} (s : Finset ι) (c ℓ ρ : ι → ℝ) :
    ∏ i ∈ s, (c i * ℓ i + c i * ρ i) - ∏ i ∈ s, (c i * ℓ i) =
      (∏ i ∈ s, c i) * (∏ i ∈ s, (ℓ i + ρ i) - ∏ i ∈ s, ℓ i) := by
  rw [mul_sub, ← prod_mul_distrib, ← prod_mul_distrib]
  congr 1
  exact prod_congr rfl fun i _ => by ring

/-- The remainder bound is nonnegative: `∏ ℓ_i ≤ ∏ (ℓ_i + ρ_i)` for `ℓ, ρ ≥ 0`. -/
theorem prod_le_prod_add {ι : Type*} (s : Finset ι) (ℓ ρ : ι → ℝ) (hℓ : ∀ i ∈ s, 0 ≤ ℓ i)
    (hρ : ∀ i ∈ s, 0 ≤ ρ i) : ∏ i ∈ s, ℓ i ≤ ∏ i ∈ s, (ℓ i + ρ i) :=
  prod_le_prod₀ hℓ fun i hi => le_add_of_nonneg_right (hρ i hi)

end Sarkozy.Envelopes
