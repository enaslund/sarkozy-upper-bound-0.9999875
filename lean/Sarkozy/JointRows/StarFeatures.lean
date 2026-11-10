module

public import Sarkozy.FiveType.Rows
public import Sarkozy.Reflection.Matrix

/-!
# The feature maps of `prop:conditional-star` (Step 1, the norm bounds)

Source: `paper/sections/16_extraction.tex`, proof of `prop:conditional-star`, "Centred feature
maps" and Step 1.

* `nrm_cen_le`, `nrm_le_of_density`, `centred_eval_bound`: **the centred evaluation** `U_ν`. For a
  coordinate law `ν = ρ u` with density `ρ ≤ κ` relative to the uniform law `u`,
  `‖ι_ν f‖²_ν = E_u ρ f² ≤ κ ‖f‖²_u`, and centring is a contraction; so
  `‖U_ν f‖_ν = ‖P₀ ι_ν f‖_ν ≤ √κ ‖f‖_u`.
* `schur_le`: **the bound of `∏_{i∈S} Γ_i`** (the step "by `lem:swapped-rectangle`(b) the kernel
  `∏_{i∈S}Γ_i` defines an operator between `0` and `κ r² I`"): if `A ⪯ c I` and `B ⪰ 0` with
  diagonal at most one, then the entrywise product satisfies `A ∘ B ⪯ c I` (Schur's product
  theorem, `matrix_prod_posSemidef`). With `A = Γ_{i₁} ⪯ κ r² I` and `B = ∏_{i ≠ i₁} Γ_i` (positive
  semidefinite with diagonal at most one) this gives `‖W_S‖² ≤ κ r²` (`prod_gamma_le`).
-/

@[expose] public section

open scoped BigOperators
open Matrix

namespace Sarkozy.JointRows.Star

open Sarkozy.FiveType

section Centred

variable {X : Type*} [Fintype X]

/-- Centring is a contraction: `‖f - E f‖ ≤ ‖f‖`. -/
theorem nrm_cen_le (μ : FiniteLaw X) (f : X → ℝ) : nrm μ (cen μ f) ≤ nrm μ f := by
  have h := ip_self_split μ f
  have h1 : ip μ (cen μ f) (cen μ f) ≤ ip μ f f := by nlinarith [sq_nonneg (μ.expect f)]
  exact Real.sqrt_le_sqrt h1

/-- A density bound `ν = ρ u`, `0 ≤ ρ ≤ κ`, gives `‖f‖_ν ≤ √κ ‖f‖_u`. -/
theorem nrm_le_of_density {ν u : FiniteLaw X} {ρ : X → ℝ} {κ : ℝ}
    (hν : ∀ x, ν.weight x = ρ x * u.weight x) (hρ0 : ∀ x, 0 ≤ ρ x) (hρ : ∀ x, ρ x ≤ κ)
    (f : X → ℝ) : nrm ν f ≤ Real.sqrt κ * nrm u f := by
  have h1 : ip ν f f ≤ κ * ip u f f := by
    unfold ip FiniteLaw.expect
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun x _ => ?_
    rw [hν]
    have := mul_le_mul_of_nonneg_right (hρ x) (mul_nonneg (u.nonneg x) (mul_self_nonneg (f x)))
    nlinarith [hρ0 x]
  have hκ : 0 ≤ κ := by
    obtain ⟨x, -, hx⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.univ)
      (f := u.weight) (by rw [u.total]; exact one_ne_zero)
    exact le_trans (hρ0 x) (hρ x)
  calc nrm ν f = Real.sqrt (ip ν f f) := rfl
    _ ≤ Real.sqrt (κ * ip u f f) := Real.sqrt_le_sqrt h1
    _ = Real.sqrt κ * nrm u f := by rw [Real.sqrt_mul hκ]; rfl

/-- **The centred evaluation**: `‖U_ν f‖_ν = ‖P₀ ι_ν f‖_ν ≤ √κ ‖f‖_u`. -/
theorem centred_eval_bound {ν u : FiniteLaw X} {ρ : X → ℝ} {κ : ℝ}
    (hν : ∀ x, ν.weight x = ρ x * u.weight x) (hρ0 : ∀ x, 0 ≤ ρ x) (hρ : ∀ x, ρ x ≤ κ)
    (f : X → ℝ) : nrm ν (cen ν f) ≤ Real.sqrt κ * nrm u f :=
  (nrm_cen_le ν f).trans (nrm_le_of_density hν hρ0 hρ f)

end Centred

section Schur

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- **Schur's bound for entrywise products**: `A ⪯ cI`, `B ⪰ 0`, `B_{tt} ≤ 1` give
`A ∘ B ⪯ cI` (with `c ≥ 0`). -/
theorem schur_le {A B : Matrix n n ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hA : (c • (1 : Matrix n n ℝ) - A).PosSemidef)
    (hB : B.PosSemidef) (hdiag : ∀ t, B t t ≤ 1) :
    (c • (1 : Matrix n n ℝ) - Matrix.of (fun t t' => A t t' * B t t')).PosSemidef := by
  -- `(cI - A) ∘ B ⪰ 0`
  have hprod := matrix_prod_posSemidef
    (fun j : Bool => if j then c • (1 : Matrix n n ℝ) - A else B)
    (fun j => by cases j <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> assumption)
  -- `c(I - diag B) ⪰ 0`
  have hD : (Matrix.diagonal (fun t => c * (1 - B t t))).PosSemidef :=
    PosSemidef.diagonal fun t => mul_nonneg hc (by linarith [hdiag t])
  have hsum := hprod.add hD
  have heq : c • (1 : Matrix n n ℝ) - Matrix.of (fun t t' => A t t' * B t t') =
      Matrix.of (fun x y => ∏ j : Bool, (if j then c • (1 : Matrix n n ℝ) - A else B) x y) +
        Matrix.diagonal (fun t => c * (1 - B t t)) := by
    ext t t'
    rw [Matrix.add_apply, Matrix.of_apply, Fintype.prod_bool, Matrix.sub_apply,
      Matrix.of_apply]
    simp only [↓reduceIte, Bool.false_eq_true, Matrix.sub_apply, Matrix.smul_apply,
      Matrix.one_apply, smul_eq_mul]
    by_cases h : t = t'
    · subst h
      rw [Matrix.diagonal_apply_eq]
      simp only [↓reduceIte]
      ring
    · rw [Matrix.diagonal_apply_ne _ h]
      simp only [h, ↓reduceIte]
      ring
  rw [heq]
  exact hsum

/-- **`∏_{i∈S} Γ_i ⪯ κ r² I`** (Step 1): if every `Γ_i` (`i ∈ S`) is positive semidefinite with
diagonal at most one, and `Γ_{i₁} ⪯ c I` for one `i₁ ∈ S`, then the entrywise product
`∏_{i∈S} Γ_i ⪯ c I`. With `c = κ r²` this gives `‖W_S‖ ≤ √κ r`, since
`‖W_S f‖² = E_{t,t'} f(t) f(t') ∏_{i∈S} Γ_i(t, t')` by independence. -/
theorem prod_gamma_le {I : Type*} [DecidableEq I] (S : Finset I) {i₁ : I} (hi₁ : i₁ ∈ S)
    (Γ : I → Matrix n n ℝ) (hpsd : ∀ i ∈ S, (Γ i).PosSemidef) (hdiag : ∀ i ∈ S, ∀ t, Γ i t t ≤ 1)
    {c : ℝ} (hc : 0 ≤ c) (h1 : (c • (1 : Matrix n n ℝ) - Γ i₁).PosSemidef) :
    (c • (1 : Matrix n n ℝ) - Matrix.of (fun t t' => ∏ i ∈ S, Γ i t t')).PosSemidef := by
  set B : Matrix n n ℝ := Matrix.of (fun t t' => ∏ i ∈ S.erase i₁, Γ i t t') with hB
  have hBpsd : B.PosSemidef := by
    have := matrix_prod_posSemidef (fun j : {i // i ∈ S.erase i₁} => Γ j.1)
      (fun j => hpsd j.1 (Finset.mem_of_mem_erase j.2))
    have heq : B = fun t t' => ∏ j : {i // i ∈ S.erase i₁}, Γ j.1 t t' := by
      ext t t'
      rw [hB, Matrix.of_apply]
      exact (Finset.prod_coe_sort (S.erase i₁) (fun i => Γ i t t')).symm
    rw [heq]
    exact this
  have hBdiag : ∀ t, B t t ≤ 1 := fun t => by
    rw [hB, Matrix.of_apply]
    have := Finset.prod_le_prod₀ (s := S.erase i₁) (f := fun i => Γ i t t)
      (g := fun _ => (1 : ℝ)) (fun i hi => (hpsd i (Finset.mem_of_mem_erase hi)).diag_nonneg)
      (fun i hi => hdiag i (Finset.mem_of_mem_erase hi) t)
    simpa using this
  have h := schur_le hc h1 hBpsd hBdiag
  have heq2 : Matrix.of (fun t t' => ∏ i ∈ S, Γ i t t') =
      Matrix.of (fun t t' => Γ i₁ t t' * B t t') := by
    ext t t'
    rw [Matrix.of_apply, Matrix.of_apply, hB, Matrix.of_apply,
      Finset.mul_prod_erase S (fun i => Γ i t t') hi₁]
  rw [heq2]
  exact h

end Schur

end Sarkozy.JointRows.Star
