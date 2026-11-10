module

public import Sarkozy.UpperComparison.LEMixture

@[expose] public section

/-!
# Non-vacuity of the form-level statements of section 26

Toy instances for the headline theorems of `ForestRecords.lean`, `DenseLaws.lean` and
`LEMixture.lean`: every hypothesis of each theorem is discharged at once for one explicit,
non-product law, and the theorem is applied.

**The toy.** `X = Fin 2` with the uniform law `ν`, the sign function `s = (1, -1)` (`E s = 0`,
`‖s‖ = 1`), the star part `𝒮^c = ½ s ⊗ s` and the kernel `K = 1 + ½ s ⊗ s` (a correlated coupling of
the uniform law with itself; its centred operator has norm `1/2`, attained at `s`). The remainders
vanish, the normalizers are one, the multipliers vanish (`F = 0`) and the half marginals are
uniform (`u₀ = 0`). The bounds hold with `Γ = 1`, `k = 1`, `r = 1/2`.

* `toy_forest_records_a`, `toy_forest_records_b`: `prop:forest-records`(a), (b);
* `toy_dense_comparison_a`, `toy_dense_comparison_b`: `prop:dense-comparison`(a), (b);
* `toy_le_mixture_law`, `toy_le_mixture_change`, `toy_le_component_change`,
  `toy_le_mixture_of_components`: `prop:le-mixture`.

The positivity, mass and marginal hypotheses are the binding ones (the lesson of 1 November about
contradictory marginal conventions): here they hold with a law that is not a product law.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.UpperComparison

open Sarkozy.Recentering Sarkozy.Structured

/-- The uniform law on `Fin 2`. -/
noncomputable def toyLaw : FiniteLaw (Fin 2) where
  weight _ := 1 / 2
  nonneg _ := by norm_num
  total := by simp

/-- The sign function `s = (1, -1)`. -/
def toyS (x : Fin 2) : ℝ := if x = 0 then 1 else -1

theorem toyS_sq (x : Fin 2) : toyS x * toyS x = 1 := by
  unfold toyS; split_ifs <;> norm_num

theorem toy_expect (f : Fin 2 → ℝ) : toyLaw.expect f = (f 0 + f 1) / 2 := by
  simp [FiniteLaw.expect, toyLaw, Fin.sum_univ_two]; ring

theorem toyS_mean : toyLaw.expect toyS = 0 := by
  rw [toy_expect]; simp [toyS]

theorem toyS_nrm : nrm toyLaw toyS = 1 := by
  unfold nrm ip
  rw [toyLaw.expect_congr toyS_sq, toyLaw.expect_const, Real.sqrt_one]

/-- The toy star part `𝒮^c = ½ s ⊗ s`. -/
noncomputable def toySc (p : Fin 2 × Fin 2) : ℝ := 1 / 2 * (toyS p.1 * toyS p.2)

/-- The toy kernel `K = 1 + ½ s ⊗ s`. -/
noncomputable def toyK (p : Fin 2 × Fin 2) : ℝ := 1 + toySc p

/-- The zero kernel. -/
def toyZero (_ : Fin 2 × Fin 2) : ℝ := 0

theorem toySc_form (φ ψ : Fin 2 → ℝ) :
    kform toyLaw toyLaw toySc φ ψ = 1 / 2 * (ip toyLaw φ toyS * ip toyLaw ψ toyS) := by
  unfold toySc
  rw [kform_const_mul toyLaw toyLaw (1 / 2) (fun p => toyS p.1 * toyS p.2),
    kform_rank_one toyLaw toyS toyS]
  rfl

theorem toySc_bound (φ ψ : Fin 2 → ℝ) :
    |kform toyLaw toyLaw toySc φ ψ| ≤ 1 / 2 * nrm toyLaw φ * nrm toyLaw ψ := by
  rw [toySc_form, abs_mul, abs_mul]
  have h1 := abs_ip_le toyLaw φ toyS
  have h2 := abs_ip_le toyLaw ψ toyS
  rw [toyS_nrm, mul_one] at h1 h2
  rw [abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2), mul_assoc]
  exact mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 (abs_nonneg _) (Real.sqrt_nonneg _))
    (by norm_num)

theorem toySc_symm (φ ψ : Fin 2 → ℝ) :
    kform toyLaw toyLaw toySc ψ φ = kform toyLaw toyLaw toySc φ ψ := by
  rw [toySc_form, toySc_form, mul_comm (ip toyLaw ψ toyS)]

theorem toySc_row (x : Fin 2) : toyLaw.expect (fun y => toySc (x, y)) = 0 := by
  unfold toySc
  rw [toy_expect]; simp [toyS]

theorem toySc_col (y : Fin 2) : toyLaw.expect (fun x => toySc (x, y)) = 0 := by
  unfold toySc
  rw [toy_expect]; fin_cases y <;> simp [toyS]

theorem toyK_row (x : Fin 2) : toyLaw.expect (fun y => toyK (x, y)) = 1 + (fun _ => (0 : ℝ)) x := by
  unfold toyK
  rw [toyLaw.expect_add, toyLaw.expect_const, toySc_row]

theorem toyK_col (y : Fin 2) : toyLaw.expect (fun x => toyK (x, y)) = 1 + (fun _ => (0 : ℝ)) y := by
  unfold toyK
  rw [toyLaw.expect_add, toyLaw.expect_const, toySc_col]

theorem toyK_mass : toyLaw.expect (fun x => toyLaw.expect (fun y => toyK (x, y))) = 1 := by
  rw [toyLaw.expect_congr toyK_row]; simp

theorem toyK_nonneg (p : Fin 2 × Fin 2) : 0 ≤ toyK p := by
  unfold toyK toySc toyS; split_ifs <;> norm_num

theorem toyK_symm (x y : Fin 2) : toyK (x, y) = toyK (y, x) := by
  unfold toyK toySc; ring

theorem toy_kform_zero (φ ψ : Fin 2 → ℝ) : kform toyLaw toyLaw toyZero φ ψ = 0 := by
  unfold kform toyZero; simp

theorem toy_mnrm (φ : Fin 2 → ℝ) : mnrm toyLaw (fun _ => 0) φ = nrm toyLaw φ := by
  unfold mnrm nrm ip
  congr 1
  exact toyLaw.expect_congr fun x => by ring

/-- The centred operator of the toy law (uniform marginals) is the form of `𝒮^c`. -/
theorem toyK_centred (φ ψ : Fin 2 → ℝ) :
    centredForm toyLaw (fun _ => 0) toyK φ ψ = kform toyLaw toyLaw toySc φ ψ := by
  rw [centredForm_eq_kform]
  apply kform_congr
  intro p
  unfold toyK
  ring

theorem toyK_centred_bound (φ ψ : Fin 2 → ℝ) :
    |centredForm toyLaw (fun _ => 0) toyK φ ψ| ≤
      1 / 2 * mnrm toyLaw (fun _ => 0) φ * mnrm toyLaw (fun _ => 0) ψ := by
  rw [toyK_centred, toy_mnrm, toy_mnrm]; exact toySc_bound φ ψ

/-- On centred functions the toy kernel has the form of its star part. -/
theorem toyK_form_centred (φ ψ : Fin 2 → ℝ) (hψ : toyLaw.expect ψ = 0) :
    kform toyLaw toyLaw toyK φ ψ = kform toyLaw toyLaw toySc φ ψ + 0 := by
  have e : ∀ p, toyK p = (fun _ : Fin 2 × Fin 2 => (1 : ℝ)) p + toySc p := fun p => rfl
  rw [kform_congr toyLaw toyLaw e, kform_add, kform_const_centred toyLaw 1 φ ψ hψ, zero_add,
    add_zero]

theorem toy_nrm_zero : nrm toyLaw (fun _ => (0 : ℝ)) = 0 := by
  unfold nrm ip; simp

theorem toy_center_zero :
    nrm toyLaw (center toyLaw (fun x => toyLaw.expect (fun y => toyZero (x, y)))) ≤ 0 := by
  unfold center toyZero; simp [nrm, ip]

theorem toy_center_zero' :
    nrm toyLaw (center toyLaw (fun y => toyLaw.expect (fun x => toyZero (x, y)))) ≤ 0 := by
  unfold center toyZero; simp [nrm, ip]

theorem toy_deltaL : nrm toyLaw (deltaL toyLaw toyK) ≤ 0 := by
  have h : deltaL toyLaw toyK = fun _ => 0 := by
    funext x; unfold deltaL; rw [toyK_row]; ring
  rw [h, toy_nrm_zero]

theorem toy_deltaR : nrm toyLaw (deltaR toyLaw toyK) ≤ 0 := by
  have h : deltaR toyLaw toyK = fun _ => 0 := by
    funext y; unfold deltaR; rw [toyK_col]; ring
  rw [h, toy_nrm_zero]

/-! ## The toy instances -/

/-- **Non-vacuity of `forest_records_a`** (`prop:forest-records`(a)). -/
theorem toy_forest_records_a (φ ψ : Fin 2 → ℝ) :
    |centredForm toyLaw (fun _ => 0) toyK φ ψ| ≤
      forestCNew (1 / 2) 0 (forestCoef 1 1 (1 / 2) 0 0 1) (0 / 1) 0 0 0 *
        mnrm toyLaw (fun _ => 0) φ * mnrm toyLaw (fun _ => 0) ψ :=
  (forest_records_a toyLaw toyK toySc toyZero toyK toyK toyK 1 1
    (fun p => by unfold toyK toyZero; ring) toyK_mass.symm (fun p => (div_one _).symm)
    toySc_row toySc_col (ΓF := 1) (kf := 1) (ks := 1) (ka := 0) (r := 1 / 2) (Eproj := 0)
    (R := 0) (Zm := 1) (by norm_num) (by norm_num) (by norm_num) le_rfl one_pos le_rfl
    (fun φ ψ _ _ => by have := toySc_bound φ ψ; norm_num at this ⊢; linarith)
    (fun φ ψ _ _ => by
      rw [toySc_symm φ ψ]
      have e : (kform toyLaw toyLaw toySc φ ψ + kform toyLaw toyLaw toySc φ ψ) / 2 =
          kform toyLaw toyLaw toySc φ ψ := by ring
      rw [e]; have := toySc_bound φ ψ; norm_num at this ⊢; linarith)
    (fun φ ψ _ _ => by rw [toySc_symm, sub_self, zero_div]; norm_num)
    (fun φ ψ _ _ => by rw [toy_kform_zero]; norm_num) toy_center_zero toy_center_zero'
    (F := 0) (ℓold := 0) (Btop := 0) (q := 0) (ρ' := 1 / 2) (ρold := 1 / 2) le_rfl
    (fun _ => 0) (fun _ => 0) (fun _ => by norm_num) (fun _ => by norm_num)
    (fun p => by ring) (fun _ => 0) (by simp [FiniteLaw.expect]) toyK_row toyK_col
    (fun _ => by norm_num) (by rw [toy_nrm_zero]; norm_num) toyK_centred_bound toyK_symm
    toyK_centred_bound φ ψ).1

/-- **Non-vacuity of `forest_records_b`** (`prop:forest-records`(b)). -/
theorem toy_forest_records_b (φ ψ : Fin 2 → ℝ) :
    |((centredForm toyLaw (fun _ => 0) toyK φ ψ - centredForm toyLaw (fun _ => 0) toyK φ ψ) +
        (centredForm toyLaw (fun _ => 0) toyK ψ φ -
          centredForm toyLaw (fun _ => 0) toyK ψ φ)) / 2| ≤
      forestDSym 0 (forestDRaw 1 0 (1 / 2) 0 0 0 0 0 0 (forestU 1 1 (1 / 2) 0 0)
          (forestU 1 1 (1 / 2) 0 0))
        (forestCoef 1 1 (1 / 2) 0 0 1) (0 / 1) 0 * mnrm toyLaw (fun _ => 0) φ *
        mnrm toyLaw (fun _ => 0) ψ :=
  forest_records_b toyLaw toyK toySc toyZero toyK toyK toyK toyK 1 1 1
    (fun p => by unfold toyK toyZero; ring) toyK_mass.symm (fun p => (div_one _).symm)
    toySc_row toySc_col (ΓF := 1) (kf := 1) (r := 1 / 2) (Eproj := 0) (R := 0) (Zm := 1)
    (by norm_num) le_rfl one_pos le_rfl
    (fun φ ψ _ _ => by have := toySc_bound φ ψ; norm_num at this ⊢; linarith)
    (fun φ ψ _ _ => by rw [toy_kform_zero]; norm_num) toy_center_zero toy_center_zero'
    (fun p => (div_one _).symm) (fun φ ψ => kform toyLaw toyLaw toySc φ ψ) (fun _ _ => 0)
    (fun φ ψ _ hψ => toyK_form_centred φ ψ hψ)
    (ΓF' := 1) (knew := 1) (kold := 1) (kΔ := 0) (Enew := 0) (Eold := 0) (Rold := 0)
    (εnew := 0) (εold := 0) (by norm_num) (by norm_num) (by norm_num) le_rfl le_rfl le_rfl
    (fun _ _ _ _ => by norm_num)
    (fun φ ψ _ _ => by have := toySc_bound φ ψ; norm_num at this ⊢; linarith)
    (fun φ ψ _ _ => by have := toySc_bound φ ψ; norm_num at this ⊢; linarith)
    (fun φ ψ _ _ => by simp only [sub_self, add_zero, zero_div, abs_zero]; norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (F := 0) (ℓold := 0) le_rfl
    (fun _ => 0) (fun _ => 0) (fun _ => by norm_num) (fun _ => by norm_num) (fun p => by ring)
    (fun _ => 0) toyK_row toyK_col toyK_row toyK_col (fun _ => by norm_num) φ ψ

/-- **Non-vacuity of `dense_comparison_a`** (`prop:dense-comparison`(a)): the repaired toy law is a
probability coupling. -/
theorem toy_dense_comparison_a :
    toyLaw.expect (fun x => toyLaw.expect (fun y => toyK (x, y))) = 1 :=
  (dense_comparison_a toyLaw toyK toyK toyK_nonneg (FN := 0) (by norm_num) (fun _ => 0)
    (fun _ => 0) (fun _ => by norm_num) (fun _ => by norm_num) (fun p => by ring) (fun _ => 0)
    (by simp [FiniteLaw.expect]) toyK_row toyK_col).2.1

/-- The toy difference kernel `K - K` has zero form. -/
theorem toy_kform_sub_self (φ ψ : Fin 2 → ℝ) :
    kform toyLaw toyLaw (fun p => toyK p - toyK p) φ ψ = 0 + 0 := by
  rw [kform_congr toyLaw toyLaw (K' := toyZero) (fun p => sub_self (toyK p)), toy_kform_zero,
    add_zero]

/-- **Non-vacuity of `dense_comparison_b`** (`prop:dense-comparison`(b)). -/
theorem toy_dense_comparison_b (φ ψ : Fin 2 → ℝ) :
    |((centredForm toyLaw (fun _ => 0) toyK φ ψ - centredForm toyLaw (fun _ => 0) toyK φ ψ) +
        (centredForm toyLaw (fun _ => 0) toyK ψ φ -
          centredForm toyLaw (fun _ => 0) toyK ψ φ)) / 2| ≤
      denseD 0 1 0 (1 / 2) (denseE 1 1 1 (1 / 2) 0 0 0 0 (1 - 0) (1 - 0)) 0
          (denseC 1 1 (1 / 2) 0 (1 - 0)) 0 * mnrm toyLaw (fun _ => 0) φ *
        mnrm toyLaw (fun _ => 0) ψ :=
  (dense_comparison_b toyLaw toyK toyK toyK toyK toyK 1 1 toyK_mass.symm
    (fun p => (div_one _).symm) (fun p => (div_one _).symm)
    (fun φ ψ => kform toyLaw toyLaw toySc φ ψ) (fun φ ψ => kform toyLaw toyLaw toySc φ ψ)
    (fun _ _ => 0) (fun _ _ => 0)
    (fun φ ψ _ hψ => toyK_form_centred φ ψ hψ) (fun φ ψ _ hψ => toyK_form_centred φ ψ hψ)
    (Γ := 1) (k₀ := 1) (k₁ := 1) (ks := 0) (ka := 0) (r := 1 / 2) (R₀ := 0) (R₁ := 0)
    (ε₀ := 0) (ε₁ := 0) (u₁ := 0) (FN := 0) (ℓ₀ := 0)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) le_rfl le_rfl
    (fun φ ψ _ _ => by have := toySc_bound φ ψ; norm_num at this ⊢; linarith)
    (fun φ ψ _ _ => by have := toySc_bound φ ψ; norm_num at this ⊢; linarith)
    (fun φ ψ _ _ => by simp only [sub_self, add_zero, zero_div, abs_zero]; norm_num)
    (fun φ ψ _ _ => by simp only [sub_self, zero_div, abs_zero]; norm_num)
    (fun φ ψ _ _ => by norm_num) (fun φ ψ _ _ => by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) toy_deltaL toy_deltaR le_rfl
    (fun _ => 0) (fun _ => 0) (fun _ => by norm_num) (fun _ => by norm_num) (fun p => by ring)
    (fun _ => 0) toyK_row toyK_col toyK_row toyK_col (fun _ => by norm_num) φ ψ).1

/-- **Non-vacuity of `le_mixture_law`** (`prop:le-mixture`): the mixture of two copies of the toy
law with weights `1/2` is a probability coupling with uniform marginals. -/
theorem toy_le_mixture_law :
    toyLaw.expect (fun x => toyLaw.expect (fun y =>
      mixKernel (fun _ : Fin 2 => (1 / 2 : ℝ)) (fun _ => toyK) (x, y))) = 1 :=
  (le_mixture_law toyLaw (fun _ : Fin 2 => (1 / 2 : ℝ)) (fun _ => by norm_num)
    (by simp) (fun _ => toyK) (fun _ => toyK_nonneg) (fun _ => 0)
    (by simp [FiniteLaw.expect]) (fun _ => toyK_row) (fun _ => toyK_col)).2.1

/-- **Non-vacuity of `le_mixture_change`** (`prop:le-mixture`). -/
theorem toy_le_mixture_change (φ ψ : Fin 2 → ℝ) :
    |((centredForm toyLaw (fun _ => 0) (mixKernel (fun _ : Fin 2 => (1 / 2 : ℝ)) (fun _ => toyK))
          φ ψ - centredForm toyLaw (fun _ => 0) toyK φ ψ) +
        (centredForm toyLaw (fun _ => 0) (mixKernel (fun _ : Fin 2 => (1 / 2 : ℝ)) (fun _ => toyK))
          ψ φ - centredForm toyLaw (fun _ => 0) toyK ψ φ)) / 2| ≤
      Real.exp 0 *
          (1 * 0 * (1 / 2) + ∑ j : Fin 2, (fun _ => (1 / 2 : ℝ)) j * (fun _ => (0 : ℝ)) j) *
        mnrm toyLaw (fun _ => 0) φ * mnrm toyLaw (fun _ => 0) ψ :=
  (le_mixture_change toyLaw (fun _ : Fin 2 => (1 / 2 : ℝ)) (fun _ => by norm_num)
    (by simp) (fun _ => toyK) toyK (fun _ => 0) (fun _ => toyK_row) (fun _ => toyK_col)
    toyK_row toyK_col (fun _ _ _ => 0) (fun _ _ _ => 0)
    (fun _ φ ψ _ _ => toy_kform_sub_self φ ψ) (fun _ => 0) (fun _ _ _ _ _ => by norm_num)
    (Γ := 1) (ks := 0) (ka := 0) (r := 1 / 2) (ℓ₀ := 0) (by norm_num) (by norm_num)
    (fun _ => le_rfl) (fun _ _ _ _ => by norm_num) (fun _ _ _ _ => by norm_num)
    (fun _ => by norm_num) φ ψ).1

/-- **Non-vacuity of `le_component_change`** (`prop:le-mixture`). -/
theorem toy_le_component_change (φ ψ : Fin 2 → ℝ) (hφ : toyLaw.expect φ = 0)
    (hψ : toyLaw.expect ψ = 0) :
    |kform toyLaw toyLaw (fun p => toyK p - toyK p) φ ψ -
        (kform toyLaw toyLaw toySc φ ψ - kform toyLaw toyLaw toySc φ ψ)| ≤
      leCompE 1 1 1 (1 / 2) 0 0 0 0 0 0 * nrm toyLaw φ * nrm toyLaw ψ :=
  le_component_change toyLaw toyK toyK toyK toyK toyK 1 1 toyK_mass.symm
    (fun p => (div_one _).symm) (fun p => (div_one _).symm)
    (fun φ ψ => kform toyLaw toyLaw toySc φ ψ) (fun φ ψ => kform toyLaw toyLaw toySc φ ψ)
    (fun _ _ => 0) (fun _ _ => 0)
    (fun φ ψ _ hψ => toyK_form_centred φ ψ hψ) (fun φ ψ _ hψ => toyK_form_centred φ ψ hψ)
    (Γ := 1) (k₀ := 1) (k₁ := 1) (r := 1 / 2) (R₀ := 0) (R₁ := 0) (ε₀ := 0) (ε₁ := 0) (u := 0)
    (F := 0) (by norm_num) le_rfl
    (fun φ ψ _ _ => by have := toySc_bound φ ψ; norm_num at this ⊢; linarith)
    (fun φ ψ _ _ => by have := toySc_bound φ ψ; norm_num at this ⊢; linarith)
    (fun φ ψ _ _ => by norm_num) (fun φ ψ _ _ => by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) toy_deltaL toy_deltaR le_rfl
    (fun _ => 0) (fun _ => 0) (fun _ => by norm_num) (fun _ => by norm_num) (fun p => by ring)
    φ ψ hφ hψ

/-- **Non-vacuity of `le_mixture_of_components`** (`prop:le-mixture` from the component inputs). -/
theorem toy_le_mixture_of_components (φ ψ : Fin 2 → ℝ) :
    |((centredForm toyLaw (fun _ => 0) (mixKernel (fun _ : Fin 2 => (1 / 2 : ℝ)) (fun _ => toyK))
          φ ψ - centredForm toyLaw (fun _ => 0) toyK φ ψ) +
        (centredForm toyLaw (fun _ => 0) (mixKernel (fun _ : Fin 2 => (1 / 2 : ℝ)) (fun _ => toyK))
          ψ φ - centredForm toyLaw (fun _ => 0) toyK ψ φ)) / 2| ≤
      Real.exp 0 * (1 * 0 * (1 / 2) + ∑ j : Fin 2, (fun _ => (1 / 2 : ℝ)) j *
          leCompE 1 ((fun _ => (1 : ℝ)) j) ((fun _ => (1 : ℝ)) j) (1 / 2) ((fun _ => (0 : ℝ)) j)
            ((fun _ => (0 : ℝ)) j) ((fun _ => (0 : ℝ)) j) ((fun _ => (0 : ℝ)) j)
            ((fun _ => (0 : ℝ)) j) ((fun _ => (0 : ℝ)) j)) *
        mnrm toyLaw (fun _ => 0) φ * mnrm toyLaw (fun _ => 0) ψ :=
  (le_mixture_of_components toyLaw (fun _ : Fin 2 => (1 / 2 : ℝ)) (fun _ => by norm_num)
    (by simp) toyK toyK 1 (fun p => (div_one _).symm) (fun _ => toyK) (fun _ => toyK)
    (fun _ => toyK) (fun _ => 1) (fun _ => toyK_mass.symm) (fun _ p => (div_one _).symm)
    (fun _ φ ψ => kform toyLaw toyLaw toySc φ ψ) (fun _ _ _ => 0)
    (fun _ φ ψ => kform toyLaw toyLaw toySc φ ψ) (fun _ _ _ => 0)
    (fun _ φ ψ _ hψ => toyK_form_centred φ ψ hψ) (fun _ φ ψ _ hψ => toyK_form_centred φ ψ hψ)
    (Γ := 1) (r := 1 / 2) (ks := 0) (ka := 0) (ℓ₀ := 0)
    (fun _ => 1) (fun _ => 1) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0)
    (fun _ => 0) (fun _ => by norm_num) (fun _ => by norm_num) (fun _ => le_rfl)
    (fun _ => le_rfl)
    (fun _ φ ψ _ _ => by have := toySc_bound φ ψ; norm_num at this ⊢; linarith)
    (fun _ φ ψ _ _ => by have := toySc_bound φ ψ; norm_num at this ⊢; linarith)
    (fun _ φ ψ _ _ => by norm_num) (fun _ φ ψ _ _ => by norm_num)
    (fun _ => by norm_num) (fun _ => by norm_num) (fun _ => by norm_num) (fun _ => by norm_num)
    (fun _ => toy_deltaL) (fun _ => toy_deltaR) (fun _ => le_rfl) (fun _ _ => 0) (fun _ _ => 0)
    (fun _ _ => by norm_num) (fun _ _ => by norm_num) (fun _ p => by ring) (fun _ => 0)
    (fun _ => toyK_row) (fun _ => toyK_col) toyK_row toyK_col (by norm_num) (by norm_num)
    (fun _ _ _ _ => by simp) (fun _ _ _ _ => by simp) (fun _ => by norm_num) φ ψ).1

end Sarkozy.UpperComparison
