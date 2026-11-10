module

public import Sarkozy.RecordExpansion.Toolkit

/-!
# The variance form at the reserved cut

`lem:record:variance-interface` (i) of the paper (Section 10), for one selected
block. `indepLaw c m` is the law `J_c(m) = (m ⊗ m)/m(1)` with independent halves
of laws proportional to `m`, and `c.diagonalLaw m` is the diagonal copy
`Diag_c(m)`. Relative to `m`, their cut operators are the projection `𝒥` onto
the constants and the identity, so `Diag(m) - J(m) ⪰_c 0` with form the centred
norm `‖F - E_m F‖²_m` (`form_diagonal_sub_indep`, `positive_diagonal_sub_indep`).

* `bracket_of_form_bound`: a bilinear bound `|Q_ζ(F, G)| ≤ a Q_L(F,F)^{1/2} Q_L(G,G)^{1/2}`
  relative to a positive law `L` gives the bracket `(aL  ζ; ζ*  aL) ⪰_c 0`
  (generalizing charging rule (ii)).
* `abs_energy_le_variance`: if the cut form of `ζ` is bounded by `γ` relative to
  the centred norm of `m`, i.e. its cut operator `Δ` on `L²(m)` satisfies
  `Δ 1 = Δ* 1 = 0` and `‖Δ‖ ≤ γ`, then with the brackets of (CP3) at the outside
  atoms, `|Y_{ζ ⊗ λ_{-X}}| ≤ γ (Y^Ñ[Diag(m)] - Y^Ñ[J(m)])`, and
  `Y^Ñ[Diag(m)] ≥ Y^Ñ[J(m)]`. This is (i) of the lemma for the selected block `X`
  with `m = m_X`.

The paper's hypothesis is a tensor product `Δ_X = ⊗_B Δ_B` of self-adjoint or
skew-adjoint factors, an even number of them skew. It yields the bilinear bound
used here with `γ = ∏_B γ_B`. That deduction, which needs the multiplicativity of
operator norms under tensor products, is not formalized, and neither are parts
(ii), (iii), which use (E1).
-/

@[expose] public section

open Finset
open scoped BigOperators

namespace Sarkozy.RecordExpansion

section Form

variable {W Y : Type*} [Fintype W] [DecidableEq W]

/-- **A bilinear bound relative to a positive law gives a bracket**:
`|Q_ζ(F, G)| ≤ a Q_L(F,F)^{1/2} Q_L(G,G)^{1/2}` for all half-functions, `L ⪰_c 0`, `a ≥ 0`
give `(aL  ζ; ζ*  aL) ⪰_c 0`. -/
theorem bracket_of_form_bound {c : ReflectionCut W} {L ζ : ((W → Y) → ℝ) →ₗ[ℝ] ℝ}
    (hL : c.Positive L) {a : ℝ} (ha : 0 ≤ a)
    (h : ∀ F G : (c.Half → Y) → ℝ, |c.form ζ F G| ≤
      a * Real.sqrt (c.form L F F) * Real.sqrt (c.form L G G)) :
    c.Bracket (a • L) ζ (a • L) := by
  refine ⟨hL.smul ha, hL.smul ha, ?_⟩
  intro F G
  change 0 ≤ a * c.form L F F + 2 * c.form ζ F G + a * c.form L G G
  set p := Real.sqrt (c.form L F F)
  set q := Real.sqrt (c.form L G G)
  have hp : p * p = c.form L F F := Real.mul_self_sqrt (hL.nonneg F)
  have hq : q * q = c.form L G G := Real.mul_self_sqrt (hL.nonneg G)
  have h1 := neg_abs_le (c.form ζ F G)
  have h2 := h F G
  have h3 : 0 ≤ a * ((p - q) * (p - q)) := mul_nonneg ha (mul_self_nonneg _)
  rw [← hp, ← hq]
  nlinarith

end Form

section Laws

variable {W Y : Type*} [Fintype W] [DecidableEq W] [Fintype Y]

/-- The law `J_c(m) = (m ⊗ m)/m(1)` with independent halves: plus half and reflected
minus half independent, each with law proportional to `m`. -/
noncomputable def indepLaw (c : ReflectionCut W) (m : (c.Half → Y) → ℝ) :
    ((W → Y) → ℝ) →ₗ[ℝ] ℝ :=
  (1 / ∑ x, m x) •
    sampleIntegral (fun p : (c.Half → Y) × (c.Half → Y) => m p.1 * m p.2)
      (fun p => c.join p.1 p.2)

theorem form_indepLaw (c : ReflectionCut W) (m : (c.Half → Y) → ℝ)
    (F G : (c.Half → Y) → ℝ) :
    c.form (indepLaw c m) F G = (∑ x, m x * F x) * (∑ y, m y * G y) / ∑ x, m x := by
  change (1 / ∑ x, m x) * (∑ p : (c.Half → Y) × (c.Half → Y), m p.1 * m p.2 *
    (F (fun v => c.join p.1 p.2 v.1) * G (fun v => c.join p.1 p.2 (c.flip v.1)))) = _
  simp only [ReflectionCut.join_plus, ReflectionCut.join_minus]
  rw [Fintype.sum_prod_type, Finset.sum_mul_sum]
  have he : ∀ x y : c.Half → Y, m x * m y * (F (fun v => x v) * G (fun v => y v)) =
      m x * F x * (m y * G y) := by
    intro x y
    ring
  simp_rw [he]
  ring

/-- The form of `Diag(m) - J(m)` is the centred norm
`∑ m F² - (∑ m F)²/∑ m = ∑ m (F - E_m F)²`. -/
theorem form_diagonal_sub_indep (c : ReflectionCut W) (m : (c.Half → Y) → ℝ)
    (F G : (c.Half → Y) → ℝ) :
    c.form (c.diagonalLaw m - indepLaw c m) F G =
      ∑ x, m x * (F x * G x) - (∑ x, m x * F x) * (∑ y, m y * G y) / ∑ x, m x := by
  change c.form (c.diagonalLaw m) F G - c.form (indepLaw c m) F G = _
  rw [c.form_diagonalLaw, form_indepLaw]

theorem positive_indepLaw (c : ReflectionCut W) {m : (c.Half → Y) → ℝ}
    (hm : ∀ x, 0 ≤ m x) : c.Positive (indepLaw c m) := by
  constructor
  · intro F G
    rw [form_indepLaw, form_indepLaw]
    ring
  · intro F
    rw [form_indepLaw]
    exact div_nonneg (mul_self_nonneg _) (sum_nonneg fun x _ => hm x)

/-- `Diag(m) - J(m) ⪰_c 0` for `m ≥ 0`: its form is a centred second moment. -/
theorem positive_diagonal_sub_indep (c : ReflectionCut W) {m : (c.Half → Y) → ℝ}
    (hm : ∀ x, 0 ≤ m x) : c.Positive (c.diagonalLaw m - indepLaw c m) := by
  constructor
  · intro F G
    rw [form_diagonal_sub_indep, form_diagonal_sub_indep]
    congr 1
    · apply sum_congr rfl
      intro x _
      ring
    · ring
  · intro F
    rw [form_diagonal_sub_indep]
    by_cases h0 : ∑ x, m x = 0
    · have hz : ∀ x, m x = 0 := fun x =>
        (Finset.sum_eq_zero_iff_of_nonneg (fun x _ => hm x)).mp h0 x (mem_univ x)
      simp [hz]
    · have hpos : 0 < ∑ x, m x := lt_of_le_of_ne (sum_nonneg fun x _ => hm x) (Ne.symm h0)
      set μF := (∑ x, m x * F x) / ∑ x, m x
      have hc : 0 ≤ ∑ x, m x * ((F x - μF) * (F x - μF)) :=
        sum_nonneg fun x _ => mul_nonneg (hm x) (mul_self_nonneg _)
      have he : ∑ x, m x * ((F x - μF) * (F x - μF)) =
          ∑ x, m x * (F x * F x) - (∑ x, m x * F x) * (∑ y, m y * F y) / ∑ x, m x := by
        have h1 : ∑ x, m x * ((F x - μF) * (F x - μF)) =
            ∑ x, m x * (F x * F x) - 2 * μF * ∑ x, m x * F x + μF * μF * ∑ x, m x := by
          rw [mul_sum, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
          apply sum_congr rfl
          intro x _
          ring
        rw [h1]
        simp only [μF]
        field_simp
        ring
      linarith

end Laws

/-! ### The variance bound for a selected block -/

section Energy

variable {J V : Type*} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
  {X : J → Type*} [∀ b, Fintype (X b)] [∀ b, DecidableEq (X b)]

/-- **`lem:record:variance-interface` (i)** for a selected block `j₀` with plus-half law
`m ≥ 0`. If the cut form of `ζ` satisfies the centred bound
`|Q_ζ(F, G)| ≤ γ ‖F - E_m F‖_m ‖G - E_m G‖_m`, and the outside factors have the brackets
`(Ñ_b λ_b; λ_b Ñ_b) ⪰_c 0` of (CP3), then
`|Y_{ζ ⊗ λ_{-X}}| ≤ γ (Y^Ñ[Diag(m)] - Y^Ñ[J(m)])`. -/
theorem abs_energy_le_variance (c : ReflectionCut V) (N lam : ∀ b, ((V → X b) → ℝ) →ₗ[ℝ] ℝ)
    (j₀ : J) (hN : ∀ j, j ≠ j₀ → c.Bracket (N j) (lam j) (N j))
    {m : (c.Half → X j₀) → ℝ} (hm : ∀ x, 0 ≤ m x) {γ : ℝ} (hγ : 0 ≤ γ)
    (ζ : ((V → X j₀) → ℝ) →ₗ[ℝ] ℝ)
    (hζ : ∀ F G : (c.Half → X j₀) → ℝ, |c.form ζ F G| ≤
      γ * Real.sqrt (c.form (c.diagonalLaw m - indepLaw c m) F F) *
        Real.sqrt (c.form (c.diagonalLaw m - indepLaw c m) G G))
    (F : (∀ b, X b) → ℝ) :
    |diagonalIntegral (tensorLaw (Function.update lam j₀ ζ)) F| ≤
      γ * (diagonalIntegral (tensorLaw (Function.update N j₀ (c.diagonalLaw m))) F -
        diagonalIntegral (tensorLaw (Function.update N j₀ (indepLaw c m))) F) := by
  have hb : ∀ j, c.Bracket (Function.update N j₀ (γ • (c.diagonalLaw m - indepLaw c m)) j)
      (Function.update lam j₀ ζ j)
      (Function.update N j₀ (γ • (c.diagonalLaw m - indepLaw c m)) j) := by
    intro j
    by_cases hj : j = j₀
    · subst hj
      simp only [Function.update_self]
      exact bracket_of_form_bound (positive_diagonal_sub_indep c hm) hγ hζ
    · simp only [Function.update_of_ne hj]
      exact hN j hj
  have h := abs_diagonal_le_self_of_bracket (ReflectionCut.Bracket.tensor hb) F
  rw [tensorLaw_update_smul, tensorLaw_update_sub] at h
  exact h

/-- The order part of (i): `Y^Ñ[Diag(m)] ≥ Y^Ñ[J(m)]` for positive outside factors. -/
theorem energy_indep_le_diagonal (c : ReflectionCut V) (N : ∀ b, ((V → X b) → ℝ) →ₗ[ℝ] ℝ)
    (j₀ : J) (hN : ∀ j, j ≠ j₀ → c.Positive (N j)) {m : (c.Half → X j₀) → ℝ}
    (hm : ∀ x, 0 ≤ m x) (F : (∀ b, X b) → ℝ) :
    diagonalIntegral (tensorLaw (Function.update N j₀ (indepLaw c m))) F ≤
      diagonalIntegral (tensorLaw (Function.update N j₀ (c.diagonalLaw m))) F :=
  energy_le_of_below_factor c N j₀ hN (positive_diagonal_sub_indep c hm) F

end Energy

end Sarkozy.RecordExpansion
