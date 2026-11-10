module

public import Sarkozy.UpperReference.MonotoneEndpoint
public import Sarkozy.UpperReference.ObservedCaps

/-!
# Non-vacuity of the hypotheses of the upper-reference theorems

Degenerate instances showing that the hypotheses of the main theorems of this directory can hold
together (the lesson of 1 November: contradictory hypotheses make a theorem vacuous). They show
only joint satisfiability, not that the paper's numbers satisfy them.

* `monotone_endpoint_prime_satisfiable`: every hypothesis of `monotone_endpoint_prime` (and so of
  `thm:record:direct-star` through `direct_star_explicit`) holds for `H = ℝ`, one mode, `n = 1`,
  the isometric frame `E = id`, `𝐁 = 0`, `D = 𝐑 = 𝐇 = 0`, `ε_V = ε_× = 0`, `ε_𝐁 = 1/4`,
  `s_⋆ = g_⋆ = 1` (the Schur test is `(1/2 - 1/4) I ⪰ 0`), `Op = K₀ = id`, `Z₀ = 1`, and zero
  inputs; the conclusion is `Op ⪰ -(1/2) I`.
* `endpoint_numbers_satisfiable`: the hypotheses of `endpoint_numbers` with constant inputs.
* `observed_lower_satisfiable`: the hypotheses of `observed_lower` for `H = ℝ`, `W = ⊤`,
  `Op = id`, zero star, nonstar and coincidence parts.
-/

@[expose] public section

open scoped InnerProductSpace Matrix ComplexOrder

namespace Sarkozy.UpperReference.Sanity

open Sarkozy Sarkozy.Spectral Sarkozy.Majorant

/-- The isometric frame `(Fin 1 → ℝ) → ℝ`, `u ↦ u 0`. -/
noncomputable def frameE : (Fin 1 → ℝ) →ₗ[ℝ] ℝ := LinearMap.proj 0

/-- **The hypotheses of `monotone_endpoint_prime` are satisfiable.** -/
theorem monotone_endpoint_prime_satisfiable :
    ∀ f : ℝ, -(1 * (1 / 2)) * ‖f‖ ^ 2 ≤ RCLike.re ⟪f, (LinearMap.id : ℝ →ₗ[ℝ] ℝ) f⟫_ℝ := by
  have hsqn0 : ∀ v : Fin 1 → ℝ, sqn ((0 : Matrix (Fin 1) (Fin 1) ℝ) *ᵥ v) = 0 := by
    intro v
    simp [sqn]
  have hq0 : ∀ v : Fin 1 → ℝ, qform (0 : Matrix (Fin 1) (Fin 1) ℝ) v v = 0 := by
    intro v
    simp [qform]
  have htest : ((0 : Matrix (Fin 1) (Fin 1) ℝ) + ((1 / (1 + 0 + 1) : ℝ) : ℝ) •
      (1 : Matrix (Fin 1) (Fin 1) ℝ) - ((1 / 1 : ℝ) : ℝ) •
        ((0 : Matrix (Fin 1) (Fin 1) ℝ) + ((1 / 4 + 2 * 0 * 0 + 0 ^ 2 * 0 +
          (0 + 0 * 0) ^ 2 / 1 : ℝ) : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ))).PosSemidef := by
    have e : ((0 : Matrix (Fin 1) (Fin 1) ℝ) + ((1 / (1 + 0 + 1) : ℝ) : ℝ) •
        (1 : Matrix (Fin 1) (Fin 1) ℝ) - ((1 / 1 : ℝ) : ℝ) •
          ((0 : Matrix (Fin 1) (Fin 1) ℝ) + ((1 / 4 + 2 * 0 * 0 + 0 ^ 2 * 0 +
            (0 + 0 * 0) ^ 2 / 1 : ℝ) : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ))) =
        (1 / 4 : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ) := by
      ext i j
      fin_cases i
      fin_cases j
      simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, Matrix.zero_apply,
        smul_eq_mul, Matrix.one_apply_eq]
      norm_num
    rw [e]
    exact Matrix.PosSemidef.one.smul (by norm_num)
  have htestm : (-(0 : Matrix (Fin 1) (Fin 1) ℝ) + ((1 / (1 + 0 + 1) : ℝ) : ℝ) •
      (1 : Matrix (Fin 1) (Fin 1) ℝ) - ((1 / 1 : ℝ) : ℝ) •
        ((0 : Matrix (Fin 1) (Fin 1) ℝ) + ((1 / 4 + 2 * 0 * 0 + 0 ^ 2 * 0 +
          (0 + 0 * 0) ^ 2 / 1 : ℝ) : ℝ) • (1 : Matrix (Fin 1) (Fin 1) ℝ))).PosSemidef := by
    rw [neg_zero]
    exact htest
  have h := monotone_endpoint_prime (𝕜 := ℝ) (H := ℝ) (Ξ := Fin 1) (n := Fin 1)
    LinearMap.id LinearMap.id 0 0 0 0 1 0 (by simp) (fun _ => frameE) (fun _ => 0)
    (fun f _ _ => f) (fun _ _ _ => 0)
    (fun f ξ z => by simp [frameE, dotProduct, mul_comm])
    (fun f ξ z => by simp [dotProduct])
    (fun ξ ξ' hξ => absurd (Subsingleton.elim ξ ξ') hξ)
    0 (fun _ => 0) (fun _ => Or.inl rfl) 0 0 Matrix.PosSemidef.zero
    (εV := 0) (εx := 0) (εB := 1 / 4) (εV₀ := 0) (εx₀ := 0) (εB₀ := 1 / 4) (Λ := 0) (s := 1)
    (g := 1) (r := 1 / 2) le_rfl le_rfl (by norm_num) le_rfl (by norm_num) (by norm_num)
    (by norm_num) (fun v => by rw [hsqn0]; exact mul_nonneg (sq_nonneg _) (sqn_nonneg v))
    (fun v => by simp [hq0, sqn])
    (fun ξ u w => by
      simp [frameE, dotProduct, mul_comm])
    (fun ξ u v => by simp [dotProduct])
    (fun ξ v => by
      have : (0 : ℝ) ≤ 1 / 4 * sqn v := mul_nonneg (by norm_num) (sqn_nonneg v)
      simpa [hq0] using this)
    le_rfl le_rfl le_rfl htest htestm
    (fun f => by simp [qform, dotProduct])
    (Z₀ := 1) (εsoft := 0) (Mstar := 0) (zstar := 0) (Zstar := 0) (Nns := 0) (Dcol := 0)
    (fun x => by simp) (by simp) LinearMap.IsSymmetric.id
    (fun x => by simp) (by simp) (by simp)
    (fun x => by simp) (fun x => by simp) (fun x => by simp) (by simp) (by simp) (by simp)
    (by norm_num) (g₀ := 1) (e₀ := 0) (r₀ := 1 / 2) (by norm_num) (by norm_num) le_rfl
    (by norm_num)
  exact h.2.1

/-- **The hypotheses of `endpoint_numbers` are satisfiable** (constant inputs on a one-point
box). -/
theorem endpoint_numbers_satisfiable :
    epsZ (Δ := Unit) (fun _ => 1 / 2) (fun _ => 0) (fun _ => 0) (fun _ => 0) () < 1 :=
  (endpoint_numbers (Δ := Unit) 1 (by norm_num) (fun _ => 1 / 2) (fun _ => 0) (fun _ => 0)
    (fun _ => 0) (fun _ => 0) (fun _ => 0) (admissible_const (by norm_num))
    (admissible_const le_rfl) (admissible_const le_rfl) (admissible_const le_rfl)
    (admissible_const le_rfl) (admissible_const le_rfl) () (fun _ => le_rfl)
    (by simp [epsZ]) (by simp [gRoot, epsZ]; norm_num) ()).2.1

/-- **The hypotheses of `observed_lower` are satisfiable** (`H = ℝ`, `W = ⊤`, `Op = id`). -/
theorem observed_lower_satisfiable :
    -((1 / (1 - 0) * (0 * 0 + 0 + 0)) + 0 ^ 2) * ‖(1 : ℝ)‖ ^ 2 ≤
      ⟪(1 : ℝ), (LinearMap.id : ℝ →ₗ[ℝ] ℝ) 1⟫_ℝ :=
  (Observed.observed_lower (H := ℝ) LinearMap.id 0 0 0 1 ⊤ (by simp) Submodule.mem_top
    LinearMap.IsSymmetric.id (by simp) (Z₀ := 1) (εZ := 0) (Nns := 0) (Dcol := 0) (ερ := 0)
    (r := 0) (s := 0) (by norm_num) (by norm_num) le_rfl le_rfl
    (fun h hh => by
      have h0 : h = 0 := by simpa [real_inner_eq_re_inner] using hh
      simp [h0])
    (fun x => by simp) (fun x => by simp) (fun h _ _ => by simp) (by simp) 1
    Submodule.mem_top).2

end Sarkozy.UpperReference.Sanity
