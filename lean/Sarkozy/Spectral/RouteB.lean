module

public import Sarkozy.Spectral.Criterion
public import Mathlib.Analysis.Matrix.PosDef

/-!
# Route B of the spectral criterion (`thm:record:direct-star`)

`paper/sections/14_spectral.tex`, Route B, in abstract form.

Part (a), `-g_⋆ r I ⪯ 𝐋 ⪯ g_⋆ r I` for `𝐋 = r (𝐄 A 𝐄^* + 𝐄 𝐖^* + 𝐖 𝐄^*)`:
* `schur_block`: the finite test `eq:record:schur`, `A + (g/α) I - P/g ⪰ 0` with
  `P = 𝐑 + β I ⪰ 0`, gives nonnegativity of the block form
  `u^*(A + g/α) u + 2 re u^* P w + g w^* P w`, i.e. of `[[A + (g/α) I, I], [I, g P^{-1}]]`
  after the substitution `v = P w` (completing the square, the Schur complement step).
* `routeB_lower`, `routeB_two_sided`: from the frame bound `𝐅^*𝐅 ⪯ 𝓜 = diag(α I, P)` summed
  over the modes, `P ≻ 0`, and the tests on every mode (both signs for the two-sided bound),
  `|∑_ξ (u_ξ^* A(ξ) u_ξ + 2 re u_ξ^* v_ξ)| ≤ g ‖f‖²` for `u = 𝐄^* f`, `v = 𝐖^* f`.
* `frame_of_modes`: the frame bound from the per-mode bounds and Young's inequality, with
  `α_⋆ = 1 + ε_V + s_⋆` and `β_⋆ = ε_𝐖 + ε_𝐄𝐖²/s_⋆`.
* `frame_inputs_of_H1`: the per-mode bounds from (H1), with `ε_𝐄𝐖 = ε_× + Λ_D ε_V` and
  `ε_𝐖 = ε_𝐁 + 2Λ_D ε_× + Λ_D² ε_V`.
* `routeB_a`: part (a) from (H1) (on every mode, as bilinear-form bounds) and (H2).
* `direct_star`: (a) and (c)–(e) together, with (b) and the mode identity defining `𝐋` as
  hypotheses.
* `routeB_cde`: (c)–(e) and `|Z₀ - 1| ≤ ε_Z` from (b) in the explicit form of the proof
  (`K₀ = (1 + h_⋆) ⊗ (1 + h_⋆) + 𝐋 + Soft - h_⋆ ⊗ h_⋆ + T_ns - T_coll`, `𝐋 1 = 0`,
  `Soft 1 = 0`), with the paper's constants `ρ_𝓡 = ε_soft + M_⋆² + z_⋆² + N_ns + D_col`,
  `‖P₀ K₀ 1‖ ≤ M_⋆ + N_ns + D_col`, `C_soft = ε_soft + N_ns + D_col`; `direct_star_explicit`:
  (a)–(e) together in this form.

Parts (c)–(e): `routeB_criterion`, from (a), the decomposition (b) `K₀ = (1 + h_⋆) ⊗ (1 + h_⋆) +
𝐋 + 𝓡` with `‖𝓡‖ ≤ ρ_𝓡`, and the two consequences of (b) used in (d) (hypotheses);
`routeB_cde` derives those consequences from the explicit form of (b). The kernel identity (b)
itself (the stars of `lem:spec:stars`, the single pairs, and the soft-star bound `ε_soft`) is not
formalized.

The adjoints are encoded by coefficient maps `cE f ξ`, `cW f ξ` with
`⟪𝐄_ξ z, f⟫ = z^* (cE f ξ)` and `⟪𝐖_ξ z, f⟫ = z^* (cW f ξ)`.
-/

@[expose] public section

open scoped InnerProductSpace ComplexConjugate Matrix ComplexOrder
open RCLike

namespace Sarkozy.Spectral

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n]

/-- The real part of the sesquilinear form `x^* M y`. -/
noncomputable def qform (M : Matrix n n 𝕜) (x y : n → 𝕜) : ℝ := re (star x ⬝ᵥ (M *ᵥ y))

theorem qform_add_right (M : Matrix n n 𝕜) (x y z : n → 𝕜) :
    qform M x (y + z) = qform M x y + qform M x z := by
  simp only [qform, Matrix.mulVec_add, dotProduct_add, map_add]

theorem qform_add_left (M : Matrix n n 𝕜) (x y z : n → 𝕜) :
    qform M (x + y) z = qform M x z + qform M y z := by
  simp only [qform, star_add, add_dotProduct, map_add]

theorem qform_smul_right (M : Matrix n n 𝕜) (x y : n → 𝕜) (c : ℝ) :
    qform M x ((c : 𝕜) • y) = c * qform M x y := by
  simp only [qform, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul, RCLike.re_ofReal_mul]

theorem qform_smul_left (M : Matrix n n 𝕜) (x y : n → 𝕜) (c : ℝ) :
    qform M ((c : 𝕜) • x) y = c * qform M x y := by
  simp only [qform, star_smul, smul_dotProduct, RCLike.star_def, RCLike.conj_ofReal,
    smul_eq_mul, RCLike.re_ofReal_mul]

theorem qform_symm {M : Matrix n n 𝕜} (hM : M.IsHermitian) (x y : n → 𝕜) :
    qform M x y = qform M y x := by
  rw [qform, qform, ← hM.star_dotProduct_mulVec_comm, RCLike.star_def, RCLike.conj_re]

theorem qform_add_smul_one [DecidableEq n] (M : Matrix n n 𝕜) (c : ℝ) (x : n → 𝕜) :
    qform (M + ((c : ℝ) : 𝕜) • (1 : Matrix n n 𝕜)) x x = qform M x x + c * sqn x := by
  unfold qform
  rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, dotProduct_add,
    dotProduct_smul, smul_eq_mul, map_add, RCLike.re_ofReal_mul, re_star_dotProduct_self]

/-- **The Route B finite test as a block form** (`eq:record:schur`, completing the square). -/
theorem schur_block [DecidableEq n] (A P : Matrix n n 𝕜) {g α : ℝ} (hg : 0 < g) (hP : P.PosSemidef)
    (htest : (A + ((g / α : ℝ) : 𝕜) • (1 : Matrix n n 𝕜) - ((1 / g : ℝ) : 𝕜) • P).PosSemidef)
    (u w : n → 𝕜) :
    0 ≤ qform A u u + g / α * sqn u + 2 * qform P u w + g * qform P w w := by
  have h1 := htest.re_dotProduct_nonneg u
  rw [Matrix.sub_mulVec, Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
    Matrix.one_mulVec, dotProduct_sub, dotProduct_add, dotProduct_smul, dotProduct_smul,
    smul_eq_mul, smul_eq_mul, map_sub, map_add, RCLike.re_ofReal_mul, RCLike.re_ofReal_mul,
    re_star_dotProduct_self] at h1
  have h2 := hP.re_dotProduct_nonneg (u + (g : 𝕜) • w)
  have e2 : re (star (u + (g : 𝕜) • w) ⬝ᵥ (P *ᵥ (u + (g : 𝕜) • w))) =
      qform P u u + 2 * g * qform P u w + g ^ 2 * qform P w w := by
    change qform P (u + (g : 𝕜) • w) (u + (g : 𝕜) • w) = _
    rw [qform_add_left, qform_add_right, qform_add_right, qform_smul_right, qform_smul_left,
      qform_smul_left, qform_smul_right, qform_symm hP.isHermitian w u]
    ring
  rw [e2] at h2
  change 0 ≤ qform A u u + g / α * sqn u - 1 / g * qform P u u at h1
  have h3 : 0 ≤ (qform P u u + 2 * g * qform P u w + g ^ 2 * qform P w w) / g :=
    div_nonneg h2 hg.le
  have e3 : (qform P u u + 2 * g * qform P u w + g ^ 2 * qform P w w) / g =
      1 / g * qform P u u + 2 * qform P u w + g * qform P w w := by
    field_simp
  rw [e3] at h3
  linarith

theorem sqn_smul_real (x : n → 𝕜) (c : ℝ) : sqn ((c : 𝕜) • x) = c ^ 2 * sqn x := by
  rw [sqn, sqn, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Pi.smul_apply, smul_eq_mul, norm_mul, RCLike.norm_ofReal, mul_pow, sq_abs]

section Frame

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] {Ξ : Type*} [Fintype Ξ]

local notation "⟪" x ", " y "⟫" => @inner 𝕜 _ _ x y

/-- **`thm:record:direct-star` (a), lower bound, abstract form.** On the modes `ξ`, `𝐄_ξ`,
`𝐖_ξ : ℂⁿ → L²(μ)` have adjoint coefficients `u_ξ = cE f ξ = 𝐄_ξ^* f`, `v_ξ = cW f ξ = 𝐖_ξ^* f`.
If `𝐅^*𝐅 ⪯ diag(α I, P)` summed over the modes (`frame`), `P ≻ 0`, and the finite test
`A(ξ) + (g/α) I - P/g ⪰ 0` holds on every mode, then
`∑_ξ (u_ξ^* A(ξ) u_ξ + 2 re u_ξ^* v_ξ) ≥ -g ‖f‖²`. With `⟪f, 𝐋 f⟫ = r ∑_ξ (…)` this is
`𝐋 ⪰ -g r I`. -/
theorem routeB_lower [DecidableEq n] (E W : Ξ → (n → 𝕜) →ₗ[𝕜] H) (cE cW : H → Ξ → n → 𝕜)
    (hcE : ∀ f ξ z, ⟪E ξ z, f⟫ = star z ⬝ᵥ cE f ξ) (hcW : ∀ f ξ z, ⟪W ξ z, f⟫ = star z ⬝ᵥ cW f ξ)
    (A : Ξ → Matrix n n 𝕜) (P : Matrix n n 𝕜) (hPd : P.PosDef) {α g : ℝ} (hα : 0 < α)
    (hg : 0 < g)
    (frame : ∀ z1 z2 : Ξ → n → 𝕜, ‖∑ ξ, (E ξ (z1 ξ) + W ξ (z2 ξ))‖ ^ 2 ≤
      ∑ ξ, (α * sqn (z1 ξ) + qform P (z2 ξ) (z2 ξ)))
    (htest : ∀ ξ, (A ξ + ((g / α : ℝ) : 𝕜) • (1 : Matrix n n 𝕜) -
      ((1 / g : ℝ) : 𝕜) • P).PosSemidef) (f : H) :
    -g * ‖f‖ ^ 2 ≤ ∑ ξ, (qform (A ξ) (cE f ξ) (cE f ξ) + 2 * re (star (cE f ξ) ⬝ᵥ cW f ξ)) := by
  set u := cE f with hu
  set v := cW f with hv
  have hPinv : P * P⁻¹ = 1 :=
    Matrix.mul_nonsing_inv P ((Matrix.isUnit_iff_isUnit_det P).mp hPd.isUnit)
  set w : Ξ → n → 𝕜 := fun ξ => P⁻¹ *ᵥ v ξ with hw
  have hPw : ∀ ξ, P *ᵥ w ξ = v ξ := fun ξ => by
    rw [hw, Matrix.mulVec_mulVec, hPinv, Matrix.one_mulVec]
  set z1 : Ξ → n → 𝕜 := fun ξ => ((α⁻¹ : ℝ) : 𝕜) • u ξ with hz1
  set Fz := ∑ ξ, (E ξ (z1 ξ) + W ξ (w ξ)) with hFz
  -- `‖f‖² ≥ 2 re ⟪F z, f⟫ - ‖F z‖²`
  have hA : 2 * re ⟪Fz, f⟫ - ‖Fz‖ ^ 2 ≤ ‖f‖ ^ 2 := by
    have := norm_sub_sq (𝕜 := 𝕜) Fz f
    nlinarith [sq_nonneg ‖Fz - f‖]
  -- `re ⟪F z, f⟫ = ∑_ξ (α⁻¹ |u_ξ|² + w_ξ^* P w_ξ)`
  have hB : re ⟪Fz, f⟫ = ∑ ξ, (α⁻¹ * sqn (u ξ) + qform P (w ξ) (w ξ)) := by
    rw [hFz, sum_inner, map_sum]
    refine Finset.sum_congr rfl fun ξ _ => ?_
    rw [inner_add_left, map_add, hcE, hcW, hz1]
    simp only
    rw [star_smul, smul_dotProduct, RCLike.star_def, RCLike.conj_ofReal, smul_eq_mul,
      RCLike.re_ofReal_mul, re_star_dotProduct_self, qform, hPw]
  -- the frame bound
  have hC : ‖Fz‖ ^ 2 ≤ ∑ ξ, (α⁻¹ * sqn (u ξ) + qform P (w ξ) (w ξ)) := by
    refine (frame z1 w).trans_eq (Finset.sum_congr rfl fun ξ _ => ?_)
    rw [hz1]
    simp only
    rw [sqn_smul_real]
    field_simp
  -- the finite test on every mode
  have hD : ∀ ξ, -g * (α⁻¹ * sqn (u ξ) + qform P (w ξ) (w ξ)) ≤
      qform (A ξ) (u ξ) (u ξ) + 2 * re (star (u ξ) ⬝ᵥ v ξ) := by
    intro ξ
    have h := schur_block (A ξ) P hg hPd.posSemidef (htest ξ) (u ξ) (w ξ)
    have e : qform P (u ξ) (w ξ) = re (star (u ξ) ⬝ᵥ v ξ) := by rw [qform, hPw]
    rw [e] at h
    have e2 : g / α * sqn (u ξ) = g * (α⁻¹ * sqn (u ξ)) := by ring
    rw [e2] at h
    linarith
  have hsum := Finset.sum_le_sum fun ξ (_ : ξ ∈ Finset.univ) => hD ξ
  rw [← Finset.mul_sum] at hsum
  have hfin : ∑ ξ, (α⁻¹ * sqn (u ξ) + qform P (w ξ) (w ξ)) ≤ ‖f‖ ^ 2 := by
    rw [hB] at hA
    linarith
  nlinarith

/-- **`thm:record:direct-star` (a), abstract form**: with the finite tests for both signs
(`eq:record:schur`), `|∑_ξ (u_ξ^* A(ξ) u_ξ + 2 re u_ξ^* v_ξ)| ≤ g ‖f‖²`, i.e.
`-g_⋆ r I ⪯ 𝐋 ⪯ g_⋆ r I`. The upper bound is the lower bound for `(-A, -𝐖)`. -/
theorem routeB_two_sided [DecidableEq n] (E W : Ξ → (n → 𝕜) →ₗ[𝕜] H) (cE cW : H → Ξ → n → 𝕜)
    (hcE : ∀ f ξ z, ⟪E ξ z, f⟫ = star z ⬝ᵥ cE f ξ) (hcW : ∀ f ξ z, ⟪W ξ z, f⟫ = star z ⬝ᵥ cW f ξ)
    (A : Ξ → Matrix n n 𝕜) (P : Matrix n n 𝕜) (hPd : P.PosDef) {α g : ℝ} (hα : 0 < α)
    (hg : 0 < g)
    (frame : ∀ z1 z2 : Ξ → n → 𝕜, ‖∑ ξ, (E ξ (z1 ξ) + W ξ (z2 ξ))‖ ^ 2 ≤
      ∑ ξ, (α * sqn (z1 ξ) + qform P (z2 ξ) (z2 ξ)))
    (htest : ∀ ξ, (A ξ + ((g / α : ℝ) : 𝕜) • (1 : Matrix n n 𝕜) -
      ((1 / g : ℝ) : 𝕜) • P).PosSemidef)
    (htest' : ∀ ξ, (-A ξ + ((g / α : ℝ) : 𝕜) • (1 : Matrix n n 𝕜) -
      ((1 / g : ℝ) : 𝕜) • P).PosSemidef) (f : H) :
    |∑ ξ, (qform (A ξ) (cE f ξ) (cE f ξ) + 2 * re (star (cE f ξ) ⬝ᵥ cW f ξ))| ≤ g * ‖f‖ ^ 2 := by
  have hlow := routeB_lower E W cE cW hcE hcW A P hPd hα hg frame htest f
  -- the same for `(-A, -𝐖)`
  have hcW' : ∀ f ξ z, ⟪(-W ξ) z, f⟫ = star z ⬝ᵥ (-cW f ξ) := fun f ξ z => by
    rw [LinearMap.neg_apply, inner_neg_left, hcW, dotProduct_neg]
  have frame' : ∀ z1 z2 : Ξ → n → 𝕜, ‖∑ ξ, (E ξ (z1 ξ) + (-W ξ) (z2 ξ))‖ ^ 2 ≤
      ∑ ξ, (α * sqn (z1 ξ) + qform P (z2 ξ) (z2 ξ)) := by
    intro z1 z2
    have h := frame z1 (fun ξ => -z2 ξ)
    have e1 : ∑ ξ, (E ξ (z1 ξ) + (-W ξ) (z2 ξ)) = ∑ ξ, (E ξ (z1 ξ) + W ξ (-z2 ξ)) :=
      Finset.sum_congr rfl fun ξ _ => by rw [LinearMap.neg_apply, map_neg]
    have e2 : ∀ ξ, qform P (-z2 ξ) (-z2 ξ) = qform P (z2 ξ) (z2 ξ) := fun ξ => by
      simp only [qform, Matrix.mulVec_neg, dotProduct_neg, star_neg, neg_dotProduct, neg_neg]
    rw [e1]
    simp only [e2] at h
    exact h
  have hup := routeB_lower E (fun ξ => -W ξ) cE (fun f ξ => -cW f ξ) hcE hcW' (fun ξ => -A ξ) P
    hPd hα hg frame' htest' f
  have e : ∀ ξ, qform (-A ξ) (cE f ξ) (cE f ξ) + 2 * re (star (cE f ξ) ⬝ᵥ (-cW f ξ)) =
      -(qform (A ξ) (cE f ξ) (cE f ξ) + 2 * re (star (cE f ξ) ⬝ᵥ cW f ξ)) := fun ξ => by
    simp only [qform, Matrix.neg_mulVec, dotProduct_neg, map_neg]
    ring
  simp only [e, Finset.sum_neg_distrib] at hup
  rw [abs_le]
  constructor <;> linarith

/-- **The frame bound from (H1)** (proof of `thm:record:direct-star` (a)): per mode,
`‖𝐄u‖² ≤ (1 + ε_V)|u|²`, `|⟪𝐄u, 𝐖v⟫| ≤ ε_EW |u| |v|` and `‖𝐖v‖² ≤ v^*(𝐑 + ε_W) v`, and
distinct modes have orthogonal images. Then, by Young's inequality with `s_⋆ > 0`,
`‖∑_ξ (𝐄_ξ z₁ + 𝐖_ξ z₂)‖² ≤ ∑_ξ (α_⋆ |z₁|² + z₂^*(𝐑 + β_⋆) z₂)` with
`α_⋆ = 1 + ε_V + s_⋆` and `β_⋆ = ε_W + ε_EW²/s_⋆`. -/
theorem frame_of_modes [DecidableEq n] [DecidableEq Ξ] (E W : Ξ → (n → 𝕜) →ₗ[𝕜] H)
    (R : Matrix n n 𝕜) {εV εEW εW s : ℝ} (hs : 0 < s)
    (hEE : ∀ ξ u, ‖E ξ u‖ ^ 2 ≤ (1 + εV) * sqn u)
    (hEW : ∀ ξ u v, ‖⟪E ξ u, W ξ v⟫‖ ≤ εEW * √(sqn u) * √(sqn v))
    (hWW : ∀ ξ v, ‖W ξ v‖ ^ 2 ≤ qform (R + ((εW : ℝ) : 𝕜) • (1 : Matrix n n 𝕜)) v v)
    (horth : ∀ ξ ξ', ξ ≠ ξ' → ∀ u v u' v', ⟪E ξ u + W ξ v, E ξ' u' + W ξ' v'⟫ = 0)
    (z1 z2 : Ξ → n → 𝕜) :
    ‖∑ ξ, (E ξ (z1 ξ) + W ξ (z2 ξ))‖ ^ 2 ≤ ∑ ξ, ((1 + εV + s) * sqn (z1 ξ) +
      qform (R + ((εW + εEW ^ 2 / s : ℝ) : 𝕜) • (1 : Matrix n n 𝕜)) (z2 ξ) (z2 ξ)) := by
  -- orthogonality of the modes
  have hpy : ‖∑ ξ, (E ξ (z1 ξ) + W ξ (z2 ξ))‖ ^ 2 = ∑ ξ, ‖E ξ (z1 ξ) + W ξ (z2 ξ)‖ ^ 2 := by
    rw [← inner_self_eq_norm_sq (𝕜 := 𝕜), sum_inner, map_sum]
    refine Finset.sum_congr rfl fun ξ _ => ?_
    rw [inner_sum, Finset.sum_eq_single ξ (fun ξ' _ h => horth ξ ξ' (Ne.symm h) _ _ _ _)
      (fun h => absurd (Finset.mem_univ ξ) h), inner_self_eq_norm_sq]
  rw [hpy]
  refine Finset.sum_le_sum fun ξ _ => ?_
  set u := z1 ξ
  set v := z2 ξ
  have hexp : ‖E ξ u + W ξ v‖ ^ 2 = ‖E ξ u‖ ^ 2 + 2 * re ⟪E ξ u, W ξ v⟫ + ‖W ξ v‖ ^ 2 :=
    norm_add_sq (𝕜 := 𝕜) _ _
  have h1 := hEE ξ u
  have h2 : 2 * re ⟪E ξ u, W ξ v⟫ ≤ s * sqn u + εEW ^ 2 / s * sqn v := by
    have hre := (re_le_norm ⟪E ξ u, W ξ v⟫).trans (hEW ξ u v)
    have hsu := Real.sq_sqrt (sqn_nonneg u)
    have hsv := Real.sq_sqrt (sqn_nonneg v)
    have hyoung : 2 * (εEW * √(sqn u) * √(sqn v)) ≤ s * sqn u + εEW ^ 2 / s * sqn v := by
      set a := √(sqn u)
      set b := √(sqn v)
      rw [← hsu, ← hsv]
      have e : s * a ^ 2 + εEW ^ 2 / s * b ^ 2 - 2 * (εEW * a * b) =
          (s * a - εEW * b) ^ 2 / s := by
        field_simp
        ring
      have : 0 ≤ (s * a - εEW * b) ^ 2 / s := by positivity
      linarith
    linarith
  have h3 := hWW ξ v
  have e3 : qform (R + ((εW + εEW ^ 2 / s : ℝ) : 𝕜) • (1 : Matrix n n 𝕜)) v v =
      qform (R + ((εW : ℝ) : 𝕜) • (1 : Matrix n n 𝕜)) v v + εEW ^ 2 / s * sqn v := by
    rw [qform_add_smul_one, qform_add_smul_one]
    ring
  rw [hexp, e3]
  linarith

end Frame

section FromH1

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] {Ξ : Type*} [Fintype Ξ]

local notation "⟪" x ", " y "⟫" => @inner 𝕜 _ _ x y

/-- **The per-mode inputs of the frame bound, from (H1)** (proof of `thm:record:direct-star` (a)).
On one mode, (H1) is stated through the bilinear forms of the operator-norm bounds:
`|⟪𝐄u, 𝐄w⟫ - u^*w| ≤ ε_V |u||w|` (`‖𝐄^*𝐄 - I‖ ≤ ε_V`),
`|⟪𝐄u, 𝐁v⟫ - u^* A v| ≤ ε_× |u||v|` (`‖𝐄^*𝐁/r - A(ξ)‖ ≤ ε_×`, with `𝐁v` for `𝐁v/r`) and
`‖𝐁v‖² ≤ v^*𝐇v + ε_𝐁 |v|²` (`𝐁^*𝐁/r² ⪯ 𝐇 + ε_𝐁 I`); `|Av| ≤ Λ_D |v|` and
`v^*𝐑v = v^*𝐇v - |Av|²` (`𝐑 = 𝐇 - (Δ^E)ᵀΔ^E = 𝐇 - A^*A`). Then, for `𝐖 = 𝐁 - 𝐄A`:
`‖𝐄u‖² ≤ (1 + ε_V)|u|²`, `|⟪𝐄u, 𝐖v⟫| ≤ ε_𝐄𝐖 |u||v|` with `ε_𝐄𝐖 = ε_× + Λ_D ε_V`, and
`‖𝐖v‖² ≤ v^*(𝐑 + ε_𝐖)v` with `ε_𝐖 = ε_𝐁 + 2Λ_D ε_× + Λ_D² ε_V`. -/
theorem frame_inputs_of_H1 [DecidableEq n] (E Bn : (n → 𝕜) →ₗ[𝕜] H) (A Hm R : Matrix n n 𝕜)
    {εV εx εB Λ : ℝ} (hεV : 0 ≤ εV) (hεx : 0 ≤ εx) (hΛ0 : 0 ≤ Λ)
    (hΛ : ∀ v, sqn (A *ᵥ v) ≤ Λ ^ 2 * sqn v)
    (hR : ∀ v, qform R v v = qform Hm v v - sqn (A *ᵥ v))
    (h1a : ∀ u w, ‖⟪E u, E w⟫ - star u ⬝ᵥ w‖ ≤ εV * √(sqn u) * √(sqn w))
    (h1b : ∀ u v, ‖⟪E u, Bn v⟫ - star u ⬝ᵥ (A *ᵥ v)‖ ≤ εx * √(sqn u) * √(sqn v))
    (h1c : ∀ v, ‖Bn v‖ ^ 2 ≤ qform Hm v v + εB * sqn v) :
    (∀ u, ‖E u‖ ^ 2 ≤ (1 + εV) * sqn u) ∧
    (∀ u v, ‖⟪E u, Bn v - E (A *ᵥ v)⟫‖ ≤ (εx + Λ * εV) * √(sqn u) * √(sqn v)) ∧
    (∀ v, ‖Bn v - E (A *ᵥ v)‖ ^ 2 ≤
      qform (R + ((εB + 2 * Λ * εx + Λ ^ 2 * εV : ℝ) : 𝕜) • (1 : Matrix n n 𝕜)) v v) := by
  have hA : ∀ v, √(sqn (A *ᵥ v)) ≤ Λ * √(sqn v) := fun v => by
    rw [← Real.sqrt_sq hΛ0, ← Real.sqrt_mul (sq_nonneg _)]
    exact Real.sqrt_le_sqrt (hΛ v)
  have hEE : ∀ u, ‖E u‖ ^ 2 ≤ (1 + εV) * sqn u := by
    intro u
    have hsu := Real.mul_self_sqrt (sqn_nonneg u)
    have hre := (re_le_norm (⟪E u, E u⟫ - star u ⬝ᵥ u)).trans (h1a u u)
    rw [map_sub, re_star_dotProduct_self, inner_self_eq_norm_sq] at hre
    have e : εV * √(sqn u) * √(sqn u) = εV * sqn u := by rw [mul_assoc, hsu]
    rw [e] at hre
    linarith
  refine ⟨hEE, fun u v => ?_, fun v => ?_⟩
  · have e : ⟪E u, Bn v - E (A *ᵥ v)⟫ = (⟪E u, Bn v⟫ - star u ⬝ᵥ (A *ᵥ v)) -
        (⟪E u, E (A *ᵥ v)⟫ - star u ⬝ᵥ (A *ᵥ v)) := by
      rw [inner_sub_right]
      ring
    rw [e]
    calc ‖(⟪E u, Bn v⟫ - star u ⬝ᵥ (A *ᵥ v)) - (⟪E u, E (A *ᵥ v)⟫ - star u ⬝ᵥ (A *ᵥ v))‖
        ≤ ‖⟪E u, Bn v⟫ - star u ⬝ᵥ (A *ᵥ v)‖ + ‖⟪E u, E (A *ᵥ v)⟫ - star u ⬝ᵥ (A *ᵥ v)‖ :=
          norm_sub_le _ _
      _ ≤ εx * √(sqn u) * √(sqn v) + εV * √(sqn u) * √(sqn (A *ᵥ v)) :=
          add_le_add (h1b u v) (h1a u (A *ᵥ v))
      _ ≤ εx * √(sqn u) * √(sqn v) + εV * √(sqn u) * (Λ * √(sqn v)) :=
          add_le_add le_rfl (mul_le_mul_of_nonneg_left (hA v)
            (mul_nonneg hεV (Real.sqrt_nonneg _)))
      _ = (εx + Λ * εV) * √(sqn u) * √(sqn v) := by ring
  · rw [qform_add_smul_one, hR]
    have hexp : ‖Bn v - E (A *ᵥ v)‖ ^ 2 =
        ‖Bn v‖ ^ 2 - 2 * re ⟪Bn v, E (A *ᵥ v)⟫ + ‖E (A *ᵥ v)‖ ^ 2 := norm_sub_sq (𝕜 := 𝕜) _ _
    have hsv := Real.mul_self_sqrt (sqn_nonneg v)
    have hcross : sqn (A *ᵥ v) - εx * Λ * sqn v ≤ re ⟪Bn v, E (A *ᵥ v)⟫ := by
      have h := h1b (A *ᵥ v) v
      rw [← norm_neg, neg_sub] at h
      have hre := (re_le_norm _).trans h
      rw [map_sub, re_star_dotProduct_self] at hre
      rw [inner_re_symm]
      have h3 : εx * √(sqn (A *ᵥ v)) * √(sqn v) ≤ εx * Λ * sqn v :=
        calc εx * √(sqn (A *ᵥ v)) * √(sqn v) ≤ εx * (Λ * √(sqn v)) * √(sqn v) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hA v) hεx)
                (Real.sqrt_nonneg _)
          _ = εx * Λ * (√(sqn v) * √(sqn v)) := by ring
          _ = εx * Λ * sqn v := by rw [hsv]
      linarith
    have hE := hEE (A *ᵥ v)
    have hEA : εV * sqn (A *ᵥ v) ≤ εV * (Λ ^ 2 * sqn v) := mul_le_mul_of_nonneg_left (hΛ v) hεV
    rw [hexp]
    nlinarith [h1c v, hcross, hE, hEA]

/-- **`thm:record:direct-star` (a) from (H1) and (H2).** The modes `ξ` carry `𝐄_ξ` and the
normalized explicit stars `𝐁_ξ` (`𝐁/r` of the paper), with adjoint coefficients `cE`, `cB`;
distinct modes have orthogonal images; (H1) holds on every mode as in `frame_inputs_of_H1`,
with `A(ξ) = ±D` (`D = ε_G Δ^E`, Hermitian, `|Dv| ≤ Λ_D |v|`, `𝐑 = 𝐇 - D^*D`); (H2): with
`α_⋆ = 1 + ε_V + s_⋆` and `β_⋆ = ε_𝐖 + ε_𝐄𝐖²/s_⋆`, `𝐑 + β_⋆ I ≻ 0` and the two tests
`eq:record:schur`, `±D + (g_⋆/α_⋆) I - (𝐑 + β_⋆ I)/g_⋆ ⪰ 0`. Then, with `u_ξ = 𝐄_ξ^* f` and
`v_ξ = 𝐖_ξ^* f = 𝐁_ξ^* f - A(ξ)^* u_ξ`,
`|∑_ξ (u_ξ^* A(ξ) u_ξ + 2 re u_ξ^* v_ξ)| ≤ g_⋆ ‖f‖²`, which is `-g_⋆ r I ⪯ 𝐋 ⪯ g_⋆ r I`
(`⟪f, 𝐋 f⟫ = r ∑_ξ (…)`). -/
theorem routeB_a [DecidableEq n] [DecidableEq Ξ] (E Bn : Ξ → (n → 𝕜) →ₗ[𝕜] H)
    (cE cB : H → Ξ → n → 𝕜) (hcE : ∀ f ξ z, ⟪E ξ z, f⟫ = star z ⬝ᵥ cE f ξ)
    (hcB : ∀ f ξ z, ⟪Bn ξ z, f⟫ = star z ⬝ᵥ cB f ξ)
    (horth : ∀ ξ ξ', ξ ≠ ξ' → ∀ u v u' v', ⟪E ξ u + Bn ξ v, E ξ' u' + Bn ξ' v'⟫ = 0)
    (D : Matrix n n 𝕜) (A : Ξ → Matrix n n 𝕜) (hA : ∀ ξ, A ξ = D ∨ A ξ = -D)
    (Hm R : Matrix n n 𝕜) {εV εx εB Λ s g : ℝ} (hεV : 0 ≤ εV) (hεx : 0 ≤ εx) (hΛ0 : 0 ≤ Λ)
    (hs : 0 < s) (hg : 0 < g) (hΛ : ∀ v, sqn (D *ᵥ v) ≤ Λ ^ 2 * sqn v)
    (hR : ∀ v, qform R v v = qform Hm v v - sqn (D *ᵥ v))
    (h1a : ∀ ξ u w, ‖⟪E ξ u, E ξ w⟫ - star u ⬝ᵥ w‖ ≤ εV * √(sqn u) * √(sqn w))
    (h1b : ∀ ξ u v, ‖⟪E ξ u, Bn ξ v⟫ - star u ⬝ᵥ (A ξ *ᵥ v)‖ ≤ εx * √(sqn u) * √(sqn v))
    (h1c : ∀ ξ v, ‖Bn ξ v‖ ^ 2 ≤ qform Hm v v + εB * sqn v)
    (hPd : (R + ((εB + 2 * Λ * εx + Λ ^ 2 * εV + (εx + Λ * εV) ^ 2 / s : ℝ) : 𝕜) •
      (1 : Matrix n n 𝕜)).PosDef)
    (htestp : (D + ((g / (1 + εV + s) : ℝ) : 𝕜) • (1 : Matrix n n 𝕜) - ((1 / g : ℝ) : 𝕜) •
      (R + ((εB + 2 * Λ * εx + Λ ^ 2 * εV + (εx + Λ * εV) ^ 2 / s : ℝ) : 𝕜) •
        (1 : Matrix n n 𝕜))).PosSemidef)
    (htestm : (-D + ((g / (1 + εV + s) : ℝ) : 𝕜) • (1 : Matrix n n 𝕜) - ((1 / g : ℝ) : 𝕜) •
      (R + ((εB + 2 * Λ * εx + Λ ^ 2 * εV + (εx + Λ * εV) ^ 2 / s : ℝ) : 𝕜) •
        (1 : Matrix n n 𝕜))).PosSemidef) (f : H) :
    |∑ ξ, (qform (A ξ) (cE f ξ) (cE f ξ) +
      2 * re (star (cE f ξ) ⬝ᵥ (cB f ξ - (A ξ)ᴴ *ᵥ cE f ξ)))| ≤ g * ‖f‖ ^ 2 := by
  -- `𝐖_ξ = 𝐁_ξ - 𝐄_ξ A(ξ)`
  set W : Ξ → (n → 𝕜) →ₗ[𝕜] H := fun ξ => Bn ξ - (E ξ).comp (A ξ).mulVecLin with hW
  have hWapp : ∀ ξ v, W ξ v = Bn ξ v - E ξ (A ξ *ᵥ v) := fun ξ v => by
    simp [hW]
  -- the sign of `A(ξ)` does not change `|A(ξ)v|` or `𝐑`
  have hsqnA : ∀ ξ v, sqn (A ξ *ᵥ v) = sqn (D *ᵥ v) := fun ξ v => by
    rcases hA ξ with h | h
    · rw [h]
    · rw [h, Matrix.neg_mulVec]
      simp [sqn]
  have hin : ∀ ξ, (∀ u, ‖E ξ u‖ ^ 2 ≤ (1 + εV) * sqn u) ∧
      (∀ u v, ‖⟪E ξ u, Bn ξ v - E ξ (A ξ *ᵥ v)⟫‖ ≤ (εx + Λ * εV) * √(sqn u) * √(sqn v)) ∧
      (∀ v, ‖Bn ξ v - E ξ (A ξ *ᵥ v)‖ ^ 2 ≤
        qform (R + ((εB + 2 * Λ * εx + Λ ^ 2 * εV : ℝ) : 𝕜) • (1 : Matrix n n 𝕜)) v v) :=
    fun ξ => frame_inputs_of_H1 (E ξ) (Bn ξ) (A ξ) Hm R hεV hεx hΛ0
      (fun v => by rw [hsqnA]; exact hΛ v) (fun v => by rw [hsqnA]; exact hR v)
      (h1a ξ) (h1b ξ) (h1c ξ)
  -- the frame bound
  have horthW : ∀ ξ ξ', ξ ≠ ξ' → ∀ u v u' v', ⟪E ξ u + W ξ v, E ξ' u' + W ξ' v'⟫ = 0 := by
    intro ξ ξ' h u v u' v'
    have e1 : E ξ u + W ξ v = E ξ (u - A ξ *ᵥ v) + Bn ξ v := by
      rw [hWapp, map_sub]
      abel
    have e2 : E ξ' u' + W ξ' v' = E ξ' (u' - A ξ' *ᵥ v') + Bn ξ' v' := by
      rw [hWapp, map_sub]
      abel
    rw [e1, e2]
    exact horth ξ ξ' h _ _ _ _
  have frame := frame_of_modes E W R hs (fun ξ => (hin ξ).1)
    (fun ξ u v => by rw [hWapp]; exact (hin ξ).2.1 u v)
    (fun ξ v => by rw [hWapp]; exact (hin ξ).2.2 v) horthW
  -- the adjoint coefficients of `𝐖`
  have hcW : ∀ f ξ z, ⟪W ξ z, f⟫ = star z ⬝ᵥ (cB f ξ - (A ξ)ᴴ *ᵥ cE f ξ) := by
    intro f ξ z
    rw [hWapp, inner_sub_left, hcB, hcE, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
      dotProduct_sub]
  -- the tests on every mode, for both signs
  have htest : ∀ ξ, (A ξ + ((g / (1 + εV + s) : ℝ) : 𝕜) • (1 : Matrix n n 𝕜) -
      ((1 / g : ℝ) : 𝕜) • (R + ((εB + 2 * Λ * εx + Λ ^ 2 * εV + (εx + Λ * εV) ^ 2 / s : ℝ) : 𝕜) •
        (1 : Matrix n n 𝕜))).PosSemidef := fun ξ => by
    rcases hA ξ with h | h <;> rw [h]
    · exact htestp
    · exact htestm
  have htest' : ∀ ξ, (-A ξ + ((g / (1 + εV + s) : ℝ) : 𝕜) • (1 : Matrix n n 𝕜) -
      ((1 / g : ℝ) : 𝕜) • (R + ((εB + 2 * Λ * εx + Λ ^ 2 * εV + (εx + Λ * εV) ^ 2 / s : ℝ) : 𝕜) •
        (1 : Matrix n n 𝕜))).PosSemidef := fun ξ => by
    rcases hA ξ with h | h <;> rw [h]
    · exact htestm
    · rw [neg_neg]
      exact htestp
  have hα : 0 < 1 + εV + s := by linarith
  have := routeB_two_sided E W cE (fun f ξ => cB f ξ - (A ξ)ᴴ *ᵥ cE f ξ) hcE hcW A _ hPd hα hg
    (fun z1 z2 => by
      have h := frame z1 z2
      simpa only [add_assoc] using h)
    htest htest' f
  exact this

end FromH1

section Criterion

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

local notation "⟪" x ", " y "⟫" => @inner 𝕜 _ _ x y

/-- **`thm:record:direct-star` (c)–(e), abstract form.** Let `Op = K₀/Z₀` with
`Z₀ = ⟪1, K₀ 1⟫ ≥ 1 - ε_Z > 0`, and (b) `K₀ = (1 + h_⋆) ⊗ (1 + h_⋆) + 𝐋 + 𝓡` with
`|⟪f, 𝐋 f⟫| ≤ g_⋆ r ‖f‖²` (from (a)) and `‖𝓡‖ ≤ ρ_𝓡`. Suppose also the two consequences of the
star structure used in (d): `‖P₀ K₀ 1‖ ≤ M_⋆ + N_ns + D_col` and
`|⟪h, (K₀ - 𝐋) h⟫| ≤ (ε_soft + N_ns + D_col) ‖h‖²` for `h ⊥ 1`. Then
(c) `Op ⪰ -(g_⋆ r + ρ_𝓡)/(1 - ε_Z)`; (d) `‖P₀ Op 1‖ ≤ ε_ϱ = (M_⋆ + N_ns + D_col)/(1 - ε_Z)`
and `|⟪h, Op h⟫| ≤ (g_⋆ r + ε_soft + N_ns + D_col)/(1 - ε_Z) ‖h‖²` on `h ⊥ 1`; (e) if that
compression bound `β` is `< 1`, then `Op ⪯ (1 + ε_ϱ²/(1 - β))`. -/
theorem routeB_criterion (T K₀ L Rm : H →ₗ[𝕜] H) (one hstar : H) (hone : ‖one‖ = 1)
    {Z₀ εZ gr ρR M0 Csoft : ℝ} (hεZ : εZ < 1) (hZ : 1 - εZ ≤ Z₀)
    (hT : ∀ x, T x = ((Z₀⁻¹ : ℝ) : 𝕜) • K₀ x) (hsym : T.IsSymmetric)
    (hmean : ⟪one, T one⟫ = 1)
    (hb : ∀ x, K₀ x = ⟪one + hstar, x⟫ • (one + hstar) + L x + Rm x)
    (ha : ∀ f, |re ⟪f, L f⟫| ≤ gr * ‖f‖ ^ 2) (hR : ∀ x, ‖Rm x‖ ≤ ρR * ‖x‖)
    (hP0 : ‖K₀ one - ⟪one, K₀ one⟫ • one‖ ≤ M0)
    (hcomp : ∀ h, ⟪one, h⟫ = 0 → |re ⟪h, K₀ h⟫ - re ⟪h, L h⟫| ≤ Csoft * ‖h‖ ^ 2) :
    (∀ f, -((gr + ρR) / (1 - εZ)) * ‖f‖ ^ 2 ≤ re ⟪f, T f⟫) ∧
    ‖T one - one‖ ≤ M0 / (1 - εZ) ∧
    (∀ h, ⟪one, h⟫ = 0 → |re ⟪h, T h⟫| ≤ (gr + Csoft) / (1 - εZ) * ‖h‖ ^ 2) ∧
    ((gr + Csoft) / (1 - εZ) < 1 → ∀ F, re ⟪F, T F⟫ ≤
      (1 + (M0 / (1 - εZ)) ^ 2 / (1 - (gr + Csoft) / (1 - εZ))) * ‖F‖ ^ 2) := by
  have hd : 0 < 1 - εZ := by linarith
  have hZ0 : 0 < Z₀ := lt_of_lt_of_le hd hZ
  have hQ : ∀ f, re ⟪f, T f⟫ = Z₀⁻¹ * re ⟪f, K₀ f⟫ := fun f => by
    rw [hT, inner_smul_right, RCLike.re_ofReal_mul]
  have hinvle : Z₀⁻¹ ≤ (1 - εZ)⁻¹ := inv_anti₀ hd hZ
  have hR0 : 0 ≤ ρR := by
    have h1 := hR 0
    have h2 := hR one
    rw [hone, mul_one] at h2
    exact (norm_nonneg _).trans h2
  -- (c)
  have hc : ∀ f, -((gr + ρR) / (1 - εZ)) * ‖f‖ ^ 2 ≤ re ⟪f, T f⟫ := by
    intro f
    have hrank : 0 ≤ re ⟪f, ⟪one + hstar, f⟫ • (one + hstar)⟫ := by
      rw [inner_smul_right, ← inner_conj_symm f (one + hstar), RCLike.mul_conj]
      norm_cast
      positivity
    have hRf : -(ρR * ‖f‖ ^ 2) ≤ re ⟪f, Rm f⟫ := by
      have := (abs_re_le_norm ⟪f, Rm f⟫).trans ((norm_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_left (hR f) (norm_nonneg _)))
      have := neg_le_of_abs_le this
      nlinarith [norm_nonneg f]
    have hLf := neg_le_of_abs_le (ha f)
    have hK : -((gr + ρR) * ‖f‖ ^ 2) ≤ re ⟪f, K₀ f⟫ := by
      rw [hb, inner_add_right, inner_add_right, map_add, map_add]
      linarith
    rw [hQ]
    have h0 : 0 ≤ (gr + ρR) * ‖f‖ ^ 2 + re ⟪f, K₀ f⟫ := by linarith
    have hgr : 0 ≤ gr := by
      have := ha 0
      have h2 := ha one
      rw [hone, one_pow, mul_one] at h2
      exact (abs_nonneg _).trans h2
    have hpos : 0 ≤ (gr + ρR) * ‖f‖ ^ 2 := mul_nonneg (by linarith) (sq_nonneg _)
    calc -((gr + ρR) / (1 - εZ)) * ‖f‖ ^ 2 = -((1 - εZ)⁻¹ * ((gr + ρR) * ‖f‖ ^ 2)) := by ring
      _ ≤ -(Z₀⁻¹ * ((gr + ρR) * ‖f‖ ^ 2)) := by
          have := mul_le_mul_of_nonneg_right hinvle hpos
          linarith
      _ ≤ Z₀⁻¹ * re ⟪f, K₀ f⟫ := by
          have := mul_le_mul_of_nonneg_left hK (inv_nonneg.mpr hZ0.le)
          linarith
  -- (d), first part
  have hone' : ⟪one, one⟫ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hone]
    simp
  have hd1 : ‖T one - one‖ ≤ M0 / (1 - εZ) := by
    have e : T one - one = ((Z₀⁻¹ : ℝ) : 𝕜) • (K₀ one - ⟪one, K₀ one⟫ • one) := by
      have hTone : ⟪one, K₀ one⟫ = (Z₀ : 𝕜) := by
        have h1 : ((Z₀⁻¹ : ℝ) : 𝕜) * ⟪one, K₀ one⟫ = 1 := by
          rw [← inner_smul_right, ← hT]
          exact hmean
        calc ⟪one, K₀ one⟫ = (Z₀ : 𝕜) * (((Z₀⁻¹ : ℝ) : 𝕜) * ⟪one, K₀ one⟫) := by
              rw [← mul_assoc, ← RCLike.ofReal_mul, mul_inv_cancel₀ hZ0.ne', RCLike.ofReal_one,
                one_mul]
          _ = (Z₀ : 𝕜) := by rw [h1, mul_one]
      rw [smul_sub, ← hT, hTone, smul_smul, ← RCLike.ofReal_mul, inv_mul_cancel₀ hZ0.ne',
        RCLike.ofReal_one, one_smul]
    rw [e, norm_smul, RCLike.norm_ofReal, abs_of_pos (inv_pos.mpr hZ0)]
    have hM0 : 0 ≤ M0 := (norm_nonneg _).trans hP0
    calc Z₀⁻¹ * ‖K₀ one - ⟪one, K₀ one⟫ • one‖ ≤ (1 - εZ)⁻¹ * M0 :=
          mul_le_mul hinvle hP0 (norm_nonneg _) (inv_nonneg.mpr hd.le)
      _ = M0 / (1 - εZ) := by ring
  -- (d), second part
  have hd2 : ∀ h, ⟪one, h⟫ = 0 → |re ⟪h, T h⟫| ≤ (gr + Csoft) / (1 - εZ) * ‖h‖ ^ 2 := by
    intro h h1
    have hK : |re ⟪h, K₀ h⟫| ≤ (gr + Csoft) * ‖h‖ ^ 2 := by
      have e1 := hcomp h h1
      have e2 := ha h
      calc |re ⟪h, K₀ h⟫| = |(re ⟪h, K₀ h⟫ - re ⟪h, L h⟫) + re ⟪h, L h⟫| := by ring_nf
        _ ≤ |re ⟪h, K₀ h⟫ - re ⟪h, L h⟫| + |re ⟪h, L h⟫| := abs_add_le _ _
        _ ≤ Csoft * ‖h‖ ^ 2 + gr * ‖h‖ ^ 2 := add_le_add e1 e2
        _ = (gr + Csoft) * ‖h‖ ^ 2 := by ring
    rw [hQ, abs_mul, abs_of_pos (inv_pos.mpr hZ0)]
    have hpos : 0 ≤ (gr + Csoft) * ‖h‖ ^ 2 := (abs_nonneg _).trans hK
    calc Z₀⁻¹ * |re ⟪h, K₀ h⟫| ≤ Z₀⁻¹ * ((gr + Csoft) * ‖h‖ ^ 2) :=
          mul_le_mul_of_nonneg_left hK (inv_nonneg.mpr hZ0.le)
      _ ≤ (1 - εZ)⁻¹ * ((gr + Csoft) * ‖h‖ ^ 2) := mul_le_mul_of_nonneg_right hinvle hpos
      _ = (gr + Csoft) / (1 - εZ) * ‖h‖ ^ 2 := by ring
  -- (e)
  refine ⟨hc, hd1, hd2, fun hβ F => ?_⟩
  exact upper_of_compression hsym hone hmean hd1 hβ hd2 F

end Criterion

section DecompositionB

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

local notation "⟪" x ", " y "⟫" => @inner 𝕜 _ _ x y

/-- `‖y - ⟪1, y⟫ 1‖² = ‖y‖² - |⟪1, y⟫|²` for a unit vector `1`. -/
theorem norm_sub_inner_smul_sq (one y : H) (hone : ‖one‖ = 1) :
    ‖y - ⟪one, y⟫ • one‖ ^ 2 = ‖y‖ ^ 2 - ‖⟪one, y⟫‖ ^ 2 := by
  have h1 : ⟪y, one⟫ = conj ⟪one, y⟫ := (inner_conj_symm y one).symm
  have h2 : re (⟪one, y⟫ * conj ⟪one, y⟫) = ‖⟪one, y⟫‖ ^ 2 := by
    rw [RCLike.mul_conj, ← RCLike.ofReal_pow, RCLike.ofReal_re]
  rw [norm_sub_sq (𝕜 := 𝕜), inner_smul_right, h1, h2, norm_smul, hone, mul_one]
  ring

/-- **`thm:record:direct-star` (b) ⟹ the inputs of (c)–(e).** Here (b) is in the explicit form of
the proof, `K₀ = (1 + h_⋆) ⊗ (1 + h_⋆) + 𝐋 + 𝓡` with
`𝓡 = Soft - h_⋆ ⊗ h_⋆ + T_ns - T_coll`, `Soft = (𝐒 - 𝐁)𝐄^* + 𝐄(𝐒 - 𝐁)^*`, together with the facts
of (c) and (d): `𝐋 1 = 0` and `Soft 1 = 0` (`𝐄^* 1 = 0`, `(𝐒 - 𝐁)^* 1 = 0`), `‖Soft‖ ≤ ε_soft`,
`‖T_ns‖ ≤ N_ns`, `‖T_coll‖ ≤ D_col`, `‖h_⋆ - E h_⋆‖ ≤ M_⋆`, `|E h_⋆| ≤ z_⋆`, `2|E h_⋆| ≤ Z_⋆`,
`ε_Z = Z_⋆ + N_ns + D_col < 1`. Then (c) `|Z₀ - 1| ≤ ε_Z`, and with (a) in the form
`|⟪f, 𝐋 f⟫| ≤ g_⋆ r ‖f‖²`: (c) `Op ⪰ -(g_⋆ r + ρ_𝓡)/(1 - ε_Z)` with
`ρ_𝓡 = ε_soft + M_⋆² + z_⋆² + N_ns + D_col`; (d) `‖P₀ Op 1‖ ≤ (M_⋆ + N_ns + D_col)/(1 - ε_Z)`
and `‖P₀ Op P₀‖ ≤ (g_⋆ r + ε_soft + N_ns + D_col)/(1 - ε_Z)`; (e) the upper bound. Both are at
most `g_root r` of the theorem. -/
theorem routeB_cde (T K₀ L Soft Tns Tcoll : H →ₗ[𝕜] H) (one hs : H) (hone : ‖one‖ = 1)
    {Z₀ gr εsoft Mstar zstar Zstar Nns Dcol : ℝ}
    (hT : ∀ x, T x = ((Z₀⁻¹ : ℝ) : 𝕜) • K₀ x) (hZ₀ : ⟪one, K₀ one⟫ = (Z₀ : 𝕜))
    (hsym : T.IsSymmetric)
    (hb : ∀ x, K₀ x = ⟪one + hs, x⟫ • (one + hs) + L x +
      (Soft x - ⟪hs, x⟫ • hs + (Tns x - Tcoll x)))
    (ha : ∀ f, |re ⟪f, L f⟫| ≤ gr * ‖f‖ ^ 2) (hL1 : L one = 0)
    (hSoft1 : Soft one = 0) (hSoft : ∀ x, ‖Soft x‖ ≤ εsoft * ‖x‖)
    (hns : ∀ x, ‖Tns x‖ ≤ Nns * ‖x‖) (hcoll : ∀ x, ‖Tcoll x‖ ≤ Dcol * ‖x‖)
    (hM : ‖hs - ⟪one, hs⟫ • one‖ ≤ Mstar) (hz : ‖⟪one, hs⟫‖ ≤ zstar)
    (hZs : 2 * ‖⟪one, hs⟫‖ ≤ Zstar) (hεZ : Zstar + Nns + Dcol < 1) :
    |Z₀ - 1| ≤ Zstar + Nns + Dcol ∧
    (∀ f, -((gr + (εsoft + Mstar ^ 2 + zstar ^ 2 + (Nns + Dcol))) /
      (1 - (Zstar + Nns + Dcol))) * ‖f‖ ^ 2 ≤ re ⟪f, T f⟫) ∧
    ‖T one - one‖ ≤ (Mstar + (Nns + Dcol)) / (1 - (Zstar + Nns + Dcol)) ∧
    (∀ h, ⟪one, h⟫ = 0 → |re ⟪h, T h⟫| ≤
      (gr + (εsoft + (Nns + Dcol))) / (1 - (Zstar + Nns + Dcol)) * ‖h‖ ^ 2) ∧
    ((gr + (εsoft + (Nns + Dcol))) / (1 - (Zstar + Nns + Dcol)) < 1 → ∀ F, re ⟪F, T F⟫ ≤
      (1 + ((Mstar + (Nns + Dcol)) / (1 - (Zstar + Nns + Dcol))) ^ 2 /
        (1 - (gr + (εsoft + (Nns + Dcol))) / (1 - (Zstar + Nns + Dcol)))) * ‖F‖ ^ 2) := by
  set m := ⟪one, hs⟫ with hm
  have hone' : ⟪one, one⟫ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hone]
    simp
  have hTD : ∀ x, ‖Tns x - Tcoll x‖ ≤ (Nns + Dcol) * ‖x‖ := fun x => by
    have := norm_sub_le (Tns x) (Tcoll x)
    have h1 := hns x
    have h2 := hcoll x
    nlinarith
  have hsone : ⟪hs, one⟫ = conj m := by rw [hm, inner_conj_symm]
  -- `Z₀ - 1 = 2 re E h_⋆ + ⟪1, (T_ns - T_coll) 1⟫`
  have hZeq : (Z₀ : 𝕜) - 1 = m + conj m + ⟪one, Tns one - Tcoll one⟫ := by
    rw [← hZ₀, hb, hL1, hSoft1]
    simp only [inner_add_right, inner_sub_right, inner_smul_right, inner_zero_right,
      inner_add_left, hone', hsone, ← hm]
    ring
  have hTD1 : ‖Tns one - Tcoll one‖ ≤ Nns + Dcol := by
    have h := hTD one
    rwa [hone, mul_one] at h
  have hD1 : ‖⟪one, Tns one - Tcoll one⟫‖ ≤ Nns + Dcol := by
    have h := (norm_inner_le_norm (𝕜 := 𝕜) one (Tns one - Tcoll one)).trans
      (mul_le_mul_of_nonneg_left hTD1 (norm_nonneg _))
    rwa [hone, one_mul] at h
  have hZ1 : |Z₀ - 1| ≤ Zstar + Nns + Dcol := by
    have h : ‖((Z₀ - 1 : ℝ) : 𝕜)‖ ≤ Zstar + Nns + Dcol := by
      push_cast
      rw [hZeq]
      calc ‖m + conj m + ⟪one, Tns one - Tcoll one⟫‖
          ≤ ‖m‖ + ‖conj m‖ + ‖⟪one, Tns one - Tcoll one⟫‖ :=
            (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
        _ ≤ Zstar + Nns + Dcol := by rw [RCLike.norm_conj]; linarith
    rwa [RCLike.norm_ofReal] at h
  have hZlow : 1 - (Zstar + Nns + Dcol) ≤ Z₀ := by linarith [(abs_le.mp hZ1).1]
  have hZ0 : 0 < Z₀ := by linarith
  have hmean : ⟪one, T one⟫ = 1 := by
    rw [hT, inner_smul_right, hZ₀, ← RCLike.ofReal_mul, inv_mul_cancel₀ hZ0.ne',
      RCLike.ofReal_one]
  -- the remainder as a linear map
  set Rm : H →ₗ[𝕜] H := Soft - (innerₛₗ 𝕜 hs).smulRight hs + (Tns - Tcoll) with hRm
  have hRmapp : ∀ x, Rm x = Soft x - ⟪hs, x⟫ • hs + (Tns x - Tcoll x) := fun x => by
    simp [hRm, innerₛₗ_apply_apply]
  have hb' : ∀ x, K₀ x = ⟪one + hs, x⟫ • (one + hs) + L x + Rm x := fun x => by
    rw [hRmapp, hb]
  -- `‖h_⋆‖² ≤ M_⋆² + z_⋆²`
  have hhs : ‖hs‖ ^ 2 ≤ Mstar ^ 2 + zstar ^ 2 := by
    have h := norm_sub_inner_smul_sq (𝕜 := 𝕜) one hs hone
    rw [← hm] at h
    have h1 : ‖hs - m • one‖ ^ 2 ≤ Mstar ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) hM 2
    have h2 : ‖m‖ ^ 2 ≤ zstar ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hz 2
    linarith
  have hR : ∀ x, ‖Rm x‖ ≤ (εsoft + Mstar ^ 2 + zstar ^ 2 + (Nns + Dcol)) * ‖x‖ := by
    intro x
    rw [hRmapp]
    have h1 : ‖⟪hs, x⟫ • hs‖ ≤ (Mstar ^ 2 + zstar ^ 2) * ‖x‖ := by
      rw [norm_smul]
      calc ‖⟪hs, x⟫‖ * ‖hs‖ ≤ (‖hs‖ * ‖x‖) * ‖hs‖ :=
            mul_le_mul_of_nonneg_right (norm_inner_le_norm (𝕜 := 𝕜) _ _) (norm_nonneg _)
        _ = ‖hs‖ ^ 2 * ‖x‖ := by ring
        _ ≤ (Mstar ^ 2 + zstar ^ 2) * ‖x‖ := mul_le_mul_of_nonneg_right hhs (norm_nonneg _)
    calc ‖Soft x - ⟪hs, x⟫ • hs + (Tns x - Tcoll x)‖
        ≤ ‖Soft x‖ + ‖⟪hs, x⟫ • hs‖ + ‖Tns x - Tcoll x‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_sub_le _ _) le_rfl)
      _ ≤ εsoft * ‖x‖ + (Mstar ^ 2 + zstar ^ 2) * ‖x‖ + (Nns + Dcol) * ‖x‖ :=
          add_le_add (add_le_add (hSoft x) h1) (hTD x)
      _ = (εsoft + Mstar ^ 2 + zstar ^ 2 + (Nns + Dcol)) * ‖x‖ := by ring
  -- (d), the vector `P₀ K₀ 1`
  have hP0 : ‖K₀ one - ⟪one, K₀ one⟫ • one‖ ≤ Mstar + (Nns + Dcol) := by
    obtain ⟨Y, hY⟩ : ∃ Y, Y = Tns one - Tcoll one := ⟨_, rfl⟩
    have hK1 : K₀ one = ((1 : 𝕜) + conj m) • one + hs + Y := by
      rw [hb, hL1, hSoft1, inner_add_left, hone', hsone, hY]
      simp only [smul_add, add_smul, one_smul, sub_eq_add_neg, zero_add]
      abel
    have hZ' : ⟪one, K₀ one⟫ = 1 + m + conj m + ⟪one, Y⟫ := by
      rw [hZ₀, hY]
      linear_combination hZeq
    have e : K₀ one - ⟪one, K₀ one⟫ • one = (hs - m • one) + (Y - ⟪one, Y⟫ • one) := by
      rw [hZ', hK1]
      simp only [add_smul, one_smul, sub_eq_add_neg, neg_add]
      abel
    rw [e]
    have hY1 : ‖Y - ⟪one, Y⟫ • one‖ ≤ ‖Y‖ := by
      have h := norm_sub_inner_smul_sq (𝕜 := 𝕜) one Y hone
      have : ‖Y - ⟪one, Y⟫ • one‖ ^ 2 ≤ ‖Y‖ ^ 2 := by
        rw [h]
        nlinarith [sq_nonneg ‖⟪one, Y⟫‖]
      exact (abs_le_of_sq_le_sq' this (norm_nonneg _)).2
    calc ‖(hs - m • one) + (Y - ⟪one, Y⟫ • one)‖
        ≤ ‖hs - m • one‖ + ‖Y - ⟪one, Y⟫ • one‖ := norm_add_le _ _
      _ ≤ Mstar + (Nns + Dcol) := add_le_add hM (hY1.trans (hY ▸ hTD1))
  -- (d), the compression
  have hcomp : ∀ h, ⟪one, h⟫ = 0 →
      |re ⟪h, K₀ h⟫ - re ⟪h, L h⟫| ≤ (εsoft + (Nns + Dcol)) * ‖h‖ ^ 2 := by
    intro h h1
    have h1' : ⟪h, one⟫ = 0 := by rw [← inner_conj_symm, h1, map_zero]
    have e : ⟪h, K₀ h⟫ - ⟪h, L h⟫ = ⟪h, Soft h⟫ + ⟪h, Tns h - Tcoll h⟫ := by
      rw [hb]
      simp only [inner_add_right, inner_sub_right, inner_smul_right, inner_add_left, h1, h1']
      ring
    rw [← map_sub, e]
    calc |re (⟪h, Soft h⟫ + ⟪h, Tns h - Tcoll h⟫)| ≤ ‖⟪h, Soft h⟫ + ⟪h, Tns h - Tcoll h⟫‖ :=
          abs_re_le_norm _
      _ ≤ ‖h‖ * ‖Soft h‖ + ‖h‖ * ‖Tns h - Tcoll h‖ :=
          (norm_add_le _ _).trans (add_le_add (norm_inner_le_norm (𝕜 := 𝕜) _ _)
            (norm_inner_le_norm (𝕜 := 𝕜) _ _))
      _ ≤ ‖h‖ * (εsoft * ‖h‖) + ‖h‖ * ((Nns + Dcol) * ‖h‖) :=
          add_le_add (mul_le_mul_of_nonneg_left (hSoft h) (norm_nonneg _))
            (mul_le_mul_of_nonneg_left (hTD h) (norm_nonneg _))
      _ = (εsoft + (Nns + Dcol)) * ‖h‖ ^ 2 := by ring
  exact ⟨hZ1, routeB_criterion T K₀ L Rm one hs hone hεZ hZlow hT hsym hmean hb' ha hR hP0 hcomp⟩

end DecompositionB

section DirectStar

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] {Ξ : Type*} [Fintype Ξ]

local notation "⟪" x ", " y "⟫" => @inner 𝕜 _ _ x y

/-- **`thm:record:direct-star`, (a) and (c)–(e) together.** The hypotheses of `routeB_a` ((H1)
on the modes and (H2)), the identity `⟪f, 𝐋 f⟫ = r ∑_ξ (u_ξ^* A(ξ) u_ξ + 2 re u_ξ^* v_ξ)` that
defines `𝐋` through the modes, and the decomposition (b) with its two consequences (as in
`routeB_criterion`). With `ρ_𝓡 = N_ns + D_col + M_⋆² + z_⋆² + ε_soft` and
`C_soft = ε_soft + N_ns + D_col` the bounds are those of the theorem with `g_root`. -/
theorem direct_star [DecidableEq n] [DecidableEq Ξ] (T K₀ L Rm : H →ₗ[𝕜] H) (one hstar : H)
    (hone : ‖one‖ = 1) (E Bn : Ξ → (n → 𝕜) →ₗ[𝕜] H)
    (cE cB : H → Ξ → n → 𝕜) (hcE : ∀ f ξ z, ⟪E ξ z, f⟫ = star z ⬝ᵥ cE f ξ)
    (hcB : ∀ f ξ z, ⟪Bn ξ z, f⟫ = star z ⬝ᵥ cB f ξ)
    (horth : ∀ ξ ξ', ξ ≠ ξ' → ∀ u v u' v', ⟪E ξ u + Bn ξ v, E ξ' u' + Bn ξ' v'⟫ = 0)
    (D : Matrix n n 𝕜) (A : Ξ → Matrix n n 𝕜) (hA : ∀ ξ, A ξ = D ∨ A ξ = -D)
    (Hm R : Matrix n n 𝕜) {εV εx εB Λ s g r : ℝ} (hεV : 0 ≤ εV) (hεx : 0 ≤ εx) (hΛ0 : 0 ≤ Λ)
    (hs : 0 < s) (hg : 0 < g) (hr : 0 ≤ r) (hΛ : ∀ v, sqn (D *ᵥ v) ≤ Λ ^ 2 * sqn v)
    (hR : ∀ v, qform R v v = qform Hm v v - sqn (D *ᵥ v))
    (h1a : ∀ ξ u w, ‖⟪E ξ u, E ξ w⟫ - star u ⬝ᵥ w‖ ≤ εV * √(sqn u) * √(sqn w))
    (h1b : ∀ ξ u v, ‖⟪E ξ u, Bn ξ v⟫ - star u ⬝ᵥ (A ξ *ᵥ v)‖ ≤ εx * √(sqn u) * √(sqn v))
    (h1c : ∀ ξ v, ‖Bn ξ v‖ ^ 2 ≤ qform Hm v v + εB * sqn v)
    (hPd : (R + ((εB + 2 * Λ * εx + Λ ^ 2 * εV + (εx + Λ * εV) ^ 2 / s : ℝ) : 𝕜) •
      (1 : Matrix n n 𝕜)).PosDef)
    (htestp : (D + ((g / (1 + εV + s) : ℝ) : 𝕜) • (1 : Matrix n n 𝕜) - ((1 / g : ℝ) : 𝕜) •
      (R + ((εB + 2 * Λ * εx + Λ ^ 2 * εV + (εx + Λ * εV) ^ 2 / s : ℝ) : 𝕜) •
        (1 : Matrix n n 𝕜))).PosSemidef)
    (htestm : (-D + ((g / (1 + εV + s) : ℝ) : 𝕜) • (1 : Matrix n n 𝕜) - ((1 / g : ℝ) : 𝕜) •
      (R + ((εB + 2 * Λ * εx + Λ ^ 2 * εV + (εx + Λ * εV) ^ 2 / s : ℝ) : 𝕜) •
        (1 : Matrix n n 𝕜))).PosSemidef)
    (hL : ∀ f, re ⟪f, L f⟫ = r * ∑ ξ, (qform (A ξ) (cE f ξ) (cE f ξ) +
      2 * re (star (cE f ξ) ⬝ᵥ (cB f ξ - (A ξ)ᴴ *ᵥ cE f ξ))))
    {Z₀ εZ ρR M0 Csoft : ℝ} (hεZ : εZ < 1) (hZ : 1 - εZ ≤ Z₀)
    (hT : ∀ x, T x = ((Z₀⁻¹ : ℝ) : 𝕜) • K₀ x) (hsym : T.IsSymmetric)
    (hmean : ⟪one, T one⟫ = 1)
    (hb : ∀ x, K₀ x = ⟪one + hstar, x⟫ • (one + hstar) + L x + Rm x)
    (hRm : ∀ x, ‖Rm x‖ ≤ ρR * ‖x‖) (hP0 : ‖K₀ one - ⟪one, K₀ one⟫ • one‖ ≤ M0)
    (hcomp : ∀ h, ⟪one, h⟫ = 0 → |re ⟪h, K₀ h⟫ - re ⟪h, L h⟫| ≤ Csoft * ‖h‖ ^ 2) :
    (∀ f, |re ⟪f, L f⟫| ≤ g * r * ‖f‖ ^ 2) ∧
    (∀ f, -((g * r + ρR) / (1 - εZ)) * ‖f‖ ^ 2 ≤ re ⟪f, T f⟫) ∧
    ‖T one - one‖ ≤ M0 / (1 - εZ) ∧
    (∀ h, ⟪one, h⟫ = 0 → |re ⟪h, T h⟫| ≤ (g * r + Csoft) / (1 - εZ) * ‖h‖ ^ 2) ∧
    ((g * r + Csoft) / (1 - εZ) < 1 → ∀ F, re ⟪F, T F⟫ ≤
      (1 + (M0 / (1 - εZ)) ^ 2 / (1 - (g * r + Csoft) / (1 - εZ))) * ‖F‖ ^ 2) := by
  have ha : ∀ f, |re ⟪f, L f⟫| ≤ g * r * ‖f‖ ^ 2 := by
    intro f
    have h := routeB_a E Bn cE cB hcE hcB horth D A hA Hm R hεV hεx hΛ0 hs hg hΛ hR h1a h1b h1c
      hPd htestp htestm f
    rw [hL, abs_mul, abs_of_nonneg hr]
    calc r * |∑ ξ, (qform (A ξ) (cE f ξ) (cE f ξ) +
          2 * re (star (cE f ξ) ⬝ᵥ (cB f ξ - (A ξ)ᴴ *ᵥ cE f ξ)))|
        ≤ r * (g * ‖f‖ ^ 2) := mul_le_mul_of_nonneg_left h hr
      _ = g * r * ‖f‖ ^ 2 := by ring
  exact ⟨ha, routeB_criterion T K₀ L Rm one hstar hone hεZ hZ hT hsym hmean hb ha hRm hP0 hcomp⟩

/-- **`thm:record:direct-star`, (a)–(e) with the paper's constants.** (H1) and (H2) as in
`routeB_a`, the identity defining `𝐋` through the modes, and (b) in the explicit form of
`routeB_cde`. Then `|Z₀ - 1| ≤ ε_Z`, `-g_⋆ r ⪯ 𝐋 ⪯ g_⋆ r`, and (c)–(e) with
`ρ_𝓡 = ε_soft + M_⋆² + z_⋆² + N_ns + D_col` (so the lower bound is `-g_root r`), `ε_ϱ` and the
compression bound `(g_⋆ r + ε_soft + N_ns + D_col)/(1 - ε_Z) ≤ g_root r`. -/
theorem direct_star_explicit [DecidableEq n] [DecidableEq Ξ] (T K₀ L Soft Tns Tcoll : H →ₗ[𝕜] H)
    (one hs : H) (hone : ‖one‖ = 1) (E Bn : Ξ → (n → 𝕜) →ₗ[𝕜] H)
    (cE cB : H → Ξ → n → 𝕜) (hcE : ∀ f ξ z, ⟪E ξ z, f⟫ = star z ⬝ᵥ cE f ξ)
    (hcB : ∀ f ξ z, ⟪Bn ξ z, f⟫ = star z ⬝ᵥ cB f ξ)
    (horth : ∀ ξ ξ', ξ ≠ ξ' → ∀ u v u' v', ⟪E ξ u + Bn ξ v, E ξ' u' + Bn ξ' v'⟫ = 0)
    (D : Matrix n n 𝕜) (A : Ξ → Matrix n n 𝕜) (hA : ∀ ξ, A ξ = D ∨ A ξ = -D)
    (Hm R : Matrix n n 𝕜) {εV εx εB Λ s g r : ℝ} (hεV : 0 ≤ εV) (hεx : 0 ≤ εx) (hΛ0 : 0 ≤ Λ)
    (hs0 : 0 < s) (hg : 0 < g) (hr : 0 ≤ r) (hΛ : ∀ v, sqn (D *ᵥ v) ≤ Λ ^ 2 * sqn v)
    (hR : ∀ v, qform R v v = qform Hm v v - sqn (D *ᵥ v))
    (h1a : ∀ ξ u w, ‖⟪E ξ u, E ξ w⟫ - star u ⬝ᵥ w‖ ≤ εV * √(sqn u) * √(sqn w))
    (h1b : ∀ ξ u v, ‖⟪E ξ u, Bn ξ v⟫ - star u ⬝ᵥ (A ξ *ᵥ v)‖ ≤ εx * √(sqn u) * √(sqn v))
    (h1c : ∀ ξ v, ‖Bn ξ v‖ ^ 2 ≤ qform Hm v v + εB * sqn v)
    (hPd : (R + ((εB + 2 * Λ * εx + Λ ^ 2 * εV + (εx + Λ * εV) ^ 2 / s : ℝ) : 𝕜) •
      (1 : Matrix n n 𝕜)).PosDef)
    (htestp : (D + ((g / (1 + εV + s) : ℝ) : 𝕜) • (1 : Matrix n n 𝕜) - ((1 / g : ℝ) : 𝕜) •
      (R + ((εB + 2 * Λ * εx + Λ ^ 2 * εV + (εx + Λ * εV) ^ 2 / s : ℝ) : 𝕜) •
        (1 : Matrix n n 𝕜))).PosSemidef)
    (htestm : (-D + ((g / (1 + εV + s) : ℝ) : 𝕜) • (1 : Matrix n n 𝕜) - ((1 / g : ℝ) : 𝕜) •
      (R + ((εB + 2 * Λ * εx + Λ ^ 2 * εV + (εx + Λ * εV) ^ 2 / s : ℝ) : 𝕜) •
        (1 : Matrix n n 𝕜))).PosSemidef)
    (hL : ∀ f, re ⟪f, L f⟫ = r * ∑ ξ, (qform (A ξ) (cE f ξ) (cE f ξ) +
      2 * re (star (cE f ξ) ⬝ᵥ (cB f ξ - (A ξ)ᴴ *ᵥ cE f ξ))))
    {Z₀ εsoft Mstar zstar Zstar Nns Dcol : ℝ}
    (hT : ∀ x, T x = ((Z₀⁻¹ : ℝ) : 𝕜) • K₀ x) (hZ₀ : ⟪one, K₀ one⟫ = (Z₀ : 𝕜))
    (hsym : T.IsSymmetric)
    (hb : ∀ x, K₀ x = ⟪one + hs, x⟫ • (one + hs) + L x +
      (Soft x - ⟪hs, x⟫ • hs + (Tns x - Tcoll x)))
    (hL1 : L one = 0) (hSoft1 : Soft one = 0) (hSoft : ∀ x, ‖Soft x‖ ≤ εsoft * ‖x‖)
    (hns : ∀ x, ‖Tns x‖ ≤ Nns * ‖x‖) (hcoll : ∀ x, ‖Tcoll x‖ ≤ Dcol * ‖x‖)
    (hM : ‖hs - ⟪one, hs⟫ • one‖ ≤ Mstar) (hz : ‖⟪one, hs⟫‖ ≤ zstar)
    (hZs : 2 * ‖⟪one, hs⟫‖ ≤ Zstar) (hεZ : Zstar + Nns + Dcol < 1) :
    (∀ f, |re ⟪f, L f⟫| ≤ g * r * ‖f‖ ^ 2) ∧
    |Z₀ - 1| ≤ Zstar + Nns + Dcol ∧
    (∀ f, -((g * r + (εsoft + Mstar ^ 2 + zstar ^ 2 + (Nns + Dcol))) /
      (1 - (Zstar + Nns + Dcol))) * ‖f‖ ^ 2 ≤ re ⟪f, T f⟫) ∧
    ‖T one - one‖ ≤ (Mstar + (Nns + Dcol)) / (1 - (Zstar + Nns + Dcol)) ∧
    (∀ h, ⟪one, h⟫ = 0 → |re ⟪h, T h⟫| ≤
      (g * r + (εsoft + (Nns + Dcol))) / (1 - (Zstar + Nns + Dcol)) * ‖h‖ ^ 2) ∧
    ((g * r + (εsoft + (Nns + Dcol))) / (1 - (Zstar + Nns + Dcol)) < 1 → ∀ F, re ⟪F, T F⟫ ≤
      (1 + ((Mstar + (Nns + Dcol)) / (1 - (Zstar + Nns + Dcol))) ^ 2 /
        (1 - (g * r + (εsoft + (Nns + Dcol))) / (1 - (Zstar + Nns + Dcol)))) * ‖F‖ ^ 2) := by
  have ha : ∀ f, |re ⟪f, L f⟫| ≤ g * r * ‖f‖ ^ 2 := by
    intro f
    have h := routeB_a E Bn cE cB hcE hcB horth D A hA Hm R hεV hεx hΛ0 hs0 hg hΛ hR h1a h1b h1c
      hPd htestp htestm f
    rw [hL, abs_mul, abs_of_nonneg hr]
    calc r * |∑ ξ, (qform (A ξ) (cE f ξ) (cE f ξ) +
          2 * re (star (cE f ξ) ⬝ᵥ (cB f ξ - (A ξ)ᴴ *ᵥ cE f ξ)))|
        ≤ r * (g * ‖f‖ ^ 2) := mul_le_mul_of_nonneg_left h hr
      _ = g * r * ‖f‖ ^ 2 := by ring
  exact ⟨ha, routeB_cde T K₀ L Soft Tns Tcoll one hs hone hT hZ₀ hsym hb ha hL1 hSoft1 hSoft
    hns hcoll hM hz hZs hεZ⟩

end DirectStar

end Sarkozy.Spectral
