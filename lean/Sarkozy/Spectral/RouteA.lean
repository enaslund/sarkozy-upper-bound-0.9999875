module

public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Analysis.InnerProductSpace.Symmetric

/-!
# Route A of the spectral criterion: the abstract argument

`thm:spectral-criterion` (`paper/sections/14_spectral.tex`, Route A), the Hilbert-space part of
its proof. The cut operator `Op` is an abstract symmetric operator `T` on a finite-dimensional
inner product space `H` over `𝕜 = ℝ` or `ℂ` (the complexification of `L²(μ)` in the paper),
with a unit vector `one` (the constants). The inputs of the earlier lemmas enter as the
hypotheses of `RouteAInputs`:
* `prop:spec2:mucentre` (a), (c3), (c4): `⟪1, Op 1⟫ = 1`, `⟪1, Op v⟫ = 0` on the degree-one
  space `V`, `‖ϱ - 1‖ ≤ ε_ϱ` with `ϱ = Op 1`, and `|⟪h, Op h⟫| ≤ a_⊥ ‖h‖²` on
  `H_⊥ = (ℂ1 ⊕ V)^⊥` (`a_⊥ = R_Z (N_ns + D_col)`);
* `lem:spec:degone` (a)–(c): `Q(F_V)` is `r ∑_ξ ĝ(ξ)^* A(ξ) ĝ(ξ)` up to `± r η_Q ‖g‖²`, and
  `‖F_V‖² ≥ (1 - ε_V) ‖g‖²`, for Fourier coefficients `ĝ = coef F_V` indexed by the modes `Ξ`;
* `cor:spec2:coupling` (complex form `eq:spec:coupling`): every `F_V` splits as
  `F_{V,+} + F_{V,-}` along the two translation sectors `Ξ_±`, the leakage
  `(I - Π_V) Op F_{V,±}` lies in the sector `S_±`, and
  `‖(I - Π_V) Op F_{V,±}‖² ≤ r² ∑_{ξ ∈ Ξ_±} ĝ^*(H⁺ - A^*A + η_B) ĝ`.

The quadratic forms of the finite matrices enter as functions `qA ξ`, `qX ξ` on coefficient
vectors (`qA ξ x = re x^* A(ξ) x`, `qX ξ x = re x^*(H⁺ - A(ξ)^* A(ξ)) x`); the finite test
`eq:spectral-test`, `M_{𝔠,±}(s) ⪰ 0`, is `FiniteTest` (and follows from positive
semidefiniteness of the matrix, `Sarkozy.Spectral.finiteTest_of_posSemidef`).

Results:
* `routeA_lower` — (a): `Op ⪰ -g r I`;
* `routeA_compression` — (b): `|⟪h, Op h⟫| ≤ g r ‖h‖²` for `h ⊥ 1`;
* `upper_of_compression` — `prop:matching:positive`(c), giving (d):
  `Op ⪯ (1 + ε_ϱ²/(1 - β)) I` when `‖P₀ Op P₀‖ ≤ β < 1`.
The numerical steps (uniformity in `p`, `B⁺`) are in `Sarkozy.Spectral.Criterion`.
-/

@[expose] public section

open scoped InnerProductSpace ComplexConjugate
open RCLike

namespace Sarkozy.Spectral

variable {𝕜 : Type*} [RCLike 𝕜] {H : Type*} [NormedAddCommGroup H] [InnerProductSpace 𝕜 H]

local notation "⟪" x ", " y "⟫" => @inner 𝕜 _ _ x y

/-- The squared norm `∑_k |x_k|²` of a coefficient vector. -/
noncomputable def sqn {n : Type*} [Fintype n] (x : n → 𝕜) : ℝ := ∑ k, ‖x k‖ ^ 2

omit [NormedAddCommGroup H] [InnerProductSpace 𝕜 H] in
theorem sqn_nonneg {n : Type*} [Fintype n] (x : n → 𝕜) : 0 ≤ sqn x :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- **Young's inequality** for inner products: `2 |⟪a, b⟫| ≤ t ‖a‖² + ‖b‖² / t`. -/
theorem two_norm_inner_le (a b : H) {t : ℝ} (ht : 0 < t) :
    2 * ‖⟪a, b⟫‖ ≤ t * ‖a‖ ^ 2 + ‖b‖ ^ 2 / t := by
  have h1 := norm_inner_le_norm (𝕜 := 𝕜) a b
  have h2 : 2 * (‖a‖ * ‖b‖) ≤ t * ‖a‖ ^ 2 + ‖b‖ ^ 2 / t := by
    rw [show t * ‖a‖ ^ 2 + ‖b‖ ^ 2 / t = (t ^ 2 * ‖a‖ ^ 2 + ‖b‖ ^ 2) / t by field_simp,
      le_div_iff₀ ht]
    nlinarith [sq_nonneg (t * ‖a‖ - ‖b‖)]
  linarith

/-- The quadratic form of a symmetric operator on a sum. -/
theorem re_inner_map_add (T : H →ₗ[𝕜] H) (hT : T.IsSymmetric) (x y : H) :
    re ⟪x + y, T (x + y)⟫ = re ⟪x, T x⟫ + 2 * re ⟪y, T x⟫ + re ⟪y, T y⟫ := by
  have hxy : ⟪x, T y⟫ = conj ⟪y, T x⟫ := by
    rw [← hT x y, inner_conj_symm]
  rw [map_add, inner_add_left, inner_add_right, inner_add_right, hxy]
  simp only [map_add, conj_re]
  ring

/-- **Bessel for two orthogonal subspaces**: `‖P₊ f‖² + ‖P₋ f‖² ≤ ‖f‖²`. -/
theorem norm_sq_add_norm_sq_starProjection_le [FiniteDimensional 𝕜 H] {Sp Sm : Submodule 𝕜 H}
    (h : Sp ⟂ Sm) (f : H) :
    ‖Sp.starProjection f‖ ^ 2 + ‖Sm.starProjection f‖ ^ 2 ≤ ‖f‖ ^ 2 := by
  set a := Sp.starProjection f
  set b := Sm.starProjection f
  have hab : ⟪a, b⟫ = 0 := h.inner_eq (Sp.starProjection_apply_mem f)
    (Sm.starProjection_apply_mem f)
  have hpy : ‖a + b‖ ^ 2 = ‖a‖ ^ 2 + ‖b‖ ^ 2 := by
    have := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := 𝕜) a b hab
    nlinarith
  have ha : re ⟪a, f⟫ = ‖a‖ ^ 2 := by
    rw [Submodule.re_inner_starProjection_eq_normSq]
    rfl
  have hb : re ⟪b, f⟫ = ‖b‖ ^ 2 := by
    rw [Submodule.re_inner_starProjection_eq_normSq]
    rfl
  have hsum : ‖a‖ ^ 2 + ‖b‖ ^ 2 ≤ ‖a + b‖ * ‖f‖ := by
    rw [← ha, ← hb, ← map_add, ← inner_add_left]
    exact (re_le_norm _).trans (norm_inner_le_norm _ _)
  rw [← hpy] at hsum ⊢
  have h0 := norm_nonneg (a + b)
  have h1 := norm_nonneg f
  nlinarith

/-- The finite test `M_{𝔠,±}(s) ⪰ 0` of `eq:spectral-test`, as nonnegativity of its quadratic
form: `x^*(A - (H⁺ - A^*A)/s + (c̄_⊥ + s - η̄_Q - η̄_B/s) I) x ≥ 0`. -/
def FiniteTest {n : Type*} [Fintype n] (qA qX : (n → 𝕜) → ℝ) (cbar s ηQbar ηBbar : ℝ) : Prop :=
  ∀ x, 0 ≤ qA x - qX x / s + (cbar + s - ηQbar - ηBbar / s) * sqn x

/-- The finite test bounds the bracket `𝓜_s(ξ) = A - (H⁺ - A^*A)/s - (η_Q + η_B/s)` from
below by `-(c̄_⊥ + s)`. -/
theorem FiniteTest.bracket {n : Type*} [Fintype n] {qA qX : (n → 𝕜) → ℝ}
    {cbar s ηQ ηB ηQbar ηBbar : ℝ} (h : FiniteTest qA qX cbar s ηQbar ηBbar) (hs : 0 < s)
    (hηQ : ηQ ≤ ηQbar) (hηB : ηB ≤ ηBbar) (x : n → 𝕜) :
    -(cbar + s) * sqn x ≤ qA x - ηQ * sqn x - (qX x + ηB * sqn x) / s := by
  have hx := h x
  have h0 := sqn_nonneg x
  have h1 : ηB * sqn x / s ≤ ηBbar * sqn x / s :=
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hηB h0) hs.le
  have e : qA x - ηQ * sqn x - (qX x + ηB * sqn x) / s =
      (qA x - qX x / s + (cbar + s - ηQbar - ηBbar / s) * sqn x) - (cbar + s) * sqn x +
        (ηQbar - ηQ) * sqn x + (ηBbar * sqn x / s - ηB * sqn x / s) := by
    field_simp
    ring
  rw [e]
  nlinarith [mul_nonneg (sub_nonneg.mpr hηQ) h0]

section Modes

variable {Ξ n : Type*} [Fintype Ξ] [Fintype n]

/-- **The mode estimate** (the core of the proof of `thm:spectral-criterion`): for a symmetric
operator `S`, `v ∈ V` and `f ⊥ V`,
`Q(v) + 2 re ⟪f, S v⟫ ≥ -r ∑_ξ (c̄_⊥ + s_ξ) |ĝ(ξ)|² - r (s1 ‖P₊ f‖² + s2 ‖P₋ f‖²)`, where
`s_ξ = s_±` on `Ξ_±`. Ingredients: the degree-one lower bound, the coupling bound on each
sector, Young's inequality with parameters `s_± r`, and the finite tests. -/
theorem mode_bound [FiniteDimensional 𝕜 H] (S : H →ₗ[𝕜] H) (V Sp Sm : Submodule 𝕜 H)
    (sgn : Ξ → Prop) [DecidablePred sgn] (coef : H → Ξ → n → 𝕜) (qS qX : Ξ → (n → 𝕜) → ℝ)
    {r ηQ ηB cbar sp sm ηQbar ηBbar : ℝ} (hr : 0 < r) (hsp : 0 < sp) (hsm : 0 < sm)
    (hηQ : ηQ ≤ ηQbar) (hηB : ηB ≤ ηBbar)
    (hdeg : ∀ v ∈ V, r * ∑ ξ, (qS ξ (coef v ξ) - ηQ * sqn (coef v ξ)) ≤ re ⟪v, S v⟫)
    (hcoup : ∀ v ∈ V, ∃ vp ∈ V, ∃ vm ∈ V, v = vp + vm ∧
      S vp - V.starProjection (S vp) ∈ Sp ∧ S vm - V.starProjection (S vm) ∈ Sm ∧
      ‖S vp - V.starProjection (S vp)‖ ^ 2 ≤
        r ^ 2 * ∑ ξ with sgn ξ, (qX ξ (coef v ξ) + ηB * sqn (coef v ξ)) ∧
      ‖S vm - V.starProjection (S vm)‖ ^ 2 ≤
        r ^ 2 * ∑ ξ with ¬ sgn ξ, (qX ξ (coef v ξ) + ηB * sqn (coef v ξ)))
    (htp : ∀ ξ, sgn ξ → FiniteTest (qS ξ) (qX ξ) cbar sp ηQbar ηBbar)
    (htm : ∀ ξ, ¬ sgn ξ → FiniteTest (qS ξ) (qX ξ) cbar sm ηQbar ηBbar)
    {v : H} (hv : v ∈ V) {f : H} (hf : ∀ u ∈ V, ⟪u, f⟫ = 0) :
    -r * ∑ ξ, (cbar + (if sgn ξ then sp else sm)) * sqn (coef v ξ) -
        r * (sp * ‖Sp.starProjection f‖ ^ 2 + sm * ‖Sm.starProjection f‖ ^ 2) ≤
      re ⟪v, S v⟫ + 2 * re ⟪f, S v⟫ := by
  obtain ⟨vp, hvp, vm, hvm, rfl, hwp, hwm, hnp, hnm⟩ := hcoup v hv
  set wp := S vp - V.starProjection (S vp) with hwpdef
  set wm := S vm - V.starProjection (S vm) with hwmdef
  set g := coef (vp + vm) with hgdef
  -- `⟪f, S v⟫ = ⟪P₊ f, w₊⟫ + ⟪P₋ f, w₋⟫`
  have hfw : ∀ u ∈ V, ⟪f, S u⟫ = ⟪f, S u - V.starProjection (S u)⟫ := by
    intro u _
    have h0 : ⟪f, V.starProjection (S u)⟫ = 0 := by
      rw [← inner_conj_symm, hf _ (V.starProjection_apply_mem _), map_zero]
    rw [inner_sub_right, h0, sub_zero]
  have hproj : ∀ (K : Submodule 𝕜 H) (w : H), w ∈ K → ⟪f, w⟫ = ⟪K.starProjection f, w⟫ := by
    intro K w hw
    have h0 : ⟪f - K.starProjection f, w⟫ = 0 :=
      Submodule.inner_left_of_mem_orthogonal hw (K.sub_starProjection_mem_orthogonal f)
    rw [inner_sub_left, sub_eq_zero] at h0
    exact h0
  have hsplit : ⟪f, S (vp + vm)⟫ = ⟪Sp.starProjection f, wp⟫ + ⟪Sm.starProjection f, wm⟫ := by
    rw [map_add, inner_add_right, hfw vp hvp, hfw vm hvm, hproj Sp wp hwp, hproj Sm wm hwm]
  -- Young's inequality on each sector
  have hyp : 2 * ‖⟪Sp.starProjection f, wp⟫‖ ≤
      sp * r * ‖Sp.starProjection f‖ ^ 2 + ‖wp‖ ^ 2 / (sp * r) :=
    two_norm_inner_le _ _ (mul_pos hsp hr)
  have hym : 2 * ‖⟪Sm.starProjection f, wm⟫‖ ≤
      sm * r * ‖Sm.starProjection f‖ ^ 2 + ‖wm‖ ^ 2 / (sm * r) :=
    two_norm_inner_le _ _ (mul_pos hsm hr)
  set Xp := ∑ ξ with sgn ξ, (qX ξ (g ξ) + ηB * sqn (g ξ)) with hXp
  set Xm := ∑ ξ with ¬ sgn ξ, (qX ξ (g ξ) + ηB * sqn (g ξ)) with hXm
  have hdp : ‖wp‖ ^ 2 / (sp * r) ≤ r / sp * Xp := by
    rw [div_le_iff₀ (mul_pos hsp hr)]
    calc ‖wp‖ ^ 2 ≤ r ^ 2 * Xp := hnp
      _ = r / sp * Xp * (sp * r) := by field_simp
  have hdm : ‖wm‖ ^ 2 / (sm * r) ≤ r / sm * Xm := by
    rw [div_le_iff₀ (mul_pos hsm hr)]
    calc ‖wm‖ ^ 2 ≤ r ^ 2 * Xm := hnm
      _ = r / sm * Xm * (sm * r) := by field_simp
  have hcross : -(sp * r * ‖Sp.starProjection f‖ ^ 2 + r / sp * Xp) -
      (sm * r * ‖Sm.starProjection f‖ ^ 2 + r / sm * Xm) ≤ 2 * re ⟪f, S (vp + vm)⟫ := by
    rw [hsplit, map_add]
    have h1 := neg_le_of_abs_le (abs_re_le_norm ⟪Sp.starProjection f, wp⟫)
    have h2 := neg_le_of_abs_le (abs_re_le_norm ⟪Sm.starProjection f, wm⟫)
    linarith
  -- the degree-one part, split by sector, and the finite tests
  have hdegv := hdeg (vp + vm) (V.add_mem hvp hvm)
  rw [← hgdef] at hdegv
  have hsum : ∀ (a : Ξ → ℝ), ∑ ξ, a ξ = ∑ ξ with sgn ξ, a ξ + ∑ ξ with ¬ sgn ξ, a ξ :=
    fun a => (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have htestp : ∀ ξ ∈ Finset.univ.filter sgn,
      -(cbar + sp) * sqn (g ξ) ≤ qS ξ (g ξ) - ηQ * sqn (g ξ) - (qX ξ (g ξ) +
        ηB * sqn (g ξ)) / sp := fun ξ hξ =>
    (htp ξ (Finset.mem_filter.mp hξ).2).bracket hsp hηQ hηB (g ξ)
  have htestm : ∀ ξ ∈ Finset.univ.filter (fun ξ => ¬ sgn ξ),
      -(cbar + sm) * sqn (g ξ) ≤ qS ξ (g ξ) - ηQ * sqn (g ξ) - (qX ξ (g ξ) +
        ηB * sqn (g ξ)) / sm := fun ξ hξ =>
    (htm ξ (Finset.mem_filter.mp hξ).2).bracket hsm hηQ hηB (g ξ)
  have hp := Finset.sum_le_sum htestp
  have hm := Finset.sum_le_sum htestm
  have eXp : ∑ ξ with sgn ξ, (qS ξ (g ξ) - ηQ * sqn (g ξ) - (qX ξ (g ξ) + ηB * sqn (g ξ)) / sp) =
      ∑ ξ with sgn ξ, (qS ξ (g ξ) - ηQ * sqn (g ξ)) - Xp / sp := by
    rw [hXp, Finset.sum_div, ← Finset.sum_sub_distrib]
  have eXm : ∑ ξ with ¬ sgn ξ, (qS ξ (g ξ) - ηQ * sqn (g ξ) - (qX ξ (g ξ) + ηB * sqn (g ξ)) / sm) =
      ∑ ξ with ¬ sgn ξ, (qS ξ (g ξ) - ηQ * sqn (g ξ)) - Xm / sm := by
    rw [hXm, Finset.sum_div, ← Finset.sum_sub_distrib]
  rw [eXp] at hp
  rw [eXm] at hm
  have eL : ∑ ξ, (cbar + (if sgn ξ then sp else sm)) * sqn (g ξ) =
      ∑ ξ with sgn ξ, (cbar + sp) * sqn (g ξ) + ∑ ξ with ¬ sgn ξ, (cbar + sm) * sqn (g ξ) := by
    rw [hsum]
    congr 1
    · exact Finset.sum_congr rfl fun ξ hξ => by rw [ite_eq_left (Finset.mem_filter.mp hξ).2]
    · exact Finset.sum_congr rfl fun ξ hξ => by rw [ite_eq_right (Finset.mem_filter.mp hξ).2]
  rw [hsum] at hdegv
  have enp : ∑ ξ with sgn ξ, -(cbar + sp) * sqn (g ξ) =
      -∑ ξ with sgn ξ, (cbar + sp) * sqn (g ξ) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring
  have enm : ∑ ξ with ¬ sgn ξ, -(cbar + sm) * sqn (g ξ) =
      -∑ ξ with ¬ sgn ξ, (cbar + sm) * sqn (g ξ) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun _ _ => by ring
  rw [enp] at hp
  rw [enm] at hm
  rw [eL]
  have e1 : r / sp * Xp = r * (Xp / sp) := by ring
  have e2 : r / sm * Xm = r * (Xm / sm) := by ring
  nlinarith [mul_le_mul_of_nonneg_left hp hr.le, mul_le_mul_of_nonneg_left hm hr.le]

end Modes

/-- The inputs (R1)–(R3) of Route A at one prime, for the operator `T = Op`, in abstract form
(see the module docstring). -/
structure RouteAInputs [FiniteDimensional 𝕜 H] (T : H →ₗ[𝕜] H) (one : H)
    (V Sp Sm : Submodule 𝕜 H) {Ξ n : Type*} [Fintype Ξ] [Fintype n] (sgn : Ξ → Prop)
    [DecidablePred sgn] (coef : H → Ξ → n → 𝕜) (qA qX : Ξ → (n → 𝕜) → ℝ)
    (r ηQ ηB εV ερ aperp : ℝ) : Prop where
  symm : T.IsSymmetric
  norm_one : ‖one‖ = 1
  V_perp_one : ∀ v ∈ V, ⟪one, v⟫ = 0
  sectors_ortho : Sp ⟂ Sm
  /-- `E_μ ϱ = 1` -/
  rho_mean : ⟪one, T one⟫ = 1
  /-- `⟪1, Op v⟫ = 0` on `V` (`prop:spec2:mucentre` (a)) -/
  rho_V : ∀ v ∈ V, ⟪one, T v⟫ = 0
  /-- `‖ϱ - 1‖ ≤ ε_ϱ` (`prop:spec2:mucentre` (c3)) -/
  rho_bound : ‖T one - one‖ ≤ ερ
  /-- `|⟪h, Op h⟫| ≤ a_⊥ ‖h‖²` on `H_⊥` (`prop:spec2:mucentre` (c4)) -/
  perp_bound : ∀ h, ⟪one, h⟫ = 0 → (∀ v ∈ V, ⟪v, h⟫ = 0) → |re ⟪h, T h⟫| ≤ aperp * ‖h‖ ^ 2
  /-- `lem:spec:degone`: lower bound of `Q(F_V)` -/
  degone_lower : ∀ v ∈ V, r * ∑ ξ, (qA ξ (coef v ξ) - ηQ * sqn (coef v ξ)) ≤ re ⟪v, T v⟫
  /-- `lem:spec:degone`: upper bound of `Q(F_V)` -/
  degone_upper : ∀ v ∈ V, re ⟪v, T v⟫ ≤ r * ∑ ξ, (qA ξ (coef v ξ) + ηQ * sqn (coef v ξ))
  /-- `lem:spec:degone` (c): `‖F_V‖² ≥ (1 - ε_V) ‖g‖²` -/
  degone_norm : ∀ v ∈ V, (1 - εV) * ∑ ξ, sqn (coef v ξ) ≤ ‖v‖ ^ 2
  /-- `cor:spec2:coupling`, complex form, on the two translation sectors -/
  coupling : ∀ v ∈ V, ∃ vp ∈ V, ∃ vm ∈ V, v = vp + vm ∧
      T vp - V.starProjection (T vp) ∈ Sp ∧ T vm - V.starProjection (T vm) ∈ Sm ∧
      ‖T vp - V.starProjection (T vp)‖ ^ 2 ≤
        r ^ 2 * ∑ ξ with sgn ξ, (qX ξ (coef v ξ) + ηB * sqn (coef v ξ)) ∧
      ‖T vm - V.starProjection (T vm)‖ ^ 2 ≤
        r ^ 2 * ∑ ξ with ¬ sgn ξ, (qX ξ (coef v ξ) + ηB * sqn (coef v ξ))

section Criterion

variable [FiniteDimensional 𝕜 H] {T : H →ₗ[𝕜] H} {one : H} {V Sp Sm : Submodule 𝕜 H}
  {Ξ n : Type*} [Fintype Ξ] [Fintype n] {sgn : Ξ → Prop} [DecidablePred sgn]
  {coef : H → Ξ → n → 𝕜} {qA qX : Ξ → (n → 𝕜) → ℝ} {r ηQ ηB εV ερ aperp : ℝ}

/-- The decomposition `h = h_V + h_⊥` of `h ⊥ 1`, with `h_V = Π_V h` and `h_⊥ ∈ H_⊥`. -/
theorem decomp_props (hin : RouteAInputs T one V Sp Sm sgn coef qA qX r ηQ ηB εV ερ aperp)
    {h : H} (h1 : ⟪one, h⟫ = 0) :
    V.starProjection h ∈ V ∧ ⟪one, h - V.starProjection h⟫ = 0 ∧
      (∀ u ∈ V, ⟪u, h - V.starProjection h⟫ = 0) ∧
      ‖h‖ ^ 2 = ‖V.starProjection h‖ ^ 2 + ‖h - V.starProjection h‖ ^ 2 := by
  have hmem := V.starProjection_apply_mem h
  have horth : ∀ u ∈ V, ⟪u, h - V.starProjection h⟫ = 0 := fun u hu =>
    Submodule.inner_right_of_mem_orthogonal hu (V.sub_starProjection_mem_orthogonal h)
  refine ⟨hmem, ?_, horth, ?_⟩
  · rw [inner_sub_right, h1, hin.V_perp_one _ hmem, sub_zero]
  · have hpy := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := 𝕜)
      (V.starProjection h) (h - V.starProjection h) (horth _ hmem)
    rw [add_sub_cancel] at hpy
    nlinarith

/-- **`thm:spectral-criterion` (a), abstract form**: `Op ⪰ -g r I`. Here `c̄_⊥ r` bounds
`a_⊥ + ε_ϱ² = c_⊥ r`, `η̄_Q, η̄_B, ε̄_V` bound `η_Q, η_B, ε_V`, the finite tests hold with the
parameters `s_± = τ^{sp}_{𝔠,±}` on the modes `Ξ_±`, and `g ≥ (c̄_⊥ + s_±)/(1 - ε̄_V)`. -/
theorem routeA_lower (hin : RouteAInputs T one V Sp Sm sgn coef qA qX r ηQ ηB εV ερ aperp)
    {cbar ηQbar ηBbar εVbar sp sm g : ℝ} (hr : 0 < r) (hcbar0 : 0 ≤ cbar)
    (hcbar : aperp + ερ ^ 2 ≤ cbar * r) (hηQ : ηQ ≤ ηQbar) (hηB : ηB ≤ ηBbar)
    (hεV : εV ≤ εVbar) (hεV0 : 0 ≤ εVbar) (hεV1 : εVbar < 1) (hsp : 0 < sp) (hsm : 0 < sm)
    (htp : ∀ ξ, sgn ξ → FiniteTest (qA ξ) (qX ξ) cbar sp ηQbar ηBbar)
    (htm : ∀ ξ, ¬ sgn ξ → FiniteTest (qA ξ) (qX ξ) cbar sm ηQbar ηBbar)
    (hgp : (cbar + sp) / (1 - εVbar) ≤ g) (hgm : (cbar + sm) / (1 - εVbar) ≤ g) (F : H) :
    -(g * r) * ‖F‖ ^ 2 ≤ re ⟪F, T F⟫ := by
  have hone : ⟪one, one⟫ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hin.norm_one]
    simp
  set c := ⟪one, F⟫ with hc
  set G := F - c • one with hGdef
  have hG1 : ⟪one, G⟫ = 0 := by
    rw [hGdef, inner_sub_right, inner_smul_right, hone, mul_one, sub_self]
  obtain ⟨hGV, hFp1, hFpV, hGnorm⟩ := decomp_props hin hG1
  set GV := V.starProjection G with hGVdef
  set Fp := G - GV with hFpdef
  have hFsplit : F = c • one + G := by rw [hGdef]; abel
  have hGsplit : G = GV + Fp := by rw [hFpdef]; abel
  -- `‖F‖² = |c|² + ‖G‖²`
  have hFnorm : ‖F‖ ^ 2 = ‖c‖ ^ 2 + ‖G‖ ^ 2 := by
    have h0 : ⟪c • one, G⟫ = 0 := by rw [inner_smul_left, hG1, mul_zero]
    have hpy := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := 𝕜) (c • one) G h0
    rw [← hFsplit, norm_smul, hin.norm_one, mul_one] at hpy
    nlinarith
  -- the expansion `prop:spec2:mucentre` (b)
  set z := ⟪Fp, T one - one⟫ with hz
  have hcross : re ⟪G, T (c • one)⟫ = re (c * z) := by
    have hG_one : ⟪G, one⟫ = 0 := by rw [← inner_conj_symm, hG1, map_zero]
    have hGV_rho : ⟪GV, T one - one⟫ = 0 := by
      rw [inner_sub_right, ← hin.symm, ← inner_conj_symm, hin.rho_V _ hGV, map_zero, zero_sub,
        ← inner_conj_symm, hin.V_perp_one _ hGV, map_zero, neg_zero]
    have e : ⟪G, T (c • one)⟫ = c * z := by
      rw [map_smul, inner_smul_right]
      congr 1
      rw [hz, show ⟪G, T one⟫ = ⟪G, T one - one⟫ by rw [inner_sub_right, hG_one, sub_zero],
        hGsplit, inner_add_left, hGV_rho, zero_add]
    rw [e]
  have hQF : re ⟪F, T F⟫ = ‖c‖ ^ 2 + 2 * re (c * z) + re ⟪G, T G⟫ := by
    rw [hFsplit, re_inner_map_add T hin.symm, hcross]
    congr 2
    rw [map_smul, inner_smul_left, inner_smul_right, hin.rho_mean, mul_one, RCLike.conj_mul,
      ← RCLike.ofReal_pow, RCLike.ofReal_re]
  have hQG : re ⟪G, T G⟫ = re ⟪GV, T GV⟫ + 2 * re ⟪Fp, T GV⟫ + re ⟪Fp, T Fp⟫ := by
    rw [hGsplit, re_inner_map_add T hin.symm]
  -- `|c|² + 2 re(c z) ≥ -|z|² ≥ -ε_ϱ² ‖F_⊥‖²`
  have hz_le : ‖z‖ ≤ ‖Fp‖ * ερ :=
    (norm_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hin.rho_bound (norm_nonneg _))
  have hcz : -(ερ ^ 2 * ‖Fp‖ ^ 2) ≤ ‖c‖ ^ 2 + 2 * re (c * z) := by
    have h1 : -(‖c‖ * ‖z‖) ≤ re (c * z) := by
      have := neg_le_of_abs_le (abs_re_le_norm (c * z))
      rwa [norm_mul] at this
    have h2 : ‖z‖ ^ 2 ≤ (‖Fp‖ * ερ) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hz_le 2
    nlinarith [sq_nonneg (‖c‖ - ‖z‖)]
  -- the perpendicular block
  have hperp := neg_le_of_abs_le (hin.perp_bound Fp hFp1 hFpV)
  -- the modes
  have hmode := mode_bound T V Sp Sm sgn coef qA qX hr hsp hsm hηQ hηB hin.degone_lower
    hin.coupling htp htm hGV hFpV
  have hbessel := norm_sq_add_norm_sq_starProjection_le hin.sectors_ortho Fp
  -- collect
  set N := ∑ ξ, sqn (coef GV ξ) with hN
  set smax := max sp sm with hsmax
  have hsum_le : ∑ ξ, (cbar + (if sgn ξ then sp else sm)) * sqn (coef GV ξ) ≤
      (cbar + smax) * N := by
    rw [hN, Finset.mul_sum]
    refine Finset.sum_le_sum fun ξ _ => mul_le_mul_of_nonneg_right ?_ (sqn_nonneg _)
    split_ifs
    · linarith [le_max_left sp sm]
    · linarith [le_max_right sp sm]
  have hsec : sp * ‖Sp.starProjection Fp‖ ^ 2 + sm * ‖Sm.starProjection Fp‖ ^ 2 ≤
      smax * ‖Fp‖ ^ 2 := by
    have h1 : sp * ‖Sp.starProjection Fp‖ ^ 2 ≤ smax * ‖Sp.starProjection Fp‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)
    have h2 : sm * ‖Sm.starProjection Fp‖ ^ 2 ≤ smax * ‖Sm.starProjection Fp‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _)
    have h3 : smax * (‖Sp.starProjection Fp‖ ^ 2 + ‖Sm.starProjection Fp‖ ^ 2) ≤
        smax * ‖Fp‖ ^ 2 := mul_le_mul_of_nonneg_left hbessel (le_max_of_le_left hsp.le)
    nlinarith
  -- `Q(F) ≥ -(c̄ + s_max) r (‖g‖² + ‖F_⊥‖²)`
  have hlow : -((cbar + smax) * r) * (N + ‖Fp‖ ^ 2) ≤ re ⟪F, T F⟫ := by
    rw [hQF, hQG]
    have hA := mul_le_mul_of_nonneg_left hsum_le hr.le
    have hB := mul_le_mul_of_nonneg_left hsec hr.le
    have hC := mul_le_mul_of_nonneg_right hcbar (sq_nonneg ‖Fp‖)
    linarith
  -- `(1 - ε̄_V)(‖g‖² + ‖F_⊥‖²) ≤ ‖F‖²`
  have hnormV := hin.degone_norm GV hGV
  have hN0 : 0 ≤ N := Finset.sum_nonneg fun _ _ => sqn_nonneg _
  have hden : 0 < 1 - εVbar := by linarith
  have hNF : (1 - εVbar) * (N + ‖Fp‖ ^ 2) ≤ ‖F‖ ^ 2 := by
    have h1 : (1 - εVbar) * N ≤ (1 - εV) * N := mul_le_mul_of_nonneg_right (by linarith) hN0
    have h2 : (1 - εVbar) * ‖Fp‖ ^ 2 ≤ ‖Fp‖ ^ 2 := by
      have := mul_le_mul_of_nonneg_right hεV0 (sq_nonneg ‖Fp‖)
      linarith
    have h3 := sq_nonneg ‖c‖
    have h4 := mul_le_mul_of_nonneg_right hεV (Finset.sum_nonneg fun ξ _ =>
      sqn_nonneg (coef GV ξ) : 0 ≤ N)
    linarith
  have hgmax : (cbar + smax) / (1 - εVbar) ≤ g := by
    rcases le_total sp sm with h | h
    · rw [hsmax, max_eq_right h]; exact hgm
    · rw [hsmax, max_eq_left h]; exact hgp
  have hcs : 0 ≤ cbar + smax := by linarith [hsp.le.trans (le_max_left sp sm)]
  have hfin : (cbar + smax) * (N + ‖Fp‖ ^ 2) ≤ g * ‖F‖ ^ 2 := by
    rw [div_le_iff₀ hden] at hgmax
    have h1 : (cbar + smax) * (N + ‖Fp‖ ^ 2) * (1 - εVbar) ≤ g * ‖F‖ ^ 2 * (1 - εVbar) := by
      calc (cbar + smax) * (N + ‖Fp‖ ^ 2) * (1 - εVbar)
          = (cbar + smax) * ((1 - εVbar) * (N + ‖Fp‖ ^ 2)) := by ring
        _ ≤ (cbar + smax) * ‖F‖ ^ 2 := mul_le_mul_of_nonneg_left hNF hcs
        _ ≤ g * (1 - εVbar) * ‖F‖ ^ 2 := mul_le_mul_of_nonneg_right hgmax (sq_nonneg _)
        _ = g * ‖F‖ ^ 2 * (1 - εVbar) := by ring
    exact le_of_mul_le_mul_right h1 hden
  have hfin' := mul_le_mul_of_nonneg_left hfin hr.le
  have e : -((cbar + smax) * r) * (N + ‖Fp‖ ^ 2) = -(r * ((cbar + smax) * (N + ‖Fp‖ ^ 2))) := by
    ring
  have e' : -(g * r) * ‖F‖ ^ 2 = -(r * (g * ‖F‖ ^ 2)) := by ring
  rw [e']
  rw [e] at hlow
  linarith

/-- **`thm:spectral-criterion` (b), abstract form**: `|⟪h, Op h⟫| ≤ g r ‖h‖²` for `h ⊥ 1`, i.e.
`‖P₀ Op P₀‖ ≤ g r`. The lower bound is (a); the upper bound is the same argument for `-Op`, whose
finite tests (`htp'`, `htm'`, with `-qA`) are the tests of the opposite sign. -/
theorem routeA_compression (hin : RouteAInputs T one V Sp Sm sgn coef qA qX r ηQ ηB εV ερ aperp)
    {cbar ηQbar ηBbar εVbar sp sm sp' sm' g : ℝ} (hr : 0 < r) (hcbar0 : 0 ≤ cbar)
    (hcbar : aperp + ερ ^ 2 ≤ cbar * r) (hηQ : ηQ ≤ ηQbar) (hηB : ηB ≤ ηBbar)
    (hεV : εV ≤ εVbar) (hεV0 : 0 ≤ εVbar) (hεV1 : εVbar < 1) (hsp : 0 < sp) (hsm : 0 < sm)
    (hsp' : 0 < sp') (hsm' : 0 < sm')
    (htp : ∀ ξ, sgn ξ → FiniteTest (qA ξ) (qX ξ) cbar sp ηQbar ηBbar)
    (htm : ∀ ξ, ¬ sgn ξ → FiniteTest (qA ξ) (qX ξ) cbar sm ηQbar ηBbar)
    (htp' : ∀ ξ, sgn ξ → FiniteTest (fun x => -qA ξ x) (qX ξ) cbar sp' ηQbar ηBbar)
    (htm' : ∀ ξ, ¬ sgn ξ → FiniteTest (fun x => -qA ξ x) (qX ξ) cbar sm' ηQbar ηBbar)
    (hgp : (cbar + sp) / (1 - εVbar) ≤ g) (hgm : (cbar + sm) / (1 - εVbar) ≤ g)
    (hgp' : (cbar + sp') / (1 - εVbar) ≤ g) (hgm' : (cbar + sm') / (1 - εVbar) ≤ g)
    {h : H} (h1 : ⟪one, h⟫ = 0) :
    |re ⟪h, T h⟫| ≤ g * r * ‖h‖ ^ 2 := by
  have hden : 0 < 1 - εVbar := by linarith
  obtain ⟨hhV, hhp1, hhpV, hnorm⟩ := decomp_props hin h1
  set hV := V.starProjection h with hhVdef
  set hp := h - hV with hhpdef
  have hsplit : h = hV + hp := by rw [hhpdef]; abel
  -- a generic lower bound for `S ∈ {T, -T}`
  have key : ∀ (S : H →ₗ[𝕜] H) (qS : Ξ → (n → 𝕜) → ℝ) (s1 s2 : ℝ), S.IsSymmetric →
      0 < s1 → 0 < s2 →
      (∀ v ∈ V, r * ∑ ξ, (qS ξ (coef v ξ) - ηQ * sqn (coef v ξ)) ≤ re ⟪v, S v⟫) →
      (∀ v ∈ V, ∃ vp ∈ V, ∃ vm ∈ V, v = vp + vm ∧
        S vp - V.starProjection (S vp) ∈ Sp ∧ S vm - V.starProjection (S vm) ∈ Sm ∧
        ‖S vp - V.starProjection (S vp)‖ ^ 2 ≤
          r ^ 2 * ∑ ξ with sgn ξ, (qX ξ (coef v ξ) + ηB * sqn (coef v ξ)) ∧
        ‖S vm - V.starProjection (S vm)‖ ^ 2 ≤
          r ^ 2 * ∑ ξ with ¬ sgn ξ, (qX ξ (coef v ξ) + ηB * sqn (coef v ξ))) →
      (∀ ξ, sgn ξ → FiniteTest (qS ξ) (qX ξ) cbar s1 ηQbar ηBbar) →
      (∀ ξ, ¬ sgn ξ → FiniteTest (qS ξ) (qX ξ) cbar s2 ηQbar ηBbar) →
      -aperp * ‖hp‖ ^ 2 ≤ re ⟪hp, S hp⟫ →
      (cbar + s1) / (1 - εVbar) ≤ g → (cbar + s2) / (1 - εVbar) ≤ g →
      -(g * r) * ‖h‖ ^ 2 ≤ re ⟪h, S h⟫ := by
    intro S qS s1 s2 hS hs1 hs2 hdeg hcoup htp htm hperp hgA hgB
    have hmode := mode_bound S V Sp Sm sgn coef qS qX hr hs1 hs2 hηQ hηB hdeg hcoup htp htm
      hhV hhpV
    have hbessel := norm_sq_add_norm_sq_starProjection_le hin.sectors_ortho hp
    set N := ∑ ξ, sqn (coef hV ξ) with hN
    set smax := max s1 s2 with hsmax
    have hsum_le : ∑ ξ, (cbar + (if sgn ξ then s1 else s2)) * sqn (coef hV ξ) ≤
        (cbar + smax) * N := by
      rw [hN, Finset.mul_sum]
      refine Finset.sum_le_sum fun ξ _ => mul_le_mul_of_nonneg_right ?_ (sqn_nonneg _)
      split_ifs
      · linarith [le_max_left s1 s2]
      · linarith [le_max_right s1 s2]
    have hsec : s1 * ‖Sp.starProjection hp‖ ^ 2 + s2 * ‖Sm.starProjection hp‖ ^ 2 ≤
        smax * ‖hp‖ ^ 2 := by
      have h1 : s1 * ‖Sp.starProjection hp‖ ^ 2 ≤ smax * ‖Sp.starProjection hp‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)
      have h2 : s2 * ‖Sm.starProjection hp‖ ^ 2 ≤ smax * ‖Sm.starProjection hp‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _)
      have h3 : smax * (‖Sp.starProjection hp‖ ^ 2 + ‖Sm.starProjection hp‖ ^ 2) ≤
          smax * ‖hp‖ ^ 2 := mul_le_mul_of_nonneg_left hbessel (le_max_of_le_left hs1.le)
      nlinarith
    have hQ : re ⟪h, S h⟫ = re ⟪hV, S hV⟫ + 2 * re ⟪hp, S hV⟫ + re ⟪hp, S hp⟫ := by
      rw [hsplit, re_inner_map_add S hS]
    have haperp : aperp ≤ cbar * r := by linarith [sq_nonneg ερ]
    have hlow : -((cbar + smax) * r) * (N + ‖hp‖ ^ 2) ≤ re ⟪h, S h⟫ := by
      rw [hQ]
      have hA := mul_le_mul_of_nonneg_left hsum_le hr.le
      have hB := mul_le_mul_of_nonneg_left hsec hr.le
      have hC := mul_le_mul_of_nonneg_right haperp (sq_nonneg ‖hp‖)
      linarith
    have hnormV := hin.degone_norm hV hhV
    have hN0 : 0 ≤ N := Finset.sum_nonneg fun _ _ => sqn_nonneg _
    have hNF : (1 - εVbar) * (N + ‖hp‖ ^ 2) ≤ ‖h‖ ^ 2 := by
      have h1 : (1 - εVbar) * N ≤ (1 - εV) * N := mul_le_mul_of_nonneg_right (by linarith) hN0
      have h2 : (1 - εVbar) * ‖hp‖ ^ 2 ≤ ‖hp‖ ^ 2 := by
        have := mul_le_mul_of_nonneg_right hεV0 (sq_nonneg ‖hp‖)
        linarith
      have h4 := mul_le_mul_of_nonneg_right hεV hN0
      linarith
    have hgmax : (cbar + smax) / (1 - εVbar) ≤ g := by
      rcases le_total s1 s2 with h' | h'
      · rw [hsmax, max_eq_right h']; exact hgB
      · rw [hsmax, max_eq_left h']; exact hgA
    have hcs : 0 ≤ cbar + smax := by linarith [hs1.le.trans (le_max_left s1 s2)]
    have hfin : (cbar + smax) * (N + ‖hp‖ ^ 2) ≤ g * ‖h‖ ^ 2 := by
      rw [div_le_iff₀ hden] at hgmax
      have h1 : (cbar + smax) * (N + ‖hp‖ ^ 2) * (1 - εVbar) ≤ g * ‖h‖ ^ 2 * (1 - εVbar) := by
        calc (cbar + smax) * (N + ‖hp‖ ^ 2) * (1 - εVbar)
            = (cbar + smax) * ((1 - εVbar) * (N + ‖hp‖ ^ 2)) := by ring
          _ ≤ (cbar + smax) * ‖h‖ ^ 2 := mul_le_mul_of_nonneg_left hNF hcs
          _ ≤ g * (1 - εVbar) * ‖h‖ ^ 2 := mul_le_mul_of_nonneg_right hgmax (sq_nonneg _)
          _ = g * ‖h‖ ^ 2 * (1 - εVbar) := by ring
      exact le_of_mul_le_mul_right h1 hden
    have hfin' := mul_le_mul_of_nonneg_left hfin hr.le
    have e : -((cbar + smax) * r) * (N + ‖hp‖ ^ 2) =
        -(r * ((cbar + smax) * (N + ‖hp‖ ^ 2))) := by ring
    have e' : -(g * r) * ‖h‖ ^ 2 = -(r * (g * ‖h‖ ^ 2)) := by ring
    rw [e']
    rw [e] at hlow
    linarith
  have hperpT := hin.perp_bound hp hhp1 hhpV
  -- lower bound: `S = T`
  have hlow := key T qA sp sm hin.symm hsp hsm hin.degone_lower hin.coupling htp htm
    (neg_le_of_abs_le hperpT |>.trans_eq' (by ring)) hgp hgm
  -- upper bound: `S = -T`
  have hnegsym : (-T).IsSymmetric := fun x y => by
    simp only [LinearMap.neg_apply, inner_neg_left, inner_neg_right, hin.symm x y]
  have hdeg' : ∀ v ∈ V, r * ∑ ξ, ((fun x => -qA ξ x) (coef v ξ) - ηQ * sqn (coef v ξ)) ≤
      re ⟪v, (-T) v⟫ := by
    intro v hv
    have := hin.degone_upper v hv
    simp only [LinearMap.neg_apply, inner_neg_right, map_neg]
    have e : ∑ ξ, (-qA ξ (coef v ξ) - ηQ * sqn (coef v ξ)) =
        -∑ ξ, (qA ξ (coef v ξ) + ηQ * sqn (coef v ξ)) := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_congr rfl fun _ _ => by ring
    rw [e]
    linarith
  have hcoup' : ∀ v ∈ V, ∃ vp ∈ V, ∃ vm ∈ V, v = vp + vm ∧
      (-T) vp - V.starProjection ((-T) vp) ∈ Sp ∧ (-T) vm - V.starProjection ((-T) vm) ∈ Sm ∧
      ‖(-T) vp - V.starProjection ((-T) vp)‖ ^ 2 ≤
        r ^ 2 * ∑ ξ with sgn ξ, (qX ξ (coef v ξ) + ηB * sqn (coef v ξ)) ∧
      ‖(-T) vm - V.starProjection ((-T) vm)‖ ^ 2 ≤
        r ^ 2 * ∑ ξ with ¬ sgn ξ, (qX ξ (coef v ξ) + ηB * sqn (coef v ξ)) := by
    intro v hv
    obtain ⟨vp, hvp, vm, hvm, hvv, hwp, hwm, hnp, hnm⟩ := hin.coupling v hv
    have e : ∀ u, (-T) u - V.starProjection ((-T) u) = -(T u - V.starProjection (T u)) :=
      fun u => by simp only [LinearMap.neg_apply, map_neg]; abel
    refine ⟨vp, hvp, vm, hvm, hvv, ?_, ?_, ?_, ?_⟩
    · rw [e]; exact Sp.neg_mem hwp
    · rw [e]; exact Sm.neg_mem hwm
    · rw [e, norm_neg]; exact hnp
    · rw [e, norm_neg]; exact hnm
  have hperp' : -aperp * ‖hp‖ ^ 2 ≤ re ⟪hp, (-T) hp⟫ := by
    simp only [LinearMap.neg_apply, inner_neg_right, map_neg]
    have := le_abs_self (re ⟪hp, T hp⟫)
    linarith
  have hup := key (-T) (fun ξ x => -qA ξ x) sp' sm' hnegsym hsp' hsm' hdeg' hcoup' htp' htm'
    hperp' hgp' hgm'
  simp only [LinearMap.neg_apply, inner_neg_right, map_neg] at hup
  rw [abs_le]
  constructor
  · linarith
  · linarith

omit [FiniteDimensional 𝕜 H] in
/-- **`prop:matching:positive`(c)**, the upper bound used in (d): if `⟪1, Op 1⟫ = 1`,
`‖Op 1 - 1‖ ≤ e` and `|⟪h, Op h⟫| ≤ β ‖h‖²` for `h ⊥ 1` with `β < 1`, then
`⟪F, Op F⟫ ≤ (1 + e²/(1 - β)) ‖F‖²`. -/
theorem upper_of_compression (hsym : T.IsSymmetric) (hone : ‖one‖ = 1)
    (hmean : ⟪one, T one⟫ = 1) {e β : ℝ} (he : ‖T one - one‖ ≤ e) (hβ : β < 1)
    (hcomp : ∀ h, ⟪one, h⟫ = 0 → |re ⟪h, T h⟫| ≤ β * ‖h‖ ^ 2) (F : H) :
    re ⟪F, T F⟫ ≤ (1 + e ^ 2 / (1 - β)) * ‖F‖ ^ 2 := by
  have hone' : ⟪one, one⟫ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hone]
    simp
  set c := ⟪one, F⟫ with hc
  set h := F - c • one with hhdef
  have hh1 : ⟪one, h⟫ = 0 := by
    rw [hhdef, inner_sub_right, inner_smul_right, hone', mul_one, sub_self]
  have hFsplit : F = c • one + h := by rw [hhdef]; abel
  have hFnorm : ‖F‖ ^ 2 = ‖c‖ ^ 2 + ‖h‖ ^ 2 := by
    have h0 : ⟪c • one, h⟫ = 0 := by rw [inner_smul_left, hh1, mul_zero]
    have hpy := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := 𝕜) (c • one) h h0
    rw [← hFsplit, norm_smul, hone, mul_one] at hpy
    nlinarith
  have hh_one : ⟪h, one⟫ = 0 := by rw [← inner_conj_symm, hh1, map_zero]
  have hcross : ⟪h, T (c • one)⟫ = c * ⟪h, T one - one⟫ := by
    rw [map_smul, inner_smul_right, inner_sub_right, hh_one, sub_zero]
  have hQ : re ⟪F, T F⟫ = ‖c‖ ^ 2 + 2 * re (c * ⟪h, T one - one⟫) + re ⟪h, T h⟫ := by
    rw [hFsplit, re_inner_map_add T hsym, hcross]
    congr 2
    rw [map_smul, inner_smul_left, inner_smul_right, hmean, mul_one, RCLike.conj_mul,
      ← RCLike.ofReal_pow, RCLike.ofReal_re]
  have hz : ‖c * ⟪h, T one - one⟫‖ ≤ ‖c‖ * (‖h‖ * e) := by
    rw [norm_mul]
    exact mul_le_mul_of_nonneg_left ((norm_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_left he (norm_nonneg _))) (norm_nonneg _)
  have hre := (re_le_norm (c * ⟪h, T one - one⟫)).trans hz
  have hcomp' := (abs_le.mp (hcomp h hh1)).2
  have hd : 0 < 1 - β := by linarith
  rw [hQ, hFnorm]
  -- `a² + 2 e a b + β b² ≤ (1 + e²/d)(a² + b²)` with `d = 1 - β`
  set a := ‖c‖
  set b := ‖h‖
  have ha : 0 ≤ a := norm_nonneg _
  have hb : 0 ≤ b := norm_nonneg _
  have key : a ^ 2 + 2 * (a * (b * e)) + β * b ^ 2 ≤ (1 + e ^ 2 / (1 - β)) * (a ^ 2 + b ^ 2) := by
    rw [← sub_nonneg]
    have e1 : (1 + e ^ 2 / (1 - β)) * (a ^ 2 + b ^ 2) - (a ^ 2 + 2 * (a * (b * e)) + β * b ^ 2) =
        ((e * a - (1 - β) * b) ^ 2 + e ^ 2 * b ^ 2) / (1 - β) := by
      field_simp
      ring
    rw [e1]
    positivity
  linarith

end Criterion

end Sarkozy.Spectral
