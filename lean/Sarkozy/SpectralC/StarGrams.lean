module

public import Sarkozy.SpectralC.Intertwiners
public import Sarkozy.SpectralC.GramComparison

@[expose] public section

/-!
# Traces of Grams and the diagonal star Grams (`eq:star-traces`, `lem:general-star`(a))

`paper/sections/14_spectral.tex`, `subsec:spec:actual-stars`. For maps `(Yh)(y) = ∑_a Y(y, a) h(a)`
with real kernels (`kerMap`), the trace of the Gram `Y^*Y'` on `L²_0(𝔽_p)` is
`tr(Y^*Y') = E_ν(p ∑_a Y Y' − ∑_a Y ∑_a Y')` (`trace_gramOp`; with `φ = pY` this is
`E_ν(E_z φφ' − E_z φ E_z φ')`, the first identity of `eq:star-traces`).

For a law `μ` on labellings `x : U → 𝔽_p`, invariant under the diagonal action of `Aff_p` and
supported on injective labellings, and a support `S`, the star map is
`(W_S h)(x) = E_z ψ_S(z, x) h(z)`, `ψ_S(z, x) = ∏_{j ∈ S} χ(z − x_j)` (kernel `starKer S`), and
`w_S(x) = E_z ψ_S(z, x)` is the star mean (`starMean`). It intertwines the two actions
(`starKer_cov`), so its Grams are `αI + γC` on `L²_0` with `α`, `γ` given by the two traces
(`eq:star-traces`: `trace_gramOp`, `trace_gaussAdj_gramOp`).

* The ranges: a covariant kernel map sends `L²_0` into the orthogonal complement of the
  translation-invariant functions (`kerMap_orth_invariant`), so `V_i h` and `W_S h` have
  `μ`-mean zero.
* `lem:general-star`(a), `p ≡ 3 (mod 4)`: `W_S^*W_S = q(1 − |S|q − E_μ w_S²)/(1 − q) I ⪯ qI`
  (`star_diagonal`).
* `lem:general-star`(b): `W_S^*W_T = q(A_ST − C_ST)/(1 − q) I + B_ST/(1 − q) C`, and for
  `p ≡ 3 (mod 4)` `‖W_S^*W_T‖ = (q/(1 − q))((A_ST − C_ST)² + B_ST²/q)^{1/2}` (`star_cross`).
* The singletons `(V_i h)(x) = h(x_i)` (`vertKer`): `V_i^*V_j` from its traces (`vert_gram`),
  `V_i^*V_i = I` (`vert_isometry`, the opening claim), and
  `‖V_i^*V_j‖ ≤ r√(1 + q)/(1 − q)` for `i ≠ j` (`vert_cross_bound`, the last claim of (d)).
* `lem:general-star`(f), in the row-sum form: `‖∑_α F_α h_α‖² ≤ (1 + ρ)∑_α‖h_α‖²`
  (`synthesis_bound`, with the Schur test `offdiag_quad_le`).

Not done: (c) (the pivot bound), the star entries of (d) (`eq:singleton-star`, which need the
Weil bound), (e), and the `λ_max` form of (f).

New material for this paper.
-/

namespace Sarkozy.SpectralC

open Finset Complex Sarkozy.Characters
open scoped BigOperators ComplexConjugate

variable {p : ℕ} [Fact p.Prime]

section Traces

variable {𝒴 : Type*} [Fintype 𝒴]

omit [Fintype 𝒴] in
lemma kerMap_ech (Y : 𝒴 → ZMod p → ℝ) (ξ : ZMod p) (y : 𝒴) :
    kerMap Y (ech ξ) y = (p : ℂ) * conj (fcoef (fun a => (Y y a : ℂ)) ξ) := by
  unfold kerMap fcoef ip
  rw [map_mul, map_sum, map_inv₀, map_natCast, ← mul_assoc, mul_inv_cancel₀ p_ne_zero_C, one_mul]
  refine sum_congr rfl fun a _ => ?_
  rw [map_mul, Complex.conj_conj, Complex.conj_ofReal, mul_comm]

/-- **`eq:star-traces`, the trace**: `tr(Y^*Y') = E_ν(p ∑_a Y Y' − ∑_a Y ∑_a Y')`. -/
theorem trace_gramOp (ν : 𝒴 → ℝ) (Y Y' : 𝒴 → ZMod p → ℝ) :
    trace0 (gramOp ν Y Y') = ∑ y, (ν y : ℂ) * ((p : ℂ) * ∑ a, (Y y a : ℂ) * (Y' y a : ℂ) -
      (∑ a, (Y y a : ℂ)) * ∑ a, (Y' y a : ℂ)) := by
  unfold trace0
  rw [sum_congr rfl fun ξ _ => (ip_kerMap ν Y Y' (ech ξ) (ech ξ)).symm, sum_comm]
  refine sum_congr rfl fun y _ => ?_
  rw [← mul_sum]
  congr 1
  rw [filter_ne', sum_erase_eq_sub (mem_univ 0)]
  have hall : ∑ ξ, conj (kerMap Y (ech ξ) y) * kerMap Y' (ech ξ) y =
      (p : ℂ) * ∑ a, (Y y a : ℂ) * (Y' y a : ℂ) := by
    simp_rw [kerMap_ech, map_mul, map_natCast, Complex.conj_conj]
    have h1 : ∀ ξ, (p : ℂ) * fcoef (fun a => (Y y a : ℂ)) ξ *
        ((p : ℂ) * conj (fcoef (fun a => (Y' y a : ℂ)) ξ)) =
        (p : ℂ) * (p : ℂ) * (conj (fcoef (fun a => (Y' y a : ℂ)) ξ) *
          fcoef (fun a => (Y y a : ℂ)) ξ) := by intro ξ; ring
    rw [sum_congr rfl fun ξ _ => h1 ξ, ← mul_sum, ← ip_eq_sum_fcoef]
    unfold ip
    dsimp only
    simp only [Complex.conj_ofReal]
    have hpC := p_ne_zero_C (p := p)
    rw [show ∀ X : ℂ, (p : ℂ) * p * ((p : ℂ)⁻¹ * X) = p * X from fun X => by field_simp]
    congr 1
    exact sum_congr rfl fun a _ => mul_comm _ _
  have h0 : conj (kerMap Y (ech 0) y) * kerMap Y' (ech 0) y =
      (∑ a, (Y y a : ℂ)) * ∑ a, (Y' y a : ℂ) := by
    unfold kerMap
    simp only [ech_zero_left, mul_one, map_sum, Complex.conj_ofReal]
  rw [hall, h0]

omit [Fintype 𝒴] in
/-- `⟨f, C^*g⟩ = ⟨Cf, g⟩`. -/
lemma ip_gaussOpAdj (f g : ZMod p → ℂ) : ip f (gaussOpAdj g) = ip (gaussOp f) g := by
  rw [← conj_ip (gaussOpAdj g) f, ← ip_gaussOp g f, conj_ip]

omit [Fintype 𝒴] in
lemma ip_smul_left (z : ℂ) (f g : ZMod p → ℂ) : ip (fun a => z * f a) g = conj z * ip f g := by
  unfold ip
  have h : ∑ a, conj (z * f a) * g a = conj z * ∑ a, conj (f a) * g a := by
    rw [Finset.mul_sum]
    exact sum_congr rfl fun a _ => by rw [map_mul]; ring
  rw [h]
  ring

omit [Fintype 𝒴] in
/-- `∑_ξ \overline{c_ξ} e_ξ(t) = χ(t)`. -/
lemma sum_conj_gaussEig_ech (hp2 : p ≠ 2) (t : ZMod p) :
    ∑ ξ, conj (gaussEig ξ) * ech ξ t = chiC p t := by
  have hG : conj (Gchi p) * Gchi p = (p : ℂ) := by
    rw [Complex.conj_mul']
    have h1 : Gchi p = epsG p * ((Real.sqrt p : ℝ) : ℂ) := by
      unfold epsG; field_simp [sqrt_p_ne_zero (p := p)]
    rw [h1, norm_mul, norm_epsG hp2, one_mul, Complex.norm_real, Real.norm_of_nonneg
      (Real.sqrt_nonneg _), ← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg p),
      Complex.ofReal_natCast]
  have h2 : ∀ ξ, conj (gaussEig ξ) * ech ξ t = conj (Gchi p) / (p : ℂ) * (chiC p ξ * ech t ξ) := by
    intro ξ
    rw [gaussEig_eq, map_div₀, map_mul, conj_chiC, map_natCast, ech_comm]
    ring
  rw [sum_congr rfl fun ξ _ => h2 ξ, ← mul_sum, sum_chiC_ech hp2 t]
  have hpC := p_ne_zero_C (p := p)
  rw [show conj (Gchi p) / (p : ℂ) * (chiC p t * Gchi p) = (conj (Gchi p) * Gchi p) / p * chiC p t
    by ring, hG, div_self hpC, one_mul]

/-- **`eq:star-traces`, the second trace**:
`tr(C^*Y^*Y') = E_ν ∑_{a,b} Y(·, a) χ(b − a) Y'(·, b)` (with `φ = pY` this is
`E_ν⟨φ, Cφ'⟩`). -/
theorem trace_gaussAdj_gramOp (hp2 : p ≠ 2) (ν : 𝒴 → ℝ) (Y Y' : 𝒴 → ZMod p → ℝ) :
    trace0 (fun h => gaussOpAdj (gramOp ν Y Y' h)) =
      ∑ y, (ν y : ℂ) * ∑ a, ∑ b, (Y y a : ℂ) * chiC p (b - a) * (Y' y b : ℂ) := by
  unfold trace0
  have h1 : ∀ ξ : ZMod p, ip (ech ξ) (gaussOpAdj (gramOp ν Y Y' (ech ξ))) =
      conj (gaussEig ξ) * ∑ y, (ν y : ℂ) * (conj (kerMap Y (ech ξ) y) * kerMap Y' (ech ξ) y) := by
    intro ξ
    rw [ip_gaussOpAdj, show gaussOp (ech ξ) = fun a => gaussEig ξ * ech ξ a from
      funext (gaussOp_ech hp2 ξ), ip_smul_left, ip_kerMap]
  rw [sum_congr rfl fun ξ _ => h1 ξ, filter_ne', sum_erase_eq_sub (mem_univ 0), gaussEig_zero,
    map_zero, zero_mul, sub_zero]
  simp_rw [mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun y _ => ?_
  unfold kerMap
  simp_rw [map_sum, map_mul, Complex.conj_ofReal, sum_mul_sum, mul_sum]
  -- reorder to `∑_a ∑_b … ∑_ξ`
  have h2 : ∀ ξ : ZMod p, ∑ a, ∑ b, conj (gaussEig ξ) * ((ν y : ℂ) * ((Y y a : ℂ) *
      conj (ech ξ a) * ((Y' y b : ℂ) * ech ξ b))) =
      ∑ a, ∑ b, (ν y : ℂ) * ((Y y a : ℂ) * (Y' y b : ℂ)) *
        (conj (gaussEig ξ) * ech ξ (b - a)) := by
    intro ξ
    refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => ?_
    rw [conj_ech, show b - a = b + -a by ring, ech_add_right, show ech ξ (-a) = ech (-ξ) a by
      unfold ech; ring_nf]
    ring
  rw [sum_congr rfl fun ξ _ => h2 ξ, sum_comm]
  refine sum_congr rfl fun a _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun b _ => ?_
  rw [← mul_sum, sum_conj_gaussEig_ech hp2]
  ring

end Traces

/-! ## Ranges -/

section Ranges

variable {𝒴 : Type*} [Fintype 𝒴]

omit [Fintype 𝒴] in
lemma isSquare_one_zmod : IsSquare (1 : ZMod p) := ⟨1, by ring⟩

/-- **The ranges** (the opening claim of `lem:general-star`): a map with a covariant real kernel
sends `L²_0(𝔽_p)` into the orthogonal complement of the functions invariant under the
translations; in particular (`F = 1`) into the `ν`-mean-zero functions. -/
theorem kerMap_orth_invariant {ν : 𝒴 → ℝ} (G : AffAction p 𝒴 ν) (Y : 𝒴 → ZMod p → ℝ)
    (hY : ∀ (s c : ZMod p), s ≠ 0 → IsSquare s → ∀ (h : ZMod p → ℂ) (y : 𝒴),
      kerMap Y (fun a => h (s * a + c)) y = kerMap Y h (G.act s c y))
    (F : 𝒴 → ℂ) (hF : ∀ (c : ZMod p) (y : 𝒴), F (G.act 1 c y) = F y)
    (h : ZMod p → ℂ) (hh : meanC h = 0) :
    ∑ y, (ν y : ℂ) * (conj (F y) * kerMap Y h y) = 0 := by
  set K : ZMod p → ℂ := fun a => ∑ y, (ν y : ℂ) * (conj (F y) * (Y y a : ℂ)) with hK
  have hKc : ∀ a c : ZMod p, K (a + c) = K a := by
    intro a c
    simp only [hK]
    rw [← (G.bij 1 c one_ne_zero isSquare_one_zmod).sum_comp]
    refine sum_congr rfl fun y _ => ?_
    have hcov := kerMap_cov G Y hY 1 c one_ne_zero isSquare_one_zmod y a
    rw [one_mul] at hcov
    rw [G.pres 1 c y one_ne_zero isSquare_one_zmod, hF c y, hcov]
  have hconst : ∀ a, K a = K 0 := fun a => by rw [← zero_add a, hKc 0 a]
  have hsum : ∑ a, h a = 0 := by
    unfold meanC at hh
    have hpC := p_ne_zero_C (p := p)
    exact (mul_eq_zero.mp hh).resolve_left (inv_ne_zero hpC)
  calc ∑ y, (ν y : ℂ) * (conj (F y) * kerMap Y h y)
      = ∑ a, K a * h a := by
        simp only [hK, kerMap, mul_sum, sum_mul]
        rw [sum_comm]
        exact sum_congr rfl fun a _ => sum_congr rfl fun y _ => by ring
    _ = K 0 * ∑ a, h a := by rw [mul_sum]; exact sum_congr rfl fun a _ => by rw [hconst a]
    _ = 0 := by rw [hsum, mul_zero]

end Ranges

/-! ## Stars -/

variable {U : Type*} [Fintype U] [DecidableEq U]

/-- The real quadratic character. -/
noncomputable def chiRe (t : ZMod p) : ℝ := (quadraticChar (ZMod p) t : ℝ)

/-- The kernel of the star map: `(W_S h)(x) = ∑_a p⁻¹ ψ_S(a, x) h(a)`. -/
noncomputable def starKer (S : Finset U) (x : U → ZMod p) (a : ZMod p) : ℝ :=
  (p : ℝ)⁻¹ * ∏ j ∈ S, chiRe (a - x j)

/-- The star mean `w_S(x) = E_z ψ_S(z, x)`. -/
noncomputable def starMean (S : Finset U) (x : U → ZMod p) : ℝ := ∑ a, starKer S x a

omit [Fintype U] [DecidableEq U] in
lemma chiRe_mul (s t : ZMod p) : chiRe (s * t) = chiRe s * chiRe t := by
  unfold chiRe; rw [map_mul]; push_cast; ring

omit [Fintype U] [DecidableEq U] in
lemma chiRe_of_isSquare {s : ZMod p} (hs : s ≠ 0) (hsq : IsSquare s) : chiRe s = 1 := by
  unfold chiRe; rw [(quadraticChar_one_iff_isSquare hs).mpr hsq]; simp

omit [Fintype U] [DecidableEq U] in
/-- `ψ_S(z, x)² = 𝟙[z ∉ x(S)]`. -/
lemma prod_chiRe_sq (S : Finset U) (x : U → ZMod p) (a : ZMod p) :
    (∏ j ∈ S, chiRe (a - x j)) ^ 2 = if a ∈ S.image x then 0 else 1 := by
  rw [← prod_pow]
  split_ifs with ha
  · obtain ⟨j, hj, hjx⟩ := mem_image.mp ha
    apply prod_eq_zero hj
    rw [hjx, sub_self]
    unfold chiRe
    simp
  · apply prod_eq_one
    intro j hj
    have hne : a - x j ≠ 0 := by
      intro h0
      exact ha (mem_image.mpr ⟨j, hj, (sub_eq_zero.mp h0).symm⟩)
    unfold chiRe
    exact_mod_cast quadraticChar_sq_one hne

omit [Fintype U] [DecidableEq U] in
/-- The star map intertwines the actions: `W_S(h ∘ γ) = (W_S h) ∘ γ` for `γ z = sz + c`,
`s ∈ Q_p`. -/
lemma starKer_cov (S : Finset U) (s c : ZMod p) (hs : s ≠ 0) (hsq : IsSquare s)
    (h : ZMod p → ℂ) (x : U → ZMod p) :
    kerMap (starKer S) (fun a => h (s * a + c)) x = kerMap (starKer S) h (affLab s c x) := by
  unfold kerMap
  have hbij : Function.Bijective (fun b : ZMod p => s * b + c) := by
    constructor
    · intro b b' hb
      exact mul_left_cancel₀ hs (by simpa using hb)
    · intro b
      exact ⟨s⁻¹ * (b - c), by field_simp; ring⟩
  rw [← hbij.sum_comp (fun b => (starKer S (affLab s c x) b : ℂ) * h b)]
  refine sum_congr rfl fun a _ => ?_
  congr 2
  unfold starKer affLab
  congr 1
  refine prod_congr rfl fun j _ => ?_
  rw [show s * a + c - (s * x j + c) = s * (a - x j) by ring, chiRe_mul,
    chiRe_of_isSquare hs hsq, one_mul]

/-- The `Aff_p` action on labellings preserving an invariant `μ`. -/
def labAction (μ : (U → ZMod p) → ℝ)
    (hinv : ∀ (s c : ZMod p) (x : U → ZMod p), s ≠ 0 → IsSquare s → μ (affLab s c x) = μ x) :
    AffAction p (U → ZMod p) μ where
  act := affLab
  bij := fun _ c hs _ => affLab_bijective hs c
  pres := fun s c x hs hsq => hinv s c x hs hsq

omit [Fintype U] in
/-- `p ∑_a (p⁻¹ψ_S)² = 1 − |S|/p` on injective labellings. -/
lemma sum_starKer_sq (S : Finset U) (x : U → ZMod p) (hx : ∀ k l, k ≠ l → x k ≠ x l) :
    (p : ℝ) * ∑ a, starKer S x a * starKer S x a = 1 - (S.card : ℝ) / p := by
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have h1 : ∀ a, starKer S x a * starKer S x a =
      (p : ℝ)⁻¹ ^ 2 * (1 - if a ∈ S.image x then 1 else 0) := by
    intro a
    unfold starKer
    rw [show ((p : ℝ)⁻¹ * ∏ j ∈ S, chiRe (a - x j)) * ((p : ℝ)⁻¹ * ∏ j ∈ S, chiRe (a - x j)) =
      (p : ℝ)⁻¹ ^ 2 * (∏ j ∈ S, chiRe (a - x j)) ^ 2 by ring, prod_chiRe_sq]
    split_ifs <;> ring
  rw [sum_congr rfl fun a _ => h1 a, ← mul_sum, sum_sub_distrib, sum_const, card_univ, ZMod.card,
    nsmul_eq_mul, mul_one, sum_ind, card_image_of_injOn (fun k _ l _ hkl => by
      by_contra hne; exact hx k l hne hkl)]
  field_simp

/-- **`lem:general-star`(a)** (`p ≡ 3 (mod 4)`): on `L²_0`,
`W_S^*W_S = q(1 − |S|q − E_μ w_S²)/(1 − q) I`, and this coefficient is at most `q` if `S ≠ ∅`. -/
theorem star_diagonal (hp2 : p ≠ 2) (hp3 : p % 4 = 3) (μ : (U → ZMod p) → ℝ)
    (hμ0 : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1)
    (hinv : ∀ (s c : ZMod p) (x : U → ZMod p), s ≠ 0 → IsSquare s → μ (affLab s c x) = μ x)
    (hinj : ∀ (x : U → ZMod p) (k l : U), μ x ≠ 0 → k ≠ l → x k ≠ x l) (S : Finset U) :
    (∀ (h : ZMod p → ℂ), meanC h = 0 → ∀ a,
      gramOp μ (starKer S) (starKer S) h a =
        (((p : ℝ)⁻¹ * (1 - (S.card : ℝ) * (p : ℝ)⁻¹ - ∑ x, μ x * starMean S x ^ 2) /
          (1 - (p : ℝ)⁻¹) : ℝ) : ℂ) * h a) ∧
    (S.Nonempty → (p : ℝ)⁻¹ * (1 - (S.card : ℝ) * (p : ℝ)⁻¹ - ∑ x, μ x * starMean S x ^ 2) /
          (1 - (p : ℝ)⁻¹) ≤ (p : ℝ)⁻¹) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp0 : (p : ℝ) ≠ 0 := by positivity
  obtain ⟨αT, hT, htr⟩ := intertwiner_gram_self hp2 hp3 (labAction μ hinv) (starKer S)
    (fun s c hs hsq h x => starKer_cov S s c hs hsq h x)
  rw [trace_gramOp] at htr
  -- the trace
  have htr' : ((1 - (S.card : ℝ) * (p : ℝ)⁻¹ - ∑ x, μ x * starMean S x ^ 2 : ℝ) : ℂ) =
      ((p : ℂ) - 1) * αT := by
    rw [← htr]
    have hx : ∀ x, (μ x : ℂ) * ((p : ℂ) * ∑ a, (starKer S x a : ℂ) * (starKer S x a : ℂ) -
        (∑ a, (starKer S x a : ℂ)) * ∑ a, (starKer S x a : ℂ)) =
        ((μ x * (1 - (S.card : ℝ) / p - starMean S x ^ 2) : ℝ) : ℂ) := by
      intro x
      by_cases hμx : μ x = 0
      · rw [hμx]; simp
      · rw [← sum_starKer_sq S x (fun k l hkl => hinj x k l hμx hkl)]
        unfold starMean
        push_cast
        ring
    rw [sum_congr rfl fun x _ => hx x]
    push_cast
    have hμ1C : ∑ x, (μ x : ℂ) = 1 := by exact_mod_cast hμ1
    simp only [mul_sub, sum_sub_distrib, ← sum_mul, hμ1C]
    ring
  have hα : αT = (p : ℝ)⁻¹ * (1 - (S.card : ℝ) * (p : ℝ)⁻¹ - ∑ x, μ x * starMean S x ^ 2) /
      (1 - (p : ℝ)⁻¹) := by
    have h2 : (1 - (S.card : ℝ) * (p : ℝ)⁻¹ - ∑ x, μ x * starMean S x ^ 2) =
        ((p : ℝ) - 1) * αT := by exact_mod_cast htr'
    rw [h2]
    have : (1 : ℝ) - (p : ℝ)⁻¹ ≠ 0 := by
      have : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp1
      linarith
    have hp1' : (p : ℝ) - 1 ≠ 0 := by linarith
    field_simp
  refine ⟨fun h hh a => by rw [hT h hh a, hα], fun hS => ?_⟩
  have hS1 : (1 : ℝ) ≤ S.card := by exact_mod_cast hS.card_pos
  have hw : 0 ≤ ∑ x, μ x * starMean S x ^ 2 :=
    sum_nonneg fun x _ => mul_nonneg (hμ0 x) (sq_nonneg _)
  have hq1 : 0 < 1 - (p : ℝ)⁻¹ := by
    have : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp1
    linarith
  rw [div_le_iff₀ hq1]
  have hq0 : 0 < (p : ℝ)⁻¹ := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hS1 hq0.le]

/-- `A_ST = E_μ E_z ψ_S ψ_T`. -/
noncomputable def starA (μ : (U → ZMod p) → ℝ) (S T : Finset U) : ℝ :=
  ∑ x, μ x * ((p : ℝ) * ∑ a, starKer S x a * starKer T x a)

/-- `C_ST = E_μ w_S w_T`. -/
noncomputable def starC (μ : (U → ZMod p) → ℝ) (S T : Finset U) : ℝ :=
  ∑ x, μ x * (starMean S x * starMean T x)

/-- `B_ST = E_μ⟨ψ_S, Cψ_T⟩ = E_μ ∑_{a,b} (ψ_S(a)/p) χ(b − a) (ψ_T(b)/p)`. -/
noncomputable def starB (μ : (U → ZMod p) → ℝ) (S T : Finset U) : ℝ :=
  ∑ x, μ x * ∑ a, ∑ b, starKer S x a * chiRe (b - a) * starKer T x b

/-- **`lem:general-star`(b)**: on `L²_0`,
`W_S^*W_T = q(A_ST − C_ST)/(1 − q) I + B_ST/(1 − q) C`; for `p ≡ 3 (mod 4)` also
`‖W_S^*W_T h‖² = (q/(1 − q))² ((A_ST − C_ST)² + B_ST²/q) ‖h‖²`. -/
theorem star_cross (hp2 : p ≠ 2) (μ : (U → ZMod p) → ℝ)
    (hinv : ∀ (s c : ZMod p) (x : U → ZMod p), s ≠ 0 → IsSquare s → μ (affLab s c x) = μ x)
    (S T : Finset U) :
    (∀ (h : ZMod p → ℂ), meanC h = 0 → ∀ a,
      gramOp μ (starKer S) (starKer T) h a =
        (((p : ℝ)⁻¹ * (starA μ S T - starC μ S T) / (1 - (p : ℝ)⁻¹) : ℝ) : ℂ) * h a +
          ((starB μ S T / (1 - (p : ℝ)⁻¹) : ℝ) : ℂ) * gaussOp h a) ∧
    (p % 4 = 3 → ∀ (h : ZMod p → ℂ), meanC h = 0 →
      l2sq (gramOp μ (starKer S) (starKer T) h) =
        ((p : ℝ)⁻¹ / (1 - (p : ℝ)⁻¹)) ^ 2 *
          ((starA μ S T - starC μ S T) ^ 2 + starB μ S T ^ 2 / (p : ℝ)⁻¹) * l2sq h) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp0 : (p : ℝ) ≠ 0 := by positivity
  have hq1 : (1 : ℝ) - (p : ℝ)⁻¹ ≠ 0 := by
    have : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp1
    linarith
  have hp1' : (p : ℝ) - 1 ≠ 0 := by linarith
  obtain ⟨αT, γT, hT⟩ := intertwiner_gram hp2 (labAction μ hinv) (starKer S) (starKer T)
    (fun s c hs hsq h x => starKer_cov S s c hs hsq h x)
    (fun s c hs hsq h x => starKer_cov T s c hs hsq h x)
  have hagree : ∀ ξ : ZMod p, ξ ≠ 0 → gramOp μ (starKer S) (starKer T) (ech ξ) =
      fun a => (αT : ℂ) * ech ξ a + (γT : ℂ) * gaussOp (ech ξ) a := by
    intro ξ hξ
    have hm : meanC (ech ξ) = 0 := by rw [meanC_ech, ite_eq_right hξ]
    exact funext (hT (ech ξ) hm)
  obtain ⟨hc1, hc2⟩ := commutant_traces hp2 αT γT
  have h1 : trace0 (gramOp μ (starKer S) (starKer T)) = ((p : ℂ) - 1) * αT := by
    rw [← hc1]
    unfold trace0
    exact sum_congr rfl fun ξ hξ => by rw [hagree ξ (mem_filter.mp hξ).2]
  have h2 : trace0 (fun h => gaussOpAdj (gramOp μ (starKer S) (starKer T) h)) =
      (1 - (p : ℂ)⁻¹) * γT := by
    rw [← hc2]
    unfold trace0
    exact sum_congr rfl fun ξ hξ => by dsimp only; rw [hagree ξ (mem_filter.mp hξ).2]
  rw [trace_gramOp] at h1
  rw [trace_gaussAdj_gramOp hp2] at h2
  have hAC : starA μ S T - starC μ S T = ((p : ℝ) - 1) * αT := by
    have : ((starA μ S T - starC μ S T : ℝ) : ℂ) = (((p : ℝ) - 1) * αT : ℝ) := by
      push_cast
      rw [← h1]
      unfold starA starC starMean
      push_cast
      rw [← sum_sub_distrib]
      exact sum_congr rfl fun x _ => by ring
    exact_mod_cast this
  have hB : starB μ S T = (1 - (p : ℝ)⁻¹) * γT := by
    have : ((starB μ S T : ℝ) : ℂ) = ((1 - (p : ℝ)⁻¹) * γT : ℝ) := by
      push_cast
      rw [← h2]
      unfold starB chiRe
      push_cast
      simp only [chiC_apply]
    exact_mod_cast this
  have hα : αT = (p : ℝ)⁻¹ * (starA μ S T - starC μ S T) / (1 - (p : ℝ)⁻¹) := by
    rw [hAC]; field_simp
  have hγ : γT = starB μ S T / (1 - (p : ℝ)⁻¹) := by
    rw [hB]; field_simp
  refine ⟨fun h hh a => by rw [hT h hh a, hα, hγ], fun hp3 h hh => ?_⟩
  have hfun : gramOp μ (starKer S) (starKer T) h =
      fun a => (αT : ℂ) * h a + (γT : ℂ) * gaussOp h a := funext (hT h hh)
  rw [hfun, commutant_norm hp2 hp3 αT γT h hh, hα, hγ]
  congr 1
  field_simp

/-! ## Singletons -/

/-- The kernel of `(V_i h)(x) = h(x_i)`. -/
noncomputable def vertKer (i : U) (x : U → ZMod p) (a : ZMod p) : ℝ := if a = x i then 1 else 0

omit [Fintype U] [DecidableEq U] in
lemma kerMap_vertKer (i : U) (h : ZMod p → ℂ) (x : U → ZMod p) :
    kerMap (vertKer i) h x = h (x i) := by
  unfold kerMap vertKer
  rw [sum_eq_single (x i) (fun b _ hb => by rw [ite_eq_right hb]; simp)
    (fun h => absurd (mem_univ _) h), ite_eq_left rfl]
  simp

omit [Fintype U] [DecidableEq U] in
lemma sum_vertKer (i : U) (x : U → ZMod p) : ∑ a, vertKer i x a = 1 := by
  unfold vertKer
  rw [sum_ite_eq']
  simp

omit [Fintype U] [DecidableEq U] in
lemma sum_vertKer_mul (i j : U) (x : U → ZMod p) :
    ∑ a, vertKer i x a * vertKer j x a = if x i = x j then 1 else 0 := by
  unfold vertKer
  rw [sum_eq_single (x i) (fun a _ ha => by rw [ite_eq_right ha, zero_mul])
    (fun h => absurd (mem_univ _) h), ite_eq_left rfl, one_mul]

omit [Fintype U] [DecidableEq U] in
lemma sum_vertKer_chi (i j : U) (x : U → ZMod p) :
    ∑ a, ∑ b, vertKer i x a * chiRe (b - a) * vertKer j x b = chiRe (x j - x i) := by
  unfold vertKer
  rw [sum_eq_single (x i) (fun a _ ha => by simp [ha]) (fun h => absurd (mem_univ _) h)]
  rw [sum_eq_single (x j) (fun b _ hb => by simp [hb]) (fun h => absurd (mem_univ _) h)]
  simp

omit [Fintype U] [DecidableEq U] in
lemma vertKer_cov (i : U) (s c : ZMod p) (h : ZMod p → ℂ) (x : U → ZMod p) :
    kerMap (vertKer i) (fun a => h (s * a + c)) x = kerMap (vertKer i) h (affLab s c x) := by
  rw [kerMap_vertKer, kerMap_vertKer]
  rfl

/-- The Gram `V_i^*V_j` on `L²_0` from its two traces (any odd `p`). -/
theorem vert_gram (hp2 : p ≠ 2) (μ : (U → ZMod p) → ℝ) (hμ1 : ∑ x, μ x = 1)
    (hinv : ∀ (s c : ZMod p) (x : U → ZMod p), s ≠ 0 → IsSquare s → μ (affLab s c x) = μ x)
    (i j : U) : ∀ (h : ZMod p → ℂ), meanC h = 0 → ∀ a,
      gramOp μ (vertKer i) (vertKer j) h a =
        ((((p : ℝ) * ∑ x, μ x * (if x i = x j then 1 else 0) - 1) / ((p : ℝ) - 1) : ℝ) : ℂ) * h a +
          (((∑ x, μ x * chiRe (x j - x i)) / (1 - (p : ℝ)⁻¹) : ℝ) : ℂ) * gaussOp h a := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hq1 : (1 : ℝ) - (p : ℝ)⁻¹ ≠ 0 := by
    have : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp1
    linarith
  have hp1' : (p : ℝ) - 1 ≠ 0 := by linarith
  obtain ⟨αT, γT, hT⟩ := intertwiner_gram hp2 (labAction μ hinv) (vertKer i) (vertKer j)
    (fun s c _ _ h x => vertKer_cov i s c h x) (fun s c _ _ h x => vertKer_cov j s c h x)
  have hagree : ∀ ξ : ZMod p, ξ ≠ 0 → gramOp μ (vertKer i) (vertKer j) (ech ξ) =
      fun a => (αT : ℂ) * ech ξ a + (γT : ℂ) * gaussOp (ech ξ) a := by
    intro ξ hξ
    have hm : meanC (ech ξ) = 0 := by rw [meanC_ech, ite_eq_right hξ]
    exact funext (hT (ech ξ) hm)
  obtain ⟨hc1, hc2⟩ := commutant_traces hp2 αT γT
  have h1 : trace0 (gramOp μ (vertKer i) (vertKer j)) = ((p : ℂ) - 1) * αT := by
    rw [← hc1]
    unfold trace0
    exact sum_congr rfl fun ξ hξ => by rw [hagree ξ (mem_filter.mp hξ).2]
  have h2 : trace0 (fun h => gaussOpAdj (gramOp μ (vertKer i) (vertKer j) h)) =
      (1 - (p : ℂ)⁻¹) * γT := by
    rw [← hc2]
    unfold trace0
    exact sum_congr rfl fun ξ hξ => by dsimp only; rw [hagree ξ (mem_filter.mp hξ).2]
  rw [trace_gramOp] at h1
  rw [trace_gaussAdj_gramOp hp2] at h2
  have hA : (p : ℝ) * ∑ x, μ x * (if x i = x j then 1 else 0) - 1 = ((p : ℝ) - 1) * αT := by
    have hx : ∀ x : U → ZMod p, (μ x : ℂ) * ((p : ℂ) * ∑ a, ((vertKer i x a : ℝ) : ℂ) *
        ((vertKer j x a : ℝ) : ℂ) - (∑ a, ((vertKer i x a : ℝ) : ℂ)) *
          ∑ a, ((vertKer j x a : ℝ) : ℂ)) =
        (((p : ℝ) * (μ x * (if x i = x j then 1 else 0)) - μ x : ℝ) : ℂ) := by
      intro x
      have e1 : ∑ a, ((vertKer i x a : ℝ) : ℂ) * ((vertKer j x a : ℝ) : ℂ) =
          (((if x i = x j then 1 else 0) : ℝ) : ℂ) := by
        rw [← sum_vertKer_mul]; push_cast; rfl
      have e2 : ∀ k, ∑ a, ((vertKer k x a : ℝ) : ℂ) = 1 := by
        intro k; exact_mod_cast sum_vertKer k x
      rw [e1, e2, e2]
      push_cast
      ring
    have : (((p : ℝ) * ∑ x, μ x * (if x i = x j then 1 else 0) - 1 : ℝ) : ℂ) =
        (((p : ℝ) - 1) * αT : ℝ) := by
      push_cast
      rw [← h1, sum_congr rfl fun x _ => hx x]
      push_cast
      rw [sum_sub_distrib, ← mul_sum]
      have hμC : ∑ x, (μ x : ℂ) = 1 := by exact_mod_cast hμ1
      rw [hμC]
    exact_mod_cast this
  have hB : ∑ x, μ x * chiRe (x j - x i) = (1 - (p : ℝ)⁻¹) * γT := by
    have : ((∑ x, μ x * chiRe (x j - x i) : ℝ) : ℂ) = ((1 - (p : ℝ)⁻¹) * γT : ℝ) := by
      push_cast
      rw [← h2]
      refine sum_congr rfl fun x _ => ?_
      congr 1
      rw [← sum_vertKer_chi i j x]
      push_cast
      unfold chiRe
      simp only [chiC_apply]
      push_cast
      rfl
    exact_mod_cast this
  have hα : αT = ((p : ℝ) * ∑ x, μ x * (if x i = x j then 1 else 0) - 1) / ((p : ℝ) - 1) := by
    rw [hA]; field_simp
  have hγ : γT = (∑ x, μ x * chiRe (x j - x i)) / (1 - (p : ℝ)⁻¹) := by
    rw [hB]; field_simp
  intro h hh a
  rw [hT h hh a, hα, hγ]

/-- **The singletons are isometries** (the opening claim of `lem:general-star`): `V_i^*V_i = I` on
`L²_0`. -/
theorem vert_isometry (hp2 : p ≠ 2) (μ : (U → ZMod p) → ℝ) (hμ1 : ∑ x, μ x = 1)
    (hinv : ∀ (s c : ZMod p) (x : U → ZMod p), s ≠ 0 → IsSquare s → μ (affLab s c x) = μ x)
    (i : U) (h : ZMod p → ℂ) (hh : meanC h = 0) (a : ZMod p) :
    gramOp μ (vertKer i) (vertKer i) h a = h a := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp1' : (p : ℝ) - 1 ≠ 0 := by linarith
  rw [vert_gram hp2 μ hμ1 hinv i i h hh a]
  simp only [ite_true, mul_one, hμ1, sub_self, chiRe, quadraticChar_zero]
  rw [div_self hp1']
  simp

/-- **`lem:general-star`(d), the singleton pairs** (`p ≡ 3 (mod 4)`): for `i ≠ j` and injective
`μ`, `‖V_i^*V_j h‖² ≤ q(1 + q)/(1 − q)² ‖h‖²` on `L²_0`, that is
`‖V_i^*V_j‖ ≤ r√(1 + q)/(1 − q)`. -/
theorem vert_cross_bound (hp2 : p ≠ 2) (hp3 : p % 4 = 3) (μ : (U → ZMod p) → ℝ)
    (hμ0 : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1)
    (hinv : ∀ (s c : ZMod p) (x : U → ZMod p), s ≠ 0 → IsSquare s → μ (affLab s c x) = μ x)
    (hinj : ∀ (x : U → ZMod p) (k l : U), μ x ≠ 0 → k ≠ l → x k ≠ x l)
    {i j : U} (hij : i ≠ j) (h : ZMod p → ℂ) (hh : meanC h = 0) :
    l2sq (gramOp μ (vertKer i) (vertKer j) h) ≤
      (p : ℝ)⁻¹ * (1 + (p : ℝ)⁻¹) / (1 - (p : ℝ)⁻¹) ^ 2 * l2sq h := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hp1' : (p : ℝ) - 1 ≠ 0 := by linarith
  have hq : 0 < (p : ℝ)⁻¹ := by positivity
  have hq1 : 0 < (1 : ℝ) - (p : ℝ)⁻¹ := by
    have : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp1
    linarith
  have h0 : ∑ x, μ x * (if x i = x j then (1 : ℝ) else 0) = 0 := by
    refine sum_eq_zero fun x _ => ?_
    by_cases hx : μ x = 0
    · rw [hx, zero_mul]
    · rw [ite_eq_right (hinj x i j hx hij), mul_zero]
  set Δ := ∑ x, μ x * chiRe (x j - x i) with hΔ
  have hΔ1 : |Δ| ≤ 1 := by
    rw [hΔ]
    calc |∑ x, μ x * chiRe (x j - x i)| ≤ ∑ x, μ x * 1 := by
          refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun x _ => ?_)
          rw [abs_mul, abs_of_nonneg (hμ0 x)]
          apply mul_le_mul_of_nonneg_left _ (hμ0 x)
          unfold chiRe
          by_cases h0 : x j - x i = 0
          · rw [h0, quadraticChar_zero]; simp
          · rcases quadraticChar_dichotomy h0 with h1 | h1 <;> rw [h1] <;> simp
      _ = 1 := by rw [← sum_mul, hμ1, one_mul]
  have hfun : gramOp μ (vertKer i) (vertKer j) h = fun a =>
      ((-((p : ℝ) - 1)⁻¹ : ℝ) : ℂ) * h a + ((Δ / (1 - (p : ℝ)⁻¹) : ℝ) : ℂ) * gaussOp h a := by
    funext a
    rw [vert_gram hp2 μ hμ1 hinv i j h hh a, h0, mul_zero, zero_sub, neg_div, ← hΔ]
    push_cast
    ring
  rw [hfun, commutant_norm hp2 hp3 _ _ h hh]
  apply mul_le_mul_of_nonneg_right _ (by unfold l2sq; positivity)
  have hΔsq : Δ ^ 2 ≤ 1 := by
    rw [← sq_abs]
    have := abs_nonneg Δ
    nlinarith
  have hpinv : ((p : ℝ) - 1)⁻¹ = (p : ℝ)⁻¹ / (1 - (p : ℝ)⁻¹) := by
    field_simp
  rw [hpinv, neg_sq, div_pow, div_pow]
  have hD : 0 < (1 - (p : ℝ)⁻¹) ^ 2 := by positivity
  have hre : ((p : ℝ)⁻¹ ^ 2 / (1 - (p : ℝ)⁻¹) ^ 2 + (p : ℝ)⁻¹ * (Δ ^ 2 / (1 - (p : ℝ)⁻¹) ^ 2)) =
      ((p : ℝ)⁻¹ ^ 2 + (p : ℝ)⁻¹ * Δ ^ 2) / (1 - (p : ℝ)⁻¹) ^ 2 := by ring
  rw [hre]
  apply div_le_div_of_nonneg_right _ hD.le
  nlinarith

/-! ## Synthesis (`lem:general-star`(f)) -/

/-- The Schur test for a symmetric nonnegative off-diagonal matrix:
`∑_{α ≠ β} N_αβ t_α t_β ≤ ρ ∑_α t_α²`. -/
lemma offdiag_quad_le {ι : Type*} [Fintype ι] [DecidableEq ι] (N : ι → ι → ℝ)
    (hN0 : ∀ a b, 0 ≤ N a b) (hNsym : ∀ a b, N a b = N b a) {ρ : ℝ}
    (hrow : ∀ a, ∑ b, (if a = b then 0 else N a b) ≤ ρ) (t : ι → ℝ) :
    ∑ a, ∑ b, (if a = b then 0 else N a b) * t a * t b ≤ ρ * ∑ a, t a ^ 2 := by
  set M : ι → ι → ℝ := fun a b => if a = b then 0 else N a b with hM
  have hM0 : ∀ a b, 0 ≤ M a b := fun a b => by
    simp only [hM]; split_ifs
    · exact le_refl 0
    · exact hN0 a b
  have hMsym : ∀ a b, M a b = M b a := fun a b => by
    simp only [hM]
    by_cases h : a = b
    · rw [ite_eq_left h, ite_eq_left h.symm]
    · rw [ite_eq_right h, ite_eq_right (Ne.symm h), hNsym]
  have h1 : ∀ a b, M a b * t a * t b ≤ M a b * t a ^ 2 / 2 + M a b * t b ^ 2 / 2 := by
    intro a b
    nlinarith [mul_nonneg (hM0 a b) (sq_nonneg (t a - t b))]
  have hrow' : ∀ a, ∑ b, M b a ≤ ρ := fun a => by
    rw [sum_congr rfl fun b _ => hMsym b a]; exact hrow a
  calc ∑ a, ∑ b, M a b * t a * t b
      ≤ ∑ a, ∑ b, (M a b * t a ^ 2 / 2 + M a b * t b ^ 2 / 2) :=
        sum_le_sum fun a _ => sum_le_sum fun b _ => h1 a b
    _ = (∑ a, t a ^ 2 * ∑ b, M a b) / 2 + (∑ b, t b ^ 2 * ∑ a, M a b) / 2 := by
        have e1 : ∑ a, ∑ b, M a b * t a ^ 2 / 2 = (∑ a, t a ^ 2 * ∑ b, M a b) / 2 := by
          rw [sum_div]
          exact sum_congr rfl fun a _ => by
            rw [mul_sum, sum_div]; exact sum_congr rfl fun b _ => by ring
        have e2 : ∑ a, ∑ b, M a b * t b ^ 2 / 2 = (∑ b, t b ^ 2 * ∑ a, M a b) / 2 := by
          rw [sum_comm, sum_div]
          exact sum_congr rfl fun b _ => by
            rw [mul_sum, sum_div]; exact sum_congr rfl fun a _ => by ring
        simp only [sum_add_distrib]
        rw [e1, e2]
    _ ≤ (∑ a, t a ^ 2 * ρ) / 2 + (∑ b, t b ^ 2 * ρ) / 2 := by
        gcongr with a _ b _
        · exact hrow a
        · exact hrow' b
    _ = ρ * ∑ a, t a ^ 2 := by rw [← sum_mul]; ring

/-- **`lem:general-star`(f), synthesis**: for features `F_α` (real kernels `Y α`) with
`‖F_α h‖ ≤ ‖h‖` and `|⟨F_α h, F_β h'⟩| ≤ N_αβ ‖h‖ ‖h'‖` for `α ≠ β` on `L²_0` (`N` symmetric,
nonnegative, off-diagonal row sums at most `ρ`), `‖∑_α F_α h_α‖² ≤ (1 + ρ) ∑_α ‖h_α‖²`.
(The singletons `V_i` are isometries, `vert_isometry`, and `‖W_S/r‖ ≤ 1` by `star_diagonal`.) -/
theorem synthesis_bound {𝒴 ι : Type*} [Fintype 𝒴] [Fintype ι] [DecidableEq ι] (ν : 𝒴 → ℝ)
    (Y : ι → 𝒴 → ZMod p → ℝ) (N : ι → ι → ℝ) (hN0 : ∀ a b, 0 ≤ N a b)
    (hNsym : ∀ a b, N a b = N b a) {ρ : ℝ}
    (hrow : ∀ a, ∑ b, (if a = b then 0 else N a b) ≤ ρ)
    (hdiag : ∀ (a : ι) (h : ZMod p → ℂ), meanC h = 0 →
      ∑ y, ν y * ‖kerMap (Y a) h y‖ ^ 2 ≤ l2sq h)
    (hoff : ∀ a b : ι, a ≠ b → ∀ (h h' : ZMod p → ℂ), meanC h = 0 → meanC h' = 0 →
      ‖∑ y, (ν y : ℂ) * (conj (kerMap (Y a) h y) * kerMap (Y b) h' y)‖ ≤
        N a b * Real.sqrt (l2sq h) * Real.sqrt (l2sq h'))
    (h : ι → ZMod p → ℂ) (hh : ∀ a, meanC (h a) = 0) :
    ∑ y, ν y * ‖∑ a, kerMap (Y a) (h a) y‖ ^ 2 ≤ (1 + ρ) * ∑ a, l2sq (h a) := by
  set G : ι → ι → ℂ := fun a b =>
    ∑ y, (ν y : ℂ) * (conj (kerMap (Y a) (h a) y) * kerMap (Y b) (h b) y) with hG
  set t : ι → ℝ := fun a => Real.sqrt (l2sq (h a)) with ht
  have hl2 : ∀ a, 0 ≤ l2sq (h a) := fun a => by unfold l2sq; positivity
  have ht2 : ∀ a, t a ^ 2 = l2sq (h a) := fun a => Real.sq_sqrt (hl2 a)
  -- expand the square
  have hexp : ∑ y, ν y * ‖∑ a, kerMap (Y a) (h a) y‖ ^ 2 = ∑ a, ∑ b, (G a b).re := by
    have hC : ((∑ y, ν y * ‖∑ a, kerMap (Y a) (h a) y‖ ^ 2 : ℝ) : ℂ) = ∑ a, ∑ b, G a b := by
      push_cast
      simp only [hG]
      have hy : ∀ y, (ν y : ℂ) * (‖∑ a, kerMap (Y a) (h a) y‖ : ℂ) ^ 2 =
          ∑ a, ∑ b, (ν y : ℂ) * (conj (kerMap (Y a) (h a) y) * kerMap (Y b) (h b) y) := by
        intro y
        rw [← Complex.conj_mul', map_sum, sum_mul_sum, mul_sum]
        exact sum_congr rfl fun a _ => by rw [mul_sum]
      rw [sum_congr rfl fun y _ => hy y, sum_comm]
      exact sum_congr rfl fun a _ => sum_comm
    have := congrArg Complex.re hC
    rw [Complex.ofReal_re, Complex.re_sum] at this
    rw [this]
    exact sum_congr rfl fun a _ => Complex.re_sum _ _
  -- split the diagonal
  have hsplit : ∀ a b, (G a b).re = (if a = b then (G a a).re else 0) +
      (if a = b then 0 else (G a b).re) := by
    intro a b
    by_cases hab : a = b
    · subst hab; simp
    · simp [hab]
  have hdiag' : ∀ a, (G a a).re ≤ l2sq (h a) := by
    intro a
    have h1 : (G a a).re = ∑ y, ν y * ‖kerMap (Y a) (h a) y‖ ^ 2 := by
      simp only [hG]
      rw [Complex.re_sum]
      refine sum_congr rfl fun y _ => ?_
      rw [Complex.conj_mul', ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
    rw [h1]
    exact hdiag a (h a) (hh a)
  have hoff' : ∀ a b, (if a = b then 0 else (G a b).re) ≤
      (if a = b then 0 else N a b) * t a * t b := by
    intro a b
    by_cases hab : a = b
    · simp [hab]
    · rw [ite_eq_right hab, ite_eq_right hab]
      exact (Complex.re_le_norm _).trans (hoff a b hab (h a) (h b) (hh a) (hh b))
  rw [hexp]
  calc ∑ a, ∑ b, (G a b).re
      = ∑ a, (G a a).re + ∑ a, ∑ b, (if a = b then 0 else (G a b).re) := by
        rw [← sum_add_distrib]
        refine sum_congr rfl fun a _ => ?_
        rw [sum_congr rfl fun b _ => hsplit a b, sum_add_distrib, sum_ite_eq, ite_eq_left (mem_univ a)]
    _ ≤ ∑ a, l2sq (h a) + ∑ a, ∑ b, (if a = b then 0 else N a b) * t a * t b :=
        add_le_add (sum_le_sum fun a _ => hdiag' a)
          (sum_le_sum fun a _ => sum_le_sum fun b _ => hoff' a b)
    _ ≤ ∑ a, l2sq (h a) + ρ * ∑ a, t a ^ 2 :=
        add_le_add (le_refl _) (offdiag_quad_le N hN0 hNsym hrow t)
    _ = (1 + ρ) * ∑ a, l2sq (h a) := by
        rw [sum_congr rfl fun a _ => ht2 a]; ring

end Sarkozy.SpectralC
