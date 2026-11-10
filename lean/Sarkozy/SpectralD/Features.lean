module

public import Sarkozy.SpectralD.SynthesisMax
public import Sarkozy.SpectralD.PivotCross

@[expose] public section

/-!
# The actual features and their synthesis (`lem:general-star`(f) for `V_i`, `W_S/r`)

`paper/sections/14_spectral.tex`, `subsec:spec:actual-stars`. For a set `𝒮` of supports the
actual features are `F_i = V_i` (`i ∈ U`) and `F_S = W_S/r` (`S ∈ 𝒮`), indexed by `U ⊕ 𝒮`
(`featKer`). This file states `lem:general-star`(f) for exactly these features:

* `feat_diag`: the diagonal Grams, `‖F_α h‖ ≤ ‖h‖` (`V_i` is an isometry, WP-K's
  `vert_isometry`; `(W_S/r)^*(W_S/r) ⪯ I` by (a), WP-K's `star_diagonal`).
* `features_synthesis`: if `N ≥ 0` bounds the off-diagonal Grams,
  `|⟨F_α h, F_β h'⟩_μ| ≤ N_αβ ‖h‖ ‖h'‖`, and `λ` bounds the quadratic form of `N`, then
  `‖∑_α F_α h_α‖² ≤ (1 + λ) ∑_α ‖h_α‖²`; `features_synthesis_eigenvalue` with `λ = λ_max(N)`.
* The entries: `entry_of_gram` turns a squared Gram bound `‖Y^*Y'h‖² ≤ C‖h‖²` into the
  bilinear form needed by `features_synthesis`, and `gramOp_smul` scales it for `W_S/r`; the
  entries of (c) (`feat_star_star_entry`, from `star_pivot_bound`) and of (d)
  (`feat_vert_star_out_entry`, `feat_vert_star_mem_entry`, `feat_vert_star_pair_entry`,
  `feat_vert_vert_entry`) are given in this form.

New material for this paper.
-/

namespace Sarkozy.SpectralD

open Finset Sarkozy.SpectralC
open scoped BigOperators ComplexConjugate symmDiff

variable {p : ℕ} [Fact p.Prime] {U : Type*} [Fintype U] [DecidableEq U]

/-- **The actual features** of a set `𝒮` of supports: `F_i = V_i` and `F_S = W_S/r`. -/
noncomputable def featKer (𝒮 : Finset (Finset U)) :
    U ⊕ 𝒮 → (U → ZMod p) → ZMod p → ℝ
  | Sum.inl i => vertKer i
  | Sum.inr S => fun x a => (rp p)⁻¹ * starKer S.1 x a

section Generic

variable {𝒴 : Type*} [Fintype 𝒴]

omit [Fintype 𝒴] in
lemma kerMap_const_mul (c : ℝ) (Y : 𝒴 → ZMod p → ℝ) (h : ZMod p → ℂ) (y : 𝒴) :
    kerMap (fun y a => c * Y y a) h y = (c : ℂ) * kerMap Y h y := by
  unfold kerMap
  rw [mul_sum]
  refine sum_congr rfl fun a _ => ?_
  push_cast
  ring

/-- Scaling the kernels scales the Gram: `(cY)^*(c'Y') = cc' Y^*Y'`. -/
lemma gramOp_smul (ν : 𝒴 → ℝ) (c c' : ℝ) (Y Y' : 𝒴 → ZMod p → ℝ) (h : ZMod p → ℂ)
    (a : ZMod p) :
    gramOp ν (fun y b => c * Y y b) (fun y b => c' * Y' y b) h a =
      ((c * c' : ℝ) : ℂ) * gramOp ν Y Y' h a := by
  unfold gramOp matOp gramKer
  rw [mul_sum]
  refine sum_congr rfl fun b _ => ?_
  have e : ∑ y, ν y * (c * Y y a) * (c' * Y' y b) = c * c' * ∑ y, ν y * Y y a * Y' y b := by
    rw [mul_sum]; exact sum_congr rfl fun y _ => by ring
  rw [e]
  push_cast
  ring

lemma l2sq_const_mul (c : ℂ) (g : ZMod p → ℂ) : l2sq (fun a => c * g a) = ‖c‖ ^ 2 * l2sq g := by
  show (p : ℝ)⁻¹ * ∑ a, ‖c * g a‖ ^ 2 = ‖c‖ ^ 2 * ((p : ℝ)⁻¹ * ∑ a, ‖g a‖ ^ 2)
  have e : ∑ a, ‖c * g a‖ ^ 2 = ‖c‖ ^ 2 * ∑ a, ‖g a‖ ^ 2 := by
    rw [mul_sum]; exact sum_congr rfl fun a _ => by rw [norm_mul, mul_pow]
  rw [e]; ring

/-- **A squared Gram bound gives the bilinear bound**: if `‖Y^*Y'h'‖² ≤ C‖h'‖²` on `L²_0`
(`C ≥ 0`), then `|⟨Yh, Y'h'⟩_ν| ≤ √C ‖h‖ ‖h'‖` for `h'` of mean zero. -/
theorem entry_of_gram (ν : 𝒴 → ℝ) (Y Y' : 𝒴 → ZMod p → ℝ) {C : ℝ}
    (hC : ∀ h' : ZMod p → ℂ, meanC h' = 0 → l2sq (gramOp ν Y Y' h') ≤ C * l2sq h')
    (h h' : ZMod p → ℂ) (hh' : meanC h' = 0) :
    ‖∑ y, (ν y : ℂ) * (conj (kerMap Y h y) * kerMap Y' h' y)‖ ≤
      Real.sqrt C * Real.sqrt (l2sq h) * Real.sqrt (l2sq h') := by
  rw [ip_kerMap]
  refine (norm_ip_le _ _).trans ?_
  have h1 : Real.sqrt (l2sq (gramOp ν Y Y' h')) ≤ Real.sqrt C * Real.sqrt (l2sq h') := by
    rw [← Real.sqrt_mul' _ (l2sq_nonneg h')]
    exact Real.sqrt_le_sqrt (hC h' hh')
  calc Real.sqrt (l2sq h) * Real.sqrt (l2sq (gramOp ν Y Y' h'))
      ≤ Real.sqrt (l2sq h) * (Real.sqrt C * Real.sqrt (l2sq h')) :=
        mul_le_mul_of_nonneg_left h1 (Real.sqrt_nonneg _)
    _ = Real.sqrt C * Real.sqrt (l2sq h) * Real.sqrt (l2sq h') := by ring

end Generic

/-- **The diagonal Grams of the actual features** (`lem:general-star`, the opening claim and
(a); `p ≡ 3 (mod 4)`): `‖F_α h‖²_μ ≤ ‖h‖²` on `L²_0`, for supports `S ∈ 𝒮` that are
nonempty. -/
theorem feat_diag (hp2 : p ≠ 2) (hp3 : p % 4 = 3) (μ : (U → ZMod p) → ℝ)
    (hμ0 : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1)
    (hinv : ∀ (s c : ZMod p) (x : U → ZMod p), s ≠ 0 → IsSquare s → μ (affLab s c x) = μ x)
    (hinj : ∀ (x : U → ZMod p) (k l : U), μ x ≠ 0 → k ≠ l → x k ≠ x l)
    (𝒮 : Finset (Finset U)) (h𝒮 : ∀ S ∈ 𝒮, S.Nonempty) (α : U ⊕ 𝒮) (h : ZMod p → ℂ)
    (hh : meanC h = 0) :
    ∑ x, μ x * ‖kerMap (featKer 𝒮 α) h x‖ ^ 2 ≤ l2sq h := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  rcases α with i | ⟨S, hS⟩
  · apply le_of_eq
    have e := norm_kerMap_sq μ (vertKer i) h
    have hg : gramOp μ (vertKer i) (vertKer i) h = h :=
      funext fun a => vert_isometry hp2 μ hμ1 hinv i h hh a
    rw [hg, ← l2sq_eq_re_ip] at e
    exact_mod_cast e
  · obtain ⟨hT, hle⟩ := star_diagonal hp2 hp3 μ hμ0 hμ1 hinv hinj S
    set α0 := (p : ℝ)⁻¹ * (1 - (S.card : ℝ) * (p : ℝ)⁻¹ - ∑ x, μ x * starMean S x ^ 2) /
      (1 - (p : ℝ)⁻¹) with hα0
    have hα0le := hle (h𝒮 S hS)
    have hk : ∀ x, kerMap (featKer 𝒮 (Sum.inr ⟨S, hS⟩)) h x =
        ((rp p)⁻¹ : ℂ) * kerMap (starKer S) h x := by
      intro x
      have := kerMap_const_mul (rp p)⁻¹ (starKer S) h x
      rw [Complex.ofReal_inv] at this
      exact this
    have e := norm_kerMap_sq μ (starKer S) h
    have hg : gramOp μ (starKer S) (starKer S) h = fun a => (α0 : ℂ) * h a :=
      funext fun a => hT h hh a
    rw [hg] at e
    have e2 : ip h (fun a => (α0 : ℂ) * h a) = (α0 : ℂ) * ip h h := by
      show (p : ℂ)⁻¹ * ∑ a, conj (h a) * ((α0 : ℂ) * h a) =
        (α0 : ℂ) * ((p : ℂ)⁻¹ * ∑ a, conj (h a) * h a)
      have e3 : ∑ a, conj (h a) * ((α0 : ℂ) * h a) = (α0 : ℂ) * ∑ a, conj (h a) * h a := by
        rw [mul_sum]; exact sum_congr rfl fun a _ => by ring
      rw [e3]; ring
    rw [e2, ← l2sq_eq_re_ip] at e
    have eR : ∑ x, μ x * ‖kerMap (starKer S) h x‖ ^ 2 = α0 * l2sq h := by exact_mod_cast e
    have hrp : (rp p)⁻¹ ^ 2 = (p : ℝ) := by
      rw [inv_pow, rp_sq, inv_inv]
    calc ∑ x, μ x * ‖kerMap (featKer 𝒮 (Sum.inr ⟨S, hS⟩)) h x‖ ^ 2
        = (rp p)⁻¹ ^ 2 * ∑ x, μ x * ‖kerMap (starKer S) h x‖ ^ 2 := by
          rw [mul_sum]
          refine sum_congr rfl fun x _ => ?_
          rw [hk x, norm_mul, mul_pow, ← Complex.ofReal_inv, Complex.norm_real, Real.norm_eq_abs,
            sq_abs]
          ring
      _ = (p : ℝ) * (α0 * l2sq h) := by rw [eR, hrp]
      _ ≤ (p : ℝ) * ((p : ℝ)⁻¹ * l2sq h) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hα0le (l2sq_nonneg h)) hp0.le
      _ = l2sq h := by field_simp

/-- **`lem:general-star`(f) for the actual features** (`p ≡ 3 (mod 4)`): if `N ≥ 0` bounds the
off-diagonal Grams of `F_i = V_i`, `F_S = W_S/r` and `λ` bounds its quadratic form on
nonnegative vectors, then `‖∑_α F_α h_α‖²_μ ≤ (1 + λ) ∑_α ‖h_α‖²` for mean-zero `h_α`. -/
theorem features_synthesis (hp2 : p ≠ 2) (hp3 : p % 4 = 3) (μ : (U → ZMod p) → ℝ)
    (hμ0 : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1)
    (hinv : ∀ (s c : ZMod p) (x : U → ZMod p), s ≠ 0 → IsSquare s → μ (affLab s c x) = μ x)
    (hinj : ∀ (x : U → ZMod p) (k l : U), μ x ≠ 0 → k ≠ l → x k ≠ x l)
    (𝒮 : Finset (Finset U)) (h𝒮 : ∀ S ∈ 𝒮, S.Nonempty) (N : U ⊕ 𝒮 → U ⊕ 𝒮 → ℝ)
    (hN0 : ∀ a b, 0 ≤ N a b) {lam : ℝ}
    (hlam : ∀ t : U ⊕ 𝒮 → ℝ, (∀ a, 0 ≤ t a) → ∑ a, ∑ b, N a b * t a * t b ≤ lam * ∑ a, t a ^ 2)
    (hoff : ∀ a b : U ⊕ 𝒮, a ≠ b → ∀ (h h' : ZMod p → ℂ), meanC h = 0 → meanC h' = 0 →
      ‖∑ x, (μ x : ℂ) * (conj (kerMap (featKer 𝒮 a) h x) * kerMap (featKer 𝒮 b) h' x)‖ ≤
        N a b * Real.sqrt (l2sq h) * Real.sqrt (l2sq h'))
    (h : U ⊕ 𝒮 → ZMod p → ℂ) (hh : ∀ a, meanC (h a) = 0) :
    ∑ x, μ x * ‖∑ a, kerMap (featKer 𝒮 a) (h a) x‖ ^ 2 ≤ (1 + lam) * ∑ a, l2sq (h a) :=
  synthesis_bound_quad μ (featKer 𝒮) N hN0 hlam
    (fun a h' hh' => feat_diag hp2 hp3 μ hμ0 hμ1 hinv hinj 𝒮 h𝒮 a h' hh') hoff h hh

/-- **`lem:general-star`(f) for the actual features, `‖𝓕‖² ≤ 1 + λ_max(N)`**. -/
theorem features_synthesis_eigenvalue (hp2 : p ≠ 2) (hp3 : p % 4 = 3) (μ : (U → ZMod p) → ℝ)
    (hμ0 : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1)
    (hinv : ∀ (s c : ZMod p) (x : U → ZMod p), s ≠ 0 → IsSquare s → μ (affLab s c x) = μ x)
    (hinj : ∀ (x : U → ZMod p) (k l : U), μ x ≠ 0 → k ≠ l → x k ≠ x l)
    (𝒮 : Finset (Finset U)) (h𝒮 : ∀ S ∈ 𝒮, S.Nonempty) (N : Matrix (U ⊕ 𝒮) (U ⊕ 𝒮) ℝ)
    (hN : N.IsHermitian) (hN0 : ∀ a b, 0 ≤ N a b)
    (hoff : ∀ a b : U ⊕ 𝒮, a ≠ b → ∀ (h h' : ZMod p → ℂ), meanC h = 0 → meanC h' = 0 →
      ‖∑ x, (μ x : ℂ) * (conj (kerMap (featKer 𝒮 a) h x) * kerMap (featKer 𝒮 b) h' x)‖ ≤
        N a b * Real.sqrt (l2sq h) * Real.sqrt (l2sq h'))
    (h : U ⊕ 𝒮 → ZMod p → ℂ) (hh : ∀ a, meanC (h a) = 0) :
    ∑ x, μ x * ‖∑ a, kerMap (featKer 𝒮 a) (h a) x‖ ^ 2 ≤
      (1 + ⨆ i, hN.eigenvalues i) * ∑ a, l2sq (h a) :=
  features_synthesis hp2 hp3 μ hμ0 hμ1 hinv hinj 𝒮 h𝒮 (fun a b => N a b) hN0
    (fun t _ => quad_le_eigenvalue_sup N hN t) hoff h hh

/-! ## The entries of `N` from (c) and (d) -/

/-- **The star–star entry from (c)**: for nonempty supports `S ≠ T` in `𝒮` and a pivot
`j ∈ S△T` with density `D_j`, `|⟨F_S h, F_T h'⟩_μ| ≤ N_ST ‖h‖ ‖h'‖` with
`N_ST = ([a_d + (c + (k − 1)(l − 1))q]² + q(D_j − 1))^{1/2}/(1 − q)`
(the right side of `eq:star-cross-bound`). -/
theorem feat_star_star_entry (hp2 : p ≠ 2) (hp3 : p % 4 = 3)
    (hW : Labellings.WeilBound (ZMod p)) (μ : (U → ZMod p) → ℝ) (hμ0 : ∀ x, 0 ≤ μ x)
    (hμ1 : ∑ x, μ x = 1)
    (hinv : ∀ (s c : ZMod p) (x : U → ZMod p), s ≠ 0 → IsSquare s → μ (affLab s c x) = μ x)
    (hinj : ∀ (x : U → ZMod p) (k l : U), μ x ≠ 0 → k ≠ l → x k ≠ x l)
    (𝒮 : Finset (Finset U)) (S T : 𝒮) (hS : S.1.Nonempty) (hT : T.1.Nonempty)
    (hST : S.1 ≠ T.1) {j : U} (hj : j ∈ S.1 ∆ T.1) {D : ℝ}
    (hD : ∀ x t, μ x ≠ 0 → condLaw μ j x t ≤ D / p) (h h' : ZMod p → ℂ) (hh' : meanC h' = 0) :
    ‖∑ x, (μ x : ℂ) * (conj (kerMap (featKer 𝒮 (Sum.inr S)) h x) *
        kerMap (featKer 𝒮 (Sum.inr T)) h' x)‖ ≤
      Real.sqrt (((aConst p (S.1 ∆ T.1).card + (((S.1 ∩ T.1).card : ℝ) +
        ((S.1.card : ℝ) - 1) * ((T.1.card : ℝ) - 1)) * (p : ℝ)⁻¹) ^ 2 +
          (p : ℝ)⁻¹ * (D - 1)) / (1 - (p : ℝ)⁻¹) ^ 2) *
        Real.sqrt (l2sq h) * Real.sqrt (l2sq h') := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  apply entry_of_gram μ _ _ _ h h' hh'
  intro g hg
  have e : gramOp μ (featKer 𝒮 (Sum.inr S)) (featKer 𝒮 (Sum.inr T)) g =
      fun a => (((rp p)⁻¹ * (rp p)⁻¹ : ℝ) : ℂ) * gramOp μ (starKer S.1) (starKer T.1) g a :=
    funext fun a => gramOp_smul μ (rp p)⁻¹ (rp p)⁻¹ (starKer S.1) (starKer T.1) g a
  rw [e, l2sq_const_mul, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  have hb := star_pivot_bound hp2 hp3 hW μ hμ0 hμ1 hinv hinj hS hT hST hj hD g hg
  have hrp : (rp p)⁻¹ * (rp p)⁻¹ = (p : ℝ) := by
    rw [← mul_inv, ← sq, rp_sq, inv_inv]
  rw [hrp]
  refine (mul_le_mul_of_nonneg_left hb (by positivity)).trans (le_of_eq ?_)
  have hq1 : (1 : ℝ) - (p : ℝ)⁻¹ ≠ 0 := by
    have : (p : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ (by exact_mod_cast (Fact.out : p.Prime).one_lt)
    linarith
  field_simp

/-- **The singleton–star entry from (d), `i ∉ S`**:
`|⟨F_i h, F_S h'⟩_μ| ≤ (r²(1 + (k − 1)r)² + k²q)^{1/2}/(1 − q) ‖h‖ ‖h'‖`. -/
theorem feat_vert_star_out_entry (hp2 : p ≠ 2) (hp3 : p % 4 = 3)
    (hW : Labellings.WeilBound (ZMod p)) (μ : (U → ZMod p) → ℝ) (hμ0 : ∀ x, 0 ≤ μ x)
    (hμ1 : ∑ x, μ x = 1)
    (hinv : ∀ (s c : ZMod p) (x : U → ZMod p), s ≠ 0 → IsSquare s → μ (affLab s c x) = μ x)
    (hinj : ∀ (x : U → ZMod p) (k l : U), μ x ≠ 0 → k ≠ l → x k ≠ x l)
    (𝒮 : Finset (Finset U)) (i : U) (S : 𝒮) (hS : S.1.Nonempty) (hi : i ∉ S.1)
    (h h' : ZMod p → ℂ) (hh' : meanC h' = 0) :
    ‖∑ x, (μ x : ℂ) * (conj (kerMap (featKer 𝒮 (Sum.inl i)) h x) *
        kerMap (featKer 𝒮 (Sum.inr S)) h' x)‖ ≤
      Real.sqrt ((rp p ^ 2 * (1 + ((S.1.card : ℝ) - 1) * rp p) ^ 2 +
        (S.1.card : ℝ) ^ 2 * (p : ℝ)⁻¹) / (1 - (p : ℝ)⁻¹) ^ 2) *
        Real.sqrt (l2sq h) * Real.sqrt (l2sq h') := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  apply entry_of_gram μ _ _ _ h h' hh'
  intro g hg
  have e : gramOp μ (featKer 𝒮 (Sum.inl i)) (featKer 𝒮 (Sum.inr S)) g =
      fun a => (((1 : ℝ) * (rp p)⁻¹ : ℝ) : ℂ) * gramOp μ (vertKer i) (starKer S.1) g a := by
    funext a
    rw [← gramOp_smul μ 1 (rp p)⁻¹ (vertKer i) (starKer S.1) g a]
    show gramOp μ (vertKer i) (fun x b => (rp p)⁻¹ * starKer S.1 x b) g a = _
    congr 1
    funext y b
    rw [one_mul]
  rw [e, l2sq_const_mul, Complex.norm_real, Real.norm_eq_abs, sq_abs, one_mul, inv_pow, rp_sq,
    inv_inv]
  have hb := vert_star_out_bound hp2 hp3 hW μ hμ0 hμ1 hinv hinj hS hi g hg
  rw [rp_sq] at hb
  refine (mul_le_mul_of_nonneg_left hb hp0.le).trans (le_of_eq ?_)
  field_simp

/-- **The singleton–star entry from (d), `i ∈ S`, `|S| ≥ 2`**:
`|⟨F_i h, F_S h'⟩_μ| ≤ (q((k − 1)r)² + (a_{k−1} + q)²)^{1/2}/(1 − q) ‖h‖ ‖h'‖`; for `k = 3` and
`k ≥ 4` this is `2√2 q/(1 − q)` and `((k − 1)²q² + ((k − 2)r + q)²)^{1/2}/(1 − q)`
(`vert_star_three_bound`, `vert_star_large_bound`). -/
theorem feat_vert_star_mem_entry (hp2 : p ≠ 2) (hp3 : p % 4 = 3)
    (hW : Labellings.WeilBound (ZMod p)) (μ : (U → ZMod p) → ℝ) (hμ0 : ∀ x, 0 ≤ μ x)
    (hμ1 : ∑ x, μ x = 1)
    (hinv : ∀ (s c : ZMod p) (x : U → ZMod p), s ≠ 0 → IsSquare s → μ (affLab s c x) = μ x)
    (hinj : ∀ (x : U → ZMod p) (k l : U), μ x ≠ 0 → k ≠ l → x k ≠ x l)
    (𝒮 : Finset (Finset U)) (i : U) (S : 𝒮) (hS2 : 2 ≤ S.1.card) (hi : i ∈ S.1)
    (h h' : ZMod p → ℂ) (hh' : meanC h' = 0) :
    ‖∑ x, (μ x : ℂ) * (conj (kerMap (featKer 𝒮 (Sum.inl i)) h x) *
        kerMap (featKer 𝒮 (Sum.inr S)) h' x)‖ ≤
      Real.sqrt (((p : ℝ)⁻¹ * (((S.1.card : ℝ) - 1) * rp p) ^ 2 +
        (aConst p (S.1.card - 1) + (p : ℝ)⁻¹) ^ 2) / (1 - (p : ℝ)⁻¹) ^ 2) *
        Real.sqrt (l2sq h) * Real.sqrt (l2sq h') := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  apply entry_of_gram μ _ _ _ h h' hh'
  intro g hg
  have e : gramOp μ (featKer 𝒮 (Sum.inl i)) (featKer 𝒮 (Sum.inr S)) g =
      fun a => (((1 : ℝ) * (rp p)⁻¹ : ℝ) : ℂ) * gramOp μ (vertKer i) (starKer S.1) g a := by
    funext a
    rw [← gramOp_smul μ 1 (rp p)⁻¹ (vertKer i) (starKer S.1) g a]
    show gramOp μ (vertKer i) (fun x b => (rp p)⁻¹ * starKer S.1 x b) g a = _
    congr 1
    funext y b
    rw [one_mul]
  rw [e, l2sq_const_mul, Complex.norm_real, Real.norm_eq_abs, sq_abs, one_mul, inv_pow, rp_sq,
    inv_inv]
  have hb := vert_star_mem_bound hp2 hp3 hW μ hμ0 hμ1 hinv hinj hS2 hi g hg
  refine (mul_le_mul_of_nonneg_left hb hp0.le).trans (le_of_eq ?_)
  field_simp

/-- **The singleton–singleton entry from (d)** (WP-K's `vert_cross_bound`): for `i ≠ j`,
`|⟨F_i h, F_j h'⟩_μ| ≤ r√(1 + q)/(1 − q) ‖h‖ ‖h'‖`. -/
theorem feat_vert_vert_entry (hp2 : p ≠ 2) (hp3 : p % 4 = 3) (μ : (U → ZMod p) → ℝ)
    (hμ0 : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1)
    (hinv : ∀ (s c : ZMod p) (x : U → ZMod p), s ≠ 0 → IsSquare s → μ (affLab s c x) = μ x)
    (hinj : ∀ (x : U → ZMod p) (k l : U), μ x ≠ 0 → k ≠ l → x k ≠ x l)
    (𝒮 : Finset (Finset U)) {i j : U} (hij : i ≠ j) (h h' : ZMod p → ℂ) (hh' : meanC h' = 0) :
    ‖∑ x, (μ x : ℂ) * (conj (kerMap (featKer 𝒮 (Sum.inl i)) h x) *
        kerMap (featKer 𝒮 (Sum.inl j)) h' x)‖ ≤
      Real.sqrt ((p : ℝ)⁻¹ * (1 + (p : ℝ)⁻¹) / (1 - (p : ℝ)⁻¹) ^ 2) *
        Real.sqrt (l2sq h) * Real.sqrt (l2sq h') :=
  entry_of_gram μ _ _ (fun g hg => vert_cross_bound hp2 hp3 μ hμ0 hμ1 hinv hinj hij g hg)
    h h' hh'

/-- **The singleton–star entry from (d), `i ∈ S`, `|S| = 2`** (WP-K's `vert_star_pair_bound`):
for `S = {i, j}`, `|⟨F_i h, F_S h'⟩_μ| ≤ q√(1 + q)/(1 − q) ‖h‖ ‖h'‖`. -/
theorem feat_vert_star_pair_entry (hp2 : p ≠ 2) (hp3 : p % 4 = 3) (μ : (U → ZMod p) → ℝ)
    (hμ0 : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1)
    (hinv : ∀ (s c : ZMod p) (x : U → ZMod p), s ≠ 0 → IsSquare s → μ (affLab s c x) = μ x)
    (hinj : ∀ (x : U → ZMod p) (k l : U), μ x ≠ 0 → k ≠ l → x k ≠ x l)
    (𝒮 : Finset (Finset U)) {i j : U} (hij : i ≠ j) (S : 𝒮) (hS : S.1 = {i, j})
    (h h' : ZMod p → ℂ) (hh' : meanC h' = 0) :
    ‖∑ x, (μ x : ℂ) * (conj (kerMap (featKer 𝒮 (Sum.inl i)) h x) *
        kerMap (featKer 𝒮 (Sum.inr S)) h' x)‖ ≤
      Real.sqrt ((p : ℝ)⁻¹ ^ 2 * (1 + (p : ℝ)⁻¹) / (1 - (p : ℝ)⁻¹) ^ 2) *
        Real.sqrt (l2sq h) * Real.sqrt (l2sq h') := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  apply entry_of_gram μ _ _ _ h h' hh'
  intro g hg
  have e : gramOp μ (featKer 𝒮 (Sum.inl i)) (featKer 𝒮 (Sum.inr S)) g =
      fun a => (((1 : ℝ) * (rp p)⁻¹ : ℝ) : ℂ) * gramOp μ (vertKer i) (starKer S.1) g a := by
    funext a
    rw [← gramOp_smul μ 1 (rp p)⁻¹ (vertKer i) (starKer S.1) g a]
    show gramOp μ (vertKer i) (fun x b => (rp p)⁻¹ * starKer S.1 x b) g a = _
    congr 1
    funext y b
    rw [one_mul]
  rw [e, l2sq_const_mul, Complex.norm_real, Real.norm_eq_abs, sq_abs, one_mul, inv_pow, rp_sq,
    inv_inv]
  have hb := vert_star_pair_bound hp2 hp3 μ hμ0 hμ1 hinv hinj hij g hg
  rw [← hS] at hb
  refine (mul_le_mul_of_nonneg_left hb hp0.le).trans (le_of_eq ?_)
  field_simp

end Sarkozy.SpectralD
