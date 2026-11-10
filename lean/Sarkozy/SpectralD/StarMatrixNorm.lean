module

public import Sarkozy.SpectralD.StarMatrix

@[expose] public section

/-!
# The complete star matrix, II: the block matrix and the norm bound (`cor:star-matrix`)

`paper/sections/14_spectral.tex`, `cor:star-matrix`. Notation of `Sarkozy.SpectralD.StarMatrix`.
`Φ̂ = C/r` (`phiHat`). For an index set `ι` and real matrices `M₀`, `M₁` the block operator
`M(Φ̂) = M₀ ⊗ I + M₁ ⊗ Φ̂` on `H^ι` has the bilinear form `blockForm M₀ M₁ u v`, and
`M(i) = M₀ + i M₁` (`matI`).

* `norm_blockForm_le` (`p ≡ 3 (mod 4)`): `|⟨u, M(Φ̂) v⟩| ≤ ‖M(i)‖ |u| |v|`. On the mode `ξ ≠ 0`,
  `Φ̂` acts as `χ(ξ)ε_G ∈ {±i}`, so `M(Φ̂)` acts as `M(i)` or `M(−i) = \overline{M(i)}`, which
  have the same norm (`normLe_conj`); this is `‖M(Φ̂)‖ = ‖M(i)‖`.
* `starPart_factor`: the factorisation of `starPart_compress` in block form,
  `⟨P₀g, K_st P₀f⟩_μ = r ⟨F^*g, M(Φ̂) F^*f⟩`, on the features `F_α`, `α ∈ U ⊔ 𝒮` (`Feat`),
  `F_i = V_i`, `F_S = W_S/r` (kernels `featKer`, adjoints `featAdj`), with the block matrix of
  `cor:star-matrix` (`starM0`, `starM1`: singleton block `d ⊗ Φ̂`, row `i` column `S` entry
  `(−1)^{|S|} L_iS`, row `S` column `j` entry `R_Sj`, zero between supports).
* `sum_l2sq_adj_le`: the dual synthesis bound `∑_α ‖F_α^* g‖² ≤ ‖F‖² ‖g‖²_μ`.
* **`starPart_norm_le`** (the norm claim of `cor:star-matrix`):
  `|⟨P₀g, K_st P₀f⟩_μ| ≤ r ‖F‖² ‖M(i)‖ ‖g‖_μ ‖f‖_μ`, with `‖F‖² ≤ Fsq` (the synthesis bound, a
  hypothesis here; `lem:general-star`(f) supplies it) and `‖M(i)‖ ≤ λ` (`NormLe`).
* `starPart_norm_le_rowsum`: the same with `‖F‖² ≤ 1 + ρ` from `SpectralC.synthesis_bound`; the
  diagonal Grams are discharged here (`V_i` is an isometry, `W_S^*W_S ⪯ qI` by
  `lem:general-star`(a), `star_diagonal`), so the remaining hypotheses are the off-diagonal Gram
  bounds `‖F_α^*F_β‖ ≤ N_αβ` with row sums at most `ρ`.
* `softStar_factor`, `softStar_norm_le`: the soft kernel `K_D`; `softStar_sub_norm_le`: the
  difference of two soft kernels in one synthesis, with the difference of their matrices;
  `starPart_subset`: the synthesis may be restricted to the supports whose coefficients do not
  vanish; `softM_hermitian`: for antisymmetric `D` (the remark after the corollary) `M(i)` is
  Hermitian.
* `symBil_factor`, `symBil_norm_le`: the symmetric part `(X + X^*)/2` of the compressed star part
  is `r F Sym M(Φ̂) F^*`, with `Sym M(i) = matI ((M₀ + M₀ᵀ)/2) ((M₁ − M₁ᵀ)/2)`; the skew part
  `(X − X^*)/2` is `skewBil_factor`, `skewBil_norm_le`, with
  `Skew M(i) = matI ((M₀ − M₀ᵀ)/2) ((M₁ + M₁ᵀ)/2)` (here `Φ̂^* = −Φ̂`, `p ≡ 3 (mod 4)`).

New material for this paper.
-/

namespace Sarkozy.SpectralD.StarMatrix

open Finset Complex Sarkozy.Characters Sarkozy.SpectralC
open scoped BigOperators ComplexConjugate

variable {p : ℕ} [Fact p.Prime]

/-! ## The block operator `M(Φ̂)` -/

/-- `Φ̂ = C/r`, the normalized Paley operator. -/
noncomputable def phiHat (h : ZMod p → ℂ) (a : ZMod p) : ℂ := ((rp p : ℝ) : ℂ)⁻¹ * gaussOp h a

section Block

variable {ι : Type*} [Fintype ι]

/-- The bilinear form of the block operator `M(Φ̂) = M₀ ⊗ I + M₁ ⊗ Φ̂` on `H^ι`:
`⟨u, M(Φ̂) v⟩ = ∑_{a,b} ⟨u_a, M₀_{ab} v_b + M₁_{ab} Φ̂ v_b⟩`. -/
noncomputable def blockForm (M0 M1 : ι → ι → ℝ) (u v : ι → ZMod p → ℂ) : ℂ :=
  ∑ a, ∑ b, ip (u a) (fun t => (M0 a b : ℂ) * v b t + (M1 a b : ℂ) * phiHat (v b) t)

/-- `M(i) = M₀ + i M₁`. -/
noncomputable def matI (M0 M1 : ι → ι → ℝ) (a b : ι) : ℂ := (M0 a b : ℂ) + I * (M1 a b : ℂ)

lemma fcoef_smul (c : ℂ) (f : ZMod p → ℂ) (ξ : ZMod p) :
    fcoef (fun t => c * f t) ξ = c * fcoef f ξ := by
  unfold fcoef ip
  simp only [mul_sum]
  exact sum_congr rfl fun a _ => by ring

lemma fcoef_lin (c d : ℂ) (f g : ZMod p → ℂ) (ξ : ZMod p) :
    fcoef (fun t => c * f t + d * g t) ξ = c * fcoef f ξ + d * fcoef g ξ := by
  unfold fcoef ip
  have : ∑ a, conj (ech ξ a) * (c * f a + d * g a) =
      c * ∑ a, conj (ech ξ a) * f a + d * ∑ a, conj (ech ξ a) * g a := by
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun a _ => by ring
  rw [this]
  ring

/-- `\widehat{Φ̂h}(ξ) = χ(ξ) ε_G ĥ(ξ)`. -/
lemma fcoef_phiHat (hp2 : p ≠ 2) (h : ZMod p → ℂ) (ξ : ZMod p) :
    fcoef (phiHat h) ξ = chiC p ξ * epsG p * fcoef h ξ := by
  have e : phiHat h = fun a => ((rp p : ℝ) : ℂ)⁻¹ * gaussOp h a := rfl
  rw [e, fcoef_smul, fcoef_gaussOp hp2, gaussEig]
  have := rp_ne_zero (p := p)
  field_simp

/-- The block form on the Fourier modes: `⟨u, M(Φ̂) v⟩ = ∑_ξ û(ξ)^*(M₀ + χ(ξ)ε_G M₁) v̂(ξ)`. -/
theorem blockForm_eq_modes (hp2 : p ≠ 2) (M0 M1 : ι → ι → ℝ) (u v : ι → ZMod p → ℂ) :
    blockForm M0 M1 u v = ∑ ξ, bform (fun a b => (M0 a b : ℂ) + chiC p ξ * epsG p * (M1 a b : ℂ))
      (fun a => fcoef (u a) ξ) (fun b => fcoef (v b) ξ) := by
  unfold blockForm bform
  have h1 : ∀ a b, ip (u a) (fun t => (M0 a b : ℂ) * v b t + (M1 a b : ℂ) * phiHat (v b) t) =
      ∑ ξ, conj (fcoef (u a) ξ) * ((M0 a b : ℂ) + chiC p ξ * epsG p * (M1 a b : ℂ)) *
        fcoef (v b) ξ := by
    intro a b
    rw [ip_eq_sum_fcoef]
    refine sum_congr rfl fun ξ _ => ?_
    rw [fcoef_lin, fcoef_phiHat hp2]
    ring
  simp_rw [h1]
  conv_lhs => arg 2; ext a; rw [Finset.sum_comm]
  rw [Finset.sum_comm]

lemma bform_conj (M : ι → ι → ℂ) (w z : ι → ℂ) :
    bform (fun a b => conj (M a b)) w z =
      conj (bform M (fun k => conj (w k)) (fun l => conj (z l))) := by
  unfold bform
  rw [map_sum]
  refine sum_congr rfl fun k _ => ?_
  rw [map_sum]
  refine sum_congr rfl fun l _ => ?_
  simp only [map_mul, Complex.conj_conj]

lemma vnorm_conj (w : ι → ℂ) : vnorm (fun k => conj (w k)) = vnorm w := by
  unfold vnorm
  congr 1
  exact sum_congr rfl fun k _ => by rw [Complex.norm_conj]

/-- `‖\overline{M}‖ = ‖M‖`. -/
theorem normLe_conj {M : ι → ι → ℂ} {lam : ℝ} (h : NormLe M lam) :
    NormLe (fun a b => conj (M a b)) lam := by
  intro w z
  calc ‖bform (fun a b => conj (M a b)) w z‖
      = ‖bform M (fun k => conj (w k)) (fun l => conj (z l))‖ := by
        rw [bform_conj, Complex.norm_conj]
    _ ≤ lam * vnorm (fun k => conj (w k)) * vnorm (fun l => conj (z l)) := h _ _
    _ = lam * vnorm w * vnorm z := by rw [vnorm_conj, vnorm_conj]

lemma sum_vnorm_fcoef_sq (w : ι → ZMod p → ℂ) :
    ∑ ξ, vnorm (fun a => fcoef (w a) ξ) ^ 2 = ∑ a, l2sq (w a) := by
  simp_rw [vnorm_sq]
  rw [Finset.sum_comm]
  exact sum_congr rfl fun a _ => (l2sq_eq_sum_fcoef (w a)).symm

/-- **The norm of the block operator** (`cor:star-matrix`, `p ≡ 3 (mod 4)`): if `‖M(i)‖ ≤ λ`,
then `|⟨u, M(Φ̂) v⟩| ≤ λ |u| |v|` for `u, v ∈ H^ι`, `|u|² = ∑_a ‖u_a‖²`. That is,
`‖M(Φ̂)‖ ≤ ‖M(i)‖`. -/
theorem norm_blockForm_le (hp2 : p ≠ 2) (hp3 : p % 4 = 3) (M0 M1 : ι → ι → ℝ) {lam : ℝ}
    (hlam : 0 ≤ lam) (hM : NormLe (matI M0 M1) lam) (u v : ι → ZMod p → ℂ)
    (hu : ∀ a, meanC (u a) = 0) :
    ‖blockForm M0 M1 u v‖ ≤ lam * √(∑ a, l2sq (u a)) * √(∑ b, l2sq (v b)) := by
  rw [blockForm_eq_modes hp2]
  have hmode : ∀ ξ : ZMod p,
      ‖bform (fun a b => (M0 a b : ℂ) + chiC p ξ * epsG p * (M1 a b : ℂ))
        (fun a => fcoef (u a) ξ) (fun b => fcoef (v b) ξ)‖ ≤
        lam * vnorm (fun a => fcoef (u a) ξ) * vnorm (fun b => fcoef (v b) ξ) := by
    intro ξ
    by_cases hξ : ξ = 0
    · have h0 : (fun a => fcoef (u a) ξ) = fun _ => 0 := by
        funext a
        rw [hξ, fcoef_zero]
        exact hu a
      rw [h0]
      have hb : bform (fun a b => (M0 a b : ℂ) + chiC p ξ * epsG p * (M1 a b : ℂ))
          (fun _ => (0 : ℂ)) (fun b => fcoef (v b) ξ) = 0 := by
        unfold bform
        simp
      rw [hb, norm_zero]
      have hv0 : vnorm (fun _ : ι => (0 : ℂ)) = 0 := by unfold vnorm; simp
      rw [hv0, mul_zero, zero_mul]
    · have hχ : chiC p ξ = 1 ∨ chiC p ξ = -1 := by
        rw [chiC_apply]
        rcases quadraticChar_dichotomy hξ with h | h <;> rw [h] <;> simp
      have hσ : chiC p ξ * epsG p = I ∨ chiC p ξ * epsG p = -I := by
        rcases (epsG_cases hp2).2 hp3 with he | he <;> rcases hχ with hc | hc <;>
          rw [hc, he] <;> simp
      rcases hσ with h | h
      · rw [h]
        exact hM _ _
      · rw [h]
        have e : (fun a b => (M0 a b : ℂ) + -I * (M1 a b : ℂ)) =
            fun a b => conj (matI M0 M1 a b) := by
          funext a b
          unfold matI
          rw [map_add, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, Complex.conj_I]
        rw [e]
        exact normLe_conj hM _ _
  calc ‖∑ ξ, bform (fun a b => (M0 a b : ℂ) + chiC p ξ * epsG p * (M1 a b : ℂ))
        (fun a => fcoef (u a) ξ) (fun b => fcoef (v b) ξ)‖
      ≤ ∑ ξ, ‖bform (fun a b => (M0 a b : ℂ) + chiC p ξ * epsG p * (M1 a b : ℂ))
        (fun a => fcoef (u a) ξ) (fun b => fcoef (v b) ξ)‖ := norm_sum_le _ _
    _ ≤ ∑ ξ, lam * vnorm (fun a => fcoef (u a) ξ) * vnorm (fun b => fcoef (v b) ξ) :=
        sum_le_sum fun ξ _ => hmode ξ
    _ = lam * ∑ ξ, vnorm (fun a => fcoef (u a) ξ) * vnorm (fun b => fcoef (v b) ξ) := by
        rw [mul_sum]
        exact sum_congr rfl fun ξ _ => by ring
    _ ≤ lam * (√(∑ ξ, vnorm (fun a => fcoef (u a) ξ) ^ 2) *
          √(∑ ξ, vnorm (fun b => fcoef (v b) ξ) ^ 2)) :=
        mul_le_mul_of_nonneg_left (Real.sum_mul_le_sqrt_mul_sqrt _ _ _) hlam
    _ = lam * √(∑ a, l2sq (u a)) * √(∑ b, l2sq (v b)) := by
        rw [sum_vnorm_fcoef_sq u, sum_vnorm_fcoef_sq v]
        ring

/-! ## The dual synthesis bound -/

/-- **The dual synthesis bound**: if the features `F_α = kerMap (Y α)` have adjoints `A_α g` on `H`
(`⟨F_α h, g⟩_ν = ⟨h, A_α g⟩`) and `‖∑_α F_α h_α‖² ≤ Fsq ∑_α ‖h_α‖²` (that is `‖F‖² ≤ Fsq`), then
`∑_α ‖A_α g‖² ≤ Fsq ‖g‖²_ν`. -/
theorem sum_l2sq_adj_le {𝒴 : Type*} [Fintype 𝒴] (ν : 𝒴 → ℝ) (hν0 : ∀ y, 0 ≤ ν y)
    (Y : ι → 𝒴 → ZMod p → ℝ) (A : ι → ZMod p → ℂ) (g : 𝒴 → ℂ) {Fsq : ℝ} (hFsq : 0 ≤ Fsq)
    (hA0 : ∀ a, meanC (A a) = 0)
    (hadj : ∀ a, ∀ h : ZMod p → ℂ, meanC h = 0 →
      ∑ y, (ν y : ℂ) * (conj (kerMap (Y a) h y) * g y) = ip h (A a))
    (hF : ∀ h : ι → ZMod p → ℂ, (∀ a, meanC (h a) = 0) →
      ∑ y, ν y * ‖∑ a, kerMap (Y a) (h a) y‖ ^ 2 ≤ Fsq * ∑ a, l2sq (h a)) :
    ∑ a, l2sq (A a) ≤ Fsq * ∑ y, ν y * ‖g y‖ ^ 2 := by
  set T := ∑ a, l2sq (A a) with hT
  set G := ∑ y, ν y * ‖g y‖ ^ 2 with hG
  set Φ : 𝒴 → ℂ := fun y => ∑ a, kerMap (Y a) (A a) y with hΦ
  have hT0 : 0 ≤ T := sum_nonneg fun a _ => l2sq_nonneg _
  have hG0 : 0 ≤ G := sum_nonneg fun y _ => mul_nonneg (hν0 y) (sq_nonneg _)
  have hTeq : (T : ℂ) = ∑ y, (ν y : ℂ) * (conj (Φ y) * g y) := by
    have e : ∀ a, (l2sq (A a) : ℂ) = ∑ y, (ν y : ℂ) * (conj (kerMap (Y a) (A a) y) * g y) := by
      intro a
      rw [hadj a (A a) (hA0 a), l2sq_eq_re_ip]
    rw [hT]
    push_cast
    rw [sum_congr rfl fun a _ => e a, sum_comm]
    refine sum_congr rfl fun y _ => ?_
    simp only [hΦ, map_sum, sum_mul, mul_sum]
  have h1 : T ≤ ∑ y, ν y * (‖Φ y‖ * ‖g y‖) := by
    have e : T = ‖(T : ℂ)‖ := by rw [Complex.norm_real, Real.norm_of_nonneg hT0]
    rw [e, hTeq]
    refine (norm_sum_le _ _).trans (le_of_eq (sum_congr rfl fun y _ => ?_))
    rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_of_nonneg (hν0 y)]
  have h2 : ∑ y, ν y * (‖Φ y‖ * ‖g y‖) ≤ √(∑ y, ν y * ‖Φ y‖ ^ 2) * √G := by
    have h := Real.sum_sqrt_mul_sqrt_le univ (f := fun y => ν y * ‖Φ y‖ ^ 2)
      (g := fun y => ν y * ‖g y‖ ^ 2) (fun y => mul_nonneg (hν0 y) (sq_nonneg _))
      (fun y => mul_nonneg (hν0 y) (sq_nonneg _))
    refine le_of_eq_of_le (sum_congr rfl fun y _ => ?_) h
    rw [Real.sqrt_mul (hν0 y), Real.sqrt_mul (hν0 y), Real.sqrt_sq (norm_nonneg _),
      Real.sqrt_sq (norm_nonneg _)]
    have := Real.mul_self_sqrt (hν0 y)
    calc ν y * (‖Φ y‖ * ‖g y‖) = (√(ν y) * √(ν y)) * (‖Φ y‖ * ‖g y‖) := by rw [this]
      _ = √(ν y) * ‖Φ y‖ * (√(ν y) * ‖g y‖) := by ring
  have hΦ2 : ∑ y, ν y * ‖Φ y‖ ^ 2 ≤ Fsq * T := hF A hA0
  have h3 : T ≤ √(Fsq * T) * √G :=
    (h1.trans h2).trans (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hΦ2) (Real.sqrt_nonneg _))
  have h4 : T ^ 2 ≤ Fsq * T * G := by
    have h5 := pow_le_pow_left₀ hT0 h3 2
    rw [mul_pow, Real.sq_sqrt (mul_nonneg hFsq hT0), Real.sq_sqrt hG0] at h5
    exact h5
  rcases hT0.eq_or_lt with h | h
  · rw [← h]; positivity
  · nlinarith

end Block

/-! ## The features and the block matrix of the star part -/

variable {U : Type*} [Fintype U] [DecidableEq U]

/-- The index set `U ⊔ 𝒮` of the features: singletons `i ∈ U` and supports `S ∈ 𝒮`. -/
abbrev Feat (U : Type*) (𝒮 : Finset (Finset U)) := U ⊕ {S : Finset U // S ∈ 𝒮}

/-- The kernels of the features `F_i = V_i` and `F_S = W_S/r`. -/
noncomputable def featKer (𝒮 : Finset (Finset U)) : Feat U 𝒮 → (U → ZMod p) → ZMod p → ℝ
  | Sum.inl i => vertKer i
  | Sum.inr S => fun x a => (rp p)⁻¹ * starKer S.1 x a

/-- The adjoints `F_i^* g = V_i^* g` and `F_S^* g = W_S^* g/r` on `H`. -/
noncomputable def featAdj (μ : (U → ZMod p) → ℝ) (𝒮 : Finset (Finset U))
    (g : (U → ZMod p) → ℂ) : Feat U 𝒮 → ZMod p → ℂ
  | Sum.inl i => vAdj μ i g
  | Sum.inr S => fun z => ((rp p : ℝ) : ℂ)⁻¹ * wAdj μ S.1 g z

/-- `M₀` of the star matrix: row `i` column `S` entry `(−1)^{|S|} L_iS`, row `S` column `j`
entry `R_Sj`, zero elsewhere. -/
noncomputable def starM0 (L : U → Finset U → ℝ) (R : Finset U → U → ℝ) (𝒮 : Finset (Finset U)) :
    Feat U 𝒮 → Feat U 𝒮 → ℝ
  | Sum.inl _, Sum.inl _ => 0
  | Sum.inl i, Sum.inr S => (-1) ^ S.1.card * L i S.1
  | Sum.inr S, Sum.inl j => R S.1 j
  | Sum.inr _, Sum.inr _ => 0

/-- `M₁` of the star matrix: the singleton block `d` (the coefficient of `Φ̂`). -/
noncomputable def starM1 (d : U → U → ℝ) (𝒮 : Finset (Finset U)) : Feat U 𝒮 → Feat U 𝒮 → ℝ
  | Sum.inl i, Sum.inl j => d i j
  | Sum.inl _, Sum.inr _ => 0
  | Sum.inr _, Sum.inl _ => 0
  | Sum.inr _, Sum.inr _ => 0

lemma meanC_smul (c : ℂ) (h : ZMod p → ℂ) : meanC (fun a => c * h a) = c * meanC h := by
  unfold meanC
  rw [← mul_sum]
  ring

lemma meanC_featAdj (μ : (U → ZMod p) → ℝ) (𝒮 : Finset (Finset U)) (g : (U → ZMod p) → ℂ) :
    ∀ α, meanC (featAdj μ 𝒮 g α) = 0
  | Sum.inl i => meanC_vAdj μ i g
  | Sum.inr S => by
      show meanC (fun z => ((rp p : ℝ) : ℂ)⁻¹ * wAdj μ S.1 g z) = 0
      rw [meanC_smul, meanC_wAdj, mul_zero]

lemma ip_smul_right' (c : ℂ) (f g : ZMod p → ℂ) : ip f (fun a => c * g a) = c * ip f g := by
  unfold ip
  simp only [mul_sum]
  exact sum_congr rfl fun a _ => by ring

lemma kerMap_smul {𝒴 : Type*} (c : ℝ) (Y : 𝒴 → ZMod p → ℝ) (h : ZMod p → ℂ) (y : 𝒴) :
    kerMap (fun y a => c * Y y a) h y = (c : ℂ) * kerMap Y h y := by
  unfold kerMap
  rw [mul_sum]
  exact sum_congr rfl fun a _ => by push_cast; ring

/-- The feature adjoints are the adjoints: `⟨F_α h, g⟩_μ = ⟨h, F_α^* g⟩` for `h ∈ H`. -/
lemma featKer_adjoint (μ : (U → ZMod p) → ℝ) (𝒮 : Finset (Finset U)) (g : (U → ZMod p) → ℂ) :
    ∀ α, ∀ h : ZMod p → ℂ, meanC h = 0 →
      ∑ x, (μ x : ℂ) * (conj (kerMap (featKer 𝒮 α) h x) * g x) = ip h (featAdj μ 𝒮 g α)
  | Sum.inl i => fun h hh => vAdj_adjoint μ i g h hh
  | Sum.inr S => fun h hh => by
      show ∑ x, (μ x : ℂ) * (conj (kerMap (fun x a => (rp p)⁻¹ * starKer S.1 x a) h x) * g x) =
        ip h (fun z => ((rp p : ℝ) : ℂ)⁻¹ * wAdj μ S.1 g z)
      rw [ip_smul_right', ← wAdj_adjoint μ S.1 g h hh, mul_sum]
      refine sum_congr rfl fun x _ => ?_
      rw [kerMap_smul, map_mul, Complex.conj_ofReal]
      push_cast
      ring

lemma ip_add_smul (f g g' : ZMod p → ℂ) (c c' : ℂ) :
    ip f (fun t => c * g t + c' * g' t) = c * ip f g + c' * ip f g' := by
  unfold ip
  have : ∑ a, conj (f a) * (c * g a + c' * g' a) =
      c * ∑ a, conj (f a) * g a + c' * ∑ a, conj (f a) * g' a := by
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    exact sum_congr rfl fun a _ => by ring
  rw [this]
  ring

lemma ip_phiHat (f g : ZMod p → ℂ) :
    ip f (phiHat g) = ((rp p : ℝ) : ℂ)⁻¹ * ip f (gaussOp g) := by
  have e : phiHat g = fun a => ((rp p : ℝ) : ℂ)⁻¹ * gaussOp g a := rfl
  rw [e, ip_smul_right']

/-- **`cor:star-matrix`, the factorisation in block form**: the star part compressed by `P₀` is
`r F M(Φ̂) F^*`, `⟨P₀g, K_st P₀f⟩_μ = r ⟨F^*g, M(Φ̂) F^*f⟩` with the block matrix `starM0`,
`starM1` (`M(Φ̂)`: singleton block `d ⊗ Φ̂`, row `i` column `S` entry `(−1)^{|S|} L_iS`, row `S`
column `j` entry `R_Sj`, each times `I_H`, zero between supports). -/
theorem starPart_factor (hp2 : p ≠ 2) (hp3 : p % 4 = 3) (μ : (U → ZMod p) → ℝ)
    (hμ1 : ∑ x, μ x = 1)
    (hinv : ∀ (s c : ZMod p) (x : U → ZMod p), s ≠ 0 → IsSquare s → μ (affLab s c x) = μ x)
    (d : U → U → ℝ) (L : U → Finset U → ℝ) (R : Finset U → U → ℝ) (𝒮 : Finset (Finset U))
    (g f : (U → ZMod p) → ℂ) :
    bil μ (cent μ g) (starPart d L R 𝒮) (cent μ f) =
      ((rp p : ℝ) : ℂ) * blockForm (starM0 L R 𝒮) (starM1 d 𝒮) (featAdj μ 𝒮 g)
        (featAdj μ 𝒮 f) := by
  rw [starPart_compress hp2 hp3 μ hμ1 hinv]
  have hr : ((rp p : ℝ) : ℂ) ≠ 0 := rp_ne_zero
  have hrc : conj (((rp p : ℝ) : ℂ)⁻¹) = ((rp p : ℝ) : ℂ)⁻¹ := by
    rw [map_inv₀, Complex.conj_ofReal]
  unfold blockForm
  simp only [Fintype.sum_sum_type]
  -- the four blocks
  have b11 : ∀ i j : U, ip (featAdj μ 𝒮 g (Sum.inl i)) (fun t =>
      ((starM0 L R 𝒮 (Sum.inl i) (Sum.inl j) : ℝ) : ℂ) * featAdj μ 𝒮 f (Sum.inl j) t +
        ((starM1 d 𝒮 (Sum.inl i) (Sum.inl j) : ℝ) : ℂ) * phiHat (featAdj μ 𝒮 f (Sum.inl j)) t) =
      ((rp p : ℝ) : ℂ)⁻¹ * ((d i j : ℂ) * ip (vAdj μ i g) (gaussOp (vAdj μ j f))) := by
    intro i j
    simp only [featAdj, starM0, starM1]
    rw [ip_add_smul, ip_phiHat]
    push_cast
    ring
  have b12 : ∀ (i : U) (S : {S : Finset U // S ∈ 𝒮}), ip (featAdj μ 𝒮 g (Sum.inl i)) (fun t =>
      ((starM0 L R 𝒮 (Sum.inl i) (Sum.inr S) : ℝ) : ℂ) * featAdj μ 𝒮 f (Sum.inr S) t +
        ((starM1 d 𝒮 (Sum.inl i) (Sum.inr S) : ℝ) : ℂ) * phiHat (featAdj μ 𝒮 f (Sum.inr S)) t) =
      ((rp p : ℝ) : ℂ)⁻¹ * ((-1 : ℂ) ^ S.1.card * (L i S.1 : ℂ) *
        ip (vAdj μ i g) (wAdj μ S.1 f)) := by
    intro i S
    simp only [featAdj, starM0, starM1]
    rw [ip_add_smul, ip_smul_right']
    push_cast
    ring
  have b21 : ∀ (S : {S : Finset U // S ∈ 𝒮}) (j : U), ip (featAdj μ 𝒮 g (Sum.inr S)) (fun t =>
      ((starM0 L R 𝒮 (Sum.inr S) (Sum.inl j) : ℝ) : ℂ) * featAdj μ 𝒮 f (Sum.inl j) t +
        ((starM1 d 𝒮 (Sum.inr S) (Sum.inl j) : ℝ) : ℂ) * phiHat (featAdj μ 𝒮 f (Sum.inl j)) t) =
      ((rp p : ℝ) : ℂ)⁻¹ * ((R S.1 j : ℂ) * ip (wAdj μ S.1 g) (vAdj μ j f)) := by
    intro S j
    simp only [featAdj, starM0, starM1]
    rw [ip_add_smul, ip_smul_left, hrc]
    push_cast
    ring
  have b22 : ∀ (S T : {S : Finset U // S ∈ 𝒮}), ip (featAdj μ 𝒮 g (Sum.inr S)) (fun t =>
      ((starM0 L R 𝒮 (Sum.inr S) (Sum.inr T) : ℝ) : ℂ) * featAdj μ 𝒮 f (Sum.inr T) t +
        ((starM1 d 𝒮 (Sum.inr S) (Sum.inr T) : ℝ) : ℂ) * phiHat (featAdj μ 𝒮 f (Sum.inr T)) t) =
      0 := by
    intro S T
    simp only [starM0, starM1]
    rw [ip_add_smul]
    push_cast
    ring
  simp only [b11, b12, b21, b22, sum_const_zero, add_zero]
  rw [← sum_coe_sort 𝒮 (fun S => ∑ j, (R S j : ℂ) * ip (wAdj μ S g) (vAdj μ j f))]
  have hL : ∀ i : U, ∑ S ∈ 𝒮, (-1 : ℂ) ^ S.card * (L i S : ℂ) * ip (vAdj μ i g) (wAdj μ S f) =
      ∑ S : {S : Finset U // S ∈ 𝒮}, (-1 : ℂ) ^ S.1.card * (L i S.1 : ℂ) *
        ip (vAdj μ i g) (wAdj μ S.1 f) := fun i =>
    (sum_coe_sort 𝒮 (fun S => (-1 : ℂ) ^ S.card * (L i S : ℂ) * ip (vAdj μ i g) (wAdj μ S f))).symm
  simp only [hL]
  simp only [← mul_sum, ← mul_add]
  rw [mul_inv_cancel_left₀ hr, sum_add_distrib]

/-! ## The norm bound -/

/-- The norm of `r F M(Φ̂) F^*` for any real block matrix: `|r ⟨F^*g, M(Φ̂) F^*f⟩| ≤
r ‖M(i)‖ ‖F‖² ‖g‖_μ ‖f‖_μ`, with `‖M(i)‖ ≤ λ` and `‖F‖² ≤ Fsq`. -/
theorem featForm_norm_le (hp2 : p ≠ 2) (hp3 : p % 4 = 3) (μ : (U → ZMod p) → ℝ)
    (hμ0 : ∀ x, 0 ≤ μ x) (𝒮 : Finset (Finset U)) (M0 M1 : Feat U 𝒮 → Feat U 𝒮 → ℝ)
    {lam Fsq : ℝ} (hlam : 0 ≤ lam) (hFsq : 0 ≤ Fsq) (hM : NormLe (matI M0 M1) lam)
    (hF : ∀ h : Feat U 𝒮 → ZMod p → ℂ, (∀ a, meanC (h a) = 0) →
      ∑ x, μ x * ‖∑ a, kerMap (featKer 𝒮 a) (h a) x‖ ^ 2 ≤ Fsq * ∑ a, l2sq (h a))
    (g f : (U → ZMod p) → ℂ) :
    ‖((rp p : ℝ) : ℂ) * blockForm M0 M1 (featAdj μ 𝒮 g) (featAdj μ 𝒮 f)‖ ≤
      rp p * lam * Fsq * √(∑ x, μ x * ‖g x‖ ^ 2) * √(∑ x, μ x * ‖f x‖ ^ 2) := by
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by unfold rp; positivity)]
  have hb := norm_blockForm_le hp2 hp3 M0 M1 hlam hM (featAdj μ 𝒮 g)
    (featAdj μ 𝒮 f) (meanC_featAdj μ 𝒮 g)
  have hg := sum_l2sq_adj_le μ hμ0 (featKer 𝒮) (featAdj μ 𝒮 g) g hFsq (meanC_featAdj μ 𝒮 g)
    (featKer_adjoint μ 𝒮 g) hF
  have hf := sum_l2sq_adj_le μ hμ0 (featKer 𝒮) (featAdj μ 𝒮 f) f hFsq (meanC_featAdj μ 𝒮 f)
    (featKer_adjoint μ 𝒮 f) hF
  have hr : 0 ≤ rp p := by unfold rp; positivity
  have hG0 : 0 ≤ ∑ x, μ x * ‖g x‖ ^ 2 := sum_nonneg fun x _ => mul_nonneg (hμ0 x) (sq_nonneg _)
  have hF0 : 0 ≤ ∑ x, μ x * ‖f x‖ ^ 2 := sum_nonneg fun x _ => mul_nonneg (hμ0 x) (sq_nonneg _)
  have hsg : √(∑ a, l2sq (featAdj μ 𝒮 g a)) ≤ √Fsq * √(∑ x, μ x * ‖g x‖ ^ 2) := by
    rw [← Real.sqrt_mul hFsq]; exact Real.sqrt_le_sqrt hg
  have hsf : √(∑ a, l2sq (featAdj μ 𝒮 f a)) ≤ √Fsq * √(∑ x, μ x * ‖f x‖ ^ 2) := by
    rw [← Real.sqrt_mul hFsq]; exact Real.sqrt_le_sqrt hf
  have hprod : √(∑ a, l2sq (featAdj μ 𝒮 g a)) * √(∑ a, l2sq (featAdj μ 𝒮 f a)) ≤
      Fsq * √(∑ x, μ x * ‖g x‖ ^ 2) * √(∑ x, μ x * ‖f x‖ ^ 2) := by
    have h1 := mul_le_mul hsg hsf (Real.sqrt_nonneg _) (by positivity)
    have h2 : √Fsq * √(∑ x, μ x * ‖g x‖ ^ 2) * (√Fsq * √(∑ x, μ x * ‖f x‖ ^ 2)) =
        (√Fsq * √Fsq) * √(∑ x, μ x * ‖g x‖ ^ 2) * √(∑ x, μ x * ‖f x‖ ^ 2) := by ring
    rw [h2, Real.mul_self_sqrt hFsq] at h1
    exact h1
  calc rp p * ‖blockForm M0 M1 (featAdj μ 𝒮 g) (featAdj μ 𝒮 f)‖
      ≤ rp p * (lam * √(∑ a, l2sq (featAdj μ 𝒮 g a)) * √(∑ a, l2sq (featAdj μ 𝒮 f a))) :=
        mul_le_mul_of_nonneg_left hb hr
    _ = rp p * lam * (√(∑ a, l2sq (featAdj μ 𝒮 g a)) * √(∑ a, l2sq (featAdj μ 𝒮 f a))) := by
        ring
    _ ≤ rp p * lam * (Fsq * √(∑ x, μ x * ‖g x‖ ^ 2) * √(∑ x, μ x * ‖f x‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left hprod (mul_nonneg hr hlam)
    _ = rp p * lam * Fsq * √(∑ x, μ x * ‖g x‖ ^ 2) * √(∑ x, μ x * ‖f x‖ ^ 2) := by ring

/-- **`cor:star-matrix`, the norm bound**: `‖r F M(Φ̂) F^*‖ ≤ r ‖F‖² ‖M(i)‖`, in bilinear form:
for `p ≡ 3 (mod 4)`, a translation-invariant probability law `μ`, `‖M(i)‖ ≤ λ` (`hM`) and the
synthesis bound `‖F‖² ≤ Fsq` (`hF`, the hypothesis supplied by `lem:general-star`(f)),
`|⟨P₀g, K_st P₀f⟩_μ| ≤ r λ Fsq ‖g‖_μ ‖f‖_μ`. -/
theorem starPart_norm_le (hp2 : p ≠ 2) (hp3 : p % 4 = 3) (μ : (U → ZMod p) → ℝ)
    (hμ0 : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1)
    (hinv : ∀ (s c : ZMod p) (x : U → ZMod p), s ≠ 0 → IsSquare s → μ (affLab s c x) = μ x)
    (d : U → U → ℝ) (L : U → Finset U → ℝ) (R : Finset U → U → ℝ) (𝒮 : Finset (Finset U))
    {lam Fsq : ℝ} (hlam : 0 ≤ lam) (hFsq : 0 ≤ Fsq)
    (hM : NormLe (matI (starM0 L R 𝒮) (starM1 d 𝒮)) lam)
    (hF : ∀ h : Feat U 𝒮 → ZMod p → ℂ, (∀ a, meanC (h a) = 0) →
      ∑ x, μ x * ‖∑ a, kerMap (featKer 𝒮 a) (h a) x‖ ^ 2 ≤ Fsq * ∑ a, l2sq (h a))
    (g f : (U → ZMod p) → ℂ) :
    ‖bil μ (cent μ g) (starPart d L R 𝒮) (cent μ f)‖ ≤
      rp p * lam * Fsq * √(∑ x, μ x * ‖g x‖ ^ 2) * √(∑ x, μ x * ‖f x‖ ^ 2) := by
  rw [starPart_factor hp2 hp3 μ hμ1 hinv]
  exact featForm_norm_le hp2 hp3 μ hμ0 𝒮 _ _ hlam hFsq hM hF g f

/-- The diagonal Grams of the features are at most `I`: `V_i` is an isometry and
`(W_S/r)^*(W_S/r) ⪯ I` (`lem:general-star`(a), `star_diagonal`; supports are nonempty). -/
lemma featKer_diag (hp2 : p ≠ 2) (hp3 : p % 4 = 3) (μ : (U → ZMod p) → ℝ)
    (hμ0 : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1)
    (hinv : ∀ (s c : ZMod p) (x : U → ZMod p), s ≠ 0 → IsSquare s → μ (affLab s c x) = μ x)
    (hinj : ∀ (x : U → ZMod p) (k l : U), μ x ≠ 0 → k ≠ l → x k ≠ x l)
    (𝒮 : Finset (Finset U)) (h𝒮 : ∀ S ∈ 𝒮, S.Nonempty) :
    ∀ (a : Feat U 𝒮) (h : ZMod p → ℂ), meanC h = 0 →
      ∑ x, μ x * ‖kerMap (featKer 𝒮 a) h x‖ ^ 2 ≤ l2sq h
  | Sum.inl i, h, hh => by
      show ∑ x, μ x * ‖kerMap (vertKer i) h x‖ ^ 2 ≤ l2sq h
      have h1 := norm_kerMap_sq μ (vertKer i) h
      have h2 : gramOp μ (vertKer i) (vertKer i) h = h :=
        funext (vert_isometry hp2 μ hμ1 hinv i h hh)
      rw [h2, ← l2sq_eq_re_ip] at h1
      exact le_of_eq (by exact_mod_cast h1)
  | Sum.inr S, h, hh => by
      show ∑ x, μ x * ‖kerMap (fun x a => (rp p)⁻¹ * starKer S.1 x a) h x‖ ^ 2 ≤ l2sq h
      have hT := (star_diagonal hp2 hp3 μ hμ0 hμ1 hinv hinj S.1).1 h hh
      have hα := (star_diagonal hp2 hp3 μ hμ0 hμ1 hinv hinj S.1).2 (h𝒮 S.1 S.2)
      set α := (p : ℝ)⁻¹ * (1 - (S.1.card : ℝ) * (p : ℝ)⁻¹ - ∑ x, μ x * starMean S.1 x ^ 2) /
          (1 - (p : ℝ)⁻¹) with hαdef
      have h1 := norm_kerMap_sq μ (starKer S.1) h
      have h2 : gramOp μ (starKer S.1) (starKer S.1) h = fun a => (α : ℂ) * h a := funext hT
      rw [h2, ip_smul_right', ← l2sq_eq_re_ip] at h1
      have h3 : ∑ x, μ x * ‖kerMap (starKer S.1) h x‖ ^ 2 = α * l2sq h := by exact_mod_cast h1
      have hr2 : ((rp p)⁻¹) ^ 2 = (p : ℝ) := by
        unfold rp
        rw [inv_inv, Real.sq_sqrt (Nat.cast_nonneg p)]
      have hrpos : 0 ≤ (rp p)⁻¹ := by unfold rp; positivity
      have e : ∀ x, μ x * ‖kerMap (fun x a => (rp p)⁻¹ * starKer S.1 x a) h x‖ ^ 2 =
          (p : ℝ) * (μ x * ‖kerMap (starKer S.1) h x‖ ^ 2) := by
        intro x
        rw [kerMap_smul, norm_mul, Complex.norm_real, Real.norm_of_nonneg hrpos, mul_pow, hr2]
        ring
      rw [sum_congr rfl fun x _ => e x, ← mul_sum, h3]
      have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
      have hl : 0 ≤ l2sq h := l2sq_nonneg h
      have hpα : (p : ℝ) * α ≤ 1 := by
        have := mul_le_mul_of_nonneg_left hα hp0.le
        rwa [mul_inv_cancel₀ hp0.ne'] at this
      nlinarith

/-- **`cor:star-matrix` with the row-sum synthesis** (`lem:general-star`(f)): if
`‖F_α^*F_β‖ ≤ N_αβ` for `α ≠ β` (`hoff`, bilinear form; `N` symmetric, nonnegative, off-diagonal
row sums at most `ρ`), then `|⟨P₀g, K_st P₀f⟩_μ| ≤ r ‖M(i)‖ (1 + ρ) ‖g‖_μ ‖f‖_μ`. The diagonal
Grams are discharged by `featKer_diag`; the remaining hypotheses are the off-diagonal Gram bounds
and `‖M(i)‖ ≤ λ`. -/
theorem starPart_norm_le_rowsum (hp2 : p ≠ 2) (hp3 : p % 4 = 3) (μ : (U → ZMod p) → ℝ)
    (hμ0 : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1)
    (hinv : ∀ (s c : ZMod p) (x : U → ZMod p), s ≠ 0 → IsSquare s → μ (affLab s c x) = μ x)
    (hinj : ∀ (x : U → ZMod p) (k l : U), μ x ≠ 0 → k ≠ l → x k ≠ x l)
    (d : U → U → ℝ) (L : U → Finset U → ℝ) (R : Finset U → U → ℝ) (𝒮 : Finset (Finset U))
    (h𝒮 : ∀ S ∈ 𝒮, S.Nonempty) {lam ρ : ℝ} (hlam : 0 ≤ lam) (hρ : 0 ≤ ρ)
    (hM : NormLe (matI (starM0 L R 𝒮) (starM1 d 𝒮)) lam)
    (N : Feat U 𝒮 → Feat U 𝒮 → ℝ) (hN0 : ∀ a b, 0 ≤ N a b) (hNsym : ∀ a b, N a b = N b a)
    (hrow : ∀ a, ∑ b, (if a = b then 0 else N a b) ≤ ρ)
    (hoff : ∀ a b : Feat U 𝒮, a ≠ b → ∀ (h h' : ZMod p → ℂ), meanC h = 0 → meanC h' = 0 →
      ‖∑ x, (μ x : ℂ) * (conj (kerMap (featKer 𝒮 a) h x) * kerMap (featKer 𝒮 b) h' x)‖ ≤
        N a b * Real.sqrt (l2sq h) * Real.sqrt (l2sq h'))
    (g f : (U → ZMod p) → ℂ) :
    ‖bil μ (cent μ g) (starPart d L R 𝒮) (cent μ f)‖ ≤
      rp p * lam * (1 + ρ) * √(∑ x, μ x * ‖g x‖ ^ 2) * √(∑ x, μ x * ‖f x‖ ^ 2) :=
  starPart_norm_le hp2 hp3 μ hμ0 hμ1 hinv d L R 𝒮 hlam (by linarith) hM
    (fun h hh => synthesis_bound μ (featKer 𝒮) N hN0 hNsym hrow
      (featKer_diag hp2 hp3 μ hμ0 hμ1 hinv hinj 𝒮 h𝒮) hoff h hh) g f

/-! ## The soft kernel and the difference of two soft kernels -/

/-- The left-star coefficients of the soft kernel: `∏_{j ∈ S} D_ij`. -/
noncomputable def softL (D : U → U → ℝ) (i : U) (S : Finset U) : ℝ := ∏ j ∈ S, D i j

/-- The right-star coefficients of the soft kernel: `∏_{i ∈ S} D_ij`. -/
noncomputable def softR (D : U → U → ℝ) (S : Finset U) (j : U) : ℝ := ∏ i ∈ S, D i j

/-- **The star matrix `M(i)` of the soft kernel** (`cor:star-matrix`), indexed by `U ⊔ 𝒮`,
`𝒮` the supports: singleton block `i D`, row `i` column `S` entry `(−1)^{|S|} ∏_{j ∈ S} D_ij`,
row `S` column `j` entry `∏_{i ∈ S} D_ij`, zero between supports. -/
noncomputable def softM (D : U → U → ℝ) : Feat U (supports U) → Feat U (supports U) → ℂ :=
  matI (starM0 (softL D) (softR D) (supports U)) (starM1 D (supports U))

lemma softStarPart_eq (D : U → U → ℝ) :
    softStarPart (p := p) D = starPart D (softL D) (softR D) (supports U) := rfl

/-- **`cor:star-matrix` for the soft kernel `K_D`**: the complete star part compressed by `P₀`
is `r F M(Φ̂) F^*`. -/
theorem softStar_factor (hp2 : p ≠ 2) (hp3 : p % 4 = 3) (μ : (U → ZMod p) → ℝ)
    (hμ1 : ∑ x, μ x = 1)
    (hinv : ∀ (s c : ZMod p) (x : U → ZMod p), s ≠ 0 → IsSquare s → μ (affLab s c x) = μ x)
    (D : U → U → ℝ) (g f : (U → ZMod p) → ℂ) :
    bil μ (cent μ g) (softStarPart D) (cent μ f) =
      ((rp p : ℝ) : ℂ) * blockForm (starM0 (softL D) (softR D) (supports U))
        (starM1 D (supports U)) (featAdj μ (supports U) g) (featAdj μ (supports U) f) :=
  starPart_factor hp2 hp3 μ hμ1 hinv D (softL D) (softR D) (supports U) g f

/-- **`cor:star-matrix`, the norm for the soft kernel**:
`‖r F M(Φ̂) F^*‖ ≤ r ‖F‖² ‖M(i)‖`. -/
theorem softStar_norm_le (hp2 : p ≠ 2) (hp3 : p % 4 = 3) (μ : (U → ZMod p) → ℝ)
    (hμ0 : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1)
    (hinv : ∀ (s c : ZMod p) (x : U → ZMod p), s ≠ 0 → IsSquare s → μ (affLab s c x) = μ x)
    (D : U → U → ℝ) {lam Fsq : ℝ} (hlam : 0 ≤ lam) (hFsq : 0 ≤ Fsq)
    (hM : NormLe (softM D) lam)
    (hF : ∀ h : Feat U (supports U) → ZMod p → ℂ, (∀ a, meanC (h a) = 0) →
      ∑ x, μ x * ‖∑ a, kerMap (featKer (supports U) a) (h a) x‖ ^ 2 ≤ Fsq * ∑ a, l2sq (h a))
    (g f : (U → ZMod p) → ℂ) :
    ‖bil μ (cent μ g) (softStarPart D) (cent μ f)‖ ≤
      rp p * lam * Fsq * √(∑ x, μ x * ‖g x‖ ^ 2) * √(∑ x, μ x * ‖f x‖ ^ 2) :=
  starPart_norm_le hp2 hp3 μ hμ0 hμ1 hinv D (softL D) (softR D) (supports U) hlam hFsq hM hF g f

omit [DecidableEq U] in
lemma starPart_sub (d d' : U → U → ℝ) (L L' : U → Finset U → ℝ) (R R' : Finset U → U → ℝ)
    (𝒮 : Finset (Finset U)) (x y : U → ZMod p) :
    starPart d L R 𝒮 x y - starPart d' L' R' 𝒮 x y =
      starPart (fun i j => d i j - d' i j) (fun i S => L i S - L' i S)
        (fun S j => R S j - R' S j) 𝒮 x y := by
  unfold starPart
  simp only [sub_mul, sum_sub_distrib]
  ring

omit [Fintype U] [DecidableEq U] in
lemma matI_sub (L L' : U → Finset U → ℝ) (R R' : Finset U → U → ℝ) (d d' : U → U → ℝ)
    (𝒮 : Finset (Finset U)) :
    matI (starM0 (fun i S => L i S - L' i S) (fun S j => R S j - R' S j) 𝒮)
        (starM1 (fun i j => d i j - d' i j) 𝒮) =
      fun a b => matI (starM0 L R 𝒮) (starM1 d 𝒮) a b - matI (starM0 L' R' 𝒮) (starM1 d' 𝒮) a b := by
  funext a b
  cases a <;> cases b <;> simp only [matI, starM0, starM1] <;> push_cast <;> ring

/-- **`cor:star-matrix`, the difference of two soft kernels** on the same half law: one synthesis
over the supports, and the difference of their matrices. -/
theorem softStar_sub_norm_le (hp2 : p ≠ 2) (hp3 : p % 4 = 3) (μ : (U → ZMod p) → ℝ)
    (hμ0 : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1)
    (hinv : ∀ (s c : ZMod p) (x : U → ZMod p), s ≠ 0 → IsSquare s → μ (affLab s c x) = μ x)
    (D D' : U → U → ℝ) {lam Fsq : ℝ} (hlam : 0 ≤ lam) (hFsq : 0 ≤ Fsq)
    (hM : NormLe (fun a b => softM D a b - softM D' a b) lam)
    (hF : ∀ h : Feat U (supports U) → ZMod p → ℂ, (∀ a, meanC (h a) = 0) →
      ∑ x, μ x * ‖∑ a, kerMap (featKer (supports U) a) (h a) x‖ ^ 2 ≤ Fsq * ∑ a, l2sq (h a))
    (g f : (U → ZMod p) → ℂ) :
    ‖bil μ (cent μ g) (fun x y => softStarPart D x y - softStarPart D' x y) (cent μ f)‖ ≤
      rp p * lam * Fsq * √(∑ x, μ x * ‖g x‖ ^ 2) * √(∑ x, μ x * ‖f x‖ ^ 2) := by
  have e : (fun x y => softStarPart (p := p) D x y - softStarPart D' x y) =
      starPart (fun i j => D i j - D' i j) (fun i S => softL D i S - softL D' i S)
        (fun S j => softR D S j - softR D' S j) (supports U) := by
    funext x y
    rw [softStarPart_eq, softStarPart_eq, starPart_sub]
  rw [e]
  refine starPart_norm_le hp2 hp3 μ hμ0 hμ1 hinv _ _ _ _ hlam hFsq ?_ hF g f
  rw [matI_sub]
  exact hM

omit [DecidableEq U] in
/-- **Restricting the supports**: if the star coefficients vanish on the supports outside `𝒮 ⊆ 𝒯`,
the star part over `𝒯` is the star part over `𝒮` (so the synthesis may use only the sets of
leaves that occur, `cor:star-matrix`). -/
lemma starPart_subset (d : U → U → ℝ) (L : U → Finset U → ℝ) (R : Finset U → U → ℝ)
    {𝒮 𝒯 : Finset (Finset U)} (h : 𝒮 ⊆ 𝒯) (hL : ∀ i, ∀ S ∈ 𝒯, S ∉ 𝒮 → L i S = 0)
    (hR : ∀ S ∈ 𝒯, S ∉ 𝒮 → ∀ j, R S j = 0) (x y : U → ZMod p) :
    starPart d L R 𝒯 x y = starPart d L R 𝒮 x y := by
  unfold starPart
  congr 1
  · congr 1
    refine sum_congr rfl fun i _ => ?_
    exact (sum_subset h fun S hS hS' => by rw [hL i S hS hS', zero_mul]).symm
  · exact (sum_subset h fun S hS hS' => sum_eq_zero fun j _ => by
      rw [hR S hS hS' j, zero_mul]).symm

/-- **The remark after `cor:star-matrix`**: if `D` is antisymmetric (as `Δ^E` for
`p ≡ 3 (mod 4)`), the soft star matrix `M(i)` is Hermitian; its right-star block is the transpose
of its left-star block, `∏_{k ∈ S} D_kj = (−1)^{|S|} ∏_{k ∈ S} D_jk`. -/
theorem softM_hermitian (D : U → U → ℝ) (hD : ∀ i j, D j i = -D i j)
    (a b : Feat U (supports U)) : conj (softM D b a) = softM D a b := by
  rcases a with i | S <;> rcases b with j | T
  · simp only [softM, matI, starM0, starM1, map_add, map_mul, Complex.conj_ofReal,
      Complex.conj_I, hD j i]
    push_cast
    ring
  · simp only [softM, matI, starM0, starM1, softL, softR, Complex.conj_ofReal,
      Complex.ofReal_zero, mul_zero, add_zero]
    congr 1
    rw [Finset.prod_congr rfl fun k _ => hD i k, Finset.prod_neg]
  · simp only [softM, matI, starM0, starM1, softL, softR, Complex.conj_ofReal,
      Complex.ofReal_zero, mul_zero, add_zero]
    congr 1
    rw [Finset.prod_congr rfl fun k _ => hD j k, Finset.prod_neg]
  · simp only [softM, matI, starM0, starM1, Complex.ofReal_zero, mul_zero, add_zero, map_zero]

/-! ## The symmetric and the skew part -/

section SymSkew

variable {ι : Type*} [Fintype ι]

/-- `(M + Mᵀ)/2`. -/
noncomputable def symM (M : ι → ι → ℝ) (a b : ι) : ℝ := (M a b + M b a) / 2

/-- `(M − Mᵀ)/2`. -/
noncomputable def skewM (M : ι → ι → ℝ) (a b : ι) : ℝ := (M a b - M b a) / 2

omit [Fintype ι] in
/-- `matI (symM M₀) (skewM M₁) = Sym M(i) = (M(i) + M(i)^*)/2`. -/
lemma matI_symM (M0 M1 : ι → ι → ℝ) (a b : ι) :
    matI (symM M0) (skewM M1) a b = (matI M0 M1 a b + conj (matI M0 M1 b a)) / 2 := by
  unfold matI symM skewM
  rw [map_add, map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.conj_ofReal]
  push_cast
  ring

omit [Fintype ι] in
/-- `matI (skewM M₀) (symM M₁) = Skew M(i) = (M(i) − M(i)^*)/2`. -/
lemma matI_skewM (M0 M1 : ι → ι → ℝ) (a b : ι) :
    matI (skewM M0) (symM M1) a b = (matI M0 M1 a b - conj (matI M0 M1 b a)) / 2 := by
  unfold matI symM skewM
  rw [map_add, map_mul, Complex.conj_I, Complex.conj_ofReal, Complex.conj_ofReal]
  push_cast
  ring

/-- `χ(−1) = −1` for `p ≡ 3 (mod 4)`. -/
lemma chiC_neg_one_three (hp2 : p ≠ 2) (hp3 : p % 4 = 3) : chiC p (-1) = -1 := by
  rw [chiC_neg_one hp2, ZMod.χ₄_nat_three_mod_four hp3]
  norm_num

/-- `C^* = −C` for `p ≡ 3 (mod 4)`. -/
lemma gaussOpAdj_eq_neg (hp2 : p ≠ 2) (hp3 : p % 4 = 3) (h : ZMod p → ℂ) (a : ZMod p) :
    gaussOpAdj h a = -gaussOp h a := by
  unfold gaussOpAdj gaussOp
  rw [← mul_neg, ← sum_neg_distrib]
  congr 1
  refine sum_congr rfl fun b _ => ?_
  rw [conj_chiC, show a - b = -1 * (b - a) by ring, map_mul, chiC_neg_one_three hp2 hp3]
  ring

/-- `Φ̂^* = −Φ̂` for `p ≡ 3 (mod 4)`: `⟨Φ̂v, u⟩ = −⟨v, Φ̂u⟩`. -/
lemma ip_phiHat_left (hp2 : p ≠ 2) (hp3 : p % 4 = 3) (v u : ZMod p → ℂ) :
    ip (phiHat v) u = -ip v (phiHat u) := by
  have e : phiHat v = fun a => ((rp p : ℝ) : ℂ)⁻¹ * gaussOp v a := rfl
  rw [e, ip_smul_left, ip_phiHat, ← ip_gaussOpAdj,
    show gaussOpAdj u = fun a => -gaussOp u a from funext (gaussOpAdj_eq_neg hp2 hp3 u),
    show (fun a => -gaussOp u a) = fun a => (-1 : ℂ) * gaussOp u a from
      funext fun a => by ring, ip_smul_right', map_inv₀, Complex.conj_ofReal]
  ring

/-- The block form, expanded: `∑_{a,b} (M₀_{ab}⟨u_a, v_b⟩ + M₁_{ab}⟨u_a, Φ̂v_b⟩)`. -/
lemma blockForm_expand (M0 M1 : ι → ι → ℝ) (u v : ι → ZMod p → ℂ) :
    blockForm M0 M1 u v =
      ∑ a, ∑ b, ((M0 a b : ℂ) * ip (u a) (v b) + (M1 a b : ℂ) * ip (u a) (phiHat (v b))) := by
  unfold blockForm
  exact sum_congr rfl fun a _ => sum_congr rfl fun b _ => ip_add_smul _ _ _ _ _

/-- `\overline{⟨u, M(Φ̂) v⟩} = ⟨v, M(Φ̂)^* u⟩` with `M(Φ̂)^* = M₀ᵀ ⊗ I − M₁ᵀ ⊗ Φ̂`
(`Φ̂^* = −Φ̂`, `p ≡ 3 (mod 4)`). -/
lemma blockForm_conj (hp2 : p ≠ 2) (hp3 : p % 4 = 3) (M0 M1 : ι → ι → ℝ)
    (u v : ι → ZMod p → ℂ) :
    conj (blockForm M0 M1 u v) = blockForm (fun a b => M0 b a) (fun a b => -M1 b a) v u := by
  rw [blockForm_expand, blockForm_expand, map_sum, sum_comm]
  refine sum_congr rfl fun b _ => ?_
  rw [map_sum]
  refine sum_congr rfl fun a _ => ?_
  rw [map_add, map_mul, map_mul, Complex.conj_ofReal, Complex.conj_ofReal, conj_ip, conj_ip,
    ip_phiHat_left hp2 hp3]
  push_cast
  ring

lemma blockForm_symm (M0 M1 : ι → ι → ℝ) (u v : ι → ZMod p → ℂ) :
    (blockForm M0 M1 u v + blockForm (fun a b => M0 b a) (fun a b => -M1 b a) u v) / 2 =
      blockForm (symM M0) (skewM M1) u v := by
  rw [blockForm_expand, blockForm_expand, blockForm_expand, ← sum_add_distrib, sum_div]
  refine sum_congr rfl fun a _ => ?_
  rw [← sum_add_distrib, sum_div]
  refine sum_congr rfl fun b _ => ?_
  unfold symM skewM
  push_cast
  ring

lemma blockForm_skew (M0 M1 : ι → ι → ℝ) (u v : ι → ZMod p → ℂ) :
    (blockForm M0 M1 u v - blockForm (fun a b => M0 b a) (fun a b => -M1 b a) u v) / 2 =
      blockForm (skewM M0) (symM M1) u v := by
  rw [blockForm_expand, blockForm_expand, blockForm_expand, ← sum_sub_distrib, sum_div]
  refine sum_congr rfl fun a _ => ?_
  rw [← sum_sub_distrib, sum_div]
  refine sum_congr rfl fun b _ => ?_
  unfold symM skewM
  push_cast
  ring

end SymSkew

/-- The symmetric part `(X + X^*)/2` of the operator `X` with kernel `K`, in bilinear form:
`(⟨g, X f⟩ + \overline{⟨f, X g⟩})/2`. -/
noncomputable def symBil (μ : (U → ZMod p) → ℝ) (g : (U → ZMod p) → ℂ)
    (K : (U → ZMod p) → (U → ZMod p) → ℝ) (f : (U → ZMod p) → ℂ) : ℂ :=
  (bil μ g K f + conj (bil μ f K g)) / 2

/-- The skew part `(X − X^*)/2`, in bilinear form. -/
noncomputable def skewBil (μ : (U → ZMod p) → ℝ) (g : (U → ZMod p) → ℂ)
    (K : (U → ZMod p) → (U → ZMod p) → ℝ) (f : (U → ZMod p) → ℂ) : ℂ :=
  (bil μ g K f - conj (bil μ f K g)) / 2

/-- **`cor:star-matrix`, the symmetric part**: `Sym(P₀ K_st P₀) = r F Sym M(Φ̂) F^*`, with
`Sym M(i) = matI (symM M₀) (skewM M₁)` (`matI_symM`). -/
theorem symBil_factor (hp2 : p ≠ 2) (hp3 : p % 4 = 3) (μ : (U → ZMod p) → ℝ)
    (hμ1 : ∑ x, μ x = 1)
    (hinv : ∀ (s c : ZMod p) (x : U → ZMod p), s ≠ 0 → IsSquare s → μ (affLab s c x) = μ x)
    (d : U → U → ℝ) (L : U → Finset U → ℝ) (R : Finset U → U → ℝ) (𝒮 : Finset (Finset U))
    (g f : (U → ZMod p) → ℂ) :
    symBil μ (cent μ g) (starPart d L R 𝒮) (cent μ f) =
      ((rp p : ℝ) : ℂ) * blockForm (symM (starM0 L R 𝒮)) (skewM (starM1 d 𝒮)) (featAdj μ 𝒮 g)
        (featAdj μ 𝒮 f) := by
  unfold symBil
  rw [starPart_factor hp2 hp3 μ hμ1 hinv d L R 𝒮 g f,
    starPart_factor hp2 hp3 μ hμ1 hinv d L R 𝒮 f g, map_mul, Complex.conj_ofReal,
    blockForm_conj hp2 hp3, ← mul_add, mul_div_assoc, blockForm_symm]

/-- **`cor:star-matrix`, the skew part**: `Skew(P₀ K_st P₀) = r F Skew M(Φ̂) F^*`, with
`Skew M(i) = matI (skewM M₀) (symM M₁)` (`matI_skewM`). -/
theorem skewBil_factor (hp2 : p ≠ 2) (hp3 : p % 4 = 3) (μ : (U → ZMod p) → ℝ)
    (hμ1 : ∑ x, μ x = 1)
    (hinv : ∀ (s c : ZMod p) (x : U → ZMod p), s ≠ 0 → IsSquare s → μ (affLab s c x) = μ x)
    (d : U → U → ℝ) (L : U → Finset U → ℝ) (R : Finset U → U → ℝ) (𝒮 : Finset (Finset U))
    (g f : (U → ZMod p) → ℂ) :
    skewBil μ (cent μ g) (starPart d L R 𝒮) (cent μ f) =
      ((rp p : ℝ) : ℂ) * blockForm (skewM (starM0 L R 𝒮)) (symM (starM1 d 𝒮)) (featAdj μ 𝒮 g)
        (featAdj μ 𝒮 f) := by
  unfold skewBil
  rw [starPart_factor hp2 hp3 μ hμ1 hinv d L R 𝒮 g f,
    starPart_factor hp2 hp3 μ hμ1 hinv d L R 𝒮 f g, map_mul, Complex.conj_ofReal,
    blockForm_conj hp2 hp3, ← mul_sub, mul_div_assoc, blockForm_skew]

/-- **`cor:star-matrix`, the norm of the symmetric part**: `‖Sym(P₀ K_st P₀)‖ ≤ r ‖F‖²
‖Sym M(i)‖`. -/
theorem symBil_norm_le (hp2 : p ≠ 2) (hp3 : p % 4 = 3) (μ : (U → ZMod p) → ℝ)
    (hμ0 : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1)
    (hinv : ∀ (s c : ZMod p) (x : U → ZMod p), s ≠ 0 → IsSquare s → μ (affLab s c x) = μ x)
    (d : U → U → ℝ) (L : U → Finset U → ℝ) (R : Finset U → U → ℝ) (𝒮 : Finset (Finset U))
    {lam Fsq : ℝ} (hlam : 0 ≤ lam) (hFsq : 0 ≤ Fsq)
    (hM : NormLe (matI (symM (starM0 L R 𝒮)) (skewM (starM1 d 𝒮))) lam)
    (hF : ∀ h : Feat U 𝒮 → ZMod p → ℂ, (∀ a, meanC (h a) = 0) →
      ∑ x, μ x * ‖∑ a, kerMap (featKer 𝒮 a) (h a) x‖ ^ 2 ≤ Fsq * ∑ a, l2sq (h a))
    (g f : (U → ZMod p) → ℂ) :
    ‖symBil μ (cent μ g) (starPart d L R 𝒮) (cent μ f)‖ ≤
      rp p * lam * Fsq * √(∑ x, μ x * ‖g x‖ ^ 2) * √(∑ x, μ x * ‖f x‖ ^ 2) := by
  rw [symBil_factor hp2 hp3 μ hμ1 hinv]
  exact featForm_norm_le hp2 hp3 μ hμ0 𝒮 _ _ hlam hFsq hM hF g f

/-- **`cor:star-matrix`, the norm of the skew part**: `‖Skew(P₀ K_st P₀)‖ ≤ r ‖F‖²
‖Skew M(i)‖`. -/
theorem skewBil_norm_le (hp2 : p ≠ 2) (hp3 : p % 4 = 3) (μ : (U → ZMod p) → ℝ)
    (hμ0 : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1)
    (hinv : ∀ (s c : ZMod p) (x : U → ZMod p), s ≠ 0 → IsSquare s → μ (affLab s c x) = μ x)
    (d : U → U → ℝ) (L : U → Finset U → ℝ) (R : Finset U → U → ℝ) (𝒮 : Finset (Finset U))
    {lam Fsq : ℝ} (hlam : 0 ≤ lam) (hFsq : 0 ≤ Fsq)
    (hM : NormLe (matI (skewM (starM0 L R 𝒮)) (symM (starM1 d 𝒮))) lam)
    (hF : ∀ h : Feat U 𝒮 → ZMod p → ℂ, (∀ a, meanC (h a) = 0) →
      ∑ x, μ x * ‖∑ a, kerMap (featKer 𝒮 a) (h a) x‖ ^ 2 ≤ Fsq * ∑ a, l2sq (h a))
    (g f : (U → ZMod p) → ℂ) :
    ‖skewBil μ (cent μ g) (starPart d L R 𝒮) (cent μ f)‖ ≤
      rp p * lam * Fsq * √(∑ x, μ x * ‖g x‖ ^ 2) * √(∑ x, μ x * ‖f x‖ ^ 2) := by
  rw [skewBil_factor hp2 hp3 μ hμ1 hinv]
  exact featForm_norm_le hp2 hp3 μ hμ0 𝒮 _ _ hlam hFsq hM hF g f

end Sarkozy.SpectralD.StarMatrix
