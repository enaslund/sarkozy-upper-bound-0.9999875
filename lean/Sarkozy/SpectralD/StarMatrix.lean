module

public import Sarkozy.SpectralC.All

@[expose] public section

/-!
# The complete star matrix, I: the factorisation (`cor:star-matrix`)

`paper/sections/14_spectral.tex`, `subsec:spec:actual-stars`, `cor:star-matrix`. Setting of
`lem:general-star`: `p ≡ 3 (mod 4)`, `H = L²_0(𝔽_p)`, a law `μ` on labellings `x : U → 𝔽_p`
invariant under `Aff_p` (here only the translations and `∑ μ = 1` are used), the singletons
`(V_i h)(x) = h(x_i)` and the stars `(W_S h)(x) = E_z ψ_S(z, x) h(z)`,
`ψ_S(z, x) = ∏_{j ∈ S} χ(z − x_j)` (`psi`), `w_S = E_z ψ_S` (`starMean`).

For a real matrix `D` the soft cross kernel is `K_D(x, y) = ∏_{i,j ∈ U} (1 + D_ij χ(y_j − x_i))`.
Its *complete star part* is the sum of the terms of its expansion that are single pairs `(i, j)`,
left stars `∏_{j ∈ S} D_ij χ(y_j − x_i)` (centre `i`) and right stars
`∏_{i ∈ S} D_ij χ(y_j − x_i)` (centre `j`), `|S| ≥ 2`. We treat general real coefficients
(`starPart d L R 𝒮`: single pairs `d i j`, left stars `L i S`, right stars `R S j`, supports in a
finite set `𝒮`); the soft kernel is `d = D`, `L i S = ∏_{j∈S} D_ij`, `R S j = ∏_{i∈S} D_ij`
(`softStarPart`), and the difference of two soft kernels is the case of the differences of the
coefficients (everything here is linear in the coefficients).

The operator with kernel `K` relative to `μ ⊗ μ`, compressed by `P₀ = I − E_μ` on both sides, has
the bilinear form `⟨P₀g, K P₀f⟩_μ = bil μ (cent μ g) K (cent μ f)`.

Results:
* the adjoints on `H`: `V_j^* f = vAdj μ j f` and `W_S^* f = wAdj μ S f` (`vAdj_adjoint`,
  `wAdj_adjoint`); they are mean zero (`meanC_vAdj`, `meanC_wAdj`) and vanish on the constants,
  `V_j^* P₀ = V_j^*`, `W_S^* P₀ = W_S^*` (`vAdj_cent`, `wAdj_cent`; the one-vertex marginals of
  `μ` are uniform, `sum_mu_ind`, and `E_μ ψ_S(z, ·)` does not depend on `z`);
* **the factorisation** (`starPart_compress`): `⟨P₀g, K_st P₀f⟩_μ =
  ∑_{i,j} d_ij ⟨V_i^*g, C V_j^*f⟩ + ∑_{i,S} (−1)^{|S|} L_iS ⟨V_i^*g, W_S^*f⟩ +
  ∑_{S,j} R_Sj ⟨W_S^*g, V_j^*f⟩`. With `Φ̂ = C/r`, `F_i = V_i`, `F_S = W_S/r` this is
  `⟨g, r F M(Φ̂) F^* f⟩` for the block matrix `M(Φ̂)` of `cor:star-matrix` (singleton block
  `d ⊗ Φ̂`, row `i` column `S` entry `(−1)^{|S|} L_iS`, row `S` column `j` entry `R_Sj`, zero between
  supports); the block form and the norm bound are in `Sarkozy.SpectralD.StarMatrixNorm`.

The pieces: `single_pair_compress` (`D_ij V_i C V_j^*`), `right_star_compress`
(`R_Sj W_S V_j^*`), `left_star_compress` (`(−1)^{|S|} L_iS V_i W_S^*`; here `χ(−1) = −1`).
Injectivity of the labellings is not used.

New material for this paper.
-/

namespace Sarkozy.SpectralD.StarMatrix

open Finset Complex Sarkozy.Characters Sarkozy.SpectralC
open scoped BigOperators ComplexConjugate

variable {p : ℕ} [Fact p.Prime] {U : Type*} [Fintype U] [DecidableEq U]

/-! ## Definitions -/

/-- The expectation `E_μ f = ∑_x μ(x) f(x)`. -/
noncomputable def muE (μ : (U → ZMod p) → ℝ) (f : (U → ZMod p) → ℂ) : ℂ :=
  ∑ x, (μ x : ℂ) * f x

/-- The centring `P₀ f = f − E_μ f`. -/
noncomputable def cent (μ : (U → ZMod p) → ℝ) (f : (U → ZMod p) → ℂ) (x : U → ZMod p) : ℂ :=
  f x - muE μ f

/-- `ψ_S(z, x) = ∏_{j ∈ S} χ(z − x_j)`. -/
noncomputable def psi (S : Finset U) (z : ZMod p) (x : U → ZMod p) : ℝ :=
  ∏ j ∈ S, chiRe (z - x j)

/-- The adjoint of the singleton `V_j` on `H`: `(V_j^* f)(t) = p E_μ[f 𝟙_{x_j = t}] − E_μ f`. -/
noncomputable def vAdj (μ : (U → ZMod p) → ℝ) (j : U) (f : (U → ZMod p) → ℂ) (t : ZMod p) : ℂ :=
  (p : ℂ) * ∑ x, (μ x : ℂ) * (if x j = t then f x else 0) - muE μ f

/-- The adjoint of the star `W_S` on `H`: `(W_S^* f)(z) = E_μ[ψ_S(z, ·) f] − E_μ[w_S f]`. -/
noncomputable def wAdj (μ : (U → ZMod p) → ℝ) (S : Finset U) (f : (U → ZMod p) → ℂ)
    (z : ZMod p) : ℂ :=
  ∑ x, (μ x : ℂ) * (psi S z x : ℂ) * f x - ∑ x, (μ x : ℂ) * (starMean S x : ℂ) * f x

/-- The bilinear form `⟨g, K f⟩_μ = E_{x∼μ} E_{y∼μ} \overline{g(x)} K(x, y) f(y)` of the operator
with kernel `K` relative to `μ ⊗ μ`. -/
noncomputable def bil (μ : (U → ZMod p) → ℝ) (g : (U → ZMod p) → ℂ)
    (K : (U → ZMod p) → (U → ZMod p) → ℝ) (f : (U → ZMod p) → ℂ) : ℂ :=
  ∑ x, ∑ y, (μ x : ℂ) * (μ y : ℂ) * conj (g x) * (K x y : ℂ) * f y

/-- **The star part of a cross kernel** (`cor:star-matrix`), with general real coefficients:
single pairs `d i j χ(y_j − x_i)`, left stars `L i S ∏_{j ∈ S} χ(y_j − x_i)` (centre `i`, leaves
`S`) and right stars `R S j ∏_{i ∈ S} χ(y_j − x_i)` (centre `j`, leaves `S`), `S ∈ 𝒮`. -/
noncomputable def starPart (d : U → U → ℝ) (L : U → Finset U → ℝ) (R : Finset U → U → ℝ)
    (𝒮 : Finset (Finset U)) (x y : U → ZMod p) : ℝ :=
  ∑ i, ∑ j, d i j * chiRe (y j - x i) +
    ∑ i, ∑ S ∈ 𝒮, L i S * ∏ j ∈ S, chiRe (y j - x i) +
    ∑ S ∈ 𝒮, ∑ j, R S j * ∏ i ∈ S, chiRe (y j - x i)

/-- The supports: the sets `S ⊆ U` with `|S| ≥ 2`. -/
def supports (U : Type*) [Fintype U] [DecidableEq U] : Finset (Finset U) :=
  univ.filter (fun S : Finset U => 2 ≤ S.card)

/-- **The complete star part of the soft cross kernel**
`K_D(x, y) = ∏_{i,j ∈ U} (1 + D_ij χ(y_j − x_i))` (`cor:star-matrix`): the single pairs
`D_ij χ(y_j − x_i)`, the left stars `∏_{j ∈ S} D_ij χ(y_j − x_i)` and the right stars
`∏_{i ∈ S} D_ij χ(y_j − x_i)`, `|S| ≥ 2`. -/
noncomputable def softStarPart (D : U → U → ℝ) (x y : U → ZMod p) : ℝ :=
  starPart D (fun i S => ∏ j ∈ S, D i j) (fun S j => ∏ i ∈ S, D i j) (supports U) x y

/-! ## Linearity of the bilinear form in the kernel -/

lemma bil_add (μ : (U → ZMod p) → ℝ) (g f : (U → ZMod p) → ℂ)
    (K₁ K₂ : (U → ZMod p) → (U → ZMod p) → ℝ) :
    bil μ g (fun x y => K₁ x y + K₂ x y) f = bil μ g K₁ f + bil μ g K₂ f := by
  unfold bil
  rw [← sum_add_distrib]
  refine sum_congr rfl fun x _ => ?_
  rw [← sum_add_distrib]
  refine sum_congr rfl fun y _ => ?_
  push_cast
  ring

lemma bil_sum {κ : Type*} (s : Finset κ) (μ : (U → ZMod p) → ℝ) (g f : (U → ZMod p) → ℂ)
    (K : κ → (U → ZMod p) → (U → ZMod p) → ℝ) :
    bil μ g (fun x y => ∑ a ∈ s, K a x y) f = ∑ a ∈ s, bil μ g (K a) f := by
  unfold bil
  symm
  rw [sum_comm]
  refine sum_congr rfl fun x _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun y _ => ?_
  push_cast
  rw [mul_sum, sum_mul]

lemma bil_smul (μ : (U → ZMod p) → ℝ) (g f : (U → ZMod p) → ℂ) (c : ℝ)
    (K : (U → ZMod p) → (U → ZMod p) → ℝ) :
    bil μ g (fun x y => c * K x y) f = (c : ℂ) * bil μ g K f := by
  unfold bil
  rw [mul_sum]
  refine sum_congr rfl fun x _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun y _ => ?_
  push_cast
  ring

/-! ## The uniform marginals and the constants -/

omit [Fintype U] [DecidableEq U] in
lemma isSquare_one' : IsSquare (1 : ZMod p) := ⟨1, by ring⟩

/-- The one-vertex marginals of a translation-invariant probability law are uniform. -/
lemma sum_mu_ind (μ : (U → ZMod p) → ℝ) (hμ1 : ∑ x, μ x = 1)
    (hinv : ∀ (s c : ZMod p) (x : U → ZMod p), s ≠ 0 → IsSquare s → μ (affLab s c x) = μ x)
    (j : U) (t : ZMod p) : ∑ x, μ x * (if x j = t then (1 : ℝ) else 0) = (p : ℝ)⁻¹ := by
  have hshift : ∀ t c : ZMod p, ∑ x, μ x * (if x j = t + c then (1 : ℝ) else 0) =
      ∑ x, μ x * (if x j = t then (1 : ℝ) else 0) := by
    intro t c
    rw [← (affLab_bijective (U := U) (one_ne_zero (α := ZMod p)) c).sum_comp]
    refine sum_congr rfl fun x _ => ?_
    rw [hinv 1 c x one_ne_zero isSquare_one']
    unfold affLab
    simp only [one_mul, add_left_inj]
  have hconst : ∀ t, ∑ x, μ x * (if x j = t then (1 : ℝ) else 0) =
      ∑ x, μ x * (if x j = 0 then (1 : ℝ) else 0) := by
    intro t
    have := hshift 0 t
    rwa [zero_add] at this
  have htot : ∑ t : ZMod p, ∑ x, μ x * (if x j = t then (1 : ℝ) else 0) = 1 := by
    rw [sum_comm]
    simp only [mul_ite, mul_one, mul_zero, sum_ite_eq, mem_univ, ite_true]
    exact hμ1
  rw [sum_congr rfl fun t _ => hconst t, sum_const, card_univ, ZMod.card, nsmul_eq_mul] at htot
  rw [hconst t]
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  field_simp
  linarith

/-- The same, as a complex sum. -/
lemma sum_mu_ind_C (μ : (U → ZMod p) → ℝ) (hμ1 : ∑ x, μ x = 1)
    (hinv : ∀ (s c : ZMod p) (x : U → ZMod p), s ≠ 0 → IsSquare s → μ (affLab s c x) = μ x)
    (j : U) (t : ZMod p) : ∑ x, (μ x : ℂ) * (if x j = t then (1 : ℂ) else 0) = (p : ℂ)⁻¹ := by
  have h := sum_mu_ind μ hμ1 hinv j t
  have h2 : ((∑ x, μ x * (if x j = t then (1 : ℝ) else 0) : ℝ) : ℂ) = (((p : ℝ)⁻¹ : ℝ) : ℂ) := by
    rw [h]
  push_cast at h2
  rw [← h2]
  refine sum_congr rfl fun x _ => ?_
  split_ifs <;> simp

/-- `E_μ ψ_S(z, ·)` does not depend on `z` (translation invariance). -/
lemma sum_mu_psi_shift (μ : (U → ZMod p) → ℝ)
    (hinv : ∀ (s c : ZMod p) (x : U → ZMod p), s ≠ 0 → IsSquare s → μ (affLab s c x) = μ x)
    (S : Finset U) (z c : ZMod p) :
    ∑ x, μ x * psi S (z + c) x = ∑ x, μ x * psi S z x := by
  rw [← (affLab_bijective (U := U) (one_ne_zero (α := ZMod p)) c).sum_comp]
  refine sum_congr rfl fun x _ => ?_
  rw [hinv 1 c x one_ne_zero isSquare_one']
  congr 1
  unfold psi affLab
  refine prod_congr rfl fun j _ => ?_
  congr 1
  ring

omit [Fintype U] [DecidableEq U] in
/-- `p w_S(x) = ∑_z ψ_S(z, x)`. -/
lemma sum_psi (S : Finset U) (x : U → ZMod p) :
    ∑ z, psi S z x = (p : ℝ) * starMean S x := by
  unfold starMean starKer psi
  rw [← mul_sum, ← mul_assoc, mul_inv_cancel₀ (by exact_mod_cast (Fact.out : p.Prime).ne_zero),
    one_mul]

/-- `E_μ ψ_S(z, ·) = E_μ w_S` for every `z`. -/
lemma sum_mu_psi (μ : (U → ZMod p) → ℝ)
    (hinv : ∀ (s c : ZMod p) (x : U → ZMod p), s ≠ 0 → IsSquare s → μ (affLab s c x) = μ x)
    (S : Finset U) (z : ZMod p) :
    ∑ x, μ x * psi S z x = ∑ x, μ x * starMean S x := by
  have hconst : ∀ z', ∑ x, μ x * psi S z' x = ∑ x, μ x * psi S z x := by
    intro z'
    have := sum_mu_psi_shift μ hinv S z (z' - z)
    rwa [add_sub_cancel] at this
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  have h1 : ∑ z' : ZMod p, ∑ x, μ x * psi S z' x = (p : ℝ) * ∑ x, μ x * starMean S x := by
    rw [sum_comm, mul_sum]
    refine sum_congr rfl fun x _ => ?_
    rw [← mul_sum, sum_psi]
    ring
  rw [sum_congr rfl fun z' _ => hconst z', sum_const, card_univ, ZMod.card, nsmul_eq_mul] at h1
  exact mul_left_cancel₀ hp h1

lemma muE_cent (μ : (U → ZMod p) → ℝ) (hμ1 : ∑ x, μ x = 1) (f : (U → ZMod p) → ℂ) :
    muE μ (cent μ f) = 0 := by
  unfold muE cent
  have hμC : ∑ x, (μ x : ℂ) = 1 := by exact_mod_cast hμ1
  simp only [mul_sub, sum_sub_distrib, ← sum_mul, hμC, one_mul]
  unfold muE
  ring

/-- `V_j^*` vanishes on the constants: `V_j^* P₀ f = V_j^* f`. -/
lemma vAdj_cent (μ : (U → ZMod p) → ℝ) (hμ1 : ∑ x, μ x = 1)
    (hinv : ∀ (s c : ZMod p) (x : U → ZMod p), s ≠ 0 → IsSquare s → μ (affLab s c x) = μ x)
    (j : U) (f : (U → ZMod p) → ℂ) : vAdj μ j (cent μ f) = vAdj μ j f := by
  funext t
  unfold vAdj
  rw [muE_cent μ hμ1 f, sub_zero]
  have h1 : ∑ x, (μ x : ℂ) * (if x j = t then cent μ f x else 0) =
      ∑ x, (μ x : ℂ) * (if x j = t then f x else 0) -
        muE μ f * ∑ x, (μ x : ℂ) * (if x j = t then (1 : ℂ) else 0) := by
    rw [mul_sum, ← sum_sub_distrib]
    refine sum_congr rfl fun x _ => ?_
    unfold cent
    split_ifs <;> ring
  rw [h1, sum_mu_ind_C μ hμ1 hinv j t, mul_sub]
  have hpC := p_ne_zero_C (p := p)
  field_simp

/-- `W_S^*` vanishes on the constants: `W_S^* P₀ f = W_S^* f`. -/
lemma wAdj_cent (μ : (U → ZMod p) → ℝ)
    (hinv : ∀ (s c : ZMod p) (x : U → ZMod p), s ≠ 0 → IsSquare s → μ (affLab s c x) = μ x)
    (S : Finset U) (f : (U → ZMod p) → ℂ) : wAdj μ S (cent μ f) = wAdj μ S f := by
  funext z
  unfold wAdj cent
  have hz : ∑ x, (μ x : ℂ) * (psi S z x : ℂ) = ∑ x, (μ x : ℂ) * (starMean S x : ℂ) := by
    have := sum_mu_psi μ hinv S z
    exact_mod_cast this
  simp only [mul_sub, sum_sub_distrib, ← sum_mul, hz]
  ring

/-- `V_j^* f` is mean zero. -/
lemma meanC_vAdj (μ : (U → ZMod p) → ℝ) (j : U) (f : (U → ZMod p) → ℂ) :
    meanC (vAdj μ j f) = 0 := by
  unfold meanC vAdj
  rw [sum_sub_distrib, ← mul_sum, sum_comm]
  have h : ∀ x : U → ZMod p, ∑ t, (μ x : ℂ) * (if x j = t then f x else 0) = (μ x : ℂ) * f x := by
    intro x
    rw [← mul_sum, sum_ite_eq, ite_eq_left (mem_univ _)]
  rw [sum_congr rfl fun x _ => h x, sum_const, card_univ, ZMod.card, nsmul_eq_mul]
  unfold muE
  ring

/-- `W_S^* f` is mean zero. -/
lemma meanC_wAdj (μ : (U → ZMod p) → ℝ) (S : Finset U) (f : (U → ZMod p) → ℂ) :
    meanC (wAdj μ S f) = 0 := by
  unfold meanC wAdj
  rw [sum_sub_distrib, sum_comm, sum_const, card_univ, ZMod.card, nsmul_eq_mul]
  have h : ∀ x : U → ZMod p, ∑ z, (μ x : ℂ) * (psi S z x : ℂ) * f x =
      (p : ℂ) * ((μ x : ℂ) * (starMean S x : ℂ) * f x) := by
    intro x
    rw [← sum_mul, ← mul_sum]
    have : ∑ z, (psi S z x : ℂ) = (p : ℂ) * (starMean S x : ℂ) := by
      have h' := sum_psi S x
      exact_mod_cast h'
    rw [this]
    ring
  rw [sum_congr rfl fun x _ => h x, ← mul_sum]
  ring

/-- **`V_j^*` is the adjoint of `V_j` on `H`**: `⟨V_j h, f⟩_μ = ⟨h, V_j^* f⟩` for `h ∈ H`. -/
lemma vAdj_adjoint (μ : (U → ZMod p) → ℝ) (j : U) (f : (U → ZMod p) → ℂ) (h : ZMod p → ℂ)
    (hh : meanC h = 0) :
    ∑ x, (μ x : ℂ) * (conj (kerMap (vertKer j) h x) * f x) = ip h (vAdj μ j f) := by
  have hsum : ∑ a, conj (h a) = 0 := by
    have : ∑ a, h a = 0 := by
      unfold meanC at hh
      exact (mul_eq_zero.mp hh).resolve_left (inv_ne_zero p_ne_zero_C)
    rw [← map_sum, this, map_zero]
  unfold ip vAdj
  simp only [mul_sub, sum_sub_distrib]
  rw [← sum_mul, hsum, zero_mul, mul_zero, sub_zero]
  simp_rw [kerMap_vertKer]
  have hpC := p_ne_zero_C (p := p)
  have e : ∀ t, conj (h t) * ((p : ℂ) * ∑ x, (μ x : ℂ) * (if x j = t then f x else 0)) =
      (p : ℂ) * ∑ x, (if x j = t then (μ x : ℂ) * (conj (h (x j)) * f x) else 0) := by
    intro t
    rw [mul_left_comm, mul_sum]
    congr 1
    refine sum_congr rfl fun x _ => ?_
    split_ifs with hx
    · rw [hx]; ring
    · ring
  rw [sum_congr rfl fun t _ => e t, ← mul_sum, sum_comm, ← mul_assoc, inv_mul_cancel₀ hpC,
    one_mul]
  refine sum_congr rfl fun x _ => ?_
  rw [sum_ite_eq, ite_eq_left (mem_univ _)]

/-- **`W_S^*` is the adjoint of `W_S` on `H`**: `⟨W_S h, f⟩_μ = ⟨h, W_S^* f⟩` for `h ∈ H`. -/
lemma wAdj_adjoint (μ : (U → ZMod p) → ℝ) (S : Finset U) (f : (U → ZMod p) → ℂ)
    (h : ZMod p → ℂ) (hh : meanC h = 0) :
    ∑ x, (μ x : ℂ) * (conj (kerMap (starKer S) h x) * f x) = ip h (wAdj μ S f) := by
  have hsum : ∑ a, conj (h a) = 0 := by
    have : ∑ a, h a = 0 := by
      unfold meanC at hh
      exact (mul_eq_zero.mp hh).resolve_left (inv_ne_zero p_ne_zero_C)
    rw [← map_sum, this, map_zero]
  unfold ip wAdj
  simp only [mul_sub, sum_sub_distrib]
  rw [← sum_mul, hsum, zero_mul, mul_zero, sub_zero]
  unfold kerMap starKer
  simp only [map_sum, map_mul, Complex.conj_ofReal, sum_mul, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun a _ => ?_
  refine sum_congr rfl fun x _ => ?_
  unfold psi
  push_cast
  ring

/-! ## The three kinds of terms, for centred `f`, `g` -/

/-- `E_μ[\overline{g} G(x_i)] = ⟨V_i^* g, G⟩` for `E_μ g = 0`. -/
lemma sum_conj_comp (μ : (U → ZMod p) → ℝ) (i : U) (g : (U → ZMod p) → ℂ)
    (hg : muE μ g = 0) (G : ZMod p → ℂ) :
    ∑ x, (μ x : ℂ) * conj (g x) * G (x i) = ip (vAdj μ i g) G := by
  unfold ip vAdj
  rw [hg]
  simp only [sub_zero]
  have hpC := p_ne_zero_C (p := p)
  have e : ∀ s, conj ((p : ℂ) * ∑ x, (μ x : ℂ) * (if x i = s then g x else 0)) * G s =
      (p : ℂ) * ∑ x, (if x i = s then (μ x : ℂ) * conj (g x) * G (x i) else 0) := by
    intro s
    rw [map_mul, Complex.conj_natCast, map_sum, mul_assoc, sum_mul]
    congr 1
    refine sum_congr rfl fun x _ => ?_
    split_ifs with hx
    · rw [map_mul, Complex.conj_ofReal, hx]
    · simp
  rw [sum_congr rfl fun s _ => e s, ← mul_sum, sum_comm, ← mul_assoc, inv_mul_cancel₀ hpC,
    one_mul]
  refine sum_congr rfl fun x _ => ?_
  rw [sum_ite_eq, ite_eq_left (mem_univ _)]

/-- `E_μ[χ(y_j − s) f(y)] = (C V_j^* f)(s)` for `E_μ f = 0`. -/
lemma sum_chi_eq_gaussOp (μ : (U → ZMod p) → ℝ) (j : U) (f : (U → ZMod p) → ℂ)
    (hf : muE μ f = 0) (s : ZMod p) :
    ∑ y, (μ y : ℂ) * (chiRe (y j - s) : ℂ) * f y = gaussOp (vAdj μ j f) s := by
  unfold gaussOp vAdj
  rw [hf]
  simp only [sub_zero]
  have hpC := p_ne_zero_C (p := p)
  have e : ∀ b, chiC p (b - s) * ((p : ℂ) * ∑ y, (μ y : ℂ) * (if y j = b then f y else 0)) =
      (p : ℂ) * ∑ y, (if y j = b then (μ y : ℂ) * (chiRe (y j - s) : ℂ) * f y else 0) := by
    intro b
    rw [mul_left_comm, mul_sum]
    congr 1
    refine sum_congr rfl fun y _ => ?_
    split_ifs with hy
    · rw [hy]
      unfold chiRe
      rw [chiC_apply]
      push_cast
      ring
    · ring
  rw [sum_congr rfl fun b _ => e b, ← mul_sum, sum_comm, ← mul_assoc, inv_mul_cancel₀ hpC,
    one_mul]
  refine sum_congr rfl fun y _ => ?_
  rw [sum_ite_eq, ite_eq_left (mem_univ _)]

/-- **A single pair** (`cor:star-matrix`): the pair `(i, j)` gives `V_i C V_j^*`, that is
`E_{x,y}[\overline{g(x)} χ(y_j − x_i) f(y)] = ⟨V_i^* g, C V_j^* f⟩` for centred `f`, `g`. -/
theorem single_pair_compress (μ : (U → ZMod p) → ℝ) (i j : U) (g f : (U → ZMod p) → ℂ)
    (hg : muE μ g = 0) (hf : muE μ f = 0) :
    bil μ g (fun x y => chiRe (y j - x i)) f = ip (vAdj μ i g) (gaussOp (vAdj μ j f)) := by
  rw [← sum_conj_comp μ i g hg]
  unfold bil
  refine sum_congr rfl fun x _ => ?_
  rw [← sum_chi_eq_gaussOp μ j f hf (x i), mul_sum]
  refine sum_congr rfl fun y _ => ?_
  ring

/-- `E_μ[ψ_S(y_j, x) f(y)] = (W_S V_j^* f)(x)` for `E_μ f = 0`. -/
lemma sum_psi_eq_kerMap (μ : (U → ZMod p) → ℝ) (S : Finset U) (j : U)
    (f : (U → ZMod p) → ℂ) (hf : muE μ f = 0) (x : U → ZMod p) :
    ∑ y, (μ y : ℂ) * (psi S (y j) x : ℂ) * f y = kerMap (starKer S) (vAdj μ j f) x := by
  unfold kerMap starKer vAdj
  rw [hf]
  simp only [sub_zero]
  have hpC := p_ne_zero_C (p := p)
  have e : ∀ t, (((p : ℝ)⁻¹ * ∏ i ∈ S, chiRe (t - x i) : ℝ) : ℂ) *
      ((p : ℂ) * ∑ y, (μ y : ℂ) * (if y j = t then f y else 0)) =
      ∑ y, (if y j = t then (μ y : ℂ) * (psi S (y j) x : ℂ) * f y else 0) := by
    intro t
    rw [mul_sum, mul_sum]
    refine sum_congr rfl fun y _ => ?_
    split_ifs with hy
    · rw [hy]
      unfold psi
      push_cast
      field_simp
    · ring
  rw [sum_congr rfl fun t _ => e t, sum_comm]
  refine sum_congr rfl fun y _ => ?_
  rw [sum_ite_eq, ite_eq_left (mem_univ _)]

/-- `E_μ[\overline{g} (W_S u)] = ⟨W_S^* g, u⟩` for `u ∈ H`. -/
lemma sum_conj_kerMap (μ : (U → ZMod p) → ℝ) (S : Finset U) (g : (U → ZMod p) → ℂ)
    (u : ZMod p → ℂ) (hu : meanC u = 0) :
    ∑ x, (μ x : ℂ) * conj (g x) * kerMap (starKer S) u x = ip (wAdj μ S g) u := by
  have hsum : ∑ a, u a = 0 := by
    unfold meanC at hu
    exact (mul_eq_zero.mp hu).resolve_left (inv_ne_zero p_ne_zero_C)
  unfold ip wAdj
  simp only [map_sub, sub_mul, sum_sub_distrib]
  rw [← mul_sum, hsum, mul_zero, sub_zero]
  unfold kerMap starKer
  simp only [map_sum, map_mul, Complex.conj_ofReal, sum_mul, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun x _ => ?_
  refine sum_congr rfl fun a _ => ?_
  unfold psi
  push_cast
  ring

/-- **A right star** (`cor:star-matrix`): the star with centre `j` and leaves `S` gives `W_S V_j^*`,
that is `E_{x,y}[\overline{g(x)} ∏_{i ∈ S} χ(y_j − x_i) f(y)] = ⟨W_S^* g, V_j^* f⟩` for centred
`f`. -/
theorem right_star_compress (μ : (U → ZMod p) → ℝ) (S : Finset U) (j : U)
    (g f : (U → ZMod p) → ℂ) (hf : muE μ f = 0) :
    bil μ g (fun x y => ∏ i ∈ S, chiRe (y j - x i)) f = ip (wAdj μ S g) (vAdj μ j f) := by
  rw [← sum_conj_kerMap μ S g (vAdj μ j f) (meanC_vAdj μ j f)]
  unfold bil
  refine sum_congr rfl fun x _ => ?_
  rw [← sum_psi_eq_kerMap μ S j f hf x, mul_sum]
  refine sum_congr rfl fun y _ => ?_
  unfold psi
  ring

omit [Fintype U] [DecidableEq U] in
/-- `χ(−t) = −χ(t)` for `p ≡ 3 (mod 4)`. -/
lemma chiRe_neg (hp2 : p ≠ 2) (hp3 : p % 4 = 3) (t : ZMod p) : chiRe (-t) = -chiRe t := by
  have h1 : chiRe (-1 : ZMod p) = -1 := by
    have h := chiC_neg_one (p := p) hp2
    rw [ZMod.χ₄_nat_three_mod_four hp3] at h
    unfold chiRe
    have h' : ((quadraticChar (ZMod p) (-1) : ℤ) : ℂ) = ((-1 : ℤ) : ℂ) := by
      rw [← chiC_apply, h]
    have h'' : quadraticChar (ZMod p) (-1) = -1 := by exact_mod_cast h'
    rw [h'']
    norm_num
  rw [show -t = -1 * t by ring, chiRe_mul, h1]
  ring

/-- **A left star** (`cor:star-matrix`, `p ≡ 3 (mod 4)`): the star with centre `i` and leaves `S`
gives `(−1)^{|S|} V_i W_S^*`, that is
`E_{x,y}[\overline{g(x)} ∏_{j ∈ S} χ(y_j − x_i) f(y)] = (−1)^{|S|} ⟨V_i^* g, W_S^* f⟩` for centred
`g`. -/
theorem left_star_compress (hp2 : p ≠ 2) (hp3 : p % 4 = 3) (μ : (U → ZMod p) → ℝ) (i : U)
    (S : Finset U) (g f : (U → ZMod p) → ℂ) (hg : muE μ g = 0) :
    bil μ g (fun x y => ∏ j ∈ S, chiRe (y j - x i)) f =
      (-1 : ℂ) ^ S.card * ip (vAdj μ i g) (wAdj μ S f) := by
  have hsign : ∀ x y : U → ZMod p, ∏ j ∈ S, chiRe (y j - x i) = (-1) ^ S.card * psi S (x i) y := by
    intro x y
    unfold psi
    rw [← prod_const (-1 : ℝ), ← prod_mul_distrib]
    refine prod_congr rfl fun j _ => ?_
    rw [show y j - x i = -(x i - y j) by ring, chiRe_neg hp2 hp3]
    ring
  rw [← sum_conj_comp μ i g hg]
  set c : ℂ := ∑ y, (μ y : ℂ) * (starMean S y : ℂ) * f y with hc
  have hrow : ∀ s : ZMod p, ∑ y, (μ y : ℂ) * (psi S s y : ℂ) * f y = wAdj μ S f s + c := by
    intro s
    unfold wAdj
    ring
  have hgc : ∑ x, (μ x : ℂ) * conj (g x) = 0 := by
    have : conj (muE μ g) = 0 := by rw [hg, map_zero]
    rw [← this]
    unfold muE
    rw [map_sum]
    refine sum_congr rfl fun x _ => ?_
    rw [map_mul, Complex.conj_ofReal]
  have h1 : bil μ g (fun x y => ∏ j ∈ S, chiRe (y j - x i)) f =
      (-1 : ℂ) ^ S.card * ∑ x, (μ x : ℂ) * conj (g x) * (wAdj μ S f (x i) + c) := by
    unfold bil
    rw [mul_sum]
    refine sum_congr rfl fun x _ => ?_
    rw [← hrow (x i), mul_sum, mul_sum]
    refine sum_congr rfl fun y _ => ?_
    dsimp only
    rw [hsign x y]
    push_cast
    ring
  rw [h1]
  congr 1
  simp only [mul_add, sum_add_distrib]
  rw [← sum_mul, hgc, zero_mul, add_zero]

/-! ## The factorisation -/

/-- The factorisation for centred `f`, `g`. -/
theorem starPart_compress_centred (hp2 : p ≠ 2) (hp3 : p % 4 = 3) (μ : (U → ZMod p) → ℝ)
    (d : U → U → ℝ) (L : U → Finset U → ℝ) (R : Finset U → U → ℝ) (𝒮 : Finset (Finset U))
    (g f : (U → ZMod p) → ℂ) (hg : muE μ g = 0) (hf : muE μ f = 0) :
    bil μ g (starPart d L R 𝒮) f =
      ∑ i, ∑ j, (d i j : ℂ) * ip (vAdj μ i g) (gaussOp (vAdj μ j f)) +
        ∑ i, ∑ S ∈ 𝒮, (-1 : ℂ) ^ S.card * (L i S : ℂ) * ip (vAdj μ i g) (wAdj μ S f) +
        ∑ S ∈ 𝒮, ∑ j, (R S j : ℂ) * ip (wAdj μ S g) (vAdj μ j f) := by
  have e : starPart (p := p) d L R 𝒮 = fun x y =>
      (∑ i, ∑ j, d i j * chiRe (y j - x i) + ∑ i, ∑ S ∈ 𝒮, L i S * ∏ j ∈ S, chiRe (y j - x i)) +
        ∑ S ∈ 𝒮, ∑ j, R S j * ∏ i ∈ S, chiRe (y j - x i) := rfl
  rw [e, bil_add, bil_add]
  congr 1
  congr 1
  · rw [bil_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [bil_sum]
    refine sum_congr rfl fun j _ => ?_
    rw [bil_smul, single_pair_compress μ i j g f hg hf]
  · rw [bil_sum]
    refine sum_congr rfl fun i _ => ?_
    rw [bil_sum]
    refine sum_congr rfl fun S _ => ?_
    rw [bil_smul, left_star_compress hp2 hp3 μ i S g f hg]
    ring
  · rw [bil_sum]
    refine sum_congr rfl fun S _ => ?_
    rw [bil_sum]
    refine sum_congr rfl fun j _ => ?_
    rw [bil_smul, right_star_compress μ S j g f hf]

/-- **`cor:star-matrix`, the factorisation** (`p ≡ 3 (mod 4)`, `μ` a translation-invariant
probability law): the star part, compressed by `P₀` on both sides, is
`∑_{i,j} d_ij V_i C V_j^* + ∑_{i,S} (−1)^{|S|} L_iS V_i W_S^* + ∑_{S,j} R_Sj W_S V_j^*`, that is
`r F M(Φ̂) F^*` (`F_i = V_i`, `F_S = W_S/r`, `Φ̂ = C/r`), in bilinear form:
`⟨P₀g, K_st P₀f⟩_μ = ∑_{i,j} d_ij ⟨V_i^*g, C V_j^*f⟩ + ∑_{i,S} (−1)^{|S|} L_iS ⟨V_i^*g, W_S^*f⟩ +
∑_{S,j} R_Sj ⟨W_S^*g, V_j^*f⟩` for all `f`, `g ∈ L²(μ)`. -/
theorem starPart_compress (hp2 : p ≠ 2) (hp3 : p % 4 = 3) (μ : (U → ZMod p) → ℝ)
    (hμ1 : ∑ x, μ x = 1)
    (hinv : ∀ (s c : ZMod p) (x : U → ZMod p), s ≠ 0 → IsSquare s → μ (affLab s c x) = μ x)
    (d : U → U → ℝ) (L : U → Finset U → ℝ) (R : Finset U → U → ℝ) (𝒮 : Finset (Finset U))
    (g f : (U → ZMod p) → ℂ) :
    bil μ (cent μ g) (starPart d L R 𝒮) (cent μ f) =
      ∑ i, ∑ j, (d i j : ℂ) * ip (vAdj μ i g) (gaussOp (vAdj μ j f)) +
        ∑ i, ∑ S ∈ 𝒮, (-1 : ℂ) ^ S.card * (L i S : ℂ) * ip (vAdj μ i g) (wAdj μ S f) +
        ∑ S ∈ 𝒮, ∑ j, (R S j : ℂ) * ip (wAdj μ S g) (vAdj μ j f) := by
  rw [starPart_compress_centred hp2 hp3 μ d L R 𝒮 _ _ (muE_cent μ hμ1 g) (muE_cent μ hμ1 f)]
  simp only [vAdj_cent μ hμ1 hinv, wAdj_cent μ hinv]

end Sarkozy.SpectralD.StarMatrix
