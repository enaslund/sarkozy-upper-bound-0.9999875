module

public import Sarkozy.SpectralD.CxDegreeOne

@[expose] public section

/-!
# The translation sectors and `RouteAInputs.coupling` in the complex realization

`paper/sections/14_spectral.tex`, `subsec:spec:degone`: the translations `x ↦ x + c𝟙` act
unitarily on `L²(μ)` and commute with `Op`, `Π_𝒱` and `P₀`, so `L²(μ)` is the orthogonal sum of
the isotypic subspaces `𝒲_ξ = {F : F(x + c𝟙) = e_ξ(c)F(x)}`, each preserved by `Op` and `Π_𝒱`,
and the mode component `v_ξ` of `F_V` lies in `𝒲_ξ`. WP-A's `RouteAInputs.coupling` asks for
the split of `F_V` into its two translation sectors (modes `ξ` in the nonzero squares and in the
non-squares, the sets `Ξ_±` on which `𝐀₀(ξ) = 𝐀_{𝔠,±}`), with the residuals in orthogonal
subspaces `S_+ ⟂ S_-` and the bound `eq:spec:coupling` on each sector.

In the complex realization (`CxRealization`):
* `transl c` (`(τ_c v)(x) = v(x + c𝟙)`, a linear isometry), `eigSec ξ = 𝒲_ξ`,
  `inner_eigSec_eq_zero` (`𝒲_ξ ⟂ 𝒲_η` for `ξ ≠ η`);
* `secP = ⨆_{ξ ∈ Q} 𝒲_ξ`, `secM = ⨆_{ξ ∉ □} 𝒲_ξ`, `sectors_ortho` (`S_+ ⟂ S_-`);
* `kernelOpC_transl` (`Op` commutes with translations: `μ` and the kernel are translation
  invariant), `degSpace_transl` (`𝒱` is invariant), `starProjection_transl` (so does `Π_𝒱`);
* `gSec`: the part of `g` on a set of modes; `degMap_gSec_mem` (residuals of a sector part lie in
  its sector);
* `cx_coupling`: **the field `coupling` of `RouteAInputs`** with `sgn ξ = (ξ ∈ Q, ξ ≠ 0)`, from
  `CouplingBoundCx` (`eq:spec:coupling` for every degree-one `F_V`, `couplingBound_cx`).

For `p ≡ 3 (mod 4)`, `−1 ∉ Q`, so `ĝ(−ξ) = \overline{ĝ(ξ)}` makes the two sector parts of a real
`F_V` complex conjugates of each other (`gSec_conj`): they are not real, which is why the
coupling field needs the complex realization; the real cut realization embeds into it
(`CxRealization.embedR_cutOp`).

New material for this paper.
-/

namespace Sarkozy.SpectralD.Cx

open Finset Sarkozy.SpectralC
open scoped BigOperators ComplexConjugate InnerProductSpace

variable {p : ℕ} [Fact p.Prime] {U : Type*} [Fintype U] [DecidableEq U]

/-! ## Translations -/

/-- `x ↦ x − c𝟙`. -/
def shiftEquiv (c : ZMod p) : (U → ZMod p) ≃ (U → ZMod p) where
  toFun x j := x j - c
  invFun x j := x j + c
  left_inv x := by funext j; simp
  right_inv x := by funext j; simp

/-- **The translation** `(τ_c v)(x) = v(x + c𝟙)`, a linear isometry of the realization. -/
noncomputable def transl (c : ZMod p) :
    EuclideanSpace ℂ (U → ZMod p) ≃ₗᵢ[ℂ] EuclideanSpace ℂ (U → ZMod p) :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℂ ℂ (shiftEquiv c)

theorem transl_ofLp (c : ZMod p) (v : EuclideanSpace ℂ (U → ZMod p)) (x : U → ZMod p) :
    (transl c v).ofLp x = v.ofLp (fun j => x j + c) := by
  simp [transl, LinearIsometryEquiv.piLpCongrLeft_apply, Equiv.piCongrLeft', shiftEquiv]

theorem transl_symm (c : ZMod p) (v : EuclideanSpace ℂ (U → ZMod p)) :
    (transl c).symm v = transl (-c) v := by
  rw [LinearIsometryEquiv.symm_apply_eq]
  ext x
  rw [transl_ofLp, transl_ofLp]
  have e : (fun j => x j + c + -c) = x := by funext j; ring
  rw [e]

omit [Fintype U] [DecidableEq U] in
/-- `μ` is translation invariant (`hinv` with `s = 1`). -/
theorem mu_shift (μ : (U → ZMod p) → ℝ)
    (hinv : ∀ (s c : ZMod p) (x : U → ZMod p), s ≠ 0 → IsSquare s → μ (affLab s c x) = μ x)
    (c : ZMod p) (x : U → ZMod p) : μ (fun j => x j + c) = μ x := by
  have h := hinv 1 c x one_ne_zero ⟨1, by ring⟩
  have e : affLab 1 c x = fun j => x j + c := by
    funext j; unfold affLab; ring
  rwa [e] at h

/-! ## The isotypic subspaces and the sectors -/

/-- **The isotypic subspace** `𝒲_ξ = {v : τ_c v = e_ξ(c) v for all c}`. -/
noncomputable def eigSec (ξ : ZMod p) : Submodule ℂ (EuclideanSpace ℂ (U → ZMod p)) where
  carrier := {v | ∀ c, transl c v = ech ξ c • v}
  add_mem' {u v} hu hv c := by
    show transl c (u + v) = ech ξ c • (u + v)
    rw [map_add, hu c, hv c, smul_add]
  zero_mem' c := by
    show transl c 0 = ech ξ c • (0 : EuclideanSpace ℂ (U → ZMod p))
    rw [map_zero, smul_zero]
  smul_mem' a v hv c := by
    show transl c (a • v) = ech ξ c • (a • v)
    rw [map_smul, hv c, smul_comm]

theorem mem_eigSec {ξ : ZMod p} {v : EuclideanSpace ℂ (U → ZMod p)} :
    v ∈ eigSec ξ ↔ ∀ c, transl c v = ech ξ c • v := Iff.rfl

lemma ech_neg_mul (ξ η c : ZMod p) : ech (-ξ) c * ech η c = ech (η - ξ) c := by
  rw [ech_comm (-ξ), ech_comm η, ← ech_add_right, ech_comm]
  congr 1
  ring

/-- **`𝒲_ξ ⟂ 𝒲_η` for `ξ ≠ η`.** -/
theorem inner_eigSec_eq_zero {ξ η : ZMod p} (hne : ξ ≠ η) {v w : EuclideanSpace ℂ (U → ZMod p)}
    (hv : v ∈ eigSec ξ) (hw : w ∈ eigSec η) : ⟪v, w⟫_ℂ = 0 := by
  have h : ∀ c : ZMod p, ⟪v, w⟫_ℂ = ech (η - ξ) c * ⟪v, w⟫_ℂ := by
    intro c
    have h1 := (transl c).inner_map_map v w
    rw [hv c, hw c, inner_smul_left, inner_smul_right, ← mul_assoc] at h1
    calc ⟪v, w⟫_ℂ = conj (ech ξ c) * ech η c * ⟪v, w⟫_ℂ := h1.symm
      _ = ech (η - ξ) c * ⟪v, w⟫_ℂ := by rw [conj_ech, ech_neg_mul]
  have hsum : (p : ℂ) * ⟪v, w⟫_ℂ = 0 := by
    calc (p : ℂ) * ⟪v, w⟫_ℂ = ∑ c : ZMod p, ⟪v, w⟫_ℂ := by
          rw [sum_const, card_univ, ZMod.card, nsmul_eq_mul]
      _ = ∑ c : ZMod p, ech (η - ξ) c * ⟪v, w⟫_ℂ := sum_congr rfl fun c _ => h c
      _ = 0 := by
          rw [← sum_mul, sum_ech]
          simp only [sub_ne_zero.mpr (Ne.symm hne), ↓reduceIte, zero_mul]
  exact (mul_eq_zero.mp hsum).resolve_left p_ne_zero_C

/-- The sector of the nonzero squares, `S_+ = ⨆_{ξ ∈ Q} 𝒲_ξ`. -/
noncomputable def secP (p : ℕ) [Fact p.Prime] (U : Type*) [Fintype U] [DecidableEq U] :
    Submodule ℂ (EuclideanSpace ℂ (U → ZMod p)) :=
  ⨆ (ξ : ZMod p) (_ : IsSquare ξ ∧ ξ ≠ 0), eigSec ξ

/-- The sector of the non-squares, `S_- = ⨆_{ξ ∉ □} 𝒲_ξ`. -/
noncomputable def secM (p : ℕ) [Fact p.Prime] (U : Type*) [Fintype U] [DecidableEq U] :
    Submodule ℂ (EuclideanSpace ℂ (U → ZMod p)) :=
  ⨆ (ξ : ZMod p) (_ : ¬ IsSquare ξ), eigSec ξ

/-- **`sectors_ortho`**: `S_+ ⟂ S_-`. -/
theorem sectors_ortho : secP p U ⟂ secM p U := by
  unfold secP secM
  refine Submodule.isOrtho_iSup_left.mpr fun ξ => Submodule.isOrtho_iSup_left.mpr fun hξ =>
    Submodule.isOrtho_iSup_right.mpr fun η => Submodule.isOrtho_iSup_right.mpr fun hη => ?_
  rw [Submodule.isOrtho_iff_inner_eq]
  intro u hu w hw
  exact inner_eigSec_eq_zero (fun (h : ξ = η) => hη (h ▸ hξ.1)) hu hw

theorem eigSec_le_secP {ξ : ZMod p} (hξ : IsSquare ξ ∧ ξ ≠ 0) : eigSec ξ ≤ secP p U := by
  unfold secP
  exact le_iSup₂_of_le ξ hξ (le_refl _)

theorem eigSec_le_secM {ξ : ZMod p} (hξ : ¬ IsSquare ξ) : eigSec ξ ≤ secM p U := by
  unfold secM
  exact le_iSup₂_of_le ξ hξ (le_refl _)

/-! ## `Op` and `Π_𝒱` commute with the translations -/

/-- **`Op` commutes with translations** (`μ` and the kernel are translation invariant). -/
theorem kernelOpC_transl (μ : (U → ZMod p) → ℝ) (hμt : ∀ c x, μ (fun j => x j + c) = μ x)
    (k : (U → ZMod p) → (U → ZMod p) → ℝ)
    (hkt : ∀ c x x', k (fun j => x j + c) (fun j => x' j + c) = k x x') (c : ZMod p)
    (v : EuclideanSpace ℂ (U → ZMod p)) :
    kernelOpC μ k (transl c v) = transl c (kernelOpC μ k v) := by
  ext x
  rw [kernelOpC_ofLp, transl_ofLp, kernelOpC_ofLp]
  conv_rhs => rw [← (shiftEquiv c).symm.sum_comp]
  refine sum_congr rfl fun y _ => ?_
  have e : (shiftEquiv c).symm y = fun j => y j + c := rfl
  rw [e, transl_ofLp, hμt, hμt, hkt]

theorem transl_degMap (μ : (U → ZMod p) → ℝ) (hμt : ∀ c x, μ (fun j => x j + c) = μ x)
    (c : ZMod p) (g : U → ZMod p → ℂ) :
    transl c (degMap μ g) = degMap μ (fun l a => g l (a + c)) := by
  ext x
  rw [transl_ofLp, degMap_apply, degMap_apply, l2MapC_ofLp, l2MapC_ofLp, hμt]
  rfl

/-- **`𝒱` is translation invariant.** -/
theorem degSpace_transl (μ : (U → ZMod p) → ℝ) (hμt : ∀ c x, μ (fun j => x j + c) = μ x)
    (c : ZMod p) {v : EuclideanSpace ℂ (U → ZMod p)} (hv : v ∈ degSpace μ) :
    transl c v ∈ degSpace μ := by
  obtain ⟨hg, hgv⟩ := degRep_spec μ hv
  rw [← hgv, transl_degMap μ hμt]
  refine degMap_mem μ fun l => ?_
  rw [Fintype.sum_equiv (Equiv.addRight c) (fun a => degRep μ v l (a + c))
    (fun a => degRep μ v l a) (fun a => rfl)]
  exact hg l

/-- **`Π_𝒱` commutes with translations.** -/
theorem starProjection_transl (μ : (U → ZMod p) → ℝ) (hμt : ∀ c x, μ (fun j => x j + c) = μ x)
    (c : ZMod p) (y : EuclideanSpace ℂ (U → ZMod p)) :
    (degSpace μ).starProjection (transl c y) = transl c ((degSpace μ).starProjection y) := by
  apply Submodule.eq_starProjection_of_mem_of_inner_eq_zero
  · exact degSpace_transl μ hμt c ((degSpace μ).starProjection_apply_mem y)
  · intro w hw
    have h1 : transl c y - transl c ((degSpace μ).starProjection y) =
        transl c (y - (degSpace μ).starProjection y) := (map_sub _ _ _).symm
    have h2 : w = transl c ((transl c).symm w) := ((transl c).apply_symm_apply w).symm
    rw [h1, h2, (transl c).inner_map_map]
    exact Submodule.starProjection_inner_eq_zero y _
      (by rw [transl_symm]; exact degSpace_transl μ hμt (-c) hw)

/-- The residual `R v = Op v − Π_𝒱 Op v`. -/
noncomputable def resid (μ : (U → ZMod p) → ℝ) (k : (U → ZMod p) → (U → ZMod p) → ℝ) :
    EuclideanSpace ℂ (U → ZMod p) →ₗ[ℂ] EuclideanSpace ℂ (U → ZMod p) :=
  kernelOpC μ k - ((degSpace μ).starProjection : EuclideanSpace ℂ (U → ZMod p) →L[ℂ] _).toLinearMap ∘ₗ
    kernelOpC μ k

theorem resid_apply (μ : (U → ZMod p) → ℝ) (k : (U → ZMod p) → (U → ZMod p) → ℝ)
    (v : EuclideanSpace ℂ (U → ZMod p)) :
    resid μ k v = kernelOpC μ k v - (degSpace μ).starProjection (kernelOpC μ k v) := rfl

/-- **The residual preserves the isotypic subspaces.** -/
theorem resid_eigSec (μ : (U → ZMod p) → ℝ) (hμt : ∀ c x, μ (fun j => x j + c) = μ x)
    (k : (U → ZMod p) → (U → ZMod p) → ℝ)
    (hkt : ∀ c x x', k (fun j => x j + c) (fun j => x' j + c) = k x x') {ξ : ZMod p}
    {u : EuclideanSpace ℂ (U → ZMod p)} (hu : u ∈ eigSec ξ) : resid μ k u ∈ eigSec ξ := by
  intro c
  rw [resid_apply, map_sub, ← starProjection_transl μ hμt, ← kernelOpC_transl μ hμt k hkt, hu c,
    map_smul, map_smul, smul_sub]

/-! ## Mode vectors and sector parts -/

/-- The mode vector `l2MapC(x ↦ e_ξ(x_l))`. -/
noncomputable def modeVec (μ : (U → ZMod p) → ℝ) (ξ : ZMod p) (l : U) :
    EuclideanSpace ℂ (U → ZMod p) :=
  l2MapC μ (fun x => ech ξ (x l))

theorem modeVec_mem (μ : (U → ZMod p) → ℝ) (hμt : ∀ c x, μ (fun j => x j + c) = μ x)
    (ξ : ZMod p) (l : U) : modeVec μ ξ l ∈ eigSec ξ := by
  intro c
  ext x
  rw [transl_ofLp, PiLp.smul_apply, modeVec, l2MapC_ofLp, l2MapC_ofLp, hμt, ech_add_right,
    smul_eq_mul]
  ring

/-- The part of `g` on the modes in `s`: `∑_{ξ ∈ s} ĝ_l(ξ) e_ξ`. -/
noncomputable def gSec (s : ZMod p → Prop) [DecidablePred s] (g : U → ZMod p → ℂ) :
    U → ZMod p → ℂ :=
  fun l a => ∑ ξ ∈ univ.filter s, fcoef (g l) ξ * ech ξ a

omit [Fintype U] [DecidableEq U] in
theorem fcoef_gSec (s : ZMod p → Prop) [DecidablePred s] (g : U → ZMod p → ℂ) (l : U)
    (ξ : ZMod p) : fcoef (gSec s g l) ξ = if s ξ then fcoef (g l) ξ else 0 := by
  have e : gSec s g l = fun a => ∑ η, (if s η then fcoef (g l) η else 0) * ech η a := by
    funext a
    unfold gSec
    rw [sum_filter]
    exact sum_congr rfl fun η _ => by split_ifs <;> simp
  rw [e, fcoef_trig (fun η => if s η then fcoef (g l) η else 0) ξ]

omit [Fintype U] [DecidableEq U] in
theorem gSec_mean (s : ZMod p → Prop) [DecidablePred s] {g : U → ZMod p → ℂ}
    (hg : ∀ l, ∑ a, g l a = 0) (l : U) : ∑ a, gSec s g l a = 0 := by
  unfold gSec
  rw [sum_comm]
  have h : ∀ ξ : ZMod p, ∑ a, fcoef (g l) ξ * ech ξ a =
      fcoef (g l) ξ * (if ξ = 0 then (p : ℂ) else 0) := fun ξ => by rw [← mul_sum, sum_ech]
  rw [sum_congr rfl fun ξ _ => h ξ]
  refine sum_eq_zero fun ξ _ => ?_
  by_cases hξ : ξ = 0
  · rw [hξ, fcoef_zero, hg l, mul_zero, zero_mul]
  · simp only [hξ, ↓reduceIte, mul_zero]

omit [Fintype U] [DecidableEq U] in
theorem gSec_add (s : ZMod p → Prop) [DecidablePred s] (g : U → ZMod p → ℂ) :
    gSec s g + gSec (fun ξ => ¬ s ξ) g = g := by
  funext l a
  show gSec s g l a + gSec (fun ξ => ¬ s ξ) g l a = g l a
  unfold gSec
  rw [sum_filter_add_sum_filter_not, ← fourier_inv]

omit [DecidableEq U] in
theorem degMap_gSec (μ : (U → ZMod p) → ℝ) (s : ZMod p → Prop) [DecidablePred s]
    (g : U → ZMod p → ℂ) :
    degMap μ (gSec s g) = ∑ ξ ∈ univ.filter s, ∑ l, fcoef (g l) ξ • modeVec μ ξ l := by
  ext x
  rw [degMap_apply, l2MapC_ofLp]
  simp only [WithLp.ofLp_sum, WithLp.ofLp_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    modeVec, l2MapC_ofLp]
  unfold degFun gSec
  rw [mul_sum, sum_comm]
  refine sum_congr rfl fun l _ => ?_
  rw [mul_sum]
  exact sum_congr rfl fun ξ _ => by ring

/-- **The residual of a sector part lies in its sector**: if every `ξ ∈ s` with `ĝ(ξ) ≠ 0`
has `𝒲_ξ ≤ S`, then `R(l2MapC(∑_l gSec_l(x_l))) ∈ S`. -/
theorem resid_gSec_mem (μ : (U → ZMod p) → ℝ) (hμt : ∀ c x, μ (fun j => x j + c) = μ x)
    (k : (U → ZMod p) → (U → ZMod p) → ℝ)
    (hkt : ∀ c x x', k (fun j => x j + c) (fun j => x' j + c) = k x x')
    (s : ZMod p → Prop) [DecidablePred s] (g : U → ZMod p → ℂ)
    (S : Submodule ℂ (EuclideanSpace ℂ (U → ZMod p)))
    (hS : ∀ ξ, s ξ → (∃ l, fcoef (g l) ξ ≠ 0) → eigSec ξ ≤ S) :
    resid μ k (degMap μ (gSec s g)) ∈ S := by
  rw [degMap_gSec, map_sum]
  refine Submodule.sum_mem _ fun ξ hξ => ?_
  rw [map_sum]
  refine Submodule.sum_mem _ fun l _ => ?_
  rw [map_smul]
  by_cases h0 : fcoef (g l) ξ = 0
  · rw [h0, zero_smul]; exact S.zero_mem
  · exact S.smul_mem _ (hS ξ (mem_filter.mp hξ).2 ⟨l, h0⟩
      (resid_eigSec μ hμt k hkt (modeVec_mem μ hμt ξ l)))

omit [Fintype U] [DecidableEq U] in
/-- For `p ≡ 3 (mod 4)` the two sector parts of a real `g` are complex conjugates:
`\overline{gSec_{Q}(a)} = gSec_{−Q}(a)` (modes `ξ ↦ −ξ`, and `−1 ∉ Q`). -/
theorem gSec_conj (s : ZMod p → Prop) [DecidablePred s] {g : U → ZMod p → ℂ}
    (hreal : ∀ l a, conj (g l a) = g l a) (l : U) (a : ZMod p) :
    conj (gSec s g l a) = gSec (fun ξ => s (-ξ)) g l a := by
  unfold gSec
  rw [map_sum]
  have hcoef : ∀ ξ, conj (fcoef (g l) ξ) = fcoef (g l) (-ξ) := by
    intro ξ
    unfold fcoef ip
    rw [map_mul, map_inv₀, map_natCast, map_sum]
    congr 1
    refine sum_congr rfl fun b _ => ?_
    rw [map_mul, Complex.conj_conj, hreal, conj_ech, neg_neg]
  have e : ∑ ξ ∈ univ.filter s, conj (fcoef (g l) ξ * ech ξ a) =
      ∑ ξ ∈ univ.filter s, fcoef (g l) (-ξ) * ech (-ξ) a := by
    refine sum_congr rfl fun ξ _ => ?_
    rw [map_mul, hcoef, conj_ech]
  rw [e]
  refine sum_nbij' (fun ξ => -ξ) (fun ξ => -ξ) ?_ ?_ ?_ ?_ ?_
  · intro ξ hξ
    simp only [mem_filter, mem_univ, true_and] at hξ ⊢
    rw [neg_neg]; exact hξ
  · intro ξ hξ
    simp only [mem_filter, mem_univ, true_and] at hξ ⊢
    exact hξ
  · intro ξ _; exact neg_neg ξ
  · intro ξ _; exact neg_neg ξ
  · intro ξ _; rfl

/-! ## The field `coupling` -/

lemma sum_ite_ne_zero (s : ZMod p → Prop) [DecidablePred s] (G : ZMod p → ℝ) (hG : G 0 = 0) :
    ∑ ξ ∈ univ.filter (fun ξ : ZMod p => ξ ≠ 0), (if s ξ then G ξ else 0) =
      ∑ ξ ∈ univ.filter s, G ξ := by
  rw [sum_filter, sum_filter]
  rw [← sum_erase_add _ _ (mem_univ (0 : ZMod p)), ← sum_erase_add _ _ (mem_univ (0 : ZMod p))]
  simp only [ne_eq, not_true_eq_false, ↓reduceIte, add_zero, hG, ite_self]
  refine sum_congr rfl fun ξ hξ => ?_
  have h0 := ne_of_mem_erase hξ
  simp only [h0, not_false_eq_true, ↓reduceIte]

/-- **`RouteAInputs.coupling` in the complex realization** (`cor:spec2:coupling`, complex form,
on the two translation sectors): if `eq:spec:coupling` holds for every degree-one `F_V`
(`CouplingBoundCx`, for instance `couplingBound_cx`), then every `v ∈ 𝒱` splits as
`v = v_+ + v_-` with `v_± ∈ 𝒱`, residuals `(I − Π_𝒱)Op v_± ∈ S_±`, and
`‖(I − Π_𝒱)Op v_±‖² ≤ r²∑_{ξ ∈ Ξ_±}(qX ξ ĝ(ξ) + η_B|ĝ(ξ)|²)` with `ĝ = degCoef μ v`,
`Ξ_+ = {sgn}`, `Ξ_- = {¬ sgn}`, `sgn ξ = (ξ ∈ Q, ξ ≠ 0)`. -/
theorem cx_coupling (μ : (U → ZMod p) → ℝ)
    (hinv : ∀ (s c : ZMod p) (x : U → ZMod p), s ≠ 0 → IsSquare s → μ (affLab s c x) = μ x)
    (k : (U → ZMod p) → (U → ZMod p) → ℝ)
    (hkt : ∀ c x x', k (fun j => x j + c) (fun j => x' j + c) = k x x')
    (qX : ZMod p → (U → ℂ) → ℝ) (hqX0 : ∀ ξ, qX ξ 0 = 0) {ηB : ℝ}
    (hbound : CouplingBoundCx μ k qX ηB) :
    ∀ v ∈ degSpace μ, ∃ vp ∈ degSpace μ, ∃ vm ∈ degSpace μ, v = vp + vm ∧
      kernelOpC μ k vp - (degSpace μ).starProjection (kernelOpC μ k vp) ∈ secP p U ∧
      kernelOpC μ k vm - (degSpace μ).starProjection (kernelOpC μ k vm) ∈ secM p U ∧
      ‖kernelOpC μ k vp - (degSpace μ).starProjection (kernelOpC μ k vp)‖ ^ 2 ≤
        rp p ^ 2 * ∑ ξ with (IsSquare ξ ∧ ξ ≠ 0),
          (qX ξ (degCoef μ v ξ) + ηB * Sarkozy.Spectral.sqn (degCoef μ v ξ)) ∧
      ‖kernelOpC μ k vm - (degSpace μ).starProjection (kernelOpC μ k vm)‖ ^ 2 ≤
        rp p ^ 2 * ∑ ξ with ¬ (IsSquare ξ ∧ ξ ≠ 0),
          (qX ξ (degCoef μ v ξ) + ηB * Sarkozy.Spectral.sqn (degCoef μ v ξ)) := by
  have hμt := mu_shift μ hinv
  intro v hv
  obtain ⟨hg, hgv⟩ := degRep_spec μ hv
  set g := degRep μ v with hgdef
  -- the bound on a sector part
  have hG0 : qX 0 (degCoef μ v 0) + ηB * Sarkozy.Spectral.sqn (degCoef μ v 0) = 0 := by
    have h0 : degCoef μ v 0 = 0 := by funext l; exact degCoef_zero μ hv l
    rw [h0, hqX0]
    unfold Sarkozy.Spectral.sqn
    simp
  have hsec : ∀ (s : ZMod p → Prop) [DecidablePred s],
      ‖kernelOpC μ k (degMap μ (gSec s g)) -
          (degSpace μ).starProjection (kernelOpC μ k (degMap μ (gSec s g)))‖ ^ 2 ≤
        rp p ^ 2 * ∑ ξ ∈ univ.filter s,
          (qX ξ (degCoef μ v ξ) + ηB * Sarkozy.Spectral.sqn (degCoef μ v ξ)) := by
    intro s _
    have h := hbound (gSec s g) (gSec_mean s hg)
    refine h.trans (le_of_eq ?_)
    congr 1
    have e : ∀ ξ, qX ξ (fun l => fcoef (gSec s g l) ξ) +
        ηB * Sarkozy.Spectral.sqn (fun l => fcoef (gSec s g l) ξ) =
        if s ξ then qX ξ (degCoef μ v ξ) + ηB * Sarkozy.Spectral.sqn (degCoef μ v ξ) else 0 := by
      intro ξ
      simp only [fcoef_gSec]
      by_cases hs : s ξ
      · simp only [hs, ↓reduceIte]
        rfl
      · simp only [hs, ↓reduceIte]
        have h0 : (fun _ : U => (0 : ℂ)) = 0 := rfl
        rw [h0, hqX0]
        unfold Sarkozy.Spectral.sqn
        simp
    rw [sum_congr rfl fun ξ _ => e ξ]
    exact sum_ite_ne_zero s _ hG0
  refine ⟨degMap μ (gSec (fun ξ => IsSquare ξ ∧ ξ ≠ 0) g), degMap_mem μ (gSec_mean _ hg),
    degMap μ (gSec (fun ξ => ¬ (IsSquare ξ ∧ ξ ≠ 0)) g), degMap_mem μ (gSec_mean _ hg),
    ?_, ?_, ?_, hsec _, hsec _⟩
  · rw [← map_add, gSec_add, hgv]
  · exact resid_gSec_mem μ hμt k hkt _ g (secP p U) fun ξ hξ _ => eigSec_le_secP hξ
  · refine resid_gSec_mem μ hμt k hkt _ g (secM p U) fun ξ hξ hne => ?_
    by_cases hsq : IsSquare ξ
    · exfalso
      have hξ0 : ξ = 0 := by
        by_contra h0; exact hξ ⟨hsq, h0⟩
      obtain ⟨l, hl⟩ := hne
      apply hl
      rw [hξ0, fcoef_zero, hg l, mul_zero]
    · exact eigSec_le_secM hsq

end Sarkozy.SpectralD.Cx
