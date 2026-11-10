module

public import Sarkozy.IndexSupport.Operators

@[expose] public section

/-!
# The difference of two tensor products of Markov operators (`lem:record:one-stage-folded-e`(d))

`paper/sections/20c_middle_frame.tex`, `lem:record:one-stage-folded-e`(d), the operator part, in
abstract form. Coordinates `e` with finite sets `Ω e` (the paper's `V_{c_p}`), the Euclidean dot
product (the uniform law, up to a common factor), and two families of doubly stochastic matrices
`Kp e`, `K0 e` (the paper's `𝒦₊^{(c_p)}`, `𝒦₀^{(c_p)}`). Each fixes the constants on both sides,
so it
preserves the two sectors of its coordinate (constants, mean-zero functions), and the tensor
products preserve the product sectors `H_S` (`lem:sector`). On `H_∅` the difference
`⊗ Kp - ⊗ K0` vanishes; on `H_{{e}}` it is the factor `Kp e - K0 e`; on `H_S` with `|S| ≥ 2` it has
norm at most `∏_S ‖Kp^∘‖ + ∏_S ‖K0^∘‖ ≤ α_e α_{e'} + β_e β_{e'}` (all factors at most one). Its norm
is the largest over the sectors (`norm_le_of_sectors`).

* `twoSectors`: the sector system of one coordinate (constants and mean-zero functions).
* `sectorOperator_of_stochastic`: a doubly stochastic matrix with `‖K f‖ ≤ α ‖f‖` on mean-zero
  functions is a sector operator with weights `1, α`.
* `norm_le_of_sectors`: an operator that preserves every sector of a sector system, with norm at
  most `c` on each, has norm at most `c`.
* **`tensor_diff_norm_le`**: `‖(⊗ Kp - ⊗ K0) f‖ ≤ D ‖f‖` as soon as `‖Kp e - K0 e‖ ≤ δ_e ≤ D` on the
  mean-zero functions and `α_e α_{e'} + β_e β_{e'} ≤ D` for `e ≠ e'`, with `0 ≤ α, β ≤ 1`.
* `tensor_diff_form_le`: the same bound for the bilinear form `⟨g, (⊗ Kp - ⊗ K0) f⟩`.
-/

open Finset
open scoped BigOperators Matrix

namespace Sarkozy.FirstStagePaper

open Sarkozy.IndexSupport

/-! ## One coordinate: constants and mean-zero functions -/

section TwoSectors

variable (Ω : Type*) [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]

/-- The projections of one coordinate: onto the constants (`false`) and onto the mean-zero
functions (`true`). -/
noncomputable def twoProj (s : Bool) : Matrix Ω Ω ℝ :=
  if s then 1 - meanMatrix Ω else meanMatrix Ω

/-- **The two sectors of one coordinate** (`lem:sector`): the constants and the mean-zero
functions. -/
noncomputable def twoSectors : SectorSystem Ω Bool where
  proj := twoProj Ω
  zero := false
  transpose_proj s := by
    cases s
    · exact meanMatrix_transpose Ω
    · simp only [twoProj, ↓reduceIte, Matrix.transpose_sub, Matrix.transpose_one,
        meanMatrix_transpose]
  proj_mul_proj s t := by
    have hm := meanMatrix_mul_self Ω
    cases s <;> cases t
    · simp only [twoProj, Bool.false_eq_true, ↓reduceIte, hm]
    · simp only [twoProj, Bool.false_eq_true, ↓reduceIte, Matrix.mul_sub, Matrix.mul_one, hm,
        sub_self]
    · simp only [twoProj, Bool.false_eq_true, ↓reduceIte, Matrix.sub_mul, Matrix.one_mul, hm,
        sub_self, Bool.true_eq_false]
    · simp only [twoProj, ↓reduceIte, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
        Matrix.one_mul, hm, sub_self, sub_zero]
  sum_proj := by
    rw [Fintype.sum_bool]
    simp only [twoProj, ↓reduceIte, Bool.false_eq_true]
    abel
  proj_zero := rfl

theorem twoSectors_proj (s : Bool) : (twoSectors Ω).proj s = twoProj Ω s := rfl

variable {Ω}

omit [DecidableEq Ω] [Nonempty Ω] in
theorem meanMatrix_mulVec_eq_zero {f : Ω → ℝ} (hf : ∑ x, f x = 0) : meanMatrix Ω *ᵥ f = 0 := by
  rw [meanMatrix_mulVec, hf, mul_zero]
  rfl

omit [DecidableEq Ω] in
theorem sum_eq_zero_of_meanMatrix {f : Ω → ℝ} (hf : meanMatrix Ω *ᵥ f = 0) : ∑ x, f x = 0 := by
  rw [meanMatrix_mulVec] at hf
  have h := congrFun hf (Classical.arbitrary Ω)
  simp only [Pi.zero_apply, mul_eq_zero, inv_eq_zero, Nat.cast_eq_zero,
    Fintype.card_ne_zero, false_or] at h
  exact h

/-- On the mean-zero sector the mean vanishes. -/
theorem mean_of_proj_true {f : Ω → ℝ} (hf : twoProj Ω true *ᵥ f = f) : meanMatrix Ω *ᵥ f = 0 := by
  rw [← hf, Matrix.mulVec_mulVec]
  simp only [twoProj, ↓reduceIte, Matrix.mul_sub, Matrix.mul_one, meanMatrix_mul_self, sub_self,
    Matrix.zero_mulVec]

/-- **A doubly stochastic matrix with norm at most `α` on the mean-zero functions is a sector
operator** for `twoSectors`, with the weights `1` (constants) and `α` (mean-zero). -/
theorem sectorOperator_of_stochastic {K : Matrix Ω Ω ℝ} (hrow : K * meanMatrix Ω = meanMatrix Ω)
    (hcol : meanMatrix Ω * K = meanMatrix Ω) {α : ℝ}
    (hα : ∀ f : Ω → ℝ, ∑ x, f x = 0 → (K *ᵥ f) ⬝ᵥ (K *ᵥ f) ≤ α ^ 2 * (f ⬝ᵥ f)) :
    SectorOperator (twoSectors Ω) K (fun s => if s then α else 1) := by
  have hfix : ∀ f : Ω → ℝ, meanMatrix Ω *ᵥ f = f → K *ᵥ f = f := by
    intro f hf
    rw [← hf, Matrix.mulVec_mulVec, hrow]
  refine ⟨?_, ?_, ?_⟩
  · intro s f hf
    cases s
    · change meanMatrix Ω *ᵥ (K *ᵥ f) = K *ᵥ f
      have hf' : meanMatrix Ω *ᵥ f = f := hf
      rw [hfix f hf', hf']
    · change twoProj Ω true *ᵥ (K *ᵥ f) = K *ᵥ f
      have h0 := mean_of_proj_true hf
      simp only [twoProj, ↓reduceIte]
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_mulVec, hcol, h0, sub_zero]
  · intro f hf
    exact hfix f hf
  · intro s f hf
    cases s
    · have hf' : meanMatrix Ω *ᵥ f = f := hf
      simp only [Bool.false_eq_true, ↓reduceIte, one_pow, one_mul, hfix f hf', le_refl]
    · simp only [↓reduceIte]
      exact hα f (sum_eq_zero_of_meanMatrix (mean_of_proj_true hf))

/-- The difference of two doubly stochastic matrices maps the mean-zero sector into itself, with
norm at most `δ` if it has norm at most `δ` on the mean-zero functions. -/
theorem rangeBound_sub {Kp K0 : Matrix Ω Ω ℝ} (hcolp : meanMatrix Ω * Kp = meanMatrix Ω)
    (hcol0 : meanMatrix Ω * K0 = meanMatrix Ω) {δ : ℝ}
    (hδ : ∀ f : Ω → ℝ, ∑ x, f x = 0 →
      ((Kp - K0) *ᵥ f) ⬝ᵥ ((Kp - K0) *ᵥ f) ≤ δ ^ 2 * (f ⬝ᵥ f)) :
    RangeBound (twoProj Ω true) (Kp - K0) δ := by
  refine RangeBound.of_vec ((twoSectors Ω).transpose_proj true) ((twoSectors Ω).proj_mul_self true)
    ?_ ?_
  · intro f _
    simp only [twoProj, ↓reduceIte]
    rw [Matrix.sub_mulVec 1 (meanMatrix Ω), Matrix.one_mulVec, Matrix.mulVec_mulVec,
      Matrix.mul_sub, hcolp, hcol0, sub_self, Matrix.zero_mulVec, sub_zero]
  · intro f hf
    exact hδ f (sum_eq_zero_of_meanMatrix (mean_of_proj_true hf))

/-- The identity on the constants. -/
theorem rangeBound_one_false : RangeBound (twoProj Ω false) (1 : Matrix Ω Ω ℝ) 1 := by
  refine RangeBound.of_vec ((twoSectors Ω).transpose_proj false)
    ((twoSectors Ω).proj_mul_self false) ?_ ?_
  · intro f hf
    rw [Matrix.one_mulVec]
    exact hf
  · intro f _
    rw [Matrix.one_mulVec, one_pow, one_mul]

end TwoSectors

/-! ## The norm of a sector-preserving operator -/

section Max

variable {Ω S : Type*} [Fintype Ω] [DecidableEq Ω] [Fintype S] [DecidableEq S]

/-- The squared norm of a sum of mutually orthogonal sector components. -/
theorem dotProduct_sum_sectors (H : SectorSystem Ω S) (g : S → Ω → ℝ)
    (hg : ∀ s, H.proj s *ᵥ g s = g s) :
    (∑ s, g s) ⬝ᵥ (∑ s, g s) = ∑ s, g s ⬝ᵥ g s := by
  rw [sum_dotProduct]
  refine sum_congr rfl fun s _ => ?_
  rw [dotProduct_sum]
  rw [Finset.sum_eq_single s]
  · intro t _ hts
    exact H.dotProduct_eq_zero (Ne.symm hts) (hg s) (hg t)
  · intro h
    exact absurd (mem_univ s) h

/-- **An operator that preserves every sector, with norm at most `c` on each, has norm at most
`c`** (`lem:sector`(a): the norm is the largest over the sectors). -/
theorem norm_le_of_sectors (H : SectorSystem Ω S) (T : Matrix Ω Ω ℝ) {c : ℝ}
    (hmaps : ∀ s f, H.proj s *ᵥ f = f → H.proj s *ᵥ (T *ᵥ f) = T *ᵥ f)
    (hnorm : ∀ s f, H.proj s *ᵥ f = f → (T *ᵥ f) ⬝ᵥ (T *ᵥ f) ≤ c ^ 2 * (f ⬝ᵥ f))
    (f : Ω → ℝ) : (T *ᵥ f) ⬝ᵥ (T *ᵥ f) ≤ c ^ 2 * (f ⬝ᵥ f) := by
  have hf : f = ∑ s, H.proj s *ᵥ f := (H.sum_proj_mulVec f).symm
  have hmem : ∀ s, H.proj s *ᵥ (H.proj s *ᵥ f) = H.proj s *ᵥ f := fun s => H.proj_proj_mulVec s f
  have hTf : T *ᵥ f = ∑ s, T *ᵥ (H.proj s *ᵥ f) := by
    conv_lhs => rw [hf]
    rw [Matrix.mulVec_sum]
  rw [hTf, dotProduct_sum_sectors H _ (fun s => hmaps s _ (hmem s))]
  conv_rhs => rw [hf, dotProduct_sum_sectors H _ hmem, mul_sum]
  exact sum_le_sum fun s _ => hnorm s _ (hmem s)

end Max

/-! ## Two vectors -/

section Triangle

variable {Ω : Type*} [Fintype Ω]

/-- The triangle inequality in squared form. -/
theorem sub_dotProduct_le {u v : Ω → ℝ} {a b N : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hN : 0 ≤ N)
    (hu : u ⬝ᵥ u ≤ a ^ 2 * N) (hv : v ⬝ᵥ v ≤ b ^ 2 * N) :
    (u - v) ⬝ᵥ (u - v) ≤ (a + b) ^ 2 * N := by
  have hexp : (u - v) ⬝ᵥ (u - v) = u ⬝ᵥ u - 2 * (u ⬝ᵥ v) + v ⬝ᵥ v := by
    simp only [sub_dotProduct, dotProduct_sub, dotProduct_comm v u]
    ring
  have hcs := dotProduct_sq_le u v
  have huu := dotProduct_self_nonneg u
  have hvv := dotProduct_self_nonneg v
  have hprod : (u ⬝ᵥ u) * (v ⬝ᵥ v) ≤ (a * b * N) ^ 2 := by
    have := mul_le_mul hu hv hvv (by positivity)
    nlinarith
  have habN : 0 ≤ a * b * N := by positivity
  have hneg : -(u ⬝ᵥ v) ≤ a * b * N := by
    have h2 : (u ⬝ᵥ v) ^ 2 ≤ (a * b * N) ^ 2 := le_trans hcs hprod
    linarith [(abs_le_of_sq_le_sq' h2 habN).1]
  rw [hexp]
  nlinarith

end Triangle

/-! ## The tensor difference -/

section Tensor

variable {E : Type*} [Fintype E] [DecidableEq E] {Ω : E → Type*} [∀ e, Fintype (Ω e)]
  [∀ e, DecidableEq (Ω e)] [∀ e, Nonempty (Ω e)]

omit [∀ e, DecidableEq (Ω e)] [∀ e, Nonempty (Ω e)] [∀ e, Fintype (Ω e)] in
/-- `piKron` is additive in one coordinate. -/
theorem piKron_ite_sub (A B C : ∀ e, Matrix (Ω e) (Ω e) ℝ) (e₀ : E) :
    piKron (fun e => if e = e₀ then A e else C e) - piKron (fun e => if e = e₀ then B e else C e) =
      piKron (fun e => if e = e₀ then A e - B e else C e) := by
  ext x y
  simp only [Matrix.sub_apply, piKron_apply]
  rw [Fintype.prod_eq_mul_prod_compl e₀, Fintype.prod_eq_mul_prod_compl e₀,
    Fintype.prod_eq_mul_prod_compl e₀]
  have hc : ∀ F : ∀ e, Matrix (Ω e) (Ω e) ℝ,
      ∏ e ∈ ({e₀}ᶜ : Finset E), (if e = e₀ then F e else C e) (x e) (y e) =
        ∏ e ∈ ({e₀}ᶜ : Finset E), C e (x e) (y e) := by
    intro F
    refine prod_congr rfl fun e he => ?_
    rw [mem_compl, mem_singleton] at he
    simp only [he, ↓reduceIte]
  rw [hc A, hc B, hc (fun e => A e - B e)]
  simp only [↓reduceIte, Matrix.sub_apply]
  ring

omit [∀ e, Fintype (Ω e)] [∀ e, DecidableEq (Ω e)] [∀ e, Nonempty (Ω e)] in
/-- A product of factors in `[0, 1]` is at most the product of two of them. -/
theorem prod_le_two_of_le_one {w : E → ℝ} (h0 : ∀ e, 0 ≤ w e) (h1 : ∀ e, w e ≤ 1) {e₀ e₁ : E}
    (hne : e₀ ≠ e₁) : ∏ e, w e ≤ w e₀ * w e₁ := by
  rw [← Finset.mul_prod_erase univ w (mem_univ e₀),
    ← Finset.mul_prod_erase (univ.erase e₀) w (mem_erase.mpr ⟨Ne.symm hne, mem_univ e₁⟩),
    ← mul_assoc]
  have hr : ∏ e ∈ (univ.erase e₀).erase e₁, w e ≤ 1 :=
    Finset.prod_le_one₀ (fun e _ => h0 e) (fun e _ => h1 e)
  have hab : 0 ≤ w e₀ * w e₁ := mul_nonneg (h0 e₀) (h0 e₁)
  calc w e₀ * w e₁ * ∏ e ∈ (univ.erase e₀).erase e₁, w e ≤ w e₀ * w e₁ * 1 :=
        mul_le_mul_of_nonneg_left hr hab
    _ = w e₀ * w e₁ := mul_one _

/-- **`lem:record:one-stage-folded-e`(d), the operator bound, abstract form.** Let `Kp e`, `K0 e`
be doubly stochastic (`K * J = J * K = J`, `J` the averaging matrix), with norms at most `α e`,
`β e` (both in `[0, 1]`) and `‖Kp e - K0 e‖ ≤ δ e` on the mean-zero functions of the coordinate
`e`. If `δ e ≤ D` for every `e` and `α e α e' + β e β e' ≤ D` for `e ≠ e'`, then
`‖(⊗_e Kp e - ⊗_e K0 e) f‖ ≤ D ‖f‖` for every `f`. The proof is the paper's: the difference
preserves the sectors `H_S`, vanishes on `H_∅`, is the factor `Kp e - K0 e` on `H_{{e}}`, and has
norm
at most `∏_S α + ∏_S β ≤ α_e α_{e'} + β_e β_{e'}` on `H_S` with `e, e' ∈ S`, `e ≠ e'`. -/
theorem tensor_diff_norm_le (Kp K0 : ∀ e, Matrix (Ω e) (Ω e) ℝ)
    (hrowp : ∀ e, Kp e * meanMatrix (Ω e) = meanMatrix (Ω e))
    (hcolp : ∀ e, meanMatrix (Ω e) * Kp e = meanMatrix (Ω e))
    (hrow0 : ∀ e, K0 e * meanMatrix (Ω e) = meanMatrix (Ω e))
    (hcol0 : ∀ e, meanMatrix (Ω e) * K0 e = meanMatrix (Ω e))
    {α β δ : E → ℝ} (hα0 : ∀ e, 0 ≤ α e) (hα1 : ∀ e, α e ≤ 1) (hβ0 : ∀ e, 0 ≤ β e)
    (hβ1 : ∀ e, β e ≤ 1) (hδ0 : ∀ e, 0 ≤ δ e)
    (hKp : ∀ e (f : Ω e → ℝ), ∑ x, f x = 0 → (Kp e *ᵥ f) ⬝ᵥ (Kp e *ᵥ f) ≤ α e ^ 2 * (f ⬝ᵥ f))
    (hK0 : ∀ e (f : Ω e → ℝ), ∑ x, f x = 0 → (K0 e *ᵥ f) ⬝ᵥ (K0 e *ᵥ f) ≤ β e ^ 2 * (f ⬝ᵥ f))
    (hΔ : ∀ e (f : Ω e → ℝ), ∑ x, f x = 0 →
      ((Kp e - K0 e) *ᵥ f) ⬝ᵥ ((Kp e - K0 e) *ᵥ f) ≤ δ e ^ 2 * (f ⬝ᵥ f))
    {D : ℝ} (hDδ : ∀ e, δ e ≤ D) (hD2 : ∀ e e', e ≠ e' → α e * α e' + β e * β e' ≤ D)
    (f : (∀ e, Ω e) → ℝ) :
    ((piKron Kp - piKron K0) *ᵥ f) ⬝ᵥ ((piKron Kp - piKron K0) *ᵥ f) ≤ D ^ 2 * (f ⬝ᵥ f) := by
  set H : SectorSystem (∀ e, Ω e) (E → Bool) := SectorSystem.pi (fun e => twoSectors (Ω e))
    with hH
  have hp : SectorOperator H (piKron Kp)
      (fun l => ∏ e, (fun s : Bool => if s then α e else 1) (l e)) :=
    SectorOperator.pi (fun e => sectorOperator_of_stochastic (hrowp e) (hcolp e) (hKp e))
  have h0 : SectorOperator H (piKron K0)
      (fun l => ∏ e, (fun s : Bool => if s then β e else 1) (l e)) :=
    SectorOperator.pi (fun e => sectorOperator_of_stochastic (hrow0 e) (hcol0 e) (hK0 e))
  apply norm_le_of_sectors H
  · intro l g hg
    rw [Matrix.sub_mulVec, Matrix.mulVec_sub, hp.maps l g hg, h0.maps l g hg]
  · intro l g hg
    have hgg := dotProduct_self_nonneg g
    by_cases hz : ∀ e, l e = false
    · -- the constants: both products are the identity
      have hl : l = H.zero := funext hz
      rw [hl] at hg
      rw [Matrix.sub_mulVec, hp.id_zero g hg, h0.id_zero g hg, sub_self, zero_dotProduct]
      exact mul_nonneg (sq_nonneg D) hgg
    · push Not at hz
      obtain ⟨e₀, he₀⟩ := hz
      have he₀' : l e₀ = true := by simpa using he₀
      by_cases hsingle : ∀ e, e ≠ e₀ → l e = false
      · -- one coordinate: the difference is the factor `Kp e₀ - K0 e₀`
        set P : ∀ e, Matrix (Ω e) (Ω e) ℝ := fun e => twoProj (Ω e) (l e) with hPdef
        have hHl : H.proj l = piKron P := rfl
        set A : ∀ e, Matrix (Ω e) (Ω e) ℝ := fun e => if e = e₀ then Kp e - K0 e else 1 with hA
        have hKP : ∀ K : ∀ e, Matrix (Ω e) (Ω e) ℝ,
            (∀ e, K e * meanMatrix (Ω e) = meanMatrix (Ω e)) →
            piKron (fun e => K e * P e) = piKron (fun e => if e = e₀ then K e * P e else P e) := by
          intro K hK
          congr 1
          funext e
          by_cases he : e = e₀
          · simp only [he, ↓reduceIte]
          · simp only [he, ↓reduceIte, hPdef, hsingle e he, twoProj, Bool.false_eq_true, hK e]
        have hdiff : (piKron Kp - piKron K0) * piKron P = piKron A * piKron P := by
          rw [Matrix.sub_mul, piKron_mul, piKron_mul, piKron_mul, hKP Kp hrowp, hKP K0 hrow0,
            piKron_ite_sub]
          congr 1
          funext e
          by_cases he : e = e₀
          · simp only [he, ↓reduceIte, hA, Matrix.sub_mul]
          · simp only [he, ↓reduceIte, hA, Matrix.one_mul]
        have hval : (piKron Kp - piKron K0) *ᵥ g = piKron A *ᵥ g := by
          rw [hHl] at hg
          rw [← hg, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hdiff]
        have hRB : RangeBound (piKron P) (piKron A) (∏ e, if e = e₀ then δ e else 1) := by
          refine RangeBound.piKron (fun e => (twoSectors (Ω e)).transpose_proj (l e)) ?_
          intro e
          by_cases he : e = e₀
          · subst he
            simp only [↓reduceIte, hA, hPdef, he₀']
            exact rangeBound_sub (hcolp e) (hcol0 e) (hΔ e)
          · simp only [he, ↓reduceIte, hA, hPdef, hsingle e he]
            exact rangeBound_one_false
        have hnorm := hRB.norm_le (H.transpose_proj l) (f := g) hg
        rw [Finset.prod_ite_eq' univ e₀ δ, ite_eq_left (mem_univ e₀)] at hnorm
        rw [hval]
        refine le_trans hnorm (mul_le_mul_of_nonneg_right ?_ hgg)
        exact pow_le_pow_left₀ (hδ0 e₀) (hDδ e₀) 2
      · -- two coordinates or more
        push Not at hsingle
        obtain ⟨e₁, he₁, hle₁⟩ := hsingle
        have hle₁' : l e₁ = true := by simpa using hle₁
        have hwα : ∏ e, (fun s : Bool => if s then α e else 1) (l e) ≤ α e₀ * α e₁ := by
          have h := prod_le_two_of_le_one
            (w := fun e => (fun s : Bool => if s then α e else 1) (l e))
            (fun e => by cases l e <;> simp [hα0 e]) (fun e => by cases l e <;> simp [hα1 e])
            (Ne.symm he₁)
          simpa only [he₀', hle₁', ↓reduceIte] using h
        have hwβ : ∏ e, (fun s : Bool => if s then β e else 1) (l e) ≤ β e₀ * β e₁ := by
          have h := prod_le_two_of_le_one
            (w := fun e => (fun s : Bool => if s then β e else 1) (l e))
            (fun e => by cases l e <;> simp [hβ0 e]) (fun e => by cases l e <;> simp [hβ1 e])
            (Ne.symm he₁)
          simpa only [he₀', hle₁', ↓reduceIte] using h
        have hwα0 : 0 ≤ ∏ e, (fun s : Bool => if s then α e else 1) (l e) :=
          prod_nonneg fun e _ => by cases l e <;> simp [hα0 e]
        have hwβ0 : 0 ≤ ∏ e, (fun s : Bool => if s then β e else 1) (l e) :=
          prod_nonneg fun e _ => by cases l e <;> simp [hβ0 e]
        have hu : (piKron Kp *ᵥ g) ⬝ᵥ (piKron Kp *ᵥ g) ≤ (α e₀ * α e₁) ^ 2 * (g ⬝ᵥ g) :=
          le_trans (hp.norm_le l g hg)
            (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hwα0 hwα 2) hgg)
        have hv : (piKron K0 *ᵥ g) ⬝ᵥ (piKron K0 *ᵥ g) ≤ (β e₀ * β e₁) ^ 2 * (g ⬝ᵥ g) :=
          le_trans (h0.norm_le l g hg)
            (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hwβ0 hwβ 2) hgg)
        have hab0 : 0 ≤ α e₀ * α e₁ := mul_nonneg (hα0 e₀) (hα0 e₁)
        have hbb0 : 0 ≤ β e₀ * β e₁ := mul_nonneg (hβ0 e₀) (hβ0 e₁)
        rw [Matrix.sub_mulVec]
        refine le_trans (sub_dotProduct_le hab0 hbb0 hgg hu hv)
          (mul_le_mul_of_nonneg_right ?_ hgg)
        exact pow_le_pow_left₀ (add_nonneg hab0 hbb0) (hD2 e₀ e₁ (Ne.symm he₁)) 2

omit [∀ e, DecidableEq (Ω e)] [∀ e, Nonempty (Ω e)] in
/-- **The bilinear form of the tensor difference** (the sharp-bound form of
`lem:record:one-stage-folded-e`(d)): `|⟨g, (⊗ Kp - ⊗ K0) f⟩| ≤ D ‖g‖ ‖f‖`. -/
theorem tensor_diff_form_le (Kp K0 : ∀ e, Matrix (Ω e) (Ω e) ℝ) {D : ℝ} (hD : 0 ≤ D)
    (hnorm : ∀ f : (∀ e, Ω e) → ℝ,
      ((piKron Kp - piKron K0) *ᵥ f) ⬝ᵥ ((piKron Kp - piKron K0) *ᵥ f) ≤ D ^ 2 * (f ⬝ᵥ f))
    (g f : (∀ e, Ω e) → ℝ) :
    |g ⬝ᵥ ((piKron Kp - piKron K0) *ᵥ f)| ≤
      D * Real.sqrt (g ⬝ᵥ g) * Real.sqrt (f ⬝ᵥ f) := by
  have hcs := dotProduct_sq_le g ((piKron Kp - piKron K0) *ᵥ f)
  have hgg := dotProduct_self_nonneg g
  have hff := dotProduct_self_nonneg f
  have h2 : (g ⬝ᵥ ((piKron Kp - piKron K0) *ᵥ f)) ^ 2 ≤
      (D * Real.sqrt (g ⬝ᵥ g) * Real.sqrt (f ⬝ᵥ f)) ^ 2 := by
    have e : (D * Real.sqrt (g ⬝ᵥ g) * Real.sqrt (f ⬝ᵥ f)) ^ 2 = (g ⬝ᵥ g) * (D ^ 2 * (f ⬝ᵥ f)) := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hgg, Real.sq_sqrt hff]
      ring
    rw [e]
    exact le_trans hcs (mul_le_mul_of_nonneg_left (hnorm f) hgg)
  have h0 : 0 ≤ D * Real.sqrt (g ⬝ᵥ g) * Real.sqrt (f ⬝ᵥ f) := by positivity
  exact abs_le_of_sq_le_sq h2 h0

end Tensor

end Sarkozy.FirstStagePaper
