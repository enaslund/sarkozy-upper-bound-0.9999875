module

public import Sarkozy.Mixing.SectorLemma

/-!
# Sectors and differences of tensor products

`lem:sector`(a) (Sectors) and the two bounds of `lem:sector`(b) (Differences), for coordinates
`j` with finite probability spaces `(A_j, π_j)`, `(B_j, β_j)`, sector-preserving operators at
the coordinates with `spec j = false` and arbitrary spectator operators at `spec j = true`
(several spectator coordinates together play the role of `T_0`).

* `prodOp_sector_intertwine`, `prodOp_sector_intertwine'`, `prodOp_maps_sector`: `T` maps
  `H_S(π)` into `H_S(β)` (on the support of the target law; everywhere when `T_j 1 = 1`
  everywhere, as for the Markov operators `condMatrix`).
* `prodOp_sector_bound`: a tensor product of arbitrary operators `R_j` bounded by `c_j` on the
  coordinate sectors of `H_S` is bounded by `∏_j c_j` on `H_S`; `prodOp_sector_norm`: for
  sector-preserving coordinates, `‖T|_{H_S}‖ ≤ ‖T_0‖ δ_S` (the norm assertion of (a), as an
  upper bound).
* `wNorm_add_le`: Minkowski's inequality for weighted `L²` norms.
* `difference_telescoping` (the first bound of (b), by telescoping; the empty sum on `H_∅`
  shows that `T' - T` vanishes there) and `difference_triangle` (the second bound,
  `‖T_0‖ (δ'_S + δ_S)`).

The bounds are stated with the weights `w_k = diffWeight`: `‖T_0‖` (`c0_k`) at spectators,
`κ_k` (or `δ_k`) on `S` and `1` off `S`, so `∏_{k ≠ j} w_k = ‖T_0‖ ∏_{k ∈ S∖{j}} κ_k` and
`∏_k w_k = ‖T_0‖ δ_S`. Not formalized: equality of norms in (a), the adjoint and
operator-matrix clauses of (a), and the refinements of (b) about symmetric and skew parts.
-/

@[expose] public section

open Finset
open scoped BigOperators Matrix

namespace Sarkozy.Mixing

open Sarkozy.IndexSupport

section Norm

variable {B : Type*} [Fintype B]

/-- The weighted norm `‖h‖_β = (∑_b β(b) h(b)²)^{1/2}`. -/
noncomputable def wNorm (β : B → ℝ) (h : B → ℝ) : ℝ := Real.sqrt (∑ b, β b * h b ^ 2)

theorem wNorm_nonneg (β : B → ℝ) (h : B → ℝ) : 0 ≤ wNorm β h := Real.sqrt_nonneg _

/-- Minkowski's inequality for weighted `L²` norms. -/
theorem wNorm_add_le {β : B → ℝ} (hβ : ∀ b, 0 ≤ β b) (f g : B → ℝ) :
    wNorm β (f + g) ≤ wNorm β f + wNorm β g := by
  set a := ∑ b, β b * f b ^ 2 with ha
  set c := ∑ b, β b * g b ^ 2 with hc
  have ha0 : 0 ≤ a := Finset.sum_nonneg (fun b _ => mul_nonneg (hβ b) (sq_nonneg _))
  have hc0 : 0 ≤ c := Finset.sum_nonneg (fun b _ => mul_nonneg (hβ b) (sq_nonneg _))
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq univ (fun b => Real.sqrt (β b) * f b)
    (fun b => Real.sqrt (β b) * g b)
  have he1 (b : B) : Real.sqrt (β b) * f b * (Real.sqrt (β b) * g b) = β b * (f b * g b) := by
    rw [show Real.sqrt (β b) * f b * (Real.sqrt (β b) * g b) =
      (Real.sqrt (β b) * Real.sqrt (β b)) * (f b * g b) by ring, Real.mul_self_sqrt (hβ b)]
  have he2 (b : B) (h : B → ℝ) : (Real.sqrt (β b) * h b) ^ 2 = β b * h b ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (hβ b)]
  simp only [he1, he2] at hcs
  rw [← ha, ← hc] at hcs
  have hsum : ∑ b, β b * (f + g) b ^ 2 = a + 2 * ∑ b, β b * (f b * g b) + c := by
    rw [ha, hc, Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    apply sum_congr rfl
    intro b _
    simp only [Pi.add_apply]
    ring
  have hcross : ∑ b, β b * (f b * g b) ≤ Real.sqrt a * Real.sqrt c := by
    have h := Real.abs_le_sqrt hcs
    rw [Real.sqrt_mul ha0] at h
    exact (le_abs_self _).trans h
  unfold wNorm
  rw [hsum, ← ha, ← hc]
  rw [Real.sqrt_le_left (by positivity)]
  have hsa := Real.sq_sqrt ha0
  have hsc := Real.sq_sqrt hc0
  nlinarith [Real.sqrt_nonneg a, Real.sqrt_nonneg c]

theorem wNorm_sq {β : B → ℝ} (hβ : ∀ b, 0 ≤ β b) (h : B → ℝ) :
    wNorm β h ^ 2 = ∑ b, β b * h b ^ 2 :=
  Real.sq_sqrt (Finset.sum_nonneg (fun b _ => mul_nonneg (hβ b) (sq_nonneg _)))

theorem wNorm_le_of_sq_le {β : B → ℝ} {h : B → ℝ} {C N : ℝ} (hC : 0 ≤ C)
    (hsq : ∑ b, β b * h b ^ 2 ≤ C ^ 2 * N ^ 2) (hN : 0 ≤ N) : wNorm β h ≤ C * N := by
  unfold wNorm
  rw [Real.sqrt_le_left (mul_nonneg hC hN)]
  nlinarith

end Norm

section Coordinate

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]

/-- A sector-preserving coordinate intertwines the coordinate projections at every row `b`
where `T 1 = 1`. -/
theorem wProj_intertwine_row {π : A → ℝ} {β : B → ℝ} {T : Matrix B A ℝ}
    (hcol : ∀ a, ∑ b, β b * T b a = π a) (s : Bool) (b : B) (hb : ∑ a, T b a = 1) (a : A) :
    (wProj β false s * T) b a = (T * wProj π false s) b a := by
  have havg : (avgMatrix β * T) b a = (T * avgMatrix π) b a := by
    simp only [Matrix.mul_apply, avgMatrix, hcol, ← Finset.sum_mul, hb, one_mul]
  cases s
  · simpa only [wProj, Bool.false_eq_true, ite_false] using havg
  · simp only [wProj, Bool.false_eq_true, ite_false, ite_true, Matrix.sub_mul, Matrix.mul_sub,
      Matrix.one_mul, Matrix.mul_one, Matrix.sub_apply, havg]

end Coordinate

section Product

variable {K : Type*} [Fintype K] [DecidableEq K] {A B : K → Type*} [∀ j, Fintype (A j)]
  [∀ j, Fintype (B j)] [∀ j, DecidableEq (A j)]

/-- A tensor product of operators bounded by `c_j` on the coordinate sectors of `H_S` is
bounded by `∏_j c_j` on `H_S`. -/
theorem prodOp_sector_bound (π : ∀ j, A j → ℝ) (β : ∀ j, B j → ℝ) (R : ∀ j, Matrix (B j) (A j) ℝ)
    (spec : K → Bool) (l : K → Bool) (hπ1 : ∀ j, ∑ a, π j a = 1) (hβ : ∀ j b, 0 ≤ β j b)
    (c : K → ℝ)
    (hR : ∀ j f, wProj (π j) (spec j) (l j) *ᵥ f = f →
      ∑ b, β j b * (R j *ᵥ f) b ^ 2 ≤ c j ^ 2 * ∑ a, π j a * f a ^ 2)
    (X : (∀ j, A j) → ℝ) (hX : wSectorProj π spec l *ᵥ X = X) :
    ∑ b, prodW β b * (prodOp R *ᵥ X) b ^ 2 ≤ (∏ j, c j) ^ 2 * ∑ a, prodW π a * X a ^ 2 := by
  have hD (j : K) (h : A j → ℝ) : h ⬝ᵥ (Matrix.diagonal (π j) *ᵥ h) = ∑ a, π j a * h a ^ 2 := by
    simp only [dotProduct, Matrix.mulVec_diagonal, sq]
    apply sum_congr rfl
    intro a _
    ring
  have hcoord (j : K) : ((c j ^ 2) • ((wProj (π j) (spec j) (l j))ᵀ * Matrix.diagonal (π j) *
      wProj (π j) (spec j) (l j)) - (wProj (π j) (spec j) (l j))ᵀ * wGram (β j) (R j) *
      wProj (π j) (spec j) (l j)).PosSemidef := by
    apply posSemidef_of_quadratic
    · rw [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_mul, Matrix.transpose_mul,
        Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
        Matrix.diagonal_transpose, wGram_transpose, Matrix.mul_assoc, Matrix.mul_assoc]
    · intro h
      rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
        wProj_transpose_mul, wProj_transpose_mul, hD, ← wEnergy_eq]
      have hidem : wProj (π j) (spec j) (l j) *ᵥ (wProj (π j) (spec j) (l j) *ᵥ h) =
          wProj (π j) (spec j) (l j) *ᵥ h := by
        rw [Matrix.mulVec_mulVec, wProj_mul (hπ1 j), ite_eq_left rfl]
      have := hR j _ hidem
      linarith
  have hL := piKron_sub_posSemidef (fun j => by
      have h1 := Matrix.PosSemidef.conjTranspose_mul_mul_same (wGram_posSemidef (hβ j) (R j))
        (wProj (π j) (spec j) (l j))
      rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h1) hcoord
  rw [piKron_smul] at hL
  have hq := quadratic_nonneg_of_posSemidef hL X
  rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul] at hq
  have hPG : piKron (fun j => (wProj (π j) (spec j) (l j))ᵀ * wGram (β j) (R j) *
      wProj (π j) (spec j) (l j)) =
      (wSectorProj π spec l)ᵀ * wGram (prodW β) (prodOp R) * wSectorProj π spec l := by
    rw [wGram_prodOp, wSectorProj, piKron_transpose, piKron_mul, piKron_mul]
  have hPD : piKron (fun j => (wProj (π j) (spec j) (l j))ᵀ * Matrix.diagonal (π j) *
      wProj (π j) (spec j) (l j)) =
      (wSectorProj π spec l)ᵀ * Matrix.diagonal (prodW π) * wSectorProj π spec l := by
    rw [← piKron_diagonal, wSectorProj, piKron_transpose, piKron_mul, piKron_mul]
  rw [hPG, hPD] at hq
  have h1 : X ⬝ᵥ (((wSectorProj π spec l)ᵀ * wGram (prodW β) (prodOp R) * wSectorProj π spec l) *ᵥ X)
      = ∑ b, prodW β b * (prodOp R *ᵥ X) b ^ 2 := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_transpose_mulVec,
      dotProduct_comm, hX, wEnergy_eq]
  have h2 : X ⬝ᵥ (((wSectorProj π spec l)ᵀ * Matrix.diagonal (prodW π) * wSectorProj π spec l) *ᵥ X)
      = ∑ a, prodW π a * X a ^ 2 := by
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_transpose_mulVec,
      dotProduct_comm, hX]
    simp only [dotProduct, Matrix.mulVec_diagonal, sq]
    apply sum_congr rfl
    intro a _
    ring
  rw [h1, h2] at hq
  rw [← Finset.prod_pow]
  linarith

/-- The weights of `lem:sector`(b): `‖T_0‖` at spectators, `κ_j` on `S`, `1` off `S`. -/
def diffWeight (spec l : K → Bool) (c0 κ : K → ℝ) (k : K) : ℝ :=
  if spec k then c0 k else if l k then κ k else 1

omit [Fintype K] [DecidableEq K] [∀ j, Fintype (B j)] in
theorem eq_const_of_avg {π : ∀ j, A j → ℝ} {j : K} {f : A j → ℝ}
    (hf : wProj (π j) false false *ᵥ f = f) : f = fun _ => ∑ a, π j a * f a := by
  funext x
  have h := congrFun hf x
  simp only [wProj, Bool.false_eq_true, ite_false, Matrix.mulVec, dotProduct, avgMatrix] at h
  exact h.symm

/-- **`lem:sector`(b), the telescoping bound.** At sector-preserving coordinates `T_j`, `T'_j`
fix the constants on the support of `β_j`, preserve the means, have `‖T^∘_j‖, ‖T'^∘_j‖ ≤ κ_j`
and `‖T'^∘_j - T^∘_j‖ ≤ d_j`; at spectators `T'_j = T_j` with `‖T_j‖ ≤ c0_j`. Then on `H_S`,
`‖(T' - T) X‖ ≤ (∑_{k ∈ S} d_k ∏_{j ≠ k} w_j) ‖X‖`, `w = diffWeight`; in particular `T' - T`
vanishes on `H_∅` (empty sum). -/
theorem difference_telescoping (π : ∀ j, A j → ℝ) (β : ∀ j, B j → ℝ)
    (T T' : ∀ j, Matrix (B j) (A j) ℝ) (spec l : K → Bool) (hπ : ∀ j a, 0 ≤ π j a)
    (hπ1 : ∀ j, ∑ a, π j a = 1) (hβ : ∀ j b, 0 ≤ β j b)
    (hrow : ∀ j, spec j = false → ∀ b, β j b ≠ 0 → ∑ a, T j b a = 1)
    (hrow' : ∀ j, spec j = false → ∀ b, β j b ≠ 0 → ∑ a, T' j b a = 1)
    (hcol : ∀ j, spec j = false → ∀ a, ∑ b, β j b * T j b a = π j a)
    (heq : ∀ j, spec j = true → T' j = T j)
    (c0 κ d : K → ℝ) (hc0 : ∀ j, 0 ≤ c0 j) (hκ0 : ∀ j, 0 ≤ κ j) (hd0 : ∀ j, 0 ≤ d j)
    (hspec : ∀ j, spec j = true → ∀ f,
      ∑ b, β j b * (T j *ᵥ f) b ^ 2 ≤ c0 j ^ 2 * ∑ a, π j a * f a ^ 2)
    (hκ : ∀ j, spec j = false → ∀ f, ∑ a, π j a * f a = 0 →
      ∑ b, β j b * (T j *ᵥ f) b ^ 2 ≤ κ j ^ 2 * ∑ a, π j a * f a ^ 2 ∧
      ∑ b, β j b * (T' j *ᵥ f) b ^ 2 ≤ κ j ^ 2 * ∑ a, π j a * f a ^ 2)
    (hd : ∀ j, spec j = false → ∀ f, ∑ a, π j a * f a = 0 →
      ∑ b, β j b * ((T' j - T j) *ᵥ f) b ^ 2 ≤ d j ^ 2 * ∑ a, π j a * f a ^ 2)
    (X : (∀ j, A j) → ℝ) (hX : wSectorProj π spec l *ᵥ X = X) :
    wNorm (prodW β) ((prodOp T' - prodOp T) *ᵥ X) ≤
      (∑ k ∈ univ.filter (fun k => spec k = false ∧ l k = true),
        d k * ∏ j : {j // j ≠ k}, diffWeight spec l c0 κ j) * wNorm (prodW π) X := by
  have hβP : ∀ b, 0 ≤ prodW β b := fun b => Finset.prod_nonneg (fun j _ => hβ j _)
  have hβ1 (j : K) (hj : spec j = false) : ∑ b, β j b = 1 := by
    rw [← hπ1 j, ← Finset.sum_congr rfl (fun a _ => hcol j hj a), Finset.sum_comm]
    apply sum_congr rfl
    intro b _
    rw [← Finset.mul_sum]
    by_cases hb : β j b = 0
    · rw [hb, zero_mul]
    · rw [hrow j hj b hb, mul_one]
  have hw0 (k : K) : 0 ≤ diffWeight spec l c0 κ k := by
    unfold diffWeight
    split_ifs
    · exact hc0 k
    · exact hκ0 k
    · exact zero_le_one
  -- energies on the constants
  have hconst (j : K) (hj : spec j = false) (M : Matrix (B j) (A j) ℝ)
      (hM : ∀ b, β j b ≠ 0 → ∑ a, M b a = 1) (f : A j → ℝ)
      (hf : wProj (π j) false false *ᵥ f = f) :
      ∑ b, β j b * (M *ᵥ f) b ^ 2 = ∑ a, π j a * f a ^ 2 := by
    have hfc := eq_const_of_avg (π := π) hf
    set m := ∑ a, π j a * f a
    have hMf (b : B j) : β j b * (M *ᵥ f) b ^ 2 = β j b * m ^ 2 := by
      by_cases hb : β j b = 0
      · rw [hb, zero_mul, zero_mul]
      · rw [hfc]
        simp only [Matrix.mulVec, dotProduct, ← Finset.sum_mul, hM b hb, one_mul]
    simp only [hMf, ← Finset.sum_mul, hβ1 j hj, one_mul]
    rw [hfc]
    simp only [← Finset.sum_mul, hπ1 j, one_mul]
  -- the coordinate bounds for `T`, `T'` (weight `w_j`) and for `T' - T` (weight `d_j` or `0`)
  have hmean (j : K) (hj : spec j = false) (hlj : l j = true) (f : A j → ℝ)
      (hf : wProj (π j) (spec j) (l j) *ᵥ f = f) : ∑ a, π j a * f a = 0 := by
    rw [← hf]
    simp only [hj, hlj, wProj, Bool.false_eq_true, ite_false, ite_true, Matrix.sub_mulVec,
      Matrix.one_mulVec, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
    simp only [Matrix.mulVec, dotProduct, avgMatrix, ← Finset.sum_mul, hπ1 j, one_mul]
    ring
  have hbndT (j : K) (M : Matrix (B j) (A j) ℝ) (hMT : M = T j ∨ M = T' j) (f : A j → ℝ)
      (hf : wProj (π j) (spec j) (l j) *ᵥ f = f) :
      ∑ b, β j b * (M *ᵥ f) b ^ 2 ≤ diffWeight spec l c0 κ j ^ 2 * ∑ a, π j a * f a ^ 2 := by
    unfold diffWeight
    cases hj : spec j
    · cases hlj : l j
      · simp only [Bool.false_eq_true, ite_false, one_pow, one_mul]
        rw [hj, hlj] at hf
        rcases hMT with rfl | rfl
        · exact (hconst j hj _ (hrow j hj) f hf).le
        · exact (hconst j hj _ (hrow' j hj) f hf).le
      · simp only [Bool.false_eq_true, ite_false, ite_true]
        have h0 := hmean j hj hlj f hf
        rcases hMT with rfl | rfl
        · exact (hκ j hj f h0).1
        · exact (hκ j hj f h0).2
    · simp only [ite_true]
      have hTT : M = T j := by
        rcases hMT with h | h
        · exact h
        · rw [h, heq j hj]
      rw [hTT]
      exact hspec j hj f
  have hbndD (j : K) (f : A j → ℝ) (hf : wProj (π j) (spec j) (l j) *ᵥ f = f) :
      ∑ b, β j b * ((T' j - T j) *ᵥ f) b ^ 2 ≤
        (if spec j = false ∧ l j = true then d j else 0) ^ 2 * ∑ a, π j a * f a ^ 2 := by
    cases hj : spec j
    · cases hlj : l j
      · simp only [Bool.false_eq_true, and_false, ite_false]
        rw [hj, hlj] at hf
        have hfc := eq_const_of_avg (π := π) hf
        have h0 (b : B j) : β j b * ((T' j - T j) *ᵥ f) b ^ 2 = 0 := by
          by_cases hb : β j b = 0
          · rw [hb, zero_mul]
          · rw [hfc]
            simp only [Matrix.mulVec, dotProduct, Matrix.sub_apply, ← Finset.sum_mul,
              Finset.sum_sub_distrib, hrow' j hj b hb, hrow j hj b hb, sub_self, zero_mul]
            ring
        simp only [h0, sum_const_zero]
        exact mul_nonneg (sq_nonneg _)
          (Finset.sum_nonneg (fun a _ => mul_nonneg (hπ j a) (sq_nonneg _)))
      · simp only [and_self, ite_true]
        exact hd j hj f (hmean j hj hlj f hf)
    · simp only [Bool.true_eq_false, false_and, ite_false]
      rw [heq j hj, sub_self, Matrix.zero_mulVec]
      simp
  -- telescoping over the coordinates switched to `T'`
  let mix (s : Finset K) : ∀ j, Matrix (B j) (A j) ℝ := fun j => if j ∈ s then T' j else T j
  have hmix (s : Finset K) (j : K) : mix s j = T j ∨ mix s j = T' j := by
    simp only [mix]
    split_ifs
    · exact Or.inr rfl
    · exact Or.inl rfl
  have hclaim : ∀ s : Finset K, wNorm (prodW β) ((prodOp (mix s) - prodOp T) *ᵥ X) ≤
      (∑ k ∈ s.filter (fun k => spec k = false ∧ l k = true),
        d k * ∏ j : {j // j ≠ k}, diffWeight spec l c0 κ j) * wNorm (prodW π) X := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      have h0 : prodOp (mix ∅) = prodOp T := by
        simp only [mix, Finset.notMem_empty, ite_false]
      rw [h0, sub_self, Matrix.zero_mulVec]
      simp [wNorm]
    | @insert k s hk ih =>
      -- the single-coordinate difference
      let R : ∀ j, Matrix (B j) (A j) ℝ := Function.update (mix s) k (T' k - T k)
      have hsplit : prodOp (mix (insert k s)) - prodOp (mix s) = prodOp R := by
        ext b a
        simp only [Matrix.sub_apply, prodOp, R]
        rw [Fintype.prod_eq_mul_prod_subtype_ne _ k, Fintype.prod_eq_mul_prod_subtype_ne _ k,
          Fintype.prod_eq_mul_prod_subtype_ne _ k]
        have hrest : ∏ j : {j // j ≠ k}, mix (insert k s) j (b j) (a j) =
            ∏ j : {j // j ≠ k}, Function.update (mix s) k (T' k - T k) j (b j) (a j) := by
          apply prod_congr rfl
          intro j _
          rw [Function.update_of_ne j.2]
          simp only [mix, Finset.mem_insert, j.2, false_or]
        have hrest' : ∏ j : {j // j ≠ k}, mix s j (b j) (a j) =
            ∏ j : {j // j ≠ k}, Function.update (mix s) k (T' k - T k) j (b j) (a j) := by
          apply prod_congr rfl
          intro j _
          rw [Function.update_of_ne j.2]
        rw [hrest, hrest', Function.update_self]
        simp only [mix, Finset.mem_insert, true_or, ite_true, hk, ite_false, Matrix.sub_apply]
        ring
      have hRbound := prodOp_sector_bound π β R spec l hπ1 hβ
        (Function.update (fun j => diffWeight spec l c0 κ j) k
          (if spec k = false ∧ l k = true then d k else 0))
        (fun j f hf => by
          by_cases hjk : j = k
          · subst hjk
            simp only [R, Function.update_self]
            exact hbndD j f hf
          · simp only [R, Function.update_of_ne hjk]
            exact hbndT j (mix s j) (hmix s j) f hf) X hX
      have hprod : ∏ j, Function.update (fun j => diffWeight spec l c0 κ j) k
          (if spec k = false ∧ l k = true then d k else 0) j =
          (if spec k = false ∧ l k = true then d k else 0) *
            ∏ j : {j // j ≠ k}, diffWeight spec l c0 κ j := by
        rw [Fintype.prod_eq_mul_prod_subtype_ne _ k, Function.update_self]
        congr 1
        apply prod_congr rfl
        intro j _
        rw [Function.update_of_ne j.2]
      rw [hprod] at hRbound
      have hC0 : 0 ≤ (if spec k = false ∧ l k = true then d k else 0) *
          ∏ j : {j // j ≠ k}, diffWeight spec l c0 κ j :=
        mul_nonneg (by split_ifs <;> [exact hd0 k; exact le_rfl])
          (Finset.prod_nonneg (fun j _ => hw0 j))
      have hfirst : wNorm (prodW β) (prodOp R *ᵥ X) ≤
          ((if spec k = false ∧ l k = true then d k else 0) *
            ∏ j : {j // j ≠ k}, diffWeight spec l c0 κ j) * wNorm (prodW π) X := by
        apply wNorm_le_of_sq_le hC0 _ (wNorm_nonneg _ _)
        rw [wNorm_sq (β := prodW π) (fun a => Finset.prod_nonneg (fun j _ => hπ j _))]
        exact hRbound
      have hdecomp : (prodOp (mix (insert k s)) - prodOp T) *ᵥ X =
          prodOp R *ᵥ X + (prodOp (mix s) - prodOp T) *ᵥ X := by
        rw [← hsplit, ← Matrix.add_mulVec, sub_add_sub_cancel]
      rw [hdecomp]
      apply (wNorm_add_le hβP _ _).trans
      rw [Finset.filter_insert]
      split_ifs with hkS
      · rw [Finset.sum_insert (by simp [hk]), add_mul]
        apply add_le_add _ ih
        simpa only [hkS, and_self, ite_true] using hfirst
      · have hzero : wNorm (prodW β) (prodOp R *ᵥ X) = 0 := by
          have h := hfirst
          simp only [hkS, ite_false, zero_mul] at h
          exact le_antisymm h (wNorm_nonneg _ _)
        rw [hzero, zero_add]
        exact ih
  have hfin := hclaim univ
  have hmixu : prodOp (mix univ) = prodOp T' := by
    simp only [mix, Finset.mem_univ, ite_true]
  rwa [hmixu] at hfin

/-- A tensor product of sector-preserving operators (bounded by `δ_j` on mean-zero functions)
and spectators (bounded by `c0_j`) is bounded on `H_S` by `∏_j w_j`, `w = diffWeight`, that is
by `‖T_0‖ δ_S` (`lem:sector`(a)). -/
theorem prodOp_sector_norm (π : ∀ j, A j → ℝ) (β : ∀ j, B j → ℝ) (M : ∀ j, Matrix (B j) (A j) ℝ)
    (spec l : K → Bool) (hπ : ∀ j a, 0 ≤ π j a) (hπ1 : ∀ j, ∑ a, π j a = 1)
    (hβ : ∀ j b, 0 ≤ β j b)
    (hrow : ∀ j, spec j = false → ∀ b, β j b ≠ 0 → ∑ a, M j b a = 1)
    (hβ1 : ∀ j, spec j = false → ∑ b, β j b = 1)
    (c0 δ : K → ℝ) (hc0 : ∀ j, 0 ≤ c0 j) (hδ0 : ∀ j, 0 ≤ δ j)
    (hspec : ∀ j, spec j = true → ∀ f,
      ∑ b, β j b * (M j *ᵥ f) b ^ 2 ≤ c0 j ^ 2 * ∑ a, π j a * f a ^ 2)
    (hδ : ∀ j, spec j = false → ∀ f, ∑ a, π j a * f a = 0 →
      ∑ b, β j b * (M j *ᵥ f) b ^ 2 ≤ δ j ^ 2 * ∑ a, π j a * f a ^ 2)
    (X : (∀ j, A j) → ℝ) (hX : wSectorProj π spec l *ᵥ X = X) :
    wNorm (prodW β) (prodOp M *ᵥ X) ≤ (∏ j, diffWeight spec l c0 δ j) * wNorm (prodW π) X := by
  have hw0 (k : K) : 0 ≤ diffWeight spec l c0 δ k := by
    unfold diffWeight
    split_ifs
    · exact hc0 k
    · exact hδ0 k
    · exact zero_le_one
  have hR : ∀ j f, wProj (π j) (spec j) (l j) *ᵥ f = f →
      ∑ b, β j b * (M j *ᵥ f) b ^ 2 ≤ diffWeight spec l c0 δ j ^ 2 * ∑ a, π j a * f a ^ 2 := by
    intro j f hf
    unfold diffWeight
    cases hj : spec j
    · cases hlj : l j
      · simp only [Bool.false_eq_true, ite_false, one_pow, one_mul]
        rw [hj, hlj] at hf
        have hfc := eq_const_of_avg (π := π) hf
        set m := ∑ a, π j a * f a
        have hMf (b : B j) : β j b * (M j *ᵥ f) b ^ 2 = β j b * m ^ 2 := by
          by_cases hb : β j b = 0
          · rw [hb, zero_mul, zero_mul]
          · rw [hfc]
            simp only [Matrix.mulVec, dotProduct, ← Finset.sum_mul, hrow j hj b hb, one_mul]
        simp only [hMf, ← Finset.sum_mul, hβ1 j hj, one_mul]
        rw [hfc]
        simp only [← Finset.sum_mul, hπ1 j, one_mul, le_refl]
      · simp only [Bool.false_eq_true, ite_false, ite_true]
        apply hδ j hj f
        rw [← hf]
        simp only [hj, hlj, wProj, Bool.false_eq_true, ite_false, ite_true, Matrix.sub_mulVec,
          Matrix.one_mulVec, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
        simp only [Matrix.mulVec, dotProduct, avgMatrix, ← Finset.sum_mul, hπ1 j, one_mul]
        ring
    · simp only [ite_true]
      exact hspec j hj f
  have hb := prodOp_sector_bound π β M spec l hπ1 hβ (fun j => diffWeight spec l c0 δ j) hR X hX
  apply wNorm_le_of_sq_le (Finset.prod_nonneg (fun j _ => hw0 j)) _ (wNorm_nonneg _ _)
  rw [wNorm_sq (β := prodW π) (fun a => Finset.prod_nonneg (fun j _ => hπ j _))]
  exact hb

/-- **`lem:sector`(b), the triangle bound.** On `H_S`,
`‖(T' - T) X‖ ≤ (‖T_0‖ δ'_S + ‖T_0‖ δ_S) ‖X‖`. -/
theorem difference_triangle (π : ∀ j, A j → ℝ) (β : ∀ j, B j → ℝ)
    (T T' : ∀ j, Matrix (B j) (A j) ℝ) (spec l : K → Bool) (hπ : ∀ j a, 0 ≤ π j a)
    (hπ1 : ∀ j, ∑ a, π j a = 1) (hβ : ∀ j b, 0 ≤ β j b)
    (hrow : ∀ j, spec j = false → ∀ b, β j b ≠ 0 → ∑ a, T j b a = 1)
    (hrow' : ∀ j, spec j = false → ∀ b, β j b ≠ 0 → ∑ a, T' j b a = 1)
    (hcol : ∀ j, spec j = false → ∀ a, ∑ b, β j b * T j b a = π j a)
    (heq : ∀ j, spec j = true → T' j = T j)
    (c0 δ δ' : K → ℝ) (hc0 : ∀ j, 0 ≤ c0 j) (hδ0 : ∀ j, 0 ≤ δ j) (hδ0' : ∀ j, 0 ≤ δ' j)
    (hspec : ∀ j, spec j = true → ∀ f,
      ∑ b, β j b * (T j *ᵥ f) b ^ 2 ≤ c0 j ^ 2 * ∑ a, π j a * f a ^ 2)
    (hδ : ∀ j, spec j = false → ∀ f, ∑ a, π j a * f a = 0 →
      ∑ b, β j b * (T j *ᵥ f) b ^ 2 ≤ δ j ^ 2 * ∑ a, π j a * f a ^ 2)
    (hδ' : ∀ j, spec j = false → ∀ f, ∑ a, π j a * f a = 0 →
      ∑ b, β j b * (T' j *ᵥ f) b ^ 2 ≤ δ' j ^ 2 * ∑ a, π j a * f a ^ 2)
    (X : (∀ j, A j) → ℝ) (hX : wSectorProj π spec l *ᵥ X = X) :
    wNorm (prodW β) ((prodOp T' - prodOp T) *ᵥ X) ≤
      (∏ j, diffWeight spec l c0 δ' j + ∏ j, diffWeight spec l c0 δ j) * wNorm (prodW π) X := by
  have hβP : ∀ b, 0 ≤ prodW β b := fun b => Finset.prod_nonneg (fun j _ => hβ j _)
  have hβ1 (j : K) (hj : spec j = false) : ∑ b, β j b = 1 := by
    rw [← hπ1 j, ← Finset.sum_congr rfl (fun a _ => hcol j hj a), Finset.sum_comm]
    apply sum_congr rfl
    intro b _
    rw [← Finset.mul_sum]
    by_cases hb : β j b = 0
    · rw [hb, zero_mul]
    · rw [hrow j hj b hb, mul_one]
  have h1 := prodOp_sector_norm π β T' spec l hπ hπ1 hβ hrow' hβ1 c0 δ' hc0 hδ0'
    (fun j hj f => by rw [heq j hj]; exact hspec j hj f) hδ' X hX
  have h2 := prodOp_sector_norm π β T spec l hπ hπ1 hβ hrow hβ1 c0 δ hc0 hδ0 hspec hδ X hX
  have hneg : wNorm (prodW β) (-(prodOp T *ᵥ X)) = wNorm (prodW β) (prodOp T *ᵥ X) := by
    unfold wNorm
    simp only [Pi.neg_apply, neg_sq]
  have hsub : (prodOp T' - prodOp T) *ᵥ X = prodOp T' *ᵥ X + -(prodOp T *ᵥ X) := by
    rw [Matrix.sub_mulVec, sub_eq_add_neg]
  rw [hsub]
  apply (wNorm_add_le hβP _ _).trans
  rw [hneg, add_mul]
  exact add_le_add h1 h2

omit [∀ j, Fintype (A j)] [∀ j, DecidableEq (A j)] in
/-- `(⊗_j P_j)(⊗_j T_j) = ⊗_j (P_j T_j)`, rectangular form. -/
theorem piKron_mul_prodOp (P : ∀ j, Matrix (B j) (B j) ℝ) (T : ∀ j, Matrix (B j) (A j) ℝ) :
    piKron P * prodOp T = prodOp (fun j => P j * T j) := by
  ext b a
  simp only [Matrix.mul_apply, piKron_apply, prodOp, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun j b' => P j (b j) b' * T j b' (a j))).symm

omit [∀ j, Fintype (B j)] [∀ j, DecidableEq (A j)] in
/-- `(⊗_j T_j)(⊗_j Q_j) = ⊗_j (T_j Q_j)`, rectangular form. -/
theorem prodOp_mul_piKron (T : ∀ j, Matrix (B j) (A j) ℝ) (Q : ∀ j, Matrix (A j) (A j) ℝ) :
    prodOp T * piKron Q = prodOp (fun j => T j * Q j) := by
  ext b a
  simp only [Matrix.mul_apply, piKron_apply, prodOp, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun j a' => T j (b j) a' * Q j a' (a j))).symm

/-- **`lem:sector`(a), sectors.** A tensor product of sector-preserving coordinates
(`T_j 1 = 1` on the support of `β_j` and `T_j^* 1 = 1`, that is
`∑_b β_j(b) T_j(b, a) = π_j(a)`) and arbitrary spectators intertwines the sector projections,
`P_S^β T = T P_S^π`, on the support of the target law `β = ⊗_j β_j` (where `L²(β)` lives). -/
theorem prodOp_sector_intertwine [∀ j, DecidableEq (B j)] (π : ∀ j, A j → ℝ)
    (β : ∀ j, B j → ℝ) (T : ∀ j, Matrix (B j) (A j) ℝ) (spec l : K → Bool)
    (hrow : ∀ j, spec j = false → ∀ b, β j b ≠ 0 → ∑ a, T j b a = 1)
    (hcol : ∀ j, spec j = false → ∀ a, ∑ b, β j b * T j b a = π j a)
    (b : ∀ j, B j) (hb : prodW β b ≠ 0) (a : ∀ j, A j) :
    (wSectorProj β spec l * prodOp T) b a = (prodOp T * wSectorProj π spec l) b a := by
  rw [wSectorProj, wSectorProj, piKron_mul_prodOp, prodOp_mul_piKron]
  simp only [prodOp]
  apply prod_congr rfl
  intro j _
  have hbj : β j (b j) ≠ 0 := fun h0 => hb (Finset.prod_eq_zero (mem_univ j) h0)
  cases hj : spec j
  · exact wProj_intertwine_row (hcol j hj) (l j) (b j) (hrow j hj (b j) hbj) (a j)
  · simp only [wProj, ite_true]
    split_ifs <;> simp

/-- `lem:sector`(a) when `T_j 1 = 1` everywhere (for instance for Markov operators
`condMatrix`, `condMatrix_row_sum`): `P_S^β (⊗_j T_j) = (⊗_j T_j) P_S^π`. -/
theorem prodOp_sector_intertwine' [∀ j, DecidableEq (B j)] (π : ∀ j, A j → ℝ)
    (β : ∀ j, B j → ℝ) (T : ∀ j, Matrix (B j) (A j) ℝ) (spec l : K → Bool)
    (hrow : ∀ j, spec j = false → ∀ b, ∑ a, T j b a = 1)
    (hcol : ∀ j, spec j = false → ∀ a, ∑ b, β j b * T j b a = π j a) :
    wSectorProj β spec l * prodOp T = prodOp T * wSectorProj π spec l := by
  rw [wSectorProj, wSectorProj, piKron_mul_prodOp, prodOp_mul_piKron]
  congr 1
  funext j
  ext b a
  cases hj : spec j
  · exact wProj_intertwine_row (hcol j hj) (l j) b (hrow j hj b) a
  · simp only [wProj, ite_true]
    split_ifs <;> simp

/-- `lem:sector`(a): `T` maps `H_S(π)` into `H_S(β)`. -/
theorem prodOp_maps_sector [∀ j, DecidableEq (B j)] (π : ∀ j, A j → ℝ)
    (β : ∀ j, B j → ℝ) (T : ∀ j, Matrix (B j) (A j) ℝ) (spec l : K → Bool)
    (hrow : ∀ j, spec j = false → ∀ b, ∑ a, T j b a = 1)
    (hcol : ∀ j, spec j = false → ∀ a, ∑ b, β j b * T j b a = π j a)
    (X : (∀ j, A j) → ℝ) (hX : wSectorProj π spec l *ᵥ X = X) :
    wSectorProj β spec l *ᵥ (prodOp T *ᵥ X) = prodOp T *ᵥ X := by
  rw [Matrix.mulVec_mulVec, prodOp_sector_intertwine' π β T spec l hrow hcol,
    ← Matrix.mulVec_mulVec, hX]

end Product

end Sarkozy.Mixing
