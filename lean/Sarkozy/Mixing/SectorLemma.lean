module

public import Sarkozy.Mixing.Decay

/-!
# The sector lemma for arbitrary finite probability spaces

`lem:sector`(e) and (c) of `paper/sections/06_lifts_sectors.tex` in the generality of the
paper's setting: finite probability spaces `(A_j, π_j)` and `(B_j, π'_j)` for the coordinates,
arbitrary (not necessarily uniform) source laws, sector-preserving operators
`T_j : L²(π_j) → L²(π'_j)` (`T_j 1 = 1` and `T_j^* 1 = 1`), and spectator coordinates whose
operators are arbitrary.

Operators are matrices `T_j : B_j × A_j → ℝ` acting by `(T_j f)(b) = ∑_a T_j(b,a) f(a)`;
norms are `‖f‖²_{π} = ∑_a π(a) f(a)²` and `‖h‖²_{π'} = ∑_b π'(b) h(b)²`. Sector preservation is
`∑_a T_j(b,a) = 1` for `π'_j(b) ≠ 0` (`T_j 1 = 1` in `L²(π'_j)`) and
`∑_b π'_j(b) T_j(b,a) = π_j(a)` (`T_j^* 1 = 1`). A spectator coordinate (`spec j = true`) has an
arbitrary operator with `‖T_j‖ ≤ δ_j`; a sector-preserving coordinate has `‖T_j^∘‖ ≤ δ_j` on
the `π_j`-mean-zero functions.

The sectors are `H_S = ⊗_{spectators} L²(π_0) ⊗ ⊗_{j∈S} L²_0(π_j) ⊗ ⊗_{j∉S} ℝ1`
(`wSectorProj l`, `l : K → Bool`; at a spectator only `l_j = false` is a nonzero sector).

* `general_exact_support_decay` (`lem:sector`(e)):
  `‖T X‖² = ∑_S ‖T X_S‖² ≤ (∏_{spectators} δ_j²) ∑_S δ_S² ‖X_S‖²`.
* `general_markov_tensor_max` (`lem:sector`(c), no spectator): if `δ_j ≤ 1` for all `j`, then
  `‖(T - J) X‖ ≤ (max_j δ_j) ‖X‖`, `J X = (∫ X dπ) 1`, and conversely every `δ_j` is at most
  any such bound.

The proof is the Gram-kernel argument of `Sarkozy/Mixing/Decay.lean` with the diagonal weight
matrices `diag(π_j)`: the coordinate projections are `diag(π_j)`-self-adjoint, the Gram kernels
`T_jᵀ diag(π'_j) T_j` intertwine them, and Loewner monotonicity of Kronecker products
tensorizes the coordinate bounds.
-/

@[expose] public section

open Finset
open scoped BigOperators Matrix

namespace Sarkozy.Mixing

open Sarkozy.IndexSupport

section Coord

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq A]

/-- The Gram kernel `G = Tᵀ diag(β) T` of an operator `T : L²(π) → L²(β)`. -/
def wGram (β : B → ℝ) (T : Matrix B A ℝ) : Matrix A A ℝ :=
  fun a a' => ∑ b, β b * T b a * T b a'

omit [DecidableEq A] in
theorem wEnergy_eq (β : B → ℝ) (T : Matrix B A ℝ) (f : A → ℝ) :
    ∑ b, β b * (T *ᵥ f) b ^ 2 = f ⬝ᵥ (wGram β T *ᵥ f) := by
  simp only [Matrix.mulVec, dotProduct, wGram, sq, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro a' _
  apply sum_congr rfl
  intro b _
  ring

omit [Fintype A] [DecidableEq A] in
theorem wGram_transpose (β : B → ℝ) (T : Matrix B A ℝ) : (wGram β T)ᵀ = wGram β T := by
  ext a a'
  simp only [Matrix.transpose_apply, wGram]
  apply sum_congr rfl
  intro b _
  ring

omit [DecidableEq A] in
theorem wGram_posSemidef {β : B → ℝ} (hβ : ∀ b, 0 ≤ β b) (T : Matrix B A ℝ) :
    (wGram β T).PosSemidef := by
  apply posSemidef_of_quadratic (wGram_transpose β T)
  intro f
  rw [← wEnergy_eq]
  exact Finset.sum_nonneg (fun b _ => mul_nonneg (hβ b) (sq_nonneg _))

/-- The averaging projection `f ↦ (∫ f dπ) 1`. -/
def avgMatrix (π : A → ℝ) : Matrix A A ℝ := fun _ a' => π a'

/-- The coordinate projections: at a spectator `1` and `0`; at a sector-preserving coordinate
the averaging projection (constants) and its complement (mean zero). -/
def wProj (π : A → ℝ) (spec s : Bool) : Matrix A A ℝ :=
  if spec then (if s then 0 else 1) else (if s then 1 - avgMatrix π else avgMatrix π)

omit [DecidableEq A] in
theorem avgMatrix_mul_self {π : A → ℝ} (hπ1 : ∑ a, π a = 1) :
    avgMatrix π * avgMatrix π = avgMatrix π := by
  ext a a''
  simp only [Matrix.mul_apply, avgMatrix, ← Finset.sum_mul, hπ1, one_mul]

theorem wProj_mul {π : A → ℝ} (hπ1 : ∑ a, π a = 1) (spec s t : Bool) :
    wProj π spec s * wProj π spec t = if s = t then wProj π spec s else 0 := by
  have hm := avgMatrix_mul_self hπ1
  cases spec <;> cases s <;> cases t
  all_goals simp only [wProj, Bool.false_eq_true, ite_false, ite_true, Matrix.mul_sub,
    Matrix.sub_mul, Matrix.one_mul, Matrix.mul_one, hm, sub_self, Matrix.mul_zero, reduceCtorEq]
  all_goals abel

omit [Fintype A] in
theorem wProj_sum (π : A → ℝ) (spec : Bool) : wProj π spec false + wProj π spec true = 1 := by
  cases spec
  all_goals simp only [wProj, Bool.false_eq_true, ite_false, ite_true, add_zero]
  all_goals abel

theorem diag_wProj (π : A → ℝ) (spec s : Bool) :
    Matrix.diagonal π * wProj π spec s = (wProj π spec s)ᵀ * Matrix.diagonal π := by
  have havg : Matrix.diagonal π * avgMatrix π = (avgMatrix π)ᵀ * Matrix.diagonal π := by
    ext a a'
    simp only [Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.transpose_apply, avgMatrix]
  cases spec <;> cases s <;>
    simp only [wProj, Bool.false_eq_true, ite_false, ite_true, Matrix.transpose_sub,
      Matrix.transpose_one, Matrix.transpose_zero, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_one, Matrix.one_mul, Matrix.mul_zero, Matrix.zero_mul, havg]

theorem wProj_transpose_mul (π : A → ℝ) (spec s : Bool) (M : Matrix A A ℝ) (h : A → ℝ) :
    h ⬝ᵥ (((wProj π spec s)ᵀ * M * wProj π spec s) *ᵥ h) =
      (wProj π spec s *ᵥ h) ⬝ᵥ (M *ᵥ (wProj π spec s *ᵥ h)) := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_transpose_mulVec,
    dotProduct_comm]

omit [DecidableEq A] in
/-- The Gram kernel of a sector-preserving operator intertwines the averaging projection. -/
theorem wGram_avg {π : A → ℝ} {β : B → ℝ} {T : Matrix B A ℝ}
    (hrow : ∀ b, β b ≠ 0 → ∑ a, T b a = 1) (hcol : ∀ a, ∑ b, β b * T b a = π a) :
    wGram β T * avgMatrix π = (avgMatrix π)ᵀ * wGram β T := by
  have hrow' (b : B) (a : A) : β b * T b a * ∑ x, T b x = β b * T b a := by
    by_cases hb : β b = 0
    · simp [hb]
    · rw [hrow b hb, mul_one]
  have hrow'' (b : B) (a : A) : β b * (∑ x, T b x) * T b a = β b * T b a := by
    by_cases hb : β b = 0
    · simp [hb]
    · rw [hrow b hb, mul_one]
  ext a a''
  simp only [Matrix.mul_apply, wGram, avgMatrix, Matrix.transpose_apply]
  have h1 : ∑ a', (∑ b, β b * T b a * T b a') * π a'' = π a'' * π a := by
    rw [← Finset.sum_mul, Finset.sum_comm]
    simp only [← Finset.mul_sum, hrow', hcol]
    ring
  have h2 : ∑ x, π a * ∑ b, β b * T b x * T b a'' = π a * π a'' := by
    rw [← Finset.mul_sum, Finset.sum_comm]
    congr 1
    rw [← hcol a'']
    apply sum_congr rfl
    intro b _
    rw [← hrow'' b a'', Finset.mul_sum, Finset.sum_mul]
  rw [h1, h2]
  ring

theorem wGram_wProj {π : A → ℝ} {β : B → ℝ} {T : Matrix B A ℝ} {spec : Bool}
    (hsp : spec = false → (∀ b, β b ≠ 0 → ∑ a, T b a = 1) ∧ (∀ a, ∑ b, β b * T b a = π a))
    (s : Bool) :
    wGram β T * wProj π spec s = (wProj π spec s)ᵀ * wGram β T := by
  cases spec
  · obtain ⟨hrow, hcol⟩ := hsp rfl
    have havg := wGram_avg hrow hcol
    cases s <;> simp only [wProj, Bool.false_eq_true, ite_false, ite_true, Matrix.transpose_sub,
      Matrix.transpose_one, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, havg]
  · cases s <;> simp only [wProj, ite_true, Bool.false_eq_true, ite_false, Matrix.transpose_zero,
      Matrix.transpose_one, Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul]

/-- The coordinate Loewner bounds `Qᵀ G Q ⪯ c² Qᵀ diag(π) Q`. -/
theorem wProj_bound {π : A → ℝ} {β : B → ℝ} {T : Matrix B A ℝ}
    (hπ1 : ∑ a, π a = 1) {spec : Bool}
    (hsp : spec = false → (∀ b, β b ≠ 0 → ∑ a, T b a = 1) ∧ (∀ a, ∑ b, β b * T b a = π a))
    {δ : ℝ}
    (hmix : spec = false → ∀ f, ∑ a, π a * f a = 0 →
      ∑ b, β b * (T *ᵥ f) b ^ 2 ≤ δ ^ 2 * ∑ a, π a * f a ^ 2)
    (hspec : spec = true → ∀ f, ∑ b, β b * (T *ᵥ f) b ^ 2 ≤ δ ^ 2 * ∑ a, π a * f a ^ 2)
    (s : Bool) :
    (((if spec then δ ^ 2 else if s then δ ^ 2 else 1)) •
        ((wProj π spec s)ᵀ * Matrix.diagonal π * wProj π spec s) -
      (wProj π spec s)ᵀ * wGram β T * wProj π spec s).PosSemidef := by
  have hD (h : A → ℝ) : h ⬝ᵥ (Matrix.diagonal π *ᵥ h) = ∑ a, π a * h a ^ 2 := by
    simp only [dotProduct, Matrix.mulVec_diagonal, sq]
    apply sum_congr rfl
    intro a _
    ring
  apply posSemidef_of_quadratic
  · rw [Matrix.transpose_sub, Matrix.transpose_smul, Matrix.transpose_mul, Matrix.transpose_mul,
      Matrix.transpose_mul, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.diagonal_transpose, wGram_transpose, Matrix.mul_assoc, Matrix.mul_assoc]
  · intro h
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
      wProj_transpose_mul, wProj_transpose_mul, hD, ← wEnergy_eq]
    set u := wProj π spec s *ᵥ h with hu
    cases spec
    · simp only [Bool.false_eq_true, ite_false]
      cases s
      · -- the constants: `T u = (∫ h dπ) 1` on the support, both sides equal
        simp only [Bool.false_eq_true, ite_false, one_mul]
        obtain ⟨hrow, hcol⟩ := hsp rfl
        have hu' : u = fun _ => ∑ a, π a * h a := by
          rw [hu]
          funext x
          simp only [wProj, Bool.false_eq_true, ite_false, Matrix.mulVec, dotProduct, avgMatrix]
        have hTu (b : B) : β b * (T *ᵥ u) b ^ 2 = β b * (∑ a, π a * h a) ^ 2 := by
          by_cases hb : β b = 0
          · rw [hb, zero_mul, zero_mul]
          · rw [hu']
            simp only [Matrix.mulVec, dotProduct, ← Finset.sum_mul, hrow b hb, one_mul]
        have hβ1 : ∑ b, β b = 1 := by
          rw [← hπ1, ← Finset.sum_congr rfl (fun a _ => hcol a), Finset.sum_comm]
          apply sum_congr rfl
          intro b _
          rw [← Finset.mul_sum]
          by_cases hb : β b = 0
          · rw [hb, zero_mul]
          · rw [hrow b hb, mul_one]
        simp only [hTu, ← Finset.sum_mul, hβ1, one_mul]
        rw [hu']
        simp only [← Finset.sum_mul, hπ1, one_mul, sub_self, le_refl]
      · simp only [ite_true]
        have hmean : ∑ a, π a * u a = 0 := by
          rw [hu]
          simp only [wProj, Bool.false_eq_true, ite_false, ite_true, Matrix.sub_mulVec,
            Matrix.one_mulVec, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
          simp only [Matrix.mulVec, dotProduct, avgMatrix, ← Finset.sum_mul, hπ1, one_mul]
          ring
        have := hmix rfl u hmean
        linarith
    · simp only [ite_true]
      have := hspec rfl u
      linarith

end Coord

section Product

variable {K : Type*} [Fintype K] [DecidableEq K] {A B : K → Type*} [∀ j, Fintype (A j)]
  [∀ j, Fintype (B j)] [∀ j, DecidableEq (A j)]

/-- The product operator `⊗_j T_j`, `(⊗_j T_j)(b, a) = ∏_j T_j(b_j, a_j)`. -/
def prodOp (T : ∀ j, Matrix (B j) (A j) ℝ) : Matrix (∀ j, B j) (∀ j, A j) ℝ :=
  fun b a => ∏ j, T j (b j) (a j)

/-- The product weights `∏_j w_j(x_j)`. -/
def prodW {C : K → Type*} (w : ∀ j, C j → ℝ) (x : ∀ j, C j) : ℝ := ∏ j, w j (x j)

/-- The sector projections `X ↦ X_S`, `S = {j : l_j}`. -/
def wSectorProj (π : ∀ j, A j → ℝ) (spec : K → Bool) (l : K → Bool) :
    Matrix (∀ j, A j) (∀ j, A j) ℝ :=
  piKron (fun j => wProj (π j) (spec j) (l j))

omit [∀ j, Fintype (A j)] [∀ j, DecidableEq (A j)] in
theorem wGram_prodOp (β : ∀ j, B j → ℝ) (T : ∀ j, Matrix (B j) (A j) ℝ) :
    wGram (prodW β) (prodOp T) = piKron (fun j => wGram (β j) (T j)) := by
  ext a a'
  simp only [wGram, prodW, prodOp, piKron_apply, ← Finset.prod_mul_distrib]
  exact (Fintype.prod_sum (fun j b => β j b * T j b (a j) * T j b (a' j))).symm

omit [DecidableEq K] [∀ j, Fintype (A j)] in
theorem piKron_diagonal (π : ∀ j, A j → ℝ) :
    piKron (fun j => Matrix.diagonal (π j)) = Matrix.diagonal (prodW π) := by
  ext x y
  simp only [piKron_apply, Matrix.diagonal_apply, prodW]
  by_cases h : x = y
  · subst h
    simp
  · rw [ite_eq_right h]
    obtain ⟨j, hj⟩ : ∃ j, x j ≠ y j := by
      by_contra h'
      exact h (funext fun j => not_not.mp (fun hne => h' ⟨j, hne⟩))
    exact prod_eq_zero (mem_univ j) (ite_eq_right hj)

/-- **`lem:sector`(e), exact-support decay, general form.** Coordinates `j` with finite
probability spaces `(A_j, π_j)`, `(B_j, β_j)`; at a sector-preserving coordinate
(`spec j = false`) `T_j` fixes the constants on the support of `β_j`, `T_j^* 1 = 1`, and
`‖T_j f‖ ≤ δ_j ‖f‖` for `π_j`-mean-zero `f`; at a spectator (`spec j = true`) `T_j` is any
operator with `‖T_j‖ ≤ δ_j`. Then `‖T X‖² = ∑_S ‖T X_S‖²` and
`‖T X‖² ≤ ∑_S (∏_{spectators} δ_j² ∏_{j ∈ S} δ_j²) ‖X_S‖²`. -/
theorem general_exact_support_decay (π : ∀ j, A j → ℝ) (β : ∀ j, B j → ℝ)
    (T : ∀ j, Matrix (B j) (A j) ℝ) (spec : K → Bool)
    (hπ1 : ∀ j, ∑ a, π j a = 1) (hβ : ∀ j b, 0 ≤ β j b)
    (hsp : ∀ j, spec j = false →
      (∀ b, β j b ≠ 0 → ∑ a, T j b a = 1) ∧ (∀ a, ∑ b, β j b * T j b a = π j a))
    (δ : K → ℝ)
    (hmix : ∀ j, spec j = false → ∀ f, ∑ a, π j a * f a = 0 →
      ∑ b, β j b * (T j *ᵥ f) b ^ 2 ≤ δ j ^ 2 * ∑ a, π j a * f a ^ 2)
    (hspec : ∀ j, spec j = true → ∀ f,
      ∑ b, β j b * (T j *ᵥ f) b ^ 2 ≤ δ j ^ 2 * ∑ a, π j a * f a ^ 2)
    (X : (∀ j, A j) → ℝ) :
    ∑ b, prodW β b * (prodOp T *ᵥ X) b ^ 2 =
        ∑ l, ∑ b, prodW β b * (prodOp T *ᵥ (wSectorProj π spec l *ᵥ X)) b ^ 2 ∧
      ∑ b, prodW β b * (prodOp T *ᵥ X) b ^ 2 ≤
        ∑ l, (∏ j, (if spec j then δ j ^ 2 else if l j then δ j ^ 2 else 1)) *
          ∑ a, prodW π a * (wSectorProj π spec l *ᵥ X) a ^ 2 := by
  set G := piKron (fun j => wGram (β j) (T j)) with hG
  set D := piKron (fun j => Matrix.diagonal (π j)) with hD
  set P := wSectorProj π spec with hP
  have hGe (f : (∀ j, A j) → ℝ) : ∑ b, prodW β b * (prodOp T *ᵥ f) b ^ 2 = f ⬝ᵥ (G *ᵥ f) := by
    rw [wEnergy_eq, wGram_prodOp]
  have hDe (f : (∀ j, A j) → ℝ) : ∑ a, prodW π a * f a ^ 2 = f ⬝ᵥ (D *ᵥ f) := by
    rw [hD, piKron_diagonal]
    simp only [dotProduct, Matrix.mulVec_diagonal, sq]
    apply sum_congr rfl
    intro a _
    ring
  have hPmul (l l' : K → Bool) : P l * P l' = if l = l' then P l else 0 := by
    simp only [hP, wSectorProj, piKron_mul]
    by_cases h : l = l'
    · subst h
      rw [ite_eq_left rfl]
      congr 1
      funext j
      rw [wProj_mul (hπ1 j), ite_eq_left rfl]
    · rw [ite_eq_right h]
      obtain ⟨j, hj⟩ : ∃ j, l j ≠ l' j := by
        by_contra h'
        exact h (funext fun j => not_not.mp (fun hne => h' ⟨j, hne⟩))
      exact piKron_eq_zero j (by rw [wProj_mul (hπ1 j), ite_eq_right hj])
  have hPsum (f : (∀ j, A j) → ℝ) : ∑ l, P l *ᵥ f = f := by
    rw [← Matrix.sum_mulVec]
    simp only [hP, wSectorProj]
    rw [piKron_sum (fun j (s : Bool) => wProj (π j) (spec j) s)]
    have h (j : K) : ∑ s : Bool, wProj (π j) (spec j) s = 1 := by
      rw [Fintype.sum_bool, add_comm, wProj_sum]
    simp only [h, piKron_one, Matrix.one_mulVec]
  have hGP (l : K → Bool) : G * P l = (P l)ᵀ * G := by
    simp only [hG, hP, wSectorProj, piKron_transpose, piKron_mul]
    congr 1
    funext j
    exact wGram_wProj (hsp j) (l j)
  have hDP (l : K → Bool) : D * P l = (P l)ᵀ * D := by
    simp only [hD, hP, wSectorProj, piKron_transpose, piKron_mul]
    congr 1
    funext j
    exact diag_wProj (π j) (spec j) (l j)
  have hcross (M : Matrix (∀ j, A j) (∀ j, A j) ℝ) (hMP : ∀ l, M * P l = (P l)ᵀ * M)
      (f : (∀ j, A j) → ℝ) (l l' : K → Bool) (hne : l ≠ l') :
      (P l *ᵥ f) ⬝ᵥ (M *ᵥ (P l' *ᵥ f)) = 0 := by
    have hre : (P l *ᵥ f) ⬝ᵥ (M *ᵥ (P l' *ᵥ f)) = f ⬝ᵥ (((P l)ᵀ * M * P l') *ᵥ f) := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_transpose_mulVec,
        dotProduct_comm]
    rw [hre, ← hMP l, Matrix.mul_assoc, hPmul, ite_eq_right hne, Matrix.mul_zero,
      Matrix.zero_mulVec, dotProduct_zero]
  have hdecomp (M : Matrix (∀ j, A j) (∀ j, A j) ℝ) (hMP : ∀ l, M * P l = (P l)ᵀ * M)
      (f : (∀ j, A j) → ℝ) :
      f ⬝ᵥ (M *ᵥ f) = ∑ l, (P l *ᵥ f) ⬝ᵥ (M *ᵥ (P l *ᵥ f)) := by
    conv_lhs => rw [← hPsum f]
    rw [Matrix.mulVec_sum, sum_dotProduct]
    apply sum_congr rfl
    intro l _
    rw [dotProduct_sum, Finset.sum_eq_single l]
    · intro l' _ hl'
      exact hcross M hMP f l l' (Ne.symm hl')
    · intro h
      exact absurd (mem_univ l) h
  refine ⟨?_, ?_⟩
  · rw [hGe, hdecomp G hGP]
    apply sum_congr rfl
    intro l _
    rw [hGe]
  · rw [hGe, hdecomp G hGP]
    apply Finset.sum_le_sum
    intro l _
    rw [hDe]
    have hL : ((∏ j, (if spec j then δ j ^ 2 else if l j then δ j ^ 2 else 1)) •
        ((P l)ᵀ * D * P l) - (P l)ᵀ * G * P l).PosSemidef := by
      have hfac : (∏ j, (if spec j then δ j ^ 2 else if l j then δ j ^ 2 else 1)) •
          ((P l)ᵀ * D * P l) =
          piKron (fun j => ((if spec j then δ j ^ 2 else if l j then δ j ^ 2 else 1)) •
            ((wProj (π j) (spec j) (l j))ᵀ * Matrix.diagonal (π j) * wProj (π j) (spec j) (l j))) := by
        rw [piKron_smul]
        congr 1
        simp only [hP, hD, wSectorProj, piKron_transpose, piKron_mul]
      have hPGP : (P l)ᵀ * G * P l = piKron (fun j => (wProj (π j) (spec j) (l j))ᵀ *
          wGram (β j) (T j) * wProj (π j) (spec j) (l j)) := by
        simp only [hP, hG, wSectorProj, piKron_transpose, piKron_mul]
      rw [hfac, hPGP]
      apply piKron_sub_posSemidef
      · intro j
        have h1 := Matrix.PosSemidef.conjTranspose_mul_mul_same (wGram_posSemidef (hβ j) (T j))
          (wProj (π j) (spec j) (l j))
        rwa [Matrix.conjTranspose_eq_transpose_of_trivial] at h1
      · intro j
        exact wProj_bound (hπ1 j) (hsp j) (hmix j) (hspec j) (l j)
    have hq := quadratic_nonneg_of_posSemidef hL X
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
      at hq
    have h1 : X ⬝ᵥ (((P l)ᵀ * G * P l) *ᵥ X) = (P l *ᵥ X) ⬝ᵥ (G *ᵥ (P l *ᵥ X)) := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_transpose_mulVec,
        dotProduct_comm]
    have h2 : X ⬝ᵥ (((P l)ᵀ * D * P l) *ᵥ X) = (P l *ᵥ X) ⬝ᵥ (D *ᵥ (P l *ᵥ X)) := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_transpose_mulVec,
        dotProduct_comm]
    rw [h1, h2] at hq
    linarith

omit [DecidableEq K] [∀ j, Fintype (A j)] [∀ j, DecidableEq (A j)] in
theorem prodOp_one [∀ j, DecidableEq (A j)] :
    prodOp (fun j => (1 : Matrix (A j) (A j) ℝ)) = 1 := by
  ext x y
  simp only [prodOp, Matrix.one_apply]
  rw [prod_indicator_forall (fun j => x j = y j)]
  by_cases h : x = y
  · subst h
    simp
  · rw [ite_eq_right (fun h' => h (funext h')), ite_eq_right h]

/-- Parseval for the weighted exact-support sectors: `‖X‖²_π = ∑_S ‖X_S‖²_π`. -/
theorem general_parseval (π : ∀ j, A j → ℝ) (spec : K → Bool) (hπ : ∀ j a, 0 ≤ π j a)
    (hπ1 : ∀ j, ∑ a, π j a = 1) (X : (∀ j, A j) → ℝ) :
    ∑ a, prodW π a * X a ^ 2 = ∑ l, ∑ a, prodW π a * (wSectorProj π spec l *ᵥ X) a ^ 2 := by
  have h := (general_exact_support_decay π π (fun j => (1 : Matrix (A j) (A j) ℝ)) spec hπ1 hπ
    (fun j _ => ⟨fun b _ => by simp [Matrix.one_apply],
      fun a => by simp [Matrix.one_apply]⟩)
    (fun _ => 1) (fun j _ f _ => by simp)
    (fun j _ f => by simp) X).1
  simpa only [prodOp_one, Matrix.one_mulVec] using h

omit [∀ j, Fintype (A j)] [∀ j, DecidableEq (A j)] in
/-- The one-coordinate marginal of product weights. -/
theorem sum_prodW_single {C : K → Type*} [∀ j, Fintype (C j)] (w : ∀ j, C j → ℝ)
    (hw1 : ∀ j, ∑ x, w j x = 1) (j₀ : K) (φ : C j₀ → ℝ) :
    ∑ x, prodW w x * φ (x j₀) = ∑ y, w j₀ y * φ y := by
  rw [sum_split j₀]
  apply sum_congr rfl
  intro y _
  simp only [prodW, prod_split j₀ w]
  have hφ (r : ∀ j : {j // j ≠ j₀}, C j) : φ ((Equiv.piSplitAt j₀ C).symm (y, r) j₀) = φ y := by
    simp
  simp only [hφ]
  rw [show (∑ r : (∀ j : {j // j ≠ j₀}, C j), w j₀ y * (∏ j : {j // j ≠ j₀}, w j (r j)) * φ y) =
      w j₀ y * φ y * ∑ r : (∀ j : {j // j ≠ j₀}, C j), ∏ j : {j // j ≠ j₀}, w j (r j) by
    rw [Finset.mul_sum]
    apply sum_congr rfl
    intro r _
    ring]
  rw [← Fintype.prod_sum (fun (j : {j // j ≠ j₀}) x => w j x)]
  simp only [hw1, prod_const_one, mul_one]

/-- **`lem:sector`(c), the Markov tensor maximum, general marginals.** No spectator; every
`T_j` is sector-preserving with `‖T_j^∘‖ ≤ 1`. For `c ≥ 0`, `‖(T - J) X‖_{π'} ≤ c ‖X‖_π` for
every `X` (`J X = (∫ X dπ) 1`) if and only if every `T_j` contracts `π_j`-mean-zero functions
by `c`; that is, `‖T - J‖ = max_j ‖T_j^∘‖`. -/
theorem general_markov_tensor_max (π : ∀ j, A j → ℝ) (β : ∀ j, B j → ℝ)
    (T : ∀ j, Matrix (B j) (A j) ℝ) (hπ : ∀ j a, 0 ≤ π j a) (hπ1 : ∀ j, ∑ a, π j a = 1)
    (hβ : ∀ j b, 0 ≤ β j b)
    (hrow : ∀ j b, β j b ≠ 0 → ∑ a, T j b a = 1) (hcol : ∀ j a, ∑ b, β j b * T j b a = π j a)
    (hcontr : ∀ j f, ∑ a, π j a * f a = 0 →
      ∑ b, β j b * (T j *ᵥ f) b ^ 2 ≤ 1 ^ 2 * ∑ a, π j a * f a ^ 2)
    {c : ℝ} (hc : 0 ≤ c) :
    (∀ X : (∀ j, A j) → ℝ,
      ∑ b, prodW β b * ((prodOp T *ᵥ X) b - ∑ a, prodW π a * X a) ^ 2 ≤
        c ^ 2 * ∑ a, prodW π a * X a ^ 2) ↔
    (∀ j f, ∑ a, π j a * f a = 0 →
      ∑ b, β j b * (T j *ᵥ f) b ^ 2 ≤ c ^ 2 * ∑ a, π j a * f a ^ 2) := by
  have hβ1 (j : K) : ∑ b, β j b = 1 := by
    rw [← hπ1 j, ← Finset.sum_congr rfl (fun a _ => hcol j a), Finset.sum_comm]
    apply sum_congr rfl
    intro b _
    rw [← Finset.mul_sum]
    by_cases hb : β j b = 0
    · rw [hb, zero_mul]
    · rw [hrow j b hb, mul_one]
  constructor
  · intro hglob j₀ f hf
    have h := hglob (fun a => f (a j₀))
    have hmean : ∑ a, prodW π a * f (a j₀) = 0 := by rw [sum_prodW_single π hπ1 j₀ f, hf]
    rw [hmean] at h
    simp only [sub_zero] at h
    have hT (b : ∀ j, B j) (hb : prodW β b ≠ 0) :
        (prodOp T *ᵥ fun a => f (a j₀)) b = (T j₀ *ᵥ f) (b j₀) := by
      have hbj (j : K) : β j (b j) ≠ 0 := fun h0 => hb (prod_eq_zero (mem_univ j) h0)
      simp only [Matrix.mulVec, dotProduct, prodOp]
      rw [sum_split j₀]
      apply sum_congr rfl
      intro x _
      simp only [prod_split j₀ (fun j a => T j (b j) a)]
      have hf' (r : ∀ j : {j // j ≠ j₀}, A j) : f ((Equiv.piSplitAt j₀ A).symm (x, r) j₀) = f x := by
        simp
      simp only [hf']
      rw [show (∑ r : (∀ j : {j // j ≠ j₀}, A j), T j₀ (b j₀) x *
          (∏ j : {j // j ≠ j₀}, T j (b j) (r j)) * f x) =
          T j₀ (b j₀) x * f x * ∑ r : (∀ j : {j // j ≠ j₀}, A j),
            ∏ j : {j // j ≠ j₀}, T j (b j) (r j) by
        rw [Finset.mul_sum]
        apply sum_congr rfl
        intro r _
        ring]
      rw [← Fintype.prod_sum (fun (j : {j // j ≠ j₀}) a => T j (b j) a)]
      simp only [fun (j : {j // j ≠ j₀}) => hrow j (b j) (hbj j), prod_const_one, mul_one]
    have hl : ∑ b, prodW β b * (prodOp T *ᵥ fun a => f (a j₀)) b ^ 2 =
        ∑ y, β j₀ y * (T j₀ *ᵥ f) y ^ 2 := by
      rw [← sum_prodW_single β hβ1 j₀ (fun y => (T j₀ *ᵥ f) y ^ 2)]
      apply sum_congr rfl
      intro b _
      by_cases hb : prodW β b = 0
      · rw [hb, zero_mul, zero_mul]
      · rw [hT b hb]
    rw [hl, sum_prodW_single π hπ1 j₀ (fun y => f y ^ 2)] at h
    exact h
  · intro hloc X
    set c' := min c 1 with hc'
    have hc'0 : 0 ≤ c' := le_min hc zero_le_one
    have hc'1 : c' ≤ 1 := min_le_right _ _
    have hmix (j : K) : ∀ f, ∑ a, π j a * f a = 0 →
        ∑ b, β j b * (T j *ᵥ f) b ^ 2 ≤ c' ^ 2 * ∑ a, π j a * f a ^ 2 := by
      intro f hf
      rcases le_total c 1 with h1 | h1
      · rw [hc', min_eq_left h1]
        exact hloc j f hf
      · rw [hc', min_eq_right h1]
        exact hcontr j f hf
    set m := ∑ a, prodW π a * X a with hm
    set Y := fun a => X a - m with hY
    have hrowP (b : ∀ j, B j) (hb : prodW β b ≠ 0) : ∑ a, prodOp T b a = 1 := by
      have hbj (j : K) : β j (b j) ≠ 0 := fun h0 => hb (prod_eq_zero (mem_univ j) h0)
      simp only [prodOp]
      rw [← Fintype.prod_sum (fun j a => T j (b j) a)]
      simp only [fun j => hrow j (b j) (hbj j), prod_const_one]
    have hTY (b : ∀ j, B j) : prodW β b * ((prodOp T *ᵥ X) b - m) ^ 2 =
        prodW β b * (prodOp T *ᵥ Y) b ^ 2 := by
      by_cases hb : prodW β b = 0
      · rw [hb, zero_mul, zero_mul]
      · congr 2
        simp only [hY, Matrix.mulVec, dotProduct, mul_sub, Finset.sum_sub_distrib]
        rw [← Finset.sum_mul, hrowP b hb, one_mul]
    simp only [hTY]
    have hdec := (general_exact_support_decay π β T (fun _ => false) hπ1 hβ
      (fun j _ => ⟨hrow j, hcol j⟩) (fun _ => c') (fun j _ => hmix j)
      (fun j h => absurd h (by simp)) Y).2
    apply hdec.trans
    have hprodπ1 : ∑ a, prodW π a = 1 := by
      simp only [prodW]
      rw [← Fintype.prod_sum (fun j a => π j a)]
      simp only [hπ1, prod_const_one]
    have hzero : wSectorProj π (fun _ => false) (fun _ => false) *ᵥ Y = 0 := by
      funext a
      simp only [wSectorProj, wProj, Bool.false_eq_true, ite_false, Matrix.mulVec, dotProduct,
        piKron_apply, avgMatrix, Pi.zero_apply]
      have : ∑ y, (∏ j, π j (y j)) * Y y = 0 := by
        simp only [hY, mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul]
        change ∑ y, prodW π y * X y - (∑ y, prodW π y) * m = 0
        rw [hprodπ1, one_mul, hm, sub_self]
      exact this
    have hterm (l : K → Bool) : (∏ j, (if (fun _ => false) j then (fun _ => c') j ^ 2 else
        if l j then (fun _ => c') j ^ 2 else 1)) *
        ∑ a, prodW π a * (wSectorProj π (fun _ => false) l *ᵥ Y) a ^ 2 ≤
        c ^ 2 * ∑ a, prodW π a * (wSectorProj π (fun _ => false) l *ᵥ Y) a ^ 2 := by
      have hS0 : 0 ≤ ∑ a, prodW π a * (wSectorProj π (fun _ => false) l *ᵥ Y) a ^ 2 :=
        Finset.sum_nonneg (fun a _ => mul_nonneg (Finset.prod_nonneg (fun j _ => hπ j _))
          (sq_nonneg _))
      by_cases hl : ∃ j, l j = true
      · apply mul_le_mul_of_nonneg_right _ hS0
        simp only [Bool.false_eq_true, ite_false]
        obtain ⟨j₀, hj₀⟩ := hl
        rw [Fintype.prod_eq_mul_prod_subtype_ne _ j₀, ite_eq_left hj₀]
        have hle : ∏ j : {j // j ≠ j₀}, (if l j then c' ^ 2 else 1) ≤ 1 :=
          Finset.prod_le_one₀ (fun j _ => by split_ifs <;> positivity)
            (fun j _ => by split_ifs <;> nlinarith)
        have hnn : 0 ≤ ∏ j : {j // j ≠ j₀}, (if l j then c' ^ 2 else 1) :=
          Finset.prod_nonneg (fun j _ => by split_ifs <;> positivity)
        have hc'c : c' ^ 2 ≤ c ^ 2 := pow_le_pow_left₀ hc'0 (min_le_left _ _) 2
        nlinarith
      · have hl0 : l = fun _ => false := by
          funext j
          cases hj : l j
          · rfl
          · exact absurd ⟨j, hj⟩ hl
        subst hl0
        rw [hzero]
        simp
    apply (Finset.sum_le_sum (fun l _ => hterm l)).trans
    rw [← Finset.mul_sum, ← general_parseval π (fun _ => false) hπ hπ1 Y]
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg c)
    -- variance at most second moment
    have hvar : ∑ a, prodW π a * Y a ^ 2 = ∑ a, prodW π a * X a ^ 2 - m ^ 2 := by
      have h1 : ∑ a, prodW π a * Y a ^ 2 = ∑ a, ((prodW π a * X a ^ 2 - 2 * m * (prodW π a * X a)) +
          m ^ 2 * prodW π a) := by
        apply sum_congr rfl
        intro a _
        simp only [hY]
        ring
      rw [h1, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
        ← hm, hprodπ1]
      ring
    rw [hvar]
    nlinarith [sq_nonneg m]

end Product

end Sarkozy.Mixing
