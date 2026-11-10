module

public import Sarkozy.Mixing.Conditional

/-!
# Products of conditional operators: exact-support decay and the Markov tensor maximum

Parts of `lem:sector` (`paper/sections/06_lifts_sectors.tex`) for conditional operators of
couplings with uniform source marginals, which is the case used by
`lem:record:prefix-conductor` and `lem:tr:pairsupport`.

Setting: finitely many coordinates `j`, joint laws `κ_j` of a source label `a_j ∈ A_j` and a
target label `b_j ∈ B_j`, with `κ_{j,A}` uniform on `A_j`; the product joint law `κ = ⊗_j κ_j`
(`prodJoint`). Its conditional operator is the tensor product of the coordinate conditional
operators on the support of `κ_B` (`condMatrix_prodJoint`); each coordinate operator is
sector-preserving (it fixes the constants and integrates against `κ_{j,B}` as against the
uniform law). The sectors of the source are the exact-support sectors
`H_S = ⊗_{j∈S} L²_0(A_j) ⊗ ⊗_{j∉S} ℝ1`, the sectors of `productSectors (wholeChains A)`, indexed
by `l : ∀ j, Fin 2` (`S = {j : l_j = 1}`).

* `lem:sector`(e) (`exact_support_decay`): `‖T g‖²_{L²(κ_B)} = ∑_S ‖T g_S‖² ≤ ∑_S δ_S² ‖g_S‖²`,
  `δ_S = ∏_{j∈S} δ_j`, where `δ_j` bounds the coordinate operator on mean-zero functions.
* `lem:sector`(c) (`markov_tensor_max`): `‖T - J‖ = max_j ‖T_j^∘‖`, stated as: for `c ≥ 0`,
  `‖(T - J) g‖ ≤ c ‖g‖` for all `g` if and only if every coordinate operator contracts
  mean-zero functions by `c` (`J g = (E g) 1`).
* `lem:sector`(f) (`product_density_chiSquare`): for a product law and densities `φ_j` with
  `E φ_j = 1`, `‖⊗_j φ_j - 1‖² = ∏_j (1 + ‖φ_j - 1‖²) - 1`.

Proof method: the Gram kernel `G = Tᵀ diag(κ_B) T` (`gram`) of a product is the Kronecker
product of the coordinate Gram kernels; each coordinate kernel commutes with the averaging
matrix (`gram_mul_mean`), and the mean-zero bound is the Loewner inequality
`Q¹ G Q¹ ⪯ δ²/|A| · Q¹`; Loewner monotonicity of Kronecker products
(`Sarkozy.IndexSupport.piKron_sub_posSemidef`) tensorizes it.

The spectator factor `T_0` of the paper's statement is not separated here: a spectator that
is itself such a conditional operator (as the prefix factor of
`lem:record:prefix-conductor`, by its uniform one-slot marginals) is one more coordinate with
`δ = 1`.
-/

@[expose] public section

open Finset
open scoped BigOperators Matrix

namespace Sarkozy.Mixing

open Sarkozy.IndexSupport

section Gram

variable {A B : Type*} [Fintype A] [Fintype B]

/-- The Gram kernel `G(a,a') = ∑_b κ_B(b) T(b,a) T(b,a')` of the conditional operator in
`L²(κ_B)`. -/
noncomputable def gram (κ : FiniteLaw (A × B)) : Matrix A A ℝ :=
  fun a a' => ∑ b, tgtWeight κ b * condMatrix κ b a * condMatrix κ b a'

theorem energy_eq_gram (κ : FiniteLaw (A × B)) (f : A → ℝ) :
    ∑ b, tgtWeight κ b * condOp κ f b ^ 2 = f ⬝ᵥ (gram κ *ᵥ f) := by
  simp only [condOp, Matrix.mulVec, dotProduct, gram, sq, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro a _
  rw [Finset.sum_comm]
  apply sum_congr rfl
  intro a' _
  apply sum_congr rfl
  intro b _
  ring

theorem gram_transpose (κ : FiniteLaw (A × B)) : (gram κ)ᵀ = gram κ := by
  ext a a'
  simp only [Matrix.transpose_apply, gram]
  apply sum_congr rfl
  intro b _
  ring

theorem gram_posSemidef (κ : FiniteLaw (A × B)) : (gram κ).PosSemidef := by
  apply posSemidef_of_quadratic (gram_transpose κ)
  intro f
  rw [← energy_eq_gram]
  exact Finset.sum_nonneg (fun b _ => mul_nonneg (tgtWeight_nonneg _ _) (sq_nonneg _))

/-- With a uniform source marginal, `G Q⁰ = |A|⁻¹ Q⁰`, `Q⁰` the averaging matrix. -/
theorem gram_mul_mean {κ : FiniteLaw (A × B)}
    (hsrc : ∀ a, srcWeight κ a = (Fintype.card A : ℝ)⁻¹) :
    gram κ * meanMatrix A = (Fintype.card A : ℝ)⁻¹ • meanMatrix A := by
  ext a a''
  simp only [Matrix.mul_apply, gram, meanMatrix_apply, Matrix.smul_apply, smul_eq_mul]
  have h1 : ∑ a', (∑ b, tgtWeight κ b * condMatrix κ b a * condMatrix κ b a') *
      (Fintype.card A : ℝ)⁻¹ = (Fintype.card A : ℝ)⁻¹ * ∑ b, tgtWeight κ b * condMatrix κ b a := by
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm, Finset.mul_sum]
    apply sum_congr rfl
    intro b _
    rw [← Finset.sum_mul, ← Finset.mul_sum, condMatrix_row_sum, mul_one]
    ring
  rw [h1, tgt_condMatrix, hsrc]

theorem mean_mul_gram {κ : FiniteLaw (A × B)}
    (hsrc : ∀ a, srcWeight κ a = (Fintype.card A : ℝ)⁻¹) :
    meanMatrix A * gram κ = (Fintype.card A : ℝ)⁻¹ • meanMatrix A := by
  have h := congrArg Matrix.transpose (gram_mul_mean hsrc)
  rwa [Matrix.transpose_mul, gram_transpose, meanMatrix_transpose, Matrix.transpose_smul,
    meanMatrix_transpose] at h


end Gram

section CoordProj

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- The coordinate sector projections of the uniform law: `Q⁰` (averaging, constants) for
`false`, `Q¹ = 1 - Q⁰` (mean zero) for `true`. -/
noncomputable def coordProj (X : Type*) [Fintype X] [DecidableEq X] (s : Bool) : Matrix X X ℝ :=
  if s then 1 - meanMatrix X else meanMatrix X

theorem coordProj_transpose (s : Bool) : (coordProj X s)ᵀ = coordProj X s := by
  unfold coordProj
  split_ifs
  · rw [Matrix.transpose_sub, Matrix.transpose_one, meanMatrix_transpose]
  · exact meanMatrix_transpose X

theorem coordProj_mul [Nonempty X] (s t : Bool) :
    coordProj X s * coordProj X t = if s = t then coordProj X s else 0 := by
  have hm := meanMatrix_mul_self X
  cases s
  · cases t
    · simp only [coordProj, Bool.false_eq_true, ite_false, ite_true, hm]
    · simp only [coordProj, Bool.false_eq_true, ite_false, ite_true, Matrix.mul_sub,
        Matrix.mul_one, hm, sub_self]
  · cases t
    · simp only [coordProj, Bool.false_eq_true, ite_false, ite_true, Matrix.sub_mul,
        Matrix.one_mul, hm, sub_self, reduceCtorEq]
    · simp only [coordProj, ite_true, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul,
        Matrix.mul_one, hm]
      abel

theorem coordProj_sum : coordProj X false + coordProj X true = 1 := by
  simp only [coordProj, Bool.false_eq_true, ite_false, ite_true]
  abel

theorem gram_comm_coordProj {B : Type*} [Fintype B] {κ : FiniteLaw (X × B)}
    (hsrc : ∀ a, srcWeight κ a = (Fintype.card X : ℝ)⁻¹) (s : Bool) :
    gram κ * coordProj X s = coordProj X s * gram κ := by
  unfold coordProj
  split_ifs
  · rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, gram_mul_mean hsrc,
      mean_mul_gram hsrc]
  · rw [gram_mul_mean hsrc, mean_mul_gram hsrc]

/-- The coordinate Loewner bounds: `Q⁰ G Q⁰ = |X|⁻¹ Q⁰` and, for a `δ`-mixing law,
`Q¹ G Q¹ ⪯ δ²|X|⁻¹ Q¹`. -/
theorem gram_sector_bound [Nonempty X] {B : Type*} [Fintype B] {κ : FiniteLaw (X × B)}
    (hsrc : ∀ a, srcWeight κ a = (Fintype.card X : ℝ)⁻¹) {δ : ℝ}
    (hmix : ContractsMeanZero κ δ) (s : Bool) :
    (((if s then δ ^ 2 else 1) * (Fintype.card X : ℝ)⁻¹) • coordProj X s -
      coordProj X s * gram κ * coordProj X s).PosSemidef := by
  have hP := coordProj_transpose (X := X) s
  have hPP : coordProj X s * coordProj X s = coordProj X s := by
    rw [coordProj_mul, ite_eq_left rfl]
  apply posSemidef_of_quadratic
  · rw [Matrix.transpose_sub, Matrix.transpose_smul, hP, Matrix.transpose_mul,
      Matrix.transpose_mul, hP, gram_transpose, Matrix.mul_assoc]
  · intro h
    set P := coordProj X s with hPdef
    have hfix : P *ᵥ (P *ᵥ h) = P *ᵥ h := by rw [Matrix.mulVec_mulVec, hPP]
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
    have hq : h ⬝ᵥ ((P * gram κ * P) *ᵥ h) = (P *ᵥ h) ⬝ᵥ (gram κ *ᵥ (P *ᵥ h)) := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, dotProduct_mulVec_symm hP]
    have hPh : h ⬝ᵥ (P *ᵥ h) = (P *ᵥ h) ⬝ᵥ (P *ᵥ h) := by
      rw [dotProduct_mulVec_symm hP (P *ᵥ h) h, hfix, dotProduct_comm]
    rw [hq, hPh, ← energy_eq_gram]
    have he : ∑ a, (Fintype.card X : ℝ)⁻¹ * (P *ᵥ h) a ^ 2 =
        (Fintype.card X : ℝ)⁻¹ * ((P *ᵥ h) ⬝ᵥ (P *ᵥ h)) := by
      simp only [dotProduct, ← Finset.mul_sum, sq]
    cases s
    · simp only [Bool.false_eq_true, ite_false, one_mul]
      have hcon := condOp_contraction κ (P *ᵥ h)
      simp only [hsrc] at hcon
      rw [he] at hcon
      linarith
    · simp only [ite_true]
      have hmean : ∑ a, srcWeight κ a * (P *ᵥ h) a = 0 := by
        simp only [hsrc, ← Finset.mul_sum]
        have hs : ∑ a, (P *ᵥ h) a = 0 := by
          rw [hPdef]
          simp only [coordProj, ite_true, Matrix.sub_mulVec, Matrix.one_mulVec, meanMatrix_mulVec,
            Pi.sub_apply, Finset.sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul]
          have hc : (Fintype.card X : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
          field_simp
          ring
        rw [hs, mul_zero]
      have hm := hmix (P *ᵥ h) hmean
      simp only [hsrc] at hm
      rw [he] at hm
      nlinarith

end CoordProj


section Product

variable {K : Type*} [Fintype K] [DecidableEq K] {A B : K → Type*} [∀ j, Fintype (A j)]
  [∀ j, Fintype (B j)]

/-- The product `⊗_j κ_j` of joint laws, a joint law on `(∀ j, A_j) × (∀ j, B_j)`. -/
noncomputable def prodJoint (κ : ∀ j, FiniteLaw (A j × B j)) :
    FiniteLaw ((∀ j, A j) × (∀ j, B j)) where
  weight x := ∏ j, (κ j).weight (x.1 j, x.2 j)
  nonneg x := Finset.prod_nonneg (fun j _ => (κ j).nonneg _)
  total := by
    rw [Fintype.sum_prod_type]
    have h1 (a : ∀ j, A j) : ∑ b : ∀ j, B j, ∏ j, (κ j).weight (a j, b j) =
        ∏ j, ∑ b, (κ j).weight (a j, b) := (Fintype.prod_sum (fun j b => (κ j).weight (a j, b))).symm
    simp only [h1]
    rw [← Fintype.prod_sum (fun j a => ∑ b, (κ j).weight (a, b))]
    apply Finset.prod_eq_one
    intro j _
    have := sum_srcWeight (κ j)
    simpa only [srcWeight] using this

theorem tgtWeight_prodJoint (κ : ∀ j, FiniteLaw (A j × B j)) (b : ∀ j, B j) :
    tgtWeight (prodJoint κ) b = ∏ j, tgtWeight (κ j) (b j) := by
  simp only [tgtWeight, prodJoint]
  exact (Fintype.prod_sum (fun j a => (κ j).weight (a, b j))).symm

theorem srcWeight_prodJoint (κ : ∀ j, FiniteLaw (A j × B j)) (a : ∀ j, A j) :
    srcWeight (prodJoint κ) a = ∏ j, srcWeight (κ j) (a j) := by
  simp only [srcWeight, prodJoint]
  exact (Fintype.prod_sum (fun j b => (κ j).weight (a j, b))).symm

/-- On the support of `κ_B`, the conditional operator of `⊗_j κ_j` is `⊗_j T^{κ_j}`. -/
theorem condMatrix_prodJoint (κ : ∀ j, FiniteLaw (A j × B j)) {b : ∀ j, B j}
    (hb : tgtWeight (prodJoint κ) b ≠ 0) (a : ∀ j, A j) :
    condMatrix (prodJoint κ) b a = ∏ j, condMatrix (κ j) (b j) (a j) := by
  have hbj (j : K) : tgtWeight (κ j) (b j) ≠ 0 := by
    intro h0
    apply hb
    rw [tgtWeight_prodJoint]
    exact Finset.prod_eq_zero (mem_univ j) h0
  unfold condMatrix
  rw [ite_eq_right hb, tgtWeight_prodJoint]
  simp only [hbj, ↓reduceIte]
  rw [Finset.prod_div_distrib]
  rfl

/-- The Gram kernel of a product is the Kronecker product of the Gram kernels. -/
theorem gram_prodJoint (κ : ∀ j, FiniteLaw (A j × B j)) :
    gram (prodJoint κ) = piKron (fun j => gram (κ j)) := by
  ext a a'
  simp only [gram, piKron_apply]
  have hrow (b : ∀ j, B j) : tgtWeight (prodJoint κ) b * condMatrix (prodJoint κ) b a *
      condMatrix (prodJoint κ) b a' =
      ∏ j, (tgtWeight (κ j) (b j) * condMatrix (κ j) (b j) (a j) * condMatrix (κ j) (b j) (a' j)) := by
    by_cases hb : tgtWeight (prodJoint κ) b = 0
    · rw [hb, zero_mul, zero_mul]
      rw [tgtWeight_prodJoint] at hb
      obtain ⟨j, _, hj⟩ := Finset.prod_eq_zero_iff.mp hb
      exact (Finset.prod_eq_zero (mem_univ j) (by rw [hj, zero_mul, zero_mul])).symm
    · rw [condMatrix_prodJoint κ hb, condMatrix_prodJoint κ hb, tgtWeight_prodJoint]
      simp only [← Finset.prod_mul_distrib]
  simp only [hrow]
  exact (Fintype.prod_sum (fun j b => tgtWeight (κ j) b * condMatrix (κ j) b (a j) *
    condMatrix (κ j) b (a' j))).symm

end Product

section Decay

variable {K : Type*} [Fintype K] [DecidableEq K] {A B : K → Type*} [∀ j, Fintype (A j)]
  [∀ j, Fintype (B j)] [∀ j, DecidableEq (A j)] [∀ j, Nonempty (A j)]

/-- The sector weights `δ_S = ∏_{j ∈ S} δ_j`, `S = {j : l_j}`. -/
def supportWeight (δ : K → ℝ) (l : K → Bool) : ℝ :=
  ∏ j, if l j then δ j else 1

/-- The exact-support sector projections of the uniform product space: `H_S` with
`S = {j : l_j}`. -/
noncomputable def sectorProj (A : K → Type*) [∀ j, Fintype (A j)] [∀ j, DecidableEq (A j)]
    (l : K → Bool) : Matrix (∀ j, A j) (∀ j, A j) ℝ :=
  piKron (fun j => coordProj (A j) (l j))

omit [DecidableEq K] [∀ j, Nonempty (A j)] in
theorem sectorProj_transpose (l : K → Bool) : (sectorProj A l)ᵀ = sectorProj A l := by
  rw [sectorProj, piKron_transpose]
  simp only [coordProj_transpose]

theorem sectorProj_mul (l l' : K → Bool) :
    sectorProj A l * sectorProj A l' = if l = l' then sectorProj A l else 0 := by
  rw [sectorProj, sectorProj, piKron_mul]
  by_cases h : l = l'
  · subst h
    rw [ite_eq_left rfl]
    congr 1
    funext j
    rw [coordProj_mul, ite_eq_left rfl]
  · obtain ⟨j, hj⟩ : ∃ j, l j ≠ l' j := by
      by_contra h'
      exact h (funext fun j => not_not.mp (fun hne => h' ⟨j, hne⟩))
    rw [ite_eq_right h]
    exact piKron_eq_zero j (by rw [coordProj_mul, ite_eq_right hj])

omit [∀ j, Nonempty (A j)] in
theorem sum_sectorProj : ∑ l : K → Bool, sectorProj A l = 1 := by
  simp only [sectorProj]
  rw [piKron_sum (fun j (s : Bool) => coordProj (A j) s)]
  have h (j : K) : ∑ s : Bool, coordProj (A j) s = 1 := by
    rw [Fintype.sum_bool, add_comm, coordProj_sum]
  simp only [h]
  exact piKron_one

omit [∀ j, Nonempty (A j)] in
theorem sum_sectorProj_mulVec (g : (∀ j, A j) → ℝ) : ∑ l : K → Bool, sectorProj A l *ᵥ g = g := by
  rw [← Matrix.sum_mulVec, sum_sectorProj, Matrix.one_mulVec]

/-- **`lem:sector`(e), exact-support decay.** For conditional operators of couplings with
uniform source marginals and coordinate bounds `δ_j` on mean-zero functions,
`‖T g‖²_{L²(κ_B)} = ∑_S ‖T g_S‖²_{L²(κ_B)} ≤ ∑_S δ_S² ‖g_S‖²`. -/
theorem exact_support_decay (κ : ∀ j, FiniteLaw (A j × B j))
    (hsrc : ∀ j a, srcWeight (κ j) a = (Fintype.card (A j) : ℝ)⁻¹)
    {δ : K → ℝ} (hmix : ∀ j, ContractsMeanZero (κ j) (δ j)) (g : (∀ j, A j) → ℝ) :
    ∑ b, tgtWeight (prodJoint κ) b * condOp (prodJoint κ) g b ^ 2 =
        ∑ l, ∑ b, tgtWeight (prodJoint κ) b * condOp (prodJoint κ) (sectorProj A l *ᵥ g) b ^ 2 ∧
      ∑ b, tgtWeight (prodJoint κ) b * condOp (prodJoint κ) g b ^ 2 ≤
        ∑ l, supportWeight δ l ^ 2 *
          (FiniteLaw.uniform (∀ j, A j)).expect (fun a => (sectorProj A l *ᵥ g) a ^ 2) := by
  set G := gram (prodJoint κ) with hG
  have hGk : G = piKron (fun j => gram (κ j)) := gram_prodJoint κ
  have hcomm (l : K → Bool) : G * sectorProj A l = sectorProj A l * G := by
    rw [hGk, sectorProj, piKron_mul, piKron_mul]
    congr 1
    funext j
    exact gram_comm_coordProj (hsrc j) (l j)
  have hcross (f : (∀ j, A j) → ℝ) (l l' : K → Bool) (hne : l ≠ l') :
      (sectorProj A l *ᵥ f) ⬝ᵥ (G *ᵥ (sectorProj A l' *ᵥ f)) = 0 := by
    rw [← dotProduct_mulVec_symm (sectorProj_transpose l), Matrix.mulVec_mulVec,
      Matrix.mulVec_mulVec, ← hcomm l, Matrix.mul_assoc, sectorProj_mul, ite_eq_right hne,
      Matrix.mul_zero, Matrix.zero_mulVec, dotProduct_zero]
  have hdecomp (f : (∀ j, A j) → ℝ) :
      f ⬝ᵥ (G *ᵥ f) = ∑ l, (sectorProj A l *ᵥ f) ⬝ᵥ (G *ᵥ (sectorProj A l *ᵥ f)) := by
    conv_lhs => rw [← sum_sectorProj_mulVec f]
    rw [Matrix.mulVec_sum, sum_dotProduct]
    apply sum_congr rfl
    intro l _
    rw [dotProduct_sum, Finset.sum_eq_single l]
    · intro l' _ hl'
      exact hcross f l l' (Ne.symm hl')
    · intro h
      exact absurd (mem_univ l) h
  refine ⟨?_, ?_⟩
  · rw [energy_eq_gram, hdecomp]
    apply sum_congr rfl
    intro l _
    rw [energy_eq_gram]
  · rw [energy_eq_gram, hdecomp]
    apply Finset.sum_le_sum
    intro l _
    have hL : ((supportWeight δ l ^ 2 * (Fintype.card (∀ j, A j) : ℝ)⁻¹) • sectorProj A l -
        sectorProj A l * G * sectorProj A l).PosSemidef := by
      have hfac : (supportWeight δ l ^ 2 * (Fintype.card (∀ j, A j) : ℝ)⁻¹) • sectorProj A l =
          piKron (fun j => ((if l j then δ j ^ 2 else 1) * (Fintype.card (A j) : ℝ)⁻¹) •
            coordProj (A j) (l j)) := by
        rw [piKron_smul, sectorProj]
        congr 1
        rw [Finset.prod_mul_distrib, supportWeight, ← Finset.prod_pow, Fintype.card_pi,
          Nat.cast_prod, Finset.prod_inv_distrib]
        congr 1
        apply prod_congr rfl
        intro j _
        split_ifs <;> ring
      have hPGP : sectorProj A l * G * sectorProj A l =
          piKron (fun j => coordProj (A j) (l j) * gram (κ j) * coordProj (A j) (l j)) := by
        rw [hGk, sectorProj, piKron_mul, piKron_mul]
      rw [hfac, hPGP]
      apply piKron_sub_posSemidef
      · intro j
        have h1 := Matrix.PosSemidef.conjTranspose_mul_mul_same (gram_posSemidef (κ j))
          (coordProj (A j) (l j))
        rwa [Matrix.conjTranspose_eq_transpose_of_trivial, coordProj_transpose] at h1
      · intro j
        exact gram_sector_bound (hsrc j) (hmix j) (l j)
    have hq := quadratic_nonneg_of_posSemidef hL g
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
      at hq
    have hP := sectorProj_transpose (A := A) l
    have hPP : sectorProj A l * sectorProj A l = sectorProj A l := by
      rw [sectorProj_mul, ite_eq_left rfl]
    have h1 : g ⬝ᵥ ((sectorProj A l * G * sectorProj A l) *ᵥ g) =
        (sectorProj A l *ᵥ g) ⬝ᵥ (G *ᵥ (sectorProj A l *ᵥ g)) := by
      rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, dotProduct_mulVec_symm hP]
    have h2 : g ⬝ᵥ (sectorProj A l *ᵥ g) = (sectorProj A l *ᵥ g) ⬝ᵥ (sectorProj A l *ᵥ g) := by
      rw [dotProduct_mulVec_symm hP (sectorProj A l *ᵥ g) g, Matrix.mulVec_mulVec, hPP,
        dotProduct_comm]
    rw [h1, h2] at hq
    have h3 : (FiniteLaw.uniform (∀ j, A j)).expect (fun a => (sectorProj A l *ᵥ g) a ^ 2) =
        (Fintype.card (∀ j, A j) : ℝ)⁻¹ * ((sectorProj A l *ᵥ g) ⬝ᵥ (sectorProj A l *ᵥ g)) := by
      rw [FiniteLaw.expect_uniform, div_eq_inv_mul]
      simp only [dotProduct, sq]
    rw [h3]
    linarith

end Decay

section Markov

variable {K : Type*} [Fintype K] [DecidableEq K] {A B : K → Type*} [∀ j, Fintype (A j)]
  [∀ j, Fintype (B j)] [∀ j, DecidableEq (A j)] [∀ j, Nonempty (A j)]

omit [∀ j, Fintype (A j)] [∀ j, DecidableEq (A j)] [∀ j, Nonempty (A j)] in
/-- Splitting a sum over a product at the coordinate `j₀`. -/
theorem sum_split (j₀ : K) (F : (∀ j, B j) → ℝ) :
    ∑ b, F b = ∑ x : B j₀, ∑ r : (∀ j : {j // j ≠ j₀}, B j),
      F ((Equiv.piSplitAt j₀ B).symm (x, r)) := by
  rw [← Fintype.sum_prod_type']
  exact Fintype.sum_equiv (Equiv.piSplitAt j₀ B) _ _ (fun b => by rw [Equiv.symm_apply_apply])

omit [∀ j, Fintype (A j)] [∀ j, Fintype (B j)] [∀ j, DecidableEq (A j)]
  [∀ j, Nonempty (A j)] in
theorem prod_split (j₀ : K) (w : ∀ j, B j → ℝ) (x : B j₀) (r : ∀ j : {j // j ≠ j₀}, B j) :
    ∏ j, w j ((Equiv.piSplitAt j₀ B).symm (x, r) j) = w j₀ x * ∏ j : {j // j ≠ j₀}, w j (r j) := by
  rw [Fintype.prod_eq_mul_prod_subtype_ne _ j₀]
  congr 1
  · simp
  · apply prod_congr rfl
    intro j _
    simp [j.2]

omit [∀ j, DecidableEq (A j)] [∀ j, Nonempty (A j)] in
/-- The `j₀`-marginal of the target law of a product is the target law of `κ_{j₀}`. -/
theorem tgt_marginal (κ : ∀ j, FiniteLaw (A j × B j)) (j₀ : K) (φ : B j₀ → ℝ) :
    ∑ b, tgtWeight (prodJoint κ) b * φ (b j₀) = ∑ x, tgtWeight (κ j₀) x * φ x := by
  rw [sum_split j₀]
  apply sum_congr rfl
  intro x _
  simp only [tgtWeight_prodJoint, prod_split j₀ (fun j b => tgtWeight (κ j) b)]
  have hφ (r : ∀ j : {j // j ≠ j₀}, B j) : φ ((Equiv.piSplitAt j₀ B).symm (x, r) j₀) = φ x := by
    simp
  simp only [hφ]
  rw [show (∑ r : (∀ j : {j // j ≠ j₀}, B j), tgtWeight (κ j₀) x *
      (∏ j : {j // j ≠ j₀}, tgtWeight (κ j) (r j)) * φ x) =
      tgtWeight (κ j₀) x * φ x * ∑ r : (∀ j : {j // j ≠ j₀}, B j),
        ∏ j : {j // j ≠ j₀}, tgtWeight (κ j) (r j) by
    rw [Finset.mul_sum]
    apply sum_congr rfl
    intro r _
    ring]
  rw [← Fintype.prod_sum (fun (j : {j // j ≠ j₀}) b => tgtWeight (κ j) b)]
  simp only [sum_tgtWeight, prod_const_one, mul_one]

omit [∀ j, DecidableEq (A j)] [∀ j, Nonempty (A j)] in
/-- A function of one coordinate is transported coordinatewise:
`T(f ∘ ev_{j₀})(b) = (T_{j₀} f)(b_{j₀})` on the support of `κ_B`. -/
theorem condOp_prodJoint_single (κ : ∀ j, FiniteLaw (A j × B j)) (j₀ : K) (f : A j₀ → ℝ)
    {b : ∀ j, B j} (hb : tgtWeight (prodJoint κ) b ≠ 0) :
    condOp (prodJoint κ) (fun a => f (a j₀)) b = condOp (κ j₀) f (b j₀) := by
  simp only [condOp, Matrix.mulVec, dotProduct, condMatrix_prodJoint κ hb]
  rw [sum_split j₀]
  apply sum_congr rfl
  intro x _
  simp only [prod_split j₀ (fun j a => condMatrix (κ j) (b j) a)]
  have hf (r : ∀ j : {j // j ≠ j₀}, A j) : f ((Equiv.piSplitAt j₀ A).symm (x, r) j₀) = f x := by
    simp
  simp only [hf]
  rw [show (∑ r : (∀ j : {j // j ≠ j₀}, A j), condMatrix (κ j₀) (b j₀) x *
      (∏ j : {j // j ≠ j₀}, condMatrix (κ j) (b j) (r j)) * f x) =
      condMatrix (κ j₀) (b j₀) x * f x * ∑ r : (∀ j : {j // j ≠ j₀}, A j),
        ∏ j : {j // j ≠ j₀}, condMatrix (κ j) (b j) (r j) by
    rw [Finset.mul_sum]
    apply sum_congr rfl
    intro r _
    ring]
  rw [← Fintype.prod_sum (fun (j : {j // j ≠ j₀}) a => condMatrix (κ j) (b j) a)]
  simp only [condMatrix_row_sum, prod_const_one, mul_one]

omit [∀ j, DecidableEq (A j)] in
theorem uniform_marginal (j₀ : K) (φ : A j₀ → ℝ) :
    (FiniteLaw.uniform (∀ j, A j)).expect (fun a => φ (a j₀)) =
      (FiniteLaw.uniform (A j₀)).expect φ := by
  rw [FiniteLaw.expect_uniform, FiniteLaw.expect_uniform, sum_split j₀]
  have h1 : ∑ x : A j₀, ∑ r : (∀ j : {j // j ≠ j₀}, A j), φ ((Equiv.piSplitAt j₀ A).symm (x, r) j₀) =
      (∑ x, φ x) * (Fintype.card (∀ j : {j // j ≠ j₀}, A j) : ℝ) := by
    rw [Finset.sum_mul]
    apply sum_congr rfl
    intro x _
    simp [mul_comm]
  have hcard : (Fintype.card (∀ j, A j) : ℝ) =
      (Fintype.card (A j₀) : ℝ) * (Fintype.card (∀ j : {j // j ≠ j₀}, A j) : ℝ) := by
    rw [Fintype.card_congr (Equiv.piSplitAt j₀ A), Fintype.card_prod, Nat.cast_mul]
  have hR : (Fintype.card (∀ j : {j // j ≠ j₀}, A j) : ℝ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [h1, hcard]
  field_simp

theorem sum_sectorProj_sq (h : (∀ j, A j) → ℝ) :
    ∑ l : K → Bool, (sectorProj A l *ᵥ h) ⬝ᵥ (sectorProj A l *ᵥ h) = h ⬝ᵥ h := by
  have hcross (l l' : K → Bool) (hne : l ≠ l') :
      (sectorProj A l *ᵥ h) ⬝ᵥ (sectorProj A l' *ᵥ h) = 0 := by
    rw [← dotProduct_mulVec_symm (sectorProj_transpose l), Matrix.mulVec_mulVec, sectorProj_mul,
      ite_eq_right hne, Matrix.zero_mulVec, dotProduct_zero]
  have hexp : h ⬝ᵥ h = ∑ l, ∑ l', (sectorProj A l *ᵥ h) ⬝ᵥ (sectorProj A l' *ᵥ h) := by
    calc h ⬝ᵥ h = (∑ l, sectorProj A l *ᵥ h) ⬝ᵥ (∑ l', sectorProj A l' *ᵥ h) := by
          rw [sum_sectorProj_mulVec]
      _ = _ := by
          rw [sum_dotProduct]
          simp only [dotProduct_sum]
  rw [hexp]
  apply sum_congr rfl
  intro l _
  rw [Finset.sum_eq_single l]
  · intro l' _ hl'
    exact hcross l l' (Ne.symm hl')
  · intro hl
    exact absurd (mem_univ l) hl

omit [∀ j, DecidableEq (A j)] [∀ j, Nonempty (A j)] in
theorem supportWeight_le {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1) {l : K → Bool} (hl : ∃ j, l j = true) :
    supportWeight (fun _ => c) l ≤ c := by
  obtain ⟨j₀, hj₀⟩ := hl
  unfold supportWeight
  rw [Fintype.prod_eq_mul_prod_subtype_ne _ j₀, ite_eq_left hj₀]
  have hle : ∏ j : {j // j ≠ j₀}, (if l j then c else 1) ≤ 1 :=
    Finset.prod_le_one₀ (fun j _ => by split_ifs <;> linarith) (fun j _ => by split_ifs <;> linarith)
  have hnn : 0 ≤ ∏ j : {j // j ≠ j₀}, (if l j then c else 1) :=
    Finset.prod_nonneg (fun j _ => by split_ifs <;> linarith)
  nlinarith

omit [DecidableEq K] [∀ j, Nonempty (A j)] in
theorem supportWeight_nonneg {c : ℝ} (hc0 : 0 ≤ c) (l : K → Bool) :
    0 ≤ supportWeight (fun _ => c) l :=
  Finset.prod_nonneg (fun j _ => by split_ifs <;> linarith)

/-- **`lem:sector`(c), the Markov tensor maximum: `‖T - J‖ = max_j ‖T_j^∘‖`.** For `c ≥ 0`,
`‖(T - J) g‖_{L²(κ_B)} ≤ c ‖g‖` for every `g` (`J g = (E g) 1`) if and only if every
coordinate conditional operator contracts mean-zero functions by `c`. (Each coordinate
operator is a contraction, `condOp_contraction`, which is the paper's `δ_j ≤ 1`.) -/
theorem markov_tensor_max (κ : ∀ j, FiniteLaw (A j × B j))
    (hsrc : ∀ j a, srcWeight (κ j) a = (Fintype.card (A j) : ℝ)⁻¹) {c : ℝ} (hc : 0 ≤ c) :
    (∀ g : (∀ j, A j) → ℝ,
      ∑ b, tgtWeight (prodJoint κ) b *
        (condOp (prodJoint κ) g b - (FiniteLaw.uniform (∀ j, A j)).expect g) ^ 2 ≤
      c ^ 2 * (FiniteLaw.uniform (∀ j, A j)).expect (fun a => g a ^ 2)) ↔
    (∀ j, ContractsMeanZero (κ j) c) := by
  constructor
  · intro hglob j₀ f hf
    have hf' : (FiniteLaw.uniform (A j₀)).expect f = 0 := by
      rw [FiniteLaw.expect_uniform]
      simp only [hsrc, ← Finset.mul_sum] at hf
      have hc' : (Fintype.card (A j₀) : ℝ)⁻¹ ≠ 0 :=
        inv_ne_zero (by exact_mod_cast Fintype.card_ne_zero)
      rcases mul_eq_zero.mp hf with h | h
      · exact absurd h hc'
      · rw [h, zero_div]
    have h := hglob (fun a => f (a j₀))
    rw [uniform_marginal j₀ f, hf', uniform_marginal j₀ (fun x => f x ^ 2)] at h
    have hl : ∑ b, tgtWeight (prodJoint κ) b * (condOp (prodJoint κ) (fun a => f (a j₀)) b - 0) ^ 2 =
        ∑ x, tgtWeight (κ j₀) x * condOp (κ j₀) f x ^ 2 := by
      rw [← tgt_marginal κ j₀ (fun x => condOp (κ j₀) f x ^ 2)]
      apply sum_congr rfl
      intro b _
      by_cases hb : tgtWeight (prodJoint κ) b = 0
      · rw [hb, zero_mul, zero_mul]
      · rw [condOp_prodJoint_single κ j₀ f hb, sub_zero]
    rw [hl] at h
    have hr : (FiniteLaw.uniform (A j₀)).expect (fun x => f x ^ 2) =
        ∑ a, srcWeight (κ j₀) a * f a ^ 2 := by
      rw [FiniteLaw.expect_uniform, div_eq_inv_mul, Finset.mul_sum]
      simp only [hsrc]
    rw [hr] at h
    exact h
  · intro hloc g
    set c' := min c 1 with hc'
    have hc'0 : 0 ≤ c' := le_min hc zero_le_one
    have hc'1 : c' ≤ 1 := min_le_right _ _
    have hmix (j : K) : ContractsMeanZero (κ j) c' := by
      intro f hf
      rcases le_total c 1 with h1 | h1
      · rw [hc', min_eq_left h1]
        exact hloc j f hf
      · rw [hc', min_eq_right h1, one_pow, one_mul]
        exact condOp_contraction (κ j) f
    set m := (FiniteLaw.uniform (∀ j, A j)).expect g with hm
    set h := fun a => g a - m with hh
    have hT (b : ∀ j, B j) : condOp (prodJoint κ) g b - m = condOp (prodJoint κ) h b := by
      simp only [hh, condOp, Matrix.mulVec, dotProduct, mul_sub, Finset.sum_sub_distrib,
        ← Finset.sum_mul, condMatrix_row_sum, one_mul]
    simp only [hT]
    have hdec := (exact_support_decay κ hsrc (δ := fun _ => c') hmix h).2
    apply hdec.trans
    -- the zero sector vanishes, the others have weight at most `c`
    have hzero : sectorProj A (fun _ => false) *ᵥ h = 0 := by
      have hP : sectorProj A (fun _ => false) = meanMatrix (∀ j, A j) := by
        rw [sectorProj]
        simp only [coordProj, Bool.false_eq_true, ite_false]
        exact piKron_meanMatrix
      rw [hP, meanMatrix_mulVec]
      funext a
      have hmean : ∑ η, h η = 0 := by
        simp only [hh, Finset.sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul, hm,
          FiniteLaw.expect_uniform]
        have hcard : (Fintype.card (∀ j, A j) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
        field_simp
        ring
      simp only [hmean, mul_zero, Pi.zero_apply]
    have hterm (l : K → Bool) : supportWeight (fun _ => c') l ^ 2 *
        (FiniteLaw.uniform (∀ j, A j)).expect (fun a => (sectorProj A l *ᵥ h) a ^ 2) ≤
        c ^ 2 * (FiniteLaw.uniform (∀ j, A j)).expect (fun a => (sectorProj A l *ᵥ h) a ^ 2) := by
      have he0 := (FiniteLaw.uniform (∀ j, A j)).expect_nonneg
        (fun a => sq_nonneg ((sectorProj A l *ᵥ h) a))
      by_cases hl : ∃ j, l j = true
      · have h1 := supportWeight_le hc'0 hc'1 hl (K := K)
        have h2 := supportWeight_nonneg hc'0 l (K := K)
        have h3 : supportWeight (fun _ => c') l ^ 2 ≤ c ^ 2 := by
          have : c' ≤ c := min_le_left _ _
          nlinarith
        exact mul_le_mul_of_nonneg_right h3 he0
      · have hl0 : l = fun _ => false := by
          funext j
          cases hj : l j
          · rfl
          · exact absurd ⟨j, hj⟩ hl
        subst hl0
        rw [hzero]
        simp
    apply (Finset.sum_le_sum (fun l _ => hterm l)).trans
    rw [← Finset.mul_sum]
    apply mul_le_mul_of_nonneg_left _ (sq_nonneg c)
    have hpars : ∑ l : K → Bool, (FiniteLaw.uniform (∀ j, A j)).expect
        (fun a => (sectorProj A l *ᵥ h) a ^ 2) =
        (FiniteLaw.uniform (∀ j, A j)).expect (fun a => h a ^ 2) := by
      simp only [FiniteLaw.expect_uniform, ← Finset.sum_div]
      congr 1
      have := sum_sectorProj_sq h
      simp only [dotProduct, ← sq] at this
      exact this
    rw [hpars]
    have hvar := (FiniteLaw.uniform (∀ j, A j)).expect_sq_sub_mean g
    simp only [hh, hm]
    rw [hvar]
    nlinarith [sq_nonneg ((FiniteLaw.uniform (∀ j, A j)).expect g)]

end Markov

section Densities

variable {K : Type*} [Fintype K] [DecidableEq K] {Ω : K → Type*} [∀ j, Fintype (Ω j)]

/-- **`lem:sector`(f), product densities.** For a product law and densities `φ_j` with
`E φ_j = 1`: `‖⊗_j φ_j - 1‖² = ∏_j (1 + ‖φ_j - 1‖²) - 1`. -/
theorem product_density_chiSquare (π : ∀ j, FiniteLaw (Ω j)) (φ : ∀ j, Ω j → ℝ)
    (hφ : ∀ j, (π j).expect (φ j) = 1) :
    (FiniteLaw.pi π).expect (fun x => (∏ j, φ j (x j) - 1) ^ 2) =
      ∏ j, (1 + (π j).expect (fun y => (φ j y - 1) ^ 2)) - 1 := by
  have hsq (j : K) : 1 + (π j).expect (fun y => (φ j y - 1) ^ 2) = (π j).expect (fun y => φ j y ^ 2) := by
    have h := (π j).expect_sq_sub_mean (φ j)
    rw [hφ j] at h
    rw [h]
    ring
  have hexp : (fun x : ∀ j, Ω j => (∏ j, φ j (x j) - 1) ^ 2) =
      fun x => (∏ j, φ j (x j) ^ 2 - 2 * ∏ j, φ j (x j)) + 1 := by
    funext x
    rw [Finset.prod_pow]
    ring
  rw [hexp, FiniteLaw.expect_add, FiniteLaw.expect_sub, FiniteLaw.expect_const_mul,
    FiniteLaw.expect_const, FiniteLaw.expect_pi_product π (fun j y => φ j y ^ 2),
    FiniteLaw.expect_pi_product π φ]
  simp only [hφ, prod_const_one, hsq]
  ring

end Densities

end Sarkozy.Mixing
