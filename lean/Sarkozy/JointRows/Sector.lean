module

public import Sarkozy.JointRows.RowsAGate
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The reduction of `𝕄` to the `Φ̂`-sectors (`hsector` of `lem:joint-rows`(a))

Source: `paper/sections/16_extraction.tex`, proof of `lem:joint-rows`(a) ("Pure stars"):
"On `ℋ_±` it acts as `(±i𝒵 𝒜; 𝒜* 0) ⊗ I`", with `𝕄 = (𝒵⊗Φ̂  𝒜⊗I; 𝒜*⊗I  0)`; and
`lem:spec:gauss` (`Φ̂* = -Φ̂`, `Φ̂² = -I` on `ℋ`).

`RowsA.joint_rows_a_gate` took this step as the hypothesis `hsector`. Here it is proved, for any
finite-dimensional real inner product space `ℋ` and any `J = Φ̂` with `J* = -J`, `J² = -I`
(`CxStruct`). The operator `𝕄` acts on `y = (u, w) ∈ ℋ^m ⊕ ℋ^s` (`PiLp 2`), and its quadratic
form is `qMat Z A J y = ∑ Z_{ab}⟨u_a, J u_b⟩ + 2∑ A_{ac}⟨u_a, w_c⟩`.

* `qMat_lower` (**the sector reduction**): if the complex block `(kI - i𝒵 𝒜; 𝒜* kI)` is positive
  semidefinite, then `⟨y, 𝕄 y⟩ ≥ -k‖y‖²` for every real `y`.
* `hsector_holds`: the hypothesis `hsector` of `joint_rows_a_gate`, for `F = ℋ^{m ⊕ s}` and
  `qM = qMat Z A J`.
* `joint_rows_a_sector`: `lem:joint-rows`(a) from the gate `eq:joint-gate`, without `hsector`.

**Proof (no complexification).** For an orthonormal basis `(e_j)` of `ℋ`, put
`α_j(p) = ⟨y_p, e_j⟩`, `β_j(p) = ⟨J y_p, e_j⟩` and `c_j = α_j + iβ_j`. The real part of
`c_j^* N c_j` is `∑_{pq} Re N_{pq}(α_pα_q + β_pβ_q) - Im N_{pq}(α_pβ_q - β_pα_q)`
(`re_quad`). Summing over `j` (Parseval), and using `⟨Jh, Jh'⟩ = ⟨h, h'⟩` and
`⟨Jh, h'⟩ = -⟨h, Jh'⟩`, gives `2(k‖y‖² + ⟨y, 𝕄 y⟩)`, a sum of nonnegative terms. This is the
statement that `𝕄` acts on the sectors as `M(∓i) ⊗ I`: the family `(y_p, J y_p)` realizes the
Gram matrix of `y` over the complex structure `J`.
-/

@[expose] public section

open scoped BigOperators ComplexOrder
open Matrix

namespace Sarkozy.JointRows

open Sarkozy.FiveType Sarkozy.FiveType.Blocks

namespace Sector

/-! ## A complex structure on `ℋ` -/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- **`J* = -J` and `J² = -I`**: the properties of the normalized Paley operator `Φ̂` on `ℋ`
(`lem:spec:gauss`). -/
structure CxStruct (J : H → H) : Prop where
  anti : ∀ h h' : H, inner ℝ (J h) h' = -inner ℝ h (J h')
  sq : ∀ h : H, J (J h) = -h

theorem CxStruct.inner_J_J {J : H → H} (hJ : CxStruct J) (h h' : H) :
    inner ℝ (J h) (J h') = inner ℝ h h' := by
  rw [hJ.anti, hJ.sq, inner_neg_right, neg_neg]

/-! ## The real part of a complex quadratic form -/

section Quad

variable {n : Type*} [Fintype n]

/-- The complex vector `α + iβ`. -/
noncomputable def cvec (α β : n → ℝ) : n → ℂ := fun p => (α p : ℂ) + (β p : ℂ) * Complex.I

theorem re_quad (N : Matrix n n ℂ) (α β : n → ℝ) :
    (star (cvec α β) ⬝ᵥ (N *ᵥ cvec α β)).re =
      ∑ p, ∑ q, ((N p q).re * (α p * α q + β p * β q) -
        (N p q).im * (α p * β q - β p * α q)) := by
  simp only [dotProduct, mulVec, Finset.mul_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
  simp only [cvec, Pi.star_apply, Complex.star_def, Complex.mul_re, Complex.mul_im,
    Complex.add_re, Complex.add_im, Complex.conj_re, Complex.conj_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

theorem re_quad_nonneg {N : Matrix n n ℂ} (hN : N.PosSemidef) (α β : n → ℝ) :
    0 ≤ ∑ p, ∑ q, ((N p q).re * (α p * α q + β p * β q) -
      (N p q).im * (α p * β q - β p * α q)) := by
  rw [← re_quad]
  exact (Complex.nonneg_iff.mp (hN.dotProduct_mulVec_nonneg _)).1

end Quad

/-! ## The Gram sum over an orthonormal basis -/

section Gram

variable [FiniteDimensional ℝ H] {n : Type*} [Fintype n]

/-- **Summing the quadratic forms of the `c_j` over an orthonormal basis.** -/
theorem gram_sum {J : H → H} (hJ : CxStruct J) (N : Matrix n n ℂ) (y : n → H) :
    ∑ j, ∑ p, ∑ q, ((N p q).re *
        (inner ℝ (y p) (stdOrthonormalBasis ℝ H j) * inner ℝ (y q) (stdOrthonormalBasis ℝ H j) +
          inner ℝ (J (y p)) (stdOrthonormalBasis ℝ H j) *
            inner ℝ (J (y q)) (stdOrthonormalBasis ℝ H j)) -
      (N p q).im *
        (inner ℝ (y p) (stdOrthonormalBasis ℝ H j) *
            inner ℝ (J (y q)) (stdOrthonormalBasis ℝ H j) -
          inner ℝ (J (y p)) (stdOrthonormalBasis ℝ H j) *
            inner ℝ (y q) (stdOrthonormalBasis ℝ H j))) =
      ∑ p, ∑ q, (2 * (N p q).re * inner ℝ (y p) (y q) -
        2 * (N p q).im * inner ℝ (y p) (J (y q))) := by
  set b := stdOrthonormalBasis ℝ H
  have hpars : ∀ u v : H, ∑ j, inner ℝ u (b j) * inner ℝ v (b j) = inner ℝ u v := by
    intro u v
    rw [← b.sum_inner_mul_inner u v]
    exact Finset.sum_congr rfl fun j _ => by rw [real_inner_comm v (b j)]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_add_distrib,
    Finset.sum_sub_distrib, hpars, hpars, hpars, hpars, hJ.inner_J_J, hJ.anti]
  ring

end Gram

/-! ## The sector reduction -/

variable [FiniteDimensional ℝ H] {m s : Type*} [Fintype m] [DecidableEq m] [Fintype s]
  [DecidableEq s]

/-- **The quadratic form of `𝕄 = (𝒵⊗Φ̂  𝒜⊗I; 𝒜*⊗I  0)`** at `y = (u, w)`:
`∑ Z_{ab}⟨u_a, J u_b⟩ + 2∑ A_{ac}⟨u_a, w_c⟩`. -/
noncomputable def qMat (Zr : Matrix m m ℝ) (Ar : Matrix m s ℝ) (J : H → H)
    (y : PiLp 2 (fun _ : m ⊕ s => H)) : ℝ :=
  ∑ a, ∑ b, Zr a b * inner ℝ (y.ofLp (Sum.inl a)) (J (y.ofLp (Sum.inl b))) +
    2 * ∑ a, ∑ c, Ar a c * inner ℝ (y.ofLp (Sum.inl a)) (y.ofLp (Sum.inr c))

omit [FiniteDimensional ℝ H] [DecidableEq m] [DecidableEq s] in
theorem norm_sq_split (y : PiLp 2 (fun _ : m ⊕ s => H)) :
    ‖y‖ ^ 2 = ∑ a, inner ℝ (y.ofLp (Sum.inl a)) (y.ofLp (Sum.inl a)) +
      ∑ c, inner ℝ (y.ofLp (Sum.inr c)) (y.ofLp (Sum.inr c)) := by
  rw [PiLp.norm_sq_eq_of_L2, Fintype.sum_sum_type]
  simp only [real_inner_self_eq_norm_sq]

/-- **The sector reduction**: if `(kI - i𝒵 𝒜; 𝒜* kI) ⪰ 0`, then `⟨y, 𝕄 y⟩ ≥ -k‖y‖²` for every
real `y ∈ ℋ^m ⊕ ℋ^s`. -/
theorem qMat_lower {J : H → H} (hJ : CxStruct J) (Zr : Matrix m m ℝ) (Ar : Matrix m s ℝ) {k : ℝ}
    (hN : (fromBlocks ((k : ℂ) • (1 : Matrix m m ℂ) + Complex.I • (-RowsA.cplx Zr))
      (RowsA.cplx Ar) (RowsA.cplx Ar)ᴴ ((k : ℂ) • (1 : Matrix s s ℂ))).PosSemidef)
    (y : PiLp 2 (fun _ : m ⊕ s => H)) : -k * ‖y‖ ^ 2 ≤ qMat Zr Ar J y := by
  set N := fromBlocks ((k : ℂ) • (1 : Matrix m m ℂ) + Complex.I • (-RowsA.cplx Zr))
    (RowsA.cplx Ar) (RowsA.cplx Ar)ᴴ ((k : ℂ) • (1 : Matrix s s ℂ)) with hNdef
  set b := stdOrthonormalBasis ℝ H
  have hj := fun j => re_quad_nonneg hN (fun p => inner ℝ (y.ofLp p) (b j))
    (fun p => inner ℝ (J (y.ofLp p)) (b j))
  have hsum := Finset.sum_nonneg fun j (_ : j ∈ Finset.univ) => hj j
  rw [gram_sum hJ N (fun p => y.ofLp p)] at hsum
  -- the entries of `N`
  have e11 : ∀ a a', (N (Sum.inl a) (Sum.inl a')).re = k * (if a = a' then 1 else 0) ∧
      (N (Sum.inl a) (Sum.inl a')).im = -Zr a a' := by
    intro a a'
    simp only [hNdef, fromBlocks_apply₁₁, Matrix.add_apply, Matrix.smul_apply, Matrix.one_apply,
      Matrix.neg_apply, RowsA.cplx, Matrix.map_apply, smul_eq_mul]
    by_cases h : a = a' <;> simp [h]
  have e12 : ∀ a c, (N (Sum.inl a) (Sum.inr c)).re = Ar a c ∧
      (N (Sum.inl a) (Sum.inr c)).im = 0 := by
    intro a c
    simp [hNdef, fromBlocks_apply₁₂, RowsA.cplx]
  have e21 : ∀ c a, (N (Sum.inr c) (Sum.inl a)).re = Ar a c ∧
      (N (Sum.inr c) (Sum.inl a)).im = 0 := by
    intro c a
    simp [hNdef, fromBlocks_apply₂₁, RowsA.cplx, Matrix.conjTranspose_apply]
  have e22 : ∀ c c', (N (Sum.inr c) (Sum.inr c')).re = k * (if c = c' then 1 else 0) ∧
      (N (Sum.inr c) (Sum.inr c')).im = 0 := by
    intro c c'
    by_cases h : c = c' <;> simp [hNdef, fromBlocks_apply₂₂, h]
  rw [Fintype.sum_sum_type] at hsum
  simp only [Fintype.sum_sum_type] at hsum
  simp only [(e11 _ _).1, (e11 _ _).2, (e12 _ _).1, (e12 _ _).2, (e21 _ _).1, (e21 _ _).2,
    (e22 _ _).1, (e22 _ _).2] at hsum
  have hd1 : ∀ a, ∑ a', (2 * (k * (if a = a' then 1 else 0)) *
      inner ℝ (y.ofLp (Sum.inl a)) (y.ofLp (Sum.inl a')) -
        2 * -Zr a a' * inner ℝ (y.ofLp (Sum.inl a)) (J (y.ofLp (Sum.inl a')))) =
      2 * k * inner ℝ (y.ofLp (Sum.inl a)) (y.ofLp (Sum.inl a)) +
        2 * ∑ a', Zr a a' * inner ℝ (y.ofLp (Sum.inl a)) (J (y.ofLp (Sum.inl a'))) := by
    intro a
    rw [Finset.sum_sub_distrib, Finset.mul_sum]
    rw [Finset.sum_eq_single a (fun a' _ h => by simp only [Ne.symm h, ↓reduceIte, mul_zero,
      zero_mul]) (fun h => absurd (Finset.mem_univ a) h)]
    simp only [↓reduceIte, mul_one]
    rw [sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    refine Finset.sum_congr rfl fun a' _ => ?_
    ring
  have hd2 : ∀ c, ∑ c', (2 * (k * (if c = c' then 1 else 0)) *
      inner ℝ (y.ofLp (Sum.inr c)) (y.ofLp (Sum.inr c')) -
        2 * 0 * inner ℝ (y.ofLp (Sum.inr c)) (J (y.ofLp (Sum.inr c')))) =
      2 * k * inner ℝ (y.ofLp (Sum.inr c)) (y.ofLp (Sum.inr c)) := by
    intro c
    rw [Finset.sum_eq_single c (fun c' _ h => by simp only [Ne.symm h, ↓reduceIte, mul_zero,
      zero_mul, sub_zero]) (fun h => absurd (Finset.mem_univ c) h)]
    simp only [↓reduceIte, mul_one, mul_zero, zero_mul, sub_zero]
  simp only [hd1, hd2] at hsum
  have hsym : ∀ c a, inner ℝ (y.ofLp (Sum.inr c)) (y.ofLp (Sum.inl a)) =
      inner ℝ (y.ofLp (Sum.inl a)) (y.ofLp (Sum.inr c)) := fun c a => real_inner_comm _ _
  simp only [hsym, mul_zero, zero_mul, sub_zero] at hsum
  simp only [Finset.sum_add_distrib, mul_assoc, ← Finset.mul_sum] at hsum
  have hcomm : ∑ c, ∑ a, Ar a c * inner ℝ (y.ofLp (Sum.inl a)) (y.ofLp (Sum.inr c)) =
      ∑ a, ∑ c, Ar a c * inner ℝ (y.ofLp (Sum.inl a)) (y.ofLp (Sum.inr c)) :=
    Finset.sum_comm
  rw [hcomm] at hsum
  rw [norm_sq_split, qMat]
  linarith [hsum]

/-- **`hsector` of `RowsA.joint_rows_a_gate` holds** for `F = ℋ^{m ⊕ s}` and `qM = qMat 𝒵 𝒜 Φ̂`.
Only the second (`-i`) sector is used. -/
theorem hsector_holds {J : H → H} (hJ : CxStruct J) (Zr : Matrix m m ℝ) (Ar : Matrix m s ℝ)
    {k : ℝ} :
    (fromBlocks ((k : ℂ) • (1 : Matrix m m ℂ) + Complex.I • RowsA.cplx Zr) (RowsA.cplx Ar)
        (RowsA.cplx Ar)ᴴ ((k : ℂ) • (1 : Matrix s s ℂ))).PosSemidef →
      (fromBlocks ((k : ℂ) • (1 : Matrix m m ℂ) + Complex.I • (-RowsA.cplx Zr)) (RowsA.cplx Ar)
        (RowsA.cplx Ar)ᴴ ((k : ℂ) • (1 : Matrix s s ℂ))).PosSemidef →
      ∀ y : PiLp 2 (fun _ : m ⊕ s => H), -k * ‖y‖ ^ 2 ≤ qMat Zr Ar J y :=
  fun _ h2 y => qMat_lower hJ Zr Ar h2 y

end Sector

end Sarkozy.JointRows
