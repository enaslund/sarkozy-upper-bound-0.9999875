module

public import Sarkozy.TraceMixing.DisjointTripleOrdered
public import Sarkozy.IndexSupport.Kronecker

@[expose] public section

/-!
# The disjoint-triple operator on a block of primes (`it:triple:block`)

`paper/sections/12_labellings.tex`, lemma `sec:frontier:empty-triple-negative` (the label is a
section-style key on a lemma; its items are `it:triple:spec`, `it:triple:bound`,
`it:triple:block`).

WP-S proved the one-prime assertions on functions on `Fin 3 → F` restricted to injective triples
(`Sarkozy.TraceMixing.tripleOp_le`, `tripleOp_ge`, `tripleOp_abs_le`, …): `T ⪯ I`,
`T ⪰ -3/(n-3) I` and `‖T - J‖ ≤ 3/(n-3)` for `n = |F| ≥ 7`. This file

* writes `T` as a matrix on the subtype `𝒯 = {x : Fin 3 → F // x injective}` (`tripleMatrix`)
  and transfers those three bounds to `Matrix.PosSemidef` statements (`tripleMatrix_le_one`,
  `tripleMatrix_ge`, `tripleMatrix_centred`; the centred one through the general
  `centred_of_meanZero`);
* proves the tensor step for any finite family of matrices (`piKron_two_sided`,
  `piKron_centred`): if every factor has `-c I ⪯ T_j ⪯ I` (resp.
  `-c (I - J_j) ⪯ T_j - J_j ⪯ c (I - J_j)`) with one `0 ≤ c ≤ 1`, so does `⊗_j T_j`. The proof is
  by induction over the coordinates with the Schur product theorem and two polynomial identities
  (for `λ, μ ∈ [-c, 1]`: `λμ + c = ((λ+c)(μ+c) + c(1-λ)(1-μ))/(1+c)` and
  `1 - λμ = ((1-λ)(1+μ) + (1+λ)(1-μ))/2`), in place of the paper's eigenvector argument;
* concludes **`it:triple:block`** (`triple_block`): for a finite family of finite sets `F_j`
  (the fields `𝔽_p`, `p ∈ 𝔅`) with `|F_j| ≥ b ≥ 7`, the tensor product
  `T_𝔅 = ⊗_j T` satisfies `-3/(b-3) I ⪯ T_𝔅 ⪯ I` and `-3/(b-3) I ⪯ T_𝔅 - J ⪯ 3/(b-3) I`, the
  last being `‖T_𝔅 - J‖ ≤ 3/(b-3)` for the symmetric matrix `T_𝔅 - J`; `triple_block_norm`
  states the norm bound itself, `‖(T_𝔅 - J) f‖₂ ≤ 3/(b-3) ‖f‖₂`, through
  `mulVec_sq_le_of_two_sided` (polarization, no spectral theorem); `triple_block_zmod` is
  the same for `F_p = ZMod p` over a finite set of primes with least element `≥ b`.

The Loewner order is with respect to the counting inner product on `∏_j 𝒯_j`; the uniform law
differs by a positive constant factor, so the order is the paper's (`def:prelim:operators`).
`J` is `meanMatrix`, the averaging operator of the uniform law (the projection on constants).

With WP-S's files this completes the lemma except the spectral-exhaustion clause of (a) (that
the four listed eigenvalues are all of `T̄`'s spectrum) and the equality `‖T - J‖ = 3/(p-3)` of
(b) as an operator-norm equality (WP-S proves `≤` and that `-3/(p-3)` is attained,
`disjOp_attained`).
-/

namespace Sarkozy.Misc

open Finset Matrix Sarkozy.TraceMixing Sarkozy.IndexSupport
open scoped BigOperators Matrix

/-! ## Symmetric stochastic matrices: centring -/

section Centring

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] [DecidableEq ι] in
/-- A real matrix equal to its transpose is Hermitian. -/
theorem isHermitian_of_transpose {A : Matrix ι ι ℝ} (hA : Aᵀ = A) : A.IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_eq_transpose_of_trivial]
  exact hA

/-- **Centring a symmetric stochastic matrix.** If `M` is symmetric with row sums one and
`|⟨g, M g⟩| ≤ c ⟨g, g⟩` for every `g` of sum zero, then
`-c (I - J) ⪯ M - J ⪯ c (I - J)`, with `J` the averaging matrix. -/
theorem centred_of_meanZero [Nonempty ι] (M : Matrix ι ι ℝ) (hsymm : Mᵀ = M)
    (hrow : ∀ i, ∑ j, M i j = 1) (c : ℝ)
    (hmz : ∀ g : ι → ℝ, ∑ i, g i = 0 → |g ⬝ᵥ (M *ᵥ g)| ≤ c * (g ⬝ᵥ g)) :
    ((M - meanMatrix ι) + c • (1 - meanMatrix ι)).PosSemidef ∧
      (c • (1 - meanMatrix ι) - (M - meanMatrix ι)).PosSemidef := by
  have hN : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  have hcol : ∀ j, ∑ i, M i j = 1 := fun j => by
    rw [← hrow j]
    refine sum_congr rfl fun i _ => ?_
    have h := congrFun (congrFun hsymm j) i
    rw [transpose_apply] at h
    exact h
  have hJt : (meanMatrix ι)ᵀ = meanMatrix ι := meanMatrix_transpose ι
  have hherm (A : Matrix ι ι ℝ) (hA : Aᵀ = A) : A.IsHermitian := isHermitian_of_transpose hA
  -- the quadratic forms of `M - J` and `I - J` are those of the centred vector
  have key (g : ι → ℝ) :
      g ⬝ᵥ ((M - meanMatrix ι) *ᵥ g) =
          (fun i => g i - (∑ k, g k) / Fintype.card ι) ⬝ᵥ
            (M *ᵥ fun i => g i - (∑ k, g k) / Fintype.card ι) ∧
        g ⬝ᵥ ((1 - meanMatrix ι) *ᵥ g) =
          (fun i => g i - (∑ k, g k) / Fintype.card ι) ⬝ᵥ
            (fun i => g i - (∑ k, g k) / Fintype.card ι) := by
    set N : ℝ := (Fintype.card ι : ℝ)
    set S : ℝ := ∑ k, g k
    have hMv : ∀ i, (M *ᵥ fun i => g i - S / N) i = (M *ᵥ g) i - S / N := fun i => by
      simp only [mulVec, dotProduct, mul_sub, sum_sub_distrib, ← sum_mul, hrow i, one_mul]
    have hSum : ∑ i, (M *ᵥ g) i = S := by
      simp only [mulVec, dotProduct]
      rw [sum_comm]
      refine sum_congr rfl fun j _ => ?_
      rw [← sum_mul, hcol j, one_mul]
    have hJv : ∀ i, (meanMatrix ι *ᵥ g) i = S / N := fun i => by
      rw [meanMatrix_mulVec]
      simp only [S, N]
      ring
    constructor
    · rw [sub_mulVec]
      simp only [dotProduct, Pi.sub_apply, hMv, hJv]
      simp only [mul_sub, sub_mul, sum_sub_distrib, ← sum_mul, ← mul_sum, hSum, sum_const,
        card_univ, nsmul_eq_mul]
      have hN0 : N ≠ 0 := hN.ne'
      field_simp
      ring
    · rw [sub_mulVec, one_mulVec]
      simp only [dotProduct, Pi.sub_apply, hJv]
      simp only [mul_sub, sub_mul, sum_sub_distrib, ← sum_mul, ← mul_sum, sum_const,
        card_univ, nsmul_eq_mul]
      have hN0 : N ≠ 0 := hN.ne'
      field_simp
      ring
  have hcent (g : ι → ℝ) : ∑ i, (g i - (∑ k, g k) / Fintype.card ι) = 0 := by
    rw [sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul]
    field_simp
    ring
  constructor
  · rw [posSemidef_iff_dotProduct_mulVec]
    refine ⟨hherm _ ?_, fun g => ?_⟩
    · rw [transpose_add, transpose_sub, transpose_smul, transpose_sub, transpose_one, hsymm, hJt]
    · simp only [star_trivial]
      rw [add_mulVec, dotProduct_add, smul_mulVec, dotProduct_smul, smul_eq_mul,
        (key g).1, (key g).2]
      have h := hmz _ (hcent g)
      rw [abs_le] at h
      linarith [h.1]
  · rw [posSemidef_iff_dotProduct_mulVec]
    refine ⟨hherm _ ?_, fun g => ?_⟩
    · rw [transpose_sub, transpose_smul, transpose_sub, transpose_one, transpose_sub, hsymm, hJt]
    · simp only [star_trivial]
      rw [sub_mulVec, dotProduct_sub, smul_mulVec, dotProduct_smul, smul_eq_mul,
        (key g).1, (key g).2]
      have h := hmz _ (hcent g)
      rw [abs_le] at h
      linarith [h.2]

end Centring

/-! ## One prime: `T` as a matrix on `𝒯` -/

section OnePrime

variable (F : Type*) [Fintype F] [DecidableEq F]

/-- `𝒯`: the ordered triples of distinct elements of `F`. -/
abbrev Trip := {x : Fin 3 → F // Function.Injective x}

/-- The normalization `(n-3)(n-4)(n-5)` of `T`. -/
noncomputable def tripleDen : ℝ := ((Fintype.card F - 3).descFactorial 3 : ℝ)

/-- **The disjoint-triple operator as a matrix on `𝒯`**: entry `((n-3)(n-4)(n-5))⁻¹` when the
triples are disjoint, `0` otherwise (`sec:frontier:empty-triple-negative`, `T`). -/
noncomputable def tripleMatrix : Matrix (Trip F) (Trip F) ℝ :=
  fun x y => if ∀ i j, x.1 i ≠ y.1 j then (tripleDen F)⁻¹ else 0

variable {F}

/-- Extension by zero from `𝒯` to `Fin 3 → F`. -/
noncomputable def extTrip (g : Trip F → ℝ) : (Fin 3 → F) → ℝ :=
  fun x => if h : Function.Injective x then g ⟨x, h⟩ else 0

theorem sum_ite_injective (φ : (Fin 3 → F) → ℝ) :
    ∑ x, (if Function.Injective x then φ x else 0) = ∑ x : Trip F, φ x.1 := by
  rw [← sum_filter]
  exact sum_subtype _ (fun x => by simp) φ

theorem tripleMatrix_mulVec (g : Trip F → ℝ) (x : Trip F) :
    (tripleMatrix F *ᵥ g) x = tripleOp (extTrip g) x.1 := by
  unfold tripleOp
  simp only [mulVec, dotProduct, tripleMatrix]
  rw [mul_sum]
  have h : ∀ y : Fin 3 → F, ((tripleDen F)⁻¹ * if DisjTriple x.1 y then extTrip g y else 0) =
      if Function.Injective y then
        ((if ∀ i j, x.1 i ≠ y j then (tripleDen F)⁻¹ else 0) * extTrip g y) else 0 := by
    intro y
    unfold DisjTriple
    by_cases hy : Function.Injective y
    · by_cases hd : ∀ i j, x.1 i ≠ y j
      · simp [hy, hd]
      · simp [hy, hd]
    · simp [hy]
  simp only [tripleDen] at h ⊢
  rw [sum_congr rfl fun y _ => h y, sum_ite_injective]
  refine sum_congr rfl fun y _ => ?_
  simp [extTrip, y.2]

theorem tripleMatrix_quad (g : Trip F → ℝ) :
    g ⬝ᵥ (tripleMatrix F *ᵥ g) =
      ∑ x, (if Function.Injective x then extTrip g x * tripleOp (extTrip g) x else 0) := by
  rw [sum_ite_injective]
  simp only [dotProduct, tripleMatrix_mulVec]
  refine sum_congr rfl fun x _ => ?_
  simp [extTrip, x.2]

theorem trip_sq (g : Trip F → ℝ) :
    g ⬝ᵥ g = ∑ x, (if Function.Injective x then extTrip g x ^ 2 else 0) := by
  rw [sum_ite_injective]
  simp only [dotProduct]
  refine sum_congr rfl fun x _ => ?_
  simp [extTrip, x.2, sq]

theorem trip_sum (g : Trip F → ℝ) :
    ∑ x, g x = ∑ x, (if Function.Injective x then extTrip g x else 0) := by
  rw [sum_ite_injective]
  refine sum_congr rfl fun x _ => ?_
  simp [extTrip, x.2]

theorem tripleMatrix_transpose : (tripleMatrix F)ᵀ = tripleMatrix F := by
  ext x y
  simp only [transpose_apply, tripleMatrix]
  have : (∀ i j, y.1 i ≠ x.1 j) ↔ ∀ i j, x.1 i ≠ y.1 j := disj_comm y.1 x.1
  simp only [this]

theorem tripleMatrix_isHermitian : (tripleMatrix F).IsHermitian := by
  unfold Matrix.IsHermitian
  rw [Matrix.conjTranspose_eq_transpose_of_trivial]
  exact tripleMatrix_transpose

theorem tripleMatrix_row (hn : 6 ≤ Fintype.card F) (x : Trip F) :
    ∑ y, tripleMatrix F x y = 1 := by
  have h := tripleMatrix_mulVec (F := F) (fun _ => 1) x
  have he : extTrip (F := F) (fun _ => (1 : ℝ)) =
      fun y => if Function.Injective y then 1 else 0 := by
    funext y
    simp [extTrip]
  have h1 : tripleOp (extTrip (F := F) (fun _ => (1 : ℝ))) x.1 =
      tripleOp (fun _ => (1 : ℝ)) x.1 := by
    rw [he]
    unfold tripleOp
    congr 1
    refine sum_congr rfl fun y _ => ?_
    by_cases hy : DisjTriple x.1 y
    · simp [hy, hy.1]
    · simp [hy]
  rw [h1, tripleOp_one hn x.2] at h
  simpa [mulVec, dotProduct] using h

/-- **`T ⪯ I`** on `L²(𝒯)` as a matrix inequality (`it:triple:bound`, from WP-S's
`tripleOp_le`). -/
theorem tripleMatrix_le_one (hn : 6 ≤ Fintype.card F) : (1 - tripleMatrix F).PosSemidef := by
  rw [posSemidef_iff_dotProduct_mulVec]
  refine ⟨isHermitian_one.sub tripleMatrix_isHermitian, fun g => ?_⟩
  simp only [star_trivial]
  rw [sub_mulVec, one_mulVec, dotProduct_sub, tripleMatrix_quad, trip_sq]
  linarith [tripleOp_le hn (extTrip g)]

/-- **`T ⪰ -3/(n-3) I`** on `L²(𝒯)` as a matrix inequality (`it:triple:bound`, from WP-S's
`tripleOp_ge`). -/
theorem tripleMatrix_ge (hn : 6 ≤ Fintype.card F) :
    (tripleMatrix F + (3 / ((Fintype.card F : ℝ) - 3)) • 1).PosSemidef := by
  rw [posSemidef_iff_dotProduct_mulVec]
  refine ⟨isHermitian_of_transpose (by
    rw [transpose_add, transpose_smul, transpose_one, tripleMatrix_transpose]), fun g => ?_⟩
  simp only [star_trivial]
  rw [add_mulVec, dotProduct_add, smul_mulVec, one_mulVec, dotProduct_smul, smul_eq_mul,
    tripleMatrix_quad, trip_sq]
  linarith [tripleOp_ge hn (extTrip g)]

/-- **`-3/(n-3) (I - J) ⪯ T - J ⪯ 3/(n-3) (I - J)`** on `L²(𝒯)` (`it:triple:bound`,
`‖T - J‖ ≤ 3/(n-3)`, from WP-S's `tripleOp_abs_le`; `n ≥ 7`). -/
theorem tripleMatrix_centred (hn : 7 ≤ Fintype.card F) :
    ((tripleMatrix F - meanMatrix (Trip F)) +
        (3 / ((Fintype.card F : ℝ) - 3)) • (1 - meanMatrix (Trip F))).PosSemidef ∧
      ((3 / ((Fintype.card F : ℝ) - 3)) • (1 - meanMatrix (Trip F)) -
        (tripleMatrix F - meanMatrix (Trip F))).PosSemidef := by
  have hne : Nonempty (Trip F) := by
    have hc : 3 ≤ Fintype.card F := by omega
    obtain ⟨e⟩ : Nonempty (Fin 3 ↪ F) := Function.Embedding.nonempty_of_card_le
      (by simpa using hc)
    exact ⟨⟨e, e.injective⟩⟩
  refine centred_of_meanZero _ tripleMatrix_transpose (tripleMatrix_row (by omega)) _ ?_
  intro g hg
  rw [tripleMatrix_quad, trip_sq]
  exact tripleOp_abs_le hn (extTrip g) (by rw [← trip_sum]; exact hg)

end OnePrime

/-! ## The tensor step -/

section Tensor

variable {K : Type*} [Fintype K] [DecidableEq K] {Ω : K → Type*} [∀ j, Fintype (Ω j)]
  [∀ j, DecidableEq (Ω j)]

omit [Fintype K] [DecidableEq K] [∀ j, Fintype (Ω j)] [∀ j, DecidableEq (Ω j)] in
/-- The pull-back of a factor to the product index set. -/
def pull (k : K) (A : Matrix (Ω k) (Ω k) ℝ) : Matrix (∀ j, Ω j) (∀ j, Ω j) ℝ :=
  A.submatrix (fun x : ∀ j, Ω j => x k) (fun x => x k)

omit [Fintype K] [DecidableEq K] [∀ j, Fintype (Ω j)] [∀ j, DecidableEq (Ω j)] in
theorem pull_posSemidef (k : K) {A : Matrix (Ω k) (Ω k) ℝ} (hA : A.PosSemidef) :
    (pull k A).PosSemidef :=
  hA.submatrix _

omit [Fintype K] [DecidableEq K] [∀ j, Fintype (Ω j)] [∀ j, DecidableEq (Ω j)] in
theorem pull_add (k : K) (A B : Matrix (Ω k) (Ω k) ℝ) : pull k (A + B) = pull k A + pull k B :=
  rfl

omit [Fintype K] [DecidableEq K] [∀ j, Fintype (Ω j)] [∀ j, DecidableEq (Ω j)] in
theorem pull_sub (k : K) (A B : Matrix (Ω k) (Ω k) ℝ) : pull k (A - B) = pull k A - pull k B :=
  rfl

omit [Fintype K] [DecidableEq K] [∀ j, Fintype (Ω j)] [∀ j, DecidableEq (Ω j)] in
theorem pull_smul (k : K) (c : ℝ) (A : Matrix (Ω k) (Ω k) ℝ) : pull k (c • A) = c • pull k A :=
  rfl

omit [Fintype K] [∀ j, Fintype (Ω j)] [∀ j, DecidableEq (Ω j)] in
theorem piKronOn_insert' {s : Finset K} {k : K} (hk : k ∉ s) (A : ∀ j, Matrix (Ω j) (Ω j) ℝ) :
    piKronOn (insert k s) A = pull k (A k) ⊙ piKronOn s A :=
  piKronOn_insert hk A

/-- **Tensor step, uncentred.** If `-c I ⪯ T_j ⪯ I` for every `j ∈ s`, with `0 ≤ c ≤ 1`, then
`-c I_s ⪯ ⊗_{j∈s} T_j ⪯ I_s` (partial products; the other factors are all-ones matrices). -/
theorem piKronOn_two_sided (s : Finset K) (T : ∀ j, Matrix (Ω j) (Ω j) ℝ) {c : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hlo : ∀ j ∈ s, (T j + c • (1 : Matrix (Ω j) (Ω j) ℝ)).PosSemidef)
    (hup : ∀ j ∈ s, ((1 : Matrix (Ω j) (Ω j) ℝ) - T j).PosSemidef) :
    (piKronOn s T + c • piKronOn s (fun j => (1 : Matrix (Ω j) (Ω j) ℝ))).PosSemidef ∧
      (piKronOn s (fun j => (1 : Matrix (Ω j) (Ω j) ℝ)) - piKronOn s T).PosSemidef := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have hones : (piKronOn (∅ : Finset K) T).PosSemidef := piKronOn_posSemidef _ (by simp)
    have he1 : piKronOn (∅ : Finset K) (fun j => (1 : Matrix (Ω j) (Ω j) ℝ)) =
        piKronOn (∅ : Finset K) T := by
      ext x y
      simp [piKronOn]
    rw [he1, sub_self]
    exact ⟨hones.add (hones.smul hc0), PosSemidef.zero⟩
  | @insert k s hk ih =>
    have hlo' : ∀ j ∈ s, (T j + c • (1 : Matrix (Ω j) (Ω j) ℝ)).PosSemidef :=
      fun j hj => hlo j (mem_insert_of_mem hj)
    have hup' : ∀ j ∈ s, ((1 : Matrix (Ω j) (Ω j) ℝ) - T j).PosSemidef :=
      fun j hj => hup j (mem_insert_of_mem hj)
    obtain ⟨ihlo, ihup⟩ := ih hlo' hup'
    have hAc0 := pull_posSemidef k (hlo k (mem_insert_self k s))
    have hA1A0 := pull_posSemidef k (hup k (mem_insert_self k s))
    rw [pull_add, pull_smul] at hAc0
    rw [pull_sub] at hA1A0
    set A := pull k (T k)
    set A1 := pull k (1 : Matrix (Ω k) (Ω k) ℝ)
    set B := piKronOn s T
    set B1 := piKronOn s (fun j => (1 : Matrix (Ω j) (Ω j) ℝ))
    have hB1 : B1.PosSemidef := piKronOn_posSemidef s (fun j _ => PosSemidef.one)
    have hAc : (A + c • A1).PosSemidef := hAc0
    have hA1A : (A1 - A).PosSemidef := hA1A0
    have hA1 : A1.PosSemidef := pull_posSemidef k PosSemidef.one
    have hAp : (A1 + A).PosSemidef := by
      have h := hAc.add (hA1.smul (sub_nonneg.mpr hc1))
      have he : A + c • A1 + (1 - c) • A1 = A1 + A := by
        ext x y
        simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
        ring
      rwa [he] at h
    have hBp : (B1 + B).PosSemidef := by
      have h := ihlo.add (hB1.smul (sub_nonneg.mpr hc1))
      have he : B + c • B1 + (1 - c) • B1 = B1 + B := by
        ext x y
        simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
        ring
      rwa [he] at h
    rw [piKronOn_insert' hk, piKronOn_insert' hk]
    change (A ⊙ B + c • (A1 ⊙ B1)).PosSemidef ∧ (A1 ⊙ B1 - A ⊙ B).PosSemidef
    constructor
    · have he : A ⊙ B + c • (A1 ⊙ B1) =
          (1 + c)⁻¹ • ((A + c • A1) ⊙ (B + c • B1) + c • ((A1 - A) ⊙ (B1 - B))) := by
        ext x y
        simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.hadamard_apply,
          smul_eq_mul]
        have : (1 + c) ≠ 0 := by linarith
        field_simp
        ring
      rw [he]
      exact ((hAc.hadamard ihlo).add ((hA1A.hadamard ihup).smul hc0)).smul
        (inv_nonneg.mpr (by linarith))
    · have he : A1 ⊙ B1 - A ⊙ B =
          (1 / 2 : ℝ) • ((A1 - A) ⊙ (B1 + B) + (A1 + A) ⊙ (B1 - B)) := by
        ext x y
        simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.hadamard_apply,
          smul_eq_mul]
        ring
      rw [he]
      exact ((hA1A.hadamard hBp).add (hAp.hadamard ihup)).smul (by norm_num)

/-- **Tensor step, centred.** If `0 ⪯ J_j ⪯ I` and
`-c (I - J_j) ⪯ T_j - J_j ⪯ c (I - J_j)` for every `j ∈ s`, with `0 ≤ c ≤ 1`, then the same holds
for the partial products `⊗_{j∈s} T_j`, `⊗_{j∈s} J_j`, `⊗_{j∈s} I`. -/
theorem piKronOn_centred (s : Finset K) (T J : ∀ j, Matrix (Ω j) (Ω j) ℝ) {c : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hJ : ∀ j ∈ s, (J j).PosSemidef)
    (hP : ∀ j ∈ s, ((1 : Matrix (Ω j) (Ω j) ℝ) - J j).PosSemidef)
    (hlo : ∀ j ∈ s, ((T j - J j) + c • ((1 : Matrix (Ω j) (Ω j) ℝ) - J j)).PosSemidef)
    (hup : ∀ j ∈ s, (c • ((1 : Matrix (Ω j) (Ω j) ℝ) - J j) - (T j - J j)).PosSemidef) :
    ((piKronOn s T - piKronOn s J) +
        c • (piKronOn s (fun j => (1 : Matrix (Ω j) (Ω j) ℝ)) - piKronOn s J)).PosSemidef ∧
      (c • (piKronOn s (fun j => (1 : Matrix (Ω j) (Ω j) ℝ)) - piKronOn s J) -
        (piKronOn s T - piKronOn s J)).PosSemidef := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have e1 : piKronOn (∅ : Finset K) T = piKronOn (∅ : Finset K) J := by
      ext x y
      simp [piKronOn]
    have e2 : piKronOn (∅ : Finset K) (fun j => (1 : Matrix (Ω j) (Ω j) ℝ)) =
        piKronOn (∅ : Finset K) J := by
      ext x y
      simp [piKronOn]
    rw [e1, e2, sub_self, smul_zero, add_zero, sub_self]
    exact ⟨PosSemidef.zero, PosSemidef.zero⟩
  | @insert k s hk ih =>
    obtain ⟨ihlo, ihup⟩ := ih (fun j hj => hJ j (mem_insert_of_mem hj))
      (fun j hj => hP j (mem_insert_of_mem hj)) (fun j hj => hlo j (mem_insert_of_mem hj))
      (fun j hj => hup j (mem_insert_of_mem hj))
    have hk' := mem_insert_self k s
    have hAJ0 := pull_posSemidef k (hJ k hk')
    have hPA0 := pull_posSemidef k (hP k hk')
    have hAlo0 := pull_posSemidef k (hlo k hk')
    have hAup0 := pull_posSemidef k (hup k hk')
    rw [pull_sub] at hPA0
    rw [pull_add, pull_sub, pull_smul, pull_sub] at hAlo0
    rw [pull_sub, pull_smul, pull_sub, pull_sub] at hAup0
    set A := pull k (T k)
    set AJ := pull k (J k)
    set A1 := pull k (1 : Matrix (Ω k) (Ω k) ℝ)
    set B := piKronOn s T
    set BJ := piKronOn s J
    set B1 := piKronOn s (fun j => (1 : Matrix (Ω j) (Ω j) ℝ))
    have hAJ : AJ.PosSemidef := hAJ0
    have hPA : (A1 - AJ).PosSemidef := hPA0
    have hAlo : ((A - AJ) + c • (A1 - AJ)).PosSemidef := hAlo0
    have hAup : (c • (A1 - AJ) - (A - AJ)).PosSemidef := hAup0
    have hBJ : BJ.PosSemidef := piKronOn_posSemidef s (fun j hj => hJ j (mem_insert_of_mem hj))
    have hPB : (B1 - BJ).PosSemidef :=
      piKronOn_sub_posSemidef s (fun j hj => hJ j (mem_insert_of_mem hj))
        (fun j hj => hP j (mem_insert_of_mem hj))
    have hcc : 0 ≤ c - c ^ 2 := by nlinarith
    rw [piKronOn_insert' hk, piKronOn_insert' hk, piKronOn_insert' hk]
    change ((A ⊙ B - AJ ⊙ BJ) + c • (A1 ⊙ B1 - AJ ⊙ BJ)).PosSemidef ∧
      (c • (A1 ⊙ B1 - AJ ⊙ BJ) - (A ⊙ B - AJ ⊙ BJ)).PosSemidef
    constructor
    · have he : (A ⊙ B - AJ ⊙ BJ) + c • (A1 ⊙ B1 - AJ ⊙ BJ) =
          AJ ⊙ ((B - BJ) + c • (B1 - BJ)) + ((A - AJ) + c • (A1 - AJ)) ⊙ BJ +
            (c - c ^ 2) • ((A1 - AJ) ⊙ (B1 - BJ)) +
            (1 / 2 : ℝ) • (((A - AJ) + c • (A1 - AJ)) ⊙ ((B - BJ) + c • (B1 - BJ)) +
              (c • (A1 - AJ) - (A - AJ)) ⊙ (c • (B1 - BJ) - (B - BJ))) := by
        ext x y
        simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.hadamard_apply,
          smul_eq_mul]
        ring
      rw [he]
      exact (((hAJ.hadamard ihlo).add (hAlo.hadamard hBJ)).add
        ((hPA.hadamard hPB).smul hcc)).add
        (((hAlo.hadamard ihlo).add (hAup.hadamard ihup)).smul (by norm_num))
    · have he : c • (A1 ⊙ B1 - AJ ⊙ BJ) - (A ⊙ B - AJ ⊙ BJ) =
          AJ ⊙ (c • (B1 - BJ) - (B - BJ)) + (c • (A1 - AJ) - (A - AJ)) ⊙ BJ +
            (c - c ^ 2) • ((A1 - AJ) ⊙ (B1 - BJ)) +
            (1 / 2 : ℝ) • ((c • (A1 - AJ) - (A - AJ)) ⊙ ((B - BJ) + c • (B1 - BJ)) +
              ((A - AJ) + c • (A1 - AJ)) ⊙ (c • (B1 - BJ) - (B - BJ))) := by
        ext x y
        simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, Matrix.hadamard_apply,
          smul_eq_mul]
        ring
      rw [he]
      exact (((hAJ.hadamard ihup).add (hAup.hadamard hBJ)).add
        ((hPA.hadamard hPB).smul hcc)).add
        (((hAup.hadamard ihlo).add (hAlo.hadamard ihup)).smul (by norm_num))

/-- **Tensor step over all coordinates, uncentred**: `-c I ⪯ ⊗_j T_j ⪯ I`. -/
theorem piKron_two_sided (T : ∀ j, Matrix (Ω j) (Ω j) ℝ) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hlo : ∀ j, (T j + c • (1 : Matrix (Ω j) (Ω j) ℝ)).PosSemidef)
    (hup : ∀ j, ((1 : Matrix (Ω j) (Ω j) ℝ) - T j).PosSemidef) :
    (piKron T + c • (1 : Matrix (∀ j, Ω j) (∀ j, Ω j) ℝ)).PosSemidef ∧
      ((1 : Matrix (∀ j, Ω j) (∀ j, Ω j) ℝ) - piKron T).PosSemidef := by
  have h := piKronOn_two_sided univ T hc0 hc1 (fun j _ => hlo j) (fun j _ => hup j)
  rw [piKronOn_univ, piKronOn_univ, piKron_one] at h
  exact h

/-- **Tensor step over all coordinates, centred**: with `J_j` the averaging matrices,
`-c (I - J) ⪯ ⊗_j T_j - J ⪯ c (I - J)` for the averaging matrix `J` of the product. -/
theorem piKron_centred (T : ∀ j, Matrix (Ω j) (Ω j) ℝ) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (hlo : ∀ j, ((T j - meanMatrix (Ω j)) + c • (1 - meanMatrix (Ω j))).PosSemidef)
    (hup : ∀ j, (c • (1 - meanMatrix (Ω j)) - (T j - meanMatrix (Ω j))).PosSemidef) :
    ((piKron T - meanMatrix (∀ j, Ω j)) + c • (1 - meanMatrix (∀ j, Ω j))).PosSemidef ∧
      (c • (1 - meanMatrix (∀ j, Ω j)) - (piKron T - meanMatrix (∀ j, Ω j))).PosSemidef := by
  have hJ : ∀ j, (meanMatrix (Ω j)).PosSemidef := fun j => by
    have he : meanMatrix (Ω j) = (Fintype.card (Ω j) : ℝ)⁻¹ •
        Matrix.vecMulVec (fun _ : Ω j => (1 : ℝ)) (star (fun _ : Ω j => (1 : ℝ))) := by
      ext x y
      simp [meanMatrix_apply, Matrix.vecMulVec]
    rw [he]
    exact (Matrix.posSemidef_vecMulVec_self_star _).smul (by positivity)
  have hP : ∀ j, (1 - meanMatrix (Ω j)).PosSemidef := fun j => by
    have h := (hlo j).add (hup j)
    have he : ((T j - meanMatrix (Ω j)) + c • (1 - meanMatrix (Ω j))) +
        (c • (1 - meanMatrix (Ω j)) - (T j - meanMatrix (Ω j))) =
        (2 * c) • (1 - meanMatrix (Ω j)) := by
      ext x y
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
      ring
    rw [he] at h
    rcases eq_or_lt_of_le hc0 with h0 | h0
    · -- `c = 0`: `1 - J` is positive semidefinite in any case
      have h1 : (1 - meanMatrix (Ω j)) = (1 - meanMatrix (Ω j)) * (1 - meanMatrix (Ω j)) := by
        rcases isEmpty_or_nonempty (Ω j) with hE | hE
        · ext x
          exact (hE.false x).elim
        · rw [sub_mul, mul_sub, mul_sub, one_mul, mul_one, one_mul, meanMatrix_mul_self]
          abel
      rw [h1]
      have hs : (1 - meanMatrix (Ω j))ᴴ = 1 - meanMatrix (Ω j) := by
        rw [Matrix.conjTranspose_eq_transpose_of_trivial, transpose_sub, transpose_one,
          meanMatrix_transpose]
      have := Matrix.posSemidef_conjTranspose_mul_self (1 - meanMatrix (Ω j))
      rwa [hs] at this
    · have h2 : (0 : ℝ) < 2 * c := by linarith
      have := h.smul (inv_nonneg.mpr h2.le)
      rwa [smul_smul, inv_mul_cancel₀ h2.ne', one_smul] at this
  have h := piKronOn_centred univ T (fun j => meanMatrix (Ω j)) hc0 hc1 (fun j _ => hJ j)
    (fun j _ => hP j) (fun j _ => hlo j) (fun j _ => hup j)
  rw [piKronOn_univ, piKronOn_univ, piKronOn_univ, piKron_one, piKron_meanMatrix] at h
  exact h

end Tensor

/-! ## The block -/

section Block

variable {K : Type*} [Fintype K] [DecidableEq K] (F : K → Type*) [∀ j, Fintype (F j)]
  [∀ j, DecidableEq (F j)]

/-- The tensor product `T_𝔅 = ⊗_j T` of the disjoint-triple matrices of a family of finite sets. -/
noncomputable def blockTripleMatrix : Matrix (∀ j, Trip (F j)) (∀ j, Trip (F j)) ℝ :=
  piKron (fun j => tripleMatrix (F j))

/-- `3/(n-3) ≤ 3/(b-3)` for `n ≥ b ≥ 7`, and `3/(b-3) ≤ 1`. -/
theorem three_div_le {b n : ℕ} (hb : 7 ≤ b) (hn : b ≤ n) :
    3 / ((n : ℝ) - 3) ≤ 3 / ((b : ℝ) - 3) ∧ 0 ≤ 3 / ((b : ℝ) - 3) ∧ 3 / ((b : ℝ) - 3) ≤ 1 := by
  have hb' : (7 : ℝ) ≤ b := by exact_mod_cast hb
  have hn' : (b : ℝ) ≤ n := by exact_mod_cast hn
  refine ⟨div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith),
    div_nonneg (by norm_num) (by linarith), ?_⟩
  rw [div_le_one (by linarith)]
  linarith

/-- **`it:triple:block`** (`sec:frontier:empty-triple-negative`(c)): for a finite family of
finite sets `F_j` with `|F_j| ≥ b ≥ 7` (the fields `𝔽_p` of the primes `p` of a block `𝔅`, with
least prime `b`), the tensor product `T_𝔅 = ⊗_j T` on `L²(∏_j 𝒯_j)` satisfies
`-3/(b-3) I ⪯ T_𝔅 ⪯ I` and `-3/(b-3) I ⪯ T_𝔅 - J ⪯ 3/(b-3) I`; the last pair is
`‖T_𝔅 - J‖ ≤ 3/(b-3)` for the symmetric matrix `T_𝔅 - J` (`J` the averaging matrix, the
projection on constants). Stated with the sharper `(I - J)` in place of `I` on the centred
part as well. -/
theorem triple_block (b : ℕ) (hb : 7 ≤ b) (hcard : ∀ j, b ≤ Fintype.card (F j)) :
    (blockTripleMatrix F + (3 / ((b : ℝ) - 3)) • 1).PosSemidef ∧
      (1 - blockTripleMatrix F).PosSemidef ∧
      ((blockTripleMatrix F - meanMatrix (∀ j, Trip (F j))) +
          (3 / ((b : ℝ) - 3)) • (1 - meanMatrix (∀ j, Trip (F j)))).PosSemidef ∧
      ((3 / ((b : ℝ) - 3)) • (1 - meanMatrix (∀ j, Trip (F j))) -
          (blockTripleMatrix F - meanMatrix (∀ j, Trip (F j)))).PosSemidef ∧
      ((blockTripleMatrix F - meanMatrix (∀ j, Trip (F j))) +
          (3 / ((b : ℝ) - 3)) • 1).PosSemidef ∧
      ((3 / ((b : ℝ) - 3)) • 1 -
          (blockTripleMatrix F - meanMatrix (∀ j, Trip (F j)))).PosSemidef := by
  unfold blockTripleMatrix
  set c : ℝ := 3 / ((b : ℝ) - 3)
  have hc0 : 0 ≤ c := (three_div_le hb le_rfl).2.1
  have hc1 : c ≤ 1 := (three_div_le hb le_rfl).2.2
  have hcj : ∀ j, 3 / ((Fintype.card (F j) : ℝ) - 3) ≤ c := fun j => (three_div_le hb (hcard j)).1
  -- uncentred
  have hlo : ∀ j, (tripleMatrix (F j) + c • (1 : Matrix (Trip (F j)) (Trip (F j)) ℝ)).PosSemidef :=
    fun j => by
      have h := (tripleMatrix_ge (F := F j) (by have := hcard j; omega)).add
        ((PosSemidef.one (n := Trip (F j)) (R := ℝ)).smul
          (sub_nonneg.mpr (hcj j)))
      have he : tripleMatrix (F j) + (3 / ((Fintype.card (F j) : ℝ) - 3)) • 1 +
          (c - 3 / ((Fintype.card (F j) : ℝ) - 3)) • (1 : Matrix (Trip (F j)) (Trip (F j)) ℝ) =
          tripleMatrix (F j) + c • 1 := by
        rw [add_assoc, ← add_smul]
        congr 2
        ring
      rwa [he] at h
  have hup : ∀ j, ((1 : Matrix (Trip (F j)) (Trip (F j)) ℝ) - tripleMatrix (F j)).PosSemidef :=
    fun j => tripleMatrix_le_one (by have := hcard j; omega)
  obtain ⟨h1, h2⟩ := piKron_two_sided (fun j => tripleMatrix (F j)) hc0 hc1 hlo hup
  -- centred
  have hP : ∀ j, (1 - meanMatrix (Trip (F j))).PosSemidef := fun j => by
    have hne : Nonempty (Trip (F j)) := by
      have hc : 3 ≤ Fintype.card (F j) := by have := hcard j; omega
      obtain ⟨e⟩ : Nonempty (Fin 3 ↪ F j) := Function.Embedding.nonempty_of_card_le
        (by simpa using hc)
      exact ⟨⟨e, e.injective⟩⟩
    have h1 : (1 - meanMatrix (Trip (F j))) =
        (1 - meanMatrix (Trip (F j)))ᴴ * (1 - meanMatrix (Trip (F j))) := by
      rw [Matrix.conjTranspose_eq_transpose_of_trivial, transpose_sub, transpose_one,
        meanMatrix_transpose, sub_mul, mul_sub, mul_sub, one_mul, mul_one, one_mul,
        meanMatrix_mul_self]
      abel
    rw [h1]
    exact Matrix.posSemidef_conjTranspose_mul_self _
  have hclo : ∀ j, ((tripleMatrix (F j) - meanMatrix (Trip (F j))) +
      c • (1 - meanMatrix (Trip (F j)))).PosSemidef := fun j => by
    have h := (tripleMatrix_centred (F := F j) (by have := hcard j; omega)).1.add
      ((hP j).smul (sub_nonneg.mpr (hcj j)))
    have he : (tripleMatrix (F j) - meanMatrix (Trip (F j))) +
        (3 / ((Fintype.card (F j) : ℝ) - 3)) • (1 - meanMatrix (Trip (F j))) +
        (c - 3 / ((Fintype.card (F j) : ℝ) - 3)) • (1 - meanMatrix (Trip (F j))) =
        (tripleMatrix (F j) - meanMatrix (Trip (F j))) + c • (1 - meanMatrix (Trip (F j))) := by
      rw [add_assoc, ← add_smul]
      congr 2
      ring
    rwa [he] at h
  have hcup : ∀ j, (c • (1 - meanMatrix (Trip (F j))) -
      (tripleMatrix (F j) - meanMatrix (Trip (F j)))).PosSemidef := fun j => by
    have h := (tripleMatrix_centred (F := F j) (by have := hcard j; omega)).2.add
      ((hP j).smul (sub_nonneg.mpr (hcj j)))
    have he : (3 / ((Fintype.card (F j) : ℝ) - 3)) • (1 - meanMatrix (Trip (F j))) -
        (tripleMatrix (F j) - meanMatrix (Trip (F j))) +
        (c - 3 / ((Fintype.card (F j) : ℝ) - 3)) • (1 - meanMatrix (Trip (F j))) =
        c • (1 - meanMatrix (Trip (F j))) - (tripleMatrix (F j) - meanMatrix (Trip (F j))) := by
      ext x y
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
      ring
    rwa [he] at h
  obtain ⟨h3, h4⟩ := piKron_centred (fun j => tripleMatrix (F j)) hc0 hc1 hclo hcup
  have hJ : (meanMatrix (∀ j, Trip (F j))).PosSemidef := by
    have he : meanMatrix (∀ j, Trip (F j)) = (Fintype.card (∀ j, Trip (F j)) : ℝ)⁻¹ •
        Matrix.vecMulVec (fun _ : (∀ j, Trip (F j)) => (1 : ℝ))
          (star (fun _ : (∀ j, Trip (F j)) => (1 : ℝ))) := by
      ext x y
      simp [meanMatrix_apply, Matrix.vecMulVec]
    rw [he]
    exact (Matrix.posSemidef_vecMulVec_self_star _).smul (by positivity)
  refine ⟨h1, h2, h3, h4, ?_, ?_⟩
  · have h := h3.add (hJ.smul hc0)
    have he : (piKron (fun j => tripleMatrix (F j)) - meanMatrix (∀ j, Trip (F j))) +
        c • (1 - meanMatrix (∀ j, Trip (F j))) + c • meanMatrix (∀ j, Trip (F j)) =
        (piKron (fun j => tripleMatrix (F j)) - meanMatrix (∀ j, Trip (F j))) + c • 1 := by
      ext x y
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
      ring
    rwa [he] at h
  · have h := h4.add (hJ.smul hc0)
    have he : c • (1 - meanMatrix (∀ j, Trip (F j))) -
        (piKron (fun j => tripleMatrix (F j)) - meanMatrix (∀ j, Trip (F j))) +
          c • meanMatrix (∀ j, Trip (F j)) =
        c • 1 - (piKron (fun j => tripleMatrix (F j)) - meanMatrix (∀ j, Trip (F j))) := by
      ext x y
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.sub_apply, smul_eq_mul]
      ring
    rwa [he] at h

end Block

/-- **From the two-sided Loewner bound to the operator norm.** For a symmetric real matrix `A`
with `-c I ⪯ A ⪯ c I` (`c ≥ 0`), `‖A f‖₂² ≤ c² ‖f‖₂²` for every `f` (counting norms; the
uniform-law norms differ by the same factor on both sides). By polarization:
`4 ⟨y, A x⟩ ≤ 2c (‖x‖² + ‖y‖²)` with `x = c f`, `y = A f`. -/
theorem mulVec_sq_le_of_two_sided {ι : Type*} [Fintype ι] [DecidableEq ι] (A : Matrix ι ι ℝ)
    (hA : Aᵀ = A) {c : ℝ} (hc : 0 ≤ c) (hlo : (A + c • 1).PosSemidef)
    (hup : (c • 1 - A).PosSemidef) (f : ι → ℝ) :
    (A *ᵥ f) ⬝ᵥ (A *ᵥ f) ≤ c ^ 2 * (f ⬝ᵥ f) := by
  have qlo : ∀ h : ι → ℝ, -(c * (h ⬝ᵥ h)) ≤ h ⬝ᵥ (A *ᵥ h) := fun h => by
    have := hlo.dotProduct_mulVec_nonneg h
    simp only [star_trivial, add_mulVec, dotProduct_add, smul_mulVec, one_mulVec,
      dotProduct_smul, smul_eq_mul] at this
    linarith
  have qup : ∀ h : ι → ℝ, h ⬝ᵥ (A *ᵥ h) ≤ c * (h ⬝ᵥ h) := fun h => by
    have := hup.dotProduct_mulVec_nonneg h
    simp only [star_trivial, sub_mulVec, dotProduct_sub, smul_mulVec, one_mulVec,
      dotProduct_smul, smul_eq_mul] at this
    linarith
  have hsym : ∀ x y : ι → ℝ, x ⬝ᵥ (A *ᵥ y) = y ⬝ᵥ (A *ᵥ x) := fun x y => by
    rw [dotProduct_mulVec, ← mulVec_transpose, hA, dotProduct_comm]
  -- `2 t U ≤ c (t² F + U)` for every `t`, with `U = ‖A f‖²`, `F = ‖f‖²`
  have key : ∀ t : ℝ, 2 * t * ((A *ᵥ f) ⬝ᵥ (A *ᵥ f)) ≤
      c * (t ^ 2 * (f ⬝ᵥ f) + (A *ᵥ f) ⬝ᵥ (A *ᵥ f)) := fun t => by
    set u := A *ᵥ f
    have h1 := qup (t • f + u)
    have h2 := qlo (t • f - u)
    have hs := hsym u (t • f)
    simp only [mulVec_add, mulVec_sub, mulVec_smul, dotProduct_add, add_dotProduct,
      dotProduct_sub, sub_dotProduct, dotProduct_smul, smul_dotProduct, smul_eq_mul] at h1 h2 hs
    have hs' := hsym (t • f) u
    simp only [mulVec_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul] at hs'
    have hfu : f ⬝ᵥ u = u ⬝ᵥ f := dotProduct_comm f u
    have hAf : f ⬝ᵥ (A *ᵥ f) = f ⬝ᵥ u := rfl
    nlinarith
  rcases eq_or_lt_of_le hc with h0 | h0
  · have := key 1
    rw [← h0] at this ⊢
    nlinarith
  · have := key c
    have h2 : c * (2 * ((A *ᵥ f) ⬝ᵥ (A *ᵥ f))) ≤
        c * (c ^ 2 * (f ⬝ᵥ f) + (A *ᵥ f) ⬝ᵥ (A *ᵥ f)) := by nlinarith
    have h3 := le_of_mul_le_mul_left h2 h0
    linarith

/-- **`it:triple:block`, the norm form**: `‖(T_𝔅 - J) f‖₂ ≤ 3/(b-3) ‖f‖₂` for every `f` on
`∏_j 𝒯_j` (squared, counting norms), i.e. `‖T_𝔅 - J‖ ≤ 3/(b-3)` (`|F_j| ≥ b ≥ 7`). -/
theorem triple_block_norm {K : Type*} [Fintype K] [DecidableEq K] (F : K → Type*)
    [∀ j, Fintype (F j)] [∀ j, DecidableEq (F j)] (b : ℕ) (hb : 7 ≤ b)
    (hcard : ∀ j, b ≤ Fintype.card (F j)) (f : (∀ j, Trip (F j)) → ℝ) :
    ((blockTripleMatrix F - meanMatrix (∀ j, Trip (F j))) *ᵥ f) ⬝ᵥ
        ((blockTripleMatrix F - meanMatrix (∀ j, Trip (F j))) *ᵥ f) ≤
      (3 / ((b : ℝ) - 3)) ^ 2 * (f ⬝ᵥ f) := by
  obtain ⟨-, -, -, -, h5, h6⟩ := triple_block F b hb hcard
  have hT : (blockTripleMatrix F - meanMatrix (∀ j, Trip (F j)))ᵀ =
      blockTripleMatrix F - meanMatrix (∀ j, Trip (F j)) := by
    rw [transpose_sub, meanMatrix_transpose]
    unfold blockTripleMatrix
    rw [piKron_transpose]
    simp only [tripleMatrix_transpose]
  exact mulVec_sq_le_of_two_sided _ hT (three_div_le hb le_rfl).2.1 h5 h6 f

/-- **`it:triple:block` for the fields `𝔽_p`** of a finite set `𝔅` of moduli (the primes of a
block) whose least element is at least `b ≥ 7`: `-3/(b-3) I ⪯ T_𝔅 ⪯ I` and
`-3/(b-3) I ⪯ T_𝔅 - J ⪯ 3/(b-3) I`, i.e. `‖T_𝔅 - J‖ ≤ 3/(b-3)`. Primality is not used. -/
theorem triple_block_zmod (B : Finset ℕ) [∀ p : B, NeZero (p : ℕ)] (b : ℕ) (hb : 7 ≤ b)
    (hB : ∀ p ∈ B, b ≤ p) :
    (blockTripleMatrix (fun p : B => ZMod (p : ℕ)) + (3 / ((b : ℝ) - 3)) • 1).PosSemidef ∧
      (1 - blockTripleMatrix (fun p : B => ZMod (p : ℕ))).PosSemidef ∧
      ((blockTripleMatrix (fun p : B => ZMod (p : ℕ)) -
          meanMatrix (∀ p : B, Trip (ZMod (p : ℕ)))) + (3 / ((b : ℝ) - 3)) • 1).PosSemidef ∧
      ((3 / ((b : ℝ) - 3)) • 1 - (blockTripleMatrix (fun p : B => ZMod (p : ℕ)) -
          meanMatrix (∀ p : B, Trip (ZMod (p : ℕ))))).PosSemidef := by
  obtain ⟨h1, h2, -, -, h5, h6⟩ := triple_block (fun p : B => ZMod (p : ℕ)) b hb
    (fun p => by rw [ZMod.card]; exact hB p.1 p.2)
  exact ⟨h1, h2, h5, h6⟩

/-- Non-vacuity: the hypotheses of `triple_block` hold for one factor with seven points. -/
example : (blockTripleMatrix (fun _ : Fin 1 => Fin 7) + (3 / ((7 : ℝ) - 3)) • 1).PosSemidef :=
  (triple_block (fun _ : Fin 1 => Fin 7) 7 le_rfl (fun _ => by simp)).1

end Sarkozy.Misc
