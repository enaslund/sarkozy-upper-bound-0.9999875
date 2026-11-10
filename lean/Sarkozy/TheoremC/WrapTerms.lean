module

public import Sarkozy.TheoremC.Main

@[expose] public section

/-!
# The fully wrapping terms (`lem:record:wrap-expansion`, "Wrapping terms")

`paper/sections/10_comparison_lemmas.tex`, proof of `lem:record:wrap-expansion`: let
`𝒲 = 𝒮` and `j = |𝒮|`. All `j` intervals wrap with probability `K^{-j}`; given this, the
averages `P_e` (`e ∉ 𝒮`) replace those inputs by `F_A` on both sides, and the term is
`K^{-j} E_s ⟨X'(s), Γ (T'Y')(s)⟩`, where `X'` carries `g^{I_K, M₀, s_e}` at `u_e` and `Y'`
carries `g^{I_1, M₀, s_e}` at `ι(v_e)` (`e ∈ 𝒮`), `Γ = C_ι(ν)`, and `T'` is the residue part
of the coupling. On every atom the brackets of (CP3) and (CP4) add up to
`(M_𝔟 ν_𝔟; ν_𝔟* M_𝔟) ⪰_ι 0`, `M_𝔟 = Ñ_𝔟 + ∑_t (π̃^s D^s + π̃^a D^a)`; then
`lem:record:common-mean`(b) bounds the term by `K^{-j}(V'_L V'_R)^{1/2}`, and
`lem:envelope-energy` with `T_Q = S + A` and fixed intervals gives
`V'_L, V'_R ≤ (B e^{S+A} (K^{2θ/d} R_I)^j + o(1)) Y`.

This file formalizes that argument:

* Stage 1. `wrapEnvelope` (the law `M_𝔟`), `wrapEnvelope_bracket` (the added brackets),
  `wrapEnvelope_price` (`∑_𝔟 ∑_t (π^s + π^a) ≤ S + A`).
* Stage 2. The matrix identities `wrapShift = D₀ · P · R₁` (the wrap from `I_K` to `I_1` is
  the mean `P` between the point masses at `b = 0` and `b' = 1`) and the reduction
  `wrapForm_eq` : `I_{ν,𝒮,𝒮} = K^{-|𝒮|} E_ω⟨X'_ω, Γ (𝒯' Y')_ω⟩` with the fixed-interval
  half-functions `wrapSourceHalf`, `wrapTargetHalf` (inactive queries averaged to `F_A`) and
  the operator `𝒯'` = mean on the interval coordinates, convolutions on the residues of the
  active queries, mean on the inactive queries. `𝒯'` is a sector operator for the
  exact-conductor sectors of (CP0)(d), so WP-S's `form_le_energies`
  (`lem:record:common-mean`(b)) gives `abs_wrapForm_le`:
  `|I_{ν,𝒮,𝒮}| ≤ K^{-|𝒮|} √V'_L √V'_R`, with the single-half random-inclusion energies
  `wrapInclusionEnergyL/R` of the fixed-interval half-functions under `⊗_𝔟 M_𝔟`.
* Stage 3. `FixedIntervalEnvelopeEnergies` (`lem:envelope-energy` with fixed intervals,
  `κ_e = K`, `T_Q = S + A`) and `wrappingTerms_of_envelope` :
  `FixedIntervalEnvelopeEnergies → WrappingTerms`.
-/

open Filter Finset Function
open scoped Topology BigOperators Matrix

namespace Sarkozy.TheoremC

open Sarkozy.FourierArithmetic Sarkozy.Functional Sarkozy.IndexSupport Sarkozy.Comparison
  Sarkozy.PaperFrame Sarkozy.RecordExpansion Sarkozy.RecordExpansion.Choice

/-! ## Brackets add -/

section BracketAdd

variable {V X : Type*} [Fintype V] [DecidableEq V]

theorem bracket_add {c : ReflectionCut V} {L K R L' K' R' : ((V → X) → ℝ) →ₗ[ℝ] ℝ}
    (h : c.Bracket L K R) (h' : c.Bracket L' K' R') : c.Bracket (L + L') (K + K') (R + R') where
  left_positive := h.left_positive.add h'.left_positive
  right_positive := h.right_positive.add h'.right_positive
  nonneg F G := by
    have h1 := h.nonneg F G
    have h2 := h'.nonneg F G
    have e : ∀ (M M' : ((V → X) → ℝ) →ₗ[ℝ] ℝ) (A B : (c.Half → X) → ℝ),
        c.form (M + M') A B = c.form M A B + c.form M' A B := fun _ _ _ _ => rfl
    rw [e, e, e]
    linarith

theorem bracket_zero (c : ReflectionCut V) :
    c.Bracket (0 : ((V → X) → ℝ) →ₗ[ℝ] ℝ) 0 0 where
  left_positive := positive_zero c
  right_positive := positive_zero c
  nonneg _ _ := by
    have e : ∀ (A B : (c.Half → X) → ℝ), c.form (0 : ((V → X) → ℝ) →ₗ[ℝ] ℝ) A B = 0 :=
      fun _ _ => rfl
    rw [e, e, e]
    norm_num

theorem bracket_sum {ι : Type*} (s : Finset ι) {c : ReflectionCut V}
    {L K R : ι → ((V → X) → ℝ) →ₗ[ℝ] ℝ} (h : ∀ i ∈ s, c.Bracket (L i) (K i) (R i)) :
    c.Bracket (∑ i ∈ s, L i) (∑ i ∈ s, K i) (∑ i ∈ s, R i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using bracket_zero c
  | insert a s ha ih =>
    rw [sum_insert ha, sum_insert ha, sum_insert ha]
    exact bracket_add (h a (mem_insert_self a s))
      (ih fun i hi => h i (mem_insert_of_mem hi))

end BracketAdd


/-! ## Stage 2: matrices -/

section ActPairing

variable {Ω ι : Type*} [Fintype Ω] [Fintype ι]

/-- `E_ω⟨X_ω, Γ (A Y)_ω⟩ = E_ω⟨(Aᵀ X)_ω, Γ Y_ω⟩`. -/
theorem pairing_act_right (Γ : Matrix ι ι ℝ) (A : Matrix Ω Ω ℝ) (X Y : Ω → ι → ℝ) :
    pairing Γ X (act A Y) = pairing Γ (act Aᵀ X) Y := by
  have hact : ∀ (B : Matrix Ω Ω ℝ) (Z : Ω → ι → ℝ) ω, act B Z ω = ∑ η, B ω η • Z η := by
    intro B Z ω
    funext a
    simp only [act, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  unfold pairing
  congr 1
  simp only [hact, Matrix.mulVec_sum, Matrix.mulVec_smul, dotProduct_sum, dotProduct_smul,
    sum_dotProduct, smul_dotProduct, smul_eq_mul, Matrix.transpose_apply]
  rw [Finset.sum_comm]

omit [Fintype ι] in
theorem act_smul (c : ℝ) (A : Matrix Ω Ω ℝ) (Z : Ω → ι → ℝ) : act (c • A) Z = c • act A Z := by
  funext ω a
  simp only [act, Matrix.smul_apply, smul_eq_mul, Pi.smul_apply, Finset.mul_sum]
  apply sum_congr rfl
  intro η _
  ring

end ActPairing

section MeanRange

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]

omit [Nonempty Ω] in
theorem meanMatrix_mul_diff (C : Chain Ω) {l : ℕ} (hl : l ≤ C.depth) (hl0 : l ≠ 0) :
    meanMatrix Ω * C.diff l = 0 := by
  unfold Chain.diff
  rw [ite_eq_right hl0, ← C.cond_zero, Matrix.mul_sub,
    C.cond_mul_cond 0 l (Nat.zero_le _) hl, C.cond_mul_cond 0 (l - 1) (Nat.zero_le _) (by omega),
    Nat.zero_min, Nat.zero_min, sub_self]

/-- The mean maps every exact-depth space of a chain into itself, as the identity on the
constants and as zero on the others: its sector bounds hold for every tail. -/
theorem meanMatrix_rangeBound (C : Chain Ω) (t : Tails C.depth) (l : Fin (C.depth + 1)) :
    RangeBound (C.diff l) (meanMatrix Ω) (t.tail l) := by
  have hl : (l : ℕ) ≤ C.depth := Nat.lt_succ_iff.mp l.isLt
  have hPP : C.diff l * C.diff l = C.diff l := by
    rw [C.diff_mul_diff hl hl, ite_eq_left rfl]
  apply RangeBound.of_vec (C.transpose_diff hl) hPP
  · intro f hf
    by_cases h0 : (l : ℕ) = 0
    · have hP : C.diff l = meanMatrix Ω := by
        unfold Chain.diff
        rw [ite_eq_left h0, C.cond_zero]
      rw [hP, Matrix.mulVec_mulVec, meanMatrix_mul_self]
    · have hz : meanMatrix Ω *ᵥ f = 0 := by
        rw [← hf, Matrix.mulVec_mulVec, meanMatrix_mul_diff C hl h0, Matrix.zero_mulVec]
      rw [hz, Matrix.mulVec_zero]
  · intro f hf
    by_cases h0 : (l : ℕ) = 0
    · have hP : C.diff l = meanMatrix Ω := by
        unfold Chain.diff
        rw [ite_eq_left h0, C.cond_zero]
      have hmf : meanMatrix Ω *ᵥ f = f := by rw [← hP]; exact hf
      have ht : t.tail l = 1 := by rw [h0]; exact t.tail_zero
      rw [hmf, ht, one_pow, one_mul]
    · have hz : meanMatrix Ω *ᵥ f = 0 := by
        rw [← hf, Matrix.mulVec_mulVec, meanMatrix_mul_diff C hl h0, Matrix.zero_mulVec]
      rw [hz, zero_dotProduct]
      exact mul_nonneg (sq_nonneg _) (by simpa using dotProduct_self_star_nonneg f)

theorem meanMatrix_mul_cond_zero (C : Chain Ω) : meanMatrix Ω * C.cond 0 = C.cond 0 := by
  rw [C.cond_zero, meanMatrix_mul_self]

end MeanRange

section IntervalMatrices

variable (K : ℕ) [NeZero K]

/-- The point mass at `b = 0` (the interval `I_K`) as a diagonal matrix. -/
def pointDiag : Matrix (ZMod K) (ZMod K) ℝ := fun b b' => if b = 0 ∧ b' = 0 then 1 else 0

/-- Evaluation at `c`: `(evalMat c *ᵥ f) b = f c`. -/
def evalMat (c : ZMod K) : Matrix (ZMod K) (ZMod K) ℝ := fun _ b' => if b' = c then 1 else 0

theorem card_zmod_ne_zero : (Fintype.card (ZMod K) : ℝ) ≠ 0 := by
  exact_mod_cast Fintype.card_ne_zero

/-- The wrap from `I_K` to `I_1` is the mean between the point masses at `b = 0` and
`b' = 1`: `wrapShift = D₀ P R₁`. -/
theorem wrapShift_eq : wrapShift K = pointDiag K * meanMatrix (ZMod K) * evalMat K 1 := by
  have hc := card_zmod_ne_zero K
  ext b b''
  simp only [Matrix.mul_apply, pointDiag, meanMatrix_apply, evalMat, wrapShift, shiftMatrix,
    convMatrix]
  have h1 : ∀ x : ZMod K, ∑ a : ZMod K, (if b = 0 ∧ a = 0 then (1 : ℝ) else 0) *
      (Fintype.card (ZMod K) : ℝ)⁻¹ = if b = 0 then (Fintype.card (ZMod K) : ℝ)⁻¹ else 0 := by
    intro _
    by_cases hb : b = 0
    · simp [hb]
    · simp [hb]
  simp only [h1 0]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  by_cases hb : b = 0
  · subst hb
    simp only [ite_true, sub_zero]
    by_cases h' : b'' = 1
    · simp [h']
    · simp [h']
  · simp [hb]

theorem mean_pointDiag_eval :
    meanMatrix (ZMod K) * pointDiag K * evalMat K 0 =
      (Fintype.card (ZMod K) : ℝ)⁻¹ • evalMat K 0 := by
  ext b b''
  simp only [Matrix.mul_apply, pointDiag, meanMatrix_apply, evalMat, Matrix.smul_apply,
    smul_eq_mul]
  have h1 : ∀ x : ZMod K, ∑ a : ZMod K, (Fintype.card (ZMod K) : ℝ)⁻¹ *
      (if a = 0 ∧ x = 0 then (1 : ℝ) else 0) = if x = 0 then (Fintype.card (ZMod K) : ℝ)⁻¹ else 0 := by
    intro x
    by_cases hx : x = 0
    · simp [hx]
    · simp [hx]
  simp only [h1]
  rw [Finset.sum_eq_single (0 : ZMod K)]
  · simp
  · intro x _ hx
    simp [hx]
  · intro h
    exact absurd (Finset.mem_univ _) h

theorem pointDiag_mul_eval : pointDiag K * evalMat K 0 = pointDiag K := by
  ext b b''
  simp only [Matrix.mul_apply, pointDiag, evalMat]
  rw [Finset.sum_eq_single (0 : ZMod K)]
  · by_cases hb : b = 0 <;> by_cases hb' : b'' = 0 <;> simp [hb, hb']
  · intro x _ hx
    simp [hx]
  · intro h
    exact absurd (Finset.mem_univ _) h

omit [NeZero K] in
theorem pointDiag_transpose : (pointDiag K)ᵀ = pointDiag K := by
  ext b b'
  simp only [Matrix.transpose_apply, pointDiag]
  by_cases hb : b = 0 <;> by_cases hb' : b' = 0 <;> simp [hb, hb']

end IntervalMatrices


section QueryMatrices

variable (K : ℕ) [NeZero K] {P : Type} [Fintype P] [DecidableEq P] (pr h : P → ℕ)
  [∀ q, NeZero (pr q ^ h q)]

/-- `A` on the interval coordinate, the identity on the residue coordinates. -/
def intervalMat (A : Matrix (ZMod K) (ZMod K) ℝ) :
    ∀ j, Matrix (CoordSpace K pr h j) (CoordSpace K pr h j) ℝ
  | none => A
  | some _ => 1

omit [Fintype P] [DecidableEq P] in
theorem intervalMat_mul (A B : Matrix (ZMod K) (ZMod K) ℝ) (j : Option P) :
    intervalMat K pr h A j * intervalMat K pr h B j = intervalMat K pr h (A * B) j := by
  cases j with
  | none => rfl
  | some q => exact Matrix.one_mul 1

omit [Fintype P] [DecidableEq P] in
theorem intervalMat_mul_coordTransitionWith (A B : Matrix (ZMod K) (ZMod K) ℝ)
    (μ : ∀ q, ZMod (pr q ^ h q) → ℝ) (j : Option P) :
    intervalMat K pr h A j * coordTransitionWith K pr h B μ j =
      coordTransitionWith K pr h (A * B) μ j := by
  cases j with
  | none => rfl
  | some q => exact Matrix.one_mul _

omit [Fintype P] [DecidableEq P] in
theorem coordTransitionWith_mul_intervalMat (A B : Matrix (ZMod K) (ZMod K) ℝ)
    (μ : ∀ q, ZMod (pr q ^ h q) → ℝ) (j : Option P) :
    coordTransitionWith K pr h B μ j * intervalMat K pr h A j =
      coordTransitionWith K pr h (B * A) μ j := by
  cases j with
  | none => rfl
  | some q => exact Matrix.mul_one _

omit [NeZero K] [Fintype P] [DecidableEq P] [∀ (q : P), NeZero (pr q ^ h q)] in
theorem intervalMat_transpose (A : Matrix (ZMod K) (ZMod K) ℝ) (j : Option P) :
    (intervalMat K pr h A j)ᵀ = intervalMat K pr h Aᵀ j := by
  cases j with
  | none => rfl
  | some q => exact Matrix.transpose_one

omit [NeZero K] [DecidableEq P] [∀ (q : P), NeZero (pr q ^ h q)] in
theorem piKron_intervalMat_smul (c : ℝ) (A : Matrix (ZMod K) (ZMod K) ℝ) :
    piKron (intervalMat K pr h (c • A)) = c • piKron (intervalMat K pr h A) := by
  have hf : intervalMat K pr h (c • A) =
      fun j => (Option.elim j c (fun _ => (1 : ℝ))) • intervalMat K pr h A j := by
    funext j
    cases j with
    | none => rfl
    | some q => exact (one_smul ℝ _).symm
  rw [hf, piKron_smul, Fintype.prod_option]
  simp

/-- `(⊗_j A_j) g (η) = g(η with b := c)` when `A` evaluates the interval coordinate at `c`
and is the identity on the residues. -/
theorem piKron_intervalMat_eval_mulVec (c : ZMod K) (g : (∀ j, CoordSpace K pr h j) → ℝ)
    (η : ∀ j, CoordSpace K pr h j) :
    (piKron (intervalMat K pr h (evalMat K c)) *ᵥ g) η =
      g (Function.update η none (c : CoordSpace K pr h none)) := by
  simp only [Matrix.mulVec, dotProduct, piKron_apply]
  rw [Finset.sum_eq_single (Function.update η none (c : CoordSpace K pr h none))]
  · rw [Finset.prod_eq_one, one_mul]
    intro j _
    cases j with
    | none => simp [intervalMat, evalMat]
    | some q =>
      simp only [intervalMat]
      rw [Function.update_of_ne (by simp)]
      exact Matrix.one_apply_eq _
  · intro η' _ hη'
    rw [Finset.prod_eq_zero_iff.mpr, zero_mul]
    by_contra hall
    push Not at hall
    apply hη'
    funext j
    cases j with
    | none =>
      have := hall none (mem_univ _)
      simp only [intervalMat, evalMat, ne_eq, ite_eq_right_iff, one_ne_zero, imp_false,
        not_not] at this
      simpa using this
    | some q =>
      have := hall (some q) (mem_univ _)
      simp only [intervalMat, Matrix.one_apply, ne_eq, ite_eq_right_iff, one_ne_zero, imp_false,
        not_not] at this
      rw [Function.update_of_ne (by simp)]
      exact this.symm
  · intro h'
    exact absurd (mem_univ _) h'

variable {E : Type} [Fintype E] [DecidableEq E] (S : Finset E)

/-- The query factors of the matrices of the reduction (`e ∈ 𝒮` active). -/
noncomputable def qDiag (e : E) :
    Matrix (∀ j, CoordSpace K pr h j) (∀ j, CoordSpace K pr h j) ℝ :=
  if e ∈ S then piKron (intervalMat K pr h (pointDiag K)) else 1

noncomputable def qEval (c : ZMod K) (e : E) :
    Matrix (∀ j, CoordSpace K pr h j) (∀ j, CoordSpace K pr h j) ℝ :=
  if e ∈ S then piKron (intervalMat K pr h (evalMat K c)) else 1

noncomputable def qMean (e : E) :
    Matrix (∀ j, CoordSpace K pr h j) (∀ j, CoordSpace K pr h j) ℝ :=
  if e ∈ S then piKron (intervalMat K pr h (meanMatrix (ZMod K))) else 1

noncomputable def qInactive (e : E) :
    Matrix (∀ j, CoordSpace K pr h j) (∀ j, CoordSpace K pr h j) ℝ :=
  if e ∈ S then 1 else meanMatrix (∀ j, CoordSpace K pr h j)

/-- The coupling `𝒯'` of the wrapping terms, per query: the mean on the interval coordinate
and the convolutions on the residues of an active query; the mean on an inactive query. -/
noncomputable def qCoupling (μ : E → ∀ q, ZMod (pr q ^ h q) → ℝ) (e : E) :
    Matrix (∀ j, CoordSpace K pr h j) (∀ j, CoordSpace K pr h j) ℝ :=
  if e ∈ S then piKron (coordTransitionWith K pr h (meanMatrix (ZMod K)) (μ e))
  else meanMatrix (∀ j, CoordSpace K pr h j)

/-- The transition of the fully wrapping term `I_{ν,𝒮,𝒮}`, per query. -/
noncomputable def qWrap (μ : E → ∀ q, ZMod (pr q ^ h q) → ℝ) (e : E) :
    Matrix (∀ j, CoordSpace K pr h j) (∀ j, CoordSpace K pr h j) ℝ :=
  if e ∈ S then piKron (coordTransitionWith K pr h (wrapShift K) (μ e))
  else meanMatrix (∀ j, CoordSpace K pr h j)

omit [Fintype E] in
theorem qWrap_eq (μ : E → ∀ q, ZMod (pr q ^ h q) → ℝ) (e : E) :
    qWrap K pr h S μ e = qDiag K pr h S e * qCoupling K pr h S μ e * qEval K pr h S 1 e := by
  unfold qWrap qDiag qCoupling qEval
  by_cases he : e ∈ S
  · simp only [he, ↓reduceIte]
    rw [piKron_mul, piKron_mul]
    congr 1
    funext j
    rw [intervalMat_mul_coordTransitionWith, coordTransitionWith_mul_intervalMat, ← wrapShift_eq]
  · simp only [he, ↓reduceIte, Matrix.one_mul, Matrix.mul_one]

omit [Fintype E] in
theorem qCoupling_eq_mean_mul (μ : E → ∀ q, ZMod (pr q ^ h q) → ℝ) (e : E) :
    qCoupling K pr h S μ e = qMean K pr h S e * qCoupling K pr h S μ e := by
  unfold qMean qCoupling
  by_cases he : e ∈ S
  · simp only [he, ↓reduceIte]
    rw [piKron_mul]
    congr 1
    funext j
    rw [intervalMat_mul_coordTransitionWith, meanMatrix_mul_self]
  · simp only [he, ↓reduceIte, Matrix.one_mul]

omit [Fintype E] in
theorem qMean_qDiag_qEval (e : E) :
    qMean K pr h S e * qDiag K pr h S e * qEval K pr h S 0 e =
      (if e ∈ S then (Fintype.card (ZMod K) : ℝ)⁻¹ else 1) • qEval K pr h S 0 e := by
  unfold qMean qDiag qEval
  by_cases he : e ∈ S
  · simp only [he, ↓reduceIte]
    rw [piKron_mul, piKron_mul]
    have : (fun j => intervalMat K pr h (meanMatrix (ZMod K)) j * intervalMat K pr h (pointDiag K) j *
        intervalMat K pr h (evalMat K 0) j) = intervalMat K pr h
          ((Fintype.card (ZMod K) : ℝ)⁻¹ • evalMat K 0) := by
      funext j
      rw [intervalMat_mul, intervalMat_mul, mean_pointDiag_eval]
    rw [this, piKron_intervalMat_smul]
  · simp only [he, ↓reduceIte, Matrix.one_mul, one_smul]

omit [Fintype E] in
theorem qDiag_eq_mul_qEval (e : E) :
    qDiag K pr h S e = qDiag K pr h S e * qEval K pr h S 0 e := by
  unfold qDiag qEval
  by_cases he : e ∈ S
  · simp only [he, ↓reduceIte]
    rw [piKron_mul]
    congr 1
    funext j
    rw [intervalMat_mul, pointDiag_mul_eval]
  · simp only [he, ↓reduceIte, Matrix.one_mul]

omit [Fintype E] [NeZero K] [DecidableEq P] [∀ (q : P), NeZero (pr q ^ h q)] in
theorem qDiag_transpose (e : E) : (qDiag K pr h S e)ᵀ = qDiag K pr h S e := by
  unfold qDiag
  by_cases he : e ∈ S
  · simp only [he, ↓reduceIte]
    rw [piKron_transpose]
    congr 1
    funext j
    rw [intervalMat_transpose, pointDiag_transpose]
  · simp only [he, ↓reduceIte, Matrix.transpose_one]

omit [Fintype E] [DecidableEq P] [∀ (q : P), NeZero (pr q ^ h q)] in
theorem qMean_transpose (e : E) : (qMean K pr h S e)ᵀ = qMean K pr h S e := by
  unfold qMean
  by_cases he : e ∈ S
  · simp only [he, ↓reduceIte]
    rw [piKron_transpose]
    congr 1
    funext j
    rw [intervalMat_transpose, meanMatrix_transpose]
  · simp only [he, ↓reduceIte, Matrix.transpose_one]

omit [Fintype E] in
theorem qInactive_transpose (e : E) : (qInactive K pr h S e)ᵀ = qInactive K pr h S e := by
  unfold qInactive
  by_cases he : e ∈ S
  · simp only [he, ↓reduceIte, Matrix.transpose_one]
  · simp only [he, ↓reduceIte, meanMatrix_transpose]

omit [Fintype E] in
theorem qCoupling_eq_inactive (μ : E → ∀ q, ZMod (pr q ^ h q) → ℝ) (e : E) :
    qCoupling K pr h S μ e =
      qInactive K pr h S e * qCoupling K pr h S μ e * qInactive K pr h S e := by
  unfold qInactive qCoupling
  by_cases he : e ∈ S
  · simp only [he, ↓reduceIte, Matrix.one_mul, Matrix.mul_one]
  · simp only [he, ↓reduceIte, meanMatrix_mul_self]

end QueryMatrices


/-! ## Stage 2: the reduction of the fully wrapping term -/

section Reduction

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] (m₀ : J₀ → ℕ) [∀ i, NeZero (m₀ i)]
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] (p : ∀ L, J L → ℕ)
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] (pr h : P → ℕ) [∀ q, NeZero (pr q ^ h q)]
  (hcop : Pairwise (Nat.Coprime on fun q => pr q ^ h q))
  {E : Type} [Fintype E] [DecidableEq E]

/-- The fixed-interval source inputs of the wrapping term of `𝒮`: `g^{I_K, M₀, s_e}` (interval
coordinate `b_e = 0`, i.e. `I_K`) for `e ∈ 𝒮`, and `F_A` for `e ∉ 𝒮`. -/
noncomputable def wrapSourceInput (L : ℕ) (A : Finset ℤ) (S : Finset E) (e : E)
    (η : ∀ j, CoordSpace blockScale pr h j) (x : ∀ b, AtomLabel m₀ p L b) : ℝ :=
  if e ∈ S then atomInput m₀ p pr h hcop L A e
    (Function.update η none ((0 : ZMod blockScale) : CoordSpace blockScale pr h none)) x
  else atomLift m₀ p L A x

/-- The fixed-interval target inputs: `g^{I_1, M₀, s_e}` (`b_e = 1`) for `e ∈ 𝒮`, `F_A`
otherwise. -/
noncomputable def wrapTargetInput (L : ℕ) (A : Finset ℤ) (S : Finset E) (e : E)
    (η : ∀ j, CoordSpace blockScale pr h j) (x : ∀ b, AtomLabel m₀ p L b) : ℝ :=
  if e ∈ S then atomInput m₀ p pr h hcop L A e
    (Function.update η none ((1 : ZMod blockScale) : CoordSpace blockScale pr h none)) x
  else atomLift m₀ p L A x

/-- The half-function `X'` of the wrapping term: the fixed-interval source inputs at the
sources `u_e`, `F_A` elsewhere. -/
noncomputable def wrapSourceHalf (u : E → reservedCut.Half) (L : ℕ) (A : Finset ℤ)
    (S : Finset E) :
    (E → ∀ j, CoordSpace blockScale pr h j) → (reservedCut.Half → ∀ b, AtomLabel m₀ p L b) → ℝ :=
  productHalf u (wrapSourceInput m₀ p pr h hcop L A S) (atomLift m₀ p L A)

/-- The half-function `Y'` of the wrapping term, at the reflected targets `ι v_e`. -/
noncomputable def wrapTargetHalf (w : E → reservedCut.Half) (L : ℕ) (A : Finset ℤ)
    (S : Finset E) :
    (E → ∀ j, CoordSpace blockScale pr h j) → (reservedCut.Half → ∀ b, AtomLabel m₀ p L b) → ℝ :=
  productHalf w (wrapTargetInput m₀ p pr h hcop L A S) (atomLift m₀ p L A)

/-- The coupling `𝒯'` of the wrapping term. -/
noncomputable def wrapCoupling (S : Finset E) (μ : E → ∀ q, ZMod (pr q ^ h q) → ℝ) :
    Matrix (E → ∀ j, CoordSpace blockScale pr h j) (E → ∀ j, CoordSpace blockScale pr h j) ℝ :=
  piKron (qCoupling blockScale pr h S μ)

theorem act_source_half (u : E → reservedCut.Half) (L : ℕ) (A : Finset ℤ) (S : Finset E) :
    act (piKron (fun e => qInactive blockScale pr h S e * qEval blockScale pr h S 0 e))
        (productHalf u (fun e => atomInput m₀ p pr h hcop L A e) (atomLift m₀ p L A)) =
      wrapSourceHalf m₀ p pr h hcop u L A S := by
  rw [act_productHalf]
  unfold wrapSourceHalf
  congr 1
  funext e ωe y
  unfold wrapSourceInput qInactive qEval
  by_cases he : e ∈ S
  · simp only [he, ↓reduceIte, Matrix.one_mul]
    exact piKron_intervalMat_eval_mulVec blockScale pr h 0 _ ωe
  · simp only [he, ↓reduceIte, Matrix.mul_one]
    rw [meanMatrix_mulVec, ← expect_atomInput m₀ p pr h hcop L A e y,
      FiniteLaw.expect_uniform, div_eq_inv_mul]

theorem act_target_half (w : E → reservedCut.Half) (L : ℕ) (A : Finset ℤ) (S : Finset E) :
    act (piKron (fun e => qInactive blockScale pr h S e * qEval blockScale pr h S 1 e))
        (productHalf w (fun e => atomInput m₀ p pr h hcop L A e) (atomLift m₀ p L A)) =
      wrapTargetHalf m₀ p pr h hcop w L A S := by
  rw [act_productHalf]
  unfold wrapTargetHalf
  congr 1
  funext e ωe y
  unfold wrapTargetInput qInactive qEval
  by_cases he : e ∈ S
  · simp only [he, ↓reduceIte, Matrix.one_mul]
    exact piKron_intervalMat_eval_mulVec blockScale pr h 1 _ ωe
  · simp only [he, ↓reduceIte, Matrix.mul_one]
    rw [meanMatrix_mulVec, ← expect_atomInput m₀ p pr h hcop L A e y,
      FiniteLaw.expect_uniform, div_eq_inv_mul]

/-- **The reduction of the fully wrapping term**: all `|𝒮|` intervals wrap with
probability `K^{-|𝒮|}`, and then the term is the coupled form of the fixed-interval
half-functions under the residue coupling `𝒯'`:
`I_{ν,𝒮,𝒮} = K^{-|𝒮|} E_ω⟨X'_ω, C_ι(ν) (𝒯' Y')_ω⟩`. -/
theorem wrapForm_eq (μ : E → ∀ q, ZMod (pr q ^ h q) → ℝ) (u w : E → reservedCut.Half)
    (ν : ∀ L b, ((Slot → AtomLabel m₀ p L b) → ℝ) →ₗ[ℝ] ℝ) (L : ℕ) (A : Finset ℤ)
    (S : Finset E) :
    wrapForm m₀ p pr h hcop μ u w ν L A S S =
      ((Fintype.card (ZMod blockScale) : ℝ)⁻¹) ^ S.card *
        pairing (reservedCut.matrix (tensorLaw (ν L))) (wrapSourceHalf m₀ p pr h hcop u L A S)
          (act (wrapCoupling pr h S μ) (wrapTargetHalf m₀ p pr h hcop w L A S)) := by
  have hW : (fun e => if e ∈ S then
      piKron (coordTransitionWith blockScale pr h (wrapShift blockScale) (μ e))
    else if e ∈ S then piKron (coordTransitionWith blockScale pr h (nowrapShift blockScale) (μ e))
    else meanMatrix (∀ j, CoordSpace blockScale pr h j)) = qWrap blockScale pr h S μ := by
    funext e
    unfold qWrap
    by_cases he : e ∈ S <;> simp [he]
  have h1 : wrapForm m₀ p pr h hcop μ u w ν L A S S =
      pairing (reservedCut.matrix (tensorLaw (ν L)))
        (productHalf u (fun e => atomInput m₀ p pr h hcop L A e) (atomLift m₀ p L A))
        (act (piKron (qWrap blockScale pr h S μ))
          (productHalf w (fun e => atomInput m₀ p pr h hcop L A e) (atomLift m₀ p L A))) := by
    unfold wrapForm
    rw [hW]
    exact expect_form_eq_pairing (Ωc := fun _ => CoordSpace blockScale pr h) reservedCut
      (tensorLaw (ν L)) _ _
  have hA : piKron (qWrap blockScale pr h S μ) = piKron (qDiag blockScale pr h S) *
      piKron (qCoupling blockScale pr h S μ) * piKron (qEval blockScale pr h S 1) := by
    rw [piKron_mul, piKron_mul]
    congr 1
    funext e
    exact qWrap_eq blockScale pr h S μ e
  have hB : piKron (qCoupling blockScale pr h S μ) =
      piKron (qMean blockScale pr h S) * piKron (qCoupling blockScale pr h S μ) := by
    rw [piKron_mul]
    congr 1
    funext e
    exact qCoupling_eq_mean_mul blockScale pr h S μ e
  have hC : piKron (qMean blockScale pr h S) * piKron (qDiag blockScale pr h S) *
      piKron (qEval blockScale pr h S 0) =
      ((Fintype.card (ZMod blockScale) : ℝ)⁻¹) ^ S.card • piKron (qEval blockScale pr h S 0) := by
    rw [piKron_mul, piKron_mul]
    have : (fun e => qMean blockScale pr h S e * qDiag blockScale pr h S e *
        qEval blockScale pr h S 0 e) =
        fun e => (if e ∈ S then (Fintype.card (ZMod blockScale) : ℝ)⁻¹ else 1) •
          qEval blockScale pr h S 0 e :=
      funext fun e => qMean_qDiag_qEval blockScale pr h S e
    rw [this, piKron_smul]
    congr 1
    rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]
  have hD : piKron (qDiag blockScale pr h S) =
      piKron (qDiag blockScale pr h S) * piKron (qEval blockScale pr h S 0) := by
    rw [piKron_mul]
    congr 1
    funext e
    exact qDiag_eq_mul_qEval blockScale pr h S e
  have hDt : (piKron (qDiag blockScale pr h S))ᵀ = piKron (qDiag blockScale pr h S) := by
    rw [piKron_transpose]
    congr 1
    funext e
    exact qDiag_transpose blockScale pr h S e
  have hMt : (piKron (qMean blockScale pr h S))ᵀ = piKron (qMean blockScale pr h S) := by
    rw [piKron_transpose]
    congr 1
    funext e
    exact qMean_transpose blockScale pr h S e
  have hIt : (piKron (qInactive blockScale pr h S))ᵀ = piKron (qInactive blockScale pr h S) := by
    rw [piKron_transpose]
    congr 1
    funext e
    exact qInactive_transpose blockScale pr h S e
  have hF : piKron (qCoupling blockScale pr h S μ) = piKron (qInactive blockScale pr h S) *
      piKron (qCoupling blockScale pr h S μ) * piKron (qInactive blockScale pr h S) := by
    rw [piKron_mul, piKron_mul]
    congr 1
    funext e
    exact qCoupling_eq_inactive blockScale pr h S μ e
  have e0 : ∀ Z : (E → ∀ j, CoordSpace blockScale pr h j) →
      (reservedCut.Half → ∀ b, AtomLabel m₀ p L b) → ℝ,
      act (piKron (qWrap blockScale pr h S μ)) Z = act (piKron (qDiag blockScale pr h S))
        (act (piKron (qCoupling blockScale pr h S μ)) (act (piKron (qEval blockScale pr h S 1)) Z)) :=
    fun Z => by rw [act_act, act_act, ← hA]
  have e1 : ∀ Z : (E → ∀ j, CoordSpace blockScale pr h j) →
      (reservedCut.Half → ∀ b, AtomLabel m₀ p L b) → ℝ,
      act (piKron (qDiag blockScale pr h S)) Z = act (piKron (qDiag blockScale pr h S))
        (act (piKron (qEval blockScale pr h S 0)) Z) :=
    fun Z => by rw [act_act, ← hD]
  have e2 : ∀ Z : (E → ∀ j, CoordSpace blockScale pr h j) →
      (reservedCut.Half → ∀ b, AtomLabel m₀ p L b) → ℝ,
      act (piKron (qCoupling blockScale pr h S μ)) Z = act (piKron (qMean blockScale pr h S))
        (act (piKron (qCoupling blockScale pr h S μ)) Z) :=
    fun Z => by rw [act_act, ← hB]
  have e3 : ∀ Z : (E → ∀ j, CoordSpace blockScale pr h j) →
      (reservedCut.Half → ∀ b, AtomLabel m₀ p L b) → ℝ,
      act (piKron (qCoupling blockScale pr h S μ)) Z = act (piKron (qInactive blockScale pr h S))
        (act (piKron (qCoupling blockScale pr h S μ)) (act (piKron (qInactive blockScale pr h S)) Z)) :=
    fun Z => by rw [act_act, act_act, ← hF]
  rw [h1, e0, pairing_act_right, hDt, e1, e2, pairing_act_right, hMt, act_act, act_act, hC,
    act_smul, pairing_smul_left, e3, pairing_act_right, hIt,
    act_act (piKron (qInactive blockScale pr h S)) (piKron (qEval blockScale pr h S 0)),
    act_act (piKron (qInactive blockScale pr h S)) (piKron (qEval blockScale pr h S 1)),
    piKron_mul, piKron_mul, act_source_half, act_target_half]
  rfl

/-- The single-half random-inclusion energy `V_{⊗M}(Z) = E_𝒥 E_ω Q_{⊗M}(Z^𝒥_ω, Z^𝒥_ω)` of a
half-function `Z`, with the revelation of (CP0)(d) (the interval coordinates are always
revealed, the residue depths have the tails `t`), as in `inclusionEnergyL` of
`Sarkozy.Comparison.ConcreteFrame`. For the fixed-interval half-functions the revealed
interval coordinates of the active queries and the coordinates of the inactive queries do
not enter (the half-functions do not depend on them), so this is the paper's `V'_s`; that
remark is not used in the proofs. -/
noncomputable def wrapInclusionEnergy (L : ℕ)
    (t : E → ∀ q, Tails (Chain.residues (pr q) (h q)).depth)
    (M : ∀ b : PaperAtom J L, ((Slot → AtomLabel m₀ p L b) → ℝ) →ₗ[ℝ] ℝ)
    (Z : (E → ∀ j, CoordSpace blockScale pr h j) → (reservedCut.Half → ∀ b, AtomLabel m₀ p L b) → ℝ) :
    ℝ :=
  (queryLaw (fun (_ : E) => coordChain blockScale pr h) (fun e => coordTails blockScale pr h (t e))).expect
    (fun J => (FiniteLaw.uniform (E → ∀ j, CoordSpace blockScale pr h j)).expect (fun ω =>
      reservedCut.form (tensorLaw M)
        (queryReveal (fun (_ : E) => coordChain blockScale pr h) J Z ω)
        (queryReveal (fun (_ : E) => coordChain blockScale pr h) J Z ω)))

theorem wrapInclusionEnergy_eq (L : ℕ) (t : E → ∀ q, Tails (Chain.residues (pr q) (h q)).depth)
    (M : ∀ b : PaperAtom J L, ((Slot → AtomLabel m₀ p L b) → ℝ) →ₗ[ℝ] ℝ)
    (Z : (E → ∀ j, CoordSpace blockScale pr h j) → (reservedCut.Half → ∀ b, AtomLabel m₀ p L b) → ℝ) :
    (queryRevelation (fun (_ : E) => coordChain blockScale pr h)
        (fun e => coordTails blockScale pr h (t e))).energy (reservedCut.matrix (tensorLaw M)) Z =
      wrapInclusionEnergy m₀ p pr h L t M Z := by
  rw [queryRevelation_energy]
  unfold queryEnergy wrapInclusionEnergy
  apply FiniteLaw.expect_congr
  intro J
  exact (expect_form_eq_pairing (Ωc := fun _ => CoordSpace blockScale pr h) reservedCut _ _ _).symm

/-- The coupling `𝒯'` is a sector operator for the exact-conductor sectors of (CP0)(d): the
mean on the interval coordinates and on the inactive queries, the convolutions (with the
residue tails `hnorm`) on the residues of the active queries. -/
theorem wrapCoupling_sectorOperator (S : Finset E) (μ : E → ∀ q, ZMod (pr q ^ h q) → ℝ)
    (hμ : ∀ e q r, 0 ≤ μ e q r) (hμ1 : ∀ e q, ∑ r, μ e q r = 1)
    (t : E → ∀ q, Tails (Chain.residues (pr q) (h q)).depth)
    (hnorm : ∀ e q (l : Fin ((Chain.residues (pr q) (h q)).depth + 1)) f,
      (Chain.residues (pr q) (h q)).diff l *ᵥ f = f →
      (convMatrix (μ e q) *ᵥ f) ⬝ᵥ (convMatrix (μ e q) *ᵥ f) ≤ (t e q).tail l ^ 2 * (f ⬝ᵥ f)) :
    SectorOperator (querySectors (fun (_ : E) => coordChain blockScale pr h))
      (wrapCoupling pr h S μ)
      (queryWeight (fun (_ : E) => coordChain blockScale pr h)
        (fun e => coordTails blockScale pr h (t e))) := by
  unfold wrapCoupling querySectors
  apply SectorOperator.pi
  intro e
  by_cases he : e ∈ S
  · have hq : qCoupling blockScale pr h S μ e =
        piKron (coordTransitionWith blockScale pr h (meanMatrix (ZMod blockScale)) (μ e)) := by
      unfold qCoupling
      exact ite_eq_left he
    rw [hq]
    apply SectorOperator.chain
    · intro j l
      cases j with
      | none => exact meanMatrix_rangeBound _ _ l
      | some q =>
        exact (coordTransition_hypotheses blockScale pr h (μ e) (hμ e) (hμ1 e) (t e) (hnorm e)
          (some q)).1 l
    · intro j
      cases j with
      | none => exact meanMatrix_mul_cond_zero _
      | some q =>
        exact (coordTransition_hypotheses blockScale pr h (μ e) (hμ e) (hμ1 e) (t e) (hnorm e)
          (some q)).2
  · have hq : qCoupling blockScale pr h S μ e = meanMatrix (∀ j, CoordSpace blockScale pr h j) := by
      unfold qCoupling
      exact ite_eq_right he
    rw [hq, ← piKron_meanMatrix]
    apply SectorOperator.chain
    · intro j l
      exact meanMatrix_rangeBound _ _ l
    · intro j
      exact meanMatrix_mul_cond_zero _

/-- **`lem:record:common-mean`(b) for the fully wrapping term**: with a per-atom bracket
`(M_𝔟 ν_𝔟; ν_𝔟* M_𝔟) ⪰_ι 0`,
`|I_{ν,𝒮,𝒮}| ≤ K^{-|𝒮|} V'_L^{1/2} V'_R^{1/2}`, where `V'_L`, `V'_R` are the single-half
random-inclusion energies under `⊗_𝔟 M_𝔟` of the fixed-interval half-functions. -/
theorem abs_wrapForm_le (μ : E → ∀ q, ZMod (pr q ^ h q) → ℝ)
    (hμ : ∀ e q r, 0 ≤ μ e q r) (hμ1 : ∀ e q, ∑ r, μ e q r = 1)
    (t : E → ∀ q, Tails (Chain.residues (pr q) (h q)).depth)
    (hnorm : ∀ e q (l : Fin ((Chain.residues (pr q) (h q)).depth + 1)) f,
      (Chain.residues (pr q) (h q)).diff l *ᵥ f = f →
      (convMatrix (μ e q) *ᵥ f) ⬝ᵥ (convMatrix (μ e q) *ᵥ f) ≤ (t e q).tail l ^ 2 * (f ⬝ᵥ f))
    (u w : E → reservedCut.Half) (ν M : ∀ L b, ((Slot → AtomLabel m₀ p L b) → ℝ) →ₗ[ℝ] ℝ)
    (hbr : ∀ L b, reservedCut.Bracket (M L b) (ν L b) (M L b)) (L : ℕ) (A : Finset ℤ)
    (S : Finset E) :
    |wrapForm m₀ p pr h hcop μ u w ν L A S S| ≤
      ((Fintype.card (ZMod blockScale) : ℝ)⁻¹) ^ S.card *
        (Real.sqrt (wrapInclusionEnergy m₀ p pr h L t (M L) (wrapSourceHalf m₀ p pr h hcop u L A S)) *
          Real.sqrt (wrapInclusionEnergy m₀ p pr h L t (M L) (wrapTargetHalf m₀ p pr h hcop w L A S))) := by
  have hG : (Matrix.fromBlocks (reservedCut.matrix (tensorLaw (M L)))
      (reservedCut.matrix (tensorLaw (ν L))) (reservedCut.matrix (tensorLaw (ν L)))ᵀ
      (reservedCut.matrix (tensorLaw (M L)))).PosSemidef :=
    (reservedCut.bracket_iff_blockMatrix_posSemidef _ _ _).mp (ReflectionCut.Bracket.tensor (hbr L))
  have hop := wrapCoupling_sectorOperator pr h S μ hμ hμ1 t hnorm
  have hb := form_le_energies
    (queryRevelation (fun (_ : E) => coordChain blockScale pr h)
      (fun e => coordTails blockScale pr h (t e)))
    (queryWeight_nonneg _ _) (fun s => (queryRevelation_prob _ _ s).symm.le) hop hG
    (wrapSourceHalf m₀ p pr h hcop u L A S) (wrapTargetHalf m₀ p pr h hcop w L A S)
  rw [wrapInclusionEnergy_eq, wrapInclusionEnergy_eq] at hb
  have hk : 0 ≤ ((Fintype.card (ZMod blockScale) : ℝ)⁻¹) ^ S.card := by positivity
  rw [wrapForm_eq, abs_mul, abs_of_nonneg hk]
  exact mul_le_mul_of_nonneg_left hb hk

end Reduction

/-! ## Stage 1: the envelope of the wrapping terms -/

namespace ComparisonData

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E] (D : ComparisonData m₀ p pr h E)

/-- The law `M_𝔟 = Ñ_𝔟 + ∑_t (π̃^s_{𝔟,t} D^s_{𝔟,t} + π̃^a_{𝔟,t} D^a_{𝔟,t})` dominating `ν_𝔟`
in the wrapping terms. -/
noncomputable def wrapEnvelope (L : ℕ) (b : PaperAtom J L) : AtomMeasure m₀ p L b :=
  D.GB.N L b + ∑ t, (D.CL.πt L b t .sym • D.CL.D L b t .sym +
    D.CL.πt L b t .skew • D.CL.D L b t .skew)

omit [DecidableEq P] in
/-- **The brackets of (CP3) and (CP4) add up**: `(M_𝔟 ν_𝔟; ν_𝔟* M_𝔟) ⪰_ι 0`. -/
theorem wrapEnvelope_bracket (L : ℕ) (b : PaperAtom J L) :
    reservedCut.Bracket (D.wrapEnvelope L b) (D.CL.ν L b) (D.wrapEnvelope L b) := by
  rw [D.nu_eq L b]
  unfold wrapEnvelope
  apply bracket_add (D.GB.bracket L b)
  apply bracket_sum
  intro t _
  exact bracket_add (D.CL.bracket L b t .sym) (D.CL.bracket L b t .skew)

omit [DecidableEq P] in
/-- The price of `M − Ñ` is at most `S + A`. -/
theorem wrapEnvelope_price (L : ℕ) :
    ∑ b, ∑ t, (D.CL.π L b t .sym + D.CL.π L b t .skew) ≤ D.CL.S + D.CL.A := by
  have h : ∑ b, ∑ t, (D.CL.π L b t .sym + D.CL.π L b t .skew) =
      ∑ b, symTotal (D.CL.π L) b + ∑ b, skewTotal (D.CL.π L) b := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro b _
    rw [sum_add_distrib]
    rfl
  rw [h]
  exact add_le_add (D.CL.S_total L) (D.CL.A_total L)

/-! ## Stage 3: the fixed-interval envelope energies give the wrapping-term bound -/

variable (hcop : Pairwise (Nat.Coprime on fun q => pr q ^ h q))

/-- `V'_L(𝒮)`: the single-half random-inclusion energy under `⊗_𝔟 M_𝔟` of the fixed-interval
source half-function of `𝒮`. -/
noncomputable def wrapInclusionEnergyL (S : Finset E) (L : ℕ) (A : Finset ℤ) : ℝ :=
  wrapInclusionEnergy m₀ p pr h L D.S.index.t (D.wrapEnvelope L)
    (wrapSourceHalf m₀ p pr h hcop D.S.Q.u L A S)

/-- `V'_R(𝒮)`: the same for the fixed-interval target half-function. -/
noncomputable def wrapInclusionEnergyR (S : Finset E) (L : ℕ) (A : Finset ℤ) : ℝ :=
  wrapInclusionEnergy m₀ p pr h L D.S.index.t (D.wrapEnvelope L)
    (wrapTargetHalf m₀ p pr h hcop D.S.Q.w L A S)

/-- The fixed-interval factor `κ_e^{2θ/d} R_I = K^{2θ/d} R_I` of one active query
(`lem:envelope-energy` with `κ_e = K`, `d = 72`). -/
noncomputable def fixedIntervalFactor : ℝ :=
  (blockScale : ℝ) ^ (2 * densityExponent / 72) * D.S.index.R_I

/-- **`lem:envelope-energy` at fixed intervals** (`κ_e = K`) for `M_𝔟 = Ñ_𝔟 + Q_𝔟`,
`Q_𝔟 = ∑_t (π̃^s D^s + π̃^a D^a)` of total price `T_Q ≤ S + A` (`wrapEnvelope_price`), robustly:
for every nonempty `𝒮`, `V'_L(𝒮), V'_R(𝒮) ≤ (B e^{S+A} (K^{2θ/d} R_I)^{|𝒮|} + o(1)) Y`. -/
def FixedIntervalEnvelopeEnergies : Prop :=
  ∃ εf : ℕ → ℝ, (∀ L, 0 ≤ εf L) ∧ Tendsto εf atTop (𝓝 0) ∧ ∃ cf : ℝ, 0 ≤ cf ∧
    AtCounterexamples D.Y (fun L A => ∀ S : Finset E, S ≠ ∅ →
      D.wrapInclusionEnergyL hcop S L A ≤
          (D.B * Real.exp (D.CL.S + D.CL.A) * D.fixedIntervalFactor ^ S.card + εf L) * D.Y L A +
            remainder cf L A ∧
      D.wrapInclusionEnergyR hcop S L A ≤
          (D.B * Real.exp (D.CL.S + D.CL.A) * D.fixedIntervalFactor ^ S.card + εf L) * D.Y L A +
            remainder cf L A)

omit [DecidableEq P] in
/-- `K^{-1} · K^{2θ/d} R_I = R_I K^{2θ/d − 1}`, the ratio of `W`. -/
theorem inv_card_mul_fixedIntervalFactor :
    (Fintype.card (ZMod blockScale) : ℝ)⁻¹ * D.fixedIntervalFactor = D.wrapRatio := by
  have hK : (blockScale : ℝ) ≠ 0 := by norm_num [blockScale]
  unfold fixedIntervalFactor wrapRatio
  rw [ZMod.card, Real.rpow_sub_one hK]
  field_simp

/-- **The wrapping terms from the fixed-interval envelope energies**:
`lem:record:common-mean`(b) (`abs_wrapForm_le`), the bracket of `M_𝔟` (`wrapEnvelope_bracket`)
and `lem:envelope-energy` at fixed intervals give the hypothesis `WrappingTerms` of Theorem C,
with the same relative error and remainder constant. -/
theorem wrappingTerms_of_envelope (hf : D.FixedIntervalEnvelopeEnergies hcop) :
    D.WrappingTerms hcop := by
  obtain ⟨εf, hεf0, hεf, cf, hcf, hV⟩ := hf
  refine ⟨εf, hεf0, hεf, cf, hcf, ?_⟩
  filter_upwards [hV] with L hL
  intro C hC hind A hA hcounter S hS
  obtain ⟨hVL, hVR⟩ := hL C hC hind A hA hcounter S hS
  have hY0 : 0 ≤ D.Y L A := nonneg_of_counterexample hC hcounter
  have hF0 : 0 ≤ D.fixedIntervalFactor :=
    mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) D.S.index.hR_I
  have hr0 : 0 ≤ remainder cf L A := remainder_nonneg' hcf L A
  have hBd0 : 0 ≤ (D.B * Real.exp (D.CL.S + D.CL.A) * D.fixedIntervalFactor ^ S.card + εf L) *
      D.Y L A + remainder cf L A := by
    have := D.B_nonneg
    have := hεf0 L
    positivity
  have hab := abs_wrapForm_le m₀ p pr h hcop D.S.index.μ D.S.index.hμ D.S.index.hμ1 D.S.index.t
    D.S.index.hnorm D.S.Q.u D.S.Q.w D.CL.ν D.wrapEnvelope D.wrapEnvelope_bracket L A S
  have hsq : Real.sqrt (D.wrapInclusionEnergyL hcop S L A) *
      Real.sqrt (D.wrapInclusionEnergyR hcop S L A) ≤
      (D.B * Real.exp (D.CL.S + D.CL.A) * D.fixedIntervalFactor ^ S.card + εf L) * D.Y L A +
        remainder cf L A := by
    calc Real.sqrt (D.wrapInclusionEnergyL hcop S L A) *
          Real.sqrt (D.wrapInclusionEnergyR hcop S L A)
        ≤ Real.sqrt ((D.B * Real.exp (D.CL.S + D.CL.A) * D.fixedIntervalFactor ^ S.card + εf L) *
              D.Y L A + remainder cf L A) *
            Real.sqrt ((D.B * Real.exp (D.CL.S + D.CL.A) * D.fixedIntervalFactor ^ S.card +
              εf L) * D.Y L A + remainder cf L A) :=
          mul_le_mul (Real.sqrt_le_sqrt hVL) (Real.sqrt_le_sqrt hVR) (Real.sqrt_nonneg _)
            (Real.sqrt_nonneg _)
      _ = _ := Real.mul_self_sqrt hBd0
  have hk0 : 0 ≤ (Fintype.card (ZMod blockScale) : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  have hk1 : (Fintype.card (ZMod blockScale) : ℝ)⁻¹ ≤ 1 := by
    apply inv_le_one_of_one_le₀
    exact_mod_cast Fintype.card_pos
  have hkS : ((Fintype.card (ZMod blockScale) : ℝ)⁻¹) ^ S.card ≤ 1 := pow_le_one₀ hk0 hk1
  have hkS0 : 0 ≤ ((Fintype.card (ZMod blockScale) : ℝ)⁻¹) ^ S.card := pow_nonneg hk0 _
  calc |wrapForm m₀ p pr h hcop D.S.index.μ D.S.Q.u D.S.Q.w D.CL.ν L A S S|
      ≤ ((Fintype.card (ZMod blockScale) : ℝ)⁻¹) ^ S.card *
          (Real.sqrt (D.wrapInclusionEnergyL hcop S L A) *
            Real.sqrt (D.wrapInclusionEnergyR hcop S L A)) := hab
    _ ≤ ((Fintype.card (ZMod blockScale) : ℝ)⁻¹) ^ S.card *
          ((D.B * Real.exp (D.CL.S + D.CL.A) * D.fixedIntervalFactor ^ S.card + εf L) * D.Y L A +
            remainder cf L A) := mul_le_mul_of_nonneg_left hsq hkS0
    _ = D.B * Real.exp (D.CL.S + D.CL.A) *
            ((Fintype.card (ZMod blockScale) : ℝ)⁻¹ * D.fixedIntervalFactor) ^ S.card * D.Y L A +
          ((Fintype.card (ZMod blockScale) : ℝ)⁻¹) ^ S.card * (εf L * D.Y L A + remainder cf L A) := by
        rw [mul_pow]
        ring
    _ ≤ (D.B * Real.exp (D.CL.S + D.CL.A) * D.wrapRatio ^ S.card + εf L) * D.Y L A +
          remainder cf L A := by
        rw [D.inv_card_mul_fixedIntervalFactor]
        have h1 : ((Fintype.card (ZMod blockScale) : ℝ)⁻¹) ^ S.card *
            (εf L * D.Y L A + remainder cf L A) ≤ εf L * D.Y L A + remainder cf L A :=
          mul_le_of_le_one_left (add_nonneg (mul_nonneg (hεf0 L) hY0) hr0) hkS
        linarith

end ComparisonData

end Sarkozy.TheoremC
