module

public import Sarkozy.IndexSupport.Operators

/-!
# The one-cut coupling inequality

This file proves `lem:hyb:coupling` (One-cut coupling inequality) of the paper, the
whole-coordinate case of the Index-support lemma with one positive form in all three
roles.

Whole-coordinate case: every coordinate carries the two-step chain `Chain.whole`
(constants, identity), and the depth of coordinate `j` is one with probability `δ_j`
(`Tails.bernoulli`), independently. A depth vector `𝒥 : ∀ j, Fin 2` is identified with
the set `{j : 𝒥_j = 1}` of revealed coordinates; then
`Z^𝒥 = (⊗_j E_{j,𝒥_j}) Z` averages over the unrevealed coordinates, i.e. it is
`E[Z | ω_𝒥]` (`Chain.whole_cond_apply`).

The coupled index: `ω` is uniform and `Pr(ω' = η | ω) = ∏_j T_j(ω_j, η_j)` for doubly
stochastic `T_j` (`couplingLaw`). With `𝖨 = E⟨X(ω), C Y(ω')⟩` and
`𝖵 = ½ E_𝒥 E_ω [‖X^𝒥‖²_C + ‖Y^𝒥‖²_C]`, the conclusion (`one_cut_coupling`) is
`½‖E X + E Y‖²_C - 𝖵 ≤ 𝖨 ≤ 𝖵 - ½‖E X - E Y‖²_C`, and `|𝖨| ≤ 𝖵`.

The paper's hypothesis "`‖T_j f‖ ≤ δ_j ‖f‖` for `f` of mean zero" is used with
`0 ≤ δ_j ≤ 1`, which is implicit in the paper since `δ_j` is also the inclusion
probability of coordinate `j`.
-/

@[expose] public section

open Finset
open scoped BigOperators Matrix

namespace Sarkozy.IndexSupport

/-- Tails of a Bernoulli depth on `{0, 1}`: `Pr(J ≥ 1) = p`. -/
def Tails.bernoulli (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : Tails 1 where
  tail l := if l = 0 then 1 else p
  tail_zero := by simp
  antitone l hl := by
    have hl0 : l = 0 := by omega
    subst hl0
    simp [hp1]
  nonneg := by simp [hp0]

theorem Tails.bernoulli_tail_zero (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (Tails.bernoulli p hp0 hp1).tail 0 = 1 := rfl

theorem Tails.bernoulli_tail_one (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (Tails.bernoulli p hp0 hp1).tail 1 = p := rfl

namespace Chain

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]

theorem whole_cond_apply (l : ℕ) (x y : Ω) :
    (Chain.whole Ω).cond l x y =
      if l = 0 then (Fintype.card Ω : ℝ)⁻¹ else if x = y then 1 else 0 := by
  change (if l = 0 then meanMatrix Ω else 1) x y = _
  split_ifs <;> simp_all [meanMatrix_apply, Matrix.one_apply]

theorem whole_depth : (Chain.whole Ω).depth = 1 := rfl

theorem whole_diff_zero : (Chain.whole Ω).diff 0 = meanMatrix Ω := rfl

theorem whole_diff_one : (Chain.whole Ω).diff 1 = 1 - meanMatrix Ω := rfl

theorem whole_cond_zero : (Chain.whole Ω).cond 0 = meanMatrix Ω := rfl

end Chain

/-- A doubly stochastic matrix. -/
structure DoublyStochastic {Ω : Type*} [Fintype Ω] (T : Matrix Ω Ω ℝ) : Prop where
  nonneg : ∀ x y, 0 ≤ T x y
  row_sum : ∀ x, ∑ y, T x y = 1
  col_sum : ∀ y, ∑ x, T x y = 1

namespace DoublyStochastic

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω] {T : Matrix Ω Ω ℝ}

omit [DecidableEq Ω] [Nonempty Ω] in
/-- Rows summing to one: `T` fixes the constants. -/
theorem mul_mean (hT : DoublyStochastic T) : T * meanMatrix Ω = meanMatrix Ω := by
  ext x y
  simp only [Matrix.mul_apply, meanMatrix_apply, ← Finset.sum_mul, hT.row_sum x, one_mul]

omit [DecidableEq Ω] [Nonempty Ω] in
/-- Columns summing to one: `T` preserves the mean. -/
theorem mean_mul (hT : DoublyStochastic T) : meanMatrix Ω * T = meanMatrix Ω := by
  ext x y
  simp only [Matrix.mul_apply, meanMatrix_apply, ← Finset.mul_sum, hT.col_sum y, mul_one]

/-- A doubly stochastic matrix maps the constants identically and the functions of mean
zero into themselves; on the latter its norm is at most `δ` if it contracts them by `δ`.
These are the sector bounds of the whole-coordinate chain (`lem:sector`(a)). -/
theorem rangeBound (hT : DoublyStochastic T) {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hTδ : ∀ f : Ω → ℝ, ∑ x, f x = 0 → (T *ᵥ f) ⬝ᵥ (T *ᵥ f) ≤ δ ^ 2 * (f ⬝ᵥ f))
    (l : Fin ((Chain.whole Ω).depth + 1)) :
    RangeBound ((Chain.whole Ω).diff l) T ((Tails.bernoulli δ hδ0 hδ1).tail l) := by
  have hmm := meanMatrix_mul_self Ω
  have hm := hT.mul_mean
  have hmT := hT.mean_mul
  have hc : (Fintype.card Ω : ℝ)⁻¹ ≠ 0 := inv_ne_zero (by exact_mod_cast Fintype.card_ne_zero)
  match l with
  | ⟨0, _⟩ =>
    change RangeBound (meanMatrix Ω) T 1
    apply RangeBound.of_vec (meanMatrix_transpose Ω) hmm
    · intro f hf
      rw [Matrix.mulVec_mulVec, hmT, hf]
      rw [← hf, Matrix.mulVec_mulVec, hm, hf]
    · intro f hf
      have hTf : T *ᵥ f = f := by rw [← hf, Matrix.mulVec_mulVec, hm, hf]
      rw [hTf, one_pow, one_mul]
  | ⟨1, _⟩ =>
    change RangeBound (1 - meanMatrix Ω) T δ
    have hzero (f : Ω → ℝ) (hf : (1 - meanMatrix Ω) *ᵥ f = f) : meanMatrix Ω *ᵥ f = 0 := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec] at hf
      have h := congrArg (fun g => f - g) hf
      simp only [sub_sub_cancel, sub_self] at h
      exact h
    apply RangeBound.of_vec
    · rw [Matrix.transpose_sub, Matrix.transpose_one, meanMatrix_transpose]
    · rw [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, Matrix.one_mul, Matrix.one_mul,
        Matrix.mul_one, hmm]
      abel
    · intro f hf
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_mulVec, hmT, hzero f hf, sub_zero]
    · intro f hf
      apply hTδ
      have h := congrFun (hzero f hf) (Classical.arbitrary Ω)
      rw [meanMatrix_mulVec] at h
      simp only [Pi.zero_apply, mul_eq_zero] at h
      rcases h with h | h
      · exact absurd h hc
      · exact h

omit [DecidableEq Ω] [Nonempty Ω] in
/-- A doubly stochastic matrix is a contraction of `ℓ²(Ω)` (each row is a probability
law, so `(Tf)(x)² ≤ ∑_y T(x,y) f(y)²`, and the columns sum to one). -/
theorem contraction (hT : DoublyStochastic T) (f : Ω → ℝ) :
    (T *ᵥ f) ⬝ᵥ (T *ᵥ f) ≤ f ⬝ᵥ f := by
  have hrow (x : Ω) : (T *ᵥ f) x ^ 2 ≤ ∑ y, T x y * f y ^ 2 := by
    let μ : FiniteLaw Ω := ⟨T x, hT.nonneg x, hT.row_sum x⟩
    have h := μ.mean_sq_le_second_moment f
    simpa only [FiniteLaw.expect, Matrix.mulVec, dotProduct, μ] using h
  calc (T *ᵥ f) ⬝ᵥ (T *ᵥ f) = ∑ x, (T *ᵥ f) x ^ 2 := by simp only [dotProduct, sq]
    _ ≤ ∑ x, ∑ y, T x y * f y ^ 2 := Finset.sum_le_sum (fun x _ => hrow x)
    _ = ∑ y, f y ^ 2 * ∑ x, T x y := by
        rw [Finset.sum_comm]
        apply sum_congr rfl
        intro y _
        rw [Finset.mul_sum]
        apply sum_congr rfl
        intro x _
        ring
    _ = f ⬝ᵥ f := by simp only [hT.col_sum, mul_one, dotProduct, sq]

/-- With the trivial tail one, the sector bounds of the whole-coordinate chain hold for
every doubly stochastic matrix. -/
theorem rangeBound_one (hT : DoublyStochastic T) (l : Fin ((Chain.whole Ω).depth + 1)) :
    RangeBound ((Chain.whole Ω).diff l) T ((Tails.bernoulli 1 zero_le_one le_rfl).tail l) :=
  hT.rangeBound zero_le_one le_rfl (fun f _ => by rw [one_pow, one_mul]; exact hT.contraction f) l

end DoublyStochastic

section Coupling

variable {K : Type*} [Fintype K] [DecidableEq K] {Ω : K → Type*} [∀ j, Fintype (Ω j)]
  [∀ j, DecidableEq (Ω j)] [∀ j, Nonempty (Ω j)]

/-- The family of whole-coordinate chains. -/
noncomputable def wholeChains (Ω : K → Type*) [∀ j, Fintype (Ω j)] [∀ j, DecidableEq (Ω j)]
    [∀ j, Nonempty (Ω j)] : ∀ j, Chain (Ω j) :=
  fun j => Chain.whole (Ω j)

/-- Independent Bernoulli inclusion with probabilities `δ_j`. -/
def bernoulliTails (Ω : K → Type*) [∀ j, Fintype (Ω j)] [∀ j, DecidableEq (Ω j)]
    [∀ j, Nonempty (Ω j)] (δ : K → ℝ) (hδ0 : ∀ j, 0 ≤ δ j) (hδ1 : ∀ j, δ j ≤ 1) :
    ∀ j, Tails (wholeChains Ω j).depth :=
  fun j => Tails.bernoulli (δ j) (hδ0 j) (hδ1 j)

/-- The coupled index: `ω` uniform, and `Pr(ω' = η | ω) = ∏_j T_j(ω_j, η_j)`. -/
noncomputable def couplingLaw (T : ∀ j, Matrix (Ω j) (Ω j) ℝ)
    (hT : ∀ j, DoublyStochastic (T j)) : FiniteLaw ((∀ j, Ω j) × (∀ j, Ω j)) where
  weight p := (Fintype.card (∀ j, Ω j) : ℝ)⁻¹ * piKron T p.1 p.2
  nonneg p := mul_nonneg (inv_nonneg.mpr (Nat.cast_nonneg _))
    (Finset.prod_nonneg (fun j _ => (hT j).nonneg _ _))
  total := by
    have hc : (Fintype.card (∀ j, Ω j) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum]
    have hrow (ω : ∀ j, Ω j) : ∑ η, piKron T ω η = 1 := by
      simp only [piKron_apply]
      rw [← Fintype.prod_sum (fun j y => T j (ω j) y)]
      simp only [(hT _).row_sum, prod_const_one]
    simp only [hrow, sum_const, card_univ, nsmul_eq_mul, mul_one]
    field_simp

omit [∀ j, DecidableEq (Ω j)] in
/-- The coupled form equals the index form of the transition `T = ⊗_j T_j`:
`E⟨X(ω), C Y(ω')⟩ = E_ω⟨X(ω), C (T Y)(ω)⟩`, since `E[Y(ω') | ω] = (T Y)(ω)`. -/
theorem couplingLaw_expect {ι : Type*} [Fintype ι] (T : ∀ j, Matrix (Ω j) (Ω j) ℝ)
    (hT : ∀ j, DoublyStochastic (T j)) (C : Matrix ι ι ℝ) (X Y : (∀ j, Ω j) → ι → ℝ) :
    (couplingLaw T hT).expect (fun p => X p.1 ⬝ᵥ (C *ᵥ Y p.2)) =
      pairing C X (act (piKron T) Y) := by
  simp only [FiniteLaw.expect, couplingLaw, Fintype.sum_prod_type, pairing]
  rw [Finset.mul_sum]
  apply sum_congr rfl
  intro ω _
  have hY : act (piKron T) Y ω = ∑ η, piKron T ω η • Y η := by
    funext a
    simp only [act, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hY, Matrix.mulVec_sum, dotProduct_sum, Finset.mul_sum]
  apply sum_congr rfl
  intro η _
  rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]
  ring

omit [∀ j, Nonempty (Ω j)] in
/-- The doubly stochastic tensor transition `⊗_j T_j` satisfies the hypotheses on `𝒯` in
the whole-coordinate case (`lem:sector`(a)). -/
theorem coupling_sectorOperator [∀ j, Nonempty (Ω j)] (T : ∀ j, Matrix (Ω j) (Ω j) ℝ)
    (hT : ∀ j, DoublyStochastic (T j)) (δ : K → ℝ) (hδ0 : ∀ j, 0 ≤ δ j) (hδ1 : ∀ j, δ j ≤ 1)
    (hTδ : ∀ j (f : Ω j → ℝ), ∑ x, f x = 0 →
      (T j *ᵥ f) ⬝ᵥ (T j *ᵥ f) ≤ δ j ^ 2 * (f ⬝ᵥ f)) :
    SectorOperator (productSectors (wholeChains Ω)) (piKron T)
      (sectorWeight (wholeChains Ω) (bernoulliTails Ω δ hδ0 hδ1)) :=
  SectorOperator.chain (wholeChains Ω) (bernoulliTails Ω δ hδ0 hδ1)
    (fun j l => (hT j).rangeBound (hδ0 j) (hδ1 j) (hTδ j) l)
    (fun j => (hT j).mul_mean)

/-- `[[C, C], [C, C]] = [[1, 1], [1, 1]] ⊗ C ⪰ 0` for `C ⪰ 0`. -/
theorem joint_self {ι : Type*} [Fintype ι] {C : Matrix ι ι ℝ} (hC : C.PosSemidef) :
    (Matrix.fromBlocks C C Cᵀ C).PosSemidef := by
  have hCt := transpose_eq_of_posSemidef hC
  apply posSemidef_of_quadratic
  · simp only [Matrix.fromBlocks_transpose, hCt]
  · intro w
    have hw : w = Sum.elim (w ∘ Sum.inl) (w ∘ Sum.inr) := by
      funext i
      cases i <;> rfl
    rw [hw, fromBlocks_quadratic]
    have hsym : (w ∘ Sum.inr) ⬝ᵥ (C *ᵥ (w ∘ Sum.inl)) = (w ∘ Sum.inl) ⬝ᵥ (C *ᵥ (w ∘ Sum.inr)) := by
      rw [dotProduct_mulVec_symm hCt, dotProduct_comm]
    have h := quadratic_nonneg_of_posSemidef hC (w ∘ Sum.inl + w ∘ Sum.inr)
    rw [Matrix.mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct, hsym] at h
    linarith

/-- **One-cut coupling inequality** (`lem:hyb:coupling`, whole-coordinate case).

Let `C ⪰ 0` (symmetric) on a finite label set `ι`, `‖F‖²_C = ⟨F, C F⟩`, and let `T_j` be
doubly stochastic matrices on `Ω_j` with `‖T_j f‖ ≤ δ_j ‖f‖` for `f` of mean zero,
`0 ≤ δ_j ≤ 1`. Let `ω` be uniform on `Ω = ∏_j Ω_j`, `Pr(ω' = η | ω) = ∏_j T_j(ω_j, η_j)`,
and let `𝒥` include each coordinate independently with probability `δ_j`. With
`𝖨 = E⟨X(ω), C Y(ω')⟩` and `𝖵 = ½ E_𝒥 E_ω[‖X^𝒥‖²_C + ‖Y^𝒥‖²_C]`:
`½‖E X + E Y‖²_C - 𝖵 ≤ 𝖨 ≤ 𝖵 - ½‖E X - E Y‖²_C`, and `|𝖨| ≤ 𝖵`. No relation between
`E X` and `E Y` is assumed. -/
theorem one_cut_coupling {ι : Type*} [Fintype ι] {C : Matrix ι ι ℝ} (hC : C.PosSemidef)
    (T : ∀ j, Matrix (Ω j) (Ω j) ℝ) (hT : ∀ j, DoublyStochastic (T j))
    (δ : K → ℝ) (hδ0 : ∀ j, 0 ≤ δ j) (hδ1 : ∀ j, δ j ≤ 1)
    (hTδ : ∀ j (f : Ω j → ℝ), ∑ x, f x = 0 →
      (T j *ᵥ f) ⬝ᵥ (T j *ᵥ f) ≤ δ j ^ 2 * (f ⬝ᵥ f))
    (X Y : (∀ j, Ω j) → ι → ℝ) :
    let I := (couplingLaw T hT).expect (fun p => X p.1 ⬝ᵥ (C *ᵥ Y p.2))
    let V := (1 / 2) * (depthLaw (wholeChains Ω) (bernoulliTails Ω δ hδ0 hδ1)).expect
      (fun J => pairing C (depthReveal (wholeChains Ω) J X) (depthReveal (wholeChains Ω) J X) +
        pairing C (depthReveal (wholeChains Ω) J Y) (depthReveal (wholeChains Ω) J Y))
    (1 / 2) * ((vmean X + vmean Y) ⬝ᵥ (C *ᵥ (vmean X + vmean Y))) - V ≤ I ∧
      I ≤ V - (1 / 2) * ((vmean X - vmean Y) ⬝ᵥ (C *ᵥ (vmean X - vmean Y))) ∧
      |I| ≤ V := by
  intro I V
  have hop := coupling_sectorOperator T hT δ hδ0 hδ1 hTδ
  obtain ⟨-, -, -, -, ha, -⟩ := index_support_lemma (wholeChains Ω)
    (bernoulliTails Ω δ hδ0 hδ1) (piKron T) hop.maps hop.id_zero hop.norm_le (joint_self hC) X Y
  have hI : I = pairing C X (act (piKron T) Y) := couplingLaw_expect T hT C X Y
  have hV : V = (1 / 2) * (depthEnergy (wholeChains Ω) (bernoulliTails Ω δ hδ0 hδ1) C X +
      depthEnergy (wholeChains Ω) (bernoulliTails Ω δ hδ0 hδ1) C Y) := by
    change (1 / 2) * (depthLaw _ _).expect
      (fun J => pairing C _ _ + pairing C _ _) = _
    rw [FiniteLaw.expect_add]
    rfl
  have hCt := transpose_eq_of_posSemidef hC
  set m := vmean X
  set n := vmean Y
  have hsym : n ⬝ᵥ (C *ᵥ m) = m ⬝ᵥ (C *ᵥ n) := by
    rw [dotProduct_mulVec_symm hCt, dotProduct_comm]
  have hplus : (m + n) ⬝ᵥ (C *ᵥ (m + n)) =
      m ⬝ᵥ (C *ᵥ m) + 2 * (m ⬝ᵥ (C *ᵥ n)) + n ⬝ᵥ (C *ᵥ n) := by
    rw [Matrix.mulVec_add, dotProduct_add, add_dotProduct, add_dotProduct, hsym]
    ring
  have hminus : (m - n) ⬝ᵥ (C *ᵥ (m - n)) =
      m ⬝ᵥ (C *ᵥ m) - 2 * (m ⬝ᵥ (C *ᵥ n)) + n ⬝ᵥ (C *ᵥ n) := by
    rw [Matrix.mulVec_sub, dotProduct_sub, sub_dotProduct, sub_dotProduct, hsym]
    ring
  have hp0 := quadratic_nonneg_of_posSemidef hC (m + n)
  have hm0 := quadratic_nonneg_of_posSemidef hC (m - n)
  rw [← hI] at ha
  have hab := abs_le.mp ha
  refine ⟨?_, ?_, ?_⟩
  · rw [hplus, hV]
    linarith [hab.1]
  · rw [hminus, hV]
    linarith [hab.2]
  · rw [hplus] at hp0
    rw [hminus] at hm0
    rw [abs_le, hV]
    constructor <;> linarith [hab.1, hab.2]

end Coupling

end Sarkozy.IndexSupport
