module

public import Sarkozy.JointRows.RowsB
public import Sarkozy.FiveType.FoldDataRemark

/-!
# The remainder of a block fold kernel (`lem:joint-rows`(c))

Source: `paper/sections/16_extraction.tex`, `lem:joint-rows`(c) and its proof.

For kernels `T_{F,p}` of mass one with marginal densities `u_{L,p} = T_{F,p}𝟙`,
`u_{R,p} = T_{F,p}*𝟙`, `C_{F,p} = T_{F,p} - u_{L,p} ⊗ u_{R,p}`, `U_L = ⊗_p u_{L,p}`,
`U_R = ⊗_p u_{R,p}` with `‖U_L - 𝟙‖, ‖U_R - 𝟙‖ ≤ υ`, and `‖C_{F,p}‖ ≤ n_p`:
`‖T_{F,𝔅} - U_L ⊗ U_R - C_𝔅‖ ≤ (2υ + υ²)(∏_p (1 + n_p) - 1)` (`jointRows_c`). This is exactly
`Blocks.JointRowsC` (`jointRowsC_holds`).

**Proof (the paper's).** `R_𝔅 = T_{F,𝔅} - U_L ⊗ U_R - C_𝔅 = ∑_{S ≠ ∅} C_S ⊗ (a ⊗ b - 𝟙 ⊗ 𝟙)`,
`C_S = ⊗_{p∈S} C_{F,p}`, with the marginal rank `a ⊗ b = ⊗_{p∉S} u_{L,p} ⊗ u_{R,p}` of the inactive
primes (`RB_eq_sum`). On the inactive primes (the subtype `{p // p ∉ S}`),
`‖a - 𝟙‖ ≤ ‖U_L - 𝟙‖ ≤ υ` because `‖⊗_{p∈A} u_{L,p} - 𝟙‖² = ∏_{p∈A} ‖u_{L,p}‖² - 1` is
nondecreasing in `A` (`nrm_inactive_le`), so `‖a ⊗ b - 𝟙 ⊗ 𝟙‖ ≤ υ(1 + υ) + υ` (`formBound_rank`).
The term of `S` has norm at most `∏_{p∈S} n_p (2υ + υ²)`: in matrix form it is the entrywise product
of the tensorized blocks `(n_p I  C_p; C_pᵀ  n_p I)` of the active primes and of the pulled-back
block `((2υ+υ²)I  a⊗b - 1; ·  (2υ+υ²)I)` of the inactive ones (`formBound_term`). Summing over
`S ≠ ∅` gives the bound, since `∑_{S≠∅} ∏_{p∈S} n_p = ∏_p (1 + n_p) - 1`.
-/

@[expose] public section

open scoped BigOperators
open Matrix

namespace Sarkozy.JointRows

open Sarkozy.FiveType Sarkozy.FiveType.Blocks

/-! ## Norm bounds and block matrices -/

section NormBlocks

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- A norm bound gives the positive semidefinite block `(eI A; Aᵀ eI)`. -/
theorem psd_of_formBound {μ : FiniteLaw X} {A : X → X → ℝ} {e : ℝ} (h : FormBound μ A e) :
    (fromBlocks (e • wI μ) (wk μ A) (wk μ A)ᵀ (e • wI μ)).PosSemidef := by
  have hT : (e • wI μ)ᵀ = e • wI μ := by rw [transpose_smul, wI_transpose]
  refine psd_of_form hT hT fun v w => ?_
  have he := formBound_nonneg h
  rw [smul_mulVec, dotProduct_smul, smul_eq_mul, dot_wI, smul_mulVec, dotProduct_smul,
    smul_eq_mul, dot_wI, dot_wk, ip_self_eq, ip_self_eq]
  have h1 := h v w
  have h2 := neg_abs_le (kf μ A v w)
  have h3 : 2 * (nrm μ v * nrm μ w) ≤ nrm μ v ^ 2 + nrm μ w ^ 2 := by
    nlinarith [sq_nonneg (nrm μ v - nrm μ w)]
  nlinarith [mul_le_mul_of_nonneg_left h3 he]

/-- The block `(eI A; Aᵀ eI) ⪰ 0` gives the norm bound `‖A‖ ≤ e`. -/
theorem formBound_of_psd {μ : FiniteLaw X} {A : X → X → ℝ} {e : ℝ} (he : 0 ≤ e)
    (h : (fromBlocks (e • wI μ) (wk μ A) (wk μ A)ᵀ (e • wI μ)).PosSemidef) : FormBound μ A e := by
  intro Φ Ψ
  have key : ∀ t : ℝ, 0 ≤ (e * nrm μ Φ ^ 2) * (t * t) + (2 * kf μ A Φ Ψ) * t + e * nrm μ Ψ ^ 2 := by
    intro t
    have h1 := h.dotProduct_mulVec_nonneg (Sum.elim (fun x => t * Φ x) Ψ)
    simp only [star_trivial] at h1
    rw [dot_fromBlocks, smul_mulVec, dotProduct_smul, smul_eq_mul, dot_wI, smul_mulVec,
      dotProduct_smul, smul_eq_mul, dot_wI, dot_wk, dotProduct_mulVec, vecMul_transpose,
      dotProduct_comm, dot_wk, ip_self_eq, ip_self_eq] at h1
    have hs : nrm μ (fun x => t * Φ x) = |t| * nrm μ Φ := nrm_smul μ t Φ
    have hk : kf μ A (fun x => t * Φ x) Ψ = t * kf μ A Φ Ψ := by
      simp only [kf, Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
    rw [hs, hk, mul_pow, sq_abs] at h1
    nlinarith
  have hd := discrim_le_zero key
  rw [discrim] at hd
  have hsq : (kf μ A Φ Ψ) ^ 2 ≤ (e * nrm μ Φ * nrm μ Ψ) ^ 2 := by nlinarith
  have hpos : 0 ≤ e * nrm μ Φ * nrm μ Ψ :=
    mul_nonneg (mul_nonneg he (FiveType.nrm_nonneg _ _)) (FiveType.nrm_nonneg _ _)
  calc |kf μ A Φ Ψ| = Real.sqrt ((kf μ A Φ Ψ) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt ((e * nrm μ Φ * nrm μ Ψ) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = e * nrm μ Φ * nrm μ Ψ := Real.sqrt_sq hpos

omit [DecidableEq X] in
/-- The kernel form is additive in the kernel. -/
theorem kf_sum {I : Type*} (s : Finset I) (μ : FiniteLaw X) (K : I → X → X → ℝ)
    (Φ Ψ : X → ℝ) : kf μ (fun x y => ∑ S ∈ s, K S x y) Φ Ψ = ∑ S ∈ s, kf μ (K S) Φ Ψ := by
  simp only [kf, Finset.mul_sum, Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm]

omit [DecidableEq X] in
/-- Norm bounds add up. -/
theorem formBound_sum {I : Type*} (s : Finset I) {μ : FiniteLaw X} {K : I → X → X → ℝ}
    {e : I → ℝ} (h : ∀ S ∈ s, FormBound μ (K S) (e S)) :
    FormBound μ (fun x y => ∑ S ∈ s, K S x y) (∑ S ∈ s, e S) := by
  intro Φ Ψ
  rw [kf_sum]
  calc |∑ S ∈ s, kf μ (K S) Φ Ψ| ≤ ∑ S ∈ s, |kf μ (K S) Φ Ψ| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ S ∈ s, e S * nrm μ Φ * nrm μ Ψ := Finset.sum_le_sum fun S hS => h S hS Φ Ψ
    _ = (∑ S ∈ s, e S) * nrm μ Φ * nrm μ Ψ := by rw [Finset.sum_mul, Finset.sum_mul]

omit [DecidableEq X] in
/-- The all-ones block `(𝟙 𝟙; 𝟙 𝟙) ⪰ 0`. -/
theorem psd_blockOnes :
    (fromBlocks (Matrix.of fun _ _ => (1 : ℝ)) (Matrix.of fun _ _ => (1 : ℝ))
      (Matrix.of fun _ _ => (1 : ℝ))ᵀ (Matrix.of fun _ _ => (1 : ℝ)) :
        Matrix (X ⊕ X) (X ⊕ X) ℝ).PosSemidef := by
  have hT : (Matrix.of fun _ _ => (1 : ℝ) : Matrix X X ℝ)ᵀ = Matrix.of fun _ _ => 1 := by
    ext; rfl
  refine psd_of_form hT hT fun v w => ?_
  have e1 : ∀ u u' : X → ℝ, u ⬝ᵥ ((Matrix.of fun _ _ => (1 : ℝ) : Matrix X X ℝ) *ᵥ u') =
      (∑ x, u x) * ∑ y, u' y := by
    intro u u'
    simp only [dotProduct, mulVec, Matrix.of_apply, one_mul, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun x _ => by rw [Finset.mul_sum]
  rw [e1, e1, e1]
  nlinarith [sq_nonneg ((∑ x, v x) + ∑ y, w y)]

omit [DecidableEq X] in
/-- **The rank-two kernel `a ⊗ b - 𝟙 ⊗ 𝟙`**: if `E a = E b = 1` and `‖a - 𝟙‖, ‖b - 𝟙‖ ≤ υ`, its
norm is at most `υ(1 + υ) + υ = 2υ + υ²`. -/
theorem formBound_rank {μ : FiniteLaw X} {a b : X → ℝ} {υ : ℝ}
    (hb1 : μ.expect b = 1)
    (ha : nrm μ (fun x => a x - 1) ≤ υ) (hb : nrm μ (fun x => b x - 1) ≤ υ) :
    FormBound μ (fun x y => a x * b y - 1) (2 * υ + υ ^ 2) := by
  intro Φ Ψ
  have hυ : 0 ≤ υ := le_trans (FiveType.nrm_nonneg _ _) ha
  have hsplit : kf μ (fun x y => a x * b y - 1) Φ Ψ =
      ip μ Φ (fun x => a x - 1) * ip μ b Ψ + μ.expect Φ * ip μ (fun x => b x - 1) Ψ := by
    have hk1 : kf μ (fun x y => a x * b y) Φ Ψ =
        μ.expect (fun x => Φ x * a x) * μ.expect (fun y => b y * Ψ y) := by
      simp only [kf, FiniteLaw.expect, Finset.sum_mul_sum]
      exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
    have h1 : kf μ (fun x y => a x * b y - 1) Φ Ψ =
        μ.expect (fun x => Φ x * a x) * μ.expect (fun y => b y * Ψ y) -
          μ.expect Φ * μ.expect Ψ := by
      rw [← hk1, ← kf_const_one]
      simp only [kf, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
    rw [h1]
    unfold ip
    have e1 : μ.expect (fun x => Φ x * (a x - 1)) = μ.expect (fun x => Φ x * a x) - μ.expect Φ := by
      rw [← FiniteLaw.expect_sub]; exact μ.expect_congr fun x => by ring
    have e2 : μ.expect (fun y => (b y - 1) * Ψ y) = μ.expect (fun y => b y * Ψ y) - μ.expect Ψ := by
      rw [← FiniteLaw.expect_sub]; exact μ.expect_congr fun y => by ring
    rw [e1, e2]
    ring
  have hnb : nrm μ b ≤ 1 + υ := by
    have hip : ip μ b b = nrm μ (fun x => b x - 1) ^ 2 + 1 := by
      rw [← ip_self_eq]
      unfold ip
      rw [show (fun x => b x * b x) = fun x => (b x - 1) * (b x - 1) + (2 * b x - 1) from
        funext fun x => by ring, FiniteLaw.expect_add, FiniteLaw.expect_sub,
        FiniteLaw.expect_const_mul, FiniteLaw.expect_const, hb1]
      ring
    have hle : ip μ b b ≤ (1 + υ) ^ 2 := by
      rw [hip]
      nlinarith [FiniteLaw.mean_sq_le_second_moment μ b, FiveType.nrm_nonneg μ (fun x => b x - 1)]
    calc nrm μ b = Real.sqrt (ip μ b b) := rfl
      _ ≤ Real.sqrt ((1 + υ) ^ 2) := Real.sqrt_le_sqrt hle
      _ = 1 + υ := Real.sqrt_sq (by linarith)
  rw [hsplit]
  have b1 : |ip μ Φ (fun x => a x - 1)| ≤ nrm μ Φ * υ :=
    (abs_ip_le _ _ _).trans (mul_le_mul_of_nonneg_left ha (FiveType.nrm_nonneg _ _))
  have b2 : |ip μ b Ψ| ≤ (1 + υ) * nrm μ Ψ :=
    (abs_ip_le _ _ _).trans (mul_le_mul_of_nonneg_right hnb (FiveType.nrm_nonneg _ _))
  have b3 : |μ.expect Φ| ≤ nrm μ Φ := by
    have := abs_ip_le μ Φ (fun _ => 1)
    have hn : nrm μ (fun _ => (1 : ℝ)) = 1 := by
      unfold nrm ip; simp only [mul_one, FiniteLaw.expect_const, Real.sqrt_one]
    unfold ip at this
    simp only [mul_one] at this
    rwa [hn, mul_one] at this
  have b4 : |ip μ (fun x => b x - 1) Ψ| ≤ υ * nrm μ Ψ :=
    (abs_ip_le _ _ _).trans (mul_le_mul_of_nonneg_right hb (FiveType.nrm_nonneg _ _))
  have hnΦ := FiveType.nrm_nonneg μ Φ
  have hnΨ := FiveType.nrm_nonneg μ Ψ
  calc |ip μ Φ (fun x => a x - 1) * ip μ b Ψ + μ.expect Φ * ip μ (fun x => b x - 1) Ψ|
      ≤ |ip μ Φ (fun x => a x - 1)| * |ip μ b Ψ| +
          |μ.expect Φ| * |ip μ (fun x => b x - 1) Ψ| := by
        rw [← abs_mul, ← abs_mul]; exact abs_add_le _ _
    _ ≤ (nrm μ Φ * υ) * ((1 + υ) * nrm μ Ψ) + nrm μ Φ * (υ * nrm μ Ψ) := by
        gcongr
    _ = (2 * υ + υ ^ 2) * nrm μ Φ * nrm μ Ψ := by ring

end NormBlocks

/-! ## The block -/

section Block

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Xp : ι → Type*} [∀ i, Fintype (Xp i)]
  [∀ i, DecidableEq (Xp i)] (νp : ∀ i, FiniteLaw (Xp i)) (TFp : ∀ i, Xp i → Xp i → ℝ)

/-- The law of the inactive coordinates `p ∉ S`. -/
noncomputable def lawIn (S : Finset ι) : FiniteLaw ((i : {i // i ∉ S}) → Xp i.1) :=
  blockLaw (fun i : {i // i ∉ S} => νp i.1)

/-- The restriction to the inactive coordinates. -/
def restr (S : Finset ι) (x : (i : ι) → Xp i) : (i : {i // i ∉ S}) → Xp i.1 := fun i => x i.1

/-- `a = ⊗_{p∉S} u_{L,p}` on the inactive coordinates. -/
noncomputable def aIn (S : Finset ι) (z : (i : {i // i ∉ S}) → Xp i.1) : ℝ :=
  ∏ i, kone (νp i.1) (TFp i.1) (z i)

/-- `b = ⊗_{p∉S} u_{R,p}` on the inactive coordinates. -/
noncomputable def bIn (S : Finset ι) (w : (i : {i // i ∉ S}) → Xp i.1) : ℝ :=
  ∏ i, kone' (νp i.1) (TFp i.1) (w i)

/-- The sector term `C_S ⊗ (a ⊗ b - 𝟙 ⊗ 𝟙)` of `R_𝔅`. -/
noncomputable def termS (S : Finset ι) (x y : (i : ι) → Xp i) : ℝ :=
  (∏ i ∈ S, foldCov (νp i) (TFp i) (x i) (y i)) *
    ((∏ i ∈ Sᶜ, kone (νp i) (TFp i) (x i)) * (∏ i ∈ Sᶜ, kone' (νp i) (TFp i) (y i)) - 1)

omit [∀ i, DecidableEq (Xp i)] in
/-- **`R_𝔅` is the sum of the nonempty sector terms.** -/
theorem RB_eq_sum (x y : (i : ι) → Xp i) :
    RB νp TFp x y = ∑ S : Finset ι, (if S = ∅ then 0 else termS νp TFp S x y) := by
  have hall : ∑ S : Finset ι, termS νp TFp S x y =
      RB νp TFp x y + termS νp TFp ∅ x y := by
    have h1 : ∑ S : Finset ι, termS νp TFp S x y =
        prodKernel TFp x y - (CB νp TFp x y + 1) := by
      have hp : prodKernel TFp x y = ∑ S : Finset ι, (∏ i ∈ S, foldCov (νp i) (TFp i) (x i) (y i)) *
          ∏ i ∈ Sᶜ, (kone (νp i) (TFp i) (x i) * kone' (νp i) (TFp i) (y i)) := by
        have := Finset.prod_add (fun i => foldCov (νp i) (TFp i) (x i) (y i))
          (fun i => kone (νp i) (TFp i) (x i) * kone' (νp i) (TFp i) (y i)) Finset.univ
        rw [Finset.powerset_univ] at this
        simp only [prodKernel]
        rw [show (∏ i, TFp i (x i) (y i)) = ∏ i, (foldCov (νp i) (TFp i) (x i) (y i) +
            kone (νp i) (TFp i) (x i) * kone' (νp i) (TFp i) (y i)) from
          Finset.prod_congr rfl fun i _ => by simp only [foldCov]; ring, this]
        exact Finset.sum_congr rfl fun S _ => by rw [Finset.compl_eq_univ_sdiff]
      have hc : CB νp TFp x y + 1 =
          ∑ S : Finset ι, ∏ i ∈ S, foldCov (νp i) (TFp i) (x i) (y i) := by
        have := Finset.prod_add (fun i => foldCov (νp i) (TFp i) (x i) (y i)) (fun _ => (1 : ℝ))
          Finset.univ
        rw [Finset.powerset_univ] at this
        simp only [CB, sectorKernel, Finset.prod_const_one, mul_one] at this ⊢
        rw [sub_add_cancel, show (∏ i, (1 + foldCov (νp i) (TFp i) (x i) (y i))) =
          ∏ i, (foldCov (νp i) (TFp i) (x i) (y i) + 1) from
            Finset.prod_congr rfl fun i _ => by ring, this]
      rw [hp, hc, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun S _ => ?_
      simp only [termS, Finset.prod_mul_distrib]
      ring
    rw [h1]
    simp only [termS, RB, UL, UR, Finset.prod_empty, one_mul, Finset.compl_empty]
    ring
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ ∅)] at hall
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ ∅)]
  simp only [↓reduceIte, zero_add]
  have hrest : ∑ S ∈ Finset.univ.erase ∅, (if S = ∅ then 0 else termS νp TFp S x y) =
      ∑ S ∈ Finset.univ.erase ∅, termS νp TFp S x y :=
    Finset.sum_congr rfl fun S hS => by simp only [Finset.ne_of_mem_erase hS, ↓reduceIte]
  rw [hrest]
  linarith

omit [∀ i, DecidableEq (Xp i)] in
theorem nrm_sub_one_sq {Y : Type*} [Fintype Y] (μ : FiniteLaw Y) (f : Y → ℝ)
    (hf : μ.expect f = 1) : nrm μ (fun x => f x - 1) ^ 2 = μ.expect (fun x => f x ^ 2) - 1 := by
  rw [← ip_self_eq]
  unfold ip
  rw [show (fun x => (f x - 1) * (f x - 1)) = fun x => f x ^ 2 - 2 * f x + 1 from
    funext fun x => by ring, FiniteLaw.expect_add, FiniteLaw.expect_sub,
    FiniteLaw.expect_const_mul, FiniteLaw.expect_const, hf]
  ring

omit [∀ i, DecidableEq (Xp i)] in
/-- **Monotonicity on the inactive primes**: `‖⊗_{p∉S} u_p - 𝟙‖ ≤ ‖⊗_p u_p - 𝟙‖`, for marginal
densities `u_p` of mean one. -/
theorem nrm_inactive_le (S : Finset ι) (u : ∀ i, Xp i → ℝ) (hu : ∀ i, (νp i).expect (u i) = 1)
    {υ : ℝ} (h : nrm (blockLaw νp) (fun x => (∏ i, u i (x i)) - 1) ≤ υ) :
    nrm (lawIn νp S) (fun z => (∏ i : {i // i ∉ S}, u i.1 (z i)) - 1) ≤ υ := by
  have hυ : 0 ≤ υ := le_trans (FiveType.nrm_nonneg _ _) h
  have hsq : ∀ i, 1 ≤ (νp i).expect (fun t => u i t ^ 2) := fun i => by
    have := FiniteLaw.mean_sq_le_second_moment (νp i) (u i)
    rwa [hu i, one_pow] at this
  have hEin : (lawIn νp S).expect (fun z => ∏ i : {i // i ∉ S}, u i.1 (z i)) = 1 := by
    unfold lawIn
    rw [expect_blockLaw_prod (fun i : {i // i ∉ S} => νp i.1) (fun i => u i.1)]
    exact Finset.prod_eq_one fun i _ => hu i.1
  have hEall : (blockLaw νp).expect (fun x => ∏ i, u i (x i)) = 1 := by
    rw [expect_blockLaw_prod]
    exact Finset.prod_eq_one fun i _ => hu i
  have h2in : (lawIn νp S).expect (fun z => (∏ i : {i // i ∉ S}, u i.1 (z i)) ^ 2) =
      ∏ i ∈ Sᶜ, (νp i).expect (fun t => u i t ^ 2) := by
    unfold lawIn
    simp_rw [← Finset.prod_pow]
    rw [expect_blockLaw_prod (fun i : {i // i ∉ S} => νp i.1) (fun i t => u i.1 t ^ 2)]
    exact (Finset.prod_subtype Sᶜ (fun i => by simp)
      (fun i => (νp i).expect (fun t => u i t ^ 2))).symm
  have h2all : (blockLaw νp).expect (fun x => (∏ i, u i (x i)) ^ 2) =
      (∏ i ∈ S, (νp i).expect (fun t => u i t ^ 2)) *
        ∏ i ∈ Sᶜ, (νp i).expect (fun t => u i t ^ 2) := by
    simp_rw [← Finset.prod_pow]
    rw [expect_blockLaw_prod (fun i => νp i) (fun i t => u i t ^ 2), Finset.prod_mul_prod_compl]
  have hge1 : 1 ≤ ∏ i ∈ S, (νp i).expect (fun t => u i t ^ 2) := by
    have := Finset.prod_le_prod₀ (s := S) (f := fun _ => (1 : ℝ))
      (g := fun i => (νp i).expect (fun t => u i t ^ 2)) (fun _ _ => zero_le_one) (fun i _ => hsq i)
    simpa using this
  have hpos : 0 ≤ ∏ i ∈ Sᶜ, (νp i).expect (fun t => u i t ^ 2) :=
    Finset.prod_nonneg fun i _ => le_trans zero_le_one (hsq i)
  have hin := nrm_sub_one_sq (lawIn νp S) _ hEin
  have hall := nrm_sub_one_sq (blockLaw νp) _ hEall
  have hle : nrm (lawIn νp S) (fun z => (∏ i : {i // i ∉ S}, u i.1 (z i)) - 1) ^ 2 ≤ υ ^ 2 := by
    rw [hin, h2in]
    have : nrm (blockLaw νp) (fun x => (∏ i, u i (x i)) - 1) ^ 2 ≤ υ ^ 2 :=
      pow_le_pow_left₀ (FiveType.nrm_nonneg _ _) h 2
    rw [hall, h2all] at this
    nlinarith
  exact (pow_le_pow_iff_left₀ (FiveType.nrm_nonneg _ _) hυ (by norm_num)).mp hle

/-! ## The sector bound and `lem:joint-rows`(c) -/

omit [∀ i, DecidableEq (Xp i)] in
theorem lawIn_weight_restr (S : Finset ι) (x : (i : ι) → Xp i) :
    (lawIn νp S).weight (restr S x) = ∏ i ∈ Sᶜ, (νp i).weight (x i) :=
  (Finset.prod_subtype Sᶜ (fun i => by simp) (fun i => (νp i).weight (x i))).symm

theorem wI_lawIn_restr (S : Finset ι) (x y : (i : ι) → Xp i) :
    wI (lawIn νp S) (restr S x) (restr S y) = ∏ i ∈ Sᶜ, wI (νp i) (x i) (y i) := by
  unfold lawIn
  rw [← tprod_wI (fun i : {i // i ∉ S} => νp i.1)]
  exact (Finset.prod_subtype Sᶜ (fun i => by simp) (fun i => wI (νp i) (x i) (y i))).symm

omit [∀ i, DecidableEq (Xp i)] in
theorem aIn_restr (S : Finset ι) (x : (i : ι) → Xp i) :
    aIn νp TFp S (restr S x) = ∏ i ∈ Sᶜ, kone (νp i) (TFp i) (x i) :=
  (Finset.prod_subtype Sᶜ (fun i => by simp) (fun i => kone (νp i) (TFp i) (x i))).symm

omit [∀ i, DecidableEq (Xp i)] in
theorem bIn_restr (S : Finset ι) (x : (i : ι) → Xp i) :
    bIn νp TFp S (restr S x) = ∏ i ∈ Sᶜ, kone' (νp i) (TFp i) (x i) :=
  (Finset.prod_subtype Sᶜ (fun i => by simp) (fun i => kone' (νp i) (TFp i) (x i))).symm

theorem wI_block_split (S : Finset ι) (x y : (i : ι) → Xp i) :
    wI (blockLaw νp) x y = (∏ i ∈ S, wI (νp i) (x i) (y i)) * ∏ i ∈ Sᶜ, wI (νp i) (x i) (y i) := by
  rw [← tprod_wI, Finset.prod_mul_prod_compl]
  rfl

omit [∀ i, DecidableEq (Xp i)] in
theorem blockLaw_weight_split (S : Finset ι) (x : (i : ι) → Xp i) :
    (blockLaw νp).weight x = (∏ i ∈ S, (νp i).weight (x i)) * ∏ i ∈ Sᶜ, (νp i).weight (x i) := by
  rw [Finset.prod_mul_prod_compl]
  rfl

/-- **The sector term of `R_𝔅`**: `‖C_S ⊗ (a ⊗ b - 𝟙 ⊗ 𝟙)‖ ≤ ∏_{p∈S} n_p (2υ + υ²)`. -/
theorem formBound_term (hTF : ∀ i, kf (νp i) (TFp i) (fun _ => 1) (fun _ => 1) = 1) {υ : ℝ}
    {n : ι → ℝ} (hUL : nrm (blockLaw νp) (fun x => UL νp TFp x - 1) ≤ υ)
    (hUR : nrm (blockLaw νp) (fun x => UR νp TFp x - 1) ≤ υ)
    (hn : ∀ i, FormBound (νp i) (foldCov (νp i) (TFp i)) (n i)) (S : Finset ι) :
    FormBound (blockLaw νp) (termS νp TFp S) ((∏ i ∈ S, n i) * (2 * υ + υ ^ 2)) := by
  have hυ : 0 ≤ υ := le_trans (FiveType.nrm_nonneg _ _) hUL
  have he2 : 0 ≤ 2 * υ + υ ^ 2 := by positivity
  have hn0 : ∀ i, 0 ≤ n i := fun i => formBound_nonneg (hn i)
  -- the inactive primes
  have haIn : nrm (lawIn νp S) (fun z => aIn νp TFp S z - 1) ≤ υ :=
    nrm_inactive_le νp S (fun i => kone (νp i) (TFp i)) (fun i => by rw [expect_kone, hTF i]) hUL
  have hbIn : nrm (lawIn νp S) (fun z => bIn νp TFp S z - 1) ≤ υ :=
    nrm_inactive_le νp S (fun i => kone' (νp i) (TFp i)) (fun i => by rw [expect_kone', hTF i]) hUR
  have hbE : (lawIn νp S).expect (bIn νp TFp S) = 1 := by
    unfold lawIn bIn
    rw [expect_blockLaw_prod (fun i : {i // i ∉ S} => νp i.1) (fun i => kone' (νp i.1) (TFp i.1))]
    exact Finset.prod_eq_one fun i _ => by rw [expect_kone', hTF i.1]
  have hD := formBound_rank (μ := lawIn νp S) (a := aIn νp TFp S) (b := bIn νp TFp S) hbE haIn hbIn
  set M2 := (fromBlocks ((2 * υ + υ ^ 2) • wI (lawIn νp S))
    (wk (lawIn νp S) (fun z w => aIn νp TFp S z * bIn νp TFp S w - 1))
    (wk (lawIn νp S) (fun z w => aIn νp TFp S z * bIn νp TFp S w - 1))ᵀ
    ((2 * υ + υ ^ 2) • wI (lawIn νp S))).submatrix (Sum.map (restr S) (restr S))
      (Sum.map (restr S) (restr S)) with hM2
  have hF2 : M2.PosSemidef := (psd_of_formBound hD).submatrix _
  -- the active primes
  let L := chooseM S (fun i => n i • wI (νp i))
    (fun i => (Matrix.of fun _ _ => (1 : ℝ) : Matrix (Xp i) (Xp i) ℝ))
  let B := chooseM S (fun i => wk (νp i) (foldCov (νp i) (TFp i)))
    (fun i => (Matrix.of fun _ _ => (1 : ℝ) : Matrix (Xp i) (Xp i) ℝ))
  set M1 := fromBlocks (tprod L) (tprod B) (tprod B)ᵀ (tprod L) with hM1
  have hF1 : M1.PosSemidef := psd_tprod_blocks L B L fun i => by
    by_cases hi : i ∈ S
    · simp only [L, B, chooseM, hi, ↓reduceIte]; exact psd_of_formBound (hn i)
    · simp only [L, B, chooseM, hi, ↓reduceIte]; exact psd_blockOnes
  -- the Hadamard product
  have hH := matrix_prod_posSemidef (fun j : Bool => if j then M1 else M2)
    (fun j => by cases j <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> assumption)
  have hL : ∀ x y : (i : ι) → Xp i,
      tprod L x y = (∏ i ∈ S, n i) * ∏ i ∈ S, wI (νp i) (x i) (y i) := by
    intro x y
    simp only [L]
    rw [tprod_chooseM_apply, prod_choose]
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.of_apply, Finset.prod_const_one, mul_one,
      Finset.prod_mul_distrib]
  have hB : ∀ x y : (i : ι) → Xp i, tprod B x y =
      (∏ i ∈ S, (νp i).weight (x i)) * (∏ i ∈ S, (νp i).weight (y i)) *
        ∏ i ∈ S, foldCov (νp i) (TFp i) (x i) (y i) := by
    intro x y
    simp only [B]
    rw [tprod_chooseM_apply, prod_choose]
    simp only [wk, Matrix.of_apply, Finset.prod_const_one, mul_one, Finset.prod_mul_distrib]
  have hid : (fun a b => ∏ j : Bool, (if j then M1 else M2) a b) =
      fromBlocks (((∏ i ∈ S, n i) * (2 * υ + υ ^ 2)) • wI (blockLaw νp))
        (wk (blockLaw νp) (termS νp TFp S)) (wk (blockLaw νp) (termS νp TFp S))ᵀ
        (((∏ i ∈ S, n i) * (2 * υ + υ ^ 2)) • wI (blockLaw νp)) := by
    ext (x | x) (y | y) <;>
      simp only [Fintype.prod_bool, ↓reduceIte, Bool.false_eq_true, hM1, hM2, submatrix_apply,
        Sum.map_inl, Sum.map_inr, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
        fromBlocks_apply₂₂, transpose_apply, Matrix.smul_apply, smul_eq_mul]
    · rw [hL, wI_lawIn_restr, wI_block_split νp S]; ring
    · rw [hB, wk, wk, lawIn_weight_restr, lawIn_weight_restr, aIn_restr, bIn_restr,
        blockLaw_weight_split νp S x, blockLaw_weight_split νp S y]
      simp only [termS]
      ring
    · rw [hB, wk, wk, lawIn_weight_restr, lawIn_weight_restr, aIn_restr, bIn_restr,
        blockLaw_weight_split νp S x, blockLaw_weight_split νp S y]
      simp only [termS]
      ring
    · rw [hL, wI_lawIn_restr, wI_block_split νp S]; ring
  rw [hid] at hH
  exact formBound_of_psd (mul_nonneg (Finset.prod_nonneg fun i _ => hn0 i) he2) hH

/-- **`lem:joint-rows`(c)**: `‖T_{F,𝔅} - U_L ⊗ U_R - C_𝔅‖ ≤ (2υ + υ²)(∏_p (1 + n_p) - 1)` for
kernels of mass one with `‖U_L - 𝟙‖, ‖U_R - 𝟙‖ ≤ υ` and `‖C_{F,p}‖ ≤ n_p`. -/
theorem jointRows_c (hTF : ∀ i, kf (νp i) (TFp i) (fun _ => 1) (fun _ => 1) = 1) {υ : ℝ}
    {n : ι → ℝ} (hUL : nrm (blockLaw νp) (fun x => UL νp TFp x - 1) ≤ υ)
    (hUR : nrm (blockLaw νp) (fun x => UR νp TFp x - 1) ≤ υ)
    (hn : ∀ i, FormBound (νp i) (foldCov (νp i) (TFp i)) (n i)) :
    FormBound (blockLaw νp) (RB νp TFp) ((2 * υ + υ ^ 2) * (∏ i, (1 + n i) - 1)) := by
  have hRB : RB νp TFp = fun x y => ∑ S : Finset ι, (if S = ∅ then 0 else termS νp TFp S x y) :=
    funext fun x => funext fun y => RB_eq_sum νp TFp x y
  have hsum := formBound_sum Finset.univ (μ := blockLaw νp)
    (K := fun S x y => if S = ∅ then 0 else termS νp TFp S x y)
    (e := fun S => if S = ∅ then 0 else (∏ i ∈ S, n i) * (2 * υ + υ ^ 2)) fun S _ => by
      by_cases hS : S = ∅
      · intro Φ Ψ
        simp only [hS, ↓reduceIte, zero_mul]
        simp [kf]
      · simp only [hS, ↓reduceIte]
        exact formBound_term νp TFp hTF hUL hUR hn S
  have he : ∑ S : Finset ι, (if S = ∅ then 0 else (∏ i ∈ S, n i) * (2 * υ + υ ^ 2)) =
      (2 * υ + υ ^ 2) * (∏ i, (1 + n i) - 1) := by
    have hp : ∏ i, (1 + n i) = ∑ S : Finset ι, ∏ i ∈ S, n i := by
      have := Finset.prod_add n (fun _ => (1 : ℝ)) Finset.univ
      rw [Finset.powerset_univ] at this
      simp only [Finset.prod_const_one, mul_one] at this
      rw [← this]
      exact Finset.prod_congr rfl fun i _ => by ring
    have hA : ∀ f : Finset ι → ℝ, ∑ S : Finset ι, (if S = ∅ then 0 else f S) =
        ∑ S : Finset ι, f S - f ∅ := by
      intro f
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ ∅),
        ← Finset.add_sum_erase _ f (Finset.mem_univ ∅)]
      simp only [↓reduceIte, zero_add, add_sub_cancel_left]
      exact Finset.sum_congr rfl fun S hS => by simp only [Finset.ne_of_mem_erase hS, ↓reduceIte]
    rw [hA (fun S => (∏ i ∈ S, n i) * (2 * υ + υ ^ 2)), ← Finset.sum_mul, ← hp]
    simp only [Finset.prod_empty]
    ring
  rw [hRB, ← he]
  exact hsum

/-- **`lem:joint-rows`(c) discharges `Blocks.JointRowsC`.** -/
theorem jointRowsC_holds : JointRowsC νp TFp :=
  fun _υ _n hTF hUL hUR hn => jointRows_c νp TFp hTF hUL hUR hn

end Block

end Sarkozy.JointRows
