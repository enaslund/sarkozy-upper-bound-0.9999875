module

public import Sarkozy.JointRows.Weighted

/-!
# The joint block of a prime block (`lem:joint-rows`(b))

Source: `paper/sections/16_extraction.tex`, `lem:joint-rows`(b) and its proof.

Let `𝔅` be a finite set of primes (a finite index type `ι`), and for `p ∈ 𝔅` let `C_{F,p}` and
`C_{E,p} = C_{E,p}^*` annihilate the constants on both sides of `L²(ν_p)`. Put
`C_𝔅 = ⊗_p (J_p + C_{F,p}) - J_𝔅` and `E_𝔅 = ⊗_p (J_p + C_{E,p}) - J_𝔅` (the kernels
`∏_p (1 + C_p) - 1`, `Blocks.sectorKernel`). If `‖C_{F,p}‖ ≤ c < 1`, `‖C_{E,p}‖ ≤ h < 1` and the
joint block at each prime is `⪰ -𝔨'_p I`, then the joint block of `(E_𝔅, C_𝔅)` is `⪰ -K I` for
every `K ≥ max(c² + h², max_p 𝔨'_p)` (`jointRows_b`). This is exactly `Blocks.JointRowsB`
(`jointRowsB_holds`).

**Proof (the paper's sector argument, in matrix form).** With the weighted matrices of
`Weighted.lean`, the identity is `I = ⊗_p (Q_p + J_p) = ∑_S P_S`, `P_S = ⊗_{p∈S} Q_p ⊗_{p∉S} J_p`
(the projection on the sector of `S`), and `E_𝔅 = ∑_{S≠∅} ⊗_{p∈S} C_{E,p} ⊗_{p∉S} J_p`, likewise
`C_𝔅`. So the matrix `(E_𝔅 + K I  C_𝔅; C_𝔅ᵀ  E_𝔅 + K I)` is the sum over the sectors `S` of
* `S = ∅`: `K (J_𝔅 ⊕ J_𝔅) ⪰ 0`;
* `S = {p}`: the joint block at `p` (plus `K Q_p`) tensored with `(J J; J J)` at the other primes;
* `|S| ≥ 2`: `(⊗C_E + h^{|S|}P_S) ⊕ (same)`, plus `(c^{|S|}P_S  ⊗C_F; ⊗C_Fᵀ  c^{|S|}P_S)`, plus
  `(K - h^{|S|} - c^{|S|})(P_S ⊕ P_S)`; the first two are tensor products of the per-prime blocks
  `(hQ C_E; C_E hQ)`, `(cQ C_F; C_Fᵀ cQ)` (`‖C‖ ≤ c`), and `h^{|S|} + c^{|S|} ≤ h² + c² ≤ K`.

Each summand is positive semidefinite by block tensorization (`psd_tprod_blocks`).
-/

@[expose] public section

open scoped BigOperators
open Matrix

namespace Sarkozy.JointRows

open Sarkozy.FiveType Sarkozy.FiveType.Blocks

/-! ## Choices over the primes -/

section Choose

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem prod_choose (t : Finset ι) (f g : ι → ℝ) :
    ∏ i, (if i ∈ t then f i else g i) = (∏ i ∈ t, f i) * ∏ i ∈ tᶜ, g i := by
  rw [← Finset.prod_mul_prod_compl t]
  congr 1
  · exact Finset.prod_congr rfl fun i hi => by simp only [hi, ↓reduceIte]
  · exact Finset.prod_congr rfl fun i hi => by
      simp only [Finset.mem_compl.mp hi, ↓reduceIte]

/-- `∑_t ∏_i (t ∋ i ? f_i : g_i) = ∏_i (f_i + g_i)`. -/
theorem sum_choose (f g : ι → ℝ) :
    ∑ t : Finset ι, ∏ i, (if i ∈ t then f i else g i) = ∏ i, (f i + g i) := by
  rw [Finset.prod_add, Finset.powerset_univ]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [prod_choose, Finset.compl_eq_univ_sdiff]

theorem prod_choose_single_add (p : ι) (f g e : ι → ℝ) (K : ℝ) :
    ∏ i, (if i ∈ ({p} : Finset ι) then f i + K * g i else e i) =
      ∏ i, (if i ∈ ({p} : Finset ι) then f i else e i) +
        K * ∏ i, (if i ∈ ({p} : Finset ι) then g i else e i) := by
  rw [prod_choose, prod_choose, prod_choose]
  simp only [Finset.prod_singleton]
  ring

theorem prod_choose_smul (t : Finset ι) (a : ℝ) (f g : ι → ℝ) :
    ∏ i, (if i ∈ t then a * f i else g i) = a ^ t.card * ∏ i, (if i ∈ t then f i else g i) := by
  rw [prod_choose, prod_choose, Finset.prod_mul_distrib, Finset.prod_const]
  ring

end Choose

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Xp : ι → Type*} [∀ i, Fintype (Xp i)]
  [∀ i, DecidableEq (Xp i)]

/-- The matrix family chosen by `S`: `a_i` for `i ∈ S`, `b_i` otherwise. -/
def chooseM (S : Finset ι) (a b : ∀ i, Matrix (Xp i) (Xp i) ℝ) : ∀ i, Matrix (Xp i) (Xp i) ℝ :=
  fun i => if i ∈ S then a i else b i

omit [∀ i, Fintype (Xp i)] [∀ i, DecidableEq (Xp i)] in
theorem tprod_chooseM_apply (S : Finset ι) (a b : ∀ i, Matrix (Xp i) (Xp i) ℝ)
    (x y : (i : ι) → Xp i) :
    tprod (chooseM S a b) x y = ∏ i, (if i ∈ S then a i (x i) (y i) else b i (x i) (y i)) := by
  simp only [tprod, chooseM]
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases hi : i ∈ S <;> simp only [hi, ↓reduceIte]

omit [∀ i, Fintype (Xp i)] [∀ i, DecidableEq (Xp i)] in
theorem tprod_chooseM_smul (S : Finset ι) (a : ℝ) (f g : ∀ i, Matrix (Xp i) (Xp i) ℝ) :
    tprod (chooseM S (fun i => a • f i) g) = a ^ S.card • tprod (chooseM S f g) := by
  ext x y
  rw [tprod_chooseM_apply, Matrix.smul_apply, tprod_chooseM_apply, smul_eq_mul,
    ← prod_choose_smul]
  rfl

omit [DecidableEq ι] [∀ i, Fintype (Xp i)] [∀ i, DecidableEq (Xp i)] in
theorem tprod_transpose (M : ∀ i, Matrix (Xp i) (Xp i) ℝ) :
    (tprod M)ᵀ = tprod (fun i => (M i)ᵀ) := by
  ext x y
  rfl

omit [DecidableEq ι] [∀ i, Fintype (Xp i)] [∀ i, DecidableEq (Xp i)] in
theorem tprod_symm {M : ∀ i, Matrix (Xp i) (Xp i) ℝ} (h : ∀ i, (M i)ᵀ = M i) :
    (tprod M)ᵀ = tprod M := by
  rw [tprod_transpose]
  congr 1
  funext i
  exact h i

variable (νp : ∀ i, FiniteLaw (Xp i))

/-- The sector projection `P_S = ⊗_{p∈S} Q_p ⊗_{p∉S} J_p`. -/
noncomputable def PS (S : Finset ι) : Matrix ((i : ι) → Xp i) ((i : ι) → Xp i) ℝ :=
  tprod (chooseM S (fun i => wQ (νp i)) (fun i => wJ (νp i)))

/-- The sector term `⊗_{p∈S} C_p ⊗_{p∉S} J_p` of a sector kernel. -/
noncomputable def TS (C : ∀ i, Xp i → Xp i → ℝ) (S : Finset ι) :
    Matrix ((i : ι) → Xp i) ((i : ι) → Xp i) ℝ :=
  tprod (chooseM S (fun i => wk (νp i) (C i)) (fun i => wJ (νp i)))

theorem sum_PS : ∑ S : Finset ι, PS νp S = wI (blockLaw νp) := by
  ext x y
  rw [Matrix.sum_apply]
  simp only [PS, tprod_chooseM_apply]
  rw [sum_choose, ← tprod_wI]
  refine Finset.prod_congr rfl fun i _ => ?_
  simp only [wQ, wJ, Matrix.sub_apply]
  ring

omit [∀ i, DecidableEq (Xp i)] in
theorem sum_TS (C : ∀ i, Xp i → Xp i → ℝ) :
    ∑ S : Finset ι, TS νp C S = wk (blockLaw νp) (sectorKernel C) + wJ (blockLaw νp) := by
  ext x y
  rw [Matrix.sum_apply]
  simp only [TS, tprod_chooseM_apply]
  rw [sum_choose]
  simp only [wk, wJ, Matrix.add_apply, sectorKernel, blockLaw]
  rw [mul_sub, mul_one, sub_add_cancel, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  ring

omit [∀ i, DecidableEq (Xp i)] in
theorem TS_empty (C : ∀ i, Xp i → Xp i → ℝ) : TS νp C ∅ = wJ (blockLaw νp) := by
  ext x y
  simp only [TS, tprod_chooseM_apply, Finset.notMem_empty, ↓reduceIte, wJ, wk, blockLaw,
    mul_one, Finset.prod_mul_distrib]

omit [∀ i, DecidableEq (Xp i)] in
/-- The sector kernel is the sum of the nonempty sector terms. -/
theorem wk_sectorKernel_eq (C : ∀ i, Xp i → Xp i → ℝ) :
    wk (blockLaw νp) (sectorKernel C) = ∑ S : Finset ι, (if S = ∅ then 0 else TS νp C S) := by
  have h := sum_TS νp C
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ ∅), TS_empty] at h
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ ∅)]
  simp only [↓reduceIte, zero_add]
  have hrest : ∑ S ∈ Finset.univ.erase ∅, (if S = ∅ then 0 else TS νp C S) =
      ∑ S ∈ Finset.univ.erase ∅, TS νp C S :=
    Finset.sum_congr rfl fun S hS => by simp only [Finset.ne_of_mem_erase hS, ↓reduceIte]
  rw [hrest]
  have h2 := congrArg (· - wJ (blockLaw νp)) h
  simp only [add_sub_cancel_left, add_sub_cancel_right] at h2
  exact h2.symm

theorem psd_PS (S : Finset ι) : (PS νp S).PosSemidef := by
  refine psd_tprod _ fun i => ?_
  by_cases hi : i ∈ S
  · simp only [chooseM, hi, ↓reduceIte]; exact psd_wQ _
  · simp only [chooseM, hi, ↓reduceIte]; exact psd_wJ _

theorem PS_symm (S : Finset ι) : (PS νp S)ᵀ = PS νp S := by
  refine tprod_symm fun i => ?_
  by_cases hi : i ∈ S
  · simp only [chooseM, hi, ↓reduceIte]; exact wQ_transpose _
  · simp only [chooseM, hi, ↓reduceIte]; exact wk_symm fun _ _ => rfl

omit [∀ i, DecidableEq (Xp i)] in
theorem TS_symm {C : ∀ i, Xp i → Xp i → ℝ} (hsym : ∀ i x y, C i x y = C i y x) (S : Finset ι) :
    (TS νp C S)ᵀ = TS νp C S := by
  refine tprod_symm fun i => ?_
  by_cases hi : i ∈ S
  · simp only [chooseM, hi, ↓reduceIte]; exact wk_symm (hsym i)
  · simp only [chooseM, hi, ↓reduceIte]; exact wk_symm fun _ _ => rfl

/-- The quadratic form of the target matrix. -/
theorem dot_target (E C : ((i : ι) → Xp i) → ((i : ι) → Xp i) → ℝ) (K : ℝ)
    (Φ Ψ : ((i : ι) → Xp i) → ℝ) :
    Sum.elim Φ Ψ ⬝ᵥ (fromBlocks (wk (blockLaw νp) E + K • wI (blockLaw νp)) (wk (blockLaw νp) C)
      (wk (blockLaw νp) C)ᵀ (wk (blockLaw νp) E + K • wI (blockLaw νp)) *ᵥ Sum.elim Φ Ψ) =
      kf (blockLaw νp) E Φ Φ + 2 * kf (blockLaw νp) C Φ Ψ + kf (blockLaw νp) E Ψ Ψ +
        K * (nrm (blockLaw νp) Φ ^ 2 + nrm (blockLaw νp) Ψ ^ 2) := by
  rw [dot_fromBlocks]
  simp only [add_mulVec, dotProduct_add, smul_mulVec, dotProduct_smul, smul_eq_mul]
  rw [dot_wk, dot_wk, dot_wk, dot_wI, dot_wI, dotProduct_mulVec, vecMul_transpose,
    dotProduct_comm, dot_wk, ip_self_eq, ip_self_eq]
  ring

/-- **`lem:joint-rows`(b).** -/
theorem jointRows_b (CE CF : ∀ i, Xp i → Xp i → ℝ) {c h K : ℝ} {k' : ι → ℝ}
    (hCF : ∀ i, Annihilates (νp i) (CF i)) (hCE : ∀ i, Annihilates (νp i) (CE i))
    (hsym : ∀ i x y, CE i x y = CE i y x)
    (hbF : ∀ i, FormBound (νp i) (CF i) c) (hc1 : c < 1)
    (hbE : ∀ i, FormBound (νp i) (CE i) h) (hh1 : h < 1)
    (hJ : ∀ i, JointBlockLower (νp i) (CE i) (CF i) (k' i))
    (hK : c ^ 2 + h ^ 2 ≤ K) (hk' : ∀ i, k' i ≤ K) :
    JointBlockLower (blockLaw νp) (sectorKernel CE) (sectorKernel CF) K := by
  have hK0 : 0 ≤ K := le_trans (by positivity) hK
  -- the sector summands
  let D' : Finset ι → Matrix ((i : ι) → Xp i) ((i : ι) → Xp i) ℝ :=
    fun S => if S = ∅ then 0 else TS νp CE S
  let O' : Finset ι → Matrix ((i : ι) → Xp i) ((i : ι) → Xp i) ℝ :=
    fun S => if S = ∅ then 0 else TS νp CF S
  let M : Finset ι → Matrix (((i : ι) → Xp i) ⊕ ((i : ι) → Xp i))
      (((i : ι) → Xp i) ⊕ ((i : ι) → Xp i)) ℝ :=
    fun S => fromBlocks (D' S + K • PS νp S) (O' S) (O' S)ᵀ (D' S + K • PS νp S)
  have hMpsd : ∀ S, (M S).PosSemidef := by
    intro S
    rcases Nat.lt_or_ge S.card 2 with hlt | hge
    · rcases Nat.lt_or_ge S.card 1 with h0 | h1
      · -- the empty sector
        have hS : S = ∅ := Finset.card_eq_zero.mp (by omega)
        subst hS
        have hP : (K • PS νp ∅).PosSemidef := (psd_PS νp ∅).smul hK0
        simp only [M, D', O', ↓reduceIte, zero_add, transpose_zero]
        exact Extraction.posSemidef_fromBlocks_diag hP
      · -- a singleton sector
        obtain ⟨p, hp⟩ := Finset.card_eq_one.mp (by omega : S.card = 1)
        subst hp
        have hne : ({p} : Finset ι) ≠ ∅ := Finset.singleton_ne_empty p
        let L := chooseM {p} (fun i => wk (νp i) (CE i) + K • wQ (νp i)) (fun i => wJ (νp i))
        let B := chooseM {p} (fun i => wk (νp i) (CF i)) (fun i => wJ (νp i))
        have hL : TS νp CE {p} + K • PS νp {p} = tprod L := by
          ext x y
          rw [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
          simp only [TS, PS, L]
          rw [tprod_chooseM_apply, tprod_chooseM_apply, tprod_chooseM_apply]
          simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
          rw [prod_choose_single_add p (fun i => wk (νp i) (CE i) (x i) (y i))
            (fun i => wQ (νp i) (x i) (y i)) (fun i => wJ (νp i) (x i) (y i)) K]
        have hMS : M {p} = fromBlocks (tprod L) (tprod B) (tprod B)ᵀ (tprod L) := by
          simp only [M, D', O', hne, ↓reduceIte, hL]
          rfl
        rw [hMS]
        refine psd_tprod_blocks L B L fun i => ?_
        by_cases hi : i ∈ ({p} : Finset ι)
        · simp only [L, B, chooseM, hi, ↓reduceIte]
          exact psd_blockJoint (hCE i) (hCF i) (hsym i) (hJ i) (hk' i)
        · simp only [L, B, chooseM, hi, ↓reduceIte]
          exact psd_blockJ _
    · -- a sector with at least two primes
      have hne : S ≠ ∅ := by
        intro h0; rw [h0, Finset.card_empty] at hge; omega
      obtain ⟨q, hq⟩ := Finset.nonempty_iff_ne_empty.mpr hne
      have hc0 : 0 ≤ c := formBound_nonneg (hbF q)
      have hh0 : 0 ≤ h := formBound_nonneg (hbE q)
      set n := S.card
      have hhn : h ^ n ≤ h ^ 2 := pow_le_pow_of_le_one hh0 hh1.le hge
      have hcn : c ^ n ≤ c ^ 2 := pow_le_pow_of_le_one hc0 hc1.le hge
      -- the two tensorized blocks
      have hE : (fromBlocks (h ^ n • PS νp S) (TS νp CE S) (TS νp CE S)ᵀ
          (h ^ n • PS νp S)).PosSemidef := by
        have := psd_tprod_blocks (chooseM S (fun i => h • wQ (νp i)) (fun i => wJ (νp i)))
          (chooseM S (fun i => wk (νp i) (CE i)) (fun i => wJ (νp i)))
          (chooseM S (fun i => h • wQ (νp i)) (fun i => wJ (νp i))) fun i => by
            by_cases hi : i ∈ S
            · simp only [chooseM, hi, ↓reduceIte]; exact psd_blockNorm (hCE i) (hbE i)
            · simp only [chooseM, hi, ↓reduceIte]; exact psd_blockJ _
        rwa [tprod_chooseM_smul] at this
      have hF : (fromBlocks (c ^ n • PS νp S) (TS νp CF S) (TS νp CF S)ᵀ
          (c ^ n • PS νp S)).PosSemidef := by
        have := psd_tprod_blocks (chooseM S (fun i => c • wQ (νp i)) (fun i => wJ (νp i)))
          (chooseM S (fun i => wk (νp i) (CF i)) (fun i => wJ (νp i)))
          (chooseM S (fun i => c • wQ (νp i)) (fun i => wJ (νp i))) fun i => by
            by_cases hi : i ∈ S
            · simp only [chooseM, hi, ↓reduceIte]; exact psd_blockNorm (hCF i) (hbF i)
            · simp only [chooseM, hi, ↓reduceIte]; exact psd_blockJ _
        rwa [tprod_chooseM_smul] at this
      -- `⊗C_E + h^n P_S ⪰ 0`
      have hG : (TS νp CE S + h ^ n • PS νp S).PosSemidef := by
        refine PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun v => ?_
        · change (TS νp CE S + h ^ n • PS νp S)ᵀ = _
          rw [transpose_add, TS_symm νp hsym, transpose_smul, PS_symm]
        · simp only [star_trivial]
          have h1 := hE.dotProduct_mulVec_nonneg (Sum.elim v v)
          simp only [star_trivial] at h1
          rw [dot_fromBlocks, TS_symm νp hsym] at h1
          rw [add_mulVec, dotProduct_add]
          linarith
      have hA1 := Extraction.posSemidef_fromBlocks_diag hG
      have hA3 : ((K - h ^ n - c ^ n) • fromBlocks (PS νp S) 0 0 (PS νp S)).PosSemidef :=
        (Extraction.posSemidef_fromBlocks_diag (psd_PS νp S)).smul (by linarith)
      have hsum := (hA1.add hF).add hA3
      have hMS : M S = fromBlocks (TS νp CE S + h ^ n • PS νp S) 0 0
          (TS νp CE S + h ^ n • PS νp S) +
          fromBlocks (c ^ n • PS νp S) (TS νp CF S) (TS νp CF S)ᵀ (c ^ n • PS νp S) +
          (K - h ^ n - c ^ n) • fromBlocks (PS νp S) 0 0 (PS νp S) := by
        simp only [M, D', O', hne, ↓reduceIte]
        rw [fromBlocks_smul, fromBlocks_add, fromBlocks_add]
        congr 1 <;> (try simp only [smul_zero, zero_add, add_zero]) <;> module
      rw [hMS]
      exact hsum
  -- the sum over the sectors
  have hsumM : ∑ S : Finset ι, M S = fromBlocks
      (wk (blockLaw νp) (sectorKernel CE) + K • wI (blockLaw νp))
      (wk (blockLaw νp) (sectorKernel CF))
      (wk (blockLaw νp) (sectorKernel CF))ᵀ
      (wk (blockLaw νp) (sectorKernel CE) + K • wI (blockLaw νp)) := by
    rw [wk_sectorKernel_eq νp CE, wk_sectorKernel_eq νp CF, ← sum_PS νp, Finset.smul_sum,
      ← Finset.sum_add_distrib]
    ext (x | x) (y | y) <;>
      simp only [Matrix.sum_apply, fromBlocks_apply₁₁, fromBlocks_apply₁₂, fromBlocks_apply₂₁,
        fromBlocks_apply₂₂, transpose_apply, M] <;> rfl
  have hT : (fromBlocks
      (wk (blockLaw νp) (sectorKernel CE) + K • wI (blockLaw νp))
      (wk (blockLaw νp) (sectorKernel CF))
      (wk (blockLaw νp) (sectorKernel CF))ᵀ
      (wk (blockLaw νp) (sectorKernel CE) + K • wI (blockLaw νp))).PosSemidef := by
    rw [← hsumM]
    exact Finset.sum_induction _ PosSemidef (fun _ _ ha hb => ha.add hb) PosSemidef.zero
      fun S _ => hMpsd S
  intro Φ Ψ
  have h1 := hT.dotProduct_mulVec_nonneg (Sum.elim Φ Ψ)
  simp only [star_trivial] at h1
  rw [dot_target] at h1
  linarith

/-- **`lem:joint-rows`(b) discharges `Blocks.JointRowsB`.** -/
theorem jointRowsB_holds (CE CF : ∀ i, Xp i → Xp i → ℝ) : JointRowsB νp CE CF :=
  fun _c _h _K _k' hCF hCE hsym hbF hc1 hbE hh1 hJ hK hk' =>
    jointRows_b νp CE CF hCF hCE hsym hbF hc1 hbE hh1 hJ hK hk'

end Sarkozy.JointRows
