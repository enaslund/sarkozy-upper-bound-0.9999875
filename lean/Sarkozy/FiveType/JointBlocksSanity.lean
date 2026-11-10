module

public import Sarkozy.FiveType.JointBlocks

/-!
# A toy block for `cor:joint-completion-blocks` (non-vacuity)

One prime, two labels with the uniform law, and the independent kernels `T_{E,p} = T_{F,p} = 1`
(the product coupling). Then `C_{F,p} = C_{E,p} = 0`, `U_L = U_R = 𝟙`, `C_𝔅 = E_𝔅 = R_𝔅 = 0`.
Every hypothesis of `joint_completion_blocks` is proved here, including the two cited
statements `JointRowsB` and `JointRowsC` (`lem:joint-rows` (b), (c)) for this block, with
`r = r_p = 1/2`, `c_F = c_E = k_J = 1`, `h = υ = 0` and `H = m_b = 1`. So the hypotheses are
jointly satisfiable, and `toy_jointData` is a `JointData` produced by the corollary.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.FiveType.JointBlocksSanity

open Sarkozy.FiveType Sarkozy.FiveType.Blocks

variable {𝔛 : Type*} [Fintype 𝔛]

theorem kf_zero (μ : FiniteLaw 𝔛) {A : 𝔛 → 𝔛 → ℝ} (hA : ∀ x y, A x y = 0) (Φ Ψ : 𝔛 → ℝ) :
    kf μ A Φ Ψ = 0 := by
  simp [kf, hA]

theorem formBound_zero (μ : FiniteLaw 𝔛) {A : 𝔛 → 𝔛 → ℝ} (hA : ∀ x y, A x y = 0) {e : ℝ}
    (he : 0 ≤ e) : FormBound μ A e := by
  intro Φ Ψ
  rw [kf_zero μ hA, abs_zero]
  exact mul_nonneg (mul_nonneg he (nrm_nonneg μ Φ)) (nrm_nonneg μ Ψ)

theorem jointBlockLower_zero (μ : FiniteLaw 𝔛) {E C : 𝔛 → 𝔛 → ℝ} (hE : ∀ x y, E x y = 0)
    (hC : ∀ x y, C x y = 0) {k : ℝ} (hk : 0 ≤ k) : JointBlockLower μ E C k := by
  intro Φ Ψ
  rw [kf_zero μ hE, kf_zero μ hE, kf_zero μ hC]
  have : 0 ≤ k * (nrm μ Φ ^ 2 + nrm μ Ψ ^ 2) := by positivity
  linarith

theorem nrm_one (μ : FiniteLaw 𝔛) : nrm μ (fun _ => 1) = 1 := by
  simp [nrm, ip]

theorem nrm_zero' (μ : FiniteLaw 𝔛) {U : 𝔛 → ℝ} (hU : ∀ x, U x = 0) : nrm μ U = 0 := by
  simp [nrm, ip, hU]

/-- The uniform law on two labels, at the single prime. -/
noncomputable def ν0 : Unit → FiniteLaw (Fin 2) := fun _ => FiniteLaw.uniform (Fin 2)

/-- The independent kernel `1`. -/
def one : Unit → Fin 2 → Fin 2 → ℝ := fun _ _ _ => 1

theorem one_eq (i : Unit) : one i = fun _ _ => 1 := rfl

theorem foldCov_one (x y : Fin 2) : foldCov (ν0 ()) (one ()) x y = 0 := by
  simp only [foldCov, one_eq, kone_one, kone'_one]
  ring

theorem matchCov_one (x y : Fin 2) : matchCov (one ()) x y = 0 := by
  simp [matchCov, one]

theorem sectorKernel_zero {C : Unit → Fin 2 → Fin 2 → ℝ} (hC : ∀ i x y, C i x y = 0)
    (x y : Unit → Fin 2) : sectorKernel C x y = 0 := by
  simp [sectorKernel, hC]

theorem UL_one (x : Unit → Fin 2) : UL ν0 one x = 1 := by
  simp only [UL, one_eq, kone_one, Finset.prod_const_one]

theorem UR_one (x : Unit → Fin 2) : UR ν0 one x = 1 := by
  simp only [UR, one_eq, kone'_one, Finset.prod_const_one]

theorem RB_one (x y : Unit → Fin 2) : RB ν0 one x y = 0 := by
  simp only [RB, UL_one, UR_one, CB, sectorKernel_zero (fun _ => foldCov_one)]
  simp [prodKernel, one]

theorem mass_one (i : Unit) : kf (ν0 i) (one i) (fun _ => 1) (fun _ => 1) = 1 := by
  rw [← expect_kone, one_eq]
  have h : kone (ν0 i) (fun _ _ => (1 : ℝ)) = fun _ => 1 := funext (kone_one _)
  rw [h, FiniteLaw.expect_const]

theorem exact_one (i : Unit) : ExactMarginals (ν0 i) (one i) := by
  rw [one_eq]
  exact ⟨fun x _ => kone_one _ x, fun y _ => kone'_one _ y⟩

/-- `lem:joint-rows`(b) holds for the toy block. -/
theorem jointRowsB_toy :
    JointRowsB ν0 (fun i => matchCov (one i)) (fun i => foldCov (ν0 i) (one i)) := by
  intro c h K k' _ _ _ _ _ _ _ _ hK _
  refine jointBlockLower_zero (blockLaw ν0) (sectorKernel_zero fun _ => matchCov_one)
    (sectorKernel_zero fun _ => foldCov_one) ?_
  nlinarith [sq_nonneg c, sq_nonneg h]

/-- `lem:joint-rows`(c) holds for the toy block. -/
theorem jointRowsC_toy : JointRowsC ν0 one := by
  intro υ n _ hυ _ hn
  have hυ0 : 0 ≤ υ := (nrm_nonneg _ _).trans hυ
  have hn0 : 0 ≤ n () := by
    have h1 := hn () (fun _ => 1) (fun _ => 1)
    rw [kf_zero _ foldCov_one, abs_zero, nrm_one, mul_one, mul_one] at h1
    exact h1
  apply formBound_zero _ RB_one
  apply mul_nonneg (by positivity)
  rw [Fintype.prod_unique]
  change 0 ≤ 1 + n () - 1
  linarith

/-- **Non-vacuity of `cor:joint-completion-blocks`**: all its hypotheses hold for the toy
block, so it produces joint data (`JointData`). -/
theorem toy_jointData :
    ExactMarginals (blockLaw ν0) (prodKernel one) ∧
    Nonempty (JointData (blockLaw ν0) (prodKernel one) (fun x y => 1 * prodKernel one x y) 1 0
      (ET 0 1 (fun _ : Unit => 1 / 2)) (0 * (1 / 2)) (1 * (1 / 2))) := by
  obtain ⟨h1, ⟨J, -⟩, -⟩ := joint_completion_blocks (r := 1 / 2) (cF := 1) (cE := 1) (kJ := 1)
    (h := 0) (H := 1) (υ := 0) (mb := 1) ν0 one one (fun _ => 1 / 2) exact_one
    (fun _ _ _ => rfl) mass_one (by norm_num) (fun _ => ⟨by norm_num, le_rfl⟩) zero_le_one
    zero_le_one (fun _ => formBound_zero (ν0 ()) foldCov_one (by norm_num))
    (fun _ => formBound_zero (ν0 ()) matchCov_one (by norm_num))
    (fun _ => jointBlockLower_zero (ν0 ()) matchCov_one foldCov_one (by norm_num)) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) le_rfl
    (le_of_eq (nrm_zero' (blockLaw ν0) fun x => by rw [UL_one, sub_self]))
    (le_of_eq (nrm_zero' (blockLaw ν0) fun x => by rw [UR_one, sub_self]))
    (fun Φ => by
      rw [kf_zero (blockLaw ν0) (A := EB one)
        (fun x y => sectorKernel_zero (C := fun i => matchCov (one i)) (fun _ => matchCov_one) x y)]
      simp)
    jointRowsB_toy jointRowsC_toy
  exact ⟨h1, ⟨J⟩⟩

end Sarkozy.FiveType.JointBlocksSanity
