module

public import Sarkozy.MiddleCertificates.Defs
public import Sarkozy.SpectralC.MatrixNorms





@[expose] public section

namespace Sarkozy.MiddlePrimeInputs

open Finset Sarkozy.SpectralC Sarkozy.SpectralD Sarkozy.MiddleCertificates
  MiddleCertificates.MidCut
open scoped BigOperators ComplexConjugate

section General

variable {U J : Type*} [Fintype U] [DecidableEq U] [Fintype J]

omit [DecidableEq U] in
theorem sq_sum_eq (B : J → U → ℝ) (x : U → ℝ) :
    ∑ m, (∑ l, B m l * x l) ^ 2 = ∑ k, ∑ l, (∑ m, B m k * B m l) * x k * x l := by
  simp_rw [sq, Finset.sum_mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine sum_congr rfl fun k _ => ?_
  rw [Finset.sum_comm]
  refine sum_congr rfl fun l _ => sum_congr rfl fun m _ => ?_
  ring

/-- `λ|x|² - |Ax|² = |Fx|²` for real `x`, from the integer identity. -/
theorem real_quad_le (A : U → U → ℤ) (F : J → U → ℤ) (lam2 : ℕ)
    (h : ∀ k l, (if k = l then (lam2 : ℤ) else 0) - ∑ m, A m k * A m l = ∑ j, F j k * F j l)
    (x : U → ℝ) : ∑ m, (∑ l, (A m l : ℝ) * x l) ^ 2 ≤ lam2 * ∑ l, x l ^ 2 := by
  have h' : ∀ k l, (if k = l then (lam2 : ℝ) else 0) - ∑ m, (A m k : ℝ) * A m l =
      ∑ j, (F j k : ℝ) * F j l := by
    intro k l
    have := congrArg (fun z : ℤ => (z : ℝ)) (h k l)
    simp only [Int.cast_sub, Int.cast_sum, Int.cast_mul] at this
    rw [← this]
    split_ifs <;> simp
  have hd : (lam2 : ℝ) * ∑ l, x l ^ 2 =
      ∑ k, ∑ l, (if k = l then (lam2 : ℝ) else 0) * x k * x l := by
    rw [mul_sum]
    refine sum_congr rfl fun k _ => ?_
    rw [sum_eq_single k (fun l _ hl => by simp [Ne.symm hl]) (by simp)]
    simp only [↓reduceIte]
    ring
  have hF : 0 ≤ ∑ j, (∑ l, (F j l : ℝ) * x l) ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  rw [sq_sum_eq] at hF ⊢
  rw [hd]
  have : ∑ k, ∑ l, (if k = l then (lam2 : ℝ) else 0) * x k * x l -
      ∑ k, ∑ l, (∑ m, (A m k : ℝ) * A m l) * x k * x l =
      ∑ k, ∑ l, (∑ j, (F j k : ℝ) * F j l) * x k * x l := by
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun k _ => ?_
    rw [← sum_sub_distrib]
    refine sum_congr rfl fun l _ => ?_
    rw [← h' k l]
    ring
  linarith

/-- **`λ I - AᵀA = FᵀF` gives `‖A‖ ≤ √λ`** for an integer matrix `A`, as `NormLe`. -/
theorem normLe_of_factor (A : U → U → ℤ) (F : J → U → ℤ) (lam2 : ℕ)
    (h : ∀ k l, (if k = l then (lam2 : ℤ) else 0) - ∑ m, A m k * A m l = ∑ j, F j k * F j l) :
    NormLe (fun k l => (A k l : ℂ)) (Real.sqrt lam2) := by
  intro w z
  set M : U → U → ℂ := fun k l => (A k l : ℂ)
  -- `|Mz|² ≤ λ|z|²`
  have hre : ∀ m, (mulV M z m).re = ∑ l, (A m l : ℝ) * (z l).re := by
    intro m
    simp [mulV, M, Complex.re_sum, Complex.mul_re]
  have him : ∀ m, (mulV M z m).im = ∑ l, (A m l : ℝ) * (z l).im := by
    intro m
    simp [mulV, M, Complex.im_sum, Complex.mul_im]
  have hsq : ∑ m, ‖mulV M z m‖ ^ 2 ≤ lam2 * ∑ l, ‖z l‖ ^ 2 := by
    have e1 : ∀ v : ℂ, ‖v‖ ^ 2 = v.re ^ 2 + v.im ^ 2 := by
      intro v
      rw [Complex.sq_norm, Complex.normSq_apply]
      ring
    simp_rw [e1, sum_add_distrib, hre, him, mul_add]
    have := real_quad_le A F lam2 h (fun l => (z l).re)
    have := real_quad_le A F lam2 h (fun l => (z l).im)
    linarith
  have hv : vnorm (mulV M z) ≤ Real.sqrt lam2 * vnorm z := by
    unfold vnorm
    rw [← Real.sqrt_mul (Nat.cast_nonneg _)]
    exact Real.sqrt_le_sqrt hsq
  -- Cauchy--Schwarz
  have hcs : ‖bform M w z‖ ≤ vnorm w * vnorm (mulV M z) := by
    rw [bform_mulV]
    refine (norm_sum_le _ _).trans ?_
    simp_rw [norm_mul, Complex.norm_conj]
    unfold vnorm
    exact Real.sum_mul_le_sqrt_mul_sqrt _ _ _
  calc ‖bform M w z‖ ≤ vnorm w * vnorm (mulV M z) := hcs
    _ ≤ vnorm w * (Real.sqrt lam2 * vnorm z) :=
        mul_le_mul_of_nonneg_left hv (vnorm_nonneg w)
    _ = Real.sqrt lam2 * vnorm w * vnorm z := by ring

end General

/-- `λ_D`: `2` (L10), `3` (L21). -/
def lamD2 : MidCut → ℕ
  | .l10 => 2
  | .l21 => 3

/-- The factor table of `λ_D I - ςᵀς` in the codes. -/
def normFactorTable : MidCut → List (List ℤ)
  | .l10 => [[1, 0, 1]]
  | .l21 => [[1, 0, 1, 0, 1, 0], [0, 1, 0, 1, 0, 1]]

/-- The cross-sign matrix `ς` of the actual data, as an integer matrix. -/
noncomputable def sgnInt (c : MidCut) (k l : c.data.cut.Half) : ℤ :=
  edgeSign c.edge c.data.cut.flip k.1 l.1

/-- The factor `F`. -/
noncomputable def normFactor (c : MidCut) (j : Fin 2) (k : c.data.cut.Half) : ℤ :=
  entry (normFactorTable c) j.val (c.code k.1)

/-- **The integer identity `λ_D I - ςᵀς = FᵀF`** (`decide`). -/
theorem norm_identity (c : MidCut) : ∀ k l : c.data.cut.Half,
    (if k = l then (lamD2 c : ℤ) else 0) - ∑ m, sgnInt c m k * sgnInt c m l =
      ∑ j, normFactor c j k * normFactor c j l := by
  cases c
  all_goals
    unfold sgnInt normFactor normFactorTable entry lamD2
    decide +kernel

/-- **`‖Δ^E‖ ≤ √λ_D`** at every prime `p ≡ 3 (mod 4)`: `λ_D = 2` for L10 and `3` for L21
(`lem:spec:degone`, the input `Λ_D` of `thm:spectral-criterion`). -/
theorem deltaE_sharp (c : MidCut) {p : ℕ} [Fact p.Prime] (hp3 : p % 4 = 3) :
    NormLe (deltaE (Cx.sgnZ (p := p) c.data)) (Real.sqrt (lamD2 c)) := by
  have h : deltaE (Cx.sgnZ (p := p) c.data) = fun k l => ((sgnInt c k l : ℤ) : ℂ) := by
    funext k l
    exact FiniteModel.deltaE_three c.data c.edge (mem_edge c) hp3 k l
  rw [h]
  exact normLe_of_factor (sgnInt c) (normFactor c) (lamD2 c) (norm_identity c)

end Sarkozy.MiddlePrimeInputs
