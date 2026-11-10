module

public import Sarkozy.PartV.CoherentDiagonalSplit
public import Sarkozy.L20Cap.CollX1

/-! Transfer the deleted-point bound to a positive reference kernel by the Schur test. -/

@[expose] public section

namespace Sarkozy.PartV.CoherentDictionary

open Finset Sarkozy.Cuts Sarkozy.Recentering

variable {Ω : Type*} [Fintype Ω]

theorem kernel_error_domination (ν : FiniteLaw Ω) (K E : Ω → Ω → ℝ)
    (hK : ∀ x y, 0 ≤ K x y) {C : ℝ} (hE : ∀ x y, |E x y| ≤ C) (f : Ω → ℝ) :
    |kernelForm ν ν (fun x y => K x y * E x y) f f| ≤
      C * kernelForm ν ν K (fun x => |f x|) (fun x => |f x|) := by
  change |∑ x, ∑ y, ν.weight x * ν.weight y * f x * (K x y * E x y) * f y| ≤
    C * ∑ x, ∑ y, ν.weight x * ν.weight y * |f x| * K x y * |f y|
  refine (abs_sum_le_sum_abs _ _).trans ?_
  rw [mul_sum]
  apply sum_le_sum
  intro x _
  refine (abs_sum_le_sum_abs _ _).trans ?_
  rw [mul_sum]
  apply sum_le_sum
  intro y _
  calc
    _ = (ν.weight x * ν.weight y * |f x| * K x y * |f y|) * |E x y| := by
      simp only [abs_mul, abs_of_nonneg (ν.nonneg x), abs_of_nonneg (ν.nonneg y),
        abs_of_nonneg (hK x y)]
      ring
    _ ≤ (ν.weight x * ν.weight y * |f x| * K x y * |f y|) * C :=
      mul_le_mul_of_nonneg_left (hE x y)
        (by positivity [ν.nonneg x, ν.nonneg y, hK x y])
    _ = _ := mul_comm _ _

theorem kernel_error_schur (ν : FiniteLaw Ω) (K E : Ω → Ω → ℝ)
    (hK : ∀ x y, 0 ≤ K x y) (hKs : ∀ x y, K x y = K y x) {C R : ℝ}
    (hC : 0 ≤ C) (hE : ∀ x y, |E x y| ≤ C)
    (hR : ∀ x, 0 < ν.weight x → ν.expect (fun y => K x y) ≤ R) (f : Ω → ℝ) :
    |kernelForm ν ν (fun x y => K x y * E x y) f f| ≤ C * R * nrm ν f ^ 2 := by
  have hs := Sarkozy.L20Cap.schur_test ν K hK hKs hR (fun x => |f x|)
  have hn : nrm ν (fun x => |f x|) ^ 2 = nrm ν f ^ 2 := by
    simp only [nrm_sq_expect, sq_abs]
  rw [hn] at hs
  calc
    _ ≤ C * kernelForm ν ν K (fun x => |f x|) (fun x => |f x|) :=
      kernel_error_domination ν K E hK hE f
    _ ≤ C * |kernelForm ν ν K (fun x => |f x|) (fun x => |f x|)| :=
      mul_le_mul_of_nonneg_left (le_abs_self _) hC
    _ ≤ C * (R * nrm ν f ^ 2) := mul_le_mul_of_nonneg_left hs hC
    _ = _ := by ring

theorem auxiliary_diagonal_kernel_error {p : ℕ} [Fact p.Prime]
    (ν : FiniteLaw Ω) (K : Ω → Ω → ℝ) (config : Ω → Ω → Vertex → ZMod p)
    (hK : ∀ x y, 0 ≤ K x y) (hKs : ∀ x y, K x y = K y x) {R : ℝ}
    (hR : ∀ x, 0 < ν.weight x → ν.expect (fun y => K x y) ≤ R) (f : Ω → ℝ) :
    |kernelForm ν ν (fun x y => K x y *
      ((∑ z, (dictionaryEval dictionary39 (fun S => evaluation S (config x y) z)) ^ 2) / p -
        dictionaryEval diagonalRaw (fun S => trace S (config x y) / p))) f f| ≤
      ((1936 / 75 : ℝ) / p) * R * nrm ν f ^ 2 := by
  exact kernel_error_schur ν K _ hK hKs (by positivity)
    (fun x y => auxiliary_diagonal_error (config x y)) hR f

end Sarkozy.PartV.CoherentDictionary
