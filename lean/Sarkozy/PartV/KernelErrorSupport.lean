module

public import Sarkozy.PartV.CoherentDiagonalOperator

/-! Pointwise error bounds need only hold on the support of the underlying law. -/

@[expose] public section

namespace Sarkozy.PartV.CoherentDictionary

open Finset Sarkozy.Cuts Sarkozy.Recentering

variable {Ω : Type*} [Fintype Ω]

theorem kernelForm_congr_support (ν : FiniteLaw Ω) (K L : Ω → Ω → ℝ)
    (h : ∀ x y, ν.weight x ≠ 0 → ν.weight y ≠ 0 → K x y = L x y) (f g : Ω → ℝ) :
    kernelForm ν ν K f g = kernelForm ν ν L f g := by
  change (∑ x, ∑ y, ν.weight x * ν.weight y * f x * K x y * g y) = _
  apply sum_congr rfl
  intro x _
  apply sum_congr rfl
  intro y _
  by_cases hx : ν.weight x = 0
  · simp only [hx, zero_mul]
  by_cases hy : ν.weight y = 0
  · simp only [hy, mul_zero, zero_mul]
  rw [h x y hx hy]

theorem kernel_error_supported (ν : FiniteLaw Ω) (K E : Ω → Ω → ℝ)
    (hK : ∀ x y, 0 ≤ K x y) {C M : ℝ} (hC : 0 ≤ C)
    (hE : ∀ x y, ν.weight x ≠ 0 → ν.weight y ≠ 0 → |E x y| ≤ C)
    (hM : ∀ f : Ω → ℝ, |kernelForm ν ν K f f| ≤ M * nrm ν f ^ 2) (f : Ω → ℝ) :
    |kernelForm ν ν (fun x y => K x y * E x y) f f| ≤ C * M * nrm ν f ^ 2 := by
  let E' := fun x y => if ν.weight x ≠ 0 ∧ ν.weight y ≠ 0 then E x y else 0
  have hE' : ∀ x y, |E' x y| ≤ C := by
    intro x y
    dsimp only [E']
    split_ifs with h
    · exact hE x y h.1 h.2
    · simpa only [abs_zero] using hC
  have he : kernelForm ν ν (fun x y => K x y * E x y) f f =
      kernelForm ν ν (fun x y => K x y * E' x y) f f := by
    apply kernelForm_congr_support
    intro x y hx hy
    dsimp only [E']
    rw [ite_eq_left ⟨hx, hy⟩]
  rw [he]
  have hm := hM (fun x => |f x|)
  have hn : nrm ν (fun x => |f x|) ^ 2 = nrm ν f ^ 2 := by
    simp only [nrm_sq_expect, sq_abs]
  rw [hn] at hm
  calc
    _ ≤ C * kernelForm ν ν K (fun x => |f x|) (fun x => |f x|) :=
      kernel_error_domination ν K E' hK hE' f
    _ ≤ C * |kernelForm ν ν K (fun x => |f x|) (fun x => |f x|)| :=
      mul_le_mul_of_nonneg_left (le_abs_self _) hC
    _ ≤ C * (M * nrm ν f ^ 2) := mul_le_mul_of_nonneg_left hm hC
    _ = _ := by ring

end Sarkozy.PartV.CoherentDictionary
