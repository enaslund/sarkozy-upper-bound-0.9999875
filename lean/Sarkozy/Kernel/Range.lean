module

public import Sarkozy.Kernel.AdmissibleRates

@[expose] public section

/-!
# The range of the kernel exponents (`rem:record:K20-range`(1))

On the diagonal `κ = β` the seven conditions of `def:kernel-conditions` reduce to the window
`10β/3 < η < 1/4 - 19β/12` (the other five conditions follow), which is nonempty exactly when
`β < 3/59`; and with `η = 17/100` they hold for every `β ∈ (0, 1/20]` (the paragraph "The range
of the exponents" of Section 7). Pure linear arithmetic.

New material for this paper.
-/

namespace Sarkozy

namespace Kernel

/-- `rem:record:K20-range`(1): for `κ = β > 0`, admissibility is the window
`10β/3 < η < 1/4 - 19β/12`. -/
theorem kernelAdmissible_diag_iff (β η : ℝ) (hβ : 0 < β) :
    KernelAdmissible β β η ↔ 10 * β / 3 < η ∧ η < 1 / 4 - 19 * β / 12 := by
  unfold KernelAdmissible
  constructor
  · rintro ⟨_, _, _, hE1, _, _, hE4, _, _, _⟩
    constructor <;> linarith
  · rintro ⟨h1, h2⟩
    refine ⟨hβ, hβ, by linarith, by linarith, by linarith, by linarith, by linarith, by linarith,
      by linarith, by linarith⟩

/-- `rem:record:K20-range`(1): the window is nonempty exactly when `β < 3/59`. -/
theorem kernelAdmissible_diag_exists_iff (β : ℝ) (hβ : 0 < β) :
    (∃ η : ℝ, KernelAdmissible β β η) ↔ β < 3 / 59 := by
  constructor
  · rintro ⟨η, hη⟩
    obtain ⟨h1, h2⟩ := (kernelAdmissible_diag_iff β η hβ).mp hη
    linarith
  · intro h
    refine ⟨(10 * β / 3 + (1 / 4 - 19 * β / 12)) / 2, ?_⟩
    rw [kernelAdmissible_diag_iff _ _ hβ]
    constructor <;> linarith

/-- Section 7, "The range of the exponents": with `κ = β` and `η = 17/100` the seven conditions
hold for every `β ∈ (0, 1/20]`. -/
theorem kernelAdmissible_seventeen (β : ℝ) (hβ : 0 < β) (hβ' : β ≤ 1 / 20) :
    KernelAdmissible β β (17 / 100) := by
  rw [kernelAdmissible_diag_iff _ _ hβ]
  constructor <;> linarith

end Kernel

end Sarkozy
