module

public import Sarkozy.L20Cap.AffineGram

/-! Translation symmetry turns zero row means into zero column means. -/

@[expose] public section

namespace Sarkozy.L20Cap

open Finset Sarkozy.Cuts Sarkozy.Recentering

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Nonempty (CoreT F)]

theorem coreKernel_column_mean_const (K : CoreT F → F → ℝ)
    (hK : ∀ (β : F) (C : CoreT F) (z : F),
      K (affCoreEquiv (map_one _) β C) (z + β) = K C z) (z : F) :
    coreLaw.expect (fun C => K C z) = coreLaw.expect (fun C => K C 0) := by
  unfold coreLaw
  rw [FiniteLaw.expect_uniform, FiniteLaw.expect_uniform]
  congr 1
  rw [← Equiv.sum_comp (affCoreEquiv (map_one _) z)]
  exact sum_congr rfl fun C _ => by simpa only [zero_add] using hK z C 0

theorem coreKernel_column_mean_zero (K : CoreT F → F → ℝ)
    (hK : ∀ (β : F) (C : CoreT F) (z : F),
      K (affCoreEquiv (map_one _) β C) (z + β) = K C z)
    (hcenter : ∀ C, (FiniteLaw.uniform F).expect (K C) = 0) (z : F) :
    coreLaw.expect (fun C => K C z) = 0 := by
  calc
    _ = (FiniteLaw.uniform F).expect (fun y => coreLaw.expect (fun C => K C y)) := by
      simp only [coreKernel_column_mean_const K hK, FiniteLaw.expect_const]
    _ = coreLaw.expect (fun C => (FiniteLaw.uniform F).expect (K C)) :=
      Cuts.expect_comm _ _ _
    _ = 0 := by simp only [hcenter, FiniteLaw.expect_const]

end Sarkozy.L20Cap
