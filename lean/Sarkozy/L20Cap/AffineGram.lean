module

public import Sarkozy.L20Cap.GapRange
public import Sarkozy.Cuts.ConstantGram

/-! Exact real Gram norms for square-affine-equivariant centered core kernels. -/

@[expose] public section

namespace Sarkozy.L20Cap

open Finset Sarkozy.Cuts Sarkozy.Recentering

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Nonempty (CoreT F)]

theorem coreKernel_gram_affine (K : CoreT F → F → ℝ)
    (hK : ∀ (α β : F) (hα : quadraticChar F α = 1) (C : CoreT F) (z : F),
      K (affCoreEquiv hα β C) (α * z + β) = K C z)
    (α β : F) (hα : quadraticChar F α = 1) (z z' : F) :
    gramKer coreLaw K K (α * z + β) (α * z' + β) = gramKer coreLaw K K z z' := by
  unfold gramKer coreLaw
  rw [FiniteLaw.expect_uniform, FiniteLaw.expect_uniform]
  congr 1
  rw [← Equiv.sum_comp (affCoreEquiv hα β)]
  exact sum_congr rfl fun C _ => by rw [hK α β hα C z, hK α β hα C z']

theorem coreKernel_gram_diag (K : CoreT F → F → ℝ)
    (hK : ∀ (α β : F) (hα : quadraticChar F α = 1) (C : CoreT F) (z : F),
      K (affCoreEquiv hα β C) (α * z + β) = K C z) (z : F) :
    gramKer coreLaw K K z z = gramKer coreLaw K K (0 : F) 0 := by
  have h := coreKernel_gram_affine K hK 1 (-z) (map_one _) z z
  simpa only [one_mul, add_neg_cancel] using h.symm

theorem coreKernel_gram_off (hm1 : quadraticChar F (-1) = -1) (K : CoreT F → F → ℝ)
    (hK : ∀ (α β : F) (hα : quadraticChar F α = 1) (C : CoreT F) (z : F),
      K (affCoreEquiv hα β C) (α * z + β) = K C z) {z z' : F} (hzz' : z ≠ z') :
    gramKer coreLaw K K z z' = gramKer coreLaw K K (0 : F) 1 := by
  apply pair_const hm1 (m := gramKer coreLaw K K)
    (fun α β hα y y' => coreKernel_gram_affine K hK α β hα y y') _ hzz' zero_ne_one
  intro y y'
  unfold gramKer
  exact coreLaw.expect_congr fun C => mul_comm _ _

theorem coreKernel_gram_trace (K : CoreT F → F → ℝ)
    (hK : ∀ (α β : F) (hα : quadraticChar F α = 1) (C : CoreT F) (z : F),
      K (affCoreEquiv hα β C) (α * z + β) = K C z) :
    gramKer coreLaw K K (0 : F) 0 =
      coreLaw.expect (fun C => (FiniteLaw.uniform F).expect (fun z => K C z ^ 2)) := by
  calc
    _ = (FiniteLaw.uniform F).expect (fun z => gramKer coreLaw K K z z) := by
      simp only [coreKernel_gram_diag K hK, FiniteLaw.expect_const]
    _ = _ := by
      unfold gramKer
      rw [Cuts.expect_comm]
      exact coreLaw.expect_congr fun C => (FiniteLaw.uniform F).expect_congr fun z => (pow_two _).symm

theorem coreKernel_mean_zero_norm_sq (hm1 : quadraticChar F (-1) = -1)
    (K : CoreT F → F → ℝ)
    (hK : ∀ (α β : F) (hα : quadraticChar F α = 1) (C : CoreT F) (z : F),
      K (affCoreEquiv hα β C) (α * z + β) = K C z)
    (hcenter : ∀ C, (FiniteLaw.uniform F).expect (K C) = 0)
    (f : F → ℝ) (hf : (FiniteLaw.uniform F).expect f = 0) :
    nrm coreLaw (recOp (FiniteLaw.uniform F) K f) ^ 2 =
      (coreLaw.expect (fun C => (FiniteLaw.uniform F).expect (fun z => K C z ^ 2)) /
        ((Fintype.card F : ℝ) - 1)) * nrm (FiniteLaw.uniform F) f ^ 2 := by
  rw [constantGram_centered_norm_sq coreLaw K hcenter (coreKernel_gram_diag K hK)
    (fun a b hab => coreKernel_gram_off hm1 K hK hab) Fintype.one_lt_card f hf,
    coreKernel_gram_trace K hK]

end Sarkozy.L20Cap
