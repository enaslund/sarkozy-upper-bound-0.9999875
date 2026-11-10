module

public import Sarkozy.SignedDecompCrude.Paper

@[expose] public section

/-!
# Non-vacuity of ND's hypotheses (ND)

`paper/sections/21_middle_records.tex`, `prop:signed-bounds`(c).

The one analytic input left in ND's chain is (K) `RecordForm` (the normalizations and completions
of the three components). Its shape is satisfiable: for the coupling
`N_toy(x, y) = 1_{H_F}(x) 1_{H_F}(y) (∑_c α_c V_c)(x, y)/|H_F|²` (the signed record with the three
normalizations replaced by the exact `|H_F|²` and no completion) it holds with `κ = 0`
(`recordForm_toy`). Then the reduction gives `NewDecomp` for `N_toy` with
`e′ = esgND(…, 0, n_T, k_RQ)` from the two proved kernel bounds (`newDecomp_toy`): the chain
composes and the proved inputs are not vacuous assumptions.
-/

open Finset Matrix

namespace Sarkozy.SignedDecompCrude

open Sarkozy.PrimeGram Sarkozy.SignedEstimates Sarkozy.SignedComponents Sarkozy.Labellings

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

local notation "qF" => (Fintype.card F : ℝ)

/-- The toy signed record: the kernel `∑_c α_c V_c` on `H_F × H_F`, normalized by `|H_F|²`. -/
noncomputable def Ntoy (t : ℝ) : Matrix (Fin 3 → F) (Fin 3 → F) ℝ :=
  fun x y => hfI x * hfI y * signedV t x y / Hcard (F := F) ^ 2

theorem dot_Ntoy (t : ℝ) (f g : (Fin 3 → F) → ℝ) :
    f ⬝ᵥ (Ntoy t *ᵥ g) = E2 (signedV t) f g := by
  unfold E2 Ntoy
  simp only [dotProduct, mulVec, mul_sum]
  exact sum_congr rfl fun x _ => sum_congr rfl fun y _ => by ring

/-- **(K) is satisfiable**: `RecordForm` holds for `N_toy` with `κ = 0`. -/
theorem recordForm_toy (hF : (injLabellings F (foldGraph (Fin 2))).Nonempty) (t : ℝ) :
    RecordForm hF (Ntoy t) t 0 := by
  intro f g _ _
  rw [dot_Ntoy, sub_self, abs_zero, zero_mul, zero_mul]

/-- **The chain composes**: `NewDecomp` for `N_toy` from `recordForm_toy` and the two proved
kernel bounds (`nonstarBound_tensor`, `removedBound_crude`). -/
theorem newDecomp_toy (hF : (injLabellings F (foldGraph (Fin 2))).Nonempty)
    (hR : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h19 : 19 ≤ Fintype.card F) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    NewDecomp (m0 hF).weight (Ntoy t) t (esgND qF⁻¹ (√qF)⁻¹ (e0 qF) (gammaW (F := F)) 0
      (2 * (√(1 + 2 * (1 - t) ^ 2) * √(1 + (1 + t) ^ 2 + (1 - t) ^ 2)) /
        ((1 - qF⁻¹) * (1 - 2 * qF⁻¹)))
      (2 * (4 * (2 - t)) / ((1 - qF⁻¹) * (1 - 2 * qF⁻¹)))) := by
  have h19' : (19 : ℝ) ≤ qF := by exact_mod_cast h19
  have h1 : 0 < 1 - qF⁻¹ := by
    rw [sub_pos]; exact inv_lt_one_of_one_lt₀ (by linarith)
  have h2 : 0 < 1 - 2 * qF⁻¹ := by
    rw [sub_pos, ← div_eq_mul_inv, div_lt_one (by linarith)]; linarith
  have hk : 0 ≤ 2 * (4 * (2 - t)) := by linarith
  exact newDecomp_of_inputs hF hR h3 h19 ht0 ht1 (by positivity) (by positivity)
    (recordForm_toy hF t) (nonstarBound_tensor hR h3 h19 t) (removedBound_crude hR h19 ht0 ht1)

end Sarkozy.SignedDecompCrude
