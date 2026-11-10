module

public import Sarkozy.BlockInputs.UpperLayer

@[expose] public section

/-!
# Sanity checks for the BA certificates

* **`upperBandLayerCap_EE`**: the band certificate shape `UpperBandLayerCap` is satisfied at the
  recorded caps for the edgeless field pair `E × E` (B6's elementary bound
  `-81/(p - 81) ⪯ A_p ⪯ 1`, `B = 0`, `X = X_k`). So the per-band certificate is not vacuous, and it
  holds with the paper's data on the one field pair whose per-prime bound is elementary.
-/

open scoped InnerProductSpace
open Finset

namespace Sarkozy.BlockInputs

open Sarkozy Sarkozy.Labellings Sarkozy.PartV Sarkozy.FiveType Sarkozy.Cuts Sarkozy.BlockAdapter
  Sarkozy.UpperRecords

/-- **The band certificate of the `E × E` field pair holds at the recorded caps.** -/
theorem upperBandLayerCap_EE (k : Fin 310) (t₀ t₁ : PType)
    (hok : EEOK (CompletionData.record k) t₀ t₁) :
    UpperBandLayerCap k .E .E (bandCap k t₀ t₁) := by
  have hstart : (CompletionData.record k).start = (bandOf k).1 :=
    congrArg Prod.fst (CompletionData.record_endpoints k)
  have h6561 : 6561 ≤ (CompletionData.record k).start := (ee_gate k).1
  set g : ℝ := bandCap k t₀ t₁ with hgdef
  set X : ℝ := ((bandOf k).1 : ℝ) with hXdef
  have hg0 : 0 < g := bandCap_pos k t₀ t₁
  have hgq : g = ((CompletionData.record k).cap t₀ t₁ : ℝ) := rfl
  have hg1 : g ≤ 1 := by
    rw [hgq]
    exact_mod_cast hok.1
  have hgX : (81 + g) ^ 2 ≤ g ^ 2 * X := by
    have h := (Rat.cast_le (K := ℝ)).mpr hok.2
    push_cast at h
    rw [hgq, hXdef, ← hstart]
    nlinarith [h]
  have hX81 : (81 : ℝ) ^ 2 ≤ X := by
    rw [hXdef, ← hstart]
    have : ((6561 : ℕ) : ℝ) ≤ ((CompletionData.record k).start : ℝ) := by exact_mod_cast h6561
    norm_num at this ⊢
    linarith
  have hX1 : (1 : ℝ) < X := by nlinarith
  have hs : (1 : ℝ) < √X := by
    rw [show (1 : ℝ) = √1 from Real.sqrt_one.symm]
    exact Real.sqrt_lt_sqrt (by norm_num) hX1
  have hgs : g * (√X)⁻¹ < 1 := by
    have hspos : 0 < √X := by linarith
    rw [← div_eq_mul_inv, div_lt_one hspos]
    linarith
  refine ⟨g, 0, X, hg0.le, le_rfl, hX1, le_rfl, hgs, by simp, ?_⟩
  intro p _ _ hp1 _ hne v
  have hXp : X ≤ p := by
    rw [hXdef]
    exact_mod_cast hp1
  have hgate := edgeless_gate hg0 hg1 (by norm_num) hX81 hgX hXp
  have hcard : (Fintype.card (upFieldLayer .E .E).cut.Half : ℝ) ^ 2 = 81 := card_eeHalf
  refine edgeless_cutCap (upFieldLayer .E .E) (fieldGraph_EE_empty (Fin 2)) le_rfl ?_ ?_ hne v
  · rw [hcard]
    exact hgate.1
  · rw [hcard]
    exact hgate.2

end Sarkozy.BlockInputs
