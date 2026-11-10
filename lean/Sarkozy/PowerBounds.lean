module

public import Sarkozy.Definitions

@[expose] public section

/-!
# Extracting the density saving

Generalizes the real-root argument in OpenAI's `SquareDifference/Main.lean`
to the nonintegral degree gap 72 - ϑ. See `NOTICES.md` and `LICENSE.openai`.
The zero-density case is handled explicitly; no division by zero is used.
-/

namespace Sarkozy

/-- Take a positive real-degree root of a decay estimate. -/
theorem density_root_bound {δ D N a d : ℝ}
    (hδ : 0 ≤ δ) (hD : 0 ≤ D) (hN : 0 < N) (hd : 0 < d)
    (h : δ ^ d ≤ D * N ^ (-a)) :
    δ ≤ D ^ d⁻¹ * N ^ (-(a / d)) := by
  have he := Real.rpow_le_rpow (Real.rpow_nonneg hδ _) h (inv_nonneg.mpr hd.le)
  rw [← Real.rpow_mul hδ, mul_inv_cancel₀ hd.ne', Real.rpow_one] at he
  rw [Real.mul_rpow hD (Real.rpow_nonneg hN.le _), ← Real.rpow_mul hN.le] at he
  simpa only [div_eq_mul_inv, neg_mul] using he

/-- Divide off the density improvement and take the (d - ϑ)-th root. -/
theorem density_bound_of_energy {δ D N a d ϑ : ℝ}
    (hδ : 0 ≤ δ) (hD : 0 ≤ D) (hN : 0 < N) (hgap : 0 < d - ϑ)
    (h : δ ^ d ≤ D * N ^ (-a) * δ ^ ϑ) :
    δ ≤ D ^ (d - ϑ)⁻¹ * N ^ (-(a / (d - ϑ))) := by
  by_cases hz : δ = 0
  · rw [hz]
    exact mul_nonneg (Real.rpow_nonneg hD _) (Real.rpow_nonneg hN.le _)
  have hp : 0 < δ := lt_of_le_of_ne hδ (Ne.symm hz)
  apply density_root_bound hδ hD hN hgap
  rw [Real.rpow_sub hp]
  exact (div_le_iff₀ (Real.rpow_pos_of_pos hp ϑ)).2 h

/-- Multiplying a density estimate by its ambient length gives the expected power. -/
theorem card_bound_of_density {N : ℕ} {A : Finset ℤ} {C ε : ℝ}
    (hN : 1 ≤ N) (h : density N A ≤ C * (N : ℝ) ^ (-ε)) :
    (A.card : ℝ) ≤ C * (N : ℝ) ^ (1 - ε) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hb := mul_le_mul_of_nonneg_right h hn.le
  change (A.card : ℝ) / (N : ℝ) * (N : ℝ) ≤ _ at hb
  rw [div_mul_cancel₀ _ hn.ne'] at hb
  have hr : (N : ℝ) ^ (-ε) * (N : ℝ) = (N : ℝ) ^ (1 - ε) := by
    calc
      _ = (N : ℝ) ^ (-ε) * (N : ℝ) ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = _ := by rw [← Real.rpow_add hn]; congr 1; ring
  simpa only [mul_assoc, hr] using hb

/-- The paper's energy bounds, with the physical scale L and ambient length K L.

Proving this proposition for an actual energy functional is still outstanding.
In particular, `closing < 1` alone does not supply this hypothesis.
-/
def ScaledEnergyEstimate (Y : ℕ → Finset ℤ → ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ L : ℕ, 1 ≤ L → ∀ A : Finset ℤ,
    Admissible (blockScale * L) A →
      density (blockScale * L) A ^ slots ≤ Y L A ∧
      Y L A ≤ C * (L : ℝ) ^ (-decay) *
        density (blockScale * L) A ^ densityExponent

/-- The energy estimate yields the explicit density saving at every physical scale. -/
theorem scaled_density_bound {Y : ℕ → Finset ℤ → ℝ} (hY : ScaledEnergyEstimate Y) :
    ∃ D : ℝ, 0 < D ∧ ∀ L : ℕ, 1 ≤ L → ∀ A : Finset ℤ,
      Admissible (blockScale * L) A →
        density (blockScale * L) A ≤ D * (L : ℝ) ^ (-saving) := by
  obtain ⟨C, hC, hY⟩ := hY
  refine ⟨C ^ ((slots : ℝ) - densityExponent)⁻¹,
    Real.rpow_pos_of_pos hC _, ?_⟩
  intro L hL A hA
  obtain ⟨hl, hu⟩ := hY L hL A hA
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hh : density (blockScale * L) A ^ (slots : ℝ) ≤
      C * (L : ℝ) ^ (-decay) * density (blockScale * L) A ^ densityExponent := by
    simpa only [Real.rpow_natCast] using hl.trans hu
  have hb := density_bound_of_energy (density_nonneg _ _) hC.le hLpos degree_gap_pos hh
  simpa only [← saving_eq] using hb

/-- Complete the final implication, including arbitrary interval lengths.

Embed [1,N] in [1,K N] and use physical scale L=N. This costs only the fixed
constant K and avoids any assumption that N is a multiple of K.
-/
theorem powerSavingBound_of_scaledEnergyEstimate {Y : ℕ → Finset ℤ → ℝ}
    (hY : ScaledEnergyEstimate Y) : PowerSavingBound := by
  obtain ⟨D, hD, h⟩ := scaled_density_bound hY
  have hK : (0 : ℝ) < blockScale := by norm_num [blockScale]
  refine ⟨(blockScale : ℝ) * D, mul_pos hK hD, ?_⟩
  intro N hN A hA
  have hKN : N ≤ blockScale * N := by
    have hKnat : 1 ≤ blockScale := by norm_num [blockScale]
    simpa using Nat.mul_le_mul_right N hKnat
  have hlarge : Admissible (blockScale * N) A := by
    refine ⟨?_, hA.2⟩
    intro z hz
    obtain ⟨hz₁, hzN⟩ := Finset.mem_Icc.mp (hA.1 hz)
    exact Finset.mem_Icc.mpr ⟨hz₁, hzN.trans (by exact_mod_cast hKN)⟩
  have hb := h N hN A hlarge
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hden : density N A = (blockScale : ℝ) * density (blockScale * N) A := by
    unfold density
    push_cast
    field_simp
  apply card_bound_of_density hN
  rw [hden]
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hb hK.le

theorem titleBound_of_scaledEnergyEstimate {Y : ℕ → Finset ℤ → ℝ}
    (hY : ScaledEnergyEstimate Y) : TitleBound :=
  titleBound_of_powerSavingBound (powerSavingBound_of_scaledEnergyEstimate hY)

end Sarkozy
