module

public import Sarkozy.JointRows.PinnedTailScalars
public import Sarkozy.JointRows.CollBridge
public import Sarkozy.SpectralD.CollisionNumerics

/-! Uniform collision allowances for pinned tail rows with at most twelve coordinates. -/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.JointRows.PinTail

open Finset Sarkozy.ExtractionK

variable {p n z : ℕ}

theorem count_error_sixteen (hp : 2 ^ 512 ≤ p) (hn : n ≤ 12) (hz : z ≤ 12)
    {d : ℕ} (hd : d ≤ 16) : ePin p n z d ≤ 1 / 4 := by
  apply (ePin_mono (p : ℝ) n z hd).trans
  have hr := SpectralD.tail_rp_le hp
  have hnR : (n : ℝ) ≤ 12 := by exact_mod_cast hn
  have hzR : (z : ℝ) ≤ 12 := by exact_mod_cast hz
  unfold ePin
  norm_num only [Nat.cast_ofNat]
  calc
    _ ≤ 2 ^ 16 * ((2 * 12 + 12) * (((2 : ℝ)⁻¹ ^ 256) ^ 2) +
        16 / 2 * (2 : ℝ)⁻¹ ^ 256) := by gcongr <;> norm_num
    _ ≤ _ := by norm_num

theorem collision_u (hn : n ≤ 12) (N : Fin n → Finset (Fin n)) :
    pinU p 4 N ≤ 2 ^ 24 * (Real.sqrt p)⁻¹ ^ 2 := by
  have he (i j : Fin n) : 4 + ((N j).card - if i ∈ N j then 1 else 0) ≤ 16 := by
    have hc := card_le_univ (N j)
    simp only [Fintype.card_fin] at hc
    omega
  have hnR : (n : ℝ) ≤ 12 := by exact_mod_cast hn
  have hsum : (∑ j, ∑ i, (2 : ℝ) ^
      (4 + ((N j).card - if i ∈ N j then 1 else 0))) ≤ 2 ^ 24 := by
    calc
      _ ≤ ∑ _j : Fin n, ∑ _i : Fin n, (2 : ℝ) ^ 16 :=
        sum_le_sum fun j _ => sum_le_sum fun i _ =>
          pow_le_pow_right₀ (by norm_num) (he i j)
      _ = (n : ℝ) * n * 2 ^ 16 := by simp; ring
      _ ≤ 12 * 12 * 2 ^ 16 := by gcongr
      _ ≤ _ := by norm_num
  unfold pinU
  nlinarith [sq_nonneg ((Real.sqrt p)⁻¹)]

theorem collision_u_small (hp : 2 ^ 512 ≤ p) (hn : n ≤ 12)
    (N : Fin n → Finset (Fin n)) : pinU p 4 N ≤ 1 := by
  apply (collision_u hn N).trans
  calc
    _ ≤ 2 ^ 24 * (((2 : ℝ)⁻¹ ^ 256) ^ 2) := by
      gcongr
      exact SpectralD.tail_rp_le hp
    _ ≤ _ := by norm_num

theorem collision_ups (hp : 2 ^ 512 ≤ p) (hn : n ≤ 12) (hz : z ≤ 12)
    (N : Fin n → Finset (Fin n)) : pinUps p z 4 N ≤ 2 ^ 12 := by
  have hd (i : Fin n) : 4 + (N i).card ≤ 16 := by
    have hc := card_le_univ (N i)
    simp only [Fintype.card_fin] at hc
    omega
  calc
    _ ≤ ∏ _i : Fin n, (2 : ℝ) := prod_le_prod₀
      (fun i _ => by unfold ePin; positivity)
      (fun i _ => by linarith [count_error_sixteen hp hn hz (hd i)])
    _ = (2 : ℝ) ^ n := by simp
    _ ≤ _ := pow_le_pow_right₀ (by norm_num) hn

theorem collision_d (hp : 2 ^ 512 ≤ p) (hn : n ≤ 12) (hz : z ≤ 12)
    (N : Fin n → Finset (Fin n)) : pinD p z 4 N ≤ 2 ^ 49 * (Real.sqrt p)⁻¹ ^ 2 := by
  have he := count_error hp hn hz
  have hden0 : (0 : ℝ) < (1 - ePin p n z 4) ^ n := pow_pos (by linarith) _
  have hden : (2⁻¹ : ℝ) ^ 12 ≤ (1 - ePin p n z 4) ^ n := by
    calc
      _ ≤ (2⁻¹ : ℝ) ^ n := pow_le_pow_of_le_one (by norm_num) (by norm_num) hn
      _ ≤ _ := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2⁻¹) (by linarith) n
  have hratio : pinUps p z 4 N / (1 - ePin p n z 4) ^ n ≤ 2 ^ 24 := by
    rw [div_le_iff₀ hden0]
    have hu := collision_ups hp hn hz N
    nlinarith
  have hu0 : 0 ≤ pinU p 4 N := by unfold pinU; positivity
  have hue := SpectralD.exp_remainder_le_square hu0 (collision_u_small hp hn N)
  have hexp : Real.exp (pinU p 4 N) - 1 ≤ 2 ^ 25 * (Real.sqrt p)⁻¹ ^ 2 := by
    have hu1 := collision_u_small hp hn N
    have hu := collision_u (p := p) hn N
    nlinarith
  unfold pinD
  calc
    _ ≤ 2 ^ 24 * (2 ^ 25 * (Real.sqrt p)⁻¹ ^ 2) := mul_le_mul hratio hexp
      (sub_nonneg.mpr (Real.one_le_exp_iff.mpr hu0)) (by positivity)
    _ = _ := by ring

theorem collision_bound (hp : 2 ^ 512 ≤ p) (hn : n ≤ 12) (hz : z ≤ 12)
    (ς : Fin n → Fin n → ℤ) : Coll.collBound p z 4 ς ≤ 2 ^ 49 * (Real.sqrt p)⁻¹ ^ 2 := by
  unfold Coll.collBound
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  have he : ePin p n z 4 < 1 := (count_error hp hn hz).trans_lt (by norm_num)
  simpa only [pow_two] using mul_le_mul (collision_d hp hn hz (pinNX ς))
    (collision_d hp hn hz (pinNY ς)) (pinD_nonneg p z 4 _ he) (by positivity)

end Sarkozy.JointRows.PinTail
