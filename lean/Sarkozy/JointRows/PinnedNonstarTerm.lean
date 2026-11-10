module

public import Sarkozy.JointRows.PinnedTailScalars
public import Sarkozy.ExtractionK.SingletonRecords

/-! Singleton extraction for every pinned nonstar monomial in a tail row. -/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.JointRows.PinTail

open Finset Sarkozy.Labellings Sarkozy.Extraction Sarkozy.ExtractionK

variable {p n : ℕ} [Fact p.Prime]

theorem nonstar_monomial (hp : 2 ^ 512 ≤ p) (hn : n ≤ 12)
    (hW : WeilBound (ZMod p)) (h4 : FourCycleBound p)
    (M : Finset (ZMod p)) (hz : M.card ≤ 12) (pin : Fin n → ZMod p → ℤ)
    (hpin : ∀ j t, pin j t = 0 ∨ pin j t = 1 ∨ pin j t = -1)
    (hpinM : ∀ j t, pin j t ≠ 0 → t ∈ M) (hcount : ∀ j, pinCount pin j ≤ 4)
    (ς : Fin n → Fin n → ℤ) (hς : ∀ i j, ς i j = 0 ∨ ς i j = 1 ∨ ς i j = -1)
    (S : Finset (Fin n × Fin n)) (hS : IsNonstar S)
    (hsign : ∀ e ∈ S, ς e.1 e.2 ≠ 0) (f g : (Fin n → ZMod p) → ℝ) :
    |(∑ x ∈ pinLab M pin, ∑ y ∈ pinLab M pin,
        f x * (∏ e ∈ S, chiPair ς e x y) * g y) / ((pinLab M pin).card : ℝ) ^ 2| ≤
      2 ^ 35 * (Real.sqrt p)⁻¹ ^ 2 *
        Real.sqrt ((∑ x ∈ pinLab M pin, f x ^ 2) / (pinLab M pin).card) *
        Real.sqrt ((∑ x ∈ pinLab M pin, g x ^ 2) / (pinLab M pin).card) := by
  obtain ⟨w, hw⟩ := singleton_witness hS
  let V := witV w
  let W := witW w
  have hV : V.card = 2 := witness_card_fst hw
  have hWc : W.card = 2 := witness_card_snd hw
  have he := count_error hp hn hz
  have he' : ePin (Fintype.card (ZMod p)) n M.card 4 < 1 := by
    rw [ZMod.card]
    exact he.trans_lt (by norm_num)
  have hk := IsWitness.rectKer_opBound_twoCycles hw (by omega : p ≠ 2) h4 ς
    (sign_pm_of_ne_zero hς hsign) (cmp_component_card_le_two (witnessIdx S w))
  have hk' : Influence.OpBound (injTuples (ZMod p) V) (injTuples (ZMod p) W)
      (rectKer ς S V W)
      (2 ^ twoCycleCount (witnessIdx S w) * Real.sqrt (Fintype.card (ZMod p)) ^ 2) := by
    simpa only [ZMod.card, V, W, witV, witW] using hk
  have hcover (e : Fin n × Fin n) :
      (e.1 ∈ V ∧ e.2 ∈ W) ∨ e.1 ∈ univ \ V ∨ e.2 ∈ univ \ W := by
    by_cases h1 : e.1 ∈ V
    · by_cases h2 : e.2 ∈ W
      · exact Or.inl ⟨h1, h2⟩
      · exact Or.inr (Or.inr (mem_sdiff.mpr ⟨mem_univ _, h2⟩))
    · exact Or.inr (Or.inl (mem_sdiff.mpr ⟨mem_univ _, h1⟩))
  have h := pe_class_sum_le hW M pin hpin hpinM 4 hcount he' ς hς S ∅
    (fun e he => False.elim (notMem_empty e he)) V W (univ \ V) (univ \ W) hV hWc
    (fun _ hu h => (mem_sdiff.mp h).2 hu) (fun _ hu h => (mem_sdiff.mp h).2 hu)
    (fun e _ => hcover e) (fun e he => False.elim (notMem_empty e he))
    (by positivity) hk' f g
  simp only [classKer, prod_empty, mul_one, filter_empty, card_empty, zero_add, ZMod.card] at h
  have hsum (C : Finset (Fin n)) (hC : C.card = 2) : ∑ i ∈ C, pinCount pin i ≤ 8 := by
    calc
      _ ≤ ∑ _i ∈ C, 4 := sum_le_sum fun i _ => hcount i
      _ = 8 := by simp [hC]
  have hexp : (∑ i ∈ V, pinCount pin i) + (∑ i ∈ W, pinCount pin i) ≤ 16 := by
    have hv := hsum V hV
    have hwc := hsum W hWc
    omega
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hfac0 : 0 ≤ peFactor p n M.card 4 pin ∅ V W (univ \ V) (univ \ W) := by
    unfold peFactor
    repeat' apply mul_nonneg
    all_goals exact prod_nonneg fun i _ => peF_nonneg hp0 (he.trans_lt (by norm_num)) _ _
  have hsqrt : Real.sqrt (2 ^ ((∑ v ∈ V, pinCount pin v) + ∑ v ∈ W, pinCount pin v) *
      peFactor p n M.card 4 pin ∅ V W (univ \ V) (univ \ W)) ≤ 2 ^ 32 := by
    apply Real.sqrt_le_iff.mpr
    refine ⟨by positivity, ?_⟩
    calc
      _ ≤ (2 : ℝ) ^ 16 * 2 ^ 48 := mul_le_mul
        (pow_le_pow_right₀ (by norm_num) hexp)
        (empty_factor hp hn hz pin hcount V W) hfac0 (by positivity)
      _ = _ := by norm_num
  have hker : (2 : ℝ) ^ twoCycleCount (witnessIdx S w) ≤ 2 := by
    simpa only [pow_one] using pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2)
      (cmp_twoCycleCount_le_one (witnessIdx S w))
  have hden : (1 / 4 : ℝ) ≤ (1 - ePin p n M.card 4) ^ 2 := by nlinarith
  have hcoef :
      2 ^ twoCycleCount (witnessIdx S w) * (Real.sqrt p)⁻¹ ^ 2 *
        Real.sqrt (2 ^ ((∑ v ∈ V, pinCount pin v) + ∑ v ∈ W, pinCount pin v) *
          peFactor p n M.card 4 pin ∅ V W (univ \ V) (univ \ W)) /
        (1 - ePin p n M.card 4) ^ 2 ≤ 2 ^ 35 * (Real.sqrt p)⁻¹ ^ 2 := by
    rw [div_le_iff₀ (pow_pos (by linarith : (0 : ℝ) < 1 - ePin p n M.card 4) 2)]
    calc
      _ ≤ 2 * (Real.sqrt p)⁻¹ ^ 2 * 2 ^ 32 := mul_le_mul
        (mul_le_mul_of_nonneg_right hker (sq_nonneg _)) hsqrt (Real.sqrt_nonneg _)
        (by positivity)
      _ = (2 ^ 35 * (Real.sqrt p)⁻¹ ^ 2) * (1 / 4) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hden (by positivity)
  exact h.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right hcoef (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _))

end Sarkozy.JointRows.PinTail
