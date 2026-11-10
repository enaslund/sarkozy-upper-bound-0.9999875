module

public import Sarkozy.JointRows.StarContractAllPrimes

/-! The full auxiliary space, including constants, in the orthogonal star frame. -/

@[expose] public section

namespace Sarkozy.JointRows.StarOps

open Finset Sarkozy.FiveType Sarkozy.FiveType.Blocks
open scoped BigOperators

variable {p : ℕ} [Fact p.Prime] {X : Type*} [Fintype X] [DecidableEq X]

theorem rawStar_synthesis (hp : p ≠ 2) (νp : X → FiniteLaw (ZMod p))
    {κ : ℝ} (hdens : ∀ i a, (νp i).weight a ≤ κ / p)
    (𝒮 : Finset (Finset X)) (h𝒮 : ∀ S ∈ 𝒮, S.Nonempty)
    (h : Finset X → ZMod p → ℝ) :
    ip (blockLaw νp) (fun x => ∑ S ∈ 𝒮, wOp νp S (h S) x)
      (fun x => ∑ S ∈ 𝒮, wOp νp S (h S) x) ≤
        κ * (p : ℝ)⁻¹ * ∑ S ∈ 𝒮, ip (FiniteLaw.uniform (ZMod p)) (h S) (h S) := by
  rw [ip_sum_sum, sum_sum_diag 𝒮 _]
  · rw [mul_sum]
    exact sum_le_sum fun S hS => wOp_norm_le_odd hp νp S (h𝒮 S hS)
      (fun i _ a => hdens i a) (h S)
  · intro S _ T _ hST
    exact Star.hoeffding_orthogonal νp hST (wOp_exactSupport νp S (h S))
      (wOp_exactSupport νp T (h T))

theorem rawStar_synthesis_subtype (hp : p ≠ 2) (νp : X → FiniteLaw (ZMod p))
    {κ : ℝ} (hdens : ∀ i a, (νp i).weight a ≤ κ / p)
    (𝒮 : Finset (Finset X)) (h𝒮 : ∀ S ∈ 𝒮, S.Nonempty)
    (h : 𝒮 → ZMod p → ℝ) :
    ip (blockLaw νp) (fun x => ∑ S : 𝒮, wOp νp S.val (h S) x)
      (fun x => ∑ S : 𝒮, wOp νp S.val (h S) x) ≤
        κ * (p : ℝ)⁻¹ * ∑ S : 𝒮, ip (FiniteLaw.uniform (ZMod p)) (h S) (h S) := by
  let H := fun S => if hS : S ∈ 𝒮 then h ⟨S, hS⟩ else 0
  have he (S : 𝒮) : H S.val = h S := dite_eq_left S.property
  have hb := rawStar_synthesis hp νp hdens 𝒮 h𝒮 H
  simp_rw [← sum_coe_sort 𝒮, he] at hb
  exact hb

/-- All raw star adjoints are bounded together, without discarding their auxiliary means. -/
theorem rawStar_analysis (hp : p ≠ 2) (νp : X → FiniteLaw (ZMod p))
    {κ : ℝ} (hκ : 0 ≤ κ) (hdens : ∀ i a, (νp i).weight a ≤ κ / p)
    (𝒮 : Finset (Finset X)) (h𝒮 : ∀ S ∈ 𝒮, S.Nonempty)
    (f : (X → ZMod p) → ℝ) :
    (∑ S ∈ 𝒮, ip (FiniteLaw.uniform (ZMod p)) (wStar νp S f) (wStar νp S f)) ≤
      κ * (p : ℝ)⁻¹ * ip (blockLaw νp) f f := by
  let N := ∑ S ∈ 𝒮, ip (FiniteLaw.uniform (ZMod p)) (wStar νp S f) (wStar νp S f)
  let F := fun x => ∑ S ∈ 𝒮, wOp νp S (wStar νp S f) x
  have hN : 0 ≤ N := sum_nonneg fun S _ =>
    FiniteLaw.expect_nonneg _ fun _ => mul_self_nonneg _
  have hf : 0 ≤ ip (blockLaw νp) f f :=
    FiniteLaw.expect_nonneg _ fun _ => mul_self_nonneg _
  have hadj : ip (blockLaw νp) F f = N := by
    change (blockLaw νp).expect (fun x => (∑ S ∈ 𝒮, wOp νp S (wStar νp S f) x) * f x) = N
    simp only [sum_mul, expect_finset_sum]
    exact sum_congr rfl fun S _ => ip_wOp νp S (wStar νp S f) f
  have hF : ip (blockLaw νp) F F ≤ κ * (p : ℝ)⁻¹ * N :=
    rawStar_synthesis hp νp hdens 𝒮 h𝒮 (fun S => wStar νp S f)
  have hcs : ip (blockLaw νp) F f ^ 2 ≤ ip (blockLaw νp) F F * ip (blockLaw νp) f f := by
    simpa only [ip, pow_two] using (blockLaw νp).cauchy_schwarz_sq F f
  rw [hadj] at hcs
  have hprod := mul_le_mul_of_nonneg_right hF hf
  change N ≤ κ * (p : ℝ)⁻¹ * ip (blockLaw νp) f f
  rcases hN.eq_or_lt with hz | hz
  · rw [← hz]
    exact mul_nonneg (mul_nonneg hκ (by positivity)) hf
  · nlinarith

end Sarkozy.JointRows.StarOps
