module

public import Sarkozy.ClassData.Steps

@[expose] public section

/-!
# Non-vacuity of `ConsistentInputs` at the paper's parameters

`ConsistentInputs` fixes the class-cost parameters to the numbers of `CostData.lean`. To see that
this does not make it contradictory, `ConsistentInputs.trivial` builds an instance for **any**
class data with `N ⊆ paperN`, `C ≥ paperC`, `B' ≥ B^{ledger}`, with no diagonal weight
(`wc = 0`) and zero residuals (`ρ = 0`), taking `wt = 1`, `C_X = mono(y^arm)`, `υ = 0`:
* the background gate needs `κ_H e^{U₀} − (κ_H − κ_b) e^{tU} ≥ 0`, which holds as `κ_H ≥ κ_b ≥ 0`
  and `tU ≤ U₀` (`paper_classCost_gates`);
* the remainder bound needs `M R_err − M^inv e^{tU} tδ ≥ 0`, which is the coupon gate of
  `paper_classCost_gates` (`lem:orbit-coupon`(iv));
* `hυ` needs `mono(y^lead) ≤ mono(y^lead + y^rem)` (`mono_le_mono`).
So the parameters satisfy W2's side conditions and the structure is satisfiable.
-/

open Finset

namespace Sarkozy.ClassData

open Sarkozy.ClassBoundsPaper Sarkozy.ClassInputsPaper
open Sarkozy.TargetLedger (targetLedger)
open Sarkozy.RecordExpansion Sarkozy.RecordExpansion.Choice

variable {a : ℝ}
  {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

/-- **`ConsistentInputs` is satisfiable** at the paper's parameters: no diagonal weight, zero
residuals. -/
noncomputable def ConsistentInputs.trivial {D : TheoremCBlock.ComparisonData a m₀ blk p pr h E}
    (cd : ClassInputsPaper.ClassData D.CL) (hN : ∀ n ∈ cd.N, n ∈ paperN)
    (hC : ∀ n ∈ cd.N, paperC n ≤ cd.C n) (hBp : targetLedger.B ≤ cd.Bp) (Θ : ℕ → Type)
    [∀ L, Fintype (Θ L)] (u : ∀ L, Θ L → ℝ) :
    ConsistentInputs cd Θ (fun _ _ _ => 0) u (fun _ _ => 0) where
  hN := hN
  hC := hC
  hBp := hBp
  wt _ _ _ := 1
  CX L _ ω := mono (cd.yarm L) (selMono ω)
  υ _ _ _ := 0
  hbg L n := by
    obtain ⟨hb0, hb, hU, -⟩ := paper_classCost_gates (hN n.1 n.2)
    simp only [zero_mul, sum_const_zero]
    have he : Real.exp paperTU ≤ Real.exp paperU0 := Real.exp_le_exp.mpr hU
    have h1 : 0 ≤ paperκH n.1 * Real.exp paperU0 - (paperκH n.1 - paperκb n.1) *
        Real.exp paperTU := by
      nlinarith [Real.exp_pos paperTU, mul_le_mul_of_nonneg_left he (hb0.trans hb)]
    exact mul_nonneg h1 (sum_nonneg fun ω _ => mono_nonneg (cd.yarm_nonneg L) _)
  hρ L n := by
    obtain ⟨-, -, -, hc⟩ := paper_classCost_gates (hN n.1 n.2)
    simp only [sum_const_zero, one_mul, mul_zero, zero_mul, add_zero]
    exact mul_nonneg (by linarith) (sum_nonneg fun ω _ => mono_nonneg (cd.yarm_nonneg L) _)
  harm _ _ _ _ := one_mul _
  hυ0 _ _ _ _ := by simp
  hυ L _ ω _ := by
    simp only [mul_zero, zero_mul, sub_nonneg]
    exact mono_le_mono (cd.ylead_nonneg L) (fun v => le_add_of_nonneg_right (cd.yrem_nonneg L v))
      _
  hwc _ _ _ := rfl
  hρv L v ω _ := mul_nonneg (cd.vcost_nonneg L ω) (monomial_nonneg (cd.π_nonneg L) ω)

end Sarkozy.ClassData
