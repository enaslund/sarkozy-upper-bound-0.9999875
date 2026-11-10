module

public import Sarkozy.L20Cap.RectGraph
public import Sarkozy.Variance.AdmissibleMoment

/-! The exact cardinality and cube density of the six-label chamber half. -/

@[expose] public section

namespace Sarkozy.L20Cap

open Finset Sarkozy.Labellings Sarkozy.Variance.WeightedMoment

variable {p : ℕ} [Fact p.Prime]

def sixEquiv : (Fin 6 → ZMod p) ≃ Six p where
  toFun x := (x 0, x 1, x 2, x 3, x 4, x 5)
  invFun y := ![y.1, y.2.1, y.2.2.1, y.2.2.2.1, y.2.2.2.2.1, y.2.2.2.2.2]
  left_inv x := by funext i; fin_cases i <;> rfl
  right_inv _ := rfl

theorem sixEquiv_mem (x : Fin 6 → ZMod p) :
    x ∈ injLabellings (ZMod p) G6 ↔ IsHalf p (sixEquiv x) := by
  have hlist : List.ofFn x = [x 0, x 1, x 2, x 3, x 4, x 5] := rfl
  have hn : [x 0, x 1, x 2, x 3, x 4, x 5].Nodup ↔ Function.Injective x := by
    rw [← hlist, List.nodup_ofFn]
  rw [mem_injLabellings_iff_feasible]
  change Feasible (ZMod p) G6 univ x ↔ [x 0, x 1, x 2, x 3, x 4, x 5].Nodup ∧
    quadraticChar (ZMod p) (x 4 - x 0) = 1 ∧ quadraticChar (ZMod p) (x 5 - x 0) = 1 ∧
    quadraticChar (ZMod p) (x 4 - x 1) = 1 ∧ quadraticChar (ZMod p) (x 5 - x 1) = 1
  simp [Feasible, G6, hn, Function.Injective]

def halfConfEquiv : (injLabellings (ZMod p) G6) ≃ HalfConf p :=
  sixEquiv.subtypeEquiv (sixEquiv_mem (p := p))

theorem card_halfConf : (Fintype.card (HalfConf p) : ℝ) =
    (((p - 4) * (p - 4) - (p - 4) : ℕ) : ℝ) * (nAdm p : ℝ) := by
  have h := weightedMoment_sum_fibre p
    (fun y : HalfConf p => y.val.1) (fun y => y.val.2.1)
    (fun y => y.val.2.2.2.2.1) (fun y => y.val.2.2.2.2.2)
    (weightedMoment_halfConf_adm p) (weightedMoment_halfConf_fibre_card p)
    (fun _ _ _ _ => (1 : ℝ))
  simp only [sum_const, card_univ, nsmul_eq_mul, mul_one] at h
  rw [h]
  unfold nAdm
  push_cast
  rfl

theorem card_G6 (h3 : p % 4 = 3) (h7 : 7 < p) :
    16 * ((injLabellings (ZMod p) G6).card : ℝ) =
      (p : ℝ) * (p - 1) * (p - 3) * (p - 7) * (p - 4) * (p - 5) := by
  have hc := Fintype.card_congr (halfConfEquiv (p := p))
  rw [Fintype.card_coe] at hc
  rw [hc, card_halfConf]
  have hn : (16 : ℝ) * nAdm p = (p : ℝ) * (p - 1) * (p - 3) * (p - 7) := by
    exact_mod_cast weightedMoment_nAdm p h3
  have h4 : 4 ≤ p := by omega
  have hsub : p - 4 ≤ (p - 4) * (p - 4) := by nlinarith
  rw [Nat.cast_sub hsub, Nat.cast_mul, Nat.cast_sub h4]
  calc
    _ = (16 * (nAdm p : ℝ)) * ((p : ℝ) - 4) * ((p : ℝ) - 5) := by push_cast; ring
    _ = _ := by rw [hn]

/-- The density `D₆ = 16/(θh)` in the finite coherent chamber estimate. -/
noncomputable def chamberCubeDensity (p : ℕ) : ℝ :=
  16 / ((1 - 1 / p) * (1 - 3 / p) * (1 - 7 / p) * (1 - 4 / p) * (1 - 5 / p))

theorem chamberCubeDensity_explicit :
    chamberCubeDensity p =
      16 * (p : ℝ) ^ 5 / ((p - 1) * (p - 3) * (p - 7) * (p - 4) * (p - 5)) := by
  have hp : (p : ℝ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  unfold chamberCubeDensity
  have he (k : ℝ) : 1 - k / p = ((p : ℝ) - k) / p := by field_simp
  simp only [he]
  rw [div_mul_div_comm, div_mul_div_comm, div_mul_div_comm, div_mul_div_comm,
    div_div_eq_mul_div]
  congr 1
  ring

theorem chamberCubeDensity_pos (h7 : 7 < p) : 0 < chamberCubeDensity p := by
  have hp : (7 : ℝ) < p := by exact_mod_cast h7
  rw [chamberCubeDensity_explicit]
  apply div_pos
  · positivity
  · exact mul_pos (mul_pos (mul_pos (mul_pos (by linarith) (by linarith))
      (by linarith)) (by linarith)) (by linarith)

theorem G6_density (h3 : p % 4 = 3) (h7 : 7 < p)
    (hne : (injLabellings (ZMod p) G6).Nonempty) (x : Fin 6 → ZMod p) :
    (graphLaw G6 hne).weight x ≤ chamberCubeDensity p / (p : ℝ) ^ 6 := by
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hc : (0 : ℝ) < (injLabellings (ZMod p) G6).card :=
    by exact_mod_cast card_pos.mpr hne
  have hn := card_G6 h3 h7
  have he : 1 / ((injLabellings (ZMod p) G6).card : ℝ) =
      16 / ((p : ℝ) * (p - 1) * (p - 3) * (p - 7) * (p - 4) * (p - 5)) := by
    rw [← hn]
    field_simp
  calc
    _ ≤ 1 / ((injLabellings (ZMod p) G6).card : ℝ) := by
      change (if x ∈ injLabellings (ZMod p) G6 then _ else 0) ≤ _
      split_ifs
      · exact le_rfl
      · positivity
    _ = _ := by
      rw [he, chamberCubeDensity_explicit]
      field_simp

end Sarkozy.L20Cap
