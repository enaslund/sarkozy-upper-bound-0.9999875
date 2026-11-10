module

public import Sarkozy.PartV.CoherentPinTrace
public import Sarkozy.PartV.DictionaryCollection
public import Sarkozy.SpectralD.WeilStars

/-!
# Products on the auxiliary diagonal, including deleted evaluation points

The exact identity and error bound hold for arbitrary label configurations,
including collisions. They therefore also apply in a fixed half chart.
-/

@[expose] public section

namespace Sarkozy.PartV.CoherentDictionary

open Finset Sarkozy.SpectralD Sarkozy.SpectralC
open scoped symmDiff

variable {p : ℕ} [Fact p.Prime]

theorem evaluation_mul (S T : Support) (x : Vertex → ZMod p) (z : ZMod p) :
    evaluation S x z * evaluation T x z = evaluation (S ∆ T) x z -
      if z ∈ (S ∩ T).image x then evaluation (S ∆ T) x z else 0 := by
  change (∏ v ∈ S, chiRe (z - x v)) * (∏ v ∈ T, chiRe (z - x v)) = _
  rw [prod_mul_prod_eq, prod_chiRe_sq]
  change evaluation (S ∆ T) x z * (if z ∈ (S ∩ T).image x then 0 else 1) = _
  split_ifs <;> ring

noncomputable def traceProduct (S T : Support) (x : Vertex → ZMod p) : ℝ :=
  (∑ z, evaluation S x z * evaluation T x z) / p

theorem traceProduct_eq (S T : Support) (x : Vertex → ZMod p) :
    traceProduct S T x = trace (S ∆ T) x / p -
      (∑ z ∈ (S ∩ T).image x, evaluation (S ∆ T) x z) / p := by
  unfold traceProduct
  simp_rw [evaluation_mul, sum_sub_distrib]
  rw [sub_div, sum_ite_mem, univ_inter]
  rfl

theorem traceProduct_error (S T : Support) (x : Vertex → ZMod p) :
    |traceProduct S T x - trace (S ∆ T) x / p| ≤ ((S ∩ T).card : ℝ) / p := by
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  rw [traceProduct_eq, sub_sub_cancel_left, abs_neg, abs_div, abs_of_pos hp]
  apply div_le_div_of_nonneg_right _ hp.le
  calc
    _ ≤ ∑ z ∈ (S ∩ T).image x, |evaluation (S ∆ T) x z| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _z ∈ (S ∩ T).image x, (1 : ℝ) := sum_le_sum (fun z _ => abs_evaluation_le _ x z)
    _ = ((S ∩ T).image x).card := by simp
    _ ≤ (S ∩ T).card := by exact_mod_cast card_image_le

theorem sum_product_mul {α β : Type*} (A : List α) (B : List β)
    (f : α → ℝ) (g : β → ℝ) :
    ((A.product B).map fun ab => f ab.1 * g ab.2).sum = (A.map f).sum * (B.map g).sum := by
  induction A with
  | nil => simp [List.product]
  | cons a A ih =>
    simp only [List.product] at ih ⊢
    simp only [List.flatMap_cons, List.map_append, List.sum_append, List.map_map,
      Function.comp_def, List.sum_map_mul_left, List.map_cons, List.sum_cons, ih]
    ring

theorem evaluation_square (D : Dictionary) (x : Vertex → ZMod p) (z : ZMod p) :
    (dictionaryEval D (fun S => evaluation S x z)) ^ 2 =
      ((D.product D).map fun st =>
        ((st.1.2 * st.2.2 : ℚ) : ℝ) * (evaluation st.1.1 x z * evaluation st.2.1 x z)).sum := by
  have h := sum_product_mul D D
    (fun sc => (sc.2 : ℝ) * evaluation sc.1 x z)
    (fun sc => (sc.2 : ℝ) * evaluation sc.1 x z)
  rw [sq]
  unfold dictionaryEval
  rw [← h]
  apply congrArg List.sum
  apply List.map_congr_left
  intro st _
  push_cast
  ring

theorem auxiliary_diagonal (D : Dictionary) (x : Vertex → ZMod p) :
    (∑ z, (dictionaryEval D (fun S => evaluation S x z)) ^ 2) / p =
      ((D.product D).map fun st =>
        ((st.1.2 * st.2.2 : ℚ) : ℝ) * traceProduct st.1.1 st.2.1 x).sum := by
  simp_rw [evaluation_square]
  rw [sum_list_map_comm]
  simp_rw [← mul_sum]
  simp only [traceProduct, div_eq_mul_inv, ← mul_assoc, List.sum_map_mul_right]

end Sarkozy.PartV.CoherentDictionary
