module

public import Sarkozy.PartV.CoherentPinData

/-!
# The coherent score on one collision

The exact trace identity and collected coefficients give the three bounds
`64/5 + (8/5)r`, `10 + (11/5)r`, and `26/3 + (31/15)r`, with `r = 1/√p`.
This establishes the score estimates in `imp:env:coherent-single-pin`.
The extension histograms and resulting operator collision prices are separate.
-/

@[expose] public section

namespace Sarkozy.PartV.CoherentDictionary

open Finset Sarkozy.Labellings

variable {p : ℕ} [Fact p.Prime]

theorem sum_map_sub {α : Type*} (l : List α) (f g : α → ℝ) :
    (l.map fun a => f a - g a).sum = (l.map f).sum - (l.map g).sum := by
  induction l with
  | nil => simp
  | cons a l ih => simp only [List.map_cons, List.sum_cons, ih]; ring

noncomputable def holeEvaluation (i : Fin 20) (x : Vertex → ZMod p) : ℝ :=
  dictionaryEval dictionary39 fun S =>
    if pinHole (pinVertices i).1 (pinVertices i).2 S then
      evaluation (pinSupport (pinVertices i).1 (pinVertices i).2 S) x
        (x (pinVertices i).1) else 0

theorem holeEvaluation_bound (i : Fin 20) (x : Vertex → ZMod p) :
    |holeEvaluation i x| ≤ (holeMass i : ℝ) := by
  refine (abs_dictionaryEval_le dictionary39 _).trans ?_
  unfold holeMass
  rw [Rat.cast_list_sum, List.map_map]
  apply List.sum_le_sum
  intro sc _
  dsimp only [Function.comp_def]
  by_cases h : pinHole (pinVertices i).1 (pinVertices i).2 sc.1
  · simp only [h, ite_true, Rat.cast_abs]
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left (abs_evaluation_le _ x _) (abs_nonneg (sc.2 : ℝ))
  · simp [h]

theorem dictionaryEval_pin (i : Fin 20) (x : Vertex → ZMod p)
    (hx : x (pinVertices i).2 = x (pinVertices i).1) :
    dictionaryEval dictionary39 (fun S => trace S x) =
      dictionaryEval (pinRaw i) (fun S => trace S x) - holeEvaluation i x := by
  unfold dictionaryEval pinRaw holeEvaluation
  simp only [dictionaryEval, List.map_map, Function.comp_def]
  rw [← sum_map_sub]
  apply congrArg List.sum
  apply List.map_congr_left
  intro sc _
  rw [trace_pin _ _ (pin_distinct i) sc.1 x hx]
  ring

theorem coherentScore_eq_dictionaryEval (D : Dictionary) (x : Vertex → ZMod p) :
    coherentScore p D x = dictionaryEval D (fun S => trace S x) / Real.sqrt p := by
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hs : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp
  have he : Real.sqrt (p : ℝ) ^ 2 = p := Real.sq_sqrt hp.le
  change Real.sqrt p * (D.map fun sc => (sc.2 : ℝ) * (trace sc.1 x / p)).sum = _
  simp_rw [div_eq_mul_inv, ← mul_assoc]
  rw [List.sum_map_mul_right]
  change Real.sqrt p * (dictionaryEval D (fun S => trace S x) * (p : ℝ)⁻¹) = _
  field_simp
  rw [he]
  ring

/-- Injectivity is required only away from the repeated vertex. -/
theorem pin_raw_bound (hW : WeilBound (ZMod p)) (i : Fin 20) (x : Vertex → ZMod p)
    (hx : Set.InjOn x {v | v ≠ (pinVertices i).2}) :
    |dictionaryEval (pinRaw i) (fun S => trace S x)| ≤
      (leadingMass (pinRaw i) : ℝ) * Real.sqrt p + (evenMass (pinRaw i) : ℝ) := by
  rw [← collect_eval]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  rw [← collected_subsetBound]
  apply sum_le_sum
  intro S hS
  rw [abs_mul]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  have hcard := (pin_supports i S hS).1
  apply trace_bound_injOn hW S (card_pos.mp (by omega)) x
  intro a ha b hb hab
  exact hx (by intro h; subst a; exact (pin_supports i S hS).2 ha)
    (by intro h; subst b; exact (pin_supports i S hS).2 hb) hab

/-- The three exact bounds for the paper's twenty surviving single collisions. -/
theorem dictionary39_single_pin_bound (hW : WeilBound (ZMod p)) (i : Fin 20)
    (x : Vertex → ZMod p) (heq : x (pinVertices i).2 = x (pinVertices i).1)
    (hx : Set.InjOn x {v | v ≠ (pinVertices i).2}) :
    |coherentScore p dictionary39 x| ≤
      (pinLeading (pinClass i) : ℝ) + (pinTail (pinClass i) : ℝ) / Real.sqrt p := by
  have hp : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hs : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp
  rw [coherentScore_eq_dictionaryEval, dictionaryEval_pin i x heq,
    abs_div, abs_of_pos hs]
  apply (div_le_div_of_nonneg_right ((abs_sub _ _).trans
    (add_le_add (pin_raw_bound hW i x hx) (holeEvaluation_bound i x))) hs.le).trans_eq
  have hlead := (pin_collections i).1
  have htail := congrArg (fun q : ℚ => (q : ℝ)) (pin_collections i).2
  push_cast at htail
  rw [hlead]
  rw [add_assoc, htail, add_div, mul_div_cancel_right₀ _ hs.ne']

theorem dictionary39_single_pin_weight (hW : WeilBound (ZMod p)) (i : Fin 20)
    (x : Vertex → ZMod p) (heq : x (pinVertices i).2 = x (pinVertices i).1)
    (hx : Set.InjOn x {v | v ≠ (pinVertices i).2}) (u η : ℚ) :
    (η : ℝ) ≤ coherentWeight p dictionary39 u η x ∧
      coherentWeight p dictionary39 u η x ≤ (η : ℝ) +
        (1 + |(u : ℝ)| * ((pinLeading (pinClass i) : ℝ) +
          (pinTail (pinClass i) : ℝ) / Real.sqrt p)) ^ 2 := by
  have h := dictionary39_single_pin_bound hW i x heq hx
  have ha : |1 + (u : ℝ) * coherentScore p dictionary39 x| ≤
      1 + |(u : ℝ)| * ((pinLeading (pinClass i) : ℝ) +
        (pinTail (pinClass i) : ℝ) / Real.sqrt p) := by
    refine (abs_add_le _ _).trans ?_
    simpa only [abs_one, abs_mul] using
      add_le_add le_rfl (mul_le_mul_of_nonneg_left h (abs_nonneg (u : ℝ)))
  constructor
  · exact le_add_of_nonneg_right (sq_nonneg _)
  · unfold coherentWeight
    apply add_le_add le_rfl
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) ha 2

omit [Fact p.Prime] in
theorem pin_price_core {r : ℝ} (hr : r ≤ 1 / 2 ^ 20) (k : Fin 3) :
    (pinLeading k : ℝ) + (pinTail k : ℝ) * r ≤ 64 / 5 + 8 / 5 * r := by
  fin_cases k <;> norm_num [pinLeading, pinTail] <;> linarith

omit [Fact p.Prime] in
theorem pin_price_generic {r : ℝ} (hr : r ≤ 1 / 2 ^ 20) (k : Fin 3) :
    (pinLeading k : ℝ) + (pinTail k : ℝ) * r < 14 + r := by
  refine (pin_price_core hr k).trans_lt ?_
  linarith

end Sarkozy.PartV.CoherentDictionary
