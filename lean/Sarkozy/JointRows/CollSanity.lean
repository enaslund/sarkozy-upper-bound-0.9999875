module

public import Sarkozy.JointRows.CollBridge

/-!
# Non-vacuity of the pinned collision bridge

* `toy_formBound`: `formBound_of_opBound` for the all-ones kernel on `Fin 2` (uniform `μ`,
  `‖𝟙 ⊗ 𝟙‖ = 1`), with the operator bound checked by hand.
* `uniform_const`: the uniform law satisfies the hypothesis `hlam` (constant on `𝓘_pin`).
* `toy_pinLab_nonempty`, `toy_ePin`, `toy_collision`: at `p = 3`, one coordinate, no fixed labels
  and no pins, `𝓘_pin` is nonempty, `e^pin_0 = 2/3 < 1`, and `Coll.formBound_pinKer` applies
  for the empty sign data. Its only remaining hypothesis is Weil's theorem `thm:weil`(a)
  (`Labellings.WeilBound (ZMod 3)`), which is true. So X1's hypotheses and `hlam`, `hI`,
  `hPpos` are jointly satisfiable.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.JointRows.CollSanity

open Sarkozy.FiveType Sarkozy.JointRows.Coll

theorem prob_univ_pos : 0 < Peyre.prob (FiniteLaw.uniform (Fin 2))
    (fun x => x ∈ (Finset.univ : Finset (Fin 2))) := by
  have h := Peyre.weight_le_prob (FiniteLaw.uniform (Fin 2))
    (E := fun x => x ∈ (Finset.univ : Finset (Fin 2))) (Finset.mem_univ (0 : Fin 2))
  have hw : (0 : ℝ) < (FiniteLaw.uniform (Fin 2)).weight 0 := by
    change (0 : ℝ) < (Fintype.card (Fin 2) : ℝ)⁻¹
    simp
  linarith

/-- **The bridge on a toy**: the all-ones kernel on `Fin 2` has form norm at most `1`. -/
theorem toy_formBound :
    FormBound (Peyre.condLaw (FiniteLaw.uniform (Fin 2))
      (fun x => x ∈ (Finset.univ : Finset (Fin 2))) prob_univ_pos) (fun _ _ => 1) 1 := by
  refine formBound_of_opBound _ Finset.univ
    (condLaw_weight_of_const _ _ _ (fun _ => Iff.rfl) (fun _ _ _ _ => rfl) _) _ zero_le_one ?_
  intro x
  simp only [Finset.card_univ, Fintype.card_fin, Fin.sum_univ_two]
  nlinarith [sq_nonneg (x 0 - x 1)]

/-- The uniform law is constant on every finset (`hlam`). -/
theorem uniform_const {Ω : Type*} [Fintype Ω] [Nonempty Ω] (s : Finset Ω) :
    ∀ x y, x ∈ s → y ∈ s → (FiniteLaw.uniform Ω).weight x = (FiniteLaw.uniform Ω).weight y :=
  fun _ _ _ _ => rfl

/-- No pins (one coordinate, `p = 3`). -/
def pin0 : Fin 1 → ZMod 3 → ℤ := fun _ _ => 0

/-- No cross pairs. -/
def sig0 : Fin 1 → Fin 1 → ℤ := fun _ _ => 0

/-- The labelling `x_0 = 0`. -/
def x0 : Lab 3 1 := fun _ => 0

/-- At `p = 3` with one coordinate, no fixed labels and no pins, `𝓘_pin` is nonempty. -/
theorem toy_pinLab_nonempty : x0 ∈ ExtractionK.pinLab (∅ : Finset (ZMod 3)) pin0 := by
  unfold ExtractionK.pinLab ExtractionK.pinAllowed
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨fun a b _ => Subsingleton.elim a b, fun j => ?_⟩
  simp [pin0]

theorem toy_prob_pos : 0 < Peyre.prob (FiniteLaw.uniform (Lab 3 1))
    (fun x => x ∈ ExtractionK.pinLab (∅ : Finset (ZMod 3)) pin0) := by
  have h := Peyre.weight_le_prob (FiniteLaw.uniform (Lab 3 1))
    (E := fun x => x ∈ ExtractionK.pinLab (∅ : Finset (ZMod 3)) pin0) toy_pinLab_nonempty
  have hw : (0 : ℝ) < (FiniteLaw.uniform (Lab 3 1)).weight x0 := by
    change (0 : ℝ) < (Fintype.card (Lab 3 1) : ℝ)⁻¹
    have : 0 < Fintype.card (Lab 3 1) := Fintype.card_pos
    positivity
  linarith

/-- `e^pin_0 = 2/3 < 1` at `p = 3`, `n = 1`, `z = 0`. -/
theorem toy_ePin : ExtractionK.ePin (3 : ℕ) 1 (∅ : Finset (ZMod 3)).card 0 < 1 := by
  unfold ExtractionK.ePin
  have h3 : (Real.sqrt ((3 : ℕ) : ℝ))⁻¹ ^ 2 = 1 / 3 := by
    rw [inv_pow, Real.sq_sqrt (by norm_num)]
    norm_num
  rw [h3]
  norm_num

/-- **`formBound_pinKer` applies to a toy pinned row** (with Weil's theorem as its hypothesis). -/
theorem toy_collision (hW : Labellings.WeilBound (ZMod 3)) :
    FormBound (Peyre.condLaw (FiniteLaw.uniform (Lab 3 1))
      (fun x => x ∈ ExtractionK.pinLab (∅ : Finset (ZMod 3)) pin0) toy_prob_pos)
      (ExtractionK.pinKer sig0) (collBound 3 (∅ : Finset (ZMod 3)).card 0 sig0) :=
  formBound_pinKer hW ∅ pin0 (fun _ _ => Or.inl rfl) (fun _ _ h => (h rfl).elim) 0
    (fun j => by simp [ExtractionK.pinCount, ExtractionK.pinRoots, pin0]) toy_ePin sig0
    (fun _ _ => Or.inl rfl) _ _ (fun _ => Iff.rfl) (uniform_const _) toy_prob_pos

end Sarkozy.JointRows.CollSanity
