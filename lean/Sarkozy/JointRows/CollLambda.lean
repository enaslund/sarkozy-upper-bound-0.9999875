module

public import Sarkozy.JointRows.CollBridge
public import Sarkozy.ProbabilityProducts

/-!
# The paper's law `λ` of the pinned rows

Source: `paper/sections/16_extraction.tex`, the setting of the pinned subsection: "with `λ_i` the
uniform law on [the allowed set of `i`] and `λ = ⊗_i λ_i`, the law `μ` is `λ` conditioned on
injectivity".

* `unifOn A`: the uniform law on a nonempty finset `A`;
* `pinLambda M pin hA = ⊗_j unifOn (allowed set of j)`;
* `pinLambda_const`: `λ` is constant on `𝓘_pin`, i.e. it satisfies the hypothesis `hlam` of
  `Coll.formBound_pinKer`, `Coll.joint_rows_a_coll` and the other pinned-row theorems;
* `pinLambda_prob_pos`: `λ(𝓘_pin) > 0` when `𝓘_pin` is nonempty (`hPpos`);
* `formBound_pinKer_lambda`: `prop:pinned-collision` for the paper's `μ`.

So the pinned-row theorems apply to the paper's `λ` with `I = (· ∈ 𝓘_pin)`.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.JointRows

namespace Coll

/-- The uniform law on a nonempty finset. -/
noncomputable def unifOn {X : Type*} [Fintype X] [DecidableEq X] (A : Finset X)
    (hA : A.Nonempty) : FiniteLaw X where
  weight x := if x ∈ A then (A.card : ℝ)⁻¹ else 0
  nonneg x := by split_ifs <;> positivity
  total := by
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
    have : (A.card : ℝ) ≠ 0 := by exact_mod_cast (Finset.card_pos.mpr hA).ne'
    field_simp

variable {p : ℕ} [Fact p.Prime] {nv : ℕ}

/-- **The paper's `λ = ⊗_i λ_i`**, `λ_i` the uniform law on the allowed set of `i`. -/
noncomputable def pinLambda (M : Finset (ZMod p)) (pin : Fin nv → ZMod p → ℤ)
    (hA : ∀ j, (ExtractionK.pinAllowed M pin j).Nonempty) : FiniteLaw (Lab p nv) :=
  FiniteLaw.pi fun j => unifOn (ExtractionK.pinAllowed M pin j) (hA j)

theorem pinLambda_weight_of_mem (M : Finset (ZMod p)) (pin : Fin nv → ZMod p → ℤ)
    (hA : ∀ j, (ExtractionK.pinAllowed M pin j).Nonempty) {x : Lab p nv}
    (hx : x ∈ ExtractionK.pinLab M pin) :
    (pinLambda M pin hA).weight x = ∏ j, ((ExtractionK.pinAllowed M pin j).card : ℝ)⁻¹ := by
  have hxA := (ExtractionK.mem_pinLab.mp hx).2
  change ∏ j, (if x j ∈ ExtractionK.pinAllowed M pin j then
    ((ExtractionK.pinAllowed M pin j).card : ℝ)⁻¹ else 0) = _
  exact Finset.prod_congr rfl fun j _ => by simp only [hxA j, ↓reduceIte]

/-- **`λ` is constant on `𝓘_pin`** (the hypothesis `hlam`). -/
theorem pinLambda_const (M : Finset (ZMod p)) (pin : Fin nv → ZMod p → ℤ)
    (hA : ∀ j, (ExtractionK.pinAllowed M pin j).Nonempty) :
    ∀ x y, x ∈ ExtractionK.pinLab M pin → y ∈ ExtractionK.pinLab M pin →
      (pinLambda M pin hA).weight x = (pinLambda M pin hA).weight y := fun _ _ hx hy => by
  rw [pinLambda_weight_of_mem M pin hA hx, pinLambda_weight_of_mem M pin hA hy]

/-- **`λ(𝓘_pin) > 0`** when `𝓘_pin` is nonempty (the hypothesis `hPpos`). -/
theorem pinLambda_prob_pos (M : Finset (ZMod p)) (pin : Fin nv → ZMod p → ℤ)
    (hA : ∀ j, (ExtractionK.pinAllowed M pin j).Nonempty) {x : Lab p nv}
    (hx : x ∈ ExtractionK.pinLab M pin) :
    0 < Peyre.prob (pinLambda M pin hA) (fun y => y ∈ ExtractionK.pinLab M pin) := by
  have h := Peyre.weight_le_prob (pinLambda M pin hA)
    (E := fun y => y ∈ ExtractionK.pinLab M pin) hx
  have hw : 0 < (pinLambda M pin hA).weight x := by
    rw [pinLambda_weight_of_mem M pin hA hx]
    exact Finset.prod_pos fun j _ => inv_pos.mpr (by exact_mod_cast (Finset.card_pos.mpr (hA j)))
  linarith

/-- **`prop:pinned-collision` for the paper's `μ = λ(· | 𝓘_pin)`**: `formBound_pinKer` with
`λ = pinLambda` (`hlam`, `hI`, `hPpos` discharged; `x0` is any point of `𝓘_pin`). -/
theorem formBound_pinKer_lambda (hW : Labellings.WeilBound (ZMod p)) (M : Finset (ZMod p))
    (pin : Fin nv → ZMod p → ℤ) (hpin : ∀ j β, pin j β = 0 ∨ pin j β = 1 ∨ pin j β = -1)
    (hpinM : ∀ j β, pin j β ≠ 0 → β ∈ M) (ϖ : ℕ) (hϖ : ∀ j, ExtractionK.pinCount pin j ≤ ϖ)
    (he : ExtractionK.ePin p nv M.card ϖ < 1) (ς : Fin nv → Fin nv → ℤ)
    (hς : ∀ i j, ς i j = 0 ∨ ς i j = 1 ∨ ς i j = -1)
    (hA : ∀ j, (ExtractionK.pinAllowed M pin j).Nonempty) {x0 : Lab p nv}
    (hx0 : x0 ∈ ExtractionK.pinLab M pin) :
    FiveType.FormBound (Peyre.condLaw (pinLambda M pin hA)
      (fun y => y ∈ ExtractionK.pinLab M pin) (pinLambda_prob_pos M pin hA hx0))
      (ExtractionK.pinKer ς) (collBound p M.card ϖ ς) :=
  formBound_pinKer hW M pin hpin hpinM ϖ hϖ he ς hς _ _ (fun _ => Iff.rfl)
    (pinLambda_const M pin hA) _

end Coll

end Sarkozy.JointRows
