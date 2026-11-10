module

public import Sarkozy.OpsFeature.Extend
public import Sarkozy.EnvelopeSteps.Multiplicative

@[expose] public section

/-!
# `hLop` from the definition of the lift by unit replacement (`lem:oct24:mask-schur`(a))

`paper/sections/23_envelopes.tex`, `lem:oct24:mask-schur`(a): "`Lift(D)` … obtained by replacing,
in every factor, a matrix unit `e_ab` of two singleton labels by `V_a V_b^* = M_ab − 𝒥`, and, at a
fold factor, the scalar units `e₃₃` and `e₄₄` by `Q₁₂` and `Q₀₁`"; (c): the diagonal witness is
"extended by any nonnegative weights to the features that are neither centres nor arms".

OPS-S (`OpsSteps/Coupling.kern_lift_expand`) takes the lift by unit replacement in the kernel form
`kern(Lift D)(x, y) = ∑_{v,w} D_vw ∏_𝔟 kern(U_𝔟(v_𝔟, w_𝔟))(x_𝔟, y_𝔟)` relative to the product
marginal `prodWeight m`, with the unit lifts `U_𝔟(a, b)` on the full alphabets (five fold labels,
three matching labels; `foldUnit`, `matchUnit`). Here:
* `unitTable m U`: the per-block table `((a, x), (b, y)) ↦ kern(U_𝔟(a, b))(x, y)`, so that the
  kernel form is `liftMap (unitTable m U) D` (`kern_lift_eq_liftMap`);
* **`hLop_of_unitLift`**: for the diagonal witness of W2's table extended by zero to the labels
  `4` (fold) and `2` (matching), the hypothesis `hLop` of `hdom_of_table_paley_blocks` with
  `CU = restrictT labInc (unitTable m U)`;
* **`hdom_of_units`**: `hdom` for the five diagonal witnesses with `hLop` discharged by the kernel
  form of the lift and `hUY` stated label by label as `U_𝔟(a, a) ⪰ ∑_p Ξ_{p,a} Ξ_{p,a}^*` (kernels).
-/

open Finset Matrix
open scoped BigOperators

namespace Sarkozy.OpsFeature

open Sarkozy.Envelopes Sarkozy.EnvelopeSteps

/-- The full label alphabets: five fold labels `0..4`, three matching labels `0, 1, 2`. -/
abbrev fullLab (n k : ℕ) : Fin n ⊕ Fin k → Type := Sum.elim (fun _ => Fin 5) (fun _ => Fin 3)

instance fullLab_fintype (n k : ℕ) : ∀ b, Fintype (fullLab n k b)
  | Sum.inl _ => inferInstanceAs (Fintype (Fin 5))
  | Sum.inr _ => inferInstanceAs (Fintype (Fin 3))

instance fullLab_decEq (n k : ℕ) : ∀ b, DecidableEq (fullLab n k b)
  | Sum.inl _ => inferInstanceAs (DecidableEq (Fin 5))
  | Sum.inr _ => inferInstanceAs (DecidableEq (Fin 3))

/-- The centre and arm labels inside the full alphabets (`castSucc`: `0..3 ⊂ 0..4`,
`0, 1 ⊂ 0..2`). -/
def labInc (n k : ℕ) : ∀ b, featLab n k b → fullLab n k b
  | Sum.inl _ => Fin.castSucc
  | Sum.inr _ => Fin.castSucc

theorem labInc_injective (n k : ℕ) (b : Fin n ⊕ Fin k) : Function.Injective (labInc n k b) := by
  cases b with
  | inl _ => exact Fin.castSucc_injective _
  | inr _ => exact Fin.castSucc_injective _

section Units

variable {X : Type*} [Fintype X] [DecidableEq X] {L O : X → Type*} [∀ b, Fintype (L b)]
  [∀ b, Fintype (O b)] [∀ b, DecidableEq (O b)]

/-- The table of kernels of the unit lifts: `((a, x), (b, y)) ↦ kern(U_𝔟(a, b))(x, y)`. -/
noncomputable def unitTable (m : ∀ b, O b → ℝ) (U : ∀ b, L b → L b → (O b → ℝ) →ₗ[ℝ] (O b → ℝ))
    (b : X) : Matrix (L b × O b) (L b × O b) ℝ :=
  fun P Q => kern (m b) (U b P.1 Q.1) P.2 Q.2

omit [∀ b, Fintype (O b)] in
/-- The kernel form of the lift by unit replacement is `liftMap` of the unit table. -/
theorem kern_lift_eq_liftMap (m : ∀ b, O b → ℝ)
    (U : ∀ b, L b → L b → (O b → ℝ) →ₗ[ℝ] (O b → ℝ)) (Dm : Matrix (∀ b, L b) (∀ b, L b) ℝ)
    (x y : ∀ b, O b) :
    ∑ v, ∑ w, Dm v w * ∏ b, kern (m b) (U b (v b) (w b)) (x b) (y b) =
      liftMap (unitTable m U) Dm x y := rfl

end Units

section Paper

variable {n k : ℕ} {Sb : Fin n ⊕ Fin k → Type*} [∀ b, Fintype (Sb b)]
  {Fld : ∀ b, Sb b → Type*} [∀ b p, Field (Fld b p)] [∀ b p, Fintype (Fld b p)]
  [∀ b p, DecidableEq (Fld b p)] {O : Fin n ⊕ Fin k → Type*} [∀ b, Fintype (O b)]
  [∀ b, DecidableEq (O b)]

/-- The diagonal witness of a table on the centre and arm words. -/
noncomputable def witnessD (Tb : EnvTable) (n k : ℕ) :
    Matrix (∀ b, featLab n k b) (∀ b, featLab n k b) ℝ :=
  diagonal ((fun v => (featWeight Tb v : ℝ)) ∘ (featEquiv n k).symm)

omit [∀ b, Fintype (O b)] in
/-- **`hLop` from the kernel form of the lift by unit replacement** (OPS-S's `hLift` of
`kern_lift_expand`), for the diagonal witness extended by zero to the labels that are neither
centres nor arms. -/
theorem hLop_of_unitLift (Tb : EnvTable) (mb : ∀ b, O b → ℝ)
    (U : ∀ b, fullLab n k b → fullLab n k b → (O b → ℝ) →ₗ[ℝ] (O b → ℝ))
    (Dop : ((∀ b, O b) → ℝ) →ₗ[ℝ] ((∀ b, O b) → ℝ))
    (hLift : ∀ x y, kern (prodWeight mb) Dop x y =
      ∑ v, ∑ w, extendD (labInc n k) (witnessD Tb n k) v w *
        ∏ b, kern (mb b) (U b (v b) (w b)) (x b) (y b)) (x y : ∀ b, O b) :
    kern (prodWeight mb) Dop x y =
      liftMap (restrictT (labInc n k) (unitTable mb U)) (witnessD Tb n k) x y := by
  rw [hLift, kern_lift_eq_liftMap, liftMap_extend]

/-- **`hdom` for the five diagonal witnesses** (B11's `hdom`, `lem:oct24:mask-schur`(a), (c)),
with `hLop` from the kernel form of the lift by unit replacement (`hLift`, OPS-S's shape) and `hUY`
label by label: at every block and every centre or arm label `a`,
`kern U_𝔟(a, a) ⪰ ∑_p Ξ_{p,a} Ξ_{p,a}ᵀ` (`hUa`; `singleton_le_proj` for `a = 0, 1, 2`,
`label3_le_substitute` for the fold label `3`). The remaining inputs: the per-block star form `hLb`
of the leading kernels (`kern_block_lead_starSum` at a fold block), `hUa`, and `hLift`. -/
theorem hdom_of_units (hF : ∀ b p, ringChar (Fld b p) ≠ 2)
    (h3 : ∀ b p, Fintype.card (Fld b p) % 4 = 3) {Tb : EnvTable}
    (hT : tablePos Tb n k = true) (hC : maskCheck Tb n k = true) (hnk : Even (n + k))
    (Ξb : ∀ b (p : Sb b), Matrix (O b) (featLab n k b × Fld b p) ℝ) (mb : ∀ b, O b → ℝ)
    (U : ∀ b, fullLab n k b → fullLab n k b → (O b → ℝ) →ₗ[ℝ] (O b → ℝ))
    (hUa : ∀ b (a : featLab n k b), (Matrix.of fun x y : O b =>
      kern (mb b) (U b (labInc n k b a) (labInc n k b a)) x y -
        ∑ p, ∑ z, Ξb b p x (a, z) * Ξb b p y (a, z)).PosSemidef)
    (c : ∀ b, Sb b → ℝ) (hc0 : ∀ b p, 0 ≤ c b p) (hc1 : ∀ b p, c b p ≤ 1)
    {Lead Lop : ((∀ b, O b) → ℝ) →ₗ[ℝ] ((∀ b, O b) → ℝ)}
    (hLb : ∀ x y, kern (prodWeight mb) Lead x y = ∏ b, starKer Ξb c b (x b) (y b))
    (hLift : ∀ x y, kern (prodWeight mb) Lop x y =
      ∑ v, ∑ w, extendD (labInc n k) (witnessD Tb n k) v w *
        ∏ b, kern (mb b) (U b (v b) (w b)) (x b) (y b)) :
    OpLE (prodWeight mb) Lead Lop ∧ OpLE (prodWeight mb) (-Lead) Lop :=
  hdom_of_table_paley_blocks hF h3 hT hC hnk Ξb (restrictT (labInc n k) (unitTable mb U))
    (fun b => hUY_of_labels _ _ b fun a => hUa b a) c hc0 hc1 hLb
    (hLop_of_unitLift Tb mb U Lop hLift)

end Paper

end Sarkozy.OpsFeature
