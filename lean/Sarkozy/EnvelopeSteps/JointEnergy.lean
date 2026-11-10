module

public import Sarkozy.EnvelopeSteps.Placement

@[expose] public section

/-!
# The energy of a joint law on a block set against an outside law, and (P5)

`paper/sections/23_envelopes.tex`, proof of `thm:envelopes`, Steps 1–2 (the energies
`Y_{[K]_ω ⊗ λ_{-X}}` and `Y^{Ñ}[[K]_ω]`); `paper/sections/10_comparison_lemmas.tex`, the positivity
property (P5) of the energy toolkit (the energy of a product of laws that are positive at the cut
is nonnegative).

In the formalization the energy of a product of per-block laws is
`diagonalIntegral (tensorLaw L) F`. The placed operators of `thm:envelopes` (the leading star
tensor `L_ω`, the remainder `Υ_ω`, the envelope `D_ω`) are **not** tensors over the blocks of `X`,
so their placements are joint laws on the labels of all blocks of `X` together. This file pairs a
joint law `κ` on labels `A` (the labels of the blocks of `X`) with an outside law `O` on labels `B`
(the labels of the blocks outside `X`, e.g. a tensor of the brackets `Ñ_𝔅`), as the two-factor
tensor over `Bool`:

* `pairLaws κ O`, `jointEnergy κ O F = Y_{κ ⊗ O}` with the integrand `F` on the joint label;
* **`jointEnergy_nonneg`** ((P5)): `κ ⪰_c 0` and `O ⪰_c 0` give `Y_{κ ⊗ O} ≥ 0`;
* `jointEnergyL O F`, the energy as a linear map in `κ` (`jointEnergyL_apply`);
* **`jointEnergy_P5`** ((P5), "± tensorization"): if `(O_Ñ O_λ; O_λ O_Ñ) ⪰_c 0` and
  `κ ± ζ ⪰_c 0`, then `|Y_{ζ ⊗ O_λ}| ≤ Y_{κ ⊗ O_Ñ}`.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.EnvelopeSteps

universe u

/-- The label family `true ↦ A` (inside `X`), `false ↦ B` (outside `X`). -/
abbrev pairFam (A B : Type u) : Bool → Type u := fun b => cond b A B

instance pairFam.instFintype {A B : Type u} [Fintype A] [Fintype B] :
    ∀ b, Fintype (pairFam A B b)
  | true => inferInstanceAs (Fintype A)
  | false => inferInstanceAs (Fintype B)

instance pairFam.instDecidableEq {A B : Type u} [DecidableEq A] [DecidableEq B] :
    ∀ b, DecidableEq (pairFam A B b)
  | true => inferInstanceAs (DecidableEq A)
  | false => inferInstanceAs (DecidableEq B)

variable {V : Type*} [Fintype V] [DecidableEq V]
  {A B : Type u} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

/-- The two factors: `κ` on the labels of `X`, `O` outside. -/
def pairLaws (κ : ((V → A) → ℝ) →ₗ[ℝ] ℝ) (O : ((V → B) → ℝ) →ₗ[ℝ] ℝ) :
    ∀ b, ((V → pairFam A B b) → ℝ) →ₗ[ℝ] ℝ
  | true => κ
  | false => O

/-- **The energy `Y_{κ ⊗ O}`** of the joint law `κ` on the labels of `X` against the outside law
`O`, with the integrand `F` on the joint label. -/
noncomputable def jointEnergy (κ : ((V → A) → ℝ) →ₗ[ℝ] ℝ) (O : ((V → B) → ℝ) →ₗ[ℝ] ℝ)
    (F : (∀ b, pairFam A B b) → ℝ) : ℝ :=
  diagonalIntegral (tensorLaw (pairLaws κ O)) F

/-- **(P5) for a joint law on `X`**: if `κ ⪰_c 0` and the outside law `O ⪰_c 0`, then
`Y_{κ ⊗ O} ≥ 0`. -/
theorem jointEnergy_nonneg (c : ReflectionCut V) {κ : ((V → A) → ℝ) →ₗ[ℝ] ℝ}
    {O : ((V → B) → ℝ) →ₗ[ℝ] ℝ} (hκ : c.Positive κ) (hO : c.Positive O)
    (F : (∀ b, pairFam A B b) → ℝ) : 0 ≤ jointEnergy κ O F := by
  have h : ∀ b, c.Positive (pairLaws κ O b) := by
    intro b
    cases b
    · exact hO
    · exact hκ
  exact (ReflectionCut.Positive.tensor h).diagonal_nonneg F

/-- The density of the two-factor tensor. -/
theorem tensorLaw_pairLaws_apply (κ : ((V → A) → ℝ) →ₗ[ℝ] ℝ) (O : ((V → B) → ℝ) →ₗ[ℝ] ℝ)
    (Φ : (V → ∀ b, pairFam A B b) → ℝ) :
    tensorLaw (pairLaws κ O) Φ = ∑ z : ∀ b, V → pairFam A B b,
      (lawDensity κ (z true) * lawDensity O (z false)) * Φ (fun v b => z b v) := by
  change (∑ z : ∀ b, V → pairFam A B b,
    (∏ b, lawDensity (pairLaws κ O b) (z b)) * Φ (fun v b => z b v)) = _
  refine sum_congr rfl fun z _ => ?_
  rw [Fintype.prod_bool]
  rfl

theorem lawDensity_add {Ω : Type*} [DecidableEq Ω] (L L' : (Ω → ℝ) →ₗ[ℝ] ℝ) (x : Ω) :
    lawDensity (L + L') x = lawDensity L x + lawDensity L' x := rfl

theorem lawDensity_smul {Ω : Type*} [DecidableEq Ω] (a : ℝ) (L : (Ω → ℝ) →ₗ[ℝ] ℝ) (x : Ω) :
    lawDensity (a • L) x = a * lawDensity L x := rfl

/-- **The energy against `O` as a linear map in the joint law `κ`.** -/
noncomputable def jointEnergyL (O : ((V → B) → ℝ) →ₗ[ℝ] ℝ) (F : (∀ b, pairFam A B b) → ℝ) :
    (((V → A) → ℝ) →ₗ[ℝ] ℝ) →ₗ[ℝ] ℝ where
  toFun κ := jointEnergy κ O F
  map_add' κ κ' := by
    simp only [jointEnergy, diagonalIntegral, multilinearIntegral, tensorLaw_pairLaws_apply,
      lawDensity_add, add_mul, sum_add_distrib]
  map_smul' a κ := by
    simp only [jointEnergy, diagonalIntegral, multilinearIntegral, tensorLaw_pairLaws_apply,
      lawDensity_smul, RingHom.id_apply, smul_eq_mul, mul_sum]
    exact sum_congr rfl fun z _ => by ring

theorem jointEnergyL_apply (O : ((V → B) → ℝ) →ₗ[ℝ] ℝ) (F : (∀ b, pairFam A B b) → ℝ)
    (κ : ((V → A) → ℝ) →ₗ[ℝ] ℝ) : jointEnergyL O F κ = jointEnergy κ O F := rfl

/-- (P5) for `jointEnergyL`. -/
theorem jointEnergyL_nonneg (c : ReflectionCut V) {O : ((V → B) → ℝ) →ₗ[ℝ] ℝ}
    (hO : c.Positive O) (F : (∀ b, pairFam A B b) → ℝ) {κ : ((V → A) → ℝ) →ₗ[ℝ] ℝ}
    (hκ : c.Positive κ) : 0 ≤ jointEnergyL O F κ :=
  jointEnergy_nonneg c hκ hO F

/-- **(P5) for the joint energies** (`it:record:P5`, "± tensorization"): if the outside laws form a
bracket `(O_Ñ O_λ; O_λ O_Ñ) ⪰_c 0` (the tensor of the brackets of (CP3)), and `κ ± ζ ⪰_c 0`, then
`|Y_{ζ ⊗ O_λ}| ≤ Y_{κ ⊗ O_Ñ}`. -/
theorem jointEnergy_P5 (c : ReflectionCut V) {ON Olam : ((V → B) → ℝ) →ₗ[ℝ] ℝ}
    (hO : c.Bracket ON Olam ON) (F : (∀ b, pairFam A B b) → ℝ)
    {κ ζ : ((V → A) → ℝ) →ₗ[ℝ] ℝ} (hp : c.Positive (κ + ζ)) (hm : c.Positive (κ - ζ)) :
    |jointEnergy ζ Olam F| ≤ jointEnergy κ ON F := by
  have hκ := ReflectionCut.bracket_of_add_sub_positive hp hm
  have h : ∀ b, c.Bracket (pairLaws κ ON b) (pairLaws ζ Olam b) (pairLaws κ ON b) := by
    intro b
    cases b
    · exact hO
    · exact hκ
  have hT := ReflectionCut.Bracket.tensor h
  have hf := hT.folding (fun _ => F)
  have h0 : 0 ≤ jointEnergy κ ON F := hT.left_positive.diagonal_nonneg F
  change |jointEnergy ζ Olam F| ^ 2 ≤ jointEnergy κ ON F * jointEnergy κ ON F at hf
  nlinarith [abs_nonneg (jointEnergy ζ Olam F)]

end Sarkozy.EnvelopeSteps
