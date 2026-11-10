module

public import Sarkozy.TailUnit.Emission
public import Sarkozy.PartV.UpperReference

/-!
# Why the tail mixture needs the typed-mixture lemma

`paper/sections/31_density_induction_upgrade.tex`, proof of `lem:density:global-moment`, second
paragraph.

The diagonal copy of the state `(C, C)` (`badIdx`) sends all 72 slots to one object. Every mixed
`L³⁶` constant of it is at least `|X|` (`upComponent_badIdx_constant`): at the indicator of a
point the left side is `1/|X|` and the right side is `C |X|^{-2}`. In the tail law its weight is
`v_CC r⁷ > 0`, so the convexity bound `mixedLpBound_mixture` over V1's components cannot give the
constant `1`; the proof of `hunit` (`Main.lean`) uses the typed-mixture lemma instead, as the
paper does.
-/

@[expose] public section

namespace Sarkozy.TailUnit

open Finset Sarkozy.PartV

/-- The diagonal copy of the state `(C, C)`: every slot reads the object `(0, 0, 0)`. -/
def badIdx : UpIdx := (false, ⟨(.C, .C), ((0 : Fin 2), (0 : Fin 2))⟩)

/-- **Every mixed `L³⁶` constant of the diagonal `CC` component is at least `|X|`**, for field laws
with uniform vertex marginals. -/
theorem upComponent_badIdx_constant {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (F : UpperFieldLaws X)
    (h1 : ∀ (i : FType.E.Obj × FType.E.Obj × Fin 1) (g : X → ℝ),
      (F.one .E .E).expect (fun y => g (y i)) = (FiniteLaw.uniform X).expect g)
    {C : ℝ} (hC : MixedLpBound (upComponent F badIdx) 36 C) : (Fintype.card X : ℝ) ≤ C := by
  obtain ⟨x₀⟩ := (inferInstance : Nonempty X)
  set ind : X → ℝ := fun x => if x = x₀ then 1 else 0 with hind
  have hN : (0 : ℝ) < Fintype.card X := by exact_mod_cast Fintype.card_pos
  -- the left side
  have hcomp : upComponent F badIdx =
      emit (F.one .E .E) (upDiagEmission (PType.C.pat 0) (PType.C.pat 0)) := rfl
  have hsum : ∑ x, ind x = 1 := by
    simp only [hind]
    rw [sum_ite_eq']
    simp
  have hEind : (FiniteLaw.uniform X).expect ind = 1 / Fintype.card X := by
    rw [FiniteLaw.expect_uniform, hsum]
  have hpow : ∀ y : X, ind y ^ Fintype.card Slot = ind y := by
    intro y
    simp only [hind]
    split_ifs <;> simp
  have hprod : ∀ y : FType.E.Obj × FType.E.Obj × Fin 1 → X,
      ∏ v : Slot, ind (y (upDiagEmission (PType.C.pat 0) (PType.C.pat 0) v)) =
        ind (y ((0 : Fin 3), (0 : Fin 3), (0 : Fin 1))) := by
    intro y
    rw [show (fun v : Slot => ind (y (upDiagEmission (PType.C.pat 0) (PType.C.pat 0) v))) =
      fun _ => ind (y ((0 : Fin 3), (0 : Fin 3), (0 : Fin 1))) from rfl]
    rw [prod_const, card_univ, hpow]
  have hlhs : (upComponent F badIdx).expect (fun z => ∏ v, ind (z v)) = 1 / Fintype.card X := by
    rw [hcomp, expect_emit]
    simp only [Function.comp_apply]
    rw [(F.one .E .E).expect_congr hprod, h1 ((0 : Fin 3), (0 : Fin 3), (0 : Fin 1)) ind, hEind]
  -- the right side
  have hmom : (FiniteLaw.uniform X).moment 36 ind = 1 / Fintype.card X := by
    unfold FiniteLaw.moment
    have : (fun x => |ind x| ^ (36 : ℝ)) = ind := by
      funext x
      simp only [hind]
      split_ifs <;> simp
    rw [this, hEind]
  have hnorm : (FiniteLaw.uniform X).lpNorm 36 ind = (1 / Fintype.card X) ^ (1 / 36 : ℝ) := by
    unfold FiniteLaw.lpNorm
    rw [hmom]
  have hrhs : ∏ _v : Slot, (FiniteLaw.uniform X).lpNorm 36 ind = (1 / Fintype.card X) ^ 2 := by
    rw [prod_const, card_univ, card_slot, hnorm, ← Real.rpow_natCast,
      ← Real.rpow_mul (by positivity)]
    norm_num
  have h := hC (fun _ => ind)
  rw [hlhs, hrhs, abs_of_pos (by positivity)] at h
  -- `1/N ≤ C/N²` gives `N ≤ C`
  have hN2 : (0 : ℝ) < (Fintype.card X : ℝ) ^ 2 := by positivity
  rw [div_pow, one_pow, ← div_eq_mul_one_div, div_le_div_iff₀ hN hN2] at h
  nlinarith

/-- **In the tail law the diagonal `CC` component has no unit mixed `L³⁶`** (at every prime with
nonempty labelling sets), although its weight `v_CC r⁷` is positive (`tail_badWeight_pos`). -/
theorem tail_badComponent_not_unit (q : ℕ) [Fact q.Prime] (hT : TailNonempty q) :
    ¬ MixedLpBound (upComponent (tailFieldLaws q hT) badIdx) 36 1 := by
  intro h
  have hc := upComponent_badIdx_constant (tailFieldLaws q hT)
    (fun i g => graphLaw_vertex_uniform (fieldGraph .E .E (Fin 1)) (hT.one .E .E) i g) h
  rw [ZMod.card] at hc
  have h2 : (2 : ℝ) ≤ q := by exact_mod_cast (Fact.out : q.Prime).two_le
  linarith

/-- The weight of the diagonal `CC` component in the tail law is `v_CC r⁷ > 0` for `r > 0`. -/
theorem tail_badWeight_pos {r : ℝ} (hr : 0 < r) : 0 < upCoeff tailWeights r badIdx := by
  simp only [upCoeff, badIdx, tailWeights, tailV, PType.deg]
  positivity

end Sarkozy.TailUnit
