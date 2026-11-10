module

public import Sarkozy.PartVLaws.RowFrame
public import Sarkozy.JointRows.LawEquiv

/-! Reading all graph rows is an exact bijection, including arbitrary row coordinates. -/

@[expose] public section

namespace Sarkozy.PartVLaws

open Finset Sarkozy.Labellings Sarkozy.PartV

theorem map_equiv_weight {X Y : Type*} [Fintype X] [Fintype Y] [DecidableEq Y]
    (μ : FiniteLaw X) (e : X ≃ Y) (y : Y) : (μ.map e).weight y = μ.weight (e.symm y) := by
  classical
  change (∑ x, if e x = y then μ.weight x else 0) = _
  rw [sum_eq_single (e.symm y)]
  · simp only [Equiv.apply_symm_apply, ↓reduceIte]
  · intro x _ hx
    exact ite_eq_right (fun h => hx (e.injective (h.trans (e.apply_symm_apply y).symm)))
  · intro h
    exact False.elim (h (mem_univ _))

variable {p : ℕ} {V Q : Type} [Fintype V] [DecidableEq V] [Fintype Q] [DecidableEq Q]

def rowReadEquiv (e : Q ≃ V) : (Fin 3 × V → ZMod p) ≃ (Fin 3 → Q → ZMod p) where
  toFun z a q := z (a, e q)
  invFun ω v := ω v.1 (e.symm v.2)
  left_inv z := by funext v; simp only [Equiv.apply_symm_apply, Prod.mk.eta]
  right_inv ω := by funext a q; simp only [Equiv.symm_apply_apply]

abbrev rowReindex (e : Q ≃ V) : (V → ZMod p) ≃ (Q → ZMod p) where
  toFun x q := x (e q)
  invFun y v := y (e.symm v)
  left_inv x := by funext v; simp only [Equiv.apply_symm_apply]
  right_inv y := by funext q; simp only [Equiv.symm_apply_apply]

variable [Fact p.Prime]

theorem graph_row_weight (G : OrientedGraph (Fin 3 × V))
    (hne : (injLabellings (ZMod p) G).Nonempty) (e : Q ≃ V) (ω : Fin 3 → Q → ZMod p) :
    ((graphLaw G hne).map (rowRead (Equiv.refl _) e)).weight ω =
      (graphLaw G hne).weight ((rowReadEquiv e).symm ω) :=
  map_equiv_weight _ (rowReadEquiv e) ω

theorem graph_middle_injective (G : OrientedGraph (Fin 3 × V))
    (hne : (injLabellings (ZMod p) G).Nonempty) (e : Q ≃ V) (b : Q → ZMod p)
    (hb : (nuOf ((graphLaw G hne).map (rowRead (Equiv.refl _) e))).weight b ≠ 0) :
    Function.Injective b := by
  classical
  rw [nuOf, map_map', map_weight_ne_zero] at hb
  obtain ⟨z, hz, hr⟩ := hb
  have hzmem : z ∈ injLabellings (ZMod p) G := by
    by_contra h
    exact hz (by simp [graphLaw, h])
  have hi := (mem_filter.mp hzmem).2.1
  intro q q' hqq
  have heq : z (1, e q) = z (1, e q') := by
    change (rowRead (Equiv.refl _) e z) 1 q = (rowRead (Equiv.refl _) e z) 1 q'
    change (fun q => rowRead (Equiv.refl _) e z 1 q) = b at hr
    rw [show rowRead (Equiv.refl _) e z 1 = b from hr]
    exact hqq
  exact e.injective (congrArg Prod.snd (hi _ (mem_univ _) _ (mem_univ _) heq))

end Sarkozy.PartVLaws
