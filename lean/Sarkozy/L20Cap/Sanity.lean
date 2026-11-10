module

public import Sarkozy.L20Cap.Caps



@[expose] public section

namespace Sarkozy.L20Cap.Sanity

open Sarkozy.L20Cap

instance : Fact (Nat.Prime 11) := ⟨by decide⟩

theorem hm1_eleven : quadraticChar (ZMod 11) (-1) = -1 := by decide

theorem adm_eleven : Adm (![0, 1, 4, 5] : Fin 4 → ZMod 11) := by
  unfold Adm
  refine ⟨?_, by decide, by decide, by decide, by decide⟩
  decide

instance : Nonempty (CoreT (ZMod 11)) := ⟨⟨_, adm_eleven⟩⟩

instance : Nonempty (PairT (ZMod 11)) := ⟨⟨(0, 1), by decide⟩⟩

theorem six_le_eleven : 6 ≤ Fintype.card (ZMod 11) := by simp

/-- The half law exists at `p = 11`. -/
noncomputable example : Sarkozy.FiniteLaw (CoreT (ZMod 11) × PairT (ZMod 11)) :=
  halfLaw six_le_eleven

end Sarkozy.L20Cap.Sanity
