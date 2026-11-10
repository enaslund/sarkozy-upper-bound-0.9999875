module

public import Sarkozy.PartV.CoherentMatching
public import Sarkozy.PartV.CoherentDiagonalData
public import Sarkozy.PartV.CubePins

/-! The two six-coordinate charts and the actual matching events for both coherent cuts. -/

@[expose] public section

namespace Sarkozy.PartV.CoherentDictionary

open Finset

abbrev Half (isLayer side : Bool) := {v : Vertex // cutSide isLayer v = side}

def halfSupport (isLayer side : Bool) (S : Support) : Finset (Half isLayer side) :=
  univ.filter fun v => v.val ∈ S

theorem half_card (isLayer side : Bool) : Fintype.card (Half isLayer side) = 6 := by
  cases isLayer <;> cases side <;> decide +kernel

def halfSupportEquiv (isLayer side : Bool) (S : Support) :
    {v // v ∈ S ∧ cutSide isLayer v = side} ≃ (halfSupport isLayer side S) where
  toFun v := ⟨⟨v.val, v.property.2⟩, mem_filter.mpr ⟨mem_univ _, v.property.1⟩⟩
  invFun v := ⟨v.val.val, (mem_filter.mp v.property).2, v.val.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable {p : ℕ}

def joinHalves (isLayer : Bool)
    (a : Half isLayer true → ZMod p) (b : Half isLayer false → ZMod p) : Vertex → ZMod p :=
  fun v => if hv : cutSide isLayer v = true then a ⟨v, hv⟩
    else b ⟨v, Bool.eq_false_iff.mpr hv⟩

@[simp] theorem joinHalves_left (isLayer : Bool)
    (a : Half isLayer true → ZMod p) (b : Half isLayer false → ZMod p)
    (v : Half isLayer true) : joinHalves isLayer a b v.val = a v := by
  simp [joinHalves, v.property]

@[simp] theorem joinHalves_right (isLayer : Bool)
    (a : Half isLayer true → ZMod p) (b : Half isLayer false → ZMod p)
    (v : Half isLayer false) : joinHalves isLayer a b v.val = b v := by
  simp [joinHalves, v.property]

theorem joinHalves_injOn_left (isLayer : Bool)
    (a : Half isLayer true → ZMod p) (b : Half isLayer false → ZMod p)
    (ha : Function.Injective a) :
    Set.InjOn (joinHalves isLayer a b) {v | cutSide isLayer v = true} := by
  intro v hv w hw he
  have he' : a ⟨v, hv⟩ = a ⟨w, hw⟩ :=
    (joinHalves_left isLayer a b ⟨v, hv⟩).symm.trans
      (he.trans (joinHalves_left isLayer a b ⟨w, hw⟩))
  exact congrArg Subtype.val (ha he')

theorem joinHalves_injOn_right (isLayer : Bool)
    (a : Half isLayer true → ZMod p) (b : Half isLayer false → ZMod p)
    (hb : Function.Injective b) :
    Set.InjOn (joinHalves isLayer a b) {v | cutSide isLayer v = false} := by
  intro v hv w hw he
  have he' : b ⟨v, hv⟩ = b ⟨w, hw⟩ :=
    (joinHalves_right isLayer a b ⟨v, hv⟩).symm.trans
      (he.trans (joinHalves_right isLayer a b ⟨w, hw⟩))
  exact congrArg Subtype.val (hb he')

def MatchingEvent (isLayer : Bool) (S : Support)
    (a : Half isLayer true → ZMod p) (b : Half isLayer false → ZMod p) : Prop :=
  ∃ e : (halfSupport isLayer true S) ≃ (halfSupport isLayer false S),
    ∀ v, b (e v).val = a v.val

theorem cancellation_matchingEvent (isLayer : Bool) (S : Support)
    (a : Half isLayer true → ZMod p) (b : Half isLayer false → ZMod p)
    (ha : Function.Injective a) (hb : Function.Injective b)
    (hc : Cancellation (joinHalves isLayer a b) S ∅) : MatchingEvent isLayer S a b := by
  obtain ⟨e, he⟩ := cancellation_matching hc (cutSide isLayer)
    (joinHalves_injOn_left isLayer a b ha) (joinHalves_injOn_right isLayer a b hb)
  let l := halfSupportEquiv isLayer true S
  let r := halfSupportEquiv isLayer false S
  refine ⟨l.symm.trans (e.trans r), ?_⟩
  intro v
  have h := he (l.symm v)
  have hl := joinHalves_left isLayer a b v.val
  have hr := joinHalves_right isLayer a b (r (e (l.symm v))).val
  exact hr.symm.trans (h.trans hl)

theorem halfSupport_min (isLayer : Bool) : ∀ sc ∈ dictionary39,
    3 ≤ (halfSupport isLayer false sc.1).card := by
  cases isLayer <;> decide +kernel

theorem halfSupport_matching_budget (isLayer : Bool) :
    (dictionary39.map fun sc => CubePins.matchingCount
      (halfSupport isLayer true sc.1).card (halfSupport isLayer false sc.1).card).sum = 144 := by
  cases isLayer <;> decide +kernel

end Sarkozy.PartV.CoherentDictionary
