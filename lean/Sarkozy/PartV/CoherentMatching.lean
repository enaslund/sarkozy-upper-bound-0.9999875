module

public import Sarkozy.PartV.CoherentCancellation

/-!
# Complete cancellation forces matches between the two distinct halves

Pair deletion preserves every label multiplicity modulo two. If both halves
are injective, each surviving label therefore has a partner in the other half.
-/

@[expose] public section

namespace Sarkozy.PartV.CoherentDictionary

open Finset

variable {p : ℕ}

theorem Cancellation.fiber_parity {x : Vertex → ZMod p} {S T : Support}
    (h : Cancellation x S T) (z : ZMod p) :
    (S.filter fun v => x v = z).card % 2 = (T.filter fun v => x v = z).card % 2 := by
  induction h with
  | refl => rfl
  | @pair S T a b ha hb hab hx rest ih =>
    rw [filter_erase, filter_erase] at ih
    by_cases hz : x a = z
    · have ha' : a ∈ S.filter (fun v => x v = z) := mem_filter.mpr ⟨ha, hz⟩
      have hb' : b ∈ S.filter (fun v => x v = z) := mem_filter.mpr ⟨hb, hx.trans hz⟩
      have hc := erase_pair_card ha' hb' hab
      omega
    · have ha' : a ∉ S.filter (fun v => x v = z) := by simp [hz]
      have hb' : b ∉ S.filter (fun v => x v = z) := by simp [hx, hz]
      simpa only [erase_eq_of_notMem ha', erase_eq_of_notMem hb'] using ih

theorem cancellation_partner {x : Vertex → ZMod p} {S : Support}
    (h : Cancellation x S ∅) (side : Vertex → Bool)
    (hleft : Set.InjOn x {v | side v = true})
    (hright : Set.InjOn x {v | side v = false}) (a : Vertex) (ha : a ∈ S) :
    ∃ b ∈ S, side b ≠ side a ∧ x b = x a := by
  by_contra hn
  push Not at hn
  let F := S.filter fun v => x v = x a
  have haF : a ∈ F := mem_filter.mpr ⟨ha, rfl⟩
  have hside (v : Vertex) (hv : v ∈ F) : side v = side a := by
    by_contra hne
    exact hn v (mem_filter.mp hv).1 hne (mem_filter.mp hv).2
  have hc : F.card ≤ 1 := by
    rw [card_le_one]
    intro v hv w hw
    have he : x v = x w := (mem_filter.mp hv).2.trans (mem_filter.mp hw).2.symm
    cases hs : side a with
    | false => exact hright ((hside v hv).trans hs) ((hside w hw).trans hs) he
    | true => exact hleft ((hside v hv).trans hs) ((hside w hw).trans hs) he
  have hp := h.fiber_parity (x a)
  have hpos : 0 < F.card := card_pos.mpr ⟨a, haF⟩
  change F.card % 2 = _ at hp
  simp only [filter_empty, card_empty, Nat.zero_mod] at hp
  omega

theorem cancellation_matching {x : Vertex → ZMod p} {S : Support}
    (h : Cancellation x S ∅) (side : Vertex → Bool)
    (hleft : Set.InjOn x {v | side v = true})
    (hright : Set.InjOn x {v | side v = false}) :
    ∃ e : {v // v ∈ S ∧ side v = true} ≃ {v // v ∈ S ∧ side v = false},
      ∀ v, x (e v).val = x v.val := by
  classical
  have hex (a : {v // v ∈ S ∧ side v = true}) :
      ∃ b : {v // v ∈ S ∧ side v = false}, x b.val = x a.val := by
    obtain ⟨b, hb, hs, hx⟩ := cancellation_partner h side hleft hright a.val a.property.1
    have hbside : side b = false := by
      rw [a.property.2] at hs
      cases hbs : side b <;> simp_all
    exact ⟨⟨b, hb, hbside⟩, hx⟩
  let f (a : {v // v ∈ S ∧ side v = true}) : {v // v ∈ S ∧ side v = false} :=
    Classical.choose (hex a)
  have hf (a) : x (f a).val = x a.val := Classical.choose_spec (hex a)
  have hinj : Function.Injective f := by
    intro a b he
    apply Subtype.ext
    apply hleft a.property.2 b.property.2
    exact (hf a).symm.trans ((congrArg (fun v => x v.val) he).trans (hf b))
  have hsurj : Function.Surjective f := by
    intro b
    obtain ⟨a, ha, hs, hx⟩ := cancellation_partner h side hleft hright b.val b.property.1
    have haside : side a = true := by
      rw [b.property.2] at hs
      cases has : side a <;> simp_all
    let a' : {v // v ∈ S ∧ side v = true} := ⟨a, ha, haside⟩
    refine ⟨a', Subtype.ext ?_⟩
    exact hright (f a').property.2 b.property.2 ((hf a').trans hx)
  exact ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, hf⟩

end Sarkozy.PartV.CoherentDictionary
