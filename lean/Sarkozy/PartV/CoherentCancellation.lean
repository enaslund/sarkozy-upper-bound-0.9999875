module

public import Sarkozy.PartV.CoherentPinTrace

/-!
# Repeated-root cancellation in a coherent trace

Equal labels can be removed in pairs. Each removal deletes at most one
evaluation point from the trace. Iterating gives an injective residual support
and an exact bound for the accumulated correction.
-/

@[expose] public section

namespace Sarkozy.PartV.CoherentDictionary

open Finset

variable {p : ℕ} [Fact p.Prime]

inductive Cancellation (x : Vertex → ZMod p) : Support → Support → Prop where
  | refl (S : Support) : Cancellation x S S
  | pair {S T : Support} (a b : Vertex) (ha : a ∈ S) (hb : b ∈ S)
      (hab : a ≠ b) (hx : x b = x a)
      (rest : Cancellation x ((S.erase a).erase b) T) : Cancellation x S T

theorem erase_pair_card {S : Support} {a b : Vertex}
    (ha : a ∈ S) (hb : b ∈ S) (hab : a ≠ b) :
    S.card = ((S.erase a).erase b).card + 2 := by
  have hb' : b ∈ S.erase a := mem_erase.mpr ⟨hab.symm, hb⟩
  have h1 := card_erase_add_one ha
  have h2 := card_erase_add_one hb'
  omega

omit [Fact p.Prime] in
theorem Cancellation.subset {x : Vertex → ZMod p} {S T : Support}
    (h : Cancellation x S T) : T ⊆ S := by
  induction h with
  | refl => exact subset_refl _
  | pair a b _ _ _ _ _ ih => exact ih.trans ((erase_subset _ _).trans (erase_subset _ _))

theorem Cancellation.trace_error {x : Vertex → ZMod p} {S T : Support}
    (h : Cancellation x S T) : ∃ n : ℕ,
      S.card = T.card + 2 * n ∧ |trace S x - trace T x| ≤ (n : ℝ) := by
  induction h with
  | refl S => exact ⟨0, by omega, by simp⟩
  | @pair S T a b ha hb hab hx rest ih =>
    obtain ⟨n, hn, he⟩ := ih
    refine ⟨n + 1, ?_, ?_⟩
    · have hc := erase_pair_card ha hb hab
      omega
    · have hid := trace_pin a b hab S x hx
      simp only [pinSupport, ha, hb, ite_true, pinHole, true_and, decide_true] at hid
      rw [hid]
      have htri := abs_sub (trace ((S.erase a).erase b) x - trace T x)
        (evaluation ((S.erase a).erase b) x (x a))
      have hh := abs_evaluation_le ((S.erase a).erase b) x (x a)
      have hrearr : trace ((S.erase a).erase b) x - evaluation ((S.erase a).erase b) x (x a) -
          trace T x = (trace ((S.erase a).erase b) x - trace T x) -
            evaluation ((S.erase a).erase b) x (x a) := by ring
      rw [hrearr]
      push_cast
      linarith

omit [Fact p.Prime] in
theorem exists_injective_cancellation (S : Support) (x : Vertex → ZMod p) :
    ∃ T, Cancellation x S T ∧ Set.InjOn x T := by
  induction S using Finset.strongInductionOn with
  | _ S ih =>
    by_cases hx : Set.InjOn x S
    · exact ⟨S, Cancellation.refl S, hx⟩
    · simp only [Set.InjOn] at hx
      push Not at hx
      obtain ⟨a, ha, b, hb, heq, hab⟩ := hx
      have hsub : (S.erase a).erase b ⊂ S :=
        Finset.ssubset_of_subset_of_ssubset (erase_subset _ _) (erase_ssubset ha)
      obtain ⟨T, hT, hi⟩ := ih _ hsub
      exact ⟨T, Cancellation.pair a b ha hb hab heq.symm hT, hi⟩

end Sarkozy.PartV.CoherentDictionary
