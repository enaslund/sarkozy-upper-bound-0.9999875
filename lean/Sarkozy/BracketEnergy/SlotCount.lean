module

public import Sarkozy.BracketEnergy.PairSlots

@[expose] public section

/-!
# The slots of the queries

The pair inputs of `envC`, `fixC` carry the query `e` at exactly two slots, its source `u_e` and
the reflected source `ι u_e`. This file counts the slots:

* `slotQuery_eq_some_iff`: `slotQuery u v = some e ↔ v = u_e ∨ v = ι u_e`;
* `card_slotQuery_some`: each query has two slots; `card_slotQuery_none`: `72 − 2|E|` slots carry
  `F_A`;
* **`prod_slotQuery`**: `∏_v G(slotQuery v) = G(none)^{72 − 2|E|} ∏_e G(some e)^2`. With it the
  main price of the revealed-input chain (`EnvFirst`) splits into the price of the outside
  slots and two factors per query.
-/

open Finset Function
open scoped BigOperators

namespace Sarkozy.BracketEnergy

variable {E : Type} [Fintype E] [DecidableEq E]

omit [DecidableEq E] in
/-- **The slots of a query** are its source and its reflected source. -/
theorem slotQuery_eq_some_iff (u : E → reservedCut.Half) (hu : Injective u) (v : Slot) (e : E) :
    slotQuery u v = some e ↔ v = (u e).1 ∨ v = reservedCut.flip (u e).1 := by
  have hflip : ∀ w : Slot, reservedCut.flip (reservedCut.flip w) = w := reservedCut.flip_flip
  unfold slotQuery
  by_cases hs : v ∈ reservedCut.half
  · simp only [hs, ↓reduceDIte]
    constructor
    · intro h1
      split at h1
      · rename_i h
        have he : h.choose = e := Option.some_inj.mp h1
        left
        have := h.choose_spec
        rw [he] at this
        rw [this]
      · exact absurd h1 (by simp)
    · rintro (h1 | h1)
      · have h : ∃ e', u e' = ⟨v, hs⟩ := ⟨e, Subtype.ext h1.symm⟩
        rw [dite_eq_left h]
        congr 1
        exact hu (h.choose_spec.trans (Subtype.ext h1))
      · exfalso
        have := reservedCut.flip_not_mem (u e).2
        rw [← h1] at this
        exact this hs
  · simp only [hs, ↓reduceDIte]
    constructor
    · intro h1
      split at h1
      · rename_i h
        have he : h.choose = e := Option.some_inj.mp h1
        right
        have := congrArg Subtype.val h.choose_spec
        rw [he] at this
        simp only at this
        rw [this, hflip]
      · exact absurd h1 (by simp)
    · rintro (h1 | h1)
      · exact absurd (h1 ▸ (u e).2) hs
      · have hv : (u e).1 = reservedCut.flip v := by rw [h1, hflip]
        have h : ∃ e', u e' = ⟨reservedCut.flip v, (reservedCut.crosses v).mpr hs⟩ :=
          ⟨e, Subtype.ext hv⟩
        rw [dite_eq_left h]
        congr 1
        exact hu (h.choose_spec.trans (Subtype.ext hv.symm))

/-- Each query has two slots. -/
theorem card_slotQuery_some (u : E → reservedCut.Half) (hu : Injective u) (e : E) :
    (univ.filter fun v : Slot => slotQuery u v = some e).card = 2 := by
  have h : (univ.filter fun v : Slot => slotQuery u v = some e) =
      {(u e).1, reservedCut.flip (u e).1} := by
    ext v
    simp only [mem_filter, mem_univ, true_and, mem_insert, mem_singleton]
    exact slotQuery_eq_some_iff u hu v e
  rw [h, card_insert_of_notMem, card_singleton]
  intro hmem
  rw [mem_singleton] at hmem
  have h2 := reservedCut.flip_not_mem (u e).2
  rw [← hmem] at h2
  exact h2 (u e).2

/-- `72 − 2|E|` slots carry `F_A`. -/
theorem card_slotQuery_none (u : E → reservedCut.Half) (hu : Injective u) :
    (univ.filter fun v : Slot => slotQuery u v = none).card + 2 * Fintype.card E = 72 := by
  have h := card_eq_sum_card_fiberwise (f := slotQuery u) (s := (univ : Finset Slot))
    (t := (univ : Finset (Option E))) (fun _ _ => mem_univ _)
  rw [card_univ, card_slot, Fintype.sum_option] at h
  simp only [card_slotQuery_some u hu, sum_const, card_univ, smul_eq_mul] at h
  omega

/-- **The product over the slots** of a function of the query: `G(none)^{72 − 2|E|}` times
`∏_e G(some e)^2`. -/
theorem prod_slotQuery {M : Type*} [CommMonoid M] (u : E → reservedCut.Half) (hu : Injective u)
    (G : Option E → M) :
    ∏ v : Slot, G (slotQuery u v) = G none ^ (72 - 2 * Fintype.card E) * ∏ e, G (some e) ^ 2 := by
  rw [← Finset.prod_fiberwise' univ (slotQuery u) G, Fintype.prod_option]
  simp only [prod_const, card_slotQuery_some u hu]
  have hn := card_slotQuery_none u hu
  congr 2
  omega

end Sarkozy.BracketEnergy
