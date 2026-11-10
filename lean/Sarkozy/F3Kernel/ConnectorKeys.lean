module

public import Sarkozy.F3Kernel.Connectors

/-!
# Recovering a connector decision from the present mask

For a connector that was not already present, an accepted decision is one precisely when
the resulting present mask contains it. Other edges retain their presence status.
-/

@[expose] public section

namespace Sarkozy.F3Kernel

open Finset Sarkozy.Extraction

theorem connector_one_iff_present {G : Consts} {c d : Cyl} (e : Fin 36 × Fin 36) {q : ℕ}
    (hP : e ∉ decT c.pt) (h : connector G c e.1.val e.2.val q = some d) :
    q = 1 ↔ e ∈ decT d.pt := by
  unfold connector at h
  dsimp only at h
  simp only [Bool.cond_eq_ite] at h
  split at h
  · split at h
    next hq =>
      have hd : c.present e = d := Option.some.inj h
      rw [← hd]
      change q = 1 ↔ e ∈ decT (Nat.lor c.pt (Nat.shiftLeft 1 (64 * e.2.val + e.1.val)))
      rw [decT_insert, mem_insert]
      exact ⟨fun _ => Or.inl rfl, fun _ => Nat.eq_of_beq_eq_true hq⟩
    next hq =>
      have hd : c.absent e = d := Option.some.inj h
      rw [← hd]
      change q = 1 ↔ e ∈ decT c.pt
      have hq' : q ≠ 1 := fun heq => hq (heq ▸ Nat.beq_refl 1)
      simp only [hq', hP]
  · split at h
    next hq =>
      have hd : c = d := Option.some.inj h
      rw [← hd, Nat.eq_of_beq_eq_true hq]
      simp only [show ¬ (0 : ℕ) = 1 from by decide, hP]
    next => cases h

theorem connector_other_present {G : Consts} {c d : Cyl} (e v : Fin 36 × Fin 36) {q : ℕ}
    (hne : v ≠ e) (h : connector G c e.1.val e.2.val q = some d) :
    v ∈ decT d.pt ↔ v ∈ decT c.pt := by
  have hb := (connector_change e h).bounds
  constructor
  · intro hv
    rcases hb.addedP v hv with hv | ⟨heq, _⟩
    · exact hv
    · exact False.elim (hne heq)
  · exact fun hv => hb.monoP hv

theorem corners_not_present {e f : Fin 36 × Fin 36} (hdis : PairDisj e f) :
    (e.1, f.2) ∉ ({e, f} : Finset _) ∧
    (f.1, e.2) ∉ ({e, f} : Finset _) ∧ (e.1, f.2) ≠ (f.1, e.2) := by
  simp only [mem_insert, mem_singleton, not_or]
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ?_⟩
  · intro h
    exact hdis.2 (congrArg Prod.snd h).symm
  · intro h
    have hh := congrArg Prod.fst h
    exact hdis.1 hh
  · intro h
    exact hdis.1 (congrArg Prod.fst h).symm
  · intro h
    have hh := congrArg Prod.snd h
    exact hdis.2 hh
  · intro h
    have hh := congrArg Prod.fst h
    exact hdis.1 hh

end Sarkozy.F3Kernel
