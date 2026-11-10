module

public import Sarkozy.F3Kernel.RootKeys
public import Sarkozy.F3Kernel.RunRecords

/-!
# The root-key enumeration in an accepted run

The machine's `last` field enforces strictly increasing root keys. Every enumerated key is
accepted by `classRoot`, so the root classes are pairwise disjoint by key injectivity.
-/

@[expose] public section

namespace Sarkozy.F3Kernel

open Finset Sarkozy.Extraction

def rootKeys : List ℕ → List ℕ
  | [] => []
  | tok :: ts =>
      if Nat.land tok 3 = 0 then Nat.shiftRight tok 2 :: rootKeys ts else rootKeys ts

theorem step_leaf_last {G : Consts} {st st' : St} {tok : ℕ}
    (ht : Nat.land tok 3 = 2) (h : step G st tok = some st') : st'.last = st.last := by
  obtain ⟨c, hc⟩ := step_current_of_tag (Or.inr ht) h
  unfold step at h
  simp only [ht, hc, show Nat.beq 2 1 = false from rfl,
    show Nat.beq 2 2 = true from rfl, Bool.cond_false, Bool.cond_true] at h
  split at h
  · cases h
  · revert h
    cases Nat.beq _ 0 <;> simp only [Bool.cond_true, Bool.cond_false]
    · intro h
      have hs := Option.some.inj h
      rw [← hs]
      unfold popNext
      split <;> rfl
    · intro h
      cases h

theorem step_root_last {G : Consts} {st st' : St} {tok : ℕ}
    (ht : Nat.land tok 3 = 0) (h : step G st tok = some st') :
    st.last ≤ Nat.shiftRight tok 2 ∧ st'.last = Nat.shiftRight tok 2 + 1 := by
  unfold step at h
  simp only [ht, show Nat.beq 0 1 = false from rfl,
    show Nat.beq 0 2 = false from rfl, Nat.beq_refl, Bool.cond_false, Bool.cond_true] at h
  split at h
  · cases h
  · simp only [Bool.cond_eq_ite] at h
    split at h
    next hle =>
      split at h
      · cases h
      · split at h
        · cases h
        · have hs := Option.some.inj h
          exact ⟨Nat.le_of_ble_eq_true hle, by rw [← hs]⟩
    next => cases h

theorem step_last_mono {G : Consts} (hG : G.WellFormedT)
    {st st' : St} {tok : ℕ} (h : step G st tok = some st') : st.last ≤ st'.last := by
  by_cases ht₁ : Nat.land tok 3 = 1
  · obtain ⟨c, hc⟩ := step_current_of_tag (Or.inl ht₁) h
    have htok : tok = 4 * Nat.shiftRight tok 2 + 1 := by
      rw [show Nat.shiftRight tok 2 = tok >>> 2 from rfl, Nat.shiftRight_eq_div_pow]
      rw [show Nat.land tok 3 = tok &&& (2 ^ 2 - 1) from rfl,
        Nat.and_two_pow_sub_one_eq_mod] at ht₁
      omega
    obtain ⟨_, _, rfl⟩ := step_split_state hG hc (htok ▸ h)
    exact le_rfl
  by_cases ht₂ : Nat.land tok 3 = 2
  · rw [step_leaf_last ht₂ h]
  by_cases ht₀ : Nat.land tok 3 = 0
  · have hr := step_root_last ht₀ h
    omega
  · unfold step at h
    simp only [Bool.cond_eq_ite, Nat.beq_eq, ht₁, ht₂, ht₀, ite_false] at h
    cases h

theorem run_rootKeys {G : Consts} (hG : G.WellFormedT) :
    ∀ (toks : List ℕ) (st st' : St), run G toks st = some st' →
      (rootKeys toks).Pairwise (· < ·) ∧
      (∀ key ∈ rootKeys toks, st.last ≤ key) ∧
      (∀ key ∈ rootKeys toks, ∃ c, classRoot G key = some c)
  | [], _, _, _ => by simp [rootKeys]
  | tok :: ts, st, st', h => by
      rw [run_cons] at h
      cases hs : step G st tok with
      | none => rw [hs] at h; cases h
      | some mid =>
        rw [hs, Option.bind_some] at h
        have ih := run_rootKeys hG ts mid st' h
        have hmono := step_last_mono hG hs
        by_cases ht : Nat.land tok 3 = 0
        · have hr := step_root_last ht hs
          obtain ⟨c, hc, _⟩ := step_root_pend ht hs
          simp only [rootKeys, ht, ite_true]
          refine ⟨List.pairwise_cons.mpr ⟨?_, ih.1⟩, ?_, ?_⟩
          · intro key hk
            have hle := ih.2.1 key hk
            omega
          · intro key hk
            rcases List.mem_cons.mp hk with rfl | hk
            · exact hr.1
            · exact hmono.trans (ih.2.1 key hk)
          · intro key hk
            rcases List.mem_cons.mp hk with rfl | hk
            · exact ⟨c, hc⟩
            · exact ih.2.2 key hk
        · simp only [rootKeys, ht, ite_false]
          exact ⟨ih.1, fun key hk => hmono.trans (ih.2.1 key hk), ih.2.2⟩

theorem run_rootKeys_disjoint {G : Consts} (hG : G.WellFormedT)
    {toks : List ℕ} {st st' : St} (h : run G toks st = some st') :
    (rootKeys toks).Pairwise (fun key key' =>
      ∀ c c', classRoot G key = some c → classRoot G key' = some c' →
        Disjoint (cls (decT G.ET) (dec c).1 (dec c).2)
          (cls (decT G.ET) (dec c').1 (dec c').2)) := by
  apply (run_rootKeys hG toks st st' h).1.imp
  intro key key' hlt c c' hc hc'
  exact classRoot_classes_disjoint hG hc hc' (ne_of_lt hlt)

end Sarkozy.F3Kernel
