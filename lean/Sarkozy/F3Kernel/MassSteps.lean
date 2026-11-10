module

public import Sarkozy.F3Kernel.FreeTotals
public import Sarkozy.F3Kernel.RootEnumeration

/-!
# Exact updates of the checker's root-mass accumulator
-/

@[expose] public section

namespace Sarkozy.F3Kernel

theorem step_leaf_cmass {G : Consts} {st st' : St} {tok : ℕ}
    (ht : Nat.land tok 3 = 2) (h : step G st tok = some st') : st'.cmass = st.cmass := by
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

theorem step_nonroot_cmass {G : Consts} (hG : G.WellFormedT)
    {st st' : St} {tok : ℕ} (ht : Nat.land tok 3 ≠ 0)
    (h : step G st tok = some st') : st'.cmass = st.cmass := by
  by_cases ht₁ : Nat.land tok 3 = 1
  · obtain ⟨c, hc⟩ := step_current_of_tag (Or.inl ht₁) h
    have htok : tok = 4 * Nat.shiftRight tok 2 + 1 := by
      rw [show Nat.shiftRight tok 2 = tok >>> 2 from rfl, Nat.shiftRight_eq_div_pow]
      rw [show Nat.land tok 3 = tok &&& (2 ^ 2 - 1) from rfl,
        Nat.and_two_pow_sub_one_eq_mod] at ht₁
      omega
    obtain ⟨_, _, rfl⟩ := step_split_state hG hc (htok ▸ h)
    rfl
  by_cases ht₂ : Nat.land tok 3 = 2
  · exact step_leaf_cmass ht₂ h
  · unfold step at h
    simp only [Bool.cond_eq_ite, Nat.beq_eq, ht₁, ht₂, ht, ite_false] at h
    cases h

theorem step_root_cmass_raw {G : Consts} {st st' : St} {tok : ℕ}
    (ht : Nat.land tok 3 = 0) (h : step G st tok = some st') :
    ∃ c, classRoot G (Nat.shiftRight tok 2) = some c ∧
      st'.cmass = st.cmass + 2 ^ horizontalSum (freeRows G c) := by
  unfold step at h
  simp only [ht, show Nat.beq 0 1 = false from rfl,
    show Nat.beq 0 2 = false from rfl, Bool.cond_false, Nat.beq_refl, Bool.cond_true] at h
  simp only [Bool.cond_eq_ite] at h
  split at h
  · cases h
  · split at h
    · split at h
      · cases h
      next c hc =>
        split at h
        · cases h
        · have he := Option.some.inj h
          refine ⟨c, hc, ?_⟩
          rw [← he]
          change st.cmass + (1 <<< horizontalSum (freeRows G c)) = _
          rw [Nat.shiftLeft_eq, Nat.one_mul]
    · cases h

theorem step_root_cmass {G : Consts} (hM : MatrixWord G.EM) (hT : G.WellFormedT)
    (hG : G.Coherent) {st st' : St} {tok : ℕ}
    (ht : Nat.land tok 3 = 0) (h : step G st tok = some st') :
    ∃ c, classRoot G (Nat.shiftRight tok 2) = some c ∧
      st'.cmass = st.cmass + 2 ^ (freePairs G c).card := by
  obtain ⟨c, hc, hm⟩ := step_root_cmass_raw ht h
  rw [classRoot_freeCount hM hT hG hc] at hm
  exact ⟨c, hc, hm⟩

end Sarkozy.F3Kernel
