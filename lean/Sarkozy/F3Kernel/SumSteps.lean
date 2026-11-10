module

public import Sarkozy.F3Kernel.LeafOutputs
public import Sarkozy.F3Kernel.MassSteps

/-!
# Exact updates of the three coefficient accumulators
-/

@[expose] public section

namespace Sarkozy.F3Kernel

def St.accumulator (st : St) (k : ℕ) : ℕ :=
  if k = 2 then st.s2 else if k = 3 then st.s3 else if k = 4 then st.s4 else 0

def Summary.accumulator (s : Summary) (k : ℕ) : ℕ :=
  if k = 2 then s.s2 else if k = 3 then s.s3 else if k = 4 then s.s4 else 0

def LeafOutput.contribution (k : ℕ) (o : LeafOutput) : ℕ := if o.k = k then o.value else 0

theorem popNext_accumulator (st : St) (k : ℕ) :
    (popNext st).accumulator k = st.accumulator k := by
  unfold popNext
  split <;> rfl

theorem step_leaf_accumulator {G : Consts} {st st' : St} {tok : ℕ} {c : Cyl}
    {size value free : ℕ} (ht : Nat.land tok 3 = 2) (hc : st.cur = some c)
    (hl : leafCheck G c (Nat.shiftRight tok 2) = some (size, value, free))
    (h : step G st tok = some st') {k : ℕ} (hk : k = 2 ∨ k = 3 ∨ k = 4) :
    st'.accumulator k = st.accumulator k + if size = k then value else 0 := by
  unfold step at h
  simp only [ht, hc, show Nat.beq 2 1 = false from rfl,
    show Nat.beq 2 2 = true from rfl, Bool.cond_false, Bool.cond_true, hl] at h
  revert h
  cases Nat.beq _ 0 <;> simp only [Bool.cond_true, Bool.cond_false]
  · intro h
    have he := Option.some.inj h
    rw [← he, popNext_accumulator]
    rcases hk with rfl | rfl | rfl <;>
      simp only [St.accumulator, Bool.cond_eq_ite, Nat.beq_eq, ite_true,
        show ¬ (3 : ℕ) = 2 from by decide, show ¬ (4 : ℕ) = 2 from by decide,
        show ¬ (4 : ℕ) = 3 from by decide, ite_false] <;>
      split <;> simp_all
  · intro h
    cases h

theorem step_root_accumulator {G : Consts} {st st' : St} {tok : ℕ}
    (ht : Nat.land tok 3 = 0) (h : step G st tok = some st') (k : ℕ) :
    st'.accumulator k = st.accumulator k := by
  unfold step at h
  simp only [ht, show Nat.beq 0 1 = false from rfl,
    show Nat.beq 0 2 = false from rfl, Bool.cond_false, Nat.beq_refl, Bool.cond_true] at h
  simp only [Bool.cond_eq_ite] at h
  split at h
  · cases h
  · split at h
    · split at h
      · cases h
      · split at h
        · cases h
        · have he := Option.some.inj h
          rw [← he]
          rfl
    · cases h

theorem step_nonleaf_accumulator {G : Consts} (hG : G.WellFormedT)
    {st st' : St} {tok : ℕ} (ht : Nat.land tok 3 ≠ 2)
    (h : step G st tok = some st') (k : ℕ) : st'.accumulator k = st.accumulator k := by
  by_cases ht₁ : Nat.land tok 3 = 1
  · obtain ⟨c, hc⟩ := step_current_of_tag (Or.inl ht₁) h
    have htok : tok = 4 * Nat.shiftRight tok 2 + 1 := by
      rw [show Nat.shiftRight tok 2 = tok >>> 2 from rfl, Nat.shiftRight_eq_div_pow]
      rw [show Nat.land tok 3 = tok &&& (2 ^ 2 - 1) from rfl,
        Nat.and_two_pow_sub_one_eq_mod] at ht₁
      omega
    obtain ⟨_, _, rfl⟩ := step_split_state hG hc (htok ▸ h)
    rfl
  by_cases ht₀ : Nat.land tok 3 = 0
  · exact step_root_accumulator ht₀ h k
  · unfold step at h
    simp only [Bool.cond_eq_ite, Nat.beq_eq, ht₁, ht₀, ht, ite_false] at h
    cases h

theorem step_accumulator {G : Consts} (hG : G.WellFormedT)
    {st st' : St} {tok : ℕ} (h : step G st tok = some st')
    {k : ℕ} (hk : k = 2 ∨ k = 3 ∨ k = 4) :
    st'.accumulator k = st.accumulator k +
      ((readLeafOutput G st tok).toList.map (LeafOutput.contribution k)).sum := by
  by_cases ht : Nat.land tok 3 = 2
  · obtain ⟨c, hc⟩ := step_current_of_tag (Or.inr ht) h
    obtain ⟨size, value, free, hl⟩ := step_leaf_check ht hc h
    rw [readLeafOutput_eq ht hc hl]
    simpa only [Option.toList_some, List.map_cons, List.map_nil, List.sum_cons,
      List.sum_nil, Nat.add_zero, LeafOutput.contribution] using step_leaf_accumulator ht hc hl h hk
  · rw [step_nonleaf_accumulator hG ht h]
    simp only [readLeafOutput, ht, ite_false, Option.toList_none, List.map_nil,
      List.sum_nil, Nat.add_zero]

end Sarkozy.F3Kernel
