module

public import Sarkozy.F3Kernel.RootSoundness

/-!
# Valid records throughout complete certificate runs

The invariant includes root tokens, as well as splits and leaves. Consequently a complete
accepted chunk supplies valid extraction records without separate hypotheses about its
root cylinders or the locations of its class boundaries.
-/

@[expose] public section

namespace Sarkozy.F3Kernel

open Finset Sarkozy.Extraction Sarkozy.ExtractionK

def Cyl.Valid (G : Consts) (c : Cyl) : Prop := c.Coherent ∧ IsClassDatum (decT G.ET) (dec c)

theorem step_current_of_tag {G : Consts} {st st' : St} {tok : ℕ}
    (ht : Nat.land tok 3 = 1 ∨ Nat.land tok 3 = 2) (h : step G st tok = some st') :
    ∃ c, st.cur = some c := by
  cases hc : st.cur with
  | some c => exact ⟨c, rfl⟩
  | none =>
    unfold step at h
    rcases ht with ht | ht
    · simp only [ht, hc, Nat.beq_refl, Bool.cond_true] at h
      cases h
    · simp only [ht, hc, show Nat.beq 2 1 = false from rfl,
        show Nat.beq 2 2 = true from rfl, Bool.cond_false, Bool.cond_true] at h
      cases h

theorem step_root_pend {G : Consts} {st st' : St} {tok : ℕ}
    (ht : Nat.land tok 3 = 0) (h : step G st tok = some st') :
    ∃ c, classRoot G (Nat.shiftRight tok 2) = some c ∧ pend st' = c :: st.stack := by
  unfold step at h
  simp only [ht, show Nat.beq 0 1 = false from rfl,
    show Nat.beq 0 2 = false from rfl, Nat.beq_refl, Bool.cond_false, Bool.cond_true] at h
  split at h
  · cases h
  · simp only [Bool.cond_eq_ite] at h
    split at h
    · split at h
      · cases h
      next c hc =>
        split at h
        · cases h
        · have he := Option.some.inj h
          refine ⟨c, hc, ?_⟩
          rw [← he]
          rfl
    · cases h

theorem step_valid {G : Consts} (hG : G.WellFormedT) (hcoh : G.Coherent)
    {st st' : St} {tok : ℕ} (h : step G st tok = some st')
    (hp : ∀ c ∈ pend st, c.Valid G) : ∀ c ∈ pend st', c.Valid G := by
  by_cases ht₁ : Nat.land tok 3 = 1
  · obtain ⟨c, hc⟩ := step_current_of_tag (Or.inl ht₁) h
    have htok : tok = 4 * Nat.shiftRight tok 2 + 1 := by
      rw [show Nat.shiftRight tok 2 = tok >>> 2 from rfl, Nat.shiftRight_eq_div_pow]
      rw [show Nat.land tok 3 = tok &&& (2 ^ 2 - 1) from rfl,
        Nat.and_two_pow_sub_one_eq_mod] at ht₁
      omega
    have hstep : step G st (4 * Nat.shiftRight tok 2 + 1) = some st' := htok ▸ h
    have hcs := step_split_coherent hG hc hstep (fun c hc => (hp c hc).1)
    obtain ⟨g, hg, c₁, c₂, hpend, he₁, he₂⟩ := step_split_pend hG hc hstep
    have hcur : c.Valid G := hp c (by simp [pend, hc])
    have hchildren := hcur.2.children hg
    intro d hd
    refine ⟨hcs d hd, ?_⟩
    rw [hpend, List.mem_cons, List.mem_cons] at hd
    rcases hd with rfl | rfl | hd
    · rw [he₁]
      exact hchildren.1
    · rw [he₂]
      exact hchildren.2
    · exact (hp d (by simp [pend, hc, hd])).2
  by_cases ht₂ : Nat.land tok 3 = 2
  · obtain ⟨c, hc⟩ := step_current_of_tag (Or.inr ht₂) h
    rw [step_leaf_pend ht₂ hc h]
    intro d hd
    exact hp d (by simp [pend, hc, hd])
  by_cases ht₀ : Nat.land tok 3 = 0
  · obtain ⟨c, hroot, hpend⟩ := step_root_pend ht₀ h
    rw [hpend]
    intro d hd
    rcases List.mem_cons.mp hd with rfl | hd
    · exact ⟨classRoot_coherent hG hcoh hroot, (classRoot_compressed hG hroot).1⟩
    · exact hp d (List.mem_append_right _ hd)
  · unfold step at h
    simp only [Bool.cond_eq_ite, Nat.beq_eq, ht₁, ht₂, ht₀, ite_false] at h
    cases h

theorem run_valid {G : Consts} (hG : G.WellFormedT) (hcoh : G.Coherent) :
    ∀ (toks : List ℕ) (st st' : St), run G toks st = some st' →
      (∀ c ∈ pend st, c.Valid G) →
      (∀ c ∈ pend st', c.Valid G) ∧ (∀ c ∈ trace G toks st, c.Valid G)
  | [], st, st', h, hp => by
      rw [run_nil, Option.some.injEq] at h
      subst st'
      exact ⟨hp, by simp [trace]⟩
  | tok :: ts, st, st', h, hp => by
      rw [run_cons] at h
      cases hs : step G st tok with
      | none => rw [hs] at h; cases h
      | some mid =>
        rw [hs, Option.bind_some] at h
        have ih := run_valid hG hcoh ts mid st' h (step_valid hG hcoh hs hp)
        refine ⟨ih.1, ?_⟩
        intro c hc
        rw [trace, hs, List.mem_append] at hc
        rcases hc with hc | hc
        · split_ifs at hc
          · exact hp c (List.mem_append_left _ hc)
          · cases hc
        · exact ih.2 c hc

theorem run_validRecords {G : Consts} (hG : G.WellFormedT) (hcoh : G.Coherent)
    (hleaf : ∀ {c : Cyl} {rec k value free : ℕ}, c.Coherent →
      IsClassDatum (decT G.ET) (dec c) → leafCheck G c rec = some (k, value, free) →
      ∃ R : LeafRecordData (Fin 36), R.k = k ∧ R.Valid (decT G.ET) (dec c))
    {toks : List ℕ} {st st' : St} (h : run G toks st = some st')
    (hp : ∀ c ∈ pend st, c.Valid G) :
    ∀ c ∈ trace G toks st, ∃ R : LeafRecordData (Fin 36), R.Valid (decT G.ET) (dec c) := by
  intro c hc
  have hv := (run_valid hG hcoh toks st st' h hp).2 c hc
  obtain ⟨rec, k, value, free, hcheck⟩ := run_leafChecks toks st st' h c hc
  obtain ⟨R, _, hR⟩ := hleaf hv.1 hv.2 hcheck
  exact ⟨R, hR⟩

def startState (last : ℕ) : St := ⟨none, [], last, 0, 0, 0, 0, 0, 0⟩

theorem chunk_run {G : Consts} {last : ℕ} {toks : List ℕ} {summary : Summary}
    (h : chunk G last toks = some summary) :
    ∃ st, run G toks (startState last) = some st ∧ pend st = [] ∧ st.cmass = st.lmass := by
  unfold chunk at h
  cases hr : run G toks (startState last) with
  | none =>
    dsimp only [startState] at hr
    rw [hr] at h
    cases h
  | some st =>
    dsimp only [startState] at hr
    rw [hr] at h
    cases hc : st.cur with
    | some c => simp only [hc] at h; cases h
    | none =>
      cases hs : st.stack with
      | cons c cs => simp only [hc, hs] at h; cases h
      | nil =>
        simp only [hc, hs, Bool.cond_eq_ite] at h
        split at h
        next hm =>
          refine ⟨st, rfl, by simp [pend, hc, hs], ?_⟩
          exact Nat.eq_of_beq_eq_true hm
        next => cases h

theorem LL20_chunk_validRecords {last : ℕ} {toks : List ℕ} {summary : Summary}
    (h : chunk LL20 last toks = some summary) :
    ∀ c ∈ trace LL20 toks (startState last),
      ∃ R : LeafRecordData (Fin 36), R.Valid (decT LL20.ET) (dec c) := by
  obtain ⟨st, hr, _, _⟩ := chunk_run h
  apply run_validRecords LL20_wellFormedT LL20_coherent leafCheck_LL20_valid_T hr
  simp [pend, startState]

theorem LL22_chunk_validRecords {last : ℕ} {toks : List ℕ} {summary : Summary}
    (h : chunk LL22 last toks = some summary) :
    ∀ c ∈ trace LL22 toks (startState last),
      ∃ R : LeafRecordData (Fin 36), R.Valid (decT LL22.ET) (dec c) := by
  obtain ⟨st, hr, _, _⟩ := chunk_run h
  apply run_validRecords LL22_wellFormedT LL22_coherent leafCheck_LL22_valid_T hr
  simp [pend, startState]

end Sarkozy.F3Kernel
