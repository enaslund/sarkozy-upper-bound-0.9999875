module

public import Sarkozy.F3Kernel.RootMaskBounds
public import Sarkozy.F3Kernel.RunRecords

/-!
# Free-degree soundness throughout accepted chunks

The raw matrix-word invariant is preserved by every accepted root, split, and leaf step.
Together with class validity and coherence, it discharges `FreeDegreeCounts` for every
leaf in any accepted LL20 or LL22 chunk.
-/

@[expose] public section

namespace Sarkozy.F3Kernel

theorem step_matrixWords {G : Consts} (hM : MatrixWord G.EM) (hT : G.WellFormedT)
    {st st' : St} {tok : ℕ} (h : step G st tok = some st')
    (hp : ∀ c ∈ pend st, c.MatrixWords) : ∀ c ∈ pend st', c.MatrixWords := by
  by_cases ht₁ : Nat.land tok 3 = 1
  · obtain ⟨c, hc⟩ := step_current_of_tag (Or.inl ht₁) h
    have htok : tok = 4 * Nat.shiftRight tok 2 + 1 := by
      rw [show Nat.shiftRight tok 2 = tok >>> 2 from rfl, Nat.shiftRight_eq_div_pow]
      rw [show Nat.land tok 3 = tok &&& (2 ^ 2 - 1) from rfl,
        Nat.and_two_pow_sub_one_eq_mod] at ht₁
      omega
    obtain ⟨hx, hy, rfl⟩ := step_split_state hT hc (htok ▸ h)
    have hcur := hp c (by simp [pend, hc])
    intro d hd
    simp only [pend, Option.toList_some, List.singleton_append, List.mem_cons] at hd
    rcases hd with rfl | rfl | hd
    · exact hcur.present _
    · exact hcur.absent _
    · exact hp d (by simp [pend, hc, hd])
  by_cases ht₂ : Nat.land tok 3 = 2
  · obtain ⟨c, hc⟩ := step_current_of_tag (Or.inr ht₂) h
    rw [step_leaf_pend ht₂ hc h]
    exact fun d hd => hp d (by simp [pend, hc, hd])
  by_cases ht₀ : Nat.land tok 3 = 0
  · obtain ⟨c, hroot, hpend⟩ := step_root_pend ht₀ h
    rw [hpend]
    intro d hd
    rcases List.mem_cons.mp hd with rfl | hd
    · exact classRoot_matrixWords hM hT hroot
    · exact hp d (List.mem_append_right _ hd)
  · unfold step at h
    simp only [Bool.cond_eq_ite, Nat.beq_eq, ht₁, ht₂, ht₀, ite_false] at h
    cases h

theorem run_matrixWords {G : Consts} (hM : MatrixWord G.EM) (hT : G.WellFormedT) :
    ∀ (toks : List ℕ) (st st' : St), run G toks st = some st' →
      (∀ c ∈ pend st, c.MatrixWords) →
      (∀ c ∈ pend st', c.MatrixWords) ∧ (∀ c ∈ trace G toks st, c.MatrixWords)
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
        have ih := run_matrixWords hM hT ts mid st' h (step_matrixWords hM hT hs hp)
        refine ⟨ih.1, ?_⟩
        intro c hc
        rw [trace, hs, List.mem_append] at hc
        rcases hc with hc | hc
        · split_ifs at hc
          · exact hp c (List.mem_append_left _ hc)
          · cases hc
        · exact ih.2 c hc

theorem chunk_freeDegreeCounts {G : Consts} (hM : MatrixWord G.EM) (hT : G.WellFormedT)
    (hG : G.Coherent) {last : ℕ} {toks : List ℕ} {summary : Summary}
    (h : chunk G last toks = some summary) :
    ∀ c ∈ trace G toks (startState last), FreeDegreeCounts G c := by
  obtain ⟨st, hr, _, _⟩ := chunk_run h
  have hv := run_valid hT hG toks (startState last) st hr (by simp [pend, startState])
  have hm := run_matrixWords hM hT toks (startState last) st hr (by simp [pend, startState])
  intro c hc
  have hcvalid := hv.2 c hc
  exact freeDegreeCounts_of_matrixWords hM hT hG (hm.2 c hc) hcvalid.1
    (classDatum_M_of_T hG hcvalid.1 hcvalid.2)

theorem LL20_chunk_freeDegreeCounts {last : ℕ} {toks : List ℕ} {summary : Summary}
    (h : chunk LL20 last toks = some summary) :
    ∀ c ∈ trace LL20 toks (startState last), FreeDegreeCounts LL20 c :=
  chunk_freeDegreeCounts LL20_matrixWordM LL20_wellFormedT LL20_coherent h

theorem LL22_chunk_freeDegreeCounts {last : ℕ} {toks : List ℕ} {summary : Summary}
    (h : chunk LL22 last toks = some summary) :
    ∀ c ∈ trace LL22 toks (startState last), FreeDegreeCounts LL22 c :=
  chunk_freeDegreeCounts LL22_matrixWordM LL22_wellFormedT LL22_coherent h

end Sarkozy.F3Kernel
