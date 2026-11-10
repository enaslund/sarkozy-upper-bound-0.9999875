module

public import Sarkozy.F3Kernel.RunMass

/-!
# Root-key intervals and tilings for separate accepted chunks

The last key in a summary is a strict upper bound for every root key in its chunk. Thus
chunks checked in sequence cannot repeat a root class.
-/

@[expose] public section

namespace Sarkozy.F3Kernel

theorem run_last_mono {G : Consts} (hG : G.WellFormedT) :
    ∀ (toks : List ℕ) (st st' : St), run G toks st = some st' → st.last ≤ st'.last
  | [], st, st', h => by
      rw [run_nil, Option.some.injEq] at h
      subst st'
      rfl
  | tok :: ts, st, st', h => by
      rw [run_cons] at h
      cases hs : step G st tok with
      | none => rw [hs] at h; cases h
      | some mid =>
        rw [hs, Option.bind_some] at h
        exact (step_last_mono hG hs).trans (run_last_mono hG ts mid st' h)

theorem run_rootKeys_lt_last {G : Consts} (hG : G.WellFormedT) :
    ∀ (toks : List ℕ) (st st' : St), run G toks st = some st' →
      ∀ key ∈ rootKeys toks, key < st'.last
  | [], _, _, _, _, hk => by cases hk
  | tok :: ts, st, st', h, key, hk => by
      rw [run_cons] at h
      cases hs : step G st tok with
      | none => rw [hs] at h; cases h
      | some mid =>
        rw [hs, Option.bind_some] at h
        by_cases ht : Nat.land tok 3 = 0
        · simp only [rootKeys, ht, ite_true, List.mem_cons] at hk
          rcases hk with rfl | hk
          · have hr := (step_root_last ht hs).2
            have hm := run_last_mono hG ts mid st' h
            omega
          · exact run_rootKeys_lt_last hG ts mid st' h key hk
        · simp only [rootKeys, ht, ite_false] at hk
          exact run_rootKeys_lt_last hG ts mid st' h key hk

theorem chunk_summary_last {G : Consts} {last : ℕ} {toks : List ℕ} {summary : Summary}
    (h : chunk G last toks = some summary) {st : St}
    (hr : run G toks (startState last) = some st) : summary.last = st.last := by
  unfold chunk at h
  dsimp only [startState] at hr
  rw [hr] at h
  simp only [Bool.cond_eq_ite] at h
  split at h
  · split at h
    · cases h
      rfl
    · cases h
  · cases h

theorem chunk_last_mono {G : Consts} (hG : G.WellFormedT)
    {last : ℕ} {toks : List ℕ} {summary : Summary}
    (h : chunk G last toks = some summary) : last ≤ summary.last := by
  obtain ⟨st, hr, _, _⟩ := chunk_run h
  rw [chunk_summary_last h hr]
  exact run_last_mono hG toks _ _ hr

theorem chunk_rootKeys_bounds {G : Consts} (hG : G.WellFormedT)
    {last : ℕ} {toks : List ℕ} {summary : Summary}
    (h : chunk G last toks = some summary) {key : ℕ} (hk : key ∈ rootKeys toks) :
    last ≤ key ∧ key < summary.last := by
  obtain ⟨st, hr, _, _⟩ := chunk_run h
  rw [chunk_summary_last h hr]
  exact ⟨(run_rootKeys hG toks _ _ hr).2.1 key hk,
    run_rootKeys_lt_last hG toks _ _ hr key hk⟩

theorem chunk_tiling {G : Consts} (hG : G.WellFormedT)
    {last : ℕ} {toks : List ℕ} {summary : Summary}
    (h : chunk G last toks = some summary) :
    Tiling (decT G.ET) ((trace G toks (startState last)).map dec) (rootFamily G toks) := by
  obtain ⟨st, hr, hend, _⟩ := chunk_run h
  have hroots := rootCyls_tiling hG hr
  have hinit : Tiling (decT G.ET) ((pend (startState last) ++ [] ++ rootCyls G toks).map dec)
      (rootFamily G toks) := by
    simpa only [pend, startState, Option.toList_none, List.nil_append] using hroots
  have ht := run_tiling_roots hG toks (startState last) st [] hr hinit
  simpa only [hend, List.nil_append] using ht

end Sarkozy.F3Kernel
