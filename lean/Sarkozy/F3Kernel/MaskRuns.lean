module

public import Sarkozy.F3Kernel.MaskLayouts
public import Sarkozy.F3Kernel.Tree
public import Sarkozy.F3Kernel.LeafRecords

/-!
# Mask coherence along refinement runs

The partition proof and the leaf-record proof use different mask layouts. Accepted splits
preserve equality of their decoded sets; leaf steps simply remove the current cylinder.
Thus coherent roots give coherent leaves throughout accepted refinement bodies.
-/

@[expose] public section

namespace Sarkozy.F3Kernel

open Finset Sarkozy.Extraction Sarkozy.ExtractionK

theorem split_position (p : ℕ) (hx : p % 64 < 36) (hy : p / 64 < 36) :
    Nat.add (Nat.mul 64 (Nat.land p 63)) (Nat.shiftRight p 6) =
      64 * (pairOf p hx hy).1.val + (pairOf p hx hy).2.val := by
  change 64 * (p &&& (2 ^ 6 - 1)) + (p >>> 6) = 64 * (p % 64) + p / 64
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.shiftRight_eq_div_pow]

theorem step_split_state {G : Consts} (hG : G.WellFormedT)
    {st st' : St} {c : Cyl} {pay : ℕ} (hc : st.cur = some c)
    (h : step G st (4 * pay + 1) = some st') :
    ∃ (hx : pay % 64 < 36) (hy : pay / 64 < 36),
      st' = { st with
        cur := some (c.present (pairOf pay hx hy))
        stack := c.absent (pairOf pay hx hy) :: st.stack } := by
  obtain ⟨htag, hpay⟩ := split_token pay
  obtain ⟨hx, hy, _, _, _⟩ := step_split hG hc h
  refine ⟨hx, hy, ?_⟩
  unfold step at h
  simp only [htag, hpay, hc, Nat.beq_refl, Bool.cond_true] at h
  have hg : (Nat.blt pay 2304 && isEdge G pay && !bit (Nat.lor c.pt c.qt) pay) = true := by
    by_contra hne
    rw [Bool.not_eq_true] at hne
    rw [hne, Bool.cond_false] at h
    cases h
  rw [hg, Bool.cond_true, Option.some.injEq] at h
  rw [← h]
  unfold Cyl.present Cyl.absent
  rw [split_position pay hx hy]
  have hp : 64 * (pairOf pay hx hy).2.val + (pairOf pay hx hy).1.val = pay := by
    dsimp [pairOf]
    omega
  rw [hp]

theorem step_split_coherent {G : Consts} (hG : G.WellFormedT)
    {st st' : St} {c : Cyl} {pay : ℕ} (hc : st.cur = some c)
    (h : step G st (4 * pay + 1) = some st')
    (hp : ∀ d ∈ pend st, d.Coherent) : ∀ d ∈ pend st', d.Coherent := by
  obtain ⟨hx, hy, rfl⟩ := step_split_state hG hc h
  have hcur : c.Coherent := hp c (by simp [pend, hc])
  intro d hd
  simp only [pend, Option.toList_some, List.singleton_append, List.mem_cons] at hd
  rcases hd with rfl | rfl | hd
  · exact hcur.present _
  · exact hcur.absent _
  · exact hp d (by simp [pend, hc, hd])

theorem step_leaf_coherent {G : Consts} {st st' : St} {c : Cyl} {tok : ℕ}
    (ht : Nat.land tok 3 = 2) (hc : st.cur = some c) (h : step G st tok = some st')
    (hp : ∀ d ∈ pend st, d.Coherent) : ∀ d ∈ pend st', d.Coherent := by
  rw [step_leaf_pend ht hc h]
  intro d hd
  exact hp d (by simp [pend, hc, hd])

theorem run_coherent {G : Consts} (hG : G.WellFormedT) :
    ∀ (toks : List ℕ) (st st' : St),
      (∀ tok ∈ toks, Nat.land tok 3 = 1 ∨ Nat.land tok 3 = 2) →
      run G toks st = some st' → (∀ c ∈ pend st, c.Coherent) →
      (∀ c ∈ pend st', c.Coherent) ∧ (∀ c ∈ trace G toks st, c.Coherent)
  | [], st, st', _, h, hp => by
      rw [run_nil, Option.some.injEq] at h
      subst st'
      exact ⟨hp, by simp [trace]⟩
  | tok :: ts, st, st', htoks, h, hp => by
      rw [run_cons] at h
      cases hs : step G st tok with
      | none => rw [hs] at h; cases h
      | some mid =>
        rw [hs, Option.bind_some] at h
        have hts : ∀ t ∈ ts, Nat.land t 3 = 1 ∨ Nat.land t 3 = 2 :=
          fun t ht => htoks t (List.mem_cons_of_mem _ ht)
        obtain ⟨c, hc⟩ : ∃ c, st.cur = some c := by
          cases hcur : st.cur with
          | some c => exact ⟨c, rfl⟩
          | none =>
            exfalso
            unfold step at hs
            rcases htoks tok List.mem_cons_self with ht | ht
            · simp only [ht, hcur, Nat.beq_refl, Bool.cond_true] at hs
              cases hs
            · simp only [ht, hcur, show Nat.beq 2 1 = false from rfl,
                show Nat.beq 2 2 = true from rfl, Bool.cond_false, Bool.cond_true] at hs
              cases hs
        have hcur : c.Coherent := hp c (by simp [pend, hc])
        rcases htoks tok List.mem_cons_self with ht | ht
        · have htok : tok = 4 * Nat.shiftRight tok 2 + 1 := by
            rw [show Nat.shiftRight tok 2 = tok >>> 2 from rfl, Nat.shiftRight_eq_div_pow]
            rw [show Nat.land tok 3 = tok &&& (2 ^ 2 - 1) from rfl,
              Nat.and_two_pow_sub_one_eq_mod] at ht
            omega
          have hm : ∀ d ∈ pend mid, d.Coherent :=
            step_split_coherent hG hc (htok ▸ hs) hp
          have ih := run_coherent hG ts mid st' hts h hm
          refine ⟨ih.1, ?_⟩
          simpa only [trace, hs, ht, show ¬ (1 : ℕ) = 2 from by decide,
            ite_false, List.nil_append] using ih.2
        · have hm := step_leaf_coherent ht hc hs hp
          have ih := run_coherent hG ts mid st' hts h hm
          refine ⟨ih.1, ?_⟩
          intro d hd
          simp only [trace, hs, ht, ite_true, hc, Option.toList_some,
            List.singleton_append, List.mem_cons] at hd
          rcases hd with rfl | hd
          · exact hcur
          · exact ih.2 d hd

theorem step_leaf_check {G : Consts} {st st' : St} {c : Cyl} {tok : ℕ}
    (ht : Nat.land tok 3 = 2) (hc : st.cur = some c) (h : step G st tok = some st') :
    ∃ k value free, leafCheck G c (Nat.shiftRight tok 2) = some (k, value, free) := by
  unfold step at h
  simp only [ht, hc, show Nat.beq 2 1 = false from rfl,
    show Nat.beq 2 2 = true from rfl, Bool.cond_false, Bool.cond_true] at h
  split at h
  · cases h
  next k value free he => exact ⟨k, value, free, he⟩

/-- Every traced leaf comes from an actual accepted leaf check, including along runs with roots. -/
theorem run_leafChecks {G : Consts} : ∀ (toks : List ℕ) (st st' : St),
    run G toks st = some st' → ∀ c ∈ trace G toks st,
      ∃ rec k value free, leafCheck G c rec = some (k, value, free)
  | [], _, _, _, _, hc => by simp only [trace, List.not_mem_nil] at hc
  | tok :: ts, st, st', h, c, hc => by
      rw [run_cons] at h
      cases hs : step G st tok with
      | none => rw [hs] at h; cases h
      | some mid =>
        rw [hs, Option.bind_some] at h
        rw [trace, hs, List.mem_append] at hc
        rcases hc with hc | hc
        · split_ifs at hc with ht
          · have hcur : st.cur = some c := by simpa using hc
            obtain ⟨k, value, free, hleaf⟩ := step_leaf_check ht hcur hs
            exact ⟨_, k, value, free, hleaf⟩
          · cases hc
        · exact run_leafChecks ts mid st' h c hc

/-- Coherence lets a valid class in the partition's `T` layout use the record checker. -/
theorem classDatum_M_of_T {G : Consts} (hG : G.Coherent) {c : Cyl} (hc : c.Coherent)
    (h : IsClassDatum (decT G.ET) (decT c.pt, decT c.qt)) :
    IsClassDatum (decM G.EM) (decM c.pm, decM c.am) := by
  rw [hG, hc.1, hc.2]
  exact h

theorem leafCheck_LL20_valid_T {c : Cyl} {rec k value free : ℕ} (hc : c.Coherent)
    (hclass : IsClassDatum (decT LL20.ET) (decT c.pt, decT c.qt))
    (h : leafCheck LL20 c rec = some (k, value, free)) :
    ∃ R : LeafRecordData (Fin 36), R.k = k ∧
      R.Valid (decT LL20.ET) (decT c.pt, decT c.qt) := by
  obtain ⟨R, hk, hR⟩ := leafCheck_LL20_valid (classDatum_M_of_T LL20_coherent hc hclass) h
  refine ⟨R, hk, ?_⟩
  have hG : decM LL20.EM = decT LL20.ET := LL20_coherent
  rw [hG, hc.1, hc.2] at hR
  exact hR

theorem leafCheck_LL22_valid_T {c : Cyl} {rec k value free : ℕ} (hc : c.Coherent)
    (hclass : IsClassDatum (decT LL22.ET) (decT c.pt, decT c.qt))
    (h : leafCheck LL22 c rec = some (k, value, free)) :
    ∃ R : LeafRecordData (Fin 36), R.k = k ∧
      R.Valid (decT LL22.ET) (decT c.pt, decT c.qt) := by
  obtain ⟨R, hk, hR⟩ := leafCheck_LL22_valid (classDatum_M_of_T LL22_coherent hc hclass) h
  refine ⟨R, hk, ?_⟩
  have hG : decM LL22.EM = decT LL22.ET := LL22_coherent
  rw [hG, hc.1, hc.2] at hR
  exact hR

end Sarkozy.F3Kernel
