module

public import Sarkozy.F3Kernel.RootEnumeration

/-!
# An accepted chunk partitions the union of its root classes

Unopened roots are kept beside pending cylinders and completed leaves in the tiling
invariant. A root token moves its class into the pending list. The strictly increasing
keys ensure the initial root classes are pairwise disjoint.
-/

@[expose] public section

namespace Sarkozy.F3Kernel

open Finset Sarkozy.Extraction

def rootCyls (G : Consts) (toks : List ℕ) : List Cyl :=
  (rootKeys toks).filterMap (classRoot G)

def rootFamily (G : Consts) (toks : List ℕ) : Finset (Finset (Fin 36 × Fin 36)) :=
  ((rootCyls G toks).map dec).toFinset.biUnion (fun c => cls (decT G.ET) c.1 c.2)

theorem rootCyls_tiling {G : Consts} (hG : G.WellFormedT)
    {toks : List ℕ} {st st' : St} (h : run G toks st = some st') :
    Tiling (decT G.ET) ((rootCyls G toks).map dec) (rootFamily G toks) := by
  refine ⟨?_, ?_, ?_⟩
  · intro d hd
    obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hd
    obtain ⟨key, _, hkey⟩ := List.mem_filterMap.mp hc
    exact (classRoot_compressed hG hkey).1
  · change ((rootKeys toks).filterMap (classRoot G) |>.map dec).Pairwise _
    rw [List.pairwise_map, List.pairwise_filterMap]
    apply (run_rootKeys hG toks st st' h).1.imp
    intro key key' hlt c hc c' hc'
    exact classRoot_classes_disjoint hG hc hc' (ne_of_lt hlt)
  · intro S
    simp only [rootFamily, mem_biUnion, List.mem_toFinset]

theorem step_root_none {G : Consts} {st st' : St} {tok : ℕ}
    (ht : Nat.land tok 3 = 0) (h : step G st tok = some st') : st.cur = none := by
  cases hc : st.cur with
  | none => rfl
  | some c =>
    unfold step at h
    simp only [ht, hc, show Nat.beq 0 1 = false from rfl,
      show Nat.beq 0 2 = false from rfl, Nat.beq_refl, Bool.cond_false, Bool.cond_true] at h
    cases h

theorem run_tiling_roots {G : Consts} (hG : G.WellFormedT)
    {U : Finset (Finset (Fin 36 × Fin 36))} :
    ∀ (toks : List ℕ) (st st' : St) (L : List Cyl), run G toks st = some st' →
      Tiling (decT G.ET) ((pend st ++ L ++ rootCyls G toks).map dec) U →
      Tiling (decT G.ET) ((pend st' ++ (L ++ trace G toks st)).map dec) U
  | [], st, st', L, h, hT => by
      rw [run_nil, Option.some.injEq] at h
      subst st'
      simpa only [rootCyls, rootKeys, List.filterMap_nil, trace, List.append_nil] using hT
  | tok :: ts, st, st', L, h, hT => by
      rw [run_cons] at h
      cases hs : step G st tok with
      | none => rw [hs] at h; cases h
      | some mid =>
        rw [hs, Option.bind_some] at h
        have htrace : trace G (tok :: ts) st =
            (if Nat.land tok 3 = 2 then st.cur.toList else []) ++ trace G ts mid := by
          rw [trace, hs]
        by_cases ht₁ : Nat.land tok 3 = 1
        · obtain ⟨c, hc⟩ := step_current_of_tag (Or.inl ht₁) hs
          have htok : tok = 4 * Nat.shiftRight tok 2 + 1 := by
            rw [show Nat.shiftRight tok 2 = tok >>> 2 from rfl, Nat.shiftRight_eq_div_pow]
            rw [show Nat.land tok 3 = tok &&& (2 ^ 2 - 1) from rfl,
              Nat.and_two_pow_sub_one_eq_mod] at ht₁
            omega
          obtain ⟨g, hg, c₁, c₂, hp, hd₁, hd₂⟩ := step_split_pend hG hc (htok ▸ hs)
          have hr : rootCyls G (tok :: ts) = rootCyls G ts := by
            simp only [rootCyls, rootKeys, ht₁, show ¬ (1 : ℕ) = 0 from by decide, ite_false]
          have h₀ : (pend st ++ L ++ rootCyls G (tok :: ts)).map dec =
              dec c :: (st.stack ++ L ++ rootCyls G ts).map dec := by
            simp only [hr, pend, hc, Option.toList_some, List.nil_append,
              List.cons_append, List.map_cons]
          have hsplit := (h₀ ▸ hT).split hg
          have hmid : Tiling (decT G.ET) ((pend mid ++ L ++ rootCyls G ts).map dec) U := by
            rw [hp, List.cons_append, List.cons_append, List.cons_append,
              List.cons_append, List.map_cons, List.map_cons, hd₁, hd₂]
            exact hsplit
          have ih := run_tiling_roots hG ts mid st' L h hmid
          rw [htrace]
          simpa only [ht₁, show ¬ (1 : ℕ) = 2 from by decide, ite_false, List.nil_append]
            using ih
        by_cases ht₂ : Nat.land tok 3 = 2
        · obtain ⟨c, hc⟩ := step_current_of_tag (Or.inr ht₂) hs
          have hp := step_leaf_pend ht₂ hc hs
          have hr : rootCyls G (tok :: ts) = rootCyls G ts := by
            simp only [rootCyls, rootKeys, ht₂, show ¬ (2 : ℕ) = 0 from by decide, ite_false]
          have hmid : Tiling (decT G.ET)
              ((pend mid ++ (L ++ [c]) ++ rootCyls G ts).map dec) U := by
            apply hT.perm
            have h₀ : (pend st ++ L ++ rootCyls G (tok :: ts)).map dec =
                ([c] ++ (st.stack ++ L) ++ rootCyls G ts).map dec := by
              simp only [hr, pend, hc, Option.toList_some, List.nil_append,
                List.cons_append]
            have h₁ : (pend mid ++ (L ++ [c]) ++ rootCyls G ts).map dec =
                ((st.stack ++ L) ++ [c] ++ rootCyls G ts).map dec := by
              rw [hp, List.append_assoc st.stack L [c]]
            rw [h₀, h₁]
            exact (List.perm_append_comm.append_right _).map dec
          have ih := run_tiling_roots hG ts mid st' (L ++ [c]) h hmid
          rw [htrace]
          simpa only [ht₂, ite_true, hc, Option.toList_some, List.append_assoc] using ih
        by_cases ht₀ : Nat.land tok 3 = 0
        · obtain ⟨c, hc, hp⟩ := step_root_pend ht₀ hs
          have hn := step_root_none ht₀ hs
          have hr : rootCyls G (tok :: ts) = c :: rootCyls G ts := by
            simp only [rootCyls, rootKeys, ht₀, ite_true, List.filterMap_cons, hc]
          have hmid : Tiling (decT G.ET) ((pend mid ++ L ++ rootCyls G ts).map dec) U := by
            apply hT.perm
            have h₀ : (pend st ++ L ++ rootCyls G (tok :: ts)).map dec =
                ((st.stack ++ L) ++ [c] ++ rootCyls G ts).map dec := by
              simp only [hr, pend, hn, Option.toList_none, List.nil_append,
                List.append_assoc, List.singleton_append]
            have h₁ : (pend mid ++ L ++ rootCyls G ts).map dec =
                ([c] ++ (st.stack ++ L) ++ rootCyls G ts).map dec := by
              simp only [hp, List.nil_append, List.cons_append]
            rw [h₀, h₁]
            exact (List.perm_append_comm.append_right _).map dec
          have ih := run_tiling_roots hG ts mid st' L h hmid
          rw [htrace]
          simpa only [ht₀, show ¬ (0 : ℕ) = 2 from by decide, ite_false, List.nil_append]
            using ih
        · unfold step at hs
          simp only [Bool.cond_eq_ite, Nat.beq_eq, ht₁, ht₂, ht₀, ite_false] at hs
          cases hs

theorem chunk_isExactPartition {G : Consts} (hG : G.WellFormedT)
    {last : ℕ} {toks : List ℕ} {summary : Summary}
    (h : chunk G last toks = some summary) :
    IsExactPartition (decT G.ET) ((trace G toks (startState last)).map dec).toFinset
      (rootFamily G toks) := by
  obtain ⟨st, hr, hend, _⟩ := chunk_run h
  have hroots := rootCyls_tiling hG hr
  have hinit : Tiling (decT G.ET)
      ((pend (startState last) ++ [] ++ rootCyls G toks).map dec) (rootFamily G toks) := by
    simpa only [pend, startState, Option.toList_none, List.nil_append] using hroots
  have ht := run_tiling_roots hG toks (startState last) st [] hr hinit
  rw [hend, List.nil_append, List.nil_append] at ht
  exact ht.isExactPartition

theorem rootFamily_subset_nonstars (G : Consts) (hG : G.WellFormedT) (toks : List ℕ) :
    rootFamily G toks ⊆ nonstars (decT G.ET) := by
  intro S hS
  obtain ⟨d, hd, hS⟩ := mem_biUnion.mp hS
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hd)
  obtain ⟨key, _, hkey⟩ := List.mem_filterMap.mp hc
  exact classRoot_nonstars hG hkey hS

end Sarkozy.F3Kernel
