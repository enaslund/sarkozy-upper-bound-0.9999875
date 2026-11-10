module

public import Sarkozy.F3Kernel.RunRecords

/-!
# The leaf results contributing to numerical summaries

This ghost trace retains the encoded record, witness size, and checked integer value of
each consumed leaf. Its cylinder projection is exactly the partition trace already proved.
-/

@[expose] public section

namespace Sarkozy.F3Kernel

structure LeafOutput where
  cylinder : Cyl
  encoded : ℕ
  k : ℕ
  value : ℕ
  free : ℕ

noncomputable def readLeafOutput (G : Consts) (st : St) (tok : ℕ) : Option LeafOutput :=
  if Nat.land tok 3 = 2 then
    match st.cur with
    | none => none
    | some c => (leafCheck G c (Nat.shiftRight tok 2)).map
        (fun (k, value, free) => ⟨c, Nat.shiftRight tok 2, k, value, free⟩)
  else none

noncomputable def leafOutputs (G : Consts) : List ℕ → St → List LeafOutput
  | [], _ => []
  | tok :: ts, st =>
      match step G st tok with
      | none => []
      | some mid => (readLeafOutput G st tok).toList ++ leafOutputs G ts mid

theorem readLeafOutput_eq {G : Consts} {st : St} {tok : ℕ} {c : Cyl} {k value free : ℕ}
    (ht : Nat.land tok 3 = 2) (hc : st.cur = some c)
    (hl : leafCheck G c (Nat.shiftRight tok 2) = some (k, value, free)) :
    readLeafOutput G st tok = some ⟨c, Nat.shiftRight tok 2, k, value, free⟩ := by
  simp only [readLeafOutput, ht, ite_true, hc, hl, Option.map_some]

theorem readLeafOutput_sound {G : Consts} {st : St} {tok : ℕ} {o : LeafOutput}
    (h : readLeafOutput G st tok = some o) :
    Nat.land tok 3 = 2 ∧ st.cur = some o.cylinder ∧
      o.encoded = Nat.shiftRight tok 2 ∧
      leafCheck G o.cylinder o.encoded = some (o.k, o.value, o.free) := by
  unfold readLeafOutput at h
  split at h
  next ht =>
    split at h
    · cases h
    next c hc =>
      cases hl : leafCheck G c (Nat.shiftRight tok 2) with
      | none => rw [hl] at h; cases h
      | some result =>
        rcases result with ⟨k, value, free⟩
        simp only [hl, Option.map_some, Option.some.injEq] at h
        subst o
        exact ⟨ht, hc, rfl, hl⟩
  · cases h

theorem readLeafOutput_cylinders {G : Consts} {st mid : St} {tok : ℕ}
    (h : step G st tok = some mid) :
    ((readLeafOutput G st tok).toList.map LeafOutput.cylinder) =
      if Nat.land tok 3 = 2 then st.cur.toList else [] := by
  by_cases ht : Nat.land tok 3 = 2
  · obtain ⟨c, hc⟩ := step_current_of_tag (Or.inr ht) h
    obtain ⟨k, value, free, hl⟩ := step_leaf_check ht hc h
    rw [readLeafOutput_eq ht hc hl]
    simp only [Option.toList_some, List.map_cons, List.map_nil, ht, ite_true, hc]
  · simp only [readLeafOutput, ht, ite_false, Option.toList_none, List.map_nil]

theorem leafOutputs_cylinders (G : Consts) (toks : List ℕ) (st : St) :
    (leafOutputs G toks st).map LeafOutput.cylinder = trace G toks st := by
  induction toks generalizing st with
  | nil => rfl
  | cons tok ts ih =>
      cases hs : step G st tok with
      | none => simp only [leafOutputs, trace, hs, List.map_nil]
      | some mid =>
          rw [leafOutputs, trace, hs, List.map_append, readLeafOutput_cylinders hs, ih]

theorem leafOutputs_sound {G : Consts} {toks : List ℕ} {st : St} {o : LeafOutput}
    (ho : o ∈ leafOutputs G toks st) :
    leafCheck G o.cylinder o.encoded = some (o.k, o.value, o.free) := by
  induction toks generalizing st with
  | nil => cases ho
  | cons tok ts ih =>
      cases hs : step G st tok with
      | none => rw [leafOutputs, hs] at ho; cases ho
      | some mid =>
          rw [leafOutputs, hs, List.mem_append] at ho
          rcases ho with ho | ho
          · exact (readLeafOutput_sound (by simpa using ho)).2.2.2
          · exact ih ho

end Sarkozy.F3Kernel
