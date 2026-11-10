module

public import Sarkozy.F3Kernel.SumSteps
public import Sarkozy.F3Kernel.ChainCoverage

/-!
# Exact coefficient sums across runs and chunk chains

The three reported integer accumulators are precisely the sums of the checked leaf values
of witness sizes two, three, and four. Chunk boundaries preserve these identities by addition.
-/

@[expose] public section

namespace Sarkozy.F3Kernel

theorem run_accumulator {G : Consts} (hG : G.WellFormedT)
    {k : ℕ} (hk : k = 2 ∨ k = 3 ∨ k = 4) :
    ∀ (toks : List ℕ) (st st' : St), run G toks st = some st' →
      st'.accumulator k = st.accumulator k +
        ((leafOutputs G toks st).map (LeafOutput.contribution k)).sum
  | [], st, st', h => by
      rw [run_nil, Option.some.injEq] at h
      subst st'
      simp only [leafOutputs, List.map_nil, List.sum_nil, Nat.add_zero]
  | tok :: ts, st, st', h => by
      rw [run_cons] at h
      cases hs : step G st tok with
      | none => rw [hs] at h; cases h
      | some mid =>
        rw [hs, Option.bind_some] at h
        rw [run_accumulator hG hk ts mid st' h, step_accumulator hG hs hk,
          leafOutputs, hs, List.map_append, List.sum_append, Nat.add_assoc]

theorem chunk_summary_accumulator {G : Consts} {last : ℕ} {toks : List ℕ} {summary : Summary}
    (h : chunk G last toks = some summary) {st : St}
    (hr : run G toks (startState last) = some st) (k : ℕ) :
    summary.accumulator k = st.accumulator k := by
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

theorem chunk_accumulator {G : Consts} (hG : G.WellFormedT)
    {last : ℕ} {toks : List ℕ} {summary : Summary} (h : chunk G last toks = some summary)
    {k : ℕ} (hk : k = 2 ∨ k = 3 ∨ k = 4) : summary.accumulator k =
      ((leafOutputs G toks (startState last)).map (LeafOutput.contribution k)).sum := by
  obtain ⟨st, hr, _, _⟩ := chunk_run h
  rw [chunk_summary_accumulator h hr, run_accumulator hG hk toks _ _ hr]
  simp only [St.accumulator, startState, ite_self, Nat.zero_add]

noncomputable def chunksOutputs (G : Consts) : ℕ → List CertificateChunk → List LeafOutput
  | _, [] => []
  | last, c :: cs => leafOutputs G c.tokens (startState last) ++ chunksOutputs G c.summary.last cs

def chunksAccumulator (cs : List CertificateChunk) (k : ℕ) : ℕ :=
  (cs.map (fun c => c.summary.accumulator k)).sum

theorem chunksOutputs_cylinders (G : Consts) (cs : List CertificateChunk) (last : ℕ) :
    (chunksOutputs G last cs).map LeafOutput.cylinder = chunksLeaves G last cs := by
  induction cs generalizing last with
  | nil => rfl
  | cons c cs ih =>
      simp only [chunksOutputs, chunksLeaves, List.map_append, leafOutputs_cylinders, ih]

theorem chunksOutputs_sound {G : Consts} {cs : List CertificateChunk} {last : ℕ} {o : LeafOutput}
    (ho : o ∈ chunksOutputs G last cs) :
    leafCheck G o.cylinder o.encoded = some (o.k, o.value, o.free) := by
  induction cs generalizing last with
  | nil => cases ho
  | cons c cs ih =>
      rcases List.mem_append.mp ho with ho | ho
      · exact leafOutputs_sound ho
      · exact ih ho

theorem chunks_accumulator {G : Consts} (hG : G.WellFormedT) {cs : List CertificateChunk}
    {last : ℕ} (h : ChunksAccepted G last cs) {k : ℕ} (hk : k = 2 ∨ k = 3 ∨ k = 4) :
    chunksAccumulator cs k =
      ((chunksOutputs G last cs).map (LeafOutput.contribution k)).sum := by
  induction cs generalizing last with
  | nil => rfl
  | cons c cs ih =>
      change c.summary.accumulator k + chunksAccumulator cs k = _
      rw [chunksOutputs, List.map_append, List.sum_append, chunk_accumulator hG h.1 hk, ih h.2]

end Sarkozy.F3Kernel
