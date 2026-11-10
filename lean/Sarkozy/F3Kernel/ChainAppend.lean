module

public import Sarkozy.F3Kernel.RunSums

/-!
# Combining independently checked certificate blocks
-/

@[expose] public section

namespace Sarkozy.F3Kernel

def chunksLast : ℕ → List CertificateChunk → ℕ
  | last, [] => last
  | _, c :: cs => chunksLast c.summary.last cs

theorem chunksAccepted_append {G : Consts} {as bs : List CertificateChunk} {last : ℕ}
    (ha : ChunksAccepted G last as) (hb : ChunksAccepted G (chunksLast last as) bs) :
    ChunksAccepted G last (as ++ bs) := by
  induction as generalizing last with
  | nil => exact hb
  | cons a as ih => exact ⟨ha.1, ih ha.2 hb⟩

theorem chunksLast_append (as bs : List CertificateChunk) (last : ℕ) :
    chunksLast last (as ++ bs) = chunksLast (chunksLast last as) bs := by
  induction as generalizing last with
  | nil => rfl
  | cons a as ih => exact ih a.summary.last

theorem chunksMass_append (as bs : List CertificateChunk) :
    chunksMass (as ++ bs) = chunksMass as + chunksMass bs := by
  simp only [chunksMass, List.map_append, List.sum_append]

theorem chunksAccumulator_append (as bs : List CertificateChunk) (k : ℕ) :
    chunksAccumulator (as ++ bs) k = chunksAccumulator as k + chunksAccumulator bs k := by
  simp only [chunksAccumulator, List.map_append, List.sum_append]

end Sarkozy.F3Kernel
