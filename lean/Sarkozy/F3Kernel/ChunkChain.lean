module

public import Sarkozy.F3Kernel.TilingAppend

/-!
# Certificates checked in a sequence of bounded-size chunks

Each chunk starts at the previous summary's last-key bound. Its numeric accumulators may
start at zero, while the key bound preserves disjointness across the whole certificate.
-/

@[expose] public section

namespace Sarkozy.F3Kernel

open Finset Sarkozy.Extraction

structure CertificateChunk where
  tokens : List ℕ
  summary : Summary

def ChunksAccepted (G : Consts) : ℕ → List CertificateChunk → Prop
  | _, [] => True
  | last, c :: cs => chunk G last c.tokens = some c.summary ∧ ChunksAccepted G c.summary.last cs

def chunksKeys : List CertificateChunk → List ℕ
  | [] => []
  | c :: cs => rootKeys c.tokens ++ chunksKeys cs

def chunksFamily (G : Consts) : List CertificateChunk → Finset (Finset (Fin 36 × Fin 36))
  | [] => ∅
  | c :: cs => rootFamily G c.tokens ∪ chunksFamily G cs

noncomputable def chunksLeaves (G : Consts) : ℕ → List CertificateChunk → List Cyl
  | _, [] => []
  | last, c :: cs => trace G c.tokens (startState last) ++ chunksLeaves G c.summary.last cs

def chunksMass (cs : List CertificateChunk) : ℕ := (cs.map (fun c => c.summary.mass)).sum

theorem chunksKeys_lower {G : Consts} (hG : G.WellFormedT) {cs : List CertificateChunk}
    {last : ℕ} (h : ChunksAccepted G last cs) : ∀ key ∈ chunksKeys cs, last ≤ key := by
  induction cs generalizing last with
  | nil => simp [chunksKeys]
  | cons c cs ih =>
      intro key hk
      rcases List.mem_append.mp hk with hk | hk
      · exact (chunk_rootKeys_bounds hG h.1 hk).1
      · exact (chunk_last_mono hG h.1).trans (ih h.2 key hk)

theorem chunksFamily_member_key {G : Consts} {cs : List CertificateChunk}
    {S : Finset (Fin 36 × Fin 36)} (hS : S ∈ chunksFamily G cs) :
    ∃ key ∈ chunksKeys cs, ∃ c, classRoot G key = some c ∧
      S ∈ cls (decT G.ET) (dec c).1 (dec c).2 := by
  induction cs with
  | nil => cases hS
  | cons c cs ih =>
      rcases mem_union.mp hS with hS | hS
      · obtain ⟨key, hk, d, hd, hS⟩ := rootFamily_member_key hS
        exact ⟨key, List.mem_append_left _ hk, d, hd, hS⟩
      · obtain ⟨key, hk, d, hd, hS⟩ := ih hS
        exact ⟨key, List.mem_append_right _ hk, d, hd, hS⟩

theorem chunksFamily_head_disjoint {G : Consts} (hG : G.WellFormedT)
    {last : ℕ} {c : CertificateChunk} {cs : List CertificateChunk}
    (h : ChunksAccepted G last (c :: cs)) :
    Disjoint (rootFamily G c.tokens) (chunksFamily G cs) := by
  rw [disjoint_left]
  intro S hS hS'
  obtain ⟨a, ha, d, hd, hSd⟩ := rootFamily_member_key hS
  obtain ⟨b, hb, e, he, hSe⟩ := chunksFamily_member_key hS'
  have hab : a < b := (chunk_rootKeys_bounds hG h.1 ha).2.trans_le
    (chunksKeys_lower hG h.2 b hb)
  exact disjoint_left.mp (classRoot_classes_disjoint hG hd he (ne_of_lt hab)) hSd hSe

theorem chunksFamily_subset_nonstars (G : Consts) (hG : G.WellFormedT)
    (cs : List CertificateChunk) : chunksFamily G cs ⊆ nonstars (decT G.ET) := by
  induction cs with
  | nil => exact empty_subset _
  | cons c cs ih => exact union_subset (rootFamily_subset_nonstars G hG c.tokens) ih

end Sarkozy.F3Kernel
