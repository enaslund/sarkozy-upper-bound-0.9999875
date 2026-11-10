module

public import Sarkozy.F3Kernel.OutputRecords

/-!
# Assigning a checked record to each partition class

Disjointness of the checked leaves makes the assignment independent of list position.
-/

@[expose] public section

namespace Sarkozy.F3Kernel

open Finset Sarkozy.Extraction Sarkozy.ExtractionK

def LeafOutput.datum (o : LeafOutput) := dec o.cylinder

def outputsFamily (os : List LeafOutput) := (os.map LeafOutput.datum).toFinset

noncomputable def outputRecordFunction (G : Consts) (os : List LeafOutput) :
    (Finset (Fin 36 × Fin 36) × Finset (Fin 36 × Fin 36)) → LeafRecordData (Fin 36) :=
  Function.extend (fun o : {o // o ∈ os} => o.val.datum)
    (fun o => o.val.mathRecord G) (fun _ => emptyRecord)

theorem outputRecordFunction_apply {G : Consts} {os : List LeafOutput}
    (hn : (os.map LeafOutput.datum).Nodup) {o : LeafOutput} (ho : o ∈ os) :
    outputRecordFunction G os o.datum = o.mathRecord G := by
  have hi : Function.Injective (fun o : {o // o ∈ os} => o.val.datum) := by
    intro a b he
    exact Subtype.ext (List.inj_on_of_nodup_map hn a.property b.property he)
  exact hi.extend_apply _ _ ⟨o, ho⟩

theorem chunksOutputs_data (G : Consts) (cs : List CertificateChunk) (last : ℕ) :
    (chunksOutputs G last cs).map LeafOutput.datum =
      (chunksLeaves G last cs).map dec := by
  rw [← chunksOutputs_cylinders, List.map_map]
  rfl

theorem chunksOutputs_nodup {G : Consts} (hT : G.WellFormedT)
    {cs : List CertificateChunk} {last : ℕ} (h : ChunksAccepted G last cs) :
    ((chunksOutputs G last cs).map LeafOutput.datum).Nodup := by
  rw [chunksOutputs_data]
  exact (chunks_tiling hT h).nodup

theorem sum_outputsFamily {os : List LeafOutput}
    (hn : (os.map LeafOutput.datum).Nodup)
    (f : (Finset (Fin 36 × Fin 36) × Finset (Fin 36 × Fin 36)) → ℝ) :
    ∑ d ∈ outputsFamily os, f d = (os.map (fun o => f o.datum)).sum := by
  rw [outputsFamily, List.sum_toFinset f hn, List.map_map]
  rfl

theorem outputRecords_valid {G : Consts} {os : List LeafOutput}
    (hn : (os.map LeafOutput.datum).Nodup) (Ex : Finset (Fin 36 × Fin 36))
    (hv : ∀ o ∈ os, (o.mathRecord G).Valid Ex o.datum)
    {d : Finset (Fin 36 × Fin 36) × Finset (Fin 36 × Fin 36)}
    (hd : d ∈ outputsFamily os) : (outputRecordFunction G os d).Valid Ex d := by
  obtain ⟨o, ho, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hd)
  rw [outputRecordFunction_apply hn ho]
  exact hv o ho

theorem outputRecords_size {G : Consts} {os : List LeafOutput}
    (hn : (os.map LeafOutput.datum).Nodup)
    (hs : ∀ o ∈ os, leafCheck G o.cylinder o.encoded = some (o.k, o.value, o.free))
    {d : Finset (Fin 36 × Fin 36) × Finset (Fin 36 × Fin 36)}
    (hd : d ∈ outputsFamily os) :
    (outputRecordFunction G os d).k = 2 ∨ (outputRecordFunction G os d).k = 3 ∨
      (outputRecordFunction G os d).k = 4 := by
  obtain ⟨o, ho, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp hd)
  rw [outputRecordFunction_apply hn ho, LeafOutput.mathRecord_size (hs o ho)]
  exact (o.checkedTrace G (hs o ho)).admissible

end Sarkozy.F3Kernel
