module

public import Sarkozy.F3Kernel.CertificatePolynomial

/-!
# From checked certificates to the nonstar operator bound

This theorem supplies the mathematical soundness interface of the finite checker. Its
numerical inputs are acceptance of the chunks, their total mass, and the real factor-table
bounds; the analytic hypotheses are the same Weil and four-cycle inputs as the extraction
theorem. No assumption about the certificate generator enters the statement.
-/

@[expose] public section

namespace Sarkozy.F3Kernel

open Finset Sarkozy.Labellings Sarkozy.Extraction Sarkozy.ExtractionK

theorem chunks_nonstar_bound {G : Consts} (hM : MatrixWord G.EM) (hT : G.WellFormedT)
    (hcoh : G.Coherent) (htables : ValidComponentTables G)
    (H : OrientedGraph (Fin 36)) (hG : AdjacencyCounts G (graphAdj H))
    (sgn : Fin 36 → Fin 36 → ℤ) (hsgn : ∀ j k, sgn j k = 0 ∨ sgn j k = 1 ∨ sgn j k = -1)
    (hanti : ∀ j k, sgn k j = -sgn j k)
    (hEx : ∀ e ∈ decT G.ET, sgn e.1 e.2 ≠ 0)
    {q : ℝ} {n : ℕ} (hn : 36 ≤ n) (hb : GradedTableBounds G H sgn q n)
    (hsq : Real.sqrt 2 ≤ value64 G.SQ2) {cs : List CertificateChunk} {last : ℕ}
    (hc : ChunksAccepted G last cs) (hm : chunksMass cs = nonstarMass (decT G.ET))
    {p : ℕ} [Fact p.Prime] (hW : WeilBound (ZMod p)) (hp2 : p ≠ 2)
    (h4 : FourCycleBound p) (hqp : q ≤ p) (hne : (injLabellings (ZMod p) H).Nonempty)
    (f h : (Fin 36 → ZMod p) → ℝ) :
    |(graphLaw H hne).expect (fun x => f x * (graphLaw H hne).expect (fun x' =>
        (∑ S ∈ nonstars (decT G.ET), ∏ e ∈ S, chiPair sgn e x x') * h x'))| ≤
      certificatePolynomial H q n cs (Real.sqrt p)⁻¹ *
        Real.sqrt ((graphLaw H hne).expect (fun x => f x ^ 2)) *
        Real.sqrt ((graphLaw H hne).expect (fun x => h x ^ 2)) := by
  let os := chunksOutputs G last cs
  have hpart : IsExactPartition (decT G.ET) (outputsFamily os) (nonstars (decT G.ET)) := by
    unfold outputsFamily os
    rw [chunksOutputs_data]
    exact chunks_partition_of_mass hM hT hcoh hc hm
  have hvalid : ∀ d ∈ outputsFamily os,
      (outputRecordFunction G os d).Valid (decT G.ET) d := by
    apply outputRecords_valid (chunksOutputs_nodup hT hc)
    intro o ho
    exact (chunksOutput_bounds hM hT hcoh htables H hG sgn hb hsq hc ho).1
  have he := gp_extraction_leaf_partition hW hp2 h4 H sgn hsgn hanti hne
    (by simpa only [Fintype.card_fin] using hn) (decT G.ET) hEx (outputsFamily os)
    hpart (outputRecordFunction G os) hvalid hb.q_pos hqp hb.error_lt_one f h
  refine he.trans ?_
  apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
  apply mul_le_mul_of_nonneg_right _ (Real.sqrt_nonneg _)
  exact chunks_coefficientPolynomial_le hM hT hcoh htables H hG sgn hb hsq hc
    (inv_nonneg.mpr (Real.sqrt_nonneg _))

end Sarkozy.F3Kernel
