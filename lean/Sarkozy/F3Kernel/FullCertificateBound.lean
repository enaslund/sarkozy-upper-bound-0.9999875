module

public import Sarkozy.F3Kernel.PaperNonstarBound
public import Sarkozy.F3Kernel.ProductionCoefficients
public import Sarkozy.F3Kernel.CertificateData.LL20
public import Sarkozy.F3Kernel.CertificateData.LL22

/-!
# The complete LL20 and LL22 production nonstar certificates

All 902,545 leaves are checked by the Lean kernel. The coefficient sums and masses below
are consequences of those checks. Real factor tables and completion estimates are proved,
and the resulting inequalities use the original paper half laws at every prime p ≥ 2^60.
The Weil and four-cycle assumptions are the existing analytic inputs of the extraction theorem.
-/

@[expose] public section

namespace Sarkozy.F3Kernel

open Finset Sarkozy.Labellings Sarkozy.Extraction Sarkozy.ExtractionK

theorem LL20_full_partition :
    IsExactPartition (decT LL20.ET)
      ((chunksLeaves LL20 0 CertificateData.LL20.chunks).map dec).toFinset
      (nonstars (decT LL20.ET)) :=
  LL20_chunks_full_partition CertificateData.LL20.accepted CertificateData.LL20.mass

theorem LL20_full_accumulators {k : ℕ} (hk : k = 2 ∨ k = 3 ∨ k = 4) :
    chunksAccumulator CertificateData.LL20.chunks k = productionTotal20 k := by
  rcases hk with rfl | rfl | rfl
  · exact CertificateData.LL20.sum2
  · exact CertificateData.LL20.sum3
  · exact CertificateData.LL20.sum4

theorem LL20_full_polynomial (p : ℕ) :
    certificatePolynomial GraphData.graph20 productionAnchor 36 CertificateData.LL20.chunks
      (Real.sqrt p)⁻¹ ≤ productionPolynomial coefficientCap20 p :=
  certificatePolynomial_le_caps _ GraphData.degree20_sup _ productionTotal20 coefficientCap20
    (fun _ hk => LL20_full_accumulators hk) (fun _ hk => coefficientCap20_sound hk) p

theorem LL20_full_nonstar_bound {p : ℕ} [Fact p.Prime]
    (hW : WeilBound (ZMod p)) (hp2 : p ≠ 2) (h4 : FourCycleBound p)
    (hp : productionAnchor ≤ p)
    (hne : (injLabellings (ZMod p) SpectralD.Root.LL20.G).Nonempty)
    (f h : (SpectralD.Root.LL20.cut.Half → ZMod p) → ℝ) :
    |(SpectralD.Root.LL20.halfLaw hne).expect (fun x => f x *
      (SpectralD.Root.LL20.halfLaw hne).expect (fun y =>
        (∑ S ∈ nonstars SpectralD.Root.LL20.crossPairs,
          ∏ e ∈ S, chiPair SpectralD.Root.LL20.sgn e x y) * h y))| ≤
      productionPolynomial coefficientCap20 p *
        Real.sqrt ((SpectralD.Root.LL20.halfLaw hne).expect (fun x => f x ^ 2)) *
        Real.sqrt ((SpectralD.Root.LL20.halfLaw hne).expect (fun x => h x ^ 2)) := by
  refine (LL20_paper_nonstar_bound CertificateData.LL20.accepted CertificateData.LL20.mass
    hW hp2 h4 hp hne f h).trans ?_
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (LL20_full_polynomial p) (Real.sqrt_nonneg _))
    (Real.sqrt_nonneg _)

theorem LL22_full_partition :
    IsExactPartition (decT LL22.ET)
      ((chunksLeaves LL22 0 CertificateData.LL22.chunks).map dec).toFinset
      (nonstars (decT LL22.ET)) :=
  LL22_chunks_full_partition CertificateData.LL22.accepted CertificateData.LL22.mass

theorem LL22_full_accumulators {k : ℕ} (hk : k = 2 ∨ k = 3 ∨ k = 4) :
    chunksAccumulator CertificateData.LL22.chunks k = productionTotal22 k := by
  rcases hk with rfl | rfl | rfl
  · exact CertificateData.LL22.sum2
  · exact CertificateData.LL22.sum3
  · exact CertificateData.LL22.sum4

theorem LL22_full_polynomial (p : ℕ) :
    certificatePolynomial GraphData.graph22 productionAnchor 36 CertificateData.LL22.chunks
      (Real.sqrt p)⁻¹ ≤ productionPolynomial coefficientCap22 p :=
  certificatePolynomial_le_caps _ GraphData.degree22_sup _ productionTotal22 coefficientCap22
    (fun _ hk => LL22_full_accumulators hk) (fun _ hk => coefficientCap22_sound hk) p

theorem LL22_full_nonstar_bound {p : ℕ} [Fact p.Prime]
    (hW : WeilBound (ZMod p)) (hp2 : p ≠ 2) (h4 : FourCycleBound p)
    (hp : productionAnchor ≤ p)
    (hne : (injLabellings (ZMod p) SpectralD.Root.LL22.G).Nonempty)
    (f h : (SpectralD.Root.LL22.cut.Half → ZMod p) → ℝ) :
    |(SpectralD.Root.LL22.halfLaw hne).expect (fun x => f x *
      (SpectralD.Root.LL22.halfLaw hne).expect (fun y =>
        (∑ S ∈ nonstars SpectralD.Root.LL22.crossPairs,
          ∏ e ∈ S, chiPair SpectralD.Root.LL22.sgn e x y) * h y))| ≤
      productionPolynomial coefficientCap22 p *
        Real.sqrt ((SpectralD.Root.LL22.halfLaw hne).expect (fun x => f x ^ 2)) *
        Real.sqrt ((SpectralD.Root.LL22.halfLaw hne).expect (fun x => h x ^ 2)) := by
  refine (LL22_paper_nonstar_bound CertificateData.LL22.accepted CertificateData.LL22.mass
    hW hp2 h4 hp hne f h).trans ?_
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (LL22_full_polynomial p) (Real.sqrt_nonneg _))
    (Real.sqrt_nonneg _)

end Sarkozy.F3Kernel
