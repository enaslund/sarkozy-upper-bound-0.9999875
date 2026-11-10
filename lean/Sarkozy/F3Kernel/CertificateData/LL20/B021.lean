module

public import Sarkozy.F3Kernel.ChainAppend
public import Sarkozy.F3Kernel.CertificateData.LL20.C0672
public import Sarkozy.F3Kernel.CertificateData.LL20.C0673
public import Sarkozy.F3Kernel.CertificateData.LL20.C0674
public import Sarkozy.F3Kernel.CertificateData.LL20.C0675
public import Sarkozy.F3Kernel.CertificateData.LL20.C0676
public import Sarkozy.F3Kernel.CertificateData.LL20.C0677
public import Sarkozy.F3Kernel.CertificateData.LL20.C0678
public import Sarkozy.F3Kernel.CertificateData.LL20.C0679
public import Sarkozy.F3Kernel.CertificateData.LL20.C0680
public import Sarkozy.F3Kernel.CertificateData.LL20.C0681
public import Sarkozy.F3Kernel.CertificateData.LL20.C0682
public import Sarkozy.F3Kernel.CertificateData.LL20.C0683
public import Sarkozy.F3Kernel.CertificateData.LL20.C0684
public import Sarkozy.F3Kernel.CertificateData.LL20.C0685
public import Sarkozy.F3Kernel.CertificateData.LL20.C0686
public import Sarkozy.F3Kernel.CertificateData.LL20.C0687
public import Sarkozy.F3Kernel.CertificateData.LL20.C0688
public import Sarkozy.F3Kernel.CertificateData.LL20.C0689
public import Sarkozy.F3Kernel.CertificateData.LL20.C0690
public import Sarkozy.F3Kernel.CertificateData.LL20.C0691
public import Sarkozy.F3Kernel.CertificateData.LL20.C0692
public import Sarkozy.F3Kernel.CertificateData.LL20.C0693
public import Sarkozy.F3Kernel.CertificateData.LL20.C0694
public import Sarkozy.F3Kernel.CertificateData.LL20.C0695
public import Sarkozy.F3Kernel.CertificateData.LL20.C0696
public import Sarkozy.F3Kernel.CertificateData.LL20.C0697
public import Sarkozy.F3Kernel.CertificateData.LL20.C0698
public import Sarkozy.F3Kernel.CertificateData.LL20.C0699
public import Sarkozy.F3Kernel.CertificateData.LL20.C0700
public import Sarkozy.F3Kernel.CertificateData.LL20.C0701
public import Sarkozy.F3Kernel.CertificateData.LL20.C0702
public import Sarkozy.F3Kernel.CertificateData.LL20.C0703


@[expose] public section

set_option maxRecDepth 10000

namespace Sarkozy.F3Kernel.CertificateData.LL20.B021

open Sarkozy.F3Kernel

noncomputable def chunks : List CertificateChunk := [
  ⟨C0672.tokens, C0672.summary⟩,
  ⟨C0673.tokens, C0673.summary⟩,
  ⟨C0674.tokens, C0674.summary⟩,
  ⟨C0675.tokens, C0675.summary⟩,
  ⟨C0676.tokens, C0676.summary⟩,
  ⟨C0677.tokens, C0677.summary⟩,
  ⟨C0678.tokens, C0678.summary⟩,
  ⟨C0679.tokens, C0679.summary⟩,
  ⟨C0680.tokens, C0680.summary⟩,
  ⟨C0681.tokens, C0681.summary⟩,
  ⟨C0682.tokens, C0682.summary⟩,
  ⟨C0683.tokens, C0683.summary⟩,
  ⟨C0684.tokens, C0684.summary⟩,
  ⟨C0685.tokens, C0685.summary⟩,
  ⟨C0686.tokens, C0686.summary⟩,
  ⟨C0687.tokens, C0687.summary⟩,
  ⟨C0688.tokens, C0688.summary⟩,
  ⟨C0689.tokens, C0689.summary⟩,
  ⟨C0690.tokens, C0690.summary⟩,
  ⟨C0691.tokens, C0691.summary⟩,
  ⟨C0692.tokens, C0692.summary⟩,
  ⟨C0693.tokens, C0693.summary⟩,
  ⟨C0694.tokens, C0694.summary⟩,
  ⟨C0695.tokens, C0695.summary⟩,
  ⟨C0696.tokens, C0696.summary⟩,
  ⟨C0697.tokens, C0697.summary⟩,
  ⟨C0698.tokens, C0698.summary⟩,
  ⟨C0699.tokens, C0699.summary⟩,
  ⟨C0700.tokens, C0700.summary⟩,
  ⟨C0701.tokens, C0701.summary⟩,
  ⟨C0702.tokens, C0702.summary⟩,
  ⟨C0703.tokens, C0703.summary⟩]

theorem accepted : ChunksAccepted LL20 23810658306 chunks :=
  ⟨C0672.accepted, C0673.accepted, C0674.accepted, C0675.accepted, C0676.accepted, C0677.accepted, C0678.accepted, C0679.accepted, C0680.accepted, C0681.accepted, C0682.accepted, C0683.accepted, C0684.accepted, C0685.accepted, C0686.accepted, C0687.accepted, C0688.accepted, C0689.accepted, C0690.accepted, C0691.accepted, C0692.accepted, C0693.accepted, C0694.accepted, C0695.accepted, C0696.accepted, C0697.accepted, C0698.accepted, C0699.accepted, C0700.accepted, C0701.accepted, C0702.accepted, C0703.accepted, True.intro⟩

end Sarkozy.F3Kernel.CertificateData.LL20.B021
