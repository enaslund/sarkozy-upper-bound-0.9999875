module

public import Sarkozy.F3Kernel.ChainAppend
public import Sarkozy.F3Kernel.CertificateData.LL20.C0640
public import Sarkozy.F3Kernel.CertificateData.LL20.C0641
public import Sarkozy.F3Kernel.CertificateData.LL20.C0642
public import Sarkozy.F3Kernel.CertificateData.LL20.C0643
public import Sarkozy.F3Kernel.CertificateData.LL20.C0644
public import Sarkozy.F3Kernel.CertificateData.LL20.C0645
public import Sarkozy.F3Kernel.CertificateData.LL20.C0646
public import Sarkozy.F3Kernel.CertificateData.LL20.C0647
public import Sarkozy.F3Kernel.CertificateData.LL20.C0648
public import Sarkozy.F3Kernel.CertificateData.LL20.C0649
public import Sarkozy.F3Kernel.CertificateData.LL20.C0650
public import Sarkozy.F3Kernel.CertificateData.LL20.C0651
public import Sarkozy.F3Kernel.CertificateData.LL20.C0652
public import Sarkozy.F3Kernel.CertificateData.LL20.C0653
public import Sarkozy.F3Kernel.CertificateData.LL20.C0654
public import Sarkozy.F3Kernel.CertificateData.LL20.C0655
public import Sarkozy.F3Kernel.CertificateData.LL20.C0656
public import Sarkozy.F3Kernel.CertificateData.LL20.C0657
public import Sarkozy.F3Kernel.CertificateData.LL20.C0658
public import Sarkozy.F3Kernel.CertificateData.LL20.C0659
public import Sarkozy.F3Kernel.CertificateData.LL20.C0660
public import Sarkozy.F3Kernel.CertificateData.LL20.C0661
public import Sarkozy.F3Kernel.CertificateData.LL20.C0662
public import Sarkozy.F3Kernel.CertificateData.LL20.C0663
public import Sarkozy.F3Kernel.CertificateData.LL20.C0664
public import Sarkozy.F3Kernel.CertificateData.LL20.C0665
public import Sarkozy.F3Kernel.CertificateData.LL20.C0666
public import Sarkozy.F3Kernel.CertificateData.LL20.C0667
public import Sarkozy.F3Kernel.CertificateData.LL20.C0668
public import Sarkozy.F3Kernel.CertificateData.LL20.C0669
public import Sarkozy.F3Kernel.CertificateData.LL20.C0670
public import Sarkozy.F3Kernel.CertificateData.LL20.C0671


@[expose] public section

set_option maxRecDepth 10000

namespace Sarkozy.F3Kernel.CertificateData.LL20.B020

open Sarkozy.F3Kernel

noncomputable def chunks : List CertificateChunk := [
  ⟨C0640.tokens, C0640.summary⟩,
  ⟨C0641.tokens, C0641.summary⟩,
  ⟨C0642.tokens, C0642.summary⟩,
  ⟨C0643.tokens, C0643.summary⟩,
  ⟨C0644.tokens, C0644.summary⟩,
  ⟨C0645.tokens, C0645.summary⟩,
  ⟨C0646.tokens, C0646.summary⟩,
  ⟨C0647.tokens, C0647.summary⟩,
  ⟨C0648.tokens, C0648.summary⟩,
  ⟨C0649.tokens, C0649.summary⟩,
  ⟨C0650.tokens, C0650.summary⟩,
  ⟨C0651.tokens, C0651.summary⟩,
  ⟨C0652.tokens, C0652.summary⟩,
  ⟨C0653.tokens, C0653.summary⟩,
  ⟨C0654.tokens, C0654.summary⟩,
  ⟨C0655.tokens, C0655.summary⟩,
  ⟨C0656.tokens, C0656.summary⟩,
  ⟨C0657.tokens, C0657.summary⟩,
  ⟨C0658.tokens, C0658.summary⟩,
  ⟨C0659.tokens, C0659.summary⟩,
  ⟨C0660.tokens, C0660.summary⟩,
  ⟨C0661.tokens, C0661.summary⟩,
  ⟨C0662.tokens, C0662.summary⟩,
  ⟨C0663.tokens, C0663.summary⟩,
  ⟨C0664.tokens, C0664.summary⟩,
  ⟨C0665.tokens, C0665.summary⟩,
  ⟨C0666.tokens, C0666.summary⟩,
  ⟨C0667.tokens, C0667.summary⟩,
  ⟨C0668.tokens, C0668.summary⟩,
  ⟨C0669.tokens, C0669.summary⟩,
  ⟨C0670.tokens, C0670.summary⟩,
  ⟨C0671.tokens, C0671.summary⟩]

theorem accepted : ChunksAccepted LL20 19548930049 chunks :=
  ⟨C0640.accepted, C0641.accepted, C0642.accepted, C0643.accepted, C0644.accepted, C0645.accepted, C0646.accepted, C0647.accepted, C0648.accepted, C0649.accepted, C0650.accepted, C0651.accepted, C0652.accepted, C0653.accepted, C0654.accepted, C0655.accepted, C0656.accepted, C0657.accepted, C0658.accepted, C0659.accepted, C0660.accepted, C0661.accepted, C0662.accepted, C0663.accepted, C0664.accepted, C0665.accepted, C0666.accepted, C0667.accepted, C0668.accepted, C0669.accepted, C0670.accepted, C0671.accepted, True.intro⟩

end Sarkozy.F3Kernel.CertificateData.LL20.B020
