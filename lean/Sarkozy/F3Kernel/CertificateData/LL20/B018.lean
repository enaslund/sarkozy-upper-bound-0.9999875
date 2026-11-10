module

public import Sarkozy.F3Kernel.ChainAppend
public import Sarkozy.F3Kernel.CertificateData.LL20.C0576
public import Sarkozy.F3Kernel.CertificateData.LL20.C0577
public import Sarkozy.F3Kernel.CertificateData.LL20.C0578
public import Sarkozy.F3Kernel.CertificateData.LL20.C0579
public import Sarkozy.F3Kernel.CertificateData.LL20.C0580
public import Sarkozy.F3Kernel.CertificateData.LL20.C0581
public import Sarkozy.F3Kernel.CertificateData.LL20.C0582
public import Sarkozy.F3Kernel.CertificateData.LL20.C0583
public import Sarkozy.F3Kernel.CertificateData.LL20.C0584
public import Sarkozy.F3Kernel.CertificateData.LL20.C0585
public import Sarkozy.F3Kernel.CertificateData.LL20.C0586
public import Sarkozy.F3Kernel.CertificateData.LL20.C0587
public import Sarkozy.F3Kernel.CertificateData.LL20.C0588
public import Sarkozy.F3Kernel.CertificateData.LL20.C0589
public import Sarkozy.F3Kernel.CertificateData.LL20.C0590
public import Sarkozy.F3Kernel.CertificateData.LL20.C0591
public import Sarkozy.F3Kernel.CertificateData.LL20.C0592
public import Sarkozy.F3Kernel.CertificateData.LL20.C0593
public import Sarkozy.F3Kernel.CertificateData.LL20.C0594
public import Sarkozy.F3Kernel.CertificateData.LL20.C0595
public import Sarkozy.F3Kernel.CertificateData.LL20.C0596
public import Sarkozy.F3Kernel.CertificateData.LL20.C0597
public import Sarkozy.F3Kernel.CertificateData.LL20.C0598
public import Sarkozy.F3Kernel.CertificateData.LL20.C0599
public import Sarkozy.F3Kernel.CertificateData.LL20.C0600
public import Sarkozy.F3Kernel.CertificateData.LL20.C0601
public import Sarkozy.F3Kernel.CertificateData.LL20.C0602
public import Sarkozy.F3Kernel.CertificateData.LL20.C0603
public import Sarkozy.F3Kernel.CertificateData.LL20.C0604
public import Sarkozy.F3Kernel.CertificateData.LL20.C0605
public import Sarkozy.F3Kernel.CertificateData.LL20.C0606
public import Sarkozy.F3Kernel.CertificateData.LL20.C0607


@[expose] public section

set_option maxRecDepth 10000

namespace Sarkozy.F3Kernel.CertificateData.LL20.B018

open Sarkozy.F3Kernel

noncomputable def chunks : List CertificateChunk := [
  ⟨C0576.tokens, C0576.summary⟩,
  ⟨C0577.tokens, C0577.summary⟩,
  ⟨C0578.tokens, C0578.summary⟩,
  ⟨C0579.tokens, C0579.summary⟩,
  ⟨C0580.tokens, C0580.summary⟩,
  ⟨C0581.tokens, C0581.summary⟩,
  ⟨C0582.tokens, C0582.summary⟩,
  ⟨C0583.tokens, C0583.summary⟩,
  ⟨C0584.tokens, C0584.summary⟩,
  ⟨C0585.tokens, C0585.summary⟩,
  ⟨C0586.tokens, C0586.summary⟩,
  ⟨C0587.tokens, C0587.summary⟩,
  ⟨C0588.tokens, C0588.summary⟩,
  ⟨C0589.tokens, C0589.summary⟩,
  ⟨C0590.tokens, C0590.summary⟩,
  ⟨C0591.tokens, C0591.summary⟩,
  ⟨C0592.tokens, C0592.summary⟩,
  ⟨C0593.tokens, C0593.summary⟩,
  ⟨C0594.tokens, C0594.summary⟩,
  ⟨C0595.tokens, C0595.summary⟩,
  ⟨C0596.tokens, C0596.summary⟩,
  ⟨C0597.tokens, C0597.summary⟩,
  ⟨C0598.tokens, C0598.summary⟩,
  ⟨C0599.tokens, C0599.summary⟩,
  ⟨C0600.tokens, C0600.summary⟩,
  ⟨C0601.tokens, C0601.summary⟩,
  ⟨C0602.tokens, C0602.summary⟩,
  ⟨C0603.tokens, C0603.summary⟩,
  ⟨C0604.tokens, C0604.summary⟩,
  ⟨C0605.tokens, C0605.summary⟩,
  ⟨C0606.tokens, C0606.summary⟩,
  ⟨C0607.tokens, C0607.summary⟩]

theorem accepted : ChunksAccepted LL20 15088300033 chunks :=
  ⟨C0576.accepted, C0577.accepted, C0578.accepted, C0579.accepted, C0580.accepted, C0581.accepted, C0582.accepted, C0583.accepted, C0584.accepted, C0585.accepted, C0586.accepted, C0587.accepted, C0588.accepted, C0589.accepted, C0590.accepted, C0591.accepted, C0592.accepted, C0593.accepted, C0594.accepted, C0595.accepted, C0596.accepted, C0597.accepted, C0598.accepted, C0599.accepted, C0600.accepted, C0601.accepted, C0602.accepted, C0603.accepted, C0604.accepted, C0605.accepted, C0606.accepted, C0607.accepted, True.intro⟩

end Sarkozy.F3Kernel.CertificateData.LL20.B018
