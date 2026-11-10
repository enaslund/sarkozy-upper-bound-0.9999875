module

public import Sarkozy.F3Kernel.ChainAppend
public import Sarkozy.F3Kernel.CertificateData.LL20.C0608
public import Sarkozy.F3Kernel.CertificateData.LL20.C0609
public import Sarkozy.F3Kernel.CertificateData.LL20.C0610
public import Sarkozy.F3Kernel.CertificateData.LL20.C0611
public import Sarkozy.F3Kernel.CertificateData.LL20.C0612
public import Sarkozy.F3Kernel.CertificateData.LL20.C0613
public import Sarkozy.F3Kernel.CertificateData.LL20.C0614
public import Sarkozy.F3Kernel.CertificateData.LL20.C0615
public import Sarkozy.F3Kernel.CertificateData.LL20.C0616
public import Sarkozy.F3Kernel.CertificateData.LL20.C0617
public import Sarkozy.F3Kernel.CertificateData.LL20.C0618
public import Sarkozy.F3Kernel.CertificateData.LL20.C0619
public import Sarkozy.F3Kernel.CertificateData.LL20.C0620
public import Sarkozy.F3Kernel.CertificateData.LL20.C0621
public import Sarkozy.F3Kernel.CertificateData.LL20.C0622
public import Sarkozy.F3Kernel.CertificateData.LL20.C0623
public import Sarkozy.F3Kernel.CertificateData.LL20.C0624
public import Sarkozy.F3Kernel.CertificateData.LL20.C0625
public import Sarkozy.F3Kernel.CertificateData.LL20.C0626
public import Sarkozy.F3Kernel.CertificateData.LL20.C0627
public import Sarkozy.F3Kernel.CertificateData.LL20.C0628
public import Sarkozy.F3Kernel.CertificateData.LL20.C0629
public import Sarkozy.F3Kernel.CertificateData.LL20.C0630
public import Sarkozy.F3Kernel.CertificateData.LL20.C0631
public import Sarkozy.F3Kernel.CertificateData.LL20.C0632
public import Sarkozy.F3Kernel.CertificateData.LL20.C0633
public import Sarkozy.F3Kernel.CertificateData.LL20.C0634
public import Sarkozy.F3Kernel.CertificateData.LL20.C0635
public import Sarkozy.F3Kernel.CertificateData.LL20.C0636
public import Sarkozy.F3Kernel.CertificateData.LL20.C0637
public import Sarkozy.F3Kernel.CertificateData.LL20.C0638
public import Sarkozy.F3Kernel.CertificateData.LL20.C0639


@[expose] public section

set_option maxRecDepth 10000

namespace Sarkozy.F3Kernel.CertificateData.LL20.B019

open Sarkozy.F3Kernel

noncomputable def chunks : List CertificateChunk := [
  ⟨C0608.tokens, C0608.summary⟩,
  ⟨C0609.tokens, C0609.summary⟩,
  ⟨C0610.tokens, C0610.summary⟩,
  ⟨C0611.tokens, C0611.summary⟩,
  ⟨C0612.tokens, C0612.summary⟩,
  ⟨C0613.tokens, C0613.summary⟩,
  ⟨C0614.tokens, C0614.summary⟩,
  ⟨C0615.tokens, C0615.summary⟩,
  ⟨C0616.tokens, C0616.summary⟩,
  ⟨C0617.tokens, C0617.summary⟩,
  ⟨C0618.tokens, C0618.summary⟩,
  ⟨C0619.tokens, C0619.summary⟩,
  ⟨C0620.tokens, C0620.summary⟩,
  ⟨C0621.tokens, C0621.summary⟩,
  ⟨C0622.tokens, C0622.summary⟩,
  ⟨C0623.tokens, C0623.summary⟩,
  ⟨C0624.tokens, C0624.summary⟩,
  ⟨C0625.tokens, C0625.summary⟩,
  ⟨C0626.tokens, C0626.summary⟩,
  ⟨C0627.tokens, C0627.summary⟩,
  ⟨C0628.tokens, C0628.summary⟩,
  ⟨C0629.tokens, C0629.summary⟩,
  ⟨C0630.tokens, C0630.summary⟩,
  ⟨C0631.tokens, C0631.summary⟩,
  ⟨C0632.tokens, C0632.summary⟩,
  ⟨C0633.tokens, C0633.summary⟩,
  ⟨C0634.tokens, C0634.summary⟩,
  ⟨C0635.tokens, C0635.summary⟩,
  ⟨C0636.tokens, C0636.summary⟩,
  ⟨C0637.tokens, C0637.summary⟩,
  ⟨C0638.tokens, C0638.summary⟩,
  ⟨C0639.tokens, C0639.summary⟩]

theorem accepted : ChunksAccepted LL20 17670197249 chunks :=
  ⟨C0608.accepted, C0609.accepted, C0610.accepted, C0611.accepted, C0612.accepted, C0613.accepted, C0614.accepted, C0615.accepted, C0616.accepted, C0617.accepted, C0618.accepted, C0619.accepted, C0620.accepted, C0621.accepted, C0622.accepted, C0623.accepted, C0624.accepted, C0625.accepted, C0626.accepted, C0627.accepted, C0628.accepted, C0629.accepted, C0630.accepted, C0631.accepted, C0632.accepted, C0633.accepted, C0634.accepted, C0635.accepted, C0636.accepted, C0637.accepted, C0638.accepted, C0639.accepted, True.intro⟩

end Sarkozy.F3Kernel.CertificateData.LL20.B019
