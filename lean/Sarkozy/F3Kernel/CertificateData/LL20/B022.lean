module

public import Sarkozy.F3Kernel.ChainAppend
public import Sarkozy.F3Kernel.CertificateData.LL20.C0704
public import Sarkozy.F3Kernel.CertificateData.LL20.C0705
public import Sarkozy.F3Kernel.CertificateData.LL20.C0706
public import Sarkozy.F3Kernel.CertificateData.LL20.C0707
public import Sarkozy.F3Kernel.CertificateData.LL20.C0708
public import Sarkozy.F3Kernel.CertificateData.LL20.C0709
public import Sarkozy.F3Kernel.CertificateData.LL20.C0710
public import Sarkozy.F3Kernel.CertificateData.LL20.C0711
public import Sarkozy.F3Kernel.CertificateData.LL20.C0712
public import Sarkozy.F3Kernel.CertificateData.LL20.C0713
public import Sarkozy.F3Kernel.CertificateData.LL20.C0714
public import Sarkozy.F3Kernel.CertificateData.LL20.C0715
public import Sarkozy.F3Kernel.CertificateData.LL20.C0716
public import Sarkozy.F3Kernel.CertificateData.LL20.C0717
public import Sarkozy.F3Kernel.CertificateData.LL20.C0718
public import Sarkozy.F3Kernel.CertificateData.LL20.C0719
public import Sarkozy.F3Kernel.CertificateData.LL20.C0720
public import Sarkozy.F3Kernel.CertificateData.LL20.C0721
public import Sarkozy.F3Kernel.CertificateData.LL20.C0722
public import Sarkozy.F3Kernel.CertificateData.LL20.C0723
public import Sarkozy.F3Kernel.CertificateData.LL20.C0724
public import Sarkozy.F3Kernel.CertificateData.LL20.C0725
public import Sarkozy.F3Kernel.CertificateData.LL20.C0726
public import Sarkozy.F3Kernel.CertificateData.LL20.C0727
public import Sarkozy.F3Kernel.CertificateData.LL20.C0728
public import Sarkozy.F3Kernel.CertificateData.LL20.C0729
public import Sarkozy.F3Kernel.CertificateData.LL20.C0730
public import Sarkozy.F3Kernel.CertificateData.LL20.C0731
public import Sarkozy.F3Kernel.CertificateData.LL20.C0732
public import Sarkozy.F3Kernel.CertificateData.LL20.C0733
public import Sarkozy.F3Kernel.CertificateData.LL20.C0734
public import Sarkozy.F3Kernel.CertificateData.LL20.C0735


@[expose] public section

set_option maxRecDepth 10000

namespace Sarkozy.F3Kernel.CertificateData.LL20.B022

open Sarkozy.F3Kernel

noncomputable def chunks : List CertificateChunk := [
  ⟨C0704.tokens, C0704.summary⟩,
  ⟨C0705.tokens, C0705.summary⟩,
  ⟨C0706.tokens, C0706.summary⟩,
  ⟨C0707.tokens, C0707.summary⟩,
  ⟨C0708.tokens, C0708.summary⟩,
  ⟨C0709.tokens, C0709.summary⟩,
  ⟨C0710.tokens, C0710.summary⟩,
  ⟨C0711.tokens, C0711.summary⟩,
  ⟨C0712.tokens, C0712.summary⟩,
  ⟨C0713.tokens, C0713.summary⟩,
  ⟨C0714.tokens, C0714.summary⟩,
  ⟨C0715.tokens, C0715.summary⟩,
  ⟨C0716.tokens, C0716.summary⟩,
  ⟨C0717.tokens, C0717.summary⟩,
  ⟨C0718.tokens, C0718.summary⟩,
  ⟨C0719.tokens, C0719.summary⟩,
  ⟨C0720.tokens, C0720.summary⟩,
  ⟨C0721.tokens, C0721.summary⟩,
  ⟨C0722.tokens, C0722.summary⟩,
  ⟨C0723.tokens, C0723.summary⟩,
  ⟨C0724.tokens, C0724.summary⟩,
  ⟨C0725.tokens, C0725.summary⟩,
  ⟨C0726.tokens, C0726.summary⟩,
  ⟨C0727.tokens, C0727.summary⟩,
  ⟨C0728.tokens, C0728.summary⟩,
  ⟨C0729.tokens, C0729.summary⟩,
  ⟨C0730.tokens, C0730.summary⟩,
  ⟨C0731.tokens, C0731.summary⟩,
  ⟨C0732.tokens, C0732.summary⟩,
  ⟨C0733.tokens, C0733.summary⟩,
  ⟨C0734.tokens, C0734.summary⟩,
  ⟨C0735.tokens, C0735.summary⟩]

theorem accepted : ChunksAccepted LL20 32991179737 chunks :=
  ⟨C0704.accepted, C0705.accepted, C0706.accepted, C0707.accepted, C0708.accepted, C0709.accepted, C0710.accepted, C0711.accepted, C0712.accepted, C0713.accepted, C0714.accepted, C0715.accepted, C0716.accepted, C0717.accepted, C0718.accepted, C0719.accepted, C0720.accepted, C0721.accepted, C0722.accepted, C0723.accepted, C0724.accepted, C0725.accepted, C0726.accepted, C0727.accepted, C0728.accepted, C0729.accepted, C0730.accepted, C0731.accepted, C0732.accepted, C0733.accepted, C0734.accepted, C0735.accepted, True.intro⟩

end Sarkozy.F3Kernel.CertificateData.LL20.B022
