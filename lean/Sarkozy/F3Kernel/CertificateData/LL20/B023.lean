module

public import Sarkozy.F3Kernel.ChainAppend
public import Sarkozy.F3Kernel.CertificateData.LL20.C0736
public import Sarkozy.F3Kernel.CertificateData.LL20.C0737
public import Sarkozy.F3Kernel.CertificateData.LL20.C0738


@[expose] public section

set_option maxRecDepth 10000

namespace Sarkozy.F3Kernel.CertificateData.LL20.B023

open Sarkozy.F3Kernel

noncomputable def chunks : List CertificateChunk := [
  ⟨C0736.tokens, C0736.summary⟩,
  ⟨C0737.tokens, C0737.summary⟩,
  ⟨C0738.tokens, C0738.summary⟩]

theorem accepted : ChunksAccepted LL20 65154953217 chunks :=
  ⟨C0736.accepted, C0737.accepted, C0738.accepted, True.intro⟩

end Sarkozy.F3Kernel.CertificateData.LL20.B023
