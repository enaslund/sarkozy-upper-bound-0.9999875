module

public import Sarkozy.F3Kernel.ChainAppend
public import Sarkozy.F3Kernel.CertificateData.LL20.C0000
public import Sarkozy.F3Kernel.CertificateData.LL20.C0001
public import Sarkozy.F3Kernel.CertificateData.LL20.C0002
public import Sarkozy.F3Kernel.CertificateData.LL20.C0003
public import Sarkozy.F3Kernel.CertificateData.LL20.C0004
public import Sarkozy.F3Kernel.CertificateData.LL20.C0005
public import Sarkozy.F3Kernel.CertificateData.LL20.C0006
public import Sarkozy.F3Kernel.CertificateData.LL20.C0007
public import Sarkozy.F3Kernel.CertificateData.LL20.C0008
public import Sarkozy.F3Kernel.CertificateData.LL20.C0009
public import Sarkozy.F3Kernel.CertificateData.LL20.C0010
public import Sarkozy.F3Kernel.CertificateData.LL20.C0011
public import Sarkozy.F3Kernel.CertificateData.LL20.C0012
public import Sarkozy.F3Kernel.CertificateData.LL20.C0013
public import Sarkozy.F3Kernel.CertificateData.LL20.C0014
public import Sarkozy.F3Kernel.CertificateData.LL20.C0015
public import Sarkozy.F3Kernel.CertificateData.LL20.C0016
public import Sarkozy.F3Kernel.CertificateData.LL20.C0017
public import Sarkozy.F3Kernel.CertificateData.LL20.C0018
public import Sarkozy.F3Kernel.CertificateData.LL20.C0019
public import Sarkozy.F3Kernel.CertificateData.LL20.C0020
public import Sarkozy.F3Kernel.CertificateData.LL20.C0021
public import Sarkozy.F3Kernel.CertificateData.LL20.C0022
public import Sarkozy.F3Kernel.CertificateData.LL20.C0023
public import Sarkozy.F3Kernel.CertificateData.LL20.C0024
public import Sarkozy.F3Kernel.CertificateData.LL20.C0025
public import Sarkozy.F3Kernel.CertificateData.LL20.C0026
public import Sarkozy.F3Kernel.CertificateData.LL20.C0027
public import Sarkozy.F3Kernel.CertificateData.LL20.C0028
public import Sarkozy.F3Kernel.CertificateData.LL20.C0029
public import Sarkozy.F3Kernel.CertificateData.LL20.C0030
public import Sarkozy.F3Kernel.CertificateData.LL20.C0031


@[expose] public section

set_option maxRecDepth 10000

namespace Sarkozy.F3Kernel.CertificateData.LL20.B000

open Sarkozy.F3Kernel

noncomputable def chunks : List CertificateChunk := [
  ⟨C0000.tokens, C0000.summary⟩,
  ⟨C0001.tokens, C0001.summary⟩,
  ⟨C0002.tokens, C0002.summary⟩,
  ⟨C0003.tokens, C0003.summary⟩,
  ⟨C0004.tokens, C0004.summary⟩,
  ⟨C0005.tokens, C0005.summary⟩,
  ⟨C0006.tokens, C0006.summary⟩,
  ⟨C0007.tokens, C0007.summary⟩,
  ⟨C0008.tokens, C0008.summary⟩,
  ⟨C0009.tokens, C0009.summary⟩,
  ⟨C0010.tokens, C0010.summary⟩,
  ⟨C0011.tokens, C0011.summary⟩,
  ⟨C0012.tokens, C0012.summary⟩,
  ⟨C0013.tokens, C0013.summary⟩,
  ⟨C0014.tokens, C0014.summary⟩,
  ⟨C0015.tokens, C0015.summary⟩,
  ⟨C0016.tokens, C0016.summary⟩,
  ⟨C0017.tokens, C0017.summary⟩,
  ⟨C0018.tokens, C0018.summary⟩,
  ⟨C0019.tokens, C0019.summary⟩,
  ⟨C0020.tokens, C0020.summary⟩,
  ⟨C0021.tokens, C0021.summary⟩,
  ⟨C0022.tokens, C0022.summary⟩,
  ⟨C0023.tokens, C0023.summary⟩,
  ⟨C0024.tokens, C0024.summary⟩,
  ⟨C0025.tokens, C0025.summary⟩,
  ⟨C0026.tokens, C0026.summary⟩,
  ⟨C0027.tokens, C0027.summary⟩,
  ⟨C0028.tokens, C0028.summary⟩,
  ⟨C0029.tokens, C0029.summary⟩,
  ⟨C0030.tokens, C0030.summary⟩,
  ⟨C0031.tokens, C0031.summary⟩]

theorem accepted : ChunksAccepted LL20 0 chunks :=
  ⟨C0000.accepted, C0001.accepted, C0002.accepted, C0003.accepted, C0004.accepted, C0005.accepted, C0006.accepted, C0007.accepted, C0008.accepted, C0009.accepted, C0010.accepted, C0011.accepted, C0012.accepted, C0013.accepted, C0014.accepted, C0015.accepted, C0016.accepted, C0017.accepted, C0018.accepted, C0019.accepted, C0020.accepted, C0021.accepted, C0022.accepted, C0023.accepted, C0024.accepted, C0025.accepted, C0026.accepted, C0027.accepted, C0028.accepted, C0029.accepted, C0030.accepted, C0031.accepted, True.intro⟩

end Sarkozy.F3Kernel.CertificateData.LL20.B000
