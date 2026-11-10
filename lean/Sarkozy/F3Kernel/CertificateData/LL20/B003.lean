module

public import Sarkozy.F3Kernel.ChainAppend
public import Sarkozy.F3Kernel.CertificateData.LL20.C0096
public import Sarkozy.F3Kernel.CertificateData.LL20.C0097
public import Sarkozy.F3Kernel.CertificateData.LL20.C0098
public import Sarkozy.F3Kernel.CertificateData.LL20.C0099
public import Sarkozy.F3Kernel.CertificateData.LL20.C0100
public import Sarkozy.F3Kernel.CertificateData.LL20.C0101
public import Sarkozy.F3Kernel.CertificateData.LL20.C0102
public import Sarkozy.F3Kernel.CertificateData.LL20.C0103
public import Sarkozy.F3Kernel.CertificateData.LL20.C0104
public import Sarkozy.F3Kernel.CertificateData.LL20.C0105
public import Sarkozy.F3Kernel.CertificateData.LL20.C0106
public import Sarkozy.F3Kernel.CertificateData.LL20.C0107
public import Sarkozy.F3Kernel.CertificateData.LL20.C0108
public import Sarkozy.F3Kernel.CertificateData.LL20.C0109
public import Sarkozy.F3Kernel.CertificateData.LL20.C0110
public import Sarkozy.F3Kernel.CertificateData.LL20.C0111
public import Sarkozy.F3Kernel.CertificateData.LL20.C0112
public import Sarkozy.F3Kernel.CertificateData.LL20.C0113
public import Sarkozy.F3Kernel.CertificateData.LL20.C0114
public import Sarkozy.F3Kernel.CertificateData.LL20.C0115
public import Sarkozy.F3Kernel.CertificateData.LL20.C0116
public import Sarkozy.F3Kernel.CertificateData.LL20.C0117
public import Sarkozy.F3Kernel.CertificateData.LL20.C0118
public import Sarkozy.F3Kernel.CertificateData.LL20.C0119
public import Sarkozy.F3Kernel.CertificateData.LL20.C0120
public import Sarkozy.F3Kernel.CertificateData.LL20.C0121
public import Sarkozy.F3Kernel.CertificateData.LL20.C0122
public import Sarkozy.F3Kernel.CertificateData.LL20.C0123
public import Sarkozy.F3Kernel.CertificateData.LL20.C0124
public import Sarkozy.F3Kernel.CertificateData.LL20.C0125
public import Sarkozy.F3Kernel.CertificateData.LL20.C0126
public import Sarkozy.F3Kernel.CertificateData.LL20.C0127


@[expose] public section

set_option maxRecDepth 10000

namespace Sarkozy.F3Kernel.CertificateData.LL20.B003

open Sarkozy.F3Kernel

noncomputable def chunks : List CertificateChunk := [
  ⟨C0096.tokens, C0096.summary⟩,
  ⟨C0097.tokens, C0097.summary⟩,
  ⟨C0098.tokens, C0098.summary⟩,
  ⟨C0099.tokens, C0099.summary⟩,
  ⟨C0100.tokens, C0100.summary⟩,
  ⟨C0101.tokens, C0101.summary⟩,
  ⟨C0102.tokens, C0102.summary⟩,
  ⟨C0103.tokens, C0103.summary⟩,
  ⟨C0104.tokens, C0104.summary⟩,
  ⟨C0105.tokens, C0105.summary⟩,
  ⟨C0106.tokens, C0106.summary⟩,
  ⟨C0107.tokens, C0107.summary⟩,
  ⟨C0108.tokens, C0108.summary⟩,
  ⟨C0109.tokens, C0109.summary⟩,
  ⟨C0110.tokens, C0110.summary⟩,
  ⟨C0111.tokens, C0111.summary⟩,
  ⟨C0112.tokens, C0112.summary⟩,
  ⟨C0113.tokens, C0113.summary⟩,
  ⟨C0114.tokens, C0114.summary⟩,
  ⟨C0115.tokens, C0115.summary⟩,
  ⟨C0116.tokens, C0116.summary⟩,
  ⟨C0117.tokens, C0117.summary⟩,
  ⟨C0118.tokens, C0118.summary⟩,
  ⟨C0119.tokens, C0119.summary⟩,
  ⟨C0120.tokens, C0120.summary⟩,
  ⟨C0121.tokens, C0121.summary⟩,
  ⟨C0122.tokens, C0122.summary⟩,
  ⟨C0123.tokens, C0123.summary⟩,
  ⟨C0124.tokens, C0124.summary⟩,
  ⟨C0125.tokens, C0125.summary⟩,
  ⟨C0126.tokens, C0126.summary⟩,
  ⟨C0127.tokens, C0127.summary⟩]

theorem accepted : ChunksAccepted LL20 287928321 chunks :=
  ⟨C0096.accepted, C0097.accepted, C0098.accepted, C0099.accepted, C0100.accepted, C0101.accepted, C0102.accepted, C0103.accepted, C0104.accepted, C0105.accepted, C0106.accepted, C0107.accepted, C0108.accepted, C0109.accepted, C0110.accepted, C0111.accepted, C0112.accepted, C0113.accepted, C0114.accepted, C0115.accepted, C0116.accepted, C0117.accepted, C0118.accepted, C0119.accepted, C0120.accepted, C0121.accepted, C0122.accepted, C0123.accepted, C0124.accepted, C0125.accepted, C0126.accepted, C0127.accepted, True.intro⟩

end Sarkozy.F3Kernel.CertificateData.LL20.B003
