module

public import Sarkozy.F3Kernel.ChainAppend
public import Sarkozy.F3Kernel.CertificateData.LL20.C0128
public import Sarkozy.F3Kernel.CertificateData.LL20.C0129
public import Sarkozy.F3Kernel.CertificateData.LL20.C0130
public import Sarkozy.F3Kernel.CertificateData.LL20.C0131
public import Sarkozy.F3Kernel.CertificateData.LL20.C0132
public import Sarkozy.F3Kernel.CertificateData.LL20.C0133
public import Sarkozy.F3Kernel.CertificateData.LL20.C0134
public import Sarkozy.F3Kernel.CertificateData.LL20.C0135
public import Sarkozy.F3Kernel.CertificateData.LL20.C0136
public import Sarkozy.F3Kernel.CertificateData.LL20.C0137
public import Sarkozy.F3Kernel.CertificateData.LL20.C0138
public import Sarkozy.F3Kernel.CertificateData.LL20.C0139
public import Sarkozy.F3Kernel.CertificateData.LL20.C0140
public import Sarkozy.F3Kernel.CertificateData.LL20.C0141
public import Sarkozy.F3Kernel.CertificateData.LL20.C0142
public import Sarkozy.F3Kernel.CertificateData.LL20.C0143
public import Sarkozy.F3Kernel.CertificateData.LL20.C0144
public import Sarkozy.F3Kernel.CertificateData.LL20.C0145
public import Sarkozy.F3Kernel.CertificateData.LL20.C0146
public import Sarkozy.F3Kernel.CertificateData.LL20.C0147
public import Sarkozy.F3Kernel.CertificateData.LL20.C0148
public import Sarkozy.F3Kernel.CertificateData.LL20.C0149
public import Sarkozy.F3Kernel.CertificateData.LL20.C0150
public import Sarkozy.F3Kernel.CertificateData.LL20.C0151
public import Sarkozy.F3Kernel.CertificateData.LL20.C0152
public import Sarkozy.F3Kernel.CertificateData.LL20.C0153
public import Sarkozy.F3Kernel.CertificateData.LL20.C0154
public import Sarkozy.F3Kernel.CertificateData.LL20.C0155
public import Sarkozy.F3Kernel.CertificateData.LL20.C0156
public import Sarkozy.F3Kernel.CertificateData.LL20.C0157
public import Sarkozy.F3Kernel.CertificateData.LL20.C0158
public import Sarkozy.F3Kernel.CertificateData.LL20.C0159


@[expose] public section

set_option maxRecDepth 10000

namespace Sarkozy.F3Kernel.CertificateData.LL20.B004

open Sarkozy.F3Kernel

noncomputable def chunks : List CertificateChunk := [
  ⟨C0128.tokens, C0128.summary⟩,
  ⟨C0129.tokens, C0129.summary⟩,
  ⟨C0130.tokens, C0130.summary⟩,
  ⟨C0131.tokens, C0131.summary⟩,
  ⟨C0132.tokens, C0132.summary⟩,
  ⟨C0133.tokens, C0133.summary⟩,
  ⟨C0134.tokens, C0134.summary⟩,
  ⟨C0135.tokens, C0135.summary⟩,
  ⟨C0136.tokens, C0136.summary⟩,
  ⟨C0137.tokens, C0137.summary⟩,
  ⟨C0138.tokens, C0138.summary⟩,
  ⟨C0139.tokens, C0139.summary⟩,
  ⟨C0140.tokens, C0140.summary⟩,
  ⟨C0141.tokens, C0141.summary⟩,
  ⟨C0142.tokens, C0142.summary⟩,
  ⟨C0143.tokens, C0143.summary⟩,
  ⟨C0144.tokens, C0144.summary⟩,
  ⟨C0145.tokens, C0145.summary⟩,
  ⟨C0146.tokens, C0146.summary⟩,
  ⟨C0147.tokens, C0147.summary⟩,
  ⟨C0148.tokens, C0148.summary⟩,
  ⟨C0149.tokens, C0149.summary⟩,
  ⟨C0150.tokens, C0150.summary⟩,
  ⟨C0151.tokens, C0151.summary⟩,
  ⟨C0152.tokens, C0152.summary⟩,
  ⟨C0153.tokens, C0153.summary⟩,
  ⟨C0154.tokens, C0154.summary⟩,
  ⟨C0155.tokens, C0155.summary⟩,
  ⟨C0156.tokens, C0156.summary⟩,
  ⟨C0157.tokens, C0157.summary⟩,
  ⟨C0158.tokens, C0158.summary⟩,
  ⟨C0159.tokens, C0159.summary⟩]

theorem accepted : ChunksAccepted LL20 454430722 chunks :=
  ⟨C0128.accepted, C0129.accepted, C0130.accepted, C0131.accepted, C0132.accepted, C0133.accepted, C0134.accepted, C0135.accepted, C0136.accepted, C0137.accepted, C0138.accepted, C0139.accepted, C0140.accepted, C0141.accepted, C0142.accepted, C0143.accepted, C0144.accepted, C0145.accepted, C0146.accepted, C0147.accepted, C0148.accepted, C0149.accepted, C0150.accepted, C0151.accepted, C0152.accepted, C0153.accepted, C0154.accepted, C0155.accepted, C0156.accepted, C0157.accepted, C0158.accepted, C0159.accepted, True.intro⟩

end Sarkozy.F3Kernel.CertificateData.LL20.B004
