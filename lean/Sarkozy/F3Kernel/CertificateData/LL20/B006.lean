module

public import Sarkozy.F3Kernel.ChainAppend
public import Sarkozy.F3Kernel.CertificateData.LL20.C0192
public import Sarkozy.F3Kernel.CertificateData.LL20.C0193
public import Sarkozy.F3Kernel.CertificateData.LL20.C0194
public import Sarkozy.F3Kernel.CertificateData.LL20.C0195
public import Sarkozy.F3Kernel.CertificateData.LL20.C0196
public import Sarkozy.F3Kernel.CertificateData.LL20.C0197
public import Sarkozy.F3Kernel.CertificateData.LL20.C0198
public import Sarkozy.F3Kernel.CertificateData.LL20.C0199
public import Sarkozy.F3Kernel.CertificateData.LL20.C0200
public import Sarkozy.F3Kernel.CertificateData.LL20.C0201
public import Sarkozy.F3Kernel.CertificateData.LL20.C0202
public import Sarkozy.F3Kernel.CertificateData.LL20.C0203
public import Sarkozy.F3Kernel.CertificateData.LL20.C0204
public import Sarkozy.F3Kernel.CertificateData.LL20.C0205
public import Sarkozy.F3Kernel.CertificateData.LL20.C0206
public import Sarkozy.F3Kernel.CertificateData.LL20.C0207
public import Sarkozy.F3Kernel.CertificateData.LL20.C0208
public import Sarkozy.F3Kernel.CertificateData.LL20.C0209
public import Sarkozy.F3Kernel.CertificateData.LL20.C0210
public import Sarkozy.F3Kernel.CertificateData.LL20.C0211
public import Sarkozy.F3Kernel.CertificateData.LL20.C0212
public import Sarkozy.F3Kernel.CertificateData.LL20.C0213
public import Sarkozy.F3Kernel.CertificateData.LL20.C0214
public import Sarkozy.F3Kernel.CertificateData.LL20.C0215
public import Sarkozy.F3Kernel.CertificateData.LL20.C0216
public import Sarkozy.F3Kernel.CertificateData.LL20.C0217
public import Sarkozy.F3Kernel.CertificateData.LL20.C0218
public import Sarkozy.F3Kernel.CertificateData.LL20.C0219
public import Sarkozy.F3Kernel.CertificateData.LL20.C0220
public import Sarkozy.F3Kernel.CertificateData.LL20.C0221
public import Sarkozy.F3Kernel.CertificateData.LL20.C0222
public import Sarkozy.F3Kernel.CertificateData.LL20.C0223


@[expose] public section

set_option maxRecDepth 10000

namespace Sarkozy.F3Kernel.CertificateData.LL20.B006

open Sarkozy.F3Kernel

noncomputable def chunks : List CertificateChunk := [
  ⟨C0192.tokens, C0192.summary⟩,
  ⟨C0193.tokens, C0193.summary⟩,
  ⟨C0194.tokens, C0194.summary⟩,
  ⟨C0195.tokens, C0195.summary⟩,
  ⟨C0196.tokens, C0196.summary⟩,
  ⟨C0197.tokens, C0197.summary⟩,
  ⟨C0198.tokens, C0198.summary⟩,
  ⟨C0199.tokens, C0199.summary⟩,
  ⟨C0200.tokens, C0200.summary⟩,
  ⟨C0201.tokens, C0201.summary⟩,
  ⟨C0202.tokens, C0202.summary⟩,
  ⟨C0203.tokens, C0203.summary⟩,
  ⟨C0204.tokens, C0204.summary⟩,
  ⟨C0205.tokens, C0205.summary⟩,
  ⟨C0206.tokens, C0206.summary⟩,
  ⟨C0207.tokens, C0207.summary⟩,
  ⟨C0208.tokens, C0208.summary⟩,
  ⟨C0209.tokens, C0209.summary⟩,
  ⟨C0210.tokens, C0210.summary⟩,
  ⟨C0211.tokens, C0211.summary⟩,
  ⟨C0212.tokens, C0212.summary⟩,
  ⟨C0213.tokens, C0213.summary⟩,
  ⟨C0214.tokens, C0214.summary⟩,
  ⟨C0215.tokens, C0215.summary⟩,
  ⟨C0216.tokens, C0216.summary⟩,
  ⟨C0217.tokens, C0217.summary⟩,
  ⟨C0218.tokens, C0218.summary⟩,
  ⟨C0219.tokens, C0219.summary⟩,
  ⟨C0220.tokens, C0220.summary⟩,
  ⟨C0221.tokens, C0221.summary⟩,
  ⟨C0222.tokens, C0222.summary⟩,
  ⟨C0223.tokens, C0223.summary⟩]

theorem accepted : ChunksAccepted LL20 2299846657 chunks :=
  ⟨C0192.accepted, C0193.accepted, C0194.accepted, C0195.accepted, C0196.accepted, C0197.accepted, C0198.accepted, C0199.accepted, C0200.accepted, C0201.accepted, C0202.accepted, C0203.accepted, C0204.accepted, C0205.accepted, C0206.accepted, C0207.accepted, C0208.accepted, C0209.accepted, C0210.accepted, C0211.accepted, C0212.accepted, C0213.accepted, C0214.accepted, C0215.accepted, C0216.accepted, C0217.accepted, C0218.accepted, C0219.accepted, C0220.accepted, C0221.accepted, C0222.accepted, C0223.accepted, True.intro⟩

end Sarkozy.F3Kernel.CertificateData.LL20.B006
