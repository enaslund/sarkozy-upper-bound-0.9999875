module

public import Sarkozy.F3Kernel.ChainAppend
public import Sarkozy.F3Kernel.CertificateData.LL22.C0160
public import Sarkozy.F3Kernel.CertificateData.LL22.C0161
public import Sarkozy.F3Kernel.CertificateData.LL22.C0162
public import Sarkozy.F3Kernel.CertificateData.LL22.C0163
public import Sarkozy.F3Kernel.CertificateData.LL22.C0164
public import Sarkozy.F3Kernel.CertificateData.LL22.C0165
public import Sarkozy.F3Kernel.CertificateData.LL22.C0166
public import Sarkozy.F3Kernel.CertificateData.LL22.C0167
public import Sarkozy.F3Kernel.CertificateData.LL22.C0168
public import Sarkozy.F3Kernel.CertificateData.LL22.C0169
public import Sarkozy.F3Kernel.CertificateData.LL22.C0170
public import Sarkozy.F3Kernel.CertificateData.LL22.C0171
public import Sarkozy.F3Kernel.CertificateData.LL22.C0172
public import Sarkozy.F3Kernel.CertificateData.LL22.C0173
public import Sarkozy.F3Kernel.CertificateData.LL22.C0174
public import Sarkozy.F3Kernel.CertificateData.LL22.C0175
public import Sarkozy.F3Kernel.CertificateData.LL22.C0176
public import Sarkozy.F3Kernel.CertificateData.LL22.C0177
public import Sarkozy.F3Kernel.CertificateData.LL22.C0178
public import Sarkozy.F3Kernel.CertificateData.LL22.C0179
public import Sarkozy.F3Kernel.CertificateData.LL22.C0180
public import Sarkozy.F3Kernel.CertificateData.LL22.C0181
public import Sarkozy.F3Kernel.CertificateData.LL22.C0182
public import Sarkozy.F3Kernel.CertificateData.LL22.C0183
public import Sarkozy.F3Kernel.CertificateData.LL22.C0184
public import Sarkozy.F3Kernel.CertificateData.LL22.C0185
public import Sarkozy.F3Kernel.CertificateData.LL22.C0186
public import Sarkozy.F3Kernel.CertificateData.LL22.C0187
public import Sarkozy.F3Kernel.CertificateData.LL22.C0188
public import Sarkozy.F3Kernel.CertificateData.LL22.C0189
public import Sarkozy.F3Kernel.CertificateData.LL22.C0190
public import Sarkozy.F3Kernel.CertificateData.LL22.C0191


@[expose] public section

set_option maxRecDepth 10000

namespace Sarkozy.F3Kernel.CertificateData.LL22.B005

open Sarkozy.F3Kernel

noncomputable def chunks : List CertificateChunk := [
  ⟨C0160.tokens, C0160.summary⟩,
  ⟨C0161.tokens, C0161.summary⟩,
  ⟨C0162.tokens, C0162.summary⟩,
  ⟨C0163.tokens, C0163.summary⟩,
  ⟨C0164.tokens, C0164.summary⟩,
  ⟨C0165.tokens, C0165.summary⟩,
  ⟨C0166.tokens, C0166.summary⟩,
  ⟨C0167.tokens, C0167.summary⟩,
  ⟨C0168.tokens, C0168.summary⟩,
  ⟨C0169.tokens, C0169.summary⟩,
  ⟨C0170.tokens, C0170.summary⟩,
  ⟨C0171.tokens, C0171.summary⟩,
  ⟨C0172.tokens, C0172.summary⟩,
  ⟨C0173.tokens, C0173.summary⟩,
  ⟨C0174.tokens, C0174.summary⟩,
  ⟨C0175.tokens, C0175.summary⟩,
  ⟨C0176.tokens, C0176.summary⟩,
  ⟨C0177.tokens, C0177.summary⟩,
  ⟨C0178.tokens, C0178.summary⟩,
  ⟨C0179.tokens, C0179.summary⟩,
  ⟨C0180.tokens, C0180.summary⟩,
  ⟨C0181.tokens, C0181.summary⟩,
  ⟨C0182.tokens, C0182.summary⟩,
  ⟨C0183.tokens, C0183.summary⟩,
  ⟨C0184.tokens, C0184.summary⟩,
  ⟨C0185.tokens, C0185.summary⟩,
  ⟨C0186.tokens, C0186.summary⟩,
  ⟨C0187.tokens, C0187.summary⟩,
  ⟨C0188.tokens, C0188.summary⟩,
  ⟨C0189.tokens, C0189.summary⟩,
  ⟨C0190.tokens, C0190.summary⟩,
  ⟨C0191.tokens, C0191.summary⟩]

theorem accepted : ChunksAccepted LL22 17637314561 chunks :=
  ⟨C0160.accepted, C0161.accepted, C0162.accepted, C0163.accepted, C0164.accepted, C0165.accepted, C0166.accepted, C0167.accepted, C0168.accepted, C0169.accepted, C0170.accepted, C0171.accepted, C0172.accepted, C0173.accepted, C0174.accepted, C0175.accepted, C0176.accepted, C0177.accepted, C0178.accepted, C0179.accepted, C0180.accepted, C0181.accepted, C0182.accepted, C0183.accepted, C0184.accepted, C0185.accepted, C0186.accepted, C0187.accepted, C0188.accepted, C0189.accepted, C0190.accepted, C0191.accepted, True.intro⟩

end Sarkozy.F3Kernel.CertificateData.LL22.B005
