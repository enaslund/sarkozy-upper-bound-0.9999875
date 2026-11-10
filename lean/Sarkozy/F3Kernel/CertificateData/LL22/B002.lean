module

public import Sarkozy.F3Kernel.ChainAppend
public import Sarkozy.F3Kernel.CertificateData.LL22.C0064
public import Sarkozy.F3Kernel.CertificateData.LL22.C0065
public import Sarkozy.F3Kernel.CertificateData.LL22.C0066
public import Sarkozy.F3Kernel.CertificateData.LL22.C0067
public import Sarkozy.F3Kernel.CertificateData.LL22.C0068
public import Sarkozy.F3Kernel.CertificateData.LL22.C0069
public import Sarkozy.F3Kernel.CertificateData.LL22.C0070
public import Sarkozy.F3Kernel.CertificateData.LL22.C0071
public import Sarkozy.F3Kernel.CertificateData.LL22.C0072
public import Sarkozy.F3Kernel.CertificateData.LL22.C0073
public import Sarkozy.F3Kernel.CertificateData.LL22.C0074
public import Sarkozy.F3Kernel.CertificateData.LL22.C0075
public import Sarkozy.F3Kernel.CertificateData.LL22.C0076
public import Sarkozy.F3Kernel.CertificateData.LL22.C0077
public import Sarkozy.F3Kernel.CertificateData.LL22.C0078
public import Sarkozy.F3Kernel.CertificateData.LL22.C0079
public import Sarkozy.F3Kernel.CertificateData.LL22.C0080
public import Sarkozy.F3Kernel.CertificateData.LL22.C0081
public import Sarkozy.F3Kernel.CertificateData.LL22.C0082
public import Sarkozy.F3Kernel.CertificateData.LL22.C0083
public import Sarkozy.F3Kernel.CertificateData.LL22.C0084
public import Sarkozy.F3Kernel.CertificateData.LL22.C0085
public import Sarkozy.F3Kernel.CertificateData.LL22.C0086
public import Sarkozy.F3Kernel.CertificateData.LL22.C0087
public import Sarkozy.F3Kernel.CertificateData.LL22.C0088
public import Sarkozy.F3Kernel.CertificateData.LL22.C0089
public import Sarkozy.F3Kernel.CertificateData.LL22.C0090
public import Sarkozy.F3Kernel.CertificateData.LL22.C0091
public import Sarkozy.F3Kernel.CertificateData.LL22.C0092
public import Sarkozy.F3Kernel.CertificateData.LL22.C0093
public import Sarkozy.F3Kernel.CertificateData.LL22.C0094
public import Sarkozy.F3Kernel.CertificateData.LL22.C0095


@[expose] public section

set_option maxRecDepth 10000

namespace Sarkozy.F3Kernel.CertificateData.LL22.B002

open Sarkozy.F3Kernel

noncomputable def chunks : List CertificateChunk := [
  ⟨C0064.tokens, C0064.summary⟩,
  ⟨C0065.tokens, C0065.summary⟩,
  ⟨C0066.tokens, C0066.summary⟩,
  ⟨C0067.tokens, C0067.summary⟩,
  ⟨C0068.tokens, C0068.summary⟩,
  ⟨C0069.tokens, C0069.summary⟩,
  ⟨C0070.tokens, C0070.summary⟩,
  ⟨C0071.tokens, C0071.summary⟩,
  ⟨C0072.tokens, C0072.summary⟩,
  ⟨C0073.tokens, C0073.summary⟩,
  ⟨C0074.tokens, C0074.summary⟩,
  ⟨C0075.tokens, C0075.summary⟩,
  ⟨C0076.tokens, C0076.summary⟩,
  ⟨C0077.tokens, C0077.summary⟩,
  ⟨C0078.tokens, C0078.summary⟩,
  ⟨C0079.tokens, C0079.summary⟩,
  ⟨C0080.tokens, C0080.summary⟩,
  ⟨C0081.tokens, C0081.summary⟩,
  ⟨C0082.tokens, C0082.summary⟩,
  ⟨C0083.tokens, C0083.summary⟩,
  ⟨C0084.tokens, C0084.summary⟩,
  ⟨C0085.tokens, C0085.summary⟩,
  ⟨C0086.tokens, C0086.summary⟩,
  ⟨C0087.tokens, C0087.summary⟩,
  ⟨C0088.tokens, C0088.summary⟩,
  ⟨C0089.tokens, C0089.summary⟩,
  ⟨C0090.tokens, C0090.summary⟩,
  ⟨C0091.tokens, C0091.summary⟩,
  ⟨C0092.tokens, C0092.summary⟩,
  ⟨C0093.tokens, C0093.summary⟩,
  ⟨C0094.tokens, C0094.summary⟩,
  ⟨C0095.tokens, C0095.summary⟩]

theorem accepted : ChunksAccepted LL22 2366668803 chunks :=
  ⟨C0064.accepted, C0065.accepted, C0066.accepted, C0067.accepted, C0068.accepted, C0069.accepted, C0070.accepted, C0071.accepted, C0072.accepted, C0073.accepted, C0074.accepted, C0075.accepted, C0076.accepted, C0077.accepted, C0078.accepted, C0079.accepted, C0080.accepted, C0081.accepted, C0082.accepted, C0083.accepted, C0084.accepted, C0085.accepted, C0086.accepted, C0087.accepted, C0088.accepted, C0089.accepted, C0090.accepted, C0091.accepted, C0092.accepted, C0093.accepted, C0094.accepted, C0095.accepted, True.intro⟩

end Sarkozy.F3Kernel.CertificateData.LL22.B002
