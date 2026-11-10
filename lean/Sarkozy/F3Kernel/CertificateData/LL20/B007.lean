module

public import Sarkozy.F3Kernel.ChainAppend
public import Sarkozy.F3Kernel.CertificateData.LL20.C0224
public import Sarkozy.F3Kernel.CertificateData.LL20.C0225
public import Sarkozy.F3Kernel.CertificateData.LL20.C0226
public import Sarkozy.F3Kernel.CertificateData.LL20.C0227
public import Sarkozy.F3Kernel.CertificateData.LL20.C0228
public import Sarkozy.F3Kernel.CertificateData.LL20.C0229
public import Sarkozy.F3Kernel.CertificateData.LL20.C0230
public import Sarkozy.F3Kernel.CertificateData.LL20.C0231
public import Sarkozy.F3Kernel.CertificateData.LL20.C0232
public import Sarkozy.F3Kernel.CertificateData.LL20.C0233
public import Sarkozy.F3Kernel.CertificateData.LL20.C0234
public import Sarkozy.F3Kernel.CertificateData.LL20.C0235
public import Sarkozy.F3Kernel.CertificateData.LL20.C0236
public import Sarkozy.F3Kernel.CertificateData.LL20.C0237
public import Sarkozy.F3Kernel.CertificateData.LL20.C0238
public import Sarkozy.F3Kernel.CertificateData.LL20.C0239
public import Sarkozy.F3Kernel.CertificateData.LL20.C0240
public import Sarkozy.F3Kernel.CertificateData.LL20.C0241
public import Sarkozy.F3Kernel.CertificateData.LL20.C0242
public import Sarkozy.F3Kernel.CertificateData.LL20.C0243
public import Sarkozy.F3Kernel.CertificateData.LL20.C0244
public import Sarkozy.F3Kernel.CertificateData.LL20.C0245
public import Sarkozy.F3Kernel.CertificateData.LL20.C0246
public import Sarkozy.F3Kernel.CertificateData.LL20.C0247
public import Sarkozy.F3Kernel.CertificateData.LL20.C0248
public import Sarkozy.F3Kernel.CertificateData.LL20.C0249
public import Sarkozy.F3Kernel.CertificateData.LL20.C0250
public import Sarkozy.F3Kernel.CertificateData.LL20.C0251
public import Sarkozy.F3Kernel.CertificateData.LL20.C0252
public import Sarkozy.F3Kernel.CertificateData.LL20.C0253
public import Sarkozy.F3Kernel.CertificateData.LL20.C0254
public import Sarkozy.F3Kernel.CertificateData.LL20.C0255


@[expose] public section

set_option maxRecDepth 10000

namespace Sarkozy.F3Kernel.CertificateData.LL20.B007

open Sarkozy.F3Kernel

noncomputable def chunks : List CertificateChunk := [
  ⟨C0224.tokens, C0224.summary⟩,
  ⟨C0225.tokens, C0225.summary⟩,
  ⟨C0226.tokens, C0226.summary⟩,
  ⟨C0227.tokens, C0227.summary⟩,
  ⟨C0228.tokens, C0228.summary⟩,
  ⟨C0229.tokens, C0229.summary⟩,
  ⟨C0230.tokens, C0230.summary⟩,
  ⟨C0231.tokens, C0231.summary⟩,
  ⟨C0232.tokens, C0232.summary⟩,
  ⟨C0233.tokens, C0233.summary⟩,
  ⟨C0234.tokens, C0234.summary⟩,
  ⟨C0235.tokens, C0235.summary⟩,
  ⟨C0236.tokens, C0236.summary⟩,
  ⟨C0237.tokens, C0237.summary⟩,
  ⟨C0238.tokens, C0238.summary⟩,
  ⟨C0239.tokens, C0239.summary⟩,
  ⟨C0240.tokens, C0240.summary⟩,
  ⟨C0241.tokens, C0241.summary⟩,
  ⟨C0242.tokens, C0242.summary⟩,
  ⟨C0243.tokens, C0243.summary⟩,
  ⟨C0244.tokens, C0244.summary⟩,
  ⟨C0245.tokens, C0245.summary⟩,
  ⟨C0246.tokens, C0246.summary⟩,
  ⟨C0247.tokens, C0247.summary⟩,
  ⟨C0248.tokens, C0248.summary⟩,
  ⟨C0249.tokens, C0249.summary⟩,
  ⟨C0250.tokens, C0250.summary⟩,
  ⟨C0251.tokens, C0251.summary⟩,
  ⟨C0252.tokens, C0252.summary⟩,
  ⟨C0253.tokens, C0253.summary⟩,
  ⟨C0254.tokens, C0254.summary⟩,
  ⟨C0255.tokens, C0255.summary⟩]

theorem accepted : ChunksAccepted LL20 2468941825 chunks :=
  ⟨C0224.accepted, C0225.accepted, C0226.accepted, C0227.accepted, C0228.accepted, C0229.accepted, C0230.accepted, C0231.accepted, C0232.accepted, C0233.accepted, C0234.accepted, C0235.accepted, C0236.accepted, C0237.accepted, C0238.accepted, C0239.accepted, C0240.accepted, C0241.accepted, C0242.accepted, C0243.accepted, C0244.accepted, C0245.accepted, C0246.accepted, C0247.accepted, C0248.accepted, C0249.accepted, C0250.accepted, C0251.accepted, C0252.accepted, C0253.accepted, C0254.accepted, C0255.accepted, True.intro⟩

end Sarkozy.F3Kernel.CertificateData.LL20.B007
