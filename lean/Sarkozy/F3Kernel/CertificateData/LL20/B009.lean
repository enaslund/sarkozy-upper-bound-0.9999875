module

public import Sarkozy.F3Kernel.ChainAppend
public import Sarkozy.F3Kernel.CertificateData.LL20.C0288
public import Sarkozy.F3Kernel.CertificateData.LL20.C0289
public import Sarkozy.F3Kernel.CertificateData.LL20.C0290
public import Sarkozy.F3Kernel.CertificateData.LL20.C0291
public import Sarkozy.F3Kernel.CertificateData.LL20.C0292
public import Sarkozy.F3Kernel.CertificateData.LL20.C0293
public import Sarkozy.F3Kernel.CertificateData.LL20.C0294
public import Sarkozy.F3Kernel.CertificateData.LL20.C0295
public import Sarkozy.F3Kernel.CertificateData.LL20.C0296
public import Sarkozy.F3Kernel.CertificateData.LL20.C0297
public import Sarkozy.F3Kernel.CertificateData.LL20.C0298
public import Sarkozy.F3Kernel.CertificateData.LL20.C0299
public import Sarkozy.F3Kernel.CertificateData.LL20.C0300
public import Sarkozy.F3Kernel.CertificateData.LL20.C0301
public import Sarkozy.F3Kernel.CertificateData.LL20.C0302
public import Sarkozy.F3Kernel.CertificateData.LL20.C0303
public import Sarkozy.F3Kernel.CertificateData.LL20.C0304
public import Sarkozy.F3Kernel.CertificateData.LL20.C0305
public import Sarkozy.F3Kernel.CertificateData.LL20.C0306
public import Sarkozy.F3Kernel.CertificateData.LL20.C0307
public import Sarkozy.F3Kernel.CertificateData.LL20.C0308
public import Sarkozy.F3Kernel.CertificateData.LL20.C0309
public import Sarkozy.F3Kernel.CertificateData.LL20.C0310
public import Sarkozy.F3Kernel.CertificateData.LL20.C0311
public import Sarkozy.F3Kernel.CertificateData.LL20.C0312
public import Sarkozy.F3Kernel.CertificateData.LL20.C0313
public import Sarkozy.F3Kernel.CertificateData.LL20.C0314
public import Sarkozy.F3Kernel.CertificateData.LL20.C0315
public import Sarkozy.F3Kernel.CertificateData.LL20.C0316
public import Sarkozy.F3Kernel.CertificateData.LL20.C0317
public import Sarkozy.F3Kernel.CertificateData.LL20.C0318
public import Sarkozy.F3Kernel.CertificateData.LL20.C0319


@[expose] public section

set_option maxRecDepth 10000

namespace Sarkozy.F3Kernel.CertificateData.LL20.B009

open Sarkozy.F3Kernel

noncomputable def chunks : List CertificateChunk := [
  ⟨C0288.tokens, C0288.summary⟩,
  ⟨C0289.tokens, C0289.summary⟩,
  ⟨C0290.tokens, C0290.summary⟩,
  ⟨C0291.tokens, C0291.summary⟩,
  ⟨C0292.tokens, C0292.summary⟩,
  ⟨C0293.tokens, C0293.summary⟩,
  ⟨C0294.tokens, C0294.summary⟩,
  ⟨C0295.tokens, C0295.summary⟩,
  ⟨C0296.tokens, C0296.summary⟩,
  ⟨C0297.tokens, C0297.summary⟩,
  ⟨C0298.tokens, C0298.summary⟩,
  ⟨C0299.tokens, C0299.summary⟩,
  ⟨C0300.tokens, C0300.summary⟩,
  ⟨C0301.tokens, C0301.summary⟩,
  ⟨C0302.tokens, C0302.summary⟩,
  ⟨C0303.tokens, C0303.summary⟩,
  ⟨C0304.tokens, C0304.summary⟩,
  ⟨C0305.tokens, C0305.summary⟩,
  ⟨C0306.tokens, C0306.summary⟩,
  ⟨C0307.tokens, C0307.summary⟩,
  ⟨C0308.tokens, C0308.summary⟩,
  ⟨C0309.tokens, C0309.summary⟩,
  ⟨C0310.tokens, C0310.summary⟩,
  ⟨C0311.tokens, C0311.summary⟩,
  ⟨C0312.tokens, C0312.summary⟩,
  ⟨C0313.tokens, C0313.summary⟩,
  ⟨C0314.tokens, C0314.summary⟩,
  ⟨C0315.tokens, C0315.summary⟩,
  ⟨C0316.tokens, C0316.summary⟩,
  ⟨C0317.tokens, C0317.summary⟩,
  ⟨C0318.tokens, C0318.summary⟩,
  ⟨C0319.tokens, C0319.summary⟩]

theorem accepted : ChunksAccepted LL20 4413853699 chunks :=
  ⟨C0288.accepted, C0289.accepted, C0290.accepted, C0291.accepted, C0292.accepted, C0293.accepted, C0294.accepted, C0295.accepted, C0296.accepted, C0297.accepted, C0298.accepted, C0299.accepted, C0300.accepted, C0301.accepted, C0302.accepted, C0303.accepted, C0304.accepted, C0305.accepted, C0306.accepted, C0307.accepted, C0308.accepted, C0309.accepted, C0310.accepted, C0311.accepted, C0312.accepted, C0313.accepted, C0314.accepted, C0315.accepted, C0316.accepted, C0317.accepted, C0318.accepted, C0319.accepted, True.intro⟩

end Sarkozy.F3Kernel.CertificateData.LL20.B009
