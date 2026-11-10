module

public import Sarkozy.F3Kernel.ChainAppend
public import Sarkozy.F3Kernel.CertificateData.LL20.C0448
public import Sarkozy.F3Kernel.CertificateData.LL20.C0449
public import Sarkozy.F3Kernel.CertificateData.LL20.C0450
public import Sarkozy.F3Kernel.CertificateData.LL20.C0451
public import Sarkozy.F3Kernel.CertificateData.LL20.C0452
public import Sarkozy.F3Kernel.CertificateData.LL20.C0453
public import Sarkozy.F3Kernel.CertificateData.LL20.C0454
public import Sarkozy.F3Kernel.CertificateData.LL20.C0455
public import Sarkozy.F3Kernel.CertificateData.LL20.C0456
public import Sarkozy.F3Kernel.CertificateData.LL20.C0457
public import Sarkozy.F3Kernel.CertificateData.LL20.C0458
public import Sarkozy.F3Kernel.CertificateData.LL20.C0459
public import Sarkozy.F3Kernel.CertificateData.LL20.C0460
public import Sarkozy.F3Kernel.CertificateData.LL20.C0461
public import Sarkozy.F3Kernel.CertificateData.LL20.C0462
public import Sarkozy.F3Kernel.CertificateData.LL20.C0463
public import Sarkozy.F3Kernel.CertificateData.LL20.C0464
public import Sarkozy.F3Kernel.CertificateData.LL20.C0465
public import Sarkozy.F3Kernel.CertificateData.LL20.C0466
public import Sarkozy.F3Kernel.CertificateData.LL20.C0467
public import Sarkozy.F3Kernel.CertificateData.LL20.C0468
public import Sarkozy.F3Kernel.CertificateData.LL20.C0469
public import Sarkozy.F3Kernel.CertificateData.LL20.C0470
public import Sarkozy.F3Kernel.CertificateData.LL20.C0471
public import Sarkozy.F3Kernel.CertificateData.LL20.C0472
public import Sarkozy.F3Kernel.CertificateData.LL20.C0473
public import Sarkozy.F3Kernel.CertificateData.LL20.C0474
public import Sarkozy.F3Kernel.CertificateData.LL20.C0475
public import Sarkozy.F3Kernel.CertificateData.LL20.C0476
public import Sarkozy.F3Kernel.CertificateData.LL20.C0477
public import Sarkozy.F3Kernel.CertificateData.LL20.C0478
public import Sarkozy.F3Kernel.CertificateData.LL20.C0479


@[expose] public section

set_option maxRecDepth 10000

namespace Sarkozy.F3Kernel.CertificateData.LL20.B014

open Sarkozy.F3Kernel

noncomputable def chunks : List CertificateChunk := [
  ⟨C0448.tokens, C0448.summary⟩,
  ⟨C0449.tokens, C0449.summary⟩,
  ⟨C0450.tokens, C0450.summary⟩,
  ⟨C0451.tokens, C0451.summary⟩,
  ⟨C0452.tokens, C0452.summary⟩,
  ⟨C0453.tokens, C0453.summary⟩,
  ⟨C0454.tokens, C0454.summary⟩,
  ⟨C0455.tokens, C0455.summary⟩,
  ⟨C0456.tokens, C0456.summary⟩,
  ⟨C0457.tokens, C0457.summary⟩,
  ⟨C0458.tokens, C0458.summary⟩,
  ⟨C0459.tokens, C0459.summary⟩,
  ⟨C0460.tokens, C0460.summary⟩,
  ⟨C0461.tokens, C0461.summary⟩,
  ⟨C0462.tokens, C0462.summary⟩,
  ⟨C0463.tokens, C0463.summary⟩,
  ⟨C0464.tokens, C0464.summary⟩,
  ⟨C0465.tokens, C0465.summary⟩,
  ⟨C0466.tokens, C0466.summary⟩,
  ⟨C0467.tokens, C0467.summary⟩,
  ⟨C0468.tokens, C0468.summary⟩,
  ⟨C0469.tokens, C0469.summary⟩,
  ⟨C0470.tokens, C0470.summary⟩,
  ⟨C0471.tokens, C0471.summary⟩,
  ⟨C0472.tokens, C0472.summary⟩,
  ⟨C0473.tokens, C0473.summary⟩,
  ⟨C0474.tokens, C0474.summary⟩,
  ⟨C0475.tokens, C0475.summary⟩,
  ⟨C0476.tokens, C0476.summary⟩,
  ⟨C0477.tokens, C0477.summary⟩,
  ⟨C0478.tokens, C0478.summary⟩,
  ⟨C0479.tokens, C0479.summary⟩]

theorem accepted : ChunksAccepted LL20 8708722689 chunks :=
  ⟨C0448.accepted, C0449.accepted, C0450.accepted, C0451.accepted, C0452.accepted, C0453.accepted, C0454.accepted, C0455.accepted, C0456.accepted, C0457.accepted, C0458.accepted, C0459.accepted, C0460.accepted, C0461.accepted, C0462.accepted, C0463.accepted, C0464.accepted, C0465.accepted, C0466.accepted, C0467.accepted, C0468.accepted, C0469.accepted, C0470.accepted, C0471.accepted, C0472.accepted, C0473.accepted, C0474.accepted, C0475.accepted, C0476.accepted, C0477.accepted, C0478.accepted, C0479.accepted, True.intro⟩

end Sarkozy.F3Kernel.CertificateData.LL20.B014
