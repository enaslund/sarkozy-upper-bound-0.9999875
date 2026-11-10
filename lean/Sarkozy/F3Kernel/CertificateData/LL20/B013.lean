module

public import Sarkozy.F3Kernel.ChainAppend
public import Sarkozy.F3Kernel.CertificateData.LL20.C0416
public import Sarkozy.F3Kernel.CertificateData.LL20.C0417
public import Sarkozy.F3Kernel.CertificateData.LL20.C0418
public import Sarkozy.F3Kernel.CertificateData.LL20.C0419
public import Sarkozy.F3Kernel.CertificateData.LL20.C0420
public import Sarkozy.F3Kernel.CertificateData.LL20.C0421
public import Sarkozy.F3Kernel.CertificateData.LL20.C0422
public import Sarkozy.F3Kernel.CertificateData.LL20.C0423
public import Sarkozy.F3Kernel.CertificateData.LL20.C0424
public import Sarkozy.F3Kernel.CertificateData.LL20.C0425
public import Sarkozy.F3Kernel.CertificateData.LL20.C0426
public import Sarkozy.F3Kernel.CertificateData.LL20.C0427
public import Sarkozy.F3Kernel.CertificateData.LL20.C0428
public import Sarkozy.F3Kernel.CertificateData.LL20.C0429
public import Sarkozy.F3Kernel.CertificateData.LL20.C0430
public import Sarkozy.F3Kernel.CertificateData.LL20.C0431
public import Sarkozy.F3Kernel.CertificateData.LL20.C0432
public import Sarkozy.F3Kernel.CertificateData.LL20.C0433
public import Sarkozy.F3Kernel.CertificateData.LL20.C0434
public import Sarkozy.F3Kernel.CertificateData.LL20.C0435
public import Sarkozy.F3Kernel.CertificateData.LL20.C0436
public import Sarkozy.F3Kernel.CertificateData.LL20.C0437
public import Sarkozy.F3Kernel.CertificateData.LL20.C0438
public import Sarkozy.F3Kernel.CertificateData.LL20.C0439
public import Sarkozy.F3Kernel.CertificateData.LL20.C0440
public import Sarkozy.F3Kernel.CertificateData.LL20.C0441
public import Sarkozy.F3Kernel.CertificateData.LL20.C0442
public import Sarkozy.F3Kernel.CertificateData.LL20.C0443
public import Sarkozy.F3Kernel.CertificateData.LL20.C0444
public import Sarkozy.F3Kernel.CertificateData.LL20.C0445
public import Sarkozy.F3Kernel.CertificateData.LL20.C0446
public import Sarkozy.F3Kernel.CertificateData.LL20.C0447


@[expose] public section

set_option maxRecDepth 10000

namespace Sarkozy.F3Kernel.CertificateData.LL20.B013

open Sarkozy.F3Kernel

noncomputable def chunks : List CertificateChunk := [
  ⟨C0416.tokens, C0416.summary⟩,
  ⟨C0417.tokens, C0417.summary⟩,
  ⟨C0418.tokens, C0418.summary⟩,
  ⟨C0419.tokens, C0419.summary⟩,
  ⟨C0420.tokens, C0420.summary⟩,
  ⟨C0421.tokens, C0421.summary⟩,
  ⟨C0422.tokens, C0422.summary⟩,
  ⟨C0423.tokens, C0423.summary⟩,
  ⟨C0424.tokens, C0424.summary⟩,
  ⟨C0425.tokens, C0425.summary⟩,
  ⟨C0426.tokens, C0426.summary⟩,
  ⟨C0427.tokens, C0427.summary⟩,
  ⟨C0428.tokens, C0428.summary⟩,
  ⟨C0429.tokens, C0429.summary⟩,
  ⟨C0430.tokens, C0430.summary⟩,
  ⟨C0431.tokens, C0431.summary⟩,
  ⟨C0432.tokens, C0432.summary⟩,
  ⟨C0433.tokens, C0433.summary⟩,
  ⟨C0434.tokens, C0434.summary⟩,
  ⟨C0435.tokens, C0435.summary⟩,
  ⟨C0436.tokens, C0436.summary⟩,
  ⟨C0437.tokens, C0437.summary⟩,
  ⟨C0438.tokens, C0438.summary⟩,
  ⟨C0439.tokens, C0439.summary⟩,
  ⟨C0440.tokens, C0440.summary⟩,
  ⟨C0441.tokens, C0441.summary⟩,
  ⟨C0442.tokens, C0442.summary⟩,
  ⟨C0443.tokens, C0443.summary⟩,
  ⟨C0444.tokens, C0444.summary⟩,
  ⟨C0445.tokens, C0445.summary⟩,
  ⟨C0446.tokens, C0446.summary⟩,
  ⟨C0447.tokens, C0447.summary⟩]

theorem accepted : ChunksAccepted LL20 6970159105 chunks :=
  ⟨C0416.accepted, C0417.accepted, C0418.accepted, C0419.accepted, C0420.accepted, C0421.accepted, C0422.accepted, C0423.accepted, C0424.accepted, C0425.accepted, C0426.accepted, C0427.accepted, C0428.accepted, C0429.accepted, C0430.accepted, C0431.accepted, C0432.accepted, C0433.accepted, C0434.accepted, C0435.accepted, C0436.accepted, C0437.accepted, C0438.accepted, C0439.accepted, C0440.accepted, C0441.accepted, C0442.accepted, C0443.accepted, C0444.accepted, C0445.accepted, C0446.accepted, C0447.accepted, True.intro⟩

end Sarkozy.F3Kernel.CertificateData.LL20.B013
