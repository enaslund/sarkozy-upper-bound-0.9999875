module

public import Sarkozy.F3Kernel.ChainAppend
public import Sarkozy.F3Kernel.CertificateData.LL20.C0384
public import Sarkozy.F3Kernel.CertificateData.LL20.C0385
public import Sarkozy.F3Kernel.CertificateData.LL20.C0386
public import Sarkozy.F3Kernel.CertificateData.LL20.C0387
public import Sarkozy.F3Kernel.CertificateData.LL20.C0388
public import Sarkozy.F3Kernel.CertificateData.LL20.C0389
public import Sarkozy.F3Kernel.CertificateData.LL20.C0390
public import Sarkozy.F3Kernel.CertificateData.LL20.C0391
public import Sarkozy.F3Kernel.CertificateData.LL20.C0392
public import Sarkozy.F3Kernel.CertificateData.LL20.C0393
public import Sarkozy.F3Kernel.CertificateData.LL20.C0394
public import Sarkozy.F3Kernel.CertificateData.LL20.C0395
public import Sarkozy.F3Kernel.CertificateData.LL20.C0396
public import Sarkozy.F3Kernel.CertificateData.LL20.C0397
public import Sarkozy.F3Kernel.CertificateData.LL20.C0398
public import Sarkozy.F3Kernel.CertificateData.LL20.C0399
public import Sarkozy.F3Kernel.CertificateData.LL20.C0400
public import Sarkozy.F3Kernel.CertificateData.LL20.C0401
public import Sarkozy.F3Kernel.CertificateData.LL20.C0402
public import Sarkozy.F3Kernel.CertificateData.LL20.C0403
public import Sarkozy.F3Kernel.CertificateData.LL20.C0404
public import Sarkozy.F3Kernel.CertificateData.LL20.C0405
public import Sarkozy.F3Kernel.CertificateData.LL20.C0406
public import Sarkozy.F3Kernel.CertificateData.LL20.C0407
public import Sarkozy.F3Kernel.CertificateData.LL20.C0408
public import Sarkozy.F3Kernel.CertificateData.LL20.C0409
public import Sarkozy.F3Kernel.CertificateData.LL20.C0410
public import Sarkozy.F3Kernel.CertificateData.LL20.C0411
public import Sarkozy.F3Kernel.CertificateData.LL20.C0412
public import Sarkozy.F3Kernel.CertificateData.LL20.C0413
public import Sarkozy.F3Kernel.CertificateData.LL20.C0414
public import Sarkozy.F3Kernel.CertificateData.LL20.C0415


@[expose] public section

set_option maxRecDepth 10000

namespace Sarkozy.F3Kernel.CertificateData.LL20.B012

open Sarkozy.F3Kernel

noncomputable def chunks : List CertificateChunk := [
  ⟨C0384.tokens, C0384.summary⟩,
  ⟨C0385.tokens, C0385.summary⟩,
  ⟨C0386.tokens, C0386.summary⟩,
  ⟨C0387.tokens, C0387.summary⟩,
  ⟨C0388.tokens, C0388.summary⟩,
  ⟨C0389.tokens, C0389.summary⟩,
  ⟨C0390.tokens, C0390.summary⟩,
  ⟨C0391.tokens, C0391.summary⟩,
  ⟨C0392.tokens, C0392.summary⟩,
  ⟨C0393.tokens, C0393.summary⟩,
  ⟨C0394.tokens, C0394.summary⟩,
  ⟨C0395.tokens, C0395.summary⟩,
  ⟨C0396.tokens, C0396.summary⟩,
  ⟨C0397.tokens, C0397.summary⟩,
  ⟨C0398.tokens, C0398.summary⟩,
  ⟨C0399.tokens, C0399.summary⟩,
  ⟨C0400.tokens, C0400.summary⟩,
  ⟨C0401.tokens, C0401.summary⟩,
  ⟨C0402.tokens, C0402.summary⟩,
  ⟨C0403.tokens, C0403.summary⟩,
  ⟨C0404.tokens, C0404.summary⟩,
  ⟨C0405.tokens, C0405.summary⟩,
  ⟨C0406.tokens, C0406.summary⟩,
  ⟨C0407.tokens, C0407.summary⟩,
  ⟨C0408.tokens, C0408.summary⟩,
  ⟨C0409.tokens, C0409.summary⟩,
  ⟨C0410.tokens, C0410.summary⟩,
  ⟨C0411.tokens, C0411.summary⟩,
  ⟨C0412.tokens, C0412.summary⟩,
  ⟨C0413.tokens, C0413.summary⟩,
  ⟨C0414.tokens, C0414.summary⟩,
  ⟨C0415.tokens, C0415.summary⟩]

theorem accepted : ChunksAccepted LL20 6518218974 chunks :=
  ⟨C0384.accepted, C0385.accepted, C0386.accepted, C0387.accepted, C0388.accepted, C0389.accepted, C0390.accepted, C0391.accepted, C0392.accepted, C0393.accepted, C0394.accepted, C0395.accepted, C0396.accepted, C0397.accepted, C0398.accepted, C0399.accepted, C0400.accepted, C0401.accepted, C0402.accepted, C0403.accepted, C0404.accepted, C0405.accepted, C0406.accepted, C0407.accepted, C0408.accepted, C0409.accepted, C0410.accepted, C0411.accepted, C0412.accepted, C0413.accepted, C0414.accepted, C0415.accepted, True.intro⟩

end Sarkozy.F3Kernel.CertificateData.LL20.B012
