module

public import Sarkozy.F3Kernel.ChainAppend
public import Sarkozy.F3Kernel.CertificateData.LL20.C0352
public import Sarkozy.F3Kernel.CertificateData.LL20.C0353
public import Sarkozy.F3Kernel.CertificateData.LL20.C0354
public import Sarkozy.F3Kernel.CertificateData.LL20.C0355
public import Sarkozy.F3Kernel.CertificateData.LL20.C0356
public import Sarkozy.F3Kernel.CertificateData.LL20.C0357
public import Sarkozy.F3Kernel.CertificateData.LL20.C0358
public import Sarkozy.F3Kernel.CertificateData.LL20.C0359
public import Sarkozy.F3Kernel.CertificateData.LL20.C0360
public import Sarkozy.F3Kernel.CertificateData.LL20.C0361
public import Sarkozy.F3Kernel.CertificateData.LL20.C0362
public import Sarkozy.F3Kernel.CertificateData.LL20.C0363
public import Sarkozy.F3Kernel.CertificateData.LL20.C0364
public import Sarkozy.F3Kernel.CertificateData.LL20.C0365
public import Sarkozy.F3Kernel.CertificateData.LL20.C0366
public import Sarkozy.F3Kernel.CertificateData.LL20.C0367
public import Sarkozy.F3Kernel.CertificateData.LL20.C0368
public import Sarkozy.F3Kernel.CertificateData.LL20.C0369
public import Sarkozy.F3Kernel.CertificateData.LL20.C0370
public import Sarkozy.F3Kernel.CertificateData.LL20.C0371
public import Sarkozy.F3Kernel.CertificateData.LL20.C0372
public import Sarkozy.F3Kernel.CertificateData.LL20.C0373
public import Sarkozy.F3Kernel.CertificateData.LL20.C0374
public import Sarkozy.F3Kernel.CertificateData.LL20.C0375
public import Sarkozy.F3Kernel.CertificateData.LL20.C0376
public import Sarkozy.F3Kernel.CertificateData.LL20.C0377
public import Sarkozy.F3Kernel.CertificateData.LL20.C0378
public import Sarkozy.F3Kernel.CertificateData.LL20.C0379
public import Sarkozy.F3Kernel.CertificateData.LL20.C0380
public import Sarkozy.F3Kernel.CertificateData.LL20.C0381
public import Sarkozy.F3Kernel.CertificateData.LL20.C0382
public import Sarkozy.F3Kernel.CertificateData.LL20.C0383


@[expose] public section

set_option maxRecDepth 10000

namespace Sarkozy.F3Kernel.CertificateData.LL20.B011

open Sarkozy.F3Kernel

noncomputable def chunks : List CertificateChunk := [
  ⟨C0352.tokens, C0352.summary⟩,
  ⟨C0353.tokens, C0353.summary⟩,
  ⟨C0354.tokens, C0354.summary⟩,
  ⟨C0355.tokens, C0355.summary⟩,
  ⟨C0356.tokens, C0356.summary⟩,
  ⟨C0357.tokens, C0357.summary⟩,
  ⟨C0358.tokens, C0358.summary⟩,
  ⟨C0359.tokens, C0359.summary⟩,
  ⟨C0360.tokens, C0360.summary⟩,
  ⟨C0361.tokens, C0361.summary⟩,
  ⟨C0362.tokens, C0362.summary⟩,
  ⟨C0363.tokens, C0363.summary⟩,
  ⟨C0364.tokens, C0364.summary⟩,
  ⟨C0365.tokens, C0365.summary⟩,
  ⟨C0366.tokens, C0366.summary⟩,
  ⟨C0367.tokens, C0367.summary⟩,
  ⟨C0368.tokens, C0368.summary⟩,
  ⟨C0369.tokens, C0369.summary⟩,
  ⟨C0370.tokens, C0370.summary⟩,
  ⟨C0371.tokens, C0371.summary⟩,
  ⟨C0372.tokens, C0372.summary⟩,
  ⟨C0373.tokens, C0373.summary⟩,
  ⟨C0374.tokens, C0374.summary⟩,
  ⟨C0375.tokens, C0375.summary⟩,
  ⟨C0376.tokens, C0376.summary⟩,
  ⟨C0377.tokens, C0377.summary⟩,
  ⟨C0378.tokens, C0378.summary⟩,
  ⟨C0379.tokens, C0379.summary⟩,
  ⟨C0380.tokens, C0380.summary⟩,
  ⟨C0381.tokens, C0381.summary⟩,
  ⟨C0382.tokens, C0382.summary⟩,
  ⟨C0383.tokens, C0383.summary⟩]

theorem accepted : ChunksAccepted LL20 6460592129 chunks :=
  ⟨C0352.accepted, C0353.accepted, C0354.accepted, C0355.accepted, C0356.accepted, C0357.accepted, C0358.accepted, C0359.accepted, C0360.accepted, C0361.accepted, C0362.accepted, C0363.accepted, C0364.accepted, C0365.accepted, C0366.accepted, C0367.accepted, C0368.accepted, C0369.accepted, C0370.accepted, C0371.accepted, C0372.accepted, C0373.accepted, C0374.accepted, C0375.accepted, C0376.accepted, C0377.accepted, C0378.accepted, C0379.accepted, C0380.accepted, C0381.accepted, C0382.accepted, C0383.accepted, True.intro⟩

end Sarkozy.F3Kernel.CertificateData.LL20.B011
