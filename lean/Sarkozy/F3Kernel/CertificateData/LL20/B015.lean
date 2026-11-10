module

public import Sarkozy.F3Kernel.ChainAppend
public import Sarkozy.F3Kernel.CertificateData.LL20.C0480
public import Sarkozy.F3Kernel.CertificateData.LL20.C0481
public import Sarkozy.F3Kernel.CertificateData.LL20.C0482
public import Sarkozy.F3Kernel.CertificateData.LL20.C0483
public import Sarkozy.F3Kernel.CertificateData.LL20.C0484
public import Sarkozy.F3Kernel.CertificateData.LL20.C0485
public import Sarkozy.F3Kernel.CertificateData.LL20.C0486
public import Sarkozy.F3Kernel.CertificateData.LL20.C0487
public import Sarkozy.F3Kernel.CertificateData.LL20.C0488
public import Sarkozy.F3Kernel.CertificateData.LL20.C0489
public import Sarkozy.F3Kernel.CertificateData.LL20.C0490
public import Sarkozy.F3Kernel.CertificateData.LL20.C0491
public import Sarkozy.F3Kernel.CertificateData.LL20.C0492
public import Sarkozy.F3Kernel.CertificateData.LL20.C0493
public import Sarkozy.F3Kernel.CertificateData.LL20.C0494
public import Sarkozy.F3Kernel.CertificateData.LL20.C0495
public import Sarkozy.F3Kernel.CertificateData.LL20.C0496
public import Sarkozy.F3Kernel.CertificateData.LL20.C0497
public import Sarkozy.F3Kernel.CertificateData.LL20.C0498
public import Sarkozy.F3Kernel.CertificateData.LL20.C0499
public import Sarkozy.F3Kernel.CertificateData.LL20.C0500
public import Sarkozy.F3Kernel.CertificateData.LL20.C0501
public import Sarkozy.F3Kernel.CertificateData.LL20.C0502
public import Sarkozy.F3Kernel.CertificateData.LL20.C0503
public import Sarkozy.F3Kernel.CertificateData.LL20.C0504
public import Sarkozy.F3Kernel.CertificateData.LL20.C0505
public import Sarkozy.F3Kernel.CertificateData.LL20.C0506
public import Sarkozy.F3Kernel.CertificateData.LL20.C0507
public import Sarkozy.F3Kernel.CertificateData.LL20.C0508
public import Sarkozy.F3Kernel.CertificateData.LL20.C0509
public import Sarkozy.F3Kernel.CertificateData.LL20.C0510
public import Sarkozy.F3Kernel.CertificateData.LL20.C0511


@[expose] public section

set_option maxRecDepth 10000

namespace Sarkozy.F3Kernel.CertificateData.LL20.B015

open Sarkozy.F3Kernel

noncomputable def chunks : List CertificateChunk := [
  ⟨C0480.tokens, C0480.summary⟩,
  ⟨C0481.tokens, C0481.summary⟩,
  ⟨C0482.tokens, C0482.summary⟩,
  ⟨C0483.tokens, C0483.summary⟩,
  ⟨C0484.tokens, C0484.summary⟩,
  ⟨C0485.tokens, C0485.summary⟩,
  ⟨C0486.tokens, C0486.summary⟩,
  ⟨C0487.tokens, C0487.summary⟩,
  ⟨C0488.tokens, C0488.summary⟩,
  ⟨C0489.tokens, C0489.summary⟩,
  ⟨C0490.tokens, C0490.summary⟩,
  ⟨C0491.tokens, C0491.summary⟩,
  ⟨C0492.tokens, C0492.summary⟩,
  ⟨C0493.tokens, C0493.summary⟩,
  ⟨C0494.tokens, C0494.summary⟩,
  ⟨C0495.tokens, C0495.summary⟩,
  ⟨C0496.tokens, C0496.summary⟩,
  ⟨C0497.tokens, C0497.summary⟩,
  ⟨C0498.tokens, C0498.summary⟩,
  ⟨C0499.tokens, C0499.summary⟩,
  ⟨C0500.tokens, C0500.summary⟩,
  ⟨C0501.tokens, C0501.summary⟩,
  ⟨C0502.tokens, C0502.summary⟩,
  ⟨C0503.tokens, C0503.summary⟩,
  ⟨C0504.tokens, C0504.summary⟩,
  ⟨C0505.tokens, C0505.summary⟩,
  ⟨C0506.tokens, C0506.summary⟩,
  ⟨C0507.tokens, C0507.summary⟩,
  ⟨C0508.tokens, C0508.summary⟩,
  ⟨C0509.tokens, C0509.summary⟩,
  ⟨C0510.tokens, C0510.summary⟩,
  ⟨C0511.tokens, C0511.summary⟩]

theorem accepted : ChunksAccepted LL20 11057823746 chunks :=
  ⟨C0480.accepted, C0481.accepted, C0482.accepted, C0483.accepted, C0484.accepted, C0485.accepted, C0486.accepted, C0487.accepted, C0488.accepted, C0489.accepted, C0490.accepted, C0491.accepted, C0492.accepted, C0493.accepted, C0494.accepted, C0495.accepted, C0496.accepted, C0497.accepted, C0498.accepted, C0499.accepted, C0500.accepted, C0501.accepted, C0502.accepted, C0503.accepted, C0504.accepted, C0505.accepted, C0506.accepted, C0507.accepted, C0508.accepted, C0509.accepted, C0510.accepted, C0511.accepted, True.intro⟩

end Sarkozy.F3Kernel.CertificateData.LL20.B015
