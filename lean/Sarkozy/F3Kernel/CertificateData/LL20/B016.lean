module

public import Sarkozy.F3Kernel.ChainAppend
public import Sarkozy.F3Kernel.CertificateData.LL20.C0512
public import Sarkozy.F3Kernel.CertificateData.LL20.C0513
public import Sarkozy.F3Kernel.CertificateData.LL20.C0514
public import Sarkozy.F3Kernel.CertificateData.LL20.C0515
public import Sarkozy.F3Kernel.CertificateData.LL20.C0516
public import Sarkozy.F3Kernel.CertificateData.LL20.C0517
public import Sarkozy.F3Kernel.CertificateData.LL20.C0518
public import Sarkozy.F3Kernel.CertificateData.LL20.C0519
public import Sarkozy.F3Kernel.CertificateData.LL20.C0520
public import Sarkozy.F3Kernel.CertificateData.LL20.C0521
public import Sarkozy.F3Kernel.CertificateData.LL20.C0522
public import Sarkozy.F3Kernel.CertificateData.LL20.C0523
public import Sarkozy.F3Kernel.CertificateData.LL20.C0524
public import Sarkozy.F3Kernel.CertificateData.LL20.C0525
public import Sarkozy.F3Kernel.CertificateData.LL20.C0526
public import Sarkozy.F3Kernel.CertificateData.LL20.C0527
public import Sarkozy.F3Kernel.CertificateData.LL20.C0528
public import Sarkozy.F3Kernel.CertificateData.LL20.C0529
public import Sarkozy.F3Kernel.CertificateData.LL20.C0530
public import Sarkozy.F3Kernel.CertificateData.LL20.C0531
public import Sarkozy.F3Kernel.CertificateData.LL20.C0532
public import Sarkozy.F3Kernel.CertificateData.LL20.C0533
public import Sarkozy.F3Kernel.CertificateData.LL20.C0534
public import Sarkozy.F3Kernel.CertificateData.LL20.C0535
public import Sarkozy.F3Kernel.CertificateData.LL20.C0536
public import Sarkozy.F3Kernel.CertificateData.LL20.C0537
public import Sarkozy.F3Kernel.CertificateData.LL20.C0538
public import Sarkozy.F3Kernel.CertificateData.LL20.C0539
public import Sarkozy.F3Kernel.CertificateData.LL20.C0540
public import Sarkozy.F3Kernel.CertificateData.LL20.C0541
public import Sarkozy.F3Kernel.CertificateData.LL20.C0542
public import Sarkozy.F3Kernel.CertificateData.LL20.C0543


@[expose] public section

set_option maxRecDepth 10000

namespace Sarkozy.F3Kernel.CertificateData.LL20.B016

open Sarkozy.F3Kernel

noncomputable def chunks : List CertificateChunk := [
  ⟨C0512.tokens, C0512.summary⟩,
  ⟨C0513.tokens, C0513.summary⟩,
  ⟨C0514.tokens, C0514.summary⟩,
  ⟨C0515.tokens, C0515.summary⟩,
  ⟨C0516.tokens, C0516.summary⟩,
  ⟨C0517.tokens, C0517.summary⟩,
  ⟨C0518.tokens, C0518.summary⟩,
  ⟨C0519.tokens, C0519.summary⟩,
  ⟨C0520.tokens, C0520.summary⟩,
  ⟨C0521.tokens, C0521.summary⟩,
  ⟨C0522.tokens, C0522.summary⟩,
  ⟨C0523.tokens, C0523.summary⟩,
  ⟨C0524.tokens, C0524.summary⟩,
  ⟨C0525.tokens, C0525.summary⟩,
  ⟨C0526.tokens, C0526.summary⟩,
  ⟨C0527.tokens, C0527.summary⟩,
  ⟨C0528.tokens, C0528.summary⟩,
  ⟨C0529.tokens, C0529.summary⟩,
  ⟨C0530.tokens, C0530.summary⟩,
  ⟨C0531.tokens, C0531.summary⟩,
  ⟨C0532.tokens, C0532.summary⟩,
  ⟨C0533.tokens, C0533.summary⟩,
  ⟨C0534.tokens, C0534.summary⟩,
  ⟨C0535.tokens, C0535.summary⟩,
  ⟨C0536.tokens, C0536.summary⟩,
  ⟨C0537.tokens, C0537.summary⟩,
  ⟨C0538.tokens, C0538.summary⟩,
  ⟨C0539.tokens, C0539.summary⟩,
  ⟨C0540.tokens, C0540.summary⟩,
  ⟨C0541.tokens, C0541.summary⟩,
  ⟨C0542.tokens, C0542.summary⟩,
  ⟨C0543.tokens, C0543.summary⟩]

theorem accepted : ChunksAccepted LL20 11161567233 chunks :=
  ⟨C0512.accepted, C0513.accepted, C0514.accepted, C0515.accepted, C0516.accepted, C0517.accepted, C0518.accepted, C0519.accepted, C0520.accepted, C0521.accepted, C0522.accepted, C0523.accepted, C0524.accepted, C0525.accepted, C0526.accepted, C0527.accepted, C0528.accepted, C0529.accepted, C0530.accepted, C0531.accepted, C0532.accepted, C0533.accepted, C0534.accepted, C0535.accepted, C0536.accepted, C0537.accepted, C0538.accepted, C0539.accepted, C0540.accepted, C0541.accepted, C0542.accepted, C0543.accepted, True.intro⟩

end Sarkozy.F3Kernel.CertificateData.LL20.B016
