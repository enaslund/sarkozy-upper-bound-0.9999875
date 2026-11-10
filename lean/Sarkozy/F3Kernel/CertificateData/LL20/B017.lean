module

public import Sarkozy.F3Kernel.ChainAppend
public import Sarkozy.F3Kernel.CertificateData.LL20.C0544
public import Sarkozy.F3Kernel.CertificateData.LL20.C0545
public import Sarkozy.F3Kernel.CertificateData.LL20.C0546
public import Sarkozy.F3Kernel.CertificateData.LL20.C0547
public import Sarkozy.F3Kernel.CertificateData.LL20.C0548
public import Sarkozy.F3Kernel.CertificateData.LL20.C0549
public import Sarkozy.F3Kernel.CertificateData.LL20.C0550
public import Sarkozy.F3Kernel.CertificateData.LL20.C0551
public import Sarkozy.F3Kernel.CertificateData.LL20.C0552
public import Sarkozy.F3Kernel.CertificateData.LL20.C0553
public import Sarkozy.F3Kernel.CertificateData.LL20.C0554
public import Sarkozy.F3Kernel.CertificateData.LL20.C0555
public import Sarkozy.F3Kernel.CertificateData.LL20.C0556
public import Sarkozy.F3Kernel.CertificateData.LL20.C0557
public import Sarkozy.F3Kernel.CertificateData.LL20.C0558
public import Sarkozy.F3Kernel.CertificateData.LL20.C0559
public import Sarkozy.F3Kernel.CertificateData.LL20.C0560
public import Sarkozy.F3Kernel.CertificateData.LL20.C0561
public import Sarkozy.F3Kernel.CertificateData.LL20.C0562
public import Sarkozy.F3Kernel.CertificateData.LL20.C0563
public import Sarkozy.F3Kernel.CertificateData.LL20.C0564
public import Sarkozy.F3Kernel.CertificateData.LL20.C0565
public import Sarkozy.F3Kernel.CertificateData.LL20.C0566
public import Sarkozy.F3Kernel.CertificateData.LL20.C0567
public import Sarkozy.F3Kernel.CertificateData.LL20.C0568
public import Sarkozy.F3Kernel.CertificateData.LL20.C0569
public import Sarkozy.F3Kernel.CertificateData.LL20.C0570
public import Sarkozy.F3Kernel.CertificateData.LL20.C0571
public import Sarkozy.F3Kernel.CertificateData.LL20.C0572
public import Sarkozy.F3Kernel.CertificateData.LL20.C0573
public import Sarkozy.F3Kernel.CertificateData.LL20.C0574
public import Sarkozy.F3Kernel.CertificateData.LL20.C0575


@[expose] public section

set_option maxRecDepth 10000

namespace Sarkozy.F3Kernel.CertificateData.LL20.B017

open Sarkozy.F3Kernel

noncomputable def chunks : List CertificateChunk := [
  ⟨C0544.tokens, C0544.summary⟩,
  ⟨C0545.tokens, C0545.summary⟩,
  ⟨C0546.tokens, C0546.summary⟩,
  ⟨C0547.tokens, C0547.summary⟩,
  ⟨C0548.tokens, C0548.summary⟩,
  ⟨C0549.tokens, C0549.summary⟩,
  ⟨C0550.tokens, C0550.summary⟩,
  ⟨C0551.tokens, C0551.summary⟩,
  ⟨C0552.tokens, C0552.summary⟩,
  ⟨C0553.tokens, C0553.summary⟩,
  ⟨C0554.tokens, C0554.summary⟩,
  ⟨C0555.tokens, C0555.summary⟩,
  ⟨C0556.tokens, C0556.summary⟩,
  ⟨C0557.tokens, C0557.summary⟩,
  ⟨C0558.tokens, C0558.summary⟩,
  ⟨C0559.tokens, C0559.summary⟩,
  ⟨C0560.tokens, C0560.summary⟩,
  ⟨C0561.tokens, C0561.summary⟩,
  ⟨C0562.tokens, C0562.summary⟩,
  ⟨C0563.tokens, C0563.summary⟩,
  ⟨C0564.tokens, C0564.summary⟩,
  ⟨C0565.tokens, C0565.summary⟩,
  ⟨C0566.tokens, C0566.summary⟩,
  ⟨C0567.tokens, C0567.summary⟩,
  ⟨C0568.tokens, C0568.summary⟩,
  ⟨C0569.tokens, C0569.summary⟩,
  ⟨C0570.tokens, C0570.summary⟩,
  ⟨C0571.tokens, C0571.summary⟩,
  ⟨C0572.tokens, C0572.summary⟩,
  ⟨C0573.tokens, C0573.summary⟩,
  ⟨C0574.tokens, C0574.summary⟩,
  ⟨C0575.tokens, C0575.summary⟩]

theorem accepted : ChunksAccepted LL20 13273157633 chunks :=
  ⟨C0544.accepted, C0545.accepted, C0546.accepted, C0547.accepted, C0548.accepted, C0549.accepted, C0550.accepted, C0551.accepted, C0552.accepted, C0553.accepted, C0554.accepted, C0555.accepted, C0556.accepted, C0557.accepted, C0558.accepted, C0559.accepted, C0560.accepted, C0561.accepted, C0562.accepted, C0563.accepted, C0564.accepted, C0565.accepted, C0566.accepted, C0567.accepted, C0568.accepted, C0569.accepted, C0570.accepted, C0571.accepted, C0572.accepted, C0573.accepted, C0574.accepted, C0575.accepted, True.intro⟩

end Sarkozy.F3Kernel.CertificateData.LL20.B017
