module

public import Sarkozy.F3Kernel.ChainAppend
public import Sarkozy.F3Kernel.CertificateData.LL20.C0320
public import Sarkozy.F3Kernel.CertificateData.LL20.C0321
public import Sarkozy.F3Kernel.CertificateData.LL20.C0322
public import Sarkozy.F3Kernel.CertificateData.LL20.C0323
public import Sarkozy.F3Kernel.CertificateData.LL20.C0324
public import Sarkozy.F3Kernel.CertificateData.LL20.C0325
public import Sarkozy.F3Kernel.CertificateData.LL20.C0326
public import Sarkozy.F3Kernel.CertificateData.LL20.C0327
public import Sarkozy.F3Kernel.CertificateData.LL20.C0328
public import Sarkozy.F3Kernel.CertificateData.LL20.C0329
public import Sarkozy.F3Kernel.CertificateData.LL20.C0330
public import Sarkozy.F3Kernel.CertificateData.LL20.C0331
public import Sarkozy.F3Kernel.CertificateData.LL20.C0332
public import Sarkozy.F3Kernel.CertificateData.LL20.C0333
public import Sarkozy.F3Kernel.CertificateData.LL20.C0334
public import Sarkozy.F3Kernel.CertificateData.LL20.C0335
public import Sarkozy.F3Kernel.CertificateData.LL20.C0336
public import Sarkozy.F3Kernel.CertificateData.LL20.C0337
public import Sarkozy.F3Kernel.CertificateData.LL20.C0338
public import Sarkozy.F3Kernel.CertificateData.LL20.C0339
public import Sarkozy.F3Kernel.CertificateData.LL20.C0340
public import Sarkozy.F3Kernel.CertificateData.LL20.C0341
public import Sarkozy.F3Kernel.CertificateData.LL20.C0342
public import Sarkozy.F3Kernel.CertificateData.LL20.C0343
public import Sarkozy.F3Kernel.CertificateData.LL20.C0344
public import Sarkozy.F3Kernel.CertificateData.LL20.C0345
public import Sarkozy.F3Kernel.CertificateData.LL20.C0346
public import Sarkozy.F3Kernel.CertificateData.LL20.C0347
public import Sarkozy.F3Kernel.CertificateData.LL20.C0348
public import Sarkozy.F3Kernel.CertificateData.LL20.C0349
public import Sarkozy.F3Kernel.CertificateData.LL20.C0350
public import Sarkozy.F3Kernel.CertificateData.LL20.C0351


@[expose] public section

set_option maxRecDepth 10000

namespace Sarkozy.F3Kernel.CertificateData.LL20.B010

open Sarkozy.F3Kernel

noncomputable def chunks : List CertificateChunk := [
  ⟨C0320.tokens, C0320.summary⟩,
  ⟨C0321.tokens, C0321.summary⟩,
  ⟨C0322.tokens, C0322.summary⟩,
  ⟨C0323.tokens, C0323.summary⟩,
  ⟨C0324.tokens, C0324.summary⟩,
  ⟨C0325.tokens, C0325.summary⟩,
  ⟨C0326.tokens, C0326.summary⟩,
  ⟨C0327.tokens, C0327.summary⟩,
  ⟨C0328.tokens, C0328.summary⟩,
  ⟨C0329.tokens, C0329.summary⟩,
  ⟨C0330.tokens, C0330.summary⟩,
  ⟨C0331.tokens, C0331.summary⟩,
  ⟨C0332.tokens, C0332.summary⟩,
  ⟨C0333.tokens, C0333.summary⟩,
  ⟨C0334.tokens, C0334.summary⟩,
  ⟨C0335.tokens, C0335.summary⟩,
  ⟨C0336.tokens, C0336.summary⟩,
  ⟨C0337.tokens, C0337.summary⟩,
  ⟨C0338.tokens, C0338.summary⟩,
  ⟨C0339.tokens, C0339.summary⟩,
  ⟨C0340.tokens, C0340.summary⟩,
  ⟨C0341.tokens, C0341.summary⟩,
  ⟨C0342.tokens, C0342.summary⟩,
  ⟨C0343.tokens, C0343.summary⟩,
  ⟨C0344.tokens, C0344.summary⟩,
  ⟨C0345.tokens, C0345.summary⟩,
  ⟨C0346.tokens, C0346.summary⟩,
  ⟨C0347.tokens, C0347.summary⟩,
  ⟨C0348.tokens, C0348.summary⟩,
  ⟨C0349.tokens, C0349.summary⟩,
  ⟨C0350.tokens, C0350.summary⟩,
  ⟨C0351.tokens, C0351.summary⟩]

theorem accepted : ChunksAccepted LL20 4550569986 chunks :=
  ⟨C0320.accepted, C0321.accepted, C0322.accepted, C0323.accepted, C0324.accepted, C0325.accepted, C0326.accepted, C0327.accepted, C0328.accepted, C0329.accepted, C0330.accepted, C0331.accepted, C0332.accepted, C0333.accepted, C0334.accepted, C0335.accepted, C0336.accepted, C0337.accepted, C0338.accepted, C0339.accepted, C0340.accepted, C0341.accepted, C0342.accepted, C0343.accepted, C0344.accepted, C0345.accepted, C0346.accepted, C0347.accepted, C0348.accepted, C0349.accepted, C0350.accepted, C0351.accepted, True.intro⟩

end Sarkozy.F3Kernel.CertificateData.LL20.B010
