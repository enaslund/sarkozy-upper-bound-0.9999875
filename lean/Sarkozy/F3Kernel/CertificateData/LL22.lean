module

public import Sarkozy.F3Kernel.CertificateData.LL22.B000
public import Sarkozy.F3Kernel.CertificateData.LL22.B001
public import Sarkozy.F3Kernel.CertificateData.LL22.B002
public import Sarkozy.F3Kernel.CertificateData.LL22.B003
public import Sarkozy.F3Kernel.CertificateData.LL22.B004
public import Sarkozy.F3Kernel.CertificateData.LL22.B005
public import Sarkozy.F3Kernel.CertificateData.LL22.B006


@[expose] public section

set_option maxRecDepth 10000

namespace Sarkozy.F3Kernel.CertificateData.LL22

open Sarkozy.F3Kernel

noncomputable def chunks : List CertificateChunk :=
  B000.chunks ++
  (B001.chunks ++
  (B002.chunks ++
  (B003.chunks ++
  (B004.chunks ++
  (B005.chunks ++
  (B006.chunks))))))

theorem accepted : ChunksAccepted LL22 0 chunks :=
  chunksAccepted_append B000.accepted (chunksAccepted_append B001.accepted (chunksAccepted_append B002.accepted (chunksAccepted_append B003.accepted (chunksAccepted_append B004.accepted (chunksAccepted_append B005.accepted (B006.accepted))))))

theorem mass : chunksMass chunks = 2 ^ 360 - 73297 := by
  decide +kernel

theorem sum2 : chunksAccumulator chunks 2 = 1208270260258534013764407225179 := by
  decide +kernel

theorem sum3 : chunksAccumulator chunks 3 = 9727121270429289682937155996613607424 := by
  decide +kernel

theorem sum4 : chunksAccumulator chunks 4 = 170767602063266717498086360775929815367680 := by
  decide +kernel


end Sarkozy.F3Kernel.CertificateData.LL22
