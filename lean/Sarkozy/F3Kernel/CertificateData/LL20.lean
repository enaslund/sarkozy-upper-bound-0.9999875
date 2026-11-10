module

public import Sarkozy.F3Kernel.CertificateData.LL20.B000
public import Sarkozy.F3Kernel.CertificateData.LL20.B001
public import Sarkozy.F3Kernel.CertificateData.LL20.B002
public import Sarkozy.F3Kernel.CertificateData.LL20.B003
public import Sarkozy.F3Kernel.CertificateData.LL20.B004
public import Sarkozy.F3Kernel.CertificateData.LL20.B005
public import Sarkozy.F3Kernel.CertificateData.LL20.B006
public import Sarkozy.F3Kernel.CertificateData.LL20.B007
public import Sarkozy.F3Kernel.CertificateData.LL20.B008
public import Sarkozy.F3Kernel.CertificateData.LL20.B009
public import Sarkozy.F3Kernel.CertificateData.LL20.B010
public import Sarkozy.F3Kernel.CertificateData.LL20.B011
public import Sarkozy.F3Kernel.CertificateData.LL20.B012
public import Sarkozy.F3Kernel.CertificateData.LL20.B013
public import Sarkozy.F3Kernel.CertificateData.LL20.B014
public import Sarkozy.F3Kernel.CertificateData.LL20.B015
public import Sarkozy.F3Kernel.CertificateData.LL20.B016
public import Sarkozy.F3Kernel.CertificateData.LL20.B017
public import Sarkozy.F3Kernel.CertificateData.LL20.B018
public import Sarkozy.F3Kernel.CertificateData.LL20.B019
public import Sarkozy.F3Kernel.CertificateData.LL20.B020
public import Sarkozy.F3Kernel.CertificateData.LL20.B021
public import Sarkozy.F3Kernel.CertificateData.LL20.B022
public import Sarkozy.F3Kernel.CertificateData.LL20.B023


@[expose] public section

set_option maxRecDepth 10000

namespace Sarkozy.F3Kernel.CertificateData.LL20

open Sarkozy.F3Kernel

noncomputable def chunks : List CertificateChunk :=
  B000.chunks ++
  (B001.chunks ++
  (B002.chunks ++
  (B003.chunks ++
  (B004.chunks ++
  (B005.chunks ++
  (B006.chunks ++
  (B007.chunks ++
  (B008.chunks ++
  (B009.chunks ++
  (B010.chunks ++
  (B011.chunks ++
  (B012.chunks ++
  (B013.chunks ++
  (B014.chunks ++
  (B015.chunks ++
  (B016.chunks ++
  (B017.chunks ++
  (B018.chunks ++
  (B019.chunks ++
  (B020.chunks ++
  (B021.chunks ++
  (B022.chunks ++
  (B023.chunks)))))))))))))))))))))))

theorem accepted : ChunksAccepted LL20 0 chunks :=
  chunksAccepted_append B000.accepted (chunksAccepted_append B001.accepted (chunksAccepted_append B002.accepted (chunksAccepted_append B003.accepted (chunksAccepted_append B004.accepted (chunksAccepted_append B005.accepted (chunksAccepted_append B006.accepted (chunksAccepted_append B007.accepted (chunksAccepted_append B008.accepted (chunksAccepted_append B009.accepted (chunksAccepted_append B010.accepted (chunksAccepted_append B011.accepted (chunksAccepted_append B012.accepted (chunksAccepted_append B013.accepted (chunksAccepted_append B014.accepted (chunksAccepted_append B015.accepted (chunksAccepted_append B016.accepted (chunksAccepted_append B017.accepted (chunksAccepted_append B018.accepted (chunksAccepted_append B019.accepted (chunksAccepted_append B020.accepted (chunksAccepted_append B021.accepted (chunksAccepted_append B022.accepted (B023.accepted)))))))))))))))))))))))

theorem mass : chunksMass chunks = 2 ^ 384 - 147001 := by
  decide +kernel

theorem sum2 : chunksAccumulator chunks 2 = 1501562124900058879249386227394 := by
  decide +kernel

theorem sum3 : chunksAccumulator chunks 3 = 8750965918808624230895849334674817024 := by
  decide +kernel

theorem sum4 : chunksAccumulator chunks 4 = 22953500344884780253843872668794413383680 := by
  decide +kernel


end Sarkozy.F3Kernel.CertificateData.LL20
