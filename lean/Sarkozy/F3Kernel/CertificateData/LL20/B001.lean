module

public import Sarkozy.F3Kernel.ChainAppend
public import Sarkozy.F3Kernel.CertificateData.LL20.C0032
public import Sarkozy.F3Kernel.CertificateData.LL20.C0033
public import Sarkozy.F3Kernel.CertificateData.LL20.C0034
public import Sarkozy.F3Kernel.CertificateData.LL20.C0035
public import Sarkozy.F3Kernel.CertificateData.LL20.C0036
public import Sarkozy.F3Kernel.CertificateData.LL20.C0037
public import Sarkozy.F3Kernel.CertificateData.LL20.C0038
public import Sarkozy.F3Kernel.CertificateData.LL20.C0039
public import Sarkozy.F3Kernel.CertificateData.LL20.C0040
public import Sarkozy.F3Kernel.CertificateData.LL20.C0041
public import Sarkozy.F3Kernel.CertificateData.LL20.C0042
public import Sarkozy.F3Kernel.CertificateData.LL20.C0043
public import Sarkozy.F3Kernel.CertificateData.LL20.C0044
public import Sarkozy.F3Kernel.CertificateData.LL20.C0045
public import Sarkozy.F3Kernel.CertificateData.LL20.C0046
public import Sarkozy.F3Kernel.CertificateData.LL20.C0047
public import Sarkozy.F3Kernel.CertificateData.LL20.C0048
public import Sarkozy.F3Kernel.CertificateData.LL20.C0049
public import Sarkozy.F3Kernel.CertificateData.LL20.C0050
public import Sarkozy.F3Kernel.CertificateData.LL20.C0051
public import Sarkozy.F3Kernel.CertificateData.LL20.C0052
public import Sarkozy.F3Kernel.CertificateData.LL20.C0053
public import Sarkozy.F3Kernel.CertificateData.LL20.C0054
public import Sarkozy.F3Kernel.CertificateData.LL20.C0055
public import Sarkozy.F3Kernel.CertificateData.LL20.C0056
public import Sarkozy.F3Kernel.CertificateData.LL20.C0057
public import Sarkozy.F3Kernel.CertificateData.LL20.C0058
public import Sarkozy.F3Kernel.CertificateData.LL20.C0059
public import Sarkozy.F3Kernel.CertificateData.LL20.C0060
public import Sarkozy.F3Kernel.CertificateData.LL20.C0061
public import Sarkozy.F3Kernel.CertificateData.LL20.C0062
public import Sarkozy.F3Kernel.CertificateData.LL20.C0063


@[expose] public section

set_option maxRecDepth 10000

namespace Sarkozy.F3Kernel.CertificateData.LL20.B001

open Sarkozy.F3Kernel

noncomputable def chunks : List CertificateChunk := [
  ⟨C0032.tokens, C0032.summary⟩,
  ⟨C0033.tokens, C0033.summary⟩,
  ⟨C0034.tokens, C0034.summary⟩,
  ⟨C0035.tokens, C0035.summary⟩,
  ⟨C0036.tokens, C0036.summary⟩,
  ⟨C0037.tokens, C0037.summary⟩,
  ⟨C0038.tokens, C0038.summary⟩,
  ⟨C0039.tokens, C0039.summary⟩,
  ⟨C0040.tokens, C0040.summary⟩,
  ⟨C0041.tokens, C0041.summary⟩,
  ⟨C0042.tokens, C0042.summary⟩,
  ⟨C0043.tokens, C0043.summary⟩,
  ⟨C0044.tokens, C0044.summary⟩,
  ⟨C0045.tokens, C0045.summary⟩,
  ⟨C0046.tokens, C0046.summary⟩,
  ⟨C0047.tokens, C0047.summary⟩,
  ⟨C0048.tokens, C0048.summary⟩,
  ⟨C0049.tokens, C0049.summary⟩,
  ⟨C0050.tokens, C0050.summary⟩,
  ⟨C0051.tokens, C0051.summary⟩,
  ⟨C0052.tokens, C0052.summary⟩,
  ⟨C0053.tokens, C0053.summary⟩,
  ⟨C0054.tokens, C0054.summary⟩,
  ⟨C0055.tokens, C0055.summary⟩,
  ⟨C0056.tokens, C0056.summary⟩,
  ⟨C0057.tokens, C0057.summary⟩,
  ⟨C0058.tokens, C0058.summary⟩,
  ⟨C0059.tokens, C0059.summary⟩,
  ⟨C0060.tokens, C0060.summary⟩,
  ⟨C0061.tokens, C0061.summary⟩,
  ⟨C0062.tokens, C0062.summary⟩,
  ⟨C0063.tokens, C0063.summary⟩]

theorem accepted : ChunksAccepted LL20 85008385 chunks :=
  ⟨C0032.accepted, C0033.accepted, C0034.accepted, C0035.accepted, C0036.accepted, C0037.accepted, C0038.accepted, C0039.accepted, C0040.accepted, C0041.accepted, C0042.accepted, C0043.accepted, C0044.accepted, C0045.accepted, C0046.accepted, C0047.accepted, C0048.accepted, C0049.accepted, C0050.accepted, C0051.accepted, C0052.accepted, C0053.accepted, C0054.accepted, C0055.accepted, C0056.accepted, C0057.accepted, C0058.accepted, C0059.accepted, C0060.accepted, C0061.accepted, C0062.accepted, C0063.accepted, True.intro⟩

end Sarkozy.F3Kernel.CertificateData.LL20.B001
