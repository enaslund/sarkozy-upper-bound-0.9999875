module

public import Sarkozy.F3Kernel.ChainAppend
public import Sarkozy.F3Kernel.CertificateData.LL20.C0256
public import Sarkozy.F3Kernel.CertificateData.LL20.C0257
public import Sarkozy.F3Kernel.CertificateData.LL20.C0258
public import Sarkozy.F3Kernel.CertificateData.LL20.C0259
public import Sarkozy.F3Kernel.CertificateData.LL20.C0260
public import Sarkozy.F3Kernel.CertificateData.LL20.C0261
public import Sarkozy.F3Kernel.CertificateData.LL20.C0262
public import Sarkozy.F3Kernel.CertificateData.LL20.C0263
public import Sarkozy.F3Kernel.CertificateData.LL20.C0264
public import Sarkozy.F3Kernel.CertificateData.LL20.C0265
public import Sarkozy.F3Kernel.CertificateData.LL20.C0266
public import Sarkozy.F3Kernel.CertificateData.LL20.C0267
public import Sarkozy.F3Kernel.CertificateData.LL20.C0268
public import Sarkozy.F3Kernel.CertificateData.LL20.C0269
public import Sarkozy.F3Kernel.CertificateData.LL20.C0270
public import Sarkozy.F3Kernel.CertificateData.LL20.C0271
public import Sarkozy.F3Kernel.CertificateData.LL20.C0272
public import Sarkozy.F3Kernel.CertificateData.LL20.C0273
public import Sarkozy.F3Kernel.CertificateData.LL20.C0274
public import Sarkozy.F3Kernel.CertificateData.LL20.C0275
public import Sarkozy.F3Kernel.CertificateData.LL20.C0276
public import Sarkozy.F3Kernel.CertificateData.LL20.C0277
public import Sarkozy.F3Kernel.CertificateData.LL20.C0278
public import Sarkozy.F3Kernel.CertificateData.LL20.C0279
public import Sarkozy.F3Kernel.CertificateData.LL20.C0280
public import Sarkozy.F3Kernel.CertificateData.LL20.C0281
public import Sarkozy.F3Kernel.CertificateData.LL20.C0282
public import Sarkozy.F3Kernel.CertificateData.LL20.C0283
public import Sarkozy.F3Kernel.CertificateData.LL20.C0284
public import Sarkozy.F3Kernel.CertificateData.LL20.C0285
public import Sarkozy.F3Kernel.CertificateData.LL20.C0286
public import Sarkozy.F3Kernel.CertificateData.LL20.C0287


@[expose] public section

set_option maxRecDepth 10000

namespace Sarkozy.F3Kernel.CertificateData.LL20.B008

open Sarkozy.F3Kernel

noncomputable def chunks : List CertificateChunk := [
  ⟨C0256.tokens, C0256.summary⟩,
  ⟨C0257.tokens, C0257.summary⟩,
  ⟨C0258.tokens, C0258.summary⟩,
  ⟨C0259.tokens, C0259.summary⟩,
  ⟨C0260.tokens, C0260.summary⟩,
  ⟨C0261.tokens, C0261.summary⟩,
  ⟨C0262.tokens, C0262.summary⟩,
  ⟨C0263.tokens, C0263.summary⟩,
  ⟨C0264.tokens, C0264.summary⟩,
  ⟨C0265.tokens, C0265.summary⟩,
  ⟨C0266.tokens, C0266.summary⟩,
  ⟨C0267.tokens, C0267.summary⟩,
  ⟨C0268.tokens, C0268.summary⟩,
  ⟨C0269.tokens, C0269.summary⟩,
  ⟨C0270.tokens, C0270.summary⟩,
  ⟨C0271.tokens, C0271.summary⟩,
  ⟨C0272.tokens, C0272.summary⟩,
  ⟨C0273.tokens, C0273.summary⟩,
  ⟨C0274.tokens, C0274.summary⟩,
  ⟨C0275.tokens, C0275.summary⟩,
  ⟨C0276.tokens, C0276.summary⟩,
  ⟨C0277.tokens, C0277.summary⟩,
  ⟨C0278.tokens, C0278.summary⟩,
  ⟨C0279.tokens, C0279.summary⟩,
  ⟨C0280.tokens, C0280.summary⟩,
  ⟨C0281.tokens, C0281.summary⟩,
  ⟨C0282.tokens, C0282.summary⟩,
  ⟨C0283.tokens, C0283.summary⟩,
  ⟨C0284.tokens, C0284.summary⟩,
  ⟨C0285.tokens, C0285.summary⟩,
  ⟨C0286.tokens, C0286.summary⟩,
  ⟨C0287.tokens, C0287.summary⟩]

theorem accepted : ChunksAccepted LL20 3273392129 chunks :=
  ⟨C0256.accepted, C0257.accepted, C0258.accepted, C0259.accepted, C0260.accepted, C0261.accepted, C0262.accepted, C0263.accepted, C0264.accepted, C0265.accepted, C0266.accepted, C0267.accepted, C0268.accepted, C0269.accepted, C0270.accepted, C0271.accepted, C0272.accepted, C0273.accepted, C0274.accepted, C0275.accepted, C0276.accepted, C0277.accepted, C0278.accepted, C0279.accepted, C0280.accepted, C0281.accepted, C0282.accepted, C0283.accepted, C0284.accepted, C0285.accepted, C0286.accepted, C0287.accepted, True.intro⟩

end Sarkozy.F3Kernel.CertificateData.LL20.B008
