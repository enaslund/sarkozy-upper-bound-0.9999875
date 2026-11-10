module

public import Sarkozy.IndexCert.MomentCompute
public import Sarkozy.IndexCert.MomentBounds
public import Sarkozy.IndexCert.MomentTerms
public import Sarkozy.IndexCert.Moment
public import Sarkozy.IndexCert.MomentSanity
public import Sarkozy.IndexCert.EnvelopeBasics
public import Sarkozy.IndexCert.EnvelopeOdd
public import Sarkozy.IndexCert.EnvelopeTwo
public import Sarkozy.IndexCert.EnvelopePaper
public import Sarkozy.IndexCert.BlockCert
public import Sarkozy.IndexCert.PaperCert

@[expose] public section

/-!
# The index-law certificates of the formal main theorem at `a₀` (CERT1)

`paper/sections/27_tail_index.tex`.
* `cert:index-moment`: `Moment.lean`, **`paperRI_le_anchorLedger`** (`Target.ThetaSmall` gives
  `PaperData.paperRI ≤ LedgerAnchor.anchorLedger.R_I`, the field `hR` of
  `MainAnchor.PaperObligations`), with `MomentCompute`, `MomentBounds`, `MomentTerms`; sanity
  checks in `MomentSanity`.
* `lem:imp:padic-envelope`: `EnvelopePaper.lean`, **`paperIndexBound`** (D1's
  `PaperData.PaperIndexBound`, the field `hIdx` of `MainAnchor.PaperData`), with no hypothesis,
  from `EnvelopeBasics`, `EnvelopeOdd`, `EnvelopeTwo`.
* The assemblies with both certified: `BlockCert.lean`, **`main_anchor_paper_block_cert`** (K0's
  `main_anchor_paper_block` on the block atoms, from `Target.ThetaSmall` and
  `BlockCertObligations`, without `hIdx` and `hR`), and `PaperCert.lean`,
  **`main_anchor_paper_cert`** (the same for D1's merged-atom `main_anchor_paper`).
-/
