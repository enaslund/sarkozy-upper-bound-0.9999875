module

public import Sarkozy.NormBoundsPaper2.Sectors
public import Sarkozy.NormBoundsPaper2.PairAlgebra
public import Sarkozy.NormBoundsPaper2.PrimeLaws
public import Sarkozy.NormBoundsPaper2.PrimeBounds
public import Sarkozy.NormBoundsPaper2.Merge2Sym
public import Sarkozy.NormBoundsPaper2.MirrorAlgebra
public import Sarkozy.NormBoundsPaper2.MirrorPrime
public import Sarkozy.NormBoundsPaper2.MirrorBlock
public import Sarkozy.NormBoundsPaper2.Constructor
public import Sarkozy.NormBoundsPaper2.Sanity
public import Sarkozy.NormBoundsPaper2.Main

@[expose] public section

/-!
# NB2: the merge norm families of the middle blocks (`lem:merge-repair`)

The three merge families of B8's `NormBounds` left open by HN (`Ms₂`, `Ms`, `Ma`) at the paper's
constants, by the paper's proof: the spectral theory of the source `D_p` on ordered pairs
(`PairAlgebra`, `PrimeBounds`), the first-coordinate and mirror-edge replacements at one prime
(`PrimeLaws`, `PrimeBounds`, `MirrorAlgebra`, `MirrorPrime`), and the exact-support sectors of
`⊗_p L²(m_p)` (`Sectors`, reusing SGA's `SignedGram.Sector`, `SectorNorm`). The block theorems are
`merge2_sym_paper` (`Merge2Sym`), `mirror_sym_paper`, `mirror_skew_paper` (`MirrorBlock`); the
constructor of HN's `NormBoundsRest` from the four remaining families is `Constructor`; the main
statement `main_goal_nb2` is `Main`; the checks are `Sanity`.
-/
