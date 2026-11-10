module

public import Sarkozy.NormBoundsPaper4.MixSectors
public import Sarkozy.NormBoundsPaper4.FoldCut
public import Sarkozy.NormBoundsPaper4.FoldCol
public import Sarkozy.NormBoundsPaper4.FoldBlock
public import Sarkozy.NormBoundsPaper4.Constructor
public import Sarkozy.NormBoundsPaper4.Sanity
public import Sarkozy.NormBoundsPaper4.ECounts
public import Sarkozy.NormBoundsPaper4.EDecomp
public import Sarkozy.NormBoundsPaper4.EBounds
public import Sarkozy.NormBoundsPaper4.EOrth
public import Sarkozy.NormBoundsPaper4.ENum
public import Sarkozy.NormBoundsPaper4.EFinal
public import Sarkozy.NormBoundsPaper4.EOrthB
public import Sarkozy.NormBoundsPaper4.EEps
public import Sarkozy.NormBoundsPaper4.Main

@[expose] public section

/-!
# FD: the fold norm families of the middle blocks (`prop:signed-bounds`(a),(b),(e))

The two fold families `Fs`, `Fa` of NB3's `NormBoundsRest4`, by Step 4 of the paper's proof of
`prop:signed-bounds` (the sectors of a signed mixture of products, `MixSectors`), on the cut forms
of B8's fold records (`FoldCut`, with SGA's kernel forms and the reflection for `F₂`), from the
one-prime statements of `prop:signed-bounds`(c) and the component norms (`FoldBlock`: `fold_sym`,
`fold_skew`, `fold_paper`, `fold_check`; the collision part of the reference record is bounded
crudely in `FoldCol`). The constructor of NB3's field `hNr4` is `Constructor`
(`hNr4_of_inputs`).

`lem:record:e-orthogonal`(c) at one prime (NB3's `EOrthPaperInput`) is proved by the paper's
orthogonal-channel argument: the singleton features and their Gram (`ECounts`), the decomposition
of `Sym(K₁ − K^E_0)` (`EDecomp`), the star part and the two-edge kernels (`EBounds`), the
projection onto `V(H₀³)` and the assembly (`EOrth`), the constants against the paper's `s^E_p`
(`ENum`, `EFinal`), `𝖢𝖣` on `V(H₀³)` (`EOrthB`) and the coincidence remainder `ε_E` (`EEps`:
`eOrthPaperInput`). The main statement `main_goal_nb4` is `Main`; the checks are `Sanity`.
-/
