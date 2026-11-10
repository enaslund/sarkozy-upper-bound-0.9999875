module

public import Sarkozy.NormBoundsPaper3.TripleLaws
public import Sarkozy.NormBoundsPaper3.ELaw
public import Sarkozy.NormBoundsPaper3.PairForms
public import Sarkozy.NormBoundsPaper3.MatchPrime
public import Sarkozy.NormBoundsPaper3.MatchBlock
public import Sarkozy.NormBoundsPaper3.MatchSkew
public import Sarkozy.NormBoundsPaper3.OldLaw
public import Sarkozy.NormBoundsPaper3.MatchSym
public import Sarkozy.NormBoundsPaper3.Constructor
public import Sarkozy.NormBoundsPaper3.Final
public import Sarkozy.NormBoundsPaper3.EsPaper
public import Sarkozy.NormBoundsPaper3.Sanity
public import Sarkozy.NormBoundsPaper3.Main

@[expose] public section

/-!
# NB3: the matching norm families of the middle blocks (`lem:record:exact-marginal-e`(ii))

The two matching families `Es`, `Ea` of NB2's `NormBoundsRest2`, by the paper's proof on the
triples of labels: the laws `ν_E`, `K^E_0`, `K₁` at one prime (`TripleLaws`, `ELaw`, `OldLaw`),
the pair kernel of `K₁` and its character forms (`PairForms`), the prime skew bound and centred
norms (`MatchPrime`, `OldLaw`), the cut identification and the sectors (`MatchBlock`, NB2's
`change_le`). The block theorems are `match_skew_paper` (`MatchSkew`, `Ea`, proved) and
`match_sym_paper` (`MatchSym`, `Es` from the one-prime input `EOrthPrime`,
`lem:record:e-orthogonal`(c)); the constructors of `NormBoundsRest2` and of the field `hNr2` are
`Constructor` (`Fs`, `Fa`, `Es` open) and `Final` (`Fs`, `Fa` and `EsPrimeInput` open);
`EsPaper` derives `EsPrimeInput paperKappa` from `lem:record:e-orthogonal`(c) at the paper's
constant `s^E_p` (`EOrthPaperInput`); the main statement `main_goal_nb3` is `Main` (open:
`Fs`, `Fa`, `EOrthPaperInput`); the checks are `Sanity`.
-/
