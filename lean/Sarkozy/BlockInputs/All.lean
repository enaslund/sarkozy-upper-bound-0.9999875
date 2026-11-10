module

public import Sarkozy.BlockInputs.UpperLayer
public import Sarkozy.BlockInputs.FoldCaps
public import Sarkozy.BlockInputs.FoldDensity
public import Sarkozy.BlockInputs.Middle
public import Sarkozy.BlockInputs.PositiveRoot
public import Sarkozy.BlockInputs.Observed
public import Sarkozy.BlockInputs.Exchange
public import Sarkozy.BlockInputs.Main
public import Sarkozy.BlockInputs.MainEC
public import Sarkozy.BlockInputs.Sanity

/-!
# Block-level analytic inputs reduced to per-prime certificates (BA), umbrella

B6's `MainFinal.BlockAnalytic` (`hUR`, `hMB`, `hIB`): every layer cap and positive-root envelope
is proved from per-prime certificates with per-band (per-piece) constants; only the rows remain
at the block level.

* `UpperLayer` — the upper layer caps (V3) of the 12 regular non-`E × E` states from band
  certificates of the layer cuts (`upperStateLayerCap_of_band`, `upperBandRowsNonEE_of_certs`);
* `Observed` — the compression adapter (`obs_block_lower`) and the caps of the 4 observed states
  `LR`, `RL`, `LC`, `CL` (`prop:observed-caps`; `upperObservedCaps_of_certs`);
* `Exchange` — the coordinate exchange of the layer cuts (`upLayerCutCap_swap`, `obsCutCap_swap`);
  the certificates in the paper's orientations (`UpperLayerCertsP`, `UpperObservedCertsP`);
* `FoldCaps` — the middle fold caps F21 at `k_D` from `T_old` on the actual marginal
  (`lem:old-f-law`(e); `act_block_lower`, `foldLayerCaps_of_cert`);
* `FoldDensity` — the density bound `g₀ ≤ 1 + e₀` of `lem:old-f-law`(a), proved from E1's
  `g0_bound` (`foldDensity_e0`); `MiddleFoldCut`, `middleFoldCert_of_cut`;
* `PositiveRoot` — the reweighted-law adapter (`wKer_block_lower`) and the L20 envelope and L21
  cap of the positive root (`prop:root-chamber`, `prop:root-layer`; `middleIndividualRoot_of_cert`);
* `Middle` — B6's middle fields from rows and certificates; the rows of the individual datum are
  the uniform rows (`rowBounds_individual_iff`);
* `Main` — `BlockInputsBA`, `CompanionObligationsBA`, `toSR`, `ofSR`, **`main_goal_rebased_ba`**;
* `MainEC` — the same over EC's `CompanionObligationsEC`: `CompanionObligationsBAEC`, `toEC`,
  `ofEC`, **`main_goal_rebased_baec`**;
* `Sanity` — the band certificate holds at the recorded caps for the edgeless pair `E × E`.
-/
