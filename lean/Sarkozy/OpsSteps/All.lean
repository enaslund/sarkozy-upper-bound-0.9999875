module

public import Sarkozy.OpsSteps.E1Diag
public import Sarkozy.OpsSteps.E1Proved
public import Sarkozy.OpsSteps.Coupling
public import Sarkozy.OpsSteps.Step3
public import Sarkozy.OpsSteps.Coupled
public import Sarkozy.OpsSteps.QSum
public import Sarkozy.OpsSteps.QPieces
public import Sarkozy.OpsSteps.QSmall
public import Sarkozy.OpsSteps.QMain
public import Sarkozy.OpsSteps.SymSplit
public import Sarkozy.OpsSteps.Sym
public import Sarkozy.OpsSteps.SymCat
public import Sarkozy.OpsSteps.SymSwap
public import Sarkozy.OpsSteps.SymFine
public import Sarkozy.OpsSteps.SymFineSum
public import Sarkozy.OpsSteps.Step3Fine
public import Sarkozy.OpsSteps.SymBridge
public import Sarkozy.OpsSteps.SymBlock
public import Sarkozy.OpsSteps.SymSharp
public import Sarkozy.OpsSteps.Step4
public import Sarkozy.OpsSteps.Uniform
public import Sarkozy.OpsSteps.Background
public import Sarkozy.OpsSteps.FineE1
public import Sarkozy.OpsSteps.FineSum
public import Sarkozy.OpsSteps.FineGroup
public import Sarkozy.OpsSteps.Step4Fine
public import Sarkozy.OpsSteps.Prices
public import Sarkozy.OpsSteps.Step4Inv
public import Sarkozy.OpsSteps.Caps
public import Sarkozy.OpsSteps.Bridges
public import Sarkozy.OpsSteps.Plug
public import Sarkozy.OpsSteps.Sanity

@[expose] public section

/-!
# OPS-S: Steps 3, 4 of `thm:envelopes`(i) and (E1) for `Diag_ω` (umbrella)

* `E1Diag`: (E1) for the diagonals `Diag_ω` (B11's `hE1`, B10's `hDN`) from the envelope bound
  of the selections, given `D^ε_{𝔟,t} = Diag_ι(m_{t,𝔟})` (`def:cp4`(b));
* `E1Proved`: the envelope bound proved at the paper's data (EC's machinery);
* `Coupling`: the coupling expansion `D_ω = ∑_C c(C) C` of a lifted envelope (kernels), the unit
  tables of `lem:oct24:mask-schur`(a);
* `Step3`: Step 3 with the orbit coupon (`lem:orbit-coupon`(i), (ii)) at the paper's energies;
* `Coupled`: the per-coupling bound of Step 3 from the coupled sharp terms (`lem:sharp-first`);
* `QSum`, `QPieces`, `QSmall`, `QMain`: EC's coupled-piece chain with an arbitrary probability law
  on the support; the summed per-coupling remainders of Step 3 (`rCan_class_sum`);
* `SymSplit`, `Sym`: `hsym` (`lem:orbit-coupon`(i)) reduced to the improved bound of the category
  `e_s` (`hsym_of_category`), with the reflection of the difference (`sym_swap`);
* `SymCat`: the category `e_s` expanded over the `G` atoms and evaluated (`hcat_of_terms`,
  `hsym_of_terms`): `hsym` from per-term bounds (symmetric price at `Z = ∅`), canonical `rCat`;
* `SymSwap`: the `G`-free term is the energy of the orbit average with the difference replaced by
  its symmetric part (`catT_zero_eq`, `catT_zero_sym`);
* `SymFine`, `SymFineSum`: the terms with `G` from G1's coupled pieces (`abs_catT_le`), their
  remainders summed (`rQ_class_sum`), and `hsym` with one per-term input left (`hsym_fine`);
* `Step3Fine`: `herr` and `hsym` of `paperDegreeOpsS` at tensor couplings with one remainder
  `r3` (`herr_hsym_of_tensor`), and its class sum (`r3_class_sum`);
* `SymBridge`: the remaining input `hsymT` from a bound on the energy with the symmetric part of
  the difference (`hsymT_of_sym`);
* `SymBlock`, `SymSharp`: `lem:record:one-stage-folded-e`(d)/(e), the symmetric part: the block
  bound `‖Sym Δ_c‖ ≤ s_crude(b)` (`block_sym_norm_le`) and the symmetric sharp bound of the
  72-slot records (`blockSymSharp_of_block`, `middle_symSharp`); `R_h` is the cut reflection
  (`avg_slotPush_eq_symPart`, `hsymT_of_symPart`);
* `Step4`: Step 4 and the background expansion of (iii), reduced to the caps and one inequality
  between diagonal energies;
* `Uniform`: Step 4 in the uniform-cost form `thm:envelopes`(ii), proved from EC's (E1) against
  `Ñ₀`, the caps and the averaging inputs;
* `Background`: the background polynomial of Step 4 (i) and `rem:completion-subtraction`
  (`background_le`); `heval` in form (i) from the finer (E1) (`heval_of_finer`);
* `FineE1`, `FineSum`, `FineGroup`, `Step4Fine`: the finer (E1) of Step 4 (i) (the tags of
  `E_add + H` and `G` apart), per term, summed (`fX_summable`), grouped by `Z` (`hfine_of_fine`),
  and Step 4 in form (i) (`step4_fine`, `step4_fine_rem`);
* `Prices`: the upper prices replaced by `U₀_total` and one scalar condition (`step4_total`);
* `Step4Inv`: the additional average at `Z = ∅` from the invariance of `Ñ^inv` (`hextra_of_inv`,
  `step4_inv`);
* `Caps`: the cap `hcapH` of `step4_inv` from the per-selection caps (`hcapH_of_caps`);
* `Bridges`: V2's `lem:oct24:invariant-background`(iv) as the background inputs of Step 4, and
  `R_{h*}[C] = [hC]` from a placement identity;
* `Plug`: B11's `paperDegreeOps` with `hE1` and `step3` discharged by the theorems above;
* `Sanity`: non-vacuity of the orbit coupon, the unit tables.
-/
