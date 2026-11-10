module

public import Sarkozy.SignedDecompCrude.Kernel
public import Sarkozy.SignedDecompCrude.Reduce
public import Sarkozy.SignedDecompCrude.Removed
public import Sarkozy.SignedDecompCrude.Nonstar
public import Sarkozy.SignedDecompCrude.Main
public import Sarkozy.SignedDecompCrude.Paper
public import Sarkozy.SignedDecompCrude.Sanity
public import Sarkozy.SignedDecompCrude.Record
public import Sarkozy.SignedDecompCrude.RecordPaper
public import Sarkozy.SignedDecompCrude.Uniform
public import Sarkozy.SignedDecompCrude.Gate
public import Sarkozy.SignedDecompCrude.Fold

/-!
# ND: `prop:signed-bounds`(c) for the signed record at a crude constant (umbrella)

* `Kernel`: the natural operator of the signed star (`lForm_eq_kernel`, `star_eq_kernel`) and the
  split `∑_c α_c V_c = 1 + K_⋆ + K_ns - K_rq` (`signedV_split`).
* `Reduce`: `NewDecomp` from (K), (NS), (RQ) (`newDecomp_of_inputs`, constant `esgND`).
* `Removed`: (RQ) by the Schur test (`removedBound_crude`, `8(2 - t)/Z`).
* `Nonstar`: (NS) as a tensor product of two rectangular stars (`nonstarBound_tensor`,
  `2|𝐚||𝐛|/Z`).
* `Main`: PG's `SignedDecompInputsC` at `c_col = 73`, `c_+ = 38`, any `e_sg′`, given the gates
  (`CrudeSD.toSD`, `FrontKC`).
* `Paper`: at the paper's records, `RecordInputs.toSD` ((K) and the gates the only inputs).
* `Sanity`: (K) is satisfiable; the chain composes (`newDecomp_toy`).
* `Record`: (K) at one prime from the `z`-estimates and the repair constants (`recordForm_of`).
* `RecordPaper`: (K) at the paper's records (`recordForm_block`, constant `κRec`); every
  `ComparisonPartsTC` carries E1's estimates (`estInputs`); `signedDecompInputs_of_gates`.
* `Uniform`: `e_sg′(p) = esgCrude κRec nT p ≤ 21` for `p ≥ 2²⁴` (`esgCrude_le`); `pieceGate_mono`.
* `Gate`: the gates at `e_sg = 21`, `c_col = 73`, `c_+ = 38` at the rebased sides
  (`gate21_check`, kernel); **`signedDecompInputs_proved`**: PG's `SD` for every `C`.
* `Fold`: NB3's `hNr4` from ND's `NewDecomp` (`hNr4_proved`); `FrontN3ND` (3 fields) `→ FrontN3`.
-/
