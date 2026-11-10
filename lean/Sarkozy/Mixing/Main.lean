module

public import Sarkozy.Mixing.PairSupport
public import Sarkozy.Mixing.Fourier
public import Sarkozy.Mixing.BlockFourier
public import Sarkozy.Mixing.TensorSpectrum
public import Sarkozy.Mixing.Differences

/-!
# Conditional mixing and conductor decay (WP-S follow-up): entry point

Main results (`paper/sections/06_lifts_sectors.tex`):

* `def:mixing` — `Sarkozy.Mixing.condOp` (conditional operator of a joint law),
  `blockJoint`, `blockOp`, `IsMixing`, `IsGammaMixing`; basic properties
  `condMatrix_row_sum` (fixes constants), `tgt_condOp` (means), `condOp_contraction`.
* `lem:mixture` — `mixture_condOp`, `mixture_energy_le`, `mixture_mixing`,
  `mixture_contractsMeanZero`, `IsMixing.mixture`.
* `lem:sector`(a) — `prodOp_sector_intertwine`, `prodOp_sector_intertwine'`,
  `prodOp_maps_sector` (sectors are preserved), `prodOp_sector_norm` (`‖T|_{H_S}‖ ≤ ‖T_0‖ δ_S`);
  (b) — `difference_telescoping`, `difference_triangle`;
* `lem:sector`(e) — `exact_support_decay` (uniform sources) and
  `general_exact_support_decay` (arbitrary finite probability spaces, spectators);
  (c) — `markov_tensor_max`, `general_markov_tensor_max` (arbitrary marginals),
  `tensor_lower_markov` (the spectral half); (f) — `product_density_chiSquare`;
  (g) — `tensor_spectrum`, `tensor_spectrum_exp`; Parseval — `general_parseval`.
* `lem:record:prefix-conductor` — `prefix_conductor` (sector form of the support
  hypothesis), `slot_conductor_decay` (abstract weights), `prodIntegral_eq`.
* `lem:tr:pairsupport` — `pair_support` (slot-block form), `pair_support_decay`.
* `(γ,v)`-mixing as `(γ,{v})`-mixing — `isMixing_singleton_iff`,
  `srcWeight_blockJoint_singleton`.
* The Fourier hypothesis of `lem:record:prefix-conductor` — `fourier_inversion`,
  `sectorProj_char`, `sectorProj_eq_zero_of_fourier`, `support_of_fourier`, and
  `prefix_conductor_fourier` (the lemma with the Fourier hypothesis, one cyclic group per
  coordinate, conductor `∏_j ord(a_j)`).
* `lem:record:prefix-conductor` as stated (block label groups, arbitrary prefix law, conductor
  `ord(ξ)`) — `prefix_conductor_blocks`, with the bridge `support_of_blockCoeff`,
  `addOrderOf_le_of_blockSupport`, `block_fourier_inversion`, `sectorProj_blockChar`.
-/
