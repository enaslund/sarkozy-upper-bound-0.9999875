module

public import Sarkozy.BlockRows.Product
public import Sarkozy.BlockRows.Eval
public import Sarkozy.BlockRows.Middle
public import Sarkozy.BlockRows.MiddleLaw
public import Sarkozy.BlockRows.MiddleCert
public import Sarkozy.BlockRows.Joint
public import Sarkozy.BlockRows.UpperProduct
public import Sarkozy.BlockRows.UpperJoint
public import Sarkozy.BlockRows.Upper
public import Sarkozy.BlockRows.Main

/-!
# Block rows (RW): the reference rows from per-prime certificates

Umbrella of `Sarkozy/BlockRows/`. The final statement is
`Sarkozy.BlockRows.main_goal_rebased_rw` (`Main.lean`).

* `Product.lean`: conditional laws of product laws, Peyre over a finite index type, and
  `lem:row-comparison`(a),(c) on a product (`rows_of_product`);
* `Eval.lean`: the density ratios `R₁`, `R₂` and the middle block evaluation (`block_eval`);
* `Middle.lean`: the per-prime middle rows (`RowPrimeCert`) and the block rows from them
  (`blockRows_of_primeCerts`, `layerRows`);
* `MiddleLaw.lean`: the middle laws of `F` and `E` agree at one prime (`primeMid_two`,
  `primeMid_one`; affine and layer-swap invariance, `χ(-1) = -1`);
* `MiddleCert.lean`: the piece certificate `MiddleRowCert` and BA's `MiddleBlockRows` from it
  (`middleBlockRows_of_cert`);
* `Joint.lean`: product kernels (`kernelOf_prod`) and the transport of joint data;
* `UpperProduct.lean`: the upper row laws of a block as products of the single-prime row laws;
* `UpperJoint.lean`: the block joint data from per-prime joint rows (`JointPrimeCert`,
  `jointData_of_primeCerts`, `cor:joint-completion-blocks`);
* `Upper.lean`: the gates of (F5)(a), `UpperRowCert`, and BA's `UpperBandRowsV2` from them
  (`upperBandRowsV2_of_cert`);
* `Main.lean`: `CompanionObligationsRW`, `toBAEC`, `ofBAEC`, `main_goal_rebased_rw`.
-/
