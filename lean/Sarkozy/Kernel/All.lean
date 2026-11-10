module

public import Sarkozy.Kernel.KernelEstimate
public import Sarkozy.Kernel.Admissible
public import Sarkozy.Kernel.IntervalCorollary
public import Sarkozy.Kernel.Rescale
public import Sarkozy.Kernel.RescaleStrict
public import Sarkozy.Kernel.Range
public import Sarkozy.Kernel.IndicatorCorollary

@[expose] public section

/-!
# The actual-square kernel estimate: all modules

Imports every module of `Sarkozy/Kernel/` (the paper's `prop:record:kernel20`,
`cor:kernel20`, Appendix C). Main results:

* `Sarkozy.Kernel.prop_kernel20` — `prop:record:kernel20`, parts (i), (ii), (iii), for every
  triple admissible in the sense of `def:kernel-conditions` (`KernelAdmissible`);
* `Sarkozy.Kernel.cor_kernel20_admissible`, `cor_kernel20_slacks` — `cor:kernel20`;
* `Sarkozy.Kernel.kernelAdmissible_diag_iff`, `kernelAdmissible_diag_exists_iff`,
  `kernelAdmissible_seventeen` — `rem:record:K20-range`(1) and the range paragraph of Section 7;
* `Sarkozy.Kernel.prop_kernel20_twentieth` — the same three parts written out at the triple
  `(1/20, 1/20, 17/100)` (`D ≤ C_D N^(1/20)`, `H ≍ N^(1/40)`, saving `N^(-1/120)`);
* `Sarkozy.Kernel.prop_kernel20_twentieth_intervals` — its last sentence (bounded functions on
  intervals);
* `Sarkozy.Kernel.prop_kernel20_squareDifferenceFree` — the estimate for the indicators of the
  parts of a square-difference-free `A ⊆ [1,N]` in two ordered intervals and two residue classes
  (the form used by `lem:record:density-can`);
* `Sarkozy.Kernel.nonunit_rescale_identity` — the rescaling identity of part (ii)
  (`lem:record:nonunit-rescale`(d)); `prop_kernel20_ii_rescaling` — the whole of
  `lem:record:nonunit-rescale` in the setting of (ii): identity, supports, classes, norms, and
  the strict class of the rescaled difference, so that (i) applies to the rescaled functions;
* `Sarkozy.Kernel.kernel_pairing_twentieth` — the earlier special case (i) with `d` squarefree,
  through the upstream model coefficient;
* `Sarkozy.Kernel.general_kernel_rate`, `actual_kernel_rate_twentieth`, `actual_kernel_uniform`
  — the uniform kernel approximation (`lem:record:K20-approx`).
-/
