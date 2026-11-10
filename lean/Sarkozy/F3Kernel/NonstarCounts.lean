module

public import Sarkozy.F3Kernel.RunMass

/-!
# The exact nonstar masses of the two certificate graphs

These checks evaluate only the edge count and 72 row/column degrees, not a powerset.
-/

@[expose] public section

namespace Sarkozy.F3Kernel

set_option maxRecDepth 100000 in
theorem LL20_nonstarMass : nonstarMass (decT LL20.ET) = 2 ^ 384 - 147001 := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem LL22_nonstarMass : nonstarMass (decT LL22.ET) = 2 ^ 360 - 73297 := by
  decide +kernel

theorem LL20_chunk_full_partition {last : ℕ} {toks : List ℕ} {summary : Summary}
    (h : chunk LL20 last toks = some summary) (hm : summary.mass = 2 ^ 384 - 147001) :
    Sarkozy.Extraction.IsExactPartition (decT LL20.ET) (leafFamily LL20 last toks)
      (Sarkozy.Extraction.nonstars (decT LL20.ET)) := by
  apply chunk_nonstar_partition_of_summary LL20_matrixWordM LL20_wellFormedT LL20_coherent h
  exact hm.trans LL20_nonstarMass.symm

theorem LL22_chunk_full_partition {last : ℕ} {toks : List ℕ} {summary : Summary}
    (h : chunk LL22 last toks = some summary) (hm : summary.mass = 2 ^ 360 - 73297) :
    Sarkozy.Extraction.IsExactPartition (decT LL22.ET) (leafFamily LL22 last toks)
      (Sarkozy.Extraction.nonstars (decT LL22.ET)) := by
  apply chunk_nonstar_partition_of_summary LL22_matrixWordM LL22_wellFormedT LL22_coherent h
  exact hm.trans LL22_nonstarMass.symm

end Sarkozy.F3Kernel
