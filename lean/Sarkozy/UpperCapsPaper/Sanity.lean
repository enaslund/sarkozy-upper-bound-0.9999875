module

public import Sarkozy.UpperCapsPaper.TablesProof
public import Sarkozy.UpperCapsPaper.RouteB
public import Sarkozy.SpectralD.RootTailThree
public import Sarkozy.DLK.Basic

/-!
# Sanity checks of the cap tables and of the anchor form

* **Fidelity of the generated rows to the paper's printed tables** (kernel):
  - `rootRows_printed`: the six rows printed in `cert:upper-root-caps` (`P₃`, `2⁴⁸`, `2⁴⁹`, `2⁵⁰`,
    `2⁵¹`, `(127/64)2⁵¹`): the band, the budget `L_band`, `g`, the printed bound `B_top < …`
    and the cap `d_L`;
  - `completed_printed`: the 9 bands from `2⁵²` carry W7's `completedRootTable`
    (`cert:upper-completed-root`): the same `g` and the cap `⌈d⌉`;
  - `nonroot_printed`: the ten nonroot `g` printed after `subsec:upper-nonroot`, and the two
    caps `d = 23.249822` (FL21 at `P₃`) and `23.073161` (at `2⁴⁸`) printed there.
* **Non-vacuity of the anchor form**: `capPrime_LL20_lower_tail`: at every class-three prime
  `p ≥ 2⁵¹²`, the lower half of `CapPrime .LL20 113 B p` holds for the actual LL20 chamber cut
  operator (S1's `LL20_tail_three`, from H1, H5 and `thm:dl:K`). So `CapPrime` is B6's chamber
  operator, identified with S1's `LL20` (`chamber_cutOp_eq_LL20`), and its lower bound is
  attained in the paper's form where the inputs are formalized.
-/

@[expose] public section

open scoped InnerProductSpace

namespace Sarkozy.UpperCapsPaper

open Sarkozy Sarkozy.PartV Sarkozy.BlockAdapter

/-- **The six rows printed in `cert:upper-root-caps`** (kernel): band index, `X`, `L_band`, `g`,
`B_top` below the printed bound, and `d_L`. -/
theorem rootRows_printed :
    ((bandOf 0).1 = 167 * 2 ^ 40 ∧ (UpperRecords.CompletionData.record 0).budget = 559 ∧
      (capRow 0 .LL20).g = 1284688753069 / 10 ^ 8 ∧ (capRow 0 .LL20).B < 252265 * 10 ^ 3 ∧
      capD 0 .LL20 = 12847187931 / 10 ^ 6) ∧
    ((bandOf 45).1 = 2 ^ 48 ∧ (UpperRecords.CompletionData.record 45).budget = 566 ∧
      (capRow 45 .LL20).g = 656889967376 / 10 ^ 8 ∧ (capRow 45 .LL20).B < 859331 * 10 ^ 2 ∧
      capD 45 .LL20 = 6568933791 / 10 ^ 6) ∧
    ((bandOf 109).1 = 2 ^ 49 ∧ (UpperRecords.CompletionData.record 109).budget = 578 ∧
      (capRow 109 .LL20).g = 255655783215 / 10 ^ 8 ∧ (capRow 109 .LL20).B < 230412 * 10 ^ 2 ∧
      capD 109 .LL20 = 2556559613 / 10 ^ 6) ∧
    ((bandOf 173).1 = 2 ^ 50 ∧ (UpperRecords.CompletionData.record 173).budget = 555 ∧
      (capRow 173 .LL20).g = 116555594825 / 10 ^ 8 ∧ (capRow 173 .LL20).B < 920408 * 10 ∧
      capD 173 .LL20 = 1165556101 / 10 ^ 6) ∧
    ((bandOf 237).1 = 2 ^ 51 ∧ (UpperRecords.CompletionData.record 237).budget = 566 ∧
      (capRow 237 .LL20).g = 61294721642 / 10 ^ 8 ∧ (capRow 237 .LL20).B < 471877 * 10 ∧
      capD 237 .LL20 = 612947237 / 10 ^ 6) ∧
    ((bandOf 300).1 = 127 * 2 ^ 45 ∧ (UpperRecords.CompletionData.record 300).budget = 577 ∧
      (capRow 300 .LL20).g = 37009363192 / 10 ^ 8 ∧ (capRow 300 .LL20).B < 281352 * 10 ∧
      capD 300 .LL20 = 370093636 / 10 ^ 6) := by
  decide +kernel

/-- **The 9 bands from `2⁵²` carry the table of `cert:upper-completed-root`** (W7's
`UpperReference.Cert.completedRootTable`): `X_k = 2⁵², …, 2⁵⁸, 2⁶⁰, 2⁶⁴`, the recorded `g` of LL20
and the integer cap `⌈d⌉`. -/
theorem completed_printed : ∀ k : Fin 310, 301 ≤ k.val →
    (capRow k .LL20).g = ((UpperReference.Cert.completedRootTable.getD (k.val - 301)
      (0, 0, 0, 0)).1) ∧
    capD k .LL20 = (UpperReference.Cert.completedRootTable.getD (k.val - 301) (0, 0, 0, 0)).2.1 ∧
    (capRow k .LL20).anchor = (bandOf k).1 := by
  decide +kernel

/-- **The nonroot rows are the printed `g` of the ten class-three nonroot caps**
(`subsec:upper-nonroot`, the table at `p₀ = 2⁴⁷`, `2⁴⁸`), and the printed caps of FL21 at `P₃`
and `2⁴⁸`. -/
theorem nonroot_printed :
    (nonroot47 .FL21).g = 2324980857 / 10 ^ 8 ∧ (nonroot48 .FL21).g = 2307315227 / 10 ^ 8 ∧
    (nonroot47 .EL21).g = 2495017938 / 10 ^ 8 ∧ (nonroot48 .EL21).g = 246357449 / 10 ^ 7 ∧
    (nonroot47 .LL10).g = 1017351517 / 10 ^ 8 ∧ (nonroot48 .LL10).g = 1005779953 / 10 ^ 8 ∧
    (nonroot47 .FL11).g = 410415806 / 10 ^ 8 ∧ (nonroot48 .FL11).g = 410396046 / 10 ^ 8 ∧
    (nonroot47 .EL11).g = 458309033 / 10 ^ 8 ∧ (nonroot48 .EL11).g = 45829422 / 10 ^ 7 ∧
    capD 0 .FL21 = 23249822 / 10 ^ 6 ∧ capD 45 .FL21 = 23073161 / 10 ^ 6 := by
  decide +kernel

/-- **Non-vacuity of the anchor form**: at every class-three prime `p ≥ 2⁵¹²`, the actual LL20
chamber cut operator satisfies the lower half of `CapPrime .LL20 113 B p`, `-113 p^{-1/2} ⪯ A_p`
(S1's `LL20_tail_three`; H1, H5 and `thm:dl:K`). -/
theorem capPrime_LL20_lower_tail (hW : Target.Weil) (hMR : Target.MovingRoot)
    (hFour : Target.FourCycle) {p : ℕ} [Fact p.Prime] (hp : 2 ^ 512 ≤ p) (hp3 : p % 4 = 3)
    (hne : (Labellings.injLabellings (ZMod p)
      (PartVLaws.FieldGraphs.chamberData .L (ZMod 2)).G).Nonempty)
    (v : EuclideanSpace ℝ ((PartVLaws.FieldGraphs.chamberData .L (ZMod 2)).cut.Half → ZMod p)) :
    -(113 * (√(p : ℝ))⁻¹) * ‖v‖ ^ 2 ≤
      ⟪v, Spectral.cutOp (PartVLaws.FieldGraphs.chamberData .L (ZMod 2)) hne v⟫_ℝ :=
  SpectralD.Root.LL20_tail_three hW hMR (DLK.fourCycleBound hFour (by omega)) hp hp3 hne v

end Sarkozy.UpperCapsPaper
