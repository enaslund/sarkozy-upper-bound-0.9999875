module

public import Sarkozy.OpsCore.Bridge
public import Sarkozy.OpsFeature.Frame

@[expose] public section

/-!
# Glue: OPS-F's feature frame at the actual half marginal of the fold record (OPS-L)

`paper/sections/23_envelopes.tex`, `lem:oct24:feature-block`(b); `Sarkozy.OpsFeature.Frame`
(read-only). OPS-F proves the frame bound `‖∑_v h_v‖² ≤ Γ_F ∑_v ‖h_v‖²` for the five fold
features in `L²(m_{0,𝔅})` on the object triples (`actual_feature_frame`). By
`mOf_fold_eq_push` the actual half marginal of the fold record `F_j` is `push m0B (triPlace j)`,
and `triPlace j` is injective, so the features extended by `0` (`extend0`) satisfy the same
bound in `L²(mOf)` on the half labellings (**`feature_frame_mOf`**). With `opLE_push` this is
what lets OPS-F's results apply at OPS-L's objects.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.OpsCore

open Sarkozy.EnvelopeSteps Sarkozy.SignedComponents Sarkozy.PartV Sarkozy.PartVRecords
  Sarkozy.MiddleComparison Sarkozy.OpsFeature Sarkozy.Envelopes

variable {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]

/-- OPS-F's `ipm` is `ip` at `m0B`. -/
theorem ipm_eq_ip (h k : Tri (fun i => ZMod (pr i)) → ℝ) :
    ipm h k = ip (m0B (F := fun i => ZMod (pr i))) h k := by
  unfold ipm ip
  exact sum_congr rfl fun x _ => by ring

/-- **OPS-F's frame bound in `L²(mOf)` of the fold record `F_j`**: for any features on the triples
with OPS-F's frame bound in `L²(m_{0,𝔅})` (e.g. `actual_feature_frame`), their extensions by `0`
along `triPlace j` satisfy it in `L²` of the actual half marginal of `F_j` on the half
labellings. -/
theorem feature_frame_mOf (hne : MiddleNonempty pr)
    (root : FiniteLaw (ZMod 6 × Fin 2 → BlockLabel pr)) (W : MiddleWeights) (I : MiddleInputs)
    {r : ℝ} (hr : 0 ≤ r) (b : ℝ) (h : ClassThreeBlock pr)
    (hR : ∀ i, ringChar (ZMod (pr i)) ≠ 2) (h3 : ∀ i, Fintype.card (ZMod (pr i)) % 4 = 3)
    (h19 : ∀ i, 19 ≤ Fintype.card (ZMod (pr i))) (j : Fin 2)
    (hf : Fin 5 → Tri (fun i => ZMod (pr i)) → ℝ) {Γ : ℝ}
    (hfr : ipm (fun x => ∑ v, hf v x) (fun x => ∑ v, hf v x) ≤ Γ * ∑ v, ipm (hf v) (hf v)) :
    ip (mOf (middleFrame pr hne root W I hr b h) (.inl j))
        (fun u => ∑ v, extend0 (triPlace pr j) (hf v) u)
        (fun u => ∑ v, extend0 (triPlace pr j) (hf v) u) ≤
      Γ * ∑ v, ip (mOf (middleFrame pr hne root W I hr b h) (.inl j))
        (extend0 (triPlace pr j) (hf v)) (extend0 (triPlace pr j) (hf v)) := by
  rw [mOf_fold_eq_push pr hne root W I hr b h hR h3 h19 j]
  refine frame_push _ (triPlace_injective pr j) hf ?_
  simp only [← ipm_eq_ip]
  exact hfr

/-- **The actual feature frame (`lem:oct24:feature-block`(b)) in `L²(mOf)`**: OPS-F's
`actual_feature_frame` (given its edge `03`, `Edge03Block`) transported to the half labellings of
the fold record `F_j`. -/
theorem actual_feature_frame_mOf (hne : MiddleNonempty pr)
    (root : FiniteLaw (ZMod 6 × Fin 2 → BlockLabel pr)) (W : MiddleWeights) (I : MiddleInputs)
    {r : ℝ} (hr : 0 ≤ r) (b : ℝ) (h : ClassThreeBlock pr)
    (h19 : ∀ i, 19 ≤ Fintype.card (ZMod (pr i)))
    (j : Fin 2) {bb : ℝ} (hB : MiddleBlock (fun i => ZMod (pr i)) bb)
    (h03 : Edge03Block (fun i => ZMod (pr i)) (rho03 (1 / bb) (1 / Real.sqrt bb)))
    (hf : Fin 5 → Tri (fun i => ZMod (pr i)) → ℝ) (hfeat : IsFoldFeat hf) :
    ip (mOf (middleFrame pr hne root W I hr b h) (.inl j))
        (fun u => ∑ v, extend0 (triPlace pr j) (hf v) u)
        (fun u => ∑ v, extend0 (triPlace pr j) (hf v) u) ≤
      (gammaF : ℝ) * ∑ v, ip (mOf (middleFrame pr hne root W I hr b h) (.inl j))
        (extend0 (triPlace pr j) (hf v)) (extend0 (triPlace pr j) (hf v)) :=
  feature_frame_mOf pr hne root W I hr b h hB.hF hB.h3 h19 j hf
    (actual_feature_frame hB h03 hf hfeat)

end Sarkozy.OpsCore
