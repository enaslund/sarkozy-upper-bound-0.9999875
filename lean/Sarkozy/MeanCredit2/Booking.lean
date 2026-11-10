module

public import Sarkozy.MeanCredit2.Evaluation

@[expose] public section

/-!
# The booking at the paper's coefficients, the variance credit counted once

`paper/sections/24a_joint_mean.tex`, `prop:joint-middle-mean` (the residual table:
`63(κ_b − variance) − mean`; "combine its comparison coefficient `c` and retained mean coefficient
`b` as `(63c − b)Z` first"); `paper/sections/23_envelopes.tex`, `cor:envelope-costs`.

**The labels.** Each label `k ∈ K` has a paper type `labK k ∈ PaperDiag` and a per-selection mean
coefficient `μK k ≥ 0`, the coefficient its family proves on each of its selections. Separate labels
per family, e.g. `K = PaperDiag × Fin 4`, keep families (i) and (iv) apart. The weights are the
exact ones, `wt = wtOf labK μK`.

**The comparison weight with the variance credit once.** On label `k` the aggregated weight is
`w_k = (κ_b − var)/wt_k`, with `κ_b − var = diagW (labK k)` the paper's class weight net of its
variance credit (`hwPaper`). Then:

* **`bookedCoef_paper`**: each selection of label `k` is booked with exactly
  `63(κ_b − var) − μK_k`, the paper's residual. The variance credit enters once, through `w`.
  The selection's residual `r_ω` and the comparison coefficient `c` of its letter degree must not
  subtract it again (`hcomp`), and `𝓔` subtracts `D_var` once (the harness).
* **`resid_paper_nonneg`**: `63(κ_b − var) − μK_k > 23.66 > 0` whenever `μK_k ≤ diagB(labK k)`
  (E4's 192 gates). **`wtOf_le_one`**: then `wt ≤ 1`, so `hw` holds.
* **`hRc_paper`**: the booking condition `hRc` of `alloc_of_sel`, with `R = 63c − mLift`, from the
  comparison identification `hcomp` (the letter degree's comparison coefficient is at least the
  selection's: `B` off the classes; `r_ω`, plus `κ_b − var` when labelled, on them) and the mean
  identification `hmean` (`mLift(deg ω) ≤ μK(label ω)`, `0` when unlabelled).
-/

open Finset

namespace Sarkozy.MeanCredit2

open Sarkozy.ClassData Sarkozy.MeanCredit Sarkozy.ClassInputsPaper
open Sarkozy.RecordExpansion Sarkozy.RecordExpansion.Choice

variable {K : Type}

theorem diagW_pos (d : PaperDiag) : (0 : ℝ) < diagW d := by
  have h1 : ((diagB d + 2366 / 100 : ℚ) : ℝ) < ((63 * diagW d : ℚ) : ℝ) := by
    exact_mod_cast diag_resid d
  have h2 : (0 : ℝ) ≤ diagB d := by exact_mod_cast diagB_nonneg d
  push_cast at h1
  linarith

/-- **The paper's residual is positive** (`prop:joint-middle-mean`, the 192 gates):
`μ ≤ diagB(d)` gives `63 (κ_b − var) − μ > 23.66`. -/
theorem resid_paper_nonneg (d : PaperDiag) (μ : ℝ) (hμ : μ ≤ diagB d) :
    2366 / 100 < 63 * (diagW d : ℝ) - μ := by
  have h1 : ((diagB d + 2366 / 100 : ℚ) : ℝ) < ((63 * diagW d : ℚ) : ℝ) := by
    exact_mod_cast diag_resid d
  push_cast at h1
  linarith

/-- With `μK ≤ diagB`, the exact weights are at most `1`. -/
theorem wtOf_le_one (labK : K → PaperDiag) (μK : K → ℝ)
    (hμ : ∀ k, μK k ≤ diagB (labK k)) (k : K) : wtOf labK μK k ≤ 1 := by
  unfold wtOf
  split_ifs with h
  · exact le_rfl
  · have hd : (0 : ℝ) < diagB (labK k) :=
      lt_of_le_of_ne (by exact_mod_cast diagB_nonneg (labK k)) (Ne.symm h)
    rw [div_le_one hd]
    exact hμ k

/-- **The booked coefficient of a labelled selection is the paper's residual**: with
`w_k = (κ_b − var)/wt_k` and `wt = wtOf labK μK`, `(63 w_k − diagB) wt_k = 63 (κ_b − var) − μK_k`.
On labels with `diagB = 0` we need `μK = 0`; on the others `μK ≠ 0`. -/
theorem bookedCoef_paper (labK : K → PaperDiag) (μK : K → ℝ)
    (hz : ∀ k, (diagB (labK k) : ℝ) = 0 → μK k = 0)
    (hnz : ∀ k, (diagB (labK k) : ℝ) ≠ 0 → μK k ≠ 0) (k : K) :
    coefOf (fun j => 63 * ((diagW (labK j) : ℝ) / wtOf labK μK j) - diagB (labK j))
        (wtOf labK μK) (some k) = 63 * (diagW (labK k) : ℝ) - μK k := by
  simp only [coefOf, Option.elim_some, wtOf]
  split_ifs with h
  · rw [hz k h, h]
    ring
  · have hμ := hnz k h
    field_simp

/-- The booked coefficient for any selection label (`0` when unlabelled). -/
theorem bookedCoef_paper' (labK : K → PaperDiag) (μK : K → ℝ)
    (hz : ∀ k, (diagB (labK k) : ℝ) = 0 → μK k = 0)
    (hnz : ∀ k, (diagB (labK k) : ℝ) ≠ 0 → μK k ≠ 0) (o : Option K) :
    coefOf (fun j => 63 * ((diagW (labK j) : ℝ) / wtOf labK μK j) - diagB (labK j))
        (wtOf labK μK) o = o.elim 0 fun k => 63 * (diagW (labK k) : ℝ) - μK k := by
  rcases o with _ | k
  · rfl
  · exact bookedCoef_paper labK μK hz hnz k

end Sarkozy.MeanCredit2
