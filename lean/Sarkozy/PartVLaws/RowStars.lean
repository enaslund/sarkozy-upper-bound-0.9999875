module

public import Sarkozy.PartVLaws.RowGeometry
public import Sarkozy.JointRows.StarTailBound

/-! The star constants for all ten nontrivial tail rows, in both prime classes. -/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.PartVLaws.FieldGraphs.RowCase

open Finset Sarkozy.JointRows Sarkozy.JointRows.StarOps Sarkozy.FiveType
  Sarkozy.FiveType.Blocks

variable {p : ℕ} [Fact p.Prime]

noncomputable def coefficients (c : RowCase) (i j : c.Index) : ℝ :=
  PaleyGauss.chiR p (c.crossSign i j : ZMod p)

theorem abs_coefficients_le_one (c : RowCase) (i j : c.Index) :
    |c.coefficients (p := p) i j| ≤ 1 := abs_chiR_le_one _

theorem coefficients_zero (c : RowCase) (i j : c.Index) (h : c.crossSign i j = 0) :
    c.coefficients (p := p) i j = 0 := by simp [coefficients, h, PaleyGauss.chiR]

theorem coefficients_row_sum (c : RowCase) (i : c.Index) :
    ∑ j, |c.coefficients (p := p) i j| ≤ c.degree := by
  calc
    _ ≤ ∑ j : c.Index, if c.crossSign i j ≠ 0 then (1 : ℝ) else 0 := by
      apply sum_le_sum
      intro j _
      split_ifs with h
      · exact c.abs_coefficients_le_one i j
      · simp only [not_not] at h
        simp [c.coefficients_zero i j h]
    _ = ((c.rowNeighbours i).card : ℝ) := by rw [sum_boole]; rfl
    _ ≤ _ := by exact_mod_cast c.row_degree i

theorem coefficients_col_sum (c : RowCase) (j : c.Index) :
    ∑ i, |c.coefficients (p := p) i j| ≤ c.degree := by
  calc
    _ ≤ ∑ i : c.Index, if c.crossSign i j ≠ 0 then (1 : ℝ) else 0 := by
      apply sum_le_sum
      intro i _
      split_ifs with h
      · exact c.abs_coefficients_le_one i j
      · simp only [not_not] at h
        simp [c.coefficients_zero i j h]
    _ = ((c.colNeighbours j).card : ℝ) := by rw [sum_boole]; rfl
    _ ≤ _ := by exact_mod_cast c.col_degree j

theorem coefficients_opBound (c : RowCase) : Influence.OpBound univ univ
    (fun i j => |c.coefficients (p := p) i j|) c.degree := by
  have h := Influence.opBound_schur (fun i j => abs_nonneg (c.coefficients (p := p) i j))
    (by positivity : (0 : ℝ) ≤ c.degree) (by positivity : (0 : ℝ) ≤ c.degree)
    (fun i _ => c.coefficients_row_sum i) (fun j _ => c.coefficients_col_sum j)
  simpa only [← pow_two, Real.sqrt_sq (by positivity : (0 : ℝ) ≤ c.degree)] using h

theorem coefficients_row_gram (c : RowCase) (i : c.Index) :
    ∑ i', ∑ T ∈ sets2 c.Index, |rowParityCoef (p := p) (c.coefficients (p := p)) i T| *
      |rowParityCoef (p := p) (c.coefficients (p := p)) i' T| ≤ c.gram := by
  calc
    _ ≤ ∑ i', (commonSupports c.rowNeighbours i i' : ℝ) := by
      apply sum_le_sum
      intro i' _
      apply rowParity_gram_le_count _ _ (c.abs_coefficients_le_one) _ i i'
      intro k j hj
      apply c.coefficients_zero
      simpa only [rowNeighbours, mem_filter, mem_univ, true_and, not_not] using hj
    _ ≤ _ := by exact_mod_cast c.row_gram i

theorem coefficients_col_gram (c : RowCase) (j : c.Index) :
    ∑ j', ∑ S ∈ sets2 c.Index, |coefB (c.coefficients (p := p)) j S| *
      |coefB (c.coefficients (p := p)) j' S| ≤ c.gram := by
  calc
    _ ≤ ∑ j', (commonSupports c.colNeighbours j j' : ℝ) := by
      apply sum_le_sum
      intro j' _
      apply coefB_gram_le_count _ _ (c.abs_coefficients_le_one) _ j j'
      intro k i hi
      apply c.coefficients_zero
      simpa only [colNeighbours, mem_filter, mem_univ, true_and, not_not] using hi
    _ ≤ _ := by exact_mod_cast c.col_gram j

theorem star_bound (c : RowCase) (hp : p ≠ 2) (νp : c.Index → FiniteLaw (ZMod p))
    {κ β : ℝ} (hκ : 0 < κ) (hβ0 : 0 ≤ β) (hβ1 : β ≤ 1)
    (hdens : ∀ i t, (νp i).weight t ≤ κ / p)
    (hm : ∀ i j t, (νp i).weight t ≠ 0 → |mchi (νp j) t| ≤ β)
    (f g : (c.Index → ZMod p) → ℝ)
    (hf : (blockLaw νp).expect f = 0) (hg : (blockLaw νp).expect g = 0) :
    |bform νp νp (starKernel (c.coefficients (p := p)) (sets2 c.Index)) f g| ≤
      κ * (Real.sqrt p)⁻¹ *
        (Star.eStar c.degree (Real.sqrt c.gram) +
          2 * Fintype.card c.Index * (sets2 c.Index).card * 2 ^ Fintype.card c.Index * β) *
        nrm (blockLaw νp) f * nrm (blockLaw νp) g :=
  starKernel_bound_odd hp νp (c.coefficients (p := p)) (sets2 c.Index) hκ hβ0 hβ1
    (by positivity) (by positivity) c.abs_coefficients_le_one hdens hm
    (fun _ h => mem_sets2.mp h) c.coefficients_opBound c.coefficients_row_gram
    c.coefficients_col_gram f g hf hg

end Sarkozy.PartVLaws.FieldGraphs.RowCase
