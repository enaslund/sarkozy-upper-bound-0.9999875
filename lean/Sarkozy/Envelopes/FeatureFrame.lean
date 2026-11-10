module

public import Sarkozy.Envelopes.FeatureCert
public import Mathlib.Analysis.InnerProductSpace.Basic

@[expose] public section

/-!
# The fold frame bound (`lem:oct24:feature-block`(b), Step 5)

`paper/sections/23_envelopes.tex`, `lem:oct24:feature-block`(b): the synthesis map
`(h_v)_v ↦ ∑_v h_v` of the five fold features has squared norm at most `Γ_F = 1 + λ` for every
`λ > ϱ₃₄` satisfying the Perron gate `eq:feature-perron`, given the correlation bounds of (a).

**Form.** The five features are vectors `h₀, …, h₄` of a real inner product space (the components
in `ℋ₀, ℋ₁, ℋ₂, 𝒦₁₂, 𝒦₀₁`), and the correlation bounds of part (a) are hypotheses: `|⟪h_v, h_w⟫|`
is at most `ϱ_{vw} ‖h_v‖ ‖h_w‖` for the edges `01, 02, 03, 12, 24, 34` (with `ϱ₁₂ = ϱ₀₁`,
`ϱ₂₄ = ϱ₀₃`), and zero for the other pairs. Part (a) itself is not proved here.

**Proof.** The paper uses the weighted-frame lemma of Part II, (a) and (c) (the Perron block
of the orbits
`{0, 2}, {3, 4}, {1}`). Here the Schur test is applied directly with the positive vector
`p = (1, 2ϱ₀₁/λ, 1, ϱ₀₃/(λ - ϱ₃₄), ϱ₀₃/(λ - ϱ₃₄))`, the Perron vector of the block: `G p ≤ λ p`
entrywise is exactly the gate (`schur_test`, `feature_frame`). With the certified gate at every
middle block (`feature_perron_gate`), `feature_frame_middle` gives the frame bound
`Γ_F = 500111979555137707696357560603/(5·10²⁹)` at every block with least prime `b ≥ Q₃`, given the
correlation bounds (a) at `b` (`ϱ₀₁, ϱ₀₃ > 0` there).
-/

namespace Sarkozy.Envelopes

open Finset
open scoped RealInnerProductSpace

/-- **The Schur test.** For a symmetric nonnegative matrix `G` and a positive vector `p` with
`∑_j G_ij p_j ≤ M p_i`, the form satisfies `∑_{i,j} G_ij a_i a_j ≤ M ∑_i a_i²`. -/
theorem schur_test {ι : Type*} [Fintype ι] (G : ι → ι → ℝ) (hGs : ∀ i j, G i j = G j i)
    (hG0 : ∀ i j, 0 ≤ G i j) (p : ι → ℝ) (hp : ∀ i, 0 < p i) {M : ℝ}
    (hM : ∀ i, ∑ j, G i j * p j ≤ M * p i) (a : ι → ℝ) :
    ∑ i, ∑ j, G i j * (a i * a j) ≤ M * ∑ i, a i ^ 2 := by
  have hamgm : ∀ i j, G i j * (a i * a j) ≤
      G i j * (p j / p i * a i ^ 2 + p i / p j * a j ^ 2) / 2 := by
    intro i j
    have hi := hp i; have hj := hp j
    have key : 2 * (a i * a j) ≤ p j / p i * a i ^ 2 + p i / p j * a j ^ 2 := by
      have e : p j / p i * a i ^ 2 + p i / p j * a j ^ 2 - 2 * (a i * a j) =
          (p j * a i - p i * a j) ^ 2 / (p i * p j) := by
        field_simp; ring
      have : 0 ≤ (p j * a i - p i * a j) ^ 2 / (p i * p j) := by positivity
      linarith
    have := mul_le_mul_of_nonneg_left key (hG0 i j)
    linarith
  have hsplit : ∑ i, ∑ j, G i j * (p j / p i * a i ^ 2 + p i / p j * a j ^ 2) / 2 =
      ∑ i, a i ^ 2 / p i * ∑ j, G i j * p j := by
    have e1 : ∑ i, ∑ j, G i j * (p j / p i * a i ^ 2 + p i / p j * a j ^ 2) / 2 =
        (∑ i, ∑ j, G i j * (p j / p i * a i ^ 2) +
          ∑ i, ∑ j, G i j * (p i / p j * a j ^ 2)) / 2 := by
      rw [← sum_add_distrib, sum_div]
      refine sum_congr rfl fun i _ => ?_
      rw [← sum_add_distrib, sum_div]
      exact sum_congr rfl fun j _ => by ring
    have e2 : ∑ i, ∑ j, G i j * (p i / p j * a j ^ 2) =
        ∑ i, ∑ j, G i j * (p j / p i * a i ^ 2) := by
      rw [sum_comm]
      exact sum_congr rfl fun i _ => sum_congr rfl fun j _ => by rw [hGs]
    rw [e1, e2]
    have e3 : ∀ i, ∑ j, G i j * (p j / p i * a i ^ 2) = a i ^ 2 / p i * ∑ j, G i j * p j := by
      intro i
      rw [mul_sum]
      exact sum_congr rfl fun j _ => by ring
    simp only [e3]
    ring
  calc ∑ i, ∑ j, G i j * (a i * a j)
      ≤ ∑ i, ∑ j, G i j * (p j / p i * a i ^ 2 + p i / p j * a j ^ 2) / 2 :=
        sum_le_sum fun i _ => sum_le_sum fun j _ => hamgm i j
    _ = ∑ i, a i ^ 2 / p i * ∑ j, G i j * p j := hsplit
    _ ≤ ∑ i, a i ^ 2 / p i * (M * p i) :=
        sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hM i)
          (div_nonneg (sq_nonneg _) (hp i).le)
    _ = M * ∑ i, a i ^ 2 := by
        rw [mul_sum]
        exact sum_congr rfl fun i _ => by field_simp [(hp i).ne']

/-- The off-diagonal correlation pattern of `lem:oct24:feature-block`(a), on the labels
`0, …, 4` of `ℋ₀, ℋ₁, ℋ₂, 𝒦₁₂, 𝒦₀₁`. -/
def foldPattern (r02 r01 r03 r34 : ℝ) : Fin 5 → Fin 5 → ℝ :=
  ![![0, r01, r02, r03, 0],
    ![r01, 0, r01, 0, 0],
    ![r02, r01, 0, 0, r03],
    ![r03, 0, 0, 0, r34],
    ![0, 0, r03, r34, 0]]

/-- **The Perron vector.** If `λ > ϱ₃₄ ≥ 0`, `ϱ₀₁, ϱ₀₃ > 0`, `ϱ₀₂ ≥ 0` and the gate
`eq:feature-perron` holds, then the off-diagonal part `G` satisfies `G p ≤ λ p` entrywise for
`p = (1, 2ϱ₀₁/λ, 1, ϱ₀₃/(λ - ϱ₃₄), ϱ₀₃/(λ - ϱ₃₄)) > 0`, hence (Schur test) its form is at most
`λ ∑ a_v²`. -/
theorem foldPattern_form_le {r02 r01 r03 r34 lam : ℝ} (h02 : 0 ≤ r02) (h01 : 0 < r01)
    (h03 : 0 < r03) (h34 : 0 ≤ r34) (hlam : r34 < lam)
    (hgate : 0 ≤ perronGate lam r02 r01 r03 r34) (a : Fin 5 → ℝ) :
    ∑ i, ∑ j, foldPattern r02 r01 r03 r34 i j * (a i * a j) ≤ lam * ∑ i, a i ^ 2 := by
  have hl : 0 < lam := lt_of_le_of_lt h34 hlam
  have hd : 0 < lam - r34 := by linarith
  set y := r03 / (lam - r34) with hy
  set z := 2 * r01 / lam with hz
  have hy0 : 0 < y := div_pos h03 hd
  have hz0 : 0 < z := div_pos (by linarith) hl
  let p : Fin 5 → ℝ := ![1, z, 1, y, y]
  have hp : ∀ i, 0 < p i := by
    intro i; fin_cases i <;> simp [p, hy0, hz0]
  have hgate' : r01 * z + r02 + r03 * y ≤ lam := by
    unfold perronGate at hgate
    have e1 : r01 * z = 2 * r01 ^ 2 / lam := by rw [hz]; field_simp
    have e2 : r03 * y = r03 ^ 2 / (lam - r34) := by rw [hy]; field_simp
    linarith
  have hrow : ∀ i, ∑ j, foldPattern r02 r01 r03 r34 i j * p j ≤ lam * p i := by
    intro i
    have hy' : r03 + r34 * y = lam * y := by
      rw [hy]; field_simp; ring
    have hz' : 2 * r01 = lam * z := by rw [hz]; field_simp
    fin_cases i <;> simp [foldPattern, p, Fin.sum_univ_five] <;> nlinarith
  have hsymm : ∀ i j, foldPattern r02 r01 r03 r34 i j = foldPattern r02 r01 r03 r34 j i := by
    intro i j; fin_cases i <;> fin_cases j <;> rfl
  have hnn : ∀ i j, 0 ≤ foldPattern r02 r01 r03 r34 i j := by
    intro i j; fin_cases i <;> fin_cases j <;> simp [foldPattern] <;> linarith
  exact schur_test _ hsymm hnn p hp hrow a

/-- **`lem:oct24:feature-block`(b).** Let `h₀, …, h₄` be the components in the five fold features,
with the correlation bounds of part (a) (`|⟪h_v, h_w⟫| ≤ ϱ_{vw} ‖h_v‖‖h_w‖`, the pattern
`foldPattern`, zero for non-edges). If `λ > ϱ₃₄` satisfies `eq:feature-perron`, then
`‖∑_v h_v‖² ≤ (1 + λ) ∑_v ‖h_v‖²`: the synthesis map has squared norm at most `Γ_F = 1 + λ`. -/
theorem feature_frame {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    {r02 r01 r03 r34 lam : ℝ} (h02 : 0 ≤ r02) (h01 : 0 < r01) (h03 : 0 < r03) (h34 : 0 ≤ r34)
    (hlam : r34 < lam) (hgate : 0 ≤ perronGate lam r02 r01 r03 r34) (h : Fin 5 → H)
    (hcor : ∀ i j, i ≠ j → |⟪h i, h j⟫| ≤ foldPattern r02 r01 r03 r34 i j * ‖h i‖ * ‖h j‖) :
    ‖∑ i, h i‖ ^ 2 ≤ (1 + lam) * ∑ i, ‖h i‖ ^ 2 := by
  have hexp : ‖∑ i, h i‖ ^ 2 = ∑ i, ∑ j, ⟪h i, h j⟫ := by
    rw [← real_inner_self_eq_norm_sq, sum_inner]
    simp only [inner_sum]
  have hoff : ∑ i, ∑ j, ⟪h i, h j⟫ ≤
      ∑ i, ‖h i‖ ^ 2 + ∑ i, ∑ j, foldPattern r02 r01 r03 r34 i j * (‖h i‖ * ‖h j‖) := by
    have hdiag : ∀ i, foldPattern r02 r01 r03 r34 i i = 0 := by
      intro i; fin_cases i <;> rfl
    have hterm : ∀ i j, ⟪h i, h j⟫ ≤ (if i = j then ‖h i‖ ^ 2 else 0) +
        foldPattern r02 r01 r03 r34 i j * (‖h i‖ * ‖h j‖) := by
      intro i j
      by_cases hij : i = j
      · subst hij
        simp only [↓reduceIte, hdiag, zero_mul, add_zero, real_inner_self_eq_norm_sq, le_refl]
      · simp only [hij, ↓reduceIte, zero_add]
        have := hcor i j hij
        calc ⟪h i, h j⟫ ≤ |⟪h i, h j⟫| := le_abs_self _
          _ ≤ _ := this
          _ = _ := by ring
    calc ∑ i, ∑ j, ⟪h i, h j⟫ ≤ ∑ i, ∑ j, ((if i = j then ‖h i‖ ^ 2 else 0) +
          foldPattern r02 r01 r03 r34 i j * (‖h i‖ * ‖h j‖)) :=
          sum_le_sum fun i _ => sum_le_sum fun j _ => hterm i j
      _ = _ := by
          simp only [sum_add_distrib, sum_ite_eq, mem_univ, ↓reduceIte]
  have hform := foldPattern_form_le h02 h01 h03 h34 hlam hgate (fun i => ‖h i‖)
  rw [hexp]
  linarith

/-- **`lem:oct24:feature-block`(b) at every middle block.** For a block with least prime `b ≥ Q₃`
(`q = 1/b`, `r = b^{-1/2}`), if the five fold features satisfy the correlation bounds (a) with the
constants `ϱ_{vw}(q, r)`, the synthesis map has squared norm at most
`Γ_F = 500111979555137707696357560603/(5·10²⁹)`. -/
theorem feature_frame_middle {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] {b : ℝ}
    (hb : 19951586 ≤ b) (h : Fin 5 → H)
    (hcor : ∀ i j, i ≠ j → |⟪h i, h j⟫| ≤ foldPattern (rho02 (1 / b) (1 / Real.sqrt b))
      (rho01 (1 / b)) (rho03 (1 / b) (1 / Real.sqrt b)) (rho34 (1 / b) (1 / Real.sqrt b)) i j *
        ‖h i‖ * ‖h j‖) :
    ‖∑ i, h i‖ ^ 2 ≤ (gammaF : ℝ) * ∑ i, ‖h i‖ ^ 2 := by
  obtain ⟨hlam, hgate⟩ := feature_perron_gate hb
  have hb0 : 0 < b := by linarith
  have hq : 0 < 1 / b := by positivity
  have hq8 : 1 / b ≤ 1 / 8 := by rw [div_le_div_iff₀ hb0 (by norm_num)]; linarith
  have hr : 0 < 1 / Real.sqrt b := by positivity
  have h02 : 0 ≤ rho02 (1 / b) (1 / Real.sqrt b) := by
    unfold rho02
    exact div_nonneg (mul_nonneg hr.le (Real.sqrt_nonneg _)) (by linarith)
  have h01 : 0 < rho01 (1 / b) := by
    unfold rho01
    refine mul_pos (div_pos hq (by linarith)) (Real.sqrt_pos.2 ?_)
    have : 0 ≤ 4 * (1 / b) / (1 - 4 * (1 / b)) ^ 2 := by positivity
    linarith
  have h03 : 0 < rho03 (1 / b) (1 / Real.sqrt b) := by
    unfold rho03
    have a : 0 < 1 - 3 * (1 / b) := by linarith
    have c : 0 < 1 - 6 * (1 / b) := by linarith
    have d : 0 < 1 - 2 * (1 / b) := by linarith
    have : 0 < 1 / b / (1 - 3 * (1 / b)) := div_pos hq a
    have : 0 ≤ 2 * (1 / b) ^ 2 / ((1 - 3 * (1 / b)) * (1 - 6 * (1 / b))) := by positivity
    have : 0 ≤ 2 * (1 / b) * (1 / Real.sqrt b) / ((1 - 6 * (1 / b)) * (1 - 2 * (1 / b))) := by
      positivity
    linarith
  have h34 : 0 ≤ rho34 (1 / b) (1 / Real.sqrt b) := by
    unfold rho34
    have a : 0 < 1 - 4 * (1 / b) := by linarith
    have c : 0 < 1 - 6 * (1 / b) := by linarith
    have : 0 ≤ 4 * (1 / b) ^ 2 / (1 - 4 * (1 / b)) := by positivity
    exact div_nonneg (by linarith) c.le
  have := feature_frame h02 h01 h03 h34 hlam hgate h hcor
  have e : (1 : ℝ) + ((gammaF : ℝ) - 1) = gammaF := by ring
  rwa [e] at this

end Sarkozy.Envelopes
