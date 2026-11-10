module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# The normalizations of the matching law (`lem:record:e-law`(b), numerical part)

`paper/sections/21_middle_records.tex`. For `p ≥ 19` and `q = 1/p` put
* `z^E_0 = (p − 3)(p − 4)(p − 5)/(p(p − 1)(p − 2))`, the probability that two independent
  uniform triples of distinct labels are disjoint;
* `z_1 = (p² − 3p + 4)/(p(p − 1))`.

Proved here (`e_law_numerics`):
* `z^E_0 ≥ 1 − 9q` and `z_1 ≥ 1 − 2q`;
* `z_1 − z^E_0 = (7p² − 37p + 52)/(p(p − 1)(p − 2)) > 0`;
* `3/(p − 3) ≤ 9q/(1 − 9q)`, i.e. the exact norm `3/(p − 3)` of `K^E_0` on mean-zero functions
  lies below the stated cap `k^E_old`.

The exact norm itself is WP-S's disjoint-triple bound (`TraceMixing.disjOp_abs_le`,
`disjOp_eigen`, `sec:frontier:empty-triple-negative`). The operator assertions of (a), (c) and
(d), and the last inequality of (b), are not formalized here.
-/

@[expose] public section

namespace Sarkozy.Certificates

/-- `z^E_0 = (p − 3)(p − 4)(p − 5)/(p(p − 1)(p − 2))`. -/
noncomputable def zE0 (p : ℝ) : ℝ := (p - 3) * (p - 4) * (p - 5) / (p * (p - 1) * (p - 2))

/-- `z_1 = (p² − 3p + 4)/(p(p − 1))`. -/
noncomputable def z1 (p : ℝ) : ℝ := (p ^ 2 - 3 * p + 4) / (p * (p - 1))

/-- **`lem:record:e-law`(b), numerical part.** -/
theorem e_law_numerics {p : ℝ} (hp : 19 ≤ p) :
    1 - 9 / p ≤ zE0 p ∧ 1 - 2 / p ≤ z1 p ∧
      z1 p - zE0 p = (7 * p ^ 2 - 37 * p + 52) / (p * (p - 1) * (p - 2)) ∧
      0 < z1 p - zE0 p ∧ 3 / (p - 3) ≤ (9 / p) / (1 - 9 / p) := by
  have h0 : 0 < p := by linarith
  have h1 : 0 < p - 1 := by linarith
  have h2 : 0 < p - 2 := by linarith
  have h3 : 0 < p - 3 := by linarith
  have h9 : 0 < p - 9 := by linarith
  have hD : 0 < p * (p - 1) * (p - 2) := by positivity
  have hdiff : z1 p - zE0 p = (7 * p ^ 2 - 37 * p + 52) / (p * (p - 1) * (p - 2)) := by
    unfold z1 zE0
    field_simp
    ring
  refine ⟨?_, ?_, hdiff, ?_, ?_⟩
  · unfold zE0
    rw [show 1 - 9 / p = (p - 9) / p by field_simp, div_le_div_iff₀ h0 hD]
    ring_nf
    nlinarith
  · unfold z1
    rw [show 1 - 2 / p = (p - 2) / p by field_simp, div_le_div_iff₀ h0 (by positivity)]
    ring_nf
    nlinarith
  · rw [hdiff]
    apply div_pos _ hD
    nlinarith
  · have hq : (9 / p) / (1 - 9 / p) = 9 / (p - 9) := by
      field_simp
    rw [hq, div_le_div_iff₀ h3 h9]
    linarith

end Sarkozy.Certificates
