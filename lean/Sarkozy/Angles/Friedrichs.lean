module

public import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
public import Mathlib.Analysis.InnerProductSpace.Projection.Submodule

/-!
# The Friedrichs angle between two subspaces

`def:prelim:angle` (`paper/sections/04_notation.tex`). For subspaces `V`, `W` of a real inner
product space,
`cos∠(V, W) = sup {|⟪v, w⟫| : v ∈ V, w ∈ W, ‖v‖ = ‖w‖ = 1, v, w ⊥ V ⊓ W}`,
and the supremum of the empty set is `0` (`Real.sSup_empty`), which is the paper's convention
when one space contains the other (`friedrichsCos_eq_zero_of_le`).

The definition makes sense in any real inner product space. The results that use orthogonal
projections assume `[FiniteDimensional ℝ E]`, the setting of the paper.

Main API.
* `friedrichsCos_nonneg`, `friedrichsCos_le_one`, `friedrichsCos_comm`.
* `abs_inner_le_friedrichsCos`: the bound `|⟪v, w⟫| ≤ cos∠(V, W) ‖v‖ ‖w‖` for admissible
  `v`, `w`; the one-sided forms `abs_inner_le_friedrichsCos_of_right` and
  `abs_inner_le_friedrichsCos_of_left` need only one of the two vectors to be orthogonal to
  `V ⊓ W`.
* `friedrichsCos_le_of_forall`, `friedrichsCos_le_iff`: the supremum characterization.
* `norm_starProjection_le_friedrichsCos` (Kassabov, Cor. 3.5(a)) and
  `one_sub_friedrichsCos_sq_mul_le` (Cor. 3.5(b), squared): the projection bounds.
* `friedrichsCos_mono`: shrinking both spaces while keeping their intersection does not
  increase the cosine.
-/

@[expose] public section

open scoped InnerProductSpace

namespace Sarkozy.Angles

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The values `|⟪v, w⟫|` over the unit vectors `v ∈ V`, `w ∈ W` orthogonal to `V ⊓ W`. -/
def friedrichsSet (V W : Submodule ℝ E) : Set ℝ :=
  {r | ∃ v ∈ V, ∃ w ∈ W, v ∈ (V ⊓ W)ᗮ ∧ w ∈ (V ⊓ W)ᗮ ∧ ‖v‖ = 1 ∧ ‖w‖ = 1 ∧ r = |⟪v, w⟫_ℝ|}

/-- **The cosine of the Friedrichs angle** (`def:prelim:angle`): the supremum of `|⟪v, w⟫|`
over unit vectors `v ∈ V`, `w ∈ W` orthogonal to `V ⊓ W`; it is `0` if there are no such
vectors (for instance if one space contains the other). -/
noncomputable def friedrichsCos (V W : Submodule ℝ E) : ℝ := sSup (friedrichsSet V W)

theorem le_one_of_mem_friedrichsSet {V W : Submodule ℝ E} {r : ℝ}
    (hr : r ∈ friedrichsSet V W) : r ≤ 1 := by
  obtain ⟨v, -, w, -, -, -, hv, hw, rfl⟩ := hr
  calc |⟪v, w⟫_ℝ| ≤ ‖v‖ * ‖w‖ := abs_real_inner_le_norm v w
    _ = 1 := by rw [hv, hw, one_mul]

theorem friedrichsSet_bddAbove (V W : Submodule ℝ E) : BddAbove (friedrichsSet V W) :=
  ⟨1, fun _ hr => le_one_of_mem_friedrichsSet hr⟩

theorem friedrichsCos_nonneg (V W : Submodule ℝ E) : 0 ≤ friedrichsCos V W :=
  Real.sSup_nonneg (by rintro _ ⟨v, -, w, -, -, -, -, -, rfl⟩; exact abs_nonneg _)

theorem friedrichsCos_le_one (V W : Submodule ℝ E) : friedrichsCos V W ≤ 1 :=
  Real.sSup_le (fun _ hr => le_one_of_mem_friedrichsSet hr) zero_le_one

theorem friedrichsSet_comm (V W : Submodule ℝ E) : friedrichsSet V W = friedrichsSet W V := by
  ext r
  constructor <;> rintro ⟨v, hv, w, hw, hv', hw', hnv, hnw, rfl⟩ <;>
    exact ⟨w, hw, v, hv, by rwa [inf_comm], by rwa [inf_comm], hnw, hnv, by
      rw [real_inner_comm]⟩

/-- The Friedrichs cosine is symmetric. -/
theorem friedrichsCos_comm (V W : Submodule ℝ E) : friedrichsCos V W = friedrichsCos W V := by
  rw [friedrichsCos, friedrichsCos, friedrichsSet_comm]

/-- **The pairwise bound.** For `v ∈ V`, `w ∈ W`, both orthogonal to `V ⊓ W`,
`|⟪v, w⟫| ≤ cos∠(V, W) ‖v‖ ‖w‖`. -/
theorem abs_inner_le_friedrichsCos {V W : Submodule ℝ E} {v w : E} (hv : v ∈ V) (hw : w ∈ W)
    (hv' : v ∈ (V ⊓ W)ᗮ) (hw' : w ∈ (V ⊓ W)ᗮ) :
    |⟪v, w⟫_ℝ| ≤ friedrichsCos V W * ‖v‖ * ‖w‖ := by
  rcases eq_or_ne v 0 with rfl | hv0
  · simp
  rcases eq_or_ne w 0 with rfl | hw0
  · simp
  have hnv : 0 < ‖v‖ := norm_pos_iff.mpr hv0
  have hnw : 0 < ‖w‖ := norm_pos_iff.mpr hw0
  have hmem : |⟪‖v‖⁻¹ • v, ‖w‖⁻¹ • w⟫_ℝ| ∈ friedrichsSet V W :=
    ⟨‖v‖⁻¹ • v, V.smul_mem _ hv, ‖w‖⁻¹ • w, W.smul_mem _ hw, (V ⊓ W)ᗮ.smul_mem _ hv',
      (V ⊓ W)ᗮ.smul_mem _ hw', by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnv.ne'],
      by rw [norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hnw.ne'], rfl⟩
  have hle := le_csSup (friedrichsSet_bddAbove V W) hmem
  have heq : |⟪‖v‖⁻¹ • v, ‖w‖⁻¹ • w⟫_ℝ| = |⟪v, w⟫_ℝ| / (‖v‖ * ‖w‖) := by
    rw [real_inner_smul_left, real_inner_smul_right, abs_mul, abs_mul, abs_inv, abs_inv,
      abs_norm, abs_norm, div_eq_mul_inv, mul_inv]
    ring
  rw [heq, div_le_iff₀ (mul_pos hnv hnw)] at hle
  calc |⟪v, w⟫_ℝ| ≤ sSup (friedrichsSet V W) * (‖v‖ * ‖w‖) := hle
    _ = friedrichsCos V W * ‖v‖ * ‖w‖ := by rw [friedrichsCos, mul_assoc]

/-- **The supremum characterization.** A nonnegative `c` that bounds `|⟪v, w⟫|/(‖v‖ ‖w‖)` for
all admissible pairs bounds `cos∠(V, W)`. -/
theorem friedrichsCos_le_of_forall {V W : Submodule ℝ E} {c : ℝ} (hc : 0 ≤ c)
    (h : ∀ v ∈ V, ∀ w ∈ W, v ∈ (V ⊓ W)ᗮ → w ∈ (V ⊓ W)ᗮ → |⟪v, w⟫_ℝ| ≤ c * ‖v‖ * ‖w‖) :
    friedrichsCos V W ≤ c := by
  refine Real.sSup_le ?_ hc
  rintro _ ⟨v, hv, w, hw, hv', hw', hnv, hnw, rfl⟩
  simpa [hnv, hnw] using h v hv w hw hv' hw'

theorem friedrichsCos_le_iff {V W : Submodule ℝ E} {c : ℝ} (hc : 0 ≤ c) :
    friedrichsCos V W ≤ c ↔
      ∀ v ∈ V, ∀ w ∈ W, v ∈ (V ⊓ W)ᗮ → w ∈ (V ⊓ W)ᗮ → |⟪v, w⟫_ℝ| ≤ c * ‖v‖ * ‖w‖ := by
  refine ⟨fun h v hv w hw hv' hw' => ?_, friedrichsCos_le_of_forall hc⟩
  calc |⟪v, w⟫_ℝ| ≤ friedrichsCos V W * ‖v‖ * ‖w‖ := abs_inner_le_friedrichsCos hv hw hv' hw'
    _ ≤ c * ‖v‖ * ‖w‖ := by gcongr

/-- If `V ≤ W` there are no admissible unit vectors in `V`, and the cosine is `0`. -/
theorem friedrichsCos_eq_zero_of_le {V W : Submodule ℝ E} (h : V ≤ W) :
    friedrichsCos V W = 0 := by
  have hempty : friedrichsSet V W = ∅ := by
    ext r
    simp only [Set.mem_empty_iff_false, iff_false]
    rintro ⟨v, hv, w, -, hv', -, hnv, -, -⟩
    have h0 : ⟪v, v⟫_ℝ = 0 :=
      Submodule.inner_right_of_mem_orthogonal (Submodule.mem_inf.mpr ⟨hv, h hv⟩) hv'
    rw [real_inner_self_eq_norm_sq, hnv] at h0
    norm_num at h0
  rw [friedrichsCos, hempty, Real.sSup_empty]

theorem friedrichsCos_eq_zero_of_ge {V W : Submodule ℝ E} (h : W ≤ V) :
    friedrichsCos V W = 0 := by
  rw [friedrichsCos_comm]
  exact friedrichsCos_eq_zero_of_le h

/-- **Monotonicity.** Shrinking both spaces without shrinking their intersection does not
increase the cosine: every admissible pair for `(V', W')` is admissible for `(V, W)`. -/
theorem friedrichsCos_mono {V V' W W' : Submodule ℝ E} (hV : V' ≤ V) (hW : W' ≤ W)
    (hI : V ⊓ W ≤ V' ⊓ W') : friedrichsCos V' W' ≤ friedrichsCos V W :=
  friedrichsCos_le_of_forall (friedrichsCos_nonneg V W) fun _ hv _ hw hv' hw' =>
    abs_inner_le_friedrichsCos (hV hv) (hW hw) (Submodule.orthogonal_le hI hv')
      (Submodule.orthogonal_le hI hw')

section FiniteDimensional

variable [FiniteDimensional ℝ E]

/-- **One-sided bound.** It suffices that the vector of `W` is orthogonal to `V ⊓ W`:
for `v ∈ V` and `w ∈ W ⊓ (V ⊓ W)ᗮ`, `|⟪v, w⟫| ≤ cos∠(V, W) ‖v‖ ‖w‖`. -/
theorem abs_inner_le_friedrichsCos_of_right {V W : Submodule ℝ E} {v w : E} (hv : v ∈ V)
    (hw : w ∈ W) (hw' : w ∈ (V ⊓ W)ᗮ) :
    |⟪v, w⟫_ℝ| ≤ friedrichsCos V W * ‖v‖ * ‖w‖ := by
  set v' := v - (V ⊓ W).starProjection v with hv'def
  have hPv : (V ⊓ W).starProjection v ∈ V ⊓ W := Submodule.starProjection_apply_mem _ _
  have hv'V : v' ∈ V := V.sub_mem hv (Submodule.mem_inf.mp hPv).1
  have hv'o : v' ∈ (V ⊓ W)ᗮ := Submodule.sub_starProjection_mem_orthogonal v
  have hinner : ⟪v, w⟫_ℝ = ⟪v', w⟫_ℝ := by
    rw [hv'def, inner_sub_left, Submodule.inner_right_of_mem_orthogonal hPv hw', sub_zero]
  have hnorm : ‖v'‖ ≤ ‖v‖ := by
    rw [hv'def, ← Submodule.starProjection_orthogonal_val]
    exact Submodule.norm_starProjection_apply_le _ v
  calc |⟪v, w⟫_ℝ| = |⟪v', w⟫_ℝ| := by rw [hinner]
    _ ≤ friedrichsCos V W * ‖v'‖ * ‖w‖ := abs_inner_le_friedrichsCos hv'V hw hv'o hw'
    _ ≤ friedrichsCos V W * ‖v‖ * ‖w‖ := by
      have := friedrichsCos_nonneg V W
      gcongr

/-- **One-sided bound**, the other side: for `v ∈ V ⊓ (V ⊓ W)ᗮ` and `w ∈ W`. -/
theorem abs_inner_le_friedrichsCos_of_left {V W : Submodule ℝ E} {v w : E} (hv : v ∈ V)
    (hv' : v ∈ (V ⊓ W)ᗮ) (hw : w ∈ W) :
    |⟪v, w⟫_ℝ| ≤ friedrichsCos V W * ‖v‖ * ‖w‖ := by
  have h := abs_inner_le_friedrichsCos_of_right (V := W) (W := V) hw hv (by rwa [inf_comm])
  rw [real_inner_comm, friedrichsCos_comm] at h
  linarith

/-- `⟪P_V w, w⟫ = ‖P_V w‖²`. -/
theorem inner_starProjection_self (V : Submodule ℝ E) (w : E) :
    ⟪V.starProjection w, w⟫_ℝ = ‖V.starProjection w‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq]
  conv_lhs => rw [← Submodule.starProjection_eq_self_iff.mpr
    (Submodule.starProjection_apply_mem V w)]
  rw [Submodule.inner_starProjection_left_eq_right]

/-- **Projection bound** (Kassabov, Cor. 3.5(a)): for `w ∈ W ⊓ (V ⊓ W)ᗮ`,
`‖P_V w‖ ≤ cos∠(V, W) ‖w‖`. -/
theorem norm_starProjection_le_friedrichsCos {V W : Submodule ℝ E} {w : E} (hw : w ∈ W)
    (hw' : w ∈ (V ⊓ W)ᗮ) : ‖V.starProjection w‖ ≤ friedrichsCos V W * ‖w‖ := by
  set x := V.starProjection w
  have hx : x ∈ V := Submodule.starProjection_apply_mem V w
  have h1 : ‖x‖ ^ 2 ≤ friedrichsCos V W * ‖x‖ * ‖w‖ := by
    rw [← inner_starProjection_self]
    exact (le_abs_self _).trans (abs_inner_le_friedrichsCos_of_right hx hw hw')
  rcases (norm_nonneg x).eq_or_lt with h0 | hpos
  · rw [← h0]
    exact mul_nonneg (friedrichsCos_nonneg V W) (norm_nonneg w)
  · have h2 : ‖x‖ * ‖x‖ ≤ ‖x‖ * (friedrichsCos V W * ‖w‖) := by nlinarith
    exact le_of_mul_le_mul_left h2 hpos

/-- **Projection bound**, the other side: for `v ∈ V ⊓ (V ⊓ W)ᗮ`,
`‖P_W v‖ ≤ cos∠(V, W) ‖v‖`. -/
theorem norm_starProjection_le_friedrichsCos' {V W : Submodule ℝ E} {v : E} (hv : v ∈ V)
    (hv' : v ∈ (V ⊓ W)ᗮ) : ‖W.starProjection v‖ ≤ friedrichsCos V W * ‖v‖ := by
  rw [friedrichsCos_comm]
  exact norm_starProjection_le_friedrichsCos hv (by rwa [inf_comm])

/-- **Projection bound on the complement** (Kassabov, Cor. 3.5(b), squared): for
`w ∈ W ⊓ (V ⊓ W)ᗮ`, `(1 - cos²∠(V, W)) ‖w‖² ≤ ‖P_{Vᗮ} w‖²`. -/
theorem one_sub_friedrichsCos_sq_mul_le {V W : Submodule ℝ E} {w : E} (hw : w ∈ W)
    (hw' : w ∈ (V ⊓ W)ᗮ) :
    (1 - friedrichsCos V W ^ 2) * ‖w‖ ^ 2 ≤ ‖Vᗮ.starProjection w‖ ^ 2 := by
  have hpy := Submodule.norm_sq_eq_add_norm_sq_starProjection w V
  have hb := norm_starProjection_le_friedrichsCos hw hw'
  have hsq : ‖V.starProjection w‖ ^ 2 ≤ (friedrichsCos V W * ‖w‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hb 2
  nlinarith

end FiniteDimensional

end Sarkozy.Angles
