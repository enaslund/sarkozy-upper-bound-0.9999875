module

public import Sarkozy.Angles.Kassabov

/-!
# The Friedrichs cosine is `< 1` in finite dimension

Kassabov, Lemma 3.6 and Corollary 3.7: in finite dimension the supremum defining
`cos∠(V, W)` is attained, and an attained value `1` would force a unit vector into
`V ⊓ W ⊓ (V ⊓ W)ᗮ = 0` (equality case of Cauchy–Schwarz). Hence `friedrichsCos_lt_one`.

Consequently the hypotheses `ε₁₃ < 1`, `ε₂₃ < 1` of `thm:kassabov` always hold in finite
dimension, and `kassabov_angle_inequality'` states the inequality without them.
-/

@[expose] public section

open scoped InnerProductSpace

namespace Sarkozy.Angles

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The admissible pairs of unit vectors for `cos∠(V, W)`. -/
def friedrichsPairs (V W : Submodule ℝ E) : Set (E × E) :=
  {p | p.1 ∈ V ⊓ (V ⊓ W)ᗮ ∧ p.2 ∈ W ⊓ (V ⊓ W)ᗮ ∧ ‖p.1‖ = 1 ∧ ‖p.2‖ = 1}

theorem friedrichsSet_eq_image (V W : Submodule ℝ E) :
    friedrichsSet V W = (fun p : E × E => |⟪p.1, p.2⟫_ℝ|) '' friedrichsPairs V W := by
  ext r
  constructor
  · rintro ⟨v, hv, w, hw, hv', hw', hnv, hnw, rfl⟩
    exact ⟨(v, w), ⟨Submodule.mem_inf.mpr ⟨hv, hv'⟩, Submodule.mem_inf.mpr ⟨hw, hw'⟩, hnv, hnw⟩,
      rfl⟩
  · rintro ⟨⟨v, w⟩, ⟨hv, hw, hnv, hnw⟩, rfl⟩
    obtain ⟨hv1, hv2⟩ := Submodule.mem_inf.mp hv
    obtain ⟨hw1, hw2⟩ := Submodule.mem_inf.mp hw
    exact ⟨v, hv1, w, hw1, hv2, hw2, hnv, hnw, rfl⟩

variable [FiniteDimensional ℝ E]

theorem isCompact_friedrichsPairs (V W : Submodule ℝ E) : IsCompact (friedrichsPairs V W) := by
  have hK : IsCompact (Metric.sphere (0 : E) 1 ×ˢ Metric.sphere (0 : E) 1) :=
    (isCompact_sphere 0 1).prod (isCompact_sphere 0 1)
  have heq : friedrichsPairs V W =
      (Prod.fst ⁻¹' ((V ⊓ (V ⊓ W)ᗮ : Submodule ℝ E) : Set E) ∩
        Prod.snd ⁻¹' ((W ⊓ (V ⊓ W)ᗮ : Submodule ℝ E) : Set E)) ∩
      (Metric.sphere (0 : E) 1 ×ˢ Metric.sphere (0 : E) 1) := by
    ext p
    simp only [friedrichsPairs, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_preimage,
      SetLike.mem_coe, Set.mem_prod, mem_sphere_iff_norm, sub_zero]
    tauto
  rw [heq]
  refine hK.of_isClosed_subset ?_ Set.inter_subset_right
  have h1 : IsClosed ((V ⊓ (V ⊓ W)ᗮ : Submodule ℝ E) : Set E) :=
    Submodule.closed_of_finiteDimensional _
  have h2 : IsClosed ((W ⊓ (V ⊓ W)ᗮ : Submodule ℝ E) : Set E) :=
    Submodule.closed_of_finiteDimensional _
  exact ((h1.preimage continuous_fst).inter (h2.preimage continuous_snd)).inter hK.isClosed

/-- **Kassabov, Lemma 3.6.** In finite dimension, if there is an admissible pair, the supremum
defining `cos∠(V, W)` is attained. -/
theorem exists_friedrichsCos_eq (V W : Submodule ℝ E) (hne : (friedrichsSet V W).Nonempty) :
    ∃ v ∈ V, ∃ w ∈ W, v ∈ (V ⊓ W)ᗮ ∧ w ∈ (V ⊓ W)ᗮ ∧ ‖v‖ = 1 ∧ ‖w‖ = 1 ∧
      friedrichsCos V W = |⟪v, w⟫_ℝ| := by
  have hc : IsCompact (friedrichsSet V W) := by
    rw [friedrichsSet_eq_image]
    exact (isCompact_friedrichsPairs V W).image (by fun_prop)
  exact hc.sSup_mem hne

/-- **Kassabov, Corollary 3.7.** In finite dimension `cos∠(V, W) < 1`. -/
theorem friedrichsCos_lt_one (V W : Submodule ℝ E) : friedrichsCos V W < 1 := by
  rcases (friedrichsSet V W).eq_empty_or_nonempty with h | h
  · rw [friedrichsCos, h, Real.sSup_empty]
    exact zero_lt_one
  obtain ⟨v, hv, w, hw, -, hw', hnv, hnw, heq⟩ := exists_friedrichsCos_eq V W h
  refine lt_of_le_of_ne (friedrichsCos_le_one V W) fun h1 => ?_
  have hone : |⟪v, w⟫_ℝ / (‖v‖ * ‖w‖)| = 1 := by
    rw [hnv, hnw, mul_one, div_one, ← heq, h1]
  obtain ⟨-, r, -, rfl⟩ := (abs_real_inner_div_norm_mul_norm_eq_one_iff v w).mp hone
  have hmem : r • v ∈ V ⊓ W := Submodule.mem_inf.mpr ⟨V.smul_mem r hv, hw⟩
  have h0 : ⟪r • v, r • v⟫_ℝ = 0 := Submodule.inner_right_of_mem_orthogonal hmem hw'
  rw [real_inner_self_eq_norm_sq, hnw] at h0
  norm_num at h0

/-- **Kassabov's angle inequality without the hypotheses `ε₁₃, ε₂₃ < 1`**, which always hold
in finite dimension (`friedrichsCos_lt_one`). -/
theorem kassabov_angle_inequality' (V₁ V₂ V₃ : Submodule ℝ E) :
    friedrichsCos (V₁ ⊓ V₃) (V₂ ⊓ V₃) ≤
      (friedrichsCos V₁ V₂ + friedrichsCos V₁ V₃ * friedrichsCos V₂ V₃) /
        √((1 - friedrichsCos V₁ V₃ ^ 2) * (1 - friedrichsCos V₂ V₃ ^ 2)) :=
  kassabov_angle_inequality V₁ V₂ V₃ (friedrichsCos_lt_one _ _) (friedrichsCos_lt_one _ _)

/-- Lemma 4.2(a) without the hypotheses `ε₁₃, ε₂₃ < 1`. -/
theorem kassabov_angle_inequality_sup' (V₁ V₂ V₃ : Submodule ℝ E) :
    friedrichsCos (V₁ ⊔ V₃) (V₂ ⊔ V₃) ≤
      (friedrichsCos V₁ V₂ + friedrichsCos V₁ V₃ * friedrichsCos V₂ V₃) /
        √((1 - friedrichsCos V₁ V₃ ^ 2) * (1 - friedrichsCos V₂ V₃ ^ 2)) :=
  kassabov_angle_inequality_sup V₁ V₂ V₃ (friedrichsCos_lt_one _ _) (friedrichsCos_lt_one _ _)

end Sarkozy.Angles
