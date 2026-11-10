module

public import Sarkozy.Angles.Kassabov



@[expose] public section

open scoped InnerProductSpace

namespace Sarkozy.Angles

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

theorem zRepair_sup {W T Z : Submodule ℝ E} (hZ : Z ≤ W) : W ⊓ Zᗮ ⊔ (T ⊔ Z) = W ⊔ T := by
  have hW : Z ⊔ Zᗮ ⊓ W = W := Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection hZ
  calc W ⊓ Zᗮ ⊔ (T ⊔ Z) = (Z ⊔ Zᗮ ⊓ W) ⊔ T := by
        rw [inf_comm W, sup_comm T, ← sup_assoc, sup_comm (Zᗮ ⊓ W) Z]
    _ = W ⊔ T := by rw [hW]

omit [FiniteDimensional ℝ E] in
theorem zRepair_inf (W₁ W₂ : Submodule ℝ E) :
    W₁ ⊓ (W₁ ⊓ W₂)ᗮ ⊓ (W₂ ⊓ (W₁ ⊓ W₂)ᗮ) = ⊥ := by
  have h : W₁ ⊓ (W₁ ⊓ W₂)ᗮ ⊓ (W₂ ⊓ (W₁ ⊓ W₂)ᗮ) = (W₁ ⊓ W₂) ⊓ (W₁ ⊓ W₂)ᗮ := by
    ext x
    simp only [Submodule.mem_inf]
    tauto
  rw [h, Submodule.inf_orthogonal_eq_bot]

omit [FiniteDimensional ℝ E] in
theorem zRepair_cos₁₂ (W₁ W₂ : Submodule ℝ E) :
    friedrichsCos (W₁ ⊓ (W₁ ⊓ W₂)ᗮ) (W₂ ⊓ (W₁ ⊓ W₂)ᗮ) ≤ friedrichsCos W₁ W₂ :=
  friedrichsCos_le_of_forall (friedrichsCos_nonneg _ _) fun _ hv _ hw _ _ =>
    abs_inner_le_friedrichsCos (Submodule.mem_inf.mp hv).1 (Submodule.mem_inf.mp hw).1
      (Submodule.mem_inf.mp hv).2 (Submodule.mem_inf.mp hw).2

theorem zRepair_cos₃ {W T Z : Submodule ℝ E} (hZ : Z ≤ W) :
    friedrichsCos (W ⊓ Zᗮ) (T ⊔ Z) ≤ friedrichsCos W T := by
  rw [← friedrichsCos_orthogonal (W ⊓ Zᗮ) (T ⊔ Z), ← friedrichsCos_orthogonal W T,
    orthogonal_inf_eq_sup, Submodule.orthogonal_orthogonal, ← Submodule.inf_orthogonal]
  have hWZ : Wᗮ ≤ Zᗮ := Submodule.orthogonal_le hZ
  refine friedrichsCos_le_of_forall (friedrichsCos_nonneg _ _) fun a ha b hb _ hb' => ?_
  obtain ⟨a', ha', z, hz, rfl⟩ := Submodule.mem_sup.mp ha
  obtain ⟨hbT, hbZ⟩ := Submodule.mem_inf.mp hb
  -- `b ⊥ Wᗮ ⊓ Tᗮ`, which lies in the intersection of the two new spaces
  have hle : Wᗮ ⊓ Tᗮ ≤ (Wᗮ ⊔ Z) ⊓ (Tᗮ ⊓ Zᗮ) := fun x hx => by
    obtain ⟨hxW, hxT⟩ := Submodule.mem_inf.mp hx
    exact Submodule.mem_inf.mpr ⟨Submodule.mem_sup_left hxW,
      Submodule.mem_inf.mpr ⟨hxT, hWZ hxW⟩⟩
  have hb'' : b ∈ (Wᗮ ⊓ Tᗮ)ᗮ := Submodule.orthogonal_le hle hb'
  have hzb : ⟪z, b⟫_ℝ = 0 := Submodule.inner_right_of_mem_orthogonal hz hbZ
  have hinner : ⟪a' + z, b⟫_ℝ = ⟪a', b⟫_ℝ := by rw [inner_add_left, hzb, add_zero]
  -- `‖a'‖ ≤ ‖a' + z‖`, since `a' ∈ Wᗮ ⊥ Z`
  have ha'z : ⟪a', z⟫_ℝ = 0 := Submodule.inner_left_of_mem_orthogonal (hZ hz) ha'
  have hnorm : ‖a'‖ ≤ ‖a' + z‖ := by
    have h := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero a' z ha'z
    have : ‖a'‖ * ‖a'‖ ≤ ‖a' + z‖ * ‖a' + z‖ := by nlinarith [mul_self_nonneg ‖z‖]
    exact (mul_self_le_mul_self_iff (norm_nonneg _) (norm_nonneg _)).mpr this
  rw [hinner]
  calc |⟪a', b⟫_ℝ| ≤ friedrichsCos Wᗮ Tᗮ * ‖a'‖ * ‖b‖ :=
        abs_inner_le_friedrichsCos_of_right ha' hbT hb''
    _ ≤ friedrichsCos Wᗮ Tᗮ * ‖a' + z‖ * ‖b‖ := by
        have := friedrichsCos_nonneg Wᗮ Tᗮ
        gcongr

end Sarkozy.Angles
