module

public import Sarkozy.JointRows.RowsAGate
public import Sarkozy.JointRows.Potential

/-!
# Toy instances for `lem:joint-rows`(a) and `lem:joint-potential` (non-vacuity)

* `toy_joint_rows_a_gate`: every hypothesis of `RowsA.joint_rows_a_gate` holds for the one-point
  row space (`Ω = Unit`), the kernels `K_E = K_F = 1` (so `T_E = T_F = 1`, `C_E = C_F = 0`), zero
  star,
  nonstar and collision parts, the gate with `𝒵 = 𝒜 = 0` (`𝗄 = 1`), and the zero quadratic forms on
  `E = F = ℝ`.
* `toy_pure_part_potential` and `toy_joint_potential`: the same for `Potential.pure_part_potential`
  (one coordinate, one point `t`, `T = 𝒢 = 0`, `D = 1`, `κ₀ = 𝗄 = r = 1`) and
  `Potential.joint_potential`.
* `toy_potential_pointwise`: a non-degenerate case of the pointwise bound: two coordinates,
  `T = 0`, `𝒢 = I`, `𝗄 = 2`, `κ₀ = 1`, `D = diag(1, 0)` supported in `S = {0}`.

The instances are degenerate (all covariances vanish); they show that the hypotheses are
consistent, not that the bounds are sharp.
-/

@[expose] public section

open scoped BigOperators ComplexOrder
open Matrix

namespace Sarkozy.JointRows.RowsASanity

open Sarkozy.FiveType Sarkozy.FiveType.Blocks Sarkozy.JointRows.RowsA

/-- The one-point law. -/
noncomputable def pt : FiniteLaw Unit := FiniteLaw.uniform Unit

theorem pt_weight (x : Unit) : pt.weight x = 1 := by
  simp [pt, FiniteLaw.uniform]

theorem pt_expect (f : Unit → ℝ) : pt.expect f = f () := by
  simp [FiniteLaw.expect, pt_weight]

theorem mass_one : mass pt (fun _ _ => 1) = 1 := by
  simp [mass, kf, pt_weight]

theorem dens1_one (x : Unit) : dens1 pt (fun _ _ => 1) x = 1 := by
  simp [dens1, mass_one, kone, pt_weight]

theorem dens2_one (x : Unit) : dens2 pt (fun _ _ => 1) x = 1 := by
  simp [dens2, mass_one, kone', pt_weight]

theorem nrm_zero_of_centred (Φ : Unit → ℝ) (hΦ : pt.expect Φ = 0) : nrm pt Φ = 0 := by
  rw [pt_expect] at hΦ
  have : Φ = fun _ => 0 := funext fun x => by cases x; exact hΦ
  subst this
  simp [nrm, ip]

theorem formBound_zero (e : ℝ) (he : 0 ≤ e) : FormBound pt (fun _ _ => 0) e := by
  intro Φ Ψ
  simp only [kf, mul_zero, zero_mul, Finset.sum_const_zero, abs_zero]
  exact mul_nonneg (mul_nonneg he (FiveType.nrm_nonneg _ _)) (FiveType.nrm_nonneg _ _)

theorem perpBound_zero : PerpBound pt (fun _ _ => 0) 0 := by
  intro Φ Ψ _ _
  simp [kf]

theorem cen_kone_one : nrm pt (cen pt (kone pt (fun _ _ => 1))) = 0 := by
  apply nrm_zero_of_centred
  exact expect_cen _ _

theorem cen_kone'_one : nrm pt (cen pt (kone' pt (fun _ _ => 1))) = 0 := by
  apply nrm_zero_of_centred
  exact expect_cen _ _

/-- **`lem:joint-rows`(a) from the gate: all hypotheses hold for the one-point toy.** -/
theorem toy_joint_rows_a_gate :
    JointBlockLower pt (matchCov (relDensity pt (fun _ _ => 1) (fun _ => 1)))
      (foldCov pt (relDensity pt (fun _ _ => 1) (fun _ => 1)))
      (Real.exp 0 * (1 * 1 * (1 + 0 + 0) / 1 + cconst 0 0 0 0 + cconst 0 0 0 0)) := by
  refine joint_rows_a_gate (E := ℝ) (F := ℝ) (m := Fin 1) (s := Fin 1) pt pt (fun _ => 1) 0
    (fun _ => by rw [pt_weight, mul_one]) (fun _ _ => by simp)
    (fun _ _ => 1) (fun _ _ => 1) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0)
    (fun _ _ => 0) (fun _ _ => 0)
    (fun x _ => (dens1_one x).symm) (fun x _ => (dens2_one x).symm)
    (fun _ _ _ _ => by ring) (fun _ _ _ _ => by ring)
    (by rw [mass_one]; simp) (by norm_num) le_rfl perpBound_zero (formBound_zero 0 le_rfl)
    (formBound_zero 0 le_rfl) (by norm_num) (by rw [cen_kone_one]) (by rw [cen_kone'_one])
    (by rw [mass_one]; simp) (by norm_num) le_rfl perpBound_zero (formBound_zero 0 le_rfl)
    (formBound_zero 0 le_rfl) (by norm_num) (by rw [cen_kone_one]) (by rw [cen_kone'_one])
    (fun _ => 0) (fun _ => 0) (fun _ => 0) id (fun _ _ => 0) (P := 1) (I₀ := 1) (κ₀ := 1)
    (r := 1) (k := 1) (eF := 0) (eE := 0) ?_ (by norm_num) le_rfl (by norm_num) (by norm_num)
    (by norm_num) le_rfl le_rfl (fun _ => by simp) (fun _ => le_rfl) (fun _ => by simp) 0
    (by simp) 0 ?_ ?_
  · intro Φ Ψ hΦ hΨ
    refine ⟨by simp [stForm, kf], ?_⟩
    rw [nrm_zero_of_centred Φ hΦ, nrm_zero_of_centred Ψ hΨ]
    simp
  · simp only [cplx, Matrix.map_zero, Complex.ofReal_zero, smul_zero, sub_zero, add_zero,
      zero_mul, Complex.ofReal_one, one_pow, one_smul]
    exact Matrix.PosSemidef.one
  · intro _ _ y
    simp only [neg_mul, one_mul, Left.neg_nonpos_iff]
    positivity

/-- **`lem:joint-potential`, the pure part: all hypotheses hold for a one-point toy.** -/
theorem toy_pure_part_potential (x : ℝ) : -(1 * 1) * ‖x‖ ^ 2 ≤ (0 : ℝ) :=
  Potential.pure_part_potential (n := Fin 1) (Ωt := Unit) (E := ℝ) (Hs := ℝ) 0 0
    (k := 1) (κ₀ := 1) (r := 1) one_pos one_pos zero_le_one {Finset.univ}
    (fun S hS => by
      rw [Finset.mem_singleton] at hS
      subst hS
      simp only [one_pow, one_smul, mul_one, smul_zero, sub_zero]
      exact Matrix.PosSemidef.one.submatrix _)
    pt (fun _ _ => 1) (fun _ => Finset.univ) (fun _ => Finset.mem_singleton_self _)
    (fun _ _ => by norm_num) (fun _ i hi => absurd (Finset.mem_univ i) hi)
    (fun y => by simp) (fun _ => 0) (fun _ _ => 0) (fun _ _ _ => 0) (fun _ => 0)
    (fun x => ⟨rfl, by simp; positivity⟩) (fun _ => 0) (fun _ _ => 0)
    (fun _ _ => by simp) (fun _ _ => by simp) (fun _ => by simp) x

/-- **`lem:joint-potential`: all hypotheses hold for the one-point toy.** -/
theorem toy_joint_potential :
    JointBlockLower pt (matchCov (relDensity pt (fun _ _ => 1) (fun _ => 1)))
      (foldCov pt (relDensity pt (fun _ _ => 1) (fun _ => 1)))
      (Real.exp 0 * ((1 * 1 + 1 * 1 * (0 + 0)) / 1 + cconst 0 0 0 0 + cconst 0 0 0 0)) := by
  refine Potential.joint_potential (E := ℝ) pt pt (fun _ => 1) 0
    (fun _ => by rw [pt_weight, mul_one]) (fun _ _ => by simp)
    (fun _ _ => 1) (fun _ _ => 1) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0) (fun _ _ => 0)
    (fun _ _ => 0) (fun _ _ => 0)
    (fun x _ => (dens1_one x).symm) (fun x _ => (dens2_one x).symm)
    (fun _ _ _ _ => by ring) (fun _ _ _ _ => by ring)
    (by rw [mass_one]; simp) (by norm_num) le_rfl perpBound_zero (formBound_zero 0 le_rfl)
    (formBound_zero 0 le_rfl) (by norm_num) (by rw [cen_kone_one]) (by rw [cen_kone'_one])
    (by rw [mass_one]; simp) (by norm_num) le_rfl perpBound_zero (formBound_zero 0 le_rfl)
    (formBound_zero 0 le_rfl) (by norm_num) (by rw [cen_kone_one]) (by rw [cen_kone'_one])
    (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ _ => 0) (P := 1) (I₀ := 1) (κ₀ := 1)
    (r := 1) (k := 1) (eF := 0) (eE := 0) ?_ (by norm_num) le_rfl (by norm_num) (by norm_num)
    (by norm_num) le_rfl le_rfl (fun _ => by simp) (fun _ => by simp)
    (fun x => toy_pure_part_potential x)
  intro Φ Ψ hΦ hΨ
  refine ⟨by simp [RowsA.stForm, kf], ?_⟩
  rw [nrm_zero_of_centred Φ hΦ, nrm_zero_of_centred Ψ hΨ]
  simp

/-- **A non-degenerate pointwise bound**: `T = 0`, `𝒢 = I`, `𝗄 = 2`, `κ₀ = 1`, `D = diag(1, 0)`. -/
theorem toy_potential_pointwise (x : Fin 2 → ℝ) :
    (fun i => (if i = 0 then (1 : ℝ) else 0) * x i) ⬝ᵥ (((2 : ℝ) • (0 : Matrix (Fin 2) (Fin 2) ℝ) +
      (1 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ)) *ᵥ
      (fun i => (if i = 0 then (1 : ℝ) else 0) * x i)) ≤ 2 ^ 2 * (x ⬝ᵥ x) := by
  refine Potential.potential_pointwise 0 1 one_pos {0} ?_ _ (fun i => by split_ifs <;> norm_num)
    (fun i hi => by
      rw [Finset.mem_singleton] at hi
      simp only [hi, ↓reduceIte]) x
  have : ((2 : ℝ) ^ 2 • (1 : Matrix (Fin 2) (Fin 2) ℝ) -
      ((2 : ℝ) * 1) • (0 : Matrix (Fin 2) (Fin 2) ℝ) -
      (1 : ℝ) ^ 2 • (1 : Matrix (Fin 2) (Fin 2) ℝ)) = (3 : ℝ) • (1 : Matrix (Fin 2) (Fin 2) ℝ) := by
    rw [smul_zero, sub_zero, one_pow, one_smul,
      show (2 : ℝ) ^ 2 • (1 : Matrix (Fin 2) (Fin 2) ℝ) - 1 = ((2 : ℝ) ^ 2 - 1) • 1 by
        rw [sub_smul, one_smul]]
    norm_num
  rw [this]
  exact (Matrix.PosSemidef.one.smul (by norm_num : (0 : ℝ) ≤ 3)).submatrix _

end Sarkozy.JointRows.RowsASanity
