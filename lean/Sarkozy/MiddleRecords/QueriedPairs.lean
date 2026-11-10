module

public import Sarkozy.PartVRecords.MergeRecords

/-!
# The transitivity argument for uniform queried pairs (section 21)

`paper/sections/21_middle_records.tex`. Section 21 uses one argument several times
(`lem:record:e-law`(a); the "Acceptance" paragraph after `def:record:mixture`; `lem:merge-repair`;
`lem:middle-comparison-prices`(a)): *a `𝒢_p`-invariant law is supported on strict-square pairs,
and `𝒢_p` acts transitively on the ordered pairs `(a, a')` with `a → a'`, so the queried pair is
uniform on them.* Here, in general form:

* `invariant_pair_uniform`: a function `π` on `F × F` that is invariant under
  `(u, v) ↦ (αu + β, αv + β)`, `χ(α) = 1`, vanishes off the strict-square pairs and has total
  mass one equals `2/(p(p - 1))` on every strict-square pair (there are `p(p - 1)/2` of them,
  `sum_strict_pairs`); transitivity is the map `α = v - u`, `β = u` from `(0, 1)`.
* `pairLaw μ i j`, the law of the pair of labels `(z_i, z_j)` under a law `μ` of four-label
  configurations, with `pairLaw_affine` (invariance passes to the pair), `pairLaw_mass`,
  `pairLaw_supp`.
* An application, as an independent cross-check by the paper's argument: the designated pair
  `x₀ → y₀` of V3's first-coordinate merge replacement `firstLaw` is uniform on the
  strict-square pairs (`firstLaw_query`). V3 proved this, and the queried pairs of the
  mirror-edge law, by counting (`Sarkozy.PartVRecords.firstLaw_queried`,
  `mirrorLaw_queried10`, `mirrorLaw_queried01`); the half marginals of the mirror-edge law are
  V3's `Sarkozy.PartVRecords.mirrorLaw_half0`, `mirrorLaw_half1`.
-/

@[expose] public section

namespace Sarkozy.MiddleRecords

open Finset Sarkozy.Labellings Sarkozy.PartV Sarkozy.PartVRecords Sarkozy.TraceMixing

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- `χ` as an integer-valued character. -/
local notation "χ" => quadraticChar F

/-- `p = |F|` as a real number. -/
local notation "qF" => (Fintype.card F : ℝ)

/-- **The number of strict-square pairs** `(u, v)`, `u → v`, is `p(p - 1)/2`. -/
theorem sum_strict_pairs (hF : ringChar F ≠ 2) :
    ∑ u : F, ∑ v : F, (if χ (v - u) = 1 then (1 : ℝ) else 0) = qF * (qF - 1) / 2 := by
  simp only [sum_out_indicator hF, sum_const, card_univ, nsmul_eq_mul]
  ring

/-- **Transitivity**: a `𝒢_p`-invariant function of a pair, vanishing off the strict-square pairs
and of total mass one, is `2/(p(p - 1))` on every strict-square pair. -/
theorem invariant_pair_uniform (hF : ringChar F ≠ 2) (π : F → F → ℝ)
    (hinv : ∀ α β u v : F, χ α = 1 → π (α * u + β) (α * v + β) = π u v)
    (hsupp : ∀ u v : F, χ (v - u) ≠ 1 → π u v = 0)
    (hmass : ∑ u, ∑ v, π u v = 1) (u v : F) :
    π u v = if χ (v - u) = 1 then 2 / (qF * (qF - 1)) else 0 := by
  have hconst : ∀ u v : F, χ (v - u) = 1 → π u v = π 0 1 := by
    intro u v huv
    have h := hinv (v - u) u 0 1 huv
    simp only [mul_zero, zero_add, mul_one, sub_add_cancel] at h
    exact h
  have hπ : ∀ u v : F, π u v = π 0 1 * (if χ (v - u) = 1 then 1 else 0) := by
    intro u v
    by_cases h : χ (v - u) = 1
    · rw [hconst u v h, ite_eq_left h, mul_one]
    · rw [hsupp u v h, ite_eq_right h, mul_zero]
  have hm : π 0 1 * (qF * (qF - 1) / 2) = 1 := by
    calc π 0 1 * (qF * (qF - 1) / 2)
        = π 0 1 * ∑ u : F, ∑ v : F, (if χ (v - u) = 1 then (1 : ℝ) else 0) := by
          rw [sum_strict_pairs hF]
      _ = ∑ u, ∑ v, π u v := by
          rw [mul_sum]
          refine sum_congr rfl fun u _ => ?_
          rw [mul_sum]
          exact sum_congr rfl fun v _ => (hπ u v).symm
      _ = 1 := hmass
  have hp1 : (1 : ℝ) < qF := card_gt_one_real
  have h0 : qF ≠ 0 := by intro h; linarith
  have h1 : qF - 1 ≠ 0 := by intro h; linarith
  rw [hπ u v]
  by_cases h : χ (v - u) = 1
  · rw [ite_eq_left h, ite_eq_left h, mul_one]
    field_simp
    linarith
  · rw [ite_eq_right h, ite_eq_right h, mul_zero]

/-! ## The law of a pair of labels -/

/-- The law of the pair `(z_i, z_j)` under a law `μ` of configurations. -/
noncomputable def pairLaw (μ : FiniteLaw (Fin 2 × Fin 2 → F)) (i j : Fin 2 × Fin 2) (u v : F) :
    ℝ :=
  μ.expect fun z => if z i = u ∧ z j = v then 1 else 0

theorem pairLaw_affine (μ : FiniteLaw (Fin 2 × Fin 2 → F))
    (haff : ∀ α : F, χ α = 1 → ∀ (β : F) (H : (Fin 2 × Fin 2 → F) → ℝ),
      μ.expect (fun z => H (fun w => α * z w + β)) = μ.expect H)
    (i j : Fin 2 × Fin 2) (α β u v : F) (hα : χ α = 1) :
    pairLaw μ i j (α * u + β) (α * v + β) = pairLaw μ i j u v := by
  have hα0 : α ≠ 0 := ne_zero_of_quadraticChar_eq_one hα
  unfold pairLaw
  rw [← haff α hα β]
  apply FiniteLaw.expect_congr
  intro z
  simp only [add_left_inj, mul_right_inj' hα0]

omit [Field F] in
theorem pairLaw_mass (μ : FiniteLaw (Fin 2 × Fin 2 → F)) (i j : Fin 2 × Fin 2) :
    ∑ u, ∑ v, pairLaw μ i j u v = 1 := by
  classical
  unfold pairLaw FiniteLaw.expect
  have e : ∀ u v : F, ∑ z, μ.weight z * (if z i = u ∧ z j = v then (1 : ℝ) else 0) =
      ∑ z, (if z i = u then (if z j = v then μ.weight z else 0) else 0) := by
    intro u v
    refine sum_congr rfl fun z _ => ?_
    by_cases h1 : z i = u <;> by_cases h2 : z j = v <;> simp [h1, h2]
  simp only [e]
  rw [sum_comm]
  have e2 : ∀ v : F, ∑ u : F, ∑ z, (if z i = u then (if z j = v then μ.weight z else 0) else 0) =
      ∑ z, (if z j = v then μ.weight z else 0) := by
    intro v
    rw [sum_comm]
    refine sum_congr rfl fun z _ => ?_
    rw [sum_ite_eq]
    simp
  simp only [e2]
  rw [sum_comm]
  have e3 : ∀ z : Fin 2 × Fin 2 → F, ∑ v : F, (if z j = v then μ.weight z else 0) = μ.weight z := by
    intro z
    rw [sum_ite_eq]
    simp
  simp only [e3]
  exact μ.total

theorem pairLaw_supp (μ : FiniteLaw (Fin 2 × Fin 2 → F)) (i j : Fin 2 × Fin 2)
    (hsupp : ∀ z, μ.weight z ≠ 0 → χ (z j - z i) = 1) (u v : F) (huv : χ (v - u) ≠ 1) :
    pairLaw μ i j u v = 0 := by
  unfold pairLaw FiniteLaw.expect
  refine sum_eq_zero fun z _ => ?_
  by_cases hw : μ.weight z = 0
  · rw [hw, zero_mul]
  · have hz := hsupp z hw
    beta_reduce
    rw [ite_eq_right, mul_zero]
    rintro ⟨h1, h2⟩
    rw [h1, h2] at hz
    exact huv hz

/-! ## A cross-check: the first-coordinate merge replacement -/

/-- **The designated pair `x₀ → y₀` of the first-coordinate merge replacement is uniform on the
strict-square pairs** (the queried-pair clause of `lem:merge-repair`, by transitivity; a
cross-check of V3's `Sarkozy.PartVRecords.firstLaw_queried`). -/
theorem firstLaw_query (hF : ringChar F ≠ 2) (u v : F) :
    pairLaw (firstLaw F hF) (0, 0) (0, 1) u v =
      if χ (v - u) = 1 then 2 / (qF * (qF - 1)) else 0 :=
  invariant_pair_uniform hF _
    (fun α β u v hα => pairLaw_affine _ (fun _ hα β H => firstLaw_affine hF hα β H) _ _ α β u v hα)
    (fun u v huv => pairLaw_supp _ _ _ (fun _ hz => (firstLaw_support hF hz).1) u v huv)
    (pairLaw_mass _ _ _) u v

end Sarkozy.MiddleRecords
