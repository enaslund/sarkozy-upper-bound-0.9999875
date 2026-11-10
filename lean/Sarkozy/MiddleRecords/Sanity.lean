module

public import Sarkozy.MiddleRecords.TwoFeature
public import Sarkozy.MiddleRecords.MergePrices
public import Sarkozy.MiddleRecords.EOrthogonalSym

/-!
# Non-vacuity of the new bundles of `Sarkozy.MiddleRecords`

* `TwoFeature` (`lem:two-feature-spectrum`): `toyTwoFeature a` on `H₀ = 𝓗 = ℝ`, with `V = I`,
  `A = a I`, `P = 0` (so `b = 0`, `c = a²`, `q = 0`); every field holds. At `a = 2` the theorem
  `TwoFeature.opNorm_symOp` gives `‖A V^* + V A^*‖ = 4` (`toy_opNorm_symOp`), which agrees with the
  direct computation `A V^* + V A^* = 4 I` (`toy_symOp_apply`).
* `MergeRepairBounds` (`lem:merge-repair`, a hypothesis of `cor:merge-repair`): the tight
  instance `tightSym`, `tightSkew` (each norm equal to its bound) at `b = X = Q₃` is valid
  (`tight_mergeRepairBounds`), and `merge_prices` applies to it (`merge_prices_at_Q3`).
* `OrthProj` (`lem:record:e-orthogonal`(c)): the identity of `ℝ` (`toyOrthProj`) is an orthogonal
  projection, and `proj_sym_step` applies to it with `S = X = 0`, `𝔰 = e = 0` (`toy_proj_sym`).

Field-by-field comparison of `TwoFeature` with the paper: `adjV`, `adjA` say that `Vs`, `As` are
the adjoints `V^*`, `A^*`; `isom` is `V^* V = I` (an isometry); `gramVA` is `V^* A = aI + bP`;
`gramAA` is `A^* A = cI`; `skewP` is `P^* = -P`; `gramP` is `P^* P = qI`. In the paper's
applications (`lem:old-f-law`(b)(i), `lem:mirror`(c), `lem:old-f-law`(f)) all of these hold with
`q = 1/p > 0` and `P ≠ 0`, `H₀` the mean-zero functions on `𝔽_p`.
-/

@[expose] public section

open scoped InnerProductSpace

namespace Sarkozy.MiddleRecords

/-- **A toy `TwoFeature`** on `ℝ`: `V = I`, `A = a I`, `P = 0`. -/
noncomputable def toyTwoFeature (a : ℝ) : TwoFeature ℝ ℝ where
  V := LinearMap.id
  Vs := LinearMap.id
  A := a • LinearMap.id
  As := a • LinearMap.id
  P := 0
  a := a
  b := 0
  c := a ^ 2
  q := 0
  adjV _ _ := rfl
  adjA x w := by
    simp only [LinearMap.smul_apply, LinearMap.id_apply, real_inner_smul_left,
      real_inner_smul_right]
  isom _ := rfl
  gramVA x := by simp
  gramAA x := by
    simp only [LinearMap.smul_apply, LinearMap.id_apply, smul_smul, sq]
  skewP x y := by simp
  gramP x y := by simp

theorem toy_symOp_apply (x : ℝ) : (toyTwoFeature 2).symOp x = 4 * x := by
  simp only [TwoFeature.symOp_apply, toyTwoFeature, LinearMap.smul_apply, LinearMap.id_apply,
    smul_eq_mul]
  ring

/-- **The theorem's value agrees with the direct computation**: `‖4 I‖ = 4`. -/
theorem toy_opNorm_symOp :
    ‖LinearMap.toContinuousLinearMap (toyTwoFeature 2).symOp‖ = 4 := by
  rw [TwoFeature.opNorm_symOp]
  simp only [toyTwoFeature]
  rw [show (2 : ℝ) ^ 2 - 0 ^ 2 * 0 = 2 ^ 2 by ring, Real.sqrt_sq (by norm_num)]
  norm_num

/-- The tight symmetric norms: each equal to its bound in `lem:merge-repair`. -/
noncomputable def tightSym (b : ℝ) : Fin 2 × Fin 3 → ℝ := fun i =>
  if i.2 = 2 then dG b + etaG b else sG b

/-- The tight skew norms. -/
noncomputable def tightSkew (b : ℝ) : Fin 2 × Fin 3 → ℝ := fun i =>
  if i.2 = 2 then gammaG b else aG b

/-- **`MergeRepairBounds` is satisfiable**: the tight norms at `b = Q₃ = 19951586`. -/
theorem tight_mergeRepairBounds :
    MergeRepairBounds 19951586 (tightSym 19951586) (tightSkew 19951586) where
  sym_nonneg i := by
    unfold tightSym dG etaG sG
    split_ifs <;> positivity
  skew_nonneg i := by
    unfold tightSkew gammaG aG
    have h1 : 0 < 1 - 2 / (19951586 : ℝ) := by norm_num
    have h2 : 0 < 1 - 3 / (19951586 : ℝ) := by norm_num
    have hs : 0 < Real.sqrt 19951586 := Real.sqrt_pos.mpr (by norm_num)
    have h4 : 0 < 4 - 6 / (19951586 : ℝ) := by norm_num
    split_ifs
    · positivity
    · positivity
  sym_mirror s k hk := by
    unfold tightSym; simp only [hk, ↓reduceIte, le_refl]
  skew_mirror s k hk := by
    unfold tightSkew; simp only [hk, ↓reduceIte, le_refl]
  sym_first s := by unfold tightSym; simp
  skew_first s := by unfold tightSkew; simp

/-- **`cor:merge-repair` applies** to the tight instance at the first piece start `X = Q₃`. -/
theorem merge_prices_at_Q3 :
    ∑ i, (1 : ℝ) * (1 / Real.sqrt 19951586) ^ 2 / 1 * tightSym 19951586 i * 1 ≤
        1 * gS (1 / ((19951586 : ℕ) : ℝ)) * (1 / Real.sqrt 19951586) ^ 4 * 1 ∧
      ∑ i, (1 : ℝ) * (1 / Real.sqrt 19951586) ^ 2 / 1 * tightSkew 19951586 i * 1 ≤
        1 * gA (1 / ((19951586 : ℕ) : ℝ)) (rXof 19951586) * (1 / Real.sqrt 19951586) ^ 3 * 1 :=
  merge_prices (X := 19951586) (by norm_num) (by norm_num) (by norm_num) le_rfl (by norm_num)
    tight_mergeRepairBounds

/-- **A toy `OrthProj`**: the identity of `ℝ`. -/
noncomputable def toyOrthProj : OrthProj ℝ where
  H := LinearMap.id
  idem _ := rfl
  symm _ _ := rfl

/-- `proj_sym_step` applies to the toy projection. -/
theorem toy_proj_sym (x : ℝ) :
    ‖(0 : ℝ →ₗ[ℝ] ℝ) x + (1 : ℝ)⁻¹ • (0 : ℝ →ₗ[ℝ] ℝ) x‖ ≤ (0 + 2 * 0 / 1) * ‖x‖ :=
  proj_sym_step toyOrthProj 0 0 one_pos (fun _ => by simp) (fun _ _ => by simp)
    (fun _ => by simp) (fun _ => by simp) (fun _ => by simp) x

end Sarkozy.MiddleRecords
