module

public import Sarkozy.PartVLaws.ExactMarginals

@[expose] public section

/-!
# The fold kernel of a row datum as ratios of marginals

`paper/sections/17_completion_repair.tex`, the remark after `def:five-type-datum`: "The fold
kernel `T_F^b` contains the density of the middle law of `π_F` relative to `ν` and those of its
conditional outer marginals relative to `ν^b`"; `paper/sections/25_upper_reference.tex`,
`def:record:upper-bands`, items (F1), (F3), (F5) (the marginal ratios `ℓ_mar`, `ℓ_mid`, and
`H = exp(n̄ ℓ_mid)`, `R_m = exp(n̄ ℓ_mar)` of the Schur rows).

For the datum `datumOfGam π_E π_F π_L` (every row datum of the upper and tail laws), at a middle
value `b` with `ν(b) > 0`:
* **`kf_fold_one`**: the mass of the fold kernel is the ratio of the middle laws,
  `m_b = ⟨𝟙, T_F^b 𝟙⟩ = π_F(ω₁ = b) / π_E(ω₁ = b)`;
* **`kone_fold`**: `T_F^b 𝟙 (x) = Γ_F(x, b) / Γ_E(x, b)`, the ratio of the laws of the objects
  `(0, 1)` (on the support of `ν^b`);
* **`kone'_fold`**: `(T_F^b)^* 𝟙 (y) = π_F(ω₂ = y, ω₁ = b) / Γ_E(y, b)`.

So the count-type fields of the Schur-row data (`SchurRowData`: the mass bounds `[H⁻¹, H]`, the
marginal densities `≤ R_m` and their distance `υ` to `𝟙`) are bounds on ratios of marginals of
the `F` and `E` laws: for the paper's laws, ratios of extension counts (`lem:graphs:sequential`(b)).
`foldMass_bounds_iff` and `margL_eq`, `margR_eq` state this for the row data. The other fields,
the correlations `ρ_F`, `ρ_E` (F4), are spectral.
-/

namespace Sarkozy.PartVLaws

open Finset Sarkozy.FiveType Sarkozy.PartV Sarkozy.FiveType.TwoCoord

variable {𝔛 : Type*} [Fintype 𝔛] [DecidableEq 𝔛]

/-- The configurations with middle object `b` are the `![x, b, y]`. -/
theorem sum_fiber_one (f : (Fin 3 → 𝔛) → ℝ) (b : 𝔛) :
    ∑ ω ∈ univ.filter (fun ω : Fin 3 → 𝔛 => ω 1 = b), f ω = ∑ x, ∑ y, f ![x, b, y] := by
  rw [← Fintype.sum_prod_type' (fun x y => f ![x, b, y])]
  have himg : (univ.filter fun ω : Fin 3 → 𝔛 => ω 1 = b) =
      (univ : Finset (𝔛 × 𝔛)).image fun p => ![p.1, b, p.2] := by
    ext ω
    simp only [mem_filter, mem_univ, true_and, mem_image]
    constructor
    · intro h
      refine ⟨(ω 0, ω 2), ?_⟩
      funext i
      fin_cases i
      · rfl
      · simp [h]
      · rfl
    · rintro ⟨p, rfl⟩
      rfl
  rw [himg, sum_image]
  intro p _ p' _ h
  have h0 := congrFun h 0
  have h2 := congrFun h 2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_cons] at h0 h2
  exact Prod.ext h0 h2

theorem nub_ne_zero_of_charged (piE piF : FiniteLaw (Fin 3 → 𝔛)) (hS : GamSupported piE piF)
    {x b y : 𝔛} (h : piF.weight ![x, b, y] ≠ 0) :
    (nubOf piE b).weight x ≠ 0 ∧ (nubOf piE b).weight y ≠ 0 := by
  obtain ⟨h01, h21⟩ := hS _ h
  have e1 := gamOf_weight piE ![x, b]
  have e2 := gamOf_weight piE ![y, b]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.tail_cons,
    Matrix.head_cons] at h01 h21 e1 e2
  rw [e1] at h01
  rw [e2] at h21
  exact ⟨right_ne_zero_of_mul h01, right_ne_zero_of_mul h21⟩

/-- One term of the fold kernel against `ν^b ⊗ ν^b`. -/
theorem fold_term (piE piF : FiniteLaw (Fin 3 → 𝔛)) (hS : GamSupported piE piF) {b : 𝔛}
    (hb : (nuOf piE).weight b ≠ 0) (x y : 𝔛) :
    (nubOf piE b).weight x * (nubOf piE b).weight y * kernelOf piE piF b x y =
      piF.weight ![x, b, y] / (nuOf piE).weight b := by
  unfold kernelOf
  split_ifs with hden
  · have hπ : piF.weight ![x, b, y] = 0 := by
      by_contra hne
      obtain ⟨hx, hy⟩ := nub_ne_zero_of_charged piE piF hS hne
      exact (mul_ne_zero (mul_ne_zero hb hx) hy) hden
    rw [hπ, mul_zero, zero_div]
  · have hx : (nubOf piE b).weight x ≠ 0 := right_ne_zero_of_mul (left_ne_zero_of_mul hden)
    have hy : (nubOf piE b).weight y ≠ 0 := right_ne_zero_of_mul hden
    field_simp

/-- **The mass of the fold kernel is the ratio of the middle laws**:
`⟨𝟙, T_F^b 𝟙⟩ = π_F(ω₁ = b) / π_E(ω₁ = b)`. -/
theorem kf_fold_one (piE piF : FiniteLaw (Fin 3 → 𝔛)) (hS : GamSupported piE piF) {b : 𝔛}
    (hb : (nuOf piE).weight b ≠ 0) :
    kf (nubOf piE b) (kernelOf piE piF b) (fun _ => 1) (fun _ => 1) =
      (piF.map fun ω => ω 1).weight b / (nuOf piE).weight b := by
  unfold kf
  have hterm : ∀ x y, (nubOf piE b).weight x * (nubOf piE b).weight y *
      (1 * kernelOf piE piF b x y * 1) = piF.weight ![x, b, y] / (nuOf piE).weight b := by
    intro x y
    rw [one_mul, mul_one]
    exact fold_term piE piF hS hb x y
  simp_rw [hterm]
  rw [map_weight_eq, sum_fiber_one, sum_div]
  exact sum_congr rfl fun x _ => (sum_div _ _ _).symm

/-- **The row sums of the fold kernel are ratios of the laws of the objects `(0, 1)`**:
`T_F^b 𝟙 (x) = Γ_F(x, b) / Γ_E(x, b)` on the support of `ν^b`. -/
theorem kone_fold (piE piF : FiniteLaw (Fin 3 → 𝔛)) (hS : GamSupported piE piF) {b : 𝔛}
    (hb : (nuOf piE).weight b ≠ 0) {x : 𝔛} (hx : (nubOf piE b).weight x ≠ 0) :
    kone (nubOf piE b) (kernelOf piE piF b) x =
      (gamOf piF).weight ![x, b] / (gamOf piE).weight ![x, b] := by
  unfold kone
  have hterm : ∀ y, (nubOf piE b).weight y * kernelOf piE piF b x y =
      piF.weight ![x, b, y] / ((nuOf piE).weight b * (nubOf piE b).weight x) := by
    intro y
    have h := fold_term piE piF hS hb x y
    rw [mul_comm ((nubOf piE b).weight x), mul_assoc] at h
    rw [eq_div_iff (mul_ne_zero hb hx)]
    rw [eq_div_iff hb] at h
    rw [← h]
    ring
  simp_rw [hterm]
  rw [← sum_div, ← gamOf_weight_eq_sum]
  congr 1
  have e := gamOf_weight piE ![x, b]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at e
  exact e.symm

/-- **The column sums of the fold kernel**: `(T_F^b)^* 𝟙 (y) = π_F(ω₂ = y, ω₁ = b) / Γ_E(y, b)` on
the support of `ν^b`. -/
theorem kone'_fold (piE piF : FiniteLaw (Fin 3 → 𝔛)) (hS : GamSupported piE piF) {b : 𝔛}
    (hb : (nuOf piE).weight b ≠ 0) {y : 𝔛} (hy : (nubOf piE b).weight y ≠ 0) :
    kone' (nubOf piE b) (kernelOf piE piF b) y =
      (∑ x, piF.weight ![x, b, y]) / (gamOf piE).weight ![y, b] := by
  unfold kone'
  have hterm : ∀ x, (nubOf piE b).weight x * kernelOf piE piF b x y =
      piF.weight ![x, b, y] / ((nuOf piE).weight b * (nubOf piE b).weight y) := by
    intro x
    have h := fold_term piE piF hS hb x y
    rw [mul_assoc] at h
    rw [eq_div_iff (mul_ne_zero hb hy)]
    rw [eq_div_iff hb] at h
    rw [← h]
    ring
  simp_rw [hterm]
  rw [← sum_div]
  congr 1
  have e := gamOf_weight piE ![y, b]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at e
  exact e.symm

/-! ## For the row data -/

section Rows

variable {X : Type} [Fintype X] [DecidableEq X] {Λ : Type} [Fintype Λ] [DecidableEq Λ]

/-- **The mass bounds of the fold data of a row datum** (`FoldData`, `SchurRowData`) are bounds on
the ratio of the middle laws of the `F` and `E` rows. -/
theorem rowD0_foldMass (lam : (f0 f1 : FieldTy) → FiniteLaw (f0.Obj × f1.Obj × Λ → X))
    (f' : FieldTy) (h : RowHyp0 lam f') (b : f'.Obj × Λ → X)
    (hb : (rowD0 lam f' h).nu.weight b ≠ 0) :
    kf ((rowD0 lam f' h).nub b) ((rowD0 lam f' h).TF b) (fun _ => 1) (fun _ => 1) =
      (((lam .F f').map fun y => (rows0 y : Fin 3 → f'.Obj × Λ → X)).map fun ω => ω 1).weight b /
        (rowD0 lam f' h).nu.weight b :=
  kf_fold_one _ _ h.supp hb

/-- The same for the coordinate `1`. -/
theorem rowD1_foldMass (lam : (f0 f1 : FieldTy) → FiniteLaw (f0.Obj × f1.Obj × Λ → X))
    (f' : FieldTy) (h : RowHyp1 lam f') (b : f'.Obj × Λ → X)
    (hb : (rowD1 lam f' h).nu.weight b ≠ 0) :
    kf ((rowD1 lam f' h).nub b) ((rowD1 lam f' h).TF b) (fun _ => 1) (fun _ => 1) =
      (((lam f' .F).map fun y => (rows1 y : Fin 3 → f'.Obj × Λ → X)).map fun ω => ω 1).weight b /
        (rowD1 lam f' h).nu.weight b :=
  kf_fold_one _ _ h.supp hb

/-- **The left marginal density of the fold kernel of a row datum**: `φ₀ = T_F^b 𝟙 / m_b` is the
ratio `Γ_F(x, b)/Γ_E(x, b)` divided by the middle ratio (`rem:five-type-fold-data`). -/
theorem rowD0_margL (lam : (f0 f1 : FieldTy) → FiniteLaw (f0.Obj × f1.Obj × Λ → X))
    (f' : FieldTy) (h : RowHyp0 lam f') (b : f'.Obj × Λ → X)
    (hb : (rowD0 lam f' h).nu.weight b ≠ 0) (x : f'.Obj × Λ → X)
    (hx : ((rowD0 lam f' h).nub b).weight x ≠ 0) :
    margL ((rowD0 lam f' h).nub b) ((rowD0 lam f' h).TF b) x =
      ((gamOf ((lam .F f').map fun y => (rows0 y : Fin 3 → f'.Obj × Λ → X))).weight ![x, b] /
          (rowD0 lam f' h).Gam.weight ![x, b]) /
        ((((lam .F f').map fun y => (rows0 y : Fin 3 → f'.Obj × Λ → X)).map fun ω => ω 1).weight b /
          (rowD0 lam f' h).nu.weight b) := by
  unfold margL
  exact congrArg₂ (· / ·) (kone_fold _ _ h.supp hb hx) (kf_fold_one _ _ h.supp hb)

/-- **The right marginal density of the fold kernel of a row datum.** -/
theorem rowD0_margR (lam : (f0 f1 : FieldTy) → FiniteLaw (f0.Obj × f1.Obj × Λ → X))
    (f' : FieldTy) (h : RowHyp0 lam f') (b : f'.Obj × Λ → X)
    (hb : (rowD0 lam f' h).nu.weight b ≠ 0) (y : f'.Obj × Λ → X)
    (hy : ((rowD0 lam f' h).nub b).weight y ≠ 0) :
    margR ((rowD0 lam f' h).nub b) ((rowD0 lam f' h).TF b) y =
      ((∑ x, ((lam .F f').map fun z => (rows0 z : Fin 3 → f'.Obj × Λ → X)).weight ![x, b, y]) /
          (rowD0 lam f' h).Gam.weight ![y, b]) /
        ((((lam .F f').map fun z => (rows0 z : Fin 3 → f'.Obj × Λ → X)).map fun ω => ω 1).weight b /
          (rowD0 lam f' h).nu.weight b) := by
  unfold margR
  exact congrArg₂ (· / ·) (kone'_fold _ _ h.supp hb hy) (kf_fold_one _ _ h.supp hb)

end Rows

end Sarkozy.PartVLaws
