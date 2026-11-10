module

public import Sarkozy.BlockAdapter.Final

@[expose] public section

/-!
# The fold layer caps F21 from per-prime certificates (`lem:old-f-law`(e))

`paper/sections/21_middle_records.tex`, `lem:old-f-law`(a) (the density `g₀ = dm₀/dν_F`,
`‖g₀‖_∞ ≤ 1 + e₀`), (e) (the block bound at the cap `k_D(X, L) = H̄_X [1 + (e_o(X) - 1) r_X]`,
`H̄_X = (1 - n_X e_X)⁻¹`) and (f) (`T_old ⪰ -[1 + (e_o - 1) r] r` on `L²(m₀)`);
`20c_middle_frame.tex`, `lem:front12:reference`(ii), the fold case.

B6 kept the fold caps `FoldLayerCaps` (cut F21, the type `D`) as a block-level hypothesis of
`MiddleUniformBlockInputs` and `MiddleIndividualBlockInputs`, because `k_D` is not of B6's block-cap
form `g e^{BL/(X log X)}`: the paper's proof of (e) tensorizes the *Markov* operator `T_old` of the
cut kernel on the *actual* half marginal `m₀` (upper bound exactly `1`, no inflation), and then
changes the measure from `m₀` to `ν_F` at the price `H̄_X`. That proof is formalized here.

For spectral data `D` and a prime, with `μ = λ(G⁺)` the half law and `K = cutK/Z` the normalized cut
kernel (for F21 the paper's `K₀`, `lem:old-f-law`; its half law is `ν_F` by
`lem:layer12-geometry`(c)):
* `actDens D hne x = E_μ K(x, ·)` (the paper's `g₀`), `actLaw` (`m₀ = g₀ μ`, a probability law
  since `Z = E_{μ⊗μ} K`), `actKernel` (`K/(g₀ ⊗ g₀)`, the kernel of `T_old` relative to
  `m₀ ⊗ m₀`); `act_weight_mul`: `m₀(x) m₀(y) T(x, y) = μ(x) μ(y) K(x, y)`;
* `actForm_le`: `T_old ⪯ 1` on `L²(m₀)` (Schur test; `K ≥ 0` is symmetric with row sums `g₀`);
* **`act_block_lower`**: on a block, per-prime `T_old ⪰ -g p^{-1/2}` on `L²(m₀)` and
  `g₀ ≤ 1 + e` give `⟨Φ, (⊗ K_p) Φ⟩_{⊗μ} ≥ -(g/(1 - n e)) b^{-1/2} ‖Φ‖²_{⊗μ}` for `|𝔅| ≤ n`,
  `n e < 1` (`lem:spec:tensorcomp`(b) via `tensorcomp_block_supp` with `B = 0`, then
  `(1 + e)^n ≤ (1 - n e)⁻¹`);
* **`layerCap_of_actCaps`**: the reserved-cut statement for any swap-invariant two-layer graph;
* `FoldCutCap g p`, `FoldDensity e p` (the per-prime inputs (f) and (a) for F21),
  `MiddleFoldCert i` (constants `(g, e, n)` of piece `i` with `570 < (n + 1) log X_i`,
  `g X_i^{-1/2} < 1`, `g/(1 - n e) ≤ k_D(i)` and the per-prime inputs at every class-three prime
  of the piece);
* **`foldLayerCaps_of_cert`**: B6's `FoldLayerCaps` at the recorded `k_D` from `MiddleFoldCert`.
-/

open scoped InnerProductSpace
open Finset

namespace Sarkozy.BlockInputs

open Sarkozy Sarkozy.Labellings Sarkozy.PartV Sarkozy.FiveType Sarkozy.Cuts Sarkozy.BlockSpecPaper
  Sarkozy.BlockSpecPaper.AllpData Sarkozy.BlockAdapter

/-! ## The actual half marginal and the Markov kernel at one prime -/

section Actual

variable {U : Type} [Fintype U] [DecidableEq U] (D : SpecData U) {F : Type} [Field F]
  [Fintype F] [DecidableEq F] (hne : (injLabellings F D.G).Nonempty)

/-- The density `g₀(x) = E_{y∼μ} K(x, y)` of the actual half marginal of the normalized cut kernel
relative to the half law. -/
noncomputable def actDens (x : D.cut.Half → F) : ℝ :=
  ∑ y, (D.halfLaw hne).weight y * (D.cutK x y / D.cutZ hne)

theorem actDens_nonneg (x : D.cut.Half → F) : 0 ≤ actDens D hne x :=
  Finset.sum_nonneg fun y _ => mul_nonneg ((D.halfLaw hne).nonneg y)
    (div_nonneg (D.cutK_nonneg x y) (D.cutZ_pos hne).le)

theorem sum_actDens : ∑ x, (D.halfLaw hne).weight x * actDens D hne x = 1 := by
  have hZ := D.cutZ_pos hne
  have h1 : ∀ x, (D.halfLaw hne).weight x * actDens D hne x =
      ((D.halfLaw hne).weight x * ∑ y, (D.halfLaw hne).weight y * D.cutK x y) / D.cutZ hne := by
    intro x
    unfold actDens
    rw [Finset.mul_sum, Finset.mul_sum, Finset.sum_div]
    exact Finset.sum_congr rfl fun y _ => by ring
  have h2 : ∑ x, (D.halfLaw hne).weight x * ∑ y, (D.halfLaw hne).weight y * D.cutK x y =
      D.cutZ hne := by
    unfold SpecData.cutZ
    rw [FiniteLaw.expect_product]
    rfl
  rw [Finset.sum_congr rfl fun x _ => h1 x, ← Finset.sum_div, h2, div_self hZ.ne']

/-- **The actual half marginal** `m₀ = g₀ μ`. -/
noncomputable def actLaw : FiniteLaw (D.cut.Half → F) where
  weight x := (D.halfLaw hne).weight x * actDens D hne x
  nonneg x := mul_nonneg ((D.halfLaw hne).nonneg x) (actDens_nonneg D hne x)
  total := sum_actDens D hne

/-- **The kernel of `T_old` relative to `m₀ ⊗ m₀`**: `K(x, y)/(g₀(x) g₀(y))` (`0` where a density
vanishes). -/
noncomputable def actKernel (x y : D.cut.Half → F) : ℝ :=
  if actDens D hne x = 0 ∨ actDens D hne y = 0 then 0
  else D.cutK x y / D.cutZ hne / (actDens D hne x * actDens D hne y)

theorem actKernel_symm (x y : D.cut.Half → F) : actKernel D hne x y = actKernel D hne y x := by
  unfold actKernel
  by_cases hx : actDens D hne x = 0 <;> by_cases hy : actDens D hne y = 0 <;>
    simp [hx, hy, D.cutK_symm x y, mul_comm]

/-- A vanishing density kills its row: `g₀(x) = 0` forces `μ(y) K(x, y) = 0` for all `y`. -/
theorem row_zero {x : D.cut.Half → F} (hx : actDens D hne x = 0) (y : D.cut.Half → F) :
    (D.halfLaw hne).weight y * (D.cutK x y / D.cutZ hne) = 0 := by
  have hnn : ∀ y ∈ (univ : Finset (D.cut.Half → F)),
      0 ≤ (D.halfLaw hne).weight y * (D.cutK x y / D.cutZ hne) := fun y _ =>
    mul_nonneg ((D.halfLaw hne).nonneg y) (div_nonneg (D.cutK_nonneg x y) (D.cutZ_pos hne).le)
  exact (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hx y (mem_univ y)

/-- **`m₀(x) m₀(y) T(x, y) = μ(x) μ(y) K(x, y)`** pointwise. -/
theorem act_weight_mul (x y : D.cut.Half → F) :
    (actLaw D hne).weight x * (actLaw D hne).weight y * actKernel D hne x y =
      (D.halfLaw hne).weight x * (D.halfLaw hne).weight y * (D.cutK x y / D.cutZ hne) := by
  change (D.halfLaw hne).weight x * actDens D hne x *
      ((D.halfLaw hne).weight y * actDens D hne y) * actKernel D hne x y = _
  by_cases hx : actDens D hne x = 0
  · have h := row_zero D hne hx y
    simp only [actKernel, hx, true_or, ↓reduceIte, mul_zero]
    linear_combination -(D.halfLaw hne).weight x * h
  · by_cases hy : actDens D hne y = 0
    · have h := row_zero D hne hy x
      rw [D.cutK_symm] at h
      simp only [actKernel, hy, or_true, ↓reduceIte, mul_zero]
      linear_combination -(D.halfLaw hne).weight y * h
    · simp only [actKernel, hx, hy, or_self, ↓reduceIte]
      field_simp

/-- The forms agree: `⟨f, T h⟩_{m₀} = ⟨f, K h⟩_μ`. -/
theorem actForm_eq (f h : (D.cut.Half → F) → ℝ) :
    kernelForm (actLaw D hne) (actLaw D hne) (actKernel D hne) f h =
      kernelForm (D.halfLaw hne) (D.halfLaw hne) (fun x y => D.cutK x y / D.cutZ hne) f h := by
  simp only [kernelForm, LinearMap.mk₂_apply]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  have := act_weight_mul D hne x y
  linear_combination f x * h y * this

/-- `‖f‖²_{m₀} = E_μ[g₀ f²]`. -/
theorem nrm_act_sq (f : (D.cut.Half → F) → ℝ) :
    Recentering.nrm (actLaw D hne) f ^ 2 =
      ∑ x, (D.halfLaw hne).weight x * actDens D hne x * (f x * f x) := by
  unfold Recentering.nrm Recentering.ip
  rw [Real.sq_sqrt ((actLaw D hne).expect_nonneg fun x => mul_self_nonneg _)]
  rfl

/-- **`T_old ⪯ 1` on `L²(m₀)`** (the Schur test: `K ≥ 0` is symmetric with row sums `g₀`). -/
theorem actForm_le (f : (D.cut.Half → F) → ℝ) :
    kernelForm (actLaw D hne) (actLaw D hne) (actKernel D hne) f f ≤
      (1 + 0 / 1) * Recentering.nrm (actLaw D hne) f ^ 2 := by
  rw [actForm_eq, nrm_act_sq, zero_div, add_zero, one_mul]
  set μ := D.halfLaw hne
  set K : (D.cut.Half → F) → (D.cut.Half → F) → ℝ := fun x y => D.cutK x y / D.cutZ hne
  have hK0 : ∀ x y, 0 ≤ K x y := fun x y => div_nonneg (D.cutK_nonneg x y) (D.cutZ_pos hne).le
  have hKs : ∀ x y, K x y = K y x := fun x y => by simp only [K, D.cutK_symm x y]
  simp only [kernelForm, LinearMap.mk₂_apply]
  have hterm : ∀ x y, μ.weight x * μ.weight y * f x * K x y * f y ≤
      (μ.weight x * μ.weight y * K x y * (f x * f x) +
        μ.weight y * μ.weight x * K y x * (f y * f y)) / 2 := by
    intro x y
    have hw : 0 ≤ μ.weight x * μ.weight y * K x y :=
      mul_nonneg (mul_nonneg (μ.nonneg x) (μ.nonneg y)) (hK0 x y)
    rw [hKs y x]
    nlinarith [mul_nonneg hw (sq_nonneg (f x - f y))]
  calc ∑ x, ∑ y, μ.weight x * μ.weight y * f x * K x y * f y
      ≤ ∑ x, ∑ y, (μ.weight x * μ.weight y * K x y * (f x * f x) +
          μ.weight y * μ.weight x * K y x * (f y * f y)) / 2 :=
        Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun y _ => hterm x y
    _ = ∑ x, μ.weight x * actDens D hne x * (f x * f x) := by
        simp only [← Finset.sum_div, Finset.sum_add_distrib]
        rw [Finset.sum_comm (f := fun x y => μ.weight y * μ.weight x * K y x * (f y * f y))]
        have h : ∑ x, ∑ y, μ.weight x * μ.weight y * K x y * (f x * f x) =
            ∑ x, μ.weight x * actDens D hne x * (f x * f x) := by
          refine Finset.sum_congr rfl fun x _ => ?_
          unfold actDens
          rw [Finset.mul_sum, Finset.sum_mul]
          exact Finset.sum_congr rfl fun y _ => by simp only [K]; ring
        rw [h]
        ring

end Actual

/-! ## The block bound -/

/-- `(1 + e)^m (1 - n e) ≤ 1` for `m ≤ n`, `0 ≤ e`, `n e < 1`. -/
theorem one_add_pow_mul_le {e : ℝ} {m n : ℕ} (he : 0 ≤ e) (hmn : m ≤ n) (hne : (n : ℝ) * e < 1) :
    (1 + e) ^ m * (1 - n * e) ≤ 1 := by
  have h1 : (1 + e) ^ m ≤ (1 + e) ^ n := pow_le_pow_right₀ (by linarith) hmn
  have h2 : (1 + e) ^ n ≤ Real.exp (n * e) := by
    rw [Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp e]) n
  have h3 : Real.exp (n * e) * (1 - n * e) ≤ 1 := by
    have h4 : 1 - (n : ℝ) * e ≤ Real.exp (-(n * e)) := by linarith [Real.add_one_le_exp (-(n * e))]
    have h5 : 0 < Real.exp ((n : ℝ) * e) := Real.exp_pos _
    calc Real.exp (n * e) * (1 - n * e) ≤ Real.exp (n * e) * Real.exp (-(n * e)) :=
          mul_le_mul_of_nonneg_left h4 h5.le
      _ = 1 := by rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
  have hpos : 0 ≤ 1 - (n : ℝ) * e := by linarith
  calc (1 + e) ^ m * (1 - n * e) ≤ Real.exp (n * e) * (1 - n * e) :=
        mul_le_mul_of_nonneg_right (h1.trans h2) hpos
    _ ≤ 1 := h3

section Block

variable {U : Type} [Fintype U] [DecidableEq U] (D : SpecData U) {ι : Type} [Fintype ι]
  [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]
  (hL : ∀ i, (injLabellings (ZMod (pr i)) D.G).Nonempty)

/-- **The block bound of `lem:old-f-law`(e)**: per-prime `T_old ⪰ -g p^{-1/2}` on `L²(m₀)` and
`g₀ ≤ 1 + e` on the support give, on a block with `|𝔅| ≤ n`, `n e < 1` and least prime at least
`b`, `⟨Φ, (⊗_p K_p) Φ⟩_{⊗ μ_p} ≥ -(g/(1 - n e)) b^{-1/2} E_{⊗ μ_p} Φ²`. -/
theorem act_block_lower {g e b : ℝ} {n : ℕ} (hg : 0 ≤ g) (he : 0 ≤ e) (hb0 : 0 < b)
    (hbp : ∀ i, b ≤ pr i) (hcard : Fintype.card ι ≤ n) (hne1 : (n : ℝ) * e < 1)
    (hgp : ∀ i, g * (√(pr i : ℝ))⁻¹ < 1)
    (hlow : ∀ i (f : (D.cut.Half → ZMod (pr i)) → ℝ),
      -(g * (√(pr i : ℝ))⁻¹) * Recentering.nrm (actLaw D (hL i)) f ^ 2 ≤
        kernelForm (actLaw D (hL i)) (actLaw D (hL i)) (actKernel D (hL i)) f f)
    (hdens : ∀ i x, (D.halfLaw (hL i)).weight x ≠ 0 → actDens D (hL i) x ≤ 1 + e)
    (Φ : (∀ i, D.cut.Half → ZMod (pr i)) → ℝ) :
    -(g / (1 - n * e) * (√b)⁻¹) * (FiniteLaw.pi fun i => D.halfLaw (hL i)).expect
        (fun ξ => Φ ξ * Φ ξ) ≤
      kernelForm (FiniteLaw.pi fun i => D.halfLaw (hL i)) (FiniteLaw.pi fun i => D.halfLaw (hL i))
        (fun x y => ∏ i, D.cutK (x i) (y i) / D.cutZ (hL i)) Φ Φ := by
  have hpr0 : ∀ i, (0 : ℝ) < pr i := fun i => lt_of_lt_of_le hb0 (hbp i)
  -- tensorization on `L²(⊗ m₀)` with `B = 0`
  have h := Spectral.tensorcomp_block_supp (fun i => actLaw D (hL i)) (fun i => actKernel D (hL i))
    (fun i x y => actKernel_symm D (hL i) x y) (fun i => (pr i : ℝ)) hg le_rfl hb0 hbp hgp hlow
    (fun i f => by
      have := actForm_le D (hL i) f
      rw [zero_div, add_zero] at this ⊢
      exact this) Φ
  simp only [zero_div, add_zero, Finset.prod_const_one, mul_one] at h
  -- the block forms agree
  have hform : kernelForm (FiniteLaw.pi fun i => actLaw D (hL i))
      (FiniteLaw.pi fun i => actLaw D (hL i)) (fun x y => ∏ i, actKernel D (hL i) (x i) (y i))
      Φ Φ = kernelForm (FiniteLaw.pi fun i => D.halfLaw (hL i))
        (FiniteLaw.pi fun i => D.halfLaw (hL i))
        (fun x y => ∏ i, D.cutK (x i) (y i) / D.cutZ (hL i)) Φ Φ := by
    simp only [kernelForm, LinearMap.mk₂_apply]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
    have hw : (FiniteLaw.pi fun i => actLaw D (hL i)).weight x *
        (FiniteLaw.pi fun i => actLaw D (hL i)).weight y *
          ∏ i, actKernel D (hL i) (x i) (y i) =
        (FiniteLaw.pi fun i => D.halfLaw (hL i)).weight x *
          (FiniteLaw.pi fun i => D.halfLaw (hL i)).weight y *
            ∏ i, D.cutK (x i) (y i) / D.cutZ (hL i) := by
      change (∏ i, (actLaw D (hL i)).weight (x i)) * (∏ i, (actLaw D (hL i)).weight (y i)) *
          ∏ i, actKernel D (hL i) (x i) (y i) =
        (∏ i, (D.halfLaw (hL i)).weight (x i)) * (∏ i, (D.halfLaw (hL i)).weight (y i)) *
          ∏ i, D.cutK (x i) (y i) / D.cutZ (hL i)
      rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib,
        ← Finset.prod_mul_distrib]
      exact Finset.prod_congr rfl fun i _ => act_weight_mul D (hL i) (x i) (y i)
    linear_combination Φ x * Φ y * hw
  -- the change of measure `m₀ → μ`
  have hH : Recentering.nrm (FiniteLaw.pi fun i => actLaw D (hL i)) Φ ^ 2 ≤
      (1 - n * e)⁻¹ * (FiniteLaw.pi fun i => D.halfLaw (hL i)).expect (fun ξ => Φ ξ * Φ ξ) := by
    have hpos : 0 < 1 - (n : ℝ) * e := by linarith
    unfold Recentering.nrm Recentering.ip
    rw [Real.sq_sqrt ((FiniteLaw.pi fun i => actLaw D (hL i)).expect_nonneg
      fun x => mul_self_nonneg _)]
    unfold FiniteLaw.expect
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun x _ => ?_
    change (∏ i, (D.halfLaw (hL i)).weight (x i) * actDens D (hL i) (x i)) * (Φ x * Φ x) ≤
      (1 - n * e)⁻¹ * ((∏ i, (D.halfLaw (hL i)).weight (x i)) * (Φ x * Φ x))
    rw [Finset.prod_mul_distrib]
    by_cases hz : ∏ i, (D.halfLaw (hL i)).weight (x i) = 0
    · rw [hz]
      simp
    · have hall : ∀ i, (D.halfLaw (hL i)).weight (x i) ≠ 0 := fun i hi =>
        hz (Finset.prod_eq_zero (mem_univ i) hi)
      have hprod : ∏ i, actDens D (hL i) (x i) ≤ (1 + e) ^ Fintype.card ι := by
        rw [← Finset.card_univ, ← Finset.prod_const]
        exact Finset.prod_le_prod₀ (fun i _ => actDens_nonneg D (hL i) (x i))
          fun i _ => hdens i (x i) (hall i)
      have hpow := one_add_pow_mul_le he hcard hne1
      have hle : ∏ i, actDens D (hL i) (x i) ≤ (1 - n * e)⁻¹ := by
        have h1 : (1 + e) ^ Fintype.card ι ≤ 1 / (1 - n * e) := (le_div_iff₀ hpos).mpr hpow
        rw [one_div] at h1
        exact hprod.trans h1
      have hw0 : 0 ≤ (∏ i, (D.halfLaw (hL i)).weight (x i)) * (Φ x * Φ x) :=
        mul_nonneg (Finset.prod_nonneg fun i _ => (D.halfLaw (hL i)).nonneg (x i))
          (mul_self_nonneg _)
      calc (∏ i, (D.halfLaw (hL i)).weight (x i)) * (∏ i, actDens D (hL i) (x i)) * (Φ x * Φ x)
          = (∏ i, actDens D (hL i) (x i)) *
              ((∏ i, (D.halfLaw (hL i)).weight (x i)) * (Φ x * Φ x)) := by ring
        _ ≤ (1 - n * e)⁻¹ * ((∏ i, (D.halfLaw (hL i)).weight (x i)) * (Φ x * Φ x)) :=
          mul_le_mul_of_nonneg_right hle hw0
  have hgb : 0 ≤ g * (√b)⁻¹ := mul_nonneg hg (inv_nonneg.mpr (Real.sqrt_nonneg _))
  rw [← hform]
  calc -(g / (1 - n * e) * (√b)⁻¹) * (FiniteLaw.pi fun i => D.halfLaw (hL i)).expect
          (fun ξ => Φ ξ * Φ ξ)
      = -(g * (√b)⁻¹) * ((1 - n * e)⁻¹ * (FiniteLaw.pi fun i => D.halfLaw (hL i)).expect
          (fun ξ => Φ ξ * Φ ξ)) := by ring
    _ ≤ -(g * (√b)⁻¹) * Recentering.nrm (FiniteLaw.pi fun i => actLaw D (hL i)) Φ ^ 2 := by
        have := mul_le_mul_of_nonneg_left hH hgb
        linarith
    _ ≤ _ := h

variable (O : Type) [Fintype O] [DecidableEq O] (G₂ : OrientedGraph (O × Fin 2))
  (hG : SwapInvariant O G₂) (G₁ : OrientedGraph (O × Fin 1))

/-- **The layer cap from the per-prime Markov bounds on the actual marginal**
(`lem:old-f-law`(e), the block step, for any swap-invariant two-layer graph): on a block with
`|𝔅| ≤ n`, `n e < 1` and least prime `b`, per-prime `T_old ⪰ -g p^{-1/2}` on `L²(m₀)` and
`g₀ ≤ 1 + e` give `Π_φ ⪰_ι -(g/(1 - n e)) b^{-1/2} Diag_ι(Π⁽¹⁾_φ)`. -/
theorem layerCap_of_actCaps (hres : LayerRestricts O G₂ G₁)
    (hL : ∀ i, (injLabellings (ZMod (pr i)) G₂).Nonempty)
    (h₁ : ∀ i, (injLabellings (ZMod (pr i)) G₁).Nonempty) (φ : ZMod 6 → O)
    {g e b : ℝ} {n : ℕ} (hg : 0 ≤ g) (he : 0 ≤ e) (hb0 : 0 < b)
    (hbp : ∀ i, b ≤ pr i) (hcard : Fintype.card ι ≤ n) (hne1 : (n : ℝ) * e < 1)
    (hgp : ∀ i, g * (√(pr i : ℝ))⁻¹ < 1)
    (hlow : ∀ i (f : ((layerData O G₂ hG).cut.Half → ZMod (pr i)) → ℝ),
      -(g * (√(pr i : ℝ))⁻¹) * Recentering.nrm (actLaw (layerData O G₂ hG) (hL i)) f ^ 2 ≤
        kernelForm (actLaw (layerData O G₂ hG) (hL i)) (actLaw (layerData O G₂ hG) (hL i))
          (actKernel (layerData O G₂ hG) (hL i)) f f)
    (hdens : ∀ i x, ((layerData O G₂ hG).halfLaw (hL i)).weight x ≠ 0 →
      actDens (layerData O G₂ hG) (hL i) x ≤ 1 + e) :
    reservedCut.Below
      (-(g / (1 - n * e) * (√b)⁻¹) •
        signedIntegral (emit (blockGraphLaw pr G₁ h₁) (midDiagEmission φ)).weight)
      (signedIntegral (emit (blockGraphLaw pr G₂ hL) (midEmission φ)).weight) := by
  set D := layerData O G₂ hG
  set μ := FiniteLaw.pi fun i => D.halfLaw (hL i)
  set K := fun x y : (∀ i, D.cut.Half → ZMod (pr i)) =>
    ∏ i, D.cutK (x i) (y i) / D.cutZ (hL i)
  set c := g / (1 - n * e) * (√b)⁻¹
  have htwo : ∀ F G : (reservedCut.Half → BlockLabel pr) → ℝ,
      reservedCut.form (signedIntegral (emit (blockGraphLaw pr G₂ hL) (midEmission φ)).weight)
        F G = kernelForm μ μ K ((F ∘ slotRows O φ) ∘ blockHalfRows pr D)
          ((G ∘ slotRows O φ) ∘ blockHalfRows pr D) := by
    intro F G
    rw [reservedForm_two]
    exact block_cut_expect pr D hL (F ∘ slotRows O φ) (G ∘ slotRows O φ)
  have hdiagPos := emit_positive (blockGraphLaw pr G₁ h₁) (midDiagEmission φ) reservedCut
    (midDiagEmission_reserved φ)
  have hK : ∀ x y, K y x = K x y := by
    intro x y
    simp only [K]
    exact Finset.prod_congr rfl fun i _ => by rw [D.cutK_symm]
  constructor
  · intro F G
    change reservedCut.form (signedIntegral (emit (blockGraphLaw pr G₂ hL)
          (midEmission φ)).weight) F G - -c *
          reservedCut.form (signedIntegral (emit (blockGraphLaw pr G₁ h₁)
            (midDiagEmission φ)).weight) F G =
      reservedCut.form (signedIntegral (emit (blockGraphLaw pr G₂ hL)
          (midEmission φ)).weight) G F - -c *
          reservedCut.form (signedIntegral (emit (blockGraphLaw pr G₁ h₁)
            (midDiagEmission φ)).weight) G F
    rw [htwo, htwo, kernelForm_symm μ K hK, hdiagPos.symmetric F G]
  · intro F
    change 0 ≤ reservedCut.form (signedIntegral (emit (blockGraphLaw pr G₂ hL)
          (midEmission φ)).weight) F F - -c *
          reservedCut.form (signedIntegral (emit (blockGraphLaw pr G₁ h₁)
            (midDiagEmission φ)).weight) F F
    have hdiag : reservedCut.form (signedIntegral (emit (blockGraphLaw pr G₁ h₁)
        (midDiagEmission φ)).weight) F F =
        μ.expect (fun ξ => ((F ∘ slotRows O φ) ∘ blockHalfRows pr D) ξ *
          ((F ∘ slotRows O φ) ∘ blockHalfRows pr D) ξ) := by
      rw [reservedForm_diag, pi_expect_equiv (fun i => D.halfLaw (hL i))
        (fun i => graphLaw G₁ (h₁ i)) (fun i => precomp (layerHalfEquiv O G₂ hG) _)
        (fun i y => layerHalfLaw_weight O G₂ hG G₁ hres (hL i) (h₁ i) y)]
      unfold blockGraphLaw
      rw [expect_tensor_eq_sum]
      rfl
    rw [htwo, hdiag]
    have h := act_block_lower D pr hL hg he hb0 hbp hcard hne1 hgp hlow hdens
      ((F ∘ slotRows O φ) ∘ blockHalfRows pr D)
    linarith

end Block

end Sarkozy.BlockInputs

namespace Sarkozy.BlockInputs

open Sarkozy Sarkozy.Labellings Sarkozy.PartV Sarkozy.FiveType Sarkozy.Cuts Sarkozy.BlockSpecPaper
  Sarkozy.BlockSpecPaper.AllpData Sarkozy.BlockAdapter

/-! ## The fold cut F21 -/

/-- `G_{F,2}` is invariant under the layer swap. -/
theorem foldGraph_swap : SwapInvariant (Fin 3) (foldGraph (Fin 2)) := by
  intro u w
  rw [mem_foldGraph, mem_foldGraph]

/-- `G_{F,1}` is the layer-`0` restriction of `G_{F,2}` (`lem:layer12-geometry`(c)). -/
theorem foldGraph_restricts : LayerRestricts (Fin 3) (foldGraph (Fin 2)) (foldGraph (Fin 1)) := by
  intro o o'
  rw [mem_foldGraph, mem_foldGraph]

/-- The spectral data of the cut F21 (the layer swap of `G_{F,2}`; cross pairs `x₀ → y₂`,
`y₀ → x₂`, so its normalized cut kernel is the paper's `K₀`). -/
noncomputable abbrev foldLayer : SpecData (Fin 3 × Fin 2) :=
  layerData (Fin 3) (foldGraph (Fin 2)) foldGraph_swap

/-- **The per-prime certificate of F21** (`lem:old-f-law`(f), the lower bound):
`T_old ⪰ -g p^{-1/2}` on `L²(m₀)`, `T_old` the Markov operator of the cut kernel on the actual half
marginal `m₀`. In the paper `g = 1 + (e_o - 1) r` at `p`, at most its value at the piece start. -/
def FoldCutCap (g : ℝ) (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (hne : (injLabellings (ZMod p) (foldGraph (Fin 2))).Nonempty)
    (f : (foldLayer.cut.Half → ZMod p) → ℝ),
    -(g * (√(p : ℝ))⁻¹) * Recentering.nrm (actLaw foldLayer hne) f ^ 2 ≤
      kernelForm (actLaw foldLayer hne) (actLaw foldLayer hne) (actKernel foldLayer hne) f f

/-- **The per-prime density bound of F21** (`lem:old-f-law`(a)): `g₀ ≤ 1 + e` on the support of
`ν_F` (the paper: `max g₀ = (p - 2)/(p - 4) ≤ 1 + e₀(p) ≤ 1 + e₀(X)`). -/
def FoldDensity (e : ℝ) (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (hne : (injLabellings (ZMod p) (foldGraph (Fin 2))).Nonempty)
    (x : foldLayer.cut.Half → ZMod p),
    (foldLayer.halfLaw hne).weight x ≠ 0 → actDens foldLayer hne x ≤ 1 + e

/-- **The F21 certificate of piece `i`** (`lem:old-f-law`(e) at `(X_i, L = 570)`,
`cert:record:old-f-cap`): constants `g` (the paper's `1 + (e_o(X) - 1) r_X`), `e` (`e₀(X)`) and
`n` (`n_X ≥ ⌊L/log X⌋`) with `n e < 1`, `570 < (n + 1) log X_i`, `g X_i^{-1/2} < 1` and
`g/(1 - n e) ≤ k_D(i)` (the paper's `k_D = H̄_X [1 + (e_o - 1) r_X]`), and the per-prime inputs at
every class-three prime of the piece. *Hypothesis* (per-prime analytic, with a finite part). -/
def MiddleFoldCert (i : Fin 33) : Prop :=
  ∃ (g e : ℝ) (n : ℕ), 0 ≤ g ∧ 0 ≤ e ∧ (n : ℝ) * e < 1 ∧
    570 < ((n : ℝ) + 1) * Real.log (pieceStart i) ∧ g * (√(pieceStart i : ℝ))⁻¹ < 1 ∧
    g / (1 - n * e) ≤ (allpInputs i).k .D ∧
    ∀ (p : ℕ) [Fact p.Prime], p % 4 = 3 → pieceStart i ≤ p → p < pieceStop i →
      FoldCutCap g p ∧ FoldDensity e p

/-- **B6's `FoldLayerCaps` at the recorded `k_D` from the F21 certificate of the piece**
(`lem:old-f-law`(e); the fold case of `lem:front12:reference`(ii)). -/
theorem foldLayerCaps_of_cert {i : Fin 33} (hc : MiddleFoldCert i) {ι : Type} [Fintype ι]
    [DecidableEq ι] (pr : ι → ℕ) [∀ j, Fact (pr j).Prime] (b : ℕ) (h3 : ∀ j, pr j % 4 = 3)
    (hpc : ∀ j, pieceStart i ≤ pr j ∧ pr j < pieceStop i)
    (hbud : ∑ j, Real.log (pr j) ≤ middleBudget) (hb : ∀ j, b ≤ pr j) (hb' : ∃ j, pr j = b)
    (hne : MiddleNonempty pr) :
    FoldLayerCaps pr hne ((allpInputs i).k .D) ((b : ℝ) ^ (-(1 / 2 : ℝ))) := by
  obtain ⟨g, e, n, hg, he, hne1, hn, hgX, hkD, hp⟩ := hc
  intro j
  have hX : (1 : ℝ) < pieceStart i := lt_trans (by norm_num) (pieceStart_gt_36 i)
  have hXp : ∀ k, (pieceStart i : ℝ) ≤ pr k := fun k => by exact_mod_cast (hpc k).1
  have hXb : (pieceStart i : ℝ) ≤ b := by
    obtain ⟨j₀, hj₀⟩ := hb'
    rw [← hj₀]
    exact hXp j₀
  have hb0 : (0 : ℝ) < b := by linarith
  have hLs : ∑ k, Real.log (pr k) ≤ 570 := middleBudget_real ▸ hbud
  have hlogX : 0 < Real.log (pieceStart i) := Real.log_pos hX
  have hcard : Fintype.card ι ≤ n := by
    have h1 : (Fintype.card ι : ℝ) * Real.log (pieceStart i) ≤ ∑ k, Real.log (pr k) := by
      rw [← nsmul_eq_mul, ← Finset.card_univ, ← Finset.sum_const]
      exact Finset.sum_le_sum fun k _ => Real.log_le_log (by linarith) (hXp k)
    have h2 : (Fintype.card ι : ℝ) < (n : ℝ) + 1 := by
      by_contra hcon
      push Not at hcon
      have := mul_le_mul_of_nonneg_right hcon hlogX.le
      linarith
    have h3 : Fintype.card ι < n + 1 := by exact_mod_cast h2
    omega
  have hgp : ∀ k, g * (√(pr k : ℝ))⁻¹ < 1 := fun k =>
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left
      (inv_anti₀ (Real.sqrt_pos.mpr (by linarith)) (Real.sqrt_le_sqrt (hXp k))) hg) hgX
  have hcert := fun k => hp (pr k) (h3 k) (hpc k).1 (hpc k).2
  have h := layerCap_of_actCaps pr (Fin 3) (foldGraph (Fin 2)) foldGraph_swap (foldGraph (Fin 1))
    foldGraph_restricts hne.F2 hne.F1 (fold j) hg he hb0 (fun k => by exact_mod_cast hb k) hcard
    hne1 hgp (fun k f => (hcert k).1 (hne.F2 k) f) (fun k x hx => (hcert k).2 (hne.F2 k) x hx)
  have hdiag := emit_positive (blockGraphLaw pr (foldGraph (Fin 1)) hne.F1)
    (midDiagEmission (fold j)) reservedCut (midDiagEmission_reserved _)
  have hr : 0 ≤ (√(b : ℝ))⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
  rw [rpow_neg_half_eq]
  exact Reserved.below_mono_coeff reservedCut hdiag (mul_le_mul_of_nonneg_right hkD hr) h

end Sarkozy.BlockInputs
