module

public import Sarkozy.PositiveRoots.Chamber
public import Sarkozy.PositiveRoots.ScoreKernel
public import Sarkozy.ProbabilityConstructions

@[expose] public section

/-!
# Non-vacuity checks for `Sarkozy.PositiveRoots`

* `root_chamber_toy`: every hypothesis of `Chamber.root_chamber` holds simultaneously on a toy
  instance (two points, the constant kernel, zero scores, no tilt `u = 0`, `r = 0`), so the
  hypothesis bundle is not contradictory; the conclusion is then the trivial
  `−(g_ch + d²/(1 + g_ch))‖f‖² ≤ (Ef)²`.
* `root_chamber_scores`: `root_chamber` specialized to the paper's chamber scores
  `η_j(x, x') = H(x_j, x'_{2−j})` (`ScoreKernel.chamberScore`) on any half chart mapping into
  triples of pairs; the transposition hypothesis `hσ` is discharged by `chamberScore_swap`, with
  `σ = Fin.revPerm` (`j ↦ 2 − j`).
* `root_normalization_b_toy`: the hypotheses of `Moments.root_normalization_b` hold on a two-point
  law with `H = qr ± 1` and no bad event.
* `pairMatrix_toy`: the matrix hypotheses of `Mlam_lower` are met at `λ = 1/2` by the rational
  `g = 5.4664113` (`f_λ(g) ≥ 0`), so the matrix cap is not vacuous at the paper's parameters.
-/

namespace Sarkozy.PositiveRoots

open Finset Sarkozy Sarkozy.Recentering Sarkozy.Cuts Sarkozy.SpectralC Sarkozy.L20Cap
open Sarkozy.SpectralD.StarMatrix

theorem expect_zero' {X : Type*} [Fintype X] (ν : FiniteLaw X) :
    ν.expect (fun _ => (0 : ℝ)) = 0 := by
  unfold FiniteLaw.expect; simp

theorem kernelForm_const {X : Type*} [Fintype X] (ν : FiniteLaw X) (c : ℝ) (f g : X → ℝ) :
    kernelForm ν ν (fun _ _ => c) f g = c * ν.expect f * ν.expect g := by
  rw [kernelForm_apply]
  have : ∀ x, f x * ν.expect (fun y => c * g y) = (c * ν.expect g) * f x := by
    intro x; rw [ν.expect_const_mul]; ring
  rw [ν.expect_congr this, ν.expect_const_mul]
  ring

theorem abs_expect_le_nrm {X : Type*} [Fintype X] (ν : FiniteLaw X) (f : X → ℝ) :
    |ν.expect f| ≤ nrm ν f := by
  have h := abs_ip_le ν f (fun _ => 1)
  rw [Cuts.nrm_one, mul_one] at h
  have e : Recentering.ip ν f (fun _ => 1) = ν.expect f := by
    unfold Recentering.ip; exact ν.expect_congr fun x => mul_one _
  rwa [e] at h

/-- **Non-vacuity of `root_chamber`**: all its hypotheses hold on a toy instance. -/
theorem root_chamber_toy :
    let ν := FiniteLaw.uniform (Fin 2)
    let K0 : Fin 2 → Fin 2 → ℝ := fun _ _ => 1
    let η : Fin 3 → Fin 2 → Fin 2 → ℝ := fun _ _ _ => 0
    (∀ f, -(gCh 0 6 0 0 (epsU 0 0 0 1) ((1 - 0) * zMinus 0 0 (1 / (1 - 0))) +
          dU 0 0 0 (1 / (1 - 0)) (zMinus 0 0 (1 / (1 - 0))) ^ 2 /
            (1 + gCh 0 6 0 0 (epsU 0 0 0 1) ((1 - 0) * zMinus 0 0 (1 / (1 - 0))))) *
          nrm ν f ^ 2 ≤
        kernelForm ν ν (tiltKernel ν (fun x y => K0 x y / kmass ν K0) η (sqMean η) 0) f f) := by
  intro ν K0 η
  have hK0m : kmass ν K0 = 1 := by
    rw [kmass_eq_kernelForm, kernelForm_const, expect_one]; ring
  have hetaBar : ∀ x y, etaBar η x y = 0 := fun x y => by simp [etaBar, η]
  have hsqM : ∀ x y, sqMean η x y = 0 := fun x y => by simp [sqMean, η]
  have hrow1 : ∀ x, rowFun ν (fun x y => K0 x y / kmass ν K0) x = 1 := by
    intro x
    simp only [rowFun, hK0m, K0, div_one]
    exact expect_one ν
  have hrow0 : rowFun ν (fun x y => K0 x y / kmass ν K0 * etaBar η x y) = fun _ => 0 := by
    funext x
    simp only [rowFun, hetaBar, mul_zero]
    exact expect_zero' ν
  have hnrm0 : nrm ν (fun _ => (0 : ℝ)) = 0 := by
    unfold nrm Recentering.ip; simp only [mul_zero]; rw [expect_zero', Real.sqrt_zero]
  have key := root_chamber ν K0 (fun _ _ => zero_le_one) (fun _ _ => rfl) η (Equiv.refl _)
    (fun _ _ _ => rfl) (fun _ _ => 0) (fun _ => 0) (u := 0) (r := 0) (εZ := 0) (ε0 := 0)
    (εlin := 0) (εsq := 1) (Γ := 0) (g := 6) (dr2 := 0) (δ := 0) (l := 0) (h0 := 0) (cc := 0)
    (b := 0) (R := 1) le_rfl le_rfl le_rfl le_rfl le_rfl zero_le_one le_rfl (by norm_num)
    (by rw [hK0m]; norm_num)
    (fun f => by simp)
    (by
      have : center ν (fun _ => (0 : ℝ)) = fun _ => 0 := by
        funext x; simp [center]
      rw [this, hnrm0]; norm_num)
    (by
      have e : (2 * (0 : ℝ) / (1 + 0 ^ 2)) = 0 := by norm_num
      rw [e, gRoot_zero]
      have : Real.sqrt 30 ≤ Real.sqrt 36 := Real.sqrt_le_sqrt (by norm_num)
      rwa [show (36 : ℝ) = 6 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)] at this)
    (fun f hf => by
      rw [kernelForm_const, hf]
      simp only [Recentering.ip, mul_zero, expect_zero']
      norm_num)
    (fun f hf => by
      have e : (fun x y => K0 x y * etaBar η x y) = fun _ _ => 0 := by
        funext x y; rw [hetaBar]; ring
      rw [e, kernelForm_const]
      simp)
    (fun f g => by
      have e : (fun x y => K0 x y * sqMean η x y - K0 x y) = fun _ _ => -1 := by
        funext x y; rw [hsqM]; simp [K0]
      rw [e, kernelForm_const]
      have h1 := abs_expect_le_nrm ν f
      have h2 := abs_expect_le_nrm ν g
      rw [show (-1 : ℝ) * ν.expect f * ν.expect g = -(ν.expect f * ν.expect g) by ring, abs_neg,
        abs_mul]
      calc |ν.expect f| * |ν.expect g| ≤ nrm ν f * nrm ν g :=
            mul_le_mul h1 h2 (abs_nonneg _) (nrm_nonneg ν f)
        _ = 1 * nrm ν f * nrm ν g := by ring)
    (by
      have : (fun x => rowFun ν (fun x y => K0 x y / kmass ν K0) x - 1) = fun _ => 0 := by
        funext x; rw [hrow1]; ring
      rw [this, hnrm0])
    (fun x x' => by rw [hrow1, hrow1]; norm_num)
    (by
      rw [hrow0]
      have : center ν (fun _ => (0 : ℝ)) = fun _ => 0 := by
        funext x; simp [center]
      rw [this, hnrm0])
    (by
      change |ν.expect (rowFun ν (fun x y => K0 x y / kmass ν K0 * etaBar η x y))| ≤ 0
      rw [hrow0, expect_zero', abs_zero])
    (fun x => by rw [hrow0]; simp)
    (fun _ _ _ _ => by simp [η])
    (by norm_num)
    (by norm_num [zMinus])
    (by norm_num [cCh, epsU, zMinus])
  exact key.1

/-- **`root_chamber` for the paper's chamber scores**: on a half chart `X` with a map `φ` to the
three pairs `(a, b, c)` of a half, the scores `η_j(x, x') = H(φx_j, φx'_{2−j})`
(`lem:positive-root-properties`(c)) satisfy the transposition hypothesis with `σ = Fin.revPerm`. -/
theorem chamberScore_hσ {F : Type*} [Field F] [Fintype F] [DecidableEq F] {X : Type*}
    (φ : X → Fin 3 → F × F) (j : Fin 3) (x y : X) :
    chamberScore j (φ y) (φ x) = chamberScore (Fin.revPerm j) (φ x) (φ y) := by
  rw [chamberScore_swap, Fin.revPerm_apply]

/-- **Non-vacuity of `root_normalization_b`**: a two-point law with `H = qr ± 1`, no bad event. -/
theorem root_normalization_b_toy {q r : ℝ} (hr : 0 < r) (hq : q = r ^ 2) (hq2 : q < 1 / 2)
    (hq36 : 36 * q < 1) :
    let μ := FiniteLaw.uniform (Fin 2)
    let H : Fin 2 → ℝ := ![q * r + 1, q * r - 1]
    |(∑ ω ∈ univ.filter (fun _ : Fin 2 => True), μ.weight ω * H ω) /
        (∑ ω ∈ univ.filter (fun _ : Fin 2 => True), μ.weight ω)| ≤
      (q * r + 36 * q * (2 + r) + 2 * q * r / (1 - q)) / (1 - 36 * q) := by
  intro μ H
  have hmean : μ.expect H = q * r := by
    rw [FiniteLaw.expect_uniform]
    simp [H, Fin.sum_univ_two]
  have hsq : 1 - 4 * q ≤ μ.expect (fun ω => H ω ^ 2) := by
    rw [FiniteLaw.expect_uniform]
    simp only [Fin.sum_univ_two, Fintype.card_fin, H, Matrix.cons_val_zero, Matrix.cons_val_one]
    have hq0 : 0 ≤ q := by rw [hq]; positivity
    nlinarith [sq_nonneg (q * r)]
  exact (root_normalization_b μ (fun _ => True) (fun _ => False) H hr hq hq2 hq36
    (by simp only [not_true_eq_false, Finset.filter_false, Finset.sum_empty]; rw [hq]; positivity)
    (by
      simp only [not_true_eq_false, false_and, Finset.filter_false, Finset.sum_empty]
      exact div_nonneg (by positivity) (by linarith))
    (fun ω h => absurd trivial h)
    (fun ω h => absurd trivial h) hmean hsq).1

/-- **Non-vacuity of the matrix cap at `λ = 1/2`**: `g = 5.4664113` satisfies the hypotheses of
`Mlam_lower` (in particular `3g³ + λg² − 90g − 26λ ≥ 0`), so `M_{1/2} ⪰ −5.4664113 I`. -/
theorem pairMatrix_toy (x : Idx → ℂ) :
    -(54664113 / 10 ^ 7) * ∑ k, ‖x k‖ ^ 2 ≤ (bform (Mlam (1 / 2)) x x).re :=
  Mlam_lower (by norm_num) (by norm_num) (by norm_num) (by norm_num) x

end Sarkozy.PositiveRoots
