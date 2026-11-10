module

public import Sarkozy.Structured.RepairExistence

/-!
# The Neumann series split (`lem:tr:repair`(g))

`lem:tr:repair`(g) (`paper/sections/17_completion_repair.tex`, brief F). Here `ρ < 1` is not
assumed. Instead there are subspaces `V_X ⊆ L²_0(ν_X)`, `V_Y ⊆ L²_0(ν_Y)` with
`A V_Y ⊆ V_X`, `A* V_X ⊆ V_Y` and `‖A|_{V_Y}‖ ≤ ρ_I < 1`. For targets `u ∈ V_X`, `v ∈ V_Y`
with `|u|, |v| ≤ U` and `‖u - Av‖, ‖v - A*u‖ ≤ e_I`, the equations of (a) have a solution
`f ∈ V_X`, `g ∈ V_Y` with `‖f‖_∞, ‖g‖_∞ ≤ F_N = 2NU + K_∞ ρ_I^{2N-1} e_I/(1 - ρ_I²)` for every
`N ≥ 1` (`repair_neumann`).

The paper writes `f = ∑_{j≥0} (AA*)^j (u - Av)`. Here `f` is the solution of
`f = (u - Av) + AA* f` in `V_X`. It exists because `I - AA*` is injective on `V_X`
(`‖AA*|_{V_X}‖ ≤ ρ_I²`), hence surjective in finite dimension. `neumann_split` is the
identity `f = ∑_{j<N} (AA*)^j (u - Av) + (AA*)^N f`, with `‖(AA*)^N f‖ ≤ ρ_I^{2N}‖f‖`
(`neumann_tail_nrm`). So `f` is the sum of the series, and the bound comes from the split
after `N` terms, as in the paper:
* the first `N` terms are at most `2U` each in sup norm, since `A` and `A*` are sup-norm
  contractions (`condOp_sup_le`);
* the tail `(AA*)^N f = A(A*(AA*)^{N-1} f)` is at most `K_∞ ρ_I^{2N-1}‖f‖`, with
  `‖f‖ ≤ e_I/(1 - ρ_I²)`.

`adjoint_nrm_le` gives `‖A*|_{V_X}‖ ≤ ρ_I` from `‖A|_{V_Y}‖ ≤ ρ_I`. The conclusion of (c) for
`2F_N < 1` is `repair_positive` (`Sarkozy/Structured/MarginalRepair.lean`). The invariance
claim of (g) is immediate when `V_X`, `V_Y` consist of invariant functions, and is not stated
separately.
-/

@[expose] public section

open Finset
open scoped BigOperators

namespace Sarkozy.Structured

open Sarkozy.Recentering

variable {X Y : Type*} [Fintype X] [Fintype Y]

/-- A conditional operator is a contraction for the sup norm: `|k| ≤ U` gives `|Ak| ≤ U`. -/
theorem condOp_sup_le (ν : FiniteLaw (X × Y)) (νX : FiniteLaw X) (hνX : ∀ x, 0 < νX.weight x)
    (hmX : ∀ φ : X → ℝ, ν.expect (fun p => φ p.1) = νX.expect φ)
    (A : (Y → ℝ) →ₗ[ℝ] (X → ℝ)) (hA : ∀ h k, ν.expect (fun p => h p.1 * k p.2) = ip νX h (A k))
    (k : Y → ℝ) {U : ℝ} (hk : ∀ y, |k y| ≤ U) (x : X) : |A k x| ≤ U := by
  classical
  have h1 := hA (fun x' => if x' = x then 1 else 0) k
  have hip : ip νX (fun x' => if x' = x then 1 else 0) (A k) = νX.weight x * A k x := by
    unfold ip FiniteLaw.expect
    simp only [ite_mul, one_mul, zero_mul, mul_ite, mul_zero, sum_ite_eq', mem_univ, ite_true]
  have hmass : ν.expect (fun p => if p.1 = x then (1 : ℝ) else 0) = νX.weight x := by
    rw [hmX (fun x' => if x' = x then 1 else 0)]
    unfold FiniteLaw.expect
    simp only [mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ, ite_true]
  have hb : |ν.expect (fun p => (if p.1 = x then (1 : ℝ) else 0) * k p.2)| ≤ U * νX.weight x := by
    rw [← hmass, ← ν.expect_const_mul]
    refine (ν.abs_expect_le _).trans (ν.expect_mono fun p => ?_)
    split_ifs
    · simp only [one_mul, mul_one]
      exact hk p.2
    · simp
  rw [h1, hip, abs_mul, abs_of_pos (hνX x), mul_comm U] at hb
  exact le_of_mul_le_mul_left hb (hνX x)

/-- **The adjoint bound**: if `A*V_X ⊆ V_Y` and `‖Ak‖ ≤ ρ‖k‖` on `V_Y`, then `‖A*h‖ ≤ ρ‖h‖`
on `V_X`. -/
theorem adjoint_nrm_le (ν : FiniteLaw (X × Y)) (νX : FiniteLaw X) (νY : FiniteLaw Y)
    (A : (Y → ℝ) →ₗ[ℝ] (X → ℝ)) (B : (X → ℝ) →ₗ[ℝ] (Y → ℝ))
    (hA : ∀ h k, ν.expect (fun p => h p.1 * k p.2) = ip νX h (A k))
    (hB : ∀ h k, ν.expect (fun p => h p.1 * k p.2) = ip νY (B h) k)
    (VX : Submodule ℝ (X → ℝ)) (VY : Submodule ℝ (Y → ℝ)) (hBV : ∀ h ∈ VX, B h ∈ VY)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hAρ : ∀ k ∈ VY, nrm νX (A k) ≤ ρ * nrm νY k)
    (h : X → ℝ) (hh : h ∈ VX) : nrm νY (B h) ≤ ρ * nrm νX h := by
  have e1 : ip νY (B h) (B h) = ip νX h (A (B h)) := by rw [← hB, hA]
  have h2 : ip νX h (A (B h)) ≤ nrm νX h * (ρ * nrm νY (B h)) :=
    (le_abs_self _).trans ((abs_ip_le νX h (A (B h))).trans
      (mul_le_mul_of_nonneg_left (hAρ _ (hBV h hh)) (Real.sqrt_nonneg _)))
  have hsq : ip νY (B h) (B h) = nrm νY (B h) ^ 2 := by
    unfold nrm
    rw [Real.sq_sqrt (show 0 ≤ ip νY (B h) (B h) from νY.expect_nonneg fun y => mul_self_nonneg _)]
  have hn : 0 ≤ nrm νY (B h) := Real.sqrt_nonneg _
  have hm : 0 ≤ nrm νX h := Real.sqrt_nonneg _
  rw [e1] at hsq
  nlinarith [mul_nonneg hρ hm]

/-- `‖(AB)h‖ ≤ ρ²‖h‖` on `V_X`. -/
theorem comp_nrm_le (νX : FiniteLaw X) (νY : FiniteLaw Y)
    (A : (Y → ℝ) →ₗ[ℝ] (X → ℝ)) (B : (X → ℝ) →ₗ[ℝ] (Y → ℝ))
    (VX : Submodule ℝ (X → ℝ)) (VY : Submodule ℝ (Y → ℝ)) (hBV : ∀ h ∈ VX, B h ∈ VY)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hAρ : ∀ k ∈ VY, nrm νX (A k) ≤ ρ * nrm νY k)
    (hBρ : ∀ h ∈ VX, nrm νY (B h) ≤ ρ * nrm νX h) (h : X → ℝ) (hh : h ∈ VX) :
    nrm νX ((A ∘ₗ B) h) ≤ ρ ^ 2 * nrm νX h := by
  rw [LinearMap.comp_apply]
  calc nrm νX (A (B h)) ≤ ρ * nrm νY (B h) := hAρ _ (hBV h hh)
    _ ≤ ρ * (ρ * nrm νX h) := mul_le_mul_of_nonneg_left (hBρ h hh) hρ
    _ = ρ ^ 2 * nrm νX h := by ring

/-- The powers of `T = AB` preserve `V_X` and contract by `ρ²`. -/
theorem neumann_tail_nrm (νX : FiniteLaw X) (νY : FiniteLaw Y)
    (A : (Y → ℝ) →ₗ[ℝ] (X → ℝ)) (B : (X → ℝ) →ₗ[ℝ] (Y → ℝ))
    (VX : Submodule ℝ (X → ℝ)) (VY : Submodule ℝ (Y → ℝ)) (hAV : ∀ k ∈ VY, A k ∈ VX)
    (hBV : ∀ h ∈ VX, B h ∈ VY)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hAρ : ∀ k ∈ VY, nrm νX (A k) ≤ ρ * nrm νY k)
    (hBρ : ∀ h ∈ VX, nrm νY (B h) ≤ ρ * nrm νX h) (w : X → ℝ) (hw : w ∈ VX) (n : ℕ) :
    ((A ∘ₗ B) ^ n) w ∈ VX ∧ nrm νX (((A ∘ₗ B) ^ n) w) ≤ ρ ^ (2 * n) * nrm νX w := by
  induction n with
  | zero => simp [hw]
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply]
    refine ⟨?_, ?_⟩
    · rw [LinearMap.comp_apply]
      exact hAV _ (hBV _ ih.1)
    · calc nrm νX ((A ∘ₗ B) (((A ∘ₗ B) ^ n) w)) ≤ ρ ^ 2 * nrm νX (((A ∘ₗ B) ^ n) w) :=
            comp_nrm_le νX νY A B VX VY hBV hρ hAρ hBρ _ ih.1
        _ ≤ ρ ^ 2 * (ρ ^ (2 * n) * nrm νX w) :=
            mul_le_mul_of_nonneg_left ih.2 (pow_nonneg hρ 2)
        _ = ρ ^ (2 * (n + 1)) * nrm νX w := by ring

omit [Fintype X] [Fintype Y] in
/-- **The split after `N` terms**: if `w = w₀ + ABw`, then
`w = ∑_{j<N} (AB)^j w₀ + (AB)^N w`. -/
theorem neumann_split (A : (Y → ℝ) →ₗ[ℝ] (X → ℝ)) (B : (X → ℝ) →ₗ[ℝ] (Y → ℝ))
    (w w0 : X → ℝ) (hfix : w = w0 + (A ∘ₗ B) w) (N : ℕ) :
    w = ∑ j ∈ range N, ((A ∘ₗ B) ^ j) w0 + ((A ∘ₗ B) ^ N) w := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [sum_range_succ, ih]
    conv_lhs => rw [hfix]
    rw [map_add, pow_succ, Module.End.mul_apply, ← ih]
    abel

omit [Fintype X] [Fintype Y] in
/-- The powers of `AB` are sup-norm contractions. -/
theorem neumann_pow_sup_le (A : (Y → ℝ) →ₗ[ℝ] (X → ℝ)) (B : (X → ℝ) →ₗ[ℝ] (Y → ℝ))
    (hAM : ∀ (k : Y → ℝ) (U : ℝ), (∀ y, |k y| ≤ U) → ∀ x, |A k x| ≤ U)
    (hBM : ∀ (h : X → ℝ) (U : ℝ), (∀ x, |h x| ≤ U) → ∀ y, |B h y| ≤ U)
    (h : X → ℝ) {U : ℝ} (hh : ∀ x, |h x| ≤ U) (n : ℕ) (x : X) :
    |((A ∘ₗ B) ^ n) h x| ≤ U := by
  induction n generalizing x with
  | zero => simpa using hh x
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, LinearMap.comp_apply]
    exact hAM _ U (hBM _ U ih) x

/-- **The sup bound of (g)** for a solution `w ∈ V_X` of `w = (u - Av) + ABw`:
`|w| ≤ 2NU + K_∞ ρ^{2N-1} e/(1 - ρ²)` for every `N ≥ 1`. -/
theorem neumann_sup_le (νX : FiniteLaw X) (νY : FiniteLaw Y)
    (A : (Y → ℝ) →ₗ[ℝ] (X → ℝ)) (B : (X → ℝ) →ₗ[ℝ] (Y → ℝ))
    (VX : Submodule ℝ (X → ℝ)) (VY : Submodule ℝ (Y → ℝ)) (hAV : ∀ k ∈ VY, A k ∈ VX)
    (hBV : ∀ h ∈ VX, B h ∈ VY)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hρ1 : ρ < 1) (hAρ : ∀ k ∈ VY, nrm νX (A k) ≤ ρ * nrm νY k)
    (hBρ : ∀ h ∈ VX, nrm νY (B h) ≤ ρ * nrm νX h)
    {Kinf : ℝ} (hK : 0 ≤ Kinf) (hAK : ∀ (k : Y → ℝ) (x : X), |A k x| ≤ Kinf * nrm νY k)
    (hAM : ∀ (k : Y → ℝ) (U : ℝ), (∀ y, |k y| ≤ U) → ∀ x, |A k x| ≤ U)
    (hBM : ∀ (h : X → ℝ) (U : ℝ), (∀ x, |h x| ≤ U) → ∀ y, |B h y| ≤ U)
    (u : X → ℝ) (v : Y → ℝ) {U e : ℝ} (hu : ∀ x, |u x| ≤ U) (hv : ∀ y, |v y| ≤ U)
    (he : nrm νX (u - A v) ≤ e) (w : X → ℝ) (hw : w ∈ VX)
    (hfix : w = (u - A v) + (A ∘ₗ B) w) (N : ℕ) (hN : 1 ≤ N) (x : X) :
    |w x| ≤ 2 * N * U + Kinf * ρ ^ (2 * N - 1) * e / (1 - ρ ^ 2) := by
  have hρ2 : 0 < 1 - ρ ^ 2 := by nlinarith
  -- `‖w‖ ≤ e/(1 - ρ²)`
  have hwn : nrm νX w ≤ e / (1 - ρ ^ 2) := by
    have h1 : nrm νX w ≤ nrm νX (u - A v) + nrm νX ((A ∘ₗ B) w) := by
      have := nrm_add_le νX (u - A v) ((A ∘ₗ B) w)
      rw [show (fun x => (u - A v) x + ((A ∘ₗ B) w) x) = (u - A v) + (A ∘ₗ B) w from rfl,
        ← hfix] at this
      exact this
    have h2 := comp_nrm_le νX νY A B VX VY hBV hρ hAρ hBρ w hw
    rw [le_div_iff₀ hρ2]
    nlinarith
  -- the split
  have hsplit := congrFun (neumann_split A B w (u - A v) hfix N) x
  rw [Pi.add_apply, Finset.sum_apply] at hsplit
  rw [hsplit]
  -- the first `N` terms
  have hterm : ∀ j, |((A ∘ₗ B) ^ j) (u - A v) x| ≤ 2 * U := by
    intro j
    rw [map_sub, Pi.sub_apply]
    have h1 := neumann_pow_sup_le A B hAM hBM u hu j x
    have h2 := neumann_pow_sup_le A B hAM hBM (A v) (hAM v U hv) j x
    calc |((A ∘ₗ B) ^ j) u x - ((A ∘ₗ B) ^ j) (A v) x| ≤
          |((A ∘ₗ B) ^ j) u x| + |((A ∘ₗ B) ^ j) (A v) x| := abs_sub _ _
      _ ≤ 2 * U := by linarith
  have hsum : |∑ j ∈ range N, ((A ∘ₗ B) ^ j) (u - A v) x| ≤ 2 * N * U := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ j ∈ range N, |((A ∘ₗ B) ^ j) (u - A v) x| ≤ ∑ _j ∈ range N, 2 * U :=
          sum_le_sum fun j _ => hterm j
      _ = 2 * N * U := by rw [sum_const, card_range, nsmul_eq_mul]; ring
  -- the tail
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have htail : |((A ∘ₗ B) ^ (M + 1)) w x| ≤ Kinf * ρ ^ (2 * (M + 1) - 1) * e / (1 - ρ ^ 2) := by
    rw [pow_succ', Module.End.mul_apply, LinearMap.comp_apply]
    have hM := neumann_tail_nrm νX νY A B VX VY hAV hBV hρ hAρ hBρ w hw M
    have hB1 := hBρ _ hM.1
    have hexp : 2 * (M + 1) - 1 = 2 * M + 1 := by omega
    rw [hexp]
    calc |A (B (((A ∘ₗ B) ^ M) w)) x| ≤ Kinf * nrm νY (B (((A ∘ₗ B) ^ M) w)) := hAK _ x
      _ ≤ Kinf * (ρ * (ρ ^ (2 * M) * nrm νX w)) := by
          apply mul_le_mul_of_nonneg_left _ hK
          exact hB1.trans (mul_le_mul_of_nonneg_left hM.2 hρ)
      _ ≤ Kinf * (ρ * (ρ ^ (2 * M) * (e / (1 - ρ ^ 2)))) := by
          apply mul_le_mul_of_nonneg_left _ hK
          apply mul_le_mul_of_nonneg_left _ hρ
          exact mul_le_mul_of_nonneg_left hwn (pow_nonneg hρ _)
      _ = Kinf * ρ ^ (2 * M + 1) * e / (1 - ρ ^ 2) := by ring
  calc |∑ j ∈ range (M + 1), ((A ∘ₗ B) ^ j) (u - A v) x + ((A ∘ₗ B) ^ (M + 1)) w x| ≤
        |∑ j ∈ range (M + 1), ((A ∘ₗ B) ^ j) (u - A v) x| + |((A ∘ₗ B) ^ (M + 1)) w x| :=
        abs_add_le _ _
    _ ≤ _ := add_le_add hsum htail

/-- The adjoint conditional operator is a sup-norm contraction: `|h| ≤ U` gives `|A*h| ≤ U`. -/
theorem condOp_sup_le' (ν : FiniteLaw (X × Y)) (νY : FiniteLaw Y) (hνY : ∀ y, 0 < νY.weight y)
    (hmY : ∀ φ : Y → ℝ, ν.expect (fun p => φ p.2) = νY.expect φ)
    (B : (X → ℝ) →ₗ[ℝ] (Y → ℝ)) (hB : ∀ h k, ν.expect (fun p => h p.1 * k p.2) = ip νY (B h) k)
    (h : X → ℝ) {U : ℝ} (hh : ∀ x, |h x| ≤ U) (y : Y) : |B h y| ≤ U := by
  classical
  have h1 := hB h (fun y' => if y' = y then 1 else 0)
  have hip : ip νY (B h) (fun y' => if y' = y then 1 else 0) = νY.weight y * B h y := by
    unfold ip FiniteLaw.expect
    simp only [mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ, ite_true]
  have hmass : ν.expect (fun p => if p.2 = y then (1 : ℝ) else 0) = νY.weight y := by
    rw [hmY (fun y' => if y' = y then 1 else 0)]
    unfold FiniteLaw.expect
    simp only [mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ, ite_true]
  have hb : |ν.expect (fun p => h p.1 * (if p.2 = y then (1 : ℝ) else 0))| ≤ U * νY.weight y := by
    rw [← hmass, ← ν.expect_const_mul]
    refine (ν.abs_expect_le _).trans (ν.expect_mono fun p => ?_)
    split_ifs
    · simp only [mul_one]
      exact hh p.1
    · simp
  rw [h1, hip, abs_mul, abs_of_pos (hνY y), mul_comm U] at hb
  exact le_of_mul_le_mul_left hb (hνY y)

/-- **`lem:tr:repair`(g), the Neumann series split**: without `ρ < 1`, let `V_X ⊆ L²_0(ν_X)`,
`V_Y ⊆ L²_0(ν_Y)` with `AV_Y ⊆ V_X`, `A*V_X ⊆ V_Y` and `‖A|_{V_Y}‖ ≤ ρ_I < 1`, and let `K_∞`
bound `A`, `A*` from `L²` to `L^∞`. For `u ∈ V_X`, `v ∈ V_Y` with `|u|, |v| ≤ U` and
`‖u - Av‖, ‖v - A*u‖ ≤ e_I`, the equations of (a) have a centred solution `f ∈ V_X`,
`g ∈ V_Y`. It is the sum of the Neumann series `f = ∑_j (AA*)^j (u - Av)`,
`g = ∑_j (A*A)^j (v - A*u)`, in the form of the split after `N` terms, and for every `N ≥ 1`
`‖f‖_∞, ‖g‖_∞ ≤ F_N = 2NU + K_∞ ρ_I^{2N-1} e_I/(1 - ρ_I²)`. -/
theorem repair_neumann (ν : FiniteLaw (X × Y)) (νX : FiniteLaw X) (νY : FiniteLaw Y)
    (hmX : ∀ φ : X → ℝ, ν.expect (fun p => φ p.1) = νX.expect φ)
    (hmY : ∀ φ : Y → ℝ, ν.expect (fun p => φ p.2) = νY.expect φ)
    (hνX : ∀ x, 0 < νX.weight x) (hνY : ∀ y, 0 < νY.weight y)
    (A : (Y → ℝ) →ₗ[ℝ] (X → ℝ)) (B : (X → ℝ) →ₗ[ℝ] (Y → ℝ))
    (hA : ∀ h k, ν.expect (fun p => h p.1 * k p.2) = ip νX h (A k))
    (hB : ∀ h k, ν.expect (fun p => h p.1 * k p.2) = ip νY (B h) k)
    (VX : Submodule ℝ (X → ℝ)) (VY : Submodule ℝ (Y → ℝ))
    (hVX0 : ∀ h ∈ VX, νX.expect h = 0) (hVY0 : ∀ k ∈ VY, νY.expect k = 0)
    (hAV : ∀ k ∈ VY, A k ∈ VX) (hBV : ∀ h ∈ VX, B h ∈ VY)
    {ρI : ℝ} (hρI : 0 ≤ ρI) (hρI1 : ρI < 1) (hAρ : ∀ k ∈ VY, nrm νX (A k) ≤ ρI * nrm νY k)
    {Kinf : ℝ} (hK : 0 ≤ Kinf) (hAK : ∀ (k : Y → ℝ) (x : X), |A k x| ≤ Kinf * nrm νY k)
    (hBK : ∀ (h : X → ℝ) (y : Y), |B h y| ≤ Kinf * nrm νX h)
    (u : X → ℝ) (v : Y → ℝ) (hu : u ∈ VX) (hv : v ∈ VY) {U eI : ℝ}
    (hUu : ∀ x, |u x| ≤ U) (hUv : ∀ y, |v y| ≤ U)
    (he1 : nrm νX (u - A v) ≤ eI) (he2 : nrm νY (v - B u) ≤ eI) :
    ∃ f ∈ VX, ∃ g ∈ VY, νX.expect f = 0 ∧ νY.expect g = 0 ∧
      (∀ x, f x + A g x = u x) ∧ (∀ y, g y + B f y = v y) ∧
      (∀ N, f = ∑ j ∈ range N, ((A ∘ₗ B) ^ j) (u - A v) + ((A ∘ₗ B) ^ N) f) ∧
      (∀ N, g = ∑ j ∈ range N, ((B ∘ₗ A) ^ j) (v - B u) + ((B ∘ₗ A) ^ N) g) ∧
      ∀ N : ℕ, 1 ≤ N →
        (∀ x, |f x| ≤ 2 * N * U + Kinf * ρI ^ (2 * N - 1) * eI / (1 - ρI ^ 2)) ∧
        (∀ y, |g y| ≤ 2 * N * U + Kinf * ρI ^ (2 * N - 1) * eI / (1 - ρI ^ 2)) := by
  have hBρ : ∀ h ∈ VX, nrm νY (B h) ≤ ρI * nrm νX h :=
    fun h hh => adjoint_nrm_le ν νX νY A B hA hB VX VY hBV hρI hAρ h hh
  have hAM : ∀ (k : Y → ℝ) (U : ℝ), (∀ y, |k y| ≤ U) → ∀ x, |A k x| ≤ U :=
    fun k _ hk x => condOp_sup_le ν νX hνX hmX A hA k hk x
  have hBM : ∀ (h : X → ℝ) (U : ℝ), (∀ x, |h x| ≤ U) → ∀ y, |B h y| ≤ U :=
    fun h _ hh y => condOp_sup_le' ν νY hνY hmY B hB h hh y
  -- existence: `I - AB` is injective, hence surjective, on `V_X`
  set T : Module.End ℝ (X → ℝ) := A ∘ₗ B with hT
  have hTV : ∀ h ∈ VX, T h ∈ VX := fun h hh => hAV _ (hBV h hh)
  set S0 : Module.End ℝ (X → ℝ) := LinearMap.id - T with hS0
  have hSmaps : ∀ h ∈ VX, S0 h ∈ VX := by
    intro h hh
    rw [hS0, LinearMap.sub_apply, LinearMap.id_apply]
    exact VX.sub_mem hh (hTV h hh)
  set S : VX →ₗ[ℝ] VX := S0.restrict hSmaps with hS
  have hSapply : ∀ h : VX, (S h : X → ℝ) = (h : X → ℝ) - T h := by
    intro h
    rw [hS, LinearMap.restrict_apply]
    show S0 h = (h : X → ℝ) - T h
    rw [hS0, LinearMap.sub_apply, LinearMap.id_apply]
  have hSinj : Function.Injective S := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro h hSh
    have h0 : (h : X → ℝ) - T h = 0 := by
      rw [← hSapply, hSh]
      rfl
    have hfixed : T h = h := (sub_eq_zero.mp h0).symm
    have hn := comp_nrm_le νX νY A B VX VY hBV hρI hAρ hBρ h h.2
    rw [← hT, hfixed] at hn
    have hn0 : nrm νX h = 0 := by
      have h00 : 0 ≤ nrm νX h := Real.sqrt_nonneg _
      have hρ2 : ρI ^ 2 < 1 := by nlinarith
      nlinarith
    exact Subtype.ext (eq_zero_of_nrm_eq_zero νX hνX h hn0)
  have hSsurj : Function.Surjective S := LinearMap.injective_iff_surjective.mp hSinj
  obtain ⟨⟨f, hf⟩, hSf⟩ := hSsurj ⟨u - A v, VX.sub_mem hu (hAV v hv)⟩
  have hf_eq : f - T f = u - A v := by
    have := hSapply ⟨f, hf⟩
    rw [hSf] at this
    exact this.symm
  have hgV : v - B f ∈ VY := VY.sub_mem hv (hBV f hf)
  have hTf : T f = A (B f) := rfl
  have hfu' : f + A (v - B f) = u := by
    rw [map_sub, ← hTf]
    calc f + (A v - T f) = (f - T f) + A v := by abel
      _ = (u - A v) + A v := by rw [hf_eq]
      _ = u := by abel
  have hfu : ∀ x, f x + A (v - B f) x = u x := fun x => congrFun hfu' x
  have hgv : ∀ y, (v - B f) y + B f y = v y := by
    intro y
    simp only [Pi.sub_apply, sub_add_cancel]
  have hffix : f = (u - A v) + (A ∘ₗ B) f := by
    rw [← hf_eq, ← hT]
    abel
  have hgfix : v - B f = (v - B u) + (B ∘ₗ A) (v - B f) := by
    have hf' : f = u - A (v - B f) := by
      rw [← hfu']
      abel
    conv_lhs => rw [hf']
    rw [map_sub, LinearMap.comp_apply]
    abel
  refine ⟨f, hf, v - B f, hgV, hVX0 f hf, hVY0 _ hgV, hfu, hgv,
    fun N => neumann_split A B f _ hffix N, fun N => neumann_split B A _ _ hgfix N,
    fun N hN => ⟨fun x => ?_, fun y => ?_⟩⟩
  · exact neumann_sup_le νX νY A B VX VY hAV hBV hρI hρI1 hAρ hBρ hK hAK hAM hBM u v hUu hUv
      he1 f hf hffix N hN x
  · exact neumann_sup_le νY νX B A VY VX hBV hAV hρI hρI1 hBρ hAρ hK hBK hBM hAM v u hUv hUu
      he2 _ hgV hgfix N hN y

end Sarkozy.Structured
