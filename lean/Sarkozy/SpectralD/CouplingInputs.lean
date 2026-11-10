module

public import Sarkozy.SpectralD.CouplingBlock

@[expose] public section

/-!
# Inputs of `lem:spec2:paley`(b) and `cor:spec2:coupling` from WP-K's lemmas

`paper/sections/14_spectral.tex`, `subsec:spec:coupling`. The numbers taken as hypotheses in
`PaleyB.paley_b` and `PaleyB.coupling_M_first` come from the following, for coupling data
`D` (`def:coupling-data`):

* `Γ_E = Ê²` (`gammaE_of_deviation`): `lem:spec2:paley`(a) (`SpectralC.paley_deviation`) at
  every `x ∈ 𝓘⁺`, with the counts of `lem:extension`(coarse) as a hypothesis;
* `H̃ ⪯ 𝐇 + ε_H I` (`hHt_of_normLe`): `lem:spec2:gram` (`SpectralC.gram_comparison`, which
  gives `‖H̃ − 𝐇‖ ≤ ε'_H + ε_X`);
* the pivot densities (`pivot_of_density`): `D_j = R_ν D⁰_j` from a pivot bound `D⁰_j/p` under
  the half law `μ` (`lem:graphs:vertex`(dens) with `lem:extension`(coarse), a hypothesis) and
  the density ratio `R_ν` of `def:coupling-data`(i), when `μ` lives on `𝓘⁺`;
* `ζ̄ = 1` is always admissible (`tJ_le_one_mul`), since `|t_J| ≤ r`;
* `λ̄(𝐇)`, `Λ₊`, `Λ_nc` from row-sum certificates (`qform_re_le_of_rowsum`, `hplus_of_rowsum`,
  `hnc_of_rowsum`, with the matrix `hncM` of `𝐇^nc`).

**Non-vacuity** (`paley_b_sanity`): for every probability law `ν` and every family `P`, the
hypotheses of `paley_b` hold with explicit constants (`Γ_E = E_ν∑_k‖E_k‖²`,
`Λ_H = E_ν∑_k‖Ψ_k‖²`, `D_j = p`, `θ = (p − 1)^{1/2}`, `ρ = (∑_l(2^{r_l} − 1))²`), so its
hypotheses are never contradictory; the conclusion is then a valid unconditional (weak) bound.

New material for this paper.
-/

namespace Sarkozy.SpectralD.PaleyB

open Finset Complex Sarkozy.Characters Sarkozy.SpectralC
open scoped BigOperators ComplexConjugate

variable {p : ℕ} [Fact p.Prime] {U : Type*} [Fintype U] [DecidableEq U]

/-- **`Γ_E = Ê²` is admissible** (`lem:spec2:paley`(a), averaged): for coupling data with the
counts `|Φ_k(x)| ∈ p2^{-r_k}[1 ± ê_k]` of `lem:extension`(coarse) on `𝓘⁺`,
`E_ν‖∑_k w_kE_k‖² ≤ Ê²|w|²`. -/
theorem gammaE_of_deviation {N : U → Finset U} {ς : U → U → ZMod p}
    {Iplus : Finset (U → ZMod p)} {μ : (U → ZMod p) → ℝ} (D : CouplingData p U N ς Iplus μ)
    (hς : ∀ k, ∀ j ∈ N k, ς j k ≠ 0) (ehat : U → ℝ) (he0 : ∀ k, 0 ≤ ehat k)
    (he1 : ∀ k, ehat k < 1)
    (hcount : ∀ x ∈ Iplus, ∀ k, (p : ℝ) / 2 ^ (N k).card * (1 - ehat k) ≤
      (allowedSet N ς k x).card ∧
      ((allowedSet N ς k x).card : ℝ) ≤ (p : ℝ) / 2 ^ (N k).card * (1 + ehat k))
    (w : U → ℂ) :
    ∑ x, D.ν x * l2sq (fun a => ∑ k, w k * ((p : ℂ) * (D.P k x a : ℂ) - starProd N ς k x a)) ≤
      (∑ k, ((2 : ℝ) ^ (N k).card * (1 + ehat k) * devConst (D.Rp k) (ehat k) ^ 2 +
        (Fintype.card U : ℝ) * 4 ^ (N k).card / p)) * ∑ k, ‖w k‖ ^ 2 := by
  set Γ := ∑ k, ((2 : ℝ) ^ (N k).card * (1 + ehat k) * devConst (D.Rp k) (ehat k) ^ 2 +
    (Fintype.card U : ℝ) * 4 ^ (N k).card / p)
  calc ∑ x, D.ν x * l2sq (fun a => ∑ k, w k * ((p : ℂ) * (D.P k x a : ℂ) -
        starProd N ς k x a))
      ≤ ∑ x, D.ν x * (Γ * ∑ k, ‖w k‖ ^ 2) := by
        refine sum_le_sum fun x _ => ?_
        by_cases hx : x ∈ Iplus
        · exact mul_le_mul_of_nonneg_left (paley_deviation N ς hς x (fun k a => D.P k x a)
            (fun k a ha => D.P_supp k x hx a ha) D.Rp D.Rp_ge (fun k a ha => D.P_dens k x hx a ha)
            ehat he0 he1 (hcount x hx) w) (D.ν_nonneg x)
        · rw [D.ν_supp x hx, zero_mul, zero_mul]
    _ = Γ * ∑ k, ‖w k‖ ^ 2 := by rw [← sum_mul, couplingData_sum_ν D, one_mul]

/-- **`H̃ ⪯ 𝐇 + ε_H I`** from `‖H̃ − 𝐇‖ ≤ ε_H` (the form of `SpectralC.gram_comparison`,
`lem:spec2:gram`): the hypothesis `hHt` of `coupling_M_first`. -/
theorem hHt_of_normLe {ν : (U → ZMod p) → ℝ} {P : U → (U → ZMod p) → ZMod p → ℝ}
    {N : U → Finset U} {ς : U → U → ZMod p} {εH : ℝ}
    (h : NormLe (fun k l => gramΓ ν (psiField P) k l - (modelH N ς k l : ℂ)) εH) (w : U → ℂ) :
    (qform (gramΓ ν (psiField P)) w).re ≤ (qform (modelHC N ς) w).re + εH * ∑ k, ‖w k‖ ^ 2 :=
  re_qform_le_of_normLe h w

/-- The density bound of `def:coupling-data`(i) holds everywhere when the half law `μ` lives on
`𝓘⁺` (as `μ = λ_p(G⁺)` does). -/
lemma dens_everywhere {N : U → Finset U} {ς : U → U → ZMod p}
    {Iplus : Finset (U → ZMod p)} {μ : (U → ZMod p) → ℝ} (D : CouplingData p U N ς Iplus μ)
    (hμI : ∀ x, x ∉ Iplus → μ x = 0) (x : U → ZMod p) :
    D.dens_c * μ x ≤ D.ν x ∧ D.ν x ≤ D.dens_R * D.dens_c * μ x := by
  by_cases hx : x ∈ Iplus
  · exact D.dens x hx
  · rw [hμI x hx, D.ν_supp x hx]; simp

/-- **The pivot densities** (`lem:spec2:paley`(b), the bound on `max ν_j`): if under the half
law `μ` every conditional probability of `x_j` is at most `D⁰_j/p` (the paper: `x_j` is
uniform on at least `p2^{-d⁰_j}(1 − e_{d⁰_j}(p, n))` values, `lem:graphs:vertex`(dens) and
`lem:extension`(coarse)), then under `ν` it is at most `R_ν D⁰_j/p`. This is the hypothesis
`hpiv` of `paley_b` with `D_j = R_ν D⁰_j`. -/
theorem pivot_of_density {N : U → Finset U} {ς : U → U → ZMod p}
    {Iplus : Finset (U → ZMod p)} {μ : (U → ZMod p) → ℝ} (D : CouplingData p U N ς Iplus μ)
    (hμ0 : ∀ x, 0 ≤ μ x) (hμI : ∀ x, x ∉ Iplus → μ x = 0) (D0 : U → ℝ)
    (hμpiv : ∀ j x t, μ x ≠ 0 → condLaw μ j x t ≤ D0 j / p) :
    ∀ j x t, D.ν x ≠ 0 → condLaw D.ν j x t ≤ D.dens_R * D0 j / p := by
  intro j x t hx
  have hR0 : 0 ≤ D.dens_R := le_trans zero_le_one D.dens_R_ge
  have hμx : μ x ≠ 0 := by
    intro h0
    apply hx
    have h2 := (dens_everywhere D hμI x).2
    have h1 := (dens_everywhere D hμI x).1
    rw [h0, mul_zero] at h1 h2
    exact le_antisymm h2 (D.ν_nonneg x)
  calc condLaw D.ν j x t ≤ D.dens_R * condLaw μ j x t :=
        condLaw_le_of_density μ D.ν hμ0 D.dens_c_pos hR0 (dens_everywhere D hμI) j x t
    _ ≤ D.dens_R * (D0 j / p) := mul_le_mul_of_nonneg_left (hμpiv j x t hμx) hR0
    _ = D.dens_R * D0 j / p := by ring

/-- `ζ̄ = 1` is always admissible in `coupling_M_first` (`|t_J| ≤ r`, `lem:spec2:paley`(c)). -/
theorem tJ_le_one_mul (hp2 : p ≠ 2) (ν : (U → ZMod p) → ℝ) (hν0 : ∀ x, 0 ≤ ν x)
    (hν1 : ∑ x, ν x = 1) (J : Finset U) : ‖tJ ν J‖ ≤ 1 * rp p := by
  rw [one_mul]; exact norm_tJ_le hp2 ν hν0 hν1 J

/-! ## Non-vacuity of the hypotheses of `paley_b` -/

omit [DecidableEq U] in
/-- `‖∑_k w_k f_k‖² ≤ |w|² ∑_k ‖f_k‖²`. -/
lemma l2sq_comb_le (w : U → ℂ) (f : U → ZMod p → ℂ) :
    l2sq (fun a => ∑ k, w k * f k a) ≤ (∑ k, ‖w k‖ ^ 2) * ∑ k, l2sq (f k) := by
  have hpt : ∀ a, ‖∑ k, w k * f k a‖ ^ 2 ≤ (∑ k, ‖w k‖ ^ 2) * ∑ k, ‖f k a‖ ^ 2 := by
    intro a
    have h1 : ‖∑ k, w k * f k a‖ ≤ ∑ k, ‖w k‖ * ‖f k a‖ := by
      refine (norm_sum_le _ _).trans (le_of_eq ?_)
      exact sum_congr rfl fun k _ => norm_mul _ _
    calc ‖∑ k, w k * f k a‖ ^ 2 ≤ (∑ k, ‖w k‖ * ‖f k a‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h1 2
      _ ≤ _ := sum_mul_sq_le_sq_mul_sq univ (fun k => ‖w k‖) (fun k => ‖f k a‖)
  unfold l2sq
  have hp : (0 : ℝ) ≤ (p : ℝ)⁻¹ := by positivity
  calc (p : ℝ)⁻¹ * ∑ a, ‖∑ k, w k * f k a‖ ^ 2
      ≤ (p : ℝ)⁻¹ * ∑ a, (∑ k, ‖w k‖ ^ 2) * ∑ k, ‖f k a‖ ^ 2 :=
        mul_le_mul_of_nonneg_left (sum_le_sum fun a _ => hpt a) hp
    _ = (∑ k, ‖w k‖ ^ 2) * ∑ k, (p : ℝ)⁻¹ * ∑ a, ‖f k a‖ ^ 2 := by
        simp only [mul_sum]
        rw [sum_comm]
        exact sum_congr rfl fun k _ => sum_congr rfl fun a _ => by ring

/-- **Non-vacuity of `paley_b`**: for every probability law `ν` and every family `P`, all the
hypotheses of `paley_b` hold with explicit constants, so `paley_b` applies unconditionally
(with these, weaker, constants). -/
theorem paley_b_sanity (hp2 : p ≠ 2) (N : U → Finset U) (ς : U → U → ZMod p)
    (ν : (U → ZMod p) → ℝ) (hν0 : ∀ x, 0 ≤ ν x) (hν1 : ∑ x, ν x = 1)
    (P : U → (U → ZMod p) → ZMod p → ℝ) (w : U → ℂ) :
    ‖qform (gramP ν (psiField P)) w - ∑ J ∈ univ.filter (fun J : Finset U => 2 ≤ J.card),
        tJ ν J * ((‖∑ k, epsJ N ς J k * w k‖ ^ 2 : ℝ) : ℂ)‖ ≤
      rp p * (rp p * Real.sqrt ((p : ℝ) - 1) * (∑ l, ((2 : ℝ) ^ (N l).card - 1)) ^ 2 +
        (2 * Real.sqrt ((∑ x, ν x * ∑ k, l2sq (fun a => (p : ℂ) * (P k x a : ℂ) -
            starProd N ς k x a)) * (∑ x, ν x * ∑ k, l2sq (psiField P k x))) +
          ∑ x, ν x * ∑ k, l2sq (fun a => (p : ℂ) * (P k x a : ℂ) - starProd N ς k x a))) *
        ∑ k, ‖w k‖ ^ 2 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hl0 : ∀ h : ZMod p → ℂ, 0 ≤ l2sq h := fun h => l2sq_nonneg' h
  set ΓE := ∑ x, ν x * ∑ k, l2sq (fun a => (p : ℂ) * (P k x a : ℂ) - starProd N ς k x a)
  set ΛH := ∑ x, ν x * ∑ k, l2sq (psiField P k x)
  have hΓ0 : 0 ≤ ΓE := sum_nonneg fun x _ =>
    mul_nonneg (hν0 x) (sum_nonneg fun k _ => hl0 _)
  have hΛ0 : 0 ≤ ΛH := sum_nonneg fun x _ =>
    mul_nonneg (hν0 x) (sum_nonneg fun k _ => hl0 _)
  have hΓ : ∀ w : U → ℂ, ∑ x, ν x * l2sq (fun a => ∑ k, w k *
      ((p : ℂ) * (P k x a : ℂ) - starProd N ς k x a)) ≤ ΓE * ∑ k, ‖w k‖ ^ 2 := by
    intro w
    calc _ ≤ ∑ x, ν x * ((∑ k, ‖w k‖ ^ 2) *
          ∑ k, l2sq (fun a => (p : ℂ) * (P k x a : ℂ) - starProd N ς k x a)) :=
          sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (l2sq_comb_le w
            (fun k a => (p : ℂ) * (P k x a : ℂ) - starProd N ς k x a)) (hν0 x)
      _ = ΓE * ∑ k, ‖w k‖ ^ 2 := by
          rw [sum_mul]; exact sum_congr rfl fun x _ => by ring
  have hH : ∀ w : U → ℂ, (qform (gramΓ ν (psiField P)) w).re ≤ ΛH * ∑ k, ‖w k‖ ^ 2 := by
    intro w
    rw [re_qform_gramΓ_eq]
    calc _ ≤ ∑ x, ν x * ((∑ k, ‖w k‖ ^ 2) * ∑ k, l2sq (psiField P k x)) :=
          sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (l2sq_comb_le w
            (fun k a => psiField P k x a)) (hν0 x)
      _ = ΛH * ∑ k, ‖w k‖ ^ 2 := by
          rw [sum_mul]; exact sum_congr rfl fun x _ => by ring
  have hθ : ∀ _j : U, (p : ℝ) - 1 ≤ Real.sqrt ((p : ℝ) - 1) ^ 2 := fun _ => by
    rw [Real.sq_sqrt (by linarith)]
  have ha : ∀ k, (0 : ℝ) ≤ (2 : ℝ) ^ (N k).card - 1 := fun k => by
    have : (1 : ℝ) ≤ 2 ^ (N k).card := one_le_pow₀ (by norm_num)
    linarith
  have hρ : ∀ k, ((2 : ℝ) ^ (N k).card - 1) * ∑ l, ((2 : ℝ) ^ (N l).card - 1) ≤
      (∑ l, ((2 : ℝ) ^ (N l).card - 1)) ^ 2 := fun k => by
    rw [sq]
    exact mul_le_mul_of_nonneg_right
      (single_le_sum (f := fun l => (2 : ℝ) ^ (N l).card - 1) (fun l _ => ha l) (mem_univ k))
      (sum_nonneg fun l _ => ha l)
  exact paley_b hp2 N ς ν hν0 hν1 P hΓ0 hΛ0 hΓ hH (fun _ => (p : ℝ))
    (fun j x t hx => pivot_trivial ν hν0 j x t hx) (Real.sqrt_nonneg _) hθ hρ w

/-! ## Row-sum certificates for `λ̄`, `Λ_nc`, `Λ₊` -/

omit [DecidableEq U] in
/-- **The row-sum certificate** (`def:coupling-model`, "the maximal absolute row sum"): if
`|X_kl| ≤ B_kl` with `B` symmetric, nonnegative, with row sums at most `λ`, then
`Re(w^*Xw) ≤ λ|w|²`; this supplies `λ̄(𝐇)` (`hlam`), `Λ₊` (`hplus`, via `qform_hplusM_re`) and
`Λ_nc` (`hnc_of_rowsum`). -/
theorem qform_re_le_of_rowsum (X : U → U → ℂ) (B : U → U → ℝ) (hB0 : ∀ k l, 0 ≤ B k l)
    (hBsym : ∀ k l, B k l = B l k) (hXB : ∀ k l, ‖X k l‖ ≤ B k l) {lam : ℝ}
    (hrow : ∀ k, ∑ l, B k l ≤ lam) (w : U → ℂ) :
    (qform X w).re ≤ lam * ∑ k, ‖w k‖ ^ 2 := by
  have h := normLe_schur X B hB0 hBsym hXB hrow w w
  have e : bform X w w = qform X w := rfl
  rw [e, mul_assoc, show vnorm w * vnorm w = ∑ k, ‖w k‖ ^ 2 from
    Real.mul_self_sqrt (sum_nonneg fun _ _ => sq_nonneg _)] at h
  exact (Complex.re_le_norm _).trans h

variable (Adj : U → U → Prop) [DecidableRel Adj]

/-- `𝐇^nc = ∑_{J not cov} ε_Jε_Jᵀ` as a matrix. -/
noncomputable def hncM (N : U → Finset U) (ς : U → U → ZMod p) (k l : U) : ℂ :=
  ∑ J ∈ ncSets Adj, conj (epsJ N ς J k) * epsJ N ς J l

/-- `w^*𝐇^nc w = ∑_{J not cov} |ε_J·w|²` for the matrix `hncM`. -/
lemma qform_hncM (N : U → Finset U) (ς : U → U → ZMod p) (w : U → ℂ) :
    qform (hncM Adj N ς) w = (hncQ Adj N ς w : ℂ) := by
  have key : ∀ J, ((‖∑ k, epsJ N ς J k * w k‖ ^ 2 : ℝ) : ℂ) =
      ∑ k, ∑ l, conj (w k) * (conj (epsJ N ς J k) * epsJ N ς J l) * w l := by
    intro J
    rw [Complex.ofReal_pow, ← Complex.conj_mul', map_sum, sum_mul_sum]
    refine sum_congr rfl fun k _ => sum_congr rfl fun l _ => ?_
    rw [map_mul]
    ring
  calc qform (hncM Adj N ς) w = ∑ k, ∑ l, ∑ J ∈ ncSets Adj,
        conj (w k) * (conj (epsJ N ς J k) * epsJ N ς J l) * w l := by
        unfold qform hncM; simp only [mul_sum, sum_mul]
    _ = ∑ k, ∑ J ∈ ncSets Adj, ∑ l,
        conj (w k) * (conj (epsJ N ς J k) * epsJ N ς J l) * w l :=
        sum_congr rfl fun k _ => sum_comm
    _ = ∑ J ∈ ncSets Adj, ∑ k, ∑ l,
        conj (w k) * (conj (epsJ N ς J k) * epsJ N ς J l) * w l := sum_comm
    _ = ∑ J ∈ ncSets Adj, ((‖∑ k, epsJ N ς J k * w k‖ ^ 2 : ℝ) : ℂ) :=
        sum_congr rfl fun J _ => (key J).symm
    _ = (hncQ Adj N ς w : ℂ) := by unfold hncQ; push_cast; rfl

/-- `Λ_nc` from a row-sum certificate of `𝐇^nc` (the hypothesis `hnc` of `coupling_M_first`). -/
theorem hnc_of_rowsum (N : U → Finset U) (ς : U → U → ZMod p) (B : U → U → ℝ)
    (hB0 : ∀ k l, 0 ≤ B k l) (hBsym : ∀ k l, B k l = B l k)
    (hXB : ∀ k l, ‖hncM Adj N ς k l‖ ≤ B k l) {lam : ℝ} (hrow : ∀ k, ∑ l, B k l ≤ lam)
    (w : U → ℂ) : hncQ Adj N ς w ≤ lam * ∑ k, ‖w k‖ ^ 2 := by
  have h := qform_re_le_of_rowsum (hncM Adj N ς) B hB0 hBsym hXB hrow w
  rwa [qform_hncM, Complex.ofReal_re] at h

/-- `Λ₊` from a row-sum certificate of `𝐇⁺` (the hypothesis `hplus` of `coupling_M_first`). -/
theorem hplus_of_rowsum (N : U → Finset U) (ς : U → U → ZMod p) (B : U → U → ℝ)
    (hB0 : ∀ k l, 0 ≤ B k l) (hBsym : ∀ k l, B k l = B l k)
    (hXB : ∀ k l, ‖hplusM Adj N ς k l‖ ≤ B k l) {lam : ℝ} (hrow : ∀ k, ∑ l, B k l ≤ lam)
    (w : U → ℂ) :
    (qform (modelHC N ς) w).re + (if p % 4 = 1 then (1 : ℝ) else 0) * hcovQ Adj N ς w ≤
      lam * ∑ k, ‖w k‖ ^ 2 := by
  have h := qform_re_le_of_rowsum (hplusM Adj N ς) B hB0 hBsym hXB hrow w
  rwa [qform_hplusM_re] at h

end Sarkozy.SpectralD.PaleyB
