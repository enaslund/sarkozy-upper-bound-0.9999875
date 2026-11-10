module

public import Sarkozy.ClassData.Residuals

@[expose] public section

/-!
# K2's fields 42 (`errw`) and 44 (`MD.hV`) from bounds on the class data

`paper/sections/09_comparison_theorem.tex`, `def:robust`; `paper/sections/11_comparison_proof.tex`,
`cor:joint-closing`; `paper/sections/23_envelopes.tex`, `thm:envelopes`(i).

* **`errw_of_inputs`** (field 42, `ClassEnergySteps.errw`): with the error weights equal to the
  upper prices, `v = u` (the relative form of `lem:bracket-energy`), the error weights are
  dominated by the class prices with `errK = 3 · eUhi · K_π`, given the background gate of
  `ConsistentInputs` and a comparison `mono(y^arm) ≤ K_π π_ω` of the raw-arm and full monomials on
  the degree classes. The constant `3` bounds the sixteen caps `κ_H` (`κHQ_le`, the largest is
  `κ_H(6,0) ≈ 2.4548`).
* **`hV_of_bounds`** (field 44, `MeanData.hV`): `∑_j (63 w_j − b_j) v_j ≤ 63 N W V_v` from
  `|Θ_L| ≤ N`, `w ≤ W`, `0 ≤ v ≤ V_v`, `b ≥ 0`. For the paper's labelled diagonals `N = 192`.
-/

open Finset

namespace Sarkozy.ClassData

open Sarkozy.ClassBoundsPaper Sarkozy.ClassInputsPaper
open Sarkozy.RecordExpansion Sarkozy.RecordExpansion.Choice

/-- The sixteen caps `κ_H` are at most `3`. -/
theorem κHQ_le (i : ℕ) : κHQ i ≤ 3 := by
  unfold κHQ
  split <;> norm_num

variable {a : ℝ}
  {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

/-- **K2's field 42** (`ClassEnergySteps.errw`, `def:robust`) with `v = u`: from the background
gate of `ConsistentInputs` and `mono(y^arm)_ω ≤ K_π π_ω` on the degree classes,
`∑_j wc_{ij} u_j ≤ (3 eUhi K_π) ∑_{𝒞_i} π_ω` for every class (on a variance class the left side is
`0`). *Hypothesis* `hyπ`: a price comparison (it holds with `K_π = 1` when every raw-arm price is at
most the full price of its record). -/
theorem errw_of_inputs {D : TheoremCBlock.ComparisonData a m₀ blk p pr h E}
    {cd : ClassInputsPaper.ClassData D.CL} {Θ : ℕ → Type} [∀ L, Fintype (Θ L)]
    {wc : ∀ L, cd.ι L → Θ L → ℝ} {u : ∀ L, Θ L → ℝ} {ρ : ∀ L, Choice (D.CL.T L) → ℝ}
    (H : ConsistentInputs cd Θ wc u ρ) (Kπ : ℝ) (hK : 0 ≤ Kπ)
    (hyπ : ∀ L (n : {n // n ∈ cd.N}), ∀ ω ∈ cd.clsSel L (.inl n),
      mono (cd.yarm L) (selMono ω) ≤ Kπ * monomial (D.CL.π L) ω) (L : ℕ) (i : cd.ι L) :
    ∑ j, wc L i j * u L j ≤ (3 * (eUhi : ℝ) * Kπ) * ∑ ω ∈ cd.clsSel L i, monomial (D.CL.π L) ω := by
  have hmono : ∀ ω : Choice (D.CL.T L), 0 ≤ monomial (D.CL.π L) ω :=
    monomial_nonneg (cd.π_nonneg L)
  have hS0 : 0 ≤ ∑ ω ∈ cd.clsSel L i, monomial (D.CL.π L) ω := sum_nonneg fun ω _ => hmono ω
  have heU : (0 : ℝ) ≤ eUhi := (Real.exp_pos _).le.trans exp_U0_le
  rcases i with n | v
  · have hbg := H.hbg L n
    obtain ⟨hb0, hb, -, -⟩ := paper_classCost_gates (H.hN n.1 n.2)
    have hA0 : 0 ≤ ∑ ω ∈ cd.clsSel L (.inl n), mono (cd.yarm L) (selMono ω) :=
      sum_nonneg fun ω _ => mono_nonneg (cd.yarm_nonneg L) _
    have hA : ∑ ω ∈ cd.clsSel L (.inl n), mono (cd.yarm L) (selMono ω) ≤
        Kπ * ∑ ω ∈ cd.clsSel L (.inl n), monomial (D.CL.π L) ω := by
      rw [mul_sum]
      exact sum_le_sum fun ω hω => hyπ L n ω hω
    have hκ3 : paperκH n.1 ≤ 3 := by
      unfold paperκH
      exact_mod_cast κHQ_le _
    have hκ0 : 0 ≤ paperκH n.1 := hb0.trans hb
    have hc : paperκH n.1 * Real.exp paperU0 - (paperκH n.1 - paperκb n.1) * Real.exp paperTU ≤
        3 * eUhi := by
      have h1 : 0 ≤ (paperκH n.1 - paperκb n.1) * Real.exp paperTU :=
        mul_nonneg (by linarith) (Real.exp_pos _).le
      have h2 : paperκH n.1 * Real.exp paperU0 ≤ 3 * eUhi :=
        mul_le_mul hκ3 exp_U0_le (Real.exp_pos _).le (by norm_num)
      linarith
    calc ∑ j, wc L (.inl n) j * u L j
        ≤ (paperκH n.1 * Real.exp paperU0 - (paperκH n.1 - paperκb n.1) * Real.exp paperTU) *
          ∑ ω ∈ cd.clsSel L (.inl n), mono (cd.yarm L) (selMono ω) := hbg
      _ ≤ (3 * eUhi) * ∑ ω ∈ cd.clsSel L (.inl n), mono (cd.yarm L) (selMono ω) :=
          mul_le_mul_of_nonneg_right hc hA0
      _ ≤ (3 * eUhi) * (Kπ * ∑ ω ∈ cd.clsSel L (.inl n), monomial (D.CL.π L) ω) :=
          mul_le_mul_of_nonneg_left hA (by positivity)
      _ = (3 * (eUhi : ℝ) * Kπ) * ∑ ω ∈ cd.clsSel L (.inl n), monomial (D.CL.π L) ω := by ring
  · simp only [H.hwc L v, zero_mul, sum_const_zero]
    exact mul_nonneg (by positivity) hS0

/-- **K2's field 44** (`MeanData.hV`, the gate on the error weights) from uniform bounds:
`∑_j (63 w_j − b_j) v_j ≤ 63 N W V_v` when `|Θ_L| ≤ N`, `w_j ≤ W`, `0 ≤ v_j ≤ V_v`, `0 ≤ b_j`. -/
theorem hV_of_bounds {Θ : ℕ → Type} [∀ L, Fintype (Θ L)] (w b v : ∀ L, Θ L → ℝ) (N : ℕ)
    (W Vv : ℝ) (hW : 0 ≤ W) (hVv : 0 ≤ Vv) (hcard : ∀ L, Fintype.card (Θ L) ≤ N)
    (hw : ∀ L j, w L j ≤ W) (hb : ∀ L j, 0 ≤ b L j) (hv0 : ∀ L j, 0 ≤ v L j)
    (hv : ∀ L j, v L j ≤ Vv) (L : ℕ) :
    ∑ j, (63 * w L j - b L j) * v L j ≤ 63 * N * W * Vv := by
  have hterm : ∀ j, (63 * w L j - b L j) * v L j ≤ 63 * W * Vv := by
    intro j
    have h1 : (63 * w L j - b L j) * v L j ≤ 63 * w L j * v L j := by
      nlinarith [mul_nonneg (hb L j) (hv0 L j)]
    have h2 : w L j * v L j ≤ W * Vv :=
      (mul_le_mul_of_nonneg_right (hw L j) (hv0 L j)).trans
        (mul_le_mul_of_nonneg_left (hv L j) hW)
    linarith
  calc ∑ j, (63 * w L j - b L j) * v L j ≤ ∑ _j : Θ L, 63 * W * Vv := sum_le_sum fun j _ => hterm j
    _ = (Fintype.card (Θ L) : ℝ) * (63 * W * Vv) := by
        rw [sum_const, nsmul_eq_mul, card_univ]
    _ ≤ (N : ℝ) * (63 * W * Vv) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hcard L) (by positivity)
    _ = 63 * N * W * Vv := by ring

end Sarkozy.ClassData
