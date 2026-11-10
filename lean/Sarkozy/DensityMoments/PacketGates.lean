module

public import Sarkozy.Certificates.Exponential
public import Sarkozy.DensityUpgrade.PacketsGates

/-!
# The middle packet gates of `lem:density:packets` (`cert:density:packets`): checks and soundness

`paper/sections/31_density_induction_upgrade.tex`, proof of `lem:density:packets`, and
`lem:density:joint-block-gate`. For a middle piece with assigned coefficients
`v_R, v_D, w_R, v_C, w_C, f_1, h_1` and start `X` (`PieceData`), and `r = b^{-1/2}`, the
symmetric and skew bad fractions, after division by `r³`, are

* `sym r = (A r + B(r) r²)/(c + d r + A r + B(r) r²)`, `A = 2 v_C`, `B(r) = 2 w_C/(1-r²)²`,
  `c = 6 v_R + 2 v_D (f_1 + h_1)`, `d = w_R g_S(X)`;
* `skew r = x/(K + x)`, `x = 2 w_C r/(1 - r²)`, `K = w_R g_A(X)`,

with `g_S(X) = 20/((1-2/X)(1-3/X)) + 4/(1-2/X) + 2/(1-1/X)` and
`g_A(X) = 4(1 + 8/⌊√X⌋)/((1-2/X)(1-3/X)) + 2/(1-1/X)` (the checker's formulas; they reproduce
the source's exact fractions). The joint gate `eq:density:joint-block-gate` at a least prime
`β` and log bound `L` is `t (1 + C(L)) < 1` with
`C(L) = (e^{L(θ_*-1)} - 1)/(κ_* - e^{-L(1-κ_*)})`.

* `GateRow.Check`: the rational certificate of one gate: `r_b ≥ β^{-1/2}` (`r_b² β ≥ 1`),
  exponential witnesses (`Certificates.ExpWitness`) for `e^{L(θ_*-1)}` from above and
  `e^{L(1-κ_*)}` from below, and the two gates at `r_b` with the resulting bound on `C(L)`.
* `GateRow.sound`: the check implies, for every real `0 < r ≤ r_b` (every least prime
  `b ≥ β`), `κ_* > e^{-L(1-κ_*)}` and both gates `sym r (1 + C(L)) < 1`, `skew r (1 + C(L)) < 1`.
  Monotonicity in `r` is WP-P's `packets_ratio_mono` and `packets_skew_mono`.
* `CoarseRow.Check`, `CoarseRow.sound`: the coarse bad fractions
  `eq:density:middle-bad-fractions` at the piece starts.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.DensityMoments

open Sarkozy.Certificates

/-- `θ_* = 1014587/10^6`. -/
def thetaStar : ℚ := 1014587 / 1000000

/-- `κ_* = 98861/10^5`. -/
def kappaStar : ℚ := 98861 / 100000

instance (w : ExpWitness) (q : ℚ) (I : Interval) : Decidable (w.Valid q I) := by
  unfold ExpWitness.Valid
  infer_instance

/-- The assigned coefficients of one middle piece. -/
structure PieceData where
  X : ℕ
  sqrtX : ℕ
  vR : ℚ
  vD : ℚ
  wR : ℚ
  vC : ℚ
  wC : ℚ
  f : ℚ
  h : ℚ
  deriving DecidableEq, Inhabited

namespace PieceData

variable (P : PieceData)

def gS : ℚ := 20 / ((1 - 2 / (P.X : ℚ)) * (1 - 3 / (P.X : ℚ))) + 4 / (1 - 2 / (P.X : ℚ)) +
  2 / (1 - 1 / (P.X : ℚ))

def gA : ℚ := 4 * (1 + 8 / (P.sqrtX : ℚ)) / ((1 - 2 / (P.X : ℚ)) * (1 - 3 / (P.X : ℚ))) +
  2 / (1 - 1 / (P.X : ℚ))

def A : ℚ := 2 * P.vC
def c : ℚ := 6 * P.vR + 2 * P.vD * (P.f + P.h)
def d : ℚ := P.wR * P.gS
def K : ℚ := P.wR * P.gA

/-- The symmetric bad fraction (divided by `r³`), rational. -/
def symQ (r : ℚ) : ℚ :=
  (P.A * r + 2 * P.wC / (1 - r ^ 2) ^ 2 * r ^ 2) /
    (P.c + P.d * r + P.A * r + 2 * P.wC / (1 - r ^ 2) ^ 2 * r ^ 2)

/-- The skew bad fraction, rational. -/
def skewQ (r : ℚ) : ℚ := (2 * P.wC * r / (1 - r ^ 2)) / (P.K + 2 * P.wC * r / (1 - r ^ 2))

/-- The symmetric bad fraction, real. -/
noncomputable def sym (r : ℝ) : ℝ :=
  ((P.A : ℝ) * r + 2 * (P.wC : ℝ) / (1 - r ^ 2) ^ 2 * r ^ 2) /
    ((P.c : ℝ) + (P.d : ℝ) * r + (P.A : ℝ) * r + 2 * (P.wC : ℝ) / (1 - r ^ 2) ^ 2 * r ^ 2)

/-- The skew bad fraction, real. -/
noncomputable def skew (r : ℝ) : ℝ :=
  (2 * (P.wC : ℝ) * r / (1 - r ^ 2)) / ((P.K : ℝ) + 2 * (P.wC : ℝ) * r / (1 - r ^ 2))

theorem cast_symQ (r : ℚ) : ((P.symQ r : ℚ) : ℝ) = P.sym (r : ℝ) := by
  unfold symQ sym
  push_cast
  ring

theorem cast_skewQ (r : ℚ) : ((P.skewQ r : ℚ) : ℝ) = P.skew (r : ℝ) := by
  unfold skewQ skew
  push_cast
  ring

/-- Signs of the coefficients. -/
def Valid : Prop := 0 ≤ P.A ∧ 0 ≤ P.wC ∧ 0 < P.c ∧ 0 ≤ P.d ∧ 0 < P.K

instance : Decidable P.Valid := by unfold Valid; infer_instance

/-- **Monotonicity in `r`**: for `0 < r ≤ r' < 1`, both fractions at `r` are at most those at
`r'` (`packets_ratio_mono`, `packets_skew_mono`). -/
theorem sym_mono (hP : P.Valid) {r r' : ℝ} (hr : 0 < r) (hrr : r ≤ r') (hr1 : r' < 1) :
    P.sym r ≤ P.sym r' := by
  obtain ⟨hA, hw, hc, hd, _⟩ := hP
  have hA' : (0 : ℝ) ≤ P.A := by exact_mod_cast hA
  have hw' : (0 : ℝ) ≤ P.wC := by exact_mod_cast hw
  have hc' : (0 : ℝ) < P.c := by exact_mod_cast hc
  have hd' : (0 : ℝ) ≤ P.d := by exact_mod_cast hd
  have h1 : 0 < 1 - r ^ 2 := by nlinarith
  have h1' : 0 < 1 - r' ^ 2 := by nlinarith
  have hsq : (1 - r' ^ 2) ^ 2 ≤ (1 - r ^ 2) ^ 2 := by
    apply pow_le_pow_left₀ h1'.le
    nlinarith
  have hB : 0 ≤ 2 * (P.wC : ℝ) / (1 - r ^ 2) ^ 2 := by positivity
  have hBB : 2 * (P.wC : ℝ) / (1 - r ^ 2) ^ 2 ≤ 2 * (P.wC : ℝ) / (1 - r' ^ 2) ^ 2 :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) hsq
  exact DensityUpgrade.packets_ratio_mono hA' hc'.le hd' hr hrr (by positivity) hB hBB

theorem skew_mono (hP : P.Valid) {r r' : ℝ} (hr : 0 < r) (hrr : r ≤ r') (hr1 : r' < 1) :
    P.skew r ≤ P.skew r' := by
  obtain ⟨_, hw, _, _, hK⟩ := hP
  have hw' : (0 : ℝ) ≤ P.wC := by exact_mod_cast hw
  have hK' : (0 : ℝ) < P.K := by exact_mod_cast hK
  have h1 : 0 < 1 - r ^ 2 := by nlinarith
  exact DensityUpgrade.packets_skew_mono hw' hK'.le hr hrr hr1 (by positivity)

end PieceData

/-- The bound on the exact mixture coefficient at `Q = e^L`, `eq:density:joint-block-gate`. -/
noncomputable def mixtureBound (L : ℝ) : ℝ :=
  (Real.exp (L * ((thetaStar : ℝ) - 1)) - 1) /
    ((kappaStar : ℝ) - Real.exp (-(L * (1 - (kappaStar : ℝ)))))

/-- One joint gate: the piece, the least-prime lower bound `β`, a rational `r_b ≥ β^{-1/2}`, the
log bound `L`, and two exponential witnesses. -/
structure GateRow where
  piece : ℕ
  beta : ℕ
  rb : ℚ
  L : ℚ
  w1 : ExpWitness
  w2 : ExpWitness
  deriving DecidableEq

namespace GateRow

variable (row : GateRow)

def U : ℚ := row.w1.upper ^ row.w1.divisions
def W : ℚ := row.w2.lower ^ row.w2.divisions
def Cbar : ℚ := (row.U - 1) / (kappaStar - 1 / row.W)

/-- **The rational certificate of one joint gate.** -/
def Check (P : PieceData) : Prop :=
  0 < row.rb ∧ row.rb < 1 ∧ 1 ≤ row.rb ^ 2 * (row.beta : ℚ) ∧ 0 ≤ row.L ∧
    row.w1.Valid (row.L * (thetaStar - 1)) ⟨row.w1.lower ^ row.w1.divisions, row.U⟩ ∧
    row.w2.Valid (row.L * (1 - kappaStar)) ⟨row.W, row.w2.upper ^ row.w2.divisions⟩ ∧
    1 < kappaStar * row.W ∧ P.symQ row.rb * (1 + row.Cbar) < 1 ∧
    P.skewQ row.rb * (1 + row.Cbar) < 1

instance (P : PieceData) : Decidable (row.Check P) := by unfold Check; infer_instance

/-- **Soundness of a joint gate**: for every real `0 < r ≤ r_b`, `κ_* > e^{-L(1-κ_*)}` and both
gates `t (1 + C(L)) < 1` hold. -/
theorem sound {P : PieceData} (hP : P.Valid) (h : row.Check P) {r : ℝ} (hr : 0 < r)
    (hrr : r ≤ row.rb) :
    Real.exp (-((row.L : ℝ) * (1 - (kappaStar : ℝ)))) < kappaStar ∧
      P.sym r * (1 + mixtureBound row.L) < 1 ∧ P.skew r * (1 + mixtureBound row.L) < 1 := by
  obtain ⟨hrb0, hrb1, _, hL, hw1, hw2, hκW, hsym, hskew⟩ := h
  have he1 := (ExpWitness.sound hw1).2
  have he2 := (ExpWitness.sound hw2).1
  simp only at he1 he2
  have hθ : (thetaStar : ℝ) - 1 ≥ 0 := by norm_num [thetaStar]
  have hκ1 : (0 : ℝ) ≤ 1 - (kappaStar : ℝ) := by norm_num [kappaStar]
  have hL' : (0 : ℝ) ≤ row.L := by exact_mod_cast hL
  -- the exponentials
  have hE1 : Real.exp ((row.L : ℝ) * ((thetaStar : ℝ) - 1)) ≤ (row.U : ℝ) := by
    have : ((row.L * (thetaStar - 1) : ℚ) : ℝ) = (row.L : ℝ) * ((thetaStar : ℝ) - 1) := by
      push_cast; ring
    rw [← this]
    exact he1
  have hE2 : (row.W : ℝ) ≤ Real.exp ((row.L : ℝ) * (1 - (kappaStar : ℝ))) := by
    have : ((row.L * (1 - kappaStar) : ℚ) : ℝ) = (row.L : ℝ) * (1 - (kappaStar : ℝ)) := by
      push_cast; ring
    rw [← this]
    exact he2
  have hκ0 : (0 : ℝ) < kappaStar := by norm_num [kappaStar]
  have hκW' : (1 : ℝ) < (kappaStar : ℝ) * row.W := by exact_mod_cast hκW
  have hW0 : (0 : ℝ) < row.W := by
    by_contra hcon
    push Not at hcon
    nlinarith
  have hexpneg : Real.exp (-((row.L : ℝ) * (1 - (kappaStar : ℝ)))) ≤ 1 / (row.W : ℝ) := by
    rw [Real.exp_neg, one_div]
    exact inv_anti₀ hW0 hE2
  have hinvW : 1 / (row.W : ℝ) < kappaStar := by
    rw [div_lt_iff₀ hW0]
    linarith
  have hden : 0 < (kappaStar : ℝ) - 1 / (row.W : ℝ) := by linarith
  -- the mixture bound
  have hnum0 : 0 ≤ Real.exp ((row.L : ℝ) * ((thetaStar : ℝ) - 1)) - 1 := by
    have := Real.add_one_le_exp ((row.L : ℝ) * ((thetaStar : ℝ) - 1))
    nlinarith [mul_nonneg hL' hθ]
  have hC : mixtureBound row.L ≤ (row.Cbar : ℝ) := by
    unfold mixtureBound Cbar
    push_cast
    apply div_le_div₀ (by linarith) (by linarith) hden (by linarith)
  have hC0 : 0 ≤ mixtureBound row.L := by
    unfold mixtureBound
    exact div_nonneg hnum0 (by linarith)
  have hrb1' : ((row.rb : ℚ) : ℝ) < 1 := by exact_mod_cast hrb1
  have hsym' : ((P.symQ row.rb * (1 + row.Cbar) : ℚ) : ℝ) < 1 := by exact_mod_cast hsym
  have hskew' : ((P.skewQ row.rb * (1 + row.Cbar) : ℚ) : ℝ) < 1 := by exact_mod_cast hskew
  push_cast at hsym' hskew'
  rw [P.cast_symQ] at hsym'
  rw [P.cast_skewQ] at hskew'
  have hs0 : 0 ≤ P.sym r := by
    obtain ⟨hA, hw, hc, hd, _⟩ := hP
    have hA' : (0 : ℝ) ≤ P.A := by exact_mod_cast hA
    have hw' : (0 : ℝ) ≤ P.wC := by exact_mod_cast hw
    have hc' : (0 : ℝ) < P.c := by exact_mod_cast hc
    have hd' : (0 : ℝ) ≤ P.d := by exact_mod_cast hd
    unfold PieceData.sym
    apply div_nonneg <;> positivity
  have hk0 : 0 ≤ P.skew r := by
    obtain ⟨_, hw, _, _, hK⟩ := hP
    have hw' : (0 : ℝ) ≤ P.wC := by exact_mod_cast hw
    have hK' : (0 : ℝ) < P.K := by exact_mod_cast hK
    have h1 : 0 < 1 - r ^ 2 := by nlinarith
    unfold PieceData.skew
    apply div_nonneg <;> positivity
  have hsm := P.sym_mono hP hr hrr hrb1'
  have hkm := P.skew_mono hP hr hrr hrb1'
  refine ⟨lt_of_le_of_lt hexpneg hinvW, ?_, ?_⟩
  · calc P.sym r * (1 + mixtureBound row.L) ≤ P.sym (row.rb : ℝ) * (1 + (row.Cbar : ℝ)) :=
          mul_le_mul hsm (by linarith) (by linarith) (hs0.trans hsm)
      _ < 1 := hsym'
  · calc P.skew r * (1 + mixtureBound row.L) ≤ P.skew (row.rb : ℝ) * (1 + (row.Cbar : ℝ)) :=
          mul_le_mul hkm (by linarith) (by linarith) (hk0.trans hkm)
      _ < 1 := hskew'

/-- The certified value of a gate: `max(sym, skew)(r_b) · (1 + C̄)`. -/
def value (row : GateRow) (P : PieceData) : ℚ := max (P.symQ row.rb) (P.skewQ row.rb) * (1 + row.Cbar)

/-- **The certified gate values**: under the check, for `0 < r ≤ r_b` both real gates are at
most `row.value P`. -/
theorem sound_le {P : PieceData} (hP : P.Valid) (h : row.Check P) {r : ℝ} (hr : 0 < r)
    (hrr : r ≤ row.rb) :
    P.sym r * (1 + mixtureBound row.L) ≤ (row.value P : ℝ) ∧
      P.skew r * (1 + mixtureBound row.L) ≤ (row.value P : ℝ) := by
  obtain ⟨hrb0, hrb1, _, hL, hw1, hw2, hκW, _, _⟩ := h
  have he1 := (ExpWitness.sound hw1).2
  have he2 := (ExpWitness.sound hw2).1
  simp only at he1 he2
  have hθ : (thetaStar : ℝ) - 1 ≥ 0 := by norm_num [thetaStar]
  have hL' : (0 : ℝ) ≤ row.L := by exact_mod_cast hL
  have hE1 : Real.exp ((row.L : ℝ) * ((thetaStar : ℝ) - 1)) ≤ (row.U : ℝ) := by
    have : ((row.L * (thetaStar - 1) : ℚ) : ℝ) = (row.L : ℝ) * ((thetaStar : ℝ) - 1) := by
      push_cast; ring
    rw [← this]
    exact he1
  have hE2 : (row.W : ℝ) ≤ Real.exp ((row.L : ℝ) * (1 - (kappaStar : ℝ))) := by
    have : ((row.L * (1 - kappaStar) : ℚ) : ℝ) = (row.L : ℝ) * (1 - (kappaStar : ℝ)) := by
      push_cast; ring
    rw [← this]
    exact he2
  have hκW' : (1 : ℝ) < (kappaStar : ℝ) * row.W := by exact_mod_cast hκW
  have hκ0 : (0 : ℝ) < kappaStar := by norm_num [kappaStar]
  have hW0 : (0 : ℝ) < row.W := by
    by_contra hcon
    push Not at hcon
    nlinarith
  have hexpneg : Real.exp (-((row.L : ℝ) * (1 - (kappaStar : ℝ)))) ≤ 1 / (row.W : ℝ) := by
    rw [Real.exp_neg, one_div]
    exact inv_anti₀ hW0 hE2
  have hinvW : 1 / (row.W : ℝ) < kappaStar := by
    rw [div_lt_iff₀ hW0]
    linarith
  have hden : 0 < (kappaStar : ℝ) - 1 / (row.W : ℝ) := by linarith
  have hnum0 : 0 ≤ Real.exp ((row.L : ℝ) * ((thetaStar : ℝ) - 1)) - 1 := by
    have := Real.add_one_le_exp ((row.L : ℝ) * ((thetaStar : ℝ) - 1))
    nlinarith [mul_nonneg hL' hθ]
  have hC : mixtureBound row.L ≤ (row.Cbar : ℝ) := by
    unfold mixtureBound Cbar
    push_cast
    apply div_le_div₀ (by linarith) (by linarith) hden (by linarith)
  have hC0 : 0 ≤ mixtureBound row.L := by
    unfold mixtureBound
    exact div_nonneg hnum0 (by linarith)
  have hrb1' : ((row.rb : ℚ) : ℝ) < 1 := by exact_mod_cast hrb1
  have hs0 : 0 ≤ P.sym r := by
    obtain ⟨hA, hw, hc, hd, _⟩ := hP
    have hA' : (0 : ℝ) ≤ P.A := by exact_mod_cast hA
    have hw' : (0 : ℝ) ≤ P.wC := by exact_mod_cast hw
    have hc' : (0 : ℝ) < P.c := by exact_mod_cast hc
    have hd' : (0 : ℝ) ≤ P.d := by exact_mod_cast hd
    unfold PieceData.sym
    apply div_nonneg <;> positivity
  have hk0 : 0 ≤ P.skew r := by
    obtain ⟨_, hw, _, _, hK⟩ := hP
    have hw' : (0 : ℝ) ≤ P.wC := by exact_mod_cast hw
    have hK' : (0 : ℝ) < P.K := by exact_mod_cast hK
    have h1 : 0 < 1 - r ^ 2 := by nlinarith
    unfold PieceData.skew
    apply div_nonneg <;> positivity
  have hsm := P.sym_mono hP hr hrr hrb1'
  have hkm := P.skew_mono hP hr hrr hrb1'
  have hval : (row.value P : ℝ) = max (P.sym (row.rb : ℝ)) (P.skew (row.rb : ℝ)) *
      (1 + (row.Cbar : ℝ)) := by
    unfold value
    push_cast
    rw [P.cast_symQ, P.cast_skewQ]
  rw [hval]
  constructor
  · calc P.sym r * (1 + mixtureBound row.L) ≤ P.sym (row.rb : ℝ) * (1 + (row.Cbar : ℝ)) :=
          mul_le_mul hsm (by linarith) (by linarith) (hs0.trans hsm)
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)
  · calc P.skew r * (1 + mixtureBound row.L) ≤ P.skew (row.rb : ℝ) * (1 + (row.Cbar : ℝ)) :=
          mul_le_mul hkm (by linarith) (by linarith) (hk0.trans hkm)
      _ ≤ _ := mul_le_mul_of_nonneg_right (le_max_right _ _) (by linarith)

/-- The least prime `b ≥ β` gives `r = b^{-1/2} ≤ r_b`. -/
theorem rsqrt_le {β : ℕ} {rb : ℚ} (hrb : 0 < rb) (h : 1 ≤ rb ^ 2 * (β : ℚ)) {b : ℝ}
    (hb : (β : ℝ) ≤ b) : 1 / Real.sqrt b ≤ (rb : ℝ) := by
  have hrb' : (0 : ℝ) < rb := by exact_mod_cast hrb
  have h' : (1 : ℝ) ≤ (rb : ℝ) ^ 2 * (β : ℝ) := by exact_mod_cast h
  have hβ0 : (0 : ℝ) < β := by
    by_contra hcon
    push Not at hcon
    have : (β : ℝ) = 0 := le_antisymm hcon (Nat.cast_nonneg _)
    rw [this] at h'
    linarith
  have hb0 : 0 < b := lt_of_lt_of_le hβ0 hb
  have hs : 0 < Real.sqrt b := Real.sqrt_pos.mpr hb0
  rw [div_le_iff₀ hs]
  have h2 : (1 : ℝ) ≤ ((rb : ℝ) * Real.sqrt b) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hb0.le]
    nlinarith
  nlinarith [mul_pos hrb' hs]

end GateRow

/-- A coarse bad-fraction bound at a piece start (`eq:density:middle-bad-fractions`). -/
structure CoarseRow where
  piece : ℕ
  rX : ℚ
  deriving DecidableEq

namespace CoarseRow

/-- `r_X ≥ X^{-1/2}`, and the two fractions at `r_X` are at most `57·10⁻⁶` and `303·10⁻⁶`. -/
def Check (row : CoarseRow) (P : PieceData) : Prop :=
  0 < row.rX ∧ row.rX < 1 ∧ 1 ≤ row.rX ^ 2 * (P.X : ℚ) ∧ P.symQ row.rX ≤ 57 / 1000000 ∧
    P.skewQ row.rX ≤ 303 / 1000000

instance (row : CoarseRow) (P : PieceData) : Decidable (row.Check P) := by
  unfold Check; infer_instance

/-- **Soundness**: at every least prime `b ≥ X` of the piece, the two bad fractions are at most
`57·10⁻⁶` and `303·10⁻⁶`. -/
theorem sound {row : CoarseRow} {P : PieceData} (hP : P.Valid) (h : row.Check P) {b : ℝ}
    (hb : (P.X : ℝ) ≤ b) :
    P.sym (1 / Real.sqrt b) ≤ 57 / 1000000 ∧ P.skew (1 / Real.sqrt b) ≤ 303 / 1000000 := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := h
  have hr := GateRow.rsqrt_le h0 h2 hb
  have hX0 : (0 : ℝ) < P.X := by
    have h2' : (1 : ℝ) ≤ (row.rX : ℝ) ^ 2 * (P.X : ℝ) := by exact_mod_cast h2
    by_contra hcon
    push Not at hcon
    have : (P.X : ℝ) = 0 := le_antisymm hcon (Nat.cast_nonneg _)
    rw [this] at h2'
    linarith
  have hpos : 0 < 1 / Real.sqrt b := by
    have : 0 < b := lt_of_lt_of_le hX0 hb
    positivity
  have h1' : ((row.rX : ℚ) : ℝ) < 1 := by exact_mod_cast h1
  have h3' : ((P.symQ row.rX : ℚ) : ℝ) ≤ ((57 / 1000000 : ℚ) : ℝ) := by exact_mod_cast h3
  have h4' : ((P.skewQ row.rX : ℚ) : ℝ) ≤ ((303 / 1000000 : ℚ) : ℝ) := by exact_mod_cast h4
  rw [P.cast_symQ] at h3'
  rw [P.cast_skewQ] at h4'
  push_cast at h3' h4'
  exact ⟨(P.sym_mono hP hpos hr h1').trans h3', (P.skew_mono hP hpos hr h1').trans h4'⟩

end CoarseRow

end Sarkozy.DensityMoments
