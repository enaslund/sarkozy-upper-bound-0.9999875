module

public import Sarkozy.NormBoundsPaper4.EBounds
public import Sarkozy.TailCorr.InjCount

@[expose] public section

/-!
# `lem:record:e-orthogonal`(c) at one prime from the orthogonal-channel argument (FD)

`paper/sections/21_middle_records.tex`, proof of `lem:record:e-orthogonal`(c): "it suffices to
bound `‖𝒮 + X/z₁‖` with `X = Π_⊥𝖢𝖣Π_⊥`. Here `𝒮 = H𝒮H`, and `X` is self-adjoint with
`XH = Π_⊥𝖢𝖣H` … so `‖XH‖ = ‖HX‖ ≤ e_E` and `‖X − (I − H)X(I − H)‖ ≤ 2e_E`. The operators `𝒮` and
`(I − H)X(I − H)/z₁` act on orthogonal subspaces, so their sum has norm at most
`max(‖𝒮‖, ‖X‖/z₁) ≤ 𝔰_p` … Hence `‖𝒮 + X/z₁‖ ≤ 𝔰_p + 2e_E/z₁`, and the other two terms of
`lem:record:e-law`(d) contribute `q²/((1 − q)(1 − 2q))` and `18q²/((1 − q)(1 − 9q))`."

* **The projection `H`** onto `V(H₀³)`, explicitly: `hP u = V c(u)` with
  `c_i = (U_i + (∑_j U_j)/(p − 3))/(p(p − 2))` (the inverse of the Gram `(p − 2)(pI − J)` of
  `ECounts.Uc_lift`); `Uc_hP` (`V^* H = V^*`), `Nq_split` (Pythagoras `‖u‖² = ‖Hu‖² + ‖u − Hu‖²`).
* `NL_eq`: `|Inj| = M(p − 3)(p − 4)(p − 5)` (TailCorr's `card_avoid`), so `z^E_0` is exact.
* **`eorth_unnorm`**: on mean-zero `u, v`,
  `|Sym(K₁ − K^E_0)(u, v)| ≤ (F + 2e₀ + y₀ + ε₀) √Nq u √Nq v` for any `F` above the constants
  `σ₀` of `𝒮` and `ξ₀` of `𝖢𝖣` (`max(‖𝒮‖, ‖X‖/z₁)`), from two inputs at the prime:
  - `HEps`: `‖ε_E‖ ≤ 18q²/(1 − q)` (`lem:record:e-law`(d), Schur over the 18 patterns), as
    `|Ef u v| ≤ 18(p − 2)√Nq u √Nq v`;
  - `HCD`: `‖𝖢𝖣 V c‖ ≤ e‖Vc‖` (`lem:record:e-orthogonal`(b)), as
    `|CHf w (V c)| ≤ eK √Nq w √Nq (V c)` for mean-zero `c_i`.
-/

open Finset Matrix
open scoped BigOperators

namespace Sarkozy.NormBoundsPaper4

open Sarkozy.NormBoundsPaper3
open Sarkozy.PartV Sarkozy.Labellings Sarkozy.PartVRecords Sarkozy.MiddleComparison
open Sarkozy.NormBoundsPaper2 (off chg1)

variable {p : ℕ} [Fact p.Prime]

local notation "T3" => (ZMod p × ZMod p) × ZMod p

/-! ## The exact count of `K^E_0` -/

/-- `|Inj| = p(p − 1)(p − 2)(p − 3)(p − 4)(p − 5)`. -/
theorem NL_eq (hp : 6 ≤ p) :
    NL (p := p) = (p : ℝ) * ((p : ℝ) - 1) * ((p : ℝ) - 2) *
      (((p : ℝ) - 3) * ((p : ℝ) - 4) * ((p : ℝ) - 5)) := by
  unfold NL
  have e : injLabellings (ZMod p) (matchGraph (Fin 2)) =
      univ.filter fun y : Fin 3 × Fin 2 → ZMod p =>
        Function.Injective y ∧ ∀ q, y q ∉ (∅ : Finset (ZMod p)) := by
    ext z
    simp only [mem_inj_iff, mem_filter, mem_univ, true_and, notMem_empty, not_false_eq_true,
      implies_true, and_true]
  rw [e, Sarkozy.TailCorr.card_avoid]
  simp only [card_empty, Nat.sub_zero, ZMod.card, Fintype.card_prod, Fintype.card_fin]
  rw [show (3 * 2 : ℕ) = 6 from rfl]
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hp
  simp only [Nat.descFactorial_succ, Nat.descFactorial_zero]
  push_cast
  rw [show 6 + n - 0 = 6 + n by omega, show 6 + n - 1 = 5 + n by omega,
    show 6 + n - 2 = 4 + n by omega, show 6 + n - 3 = 3 + n by omega,
    show 6 + n - 4 = 2 + n by omega, show 6 + n - 5 = 1 + n by omega]
  push_cast
  ring

/-! ## The projection onto `V(H₀³)` -/

/-- The coordinates of `Hu`: `c_i = (U_i + (∑_j U_j)/(p − 3))/(p(p − 2))`. -/
noncomputable def cP (u : T3 → ℝ) (i : Fin 3) (t : ZMod p) : ℝ :=
  (Uc u i t + (∑ j, Uc u j t) / ((p : ℝ) - 3)) / ((p : ℝ) * ((p : ℝ) - 2))

/-- `Hu = V c(u)`. -/
noncomputable def hP (u : T3 → ℝ) : T3 → ℝ := lift (cP u)

theorem cP_mean (u : T3 → ℝ) (hu : ∑ x, ind3 x * u x = 0) (i : Fin 3) : ∑ t, cP u i t = 0 := by
  unfold cP
  rw [← sum_div, sum_add_distrib, ← sum_div, sum_comm]
  simp only [sum_Uc, hu, sum_const_zero, zero_div, add_zero]

theorem Uc_hP (hp : 4 ≤ p) (u : T3 → ℝ) (hu : ∑ x, ind3 x * u x = 0) (i : Fin 3) (t : ZMod p) :
    Uc (hP u) i t = Uc u i t := by
  unfold hP
  rw [Uc_lift _ (cP_mean u hu)]
  have hp' : (4 : ℝ) ≤ p := by exact_mod_cast hp
  have h2 : (p : ℝ) - 2 ≠ 0 := by linarith
  have h3 : (p : ℝ) - 3 ≠ 0 := by linarith
  have h0 : (p : ℝ) ≠ 0 := by linarith
  unfold cP
  simp only [Fin.sum_univ_three]
  fin_cases i <;> simp <;> field_simp <;> ring

theorem Uc_sub (u w : T3 → ℝ) (i : Fin 3) (t : ZMod p) :
    Uc (u - w) i t = Uc u i t - Uc w i t := by
  unfold Uc
  simp only [Pi.sub_apply, mul_sub, sum_sub_distrib]

theorem hP_mean (u : T3 → ℝ) (hu : ∑ x, ind3 x * u x = 0) : ∑ x, ind3 x * hP u x = 0 := by
  unfold hP lift
  simp only [mul_sum]
  rw [sum_comm]
  refine sum_eq_zero fun i _ => ?_
  rw [cnt_one i (cP u i), cP_mean u hu i, mul_zero]

theorem orth_hP (hp : 4 ≤ p) (u : T3 → ℝ) (hu : ∑ x, ind3 x * u x = 0) :
    ∑ x, ind3 x * hP u x * (u - hP u) x = 0 := by
  have e : ∀ x : T3, ind3 x * hP u x * (u - hP u) x =
      ∑ i, ind3 x * cP u i (crd i x) * (u - hP u) x := fun x => by
    rw [show hP u x = ∑ i, cP u i (crd i x) from rfl, mul_sum, sum_mul]
  rw [sum_congr rfl fun x _ => e x, sum_comm]
  refine sum_eq_zero fun i _ => ?_
  rw [← Uc_pair (u - hP u) i (cP u i)]
  refine sum_eq_zero fun t _ => ?_
  rw [Uc_sub, Uc_hP hp u hu, sub_self, mul_zero]

/-- **Pythagoras**: `‖u‖² = ‖Hu‖² + ‖u − Hu‖²`. -/
theorem Nq_split (hp : 4 ≤ p) (u : T3 → ℝ) (hu : ∑ x, ind3 x * u x = 0) :
    Nq u = Nq (hP u) + Nq (u - hP u) := by
  have ho := orth_hP hp u hu
  unfold Nq
  rw [← sum_add_distrib]
  have e : ∀ x, ind3 x * u x ^ 2 = ind3 x * hP u x ^ 2 + ind3 x * (u - hP u) x ^ 2 +
      2 * (ind3 x * hP u x * (u - hP u) x) := fun x => by
    simp only [Pi.sub_apply]; ring
  rw [sum_congr rfl fun x _ => e x, sum_add_distrib, ← mul_sum, ho, mul_zero, add_zero]

theorem Tu_hP (hp : 4 ≤ p) (u : T3 → ℝ) (hu : ∑ x, ind3 x * u x = 0) : Tu u = Tu (hP u) := by
  unfold Tu
  simp only [Uc_hP hp u hu]

/-! ## The assembly -/

theorem sqrt_le_sqrt_add {a a' : ℝ} (h1 : 0 ≤ a') : Real.sqrt a ≤ Real.sqrt (a + a') :=
  Real.sqrt_le_sqrt (by linarith)

/-- `ab + a'b' ≤ √(a² + a'²)√(b² + b'²)`. -/
theorem cs2 (a a' b b' : ℝ) :
    a * b + a' * b' ≤ Real.sqrt (a ^ 2 + a' ^ 2) * Real.sqrt (b ^ 2 + b' ^ 2) := by
  rw [← Real.sqrt_mul (by positivity)]
  refine Real.le_sqrt_of_sq_le ?_
  nlinarith [sq_nonneg (a * b' - a' * b)]

/-- The unnormalized constant of `e_E`: `(p − 2)√p √((2(p − 2)² + 4)/((p − 2)(p − 3)))`. -/
noncomputable def eK (p : ℕ) : ℝ :=
  ((p : ℝ) - 2) * Real.sqrt p *
    Real.sqrt ((2 * ((p : ℝ) - 2) ^ 2 + 4) / (((p : ℝ) - 2) * ((p : ℝ) - 3)))

/-- **`lem:record:e-orthogonal`(c), unnormalized, from the two inputs** `HEps`
(`lem:record:e-law`(d), `‖ε_E‖`) and `HCD` (`lem:record:e-orthogonal`(b), `‖𝖢𝖣 H‖`). -/
theorem eorth_unnorm (hE : (eSet (F := ZMod p)).Nonempty)
    (hne : (injLabellings (ZMod p) (matchGraph (Fin 2))).Nonempty) (h3 : p % 4 = 3) (hp : 7 ≤ p)
    (HEps : ∀ u v : T3 → ℝ, |Ef u v| ≤ 18 * ((p : ℝ) - 2) * Real.sqrt (Nq u) * Real.sqrt (Nq v))
    (HCD : ∀ (c : Fin 3 → ZMod p → ℝ), (∀ i, ∑ t, c i t = 0) → ∀ w : T3 → ℝ,
      |CHf w (lift c)| ≤ eK p * Real.sqrt (Nq w) * Real.sqrt (Nq (lift c)))
    {F : ℝ}
    (hσ : (p : ℝ) * ((p : ℝ) - 2) * ((1 + Real.sqrt 2) / NL (p := p) +
      |1 / NL (p := p) - 1 / (4 * Nk (p := p))|) ≤ F)
    (hξ : (p : ℝ) * ((p : ℝ) - 2) / (4 * Nk (p := p)) ≤ F)
    (u v : T3 → ℝ) (hu : ∑ x, ind3 x * u x = 0) (hv : ∑ x, ind3 x * v x = 0) :
    |chg1 (P3 hE) (C0 hne) (1 / 2) (1 / 2) 1 u v| ≤
      (F + 2 * (eK p / (4 * Nk (p := p))) + ((p : ℝ) - 2) / (4 * Nk (p := p)) +
        18 * ((p : ℝ) - 2) / NL (p := p)) * Real.sqrt (Nq u) * Real.sqrt (Nq v) := by
  have hp' : (7 : ℝ) ≤ p := by exact_mod_cast hp
  have hp4 : 4 ≤ p := by omega
  have hp3 : 3 ≤ p := by omega
  have hNk := Nk_pos (p := p) hE
  have hNL := NL_pos hne
  have h4Nk : 0 < 4 * Nk (p := p) := by positivity
  have hpp : 0 ≤ (p : ℝ) * ((p : ℝ) - 2) := by nlinarith
  have heK : 0 ≤ eK p := by
    unfold eK
    have : (0 : ℝ) ≤ (p : ℝ) - 2 := by linarith
    positivity
  -- the decomposition and the projection
  rw [chg1_decomp hE hne h3 u v hu hv]
  set hu' := hP u
  set hv' := hP v
  set ru := u - hP u
  set rv := v - hP v
  have hsu := Nq_split hp4 u hu
  have hsv := Nq_split hp4 v hv
  set a := Real.sqrt (Nq hu')
  set a' := Real.sqrt (Nq ru)
  set b := Real.sqrt (Nq hv')
  set b' := Real.sqrt (Nq rv)
  set nu := Real.sqrt (Nq u)
  set nv := Real.sqrt (Nq v)
  have ha : 0 ≤ a := Real.sqrt_nonneg _
  have ha' : 0 ≤ a' := Real.sqrt_nonneg _
  have hb : 0 ≤ b := Real.sqrt_nonneg _
  have hb' : 0 ≤ b' := Real.sqrt_nonneg _
  have hnu : 0 ≤ nu := Real.sqrt_nonneg _
  have hnv : 0 ≤ nv := Real.sqrt_nonneg _
  have hNa := Nq_nonneg hu'
  have hNa' := Nq_nonneg ru
  have hNb := Nq_nonneg hv'
  have hNb' := Nq_nonneg rv
  have hanu : a ≤ nu := by
    change Real.sqrt (Nq hu') ≤ Real.sqrt (Nq u); rw [hsu]; exact sqrt_le_sqrt_add hNa'
  have ha'nu : a' ≤ nu := by
    change Real.sqrt (Nq ru) ≤ Real.sqrt (Nq u); rw [hsu, add_comm]
    exact sqrt_le_sqrt_add hNa
  have hbnv : b ≤ nv := by
    change Real.sqrt (Nq hv') ≤ Real.sqrt (Nq v); rw [hsv]; exact sqrt_le_sqrt_add hNb'
  have hcs : a * b + a' * b' ≤ nu * nv := by
    have := cs2 a a' b b'
    rw [Real.sq_sqrt hNa, Real.sq_sqrt hNa', Real.sq_sqrt hNb, Real.sq_sqrt hNb', ← hsu,
      ← hsv] at this
    exact this
  -- the star part
  have hTu : Real.sqrt (Tu u) ≤ Real.sqrt ((p : ℝ) * ((p : ℝ) - 2)) * a := by
    rw [Tu_hP hp4 u hu, ← Real.sqrt_mul hpp]
    exact Real.sqrt_le_sqrt (Tu_le hp3 _ (hP_mean u hu))
  have hTv : Real.sqrt (Tu v) ≤ Real.sqrt ((p : ℝ) * ((p : ℝ) - 2)) * b := by
    rw [Tu_hP hp4 v hv, ← Real.sqrt_mul hpp]
    exact Real.sqrt_le_sqrt (Tu_le hp3 _ (hP_mean v hv))
  have hTT : Real.sqrt (Tu u) * Real.sqrt (Tu v) ≤ (p : ℝ) * ((p : ℝ) - 2) * (a * b) := by
    have := mul_le_mul hTu hTv (Real.sqrt_nonneg _) (by positivity)
    calc _ ≤ _ := this
      _ = (Real.sqrt ((p : ℝ) * ((p : ℝ) - 2)) * Real.sqrt ((p : ℝ) * ((p : ℝ) - 2))) *
          (a * b) := by ring
      _ = _ := by rw [Real.mul_self_sqrt hpp]
  have hS1 := Sraw_le u v
  have hS2 := Sc_le u v
  -- the two-edge part through the projection
  have hCH : CHf u v = CHf hu' v + CHf ru hv' + CHf ru rv := by
    have e1 : CHf ru v = CHf u v - CHf hu' v := CHf_sub_left _ _ _
    have e2 : CHf ru rv = CHf ru v - CHf ru hv' := CHf_sub_right _ _ _
    linarith
  have hc1 : |CHf hu' v| ≤ eK p * nv * a := by
    rw [CHf_comm h3]
    exact HCD _ (cP_mean u hu) v
  have hc2 : |CHf ru hv'| ≤ eK p * a' * b := HCD _ (cP_mean v hv) ru
  have hc3 : |CHf ru rv| ≤ (p : ℝ) * ((p : ℝ) - 2) * a' * b' := CHf_le hp3 h3 ru rv
  have hZ : |ZZf u v| ≤ ((p : ℝ) - 2) * nu * nv := ZZf_le hp3 u v
  have hEf : |Ef u v| ≤ 18 * ((p : ℝ) - 2) * nu * nv := HEps u v
  -- combine
  set Bc := 1 / NL (p := p) - 1 / (4 * Nk (p := p))
  have e : Sraw u v / NL (p := p) - Sc u v / (4 * Nk (p := p)) +
      (CHf u v + ZZf u v) / (4 * Nk (p := p)) - Ef u v / NL (p := p) =
      (Sraw u v - Sc u v) * (1 / NL (p := p)) + Sc u v * Bc +
        (CHf hu' v + CHf ru hv') / (4 * Nk (p := p)) + CHf ru rv / (4 * Nk (p := p)) +
        ZZf u v / (4 * Nk (p := p)) - Ef u v / NL (p := p) := by
    rw [hCH]; simp only [Bc]; field_simp; ring
  rw [e]
  have k1 : |(Sraw u v - Sc u v) * (1 / NL (p := p))| ≤ (1 + Real.sqrt 2) / NL (p := p) *
      ((p : ℝ) * ((p : ℝ) - 2) * (a * b)) := by
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / NL (p := p))]
    calc _ ≤ (1 + Real.sqrt 2) * Real.sqrt (Tu u) * Real.sqrt (Tu v) * (1 / NL (p := p)) :=
          mul_le_mul_of_nonneg_right hS1 (by positivity)
      _ = (1 + Real.sqrt 2) / NL (p := p) * (Real.sqrt (Tu u) * Real.sqrt (Tu v)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hTT (by positivity)
  have k2 : |Sc u v * Bc| ≤ |Bc| * ((p : ℝ) * ((p : ℝ) - 2) * (a * b)) := by
    rw [abs_mul, mul_comm]
    exact mul_le_mul_of_nonneg_left (hS2.trans hTT) (abs_nonneg _)
  have k3 : |(CHf hu' v + CHf ru hv') / (4 * Nk (p := p))| ≤
      eK p / (4 * Nk (p := p)) * (2 * (nu * nv)) := by
    rw [abs_div, abs_of_pos h4Nk, div_le_iff₀ h4Nk]
    have : |CHf hu' v + CHf ru hv'| ≤ eK p * (2 * (nu * nv)) := by
      refine (abs_add_le _ _).trans ?_
      have t1 : eK p * nv * a ≤ eK p * (nu * nv) := by
        rw [mul_assoc, mul_comm nv a]; exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hanu hnv) heK
      have t2 : eK p * a' * b ≤ eK p * (nu * nv) := by
        rw [mul_assoc]; exact mul_le_mul_of_nonneg_left (mul_le_mul ha'nu hbnv hb hnu) heK
      linarith
    calc _ ≤ _ := this
      _ = eK p / (4 * Nk (p := p)) * (2 * (nu * nv)) * (4 * Nk (p := p)) := by
          field_simp
  have k4 : |CHf ru rv / (4 * Nk (p := p))| ≤
      (p : ℝ) * ((p : ℝ) - 2) / (4 * Nk (p := p)) * (a' * b') := by
    rw [abs_div, abs_of_pos h4Nk, div_le_iff₀ h4Nk]
    calc _ ≤ _ := hc3
      _ = (p : ℝ) * ((p : ℝ) - 2) / (4 * Nk (p := p)) * (a' * b') * (4 * Nk (p := p)) := by
          field_simp
  have k5 : |ZZf u v / (4 * Nk (p := p))| ≤ ((p : ℝ) - 2) / (4 * Nk (p := p)) * (nu * nv) := by
    rw [abs_div, abs_of_pos h4Nk, div_le_iff₀ h4Nk]
    calc _ ≤ _ := hZ
      _ = ((p : ℝ) - 2) / (4 * Nk (p := p)) * (nu * nv) * (4 * Nk (p := p)) := by
          field_simp
  have k6 : |Ef u v / NL (p := p)| ≤ 18 * ((p : ℝ) - 2) / NL (p := p) * (nu * nv) := by
    rw [abs_div, abs_of_pos hNL, div_le_iff₀ hNL]
    calc _ ≤ _ := hEf
      _ = 18 * ((p : ℝ) - 2) / NL (p := p) * (nu * nv) * NL (p := p) := by field_simp
  -- the star and the far two-edge part share `F`
  have hab : 0 ≤ a * b := mul_nonneg ha hb
  have hab' : 0 ≤ a' * b' := mul_nonneg ha' hb'
  have kS : (1 + Real.sqrt 2) / NL (p := p) * ((p : ℝ) * ((p : ℝ) - 2) * (a * b)) +
      |Bc| * ((p : ℝ) * ((p : ℝ) - 2) * (a * b)) +
      (p : ℝ) * ((p : ℝ) - 2) / (4 * Nk (p := p)) * (a' * b') ≤ F * (nu * nv) := by
    have h1 : ((1 + Real.sqrt 2) / NL (p := p) + |Bc|) * ((p : ℝ) * ((p : ℝ) - 2)) ≤ F := by
      rw [mul_comm]; exact hσ
    have hF0 : 0 ≤ F := le_trans (by positivity) hξ
    calc (1 + Real.sqrt 2) / NL (p := p) * ((p : ℝ) * ((p : ℝ) - 2) * (a * b)) +
          |Bc| * ((p : ℝ) * ((p : ℝ) - 2) * (a * b)) +
          (p : ℝ) * ((p : ℝ) - 2) / (4 * Nk (p := p)) * (a' * b')
        = (((1 + Real.sqrt 2) / NL (p := p) + |Bc|) * ((p : ℝ) * ((p : ℝ) - 2))) * (a * b) +
          (p : ℝ) * ((p : ℝ) - 2) / (4 * Nk (p := p)) * (a' * b') := by ring
      _ ≤ F * (a * b) + F * (a' * b') :=
          add_le_add (mul_le_mul_of_nonneg_right h1 hab) (mul_le_mul_of_nonneg_right hξ hab')
      _ = F * (a * b + a' * b') := by ring
      _ ≤ F * (nu * nv) := mul_le_mul_of_nonneg_left hcs hF0
  have habs := abs_sub (((Sraw u v - Sc u v) * (1 / NL (p := p)) + Sc u v * Bc +
      (CHf hu' v + CHf ru hv') / (4 * Nk (p := p)) + CHf ru rv / (4 * Nk (p := p)) +
      ZZf u v / (4 * Nk (p := p)))) (Ef u v / NL (p := p))
  have h12 := abs_add_le ((Sraw u v - Sc u v) * (1 / NL (p := p))) (Sc u v * Bc)
  have h123 := abs_add_le ((Sraw u v - Sc u v) * (1 / NL (p := p)) + Sc u v * Bc)
    ((CHf hu' v + CHf ru hv') / (4 * Nk (p := p)))
  have h1234 := abs_add_le ((Sraw u v - Sc u v) * (1 / NL (p := p)) + Sc u v * Bc +
    (CHf hu' v + CHf ru hv') / (4 * Nk (p := p))) (CHf ru rv / (4 * Nk (p := p)))
  have h12345 := abs_add_le ((Sraw u v - Sc u v) * (1 / NL (p := p)) + Sc u v * Bc +
    (CHf hu' v + CHf ru hv') / (4 * Nk (p := p)) + CHf ru rv / (4 * Nk (p := p)))
    (ZZf u v / (4 * Nk (p := p)))
  have hfin : (F + 2 * (eK p / (4 * Nk (p := p))) + ((p : ℝ) - 2) / (4 * Nk (p := p)) +
      18 * ((p : ℝ) - 2) / NL (p := p)) * nu * nv = F * (nu * nv) +
      eK p / (4 * Nk (p := p)) * (2 * (nu * nv)) + ((p : ℝ) - 2) / (4 * Nk (p := p)) * (nu * nv) +
      18 * ((p : ℝ) - 2) / NL (p := p) * (nu * nv) := by ring
  rw [hfin]
  linarith only [habs, h12, h123, h1234, h12345, k1, k2, k3, k4, k5, k6, kS]

end Sarkozy.NormBoundsPaper4
