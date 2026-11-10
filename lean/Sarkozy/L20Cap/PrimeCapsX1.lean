module

public import Sarkozy.L20Cap.GapCross
public import Sarkozy.L20Cap.RectGraph
public import Sarkozy.L20Cap.PrimeCapsFull
public import Sarkozy.ExtractionK.SoftGeneralCorollaries

/-!
# The caps of L20 with `x_g` proved and `N_A` from `cor:soft-kernels`(a)

`paper/sections/20_middle_reference.tex`, `prop:l20-collisions`(b) ("The caps"), with the two
remaining block bounds of `prop:l20-pair-gap` discharged:

* **`l20_prime_caps_rect`** (any finite field): `l20_prime_caps_full` with the cross bound `hC`
  proved (`hC_of_nonstar`, `GapCross`), for any `x_g` at least the exact constant
  `τ_gN_A + |L(0,1)|/p·(p(1 - q)/(2(1 - 2q)))^{1/2}` (`hxg`);
* **`l20_prime_caps_X1`** (`𝔽_p`): moreover `N_A` is any upper bound for X1's partition sum
  `∑_c p^{-k_c/2}·leafCoef(c)` of `cor:soft-kernels`(a)/`cor:extraction-leaf`(b)
  (`sk_soft_extraction_leaf_partition_g`) for an exact partition of the `221` nonstars of the
  eight cross pairs into classes with valid leaf records (`prop:l20-rectangular`(b): "A raw cap
  from `cor:soft-kernels`(a) suffices"). The class data (the `42` classes of the histogram of
  `cert:l20-grid`) and the numerical value of the sum stay hypotheses (`h𝔓`, `hrec`, `hNAle`);
* `Lker_abs_le`, `xG`: the explicit cross constant used by `l20_prime_caps_X1` (`hxg : xG ≤ x_g`;
  `CrossPaper.xG_le_xPaper` shows the paper's `x_g` qualifies for `p ≥ 2²⁰`).
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace Sarkozy.L20Cap

open Sarkozy Sarkozy.Recentering Sarkozy.Cuts Sarkozy.Labellings Sarkozy.Extraction
  Sarkozy.ExtractionK

section Field

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Nonempty (CoreT F)]
  [Nonempty (PairT F)]

/-- `G_{F,2}` has labellings once `p ≥ 6`. -/
theorem injLabellings_G6_nonempty (h6 : 6 ≤ Fintype.card F) : (injLabellings F G6).Nonempty := by
  by_contra hne
  rw [Finset.not_nonempty_iff_eq_empty] at hne
  have hP := hP_pos (F := F) h6
  have h0 : prob ((coreLaw (F := F)).product (pairLaw (F := F))) Avoid = 0 := by
    unfold prob FiniteLaw.expect
    refine sum_eq_zero fun x _ => ?_
    have hx : ¬ Avoid x := fun hx => by
      have := (labels_mem x).mpr hx
      rw [hne] at this
      simp at this
    simp [hx]
  linarith

omit [Nonempty (PairT F)] in
/-- **`|b| = |L(0, 1)| ≤ 128(η + 1 + 16q)/((1 - q)(p - 1))`**: `(p - 1)b = 4E_C[ψ𝖪(0, C)]`
(`Lker_row_sum`, `Lker_row_sum_eq`) with `|ψ| ≤ 2(η + 1 + 16q)/(1 - q)` (`Kbar_dev`) and
`0 ≤ 𝖪 ≤ 16`. -/
theorem Lker_abs_le (hm1 : quadraticChar F (-1) = -1) (hF : ringChar F ≠ 2) (hW : WeilBound F) :
    |Lker (0 : F) (1 : F)| ≤ 128 * (etaL F + 1 + 16 * (Fintype.card F : ℝ)⁻¹) /
      ((1 - (Fintype.card F : ℝ)⁻¹) * ((Fintype.card F : ℝ) - 1)) := by
  have hp1 : (1 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.one_lt_card
  have hp0 : (0 : ℝ) < Fintype.card F := by linarith
  set q := (Fintype.card F : ℝ)⁻¹ with hq
  have hq0 : 0 < q := inv_pos.mpr hp0
  have hq1 : q < 1 := inv_lt_one_of_one_lt₀ hp1
  have h1q : 0 < 1 - q := by linarith
  have hη0 : 0 ≤ etaL F := by unfold etaL; positivity
  have hψ : ∀ C : CoreT F, |psiR C * Kz 0 C.1| ≤ 32 * (etaL F + 1 + 16 * q) / (1 - q) := by
    intro C
    have hK0 := Kz_nonneg hm1 C.2 0
    have hK16 := Kz_le hm1 C.2 0
    have hdev := Kbar_dev hF hW C.2.1
    have hdev' : |Kbar C.1 - 1| ≤ etaL F := by unfold etaL; exact hdev
    have hab : |Kbar C.1 - 16 * q| ≤ etaL F + 1 + 16 * q := by
      have e : Kbar C.1 - 16 * q = (Kbar C.1 - 1) + (1 - 16 * q) := by ring
      rw [e]
      refine (abs_add_le _ _).trans ?_
      have : |1 - 16 * q| ≤ 1 + 16 * q := by
        rw [abs_le]; constructor <;> linarith
      linarith
    have hpsi : |psiR C| ≤ 2 * (etaL F + 1 + 16 * q) / (1 - q) := by
      unfold psiR
      rw [← hq, abs_div, abs_mul, abs_of_pos h1q, abs_two]
      exact div_le_div_of_nonneg_right (by linarith) h1q.le
    rw [abs_mul, abs_of_nonneg hK0]
    calc |psiR C| * Kz 0 C.1 ≤ 2 * (etaL F + 1 + 16 * q) / (1 - q) * 16 :=
          mul_le_mul hpsi hK16 hK0 (by positivity)
      _ = 32 * (etaL F + 1 + 16 * q) / (1 - q) := by ring
  have hrow := Lker_row_sum (F := F) 0
  rw [Lker_row_sum_eq hm1 hF] at hrow
  have hE := FiniteLaw.abs_expect_le_const (μ := coreLaw (F := F)) hψ
  have hp1' : 0 < (Fintype.card F : ℝ) - 1 := by linarith
  have hb : ((Fintype.card F : ℝ) - 1) * |Lker (0 : F) (1 : F)| ≤
      4 * (32 * (etaL F + 1 + 16 * q) / (1 - q)) := by
    rw [← abs_of_pos hp1', ← abs_mul, hrow, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    exact mul_le_mul_of_nonneg_left hE (by norm_num)
  rw [le_div_iff₀ (mul_pos h1q hp1')]
  have : |Lker (0 : F) (1 : F)| * ((1 - q) * ((Fintype.card F : ℝ) - 1)) =
      (1 - q) * (((Fintype.card F : ℝ) - 1) * |Lker (0 : F) (1 : F)|) := by ring
  rw [this]
  calc (1 - q) * (((Fintype.card F : ℝ) - 1) * |Lker (0 : F) (1 : F)|)
      ≤ (1 - q) * (4 * (32 * (etaL F + 1 + 16 * q) / (1 - q))) :=
        mul_le_mul_of_nonneg_left hb h1q.le
    _ = 128 * (etaL F + 1 + 16 * q) := by field_simp; ring

end Field

/-- **The explicit cross constant** `x_g = τ_gN_A + b⁺/p·(p(1 - q)/(2(1 - 2q)))^{1/2}`,
`b⁺ = 128(η + 1 + 16q)/((1 - q)(p - 1))` (`Lker_abs_le`; at `p = 2²⁰` the second term is about
`91qr`, below the paper's `2rw_g ≈ 126qr`). -/
noncomputable def xG (F : Type*) [Fintype F] (m NA : ℝ) : ℝ :=
  tauG F m * NA + 128 * (etaL F + 1 + 16 * (Fintype.card F : ℝ)⁻¹) /
      ((1 - (Fintype.card F : ℝ)⁻¹) * ((Fintype.card F : ℝ) - 1)) / Fintype.card F *
    Real.sqrt (Fintype.card F * (1 - (Fintype.card F : ℝ)⁻¹) /
      (2 * (1 - 2 * (Fintype.card F : ℝ)⁻¹)))

section Field2

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Nonempty (CoreT F)]
  [Nonempty (PairT F)]

omit [Nonempty (PairT F)] in
/-- The exact cross constant is at most `xG`. -/
theorem xExact_le_xG (hm1 : quadraticChar F (-1) = -1) (hF : ringChar F ≠ 2) (hW : WeilBound F)
    (m NA : ℝ) :
    tauG F m * NA + |Lker (0 : F) (1 : F)| / Fintype.card F *
        Real.sqrt (Fintype.card F * (1 - (Fintype.card F : ℝ)⁻¹) /
          (2 * (1 - 2 * (Fintype.card F : ℝ)⁻¹))) ≤ xG F m NA := by
  unfold xG
  have hp0 : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have := Lker_abs_le hm1 hF hW
  gcongr

/-- **The caps of L20 at a prime with the cross bound proved** (`prop:l20-collisions`(b),
`prop:l20-pair-gap`): `l20_prime_caps_full` without `hC`; `x_g` is any upper bound of the exact
cross constant `τ_gN_A + |L(0,1)|/p·(p(1 - q)/(2(1 - 2q)))^{1/2}` of `hC_of_nonstar`. -/
theorem l20_prime_caps_rect (hm1 : quadraticChar F (-1) = -1) (hF : ringChar F ≠ 2)
    (hW : WeilBound F) (h6 : 6 ≤ Fintype.card F) {m NA xg D mstar Nns χp : ℝ}
    (hm : (coreLaw (F := F)).expect (fun C => Kbar C.1 - 1) ≤ m) (hm0 : 0 ≤ m)
    (hΔ : 0 < 30 * (Fintype.card F : ℝ)⁻¹ - (2 * (Real.sqrt (Fintype.card F))⁻¹ + NA) ^ 2)
    (hNA : 0 ≤ NA)
    (hN : ∀ g : PairT F → ℝ, (pairLaw (F := F)).expect g = 0 →
      (∀ h' : F → ℝ, ∑ z, h' z = 0 → ip (pairLaw (F := F)) (vOp h') g = 0) →
      nrm (coreLaw (F := F)) (fun C => (pairLaw (F := F)).expect (fun b => Nrect C b * g b)) ≤
        NA * nrm (pairLaw (F := F)) g)
    (hxg : tauG F m * NA + |Lker (0 : F) (1 : F)| / Fintype.card F *
        Real.sqrt (Fintype.card F * (1 - (Fintype.card F : ℝ)⁻¹) /
          (2 * (1 - 2 * (Fintype.card F : ℝ)⁻¹))) ≤ xg)
    (hgate : cGap (Fintype.card F : ℝ)⁻¹ (tauG F m) (2 * (Real.sqrt (Fintype.card F))⁻¹ + NA) xg ≤
      sP F m)
    (hD0 : 0 ≤ D)
    (hD : ∀ f, |kernelForm (halfLaw h6) (halfLaw h6) collK f f| ≤ D * nrm (halfLaw h6) f ^ 2)
    (hNns0 : 0 ≤ Nns)
    (hns : ∀ f, |kernelForm (halfLaw h6) (halfLaw h6) nonstar f f| ≤ Nns * nrm (halfLaw h6) f ^ 2)
    (hstar : |kernelForm (halfLaw h6) (halfLaw h6)
      (fun x x' => starPart6 (labels x) (labels x')) (fun _ => 1) (fun _ => 1)| ≤ mstar)
    (hεZ : Nns + D + mstar < 1)
    (hχ0 : 0 ≤ χp)
    (hchi : nrm (halfLaw h6) (fun x => recOp (halfLaw h6) (cutT h6) (fun _ => 1) x - 1) ^ 2 ≤ χp)
    (hC1 : (sP F m * cGap (Fintype.card F : ℝ)⁻¹ (tauG F m)
        (2 * (Real.sqrt (Fintype.card F))⁻¹ + NA) xg /
      prob ((coreLaw (F := F)).product (pairLaw (F := F))) Avoid + D) /
        (1 - (Nns + D + mstar)) < 1)
    (hH1 : (Nns + D) / (1 - (Nns + D + mstar)) < 1) (f : CoreT F × PairT F → ℝ) :
    -((sP F m * cGap (Fintype.card F : ℝ)⁻¹ (tauG F m)
        (2 * (Real.sqrt (Fintype.card F))⁻¹ + NA) xg /
        prob ((coreLaw (F := F)).product (pairLaw (F := F))) Avoid + D) /
          (1 - (Nns + D + mstar))) *
        nrm (halfLaw h6) f ^ 2 ≤ kernelForm (halfLaw h6) (halfLaw h6) (cutT h6) f f ∧
      kernelForm (halfLaw h6) (halfLaw h6) (cutT h6) f f ≤
        (1 + χp / (1 - (Nns + D) / (1 - (Nns + D + mstar)))) * nrm (halfLaw h6) f ^ 2 := by
  have h5 : 5 ≤ Fintype.card F := by omega
  have hA : ∀ h : F → ℝ, ∑ z, h z = 0 →
      nrm (coreLaw (F := F)) (recOp (pairLaw (F := F)) Rc (vOp h)) ≤
        tauG F m * nrm (pairLaw (F := F)) (vOp h) :=
    fun h h0 => hA_proved hm1 h5 (fun C => Kbar_dev hF hW C.2.1) hm h h0
  have hτ0 : 0 ≤ tauG F m := Real.sqrt_nonneg _
  have hx0 : 0 ≤ tauG F m * NA + |Lker (0 : F) (1 : F)| / Fintype.card F *
      Real.sqrt (Fintype.card F * (1 - (Fintype.card F : ℝ)⁻¹) /
        (2 * (1 - 2 * (Fintype.card F : ℝ)⁻¹))) := by
    have : 0 ≤ |Lker (0 : F) (1 : F)| / Fintype.card F := by positivity
    have := mul_nonneg hτ0 hNA
    positivity
  have hx : 0 ≤ xg := hx0.trans hxg
  have hC : ∀ (h : F → ℝ) (g : PairT F → ℝ), ∑ z, h z = 0 → (pairLaw (F := F)).expect g = 0 →
      (∀ h' : F → ℝ, ∑ z, h' z = 0 → ip (pairLaw (F := F)) (vOp h') g = 0) →
      |ip (coreLaw (F := F)) (recOp (pairLaw (F := F)) Rc (vOp h))
          (recOp (pairLaw (F := F)) Rc g)| ≤
        xg * nrm (pairLaw (F := F)) (vOp h) * nrm (pairLaw (F := F)) g := by
    intro h g h0 hg0 horth
    refine (hC_of_nonstar hm1 hF h5 hτ0 hA hN h g h0 hg0 horth).trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hxg (nrm_nonneg _ _))
      (nrm_nonneg _ _)
  exact l20_prime_caps_full hm1 hF hW h6 hm hm0 hΔ hNA hx hN hC hgate hD0 hD hNns0 hns hstar hεZ
    hχ0 hchi hC1 hH1 f

end Field2

section Prime

variable {p : ℕ} [Fact p.Prime] [Nonempty (CoreT (ZMod p))] [Nonempty (PairT (ZMod p))]

omit [Fact p.Prime] [Nonempty (CoreT (ZMod p))] [Nonempty (PairT (ZMod p))] in
/-- X1's partition sum is nonnegative. -/
theorem partitionSum_nonneg (𝔓 : Finset (Finset (Fin 6 × Fin 6) × Finset (Fin 6 × Fin 6)))
    (rec : Finset (Fin 6 × Fin 6) × Finset (Fin 6 × Fin 6) → LeafRecordData (Fin 6)) {Q : ℝ}
    (hS1 : leafEhat G6 Q 6 < 1) :
    0 ≤ ∑ c ∈ 𝔓, (Real.sqrt p)⁻¹ ^ (rec c).k * leafCoef G6 D20Z Q 6 Ex8 c (rec c) := by
  refine sum_nonneg fun c _ => mul_nonneg (by positivity) ?_
  unfold leafCoef
  have h1 : 0 < 1 - leafEhat G6 Q 6 := by linarith
  positivity

/-- **The caps of L20 over `𝔽_p` with `N_A` from `cor:soft-kernels`(a)**
(`prop:l20-rectangular`(b), `prop:l20-pair-gap`, `prop:l20-collisions`(b)): for an exact
partition `𝔓` of the `221` nonstars of the eight cross pairs `Ex8` into classes with valid leaf
records (`cor:extraction-leaf`(b)), any `N_A` at least X1's partition sum
`∑_c p^{-k_c/2}·leafCoef(c)` (evaluated at a threshold `Q ≤ p`) is a nonstar bound, and the caps
`-C₂₀ ⪯ T ⪯ 1 + χ⁺_p/(1 - H₂₀)` hold. -/
theorem l20_prime_caps_X1 (hm1 : quadraticChar (ZMod p) (-1) = -1) (hW : WeilBound (ZMod p))
    (h4 : FourCycleBound p) (h6 : 6 ≤ Fintype.card (ZMod p)) {m NA xg D mstar Nns χp : ℝ}
    (𝔓 : Finset (Finset (Fin 6 × Fin 6) × Finset (Fin 6 × Fin 6)))
    (h𝔓 : IsExactPartition Ex8 𝔓 (nonstars Ex8))
    (rec : Finset (Fin 6 × Fin 6) × Finset (Fin 6 × Fin 6) → LeafRecordData (Fin 6))
    (hrec : ∀ c ∈ 𝔓, (rec c).Valid Ex8 c) {Q : ℝ} (hQ : 0 < Q) (hQp : Q ≤ p)
    (hS1 : leafEhat G6 Q 6 < 1)
    (hNAle : ∑ c ∈ 𝔓, (Real.sqrt p)⁻¹ ^ (rec c).k * leafCoef G6 D20Z Q 6 Ex8 c (rec c) ≤ NA)
    (hm : (coreLaw (F := ZMod p)).expect (fun C => Kbar C.1 - 1) ≤ m) (hm0 : 0 ≤ m)
    (hΔ : 0 < 30 * (Fintype.card (ZMod p) : ℝ)⁻¹ -
      (2 * (Real.sqrt (Fintype.card (ZMod p)))⁻¹ + NA) ^ 2)
    (hxg : xG (ZMod p) m NA ≤ xg)
    (hgate : cGap (Fintype.card (ZMod p) : ℝ)⁻¹ (tauG (ZMod p) m)
      (2 * (Real.sqrt (Fintype.card (ZMod p)))⁻¹ + NA) xg ≤ sP (ZMod p) m)
    (hD0 : 0 ≤ D)
    (hD : ∀ f, |kernelForm (halfLaw h6) (halfLaw h6) collK f f| ≤ D * nrm (halfLaw h6) f ^ 2)
    (hNns0 : 0 ≤ Nns)
    (hns : ∀ f, |kernelForm (halfLaw h6) (halfLaw h6) nonstar f f| ≤ Nns * nrm (halfLaw h6) f ^ 2)
    (hstar : |kernelForm (halfLaw h6) (halfLaw h6)
      (fun x x' => starPart6 (labels x) (labels x')) (fun _ => 1) (fun _ => 1)| ≤ mstar)
    (hεZ : Nns + D + mstar < 1)
    (hχ0 : 0 ≤ χp)
    (hchi : nrm (halfLaw h6) (fun x => recOp (halfLaw h6) (cutT h6) (fun _ => 1) x - 1) ^ 2 ≤ χp)
    (hC1 : (sP (ZMod p) m * cGap (Fintype.card (ZMod p) : ℝ)⁻¹ (tauG (ZMod p) m)
        (2 * (Real.sqrt (Fintype.card (ZMod p)))⁻¹ + NA) xg /
      prob ((coreLaw (F := ZMod p)).product (pairLaw (F := ZMod p))) Avoid + D) /
        (1 - (Nns + D + mstar)) < 1)
    (hH1 : (Nns + D) / (1 - (Nns + D + mstar)) < 1) (f : CoreT (ZMod p) × PairT (ZMod p) → ℝ) :
    -((sP (ZMod p) m * cGap (Fintype.card (ZMod p) : ℝ)⁻¹ (tauG (ZMod p) m)
        (2 * (Real.sqrt (Fintype.card (ZMod p)))⁻¹ + NA) xg /
        prob ((coreLaw (F := ZMod p)).product (pairLaw (F := ZMod p))) Avoid + D) /
          (1 - (Nns + D + mstar))) *
        nrm (halfLaw h6) f ^ 2 ≤ kernelForm (halfLaw h6) (halfLaw h6) (cutT h6) f f ∧
      kernelForm (halfLaw h6) (halfLaw h6) (cutT h6) f f ≤
        (1 + χp / (1 - (Nns + D) / (1 - (Nns + D + mstar)))) * nrm (halfLaw h6) f ^ 2 := by
  have hp6 : 6 ≤ p := by rwa [ZMod.card] at h6
  have hp2 : p ≠ 2 := by omega
  have hF : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  have hne := injLabellings_G6_nonempty (F := ZMod p) h6
  have hNA : 0 ≤ NA := (partitionSum_nonneg 𝔓 rec hS1).trans hNAle
  have hς : ∀ j k, D20Z j k = 0 ∨ D20Z j k = 1 ∨ D20Z j k = -1 := by decide
  have hEx : ∀ e ∈ Ex8, D20Z e.1 e.2 ≠ 0 := by decide
  have hn : Fintype.card (Fin 6) ≤ 6 := by simp
  have hX1 : ∀ φ h : (Fin 6 → ZMod p) → ℝ,
      |(graphLaw G6 hne).expect (fun z => φ z * (graphLaw G6 hne).expect (fun z' =>
          K6 z z' * h z'))| ≤
        NA * Real.sqrt ((graphLaw G6 hne).expect (fun z => φ z ^ 2)) *
          Real.sqrt ((graphLaw G6 hne).expect (fun z => h z ^ 2)) := by
    intro φ h
    have hb := sk_soft_extraction_leaf_partition_g hW hp2 h4 G6 D20Z hς D20Z_antisymm hne hn Ex8
      hEx 𝔓 h𝔓 rec hrec hQ hQp hS1 (fun _ => 1) (fun _ => by simp) φ h
    refine hb.trans ?_
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hNAle (Real.sqrt_nonneg _))
      (Real.sqrt_nonneg _)
  exact l20_prime_caps_rect hm1 hF hW h6 hm hm0 hΔ hNA
    (fun g _ _ => hN_of_X1 hm1 h6 hne hNA hX1 g) ((xExact_le_xG hm1 hF hW m NA).trans hxg) hgate
    hD0 hD hNns0 hns hstar hεZ hχ0 hchi hC1 hH1 f

end Prime

end Sarkozy.L20Cap
