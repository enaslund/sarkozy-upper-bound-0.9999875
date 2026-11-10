module

public import Sarkozy.SpectralD.RootCuts
public import Sarkozy.SpectralD.CxInputs

/-!
# The root cuts: (S1) from `2^52` and the cross bound `Λ_D`

`paper/sections/25_upper_reference.tex`, `subsec:record:upper_root`, the setting: for LL20 and
LL22 (`Sarkozy.SpectralD.Root.LL20`, `LL22`), with `n = 36` and `Δ = 20`, the threshold
hypothesis (S1) of `def:spec:data` is `e_20(p, 72) < 1` and `p > 4n² = 5184`.

* `coarseErr_antitone`: `q ↦ e_t(q, n)` is antitone on `q > 0`;
* `coarseErr_two_pow_52`: `e_20(2^52, 72) = 75497489/536870912 ≈ 0.1406`;
* `coarseErr_root_lt`: **(S1) holds from `2^52` on**: `e_20(q, 72) < 1` for every real
  `q ≥ 2^52`; `LL20_S1`, `LL22_S1`: (S1) in the form `Cuts.SpecData.S1` of `def:spec:data`;
* `LL20_deltaE`, `LL22_deltaE`: `‖Δ^E‖ ≤ 12` (LL20) and `‖Δ^E‖ ≤ 10` (LL22) at every prime,
  the hypothesis `hDE` of `cor:spec2:coupling` with `Λ_D = max_k r_k`, from
  `Sarkozy.SpectralD.Cx.deltaE_normLe` and the cross degrees;
* `LL20_hne`, `LL22_hne`: `Inj_p(G) ≠ ∅` for primes `p ≥ 2^52`, from `thm:weil`
  (`Cuts.SpecData.inj_nonempty`).

New material for this paper.
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace Sarkozy.SpectralD.Root

open Sarkozy Sarkozy.SpectralC

/-! ### (S1) -/

/-- `e_t(q, n)` is antitone in `q > 0`. -/
theorem coarseErr_antitone {q q' : ℝ} (hq : 0 < q) (hqq : q ≤ q') (t n : ℕ) :
    TraceMixing.coarseErr q' t n ≤ TraceMixing.coarseErr q t n := by
  unfold TraceMixing.coarseErr
  have hH := TraceMixing.coarseH_nonneg t
  have hs0 : 0 < Real.sqrt q := Real.sqrt_pos.mpr hq
  have h1 : (Real.sqrt q')⁻¹ ≤ (Real.sqrt q)⁻¹ := inv_anti₀ hs0 (Real.sqrt_le_sqrt hqq)
  have h2 : (n : ℝ) / q' ≤ n / q := div_le_div_of_nonneg_left (Nat.cast_nonneg _) hq hqq
  have h3 := mul_le_mul_of_nonneg_left h1 hH
  have h2t : (0 : ℝ) ≤ 2 ^ t := by positivity
  exact mul_le_mul_of_nonneg_left (by linarith) h2t

theorem sqrt_two_pow_52 : Real.sqrt ((2 : ℝ) ^ 52) = 2 ^ 26 := by
  rw [show (2 : ℝ) ^ 52 = (2 ^ 26) ^ 2 by norm_num]
  exact Real.sqrt_sq (by norm_num)

/-- `e_20(2^52, 72) = 2^20 ((9 + 2^{-20}) 2^{-26} + 72 · 2^{-52}) = 75497489/536870912`. -/
theorem coarseErr_two_pow_52 :
    TraceMixing.coarseErr (2 ^ 52) 20 72 = 75497489 / 536870912 := by
  unfold TraceMixing.coarseErr
  rw [sqrt_two_pow_52]
  norm_num

/-- **(S1) for the root cuts from `2^52`** (`subsec:record:upper_root`): `e_20(q, 72) < 1` for
every real `q ≥ 2^52`. -/
theorem coarseErr_root_lt {q : ℝ} (hq : 2 ^ 52 ≤ q) : TraceMixing.coarseErr q 20 72 < 1 := by
  refine lt_of_le_of_lt (coarseErr_antitone (by norm_num) hq 20 72) ?_
  rw [coarseErr_two_pow_52]
  norm_num

/-- (S1) at a natural number `p ≥ 2^52`, in the form `hS1` of
`Sarkozy.SpectralD.Cx.spectral_criterion_cut_S1` (`Δ = 20`, `n' = 72`). -/
theorem coarseErr_root_lt_nat {p : ℕ} (hp : 2 ^ 52 ≤ p) :
    TraceMixing.coarseErr p 20 72 < 1 :=
  coarseErr_root_lt (by exact_mod_cast hp)

/-- **(S1) of `def:spec:data` for LL20** at every `p₀ ≥ 2^52`: `e_Δ(p₀, 2n) < 1` and
`p₀ > 4n²`, with `Δ = 20`, `n = 36`. -/
theorem LL20_S1 {p₀ : ℝ} (hp : 2 ^ 52 ≤ p₀) :
    LL20.S1 (fun t => TraceMixing.coarseErr p₀ t 72) p₀ := by
  refine ⟨?_, ?_⟩
  · rw [LL20_Delta]
    exact coarseErr_root_lt hp
  · rw [LL20_n]
    norm_num
    linarith

/-- **(S1) of `def:spec:data` for LL22** at every `p₀ ≥ 2^52`. -/
theorem LL22_S1 {p₀ : ℝ} (hp : 2 ^ 52 ≤ p₀) :
    LL22.S1 (fun t => TraceMixing.coarseErr p₀ t 72) p₀ := by
  refine ⟨?_, ?_⟩
  · rw [LL22_Delta]
    exact coarseErr_root_lt hp
  · rw [LL22_n]
    norm_num
    linarith

/-! ### `Λ_D` -/

/-- **`Λ_D` for LL20**: `‖Δ^E‖ ≤ 12` at every prime (`cor:spec2:coupling`, hypothesis `hDE`). -/
theorem LL20_deltaE {p : ℕ} [Fact p.Prime] : NormLe (deltaE (Cx.sgnZ (p := p) LL20)) 12 :=
  Cx.deltaE_normLe LL20 (fun k => by exact_mod_cast LL20_r_le k)

/-- **`Λ_D` for LL22**: `‖Δ^E‖ ≤ 10` at every prime (`cor:spec2:coupling`, hypothesis `hDE`). -/
theorem LL22_deltaE {p : ℕ} [Fact p.Prime] : NormLe (deltaE (Cx.sgnZ (p := p) LL22)) 10 :=
  Cx.deltaE_normLe LL22 (fun k => by exact_mod_cast LL22_r_le k)

/-! ### `Inj_p(G) ≠ ∅` -/

/-- `Inj_p(G) ≠ ∅` for the root at primes `p ≥ 2^52`, from `thm:weil`. -/
theorem LL20_hne (hW : Target.Weil) {p : ℕ} [Fact p.Prime] (hp : 2 ^ 52 ≤ p) :
    (Labellings.injLabellings (ZMod p) LL20.G).Nonempty := by
  have hp2 : p ≠ 2 := by omega
  refine LL20.inj_nonempty (Labellings.weilBound_of_target hW p hp2) card_slot.le
    (fun t ht => ?_)
  rw [LL20_Delta] at ht
  rw [ZMod.card]
  exact lt_of_le_of_lt (TraceMixing.coarseErr_mono (by positivity) ht le_rfl)
    (coarseErr_root_lt_nat hp)

/-- `Inj_p(G) ≠ ∅` for the root at primes `p ≥ 2^52`, from `thm:weil`. -/
theorem LL22_hne (hW : Target.Weil) {p : ℕ} [Fact p.Prime] (hp : 2 ^ 52 ≤ p) :
    (Labellings.injLabellings (ZMod p) LL22.G).Nonempty := by
  have hp2 : p ≠ 2 := by omega
  refine LL22.inj_nonempty (Labellings.weilBound_of_target hW p hp2) card_slot.le
    (fun t ht => ?_)
  rw [LL22_Delta] at ht
  rw [ZMod.card]
  exact lt_of_le_of_lt (TraceMixing.coarseErr_mono (by positivity) ht le_rfl)
    (coarseErr_root_lt_nat hp)

end Sarkozy.SpectralD.Root
