module

public import Sarkozy.Parameters

@[expose] public section

/-!
# The exponents of the upgraded induction, as parameters

`Sarkozy/Parameters.lean` fixes the exponents of the Lean endgame: the paper's record values
`decay = a = 1814179/(2·10⁹)`, `blockScale = K = 863660`, `cancellationDecay = σ = 1/825` and
`momentSlack = η = 1/10000`, and, since 7 November 2026, the baseline `densityExponent = ϑ = 1`
(the paper's record uses the upgraded `ϑ = 1014587/10⁶`). This file makes them data.

* `Params`: the five exponents `(a, ϑ, K, σ, η)` of `thm:density:induction`
  (`paper/sections/31_density_induction_upgrade.tex`). The field names are the names of the
  hard-coded constants, so a hard-coded statement becomes a parametrized one by replacing
  `decay` with `P.decay`, and so on.
* `Params.Valid`: the side conditions that the scalar endgame uses, namely `1 ≤ ϑ < 2`,
  `1 ≤ K` and the uniform error gate `a + (a + η)(ϑ − 1)/(2 − ϑ) < σ` of the proof of
  `thm:density:induction`.
* `Params.InPaperRange`: the parameter range `eq:density:parameter-range`,
  `0 < a ≤ 91/100000`, `1 ≤ ϑ ≤ 1014587/10⁶`, with `σ = 1/825` and `η = 1/10000`. The paper
  states `1 < ϑ` for the upgrade; the endpoint `ϑ = 1` is the baseline `thm:baseline`, which the
  formal endgame uses since 7 November 2026.
  `Params.InPaperRange.valid` is the paper's verification of the error gate on the whole range
  (margin `943271/3284710000`).
* `Params.ofDecay a`: the paper's construction parameters `(ϑ, K, σ, η)` with the price exponent
  `a` left free. Since 7 November 2026 `ϑ = Sarkozy.densityExponent = 1` (the baseline).
  `Params.paper = ofDecay decay` is the record price exponent (at `ϑ = 1`),
  `Params.anchor = ofDecay a₀` is the
  formal exponent `a₀ = 8896611739/10¹³` (the paper's middle charge anchor `\FourRoutesAnchor`
  of `sec:four-routes-closing`, chosen for the formalization on 1 November 2026).

The density saving is `Params.saving P = a/(72 − ϑ)`, the exponent `ε` of
`thm:density:induction`.
-/

namespace Sarkozy.Param

/-- The exponents of the upgraded induction `thm:density:induction`. The induction proves
`Y(L, A) ≤ C L^{-a} α^ϑ` for square-difference-free `A ⊆ [1, K L]`, with density-linear
analytic remainders `O(L^{-σ} α)` and the global moment bound `Y ≤ C_η L^η α²`
(`lem:density:global-moment`). -/
structure Params where
  /-- The price exponent `a` (hard-coded as `Sarkozy.decay`). -/
  decay : ℝ
  /-- The density exponent `ϑ` (hard-coded as `Sarkozy.densityExponent`). -/
  densityExponent : ℝ
  /-- The interval scale `K` (hard-coded as `Sarkozy.blockScale`): scale `L` is `[1, K L]`. -/
  blockScale : ℕ
  /-- The exponent `σ` of the density-linear remainders `L^{-σ} α`
  (hard-coded as `Sarkozy.cancellationDecay`). -/
  cancellationDecay : ℝ
  /-- The slack `η` of the global moment bound (hard-coded as `Sarkozy.momentSlack`). -/
  momentSlack : ℝ

namespace Params

variable (P : Params)

/-- `(ϑ − 1)/(2 − ϑ)`, the exponent of the inverse density forced by the global moment. -/
noncomputable def densityRatio : ℝ := (P.densityExponent - 1) / (2 - P.densityExponent)

/-- `σ − a − (a + η)(ϑ − 1)/(2 − ϑ)`: the decay of a density-linear remainder relative to the
energy at a least counterexample (proof of `thm:density:induction`). -/
noncomputable def relativeErrorDecay : ℝ :=
  P.cancellationDecay - P.decay - (P.decay + P.momentSlack) * P.densityRatio

/-- The density saving `ε = a/(72 − ϑ)` of `thm:density:induction`. -/
noncomputable def saving : ℝ := P.decay / ((slots : ℝ) - P.densityExponent)

/-- **Side conditions of the scalar endgame** (proof of `thm:density:induction`).

* `1 ≤ ϑ < 2`: used to turn the global moment bound into a lower bound for the density;
* `1 ≤ K`: the interval embedding `[1, N] ⊆ [1, K N]`;
* the uniform error gate `a + (a + η)(ϑ − 1)/(2 − ϑ) < σ`: a density-linear remainder divided by
  the energy is then `o(1)` uniformly at least counterexamples.

`0 < a` is not needed by the implication; it holds in the paper's range (`InPaperRange`). -/
structure Valid : Prop where
  one_le_densityExponent : 1 ≤ P.densityExponent
  densityExponent_lt_two : P.densityExponent < 2
  one_le_blockScale : 1 ≤ P.blockScale
  error_gate : P.decay + (P.decay + P.momentSlack) * P.densityRatio < P.cancellationDecay

namespace Valid

variable {P}

theorem densityExponent_pos (h : P.Valid) : 0 < P.densityExponent :=
  lt_of_lt_of_le zero_lt_one h.one_le_densityExponent

theorem densityExponent_ne_zero (h : P.Valid) : P.densityExponent ≠ 0 :=
  h.densityExponent_pos.ne'

theorem two_sub_pos (h : P.Valid) : 0 < 2 - P.densityExponent := by
  linarith [h.densityExponent_lt_two]

/-- The degree gap `72 − ϑ` is positive. -/
theorem degree_gap_pos (h : P.Valid) : 0 < (slots : ℝ) - P.densityExponent := by
  have := h.densityExponent_lt_two
  norm_num [slots]
  linarith

theorem densityRatio_nonneg (h : P.Valid) : 0 ≤ P.densityRatio :=
  div_nonneg (by linarith [h.one_le_densityExponent]) h.two_sub_pos.le

theorem relativeErrorDecay_pos (h : P.Valid) : 0 < P.relativeErrorDecay := by
  have := h.error_gate
  unfold relativeErrorDecay
  linarith

theorem blockScale_pos (h : P.Valid) : 0 < P.blockScale :=
  lt_of_lt_of_le zero_lt_one h.one_le_blockScale

theorem blockScale_real_pos (h : P.Valid) : (0 : ℝ) < P.blockScale := by
  exact_mod_cast h.blockScale_pos

end Valid

/-- **The parameter range `eq:density:parameter-range`** of `sec:density-upgrade`:
`0 < a ≤ 91/100000`, `1 ≤ ϑ ≤ θ_* = 1014587/1000000` (closed at the baseline endpoint `ϑ = 1`;
the paper states `1 < ϑ` for the upgrade), with the cancellation exponent
`σ = 1/825` and the moment slack `η = 1/10000` of the proof of `thm:density:induction`. -/
structure InPaperRange : Prop where
  decay_pos : 0 < P.decay
  decay_le : P.decay ≤ 91 / 100000
  one_le_densityExponent : 1 ≤ P.densityExponent
  densityExponent_le : P.densityExponent ≤ 1014587 / 1000000
  cancellationDecay_eq : P.cancellationDecay = 1 / 825
  momentSlack_eq : P.momentSlack = 1 / 10000

/-- `(ϑ − 1)/(2 − ϑ) ≤ 14587/985413` on the paper's range. -/
theorem InPaperRange.densityRatio_le {P : Params} (h : P.InPaperRange) :
    P.densityRatio ≤ 14587 / 985413 := by
  have h1 := h.densityExponent_le
  have h2 : 0 < 2 - P.densityExponent := by linarith
  unfold densityRatio
  rw [div_le_iff₀ h2]
  linarith

/-- **The uniform error gate of `thm:density:induction`.** On the whole parameter range,
`a + (a + η)(ϑ − 1)/(2 − ϑ) ≤ 91/100000 + (101/100000)(14587/985413) < 1/825 = σ`, with margin
`943271/3284710000` (`Sarkozy.uniform_error_margin`). Together with `1 ≤ K` this gives `Valid`. -/
theorem InPaperRange.valid {P : Params} (h : P.InPaperRange) (hK : 1 ≤ P.blockScale) :
    P.Valid := by
  have hθ1 := h.one_le_densityExponent
  have hθ2 := h.densityExponent_le
  have h2 : 0 < 2 - P.densityExponent := by linarith
  have hρ0 : 0 ≤ P.densityRatio := div_nonneg (by linarith) h2.le
  have hρ := h.densityRatio_le
  have ha0 := h.decay_pos
  have ha := h.decay_le
  have hη := h.momentSlack_eq
  have hσ := h.cancellationDecay_eq
  refine ⟨hθ1, by linarith, hK, ?_⟩
  have hsum0 : 0 ≤ P.decay + P.momentSlack := by rw [hη]; linarith
  have hprod : (P.decay + P.momentSlack) * P.densityRatio ≤
      (101 / 100000) * (14587 / 985413) :=
    mul_le_mul (by rw [hη]; linarith) hρ hρ0 (by norm_num)
  have hgate := uniform_error_margin
  rw [hσ]
  linarith

/-! ## The paper's construction with a free price exponent -/

/-- The paper's construction parameters `ϑ = Sarkozy.densityExponent = 1` (the baseline, since
7 November 2026; the paper's record uses `ϑ = 1014587/10⁶`), `K = 863660`, `σ = 1/825`,
`η = 1/10000`, with the price exponent `a` free. -/
noncomputable def ofDecay (a : ℝ) : Params where
  decay := a
  densityExponent := Sarkozy.densityExponent
  blockScale := Sarkozy.blockScale
  cancellationDecay := Sarkozy.cancellationDecay
  momentSlack := Sarkozy.momentSlack

/-- The paper's record price exponent `a = 1814179/(2·10⁹)` (`\FourRoutesA`), at the construction
parameters of `ofDecay` (since 7 November 2026 `ϑ = 1`, not the record's `ϑ = 1014587/10⁶`). -/
noncomputable def paper : Params := ofDecay Sarkozy.decay

/-- The formal price exponent `a₀ = 8896611739/10¹³`: the middle charge anchor
`\FourRoutesAnchor` of `sec:four-routes-closing`, at which the middle charges need no
repricing (`t = e^{2(a − a₀)570} = 1`). -/
noncomputable def anchorDecay : ℝ := 8896611739 / 10000000000000

/-- The parameters of the formalization (user decision of 1 November 2026): the paper's
construction at the price exponent `a₀ = anchorDecay`. -/
noncomputable def anchor : Params := ofDecay anchorDecay

theorem ofDecay_inPaperRange {a : ℝ} (ha0 : 0 < a) (ha : a ≤ 91 / 100000) :
    (ofDecay a).InPaperRange where
  decay_pos := ha0
  decay_le := ha
  one_le_densityExponent := by norm_num [ofDecay, Sarkozy.densityExponent]
  densityExponent_le := by norm_num [ofDecay, Sarkozy.densityExponent]
  cancellationDecay_eq := by norm_num [ofDecay, Sarkozy.cancellationDecay]
  momentSlack_eq := by norm_num [ofDecay, Sarkozy.momentSlack]

/-- Every price exponent `a ≤ 91/100000` passes the side conditions at the paper's
`(ϑ, K, σ, η)`; positivity of `a` is not needed here, since the gate is increasing in `a`. -/
theorem ofDecay_valid {a : ℝ} (ha : a ≤ 91 / 100000) : (ofDecay a).Valid := by
  refine ⟨by norm_num [ofDecay, Sarkozy.densityExponent],
    by norm_num [ofDecay, Sarkozy.densityExponent],
    by norm_num [ofDecay, Sarkozy.blockScale], ?_⟩
  simp only [ofDecay, densityRatio, Sarkozy.densityExponent, Sarkozy.momentSlack,
    Sarkozy.cancellationDecay]
  norm_num
  linarith

/-- **The exact range of the side conditions** at `(ϑ, K, σ, η) = (1, 863660, 1/825, 1/10⁴)`:
since `ρ = (ϑ − 1)/(2 − ϑ) = 0` at the baseline, they hold if and only if `a < σ = 1/825`.
(At the paper's upgraded `ϑ = 1014587/10⁶` the bound was `11929813/10¹⁰`.) -/
theorem ofDecay_valid_iff (a : ℝ) : (ofDecay a).Valid ↔ a < 1 / 825 := by
  have hgate : (ofDecay a).decay + ((ofDecay a).decay + (ofDecay a).momentSlack) *
      (ofDecay a).densityRatio < (ofDecay a).cancellationDecay ↔ a < 1 / 825 := by
    simp only [ofDecay, densityRatio, Sarkozy.densityExponent, Sarkozy.momentSlack,
      Sarkozy.cancellationDecay]
    norm_num
  constructor
  · exact fun h => hgate.mp h.error_gate
  · intro h
    exact ⟨by norm_num [ofDecay, Sarkozy.densityExponent],
      by norm_num [ofDecay, Sarkozy.densityExponent],
      by norm_num [ofDecay, Sarkozy.blockScale], hgate.mpr h⟩

theorem paper_valid : paper.Valid := ofDecay_valid (by norm_num [Sarkozy.decay])

theorem anchor_valid : anchor.Valid := ofDecay_valid (by norm_num [anchorDecay])

theorem paper_inPaperRange : paper.InPaperRange :=
  ofDecay_inPaperRange (by norm_num [Sarkozy.decay]) (by norm_num [Sarkozy.decay])

theorem anchor_inPaperRange : anchor.InPaperRange :=
  ofDecay_inPaperRange (by norm_num [anchorDecay]) (by norm_num [anchorDecay])

/-- The anchor lies below the record exponent: `a₀/a ≈ 0.9808`. -/
theorem anchorDecay_lt_decay : anchorDecay < Sarkozy.decay := by
  norm_num [anchorDecay, Sarkozy.decay]

theorem ofDecay_saving (a : ℝ) :
    (ofDecay a).saving = a / ((slots : ℝ) - Sarkozy.densityExponent) := rfl

/-- At the record parameters the saving is the hard-coded `Sarkozy.saving`. -/
theorem paper_saving : paper.saving = Sarkozy.saving := Sarkozy.saving_eq.symm

/-- The saving at the anchor, `ε′ = a₀/(72 − ϑ) = a₀/71 = 8896611739/710000000000000
≈ 1.25304·10⁻⁵` (at the baseline `ϑ = 1`). -/
theorem anchor_saving : anchor.saving = 8896611739 / 710000000000000 := by
  norm_num [saving, anchor, ofDecay, anchorDecay, slots, Sarkozy.densityExponent]

/-- The relative-error decay at the anchor, `σ − a₀ − (a₀ + η)ρ = σ − a₀ ≈ 3.2246·10⁻⁴` (at the
baseline `ρ = 0`; at the paper's record `a` it is `20132093/66000000000 ≈ 3.050·10⁻⁴`). -/
theorem anchor_relativeErrorDecay : anchor.relativeErrorDecay = 106411812613 / 330000000000000 := by
  norm_num [relativeErrorDecay, densityRatio, anchor, ofDecay, anchorDecay,
    Sarkozy.densityExponent, Sarkozy.momentSlack, Sarkozy.cancellationDecay]

theorem paper_relativeErrorDecay_eq : paper.relativeErrorDecay = 20132093 / 66000000000 := by
  norm_num [relativeErrorDecay, densityRatio, paper, ofDecay, Sarkozy.decay,
    Sarkozy.densityExponent, Sarkozy.momentSlack, Sarkozy.cancellationDecay]

theorem paper_densityRatio : paper.densityRatio = Sarkozy.densityRatio := rfl

theorem paper_relativeErrorDecay : paper.relativeErrorDecay = Sarkozy.relativeErrorDecay := rfl

end Params

end Sarkozy.Param
