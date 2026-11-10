module

public import Sarkozy.DensityMoments.PacketGateData

/-!
# The middle gates of `lem:density:packets` (`cert:density:packets`)

`paper/sections/31_density_induction_upgrade.tex`, proof of `lem:density:packets`, with the
gate `eq:density:joint-block-gate` of `lem:density:joint-block-gate`.

* `middle_joint_gates`: **the joint block-size gates.** For each of the `553` rows
  (`526` groups of the authenticated budget-570 histogram in the first six pieces, then one row
  for each of the `27` later pieces), at every least prime `b ≥ β` of the row,
  `κ_* > e^{-L(1-κ_*)}` and both gates `t (1 + C(L)) < 1` hold, for the symmetric and the skew
  bad fraction at `r = b^{-1/2}`, with `C(L) = (e^{L(θ_*-1)} - 1)/(κ_* - e^{-L(1-κ_*)})`.
* `middle_coarse_fractions`: **`eq:density:middle-bad-fractions`**: at every least prime
  `b ≥ X` of each of the `33` pieces, the symmetric bad fraction is at most `57·10⁻⁶` and the skew
  one at most `303·10⁻⁶`.

The rows and coefficients are data (`PacketGateData.lean`): the assigned envelope coefficients
of the pieces and, for each row, the least-prime bound `β` and the log bound `L` of
`lem:density:joint-block-gate` (`L = 570 k/2^{16}` for histogram bucket `k`, or
`min(570, n log Y)` for the cardinality bound). Their provenance (the authenticated histogram,
the piece partition and the assignments of `def:closing-quantities`) is not formalized. The
analytic implication from a passing gate to a unit mixed moment (`lem:density:joint-block-gate`,
which uses the exact mixture coefficient of `lem:density:typed-mixture`) is not formalized
either.
-/

@[expose] public section

namespace Sarkozy.DensityMoments

theorem gateRows_count : gateRows.length = 553 := gateRows_length

/-- **The joint block-size gates of `lem:density:packets`.** -/
theorem middle_joint_gates : ∀ row ∈ gateRows, ∀ b : ℝ, (row.beta : ℝ) ≤ b →
    Real.exp (-((row.L : ℝ) * (1 - (kappaStar : ℝ)))) < kappaStar ∧
      (packetPiece row.piece).sym (1 / Real.sqrt b) * (1 + mixtureBound row.L) < 1 ∧
      (packetPiece row.piece).skew (1 / Real.sqrt b) * (1 + mixtureBound row.L) < 1 := by
  intro row hrow b hb
  obtain ⟨hc, hlt⟩ := gateRows_check row hrow
  have hP := packetPiece_valid row.piece hlt
  have hr := GateRow.rsqrt_le hc.1 hc.2.2.1 hb
  have hβ : (1 : ℝ) ≤ row.beta := by
    have h1 : (1 : ℚ) ≤ row.rb ^ 2 * (row.beta : ℚ) := hc.2.2.1
    have h2 : row.rb < 1 := hc.2.1
    have h3 : 0 < row.rb := hc.1
    have h4 : (1 : ℚ) ≤ row.beta := by
      by_contra hcon
      push Not at hcon
      have : row.rb ^ 2 * (row.beta : ℚ) < 1 := by
        have hb0 : (0 : ℚ) ≤ row.beta := Nat.cast_nonneg _
        have hr2 : row.rb ^ 2 < 1 := by nlinarith
        nlinarith
      linarith
    exact_mod_cast h4
  have hpos : 0 < 1 / Real.sqrt b := by
    have : 0 < b := by linarith
    positivity
  exact row.sound hP hc hpos hr

/-- **The gate table of `lem:density:packets`**: at every least prime `b ≥ β` of every row, both
gates are at most the table bound of the row's piece (`.999905396`, `.997725686`, `.995610104`,
`.993840613`, `.993514967`, `.991403303` in the first six pieces, `.830800905` in each later one),
and at most the exact worst bound `7811760900169/7812500000000 < 1`. The rows per piece are
`87, 88, 70, 19, 87, 175` and then one (`gateRows_per_piece`). -/
theorem middle_gate_table : ∀ row ∈ gateRows, ∀ b : ℝ, (row.beta : ℝ) ≤ b →
    max ((packetPiece row.piece).sym (1 / Real.sqrt b) * (1 + mixtureBound row.L))
        ((packetPiece row.piece).skew (1 / Real.sqrt b) * (1 + mixtureBound row.L)) ≤
      (gateTableBound row.piece : ℝ) ∧
    max ((packetPiece row.piece).sym (1 / Real.sqrt b) * (1 + mixtureBound row.L))
        ((packetPiece row.piece).skew (1 / Real.sqrt b) * (1 + mixtureBound row.L)) ≤
      7811760900169 / 7812500000000 := by
  intro row hrow b hb
  obtain ⟨hc, hlt, htab, hworst⟩ := gateRows_full row hrow
  have hP := packetPiece_valid row.piece hlt
  have hr := GateRow.rsqrt_le hc.1 hc.2.2.1 hb
  have hβ : (1 : ℝ) ≤ row.beta := by
    have h1 : (1 : ℚ) ≤ row.rb ^ 2 * (row.beta : ℚ) := hc.2.2.1
    have h2 : row.rb < 1 := hc.2.1
    have h3 : 0 < row.rb := hc.1
    have h4 : (1 : ℚ) ≤ row.beta := by
      by_contra hcon
      push Not at hcon
      have : row.rb ^ 2 * (row.beta : ℚ) < 1 := by
        have hb0 : (0 : ℚ) ≤ row.beta := Nat.cast_nonneg _
        have hr2 : row.rb ^ 2 < 1 := by nlinarith
        nlinarith
      linarith
    exact_mod_cast h4
  have hpos : 0 < 1 / Real.sqrt b := by
    have : 0 < b := by linarith
    positivity
  obtain ⟨hs, hk⟩ := row.sound_le hP hc hpos hr
  have htab' : ((row.value (packetPiece row.piece) : ℚ) : ℝ) ≤ (gateTableBound row.piece : ℝ) := by
    exact_mod_cast htab
  have hworst' : ((row.value (packetPiece row.piece) : ℚ) : ℝ) ≤
      ((7811760900169 / 7812500000000 : ℚ) : ℝ) := by exact_mod_cast hworst
  push_cast at hworst'
  exact ⟨max_le (hs.trans htab') (hk.trans htab'), max_le (hs.trans hworst') (hk.trans hworst')⟩

/-- **`eq:density:middle-bad-fractions`**: at every least prime `b ≥ X` of each of the `33` pieces,
the symmetric and skew bad fractions are at most `57·10⁻⁶` and `303·10⁻⁶`. -/
theorem middle_coarse_fractions : ∀ row ∈ coarseRows, ∀ b : ℝ,
    ((packetPiece row.piece).X : ℝ) ≤ b →
    (packetPiece row.piece).sym (1 / Real.sqrt b) ≤ 57 / 1000000 ∧
      (packetPiece row.piece).skew (1 / Real.sqrt b) ≤ 303 / 1000000 := by
  intro row hrow b hb
  have hc := coarseRows_check row hrow
  have hlt : row.piece < 33 := by
    have : ∀ row ∈ coarseRows, row.piece < 33 := by decide +kernel
    exact this row hrow
  exact CoarseRow.sound (packetPiece_valid row.piece hlt) hc hb

/-- The coarse rows cover the 33 pieces. -/
theorem coarseRows_pieces : coarseRows.map (fun row => row.piece) = List.range 33 := by
  decide +kernel

end Sarkozy.DensityMoments
