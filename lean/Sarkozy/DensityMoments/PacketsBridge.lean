module

public import Sarkozy.DensityMoments.PacketsMain
public import Sarkozy.DensityUpgrade.BlockGate
public import Sarkozy.DensityMoments.ExactTypedMixture

/-!
# The certified joint gates feed `lem:density:joint-block-gate`

`paper/sections/31_density_induction_upgrade.tex`, `lem:density:joint-block-gate` and the proof
of `lem:density:packets`. WP-FI's `DensityUpgrade.blockGate_joint_block_gate` proves the analytic
gate from the final sentence of `lem:density:typed-mixture` (its named hypothesis
`blockGateTypedMixture`): a twelve-slot packet `(1 - t) good + t bad` with `good` of unit mixed
`L^{11}`, `bad` with uniform marginals, `log Q ≤ L`, `κ_* > e^{-L(1-κ_*)}` and
`t(β)(1 + C(L)) < 1` has unit mixed `L^{R_*}`. The two numerical premises are exactly what
`middle_joint_gates` certifies for each of the `553` rows.

* `middle_packet_unit_mixed`: for every row and every packet whose bad fraction is at most the
  symmetric or the skew fraction of the row's piece at `r = b^{-1/2}`, `b ≥ β`, and whose
  alphabet has `log Q ≤ L`, the packet has unit mixed `L^{R_*}`, given WP-FI's named hypothesis.
* `middle_packet_unit_mixed_proved`: the same **without named hypotheses**, through
  `exact_joint_block_gate` (`ExactTypedMixture.lean`); the extra curvature premise
  `t(β)(1 + θ_*(θ_*-1)/(κ_*(1-κ_*))) ≤ 1` follows from the coarse fractions
  (`t ≤ 303·10⁻⁶` for `b ≥ X`).
-/

@[expose] public section

namespace Sarkozy.DensityMoments

open Sarkozy.DensityUpgrade

theorem thetaStar_cast : ((thetaStar : ℚ) : ℝ) = blockGateTheta := by
  unfold thetaStar blockGateTheta
  push_cast
  rfl

theorem kappaStar_cast : ((kappaStar : ℚ) : ℝ) = blockGateKappa := by
  unfold kappaStar blockGateKappa
  push_cast
  rfl

theorem mixtureBound_eq (L : ℝ) : mixtureBound L =
    (Real.exp (L * (blockGateTheta - 1)) - 1) /
      (blockGateKappa - Real.exp (-(L * (1 - blockGateKappa)))) := by
  unfold mixtureBound
  rw [thetaStar_cast, kappaStar_cast]

/-- **A certified row gives the moment of `lem:density:joint-block-gate`.** -/
theorem middle_packet_unit_mixed.{u} (hmix : blockGateTypedMixture.{u} 12 blockGateR blockGateS)
    {row : GateRow} (hrow : row ∈ gateRows) {b : ℝ} (hb : (row.beta : ℝ) ≤ b)
    {X : Type u} [Fintype X] [Nonempty X] (hQ : 2 ≤ Fintype.card X)
    (hL : Real.log (Fintype.card X) ≤ row.L) {good bad packet : FiniteLaw (Fin 12 → X)}
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (ht : t ≤ (packetPiece row.piece).sym (1 / Real.sqrt b) ∨
      t ≤ (packetPiece row.piece).skew (1 / Real.sqrt b))
    (hgood : blockGateUnitMixed good 11) (hbad : HasUniformMarginals bad)
    (hpacket : ∀ z, packet.weight z = (1 - t) * good.weight z + t * bad.weight z) :
    blockGateUnitMixed packet blockGateR := by
  obtain ⟨hk, hs, hk'⟩ := middle_joint_gates row hrow b hb
  rw [kappaStar_cast] at hk
  rw [mixtureBound_eq] at hs hk'
  rcases ht with ht | ht
  · exact blockGate_joint_block_gate hmix hQ hL ht0 ht1 ht hgood hbad hpacket hk hs
  · exact blockGate_joint_block_gate hmix hQ hL ht0 ht1 ht hgood hbad hpacket hk hk'

/-- Every row's least-prime bound is at least its piece start. -/
theorem gateRows_beta_ge : ∀ row ∈ gateRows, (packetPiece row.piece).X ≤ row.beta := by
  decide +kernel

/-- The coarse fractions for a piece index. -/
theorem coarse_of_piece {i : ℕ} (hi : i < 33) {b : ℝ} (hb : ((packetPiece i).X : ℝ) ≤ b) :
    (packetPiece i).sym (1 / Real.sqrt b) ≤ 57 / 1000000 ∧
      (packetPiece i).skew (1 / Real.sqrt b) ≤ 303 / 1000000 := by
  have hmem : i ∈ coarseRows.map (fun row => row.piece) := by
    rw [coarseRows_pieces]
    exact List.mem_range.mpr hi
  obtain ⟨row, hrow, hpi⟩ := List.mem_map.mp hmem
  have h := middle_coarse_fractions row hrow b
  rw [hpi] at h
  exact h hb

/-- **A certified row gives the moment of `lem:density:joint-block-gate`, with no named
hypothesis.** -/
theorem middle_packet_unit_mixed_proved {row : GateRow} (hrow : row ∈ gateRows) {b : ℝ}
    (hb : (row.beta : ℝ) ≤ b) {X : Type*} [Fintype X] [Nonempty X] (hQ : 2 ≤ Fintype.card X)
    (hL : Real.log (Fintype.card X) ≤ row.L) {good bad packet : FiniteLaw (Fin 12 → X)}
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (ht : t ≤ (packetPiece row.piece).sym (1 / Real.sqrt b) ∨
      t ≤ (packetPiece row.piece).skew (1 / Real.sqrt b))
    (hgood : blockGateUnitMixed good 11) (hbad : HasUniformMarginals bad)
    (hpacket : ∀ z, packet.weight z = (1 - t) * good.weight z + t * bad.weight z) :
    blockGateUnitMixed packet blockGateR := by
  obtain ⟨hk, hs, hk'⟩ := middle_joint_gates row hrow b hb
  rw [kappaStar_cast] at hk
  rw [mixtureBound_eq] at hs hk'
  have hlt := (gateRows_check row hrow).2
  have hXb : ((packetPiece row.piece).X : ℝ) ≤ b := by
    have := gateRows_beta_ge row hrow
    have h' : ((packetPiece row.piece).X : ℝ) ≤ row.beta := by exact_mod_cast this
    linarith
  obtain ⟨hcs, hck⟩ := coarse_of_piece hlt hXb
  have hc : blockGateTheta * (blockGateTheta - 1) / (blockGateKappa * (1 - blockGateKappa)) ≤ 2 := by
    unfold blockGateTheta blockGateKappa
    norm_num
  have hcpos : 0 ≤ blockGateTheta * (blockGateTheta - 1) /
      (blockGateKappa * (1 - blockGateKappa)) := by
    unfold blockGateTheta blockGateKappa
    norm_num
  rcases ht with ht | ht
  · apply exact_joint_block_gate hQ hL ht0 ht1 ht hgood hbad hpacket hk hs
    have : (0 : ℝ) ≤ (packetPiece row.piece).sym (1 / Real.sqrt b) := ht0.trans ht
    nlinarith
  · apply exact_joint_block_gate hQ hL ht0 ht1 ht hgood hbad hpacket hk hk'
    have : (0 : ℝ) ≤ (packetPiece row.piece).skew (1 / Real.sqrt b) := ht0.trans ht
    nlinarith

end Sarkozy.DensityMoments
