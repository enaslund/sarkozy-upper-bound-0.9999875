module

public import Sarkozy.JointClosing.Endgame

@[expose] public section

/-!
# The joint bound from a joint allocation on labelled diagonals

`paper/sections/11_comparison_proof.tex`, `cor:joint-closing` ("positive comparison energies and
negative mean energies may first be combined on the same labelled diagonal. If their residual
coefficients are nonnegative, their common energies may then be bounded by upper prices");
`paper/sections/24a_joint_mean.tex`, end of the proof of `prop:joint-middle-mean` ("For a labelled
diagonal energy `Z`, combine its comparison coefficient `c` and retained mean coefficient `b` as
`(63c − b)Z` first. The finite checks below show `63c − b ≥ 0` … This proves the proposition
without asserting a lower bound for any isolated upper-priced mean term").

`JointAllocation D H` is the abstract form of that argument, at every scale `L`, over a finite
set `ι L` of labelled positive diagonals with energies `Z_i`:
* (J1) **comparison at energy level** (`lem:record:record-expansion`, with (E1) on the parts that are
  not shared): `(2^k − 1)(Y_λ − Y_ν) ≤ ∑_i c_i Z_i + (κ + o(1)) Y`, robustly;
* (J2) **mean at energy level** (`prop:record:mean-credit`, Steps 1–2, the one-block credits `m₁`,
  the higher terms kept as energies): `½(e_L + e_R) ≥ (m₁ − o(1)) Y + ∑_i b_i Z_i`, robustly;
* (J3) **upper prices of the shared diagonals** (`lem:bracket-energy`, (E1)):
  `Z_i ≤ (u_i + o(1) v_i) Y + r_i`, robustly, the remainders weighted by the residuals adding up
  to a density-linear remainder;
* (J4) **the residual gates** (`cert:four-routes-closing`, the `192` residuals `63c − b`):
  `b_i ≤ c_i`, and `κ + ∑_i (c_i − b_i) u_i ≤ 2^k H − 1 + m₁` at every scale.

**`JointAllocation.jointBound`**: (J1)–(J4) give `JointBound D H`. The residual gate `b_i ≤ c_i` is
used exactly where the paper uses it: to apply the upper prices of (J3) to `(c_i − b_i) Z_i`.

**`JointAllocation.ofSeparate`**: the separate route is the case of no shared diagonal
(`ι = ∅`, `κ = (2^k − 1)𝓔`, `m₁ = MC.m`, `H = jointConstantC k 𝓔 m`), so the shape is satisfiable
whenever the separate bounds are.
-/

open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.JointClosing

open Sarkozy.TheoremC Sarkozy.TheoremCBlock
open Sarkozy.Param (Params)
open Sarkozy.BlockFrame
open Sarkozy.FourierArithmetic Sarkozy.Functional Sarkozy.IndexSupport Sarkozy.Comparison
  Sarkozy.PaperFrame Sarkozy.RecordExpansion Sarkozy.RecordExpansion.Choice

variable {a : ℝ}
  {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

/-- **A joint allocation on labelled diagonals** (`cor:joint-closing`, the combination step of
`prop:joint-middle-mean` and `prop:joint-upper-mean`), with joint constant `H`; see the module
docstring for (J1)–(J4). -/
structure JointAllocation (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (H : ℝ) where
  /-- The labelled diagonals shared by the comparison and the mean expansions. -/
  ι : ℕ → Type
  [ιFintype : ∀ L, Fintype (ι L)]
  /-- Their energies `Z_i = Y_{D_i}` at a counterexample. -/
  Z : ∀ L, Finset ℤ → ι L → ℝ
  /-- Comparison coefficients `c_i`, mean coefficients `b_i`. -/
  c : ∀ L, ι L → ℝ
  b : ∀ L, ι L → ℝ
  /-- The comparison constant `κ` of the parts on no shared diagonal, and the separate mean credit
  `m₁` (one-block credits). -/
  κ : ℝ
  m₁ : ℝ
  /-- (J1) The comparison loss at energy level. -/
  comparison : ∃ ε₁ : ℕ → ℝ, Tendsto ε₁ atTop (𝓝 0) ∧ ∃ c₁ : ℝ, 0 ≤ c₁ ∧
    Param.AtCounterexamples (Params.ofDecay a) D.Y fun L A =>
      (2 ^ Fintype.card E - 1) * (energyFirst D.FS.lam (blockLift m₀ blk p) L A -
          energyComparison D.CL.ν (blockLift m₀ blk p) L A) ≤
        ∑ i, c L i * Z L A i + (κ + ε₁ L) * D.Y L A + remainder c₁ L A
  /-- (J2) The mean energies at energy level. -/
  mean : ∃ ε₂ : ℕ → ℝ, Tendsto ε₂ atTop (𝓝 0) ∧ ∃ c₂ : ℝ, 0 ≤ c₂ ∧
    Param.AtCounterexamples (Params.ofDecay a) D.Y fun L A =>
      (m₁ - ε₂ L) * D.Y L A + ∑ i, b L i * Z L A i - remainder c₂ L A ≤
        (energyMean (blockLift m₀ blk p) D.ME.ML L A +
          energyMean (blockLift m₀ blk p) D.ME.MR L A) / 2
  /-- The upper prices `u_i` and the error weights `v_i` of the shared diagonals. -/
  u : ∀ L, ι L → ℝ
  v : ∀ L, ι L → ℝ
  /-- (J3) The upper prices, robustly, with residual-weighted remainders. -/
  upper : ∃ ε₃ : ℕ → ℝ, (∀ L, 0 ≤ ε₃ L) ∧ Tendsto ε₃ atTop (𝓝 0) ∧ ∃ V c₃ : ℝ, 0 ≤ c₃ ∧
    (∀ L, ∑ i, (c L i - b L i) * v L i ≤ V) ∧ ∃ r : ∀ L, Finset ℤ → ι L → ℝ,
    Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
      ∀ i, Z L A i ≤ (u L i + ε₃ L * v L i) * D.Y L A + r L A i) ∧
    Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
      ∑ i, (c L i - b L i) * r L A i ≤ remainder c₃ L A)
  /-- (J4) The residual coefficients are nonnegative. -/
  resid_nonneg : ∀ L i, b L i ≤ c L i
  /-- (J4) The evaluated residual series closes with the joint constant `H`. -/
  gate : ∀ L, κ + ∑ i, (c L i - b L i) * u L i ≤ 2 ^ Fintype.card E * H - 1 + m₁

attribute [instance] JointAllocation.ιFintype

theorem remainder_add (c₁ c₂ : ℝ) (L : ℕ) (A : Finset ℤ) :
    remainder (c₁ + c₂) L A = remainder c₁ L A + remainder c₂ L A := by
  unfold remainder
  ring

omit [DecidableEq P] in
/-- **The joint bound from a joint allocation** (`cor:joint-closing`): combine the comparison and
mean coefficients on each labelled diagonal first, then bound the nonnegative residuals
`(c_i − b_i) Z_i` by the upper prices. -/
theorem JointAllocation.jointBound {D : TheoremCBlock.ComparisonData a m₀ blk p pr h E} {H : ℝ}
    (JA : JointAllocation D H) : JointBound D H := by
  obtain ⟨ε₁, hε₁, c₁, hc₁, h1⟩ := JA.comparison
  obtain ⟨ε₂, hε₂, c₂, hc₂, h2⟩ := JA.mean
  obtain ⟨ε₃, hε₃0, hε₃, V, c₃, hc₃, hV, r, h3, h3r⟩ := JA.upper
  refine ⟨fun L => ε₁ L + ε₂ L + ε₃ L * V, ?_, c₁ + c₂ + c₃, by positivity, ?_⟩
  · have := (hε₁.add hε₂).add (hε₃.mul_const V)
    simpa only [add_zero, zero_mul] using this
  · unfold Param.AtCounterexamples at h1 h2 h3 h3r ⊢
    filter_upwards [h1, h2, h3, h3r] with L hL1 hL2 hL3 hL3r
    intro C hC hk A hAd hY
    have hYpos := Param.counterexample_pos (Params.ofDecay a) hC hY
    have e1 := hL1 C hC hk A hAd hY
    have e2 := hL2 C hC hk A hAd hY
    have e3 := hL3 C hC hk A hAd hY
    have e3r := hL3r C hC hk A hAd hY
    -- the residual series
    have hres : ∑ i, (JA.c L i - JA.b L i) * JA.Z L A i ≤
        (∑ i, (JA.c L i - JA.b L i) * JA.u L i) * D.Y L A +
          ε₃ L * (∑ i, (JA.c L i - JA.b L i) * JA.v L i) * D.Y L A +
          ∑ i, (JA.c L i - JA.b L i) * r L A i := by
      have hterm : ∀ i, (JA.c L i - JA.b L i) * JA.Z L A i ≤
          (JA.c L i - JA.b L i) * JA.u L i * D.Y L A +
            ε₃ L * ((JA.c L i - JA.b L i) * JA.v L i) * D.Y L A +
            (JA.c L i - JA.b L i) * r L A i := by
        intro i
        have hcb : 0 ≤ JA.c L i - JA.b L i := sub_nonneg.mpr (JA.resid_nonneg L i)
        have := mul_le_mul_of_nonneg_left (e3 i) hcb
        nlinarith
      calc _ ≤ ∑ i, ((JA.c L i - JA.b L i) * JA.u L i * D.Y L A +
            ε₃ L * ((JA.c L i - JA.b L i) * JA.v L i) * D.Y L A +
            (JA.c L i - JA.b L i) * r L A i) := sum_le_sum fun i _ => hterm i
        _ = _ := by
          rw [sum_add_distrib, sum_add_distrib, ← sum_mul, ← sum_mul, ← mul_sum]
    have hsplit : ∑ i, JA.c L i * JA.Z L A i - ∑ i, JA.b L i * JA.Z L A i =
        ∑ i, (JA.c L i - JA.b L i) * JA.Z L A i := by
      rw [← sum_sub_distrib]
      exact sum_congr rfl fun i _ => by ring
    have hgate := mul_le_mul_of_nonneg_right (JA.gate L) hYpos.le
    have hVY := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hV L) (hε₃0 L)) hYpos.le
    rw [remainder_add, remainder_add]
    nlinarith

/-- **The separate route is a joint allocation with no shared diagonal**: a comparison bound
`(2^k − 1)(Y_λ − Y_ν) ≤ ((2^k − 1)𝓔 + o(1)) Y` and the mean credit (CP7) of the data give a joint
allocation with the joint constant `jointConstantC k 𝓔 m` of K0's route. -/
noncomputable def JointAllocation.ofSeparate (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)
    {𝓔 : ℝ}
    (hcomp : ∃ ε₁ : ℕ → ℝ, Tendsto ε₁ atTop (𝓝 0) ∧ ∃ c₁ : ℝ, 0 ≤ c₁ ∧
      Param.AtCounterexamples (Params.ofDecay a) D.Y fun L A =>
        (2 ^ Fintype.card E - 1) * (energyFirst D.FS.lam (blockLift m₀ blk p) L A -
            energyComparison D.CL.ν (blockLift m₀ blk p) L A) ≤
          ((2 ^ Fintype.card E - 1) * 𝓔 + ε₁ L) * D.Y L A + remainder c₁ L A) :
    JointAllocation D (jointConstantC (Fintype.card E) 𝓔 D.MC.m) where
  ι _ := Empty
  ιFintype _ := inferInstanceAs (Fintype Empty)
  Z _ _ i := i.elim
  c _ i := i.elim
  b _ i := i.elim
  κ := (2 ^ Fintype.card E - 1) * 𝓔
  m₁ := D.MC.m
  comparison := by
    obtain ⟨ε₁, hε₁, c₁, hc₁, h⟩ := hcomp
    refine ⟨ε₁, hε₁, c₁, hc₁, ?_⟩
    unfold Param.AtCounterexamples at h ⊢
    filter_upwards [h] with L hL
    intro C hC hk A hAd hY
    have := hL C hC hk A hAd hY
    simp only [Finset.univ_eq_empty, sum_empty, zero_add]
    exact this
  mean := by
    obtain ⟨ε₂, hε₂, c₂, hc₂, h⟩ := D.MC.bound
    refine ⟨ε₂, hε₂, c₂, hc₂, ?_⟩
    unfold Param.AtCounterexamples at h ⊢
    filter_upwards [h] with L hL
    intro C hC hk A hAd hY
    have := hL C hC hk A hAd hY
    simp only [Finset.univ_eq_empty, sum_empty, add_zero]
    exact this
  u _ i := i.elim
  v _ i := i.elim
  upper := by
    refine ⟨fun _ => 0, fun _ => le_refl 0, tendsto_const_nhds, 0, 0, le_refl 0, fun L => ?_,
      fun _ _ i => i.elim, ?_, ?_⟩
    · simp
    · exact Param.AtCounterexamples.of_forall _ fun L A i => i.elim
    · refine Param.AtCounterexamples.of_forall _ fun L A => ?_
      simp only [Finset.univ_eq_empty, sum_empty]
      unfold remainder
      norm_num
  resid_nonneg _ i := i.elim
  gate L := by
    simp only [Finset.univ_eq_empty, sum_empty, add_zero]
    unfold jointConstantC
    have h2 : (0 : ℝ) < 2 ^ Fintype.card E := by positivity
    field_simp
    ring_nf
    exact le_refl _

end Sarkozy.JointClosing
