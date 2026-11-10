module

public import Sarkozy.Comparison.Criterion
public import Sarkozy.IndexSupport.HalfFunctions
public import Sarkozy.Slots

/-!
# Concrete energies of the closing criterion and the frame estimate

The energies of `Sarkozy.Comparison.ClosingEstimates` are here defined from actual
data, as in `def:hyb:coupled` and `cor:index-support-frame`
(`paper/sections/09_comparison_theorem.tex`, `10_comparison_lemmas.tex`):

* per-atom first-stage laws `λ_b`, comparison laws `ν_b` and envelopes `M_{L,b}, M_{R,b}`
  (linear functionals on labellings of the 72 slots by the atom alphabet), tensorized over
  the atoms of the scale;
* the coupled index: queries, prime-power and interval coordinates with their chains of
  conditional expectations, depth tails and transitions satisfying (CP0)(d);
* the half-functions carrying the index inputs `φ_e(ω_e)` at the query sources, resp.
  `ψ_e(ω_e)` at the reflected targets, and the lift `F` at the other slots of the plus half
  of the reserved cut.

With brackets `(M_L, ν, M_R)` at the reserved cut for every atom (CP6), and the mean
identities `E_ω φ_e = E_ω ψ_e = F` (`lem:twointerval`), the frame estimate
`J_ν ≤ Y_ν + ½[(V_L - e_L) + (V_R - e_R)]` (`eq:cp:mean-step`) is the theorem
`Sarkozy.IndexSupport.cut_signed_index_bounds_of_product` (WP-S). So
`ClosingEstimates.ofConcrete` needs only the other four estimates.
-/

@[expose] public section

open Filter
open scoped Topology

namespace Sarkozy.Comparison

open IndexSupport

variable {E : Type} [Fintype E] [DecidableEq E] {Kq : E → Type} [∀ e, Fintype (Kq e)]
  [∀ e, DecidableEq (Kq e)] {Ωc : ∀ e, Kq e → Type} [∀ e j, Fintype (Ωc e j)]
  [∀ e j, DecidableEq (Ωc e j)] [∀ e j, Nonempty (Ωc e j)]
  {Atom : ℕ → Type} [∀ L, Fintype (Atom L)] [∀ L, DecidableEq (Atom L)]
  {Xb : ∀ L, Atom L → Type} [∀ L b, Fintype (Xb L b)] [∀ L b, DecidableEq (Xb L b)]

/-- The coupled index of `def:hyb:coupled`, with (CP0)(d) and distinct query slots. -/
structure CoupledIndex (E : Type) [Fintype E] [DecidableEq E] (Kq : E → Type)
    [∀ e, Fintype (Kq e)] [∀ e, DecidableEq (Kq e)] (Ωc : ∀ e, Kq e → Type)
    [∀ e j, Fintype (Ωc e j)] [∀ e j, DecidableEq (Ωc e j)] where
  /-- Chains of conditional expectations (conductor depths) of the index coordinates. -/
  C : ∀ e j, Chain (Ωc e j)
  /-- Decreasing depth tails. -/
  t : ∀ e j, Tails (C e j).depth
  /-- Coordinate transitions. -/
  Tc : ∀ e j, Matrix (Ωc e j) (Ωc e j) ℝ
  /-- The transition norm on each exact-conductor space is bounded by the tail. -/
  hT : ∀ e j (l : Fin ((C e j).depth + 1)),
    RangeBound ((C e j).diff l) (Tc e j) ((t e j).tail l)
  /-- The transitions fix the constants. -/
  hT0 : ∀ e j, Tc e j * (C e j).cond 0 = (C e j).cond 0
  /-- Query sources in the plus half of the reserved cut. -/
  u : E → reservedCut.Half
  /-- Reflected query targets in the plus half of the reserved cut. -/
  w : E → reservedCut.Half
  hu : Function.Injective u
  hw : Function.Injective w

/-- The half-function `X̄` carrying `F` at every slot of the plus half. -/
def barHalf {Y : Type} (F : Y → ℝ) : (reservedCut.Half → Y) → ℝ := fun x => ∏ v, F (x v)

variable (I : CoupledIndex E Kq Ωc)
  (lam ML ν MR : ∀ L b, ((Slot → Xb L b) → ℝ) →ₗ[ℝ] ℝ)
  (φ ψ : ∀ L : ℕ, Finset ℤ → ∀ e, (∀ j, Ωc e j) → (∀ b, Xb L b) → ℝ)
  (F : ∀ L, Finset ℤ → (∀ b, Xb L b) → ℝ)

/-- Energy of the first-stage law, `Y_λ = Q_λ(X̄, X̄)`. -/
noncomputable def energyFirst (L : ℕ) (A : Finset ℤ) : ℝ :=
  reservedCut.form (tensorLaw (lam L)) (barHalf (F L A)) (barHalf (F L A))

/-- Energy of the comparison law, `Y_ν = Q_ν(X̄, X̄)`. -/
noncomputable def energyComparison (L : ℕ) (A : Finset ℤ) : ℝ :=
  reservedCut.form (tensorLaw (ν L)) (barHalf (F L A)) (barHalf (F L A))

/-- Mean energy of an envelope, `e_s = Q_{⊗M_s}(X̄, X̄)` (CP7). -/
noncomputable def energyMean (M : ∀ L b, ((Slot → Xb L b) → ℝ) →ₗ[ℝ] ℝ) (L : ℕ)
    (A : Finset ℤ) : ℝ :=
  reservedCut.form (tensorLaw (M L)) (barHalf (F L A)) (barHalf (F L A))

/-- The signed index form `J_ν = E_ω Q_ν(X_ω, (𝒯 Y)_ω)`. -/
noncomputable def signedIndexForm (L : ℕ) (A : Finset ℤ) : ℝ :=
  (FiniteLaw.uniform (∀ e, ∀ j, Ωc e j)).expect (fun ω =>
    reservedCut.form (tensorLaw (ν L)) (productHalf I.u (φ L A) (F L A) ω)
      (act (signedIndexOp I.Tc) (productHalf I.w (ψ L A) (F L A)) ω))

/-- The single-half random-inclusion energy of the source half-function. -/
noncomputable def inclusionEnergyL (L : ℕ) (A : Finset ℤ) : ℝ :=
  (queryLaw I.C I.t).expect (fun J => (FiniteLaw.uniform (∀ e, ∀ j, Ωc e j)).expect (fun ω =>
    reservedCut.form (tensorLaw (ML L)) (queryReveal I.C J (productHalf I.u (φ L A) (F L A)) ω)
      (queryReveal I.C J (productHalf I.u (φ L A) (F L A)) ω)))

/-- The single-half random-inclusion energy of the target half-function. -/
noncomputable def inclusionEnergyR (L : ℕ) (A : Finset ℤ) : ℝ :=
  (queryLaw I.C I.t).expect (fun J => (FiniteLaw.uniform (∀ e, ∀ j, Ωc e j)).expect (fun ω =>
    reservedCut.form (tensorLaw (MR L)) (queryReveal I.C J (productHalf I.w (ψ L A) (F L A)) ω)
      (queryReveal I.C J (productHalf I.w (ψ L A) (F L A)) ω)))

/-- **The frame estimate for the concrete energies** (`eq:cp:mean-step`). -/
theorem frame_of_brackets
    (hbr : ∀ L b, reservedCut.Bracket (ML L b) (ν L b) (MR L b))
    (hφ : ∀ L A e y, (FiniteLaw.uniform (∀ j, Ωc e j)).expect (fun η => φ L A e η y) = F L A y)
    (hψ : ∀ L A e y, (FiniteLaw.uniform (∀ j, Ωc e j)).expect (fun η => ψ L A e η y) = F L A y)
    (L : ℕ) (A : Finset ℤ) :
    signedIndexForm I ν φ ψ F L A ≤ energyComparison ν F L A +
      ((inclusionEnergyL I ML φ F L A - energyMean F ML L A) +
        (inclusionEnergyR I MR ψ F L A - energyMean F MR L A)) / 2 := by
  have h := cut_signed_index_bounds_of_product I.C I.t I.Tc I.hT I.hT0 reservedCut
    (ML L) (ν L) (MR L) (hbr L) I.hu I.hw (φ L A) (ψ L A) (F L A) (hφ L A) (hψ L A)
  have h7 := h.2.2.2.2.2.2
  unfold signedIndexForm energyComparison inclusionEnergyL inclusionEnergyR energyMean barHalf
  linarith

/-- **The closing estimates with concrete energies.** The frame estimate is proved from
the brackets (CP6) and the mean identities; the wrap, envelope, first-stage and joint
estimates remain hypotheses, now about the concrete energies. -/
noncomputable def ClosingEstimates.ofConcrete {Y : ℕ → Finset ℤ → ℝ} {k : ℕ} {L₀ J W H : ℝ}
    (hbr : ∀ L b, reservedCut.Bracket (ML L b) (ν L b) (MR L b))
    (hφ : ∀ L A e y, (FiniteLaw.uniform (∀ j, Ωc e j)).expect (fun η => φ L A e η y) = F L A y)
    (hψ : ∀ L A e y, (FiniteLaw.uniform (∀ j, Ωc e j)).expect (fun η => ψ L A e η y) = F L A y)
    (εwrap εenv εfirst εjoint : ℕ → ℝ) (cwrap cenv cfirst cjoint : ℝ)
    (hεwrap : Tendsto εwrap atTop (𝓝 0)) (hεenv : Tendsto εenv atTop (𝓝 0))
    (hεfirst : Tendsto εfirst atTop (𝓝 0)) (hεjoint : Tendsto εjoint atTop (𝓝 0))
    (hcwrap : 0 ≤ cwrap) (hcenv : 0 ≤ cenv) (hcfirst : 0 ≤ cfirst) (hcjoint : 0 ≤ cjoint)
    (wrap : AtCounterexamples Y fun L A =>
      2 ^ k * energyComparison ν F L A ≤ signedIndexForm I ν φ ψ F L A +
        (2 ^ k * W + εwrap L) * Y L A + remainder cwrap L A)
    (envelopeL : AtCounterexamples Y fun L A =>
      inclusionEnergyL I ML φ F L A ≤ (2 ^ k * J + εenv L) * Y L A + remainder cenv L A)
    (envelopeR : AtCounterexamples Y fun L A =>
      inclusionEnergyR I MR ψ F L A ≤ (2 ^ k * J + εenv L) * Y L A + remainder cenv L A)
    (firstStage : AtCounterexamples Y fun L A =>
      (1 - L₀ - εfirst L) * Y L A - remainder cfirst L A ≤ energyFirst lam F L A)
    (joint : AtCounterexamples Y fun L A =>
      (2 ^ k - 1) * (energyFirst lam F L A - energyComparison ν F L A) -
          (energyMean F ML L A + energyMean F MR L A) / 2 ≤
        (2 ^ k * H - 1 + εjoint L) * Y L A + remainder cjoint L A) :
    ClosingEstimates Y k L₀ J W H where
  Yfs := energyFirst lam F
  Yν := energyComparison ν F
  Jν := signedIndexForm I ν φ ψ F
  eL := energyMean F ML
  eR := energyMean F MR
  VL := inclusionEnergyL I ML φ F
  VR := inclusionEnergyR I MR ψ F
  εwrap := εwrap
  εenv := εenv
  εfirst := εfirst
  εjoint := εjoint
  cwrap := cwrap
  cenv := cenv
  cfirst := cfirst
  cjoint := cjoint
  εwrap_tendsto := hεwrap
  εenv_tendsto := hεenv
  εfirst_tendsto := hεfirst
  εjoint_tendsto := hεjoint
  cwrap_nonneg := hcwrap
  cenv_nonneg := hcenv
  cfirst_nonneg := hcfirst
  cjoint_nonneg := hcjoint
  wrap := wrap
  frame := Eventually.of_forall fun L _ _ _ A _ _ =>
    frame_of_brackets I ML ν MR φ ψ F hbr hφ hψ L A
  envelopeL := envelopeL
  envelopeR := envelopeR
  firstStage := firstStage
  joint := joint

end Sarkozy.Comparison
