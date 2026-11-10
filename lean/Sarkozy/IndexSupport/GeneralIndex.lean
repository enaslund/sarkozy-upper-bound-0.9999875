module

public import Sarkozy.IndexSupport.Operators

/-!
# The signed index operator on arbitrary per-query index spaces

`Sarkozy/IndexSupport/SignedIndex.lean` treats the index of each query as a product of
coordinates with chains of conditional expectations. This file gives the same results for
an arbitrary finite index space `Ω_e` per query (for instance the paper's unsplit
`ℤ/Kℤ × ℤ/M_0ℤ`), equipped with any sector system `H_e` (zero sector = constants), any
revelation law `V_e` of retained sectors, and any transition `T_e` that preserves every
sector of `H_e`, fixes the constants and has norm at most `δ_e(s)` on sector `s`, with
`δ_e(0) = 1` and `δ_e(s) ≤ Pr(s retained)`.

* `signedOp_sectorOperator` (`cor:index-support-frame`(i)): `𝒯 = ⊗_e (2P_e - T_e)` and
  `𝒯ᵀ` preserve every product sector, are the identity on the constants and have norm at
  most `∏_e δ_e(s_e)` there.
* `signedOp_bounds` (`cor:index-support-frame`(iii), matrix form): the index-support
  bounds for `𝒯` with independent revelations across queries and half-functions with a
  common mean.

Interface note (not checked formally here; this package does not import
`Sarkozy/Functional`): by their definitions, the kernel `signedKernel T e` of
`Sarkozy/Functional/SignedIndex.lean` is entrywise the matrix `2 • meanMatrix - T e` used here,
and its `kernelOp K Φ ω` is `(piKron K *ᵥ Φ) ω`.
-/

@[expose] public section

open Finset
open scoped BigOperators Matrix

namespace Sarkozy.IndexSupport

variable {E : Type*} [Fintype E] [DecidableEq E] {Ωe : E → Type*} [∀ e, Fintype (Ωe e)]
  [∀ e, DecidableEq (Ωe e)] {S : E → Type*} [∀ e, Fintype (S e)] [∀ e, DecidableEq (S e)]

/-- The signed index operator `𝒯 = ⊗_e (2P_e - T_e)` on `∏_e Ω_e`. -/
noncomputable def signedOp (T : ∀ e, Matrix (Ωe e) (Ωe e) ℝ) :
    Matrix (∀ e, Ωe e) (∀ e, Ωe e) ℝ :=
  piKron (fun e => (2 : ℝ) • meanMatrix (Ωe e) - T e)

/-- **`cor:index-support-frame`(i)**, general per-query index spaces. -/
theorem signedOp_sectorOperator (H : ∀ e, SectorSystem (Ωe e) (S e))
    {T : ∀ e, Matrix (Ωe e) (Ωe e) ℝ} {δ : ∀ e, S e → ℝ}
    (hT : ∀ e, SectorOperator (H e) (T e) (δ e)) (hδ0 : ∀ e, δ e (H e).zero = 1) :
    SectorOperator (SectorSystem.pi H) (signedOp T) (fun s => ∏ e, δ e (s e)) ∧
      SectorOperator (SectorSystem.pi H) (signedOp T)ᵀ (fun s => ∏ e, δ e (s e)) := by
  have hq (e : E) : SectorOperator (H e) ((2 : ℝ) • meanMatrix (Ωe e) - T e) (δ e) := by
    have h := (hT e).signed (hδ0 e)
    rwa [(H e).proj_zero] at h
  have h := SectorOperator.pi hq
  exact ⟨h, h.transpose⟩

/-- **`cor:index-support-frame`(iii)**, general per-query index spaces, matrix form: with
independent revelations `V_e` (product revelation `Revelation.pi V`), a joint Gram matrix
`[[M_L, Γ], [Γᵀ, M_R]] ⪰ 0`, and half-functions with `E X = E Y = X̄`:
`V_L ≥ e_L ≥ 0`, `V_R ≥ e_R ≥ 0`, `|J - ⟨X̄, Γ X̄⟩| ≤ ½[(V_L - e_L) + (V_R - e_R)]` and
`|J| ≤ V_L^{1/2} V_R^{1/2}`, where `J = E_ω⟨X_ω, Γ (𝒯Y)_ω⟩`. -/
theorem signedOp_bounds [∀ e, Nonempty (Ωe e)] {R : E → Type*} [∀ e, Fintype (R e)]
    {ι : Type*} [Fintype ι] (H : ∀ e, SectorSystem (Ωe e) (S e))
    (V : ∀ e, Revelation (H e) (R e)) {T : ∀ e, Matrix (Ωe e) (Ωe e) ℝ}
    {δ : ∀ e, S e → ℝ} (hT : ∀ e, SectorOperator (H e) (T e) (δ e))
    (hδ0 : ∀ e, δ e (H e).zero = 1) (hδnn : ∀ e s, 0 ≤ δ e s)
    (hδ : ∀ e s, δ e s ≤ (V e).prob s)
    {ML Γ MR : Matrix ι ι ℝ} (hG : (Matrix.fromBlocks ML Γ Γᵀ MR).PosSemidef)
    (X Y : (∀ e, Ωe e) → ι → ℝ) (Xbar : ι → ℝ) (hX : vmean X = Xbar) (hY : vmean Y = Xbar) :
    Xbar ⬝ᵥ (ML *ᵥ Xbar) ≤ (Revelation.pi V).energy ML X ∧ 0 ≤ Xbar ⬝ᵥ (ML *ᵥ Xbar) ∧
    Xbar ⬝ᵥ (MR *ᵥ Xbar) ≤ (Revelation.pi V).energy MR Y ∧ 0 ≤ Xbar ⬝ᵥ (MR *ᵥ Xbar) ∧
    |pairing Γ X (act (signedOp T) Y) - Xbar ⬝ᵥ (Γ *ᵥ Xbar)| ≤
      (1 / 2) * (((Revelation.pi V).energy ML X - Xbar ⬝ᵥ (ML *ᵥ Xbar)) +
        ((Revelation.pi V).energy MR Y - Xbar ⬝ᵥ (MR *ᵥ Xbar))) ∧
    |pairing Γ X (act (signedOp T) Y)| ≤
      Real.sqrt ((Revelation.pi V).energy ML X) * Real.sqrt ((Revelation.pi V).energy MR Y) := by
  have hop := (signedOp_sectorOperator H hT hδ0).1
  have hw0 (s : ∀ e, S e) : 0 ≤ ∏ e, δ e (s e) :=
    Finset.prod_nonneg (fun e _ => hδnn e (s e))
  have hw (s : ∀ e, S e) : ∏ e, δ e (s e) ≤ (Revelation.pi V).prob s := by
    rw [Revelation.pi_prob]
    exact Finset.prod_le_prod₀ (fun e _ => hδnn e (s e)) (fun e _ => hδ e (s e))
  have hML := joint_left hG
  have hMR := joint_right hG
  have hXm := mean_le_energy (Revelation.pi V) hML X
  have hYm := mean_le_energy (Revelation.pi V) hMR Y
  have ha := common_mean (Revelation.pi V) hw0 hw hop hG X Y
  have hb := form_le_energies (Revelation.pi V) hw0 hw hop hG X Y
  rw [hX] at hXm ha
  rw [hY] at hYm ha
  exact ⟨hXm.1, hXm.2, hYm.1, hYm.2, ha, hb⟩

/-- The revealed projection of the product revelation is the tensor product of the
per-query revealed projections. -/
theorem Revelation.pi_reveal {R : E → Type*} [∀ e, Fintype (R e)] {ι : Type*}
    {H : ∀ e, SectorSystem (Ωe e) (S e)} (V : ∀ e, Revelation (H e) (R e)) (r : ∀ e, R e)
    (Z : (∀ e, Ωe e) → ι → ℝ) :
    (Revelation.pi V).reveal r Z =
      act (piKron (fun e => ∑ u ∈ (V e).retained (r e), (H e).proj u)) Z := by
  unfold Revelation.reveal
  rw [Revelation.pi_sum_proj]

end Sarkozy.IndexSupport
