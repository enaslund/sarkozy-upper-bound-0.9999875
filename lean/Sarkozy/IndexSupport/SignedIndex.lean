module

public import Sarkozy.IndexSupport.Coupling
public import Sarkozy.Reflection.BracketMatrix

/-!
# The signed index form and the common mean

This file formalizes the construction-independent content of
`cor:index-support-frame` (The signed index form and the common mean) and the
inequality `eq:cp:mean-step` used in the proof of `thm:record:criterion`.

Setting (`def:hyb:coupled`(a),(c),(e) and (CP0)(d), abstracted): a finite set `E` of
queries; each query `e` has finitely many coordinates `j ∈ K_e` with finite coordinate
sets `Ω_{e,j}` (for the paper: the interval coordinate `ℤ/Kℤ` and the prime-power
residues `ℤ/p^{h_p}ℤ`), a chain of conditional-expectation projections `C e j` on each
coordinate with tails `t e j`, and a coordinate transition `T_{e,j}` that maps every
exact-conductor space `ran Π_{e,j,l}` into itself with norm at most `δ_{e,j,l}` and fixes
the constants. The index of query `e` is `Ω_e = ∏_j Ω_{e,j}`, the index space is
`Ω = ∏_e Ω_e`, `T_e = ⊗_j T_{e,j}`, and `P_e` averages over the entire index `ω_e`.

* `signedIndexOp`: `𝒯 = ⊗_e (2 P_e - T_e)`.
* `signedIndexOp_sectorOperator` (`cor:index-support-frame`(i)): `𝒯` and `𝒯ᵀ` map every
  exact-conductor sector `H_S` (`S` a vector of conductor depths, `querySectors`) into
  itself, are the identity on `H_0`, and have norm at most `δ_S` on `H_S`.
* `signed_index_bounds` (`cor:index-support-frame`(iii), matrix form): for a joint Gram
  matrix `[[M_L, Γ], [Γᵀ, M_R]] ⪰ 0` and half-functions `X, Y` with the common mean
  `E X = E Y = X̄` (the abstract content of (ii)), `V_s ≥ e_s ≥ 0`,
  `|J - ⟨X̄, Γ X̄⟩| ≤ ½[(V_L - e_L) + (V_R - e_R)]` and `|J| ≤ V_L^{1/2} V_R^{1/2}`.
* `cut_signed_index_bounds` (`cor:index-support-frame`(iii) and `eq:cp:mean-step`, cut
  form): the same for the cut matrices at a cut `ι` of the tensor products
  `⊗_𝔟 M_{L,𝔟}`, `⊗_𝔟 ν_𝔟`, `⊗_𝔟 M_{R,𝔟}` of per-atom laws with brackets
  `[[M_{L,𝔟}, ν_𝔟], [ν_𝔟^*, M_{R,𝔟}]] ⪰_ι 0`; then `J_ν ≤ Y_ν + ½[(V_L - e_L) + (V_R - e_R)]`.

Part (ii) of the corollary (the means and conditional expectations of the actual
half-functions, `lem:twointerval`) depends on the construction and is a hypothesis here.
-/

@[expose] public section

open Finset
open scoped BigOperators Matrix

namespace Sarkozy.IndexSupport

section Queries

variable {E : Type*} [Fintype E] [DecidableEq E] {Kq : E → Type*} [∀ e, Fintype (Kq e)]
  [∀ e, DecidableEq (Kq e)] {Ωc : ∀ e, Kq e → Type*} [∀ e j, Fintype (Ωc e j)]
  [∀ e j, DecidableEq (Ωc e j)]

/-- The exact-conductor sectors of the index space `Ω = ∏_e ∏_{j ∈ K_e} Ω_{e,j}`, indexed by
the vectors `S = (S_{e,j})` of conductor depths. -/
def querySectors (C : ∀ e j, Chain (Ωc e j)) :
    SectorSystem (∀ e, ∀ j, Ωc e j) (∀ e, ∀ j, Fin ((C e j).depth + 1)) :=
  SectorSystem.pi (fun e => productSectors (C e))

/-- The sector weights `δ_S = ∏_e ∏_j δ_{e,j,S_{e,j}}`. -/
def queryWeight (C : ∀ e j, Chain (Ωc e j)) (t : ∀ e j, Tails (C e j).depth)
    (S : ∀ e, ∀ j, Fin ((C e j).depth + 1)) : ℝ :=
  ∏ e, sectorWeight (C e) (t e) (S e)

/-- The signed index operator `𝒯 = ⊗_e (2 P_e - T_e)`, with `T_e = ⊗_j T_{e,j}` and `P_e`
the average over the whole index of query `e`. -/
noncomputable def signedIndexOp (Tc : ∀ e j, Matrix (Ωc e j) (Ωc e j) ℝ) :
    Matrix (∀ e, ∀ j, Ωc e j) (∀ e, ∀ j, Ωc e j) ℝ :=
  piKron (fun e => (2 : ℝ) • meanMatrix (∀ j, Ωc e j) - piKron (Tc e))

/-- The revealed projection `Z^𝒥 = (⊗_e ⊗_j E_{e,j,𝒥_{e,j}}) Z`. -/
def queryReveal {ι : Type*} (C : ∀ e j, Chain (Ωc e j))
    (J : ∀ e, ∀ j, Fin ((C e j).depth + 1)) (Z : (∀ e, ∀ j, Ωc e j) → ι → ℝ) :
    (∀ e, ∀ j, Ωc e j) → ι → ℝ :=
  act (piKron (fun e => piKron (fun j => (C e j).cond (J e j)))) Z

/-- Independent depths across queries and coordinates, `Pr(𝒥_{e,j} ≥ l) = δ_{e,j,l}`. -/
noncomputable def queryLaw (C : ∀ e j, Chain (Ωc e j)) (t : ∀ e j, Tails (C e j).depth) :
    FiniteLaw (∀ e, ∀ j, Fin ((C e j).depth + 1)) :=
  FiniteLaw.pi (fun e => depthLaw (C e) (t e))

/-- The single-half random-inclusion energy `V_M(Z) = E_𝒥 E_ω ⟨Z^𝒥_ω, M Z^𝒥_ω⟩`
(`def:hyb:coupled`(f)). -/
noncomputable def queryEnergy {ι : Type*} [Fintype ι] (C : ∀ e j, Chain (Ωc e j))
    (t : ∀ e j, Tails (C e j).depth) (M : Matrix ι ι ℝ) (Z : (∀ e, ∀ j, Ωc e j) → ι → ℝ) :
    ℝ :=
  (queryLaw C t).expect (fun J => pairing M (queryReveal C J Z) (queryReveal C J Z))

/-- The revelation underlying `queryReveal` and `queryLaw`. -/
noncomputable def queryRevelation (C : ∀ e j, Chain (Ωc e j))
    (t : ∀ e j, Tails (C e j).depth) :
    Revelation (querySectors C) (∀ e, ∀ j, Fin ((C e j).depth + 1)) :=
  Revelation.pi (fun e => depthRevelation (C e) (t e))

theorem queryRevelation_energy {ι : Type*} [Fintype ι] (C : ∀ e j, Chain (Ωc e j))
    (t : ∀ e j, Tails (C e j).depth) (M : Matrix ι ι ℝ) (Z : (∀ e, ∀ j, Ωc e j) → ι → ℝ) :
    (queryRevelation C t).energy M Z = queryEnergy C t M Z := by
  unfold Revelation.energy queryEnergy
  have hrev (J : ∀ e, ∀ j, Fin ((C e j).depth + 1)) :
      (queryRevelation C t).reveal J Z = queryReveal C J Z := by
    unfold Revelation.reveal queryReveal
    congr 1
    change ∑ s ∈ (Revelation.pi (fun e => depthRevelation (C e) (t e))).retained J,
      (SectorSystem.pi (fun e => productSectors (C e))).proj s = _
    rw [Revelation.pi_sum_proj]
    congr 1
    funext e
    exact depthRevelation_sum_proj (C e) (t e) (J e)
  simp only [hrev]
  rfl

theorem queryRevelation_prob (C : ∀ e j, Chain (Ωc e j)) (t : ∀ e j, Tails (C e j).depth)
    (S : ∀ e, ∀ j, Fin ((C e j).depth + 1)) :
    (queryRevelation C t).prob S = queryWeight C t S := by
  have h := Revelation.pi_prob (fun e => depthRevelation (C e) (t e)) S
  have h2 : ∏ e, sectorWeight (C e) (t e) (S e) =
      ∏ e, (depthRevelation (C e) (t e)).prob (S e) :=
    prod_congr rfl (fun e _ => (depthRevelation_prob (C e) (t e) (S e)).symm)
  rw [queryWeight, h2]
  exact h

theorem queryWeight_nonneg (C : ∀ e j, Chain (Ωc e j)) (t : ∀ e j, Tails (C e j).depth)
    (S : ∀ e, ∀ j, Fin ((C e j).depth + 1)) : 0 ≤ queryWeight C t S := by
  rw [← queryRevelation_prob]
  exact (queryRevelation C t).prob_nonneg S

theorem sectorWeight_zero {K : Type*} [Fintype K] [DecidableEq K] {Ω : K → Type*}
    [∀ j, Fintype (Ω j)] [∀ j, DecidableEq (Ω j)] (C : ∀ j, Chain (Ω j))
    (t : ∀ j, Tails (C j).depth) : sectorWeight C t (productSectors C).zero = 1 := by
  unfold sectorWeight
  apply Finset.prod_eq_one
  intro j _
  exact (t j).tail_zero

/-- **`cor:index-support-frame`(i)**: `𝒯 = ⊗_e (2 P_e - T_e)` and its adjoint map every
exact-conductor sector `H_S` into itself, are the identity on `H_0`, and have norm at most
`δ_S` on `H_S`. -/
theorem signedIndexOp_sectorOperator (C : ∀ e j, Chain (Ωc e j))
    (t : ∀ e j, Tails (C e j).depth) (Tc : ∀ e j, Matrix (Ωc e j) (Ωc e j) ℝ)
    (hT : ∀ e j (l : Fin ((C e j).depth + 1)),
      RangeBound ((C e j).diff l) (Tc e j) ((t e j).tail l))
    (hT0 : ∀ e j, Tc e j * (C e j).cond 0 = (C e j).cond 0) :
    SectorOperator (querySectors C) (signedIndexOp Tc) (queryWeight C t) ∧
      SectorOperator (querySectors C) (signedIndexOp Tc)ᵀ (queryWeight C t) := by
  have hq (e : E) : SectorOperator (productSectors (C e))
      ((2 : ℝ) • meanMatrix (∀ j, Ωc e j) - piKron (Tc e)) (sectorWeight (C e) (t e)) := by
    have h := (SectorOperator.chain (C e) (t e) (hT e) (hT0 e)).signed
      (sectorWeight_zero (C e) (t e))
    rwa [(productSectors (C e)).proj_zero] at h
  have h := SectorOperator.pi hq
  exact ⟨h, h.transpose⟩

/-- **`cor:index-support-frame`(iii)**, matrix form. For a joint Gram matrix
`[[M_L, Γ], [Γᵀ, M_R]] ⪰ 0` and half-functions with the common mean `E X = E Y = X̄`:
`V_L ≥ e_L ≥ 0`, `V_R ≥ e_R ≥ 0`, `|J - ⟨X̄, Γ X̄⟩| ≤ ½[(V_L - e_L) + (V_R - e_R)]`, and
`|J| ≤ V_L^{1/2} V_R^{1/2}`, where `J = E_ω ⟨X_ω, Γ (𝒯 Y)_ω⟩`, `e_s = ⟨X̄, M_s X̄⟩`,
`V_L = V_{M_L}(X)`, `V_R = V_{M_R}(Y)`. -/
theorem signed_index_bounds [∀ e j, Nonempty (Ωc e j)] {ι : Type*} [Fintype ι]
    (C : ∀ e j, Chain (Ωc e j)) (t : ∀ e j, Tails (C e j).depth)
    (Tc : ∀ e j, Matrix (Ωc e j) (Ωc e j) ℝ)
    (hT : ∀ e j (l : Fin ((C e j).depth + 1)),
      RangeBound ((C e j).diff l) (Tc e j) ((t e j).tail l))
    (hT0 : ∀ e j, Tc e j * (C e j).cond 0 = (C e j).cond 0)
    {ML Γ MR : Matrix ι ι ℝ} (hG : (Matrix.fromBlocks ML Γ Γᵀ MR).PosSemidef)
    (X Y : (∀ e, ∀ j, Ωc e j) → ι → ℝ) (Xbar : ι → ℝ)
    (hX : vmean X = Xbar) (hY : vmean Y = Xbar) :
    Xbar ⬝ᵥ (ML *ᵥ Xbar) ≤ queryEnergy C t ML X ∧ 0 ≤ Xbar ⬝ᵥ (ML *ᵥ Xbar) ∧
    Xbar ⬝ᵥ (MR *ᵥ Xbar) ≤ queryEnergy C t MR Y ∧ 0 ≤ Xbar ⬝ᵥ (MR *ᵥ Xbar) ∧
    |pairing Γ X (act (signedIndexOp Tc) Y) - Xbar ⬝ᵥ (Γ *ᵥ Xbar)| ≤
      (1 / 2) * ((queryEnergy C t ML X - Xbar ⬝ᵥ (ML *ᵥ Xbar)) +
        (queryEnergy C t MR Y - Xbar ⬝ᵥ (MR *ᵥ Xbar))) ∧
    |pairing Γ X (act (signedIndexOp Tc) Y)| ≤
      Real.sqrt (queryEnergy C t ML X) * Real.sqrt (queryEnergy C t MR Y) := by
  have hop := (signedIndexOp_sectorOperator C t Tc hT hT0).1
  have hδ0 := queryWeight_nonneg C t
  have hδ : ∀ S, queryWeight C t S ≤ (queryRevelation C t).prob S :=
    fun S => (queryRevelation_prob C t S).symm.le
  have hML := joint_left hG
  have hMR := joint_right hG
  have eX : (queryRevelation C t).energy ML X = queryEnergy C t ML X :=
    queryRevelation_energy C t ML X
  have eY : (queryRevelation C t).energy MR Y = queryEnergy C t MR Y :=
    queryRevelation_energy C t MR Y
  have hXm := mean_le_energy (queryRevelation C t) hML X
  have hYm := mean_le_energy (queryRevelation C t) hMR Y
  have ha := common_mean (queryRevelation C t) hδ0 hδ hop hG X Y
  have hb := form_le_energies (queryRevelation C t) hδ0 hδ hop hG X Y
  rw [eX, hX] at hXm
  rw [eY, hY] at hYm
  rw [eX, eY, hX, hY] at ha
  rw [eX, eY] at hb
  exact ⟨hXm.1, hXm.2, hYm.1, hYm.2, ha, hb⟩

end Queries

section Cut

variable {E : Type*} [Fintype E] [DecidableEq E] {Kq : E → Type*} [∀ e, Fintype (Kq e)]
  [∀ e, DecidableEq (Kq e)] {Ωc : ∀ e, Kq e → Type*} [∀ e j, Fintype (Ωc e j)]
  [∀ e j, DecidableEq (Ωc e j)] [∀ e j, Nonempty (Ωc e j)]
  {V : Type*} [Fintype V] [DecidableEq V]
  {𝔅 : Type*} [Fintype 𝔅] [DecidableEq 𝔅] {Xb : 𝔅 → Type*} [∀ b, Fintype (Xb b)]
  [∀ b, DecidableEq (Xb b)]

omit [∀ e j, DecidableEq (Ωc e j)] in
/-- The expected cut form `E_ω Q_κ(A_ω, B_ω)` is the pairing of the cut matrix. -/
theorem expect_form_eq_pairing (c : ReflectionCut V)
    (κ : ((V → ∀ b, Xb b) → ℝ) →ₗ[ℝ] ℝ) (A B : (∀ e, ∀ j, Ωc e j) → (c.Half → ∀ b, Xb b) → ℝ) :
    (FiniteLaw.uniform (∀ e, ∀ j, Ωc e j)).expect (fun ω => c.form κ (A ω) (B ω)) =
      pairing (c.matrix κ) A B := by
  rw [pairing_eq_expect]
  apply FiniteLaw.expect_congr
  intro ω
  exact c.form_eq_dotProduct κ (A ω) (B ω)

/-- **`cor:index-support-frame`(iii) and `eq:cp:mean-step`**, cut form.

Let `ν = ⊗_𝔟 ν_𝔟` be a product of finite signed laws and `M_{L,𝔟}`, `M_{R,𝔟}` laws with
brackets `[[M_{L,𝔟}, ν_𝔟], [ν_𝔟^*, M_{R,𝔟}]] ⪰_ι 0` at the cut `ι` (as in (CP6)). Let
`X, Y` be half-functions indexed by `Ω` with `E_ω X_ω = E_ω Y_ω = X̄`
(`cor:index-support-frame`(ii)). With the signed index form
`J_ν = E_ω Q_ν(X_ω, (𝒯 Y)_ω)`, `Y_ν = Q_ν(X̄, X̄)`, `e_s = Q_{⊗M_s}(X̄, X̄)` and the
single-half random-inclusion energies `V_L = V_{⊗M_L}(X)`, `V_R = V_{⊗M_R}(Y)`:
`V_s ≥ e_s ≥ 0`, `|J_ν - Y_ν| ≤ ½[(V_L - e_L) + (V_R - e_R)]`, `|J_ν| ≤ V_L^{1/2} V_R^{1/2}`,
and in particular `J_ν ≤ Y_ν + ½[(V_L - e_L) + (V_R - e_R)]` (`eq:cp:mean-step`). -/
theorem cut_signed_index_bounds (C : ∀ e j, Chain (Ωc e j)) (t : ∀ e j, Tails (C e j).depth)
    (Tc : ∀ e j, Matrix (Ωc e j) (Ωc e j) ℝ)
    (hT : ∀ e j (l : Fin ((C e j).depth + 1)),
      RangeBound ((C e j).diff l) (Tc e j) ((t e j).tail l))
    (hT0 : ∀ e j, Tc e j * (C e j).cond 0 = (C e j).cond 0)
    (c : ReflectionCut V) (ML ν MR : ∀ b, ((V → Xb b) → ℝ) →ₗ[ℝ] ℝ)
    (hbr : ∀ b, c.Bracket (ML b) (ν b) (MR b))
    (X Y : (∀ e, ∀ j, Ωc e j) → (c.Half → ∀ b, Xb b) → ℝ) (Xbar : (c.Half → ∀ b, Xb b) → ℝ)
    (hX : vmean X = Xbar) (hY : vmean Y = Xbar) :
    let unif := FiniteLaw.uniform (∀ e, ∀ j, Ωc e j)
    let Jν := unif.expect (fun ω => c.form (tensorLaw ν) (X ω) (act (signedIndexOp Tc) Y ω))
    let Yν := c.form (tensorLaw ν) Xbar Xbar
    let eL := c.form (tensorLaw ML) Xbar Xbar
    let eR := c.form (tensorLaw MR) Xbar Xbar
    let VL := (queryLaw C t).expect (fun J => unif.expect (fun ω =>
      c.form (tensorLaw ML) (queryReveal C J X ω) (queryReveal C J X ω)))
    let VR := (queryLaw C t).expect (fun J => unif.expect (fun ω =>
      c.form (tensorLaw MR) (queryReveal C J Y ω) (queryReveal C J Y ω)))
    eL ≤ VL ∧ 0 ≤ eL ∧ eR ≤ VR ∧ 0 ≤ eR ∧
      |Jν - Yν| ≤ (1 / 2) * ((VL - eL) + (VR - eR)) ∧
      |Jν| ≤ Real.sqrt VL * Real.sqrt VR ∧
      Jν ≤ Yν + (1 / 2) * ((VL - eL) + (VR - eR)) := by
  intro unif Jν Yν eL eR VL VR
  have hG : (Matrix.fromBlocks (c.matrix (tensorLaw ML)) (c.matrix (tensorLaw ν))
      (c.matrix (tensorLaw ν))ᵀ (c.matrix (tensorLaw MR))).PosSemidef :=
    (c.bracket_iff_blockMatrix_posSemidef _ _ _).mp (ReflectionCut.Bracket.tensor hbr)
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ :=
    signed_index_bounds C t Tc hT hT0 hG X Y Xbar hX hY
  have hJ : Jν = pairing (c.matrix (tensorLaw ν)) X (act (signedIndexOp Tc) Y) :=
    expect_form_eq_pairing c _ X _
  have hVL : VL = queryEnergy C t (c.matrix (tensorLaw ML)) X := by
    change (queryLaw C t).expect _ = (queryLaw C t).expect _
    apply FiniteLaw.expect_congr
    intro J
    exact expect_form_eq_pairing c _ _ _
  have hVR : VR = queryEnergy C t (c.matrix (tensorLaw MR)) Y := by
    change (queryLaw C t).expect _ = (queryLaw C t).expect _
    apply FiniteLaw.expect_congr
    intro J
    exact expect_form_eq_pairing c _ _ _
  have hY' : Yν = Xbar ⬝ᵥ (c.matrix (tensorLaw ν) *ᵥ Xbar) := c.form_eq_dotProduct _ _ _
  have heL : eL = Xbar ⬝ᵥ (c.matrix (tensorLaw ML) *ᵥ Xbar) := c.form_eq_dotProduct _ _ _
  have heR : eR = Xbar ⬝ᵥ (c.matrix (tensorLaw MR) *ᵥ Xbar) := c.form_eq_dotProduct _ _ _
  rw [hJ, hVL, hVR, hY', heL, heR]
  refine ⟨h1, h2, h3, h4, h5, h6, ?_⟩
  have := (abs_le.mp h5).2
  linarith

end Cut

end Sarkozy.IndexSupport
