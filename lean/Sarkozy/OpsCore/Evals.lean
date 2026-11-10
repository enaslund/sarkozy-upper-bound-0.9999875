module

public import Sarkozy.OpsCore.Signs
public import Sarkozy.EnvelopeSteps.PaperAveraging

@[expose] public section




open Finset
open scoped BigOperators

namespace Sarkozy.OpsCore

open Sarkozy.ClassInputsPaper Sarkozy.EnvelopeSteps Sarkozy.MainFinal2
open Sarkozy.ClassBoundsPaper Sarkozy.TheoremC Sarkozy.TheoremCBlock Sarkozy.BlockFrame
open Sarkozy.RecordExpansion Sarkozy.RecordExpansion.Choice

/-! ## The class averages -/

section Averages

variable {Ω : Type*} {𝒞 : Finset Ω}

/-- `hM` from a uniform bound of the coupling masses on the class. -/
theorem hM_of_le {wt CX Mω : Ω → ℝ} {M : ℝ} (h0 : ∀ ω ∈ 𝒞, 0 ≤ wt ω * CX ω)
    (h : ∀ ω ∈ 𝒞, Mω ω ≤ M) :
    ∑ ω ∈ 𝒞, wt ω * CX ω * Mω ω ≤ M * ∑ ω ∈ 𝒞, wt ω * CX ω := by
  rw [mul_sum]
  exact sum_le_sum fun ω hω => by nlinarith [h0 ω hω, h ω hω]

/-- `hMinv` from a uniform lower bound of the orbit masses on the class (e.g. `M^inv = 0` with
`M_h ≥ 0`: the uniform cost of `thm:envelopes`(ii)). -/
theorem hMinv_of_le {wt CX Mh : Ω → ℝ} {Minv : ℝ} (h0 : ∀ ω ∈ 𝒞, 0 ≤ wt ω * CX ω)
    (h : ∀ ω ∈ 𝒞, Minv ≤ Mh ω) :
    Minv * ∑ ω ∈ 𝒞, wt ω * CX ω ≤ ∑ ω ∈ 𝒞, wt ω * CX ω * Mh ω := by
  rw [mul_sum]
  exact sum_le_sum fun ω hω => by nlinarith [h0 ω hω, h ω hω]

/-- `hρ` (the residual carries the coupling and remainder parts) from the same bound per
selection. -/
theorem hρ_of_le {wt CX υ ρ : Ω → ℝ} {M Rerr Minv tU tδ B : ℝ}
    (h : ∀ ω ∈ 𝒞, (M * Rerr - Minv * Real.exp tU * tδ) * (wt ω * CX ω) +
      B * (wt ω * υ ω * CX ω) ≤ ρ ω) :
    (M * Rerr - Minv * Real.exp tU * tδ) * (∑ ω ∈ 𝒞, wt ω * CX ω) +
      B * (∑ ω ∈ 𝒞, wt ω * υ ω * CX ω) ≤ ∑ ω ∈ 𝒞, ρ ω := by
  rw [mul_sum, mul_sum, ← sum_add_distrib]
  exact sum_le_sum h

end Averages

/-- **Only the class total matters** (`hbg`, `hρ` of `DegreeInputs`): with `S = ∑ π̃ C_X > 0`, a
background `Wbg ≤ κ S Y` and the total `(κ + Mc) S + Bυ ≤ Δ + ρsum`, the spill `κ − Δ/S` gives
`Wbg ≤ Δ Y + spill S Y` and `(Mc + spill) S + Bυ ≤ ρsum`. -/
theorem exists_spill {S Y κ Mc Bυ Δ ρsum Wbg : ℝ} (hS : 0 < S) (hbg : Wbg ≤ κ * S * Y)
    (htot : (κ + Mc) * S + Bυ ≤ Δ + ρsum) :
    ∃ spill : ℝ, Wbg ≤ Δ * Y + spill * S * Y ∧ (Mc + spill) * S + Bυ ≤ ρsum := by
  refine ⟨κ - Δ / S, ?_, ?_⟩
  · have e : Δ * Y + (κ - Δ / S) * S * Y = κ * S * Y := by
      field_simp
      ring
    rw [e]
    exact hbg
  · have e : (Mc + (κ - Δ / S)) * S + Bυ = (κ + Mc) * S + Bυ - Δ := by
      field_simp
      ring
    rw [e]
    linarith

/-! ## The leading stars -/

variable {a : ℝ}
  {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

/-- **The leading data of a selection** (data): raw-arm coefficients, leading stars, bounds. -/
structure LeadData (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ)
    (ω : Choice (D.CL.T L)) where
  w : {b // b ∈ Choice.support ω} → ℝ
  Lb : ∀ b : {b // b ∈ Choice.support ω},
    (HalfB (m₀ := m₀) (blk := blk) (p := p) L (Choice.support ω) b → ℝ) →ₗ[ℝ]
      (HalfB (m₀ := m₀) (blk := blk) (p := p) L (Choice.support ω) b → ℝ)
  ℓ : {b // b ∈ Choice.support ω} → ℝ
  ρ : {b // b ∈ Choice.support ω} → ℝ

/-- The star data of the leading data, at the selected marginals and signs. -/
noncomputable abbrev LeadData.star {D : TheoremCBlock.ComparisonData a m₀ blk p pr h E} {L : ℕ}
    {ω : Choice (D.CL.T L)} (G : LeadData D L ω) : StarData D L ω :=
  StarData.ofSel' G.w G.Lb G.ℓ G.ρ

/-- **The open part of the star form** (C; `prop:signed-bounds`(b),(e), (N1)–(N3)):
`w_𝔅 > 0`, `‖L_𝔅‖ ≤ ℓ_𝔅`, `‖Δ̂_𝔅 − L_𝔅‖ ≤ ρ_𝔅` in `L²(m_𝔅)`, and `L_𝔅` has an
`ε_𝔅`-symmetric kernel (a star is skew-adjoint at a skew record). -/
structure LeadOK {D : TheoremCBlock.ComparisonData a m₀ blk p pr h E} {L : ℕ}
    {ω : Choice (D.CL.T L)} (G : LeadData D L ω) : Prop where
  hw : ∀ b, 0 < G.w b
  hL : ∀ b, OpNormLE (selMarg D L ω b.1) (G.Lb b) (G.ℓ b)
  hE : ∀ b, OpNormLE (selMarg D L ω b.1) (G.star.Δhat b - G.Lb b) (G.ρ b)
  hLs : ∀ b x y, kern (selMarg D L ω b.1) (G.Lb b) y x =
    selSign ω b.1 * kern (selMarg D L ω b.1) (G.Lb b) x y

omit [DecidableEq P] in
theorem LeadOK.starOK {D : TheoremCBlock.ComparisonData a m₀ blk p pr h E} {L : ℕ}
    {ω : Choice (D.CL.T L)} {G : LeadData D L ω} (H : LeadOK G) (hω : IsSelection ω) :
    StarOK G.star :=
  starOK_sel hω H.hw H.hL H.hE H.hLs

omit [DecidableEq P] in
/-- **`DegreeInputs` with the star form proved**: from the leading data (`LeadOK`, open, C) of
every selection of a class of selections, the envelopes `D_ω` with the domination (OPS-F), (E1) for
`Diag_ω`, Steps 3 and 4 (OPS-S), and the evaluations. -/
noncomputable def DegreeInputs.ofLead {D : TheoremCBlock.ComparisonData a m₀ blk p pr h E}
    {L : ℕ} {A : Finset ℤ} {𝒞 : Finset (Choice (D.CL.T L))} {π ρ rr : Choice (D.CL.T L) → ℝ}
    {Wd z K : ℝ} (h𝒞 : ∀ ω ∈ 𝒞, IsSelection ω)
    (G : ∀ ω, LeadData D L ω) (hG : ∀ ω ∈ 𝒞, LeadOK (G ω))
    (Dop : ∀ ω, (StarData.Obj (D := D) (L := L) (ω := ω) → ℝ) →ₗ[ℝ]
      (StarData.Obj (D := D) (L := L) (ω := ω) → ℝ))
    (hdom : ∀ ω ∈ 𝒞, OpLE (G ω).star.m (G ω).star.Lop (Dop ω) ∧
      OpLE (G ω).star.m (-(G ω).star.Lop) (Dop ω))
    (B : ℝ) (CX r₁' : Choice (D.CL.T L) → ℝ)
    (hE1 : ∀ ω ∈ 𝒞, paperEN D L A (Choice.support ω)
      (reservedCut.diagonalLaw (push (G ω).star.m (G ω).star.φ)) ≤
        (B + z) * CX ω * D.Y L A + r₁' ω)
    (YN0 Mω Mh r₃ : Choice (D.CL.T L) → ℝ) (Rerr tU tδ : ℝ) (hR : 0 ≤ Rerr) (htδ : 0 ≤ tδ)
    (step3 : ∀ ω ∈ 𝒞, paperEN D L A (Choice.support ω)
      (place reservedCut (G ω).star.m (G ω).star.φ (Dop ω)) ≤
      YN0 ω + (Mω ω * Rerr - Mh ω * Real.exp tU * tδ + z) * CX ω * D.Y L A + r₃ ω)
    (Wbg r₄ : ℝ)
    (step4 : ∑ ω ∈ 𝒞, (G ω).star.wt * YN0 ω ≤
      Wbg + z * (∑ ω ∈ 𝒞, (G ω).star.wt * CX ω) * D.Y L A + r₄)
    (spill : ℝ) (hspill : Rerr ≠ 0 ∨ spill = 0)
    (hbg : Wbg ≤ Wd + spill * (∑ ω ∈ 𝒞, (G ω).star.wt * CX ω) * D.Y L A) (M Minv : ℝ)
    (hM : ∑ ω ∈ 𝒞, (G ω).star.wt * CX ω * Mω ω ≤ M * ∑ ω ∈ 𝒞, (G ω).star.wt * CX ω)
    (hMinv : Minv * ∑ ω ∈ 𝒞, (G ω).star.wt * CX ω ≤ ∑ ω ∈ 𝒞, (G ω).star.wt * CX ω * Mh ω)
    (hρ : (M * Rerr - Minv * Real.exp tU * tδ + spill) * (∑ ω ∈ 𝒞, (G ω).star.wt * CX ω) +
      B * (∑ ω ∈ 𝒞, (G ω).star.wt * (G ω).star.υ * CX ω) ≤ ∑ ω ∈ 𝒞, ρ ω)
    (hπ : ∀ ω ∈ 𝒞, (G ω).star.wt * (2 + (G ω).star.υ) * CX ω ≤ K * π ω)
    (hrr : ∑ ω ∈ 𝒞, (G ω).star.wt * ((G ω).star.υ * r₁' ω + r₃ ω) + r₄ ≤ ∑ ω ∈ 𝒞, rr ω) :
    DegreeInputs D L A 𝒞 π ρ rr Wd z K :=
  DegreeInputs.ofStar (fun ω => (G ω).star) (fun ω hω => (hG ω hω).starOK (h𝒞 ω hω)) Dop hdom B
    CX r₁' hE1 YN0 Mω Mh r₃ Rerr tU tδ hR htδ step3 Wbg r₄ step4 spill hspill hbg M Minv hM hMinv
    hρ hπ hrr

omit [DecidableEq P] in
/-- The selections of a class are selections. -/
theorem isSelection_of_clsSel {D : TheoremCBlock.ComparisonData a m₀ blk p pr h E}
    (cd : ClassData D.CL) {L : ℕ} (i : cd.ι L) :
    ∀ ω ∈ cd.clsSel L i, IsSelection ω :=
  fun _ hω => (mem_filter.mp (mem_filter.mp hω).1).2

omit [DecidableEq P] in
/-- `push` along the identity. -/
theorem push_id {Q : Type*} [Fintype Q] [DecidableEq Q] (m : Q → ℝ) : push m id = m := by
  funext x
  unfold push
  rw [show univ.filter (fun y : Q => id y = x) = {x} by ext y; simp]
  simp

omit [DecidableEq P] in
/-- **(E1) for `Diag_ω` at the star objects is (E1) for `varDiag` at the selected marginals**
(`paperEN_diag_eq_varDiag`): the input `hE1` of `DegreeInputs.ofLead` is OPS-S's (E1) for
`Y[Diag_X(selMarg) ⊗ Ñ]`. -/
theorem hE1_star {D : TheoremCBlock.ComparisonData a m₀ blk p pr h E} {L : ℕ} (A : Finset ℤ)
    {ω : Choice (D.CL.T L)} (G : LeadData D L ω) :
    paperEN D L A (Choice.support ω) (reservedCut.diagonalLaw (push G.star.m G.star.φ)) =
      varDiag D L A ω (selMarg D L ω) := by
  have h := paperEN_diag_eq_varDiag D L A ω _ G.star.mB (fun _ => id)
  change paperEN D L A (Choice.support ω)
    (reservedCut.diagonalLaw (push (prodWeight G.star.mB) (prodPlace reservedCut fun _ => id))) = _
  rw [h]
  unfold varDiag
  congr 2
  funext b
  by_cases hb : b ∈ Choice.support ω
  · simp only [hb, ↓reduceIte, ↓reduceDIte, push_id]
    rfl
  · simp only [hb, ↓reduceIte]

omit [DecidableEq P] in
/-- The product of the selected prices is the monomial of `π̃`. -/
theorem prod_selPrice (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ)
    (ω : Choice (D.CL.T L)) :
    ∏ b : {b // b ∈ Choice.support ω}, selPrice D L ω b.1 = monomial (D.CL.πt L) ω := by
  rw [Finset.prod_coe_sort (Choice.support ω) (fun b => selPrice D L ω b)]
  unfold monomial Choice.support
  rw [Finset.prod_filter]
  refine prod_congr rfl fun b _ => ?_
  unfold selPrice
  rcases ω b with _ | ⟨t, e⟩
  · rfl
  · rfl

omit [DecidableEq P] in
/-- **The error weights** (`hπ`, `thm:envelopes`(i), last paragraph): if every raw-arm coefficient
is at most the record's price, `0 ≤ w_𝔅 ≤ π̃_{ω(𝔅)}`, and `0 ≤ υ_ω ≤ U`, then
`π̃_ω (2 + υ_ω) C_X ≤ (2 + U) π_ω`, with `C_X = ∏_{𝔅 ∈ X} q_𝔅^{2a}`. -/
theorem hπ_of_le (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ)
    (ω : Choice (D.CL.T L)) (w : {b // b ∈ Choice.support ω} → ℝ) (hw0 : ∀ b, 0 ≤ w b)
    (hw : ∀ b, w b ≤ selPrice D L ω b.1) {υ U : ℝ} (hυ0 : 0 ≤ υ) (hυ : υ ≤ U) :
    (∏ b, w b) * (2 + υ) * (∏ b ∈ Choice.support ω, selectionFactor a p D.S.selPre L b) ≤
      (2 + U) * monomial (D.CL.π L) ω := by
  have hq : 0 ≤ ∏ b ∈ Choice.support ω, selectionFactor a p D.S.selPre L b :=
    prod_nonneg fun b _ => D.selectionFactor_nonneg L b
  have h1 : ∏ b, w b ≤ monomial (D.CL.πt L) ω := by
    rw [← prod_selPrice]
    exact Finset.prod_le_prod₀ (fun b _ => hw0 b) fun b _ => hw b
  have h0 : 0 ≤ ∏ b, w b := prod_nonneg fun b _ => hw0 b
  have e : monomial (D.CL.π L) ω = monomial (D.CL.πt L) ω *
      ∏ b ∈ Choice.support ω, selectionFactor a p D.S.selPre L b :=
    monomial_mul_selectionFactor (D.CL.πt L) (fun b => selectionFactor a p D.S.selPre L b) ω
  rw [e]
  have h2 : (∏ b, w b) * (2 + υ) ≤ monomial (D.CL.πt L) ω * (2 + U) :=
    mul_le_mul h1 (by linarith) (by linarith) (h0.trans h1)
  calc (∏ b, w b) * (2 + υ) * (∏ b ∈ Choice.support ω, selectionFactor a p D.S.selPre L b)
      ≤ monomial (D.CL.πt L) ω * (2 + U) *
          (∏ b ∈ Choice.support ω, selectionFactor a p D.S.selPre L b) :=
        mul_le_mul_of_nonneg_right h2 hq
    _ = _ := by ring

end Sarkozy.OpsCore
