module

public import Sarkozy.OpsSteps.Step4Fine

@[expose] public section

/-!
# The prices of Step 4 (i) from the data (OPS-S)

`paper/sections/23_envelopes.tex`, proof of `lem:oct24:invariant-background`(v) and
`rem:completion-subtraction`.

The upper prices `m ≥ v`, `n ≥ w`, `∑ m = tU`, `∑(m + n) ≤ U₀` of `heval_of_finer` are more than
the evaluation needs. Since `κ_H e^{V+W} − c e^{V}` is nondecreasing in `V` (`c ≤ κ_H`):

* **`background_le_total`**:
  `κ_H ∏(1 + v + w) − (κ_H − κ_b) ∏(1 + v) ≤ κ_H e^{U₀} − (κ_H − κ_b) e^{tU}` as soon as
  `∑(v + w) ≤ U₀` and `tU + ∑ w ≤ U₀`;
* `heval_of_total`: `heval_of_finer` under these two conditions;
* **`hVW_fine`**: at the paper's data the first is a theorem (`U₀_total`: the invariant and
  generic prices of an atom add up to its bracket price);
* **`step4_total`**: Step 4 in form (i) with the single price condition `w ≤ n`, `tU + ∑ n ≤ U₀`
  (`U₀ ≥ t(U_inv + ∑ u^G)`, F).
-/

namespace Sarkozy.OpsSteps

open Filter Finset Function
open scoped Topology BigOperators
open Sarkozy.BracketEnergy Sarkozy.EnvelopeInputs Sarkozy.EnvelopeEnergiesPaper
  Sarkozy.Structured Sarkozy.Functional Sarkozy.FourierArithmetic Sarkozy.PaperFrame
  Sarkozy.BlockFrame Sarkozy.IndexSupport Sarkozy.TheoremC Sarkozy.Comparison
  Sarkozy.DensityChain Sarkozy.CancellationSteps Sarkozy.BlockAnchor Sarkozy.DensityChain2
  Sarkozy.DensityFibre Sarkozy.EnvelopeInputsBlock Sarkozy.RecordExpansion
  Sarkozy.RecordExpansion.Choice Sarkozy.E1Closure Sarkozy.EnvelopeSteps Sarkozy.Envelopes
open Sarkozy.Param (Params)
open Sarkozy.SharpFirst (sfEps sfEps_nonneg)

section Generic

variable {ι : Type*} [DecidableEq ι]

/-- **The background polynomial from the two totals** (see the module docstring). -/
theorem background_le_total (s : Finset ι) {κH κb U₀ tU : ℝ} (hb : 0 ≤ κb) (hbH : κb ≤ κH)
    {v w : ι → ℝ} (hv : ∀ b, 0 ≤ v b) (hw : ∀ b, 0 ≤ w b)
    (hVW : ∑ b ∈ s, (v b + w b) ≤ U₀) (htW : tU + ∑ b ∈ s, w b ≤ U₀) :
    κH * ∏ b ∈ s, (1 + v b + w b) - (κH - κb) * ∏ b ∈ s, (1 + v b) ≤
      κH * Real.exp U₀ - (κH - κb) * Real.exp tU := by
  have hc : 0 ≤ κH - κb := by linarith
  have hcκ : κH - κb ≤ κH := by linarith
  have h1 := bgPoly_le_exp s hc hcκ v w hv hw
  unfold bgPoly at h1
  have hVW' : ∑ b ∈ s, (v b + w b) = ∑ b ∈ s, v b + ∑ b ∈ s, w b := sum_add_distrib
  rw [hVW'] at h1 hVW
  set V := ∑ b ∈ s, v b with hV
  set W := ∑ b ∈ s, w b with hW
  have hW0 : 0 ≤ W := sum_nonneg fun b _ => hw b
  have hκ0 : 0 ≤ κH := hb.trans hbH
  refine h1.trans ?_
  rcases le_or_gt V tU with hVt | hVt
  · have hA : 0 ≤ κH * Real.exp W - (κH - κb) := by
      have : κH ≤ κH * Real.exp W := le_mul_of_one_le_right hκ0 (Real.one_le_exp hW0)
      linarith
    have e1 : κH * Real.exp (V + W) - (κH - κb) * Real.exp V =
        Real.exp V * (κH * Real.exp W - (κH - κb)) := by
      rw [Real.exp_add]
      ring
    have e2 : Real.exp V * (κH * Real.exp W - (κH - κb)) ≤
        Real.exp tU * (κH * Real.exp W - (κH - κb)) :=
      mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hVt) hA
    have e3 : Real.exp tU * (κH * Real.exp W - (κH - κb)) =
        κH * Real.exp (tU + W) - (κH - κb) * Real.exp tU := by
      rw [Real.exp_add]
      ring
    have e4 : κH * Real.exp (tU + W) ≤ κH * Real.exp U₀ :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr htW) hκ0
    linarith
  · have e4 : κH * Real.exp (V + W) ≤ κH * Real.exp U₀ :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hVW) hκ0
    have e5 : (κH - κb) * Real.exp tU ≤ (κH - κb) * Real.exp V :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hVt.le) hc
    linarith

/-- **`heval` in form (i) from the two totals** (`heval_of_finer` with `background_le_total`). -/
theorem heval_of_total [Fintype ι] {Ω : Type*} (𝒞 : Finset Ω) (wt CX : Ω → ℝ) (κH κb : Ω → ℝ)
    (EO r : Ω → (ι → Bool) → ℝ) {v w : ι → ℝ} {ε Y U₀ tU z κM : ℝ}
    (hv : ∀ b, 0 ≤ v b) (hw : ∀ b, 0 ≤ w b)
    (hVW : ∑ b, (v b + w b) ≤ U₀) (htW : tU + ∑ b, w b ≤ U₀) (hε : 0 ≤ ε)
    (hwt : ∀ ω ∈ 𝒞, 0 ≤ wt ω) (hCY : ∀ ω ∈ 𝒞, 0 ≤ CX ω * Y)
    (hκb : ∀ ω ∈ 𝒞, 0 ≤ κb ω) (hκbH : ∀ ω ∈ 𝒞, κb ω ≤ κH ω) (hκM : ∀ ω ∈ 𝒞, κH ω ≤ κM)
    (hz : ε * κM * Real.exp U₀ ≤ z)
    (hfine : ∀ ω ∈ 𝒞, ∀ f, EO ω f ≤
      (1 + ε) * CX ω * Y * ∏ c, (if f c then w c else 1 + v c) + r ω f) :
    ∑ ω ∈ 𝒞, wt ω * ∑ f : ι → Bool, (if f = (fun _ => false) then κb ω else κH ω) * EO ω f ≤
      (∑ ω ∈ 𝒞, wt ω * CX ω * (κH ω * Real.exp U₀ - (κH ω - κb ω) * Real.exp tU)) * Y +
        z * (∑ ω ∈ 𝒞, wt ω * CX ω) * Y +
        ∑ ω ∈ 𝒞, wt ω * ∑ f : ι → Bool, (if f = (fun _ => false) then κb ω else κH ω) * r ω f := by
  have hper : ∀ ω ∈ 𝒞, wt ω * ∑ f : ι → Bool, (if f = (fun _ => false) then κb ω else κH ω) *
      EO ω f ≤ wt ω * CX ω * (κH ω * Real.exp U₀ - (κH ω - κb ω) * Real.exp tU) * Y +
        z * (wt ω * CX ω) * Y +
        wt ω * ∑ f : ι → Bool, (if f = (fun _ => false) then κb ω else κH ω) * r ω f := by
    intro ω hω
    have hcap0 : ∀ f : ι → Bool, 0 ≤ (if f = (fun _ => false) then κb ω else κH ω) := fun f => by
      split_ifs
      · exact hκb ω hω
      · exact (hκb ω hω).trans (hκbH ω hω)
    have h1 : ∑ f : ι → Bool, (if f = (fun _ => false) then κb ω else κH ω) * EO ω f ≤
        ∑ f : ι → Bool, (if f = (fun _ => false) then κb ω else κH ω) *
          ((1 + ε) * CX ω * Y * ∏ c, (if f c then w c else 1 + v c) + r ω f) :=
      sum_le_sum fun f _ => mul_le_mul_of_nonneg_left (hfine ω hω f) (hcap0 f)
    have h2 : ∑ f : ι → Bool, (if f = (fun _ => false) then κb ω else κH ω) *
          ((1 + ε) * CX ω * Y * ∏ c, (if f c then w c else 1 + v c) + r ω f) =
        (1 + ε) * (CX ω * Y) * (κH ω * ∏ c, (1 + v c + w c) - (κH ω - κb ω) * ∏ c, (1 + v c)) +
          ∑ f : ι → Bool, (if f = (fun _ => false) then κb ω else κH ω) * r ω f := by
      rw [← background_poly_eq v w (κH ω) (κb ω), mul_sum, ← sum_add_distrib]
      exact sum_congr rfl fun f _ => by ring
    have h3 := background_le_total univ (hκb ω hω) (hκbH ω hω) hv hw hVW htW
    set X := κH ω * Real.exp U₀ - (κH ω - κb ω) * Real.exp tU
    have hXle : X ≤ κH ω * Real.exp U₀ := by
      have : 0 ≤ (κH ω - κb ω) * Real.exp tU :=
        mul_nonneg (by linarith [hκbH ω hω]) (Real.exp_pos _).le
      linarith
    have hCY0 := hCY ω hω
    have h4 : (1 + ε) * (CX ω * Y) * (κH ω * ∏ c, (1 + v c + w c) -
        (κH ω - κb ω) * ∏ c, (1 + v c)) ≤ (1 + ε) * (CX ω * Y) * X :=
      mul_le_mul_of_nonneg_left h3 (mul_nonneg (by linarith) hCY0)
    have h5 : (1 + ε) * (CX ω * Y) * X ≤ CX ω * Y * X + z * (CX ω * Y) := by
      have h6 : ε * X ≤ z := by
        have : ε * X ≤ ε * (κM * Real.exp U₀) := by
          refine mul_le_mul_of_nonneg_left (hXle.trans ?_) hε
          exact mul_le_mul_of_nonneg_right (hκM ω hω) (Real.exp_pos _).le
        linarith
      nlinarith [mul_le_mul_of_nonneg_left h6 hCY0]
    have h7 := h1.trans (h2.le.trans (add_le_add_left (h4.trans h5) _))
    have h8 := mul_le_mul_of_nonneg_left h7 (hwt ω hω)
    calc _ ≤ _ := h8
      _ = _ := by ring
  calc _ ≤ ∑ ω ∈ 𝒞, (wt ω * CX ω * (κH ω * Real.exp U₀ - (κH ω - κb ω) * Real.exp tU) * Y +
        z * (wt ω * CX ω) * Y +
        wt ω * ∑ f : ι → Bool, (if f = (fun _ => false) then κb ω else κH ω) * r ω f) :=
      sum_le_sum hper
    _ = _ := by
      rw [sum_add_distrib, sum_add_distrib, ← sum_mul, ← sum_mul, ← mul_sum]

end Generic

variable {a : ℝ}
variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

variable (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E) (L : ℕ)
  (isG : ∀ b : BlockAtom Bk PaperJt L, D.GB.Iu L b → Bool)

omit [DecidableEq P] in
/-- **The invariant and generic prices of the outside atoms add up to at most `U₀`**
(`U₀_total`). -/
theorem hVW_fine (S : Finset (BlockAtom Bk PaperJt L)) :
    ∑ c : {b // b ∉ S}, (finePr D L isG c.1 none (some false) +
      finePr D L isG c.1 none (some true)) ≤ D.GB.U₀ := by
  have hpt : ∀ b : BlockAtom Bk PaperJt L, finePr D L isG b none (some false) +
      finePr D L isG b none (some true) =
      ∑ i, mass (D.GB.κu L b i) * TheoremCBlock.selectionFactor a paperTail D.S.selPre L b := by
    intro b
    simp only [finePr, Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
    rw [← add_mul, add_comm, mass_filter_add D L isG b, mass_sum_measure, sum_mul]
  have h0 : ∀ b : BlockAtom Bk PaperJt L, 0 ≤
      ∑ i, mass (D.GB.κu L b i) * TheoremCBlock.selectionFactor a paperTail D.S.selPre L b :=
    fun b => sum_nonneg fun i _ => mul_nonneg
      (TheoremCBlock.ComparisonData.mass_nonneg_of_nonneg (D.GB.κu_pos L b i).1)
      (D.selectionFactor_nonneg L b)
  simp only [hpt]
  rw [← Finset.sum_subtype (univ.filter (fun b => b ∉ S)) (p := fun b => b ∉ S) (fun b => by simp)
    (fun b => ∑ i, mass (D.GB.κu L b i) * TheoremCBlock.selectionFactor a paperTail D.S.selPre L b)]
  exact (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun b _ _ => h0 b).trans
    (D.GB.U₀_total L)

omit [DecidableEq P] in
theorem htW_of_le (S : Finset (BlockAtom Bk PaperJt L)) {n : {b // b ∉ S} → ℝ} {tU : ℝ}
    (hwn : ∀ c, finePr D L isG c.1 none (some true) ≤ n c) (htn : tU + ∑ c, n c ≤ D.GB.U₀) :
    tU + ∑ c : {b // b ∉ S}, finePr D L isG c.1 none (some true) ≤ D.GB.U₀ :=
  le_trans (add_le_add_right (sum_le_sum fun c _ => hwn c) _) htn

omit [DecidableEq P] in
/-- **Step 4 in form (i), with the prices from the data**: `step4_fine` where the upper prices are
replaced by `U₀_total` (proved: `∑_𝔟 (v_𝔟 + w_𝔟) ≤ U₀`) and one scalar condition on the generic
prices: `w ≤ n` and `tU + ∑ n ≤ U₀` (`lem:oct24:invariant-background`(v): `U₀ ≥ t(U_inv + ∑ u^G)`,
F). -/
theorem step4_total (A : Finset ℤ) (S : Finset (BlockAtom Bk PaperJt L)) (hY : 0 ≤ D.Y L A)
    (hR : ZMod 6) (hinv : ∀ b ∉ S, slotPush (slotREquiv hR) (D.GB.N₀ L b) = D.GB.N₀ L b)
    (𝒞 : Finset (Choice (D.CL.T L))) (hS : ∀ ω ∈ 𝒞, Choice.support ω = S)
    (bar : Choice (D.CL.T L) → Choice (D.CL.T L)) (hbar𝒞 : ∀ ω ∈ 𝒞, bar ω ∈ 𝒞)
    (hbar : ∀ ω ∈ 𝒞, bar (bar ω) = ω) (wt : Choice (D.CL.T L) → ℝ)
    (hwtb : ∀ ω ∈ 𝒞, wt (bar ω) = wt ω) (hwt : ∀ ω ∈ 𝒞, 0 ≤ wt ω)
    (O : {b // b ∈ S} → Type) [∀ b, Fintype (O b)] [∀ b, DecidableEq (O b)]
    (mb : ∀ b, O b → ℝ)
    (φb : Choice (D.CL.T L) → ∀ b, O b → (reservedCut.Half → BlockLabel m₀ blk paperTail L b.1))
    (hD : ∀ ω ∈ 𝒞, ∀ b (hb : b ∈ S), ∀ t e, ω b = some (t, e) →
      reservedCut.diagonalLaw (push (mb ⟨b, hb⟩) (φb ω ⟨b, hb⟩)) = D.CL.D L b t e)
    (ψ : Choice (D.CL.T L) → (∀ b, O b) ≃ (∀ b, O b))
    (hm : ∀ ω ∈ 𝒞, ∀ x, prodWeight mb (ψ ω x) = prodWeight mb x)
    (ha : ∀ ω ∈ 𝒞, ∀ x, (fun v => prodPlace reservedCut (φb (bar ω)) x
        (halfPerm reservedCut (slotREquiv hR) (slotR_half hR) v)) =
      prodPlace reservedCut (φb ω) (ψ ω x))
    (T : Choice (D.CL.T L) →
      (((∀ b, O b) → ℝ) →ₗ[ℝ] ((∀ b, O b) → ℝ)) →ₗ[ℝ] (((∀ b, O b) → ℝ) →ₗ[ℝ] ((∀ b, O b) → ℝ)))
    (K : Choice (D.CL.T L) → ((∀ b, O b) → ℝ) →ₗ[ℝ] ((∀ b, O b) → ℝ))
    (hK : ∀ ω ∈ 𝒞, K (bar ω) = T ω (K ω))
    (Kx : Choice (D.CL.T L) → ({b // b ∉ S} → Bool) → ((∀ b, O b) → ℝ) →ₗ[ℝ] ((∀ b, O b) → ℝ))
    (κH κb : Choice (D.CL.T L) → ℝ) {κM : ℝ}
    (hκb : ∀ ω ∈ 𝒞, 0 ≤ κb ω) (hκbH : ∀ ω ∈ 𝒞, κb ω ≤ κH ω) (hκM : ∀ ω ∈ 𝒞, κH ω ≤ κM)
    (hextra : ∀ ω ∈ 𝒞, ∀ f, paperEO L A S (NinvOf D L isG) (GOf D L isG) f
      (place reservedCut (prodWeight mb) (prodPlace reservedCut (φb ω))
        ((1 / 2 : ℝ) • (K ω + conjObj (ψ ω) (T ω (K ω))))) =
        paperEO L A S (NinvOf D L isG) (GOf D L isG) f
          (place reservedCut (prodWeight mb) (prodPlace reservedCut (φb ω)) (Kx ω f)))
    (hcap : ∀ ω ∈ 𝒞, ∀ f, OpLE (prodWeight mb) (Kx ω f) (capZ L (κH ω) (κb ω) f • LinearMap.id))
    {n : {b // b ∉ S} → ℝ} {tU z : ℝ}
    (hwn : ∀ c, finePr D L isG c.1 none (some true) ≤ n c)
    (htn : tU + ∑ c, n c ≤ D.GB.U₀)
    (hz : sfEps D L * κM * Real.exp D.GB.U₀ ≤ z)
    (YN0 : Choice (D.CL.T L) → ℝ)
    (hYN0 : ∀ ω ∈ 𝒞, YN0 ω = paperEN0 D L A S
      (place reservedCut (prodWeight mb) (prodPlace reservedCut (φb ω)) (K ω))) :
    ∑ ω ∈ 𝒞, wt ω * YN0 ω ≤
      (∑ ω ∈ 𝒞, wt ω * (∏ b ∈ Choice.support ω,
          TheoremCBlock.selectionFactor a paperTail D.S.selPre L b) *
          (κH ω * Real.exp D.GB.U₀ - (κH ω - κb ω) * Real.exp tU)) * D.Y L A +
        z * (∑ ω ∈ 𝒞, wt ω * (∏ b ∈ Choice.support ω,
          TheoremCBlock.selectionFactor a paperTail D.S.selPre L b)) * D.Y L A +
        ∑ ω ∈ 𝒞, wt ω * ∑ f : {b // b ∉ S} → Bool, capZ L (κH ω) (κb ω) f *
          ∑ g ∈ Fintype.piFinset (Tset L S f), fX D L isG (sfEps D) A ω g := by
  set CX : Choice (D.CL.T L) → ℝ :=
    fun ω => ∏ b ∈ Choice.support ω, TheoremCBlock.selectionFactor a paperTail D.S.selPre L b
    with hCX
  refine step4_of_caps_finset D L A S hR hinv 𝒞 bar hbar𝒞 hbar wt hwtb hwt (prodWeight mb)
    (fun ω => prodPlace reservedCut (φb ω)) ψ hm ha T K hK (NinvOf D L isG) (GOf D L isG)
    (fun b _ => N₀_eq_split D L isG b) (fun b _ => NinvOf_positive D L isG b)
    (fun b _ => GOf_positive D L isG b) Kx (fun ω f => capZ L (κH ω) (κb ω) f) hextra
    hcap CX YN0 hYN0 ?_
  exact heval_of_total 𝒞 wt CX κH κb
    (fun ω f => paperEO L A S (NinvOf D L isG) (GOf D L isG) f
      (reservedCut.diagonalLaw (push (prodWeight mb) (prodPlace reservedCut (φb ω)))))
    (fun ω f => ∑ g ∈ Fintype.piFinset (Tset L S f), fX D L isG (sfEps D) A ω g)
    (v := fun c => finePr D L isG c.1 none (some false))
    (w := fun c => finePr D L isG c.1 none (some true))
    (fun c => finePr_nonneg D L isG c.1 none _) (fun c => finePr_nonneg D L isG c.1 none _)
    (hVW_fine D L isG S) (htW_of_le D L isG S hwn htn) (sfEps_nonneg D L) hwt
    (fun ω _ => mul_nonneg (prod_nonneg fun b _ => D.selectionFactor_nonneg L b) hY)
    hκb hκbH hκM hz
    (fun ω hω f => hfine_of_fine D L isG (sfEps D) A ω S (hS ω hω) O mb (φb ω) (hD ω hω) f)

end Sarkozy.OpsSteps
