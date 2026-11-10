module

public import Sarkozy.OpsSteps.Prices

@[expose] public section

/-!
# The additional average of Step 4 (i) at `Z = ∅` (OPS-S)

`paper/sections/23_envelopes.tex`, proof of `thm:envelopes`, Step 4 and "(iii) and (i)";
`lem:oct24:invariant-background`(i)–(iv), `lem:reflection-averaging`(f).

At the outside set `Z = ∅` the outside law `O_∅ = ⊗ Ñ^inv` is invariant under a further reflection
`R_{h'}` when every `Ñ^inv_𝔟` is, so the kernel may be averaged once more before its norm is taken
(cap `κ_b` instead of `κ_H`).

* **`hextra_of_inv`**: the input `hextra` of `step4_of_caps` with
  `K^x_{ω,∅} = ½(D̄_ω + 𝒫'D̄_ω𝒫'^*)` and `K^x_{ω,Z} = D̄_ω` for `Z ≠ ∅`, from the
  `R_{h'}`-invariance of `Ñ^inv` outside `S` and a relabelling `ψ'` of the objects carrying the
  placement (`extra_average_placed`);
* **`step4_inv`**: Step 4 in form (i) (`step4_total`) with `hextra` discharged: the caps are
  `D̄_ω ⪯ κ_H I` and `½(D̄_ω + 𝒫'D̄_ω𝒫'^*) ⪯ κ_b I`.
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

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]

/-- **`hextra` from the invariance of `Ñ^inv`** (see the module docstring). -/
theorem hextra_of_inv (L : ℕ) (A : Finset ℤ) (S : Finset (BlockAtom Bk J L)) (h' : ZMod 6)
    (Ninv G : ∀ b : BlockAtom Bk J L, TheoremCBlock.AtomMeasure m₀ blk p L b)
    (hinvN : ∀ b ∉ S, slotPush (slotREquiv h') (Ninv b) = Ninv b)
    {O : Type} [Fintype O] [DecidableEq O] (m : O → ℝ)
    (φ : O → (reservedCut.Half → PIn (m₀ := m₀) (blk := blk) (p := p) L S))
    (ψ' : O ≃ O) (hm' : ∀ x, m (ψ' x) = m x)
    (ha' : ∀ x, (fun v => φ x (halfPerm reservedCut (slotREquiv h') (slotR_half h') v)) = φ (ψ' x))
    (K : (O → ℝ) →ₗ[ℝ] (O → ℝ)) (f : {b // b ∉ S} → Bool) :
    paperEO L A S Ninv G f (place reservedCut m φ K) =
      paperEO L A S Ninv G f (place reservedCut m φ
        (if f = (fun _ => false) then (1 / 2 : ℝ) • (K + conjObj ψ' K) else K)) := by
  split_ifs with hf
  · subst hf
    unfold paperEO
    rw [jointEnergyL_apply, jointEnergyL_apply]
    refine extra_average_placed reservedCut (slotREquiv h') (slotR_half h') (slotR_flip h') ?_ m φ
      ψ' hm' ha' K _
    unfold OZ
    rw [slotPush_tensorLaw]
    congr 1
    funext b
    simp only [Bool.false_eq_true, ↓reduceIte]
    exact hinvN b.1 b.2
  · rfl

end Generic

variable {a : ℝ}
variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

variable (D : TheoremCBlock.ComparisonData a m₀ blk paperTail pr h E) (L : ℕ)
  (isG : ∀ b : BlockAtom Bk PaperJt L, D.GB.Iu L b → Bool)

omit [DecidableEq P] in
/-- **Step 4 in form (i) with the additional average at `Z = ∅`** (see the module docstring). -/
theorem step4_inv (A : Finset ℤ) (S : Finset (BlockAtom Bk PaperJt L)) (hY : 0 ≤ D.Y L A)
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
    (κH κb : Choice (D.CL.T L) → ℝ) {κM : ℝ}
    (hκb : ∀ ω ∈ 𝒞, 0 ≤ κb ω) (hκbH : ∀ ω ∈ 𝒞, κb ω ≤ κH ω) (hκM : ∀ ω ∈ 𝒞, κH ω ≤ κM)
    (h' : ZMod 6) (hinvN : ∀ b ∉ S, slotPush (slotREquiv h') (NinvOf D L isG b) = NinvOf D L isG b)
    (ψ' : Choice (D.CL.T L) → (∀ b, O b) ≃ (∀ b, O b))
    (hm' : ∀ ω ∈ 𝒞, ∀ x, prodWeight mb (ψ' ω x) = prodWeight mb x)
    (ha' : ∀ ω ∈ 𝒞, ∀ x, (fun v => prodPlace reservedCut (φb ω) x
        (halfPerm reservedCut (slotREquiv h') (slotR_half h') v)) =
      prodPlace reservedCut (φb ω) (ψ' ω x))
    (hcapH : ∀ ω ∈ 𝒞, OpLE (prodWeight mb)
      ((1 / 2 : ℝ) • (K ω + conjObj (ψ ω) (T ω (K ω)))) (κH ω • LinearMap.id))
    (hcapb : ∀ ω ∈ 𝒞, OpLE (prodWeight mb)
      ((1 / 2 : ℝ) • ((1 / 2 : ℝ) • (K ω + conjObj (ψ ω) (T ω (K ω))) +
        conjObj (ψ' ω) ((1 / 2 : ℝ) • (K ω + conjObj (ψ ω) (T ω (K ω))))))
      (κb ω • LinearMap.id))
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
  refine step4_total D L isG A S hY hR hinv 𝒞 hS bar hbar𝒞 hbar wt hwtb hwt O mb φb hD ψ hm ha T K
    hK (fun ω f => if f = (fun _ => false) then
      (1 / 2 : ℝ) • ((1 / 2 : ℝ) • (K ω + conjObj (ψ ω) (T ω (K ω))) +
        conjObj (ψ' ω) ((1 / 2 : ℝ) • (K ω + conjObj (ψ ω) (T ω (K ω)))))
      else (1 / 2 : ℝ) • (K ω + conjObj (ψ ω) (T ω (K ω))))
    κH κb hκb hκbH hκM (fun ω hω f => ?_) (fun ω hω f => ?_) hwn htn hz YN0 hYN0
  · exact hextra_of_inv L A S h' (NinvOf D L isG) (GOf D L isG) hinvN (prodWeight mb)
      (prodPlace reservedCut (φb ω)) (ψ' ω) (hm' ω hω) (ha' ω hω) _ f
  · unfold capZ
    split_ifs
    · exact hcapb ω hω
    · exact hcapH ω hω

end Sarkozy.OpsSteps
