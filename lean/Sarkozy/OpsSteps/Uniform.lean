module

public import Sarkozy.OpsSteps.Step4
public import Sarkozy.OpsSteps.Coupled
public import Sarkozy.OpsSteps.E1Proved

@[expose] public section

/-!
# Step 4 in the uniform-cost form `thm:envelopes`(ii), proved from (E1) (OPS-S)

`paper/sections/23_envelopes.tex`, `thm:envelopes`(ii) and its proof ("(ii) is the case
`κ_b = κ_H`, `M^inv = 0` of (i), which needs neither the additional averages nor
`lem:orbit-coupon`: by (E2) with `Ñ₀ ⪰_ι 0` outside and (E1),
`Y^{Ñ₀}[[D̄_ω]_ω] ≤ ‖D̄_ω‖ (e^{U₀} + o(1)) C_X Y`"); `paper/sections/10_comparison_lemmas.tex`,
`lem:bracket-energy` (second bound, `|𝔈_{Ñ₀}[κ]| ≤ (e^{U₀} + o(1)) ‖κ‖ Π_X Y`).

EC proved the subset terms of (E1) for the norm envelopes of **all** selections (`E1Sub` at the
canonical remainders `r0X`, summed in `E1Rem`). Their sum over the outside sets is the energy of the
envelope law against `Ñ₀`. With the identification `D^ε_{𝔟,t} = Diag_ι(m_{t,𝔟})` this bounds
`Y^{Ñ₀}[Diag_ω]`, and with the caps it closes Step 4 in the uniform-cost form:

* `envN0_eq_sum_subInt`: `Y[env_ω ⊗ Ñ₀] = ∑_f 𝔈_{ω,f}` (EC's `subInt`; `Ñ₀ = μ + ∑_i κu_i`);
* `sum_subMain_le`: `∑_f M_{ω,f} ≤ (1 + ε_E) e^{U₀} C_X Y` (`∏ (1 + u_𝔟) ≤ e^{∑ u} ≤ e^{U₀}`);
* `paperEN0_diag_eq_envN0`: `Y^{Ñ₀}[Diag_ω] = Y[env_ω ⊗ Ñ₀]` (product objects, `supp ω = S`,
  the identification `hD`);
* **`paperEN0_diag_le`**: `Y^{Ñ₀}[Diag_ω] ≤ (1 + ε_E) e^{U₀} C_X Y + ∑_f r0X_{ω,f}`;
* **`heval_uniform`**: the evaluation input `heval` of `step4_of_caps` with `Ñ^inv = Ñ₀`, `G = 0`
  and caps `b_ω`: `∑ π̃ b_ω Y^{Ñ₀}[Diag_ω] ≤ e^{U₀} (∑ π̃ b C_X) Y + z (∑ π̃ C_X) Y + ∑ π̃ b r`;
* **`step4_uniform`**: the field `step4` of B11's `DegreeOps` with
  `W_Z = e^{U₀} (∑_ω π̃_ω b_ω C_X) Y` (the uniform background `κ_H e^{U₀} π^arm Y`), from the
  averaging inputs, `Ñ_{0,𝔅} ⪰_ι 0`, the caps `D̄_ω ⪯ b_ω I`, the identification, and the
  envelope bound of EC (no further analytic input). The remainders `r₄ = ∑ π̃ b ∑_f r0X` are a part
  of EC's summed `E1Rem` (`E1Diag.sum_rem_le`).

What `thm:envelopes`(i) adds to this is the split `Ñ₀ = Ñ^inv + G` with the smaller cap
`b(ω) < κ_H` on the invariant monomials (`(κ_H − κ_b) e^{tU}`) and the orbit coupon: these need
(E1) for the finer subset terms (the tags of `E_add + H` and of `G` separately), which is the
remaining input `heval` of `step4_of_caps`.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.OpsSteps

open Sarkozy.EnvelopeSteps Sarkozy.RecordExpansion Sarkozy.RecordExpansion.Choice
  Sarkozy.TheoremC Sarkozy.TheoremCBlock Sarkozy.BlockFrame Sarkozy.E1Closure Sarkozy.Envelopes

variable {a : ℝ}
  {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

variable (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)

omit [DecidableEq P] in
/-- **The energy of the envelope law against `Ñ₀` is the sum of EC's subset terms**:
`Y[(⊗_X D) ⊗ Ñ₀] = ∑_f 𝔈_{ω,f}` (`Ñ_{0,𝔟} = μ_𝔟 + ∑_i κu_{𝔟,i}`, `subLaw`). -/
theorem envN0_eq_sum_subInt (L : ℕ) (A : Finset ℤ) (ω : Choice (D.CL.T L)) :
    diagonalIntegral (envelopeLaw (D.GB.N₀ L) (D.CL.D L) ω) (blockLift m₀ blk p L A) =
      ∑ f : BlockAtom Bk J L → Bool, subInt D L A ω f := by
  unfold subInt envelopeLaw
  have hsplit : (fun b => entryFactor (D.GB.N₀ L b) (D.CL.D L b) (ω b)) =
      fun b => entryFactor (D.R.law p L b) (D.CL.D L b) (ω b) +
        (if (ω b).isSome then 0 else ∑ i, D.GB.κu L b i) := by
    funext b
    rcases hω : ω b with _ | ⟨t, e⟩
    · simp only [Option.isSome_none, Bool.false_eq_true, ↓reduceIte]
      change D.GB.N₀ L b = D.R.law p L b + ∑ i, D.GB.κu L b i
      rw [← D.GB.N₀_sub L b]
      abel
    · simp only [Option.isSome_some, ↓reduceIte, add_zero]
      rfl
  rw [hsplit, energy_add_eq_sum]
  rfl

omit [DecidableEq P] in
/-- **The main terms of the subset terms sum to at most `(1 + ε_E) e^{U₀} C_X Y`**. -/
theorem sum_subMain_le (εE : ℕ → ℝ) (L : ℕ) (A : Finset ℤ) (ω : Choice (D.CL.T L))
    (h0 : 0 ≤ (1 + εE L) * (∏ b ∈ Choice.support ω, selectionFactor a p D.S.selPre L b) * D.Y L A) :
    ∑ f : BlockAtom Bk J L → Bool, subMain D εE L A ω f ≤
      (1 + εE L) * (∏ b ∈ Choice.support ω, selectionFactor a p D.S.selPre L b) * D.Y L A *
        Real.exp D.GB.U₀ := by
  set K := (1 + εE L) * (∏ b ∈ Choice.support ω, selectionFactor a p D.S.selPre L b) * D.Y L A
  let u' : BlockAtom Bk J L → ℝ := fun b => if (ω b).isSome then 0 else D.GB.uprice L b
  have hu0 : ∀ b, 0 ≤ u' b := fun b => by
    show 0 ≤ if (ω b).isSome then 0 else D.GB.uprice L b
    split_ifs
    · exact le_rfl
    · exact BracketEnergy.uprice_nonneg D L b
  have hsum : ∑ f : BlockAtom Bk J L → Bool, subMain D εE L A ω f = K * ∏ b, (1 + u' b) := by
    unfold subMain
    rw [← mul_sum]
    congr 1
    rw [← Fintype.prod_sum (fun b (y : Bool) => if y then u' b else 1)]
    refine prod_congr rfl fun b _ => ?_
    rw [Fintype.sum_bool]
    simp only [↓reduceIte, Bool.false_eq_true, u']
    ring
  rw [hsum]
  refine mul_le_mul_of_nonneg_left ?_ h0
  refine (RecordExpansion.prod_one_add_le_exp u' hu0).trans (Real.exp_le_exp.mpr ?_)
  refine le_trans (sum_le_sum fun b _ => ?_) (BracketEnergy.sum_uprice_le D L)
  show (if (ω b).isSome then 0 else D.GB.uprice L b) ≤ D.GB.uprice L b
  split_ifs
  · exact BracketEnergy.uprice_nonneg D L b
  · exact le_rfl

omit [DecidableEq P] in
/-- **`Y^{Ñ₀}[Diag_ω]` is the energy of the envelope law against `Ñ₀`**, for product objects on
the block set `S = supp ω` whose diagonals are the norm envelopes (`def:cp4`(b)). -/
theorem paperEN0_diag_eq_envN0 (L : ℕ) (A : Finset ℤ) (S : Finset (BlockAtom Bk J L))
    (ω : Choice (D.CL.T L)) (hS : Choice.support ω = S)
    (O : {b // b ∈ S} → Type) [∀ b, Fintype (O b)] [∀ b, DecidableEq (O b)]
    (m : ∀ b, O b → ℝ) (φ : ∀ b, O b → (reservedCut.Half → BlockLabel m₀ blk p L b.1))
    (hD : ∀ b (hb : b ∈ S), ∀ t e, ω b = some (t, e) →
      reservedCut.diagonalLaw (push (m ⟨b, hb⟩) (φ ⟨b, hb⟩)) = D.CL.D L b t e) :
    paperEN0 D L A S
        (reservedCut.diagonalLaw (push (prodWeight m) (prodPlace reservedCut φ))) =
      diagonalIntegral (envelopeLaw (D.GB.N₀ L) (D.CL.D L) ω) (blockLift m₀ blk p L A) := by
  rw [← place_id, place_tensor reservedCut m φ (fun _ => LinearMap.id) LinearMap.id
    (kern_id_prod m)]
  simp only [place_id]
  let Qb : ∀ b : BlockAtom Bk J L, TheoremCBlock.AtomMeasure m₀ blk p L b := fun b =>
    if hb : b ∈ S then reservedCut.diagonalLaw (push (m ⟨b, hb⟩) (φ ⟨b, hb⟩)) else 0
  have hQ : (fun b : {b // b ∈ S} => reservedCut.diagonalLaw (push (m b) (φ b))) =
      fun b : {b // b ∈ S} => Qb b.1 := by
    funext b
    simp only [Qb, b.2, ↓reduceDIte]
  rw [hQ, paperEN0_tensor]
  unfold envelopeLaw
  congr 2
  funext b
  by_cases hb : b ∈ S
  · simp only [hb, decide_true, ↓reduceIte, Qb, ↓reduceDIte]
    have hb' : b ∈ Choice.support ω := hS ▸ hb
    rcases hω : ω b with _ | ⟨t, e⟩
    · exact absurd (by simpa [Choice.support] using hb') (by simp [hω])
    · exact hD b hb t e hω
  · simp only [hb, decide_false, Bool.false_eq_true, ↓reduceIte]
    have hb' : b ∉ Choice.support ω := hS ▸ hb
    rw [eq_none_of_not_mem_support D hb']
    rfl

omit [DecidableEq P] in
/-- **(E1) against `Ñ₀` for the diagonal of a selection** (`lem:bracket-energy`, second bound, from
EC's subset terms): `Y^{Ñ₀}[Diag_ω] ≤ (1 + ε_E) e^{U₀} C_X Y + ∑_f r0X_{ω,f}`. -/
theorem paperEN0_diag_le (εE : ℕ → ℝ) (L : ℕ) (A : Finset ℤ) (S : Finset (BlockAtom Bk J L))
    (ω : Choice (D.CL.T L)) (hS : Choice.support ω = S)
    (O : {b // b ∈ S} → Type) [∀ b, Fintype (O b)] [∀ b, DecidableEq (O b)]
    (m : ∀ b, O b → ℝ) (φ : ∀ b, O b → (reservedCut.Half → BlockLabel m₀ blk p L b.1))
    (hD : ∀ b (hb : b ∈ S), ∀ t e, ω b = some (t, e) →
      reservedCut.diagonalLaw (push (m ⟨b, hb⟩) (φ ⟨b, hb⟩)) = D.CL.D L b t e)
    (h0 : 0 ≤ (1 + εE L) * (∏ b ∈ Choice.support ω, selectionFactor a p D.S.selPre L b) *
      D.Y L A) :
    paperEN0 D L A S
        (reservedCut.diagonalLaw (push (prodWeight m) (prodPlace reservedCut φ))) ≤
      (1 + εE L) * (∏ b ∈ Choice.support ω, selectionFactor a p D.S.selPre L b) * D.Y L A *
        Real.exp D.GB.U₀ + ∑ f : BlockAtom Bk J L → Bool, r0X D εE L A ω f := by
  rw [paperEN0_diag_eq_envN0 D L A S ω hS O m φ hD, envN0_eq_sum_subInt]
  have hle : ∀ f : BlockAtom Bk J L → Bool,
      subInt D L A ω f ≤ subMain D εE L A ω f + r0X D εE L A ω f := by
    intro f
    unfold r0X
    linarith [le_abs_self (subInt D L A ω f),
      le_max_right 0 (|subInt D L A ω f| - subMain D εE L A ω f)]
  calc ∑ f, subInt D L A ω f ≤ ∑ f, (subMain D εE L A ω f + r0X D εE L A ω f) :=
        sum_le_sum fun f _ => hle f
    _ = _ := by rw [sum_add_distrib]
    _ ≤ _ := by linarith [sum_subMain_le D εE L A ω h0]

/-- **The evaluation of Step 4 in the uniform-cost form**: per-selection bounds
`Y^{Ñ₀}[Diag_ω] ≤ (1 + ε) e^{U₀} C_X Y + r_ω` and caps `0 ≤ b_ω ≤ b` with `ε e^{U₀} b ≤ z` give
`∑ π̃ b_ω Y^{Ñ₀}[Diag_ω] ≤ e^{U₀} (∑ π̃ b C_X) Y + z (∑ π̃ C_X) Y + ∑ π̃ b r`. -/
theorem heval_uniform {Ω : Type*} (𝒞 : Finset Ω) (wt cap CX YD r : Ω → ℝ) {ε U₀ Y z bmax : ℝ}
    (hwt : ∀ ω ∈ 𝒞, 0 ≤ wt ω) (hcap0 : ∀ ω ∈ 𝒞, 0 ≤ cap ω) (hcap : ∀ ω ∈ 𝒞, cap ω ≤ bmax)
    (hCY : ∀ ω ∈ 𝒞, 0 ≤ CX ω * Y) (hε : 0 ≤ ε) (hz : ε * Real.exp U₀ * bmax ≤ z)
    (hYD : ∀ ω ∈ 𝒞, YD ω ≤ (1 + ε) * CX ω * Y * Real.exp U₀ + r ω) :
    ∑ ω ∈ 𝒞, wt ω * (cap ω * YD ω) ≤
      Real.exp U₀ * (∑ ω ∈ 𝒞, wt ω * cap ω * CX ω) * Y + z * (∑ ω ∈ 𝒞, wt ω * CX ω) * Y +
        ∑ ω ∈ 𝒞, wt ω * cap ω * r ω := by
  have hper : ∀ ω ∈ 𝒞, wt ω * (cap ω * YD ω) ≤
      Real.exp U₀ * (wt ω * cap ω * CX ω) * Y + z * (wt ω * CX ω) * Y + wt ω * cap ω * r ω := by
    intro ω hω
    have h1 := mul_le_mul_of_nonneg_left (hYD ω hω) (mul_nonneg (hwt ω hω) (hcap0 ω hω))
    have he : 0 ≤ Real.exp U₀ := (Real.exp_pos _).le
    have hwCY : 0 ≤ wt ω * (CX ω * Y) := mul_nonneg (hwt ω hω) (hCY ω hω)
    have h2 : ε * Real.exp U₀ * cap ω ≤ z :=
      le_trans (mul_le_mul_of_nonneg_left (hcap ω hω) (mul_nonneg hε he)) hz
    have h3 := mul_le_mul_of_nonneg_right h2 hwCY
    nlinarith
  calc _ ≤ ∑ ω ∈ 𝒞, (Real.exp U₀ * (wt ω * cap ω * CX ω) * Y + z * (wt ω * CX ω) * Y +
        wt ω * cap ω * r ω) := sum_le_sum hper
    _ = _ := by
      rw [sum_add_distrib, sum_add_distrib, ← sum_mul, ← mul_sum, ← sum_mul, ← mul_sum]

omit [DecidableEq P] in
/-- **The field `step4` of B11's `DegreeOps` in the uniform-cost form** (`thm:envelopes`(ii)), with
the background `W_Z = e^{U₀} (∑_ω π̃_ω b_ω C_X) Y` and `r₄ = ∑ π̃ b ∑_f r0X`: from the averaging
inputs of `step4_averaging` (`hinv`, `ha`, `hK`), `Ñ_{0,𝔟} ⪰_ι 0` outside `S`, the caps
`D̄_ω ⪯ b_ω I` (`lem:oct24:mask-schur`(b)), the identification of the norm envelopes (`hD`) and
`supp ω = S` on the class. The analytic content, (E1) against `Ñ₀`, is EC's. -/
theorem step4_uniform (εE : ℕ → ℝ) (hεE : ∀ L, 0 ≤ εE L) (L : ℕ) (A : Finset ℤ)
    (S : Finset (BlockAtom Bk J L)) (hY : 0 ≤ D.Y L A)
    (hR : ZMod 6) (hinv : ∀ b ∉ S, slotPush (slotREquiv hR) (D.GB.N₀ L b) = D.GB.N₀ L b)
    (hN0 : ∀ b ∉ S, reservedCut.Positive (D.GB.N₀ L b))
    (𝒞 : Finset (Choice (D.CL.T L))) (hS : ∀ ω ∈ 𝒞, Choice.support ω = S)
    (bar : Choice (D.CL.T L) → Choice (D.CL.T L)) (hbar𝒞 : ∀ ω ∈ 𝒞, bar ω ∈ 𝒞)
    (hbar : ∀ ω ∈ 𝒞, bar (bar ω) = ω) (wt : Choice (D.CL.T L) → ℝ)
    (hwtb : ∀ ω ∈ 𝒞, wt (bar ω) = wt ω) (hwt : ∀ ω ∈ 𝒞, 0 ≤ wt ω)
    (O : {b // b ∈ S} → Type) [∀ b, Fintype (O b)] [∀ b, DecidableEq (O b)]
    (mb : ∀ b, O b → ℝ)
    (φb : Choice (D.CL.T L) → ∀ b, O b → (reservedCut.Half → BlockLabel m₀ blk p L b.1))
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
    (cap : Choice (D.CL.T L) → ℝ) {bmax z : ℝ} (hcap0 : ∀ ω ∈ 𝒞, 0 ≤ cap ω)
    (hcapM : ∀ ω ∈ 𝒞, cap ω ≤ bmax) (hz : εE L * Real.exp D.GB.U₀ * bmax ≤ z)
    (hcap : ∀ ω ∈ 𝒞, OpLE (prodWeight mb)
      ((1 / 2 : ℝ) • (K ω + conjObj (ψ ω) (T ω (K ω)))) (cap ω • LinearMap.id))
    (YN0 : Choice (D.CL.T L) → ℝ)
    (hYN0 : ∀ ω ∈ 𝒞, YN0 ω = paperEN0 D L A S
      (place reservedCut (prodWeight mb) (prodPlace reservedCut (φb ω)) (K ω))) :
    ∑ ω ∈ 𝒞, wt ω * YN0 ω ≤
      Real.exp D.GB.U₀ * (∑ ω ∈ 𝒞, wt ω * cap ω *
          (∏ b ∈ Choice.support ω, selectionFactor a p D.S.selPre L b)) * D.Y L A +
        z * (∑ ω ∈ 𝒞, wt ω * (∏ b ∈ Choice.support ω, selectionFactor a p D.S.selPre L b)) *
          D.Y L A +
        ∑ ω ∈ 𝒞, wt ω * cap ω * ∑ f : BlockAtom Bk J L → Bool, r0X D εE L A ω f := by
  set CX : Choice (D.CL.T L) → ℝ :=
    fun ω => ∏ b ∈ Choice.support ω, selectionFactor a p D.S.selPre L b with hCX
  have hsplit : ∀ b ∉ S, D.GB.N₀ L b = D.GB.N₀ L b + 0 := fun b _ => (add_zero _).symm
  have hG : ∀ b ∉ S, reservedCut.Positive (0 : TheoremCBlock.AtomMeasure m₀ blk p L b) := by
    intro b hb
    have := (hN0 b hb).smul (le_refl (0 : ℝ))
    rwa [zero_smul] at this
  refine step4_of_caps_finset D L A S hR hinv 𝒞 bar hbar𝒞 hbar wt hwtb hwt (prodWeight mb)
    (fun ω => prodPlace reservedCut (φb ω)) ψ hm ha T K hK (D.GB.N₀ L) (fun _ => 0) hsplit hN0 hG
    (fun ω _ => (1 / 2 : ℝ) • (K ω + conjObj (ψ ω) (T ω (K ω)))) (fun ω _ => cap ω)
    (fun _ _ _ => rfl) (fun ω hω _ => hcap ω hω) CX YN0 hYN0 ?_
  have hexp : ∀ ω ∈ 𝒞, ∑ f : {b // b ∉ S} → Bool, cap ω *
      paperEO L A S (D.GB.N₀ L) (fun _ => 0) f
        (reservedCut.diagonalLaw (push (prodWeight mb) (prodPlace reservedCut (φb ω)))) =
      cap ω * paperEN0 D L A S
        (reservedCut.diagonalLaw (push (prodWeight mb) (prodPlace reservedCut (φb ω)))) := by
    intro ω _
    rw [← mul_sum, paperEN0_expand D L A S (D.GB.N₀ L) (fun _ => 0) hsplit]
  rw [sum_congr rfl fun ω hω => by rw [hexp ω hω]]
  have hb := heval_uniform 𝒞 wt cap CX
    (fun ω => paperEN0 D L A S
      (reservedCut.diagonalLaw (push (prodWeight mb) (prodPlace reservedCut (φb ω)))))
    (fun ω => ∑ f : BlockAtom Bk J L → Bool, r0X D εE L A ω f) hwt hcap0 hcapM
    (fun ω _ => mul_nonneg (prod_selectionFactor_nonneg D L _) hY) (hεE L) hz
    (fun ω hω => paperEN0_diag_le D εE L A S ω (hS ω hω) O mb (φb ω) (hD ω hω)
      (mul_nonneg (mul_nonneg (by linarith [hεE L]) (prod_selectionFactor_nonneg D L _)) hY))
  exact hb

end Sarkozy.OpsSteps
