module

public import Sarkozy.Structured.PaperEnergy
public import Sarkozy.Functional.ScaleAtoms
public import Sarkozy.Functional.FibreRestoration

/-!
# Scale conditions and restoration for `prop:record:density-structured`

This file discharges two hypotheses of `density_structured_paper` from WP-FI's results.

* **The scale condition `λ_v^{72} ≤ 1 + u_L`.** `lambda_pow_le_scaleU` derives it, with the
  paper's `u_L` (`Sarkozy.Functional.scaleU`), from conditions (i)–(vii) of
  `lem:scale-conditions` at the scale `L` (`ScaleConditionsAt`, which
  `scaleConditions_assembled` proves for all `L ≥ L_*`). It uses the factorization
  `D_E = q_E c_E` of the selection (`q_E` squarefree, `q_E ≤ N^τ`, `c_E` a perfect
  square, `c_E ≤ Q_cl`) and `D_{0,v} ∣ M₀`. `lambda_pow_le_scaleU_paper` proves the
  factorization for the paper's groups (`Sarkozy/Functional/ScaleAtoms.lean`).
  `density_structured_scale` is `density_structured_paper` with `u = u_L`. Its hypotheses
  are those of `def:record:structured-energy` and `prop:record:density-structured`
  (`L ≥ L_*` becomes `ScaleConditionsAt … L`), together with `hdc`, `hrest`, `hinvT`
  and `hun` (see `Sarkozy/Structured/PaperEnergy.lean`).
* **Restoration `lem:record:fibre-scale`(c).** `restoration_of_two_scales` derives the
  hypothesis `hrest` of `changed_slot_bound_paper` at one changed slot from WP-FI's
  `referenceEnergy_stepLift_le_scale`, when the group at the scale `L` splits as
  `G_N = G_n × X_extra` (`joinModuli m₀ p`). The precise hypotheses are:
  - `hprod`: `μ_N = μ_n ⊗ ν` ((R1) and the product form of the reference law);
  - `hp`: reflection positivity of `μ_N` ((R2));
  - `hinv`: invariance under the translations supported on `E` ((R3), `r_p = 1`);
  - `hlarge`: the extra coordinates have all nonzero orders `> Q'` (tail primes
    `> n^β`);
  - `hY`: `Λ_{μ_n}(F_B) ≤ Y(ℓ, B)` for `B ⊆ [n]`, where `F_B` is the lift
    (`wholeLift`) at the scale `ℓ`. This is the definition of `Y(ℓ, ·)` when `μ_n` is
    the reference law at the scale `ℓ` and `Q' = n^β`.
  `changed_slot_bound_two_scales` is the changed-slot bound with these hypotheses in
  place of `hrest`.

What remains between this and a closed `density_structured_paper` with `hrest`
discharged is the bookkeeping across the slots. The child scale
`ℓ_v = ⌈M_v/(K R_v)⌉` depends on the slot through `D_{0,v}` and `M_v`. So the
splitting `G_N = G_{n_v} × X_extra,v` is a different identification of types for each
changed slot, which neither this package nor WP-FI formalizes.
-/

@[expose] public section

open Finset
open scoped BigOperators

namespace Sarkozy.Structured

open Sarkozy.Functional Sarkozy.FourierArithmetic

/-! ## The scale condition -/

/-- `u_L ≥ 0`. -/
theorem scaleU_nonneg (K M0 Qcl : ℕ) (τ : ℝ) (L : ℕ) : 0 ≤ scaleU K M0 Qcl τ L := by
  unfold scaleU
  have h : 0 ≤ (K : ℝ) ^ 2 * (M0 : ℝ) ^ 2 * (Qcl : ℝ) * ((K * L : ℕ) : ℝ) ^ (2 * τ - 1) := by
    positivity
  have h1 : 1 ≤ (1 + (K : ℝ) ^ 2 * (M0 : ℝ) ^ 2 * (Qcl : ℝ) *
      ((K * L : ℕ) : ℝ) ^ (2 * τ - 1)) ^ 72 := one_le_pow₀ (by linarith)
  linarith

/-- **`λ_v^{72} ≤ 1 + u_L`** (`lem:scale-conditions`, consequences) at a slot with divisor
`D₀ ∣ M₀` and length `M ∈ {N, L}`, for a selection with `D_E = q_E c_E` as in
`def:record:structured-energy`(a): `q_E` squarefree with `q_E ≤ N^τ`, `c_E` a perfect
square with `c_E ≤ Q_cl`. -/
theorem lambda_pow_le_scaleU {J : Type*} (m : J → ℕ) (E : Finset J)
    {qE cE Qcl M0 Qpre N0 N0' L : ℕ} (hsc : ScaleConditionsAt blockScale M0 Qcl Qpre N0 N0' L)
    (hL : 1 ≤ L) (hM0 : 1 ≤ M0) (hDE : ∏ j ∈ E, m j = qE * cE) (hqE : Squarefree qE)
    (hcE : IsSquare cE) (hcE0 : cE ≠ 0) (hcQ : cE ≤ Qcl) (hcopE : qE.Coprime cE)
    (hqN : (qE : ℝ) ≤ ((blockScale * L : ℕ) : ℝ) ^ stageTau) {D0 M : ℕ} (hD0 : D0 ∣ M0)
    (hcop0 : ∀ k, D0.Coprime (m k)) (hM : M = blockScale * L ∨ M = L) :
    (((stepR m E D0 : ℕ) : ℝ) * ((blockScale * stepEll m E D0 M : ℕ) : ℝ) / M) ^ 72 ≤
      1 + scaleU blockScale M0 Qcl stageTau L := by
  have hcop : D0.Coprime (qE * cE) := by
    rw [← hDE]
    exact Nat.Coprime.prod_right fun k _ => hcop0 k
  have h := hsc.consequences (by norm_num [blockScale]) hL hM hD0 hM0 hqE hcE hcE0 hcQ hcop
    hcopE hqN
  dsimp only at h
  have h7 := h.2.2.2.2.2.2
  unfold stepEll stepR
  rw [hDE]
  exact h7

/-- `λ_v^{72} ≤ 1 + u_L` for the paper's groups: a prefix of prime powers `P₀ i ^ e₀ i`
with even exponents and a tail of primes, all distinct, with `Q_cl = ∏_i P₀ i ^ e₀ i`. -/
theorem lambda_pow_le_scaleU_paper {J₀ J' : Type*} [Fintype J₀] {P₀ e₀ : J₀ → ℕ}
    {p : J' → ℕ} (hP : ∀ i, (P₀ i).Prime) (he : ∀ i, Even (e₀ i)) (hp : ∀ j, (p j).Prime)
    (hinj : Function.Injective p) (hdist : ∀ i j, P₀ i ≠ p j) {M0 Qpre N0 N0' L : ℕ}
    (hsc : ScaleConditionsAt blockScale M0 (∏ i, P₀ i ^ e₀ i) Qpre N0 N0' L) (hL : 1 ≤ L)
    (hM0 : 1 ≤ M0) (E : Finset (J₀ ⊕ J'))
    (hqN : (tailPart p E : ℝ) ≤ ((blockScale * L : ℕ) : ℝ) ^ stageTau) {D0 M : ℕ}
    (hD0 : D0 ∣ M0) (hcop0 : ∀ k, D0.Coprime (joinModuli (fun i => P₀ i ^ e₀ i) p k))
    (hM : M = blockScale * L ∨ M = L) :
    (((stepR (joinModuli (fun i => P₀ i ^ e₀ i) p) E D0 : ℕ) : ℝ) *
      ((blockScale * stepEll (joinModuli (fun i => P₀ i ^ e₀ i) p) E D0 M : ℕ) : ℝ) / M) ^ 72 ≤
      1 + scaleU blockScale M0 (∏ i, P₀ i ^ e₀ i) stageTau L :=
  lambda_pow_le_scaleU _ E hsc hL hM0 (prod_joinModuli_eq P₀ e₀ p E)
    (tailPart_squarefree hp hinj E) (cliquePart_isSquare he E) (cliquePart_ne_zero hP E)
    (cliquePart_le hP E) (tailPart_coprime_cliquePart hP hp hdist E) hqN hD0 hcop0 hM

/-! ## `prop:record:density-structured` with the scale conditions -/

section Scale

variable {J : Type*} [Fintype J] [DecidableEq J] (m : J → ℕ) [∀ j, NeZero (m j)]
  {Ω : Type*} [Fintype Ω]

/-- **`prop:record:density-structured` for the paper's inputs, with `u = u_L`.** The
hypothesis `L ≥ L_*` of the paper is `ScaleConditionsAt … L`; the selection has
`D_E = q_E c_E` with `q_E ≤ N^τ` (`def:record:structured-energy`(a)), and every `D_{0,v}`
divides `M₀` ((c)). The remaining hypotheses are as in `density_structured_paper`. -/
theorem density_structured_scale (hpair : Pairwise fun i j => (m i).Coprime (m j))
    {Yf : ℕ → Finset ℤ → ℝ} {a θ C0 : ℝ} {L : ℕ} {A : Finset ℤ}
    (hcex : IsLeastCounterexample Yf a θ C0 L A) (hθ : 0 < θ) (hθ1 : θ ≤ 1) (ha : 0 ≤ a)
    (hC0 : 0 ≤ C0) (hL : 2 ≤ L) (hY0 : Yf L ∅ ≤ 0)
    {M0 Qcl Qpre N0 N0' : ℕ} (hsc : ScaleConditionsAt blockScale M0 Qcl Qpre N0 N0' L)
    (hM0 : 1 ≤ M0)
    (μS : FiniteLaw (Slot → ResidueSpace m))
    (hμS : SlotReflectionPositive (signedIntegral μS.weight)) (E : Finset J) {qE cE : ℕ}
    (hDE : ∏ j ∈ E, m j = qE * cE) (hqE : Squarefree qE) (hcE : IsSquare cE) (hcE0 : cE ≠ 0)
    (hcQ : cE ≤ Qcl) (hcopE : qE.Coprime cE)
    (hqN : (qE : ℝ) ≤ ((blockScale * L : ℕ) : ℝ) ^ stageTau)
    (P : FiniteLaw Ω) (ρ : (Slot → ResidueSpace m) → ℝ) (hunif : selectedMarginalsUniform ρ)
    (D0 : Slot → ℕ) (hD0 : ∀ v, 1 ≤ D0 v) (hD0M : ∀ v, D0 v ∣ M0)
    (hcop0 : ∀ v k, (D0 v).Coprime (m k))
    (M : Slot → ℕ) (hM : ∀ v, M v = blockScale * L ∨ M v = L)
    (c : Ω → Slot → ℤ) (s : ∀ (_ : Ω) (v : Slot), ZMod (D0 v))
    (changed : Slot → Prop) [DecidablePred changed]
    (hchg : ∀ v, changed v → ¬(D0 v * ∏ j ∈ E, m j = 1 ∧ M v = blockScale * L))
    (Q : ℝ) (Q' : Slot → ℝ) (gt : Ω → Slot → ResidueSpace m → ResidueSpace m → ℝ)
    (hgt : ∀ ω v x, changed v → gt ω v x = fun y =>
      (squareStepModel m E x (s ω v) A (Icc (c ω v + 1) (c ω v + M v)) (c ω v) (M v)
        (stepR m E (D0 v)) (blockScale * stepEll m E (D0 v) (M v)) (Q' v) y).re)
    (hun : ∀ v, ¬changed v → ∀ ω x, referenceEnergy μS (gt ω v x) ≤ Yf L A)
    {Cdc σ : ℝ}
    (hrest : ∀ v, changed v → ∀ B : Finset ℤ,
      B ⊆ Icc 1 ((blockScale * stepEll m E (D0 v) (M v) : ℕ) : ℤ) →
      referenceEnergy μS (child m E (Q' v) B (blockScale * stepEll m E (D0 v) (M v))) ≤
        Yf (stepEll m E (D0 v) (M v)) B)
    (hinvT : ∀ v, changed v → ∀ ω (j : ℤ) (F : (Slot → ResidueSpace m) → ℝ),
      μS.expect (fun w => F (fun v' => stepMapOff m E (stepR m E (D0 v)) (c ω v) j (w v'))) =
        μS.expect F)
    (hdc : |structuredEnergy μS P ρ (paperInputs m E Q A D0 M c s) -
        structuredEnergy μS P ρ gt| ≤
      Cdc * totalVariation ρ * (L : ℝ) ^ (-σ) * density (blockScale * L) A) :
    |structuredEnergy μS P ρ (paperInputs m E Q A D0 M c s)| ≤
      totalVariation ρ * ((1 + scaleU blockScale M0 Qcl stageTau L) *
        mainPrice (paperPrice m E D0 M L) (paperMeanDensity P A D0 M c s) changed a θ
          (density (blockScale * L) A) * Yf L A +
        Cdc * (L : ℝ) ^ (-σ) * density (blockScale * L) A) :=
  density_structured_paper m hpair hcex hθ hθ1 ha hC0 hL hY0 μS hμS E P ρ hunif D0 hD0 hcop0 M
    hM c s changed hchg Q Q' gt hgt hun (scaleU_nonneg _ _ _ _ _) hrest hinvT
    (fun v _ => lambda_pow_le_scaleU m E hsc (by omega) hM0 hDE hqE hcE hcE0 hcQ hcopE hqN
      (hD0M v) (hcop0 v) (hM v)) hdc

end Scale

/-! ## Restoration from two scales -/

section Restoration

variable {J₀ J' : Type*} [Fintype J₀] [DecidableEq J₀] [Fintype J'] [DecidableEq J']
  (m₀ : J₀ → ℕ) [∀ i, NeZero (m₀ i)] (p : J' → ℕ) [∀ j, NeZero (p j)]

/-- **`lem:record:fibre-scale`(c) in the form of `hrest`**: when `G_N = G_n × X_extra`, the
energy of every child `h_j` at the scale `L` is at most `Y(ℓ, B)`, given WP-FI's
two-scale hypotheses and `Λ_{μ_n}(F_B) ≤ Y(ℓ, B)`. -/
theorem restoration_of_two_scales (μn : FiniteLaw (Slot → ResidueSpace m₀))
    (ν : FiniteLaw (Slot → ResidueSpace p))
    (μN : FiniteLaw (Slot → ResidueSpace (joinModuli m₀ p)))
    (hprod : ∀ F : (Slot → ResidueSpace (joinModuli m₀ p)) → ℝ, μN.expect F =
      (μn.product ν).expect (fun w => F (fun v => (splitEquiv m₀ p).symm (w.1 v, w.2 v))))
    (hp : SlotReflectionPositive (signedIntegral μN.weight)) (E : Finset (J₀ ⊕ J'))
    (hinv : ∀ s : ResidueSpace (joinModuli m₀ p), (∀ k ∉ E, s k = 0) →
      ∀ F : (Slot → ResidueSpace (joinModuli m₀ p)) → ℝ,
        μN.expect (fun z => F (fun v => z v + s)) = μN.expect F)
    {Q' : ℝ} (hlarge : ∀ k (x : ZMod (p k)), x ≠ 0 → Q' < addOrderOf x)
    (Yf : ℕ → Finset ℤ → ℝ) (n ℓ : ℕ)
    (hY : ∀ B : Finset ℤ, B ⊆ Icc 1 (n : ℤ) →
      referenceEnergy μn (fun x => (wholeLift m₀ Q' n B x).re) ≤ Yf ℓ B) :
    ∀ B : Finset ℤ, B ⊆ Icc 1 (n : ℤ) →
      referenceEnergy μN (child (joinModuli m₀ p) E Q' B n) ≤ Yf ℓ B :=
  fun B hB =>
    (referenceEnergy_stepLift_le_scale m₀ p μn ν μN hprod hp E hinv hlarge B n).trans (hY B hB)

/-- **The changed-slot bound with restoration from two scales**: `changed_slot_bound_paper`
for `G_N = G_n × X_extra`, with `hrest` replaced by the hypotheses of
`restoration_of_two_scales` at `n = Kℓ`, `ℓ = ⌈M/(KR)⌉`. -/
theorem changed_slot_bound_two_scales (μn : FiniteLaw (Slot → ResidueSpace m₀))
    (ν : FiniteLaw (Slot → ResidueSpace p))
    (μN : FiniteLaw (Slot → ResidueSpace (joinModuli m₀ p)))
    (hprod : ∀ F : (Slot → ResidueSpace (joinModuli m₀ p)) → ℝ, μN.expect F =
      (μn.product ν).expect (fun w => F (fun v => (splitEquiv m₀ p).symm (w.1 v, w.2 v))))
    (hp : SlotReflectionPositive (signedIntegral μN.weight)) (E : Finset (J₀ ⊕ J'))
    (hinv : ∀ s : ResidueSpace (joinModuli m₀ p), (∀ k ∉ E, s k = 0) →
      ∀ F : (Slot → ResidueSpace (joinModuli m₀ p)) → ℝ,
        μN.expect (fun z => F (fun v => z v + s)) = μN.expect F)
    {Q' : ℝ} (hlarge : ∀ k (x : ZMod (p k)), x ≠ 0 → Q' < addOrderOf x)
    (z : ResidueSpace (joinModuli m₀ p)) {D0 : ℕ} (hD0 : 1 ≤ D0) (s : ZMod D0)
    (hcop0 : ∀ k, D0.Coprime (joinModuli m₀ p k))
    (hpair : Pairwise fun i j => (joinModuli m₀ p i).Coprime (joinModuli m₀ p j))
    (A : Finset ℤ) (hA : IsSquareDifferenceFree A) (c : ℤ) {M L : ℕ} (hM : 1 ≤ M) (hL : 2 ≤ L)
    (hML : M = blockScale * L ∨ M = L)
    (hchg : ¬(D0 * ∏ j ∈ E, joinModuli m₀ p j = 1 ∧ M = blockScale * L))
    {Yf : ℕ → Finset ℤ → ℝ} {a θ C0 u : ℝ} (ha : 0 ≤ a) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 72)
    (hC0 : 0 ≤ C0) (hsmall : ∀ ℓ : ℕ, 1 ≤ ℓ → ℓ < L → ScaleBound Yf a θ C0 ℓ)
    (hY : ∀ B : Finset ℤ,
      B ⊆ Icc 1 ((blockScale * stepEll (joinModuli m₀ p) E D0 M : ℕ) : ℤ) →
      referenceEnergy μn (fun x => (wholeLift m₀ Q' (blockScale * stepEll (joinModuli m₀ p) E D0 M)
        B x).re) ≤ Yf (stepEll (joinModuli m₀ p) E D0 M) B)
    (hinvT : ∀ j : ℤ, ∀ F : (Slot → ResidueSpace (joinModuli m₀ p)) → ℝ,
      μN.expect (fun w => F (fun v => stepMapOff (joinModuli m₀ p) E
        (stepR (joinModuli m₀ p) E D0) c j (w v))) = μN.expect F)
    (hlamu : (((stepR (joinModuli m₀ p) E D0 : ℕ) : ℝ) *
      ((blockScale * stepEll (joinModuli m₀ p) E D0 M : ℕ) : ℝ) / M) ^ 72 ≤ 1 + u) :
    referenceEnergy μN (fun y => (squareStepModel (joinModuli m₀ p) E z s A (Icc (c + 1) (c + M))
        c M (stepR (joinModuli m₀ p) E D0) (blockScale * stepEll (joinModuli m₀ p) E D0 M) Q'
        y).re) ≤
      (1 + u) * C0 * (L : ℝ) ^ (-a) *
        ((((blockScale * L : ℕ) : ℝ) / M) * (stepR (joinModuli m₀ p) E D0 : ℕ)) ^ a *
        fibreDensity (joinModuli m₀ p) E z s A c M ^ θ :=
  changed_slot_bound_paper (joinModuli m₀ p) μN hp E z hD0 s hcop0 hpair A hA c hM hL hML hchg
    Q' ha hθ0 hθ1 hC0 hsmall
    (restoration_of_two_scales m₀ p μn ν μN hprod hp E hinv hlarge Yf _ _ hY) hinvT hlamu

end Restoration

end Sarkozy.Structured
