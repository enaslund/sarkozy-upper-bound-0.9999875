module

public import Sarkozy.DensityDC.Groups

/-!
# The scale facts used by `lem:record:density-dc`

`density_structured_groups` assumes the following inequalities about the cutoffs and the
square step, at the paper's cutoff `Q = N^{1/20}` and with `H = N^{1/40}`:
* `2⌊Q⌋ ≤ M_v + 1` and `⌊Q⌋^5 ≤ M_v + 1`;
* `λ_v ≤ 2`;
* `n_v^{1/20} ≤ N^{1/20}`;
* `N^{1/40} ≤ n_v^{1/20}`;
* `N^{1/40} D_E ≤ Q`.

All of them are consequences of `lem:scale-conditions` at the scale `L`
(`Sarkozy.Functional.ScaleConditionsAt`, WP-FI). This file derives them:
* `cutoff_conditions_of_scale`: the cutoff conditions, from condition (i)
  `L ≥ 10 N^{6β}`;
* `step_facts_of_scale`: `λ_v ≤ 2`, `n_v ≤ N`, `H ≤ n_v^β` and `H D_E ≤ Q`, from
  `ScaleConditionsAt.consequences`.
-/

@[expose] public section

open Finset Complex
open scoped BigOperators ComplexConjugate

namespace Sarkozy.DensityDC

open Sarkozy.Structured Sarkozy.Functional Sarkozy.FourierArithmetic Sarkozy.Mixing

/-- **The cutoff conditions** of the moment bounds at `Q = N^{1/20}`: from
`lem:scale-conditions`(i), `L ≥ 10 N^{6β}`, every `M ≥ L` has `2⌊Q⌋ ≤ M + 1` and
`⌊Q⌋^5 ≤ M + 1`. -/
theorem cutoff_conditions_of_scale {K M0 Qcl Qpre N0 N0' L : ℕ}
    (hsc : ScaleConditionsAt K M0 Qcl Qpre N0 N0' L) (hKL : 1 ≤ K * L) {M : ℕ} (hLM : L ≤ M) :
    2 * ⌊paperCutoff (K * L)⌋₊ ≤ M + 1 ∧ ⌊paperCutoff (K * L)⌋₊ ^ 5 ≤ M + 1 := by
  set N : ℝ := ((K * L : ℕ) : ℝ) with hN
  have hN1 : (1 : ℝ) ≤ N := by rw [hN]; exact_mod_cast hKL
  have hN0 : 0 ≤ N := zero_le_one.trans hN1
  have hi := hsc.cond_i
  rw [show 6 * stageBeta = (3 : ℝ) / 10 by norm_num [stageBeta]] at hi
  have hQ0 : 0 ≤ paperCutoff (K * L) := by
    unfold paperCutoff; exact Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hfl : (⌊paperCutoff (K * L)⌋₊ : ℝ) ≤ N ^ ((1 : ℝ) / 20) := by
    have := Nat.floor_le hQ0
    unfold paperCutoff liftExponent at this
    exact this
  have hfl0 : (0 : ℝ) ≤ ⌊paperCutoff (K * L)⌋₊ := Nat.cast_nonneg _
  have hM : (L : ℝ) ≤ M := by exact_mod_cast hLM
  have h310 : (1 : ℝ) ≤ N ^ ((3 : ℝ) / 10) := Real.one_le_rpow hN1 (by norm_num)
  constructor
  · have h1 : (N ^ ((1 : ℝ) / 20)) ≤ N ^ ((3 : ℝ) / 10) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
    have : (2 * ⌊paperCutoff (K * L)⌋₊ : ℝ) ≤ M + 1 := by nlinarith
    exact_mod_cast this
  · have h5 : (⌊paperCutoff (K * L)⌋₊ : ℝ) ^ 5 ≤ (N ^ ((1 : ℝ) / 20)) ^ 5 :=
      pow_le_pow_left₀ hfl0 hfl 5
    have h5' : (N ^ ((1 : ℝ) / 20)) ^ 5 = N ^ ((1 : ℝ) / 4) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hN0]
      norm_num
    have h14 : N ^ ((1 : ℝ) / 4) ≤ N ^ ((3 : ℝ) / 10) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
    have : ((⌊paperCutoff (K * L)⌋₊ ^ 5 : ℕ) : ℝ) ≤ M + 1 := by
      push_cast
      nlinarith
    exact_mod_cast this

/-- **The square-step facts** from `lem:scale-conditions` (`ScaleConditionsAt.consequences`):
at a slot with `D₀ ∣ M₀` and `M ∈ {N, L}`, for a selection with `D_E = q_E c_E` as in
`def:record:structured-energy`(a), `λ ≤ 2`, `n ≤ N`, `N^{1/40} ≤ n^{1/20}` and
`N^{1/40} D_E ≤ N^{1/20}`. -/
theorem step_facts_of_scale {J : Type*} (m : J → ℕ) (E : Finset J)
    {qE cE Qcl M0 Qpre N0 N0' L : ℕ} (hsc : ScaleConditionsAt blockScale M0 Qcl Qpre N0 N0' L)
    (hL : 1 ≤ L) (hM0 : 1 ≤ M0) (hDE : ∏ j ∈ E, m j = qE * cE) (hqE : Squarefree qE)
    (hcE : IsSquare cE) (hcE0 : cE ≠ 0) (hcQ : cE ≤ Qcl) (hcopE : qE.Coprime cE)
    (hqN : (qE : ℝ) ≤ ((blockScale * L : ℕ) : ℝ) ^ stageTau) {D0 M : ℕ} (hD0 : D0 ∣ M0)
    (hcop0 : ∀ k, D0.Coprime (m k)) (hM : M = blockScale * L ∨ M = L) :
    (((leastSquare (D0 * ∏ j ∈ E, m j) *
        (blockScale * stepScale blockScale M (leastSquare (D0 * ∏ j ∈ E, m j))) : ℕ) : ℝ) / M) ≤
        2 ∧
      blockScale * stepEll m E D0 M ≤ blockScale * L ∧
      ((blockScale * L : ℕ) : ℝ) ^ ((1 : ℝ) / 40) ≤
        paperCutoff (blockScale * stepEll m E D0 M) ∧
      ((blockScale * L : ℕ) : ℝ) ^ ((1 : ℝ) / 40) * (∏ j ∈ E, m j : ℕ) ≤
        paperCutoff (blockScale * L) := by
  have hcop : D0.Coprime (qE * cE) := by
    rw [← hDE]
    exact Nat.Coprime.prod_right fun k _ => hcop0 k
  have h := hsc.consequences (by norm_num [blockScale]) hL hM hD0 hM0 hqE hcE hcE0 hcQ hcop
    hcopE hqN
  dsimp only at h
  obtain ⟨_, hHQ, ⟨_, hnN⟩, hHn, _, ⟨_, hlam2⟩, _⟩ := h
  have hb : stageBeta / 2 = (1 : ℝ) / 40 := by norm_num [stageBeta]
  have hb' : stageBeta = liftExponent := by norm_num [stageBeta, liftExponent]
  rw [hb, hb'] at hHQ hHn
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← hDE] at hlam2
    push_cast at hlam2 ⊢
    exact hlam2
  · unfold stepEll stepR
    rw [hDE]
    exact hnN
  · unfold paperCutoff stepEll stepR
    rw [hDE]
    exact hHn
  · unfold paperCutoff
    rw [hDE]
    exact hHQ

/-- **`prop:record:density-structured` (first inequality) on the paper's groups at the
paper's cutoff `Q = N^{1/20}`, with `lem:record:density-dc` proved and the scale facts
derived from `lem:scale-conditions`.** Compared with `density_structured_groups`, the
cutoff conditions, `λ_v ≤ 2`, `n_v ≤ N`, `H ≤ n_v^β` and `H D_E ≤ Q` are derived from
`ScaleConditionsAt` (`cutoff_conditions_of_scale`, `step_facts_of_scale`). -/
theorem density_structured_dc_scale (ε : ℝ) (hε : 0 < ε) :
    ∃ C1 C71 : ℝ, 0 < C1 ∧ 0 < C71 ∧
    ∀ {J₀ J : Type} [Fintype J₀] [DecidableEq J₀] [Fintype J] [DecidableEq J]
      (m₀ : J₀ → ℕ) [∀ i, NeZero (m₀ i)] (p : J → ℕ) [∀ j, NeZero (p j)] {Ω : Type}
      [Fintype Ω],
      (∀ j, (p j).Prime) → Function.Injective p →
      ∀ (_hpair : Pairwise fun i j => (joinModuli m₀ p i).Coprime (joinModuli m₀ p j))
      {Yf : ℕ → Finset ℤ → ℝ} {a θ C0 : ℝ} {L : ℕ} {A : Finset ℤ}
      (_hcex : IsLeastCounterexample Yf a θ C0 L A) (_hθ : 0 < θ) (_hθ1 : θ ≤ 1) (_ha : 0 ≤ a)
      (_hC0 : 0 ≤ C0) (_hL : 2 ≤ L) (_hY0 : Yf L ∅ ≤ 0)
      {M0 Qcl Qpre N0 N0' : ℕ} (_hsc : ScaleConditionsAt blockScale M0 Qcl Qpre N0 N0' L)
      (_hM0 : 1 ≤ M0)
      (μb : ∀ b, FiniteLaw (Slot → ZMod (joinModuli m₀ p b)))
      (_hμb : ∀ b, SlotReflectionPositive (signedIntegral (μb b).weight))
      (_hR3 : SquareAffineInvariant (joinModuli m₀ p) μb)
      (T : Finset (J₀ ⊕ J)) (_hprime : ∀ j ∈ T, (joinModuli m₀ p j).Prime) {γ : ℝ}
      (_hγ : 0 ≤ γ) (_hmix : ∀ j ∈ T, ∀ v, IsGammaMixing (joinModuli m₀ p j) γ (μb j) {v})
      {C' : ℕ} (_hC' : 0 < C')
      (_hdiv : ∀ a : ResidueSpace (joinModuli m₀ p),
        (∏ j ∈ univ.filter (· ∉ T), addOrderOf (a j)) ∣ C')
      (E : Finset (J₀ ⊕ J)) {qE cE : ℕ}
      (_hDE : ∏ j ∈ E, joinModuli m₀ p j = qE * cE) (_hqE : Squarefree qE) (_hcE : IsSquare cE)
      (_hcE0 : cE ≠ 0) (_hcQ : cE ≤ Qcl) (_hcopE : qE.Coprime cE)
      (_hqN : (qE : ℝ) ≤ ((blockScale * L : ℕ) : ℝ) ^ stageTau)
      (P : FiniteLaw Ω) (ρ : (Slot → ResidueSpace (joinModuli m₀ p)) → ℝ)
      (_hunif : selectedMarginalsUniform ρ)
      (D0 : Slot → ℕ) (_hD0 : ∀ v, 1 ≤ D0 v) (_hD0M : ∀ v, D0 v ∣ M0)
      (_hcop0 : ∀ v k, (D0 v).Coprime (joinModuli m₀ p k))
      (M : Slot → ℕ) (_hM : ∀ v, M v = blockScale * L ∨ M v = L)
      (c : Ω → Slot → ℤ) (s : ∀ (_ : Ω) (v : Slot), ZMod (D0 v))
      (changed : Slot → Prop) [DecidablePred changed]
      (_hchg : ∀ v, changed v → ¬(D0 v * ∏ j ∈ E, joinModuli m₀ p j = 1 ∧ M v = blockScale * L))
      (gt : Ω → Slot → ResidueSpace (joinModuli m₀ p) → ResidueSpace (joinModuli m₀ p) → ℝ)
      (_hgt : ∀ ω v x, changed v → gt ω v x = fun y =>
        (squareStepModel (joinModuli m₀ p) E x (s ω v) A (Icc (c ω v + 1) (c ω v + M v))
          (c ω v) (M v) (stepR (joinModuli m₀ p) E (D0 v))
          (blockScale * stepEll (joinModuli m₀ p) E (D0 v) (M v))
          (paperCutoff (blockScale * stepEll (joinModuli m₀ p) E (D0 v) (M v))) y).re)
      (_hgu : ∀ v, ¬changed v → ∀ ω x,
        gt ω v x = paperInputs (joinModuli m₀ p) E (paperCutoff (blockScale * L)) A D0 M c s ω v x)
      (_hun : ∀ v, ¬changed v → ∀ ω x,
        referenceEnergy (FiniteLaw.tensor μb) (gt ω v x) ≤ Yf L A)
      (_hrest : ∀ v, changed v → ∀ B : Finset ℤ,
        B ⊆ Icc 1 ((blockScale * stepEll (joinModuli m₀ p) E (D0 v) (M v) : ℕ) : ℤ) →
        referenceEnergy (FiniteLaw.tensor μb)
            (child (joinModuli m₀ p) E (paperCutoff (blockScale *
              stepEll (joinModuli m₀ p) E (D0 v) (M v))) B
              (blockScale * stepEll (joinModuli m₀ p) E (D0 v) (M v))) ≤
          Yf (stepEll (joinModuli m₀ p) E (D0 v) (M v)) B)
      {σ : ℝ} (_hσ : 0 ≤ σ) (_hS1 : ε / 20 - γ / 40 ≤ -σ),
      |structuredEnergy (FiniteLaw.tensor μb) P ρ
          (paperInputs (joinModuli m₀ p) E (paperCutoff (blockScale * L)) A D0 M c s)| ≤
        totalVariation ρ * ((1 + scaleU blockScale M0 Qcl stageTau L) *
          mainPrice (paperPrice (joinModuli m₀ p) E D0 M L) (paperMeanDensity P A D0 M c s)
            changed a θ (density (blockScale * L) A) * Yf L A +
          (72 * (C' : ℝ) ^ γ *
            (2 * (M0 : ℝ) ^ 2 * (Fintype.card (ResidueSpace m₀) : ℝ) ^ 2 * C1 * blockScale +
              4 * (Fintype.card (ResidueSpace m₀) : ℝ) ^ 2 * C1 * M0 * blockScale) ^
                ((1 : ℝ) / 2) *
            ((M0 : ℝ) ^ 142 * (Fintype.card (ResidueSpace m₀) : ℝ) ^ 142 * C71 * blockScale +
              2 ^ 141 * (Fintype.card (ResidueSpace m₀) : ℝ) ^ 142 * C71 * M0 * blockScale) ^
                ((71 : ℝ) / 142)) * (L : ℝ) ^ (-σ) * density (blockScale * L) A) := by
  obtain ⟨C1, C71, hC1, hC71, h⟩ := density_structured_groups ε hε
  refine ⟨C1, C71, hC1, hC71, ?_⟩
  intro J₀ J _ _ _ _ m₀ _ p _ Ω _ hp hinj hpair Yf a θ C0 L A hcex hθ hθ1 ha hC0 hL hY0 M0 Qcl
    Qpre N0 N0' hsc hM0 μb hμb hR3 T hprime γ hγ hmix C' hC' hdiv E qE cE hDE hqE hcE hcE0 hcQ
    hcopE hqN P ρ hunif D0 hD0 hD0M hcop0 M hM c s changed _ hchg gt hgt hgu hun hrest σ hσ hS1
  have hL1 : 1 ≤ L := by omega
  have hKL : 1 ≤ blockScale * L := Nat.mul_pos (by norm_num [blockScale]) (by omega)
  have hLM : ∀ v, L ≤ M v := by
    intro v
    rcases hM v with h | h
    · rw [h]; exact Nat.le_mul_of_pos_left L (by norm_num [blockScale])
    · rw [h]
  have hfacts := fun v => step_facts_of_scale (joinModuli m₀ p) E hsc hL1 hM0 hDE hqE hcE hcE0
    hcQ hcopE hqN (hD0M v) (hcop0 v) (hM v)
  have hQN : paperCutoff (blockScale * L) ≤ ((blockScale * L : ℕ) : ℝ) ^ ((1 : ℝ) / 20) := by
    unfold paperCutoff liftExponent
    exact le_rfl
  exact h m₀ p hp hinj hpair hcex hθ hθ1 ha hC0 hL hY0 hsc hM0 μb hμb hR3 T hprime hγ hmix hC'
    hdiv E hDE hqE hcE hcE0 hcQ hcopE hqN P ρ hunif D0 hD0 hD0M hcop0 M hM c s changed hchg
    (paperCutoff (blockScale * L)) gt hgt hgu hun hrest (one_le_paperCutoff hKL) hQN
    (fun v => cutoff_conditions_of_scale hsc hKL (hLM v)) (fun v _ => (hfacts v).1)
    (fun v _ => by
      have hn := (hfacts v).2.1
      unfold paperCutoff liftExponent
      exact Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hn) (by norm_num))
    (fun v _ => (hfacts v).2.2.1) (hfacts (0, 0, 0)).2.2.2 hσ hS1

end Sarkozy.DensityDC
