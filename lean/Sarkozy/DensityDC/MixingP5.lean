module

public import Sarkozy.DensityDC.Restoration

/-!
# (R4) only above `P₅`: `prop:record:density-structured` for WP-FI's reference

WP-FI's `Sarkozy.TheoremC.Reference.mixing` gives `γ`-mixing of the tail laws `μ_q` only
for primes `q ≥ P₅` (the part of (R4) that concerns `μ`). `density_structured_dc_tailPrimes`
(`Sarkozy/DensityDC/Restoration.lean`) took every tail prime as a mixing atom. Here the
mixing atoms are the tail primes `q ≥ P₅` (`tailAbove`). The non-mixing atoms are then the
prefix coordinates and the tail primes `P₄ ≤ q < P₅`, so the prefix conductor becomes
`C' = ∏_i m₀ i · ∏_{P₄ ≤ q < P₅ prime} q` (`primeConductorP5`). This is a constant,
independent of the scale `L`, playing the role of the paper's
`Q_pre = Q_cl ∏_{Q₃ ≤ p < P₅} p` (06:155), a common multiple of the orders of all atoms
below `P₅`.

* `prod_order_dvd_primeConductorP5`: every character's order on the non-mixing atoms
  divides `C'` (the hypothesis `hdiv` of `density_structured_dc_paper`).
* `density_structured_dc_P5`: `density_structured_dc_paper` for `T = tailPrimes P₄`, with
  (R4) assumed exactly in WP-FI's form `∀ q prime, P₅ ≤ q → ∀ v, IsGammaMixing q γ (μ_q) {v}`.
  `hrest` and `hun` are discharged as before, and the models `g̃` are constructed in the
  proof.
-/

@[expose] public section

open Finset
open scoped BigOperators

namespace Sarkozy.DensityDC

open Sarkozy.Structured Sarkozy.Functional Sarkozy.FourierArithmetic Sarkozy.Mixing
  Sarkozy.PaperFrame Sarkozy.Comparison

/-- The mixing tail atoms at the scale `L`: the tail primes `q ≥ P₅`. -/
def tailAbove {J₀ : Type} (P4 P5 L : ℕ) : Finset (J₀ ⊕ ↥(tailPrimes P4 L)) :=
  (univ.filter (fun j : ↥(tailPrimes P4 L) => P5 ≤ (j : ℕ))).map
    ⟨Sum.inr, Sum.inr_injective⟩

theorem inl_not_mem_tailAbove {J₀ : Type} (P4 P5 L : ℕ) (i : J₀) :
    (Sum.inl i : J₀ ⊕ ↥(tailPrimes P4 L)) ∉ tailAbove P4 P5 L := by
  simp [tailAbove]

theorem inr_mem_tailAbove {J₀ : Type} (P4 P5 L : ℕ) (j : ↥(tailPrimes P4 L)) :
    (Sum.inr j : J₀ ⊕ ↥(tailPrimes P4 L)) ∈ tailAbove P4 P5 L ↔ P5 ≤ (j : ℕ) := by
  simp [tailAbove]

/-- The prefix conductor `C' = ∏_i m₀ i · ∏_{P₄ ≤ q < P₅ prime} q` of the non-mixing atoms. -/
def primeConductorP5 {J₀ : Type} [Fintype J₀] (m₀ : J₀ → ℕ) (P4 P5 : ℕ) : ℕ :=
  (∏ i, m₀ i) * ∏ q ∈ (range P5).filter (fun q => q.Prime ∧ P4 ≤ q), q

theorem primeConductorP5_pos {J₀ : Type} [Fintype J₀] (m₀ : J₀ → ℕ) [∀ i, NeZero (m₀ i)]
    (P4 P5 : ℕ) : 0 < primeConductorP5 m₀ P4 P5 := by
  unfold primeConductorP5
  refine Nat.mul_pos (Finset.prod_pos fun i _ => Nat.pos_of_ne_zero (NeZero.ne (m₀ i)))
    (Finset.prod_pos fun q hq => ?_)
  exact ((mem_filter.mp hq).2.1).pos

/-- The additive order of a residue divides the modulus. -/
theorem addOrderOf_dvd_mod {n : ℕ} [NeZero n] (x : ZMod n) : addOrderOf x ∣ n := by
  have h := addOrderOf_dvd_card (x := x)
  rwa [ZMod.card] at h

/-- **The prefix conductor divides the orders on the non-mixing atoms** (`hdiv` of
`density_structured_dc_paper` with `Tm = tailAbove`). -/
theorem prod_order_dvd_primeConductorP5 {J₀ : Type} [Fintype J₀] [DecidableEq J₀]
    (m₀ : J₀ → ℕ) [∀ i, NeZero (m₀ i)] (P4 P5 L : ℕ)
    (a : ResidueSpace (joinModuli m₀ (tailModuli (tailPrimes P4) L))) :
    (∏ j ∈ univ.filter (· ∉ tailAbove P4 P5 L), addOrderOf (a j)) ∣
      primeConductorP5 m₀ P4 P5 := by
  unfold primeConductorP5
  rw [Finset.prod_filter, Fintype.prod_sum_type]
  apply mul_dvd_mul
  · rw [prod_congr rfl fun i _ => ite_eq_left (inl_not_mem_tailAbove P4 P5 L i)]
    exact Finset.prod_dvd_prod_of_dvd _ _ fun i _ => addOrderOf_dvd_mod (a (Sum.inl i))
  · simp only [inr_mem_tailAbove, not_le]
    calc ∏ j : ↥(tailPrimes P4 L), (if (j : ℕ) < P5 then addOrderOf (a (Sum.inr j)) else 1) ∣
        ∏ j : ↥(tailPrimes P4 L), (if (j : ℕ) < P5 then (j : ℕ) else 1) := by
          apply Finset.prod_dvd_prod_of_dvd
          intro j _
          by_cases hj : (j : ℕ) < P5
          · rw [ite_eq_left hj, ite_eq_left hj]
            exact addOrderOf_dvd_mod (a (Sum.inr j))
          · rw [ite_eq_right hj, ite_eq_right hj]
      _ = ∏ j ∈ univ.filter (fun j : ↥(tailPrimes P4 L) => (j : ℕ) < P5), (j : ℕ) := by
          rw [Finset.prod_filter]
      _ = ∏ q ∈ (univ.filter (fun j : ↥(tailPrimes P4 L) => (j : ℕ) < P5)).map
            ⟨Subtype.val, Subtype.val_injective⟩, q := by
          rw [Finset.prod_map]
          rfl
      _ ∣ ∏ q ∈ (range P5).filter (fun q => q.Prime ∧ P4 ≤ q), q := by
          apply Finset.prod_dvd_prod_of_subset
          intro q hq
          simp only [mem_map, mem_filter, mem_univ, true_and, Function.Embedding.coeFn_mk] at hq
          obtain ⟨j, hj, rfl⟩ := hq
          have hmem := mem_tailPrimes.mp j.2
          simp only [mem_filter, mem_range]
          exact ⟨hj, hmem.1, hmem.2.1⟩

/-- **`prop:record:density-structured` (first inequality) with (R4) in WP-FI's form**:
`density_structured_dc_tailPrimes` with the mixing atoms the tail primes `q ≥ P₅`
(`tailAbove`). (R4) is assumed for the laws `μ_q` of the primes `q ≥ P₅`, as in
`Sarkozy.TheoremC.Reference.mixing`. The prefix conductor is `C' = primeConductorP5`. -/
theorem density_structured_dc_P5 (ε : ℝ) (hε : 0 < ε) :
    ∃ C1 C71 : ℝ, 0 < C1 ∧ 0 < C71 ∧
    ∀ {J₀ : Type} [Fintype J₀] [DecidableEq J₀] (m₀ : J₀ → ℕ) [∀ i, NeZero (m₀ i)]
      (P4 P5 : ℕ) {Ω : Type} [Fintype Ω]
      (μ0 : ∀ i, FiniteLaw (Slot → ZMod (m₀ i)))
      (μp : ∀ (q : ℕ) [NeZero q], FiniteLaw (Slot → ZMod q))
      {a θ C0 : ℝ} {L : ℕ} {A : Finset ℤ},
      ∀ (_hpair : Pairwise fun i j =>
          (joinModuli m₀ (tailModuli (tailPrimes P4) L) i).Coprime
            (joinModuli m₀ (tailModuli (tailPrimes P4) L) j))
      (_hcex : IsLeastCounterexample (paperY m₀ (tailPrimes P4) μ0 μp) a θ C0 L A) (_hθ : 0 < θ)
      (_hθ1 : θ ≤ 1) (_ha : 0 ≤ a) (_hC0 : 0 ≤ C0) (_hL : 2 ≤ L)
      (_hY0 : paperY m₀ (tailPrimes P4) μ0 μp L ∅ ≤ 0)
      {M0 Qcl Qpre N0 N0' : ℕ} (_hsc : ScaleConditionsAt blockScale M0 Qcl Qpre N0 N0' L)
      (_hM0 : 1 ≤ M0)
      (_hp0 : ∀ i, SlotReflectionPositive (signedIntegral (μ0 i).weight))
      (_hpp : ∀ (q : ℕ) [NeZero q], q.Prime →
        SlotReflectionPositive (signedIntegral (μp q).weight))
      (_hR30 : ∀ i (r t : ZMod (m₀ i)), IsUnit r → IsSquare r →
        ∀ F : (Slot → ZMod (m₀ i)) → ℝ,
          (μ0 i).expect (fun w => F (fun v => r * w v + t)) = (μ0 i).expect F)
      (_hR3p : ∀ (q : ℕ) [NeZero q] (r t : ZMod q), IsUnit r → IsSquare r →
        ∀ F : (Slot → ZMod q) → ℝ,
          (μp q).expect (fun w => F (fun v => r * w v + t)) = (μp q).expect F)
      {γ : ℝ} (_hγ : 0 ≤ γ)
      (_hmixp : ∀ (q : ℕ) [NeZero q], q.Prime → P5 ≤ q → ∀ v : Slot,
        IsGammaMixing q γ (μp q) {v})
      (E : Finset (J₀ ⊕ ↥(tailPrimes P4 L))) {qE cE : ℕ}
      (_hDE : ∏ j ∈ E, joinModuli m₀ (tailModuli (tailPrimes P4) L) j = qE * cE)
      (_hqE : Squarefree qE)
      (_hcE : IsSquare cE) (_hcE0 : cE ≠ 0) (_hcQ : cE ≤ Qcl) (_hcopE : qE.Coprime cE)
      (_hqN : (qE : ℝ) ≤ ((blockScale * L : ℕ) : ℝ) ^ stageTau)
      (P : FiniteLaw Ω)
      (ρ : (Slot → ResidueSpace (joinModuli m₀ (tailModuli (tailPrimes P4) L))) → ℝ)
      (_hunif : selectedMarginalsUniform ρ)
      (D0 : Slot → ℕ) (_hD0 : ∀ v, 1 ≤ D0 v) (_hD0M : ∀ v, D0 v ∣ M0)
      (_hcop0 : ∀ v k, (D0 v).Coprime (joinModuli m₀ (tailModuli (tailPrimes P4) L) k))
      (M : Slot → ℕ) (_hM : ∀ v, M v = blockScale * L ∨ M v = L)
      (c : Ω → Slot → ℤ) (s : ∀ (_ : Ω) (v : Slot), ZMod (D0 v))
      (changed : Slot → Prop) [DecidablePred changed]
      (_hchg : ∀ v, changed v →
        ¬(D0 v * ∏ j ∈ E, joinModuli m₀ (tailModuli (tailPrimes P4) L) j = 1 ∧
          M v = blockScale * L))
      (_hunch : ∀ v, ¬changed v → E = ∅ ∧ D0 v = 1 ∧ M v = blockScale * L ∧ ∀ ω, c ω v = 0)
      {σ : ℝ} (_hσ : 0 ≤ σ) (_hS1 : ε / 20 - γ / 40 ≤ -σ),
      |structuredEnergy (FiniteLaw.tensor (atomLaws m₀ (tailPrimes P4) μ0 μp L)) P ρ
          (paperInputs (joinModuli m₀ (tailModuli (tailPrimes P4) L)) E
            (paperCutoff (blockScale * L)) A D0 M
            c s)| ≤
        totalVariation ρ * ((1 + scaleU blockScale M0 Qcl stageTau L) *
          mainPrice (paperPrice (joinModuli m₀ (tailModuli (tailPrimes P4) L)) E D0 M L)
            (paperMeanDensity P A D0 M c s) changed a θ (density (blockScale * L) A) *
            paperY m₀ (tailPrimes P4) μ0 μp L A +
          (72 * ((primeConductorP5 m₀ P4 P5 : ℕ) : ℝ) ^ γ *
            (2 * (M0 : ℝ) ^ 2 * (Fintype.card (ResidueSpace m₀) : ℝ) ^ 2 * C1 * blockScale +
              4 * (Fintype.card (ResidueSpace m₀) : ℝ) ^ 2 * C1 * M0 * blockScale) ^
                ((1 : ℝ) / 2) *
            ((M0 : ℝ) ^ 142 * (Fintype.card (ResidueSpace m₀) : ℝ) ^ 142 * C71 * blockScale +
              2 ^ 141 * (Fintype.card (ResidueSpace m₀) : ℝ) ^ 142 * C71 * M0 * blockScale) ^
                ((71 : ℝ) / 142)) * (L : ℝ) ^ (-σ) * density (blockScale * L) A) := by
  obtain ⟨C1, C71, hC1, hC71, h⟩ := density_structured_dc_paper ε hε
  refine ⟨C1, C71, hC1, hC71, ?_⟩
  intro J₀ _ _ m₀ _ P4 P5 Ω _ μ0 μp a θ C0 L A hpair hcex hθ hθ1 ha hC0 hL hY0 M0 Qcl Qpre N0 N0'
    hsc hM0 hp0 hpp hR30 hR3p γ hγ hmixp E qE cE hDE hqE hcE hcE0 hcQ hcopE hqN P ρ hunif D0 hD0
    hD0M hcop0 M hM c s changed _ hchg hunch σ hσ hS1
  obtain ⟨hmono, hprime, hlarge⟩ := tailPrimes_hyps P4 L
  set Tm : Finset (J₀ ⊕ ↥(tailPrimes P4 L)) := tailAbove P4 P5 L with hTm
  have hprimeT : ∀ j ∈ Tm, (joinModuli m₀ (tailModuli (tailPrimes P4) L) j).Prime := by
    intro j hj
    rcases j with i | j
    · exact absurd hj (inl_not_mem_tailAbove P4 P5 L i)
    · exact hprime j j.2
  have hmix : ∀ j ∈ Tm, ∀ v, IsGammaMixing (joinModuli m₀ (tailModuli (tailPrimes P4) L) j) γ
      (atomLaws m₀ (tailPrimes P4) μ0 μp L j) {v} := by
    intro j hj v
    rcases j with i | j
    · exact absurd hj (inl_not_mem_tailAbove P4 P5 L i)
    · exact hmixp (j : ℕ) (hprime j j.2) ((inr_mem_tailAbove P4 P5 L j).mp hj) v
  have hC' : 0 < primeConductorP5 m₀ P4 P5 := primeConductorP5_pos m₀ P4 P5
  have hdiv := prod_order_dvd_primeConductorP5 m₀ P4 P5 L
  -- the square-step models `g̃` at the changed slots, the inputs at the others
  set gt : Ω → Slot → ResidueSpace (joinModuli m₀ (tailModuli (tailPrimes P4) L)) →
      ResidueSpace (joinModuli m₀ (tailModuli (tailPrimes P4) L)) → ℝ := fun ω v x =>
    if changed v then fun y =>
      (squareStepModel (joinModuli m₀ (tailModuli (tailPrimes P4) L)) E x (s ω v) A
        (Icc (c ω v + 1) (c ω v + M v)) (c ω v) (M v)
        (stepR (joinModuli m₀ (tailModuli (tailPrimes P4) L)) E (D0 v))
        (blockScale * stepEll (joinModuli m₀ (tailModuli (tailPrimes P4) L)) E (D0 v) (M v))
        (paperCutoff (blockScale *
          stepEll (joinModuli m₀ (tailModuli (tailPrimes P4) L)) E (D0 v) (M v)))
        y).re
    else paperInputs (joinModuli m₀ (tailModuli (tailPrimes P4) L)) E
      (paperCutoff (blockScale * L)) A D0 M c s ω v x with hgtdef
  have hgt : ∀ ω v x, changed v → gt ω v x = fun y =>
      (squareStepModel (joinModuli m₀ (tailModuli (tailPrimes P4) L)) E x (s ω v) A
        (Icc (c ω v + 1) (c ω v + M v)) (c ω v) (M v)
        (stepR (joinModuli m₀ (tailModuli (tailPrimes P4) L)) E (D0 v))
        (blockScale * stepEll (joinModuli m₀ (tailModuli (tailPrimes P4) L)) E (D0 v) (M v))
        (paperCutoff (blockScale *
          stepEll (joinModuli m₀ (tailModuli (tailPrimes P4) L)) E (D0 v) (M v)))
        y).re := by
    intro ω v x hv
    rw [hgtdef]
    exact ite_eq_left hv
  have hgu : ∀ v, ¬changed v → ∀ ω x,
      gt ω v x = paperInputs (joinModuli m₀ (tailModuli (tailPrimes P4) L)) E
        (paperCutoff (blockScale * L)) A D0 M c s ω v x := by
    intro v hv ω x
    rw [hgtdef]
    exact ite_eq_right hv
  exact h m₀ (tailPrimes P4) μ0 μp hmono hprime hlarge hpair hcex hθ hθ1 ha hC0 hL hY0 hsc hM0
    hp0 hpp hR30 hR3p Tm hprimeT hγ hmix hC' hdiv E hDE hqE hcE hcE0 hcQ hcopE hqN P ρ hunif D0
    hD0 hD0M hcop0 M hM c s changed hchg gt hgt hgu hunch hσ hS1

end Sarkozy.DensityDC
