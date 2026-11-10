module

public import Sarkozy.DensityDC.ScaleFacts
public import Sarkozy.PaperFrame.RestorationPaper
public import Sarkozy.PaperFrame.TailFamily

/-!
# Restoration on the paper's groups: the hypothesis `hrest` (`lem:record:fibre-scale`(c))

`density_structured_dc_scale` (`Sarkozy/DensityDC/ScaleFacts.lean`) keeps the restoration
`lem:record:fibre-scale`(c) at the child scales `ℓ_v` as the hypothesis `hrest`:
`Z_{μ_N}(h) ≤ Y(ℓ_v, B)` for the children `h` of each changed slot `v`. This file proves
`hrest` for the paper's reference law and the paper's functional `Y`, slot by slot, from
WP-FI's `fibreScale_restoration_paper` (`Sarkozy/PaperFrame/RestorationPaper.lean`).

The model is the one of `Sarkozy/PaperFrame` and `Sarkozy/Comparison/PaperMain.lean`:
* the group at the scale `L` is `G_N = ∏_{J₀} ZMod m₀ × ∏_{q ∈ T L} ZMod q`
  (`joinModuli m₀ (tailModuli T L)`), with prefix moduli `m₀` and the tail primes `T L`;
* the atom laws do not depend on the scale ((R1)): one law `μ0 i` per prefix coordinate
  and one law `μp q` per prime (`atomLaws`);
* `μ_N = ⊗_b μ_b` (`FiniteLaw.tensor (atomLaws …)`), the law of `density_structured_dc_scale`;
* `Y(ℓ, B) = prefixedFunctional … ℓ B`, the paper's functional for
  `paperLaw = μ₀ ⊗ ⊗_q μ_q` with `μ₀ = ⊗_i μ0_i`.

So the prefix coordinates are separate atoms, as in `density_structured_dc_scale`.

* `tensor_atomLaws_expect`: `⊗_b μ_b` is `paperLaw` transported along `splitEquiv`.
* `restoration_atomLaws`: `Z_{μ_N}(h) ≤ Y(ℓ, B)` for one child scale `ℓ` with
  `T ℓ ⊆ T L` whose missing primes exceed `(Kℓ)^β`.
* `hrest_atomLaws`: the hypothesis `hrest` of `density_structured_dc_scale`, for every
  changed slot. The child scales satisfy `ℓ_v ≤ L` (`step_facts_of_scale`), and the
  tail family is monotone, with the primes added between `ℓ_v` and `L` above `(Kℓ_v)^β`.
  For the paper's tail family `tailPrimes P₄` these are `tailPrimes_mono` and
  `tailPrimes_large`.
* `hun_atomLaws`: the hypothesis `hun` (the unchanged slots, where the input is `F_A`).
* `density_structured_dc_paper`: `density_structured_dc_scale` on these groups, with
  `hrest` and `hun` discharged.
* `density_structured_dc_tailPrimes`: the same for the paper's tail family
  `T = tailPrimes P₄`. The mixing atoms are the tail primes, with (R4) stated for their laws,
  and the prefix conductor is `C' = ∏_i m₀ i`. The models `g̃` are constructed in the proof.
-/

@[expose] public section

open Finset
open scoped BigOperators

namespace Sarkozy.DensityDC

open Sarkozy.Structured Sarkozy.Functional Sarkozy.FourierArithmetic Sarkozy.Mixing
  Sarkozy.PaperFrame Sarkozy.Comparison

section Atoms

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] (m₀ : J₀ → ℕ) [∀ i, NeZero (m₀ i)]
  (T : ℕ → Finset ℕ) [∀ L (j : ↥(T L)), NeZero (j : ℕ)]

/-- The atom laws at the scale `L`: the law `μ0 i` of each prefix coordinate and the law
`μp q` of each tail prime `q ∈ T L` ((R1): they do not depend on `L`). -/
noncomputable def atomLaws (μ0 : ∀ i, FiniteLaw (Slot → ZMod (m₀ i)))
    (μp : ∀ (q : ℕ) [NeZero q], FiniteLaw (Slot → ZMod q)) (L : ℕ) :
    ∀ b : J₀ ⊕ ↥(T L), FiniteLaw (Slot → ZMod (joinModuli m₀ (tailModuli T L) b))
  | Sum.inl i => μ0 i
  | Sum.inr j => μp (j : ℕ)

/-- **The reference law as a tensor of the atom laws**: `⊗_b μ_b` is the paper's
`paperLaw = μ₀ ⊗ ⊗_{q ∈ T L} μ_q` with `μ₀ = ⊗_i μ0_i`, transported along `splitEquiv`. -/
theorem tensor_atomLaws_expect (μ0 : ∀ i, FiniteLaw (Slot → ZMod (m₀ i)))
    (μp : ∀ (q : ℕ) [NeZero q], FiniteLaw (Slot → ZMod q)) (L : ℕ)
    (F : (Slot → ResidueSpace (joinModuli m₀ (tailModuli T L))) → ℝ) :
    (FiniteLaw.tensor (atomLaws m₀ T μ0 μp L)).expect F =
      (paperLaw m₀ (J := fun L => ↥(T L)) (fun _ j => (j : ℕ)) (FiniteLaw.tensor μ0) μp L).expect
        (fun w => F (fun v => (splitEquiv m₀ (tailModuli T L)).symm (w v))) := by
  unfold paperLaw primeTailLaw
  rw [FiniteLaw.expect_slotProduct, tensor_expect_sum, tensor_expect_sum]
  simp_rw [tensor_expect_sum]
  set e := Equiv.sumPiEquivProdPi
    (fun b : J₀ ⊕ ↥(T L) => Slot → ZMod (joinModuli m₀ (tailModuli T L) b))
  rw [← e.symm.sum_comp, Fintype.sum_prod_type]
  refine sum_congr rfl fun z0 _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun z1 _ => ?_
  rw [Fintype.prod_sum_type]
  have hF : (fun v b => e.symm (z0, z1) b v) =
      fun v => (splitEquiv m₀ (tailModuli T L)).symm ((fun i => z0 i v), (fun j => z1 j v)) := by
    funext v b
    cases b <;> rfl
  rw [hF, mul_assoc]
  rfl

/-- **`lem:record:fibre-scale`(c) for the tensor of the atom laws**: for a child scale `ℓ`
with `T ℓ ⊆ T L` whose missing primes exceed `(Kℓ)^β`, the children
`h = Re 𝓛^𝒮_{[Kℓ],(Kℓ)^β} 1_B` satisfy `Z_{μ_N}(h) ≤ Y(ℓ, B)`. The atom laws are
reflection positive ((R2)) and invariant under the simultaneous translations of the slots
((R3) with `r_p = 1`). -/
theorem restoration_atomLaws {ℓ L : ℕ} (hT : T ℓ ⊆ T L) (hprime : ∀ q ∈ T L, q.Prime)
    (hlarge : ∀ q ∈ T L, q ∉ T ℓ → paperCutoff (blockScale * ℓ) < q)
    (μ0 : ∀ i, FiniteLaw (Slot → ZMod (m₀ i)))
    (μp : ∀ (q : ℕ) [NeZero q], FiniteLaw (Slot → ZMod q))
    (hp0 : ∀ i, SlotReflectionPositive (signedIntegral (μ0 i).weight))
    (hpp : ∀ (q : ℕ) [NeZero q], q.Prime → SlotReflectionPositive (signedIntegral (μp q).weight))
    (hinv0 : ∀ i (r : ZMod (m₀ i)) (F : (Slot → ZMod (m₀ i)) → ℝ),
      (μ0 i).expect (fun z => F (fun v => z v + r)) = (μ0 i).expect F)
    (hinvp : ∀ (q : ℕ) [NeZero q] (r : ZMod q) (F : (Slot → ZMod q) → ℝ),
      (μp q).expect (fun z => F (fun v => z v + r)) = (μp q).expect F)
    (E : Finset (J₀ ⊕ ↥(T L))) (B : Finset ℤ) :
    referenceEnergy (FiniteLaw.tensor (atomLaws m₀ T μ0 μp L))
        (child (joinModuli m₀ (tailModuli T L)) E (paperCutoff (blockScale * ℓ)) B
          (blockScale * ℓ)) ≤
      prefixedFunctional m₀ (J := fun L => ↥(T L)) (fun _ j => (j : ℕ))
        (paperLaw m₀ (J := fun L => ↥(T L)) (fun _ j => (j : ℕ)) (FiniteLaw.tensor μ0) μp) ℓ B := by
  have h := fibreScale_restoration_paper m₀ T hT hprime hlarge (FiniteLaw.tensor μ0) μp
    (tensor_slot_reflection_positive μ0 hp0) hpp
    (fun s₀ F => tensor_translate μ0 hinv0 s₀ F) hinvp E B
  refine le_of_eq_of_le ?_ h
  unfold referenceEnergy child
  exact tensor_atomLaws_expect m₀ T μ0 μp L _

/-- The paper's functional `Y(ℓ, B) = Λ_{μ_{Kℓ}}(F_B)` (`def:record:functional`(d),(e)) for
the reference laws `paperLaw = (⊗_i μ0_i) ⊗ ⊗_{q ∈ T ℓ} μ_q` (`prefixedFunctional`). -/
noncomputable def paperY (μ0 : ∀ i, FiniteLaw (Slot → ZMod (m₀ i)))
    (μp : ∀ (q : ℕ) [NeZero q], FiniteLaw (Slot → ZMod q)) : ℕ → Finset ℤ → ℝ :=
  prefixedFunctional m₀ (J := fun L => ↥(T L)) (fun _ j => (j : ℕ))
    (paperLaw m₀ (J := fun L => ↥(T L)) (fun _ j => (j : ℕ)) (FiniteLaw.tensor μ0) μp)

/-- **The hypothesis `hrest` of `density_structured_dc_scale`** for the tensor of the atom
laws and the paper's functional: at every changed slot `v` whose child scale satisfies
`ℓ_v ≤ L`, `Z_{μ_N}(h) ≤ Y(ℓ_v, B)` for every `B`. The tail family is monotone up to `L`, and
the primes of `T L` missing from `T ℓ` exceed `(Kℓ)^β`. -/
theorem hrest_atomLaws {L : ℕ} (hmono : ∀ ℓ, ℓ ≤ L → T ℓ ⊆ T L) (hprime : ∀ q ∈ T L, q.Prime)
    (hlarge : ∀ ℓ, ℓ ≤ L → ∀ q ∈ T L, q ∉ T ℓ → paperCutoff (blockScale * ℓ) < q)
    (μ0 : ∀ i, FiniteLaw (Slot → ZMod (m₀ i)))
    (μp : ∀ (q : ℕ) [NeZero q], FiniteLaw (Slot → ZMod q))
    (hp0 : ∀ i, SlotReflectionPositive (signedIntegral (μ0 i).weight))
    (hpp : ∀ (q : ℕ) [NeZero q], q.Prime → SlotReflectionPositive (signedIntegral (μp q).weight))
    (hinv0 : ∀ i (r : ZMod (m₀ i)) (F : (Slot → ZMod (m₀ i)) → ℝ),
      (μ0 i).expect (fun z => F (fun v => z v + r)) = (μ0 i).expect F)
    (hinvp : ∀ (q : ℕ) [NeZero q] (r : ZMod q) (F : (Slot → ZMod q) → ℝ),
      (μp q).expect (fun z => F (fun v => z v + r)) = (μp q).expect F)
    (E : Finset (J₀ ⊕ ↥(T L))) (D0 M : Slot → ℕ) (changed : Slot → Prop)
    (hℓ : ∀ v, changed v → stepEll (joinModuli m₀ (tailModuli T L)) E (D0 v) (M v) ≤ L) :
    ∀ v, changed v → ∀ B : Finset ℤ,
      B ⊆ Icc 1 ((blockScale * stepEll (joinModuli m₀ (tailModuli T L)) E (D0 v) (M v) : ℕ) : ℤ) →
      referenceEnergy (FiniteLaw.tensor (atomLaws m₀ T μ0 μp L))
          (child (joinModuli m₀ (tailModuli T L)) E (paperCutoff (blockScale *
            stepEll (joinModuli m₀ (tailModuli T L)) E (D0 v) (M v))) B
            (blockScale * stepEll (joinModuli m₀ (tailModuli T L)) E (D0 v) (M v))) ≤
        paperY m₀ T μ0 μp (stepEll (joinModuli m₀ (tailModuli T L)) E (D0 v) (M v)) B := by
  intro v hv B _
  exact restoration_atomLaws m₀ T (hmono _ (hℓ v hv)) hprime (hlarge _ (hℓ v hv)) μ0 μp hp0 hpp
    hinv0 hinvp E B

/-- `D₀ 1_{n ≡ s (D₀)} 1_A = 1_A` when `D₀ = 1`. -/
theorem inputFun_of_eq_one {D : ℕ} (hD : D = 1) (s : ZMod D) (A : Finset ℤ) :
    inputFun D s A = indicator A := by
  subst hD
  funext n
  have h : ((n : ZMod 1) = s) := Subsingleton.elim _ _
  simp [inputFun, indicator, h]

/-- **The unchanged slots** (`prop:record:density-structured`, proof: "At an unchanged slot
`E = ∅`, `𝒮 = 𝒜_N` and `Z_𝒮(F_A) = Y`"): if `E = ∅`, `D_{0,v} = 1`, `M_v = N` and
`I_v = [N]`, the input is `F_A` and its energy is `Y(L, A)`. This is the hypothesis `hun`
of `density_structured_dc_scale`, with equality. -/
theorem hun_atomLaws {Ω : Type} (μ0 : ∀ i, FiniteLaw (Slot → ZMod (m₀ i)))
    (μp : ∀ (q : ℕ) [NeZero q], FiniteLaw (Slot → ZMod q)) {L : ℕ} (A : Finset ℤ)
    (E : Finset (J₀ ⊕ ↥(T L))) (D0 M : Slot → ℕ) (c : Ω → Slot → ℤ)
    (s : ∀ (_ : Ω) (v : Slot), ZMod (D0 v)) (changed : Slot → Prop)
    (gt : Ω → Slot → ResidueSpace (joinModuli m₀ (tailModuli T L)) →
      ResidueSpace (joinModuli m₀ (tailModuli T L)) → ℝ)
    (hgu : ∀ v, ¬changed v → ∀ ω x,
      gt ω v x = paperInputs (joinModuli m₀ (tailModuli T L)) E (paperCutoff (blockScale * L))
        A D0 M c s ω v x)
    (hunch : ∀ v, ¬changed v → E = ∅ ∧ D0 v = 1 ∧ M v = blockScale * L ∧ ∀ ω, c ω v = 0) :
    ∀ v, ¬changed v → ∀ ω x,
      referenceEnergy (FiniteLaw.tensor (atomLaws m₀ T μ0 μp L)) (gt ω v x) ≤
        paperY m₀ T μ0 μp L A := by
  intro v hv ω x
  obtain ⟨hE, hD, hMv, hc⟩ := hunch v hv
  have hfun : gt ω v x = fun y => (wholeLift (joinModuli m₀ (tailModuli T L))
      (paperCutoff (blockScale * L)) (blockScale * L) A y).re := by
    rw [hgu v hv ω x]
    funext y
    have hfr : coordinateFreeze (joinModuli m₀ (tailModuli T L)) E x y = y := by
      funext k
      simp [coordinateFreeze, hE]
    unfold paperInputs input wholeLift
    rw [hfr, hc ω, hMv, inputFun_of_eq_one hD, zero_add, zero_add]
  rw [hfun]
  apply le_of_eq
  unfold referenceEnergy
  rw [tensor_atomLaws_expect]
  rfl

/-- The tail hypotheses of `density_structured_dc_paper` hold for the paper's tail family
`𝒯_N = tailPrimes P₄` (WP-FI's `tailPrimes_mono`, `tailPrimes_prime`, `tailPrimes_large`). -/
theorem tailPrimes_hyps (P4 L : ℕ) :
    (∀ ℓ, ℓ ≤ L → tailPrimes P4 ℓ ⊆ tailPrimes P4 L) ∧ (∀ q ∈ tailPrimes P4 L, q.Prime) ∧
      (∀ ℓ, ℓ ≤ L → ∀ q ∈ tailPrimes P4 L, q ∉ tailPrimes P4 ℓ →
        paperCutoff (blockScale * ℓ) < q) :=
  ⟨fun _ h => tailPrimes_mono P4 h, tailPrimes_prime P4 L, fun _ _ => tailPrimes_large P4⟩

end Atoms

/-- **`prop:record:density-structured` (first inequality) on the paper's groups with
`lem:record:density-dc` and the restoration `lem:record:fibre-scale`(c) proved**:
`density_structured_dc_scale` for the tensor `μ_N = ⊗_b μ_b` of the atom laws (the prefix
coordinates and the tail primes `T L`) and the paper's functional `Y = paperY`, with the
hypotheses `hrest` (`hrest_atomLaws`) and `hun` (`hun_atomLaws`) discharged.

Compared with `density_structured_dc_scale`:
* the group is `joinModuli m₀ (tailModuli T L)`; the tail moduli are primes (`hprime`) and
  injective (they are the elements of `T L`);
* the tail family is monotone up to `L` (`hmono`), and the primes of `T L \ T ℓ` exceed
  `(Kℓ)^β` (`hlarge`); for `tailPrimes P₄` these are `tailPrimes_mono` and
  `tailPrimes_large`;
* (R2) and (R3) are assumed for each atom law, at all primes for the tail laws. They give the
  hypotheses `hμb` and `hR3` of `density_structured_dc_scale`, and the translation invariance
  used by the restoration (the case `r = 1` of (R3));
* the unchanged slots are those of the paper: `E = ∅`, `D_{0,v} = 1`, `M_v = N`, and
  `I_v = [N]` (`c_v = 0`). -/
theorem density_structured_dc_paper (ε : ℝ) (hε : 0 < ε) :
    ∃ C1 C71 : ℝ, 0 < C1 ∧ 0 < C71 ∧
    ∀ {J₀ : Type} [Fintype J₀] [DecidableEq J₀] (m₀ : J₀ → ℕ) [∀ i, NeZero (m₀ i)]
      (T : ℕ → Finset ℕ) [∀ L (j : ↥(T L)), NeZero (j : ℕ)] {Ω : Type} [Fintype Ω]
      (μ0 : ∀ i, FiniteLaw (Slot → ZMod (m₀ i)))
      (μp : ∀ (q : ℕ) [NeZero q], FiniteLaw (Slot → ZMod q))
      {a θ C0 : ℝ} {L : ℕ} {A : Finset ℤ},
      (∀ ℓ, ℓ ≤ L → T ℓ ⊆ T L) → (∀ q ∈ T L, q.Prime) →
      (∀ ℓ, ℓ ≤ L → ∀ q ∈ T L, q ∉ T ℓ → paperCutoff (blockScale * ℓ) < q) →
      ∀ (_hpair : Pairwise fun i j =>
          (joinModuli m₀ (tailModuli T L) i).Coprime (joinModuli m₀ (tailModuli T L) j))
      (_hcex : IsLeastCounterexample (paperY m₀ T μ0 μp) a θ C0 L A) (_hθ : 0 < θ)
      (_hθ1 : θ ≤ 1) (_ha : 0 ≤ a) (_hC0 : 0 ≤ C0) (_hL : 2 ≤ L)
      (_hY0 : paperY m₀ T μ0 μp L ∅ ≤ 0)
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
      (Tm : Finset (J₀ ⊕ ↥(T L)))
      (_hprimeT : ∀ j ∈ Tm, (joinModuli m₀ (tailModuli T L) j).Prime) {γ : ℝ}
      (_hγ : 0 ≤ γ)
      (_hmix : ∀ j ∈ Tm, ∀ v, IsGammaMixing (joinModuli m₀ (tailModuli T L) j) γ
        (atomLaws m₀ T μ0 μp L j) {v})
      {C' : ℕ} (_hC' : 0 < C')
      (_hdiv : ∀ a : ResidueSpace (joinModuli m₀ (tailModuli T L)),
        (∏ j ∈ univ.filter (· ∉ Tm), addOrderOf (a j)) ∣ C')
      (E : Finset (J₀ ⊕ ↥(T L))) {qE cE : ℕ}
      (_hDE : ∏ j ∈ E, joinModuli m₀ (tailModuli T L) j = qE * cE) (_hqE : Squarefree qE)
      (_hcE : IsSquare cE) (_hcE0 : cE ≠ 0) (_hcQ : cE ≤ Qcl) (_hcopE : qE.Coprime cE)
      (_hqN : (qE : ℝ) ≤ ((blockScale * L : ℕ) : ℝ) ^ stageTau)
      (P : FiniteLaw Ω) (ρ : (Slot → ResidueSpace (joinModuli m₀ (tailModuli T L))) → ℝ)
      (_hunif : selectedMarginalsUniform ρ)
      (D0 : Slot → ℕ) (_hD0 : ∀ v, 1 ≤ D0 v) (_hD0M : ∀ v, D0 v ∣ M0)
      (_hcop0 : ∀ v k, (D0 v).Coprime (joinModuli m₀ (tailModuli T L) k))
      (M : Slot → ℕ) (_hM : ∀ v, M v = blockScale * L ∨ M v = L)
      (c : Ω → Slot → ℤ) (s : ∀ (_ : Ω) (v : Slot), ZMod (D0 v))
      (changed : Slot → Prop) [DecidablePred changed]
      (_hchg : ∀ v, changed v →
        ¬(D0 v * ∏ j ∈ E, joinModuli m₀ (tailModuli T L) j = 1 ∧ M v = blockScale * L))
      (gt : Ω → Slot → ResidueSpace (joinModuli m₀ (tailModuli T L)) →
        ResidueSpace (joinModuli m₀ (tailModuli T L)) → ℝ)
      (_hgt : ∀ ω v x, changed v → gt ω v x = fun y =>
        (squareStepModel (joinModuli m₀ (tailModuli T L)) E x (s ω v) A
          (Icc (c ω v + 1) (c ω v + M v)) (c ω v) (M v)
          (stepR (joinModuli m₀ (tailModuli T L)) E (D0 v))
          (blockScale * stepEll (joinModuli m₀ (tailModuli T L)) E (D0 v) (M v))
          (paperCutoff (blockScale * stepEll (joinModuli m₀ (tailModuli T L)) E (D0 v) (M v)))
          y).re)
      (_hgu : ∀ v, ¬changed v → ∀ ω x,
        gt ω v x = paperInputs (joinModuli m₀ (tailModuli T L)) E (paperCutoff (blockScale * L))
          A D0 M c s ω v x)
      (_hunch : ∀ v, ¬changed v → E = ∅ ∧ D0 v = 1 ∧ M v = blockScale * L ∧ ∀ ω, c ω v = 0)
      {σ : ℝ} (_hσ : 0 ≤ σ) (_hS1 : ε / 20 - γ / 40 ≤ -σ),
      |structuredEnergy (FiniteLaw.tensor (atomLaws m₀ T μ0 μp L)) P ρ
          (paperInputs (joinModuli m₀ (tailModuli T L)) E (paperCutoff (blockScale * L)) A D0 M
            c s)| ≤
        totalVariation ρ * ((1 + scaleU blockScale M0 Qcl stageTau L) *
          mainPrice (paperPrice (joinModuli m₀ (tailModuli T L)) E D0 M L)
            (paperMeanDensity P A D0 M c s) changed a θ (density (blockScale * L) A) *
            paperY m₀ T μ0 μp L A +
          (72 * (C' : ℝ) ^ γ *
            (2 * (M0 : ℝ) ^ 2 * (Fintype.card (ResidueSpace m₀) : ℝ) ^ 2 * C1 * blockScale +
              4 * (Fintype.card (ResidueSpace m₀) : ℝ) ^ 2 * C1 * M0 * blockScale) ^
                ((1 : ℝ) / 2) *
            ((M0 : ℝ) ^ 142 * (Fintype.card (ResidueSpace m₀) : ℝ) ^ 142 * C71 * blockScale +
              2 ^ 141 * (Fintype.card (ResidueSpace m₀) : ℝ) ^ 142 * C71 * M0 * blockScale) ^
                ((71 : ℝ) / 142)) * (L : ℝ) ^ (-σ) * density (blockScale * L) A) := by
  obtain ⟨C1, C71, hC1, hC71, h⟩ := density_structured_dc_scale ε hε
  refine ⟨C1, C71, hC1, hC71, ?_⟩
  intro J₀ _ _ m₀ _ T _ Ω _ μ0 μp a θ C0 L A hmono hprime hlarge hpair hcex hθ hθ1 ha hC0 hL hY0
    M0 Qcl Qpre N0 N0' hsc hM0 hp0 hpp hR30 hR3p Tm hprimeT γ hγ hmix C' hC' hdiv E qE cE hDE hqE
    hcE hcE0 hcQ hcopE hqN P ρ hunif D0 hD0 hD0M hcop0 M hM c s changed _ hchg gt hgt hgu hunch σ
    hσ hS1
  have hL1 : 1 ≤ L := by omega
  have hℓ : ∀ v, changed v → stepEll (joinModuli m₀ (tailModuli T L)) E (D0 v) (M v) ≤ L := by
    intro v _
    have h2 := (step_facts_of_scale (joinModuli m₀ (tailModuli T L)) E hsc hL1 hM0 hDE hqE hcE
      hcE0 hcQ hcopE hqN (hD0M v) (hcop0 v) (hM v)).2.1
    exact Nat.le_of_mul_le_mul_left h2 (by norm_num [blockScale])
  have hinv0 : ∀ i (r : ZMod (m₀ i)) (F : (Slot → ZMod (m₀ i)) → ℝ),
      (μ0 i).expect (fun z => F (fun v => z v + r)) = (μ0 i).expect F := by
    intro i r F
    simpa only [one_mul] using hR30 i 1 r isUnit_one ⟨1, (mul_one 1).symm⟩ F
  have hinvp : ∀ (q : ℕ) [NeZero q] (r : ZMod q) (F : (Slot → ZMod q) → ℝ),
      (μp q).expect (fun z => F (fun v => z v + r)) = (μp q).expect F := by
    intro q _ r F
    simpa only [one_mul] using hR3p q 1 r isUnit_one ⟨1, (mul_one 1).symm⟩ F
  have hμb : ∀ b, SlotReflectionPositive (signedIntegral (atomLaws m₀ T μ0 μp L b).weight) := by
    intro b
    cases b with
    | inl i => exact hp0 i
    | inr j => exact hpp (j : ℕ) (hprime j j.2)
  have hR3 : SquareAffineInvariant (joinModuli m₀ (tailModuli T L)) (atomLaws m₀ T μ0 μp L) := by
    intro b
    cases b with
    | inl i => exact hR30 i
    | inr j => exact hR3p (j : ℕ)
  exact h m₀ (tailModuli T L) (fun j => hprime j j.2) Subtype.val_injective hpair hcex hθ hθ1 ha
    hC0 hL hY0 hsc hM0 (atomLaws m₀ T μ0 μp L) hμb hR3 Tm hprimeT hγ hmix hC' hdiv E hDE hqE hcE
    hcE0 hcQ hcopE hqN P ρ hunif D0 hD0 hD0M hcop0 M hM c s changed hchg gt hgt hgu
    (hun_atomLaws m₀ T μ0 μp A E D0 M c s changed gt hgu hunch)
    (hrest_atomLaws m₀ T hmono hprime hlarge μ0 μp hp0 hpp hinv0 hinvp E D0 M changed hℓ) hσ hS1

/-- **`prop:record:density-structured` (first inequality) for the paper's tail family**:
`density_structured_dc_paper` with `T = tailPrimes P₄` (the tail hypotheses discharged by
`tailPrimes_hyps`). The mixing atoms are the tail primes, and (R4) is stated for their laws
`μ_q`. The prefix conductor is `C' = ∏_i m₀ i`, the full order of the prefix group, which
every prefix character's conductor divides (the role of the paper's `Q_pre`). The models `g̃` (the
square-step models at the changed slots, the inputs at the others) are constructed in the
proof, so they do not appear in the statement. -/
theorem density_structured_dc_tailPrimes (ε : ℝ) (hε : 0 < ε) :
    ∃ C1 C71 : ℝ, 0 < C1 ∧ 0 < C71 ∧
    ∀ {J₀ : Type} [Fintype J₀] [DecidableEq J₀] (m₀ : J₀ → ℕ) [∀ i, NeZero (m₀ i)]
      (P4 : ℕ) {Ω : Type} [Fintype Ω]
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
      (_hmixp : ∀ (j : ↥(tailPrimes P4 L)) (v : Slot), IsGammaMixing (j : ℕ) γ (μp (j : ℕ)) {v})
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
          (72 * ((∏ i, m₀ i : ℕ) : ℝ) ^ γ *
            (2 * (M0 : ℝ) ^ 2 * (Fintype.card (ResidueSpace m₀) : ℝ) ^ 2 * C1 * blockScale +
              4 * (Fintype.card (ResidueSpace m₀) : ℝ) ^ 2 * C1 * M0 * blockScale) ^
                ((1 : ℝ) / 2) *
            ((M0 : ℝ) ^ 142 * (Fintype.card (ResidueSpace m₀) : ℝ) ^ 142 * C71 * blockScale +
              2 ^ 141 * (Fintype.card (ResidueSpace m₀) : ℝ) ^ 142 * C71 * M0 * blockScale) ^
                ((71 : ℝ) / 142)) * (L : ℝ) ^ (-σ) * density (blockScale * L) A) := by
  obtain ⟨C1, C71, hC1, hC71, h⟩ := density_structured_dc_paper ε hε
  refine ⟨C1, C71, hC1, hC71, ?_⟩
  intro J₀ _ _ m₀ _ P4 Ω _ μ0 μp a θ C0 L A hpair hcex hθ hθ1 ha hC0 hL hY0 M0 Qcl Qpre N0 N0'
    hsc hM0 hp0 hpp hR30 hR3p γ hγ hmixp E qE cE hDE hqE hcE hcE0 hcQ hcopE hqN P ρ hunif D0 hD0
    hD0M hcop0 M hM c s changed _ hchg hunch σ hσ hS1
  obtain ⟨hmono, hprime, hlarge⟩ := tailPrimes_hyps P4 L
  set Tm : Finset (J₀ ⊕ ↥(tailPrimes P4 L)) := univ.filter (fun b => b.isRight) with hTm
  have hprimeT : ∀ j ∈ Tm, (joinModuli m₀ (tailModuli (tailPrimes P4) L) j).Prime := by
    intro j hj
    rcases j with i | j
    · simp [hTm] at hj
    · exact hprime j j.2
  have hmix : ∀ j ∈ Tm, ∀ v, IsGammaMixing (joinModuli m₀ (tailModuli (tailPrimes P4) L) j) γ
      (atomLaws m₀ (tailPrimes P4) μ0 μp L j) {v} := by
    intro j hj v
    rcases j with i | j
    · simp [hTm] at hj
    · exact hmixp j v
  have hC' : 0 < ∏ i, m₀ i := Finset.prod_pos fun i _ => Nat.pos_of_ne_zero (NeZero.ne (m₀ i))
  have hdiv : ∀ a : ResidueSpace (joinModuli m₀ (tailModuli (tailPrimes P4) L)),
      (∏ j ∈ univ.filter (· ∉ Tm), addOrderOf (a j)) ∣ ∏ i, m₀ i := by
    intro a
    rw [Finset.prod_filter, Fintype.prod_sum_type]
    simp only [hTm, mem_filter, mem_univ, true_and, Sum.isRight_inl, Sum.isRight_inr,
      Bool.false_eq_true, not_false_eq_true, not_true_eq_false, ite_true, ite_false,
      prod_const_one, mul_one]
    apply Finset.prod_dvd_prod_of_dvd
    intro i _
    have h := addOrderOf_dvd_card (x := a (Sum.inl i))
    rwa [ZMod.card] at h
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
