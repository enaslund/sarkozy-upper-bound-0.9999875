module

public import Sarkozy.Cancellation.TailEncoding
public import Sarkozy.ProbabilityProducts

@[expose] public section

/-!
# Step 1 of `lem:record:density-can` over the PaperFrame objects

`paper/sections/08_scale_comparison.tex`, `lem:record:density-can`, Step 1 (the encoding of the
query integral), for the objects of `Sarkozy.PaperFrame` and WP-FI's corrected
`Sarkozy.TheoremC.DensityCancellation`.

**The atoms.** The atoms are split by `IsLow`: an atom is low if it is the prefix or a tail prime
below `P₅`. The tail primes `p ≥ P₅` (`TailIdx`) are reindexed by `tailEquiv`/`tailRelabel`.
At one slot, the labels of the low and the tail atoms are merged by `mergeAt`. The encoded data:
* `μ = FiniteLaw.pi (ϱ_b)_{b low}`;
* `κ_k = encKappa`, the tail pair laws (`tailLaw`) of `ϱ_{p_k}` on `Ω_{p_k} × B_k`;
* `F₁ = encF G u`, `F₂ = encF G v`, the pair factors read through the low labels;
* `W = encW G u v = ∏_{w ≠ u, v} G_w`.

**Results.**
* `paper_encoding`: `∫∏_w G_w dϱ = μ.expect(∑_b κ_B(b) T^κ φ_x(b) W_x(b))`. This is the identity
  for `I₀` in `PairLawForm`.
* `pairLawForm_of_steps`: `PairLawForm` for a query, from Steps 2 and 3 at the encoded data,
  given the intervals and these hypotheses:
  - distinct prime moduli and `P₅ ≥ 64`;
  - the corrected (a): `PairUniformOmega` and `IsGammaMixing` at every tail prime `≥ P₅`.
* `densityCancellation_of_steps`: WP-FI's `DensityCancellation` from Steps 2 and 3 alone
  (`LiftMoments`, `FibreData` at the encoded data, with the constants fixed in advance). Step 1
  is fully discharged.

New material for this paper.
-/

namespace Sarkozy.Cancellation

open Finset
open scoped BigOperators
open Sarkozy.Mixing Sarkozy.PaperFrame Sarkozy.FourierArithmetic

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] (m₀ : J₀ → ℕ) [∀ i, NeZero (m₀ i)]
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] (p : ∀ L, J L → ℕ)
  [∀ L j, NeZero (p L j)]

/-- The atoms below `P₅`: the prefix and the tail primes `p < P₅`. -/
def IsLow (L P5 : ℕ) (b : PaperAtom J L) : Prop := ∀ j, b = some j → p L j < P5

instance (L P5 : ℕ) : DecidablePred (IsLow p L P5) := fun b => by unfold IsLow; infer_instance

/-- The tail primes `p ≥ P₅`. -/
abbrev TailIdx (L P5 : ℕ) : Type := {j : J L // P5 ≤ p L j}

/-- The tail moduli `q_k = p_k`. -/
def tailQ (L P5 : ℕ) (k : TailIdx p L P5) : ℕ := p L k.1

instance (L P5 : ℕ) (k : TailIdx p L P5) : NeZero (tailQ p L P5 k) :=
  inferInstanceAs (NeZero (p L k.1))

/-- The tail primes are the atoms that are not low. -/
def tailEquiv (L P5 : ℕ) : TailIdx p L P5 ≃ {b : PaperAtom J L // ¬ IsLow p L P5 b} where
  toFun k := ⟨some k.1, fun h => absurd (h k.1 rfl) (not_lt.mpr k.2)⟩
  invFun b := match b with
    | ⟨some j, hb⟩ => ⟨j, by
        unfold IsLow at hb
        push Not at hb
        obtain ⟨j', hj', hp⟩ := hb
        cases hj'
        exact hp⟩
    | ⟨none, hb⟩ => absurd (fun j h => by cases h) hb
  left_inv k := rfl
  right_inv b := by
    match b with
    | ⟨some j, hb⟩ => rfl
    | ⟨none, hb⟩ => exact absurd (fun j h => by cases h) hb

/-- The atom labels at one slot, from the labels `xw` of the low atoms and the labels `a` of the
tail primes. -/
def mergeAt (L P5 : ℕ) (xw : ∀ i : {b : PaperAtom J L // IsLow p L P5 b}, AtomLabel m₀ p L i.1)
    (a : ∀ k : TailIdx p L P5, ZMod (tailQ p L P5 k)) : ∀ b, AtomLabel m₀ p L b :=
  (Equiv.piEquivPiSubtypeProd (IsLow p L P5) (AtomLabel m₀ p L)).symm
    (xw, Equiv.piCongrLeft (fun i : {b // ¬ IsLow p L P5 b} => AtomLabel m₀ p L i.1)
      (tailEquiv p L P5) a)

/-- The low labels: the prefix and the tail primes below `P₅`, at every slot. -/
abbrev LowLabels (L P5 : ℕ) : Type :=
  ∀ i : {b : PaperAtom J L // IsLow p L P5 b}, Slot → AtomLabel m₀ p L i.1

/-- The pair factor `F₁(x, ·) = G_u` with the low labels `x` fixed. -/
def encF (L P5 : ℕ) (G : Slot → (∀ b, AtomLabel m₀ p L b) → ℝ) (w : Slot)
    (x : LowLabels m₀ p L P5) (a : ResidueSpace (tailQ p L P5)) : ℝ :=
  G w (mergeAt m₀ p L P5 (fun i => x i w) a)

/-- The other factors `W(x, ·) = ∏_{w ≠ u, v} G_w`. -/
def encW (L P5 : ℕ) (G : Slot → (∀ b, AtomLabel m₀ p L b) → ℝ) (u v : Slot)
    (x : LowLabels m₀ p L P5)
    (b : ∀ k : TailIdx p L P5, {w // w ∉ ({u, v} : Finset Slot)} → ZMod (tailQ p L P5 k)) : ℝ :=
  ∏ w : {w // w ∉ ({u, v} : Finset Slot)}, G w.1 (mergeAt m₀ p L P5 (fun i => x i w.1)
    (fun k => b k w))

omit [Fintype J₀] [DecidableEq J₀] [∀ i, NeZero (m₀ i)] [∀ L j, NeZero (p L j)] in
/-- The merged labels at a slot are `mergeAt`. -/
lemma merge_eq_mergeAt (L P5 : ℕ) (x : LowLabels m₀ p L P5)
    (y' : ∀ k : TailIdx p L P5, Slot → AtomLabel m₀ p L ((tailEquiv p L P5) k).1) (w : Slot) :
    (fun b => (Equiv.piEquivPiSubtypeProd (IsLow p L P5) (fun b => Slot → AtomLabel m₀ p L b)).symm
      (x, Equiv.piCongrLeft (fun i : {b // ¬ IsLow p L P5 b} => Slot → AtomLabel m₀ p L i.1)
        (tailEquiv p L P5) y') b w) =
      mergeAt m₀ p L P5 (fun i => x i w) (fun k => y' k w) := by
  have key : ∀ i : {b // ¬ IsLow p L P5 b},
      (Equiv.piCongrLeft (fun i : {b // ¬ IsLow p L P5 b} => Slot → AtomLabel m₀ p L i.1)
        (tailEquiv p L P5) y') i w =
      (Equiv.piCongrLeft (fun i : {b // ¬ IsLow p L P5 b} => AtomLabel m₀ p L i.1)
        (tailEquiv p L P5) (fun k => y' k w)) i := by
    intro i
    obtain ⟨k, rfl⟩ := (tailEquiv p L P5).surjective i
    rw [Equiv.piCongrLeft_apply_apply, Equiv.piCongrLeft_apply_apply]
  funext b
  unfold mergeAt
  simp only [Equiv.piEquivPiSubtypeProd_symm_apply]
  by_cases hb : IsLow p L P5 b
  · simp only [hb, ↓reduceDIte]
  · simp only [hb, ↓reduceDIte]
    exact key ⟨b, hb⟩

/-- The tail pair laws of the query: `κ_k = tailLaw` of `ϱ_{p_k}`. -/
noncomputable def encKappa (L P5 : ℕ)
    (ϱ : ∀ b : PaperAtom J L, FiniteLaw (Slot → AtomLabel m₀ p L b)) {u v : Slot} (huv : u ≠ v)
    (hU : ∀ k : TailIdx p L P5,
      Sarkozy.TheoremC.PairUniformOmega (q := tailQ p L P5 k) (ϱ (some k.1)) u v)
    (k : TailIdx p L P5) :
    FiniteLaw (PairAlphabet (tailQ p L P5) k ×
      ({w // w ∉ ({u, v} : Finset Slot)} → ZMod (tailQ p L P5 k))) :=
  tailLaw (tailQ p L P5) k huv (ϱ (some k.1)) (hU k)

/-- The reindexing of the tail atoms by the tail primes. -/
noncomputable def tailRelabel (L P5 : ℕ) :
    (∀ k : TailIdx p L P5, Slot → ZMod (tailQ p L P5 k)) ≃
      (∀ i : {b : PaperAtom J L // ¬ IsLow p L P5 b}, Slot → AtomLabel m₀ p L i.1) :=
  Equiv.piCongrLeft (fun i : {b // ¬ IsLow p L P5 b} => Slot → AtomLabel m₀ p L i.1)
    (tailEquiv p L P5)

omit [Fintype J₀] [DecidableEq J₀] [∀ i, NeZero (m₀ i)] [∀ L, Fintype (J L)]
  [∀ L, DecidableEq (J L)] [∀ L j, NeZero (p L j)] in
lemma tailRelabel_apply (L P5 : ℕ) (y' : ∀ k : TailIdx p L P5, Slot → ZMod (tailQ p L P5 k))
    (k : TailIdx p L P5) : tailRelabel m₀ p L P5 y' (tailEquiv p L P5 k) = y' k :=
  Equiv.piCongrLeft_apply_apply _ _ _ _

/-- **Step 1 of `lem:record:density-can`, the encoding of the query integral**: the coupled
integral of a query is `I = ∫_x ∑_b κ_B(b) T^κ φ_x(b) W_x(b) dμ(x)`, with `μ` the product of the
laws of the atoms below `P₅` over all slots, `κ = ⊗_k κ_k` the tail pair laws on `Ω_{p_k} × B_k`
(`encKappa`), `φ_x(a) = F₁(x, x(a)) F₂(x, y(a))` with `F₁ = G_u`, `F₂ = G_v` read through the
low labels `x` (`encF`), and `W_x = ∏_{w ≠ u, v} G_w` (`encW`). This is the identity for `I₀` in
`PairLawForm`. -/
theorem paper_encoding (L P5 : ℕ)
    (ϱ : ∀ b : PaperAtom J L, FiniteLaw (Slot → AtomLabel m₀ p L b)) {u v : Slot} (huv : u ≠ v)
    (hU : ∀ k : TailIdx p L P5,
      Sarkozy.TheoremC.PairUniformOmega (q := tailQ p L P5 k) (ϱ (some k.1)) u v)
    (G : Slot → (∀ b, AtomLabel m₀ p L b) → ℝ) :
    multilinearIntegral (tensorLaw fun b => signedIntegral (ϱ b).weight) G =
      (FiniteLaw.pi (fun i : {b : PaperAtom J L // IsLow p L P5 b} => ϱ i.1)).expect fun x =>
        ∑ b, tgtWeight (prodJoint (encKappa m₀ p L P5 ϱ huv hU)) b *
          condOp (prodJoint (encKappa m₀ p L P5 ϱ huv hU))
            (fun a => encF m₀ p L P5 G u x (pairsToVectors (tailQ p L P5) a).1 *
              encF m₀ p L P5 G v x (pairsToVectors (tailQ p L P5) a).2) b *
          encW m₀ p L P5 G u v x b := by
  rw [coupled_integral_split ϱ G (IsLow p L P5)]
  unfold FiniteLaw.expect
  refine sum_congr rfl fun x _ => ?_
  congr 1
  beta_reduce
  unfold encKappa
  rw [← tail_integral_eq (tailQ p L P5) huv (fun k => ϱ (some k.1)) hU (encF m₀ p L P5 G u x)
    (encF m₀ p L P5 G v x) (encW m₀ p L P5 G u v x)]
  rw [← (tailRelabel m₀ p L P5).sum_comp]
  refine sum_congr rfl fun y' _ => ?_
  have hw : ∏ i : {b // ¬ IsLow p L P5 b}, (ϱ i.1).weight (tailRelabel m₀ p L P5 y' i) =
      ∏ k : TailIdx p L P5,
        ((ϱ (some k.1) : FiniteLaw (Slot → ZMod (tailQ p L P5 k)))).weight (y' k) := by
    refine (Fintype.prod_equiv (tailEquiv p L P5)
      (fun k => ((ϱ (some k.1) : FiniteLaw (Slot → ZMod (tailQ p L P5 k)))).weight (y' k)) _
      (fun k => ?_)).symm
    rw [tailRelabel_apply]
    rfl
  rw [hw]
  have hG : ∀ w, G w (fun i => (Equiv.piEquivPiSubtypeProd (IsLow p L P5)
      (fun b => Slot → AtomLabel m₀ p L b)).symm (x, tailRelabel m₀ p L P5 y') i w) =
      G w (mergeAt m₀ p L P5 (fun i => x i w) (fun k => y' k w)) := by
    intro w
    congr 1
    exact merge_eq_mergeAt m₀ p L P5 x y' w
  simp only [hG]
  rw [prod_slots_split huv]
  unfold encF encW
  ring

/-! ## Step 1 discharged: `PairLawForm` from Steps 2–3 at the encoded data -/

section Packaged

variable [hprime : ∀ L j, Fact (p L j).Prime]

instance tailQ_prime (L P5 : ℕ) (k : TailIdx p L P5) : Fact (tailQ p L P5 k).Prime :=
  inferInstanceAs (Fact (p L k.1).Prime)

/-- **`PairLawForm` for a query, with Step 1 discharged**: for a query whose tail laws satisfy
the corrected (a) (`PairUniformOmega` and `IsGammaMixing` at every tail prime `p ≥ P₅`), with
distinct prime moduli and `P₅ ≥ 64`, the coupled integral has the pair-law form as soon as
Step 2 (`LiftMoments`) and Step 3 (`FibreData`) hold for the encoded data `μ`, `κ = encKappa`,
`F₁ = encF G u`, `F₂ = encF G v`, `W = encW G u v`, and the intervals `[u₁, v₁]`, `[u₂, v₂]`
satisfy the ordering and length conditions. -/
theorem pairLawForm_of_steps (L P5 : ℕ)
    (ϱ : ∀ b : PaperAtom J L, FiniteLaw (Slot → AtomLabel m₀ p L b)) {u v : Slot} (huv : u ≠ v)
    (hU : ∀ k : TailIdx p L P5,
      Sarkozy.TheoremC.PairUniformOmega (q := tailQ p L P5 k) (ϱ (some k.1)) u v)
    (hmix : ∀ k : TailIdx p L P5, IsGammaMixing (tailQ p L P5 k) Sarkozy.AnalyticStage.γ
      (ϱ (some k.1) : FiniteLaw (Slot → ZMod (tailQ p L P5 k))) {u, v})
    (hinj : Function.Injective (p L)) (h64 : 64 ≤ P5)
    (G : Slot → (∀ b, AtomLabel m₀ p L b) → ℝ) (N : ℕ) (Lr : ℝ) (A : Finset ℤ)
    (C₂ Kc M₀ Cε : ℝ) (u₁ v₁ u₂ v₂ : ℤ) (h1 : v₁ < u₂) (h2 : u₂ ≤ v₂)
    (hlen : ((v₂ - u₂ + 1 : ℤ) : ℝ) ≤ Lr)
    (hMom : LiftMoments (tailQ p L P5)
      (FiniteLaw.pi (fun i : {b : PaperAtom J L // IsLow p L P5 b} => ϱ i.1))
      (encKappa m₀ p L P5 ϱ huv hU) (encF m₀ p L P5 G u) (encF m₀ p L P5 G v)
      (encW m₀ p L P5 G u v) N C₂ (density N A))
    (hFib : ∀ U : TailIdx p L P5 → Bool, supportConductor (tailQ p L P5) U ≤ (N : ℝ) ^ stageTan →
      FibreData (tailQ p L P5)
        (FiniteLaw.pi (fun i : {b : PaperAtom J L // IsLow p L P5 b} => ϱ i.1))
        (encF m₀ p L P5 G u) (encF m₀ p L P5 G v) A u₁ v₁ u₂ v₂ N Lr Kc M₀ Cε (density N A) U) :
    PairLawForm N Lr A C₂ Kc M₀ Cε
      (multilinearIntegral (tensorLaw fun b => signedIntegral (ϱ b).weight) G) := by
  refine ⟨TailIdx p L P5, inferInstance, inferInstance, tailQ p L P5, inferInstance,
    inferInstance, fun k k' h => Subtype.ext (hinj h), fun k => h64.trans k.2,
    LowLabels m₀ p L P5, inferInstance,
    FiniteLaw.pi (fun i : {b : PaperAtom J L // IsLow p L P5 b} => ϱ i.1),
    fun k => {w // w ∉ ({u, v} : Finset Slot)} → ZMod (tailQ p L P5 k), inferInstance,
    encKappa m₀ p L P5 ϱ huv hU,
    fun k c => tailLaw_src (tailQ p L P5) k huv _ (hU k) c,
    fun k => tailLaw_mix (tailQ p L P5) k huv _ (hU k) (hmix k),
    encF m₀ p L P5 G u, encF m₀ p L P5 G v, encW m₀ p L P5 G u v, u₁, v₁, u₂, v₂, h1, h2, hlen,
    hMom, hFib, ?_⟩
  exact paper_encoding m₀ p L P5 ϱ huv hU G

end Packaged

/-! ## `DensityCancellation` from Steps 2–3 -/

section FromSteps

variable [∀ L j, Fact (p L j).Prime] {P : Type} [Fintype P] (pr h : P → ℕ)

open Sarkozy.TheoremC Sarkozy.Functional Sarkozy.IndexSupport Sarkozy.Comparison in
/-- **`DensityCancellation` from Steps 2 and 3 alone** (Step 1, the encoding, discharged by
`paper_encoding`, `tailLaw_src`, `tailLaw_mix`): for every query at every scale `L ≥ L₁`, with the
intervals `[u₁, v₁] = I_b`, `[u₂, v₂] = I_{b+1}`, the moment bounds `LiftMoments`
(`lem:record:lift-moments`(c)) and the fibre data `FibreData` hold for the encoded data with the
constants `C₂, M₀, Cε` fixed in advance. -/
theorem densityCancellation_of_steps (P5 : ℕ) (pp ep : J₀ → ℕ)
    (hinj : ∀ L, Function.Injective (p L)) (h64 : 64 ≤ P5) {C₂ M₀ Cε : ℝ} (hC₂ : 0 ≤ C₂)
    (hM₀ : 0 ≤ M₀) (hCε : 0 ≤ Cε) (L₁ : ℕ)
    (hSteps : ∀ L : ℕ, L₁ ≤ L → ∀ A : Finset ℤ, Admissible (blockScale * L) A →
      ∀ ϱ : ∀ b : PaperAtom J L, FiniteLaw (Slot → AtomLabel m₀ p L b),
      (∀ b, HasUniformMarginals (ϱ b)) → ∀ (u v : Slot) (huv : u ≠ v),
      ∀ ha : (∀ j : J L, P5 ≤ p L j → PairUniformOmega (q := p L j) (ϱ (some j)) u v ∧
        Sarkozy.Mixing.IsGammaMixing (p L j) Sarkozy.AnalyticStage.γ (ϱ (some j)) {u, v}),
      (∀ b : PaperAtom J L, (∀ j, b = some j → p L j < P5) → ∀ z, (ϱ b).weight z ≠ 0 →
        AcceptedPair m₀ p pp ep L b (z u) (z v)) →
      ∀ (bI : ZMod blockScale) (s r : ZMod (modulus pr h)), bI ≠ 0 →
      IsNonvanishingSquareClass (modulus pr h) r →
      ∀ G : Slot → (∀ b, AtomLabel m₀ p L b) → ℝ,
      G u = indexInputAt m₀ p pr h L A (bI, s) →
      G v = indexInputAt m₀ p pr h L A (bI + 1, s + r) →
      (∀ w, w ≠ u → w ≠ v → IsQueryInput m₀ p pr h L A (G w)) →
      ∃ u₁ v₁ u₂ v₂ : ℤ, v₁ < u₂ ∧ u₂ ≤ v₂ ∧ ((v₂ - u₂ + 1 : ℤ) : ℝ) ≤ (L : ℝ) ∧
        LiftMoments (tailQ p L P5)
          (FiniteLaw.pi (fun i : {b : PaperAtom J L // IsLow p L P5 b} => ϱ i.1))
          (encKappa m₀ p L P5 ϱ huv (fun k => (ha k.1 k.2).1)) (encF m₀ p L P5 G u)
          (encF m₀ p L P5 G v) (encW m₀ p L P5 G u v) (blockScale * L) C₂
          (density (blockScale * L) A) ∧
        ∀ U : TailIdx p L P5 → Bool,
          supportConductor (tailQ p L P5) U ≤ ((blockScale * L : ℕ) : ℝ) ^ stageTan →
          FibreData (tailQ p L P5)
            (FiniteLaw.pi (fun i : {b : PaperAtom J L // IsLow p L P5 b} => ϱ i.1))
            (encF m₀ p L P5 G u) (encF m₀ p L P5 G v) A u₁ v₁ u₂ v₂ (blockScale * L) (L : ℝ)
            (blockScale : ℝ) M₀ Cε (density (blockScale * L) A) U) :
    DensityCancellation m₀ p pr h P5 pp ep := by
  apply Glue.densityCancellation_of_pairLawForm m₀ p pr h P5 pp ep hC₂ hM₀ hCε L₁
  intro L hL A hA I₀ hQ
  obtain ⟨ϱ, hϱ, u, v, huv, ha, hb, bI, s, r, hbI, hr, G, hGu, hGv, hGw, hI⟩ := hQ
  obtain ⟨u₁, v₁, u₂, v₂, h1, h2, hlen, hMom, hFib⟩ :=
    hSteps L hL A hA ϱ hϱ u v huv ha hb bI s r hbI hr G hGu hGv hGw
  rw [hI]
  exact pairLawForm_of_steps m₀ p L P5 ϱ huv (fun k => (ha k.1 k.2).1) (fun k => (ha k.1 k.2).2)
    (hinj L) h64 G (blockScale * L) (L : ℝ) A C₂ (blockScale : ℝ) M₀ Cε u₁ v₁ u₂ v₂ h1 h2 hlen
    hMom hFib

end FromSteps

end Sarkozy.Cancellation
