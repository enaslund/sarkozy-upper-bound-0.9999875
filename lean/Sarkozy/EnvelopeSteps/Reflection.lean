module

public import Sarkozy.MiddleRecords.ActualFeatures

@[expose] public section

/-!
# The arithmetic transport `𝒰` (`lem:reflection-averaging`(b))

`paper/sections/23_envelopes.tex`, `lem:reflection-averaging`(b): with
`ς(x) = (-x₂, -x₁, -x₀)` and `𝒰 f = f ∘ ς`, on a block `𝒰 = ⊗_p 𝒰_p`, `𝒰` is a self-adjoint
unitary of `L²(m_{0,𝔅})` that maps `𝓗₀, 𝓗₁, 𝓗₂, 𝒦₁₂, 𝒦₀₁` onto `𝓗₂, 𝓗₁, 𝓗₀, 𝒦₀₁, 𝒦₁₂`, i.e.
permutes the fold labels by `φ = (0 2)(3 4)`; it conjugates `P₀, P₂, P₁₂` into `P₂, P₀, P₀₁`,
`M_{ab}` into `M_{φ(a)φ(b)}` and `Q₁₂` into `Q₀₁`.

**Generic part.** For an involution `σ` of a finite type preserving a weight `w`:
* `transport σ f = f ∘ σ` is an involution (`transport_transport`), an isometry and self-adjoint
  for `⟨f, g⟩_w = ∑ w f g` (`wip_transport`, `wip_transport_symm`);
* the **coupling operators** `coupOp w πa πb g (x) = E_w[g(y) | π_b(y) = π_a(x)]` (the Markov
  operator of the coupling of the coordinates `a`, `b`; with `πa = πb` the conditional expectation
  `P_a`, with a constant map the projection `𝒥`) are conjugated by `transport σ` into the coupling
  operators of the transported coordinates, whenever `π ∘ σ = τ ∘ π'` with `τ` injective
  (**`coupOp_conj`**).

**The actual fold law.** For the weight `oldW` of the actual half marginal `m₀` at a prime
(`lem:old-f-law`(a), `MiddleRecords.oldW`):
* **`oldW_varsigma`**: `m₀` is `ς`-invariant (no character sum is used: `ς` exchanges the
  differences `x₁ - x₀` and `x₂ - x₁` and fixes `x₂ - x₀`);
* the coordinate maps satisfy `π_a ∘ ς = neg ∘ π_{φ(a)}` (`coord_varsigma`) and
  `π₁₂ ∘ ς = τ ∘ π₀₁`, `π₀₁ ∘ ς = τ ∘ π₁₂` with `τ(a, b) = (-b, -a)`;
* hence **`U_P0`**, **`U_P2`**, **`U_P1`**, **`U_P12`**, **`U_P01`**, **`U_M`** (`M_{ab} ↦
  M_{φ(a)φ(b)}`), **`U_J`**, and **`U_Q12`** (`Q₁₂ ↦ Q₀₁` for the pure-pair substitute
  `Q_ij = P_ij − (P_i + P_j)/(1 + ρ) + (1 − ρ)/(1 + ρ) 𝒥`);
* the feature spaces: `𝒰 (h ∘ π₀) = (h ∘ neg) ∘ π₂` etc. (`U_feature`), and `h ↦ h ∘ neg`
  preserves the mean-zero functions (`sum_comp_neg`).

**The block.** `blockSigma` acts coordinatewise on `∀ p, F p × F p × F p`; the product weight
`∏_p oldW_p` is invariant (`blockW_varsigma`), so the generic statements apply to the block with
`𝒰 = ⊗_p 𝒰_p` (`blockSigma_invol`, `blockCoord_varsigma`).

**Not formalized here:** the record identity `D_{F₂} = 𝒰 D_{F₁}^* 𝒰^*` (it needs the record
differences of `prop:signed-bounds` as operators) and the tensor statement
`𝒰 Lift(D) 𝒰^* = Lift(φ·D)` over several blocks (only its single-factor units are proved).
-/

open Finset
open scoped BigOperators

namespace Sarkozy.EnvelopeSteps

/-! ## Transport by a weight-preserving involution -/

section Generic

variable {Ω : Type*} [Fintype Ω]

/-- `⟨f, g⟩_w = ∑ w f g`. -/
noncomputable def wip (w : Ω → ℝ) (f g : Ω → ℝ) : ℝ := ∑ x, w x * (f x * g x)

/-- `𝒰 f = f ∘ σ`. -/
def transport (σ : Ω → Ω) (f : Ω → ℝ) : Ω → ℝ := fun x => f (σ x)

omit [Fintype Ω] in
theorem transport_transport {σ : Ω → Ω} (hσ : ∀ x, σ (σ x) = x) (f : Ω → ℝ) :
    transport σ (transport σ f) = f := by
  funext x
  simp only [transport, hσ]

/-- The involution as an equivalence. -/
def involEquiv (σ : Ω → Ω) (hσ : ∀ x, σ (σ x) = x) : Ω ≃ Ω :=
  ⟨σ, σ, hσ, hσ⟩

/-- **`𝒰` is an isometry of `L²(w)`** when `w ∘ σ = w`. -/
theorem wip_transport {σ : Ω → Ω} (hσ : ∀ x, σ (σ x) = x) {w : Ω → ℝ} (hw : ∀ x, w (σ x) = w x)
    (f g : Ω → ℝ) : wip w (transport σ f) (transport σ g) = wip w f g := by
  unfold wip transport
  rw [← Equiv.sum_comp (involEquiv σ hσ)]
  exact sum_congr rfl fun x _ => by
    change w (σ x) * (f (σ (σ x)) * g (σ (σ x))) = _
    rw [hw, hσ]

/-- **`𝒰` is self-adjoint in `L²(w)`**. -/
theorem wip_transport_symm {σ : Ω → Ω} (hσ : ∀ x, σ (σ x) = x) {w : Ω → ℝ}
    (hw : ∀ x, w (σ x) = w x) (f g : Ω → ℝ) :
    wip w f (transport σ g) = wip w (transport σ f) g := by
  have h := wip_transport hσ hw (transport σ f) g
  rwa [transport_transport hσ] at h

/-- **The coupling operator** of the coordinates `πa`, `πb`:
`(coupOp w πa πb g)(x) = (∑_{π_b y = π_a x} w(y) g(y)) / ∑_{π_b y = π_a x} w(y)`. With
`πa = πb = π` it is the conditional expectation onto the functions of `π`. -/
noncomputable def coupOp {T : Type*} [DecidableEq T] (w : Ω → ℝ) (πa πb : Ω → T) (g : Ω → ℝ) :
    Ω → ℝ := fun x =>
  (∑ y ∈ univ.filter (fun y => πb y = πa x), w y * g y) /
    ∑ y ∈ univ.filter (fun y => πb y = πa x), w y

/-- **Conjugation of coupling operators.** If `σ` is an involution preserving `w`, and the
coordinates satisfy `πa ∘ σ = τ ∘ πa'`, `πb ∘ σ = τ ∘ πb'` with `τ` injective, then
`𝒰 coupOp(πa, πb) 𝒰 = coupOp(πa', πb')`. -/
theorem coupOp_conj {T T' : Type*} [DecidableEq T] [DecidableEq T'] {σ : Ω → Ω}
    (hσ : ∀ x, σ (σ x) = x) {w : Ω → ℝ} (hw : ∀ x, w (σ x) = w x) (πa πb : Ω → T)
    (πa' πb' : Ω → T') (τ : T' → T) (hτ : Function.Injective τ)
    (ha : ∀ x, πa (σ x) = τ (πa' x)) (hb : ∀ x, πb (σ x) = τ (πb' x)) (g : Ω → ℝ) :
    transport σ (coupOp w πa πb (transport σ g)) = coupOp w πa' πb' g := by
  funext x
  simp only [transport, coupOp]
  have key : ∀ G : Ω → ℝ, ∑ y ∈ univ.filter (fun y => πb y = πa (σ x)), G y =
      ∑ y ∈ univ.filter (fun y => πb' y = πa' x), G (σ y) := by
    intro G
    rw [sum_filter, sum_filter, ← Equiv.sum_comp (involEquiv σ hσ)]
    refine sum_congr rfl fun y _ => ?_
    change (if πb (σ y) = πa (σ x) then G (σ y) else 0) =
      if πb' y = πa' x then G (σ y) else 0
    rw [hb, ha]
    by_cases h : πb' y = πa' x
    · rw [ite_eq_left (congrArg τ h), ite_eq_left h]
    · rw [ite_eq_right (fun h' => h (hτ h')), ite_eq_right h]
  rw [key (fun y => w y * g (σ y)), key w]
  simp only [hσ, hw]

end Generic

/-! ## The actual fold law at a prime -/

section Prime

variable {F : Type*} [Field F]

/-- `ς(x₀, x₁, x₂) = (-x₂, -x₁, -x₀)`. -/
def varsigma (x : F × F × F) : F × F × F := (-x.2.2, -x.2.1, -x.1)

theorem varsigma_invol (x : F × F × F) : varsigma (varsigma x) = x := by
  simp only [varsigma, neg_neg]

/-- The coordinate maps `π₀, π₁, π₂` of an object triple. -/
def coord : Fin 3 → F × F × F → F
  | 0 => fun x => x.1
  | 1 => fun x => x.2.1
  | 2 => fun x => x.2.2

/-- The singleton part of `φ = (0 2)(3 4)`: `(0 2)` on `{0, 1, 2}`. -/
def phi3 : Fin 3 → Fin 3
  | 0 => 2
  | 1 => 1
  | 2 => 0

/-- **`π_a ∘ ς = neg ∘ π_{φ(a)}`.** -/
theorem coord_varsigma (a : Fin 3) (x : F × F × F) :
    coord a (varsigma x) = -coord (phi3 a) x := by
  fin_cases a <;> rfl

/-- The pair coordinates `π₁₂ = (x₁, x₂)` and `π₀₁ = (x₀, x₁)`. -/
def pair12 (x : F × F × F) : F × F := (x.2.1, x.2.2)

/-- `π₀₁ = (x₀, x₁)`. -/
def pair01 (x : F × F × F) : F × F := (x.1, x.2.1)

/-- `τ(a, b) = (-b, -a)`. -/
def tauPair (u : F × F) : F × F := (-u.2, -u.1)

theorem tauPair_injective : Function.Injective (tauPair (F := F)) := by
  intro u v h
  simp only [tauPair, Prod.mk.injEq, neg_inj] at h
  exact Prod.ext h.2 h.1

theorem pair12_varsigma (x : F × F × F) : pair12 (varsigma x) = tauPair (pair01 x) := rfl

theorem pair01_varsigma (x : F × F × F) : pair01 (varsigma x) = tauPair (pair12 x) := rfl

theorem neg_injective' : Function.Injective (fun u : F => -u) := neg_injective

omit [Field F] in
theorem transport_add (σ : F × F × F → F × F × F) (f g : F × F × F → ℝ) :
    transport σ (f + g) = transport σ f + transport σ g := rfl

omit [Field F] in
theorem transport_sub (σ : F × F × F → F × F × F) (f g : F × F × F → ℝ) :
    transport σ (f - g) = transport σ f - transport σ g := rfl

omit [Field F] in
theorem transport_smul (σ : F × F × F → F × F × F) (a : ℝ) (f : F × F × F → ℝ) :
    transport σ (a • f) = a • transport σ f := rfl

/-- **The feature spaces**: `𝒰 (h ∘ π_a) = (h ∘ neg) ∘ π_{φ(a)}`, so `𝒰` maps the functions of
`x₀, x₁, x₂` onto those of `x₂, x₁, x₀`. -/
theorem U_feature (a : Fin 3) (h : F → ℝ) :
    transport varsigma (fun x => h (coord a x)) = fun x => h (-coord (phi3 a) x) := by
  funext x
  simp only [transport, coord_varsigma]

/-- **The pair features**: `𝒰` maps the functions of `(x₁, x₂)` onto those of `(x₀, x₁)`, and
back. -/
theorem U_pair12 (g : F × F → ℝ) :
    transport varsigma (fun x => g (pair12 x)) = fun x => g (tauPair (pair01 x)) := rfl

theorem U_pair01 (g : F × F → ℝ) :
    transport varsigma (fun x => g (pair01 x)) = fun x => g (tauPair (pair12 x)) := rfl

variable [Fintype F] [DecidableEq F]

/-- The weight of `m₀` on triples. -/
noncomputable def foldW (x : F × F × F) : ℝ := MiddleRecords.oldW x.1 x.2.1 x.2.2

/-- **`m₀` is `ς`-invariant**: `oldW(-x₂, -x₁, -x₀) = oldW(x₀, x₁, x₂)`. -/
theorem oldW_varsigma (x₀ x₁ x₂ : F) :
    MiddleRecords.oldW (-x₂) (-x₁) (-x₀) = MiddleRecords.oldW x₀ x₁ x₂ := by
  unfold MiddleRecords.oldW
  have e1 : -x₀ - -x₂ = x₂ - x₀ := by ring
  have e2 : -x₁ - -x₂ = x₂ - x₁ := by ring
  have e3 : -x₀ - -x₁ = x₁ - x₀ := by ring
  rw [e1, e2, e3]
  have hd : (-x₂ ≠ -x₁ ∧ -x₂ ≠ -x₀ ∧ -x₁ ≠ -x₀) ↔ (x₀ ≠ x₁ ∧ x₀ ≠ x₂ ∧ x₁ ≠ x₂) := by
    simp only [ne_eq, neg_inj]
    tauto
  by_cases h : x₀ ≠ x₁ ∧ x₀ ≠ x₂ ∧ x₁ ≠ x₂
  · rw [ite_eq_left (hd.mpr h), ite_eq_left h]
    ring
  · rw [ite_eq_right (fun h' => h (hd.mp h')), ite_eq_right h]

theorem foldW_varsigma (x : F × F × F) : foldW (varsigma x) = foldW x := by
  simp only [foldW, varsigma]
  exact oldW_varsigma x.1 x.2.1 x.2.2

/-- The conditional expectation `P_a` onto the functions of the coordinate `a`, in `L²(m₀)`. -/
noncomputable def Pcoord (a : Fin 3) : (F × F × F → ℝ) → (F × F × F → ℝ) :=
  coupOp foldW (coord a) (coord a)

/-- The singleton couplings `M_{ab}` (`lem:oct24:pure-pair-substitute`), in `L²(m₀)`. -/
noncomputable def Mcoup (a b : Fin 3) : (F × F × F → ℝ) → (F × F × F → ℝ) :=
  coupOp foldW (coord a) (coord b)

/-- `P₁₂`, the conditional expectation onto the functions of `(x₁, x₂)`. -/
noncomputable def P12 : (F × F × F → ℝ) → (F × F × F → ℝ) := coupOp foldW pair12 pair12

/-- `P₀₁`, the conditional expectation onto the functions of `(x₀, x₁)`. -/
noncomputable def P01 : (F × F × F → ℝ) → (F × F × F → ℝ) := coupOp foldW pair01 pair01

/-- The projection `𝒥` onto the constants. -/
noncomputable def Jfold : (F × F × F → ℝ) → (F × F × F → ℝ) :=
  coupOp foldW (fun _ => ()) (fun _ => ())

/-- **`𝒰 M_{ab} 𝒰 = M_{φ(a)φ(b)}`** (with `M_{aa} = P_a`). -/
theorem U_M (a b : Fin 3) (g : F × F × F → ℝ) :
    transport varsigma (Mcoup a b (transport varsigma g)) = Mcoup (phi3 a) (phi3 b) g :=
  coupOp_conj varsigma_invol foldW_varsigma _ _ _ _ (fun u : F => -u) neg_injective'
    (coord_varsigma a) (coord_varsigma b) g

/-- **`𝒰 P_a 𝒰 = P_{φ(a)}`**: `P₀ ↔ P₂`, `P₁` fixed. -/
theorem U_P (a : Fin 3) (g : F × F × F → ℝ) :
    transport varsigma (Pcoord a (transport varsigma g)) = Pcoord (phi3 a) g :=
  U_M a a g

theorem U_P0 (g : F × F × F → ℝ) :
    transport varsigma (Pcoord 0 (transport varsigma g)) = Pcoord 2 g := U_P 0 g

theorem U_P2 (g : F × F × F → ℝ) :
    transport varsigma (Pcoord 2 (transport varsigma g)) = Pcoord 0 g := U_P 2 g

theorem U_P1 (g : F × F × F → ℝ) :
    transport varsigma (Pcoord 1 (transport varsigma g)) = Pcoord 1 g := U_P 1 g

/-- **`𝒰 P₁₂ 𝒰 = P₀₁`.** -/
theorem U_P12 (g : F × F × F → ℝ) :
    transport varsigma (P12 (transport varsigma g)) = P01 g :=
  coupOp_conj varsigma_invol foldW_varsigma _ _ _ _ tauPair tauPair_injective
    pair12_varsigma pair12_varsigma g

/-- **`𝒰 P₀₁ 𝒰 = P₁₂`.** -/
theorem U_P01 (g : F × F × F → ℝ) :
    transport varsigma (P01 (transport varsigma g)) = P12 g :=
  coupOp_conj varsigma_invol foldW_varsigma _ _ _ _ tauPair tauPair_injective
    pair01_varsigma pair01_varsigma g

/-- **`𝒰 𝒥 𝒰 = 𝒥`.** -/
theorem U_J (g : F × F × F → ℝ) :
    transport varsigma (Jfold (transport varsigma g)) = Jfold g :=
  coupOp_conj varsigma_invol foldW_varsigma (fun _ : F × F × F => ()) (fun _ => ())
    (fun _ => ()) (fun _ => ()) id Function.injective_id (fun _ => rfl) (fun _ => rfl) g

/-- The pure-pair substitute `Q_ij = P_ij − (P_i + P_j)/(1 + ρ) + (1 − ρ)/(1 + ρ) 𝒥`
(`lem:oct24:pure-pair-substitute`), given `P_ij`, `P_i`, `P_j`. -/
noncomputable def Qsub (ρ : ℝ) (Pij Pi Pj : (F × F × F → ℝ) → (F × F × F → ℝ))
    (g : F × F × F → ℝ) : F × F × F → ℝ :=
  Pij g - (1 / (1 + ρ)) • (Pi g + Pj g) + ((1 - ρ) / (1 + ρ)) • Jfold g

/-- **`𝒰 Q₁₂ 𝒰 = Q₀₁`.** -/
theorem U_Q12 (ρ : ℝ) (g : F × F × F → ℝ) :
    transport varsigma (Qsub ρ P12 (Pcoord 1) (Pcoord 2) (transport varsigma g)) =
      Qsub ρ P01 (Pcoord 1) (Pcoord 0) g := by
  simp only [Qsub, transport_add, transport_sub, transport_smul, U_P12, U_P1, U_P2, U_J]

/-- **`𝒰 Q₀₁ 𝒰 = Q₁₂`.** -/
theorem U_Q01 (ρ : ℝ) (g : F × F × F → ℝ) :
    transport varsigma (Qsub ρ P01 (Pcoord 0) (Pcoord 1) (transport varsigma g)) =
      Qsub ρ P12 (Pcoord 2) (Pcoord 1) g := by
  simp only [Qsub, transport_add, transport_sub, transport_smul, U_P01, U_P1, U_P0, U_J]

omit [DecidableEq F] in
/-- `h ↦ h ∘ neg` preserves the mean-zero functions of one label. -/
theorem sum_comp_neg (h : F → ℝ) : ∑ u, h (-u) = ∑ u, h u :=
  Equiv.sum_comp (Equiv.neg F) h

/-- `𝒰` is a self-adjoint isometry of `L²(m₀)`. -/
theorem U_isometry (f g : F × F × F → ℝ) :
    wip foldW (transport varsigma f) (transport varsigma g) = wip foldW f g :=
  wip_transport varsigma_invol foldW_varsigma f g

theorem U_selfAdjoint (f g : F × F × F → ℝ) :
    wip foldW f (transport varsigma g) = wip foldW (transport varsigma f) g :=
  wip_transport_symm varsigma_invol foldW_varsigma f g

end Prime

/-! ## The block -/

section Block

variable {P : Type*} {F : P → Type*} [∀ p, Field (F p)]

/-- `ς` on a block, coordinatewise. -/
def blockSigma (x : ∀ p, F p × F p × F p) : ∀ p, F p × F p × F p := fun p => varsigma (x p)

theorem blockSigma_invol (x : ∀ p, F p × F p × F p) : blockSigma (blockSigma x) = x := by
  funext p
  exact varsigma_invol (x p)

/-- The coordinate `a` of the whole object, `(x_{a,p})_p`. -/
def blockCoord (a : Fin 3) (x : ∀ p, F p × F p × F p) : ∀ p, F p := fun p => coord a (x p)

/-- **`π_a ∘ ς = neg ∘ π_{φ(a)}` on the block.** -/
theorem blockCoord_varsigma (a : Fin 3) (x : ∀ p, F p × F p × F p) :
    blockCoord a (blockSigma x) = fun p => -blockCoord (phi3 a) x p := by
  funext p
  exact coord_varsigma a (x p)

theorem blockNeg_injective : Function.Injective (fun (u : ∀ p, F p) p => -u p) := by
  intro u v h
  funext p
  exact neg_injective (congrFun h p)

variable [Fintype P] [∀ p, Fintype (F p)] [∀ p, DecidableEq (F p)]

/-- The product weight `m_{0,𝔅} = ⊗_p m_{0,p}` (unnormalized). -/
noncomputable def blockW (x : ∀ p, F p × F p × F p) : ℝ := ∏ p, foldW (x p)

/-- **`m_{0,𝔅}` is `ς`-invariant.** -/
theorem blockW_varsigma (x : ∀ p, F p × F p × F p) : blockW (blockSigma x) = blockW x := by
  unfold blockW blockSigma
  exact prod_congr rfl fun p _ => foldW_varsigma (x p)

variable [DecidableEq P]

/-- **`𝒰 M_{ab} 𝒰 = M_{φ(a)φ(b)}` on a block** (with `𝒰 = ⊗_p 𝒰_p` and the actual block law); with
`a = b` this is `P₀ ↔ P₂`, `P₁` fixed for the whole objects. -/
theorem U_M_block (a b : Fin 3) (g : (∀ p, F p × F p × F p) → ℝ) :
    transport blockSigma (coupOp blockW (blockCoord a) (blockCoord b) (transport blockSigma g)) =
      coupOp blockW (blockCoord (phi3 a)) (blockCoord (phi3 b)) g :=
  coupOp_conj blockSigma_invol blockW_varsigma _ _ _ _ (fun (u : ∀ p, F p) p => -u p)
    blockNeg_injective (blockCoord_varsigma a) (blockCoord_varsigma b) g

/-- `𝒰` is a self-adjoint isometry of `L²(m_{0,𝔅})`. -/
theorem U_block_selfAdjoint (f g : (∀ p, F p × F p × F p) → ℝ) :
    wip blockW f (transport blockSigma g) = wip blockW (transport blockSigma f) g :=
  wip_transport_symm blockSigma_invol blockW_varsigma f g

end Block

end Sarkozy.EnvelopeSteps
