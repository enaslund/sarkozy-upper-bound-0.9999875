module

public import Sarkozy.PartV.BlockLaw
public import Sarkozy.Labellings.TwoLayer
public import Sarkozy.Labellings.Layer12
public import Sarkozy.Reflection.ChamberIid
public import Sarkozy.Reflection.CommonCut

@[expose] public section

/-!
# Pattern types, emissions and weighted completions (`def:patterns`, `def:two-coordinate-five-type`)

`paper/sections/17_completion_repair.tex`, `def:patterns`, `def:five-type-datum`,
`def:two-coordinate-five-type`; `paper/sections/20c_middle_frame.tex`,
`subsec:middle-reference-law`; `paper/sections/25_upper_reference.tex`, `subsec:layer72:upper`.

* `PType`: the five pattern types `L, D, S, R, C` with multiplicities `1, 3, 2, 6, 2` and formal
  degrees `0, 1, 1, 2, 3` (`def:patterns`); `PType.Pat t` indexes the patterns of type `t`
  (`P_L = {id}`, `P_D = {F₀, F₁, F₂}`, `P_S = {E₀, E₁}`, `P_R = {G_{sk}}`, `P_C = {C₀, C₁}`), and
  `Fintype.card (Pat t) = mult t` (`card_pat`).
* `FType`: the three field types `L, F, E` of `def:two-coordinate-five-type`, with object sets
  `O_L = ℤ/6ℤ`, `O_F = O_E = {0, 1, 2}` and the relations of `Sarkozy.Labellings.TwoLayer`;
  `PType.field` is the field type of a pattern type (`𝔣(L) = L`, `𝔣(D) = F`, `𝔣(S) = 𝔣(R) =
  𝔣(C) = E`), and `PType.pat t φ : ℤ/6ℤ → O_{𝔣(t)}` the pattern map itself (the merges take
  values in `{0, 1} ⊂ {0, 1, 2}`, i.e. they read the objects `0, 1` of the `E` law, which is the
  paper's `Π_{G_{sk}}(Γ)` with `Γ` the two-object marginal; the constants read the object `0`,
  which is `Π_0(ν)`).
* Emissions to the 72 slots: `midEmission` (`def:construction`(b), middle: the slot
  `(u₀, u₁, ℓ)` reads the label of the object `φ(u₀)` at the layer `ℓ`, whatever `u₁` is) and
  `upEmission` (`subsec:layer72:upper`: `(u₀, u₁, ℓ) ↦ (φ₀(u₀), φ₁(u₁), ℓ)`), each with its
  one-layer diagonal copy `Diag_ι` (the layer is forgotten).
* `weightedCompletion c comp`: the normalized nonnegative combination `∑ᵢ cᵢ Πᵢ / ∑ᵢ cᵢ` of
  probability laws; it is a probability law, inherits uniform one-slot marginals, and is
  reflection positive at every cut at which every component is
  (`weightedCompletion_positive`).
* A pulled-back law whose emission is fixed by a cut is positive at that cut
  (`map_emission_positive`): this gives positivity at the chamber cuts of the second coordinate
  for every middle component, and at `ι` for every one-layer diagonal copy.
-/

namespace Sarkozy.PartV

open Finset Sarkozy.Labellings

/-! ## Pattern types (`def:patterns`) -/

/-- The five pattern types `L, D, S, R, C` (root, folds, matchings, merges, constants). -/
inductive PType where
  | L | D | S | R | C
  deriving DecidableEq

instance : Fintype PType where
  elems := {.L, .D, .S, .R, .C}
  complete := by intro x; cases x <;> decide

namespace PType

/-- The multiplicities `1, 3, 2, 6, 2`. -/
def mult : PType → ℕ
  | L => 1 | D => 3 | S => 2 | R => 6 | C => 2

/-- The formal degrees `0, 1, 1, 2, 3`. -/
def deg : PType → ℕ
  | L => 0 | D => 1 | S => 1 | R => 2 | C => 3

/-- The index set of the patterns of a type. -/
abbrev Pat : PType → Type
  | L => Unit
  | D => Fin 3
  | S => Fin 2
  | R => Fin 2 × Fin 3
  | C => Fin 2

instance instFintypePat : ∀ t : PType, Fintype t.Pat
  | L => inferInstanceAs (Fintype Unit)
  | D => inferInstanceAs (Fintype (Fin 3))
  | S => inferInstanceAs (Fintype (Fin 2))
  | R => inferInstanceAs (Fintype (Fin 2 × Fin 3))
  | C => inferInstanceAs (Fintype (Fin 2))

instance instDecidableEqPat : ∀ t : PType, DecidableEq t.Pat
  | L => inferInstanceAs (DecidableEq Unit)
  | D => inferInstanceAs (DecidableEq (Fin 3))
  | S => inferInstanceAs (DecidableEq (Fin 2))
  | R => inferInstanceAs (DecidableEq (Fin 2 × Fin 3))
  | C => inferInstanceAs (DecidableEq (Fin 2))

/-- A sum over the five pattern types, written out. -/
theorem sum_pType {M : Type*} [AddCommMonoid M] (f : PType → M) :
    ∑ t, f t = f .L + (f .D + (f .S + (f .R + f .C))) := by
  rw [show (univ : Finset PType) = {.L, .D, .S, .R, .C} from rfl]
  simp

/-- **The number of patterns of a type is its multiplicity.** -/
theorem card_pat : ∀ t : PType, Fintype.card t.Pat = t.mult
  | L => rfl
  | D => rfl
  | S => rfl
  | R => rfl
  | C => rfl

end PType

/-! ## Field types (`def:two-coordinate-five-type`, `subsec:push:layer72spectral`) -/

/-- The three field types: the six-object root coordinate `L`, its three-object fold half `F`,
and the three-object matching coordinate `E`. -/
inductive FType where
  | L | F | E
  deriving DecidableEq

instance : Fintype FType where
  elems := {.L, .F, .E}
  complete := by intro x; cases x <;> decide

namespace FType

/-- The object set of a field type. -/
abbrev Obj : FType → Type
  | L => ZMod 6
  | F => Fin 3
  | E => Fin 3

instance instFintypeObj : ∀ f : FType, Fintype f.Obj
  | L => inferInstanceAs (Fintype (ZMod 6))
  | F => inferInstanceAs (Fintype (Fin 3))
  | E => inferInstanceAs (Fintype (Fin 3))

instance instDecidableEqObj : ∀ f : FType, DecidableEq f.Obj
  | L => inferInstanceAs (DecidableEq (ZMod 6))
  | F => inferInstanceAs (DecidableEq (Fin 3))
  | E => inferInstanceAs (DecidableEq (Fin 3))

/-- The relation and forward relation of a field type (`Sarkozy.Labellings.typeL`, `typeF`,
`typeE`). -/
def rel : ∀ f : FType, FieldType f.Obj
  | L => typeL
  | F => typeF
  | E => typeE

theorem rel_proper : ∀ f : FType, f.rel.Proper
  | L => typeL_proper
  | F => typeF_proper
  | E => typeE_proper

end FType

namespace PType

/-- The field type of a pattern type: `𝔣(L) = L`, `𝔣(D) = F`, `𝔣(S) = 𝔣(R) = 𝔣(C) = E`. -/
def field : PType → FType
  | L => .L
  | D => .F
  | S => .E
  | R => .E
  | C => .E

/-- **The pattern maps** `φ : ℤ/6ℤ → O_{𝔣(t)}` (`def:patterns`): the identity, the folds `F_j`,
the matchings `E_s`, the merges `G_{sk}` (values `0, 1`, read as the objects `0, 1`) and the
constant map `0`. -/
def pat : ∀ t : PType, t.Pat → ZMod 6 → t.field.Obj
  | L, _ => fun u => u
  | D, j => fold j
  | S, s => matching s
  | R, sk => fun u => (merge sk.1 sk.2 u).castSucc
  | C, _ => fun _ => (0 : Fin 3)

end PType

/-! ## Layers and emissions -/

/-- The layer of a slot as an element of the two-element layer set `{0, 1}` of the graphs. -/
def layerFin (ℓ : Layer) : Fin 2 := ⟨ℓ.val, ℓ.val_lt⟩

/-- **The middle emission** (`subsec:middle-reference-law`): under a pattern `φ` the slot
`(u₀, u₁, ℓ)` reads the label `y_{φ(u₀), ℓ}`, whatever `u₁` is. -/
def midEmission {O : Type*} (φ : ZMod 6 → O) (v : Slot) : O × Fin 2 := (φ v.1, layerFin v.2.2)

/-- The middle one-layer diagonal copy `Diag_ι`: the slot `(u₀, u₁, ℓ)` reads `y_{φ(u₀), 0}`. -/
def midDiagEmission {O : Type*} (φ : ZMod 6 → O) (v : Slot) : O × Fin 1 := (φ v.1, 0)

/-- **The upper emission** `e_φ` (`def:two-coordinate-five-type`):
`(u₀, u₁, ℓ) ↦ (φ₀(u₀), φ₁(u₁), ℓ)`. -/
def upEmission {O₀ O₁ : Type*} (φ₀ : ZMod 6 → O₀) (φ₁ : ZMod 6 → O₁) (v : Slot) :
    O₀ × O₁ × Fin 2 := (φ₀ v.1, φ₁ v.2.1, layerFin v.2.2)

/-- The upper one-layer diagonal copy: `(u₀, u₁, ℓ) ↦ (φ₀(u₀), φ₁(u₁), 0)`. -/
def upDiagEmission {O₀ O₁ : Type*} (φ₀ : ZMod 6 → O₀) (φ₁ : ZMod 6 → O₁) (v : Slot) :
    O₀ × O₁ × Fin 1 := (φ₀ v.1, φ₁ v.2.1, 0)

/-- The middle emissions forget the second chamber coordinate: they are fixed by every chamber
cut of the second coordinate. -/
theorem midEmission_secondCut {O : Type*} (φ : ZMod 6 → O) (a : Chamber) (v : Slot) :
    midEmission φ ((secondChamberCut a).flip v) = midEmission φ v := rfl

theorem midDiagEmission_secondCut {O : Type*} (φ : ZMod 6 → O) (a : Chamber) (v : Slot) :
    midDiagEmission φ ((secondChamberCut a).flip v) = midDiagEmission φ v := rfl

/-- The diagonal copies forget the layer: they are fixed by the reserved cut `ι`. -/
theorem midDiagEmission_reserved {O : Type*} (φ : ZMod 6 → O) (v : Slot) :
    midDiagEmission φ (reservedCut.flip v) = midDiagEmission φ v := rfl

theorem upDiagEmission_reserved {O₀ O₁ : Type*} (φ₀ : ZMod 6 → O₀) (φ₁ : ZMod 6 → O₁) (v : Slot) :
    upDiagEmission φ₀ φ₁ (reservedCut.flip v) = upDiagEmission φ₀ φ₁ v := rfl

/-! ## Images of laws under emissions -/

section Image

variable {I X : Type*} [Fintype I] [DecidableEq I] [Fintype X] [DecidableEq X]

/-- The image `Π` of a law on labellings of `I` under an emission `π : Slot → I`: the law of
`y ∘ π` for `y ∼ λ`. -/
noncomputable def emit (lam : FiniteLaw (I → X)) (π : Slot → I) : FiniteLaw (Slot → X) :=
  lam.map fun y => y ∘ π

theorem expect_emit (lam : FiniteLaw (I → X)) (π : Slot → I) (f : (Slot → X) → ℝ) :
    (emit lam π).expect f = lam.expect (fun y => f (y ∘ π)) := by
  unfold emit
  rw [FiniteLaw.expect_map]
  rfl

/-- The image's functional is the pullback of the law's functional along the emission. -/
theorem signedIntegral_emit (lam : FiniteLaw (I → X)) (π : Slot → I) :
    signedIntegral (emit lam π).weight =
      ReflectionCut.pullback (signedIntegral lam.weight) π := by
  apply LinearMap.ext
  intro f
  rw [← FiniteLaw.expect_eq_signedIntegral, expect_emit]
  rfl

/-- **An image whose emission is fixed by a cut is positive at that cut** (every configuration
is fixed by the reflection; `lem:commoncut`). -/
theorem emit_positive (lam : FiniteLaw (I → X)) (π : Slot → I) (c : ReflectionCut Slot)
    (hπ : ∀ v, π (c.flip v) = π v) : c.Positive (signedIntegral (emit lam π).weight) := by
  rw [signedIntegral_emit]
  exact ReflectionCut.pullback_positive_of_fixed c hπ fun f hf => lam.expect_nonneg hf

/-- **Images of laws with uniform vertex marginals have uniform slot marginals.** -/
theorem emit_uniform [Nonempty X] (lam : FiniteLaw (I → X)) (π : Slot → I)
    (hlam : ∀ (i : I) (g : X → ℝ), lam.expect (fun y => g (y i)) = (FiniteLaw.uniform X).expect g) :
    HasUniformMarginals (emit lam π) := by
  intro v g
  rw [expect_emit]
  exact hlam (π v) g

end Image

/-! ## Weighted completions -/

section Completion

variable {Idx Ω : Type*} [Fintype Idx] [Fintype Ω]

/-- The normalized weights `cᵢ / ∑ⱼ cⱼ` as a probability law on the index set. -/
noncomputable def normWeights (c : Idx → ℝ) (hc : ∀ i, 0 ≤ c i) (hpos : 0 < ∑ i, c i) :
    FiniteLaw Idx where
  weight i := c i / ∑ j, c j
  nonneg i := div_nonneg (hc i) hpos.le
  total := by rw [← sum_div, div_self hpos.ne']

/-- **The weighted completion** `∑ᵢ cᵢ Πᵢ / ∑ᵢ cᵢ` of the probability laws `Πᵢ` with
nonnegative weights `cᵢ`; the unnormalized measure `∑ᵢ cᵢ Πᵢ` has mass `∑ᵢ cᵢ`. -/
noncomputable def weightedCompletion (c : Idx → ℝ) (hc : ∀ i, 0 ≤ c i) (hpos : 0 < ∑ i, c i)
    (comp : Idx → FiniteLaw Ω) : FiniteLaw Ω :=
  FiniteLaw.mixture (normWeights c hc hpos) comp

/-- The unnormalized completion `μ̃ = ∑ᵢ cᵢ Πᵢ`, as a functional. -/
noncomputable def tildeMeasure (c : Idx → ℝ) (comp : Idx → FiniteLaw Ω) : (Ω → ℝ) →ₗ[ℝ] ℝ :=
  ∑ i, c i • signedIntegral (comp i).weight

/-- `μ̃(1) = ∑ᵢ cᵢ`. -/
theorem tildeMeasure_mass (c : Idx → ℝ) (comp : Idx → FiniteLaw Ω) :
    tildeMeasure c comp (fun _ => 1) = ∑ i, c i := by
  unfold tildeMeasure
  rw [LinearMap.sum_apply]
  refine sum_congr rfl fun i _ => ?_
  rw [LinearMap.smul_apply, ← FiniteLaw.expect_eq_signedIntegral, FiniteLaw.expect_const,
    smul_eq_mul, mul_one]

theorem expect_weightedCompletion (c : Idx → ℝ) (hc : ∀ i, 0 ≤ c i) (hpos : 0 < ∑ i, c i)
    (comp : Idx → FiniteLaw Ω) (f : Ω → ℝ) :
    (weightedCompletion c hc hpos comp).expect f = (∑ i, c i * (comp i).expect f) / ∑ i, c i := by
  unfold weightedCompletion
  rw [FiniteLaw.expect_mixture]
  unfold FiniteLaw.expect normWeights
  simp only
  rw [sum_div]
  refine sum_congr rfl fun i _ => ?_
  ring

/-- **The normalized law is `μ̃ / μ̃(1)`.** -/
theorem signedIntegral_weightedCompletion (c : Idx → ℝ) (hc : ∀ i, 0 ≤ c i)
    (hpos : 0 < ∑ i, c i) (comp : Idx → FiniteLaw Ω) :
    signedIntegral (weightedCompletion c hc hpos comp).weight =
      (∑ i, c i)⁻¹ • tildeMeasure c comp := by
  apply LinearMap.ext
  intro f
  rw [← FiniteLaw.expect_eq_signedIntegral, expect_weightedCompletion, LinearMap.smul_apply,
    smul_eq_mul]
  unfold tildeMeasure
  rw [LinearMap.sum_apply, div_eq_inv_mul]
  congr 1

/-- The unnormalized completion is a nonnegative measure. -/
theorem tildeMeasure_nonneg (c : Idx → ℝ) (hc : ∀ i, 0 ≤ c i) (comp : Idx → FiniteLaw Ω)
    (f : Ω → ℝ) (hf : ∀ ω, 0 ≤ f ω) : 0 ≤ tildeMeasure c comp f := by
  unfold tildeMeasure
  rw [LinearMap.sum_apply]
  refine sum_nonneg fun i _ => ?_
  rw [LinearMap.smul_apply, smul_eq_mul, ← FiniteLaw.expect_eq_signedIntegral]
  exact mul_nonneg (hc i) ((comp i).expect_nonneg hf)

/-- **Uniform one-slot marginals pass to the completion.** -/
theorem weightedCompletion_uniform {X : Type*} [Fintype X] [DecidableEq X] [Nonempty X]
    (c : Idx → ℝ) (hc : ∀ i, 0 ≤ c i) (hpos : 0 < ∑ i, c i)
    (comp : Idx → FiniteLaw (Slot → X)) (hcomp : ∀ i, HasUniformMarginals (comp i)) :
    HasUniformMarginals (weightedCompletion c hc hpos comp) := by
  intro v g
  rw [expect_weightedCompletion]
  simp_rw [hcomp _ v g]
  rw [← sum_mul]
  field_simp

/-- **Reflection positivity at a cut passes to the completion** when every component is
positive there (nonnegative combinations of positive functionals). -/
theorem weightedCompletion_positive {X : Type*} [Fintype X] [DecidableEq X]
    (c : Idx → ℝ) (hc : ∀ i, 0 ≤ c i) (hpos : 0 < ∑ i, c i)
    (comp : Idx → FiniteLaw (Slot → X)) (cut : ReflectionCut Slot)
    (hcomp : ∀ i, cut.Positive (signedIntegral (comp i).weight)) :
    cut.Positive (signedIntegral (weightedCompletion c hc hpos comp).weight) := by
  rw [signedIntegral_weightedCompletion]
  refine ReflectionCut.Positive.smul ?_ (inv_nonneg.mpr hpos.le)
  unfold tildeMeasure
  exact ReflectionCut.Positive.sum _ fun i _ => (hcomp i).smul (hc i)

end Completion

end Sarkozy.PartV
