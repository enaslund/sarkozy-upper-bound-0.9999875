module

public import Sarkozy.EnvelopeSteps.PaperEnergy
public import Sarkozy.SignedComponents.OptNorm

@[expose] public section

/-!
# The record operators `Δ̂` and the per-record identity of (N4) (OPS-L)

`paper/sections/23_envelopes.tex`, `subsec:envelope-tools` ("the normalized skew change
`Δ̂_{φ,𝔅}` is the cut operator of `ζ^a_{𝔅,φ}` at `ι`, relative to `m_{φ,𝔅}`, divided by the
raw-arm coefficient"), the star form (N1)–(N4); `paper/sections/21_middle_records.tex`,
`prop:signed-bounds`.

* **`recOp c m ζ`**: the cut operator of a signed law `ζ` on labellings `V → X` relative to a
  half marginal `m`: `(K g)(x) = m(x)⁻¹ ∑_y ζ(join(x, y)) g(y)`. It is the paper's `Δ̂` before
  the division by the raw-arm coefficient.
* `PlusIn m ζ`: `ζ` charges no labelling whose plus half is outside the support of `m` (B8's
  `HalvesIn` gives it for the middle records and their replacements).
* **`kern_recOp`**, **`place_recOp`**: under `PlusIn`, `[recOp ζ]_{id} = ζ`: the record is the
  placement of its operator (`subsec:reflection-averaging`, "Record assignments and placed
  measures").
* **`ip_recOp`**: `⟨F, recOp ζ G⟩_m = Q_ζ(F, G)`, so B8's `FormBound c m ζ C` is the operator norm
  bound `‖recOp ζ‖ ≤ C` in `L²(m)` (**`formLE_of_formBound`**). In particular the 24 middle norm
  bounds give `‖Δ̂_𝔅‖ ≤ ℓ_𝔅 + ρ_𝔅` (the joint bound) but not the split `‖L‖ ≤ ℓ`,
  `‖Δ̂ − L‖ ≤ ρ` of (N1), which needs the leading star `L` as an operator.
* **`record_eq_place`**: the per-record identity `ζ_{ω(𝔅),𝔅} = w_𝔅 [Δ̂_𝔅]` of `hN4_of_records`
  with `Δ̂_𝔅 = w_𝔅⁻¹ recOp ζ`, for every `w_𝔅 ≠ 0`.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.OpsCore

open Sarkozy.EnvelopeSteps Sarkozy.SignedComponents

variable {V X : Type*} [Fintype V] [DecidableEq V] [Fintype X] [DecidableEq X]
  (c : ReflectionCut V)

/-- **The cut operator of a signed law relative to a half marginal**:
`(recOp ζ g)(x) = m(x)⁻¹ ∑_y ζ(join(x, y)) g(y)`. -/
noncomputable def recOp (m : (c.Half → X) → ℝ) (ζ : ((V → X) → ℝ) →ₗ[ℝ] ℝ) :
    ((c.Half → X) → ℝ) →ₗ[ℝ] ((c.Half → X) → ℝ) where
  toFun g x := (m x)⁻¹ * ∑ y, lawDensity ζ (c.join x y) * g y
  map_add' g g' := by
    funext x
    simp only [Pi.add_apply, mul_add, sum_add_distrib]
  map_smul' a g := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_sum]
    refine sum_congr rfl fun y _ => by ring

/-- `ζ` charges only labellings whose plus half lies in the support of `m`. -/
def PlusIn (m : (c.Half → X) → ℝ) (ζ : ((V → X) → ℝ) →ₗ[ℝ] ℝ) : Prop :=
  ∀ x y, m x = 0 → lawDensity ζ (c.join x y) = 0

variable {c}

omit [Fintype X] in
/-- B8's `HalvesIn` for every charged labelling gives `PlusIn`. -/
theorem plusIn_of_halves {m : (c.Half → X) → ℝ} {ζ : ((V → X) → ℝ) →ₗ[ℝ] ℝ}
    (h : ∀ z, lawDensity ζ z ≠ 0 → HalvesIn (c := c) m z) : PlusIn c m ζ := by
  intro x y hx
  by_contra hne
  have h1 := (h _ hne).1
  have e : plusHalf (c := c) (c.join x y) = x := by
    funext v
    exact c.join_plus x y v
  rw [e, hx] at h1
  exact lt_irrefl _ h1

/-- **The kernel of the record operator is the record's matrix** (under `PlusIn`). -/
theorem kern_recOp {m : (c.Half → X) → ℝ} {ζ : ((V → X) → ℝ) →ₗ[ℝ] ℝ} (hζ : PlusIn c m ζ)
    (x y : c.Half → X) : kern m (recOp c m ζ) x y = lawDensity ζ (c.join x y) := by
  unfold kern
  change m x * ((m x)⁻¹ * ∑ z, lawDensity ζ (c.join x z) * EnvelopeSteps.delta y z) = _
  have hs : ∑ z, lawDensity ζ (c.join x z) * EnvelopeSteps.delta y z =
      lawDensity ζ (c.join x y) := by
    simp only [EnvelopeSteps.delta, mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ,
      ↓reduceIte]
  rw [hs]
  by_cases hx : m x = 0
  · rw [hx, hζ x y hx]
    simp
  · field_simp

/-- **The record is the placement of its operator**: `[recOp ζ]_{id} = ζ` (under `PlusIn`). -/
theorem place_recOp {m : (c.Half → X) → ℝ} {ζ : ((V → X) → ℝ) →ₗ[ℝ] ℝ} (hζ : PlusIn c m ζ) :
    place c m id (recOp c m ζ) = ζ := by
  refine LinearMap.ext fun Φ => ?_
  change ∑ q : (c.Half → X) × (c.Half → X), kern m (recOp c m ζ) q.1 q.2 *
      Φ (c.join (id q.1) (id q.2)) = ζ Φ
  rw [linearFunctional_density ζ Φ]
  simp only [kern_recOp hζ, id]
  refine Fintype.sum_equiv c.configurationEquiv.symm _ _ fun q => ?_
  rfl

/-- **The bilinear form of the record operator is the record's cut form** (under `PlusIn`). -/
theorem ip_recOp {m : (c.Half → X) → ℝ} {ζ : ((V → X) → ℝ) →ₗ[ℝ] ℝ} (hζ : PlusIn c m ζ)
    (F G : (c.Half → X) → ℝ) : ip m F (recOp c m ζ G) = c.form ζ F G := by
  have h := form_place c m id (recOp c m ζ) F G
  rw [place_recOp hζ] at h
  rw [h]
  rfl

/-- **The operator norm bound in `L²(m)`**: `|⟨F, K G⟩_m| ≤ C ‖F‖_m ‖G‖_m`, `C ≥ 0`. -/
def FormLE {O : Type*} [Fintype O] (m : O → ℝ) (K : (O → ℝ) →ₗ[ℝ] (O → ℝ)) (C : ℝ) : Prop :=
  0 ≤ C ∧ ∀ F G, |ip m F (K G)| ≤ C * Real.sqrt (ip m F F) * Real.sqrt (ip m G G)

/-- **B8's `FormBound` of a record is the operator norm bound of its record operator**
(`prop:signed-bounds` as a bound on `‖Δ̂‖`). -/
theorem formLE_of_formBound {m : (c.Half → X) → ℝ} {ζ : ((V → X) → ℝ) →ₗ[ℝ] ℝ}
    (hζ : PlusIn c m ζ) {C : ℝ} (h : FormBound c m ζ C) : FormLE m (recOp c m ζ) C := by
  refine ⟨h.1, fun F G => ?_⟩
  rw [ip_recOp hζ]
  exact h.2 F G

/-- The converse: an operator norm bound of the record operator is B8's `FormBound`. -/
theorem formBound_of_formLE {m : (c.Half → X) → ℝ} {ζ : ((V → X) → ℝ) →ₗ[ℝ] ℝ}
    (hζ : PlusIn c m ζ) {C : ℝ} (h : FormLE m (recOp c m ζ) C) : FormBound c m ζ C := by
  refine ⟨h.1, fun F G => ?_⟩
  rw [← ip_recOp hζ]
  exact h.2 F G

/-- **The per-record identity of (N4)**: with `Δ̂ = w⁻¹ recOp ζ` (the cut operator divided by the
raw-arm coefficient `w ≠ 0`), `ζ = w [Δ̂]_{id}`. -/
theorem record_eq_place {m : (c.Half → X) → ℝ} {ζ : ((V → X) → ℝ) →ₗ[ℝ] ℝ}
    (hζ : PlusIn c m ζ) {w : ℝ} (hw : w ≠ 0) :
    ζ = w • place c m id (w⁻¹ • recOp c m ζ) := by
  rw [place_smul, smul_smul, mul_inv_cancel₀ hw, one_smul, place_recOp hζ]

end Sarkozy.OpsCore
