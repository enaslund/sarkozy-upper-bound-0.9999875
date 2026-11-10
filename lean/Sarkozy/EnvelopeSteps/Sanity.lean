module

public import Sarkozy.EnvelopeSteps.Constructor
public import Sarkozy.Slots
public import Sarkozy.EnvelopeSteps.FeatureCorr

@[expose] public section

/-!
# Non-vacuity checks for `EnvelopeSteps`

* `massE`, `massE_P5`: the total-mass energy `κ ↦ Y_κ[1]` has (P5) (with `Eλ = EN`), so `P5` is
  satisfiable.
* **`toyDegreeOps`**: a one-selection degree class at the reserved cut with a nontrivial leading
  operator `L = I/2`, remainder `Υ = I/4` (`υ = 1/4`) and envelope `D = I/2`; every field of
  `DegreeOps` is checked, and the class bound of B10's `EnvStepsAt.bound` is tight
  (`toy_bound`: `3/4 ≤ 1/2 + 1/4`).
* **`toyStar_mask`**: the hypotheses of `mask_lift` hold for the one-arm star `T = e₀₁ + e₁₀`
  (arm norm `1`) with the diagonal envelope `D = I` (the one-factor case `d_c d_a ≥ α²` of
  `eq:oct24:mask-schur`) and `c = 1`; the conclusion `D ± T ⪰ 0` is then not vacuous.
* **`corr12_toy`**: the hypotheses of `corr12_actual` (`lem:oct24:feature-block`(a), edge `12`)
  hold at the one-prime block `𝔽₇`, `c = 1`.
-/

open Finset Matrix
open scoped BigOperators Kronecker

namespace Sarkozy.EnvelopeSteps

open Sarkozy.ClassInputsPaper

section Mass

variable {V X : Type*} [Fintype V] [DecidableEq V]

/-- The total-mass energy `κ ↦ Y_κ[1] = κ(1)`. -/
noncomputable def massE : (((V → X) → ℝ) →ₗ[ℝ] ℝ) →ₗ[ℝ] ℝ where
  toFun κ := diagonalIntegral κ (fun _ => 1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem massE_P5 (c : ReflectionCut V) : P5 c (massE (X := X)) massE := by
  intro κ ζ hp hm
  have h1 : 0 ≤ massE (κ + ζ) := hp.diagonal_nonneg (fun _ => 1)
  have h2 : 0 ≤ massE (κ - ζ) := hm.diagonal_nonneg (fun _ => 1)
  rw [map_add] at h1
  rw [map_sub] at h2
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end Mass

/-- The total mass of the placement of `k I` with one object of weight `1`. -/
theorem massE_place_unit {V X : Type*} [Fintype V] [DecidableEq V] (c : ReflectionCut V)
    (φ : Unit → (c.Half → X)) (k : ℝ) :
    massE (place c (fun _ => (1 : ℝ)) φ (k • LinearMap.id)) = k := by
  change (∑ q : Unit × Unit, kern (fun _ => (1 : ℝ)) (k • LinearMap.id) q.1 q.2 *
    ∏ _v : V, (1 : ℝ)) = k
  simp [kern, delta]

theorem opPos_smul_id {O : Type*} [Fintype O] {m : O → ℝ} (hm : ∀ x, 0 ≤ m x) {k : ℝ}
    (hk : 0 ≤ k) : OpPos m (k • LinearMap.id) :=
  (opPos_id hm).smul hk

/-- **A toy degree class**: one selection, `I = 3/4`, `L = I/2`, `Υ = I/4`, `D = I/2`. -/
noncomputable def toyDegreeOps :
    DegreeOps reservedCut ({()} : Finset Unit) (fun _ => 3 / 4) (fun _ => 1) (fun _ => 1 / 4)
      (fun _ => 0) (1 / 2) 1 0 3 where
  Obj _ := Unit
  instFO _ := inferInstance
  instDO _ := inferInstance
  Lab _ := Unit
  instFL _ := inferInstance
  instDL _ := inferInstance
  Elam _ := massE
  EN _ := massE
  hE _ _ := massE_P5 reservedCut
  m _ _ := 1
  φ _ _ _ := ()
  Lop _ := (1 / 2 : ℝ) • LinearMap.id
  Υop _ := (1 / 4 : ℝ) • LinearMap.id
  Dop _ := (1 / 2 : ℝ) • LinearMap.id
  hdom _ _ := by
    have h1 : (1 / 2 : ℝ) • (LinearMap.id : (Unit → ℝ) →ₗ[ℝ] (Unit → ℝ)) -
        (1 / 2 : ℝ) • LinearMap.id = (0 : ℝ) • LinearMap.id := by rw [sub_self, zero_smul]
    have h2 : (1 / 2 : ℝ) • (LinearMap.id : (Unit → ℝ) →ₗ[ℝ] (Unit → ℝ)) -
        -((1 / 2 : ℝ) • LinearMap.id) = (1 : ℝ) • LinearMap.id := by
      rw [sub_neg_eq_add, ← add_smul]; norm_num
    refine ⟨?_, ?_⟩
    · unfold OpLE; rw [h1]; exact opPos_smul_id (fun _ => zero_le_one) le_rfl
    · unfold OpLE; rw [h2]; exact opPos_smul_id (fun _ => zero_le_one) zero_le_one
  υ _ := 1 / 4
  hυ _ _ := by norm_num
  hΥsym _ _ f g := by
    unfold ip
    simp only [LinearMap.smul_apply, LinearMap.id_apply, Pi.smul_apply, smul_eq_mul]
    exact sum_congr rfl fun _ _ => by ring
  hΥ _ _ f := by
    have e : ip (fun _ : Unit => (1 : ℝ)) f (((1 / 4 : ℝ) •
        (LinearMap.id : (Unit → ℝ) →ₗ[ℝ] (Unit → ℝ))) f) =
        1 / 4 * ip (fun _ => 1) f f := by
      simp only [LinearMap.smul_apply, LinearMap.id_apply, ip_smul_right]
    have h0 : 0 ≤ ip (fun _ : Unit => (1 : ℝ)) f f :=
      sum_nonneg fun _ _ => by simp only [one_mul]; exact mul_self_nonneg _
    rw [e, abs_of_nonneg (by positivity)]
  B := 1
  CX _ := 1
  r₁' _ := 0
  hE1 _ _ := by
    rw [← place_id, ← one_smul ℝ (LinearMap.id : (Unit → ℝ) →ₗ[ℝ] (Unit → ℝ)),
      massE_place_unit]
    norm_num
  wt _ := 1
  hwt _ _ := zero_le_one
  hI _ _ := by
    rw [massE_place_unit, massE_place_unit]
    norm_num
  YN0 _ := 1 / 2
  Mω _ := 0
  Mh _ := 0
  r₃ _ := 0
  r₄ := 0
  M := 0
  Minv := 0
  Rerr := 0
  tU := 0
  tδ := 0
  hR := le_rfl
  htδ := le_rfl
  step3 _ _ := by
    rw [massE_place_unit]
    norm_num
  step4 := by simp
  hM := by simp
  hMinv := by simp
  hρ := by simp
  hπ _ _ := by norm_num
  hrr := by simp

/-- The class bound of the toy class is tight: `|I| = 3/4 ≤ W_Z + ρ Y = 1/2 + 1/4`. -/
theorem toy_bound :
    ∑ ω ∈ ({()} : Finset Unit), |(fun _ : Unit => (3 / 4 : ℝ)) ω| ≤
      1 / 2 + ∑ ω ∈ ({()} : Finset Unit),
        (((fun _ : Unit => (1 / 4 : ℝ)) ω + 0 * 3 * (fun _ : Unit => (1 : ℝ)) ω) * 1 +
          (fun _ : Unit => (0 : ℝ)) ω) :=
  toyDegreeOps.toEnvSteps.bound zero_le_one le_rfl

/-! ## The one-arm star -/

/-- The one-arm star `e₀₁ + e₁₀` on `Fin 2 × Unit`. -/
def toyStar : Matrix (Fin 2 × Unit) (Fin 2 × Unit) ℝ := fun i j => if i.1 = j.1 then 0 else 1

/-- **The hypotheses of `mask_lift` for the one-arm star** with `D = I`, `c = 1`, `Ξ = I`,
`Lift = D ⊗ I`. -/
theorem toyStar_mask :
    ((1 : Matrix (Fin 2) (Fin 2) ℝ) ⊗ₖ (1 : Matrix Unit Unit ℝ) + toyStar).PosSemidef ∧
    ((1 : Matrix (Fin 2) (Fin 2) ℝ) ⊗ₖ (1 : Matrix Unit Unit ℝ) - toyStar).PosSemidef := by
  have hv := posSemidef_vecMulVec_self_star (fun _ : Fin 2 × Unit => (1 : ℝ))
  have hw := posSemidef_vecMulVec_self_star
    (fun i : Fin 2 × Unit => if i.1 = 0 then (1 : ℝ) else -1)
  refine ⟨?_, ?_⟩
  · convert hv using 1
    ext ⟨i, u⟩ ⟨j, v⟩
    fin_cases i <;> fin_cases j <;> simp [toyStar, vecMulVec, one_apply]
  · convert hw using 1
    ext ⟨i, u⟩ ⟨j, v⟩
    fin_cases i <;> fin_cases j <;> simp [toyStar, vecMulVec, one_apply]

/-- `mask_lift` at the one-arm star: `Lift ± T ⪰ 0`. -/
theorem toyStar_lift :
    (((1 : Matrix (Fin 2) (Fin 2) ℝ) ⊗ₖ (1 : Matrix Unit Unit ℝ)) +
        ∑ _s : Unit, (1 : ℝ) • ((1 : Matrix (Fin 2 × Unit) (Fin 2 × Unit) ℝ) * toyStar *
          (1 : Matrix (Fin 2 × Unit) (Fin 2 × Unit) ℝ)ᴴ)).PosSemidef ∧
    (((1 : Matrix (Fin 2) (Fin 2) ℝ) ⊗ₖ (1 : Matrix Unit Unit ℝ)) -
        ∑ _s : Unit, (1 : ℝ) • ((1 : Matrix (Fin 2 × Unit) (Fin 2 × Unit) ℝ) * toyStar *
          (1 : Matrix (Fin 2 × Unit) (Fin 2 × Unit) ℝ)ᴴ)).PosSemidef := by
  refine mask_lift (Z := fun _ : Unit => Unit) (1 : Matrix (Fin 2) (Fin 2) ℝ)
    (fun _ => toyStar) (fun _ => 1) (fun _ => zero_le_one) (fun _ => le_rfl)
    (fun _ => toyStar_mask) (fun _ => 1) _ ?_
  simp only [Matrix.one_mul, conjTranspose_one, Matrix.mul_one, Finset.univ_unique,
    Finset.sum_singleton, sub_self]
  exact PosSemidef.zero

/-! ## The block correlation at a toy block -/

instance fact_prime_seven : Fact (Nat.Prime 7) := ⟨by norm_num⟩

theorem r01sq_seven : r01sq 7 ≤ 1 ^ 2 := by
  unfold r01sq
  norm_num

/-- **The hypotheses of `corr12_actual` hold** at the one-prime block `𝔽₇` with `c = 1`
(`ϱ₀₁(7)² = 37/324`). -/
theorem corr12_toy (f g : (Unit → ZMod 7) → ℝ) (hg : ∑ v, Mixing.prodW unifB v * g v = 0) :
    |∑ x : Unit → ZMod 7 × ZMod 7 × ZMod 7, m0B x * f (fun p => (x p).2.1) * g (fun p => (x p).2.2)|
      ≤ 1 * (Real.sqrt (∑ u, Mixing.prodW unifB u * f u ^ 2) *
        Real.sqrt (∑ v, Mixing.prodW unifB v * g v ^ 2)) := by
  have hc : (Fintype.card (ZMod 7) : ℝ) = 7 := by rw [ZMod.card]; norm_num
  refine corr12_actual (F := fun _ : Unit => ZMod 7) (fun _ => ?_) (fun _ => ?_) (fun _ => ?_)
    zero_le_one le_rfl (fun _ => ?_) f g hg
  · rw [ZMod.ringChar_zmod_n]
    norm_num
  · rw [ZMod.card]
  · rw [hc]
  · rw [hc]
    exact r01sq_seven

end Sarkozy.EnvelopeSteps
