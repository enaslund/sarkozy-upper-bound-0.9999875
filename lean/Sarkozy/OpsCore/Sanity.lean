module

public import Sarkozy.OpsCore.Evals

@[expose] public section

/-!
# Non-vacuity checks for OPS-L

* `tensorOp_smul_id`: `⊗_b (c_b I) = (∏ c_b) I`.
* **`star_tensor_error_tight`**: at one block with `L = ℓ I`, `E = ρ I`, the error is exactly
  `ρ I = ((ℓ + ρ) − ℓ) I`, so `star_tensor_error` is attained and its hypotheses hold
  (`opNormLE_smul_id`).
* `plusIn_one`: at the marginal `m ≡ 1` every law satisfies `PlusIn`, so `place_recOp` applies to
  every law (`place_recOp_one`).
* **`leadOK_zero`**: at the paper's comparison data, `LeadOK` holds for **every** selection with the
  zero leading star, `w = 1` and `ρ_𝔅 = π̃_{ω(𝔅)}` (from (CP3), `formLE_sel`). Then `Υ_ω = ⊗ Δ̂`
  and Step 1 alone gives the trivial bound `|I_ω| ≤ (B + z) π_ω Y`: the star-form inputs are
  consistent at the paper's data, and the content of `LeadOK` is the improvement, a leading star
  with a small remainder (`prop:signed-bounds`(b)).
-/

open Finset
open scoped BigOperators

namespace Sarkozy.OpsCore

open Sarkozy.EnvelopeSteps

section Tensor

variable {S : Type*} [Fintype S] [DecidableEq S] {O : S → Type*} [∀ j, Fintype (O j)]
  [∀ j, DecidableEq (O j)]

/-- `⊗_b (c_b I) = (∏ c_b) I`. -/
theorem tensorOp_smul_id (c : S → ℝ) :
    tensorOp (fun b => c b • (LinearMap.id : (O b → ℝ) →ₗ[ℝ] (O b → ℝ))) =
      (∏ b, c b) • LinearMap.id := by
  refine linearMap_ext_delta fun x y => ?_
  rw [tensorOp_delta]
  simp only [LinearMap.smul_apply, LinearMap.id_apply, Pi.smul_apply, smul_eq_mul,
    EnvelopeSteps.delta]
  rw [prod_mul_distrib]
  congr 1
  by_cases h : x = y
  · subst h
    simp
  · obtain ⟨b, hb⟩ : ∃ b, x b ≠ y b := by
      by_contra hc
      exact h (funext fun b => not_not.mp fun hb => hc ⟨b, hb⟩)
    simp only [h, ↓reduceIte]
    exact prod_eq_zero (mem_univ b) (by simp [hb])

theorem opNormLE_smul_id {Q : Type*} [Fintype Q] {m : Q → ℝ} {c : ℝ} (hc : 0 ≤ c) :
    OpNormLE m (c • (LinearMap.id : (Q → ℝ) →ₗ[ℝ] (Q → ℝ))) c := by
  refine ⟨hc, fun g => le_of_eq ?_⟩
  unfold ip
  rw [mul_sum]
  refine sum_congr rfl fun x _ => ?_
  simp only [LinearMap.smul_apply, LinearMap.id_apply, Pi.smul_apply, smul_eq_mul]
  ring

end Tensor

/-- **`star_tensor_error` is attained**: at one block, `L = ℓ I` and `E = ρ I` (`ℓ, ρ ≥ 0`)
satisfy its norm hypotheses, and `⟨f, Υ f⟩ = ((ℓ + ρ) − ℓ) ‖f‖²`. -/
theorem star_tensor_error_tight {Q : Type} [Fintype Q] [DecidableEq Q] {m : Q → ℝ} {ℓ ρ : ℝ}
    (hℓ : 0 ≤ ℓ) (hρ : 0 ≤ ρ)
    (f : (∀ _ : Unit, Q) → ℝ) :
    (∀ _ : Unit, OpNormLE m (ℓ • (LinearMap.id : (Q → ℝ) →ₗ[ℝ] (Q → ℝ))) ℓ) ∧
    (∀ _ : Unit, OpNormLE m (ρ • (LinearMap.id : (Q → ℝ) →ₗ[ℝ] (Q → ℝ))) ρ) ∧
    ip (prodWeight fun _ : Unit => m) f
        (((tensorOp (O := fun _ : Unit => Q) (fun _ => ℓ • LinearMap.id + ρ • LinearMap.id) -
          tensorOp (O := fun _ : Unit => Q) (fun _ => ℓ • LinearMap.id) :
            ((∀ _ : Unit, Q) → ℝ) →ₗ[ℝ] ((∀ _ : Unit, Q) → ℝ))) f) =
      ((∏ _ : Unit, (ℓ + ρ)) - ∏ _ : Unit, ℓ) * ip (prodWeight fun _ : Unit => m) f f := by
  refine ⟨fun _ => opNormLE_smul_id hℓ, fun _ => opNormLE_smul_id hρ, ?_⟩
  have e1 : (fun _ : Unit => ℓ • (LinearMap.id : (Q → ℝ) →ₗ[ℝ] (Q → ℝ)) + ρ • LinearMap.id) =
      fun _ => (ℓ + ρ) • LinearMap.id := funext fun _ => (add_smul ℓ ρ _).symm
  rw [e1, tensorOp_smul_id (O := fun _ : Unit => Q) (fun _ => ℓ + ρ),
    tensorOp_smul_id (O := fun _ : Unit => Q) (fun _ => ℓ), LinearMap.sub_apply,
    LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.id_apply, ip_sub_right, ip_smul_right,
    ip_smul_right]
  ring

variable {V X : Type*} [Fintype V] [DecidableEq V] [Fintype X] [DecidableEq X]
  (c : ReflectionCut V)

omit [Fintype X] in
/-- At the marginal `m ≡ 1` every law satisfies `PlusIn`. -/
theorem plusIn_one (ζ : ((V → X) → ℝ) →ₗ[ℝ] ℝ) : PlusIn c (fun _ => 1) ζ :=
  fun _ _ h => absurd h one_ne_zero

/-- So every law is the placement of its record operator at `m ≡ 1`. -/
theorem place_recOp_one (ζ : ((V → X) → ℝ) →ₗ[ℝ] ℝ) :
    place c (fun _ => 1) id (recOp c (fun _ => 1) ζ) = ζ :=
  place_recOp (plusIn_one c ζ)

section Zero

open Sarkozy.ClassInputsPaper Sarkozy.ClassBoundsPaper Sarkozy.TheoremC Sarkozy.TheoremCBlock
  Sarkozy.BlockFrame Sarkozy.RecordExpansion Sarkozy.RecordExpansion.Choice

theorem OpNormLE.smul {Q : Type*} [Fintype Q] {m : Q → ℝ} {K : (Q → ℝ) →ₗ[ℝ] (Q → ℝ)} {a c : ℝ}
    (h : OpNormLE m K a) (hc : 0 ≤ c) : OpNormLE m (c • K) (c * a) := by
  refine ⟨mul_nonneg hc h.1, fun g => ?_⟩
  simp only [LinearMap.smul_apply]
  have e : ip m (c • K g) (c • K g) = c ^ 2 * ip m (K g) (K g) := by
    unfold ip
    rw [mul_sum]
    refine sum_congr rfl fun x _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  rw [e, mul_pow, mul_assoc]
  exact mul_le_mul_of_nonneg_left (h.2 g) (sq_nonneg c)

variable {a' : ℝ}
  {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

/-- The trivial leading data: no leading star, `w = 1`, `ℓ = 0`, `ρ = π̃`. -/
noncomputable def leadZero (D : TheoremCBlock.ComparisonData a' m₀ blk p pr h E) (L : ℕ)
    (ω : Choice (D.CL.T L)) : LeadData D L ω where
  w _ := 1
  Lb _ := 0
  ℓ _ := 0
  ρ b := selPrice D L ω b.1

omit [DecidableEq P] in
/-- **`LeadOK` holds at the paper's data with the zero leading star** (non-vacuity). -/
theorem leadOK_zero (D : TheoremCBlock.ComparisonData a' m₀ blk p pr h E) (L : ℕ)
    (ω : Choice (D.CL.T L)) : LeadOK (leadZero D L ω) where
  hw _ := one_pos
  hL _ := ⟨le_rfl, fun g => by simp [ip, leadZero]⟩
  hE b := by
    have h1 := (formLE_sel D L ω b.1 b.2).opNormLE (selMarg_nonneg D L ω b.1)
    have h2 := h1.smul (c := (1 : ℝ)⁻¹) (by norm_num)
    change OpNormLE (selMarg D L ω b.1) ((1 : ℝ)⁻¹ • recOp reservedCut (selMarg D L ω b.1)
      (entryFactor (D.FS.lam L b.1) (D.CL.ζ L b.1) (ω b.1)) - 0) (selPrice D L ω b.1)
    rw [sub_zero]
    convert h2 using 1
    rw [inv_one, one_mul]
  hLs _ x y := by simp [kern, leadZero]

end Zero

end Sarkozy.OpsCore
