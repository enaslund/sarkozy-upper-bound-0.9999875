module

public import Sarkozy.FiveType.CutForms
public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Invariance, chamber transport and the inner-product bound (`lem:five-type`(a))

Source: `paper/sections/17_completion_repair.tex`, `lem:five-type`(a) and its proof;
`lem:record:fold-identification`(e) (the action of `𝒢₆` on the patterns, `tab:reflection`);
`lem:slot-array`(i) (chamber transport).

* `Datum.Q_inv6`: **`𝒬_a` is invariant under `𝒢₆`.** As in the paper: precomposition with
  `α ∈ 𝒢₆` permutes the folds (`fold_g6`), maps `E_s` to `ψ ∘ E_s` (`matching_g6`), permutes the
  merges of each partition (`merge_relabel`) and fixes the constant map; `Π_{ψ ∘ E_s}(π_E) =
  Π_{E_s}(π_E)` by exchangeability, and `Π_L` is invariant by (v). The permutation facts are
  checked for all six elements of `𝒢₆` by `decide`.
* `rpAll_of_inv6`: **chamber transport.** A `𝒢₆`-invariant functional that is reflection positive
  at `ϑ₀` is reflection positive at every `ϑ_i`, `i ∈ ℤ/6ℤ`: for each `i` some `α ∈ 𝒢₆` carries
  `H_i` into `H₀` and intertwines `ϑ_i` with `ϑ₀` (`cutMap_g6`, by `decide`), and the pullback
  along `α` is the functional itself.
* `form_symm_of_flip_inv`: a functional invariant under a cut reflection has a symmetric cut
  form.
* The last claim of (a): **`⟨Φ, TΨ⟩ ≥ E Φ E Ψ - e ‖Φ‖ ‖Ψ‖` when `‖T - J‖ ≤ e`.**
  `inner_lower_of_opNorm` proves it for every continuous linear operator `T` on any real inner
  product space, with `J Ψ = ⟨𝟙, Ψ⟩ 𝟙` (on `L²(ν^b)`, `⟨𝟙, Ψ⟩ = E_{ν^b} Ψ`); the true operator
  norm is used. `form_bound_of_opNorm` derives the form bound `|⟨Φ, AΨ⟩| ≤ ‖A‖ ‖Φ‖ ‖Ψ‖` used as
  the norm convention of `Datum.lean`; `NormBound.lower` is the claim in that convention.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.FiveType

open Sarkozy.Labellings

/-! ## The action of `𝒢₆` on the patterns -/

/-- Every element of `𝒢₆` permutes the folds. -/
theorem fold_g6 : ∀ k : Fin 6, ∃ σ : Equiv.Perm (Fin 3), ∀ j u, fold j (g6 k u) = fold (σ j) u := by
  decide

/-- Every element of `𝒢₆` maps each matching `E_s` to `ψ ∘ E_s`. -/
theorem matching_g6 :
    ∀ (k : Fin 6) (s : Fin 2), ∃ ψ : Equiv.Perm (Fin 3),
      ∀ u, matching s (g6 k u) = ψ (matching s u) := by
  decide

/-- The elements of `𝒢₆` are bijections. -/
theorem g6_bijective : ∀ k : Fin 6, Function.Bijective (g6 k) := by decide

/-- For every chamber cut `ϑ_i` some `α ∈ 𝒢₆` maps `H_i` into `H₀` and intertwines `ϑ_i`
with `ϑ₀`. -/
theorem cutMap_g6 : ∀ i : ZMod 6, ∃ k : Fin 6,
    (∀ v ∈ (chamberCut i).half, g6 k v ∈ (chamberCut 0).half) ∧
    ∀ v, g6 k ((chamberCut i).flip v) = (chamberCut 0).flip (g6 k v) := by
  decide

/-! ## Chamber transport -/

section Transport

variable {X : Type*}

/-- **Chamber transport** (`lem:slot-array`(i)): a `𝒢₆`-invariant functional that is reflection
positive at `ϑ₀` is reflection positive at every chamber cut. -/
theorem rpAll_of_inv6 {L : ((ZMod 6 → X) → ℝ) →ₗ[ℝ] ℝ} (hinv : Inv6 L)
    (h0 : (chamberCut 0).Positive L) : RPAll L := by
  intro i
  obtain ⟨k, hhalf, hflip⟩ := cutMap_g6 i
  have hcm : ReflectionCut.CutMap (chamberCut i) (chamberCut 0) (g6 k) := ⟨hhalf, hflip⟩
  have hp := h0.pullback hcm
  have he : ReflectionCut.pullback L (g6 k) = L := LinearMap.ext fun f => hinv k f
  rwa [he] at hp

/-- A functional invariant under the reflection of a cut has a symmetric cut form. -/
theorem form_symm_of_flip_inv {V : Type*} [Fintype V] [DecidableEq V] (c : ReflectionCut V)
    {L : ((V → X) → ℝ) →ₗ[ℝ] ℝ} (hL : ∀ f : (V → X) → ℝ, L (fun z => f (z ∘ c.flip)) = L f)
    (F G : (c.Half → X) → ℝ) : c.form L F G = c.form L G F := by
  have h := hL (fun z => G (fun v => z v.1) * F (fun v => z (c.flip v.1)))
  simp only [Function.comp_apply, c.flip_flip] at h
  change L (fun z => F (fun v => z v.1) * G (fun v => z (c.flip v.1))) =
    L (fun z => G (fun v => z v.1) * F (fun v => z (c.flip v.1)))
  rw [← h]
  congr 1
  funext z
  ring

/-- The element `u ↦ 5 - u` of `𝒢₆` is the reflection `ϑ₀`. -/
theorem g6_five_eq_flip : ∀ u, g6 5 u = (chamberCut 0).flip u := by decide

/-- A `𝒢₆`-invariant functional is invariant under the reflection `ϑ₀`. -/
theorem flip_inv_of_inv6 {L : ((ZMod 6 → X) → ℝ) →ₗ[ℝ] ℝ} (hinv : Inv6 L)
    (f : (ZMod 6 → X) → ℝ) : L (fun z => f (z ∘ (chamberCut 0).flip)) = L f := by
  have h := hinv 5 f
  have he : g6 5 = ⇑(chamberCut 0).flip := funext g6_five_eq_flip
  rwa [he] at h

theorem Inv6.add {L M : ((ZMod 6 → X) → ℝ) →ₗ[ℝ] ℝ} (hL : Inv6 L) (hM : Inv6 M) :
    Inv6 (L + M) := fun k f => by
  simp only [LinearMap.add_apply, hL k f, hM k f]

theorem Inv6.sub {L M : ((ZMod 6 → X) → ℝ) →ₗ[ℝ] ℝ} (hL : Inv6 L) (hM : Inv6 M) :
    Inv6 (L - M) := fun k f => by
  simp only [LinearMap.sub_apply, hL k f, hM k f]

theorem Inv6.smul {L : ((ZMod 6 → X) → ℝ) →ₗ[ℝ] ℝ} (hL : Inv6 L) (a : ℝ) : Inv6 (a • L) :=
  fun k f => by simp only [LinearMap.smul_apply, hL k f]

theorem Inv6.sum {I : Type*} (s : Finset I) {L : I → ((ZMod 6 → X) → ℝ) →ₗ[ℝ] ℝ}
    (h : ∀ i ∈ s, Inv6 (L i)) : Inv6 (∑ i ∈ s, L i) := fun k f => by
  simp only [LinearMap.sum_apply]
  exact Finset.sum_congr rfl fun i hi => h i hi k f

end Transport

/-! ## `𝒬_a` is `𝒢₆`-invariant -/

namespace Datum

variable {𝔛 : Type*} [Fintype 𝔛] [DecidableEq 𝔛] (D : Datum 𝔛)

/-- The root `Π_L` is `𝒢₆`-invariant, by (v). -/
theorem compL_inv6 : Inv6 D.compL := by
  intro k f
  obtain ⟨g, hg⟩ := (g6_bijective k)
  let e : ZMod 6 ≃ ZMod 6 := Equiv.ofBijective (g6 k) ⟨g, hg⟩
  change ∑ Ψ, D.piL.weight Ψ * f (Ψ ∘ g6 k) = ∑ Ψ, D.piL.weight Ψ * f Ψ
  rw [← Fintype.sum_equiv (Equiv.arrowCongr e.symm (Equiv.refl 𝔛))
    (fun Ψ => D.piL.weight (Ψ ∘ g6 k) * f (Ψ ∘ g6 k)) (fun Ψ => D.piL.weight Ψ * f Ψ)
    (fun _ => rfl)]
  exact Finset.sum_congr rfl fun Ψ _ => by rw [D.piL_inv]

/-- The folds are permuted by `𝒢₆`, so `π_D = ∑_j Π_{F_j}` is invariant. -/
theorem piD_inv6 : Inv6 (D.piT .D) := by
  intro k f
  obtain ⟨σ, hσ⟩ := fold_g6 k
  change (∑ j, D.compF j) (fun Ψ => f (Ψ ∘ g6 k)) = (∑ j, D.compF j) f
  simp only [LinearMap.sum_apply, compF, lawL_pattern]
  rw [← Equiv.sum_comp σ (fun j => D.piF.expect (fun ω => f (fun u => ω (fold j u))))]
  refine Finset.sum_congr rfl fun j _ => D.piF.expect_congr fun ω => ?_
  congr 1
  funext u
  simp only [Function.comp_apply, hσ]

/-- Each matching component is invariant: `E_s ∘ α = ψ ∘ E_s` and `π_E` is exchangeable. -/
theorem compE_inv6 (s : Fin 2) : Inv6 (D.compE s) := by
  intro k f
  obtain ⟨ψ, hψ⟩ := matching_g6 k s
  simp only [compE, lawL_pattern]
  rw [expect_perm D.piE ψ (D.piE_exch ψ) (fun ω => f (fun u => ω (matching s u)))]
  refine D.piE.expect_congr fun ω => ?_
  congr 1
  funext u
  simp only [Function.comp_apply, hψ]

/-- The merges of each partition are permuted by `𝒢₆`. -/
theorem merges_inv6 (s : Fin 2) : Inv6 (∑ k', D.compG s k') := by
  intro k f
  obtain ⟨ψ, hψ⟩ := matching_g6 k s
  simp only [LinearMap.sum_apply, compG, lawL_pattern]
  rw [← Equiv.sum_comp ψ.symm (fun k' => D.Gam.expect (fun ω => f (fun u => ω (merge s k' u))))]
  refine Finset.sum_congr rfl fun k' _ => D.Gam.expect_congr fun ω => ?_
  congr 1
  funext u
  simp only [Function.comp_apply, merge_relabel s (g6 k) ψ hψ k' u]

/-- The constant component is invariant. -/
theorem compC_inv6 : Inv6 D.compC := by
  intro k f
  simp only [compC, lawL_pattern]
  rfl

/-- Every type sum `π_t` is `𝒢₆`-invariant. -/
theorem piT_inv6 : ∀ t, Inv6 (D.piT t)
  | .L => D.compL_inv6
  | .D => D.piD_inv6
  | .S => Inv6.sum _ fun s _ => D.compE_inv6 s
  | .R => Inv6.sum _ fun s _ => D.merges_inv6 s
  | .C => Inv6.sum _ fun _ _ => D.compC_inv6

/-- **`lem:five-type`(a), first claim: `𝒬_a` is invariant under `𝒢₆`.** -/
theorem Q_inv6 (a : Ty → ℝ) : Inv6 (D.Q a) :=
  Inv6.sum _ fun t _ => (D.piT_inv6 t).smul (a t)

/-- `Π_{F_0}` is fixed samplewise by `ϑ₀` (`lem:record:fold-identification`(b)), so it is
invariant under the reflection. -/
theorem compF0_flip_inv (f : (ZMod 6 → 𝔛) → ℝ) :
    D.compF 0 (fun z => f (z ∘ (chamberCut 0).flip)) = D.compF 0 f := by
  simp only [compF, lawL_pattern]
  refine D.piF.expect_congr fun ω => ?_
  congr 1
  funext u
  have h := fold_chamberRefl 0 u
  have h5 : foldChamber 0 = 5 := by decide
  rw [h5] at h
  simp only [Function.comp_apply]
  rw [← g6_five_eq_flip]
  exact congrArg ω (by rw [← h]; rfl)

/-- `Π_{F_0}` is positive at `ϑ₀`: it is the diagonal copy `Diag_{ϑ₀}` of its half law
(`lem:record:fold-identification`(b), `lem:commoncut`(i)). -/
theorem compF0_positive : (chamberCut 0).Positive (D.compF 0) := by
  constructor
  · intro F G
    exact form_symm_of_flip_inv (chamberCut 0) D.compF0_flip_inv F G
  · intro F
    unfold compF
    rw [form_pattern]
    obtain ⟨h0, h1, h2, h5, h4, h3⟩ : fold 0 0 = 0 ∧ fold 0 1 = 1 ∧ fold 0 2 = 2 ∧
        fold 0 5 = 0 ∧ fold 0 4 = 1 ∧ fold 0 3 = 2 := by decide
    simp only [h0, h1, h2, h3, h4, h5]
    exact D.piF.expect_nonneg fun ω => mul_self_nonneg _

end Datum

/-! ## The last claim of (a) -/

section InnerProduct

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The form bound of an operator norm: `|⟨Φ, AΨ⟩| ≤ ‖A‖ ‖Φ‖ ‖Ψ‖`. -/
theorem form_bound_of_opNorm (A : E →L[ℝ] E) (Φ Ψ : E) :
    |inner ℝ Φ (A Ψ)| ≤ ‖A‖ * ‖Φ‖ * ‖Ψ‖ := by
  calc |inner ℝ Φ (A Ψ)| ≤ ‖Φ‖ * ‖A Ψ‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖Φ‖ * (‖A‖ * ‖Ψ‖) := by gcongr; exact A.le_opNorm Ψ
    _ = ‖A‖ * ‖Φ‖ * ‖Ψ‖ := by ring

/-- **`lem:five-type`(a), last claim**, for a true operator norm: for every continuous linear
operator `T`, every `e` with `‖T - J‖ ≤ e`, where `J Ψ = ⟨𝟙, Ψ⟩ 𝟙`, and all `Φ, Ψ`,
`⟨Φ, TΨ⟩ ≥ ⟨𝟙, Φ⟩⟨𝟙, Ψ⟩ - e ‖Φ‖ ‖Ψ‖`. On `L²(ν^b)`, `⟨𝟙, Φ⟩ = E_{ν^b} Φ` and `J` is the
projection onto the constants. -/
theorem inner_lower_of_opNorm (one : E) (T : E →L[ℝ] E) {e : ℝ}
    (h : ‖T - (innerSL ℝ one).smulRight one‖ ≤ e) (Φ Ψ : E) :
    inner ℝ one Φ * inner ℝ one Ψ - e * ‖Φ‖ * ‖Ψ‖ ≤ inner ℝ Φ (T Ψ) := by
  set J : E →L[ℝ] E := (innerSL ℝ one).smulRight one with hJdef
  have hJ : J Ψ = inner ℝ one Ψ • one := rfl
  have hsplit : inner ℝ Φ (T Ψ) = inner ℝ Φ (J Ψ) + inner ℝ Φ ((T - J) Ψ) := by
    rw [show (T - J) Ψ = T Ψ - J Ψ from rfl, inner_sub_right]
    ring
  have hJΦ : inner ℝ Φ (J Ψ) = inner ℝ one Φ * inner ℝ one Ψ := by
    rw [hJ, inner_smul_right, real_inner_comm one Φ]
    ring
  have hb : |inner ℝ Φ ((T - J) Ψ)| ≤ e * ‖Φ‖ * ‖Ψ‖ := by
    calc |inner ℝ Φ ((T - J) Ψ)| ≤ ‖T - J‖ * ‖Φ‖ * ‖Ψ‖ := form_bound_of_opNorm _ _ _
      _ ≤ e * ‖Φ‖ * ‖Ψ‖ := by gcongr
  have := neg_abs_le (inner ℝ Φ ((T - J) Ψ))
  linarith

end InnerProduct

/-- **`lem:five-type`(a), last claim**, in the norm convention of `Datum.lean`. -/
theorem NormBound.lower {𝔛 : Type*} [Fintype 𝔛] {μ : FiniteLaw 𝔛} {T : 𝔛 → 𝔛 → ℝ} {e : ℝ}
    (h : NormBound μ T e) (Φ Ψ : 𝔛 → ℝ) :
    μ.expect Φ * μ.expect Ψ - e * nrm μ Φ * nrm μ Ψ ≤ kf μ T Φ Ψ := by
  have := neg_abs_le (kf μ T Φ Ψ - μ.expect Φ * μ.expect Ψ)
  linarith [h Φ Ψ]

end Sarkozy.FiveType
