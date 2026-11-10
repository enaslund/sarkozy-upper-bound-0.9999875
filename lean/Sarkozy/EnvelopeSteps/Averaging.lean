module

public import Sarkozy.EnvelopeSteps.StepsOneTwo
public import Sarkozy.EnvelopeSteps.MaskLift
public import Sarkozy.Envelopes.Averaging

@[expose] public section

/-!
# Reflection averaging at the placements (`lem:reflection-averaging`(c), (d))

`paper/sections/23_envelopes.tex`, `lem:reflection-averaging`(c), (d), and Step 4 of the proof of
`thm:envelopes` (the averaging `∑ π̃ Y^{Ñ₀}[[D_ω]] = ∑ π̃ Y^{Ñ₀}[[D̄_ω]]`).

W2's `Envelopes.reflection_average` is (d) for abstract energies `Y_ω` with the transport
`Y_ω̄(K) = Y_ω(P_ω K)` as a hypothesis, and W2's `slotPush` file is (c) for tensors. Here the
transport is **proved** for placed operators, from three facts:

* **`slotPush_place`** (the reflection moves the placement): for a slot permutation `α` that maps
  the half onto itself and commutes with the flip (as `R_h` does at `ι`),
  `α_*[K]_φ = [K]_{φ ∘ α}`;
* **`place_relabel`** (relabelling the objects): for a bijection `ψ` of the objects preserving `m`,
  `[K]_{φ ∘ ψ} = [𝒫 K 𝒫^*]_φ`, `𝒫 f = f ∘ ψ⁻¹`;
* **`jointEnergy_slotPush`** ((c) for joint laws): `Y_{α_*κ ⊗ O} = Y_{κ ⊗ O}` if `α_*O = O`.

With the placement identity of (a) as a hypothesis (`φ_ω̄ ∘ α = φ_ω ∘ ψ_ω`: `R_h` maps the
placement of `ω̄` to that of `ω` up to the name permutation `ψ_ω` of the matching objects),
**`transport_placed`** is W2's transport hypothesis and **`reflection_average_placed`** is (d):
`∑ π_ω Y[[K_ω]_ω] = ∑ π_ω Y[[½(K_ω + 𝒫_ω T_ω(K_ω) 𝒫_ω^*)]_ω]` whenever `K_ω̄ = T_ω(K_ω)`.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.EnvelopeSteps

open Sarkozy.Envelopes

variable {V X : Type*} [Fintype V] [DecidableEq V]

/-- The restriction of a cut-preserving slot permutation to the half. -/
def halfPerm (c : ReflectionCut V) (α : V ≃ V) (hhalf : ∀ v, α v ∈ c.half ↔ v ∈ c.half) :
    c.Half → c.Half := fun v => ⟨α v.1, (hhalf v.1).2 v.2⟩

/-- Joining commutes with a slot permutation that preserves the half and commutes with the
flip. -/
theorem join_comp (c : ReflectionCut V) (α : V ≃ V) (hhalf : ∀ v, α v ∈ c.half ↔ v ∈ c.half)
    (hflip : ∀ v, α (c.flip v) = c.flip (α v)) (a b : c.Half → X) :
    c.join a b ∘ α = c.join (fun v => a (halfPerm c α hhalf v))
      (fun v => b (halfPerm c α hhalf v)) := by
  funext v
  simp only [Function.comp_apply]
  by_cases hv : v ∈ c.half
  · have hav : α v ∈ c.half := (hhalf v).2 hv
    have e1 := c.join_plus a b ⟨α v, hav⟩
    have e2 := c.join_plus (fun v => a (halfPerm c α hhalf v))
      (fun v => b (halfPerm c α hhalf v)) ⟨v, hv⟩
    simp only at e1 e2
    rw [e1, e2]
    rfl
  · -- `v = flip w` with `w` in the half
    have hw : c.flip v ∈ c.half := (c.crosses v).2 hv
    have hv' : v = c.flip (c.flip v) := (c.flip_flip v).symm
    have hα : α v = c.flip (α (c.flip v)) := by rw [← hflip, c.flip_flip]
    have hαw : α (c.flip v) ∈ c.half := (hhalf _).2 hw
    have e1 := c.join_minus a b ⟨α (c.flip v), hαw⟩
    have e2 := c.join_minus (fun v => a (halfPerm c α hhalf v))
      (fun v => b (halfPerm c α hhalf v)) ⟨c.flip v, hw⟩
    simp only at e1 e2
    rw [hα, e1]
    conv_rhs => rw [hv', e2]
    rfl

variable {O : Type*} [Fintype O] [DecidableEq O]

/-- **The reflection moves the placement**: `α_*[K]_φ = [K]_{φ ∘ α}`. -/
theorem slotPush_place (c : ReflectionCut V) (α : V ≃ V)
    (hhalf : ∀ v, α v ∈ c.half ↔ v ∈ c.half) (hflip : ∀ v, α (c.flip v) = c.flip (α v))
    (m : O → ℝ) (φ : O → (c.Half → X)) (K : (O → ℝ) →ₗ[ℝ] (O → ℝ)) :
    slotPush α (place c m φ K) =
      place c m (fun x v => φ x (halfPerm c α hhalf v)) K := by
  refine LinearMap.ext fun Φ => ?_
  rw [slotPush_apply]
  change (∑ q : O × O, kern m K q.1 q.2 * Φ (c.join (φ q.1) (φ q.2) ∘ α)) =
    ∑ q : O × O, kern m K q.1 q.2 *
      Φ (c.join (fun v => φ q.1 (halfPerm c α hhalf v)) (fun v => φ q.2 (halfPerm c α hhalf v)))
  refine sum_congr rfl fun q _ => ?_
  congr 1
  exact congrArg Φ (join_comp c α hhalf hflip (φ q.1) (φ q.2))

/-- The conjugation `K ↦ 𝒫 K 𝒫^*` by the relabelling `𝒫 f = f ∘ ψ⁻¹` of the objects. -/
def conjObj (ψ : O ≃ O) : ((O → ℝ) →ₗ[ℝ] (O → ℝ)) →ₗ[ℝ] ((O → ℝ) →ₗ[ℝ] (O → ℝ)) where
  toFun K := transportL ψ.symm ∘ₗ K ∘ₗ transportL ψ
  map_add' K K' := by rw [LinearMap.add_comp, LinearMap.comp_add]
  map_smul' a K := by
    rw [LinearMap.smul_comp, LinearMap.comp_smul]
    rfl

/-- **Relabelling the objects**: for a bijection `ψ` preserving `m`,
`[K]_{φ ∘ ψ} = [𝒫 K 𝒫^*]_φ`. -/
theorem place_relabel (c : ReflectionCut V) (m : O → ℝ) (ψ : O ≃ O) (hm : ∀ x, m (ψ x) = m x)
    (φ : O → (c.Half → X)) (K : (O → ℝ) →ₗ[ℝ] (O → ℝ)) :
    place c m (fun x => φ (ψ x)) K = place c m φ (conjObj ψ K) := by
  refine LinearMap.ext fun Φ => ?_
  change (∑ q : O × O, kern m K q.1 q.2 * Φ (c.join (φ (ψ q.1)) (φ (ψ q.2)))) =
    ∑ q : O × O, kern m (conjObj ψ K) q.1 q.2 * Φ (c.join (φ q.1) (φ q.2))
  let e : O × O ≃ O × O := Equiv.prodCongr ψ ψ
  conv_rhs => rw [← e.sum_comp]
  refine sum_congr rfl fun q _ => ?_
  change kern m K q.1 q.2 * _ = kern m (conjObj ψ K) (ψ q.1) (ψ q.2) * _
  congr 1
  have hδ : (fun x => delta (ψ q.2) (ψ x)) = delta q.2 := by
    funext x
    simp only [delta, EmbeddingLike.apply_eq_iff_eq]
  simp only [kern, conjObj, LinearMap.coe_mk, AddHom.coe_mk, LinearMap.comp_apply, transportL,
    Equiv.symm_apply_apply, hm, hδ]

/-- **`lem:reflection-averaging`(c) for joint laws**: if the outside law is invariant,
`Y_{α_*κ ⊗ O} = Y_{κ ⊗ O}`. -/
theorem jointEnergy_slotPush {A B : Type} [Fintype A] [DecidableEq A] [Fintype B]
    [DecidableEq B] (α : V ≃ V) (κ : ((V → A) → ℝ) →ₗ[ℝ] ℝ) (Ob : ((V → B) → ℝ) →ₗ[ℝ] ℝ)
    (hO : slotPush α Ob = Ob) (F : (∀ b, pairFam A B b) → ℝ) :
    jointEnergy (slotPush α κ) Ob F = jointEnergy κ Ob F := by
  unfold jointEnergy
  have e : pairLaws (slotPush α κ) Ob = fun b => slotPush α (pairLaws κ Ob b) := by
    funext b
    cases b
    · exact hO.symm
    · rfl
  rw [e, ← slotPush_tensorLaw, diagonalIntegral_slotPush]

/-- **The transport of `lem:reflection-averaging`(d), proved for placed operators**: if `α`
preserves the cut, the energy is `α`-invariant, and `φ_ω̄ ∘ α = φ_ω ∘ ψ_ω` with `ψ_ω` preserving
`m` (the placement identity of (a)), then `Y[[A]_{ω̄}] = Y[[𝒫_ω A 𝒫_ω^*]_ω]`. -/
theorem transport_placed (c : ReflectionCut V) (α : V ≃ V)
    (hhalf : ∀ v, α v ∈ c.half ↔ v ∈ c.half) (hflip : ∀ v, α (c.flip v) = c.flip (α v))
    (E : (((V → X) → ℝ) →ₗ[ℝ] ℝ) →ₗ[ℝ] ℝ) (hE : ∀ κ, E (slotPush α κ) = E κ)
    (m : O → ℝ) (φ φbar : O → (c.Half → X)) (ψ : O ≃ O) (hm : ∀ x, m (ψ x) = m x)
    (ha : ∀ x, (fun v => φbar x (halfPerm c α hhalf v)) = φ (ψ x))
    (A : (O → ℝ) →ₗ[ℝ] (O → ℝ)) :
    E (place c m φbar A) = E (place c m φ (conjObj ψ A)) := by
  rw [← hE, slotPush_place c α hhalf hflip, ← place_relabel c m ψ hm]
  congr 2
  funext x
  exact ha x

/-- **`lem:reflection-averaging`(d) at the placements.** For record assignments `Ω` with an
involution `ω ↦ ω̄`, weights `π_ω̄ = π_ω`, common objects with the half marginal `m`, placements
`φ_ω` with the placement identity `φ_ω̄ ∘ α = φ_ω ∘ ψ_ω` of (a), an `α`-invariant energy (c), and
operators with `K_ω̄ = T_ω(K_ω)`:
`∑ π_ω Y[[K_ω]_ω] = ∑ π_ω Y[[½(K_ω + 𝒫_ω T_ω(K_ω) 𝒫_ω^*)]_ω]`. -/
theorem reflection_average_placed {Ω : Type*} [Fintype Ω] (c : ReflectionCut V) (α : V ≃ V)
    (hhalf : ∀ v, α v ∈ c.half ↔ v ∈ c.half) (hflip : ∀ v, α (c.flip v) = c.flip (α v))
    (E : (((V → X) → ℝ) →ₗ[ℝ] ℝ) →ₗ[ℝ] ℝ) (hE : ∀ κ, E (slotPush α κ) = E κ)
    (bar : Ω → Ω) (hbar : ∀ ω, bar (bar ω) = ω) (π : Ω → ℝ) (hπ : ∀ ω, π (bar ω) = π ω)
    (m : O → ℝ) (φ : Ω → O → (c.Half → X)) (ψ : Ω → O ≃ O) (hm : ∀ ω x, m (ψ ω x) = m x)
    (ha : ∀ ω x, (fun v => φ (bar ω) x (halfPerm c α hhalf v)) = φ ω (ψ ω x))
    (T : Ω → ((O → ℝ) →ₗ[ℝ] (O → ℝ)) →ₗ[ℝ] ((O → ℝ) →ₗ[ℝ] (O → ℝ)))
    (K : Ω → (O → ℝ) →ₗ[ℝ] (O → ℝ)) (hK : ∀ ω, K (bar ω) = T ω (K ω)) :
    ∑ ω, π ω * E (place c m (φ ω) (K ω)) =
      ∑ ω, π ω * E (place c m (φ ω) ((1 / 2 : ℝ) • (K ω + conjObj (ψ ω) (T ω (K ω))))) := by
  have h := reflection_average bar hbar π hπ (fun ω => E ∘ₗ placeL c m (φ ω))
    (fun ω => conjObj (ψ ω)) T K
    (fun ω A => transport_placed c α hhalf hflip E hE m (φ ω) (φ (bar ω)) (ψ ω) (hm ω) (ha ω) A)
    hK
  exact h

end Sarkozy.EnvelopeSteps
