module

public import Sarkozy.OpsSteps.Step4Inv

@[expose] public section

/-!
# The cap `hcapH` of Step 4 from the per-selection caps (OPS-S)

`paper/sections/23_envelopes.tex`, Step 4 of `thm:envelopes`; `lem:oct24:mask-schur`(b);
`lem:reflection-averaging`(e)–(g).

The input `hcapH` of `step4_inv` asks `D̄_ω = ½(K_ω + 𝒫_ω T_ω(K_ω) 𝒫_ω^*) ⪯ κ_H(ω) I` in
`L²(m)`. Here (**`hcapH_of_caps`**) it follows from the per-selection caps `K_ω ⪯ κ_H(ω) I` (the
form in which `lem:oct24:mask-schur`(b) bounds `Lift(D_ω)`), `T_ω(K_ω) = K_{ω̄}` (`hK`),
`κ_H(ω̄) = κ_H(ω)` and an `m`-preserving relabelling `ψ_ω`:

* `ip_transport_symm`, `opPos_conjObj`, `opLE_conjObj_smul_id`: the relabelling conjugation
  preserves the order of `L²(m)` and fixes `κ I`;
* `opLE_avg`: the order is convex.

The improved cap `κ_b` of the additional average (`hcapb`) is not implied by these: it needs the
invariant-part analysis of `lem:oct24:mask-schur`(b) (C).
-/

namespace Sarkozy.OpsSteps

open Finset
open scoped BigOperators
open Sarkozy.EnvelopeSteps

section Order

variable {O : Type*} [Fintype O]

/-- The adjoint of a relabelling transport in `L²(m)`, for `m ∘ ψ = m`. -/
theorem ip_transport_symm (m : O → ℝ) (ψ : O ≃ O) (hm : ∀ x, m (ψ x) = m x) (f g : O → ℝ) :
    ip m f (transportL ψ.symm g) = ip m (transportL ψ f) g := by
  unfold ip transportL
  simp only [LinearMap.coe_mk, AddHom.coe_mk]
  rw [← Equiv.sum_comp ψ]
  refine sum_congr rfl fun x _ => ?_
  rw [hm, Equiv.symm_apply_apply]

/-- **The relabelling conjugation preserves positivity in `L²(m)`.** -/
theorem opPos_conjObj {m : O → ℝ} (ψ : O ≃ O) (hm : ∀ x, m (ψ x) = m x)
    {K : (O → ℝ) →ₗ[ℝ] (O → ℝ)} (hK : OpPos m K) : OpPos m (conjObj ψ K) := by
  constructor
  · intro f g
    change ip m f (transportL ψ.symm (K (transportL ψ g))) =
      ip m g (transportL ψ.symm (K (transportL ψ f)))
    rw [ip_transport_symm m ψ hm, ip_transport_symm m ψ hm, hK.symm]
  · intro f
    change 0 ≤ ip m f (transportL ψ.symm (K (transportL ψ f)))
    rw [ip_transport_symm m ψ hm]
    exact hK.nonneg _

omit [Fintype O] in
/-- The conjugation fixes `κ I`. -/
theorem conjObj_smul_id (ψ : O ≃ O) (κ : ℝ) :
    conjObj ψ (κ • (LinearMap.id : (O → ℝ) →ₗ[ℝ] (O → ℝ))) = κ • LinearMap.id := by
  apply LinearMap.ext
  intro f
  funext x
  change (κ • f) (ψ (ψ.symm x)) = (κ • f) x
  rw [Equiv.apply_symm_apply]

/-- **`K ⪯ κ I` is preserved by the relabelling conjugation.** -/
theorem opLE_conjObj_smul_id {m : O → ℝ} (ψ : O ≃ O) (hm : ∀ x, m (ψ x) = m x)
    {K : (O → ℝ) →ₗ[ℝ] (O → ℝ)} {κ : ℝ} (hK : OpLE m K (κ • LinearMap.id)) :
    OpLE m (conjObj ψ K) (κ • LinearMap.id) := by
  have h := opPos_conjObj ψ hm hK
  unfold OpLE
  rwa [map_sub, conjObj_smul_id] at h

/-- **The order of `L²(m)` is convex.** -/
theorem opLE_avg {m : O → ℝ} {A B C : (O → ℝ) →ₗ[ℝ] (O → ℝ)} (hA : OpLE m A C)
    (hB : OpLE m B C) : OpLE m ((1 / 2 : ℝ) • (A + B)) C := by
  have h := (hA.smul (by norm_num : (0 : ℝ) ≤ 1 / 2)).add (hB.smul (by norm_num : (0 : ℝ) ≤ 1 / 2))
  unfold OpLE
  have e : C - (1 / 2 : ℝ) • (A + B) = (1 / 2 : ℝ) • (C - A) + (1 / 2 : ℝ) • (C - B) := by
    rw [← smul_add, smul_add (1 / 2 : ℝ) A B]
    module
  rw [e]
  exact h

end Order

/-- **`hcapH` from the per-selection caps** (see the module docstring). -/
theorem hcapH_of_caps {Ω : Type*} {O : Type*} [Fintype O] (𝒞 : Finset Ω) (bar : Ω → Ω)
    (hbar𝒞 : ∀ ω ∈ 𝒞, bar ω ∈ 𝒞) (m : O → ℝ) (ψ : Ω → O ≃ O)
    (hm : ∀ ω ∈ 𝒞, ∀ x, m (ψ ω x) = m x)
    (T : Ω → ((O → ℝ) →ₗ[ℝ] (O → ℝ)) →ₗ[ℝ] ((O → ℝ) →ₗ[ℝ] (O → ℝ)))
    (K : Ω → (O → ℝ) →ₗ[ℝ] (O → ℝ)) (hK : ∀ ω ∈ 𝒞, K (bar ω) = T ω (K ω))
    (κH : Ω → ℝ) (hκ : ∀ ω ∈ 𝒞, κH (bar ω) = κH ω)
    (hcap : ∀ ω ∈ 𝒞, OpLE m (K ω) (κH ω • LinearMap.id)) :
    ∀ ω ∈ 𝒞, OpLE m ((1 / 2 : ℝ) • (K ω + conjObj (ψ ω) (T ω (K ω))))
      (κH ω • LinearMap.id) := by
  intro ω hω
  refine opLE_avg (hcap ω hω) (opLE_conjObj_smul_id (ψ ω) (hm ω hω) ?_)
  rw [← hK ω hω, ← hκ ω hω]
  exact hcap (bar ω) (hbar𝒞 ω hω)

end Sarkozy.OpsSteps
