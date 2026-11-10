module

public import Sarkozy.PartV.ChamberCut

@[expose] public section

/-!
# Five-type data whose fold law is dominated by `ν ⊗ ν^b ⊗ ν^b`

`paper/sections/17_completion_repair.tex`, `def:five-type-datum` (and the remark after it: "The
fold kernel `T_F^b` contains the density of the middle law of `π_F` relative to `ν` and those of
its conditional outer marginals relative to `ν^b`"); `paper/sections/25_upper_reference.tex`,
`subsec:upper-rows`, `lem:upper-reference-rp`, "Chamber cuts".

V1's `PartV.datumOf` builds a five-type datum from an exchangeable matching law `π_E` and a fold
law `π_F` supported in the support of `π_E`. In the middle that inclusion holds because `G_E`
has no edges. For the two-layer rows of the upper reference it fails: `G_{E𝔣'}` relates every
pair of distinct objects, `G_{F𝔣'}` does not relate `(2, 0)` (V1's finding 3). What the
factorization `π_F(ω) = ν(ω₁) ν^{ω₁}(ω₀) ν^{ω₁}(ω₂) T_F^{ω₁}(ω₀, ω₂)` of
`def:five-type-datum`(iv) actually needs is weaker: that every configuration charged by `π_F`
has `(ω₀, ω₁)` and `(ω₂, ω₁)` in the support of `Γ` (`GamSupported`), i.e. `π_F ≪ ν ⊗ ν^b ⊗ ν^b`.

* `factor_of_gam`: the factorization under `GamSupported`, with `T_F = kernelOf π_E π_F`.
* `gamSupported_self`, `gamSupported_of_support`: `π_E` itself, and every law supported in
  `supp π_E`, is `Γ`-supported.
* **`datumOfGam`**: the five-type datum (`FiveType.Datum`) from an exchangeable `π_E`, a
  `Γ`-supported `π_F` and a `𝒢₆`-invariant `π_L`; its middle law is the law of object `1`, which
  is also the law of object `0` (`nuOf_eq_obj0`).
* Tools on finite laws: `law_ext`, `law_eq_of_expect`, `map_map'`.
-/

namespace Sarkozy.PartVLaws

open Finset Sarkozy.Labellings Sarkozy.FiveType Sarkozy.PartV

/-! ## Finite laws -/

/-- Two finite laws with the same weights are equal. -/
theorem law_ext {Ω : Type*} [Fintype Ω] {μ ν : FiniteLaw Ω} (h : ∀ ω, μ.weight ω = ν.weight ω) :
    μ = ν := by
  obtain ⟨w₁, n₁, t₁⟩ := μ
  obtain ⟨w₂, n₂, t₂⟩ := ν
  have hw : w₁ = w₂ := funext h
  subst hw
  rfl

/-- Two finite laws with the same expectations are equal. -/
theorem law_eq_of_expect {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {μ ν : FiniteLaw Ω}
    (h : ∀ f : Ω → ℝ, μ.expect f = ν.expect f) : μ = ν :=
  law_ext fun ω => by rw [weight_eq_expect, weight_eq_expect, h]

/-- `(μ.map f).map g = μ.map (g ∘ f)`. -/
theorem map_map' {Ω Ξ Θ : Type*} [Fintype Ω] [Fintype Ξ] [DecidableEq Ξ] [Fintype Θ]
    [DecidableEq Θ] (μ : FiniteLaw Ω) (f : Ω → Ξ) (g : Ξ → Θ) :
    (μ.map f).map g = μ.map (g ∘ f) :=
  law_eq_of_expect fun h => by
    rw [FiniteLaw.expect_map, FiniteLaw.expect_map, FiniteLaw.expect_map]
    rfl

/-- The weight of an image law is positive exactly at the images of charged points. -/
theorem map_weight_ne_zero {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ] [DecidableEq Ξ]
    (μ : FiniteLaw Ω) (φ : Ω → Ξ) (ξ : Ξ) :
    (μ.map φ).weight ξ ≠ 0 ↔ ∃ ω, μ.weight ω ≠ 0 ∧ φ ω = ξ := by
  rw [map_weight_eq]
  constructor
  · intro h
    obtain ⟨ω, hω, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
    exact ⟨ω, hne, (mem_filter.mp hω).2⟩
  · rintro ⟨ω, hω, rfl⟩ h0
    have hle : μ.weight ω ≤ ∑ ω' ∈ univ.filter (fun ω' => φ ω' = φ ω), μ.weight ω' :=
      single_le_sum (f := μ.weight) (fun x _ => μ.nonneg x) (by simp)
    rw [h0] at hle
    exact hω (le_antisymm hle (μ.nonneg ω))

/-! ## `Γ`-supported fold laws -/

section Generic

variable {𝔛 : Type*} [Fintype 𝔛] [DecidableEq 𝔛]

/-- **`π ≪ ν ⊗ ν^b ⊗ ν^b`**: every configuration charged by `π` has its pairs `(ω₀, ω₁)` and
`(ω₂, ω₁)` in the support of the merge law `Γ` of `π_E`. -/
def GamSupported (piE pi : FiniteLaw (Fin 3 → 𝔛)) : Prop :=
  ∀ ω, pi.weight ω ≠ 0 →
    (gamOf piE).weight ![ω 0, ω 1] ≠ 0 ∧ (gamOf piE).weight ![ω 2, ω 1] ≠ 0

/-- **The factorization of `def:five-type-datum`(iv) for a `Γ`-supported law**:
`π(ω) = ν(ω₁) ν^{ω₁}(ω₀) ν^{ω₁}(ω₂) T^{ω₁}(ω₀, ω₂)` with `T = kernelOf π_E π`. -/
theorem factor_of_gam (piE pi : FiniteLaw (Fin 3 → 𝔛)) (hsupp : GamSupported piE pi)
    (ω : Fin 3 → 𝔛) :
    pi.weight ω = (nuOf piE).weight (ω 1) * (nubOf piE (ω 1)).weight (ω 0) *
      (nubOf piE (ω 1)).weight (ω 2) * kernelOf piE pi (ω 1) (ω 0) (ω 2) := by
  unfold kernelOf
  split_ifs with hden
  · rw [mul_zero]
    by_contra hne
    obtain ⟨h01, h21⟩ := hsupp ω hne
    have e01 := gamOf_weight piE ![ω 0, ω 1]
    have e21 := gamOf_weight piE ![ω 2, ω 1]
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at e01 e21
    rw [e01] at h01
    rw [e21] at h21
    exact (mul_ne_zero (mul_ne_zero (left_ne_zero_of_mul h01) (right_ne_zero_of_mul h01))
      (right_ne_zero_of_mul h21)) hden
  · rw [← three_eq ω, mul_div_assoc']
    exact (eq_div_iff hden).mpr (by ring)

/-- **The matching law is `Γ`-supported** when it is invariant under the swap of the objects
`0, 2`. -/
theorem gamSupported_self (piE : FiniteLaw (Fin 3 → 𝔛))
    (hswap : ∀ ω : Fin 3 → 𝔛, piE.weight (ω ∘ Equiv.swap 0 2) = piE.weight ω) :
    GamSupported piE piE := by
  intro ω hω
  refine ⟨fun h => hω (le_antisymm ((piE_le_gam piE ω).trans h.le) (piE.nonneg ω)), fun h => ?_⟩
  have h1 := piE_le_gam piE (ω ∘ Equiv.swap 0 2)
  have e0 : (ω ∘ Equiv.swap 0 2) 0 = ω 2 := rfl
  have e1 : (ω ∘ Equiv.swap 0 2) 1 = ω 1 := rfl
  rw [e0, e1, h, hswap] at h1
  exact hω (le_antisymm h1 (piE.nonneg ω))

/-- A law supported in the support of an exchangeable `π_E` is `Γ`-supported (V1's hypothesis
of `datumOf` is the special case). -/
theorem gamSupported_of_support (piE pi : FiniteLaw (Fin 3 → 𝔛))
    (hswap : ∀ ω : Fin 3 → 𝔛, piE.weight (ω ∘ Equiv.swap 0 2) = piE.weight ω)
    (hsupp : ∀ ω, pi.weight ω ≠ 0 → piE.weight ω ≠ 0) : GamSupported piE pi :=
  fun ω hω => gamSupported_self piE hswap ω (hsupp ω hω)

/-- **The five-type datum of an exchangeable matching law, a `Γ`-supported fold law and a
`𝒢₆`-invariant root** (`def:five-type-datum`): `ν`, `ν^b`, `Γ` are the marginal of object `1`,
the conditional law of object `0` and the law of the objects `0, 1` under `π_E`; the kernels
are the densities against `ν ⊗ ν^b ⊗ ν^b`. -/
noncomputable def datumOfGam (piE piF : FiniteLaw (Fin 3 → 𝔛)) (piL : FiniteLaw (ZMod 6 → 𝔛))
    (hexch : ∀ (σ : Equiv.Perm (Fin 3)) (ω : Fin 3 → 𝔛), piE.weight (ω ∘ σ) = piE.weight ω)
    (hsupp : GamSupported piE piF)
    (hL : ∀ (k : Fin 6) (Ψ : ZMod 6 → 𝔛), piL.weight (Ψ ∘ g6 k) = piL.weight Ψ) : Datum 𝔛 where
  nu := nuOf piE
  nub := nubOf piE
  Gam := gamOf piE
  Gam_weight := gamOf_weight piE
  Gam_symm := gamOf_symm piE (hexch (Equiv.swap 0 1))
  piE := piE
  TE := kernelOf piE piE
  TE_nonneg := kernelOf_nonneg piE piE
  piE_weight := factor_of_support piE piE (hexch (Equiv.swap 0 2)) (fun _ h => h)
  piE_exch := hexch
  piF := piF
  TF := kernelOf piE piF
  TF_nonneg := kernelOf_nonneg piE piF
  piF_weight := factor_of_gam piE piF hsupp
  piL := piL
  piL_inv := hL

/-- **The middle law is also the law of the object `0`**, by exchangeability. -/
theorem nuOf_eq_obj0 (piE : FiniteLaw (Fin 3 → 𝔛))
    (hexch : ∀ (σ : Equiv.Perm (Fin 3)) (ω : Fin 3 → 𝔛), piE.weight (ω ∘ σ) = piE.weight ω) :
    nuOf piE = piE.map fun ω => ω 0 :=
  law_eq_of_expect fun g => by
    rw [nuOf, FiniteLaw.expect_map, FiniteLaw.expect_map]
    exact expect_swap01 piE hexch g

end Generic

end Sarkozy.PartVLaws
