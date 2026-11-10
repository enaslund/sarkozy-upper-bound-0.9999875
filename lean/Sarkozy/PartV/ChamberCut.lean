module

public import Sarkozy.FiveType.Criteria
public import Sarkozy.FiveType.Invariance
public import Sarkozy.PartV.MiddleReference
public import Sarkozy.PartV.LayerCut

@[expose] public section

/-!
# The middle reference at the chamber cuts of the first coordinate (bridge to `FiveType`)

`paper/sections/20c_middle_frame.tex`, `lem:front12:reference`(iii), "First-coordinate cuts";
`paper/sections/17_completion_repair.tex`, `def:five-type-datum`, `lem:five-type`(b), applied
through C1's `Sarkozy.FiveType` (`Datum`, `Datum.full_norm_rp`).

**The datum.** The proof of (iii) observes that, for `j ∈ {1, 2}`, the middle law `ν`, the
conditional references `ν^ξ` and the two-object marginal of the `j`-layer `E` law, the `E` and
`F` laws and the root form a five-type datum on the labels of one object. Here:
* `datumOf`: from an exchangeable matching law `π_E`, a fold law `π_F` supported in the support of
  `π_E`, and a `𝒢₆`-invariant root, the datum whose `ν`, `ν^b`, `Γ` are the marginals and
  conditional laws of `π_E` and whose kernels are the densities against `ν ⊗ ν^b ⊗ ν^b`
  (`factor_of_support`: the factorizations of `def:five-type-datum`(iii),(iv) hold);
* `fieldDatum`: this datum for the field laws read as laws of objects (`objLaw`,
  `𝔛 = X^Λ`), under `DatumHyp`;
* `middleBlock_datumHyp₂`, `middleBlock_datumHyp₁`: `DatumHyp` holds for the paper's block laws
  with the uniform root (exchangeability: every permutation of the objects is an automorphism
  of `G_E`; support: `Inj(G_F) ⊆ Inj(G_E)`; the root: `𝒢₆` acts by automorphisms of `G_L`).

**The law.** `middleTilde_eq`: `μ̃_𝔅` is the sum of the push-forwards of the two five-type
measures `𝒬_{w r^deg}` (two layers, written into the slots by `(u₀, u₁, ℓ) ↦ Ψ(u₀)(ℓ)`) and
`𝒬_{v r^{deg+1}}` (one layer, `(u₀, u₁, ℓ) ↦ Ψ(u₀)(0)`); the merges and the constants are
identified through `Γ` and, for the constants, the exchangeability of `π_E`
(`lawL_merge`, `lawL_const`). `pushL_firstCut_positive` transports positivity at the chamber
cut `ϑ_a` of `ℤ/6ℤ` to the cut `ϑ_{0,a}` of the slots.

**Results.**
* `middleTilde_firstCut_positive`: `μ̃_𝔅 ⪰ 0` at every chamber cut of the first coordinate,
  from the thirteen inequalities, the rows (`RowBounds`, `lem:front12:reference`(i)) and the
  root envelopes (`RootEnvelope`, the L20 and L10 parts of (ii)), via `lem:five-type`(b).
* `middleBlockReference_uniform_familyPositive`: **(R2) for the middle block law with the
  uniform root at every cut of the family `𝔉`**, with the rows, the root envelopes and the
  layer caps at `ι` as hypotheses (`lem:front12:reference`(iii) on the pieces below `2³⁰`).

Remaining hypotheses: the rows (i) and the caps (ii) of `lem:front12:reference` (the spectral
inputs). For the positive roots of the pieces from `2³⁰`, `DatumHyp` also needs their
`𝒢₆`-invariance (`lem:positive-root-properties`(b), not proved here).
-/

namespace Sarkozy.PartV

open Finset Sarkozy.Labellings Sarkozy.FiveType

section Generic

variable {𝔛 : Type*} [Fintype 𝔛] [DecidableEq 𝔛]

/-- The weight of a finite law is its expectation of an indicator. -/
theorem weight_eq_expect {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (μ : FiniteLaw Ω) (ω : Ω) :
    μ.weight ω = μ.expect (fun ω' => if ω' = ω then 1 else 0) := by
  unfold FiniteLaw.expect
  simp

/-- Expectation invariance under a bijection gives weight invariance. -/
theorem weight_comp_of_expect {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (μ : FiniteLaw Ω)
    (e : Ω ≃ Ω) (h : ∀ f : Ω → ℝ, μ.expect (fun ω => f (e ω)) = μ.expect f) (ω : Ω) :
    μ.weight (e ω) = μ.weight ω := by
  rw [weight_eq_expect, weight_eq_expect, ← h]
  congr 1
  funext ω'
  simp only [e.apply_eq_iff_eq]

/-- The middle law `ν`: the law of the object `1` under `π_E`. -/
noncomputable def nuOf (piE : FiniteLaw (Fin 3 → 𝔛)) : FiniteLaw 𝔛 := piE.map fun ω => ω 1

/-- The merge law `Γ`: the law of the objects `0, 1` under `π_E`. -/
noncomputable def gamOf (piE : FiniteLaw (Fin 3 → 𝔛)) : FiniteLaw (Fin 2 → 𝔛) :=
  piE.map fun ω i => ω i.castSucc

theorem map_weight_eq {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ] [DecidableEq Ξ] (μ : FiniteLaw Ω)
    (φ : Ω → Ξ) (ξ : Ξ) :
    (μ.map φ).weight ξ = ∑ ω ∈ univ.filter (fun ω => φ ω = ξ), μ.weight ω := by
  change (∑ ω, if φ ω = ξ then μ.weight ω else 0) = _
  rw [sum_filter]

theorem le_map_weight {Ω Ξ : Type*} [Fintype Ω] [Fintype Ξ] [DecidableEq Ξ] (μ : FiniteLaw Ω)
    (φ : Ω → Ξ) (ω : Ω) : μ.weight ω ≤ (μ.map φ).weight (φ ω) := by
  rw [map_weight_eq]
  exact single_le_sum (f := μ.weight) (fun x _ => μ.nonneg x) (by simp)

/-- `∑_x Γ(x, b) = ν(b)`. -/
theorem sum_gamOf (piE : FiniteLaw (Fin 3 → 𝔛)) (b : 𝔛) :
    ∑ x, (gamOf piE).weight ![x, b] = (nuOf piE).weight b := by
  simp only [gamOf, nuOf, map_weight_eq]
  rw [← sum_biUnion]
  · congr 1
    ext ω
    simp only [mem_biUnion, mem_filter, mem_univ, true_and]
    constructor
    · rintro ⟨x, hx⟩
      have := congrFun hx 1
      simpa using this
    · intro h
      refine ⟨ω 0, ?_⟩
      funext i
      fin_cases i
      · rfl
      · simpa using h
  · intro x _ y _ hxy
    simp only [Function.onFun]
    rw [disjoint_filter]
    intro ω _ h1 h2
    apply hxy
    have a := congrFun h1 0
    have b' := congrFun h2 0
    simp at a b'
    rw [← a, ← b']


/-- The conditional reference `ν^b`: the law of the object `0` given that the object `1` is `b`
(for `ν(b) = 0`, any law; we take `ν`). -/
noncomputable def nubOf (piE : FiniteLaw (Fin 3 → 𝔛)) (b : 𝔛) : FiniteLaw 𝔛 :=
  if hb : (nuOf piE).weight b = 0 then nuOf piE else
  { weight := fun x => (gamOf piE).weight ![x, b] / (nuOf piE).weight b
    nonneg := fun x => div_nonneg ((gamOf piE).nonneg _) ((nuOf piE).nonneg b)
    total := by rw [← sum_div, sum_gamOf, div_self hb] }

theorem nubOf_weight (piE : FiniteLaw (Fin 3 → 𝔛)) {b : 𝔛} (hb : (nuOf piE).weight b ≠ 0)
    (x : 𝔛) : (nubOf piE b).weight x = (gamOf piE).weight ![x, b] / (nuOf piE).weight b := by
  unfold nubOf
  simp only [hb, ↓reduceDIte]

theorem gam_le_nu (piE : FiniteLaw (Fin 3 → 𝔛)) (x b : 𝔛) :
    (gamOf piE).weight ![x, b] ≤ (nuOf piE).weight b := by
  rw [← sum_gamOf]
  exact single_le_sum (f := fun x => (gamOf piE).weight ![x, b]) (fun y _ => (gamOf piE).nonneg _)
    (mem_univ x)

/-- `Γ(ω) = ν(ω₁) ν^{ω₁}(ω₀)`. -/
theorem gamOf_weight (piE : FiniteLaw (Fin 3 → 𝔛)) (ω : Fin 2 → 𝔛) :
    (gamOf piE).weight ω = (nuOf piE).weight (ω 1) * (nubOf piE (ω 1)).weight (ω 0) := by
  have hω : ω = ![ω 0, ω 1] := by
    funext i
    fin_cases i <;> rfl
  by_cases hb : (nuOf piE).weight (ω 1) = 0
  · rw [hb, zero_mul]
    have := gam_le_nu piE (ω 0) (ω 1)
    rw [← hω, hb] at this
    exact le_antisymm this ((gamOf piE).nonneg ω)
  · rw [nubOf_weight piE hb, mul_div_cancel₀ _ hb, ← hω]

/-- The density `T^b(x, y) = π(x, b, y) / (ν(b) ν^b(x) ν^b(y))` of a law of three objects against
`ν ⊗ ν^b ⊗ ν^b` (zero where the denominator vanishes). -/
noncomputable def kernelOf (piE pi : FiniteLaw (Fin 3 → 𝔛)) (b x y : 𝔛) : ℝ :=
  if (nuOf piE).weight b * (nubOf piE b).weight x * (nubOf piE b).weight y = 0 then 0
  else pi.weight ![x, b, y] /
    ((nuOf piE).weight b * (nubOf piE b).weight x * (nubOf piE b).weight y)

theorem kernelOf_nonneg (piE pi : FiniteLaw (Fin 3 → 𝔛)) (b x y : 𝔛) :
    0 ≤ kernelOf piE pi b x y := by
  unfold kernelOf
  split_ifs
  · exact le_rfl
  · exact div_nonneg (pi.nonneg _) (mul_nonneg (mul_nonneg ((nuOf piE).nonneg _)
      ((nubOf piE b).nonneg _)) ((nubOf piE b).nonneg _))

omit [Fintype 𝔛] [DecidableEq 𝔛] in
theorem three_eq (ω : Fin 3 → 𝔛) : ω = ![ω 0, ω 1, ω 2] := by
  funext i
  fin_cases i <;> rfl

/-- `π_E(ω) ≤ Γ(ω₀, ω₁)`. -/
theorem piE_le_gam (piE : FiniteLaw (Fin 3 → 𝔛)) (ω : Fin 3 → 𝔛) :
    piE.weight ω ≤ (gamOf piE).weight ![ω 0, ω 1] := by
  have h := le_map_weight piE (fun (ω : Fin 3 → 𝔛) (i : Fin 2) => ω i.castSucc) ω
  have he : (fun i : Fin 2 => ω i.castSucc) = ![ω 0, ω 1] := by
    funext i
    fin_cases i <;> rfl
  rw [he] at h
  exact h

/-- **Factorization of a law supported in the support of an exchangeable `π_E`**: if `π_E` is
invariant under the swap of the objects `0, 2`, and `π(ω) ≠ 0` implies `π_E(ω) ≠ 0`, then
`π(ω) = ν(ω₁) ν^{ω₁}(ω₀) ν^{ω₁}(ω₂) T^{ω₁}(ω₀, ω₂)` with `T = kernelOf π_E π`. -/
theorem factor_of_support (piE pi : FiniteLaw (Fin 3 → 𝔛))
    (hswap : ∀ ω : Fin 3 → 𝔛, piE.weight (ω ∘ Equiv.swap 0 2) = piE.weight ω)
    (hsupp : ∀ ω, pi.weight ω ≠ 0 → piE.weight ω ≠ 0) (ω : Fin 3 → 𝔛) :
    pi.weight ω = (nuOf piE).weight (ω 1) * (nubOf piE (ω 1)).weight (ω 0) *
      (nubOf piE (ω 1)).weight (ω 2) * kernelOf piE pi (ω 1) (ω 0) (ω 2) := by
  unfold kernelOf
  split_ifs with hden
  · rw [mul_zero]
    by_contra hne
    have hE := hsupp ω hne
    -- every factor of the denominator is nonzero
    have hb : (nuOf piE).weight (ω 1) ≠ 0 := by
      intro h0
      apply hE
      have h1 := (piE_le_gam piE ω).trans (gam_le_nu piE (ω 0) (ω 1))
      rw [h0] at h1
      exact le_antisymm h1 (piE.nonneg ω)
    have hx : (nubOf piE (ω 1)).weight (ω 0) ≠ 0 := by
      intro h0
      apply hE
      have hg : (gamOf piE).weight ![ω 0, ω 1] = 0 := by
        have := gamOf_weight piE ![ω 0, ω 1]
        simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at this
        rw [this, h0, mul_zero]
      have h1 := piE_le_gam piE ω
      rw [hg] at h1
      exact le_antisymm h1 (piE.nonneg ω)
    have hy : (nubOf piE (ω 1)).weight (ω 2) ≠ 0 := by
      intro h0
      apply hE
      have hg : (gamOf piE).weight ![ω 2, ω 1] = 0 := by
        have := gamOf_weight piE ![ω 2, ω 1]
        simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at this
        rw [this, h0, mul_zero]
      have h1 := piE_le_gam piE (ω ∘ Equiv.swap 0 2)
      have e0 : (ω ∘ Equiv.swap 0 2) 0 = ω 2 := rfl
      have e1 : (ω ∘ Equiv.swap 0 2) 1 = ω 1 := rfl
      rw [e0, e1, hg, hswap] at h1
      exact le_antisymm h1 (piE.nonneg ω)
    exact (mul_ne_zero (mul_ne_zero hb hx) hy) hden
  · rw [← three_eq ω, mul_div_assoc']
    exact (eq_div_iff hden).mpr (by ring)

/-- `Γ` is symmetric when `π_E` is invariant under the swap of the objects `0, 1`. -/
theorem gamOf_symm (piE : FiniteLaw (Fin 3 → 𝔛))
    (hswap : ∀ ω : Fin 3 → 𝔛, piE.weight (ω ∘ Equiv.swap 0 1) = piE.weight ω)
    (ω : Fin 2 → 𝔛) : (gamOf piE).weight (ω ∘ Equiv.swap 0 1) = (gamOf piE).weight ω := by
  change (∑ ω', if (fun i : Fin 2 => ω' i.castSucc) = ω ∘ Equiv.swap 0 1 then piE.weight ω'
      else 0) = ∑ ω', if (fun i : Fin 2 => ω' i.castSucc) = ω then piE.weight ω' else 0
  refine Fintype.sum_equiv (Equiv.arrowCongr (Equiv.swap (0 : Fin 3) 1) (Equiv.refl 𝔛)) _ _
    fun ω' => ?_
  have he : ∀ ω'' : Fin 3 → 𝔛,
      (Equiv.arrowCongr (Equiv.swap (0 : Fin 3) 1) (Equiv.refl 𝔛)) ω'' =
        ω'' ∘ Equiv.swap (0 : Fin 3) 1 := by
    intro ω''
    funext j
    simp [Equiv.arrowCongr_apply]
  rw [he, hswap]
  congr 1
  apply propext
  constructor
  · intro h
    funext i
    have := congrFun h (Equiv.swap 0 1 i)
    simp only [Function.comp_apply, Equiv.swap_apply_self] at this
    rw [← this]
    fin_cases i <;> rfl
  · intro h
    funext i
    rw [← h]
    fin_cases i <;> rfl

/-- **A five-type datum** (`def:five-type-datum`) from an exchangeable matching law `π_E`, a fold
law `π_F` supported in the support of `π_E`, and a `𝒢₆`-invariant root `π_L`: the middle law,
the conditional references and the merge law are the marginals and conditional laws of `π_E`,
and the kernels are the densities against `ν ⊗ ν^b ⊗ ν^b`. -/
noncomputable def datumOf (piE piF : FiniteLaw (Fin 3 → 𝔛)) (piL : FiniteLaw (ZMod 6 → 𝔛))
    (hexch : ∀ (σ : Equiv.Perm (Fin 3)) (ω : Fin 3 → 𝔛), piE.weight (ω ∘ σ) = piE.weight ω)
    (hsupp : ∀ ω, piF.weight ω ≠ 0 → piE.weight ω ≠ 0)
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
  piF_weight := factor_of_support piE piF (hexch (Equiv.swap 0 2)) hsupp
  piL := piL
  piL_inv := hL

end Generic

/-! ## Laws of objects, and the push-forward to the slots -/

section Objects

variable {X : Type*} [Fintype X] [DecidableEq X]

/-- A labelling of `O × Λ`, read as a configuration of objects carrying one label per layer. -/
def curryObj {O Λ : Type*} (y : O × Λ → X) : O → Λ → X := fun o ℓ => y (o, ℓ)

/-- A field law as a law of objects (`𝔛 = X^Λ`). -/
noncomputable def objLaw {O Λ : Type*} [Fintype O] [DecidableEq O] [Fintype Λ] [DecidableEq Λ]
    (lam : FiniteLaw (O × Λ → X)) : FiniteLaw (O → Λ → X) :=
  lam.map curryObj

theorem expect_objLaw {O Λ : Type*} [Fintype O] [DecidableEq O] [Fintype Λ] [DecidableEq Λ]
    (lam : FiniteLaw (O × Λ → X)) (g : (O → Λ → X) → ℝ) :
    (objLaw lam).expect g = lam.expect (fun y => g (curryObj y)) := by
  unfold objLaw
  rw [FiniteLaw.expect_map]
  rfl

theorem objLaw_weight {O Λ : Type*} [Fintype O] [DecidableEq O] [Fintype Λ] [DecidableEq Λ]
    (lam : FiniteLaw (O × Λ → X)) (ω : O → Λ → X) :
    (objLaw lam).weight ω = lam.weight (fun p => ω p.1 p.2) := by
  unfold objLaw
  rw [map_weight_eq]
  have : (univ.filter fun y : O × Λ → X => curryObj y = ω) = {fun p => ω p.1 p.2} := by
    ext y
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    constructor
    · rintro rfl
      rfl
    · rintro rfl
      rfl
  rw [this, sum_singleton]

/-- The push-forward of a functional on configurations along a map to the slot labellings. -/
def pushL {Ω Ω' : Type*} (L : (Ω → ℝ) →ₗ[ℝ] ℝ) (T : Ω → Ω') : (Ω' → ℝ) →ₗ[ℝ] ℝ :=
  L ∘ₗ LinearMap.funLeft ℝ ℝ T

theorem pushL_apply {Ω Ω' : Type*} (L : (Ω → ℝ) →ₗ[ℝ] ℝ) (T : Ω → Ω') (f : Ω' → ℝ) :
    pushL L T f = L (fun ω => f (T ω)) := rfl

/-- The two-layer configurations to the slots: `(u₀, u₁, ℓ) ↦ Ψ(u₀)(ℓ)`. -/
def toSlot₂ (Ψ : ZMod 6 → Fin 2 → X) : Slot → X := fun v => Ψ v.1 (layerFin v.2.2)

/-- The one-layer configurations to the slots, on both layers: `(u₀, u₁, ℓ) ↦ Ψ(u₀)(0)`. -/
def toSlot₁ (Ψ : ZMod 6 → Fin 1 → X) : Slot → X := fun v => Ψ v.1 0

end Objects

/-! ## Transport of positivity from the chamber cuts of `ℤ/6ℤ` to the first-coordinate cuts -/

section Transport

variable {X : Type*} {𝔛 : Type*}

theorem mem_firstChamberCut_half {a : Chamber} {v : Slot} (hv : v ∈ (firstChamberCut a).half) :
    v.1 ∈ (chamberCut a).half :=
  (Finset.mem_product.mp hv).1

/-- **Positivity at `ϑ_{0,a}` from positivity at the chamber cut `ϑ_a` of `ℤ/6ℤ`**, for a law
on configurations `Ψ : ℤ/6ℤ → 𝔛` written into the slots by `z_v = κ(Ψ(v₀), (v₁, ℓ))` (the label
of a slot depends on its first chamber coordinate only through `Ψ(v₀)`). -/
theorem pushL_firstCut_positive (κ : 𝔛 → Chamber × Layer → X)
    (L : ((ZMod 6 → 𝔛) → ℝ) →ₗ[ℝ] ℝ) (a : Chamber) (h : (chamberCut a).Positive L) :
    (firstChamberCut a).Positive (pushL L (fun Ψ v => κ (Ψ v.1) v.2)) := by
  let lift : (((firstChamberCut a).Half → X) → ℝ) → (((chamberCut a).Half → 𝔛) → ℝ) :=
    fun F x => F (fun v => κ (x ⟨v.1.1, mem_firstChamberCut_half v.2⟩) v.1.2)
  have hform : ∀ F G, (firstChamberCut a).form (pushL L (fun Ψ v => κ (Ψ v.1) v.2)) F G =
      (chamberCut a).form L (lift F) (lift G) := by
    intro F G
    rfl
  constructor
  · intro F G
    rw [hform, hform]
    exact h.symmetric _ _
  · intro F
    rw [hform]
    exact h.nonneg _

end Transport

/-! ## The data of a middle field-law family -/

section MiddleDatum

variable {X : Type} [Fintype X] [DecidableEq X]

/-- The type of `FiveType` matching a pattern type. -/
def toTy : PType → Ty
  | .L => .L | .D => .D | .S => .S | .R => .R | .C => .C

/-- The pattern type matching a type of `FiveType`. -/
def ofTy : Ty → PType
  | .L => .L | .D => .D | .S => .S | .R => .R | .C => .C

/-- **The hypotheses that make the field laws a five-type datum**, for one layer set `Λ`: the
`E` law is exchangeable, the `F` law is supported in its support, and the root is
`𝒢₆`-invariant (as laws of objects). -/
structure DatumHyp {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    (lamE lamF : FiniteLaw (Fin 3 × Λ → X)) (lamL : FiniteLaw (ZMod 6 × Λ → X)) : Prop where
  exch : ∀ (σ : Equiv.Perm (Fin 3)) (ω : Fin 3 → Λ → X),
    (objLaw lamE).weight (ω ∘ σ) = (objLaw lamE).weight ω
  supp : ∀ ω, (objLaw lamF).weight ω ≠ 0 → (objLaw lamE).weight ω ≠ 0
  root : ∀ (k : Fin 6) (Ψ : ZMod 6 → Λ → X),
    (objLaw lamL).weight (Ψ ∘ g6 k) = (objLaw lamL).weight Ψ

/-- The five-type datum of field laws on objects carrying one label per layer of `Λ`. -/
noncomputable def fieldDatum {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    {lamE lamF : FiniteLaw (Fin 3 × Λ → X)} {lamL : FiniteLaw (ZMod 6 × Λ → X)}
    (h : DatumHyp lamE lamF lamL) : Datum (Λ → X) :=
  datumOf (objLaw lamE) (objLaw lamF) (objLaw lamL) h.exch h.supp h.root

theorem expect_swap01 {𝔛 : Type*} [Fintype 𝔛] (π : FiniteLaw (Fin 3 → 𝔛))
    (hexch : ∀ (σ : Equiv.Perm (Fin 3)) (ω : Fin 3 → 𝔛), π.weight (ω ∘ σ) = π.weight ω)
    (g : 𝔛 → ℝ) : π.expect (fun ω => g (ω 1)) = π.expect (fun ω => g (ω 0)) := by
  unfold FiniteLaw.expect
  refine Fintype.sum_equiv (Equiv.arrowCongr (Equiv.swap (0 : Fin 3) 1) (Equiv.refl 𝔛)) _ _
    fun ω => ?_
  have he : (Equiv.arrowCongr (Equiv.swap (0 : Fin 3) 1) (Equiv.refl 𝔛)) ω =
      ω ∘ Equiv.swap (0 : Fin 3) 1 := by
    funext j
    simp [Equiv.arrowCongr_apply]
  rw [he, hexch]
  rfl

end MiddleDatum

/-! ## The middle components as push-forwards of the datum's components -/

section Identification

variable {X : Type} [Fintype X] [DecidableEq X]

/-- An emitted law with a middle emission is the push-forward of the pattern image of its law of
objects (two layers). -/
theorem emit_mid_eq {O : Type} [Fintype O] [DecidableEq O] (lam : FiniteLaw (O × Fin 2 → X))
    (φ : ZMod 6 → O) :
    signedIntegral (emit lam (midEmission φ)).weight =
      pushL (lawL (patternLaw φ (objLaw lam))) toSlot₂ := by
  apply LinearMap.ext
  intro f
  rw [← FiniteLaw.expect_eq_signedIntegral, expect_emit, pushL_apply, lawL_apply, patternLaw,
    FiniteLaw.expect_map, expect_objLaw]
  rfl

/-- The same for the one-layer diagonal copy. -/
theorem emit_midDiag_eq {O : Type} [Fintype O] [DecidableEq O] (lam : FiniteLaw (O × Fin 1 → X))
    (φ : ZMod 6 → O) :
    signedIntegral (emit lam (midDiagEmission φ)).weight =
      pushL (lawL (patternLaw φ (objLaw lam))) toSlot₁ := by
  apply LinearMap.ext
  intro f
  rw [← FiniteLaw.expect_eq_signedIntegral, expect_emit, pushL_apply, lawL_apply, patternLaw,
    FiniteLaw.expect_map, expect_objLaw]
  rfl

/-- The merge components: `Π_{G_{sk}}(Γ)` reads the objects `0, 1` of `π_E`. -/
theorem lawL_merge {𝔛 : Type*} [Fintype 𝔛] [DecidableEq 𝔛] (π : FiniteLaw (Fin 3 → 𝔛))
    (s : Fin 2) (k : Fin 3) :
    lawL (patternLaw (merge s k) (gamOf π)) =
      lawL (patternLaw (fun u => (merge s k u).castSucc) π) := by
  apply LinearMap.ext
  intro f
  rw [lawL_apply, lawL_apply, patternLaw, patternLaw, FiniteLaw.expect_map, FiniteLaw.expect_map,
    gamOf, FiniteLaw.expect_map]
  rfl

/-- The constant components: `Π_0(ν)` (`ν` the law of the object `1`) is the constant image of
the object `0`, by exchangeability. -/
theorem lawL_const {𝔛 : Type*} [Fintype 𝔛] [DecidableEq 𝔛] (π : FiniteLaw (Fin 3 → 𝔛))
    (hexch : ∀ (σ : Equiv.Perm (Fin 3)) (ω : Fin 3 → 𝔛), π.weight (ω ∘ σ) = π.weight ω) :
    lawL (patternLaw Datum.constPat ((nuOf π).map fun x _ => x)) =
      lawL (patternLaw (fun _ => (0 : Fin 3)) π) := by
  apply LinearMap.ext
  intro f
  rw [lawL_apply, lawL_apply, patternLaw, patternLaw, FiniteLaw.expect_map, FiniteLaw.expect_map,
    FiniteLaw.expect_map, nuOf, FiniteLaw.expect_map]
  exact expect_swap01 π hexch (fun x => f (fun _ => x))

end Identification

/-! ## The two parts of the middle law as push-forwards of five-type measures -/

section Decomposition

variable {X : Type} [Fintype X] [DecidableEq X]

theorem pushL_sum {Ω Ω' I : Type*} (s : Finset I) (L : I → (Ω → ℝ) →ₗ[ℝ] ℝ) (T : Ω → Ω') :
    pushL (∑ i ∈ s, L i) T = ∑ i ∈ s, pushL (L i) T := by
  apply LinearMap.ext
  intro f
  simp only [pushL_apply, LinearMap.sum_apply]

theorem pushL_smul {Ω Ω' : Type*} (c : ℝ) (L : (Ω → ℝ) →ₗ[ℝ] ℝ) (T : Ω → Ω') :
    pushL (c • L) T = c • pushL L T := rfl

theorem lawL_patternLaw_id {𝔛 : Type*} [Fintype 𝔛] [DecidableEq 𝔛] (π : FiniteLaw (ZMod 6 → 𝔛)) :
    lawL (patternLaw (fun u => u) π) = lawL π := by
  apply LinearMap.ext
  intro f
  rw [lawL_apply, lawL_apply, patternLaw, FiniteLaw.expect_map]
  rfl

theorem sum_ty {M : Type*} [AddCommMonoid M] (f : Ty → M) :
    ∑ t, f t = f .L + (f .D + (f .S + (f .R + f .C))) := by
  rw [show (univ : Finset Ty) = {.L, .D, .S, .R, .C} from rfl]
  simp

/-- **The sum of the two-layer components of a type is the push-forward of `π_t`.** -/
theorem twoLayer_sum (F : MiddleFieldLaws X) (h : DatumHyp (F.two .E) (F.two .F) (F.two .L))
    (t : PType) :
    ∑ φ : t.Pat, signedIntegral (midComponent F (true, ⟨t, φ⟩)).weight =
      pushL ((fieldDatum h).piT (toTy t)) toSlot₂ := by
  cases t
  · rw [Fintype.sum_unique]
    change signedIntegral (emit (F.two .L) (midEmission fun u => u)).weight = _
    rw [emit_mid_eq]
    exact congrArg (fun L => pushL L toSlot₂) (lawL_patternLaw_id _)
  · change ∑ j : Fin 3, signedIntegral (emit (F.two .F) (midEmission (fold j))).weight = _
    simp only [emit_mid_eq]
    rw [show (fieldDatum h).piT (toTy .D) = ∑ j, (fieldDatum h).compF j from rfl, pushL_sum]
    rfl
  · change ∑ s : Fin 2, signedIntegral (emit (F.two .E) (midEmission (matching s))).weight = _
    simp only [emit_mid_eq]
    rw [show (fieldDatum h).piT (toTy .S) = ∑ s, (fieldDatum h).compE s from rfl, pushL_sum]
    rfl
  · change ∑ sk : Fin 2 × Fin 3, signedIntegral (emit (F.two .E)
      (midEmission (fun u => (merge sk.1 sk.2 u).castSucc))).weight = _
    simp only [emit_mid_eq]
    rw [show (fieldDatum h).piT (toTy .R) = ∑ s, ∑ k, (fieldDatum h).compG s k from rfl,
      pushL_sum, Fintype.sum_prod_type]
    refine sum_congr rfl fun s _ => ?_
    rw [pushL_sum]
    refine sum_congr rfl fun k _ => ?_
    change _ = pushL (lawL (patternLaw (merge s k) (gamOf (objLaw (F.two .E))))) toSlot₂
    rw [lawL_merge]
  · change ∑ _k : Fin 2, signedIntegral (emit (F.two .E)
      (midEmission (fun _ => (0 : Fin 3)))).weight = _
    simp only [emit_mid_eq]
    rw [show (fieldDatum h).piT (toTy .C) = ∑ _k : Fin 2, (fieldDatum h).compC from rfl,
      pushL_sum]
    refine sum_congr rfl fun _ _ => ?_
    change _ = pushL (lawL (patternLaw Datum.constPat
      ((nuOf (objLaw (F.two .E))).map fun x _ => x))) toSlot₂
    rw [lawL_const _ h.exch]

/-- **The sum of the one-layer components of a type is the push-forward of `π_t`.** -/
theorem oneLayer_sum (F : MiddleFieldLaws X) (h : DatumHyp (F.one .E) (F.one .F) (F.one .L))
    (t : PType) :
    ∑ φ : t.Pat, signedIntegral (midComponent F (false, ⟨t, φ⟩)).weight =
      pushL ((fieldDatum h).piT (toTy t)) toSlot₁ := by
  cases t
  · rw [Fintype.sum_unique]
    change signedIntegral (emit (F.one .L) (midDiagEmission fun u => u)).weight = _
    rw [emit_midDiag_eq]
    exact congrArg (fun L => pushL L toSlot₁) (lawL_patternLaw_id _)
  · change ∑ j : Fin 3, signedIntegral (emit (F.one .F) (midDiagEmission (fold j))).weight = _
    simp only [emit_midDiag_eq]
    rw [show (fieldDatum h).piT (toTy .D) = ∑ j, (fieldDatum h).compF j from rfl, pushL_sum]
    rfl
  · change ∑ s : Fin 2, signedIntegral (emit (F.one .E) (midDiagEmission (matching s))).weight = _
    simp only [emit_midDiag_eq]
    rw [show (fieldDatum h).piT (toTy .S) = ∑ s, (fieldDatum h).compE s from rfl, pushL_sum]
    rfl
  · change ∑ sk : Fin 2 × Fin 3, signedIntegral (emit (F.one .E)
      (midDiagEmission (fun u => (merge sk.1 sk.2 u).castSucc))).weight = _
    simp only [emit_midDiag_eq]
    rw [show (fieldDatum h).piT (toTy .R) = ∑ s, ∑ k, (fieldDatum h).compG s k from rfl,
      pushL_sum, Fintype.sum_prod_type]
    refine sum_congr rfl fun s _ => ?_
    rw [pushL_sum]
    refine sum_congr rfl fun k _ => ?_
    change _ = pushL (lawL (patternLaw (merge s k) (gamOf (objLaw (F.one .E))))) toSlot₁
    rw [lawL_merge]
  · change ∑ _k : Fin 2, signedIntegral (emit (F.one .E)
      (midDiagEmission (fun _ => (0 : Fin 3)))).weight = _
    simp only [emit_midDiag_eq]
    rw [show (fieldDatum h).piT (toTy .C) = ∑ _k : Fin 2, (fieldDatum h).compC from rfl,
      pushL_sum]
    refine sum_congr rfl fun _ _ => ?_
    change _ = pushL (lawL (patternLaw Datum.constPat
      ((nuOf (objLaw (F.one .E))).map fun x _ => x))) toSlot₁
    rw [lawL_const _ h.exch]


/-- The coefficients of the two-layer part: `w_t r^{deg t}`. -/
noncomputable def twoCoeff (W : MiddleWeights) (r : ℝ) (t : Ty) : ℝ := W.w (ofTy t) * r ^ t.deg

/-- The coefficients of the one-layer part: `v_t r^{deg t + 1}`. -/
noncomputable def oneCoeff (W : MiddleWeights) (r : ℝ) (t : Ty) : ℝ :=
  W.v (ofTy t) * r ^ (t.deg + 1)

/-- **The middle law as two push-forwards of five-type measures**:
`μ̃_𝔅 = e₂(𝒬_{w r^deg}) + e₁(𝒬_{v r^{deg+1}})`, the two-layer part written into the slots by
`(u₀, u₁, ℓ) ↦ Ψ(u₀)(ℓ)` and the one-layer part by `(u₀, u₁, ℓ) ↦ Ψ(u₀)(0)`. -/
theorem middleTilde_eq (F : MiddleFieldLaws X) (h₂ : DatumHyp (F.two .E) (F.two .F) (F.two .L))
    (h₁ : DatumHyp (F.one .E) (F.one .F) (F.one .L)) (W : MiddleWeights) (r : ℝ) :
    middleTilde F W r = pushL ((fieldDatum h₂).Q (twoCoeff W r)) toSlot₂ +
      pushL ((fieldDatum h₁).Q (oneCoeff W r)) toSlot₁ := by
  unfold middleTilde tildeMeasure
  rw [Fintype.sum_prod_type, Fintype.sum_bool, Fintype.sum_sigma, Fintype.sum_sigma]
  have e2 : ∀ t : PType, ∑ φ : t.Pat, midCoeff W r (true, ⟨t, φ⟩) •
      signedIntegral (midComponent F (true, ⟨t, φ⟩)).weight =
        twoCoeff W r (toTy t) • pushL ((fieldDatum h₂).piT (toTy t)) toSlot₂ := by
    intro t
    rw [← twoLayer_sum F h₂ t, Finset.smul_sum]
    refine sum_congr rfl fun φ _ => ?_
    cases t <;> rfl
  have e1 : ∀ t : PType, ∑ φ : t.Pat, midCoeff W r (false, ⟨t, φ⟩) •
      signedIntegral (midComponent F (false, ⟨t, φ⟩)).weight =
        oneCoeff W r (toTy t) • pushL ((fieldDatum h₁).piT (toTy t)) toSlot₁ := by
    intro t
    rw [← oneLayer_sum F h₁ t, Finset.smul_sum]
    refine sum_congr rfl fun φ _ => ?_
    cases t <;> rfl
  simp only [e2, e1]
  unfold Datum.Q
  rw [pushL_sum, pushL_sum, PType.sum_pType, PType.sum_pType, sum_ty, sum_ty]
  rfl

end Decomposition

/-! ## Reflection positivity at the chamber cuts of the first coordinate -/

section FirstCut

variable {X : Type} [Fintype X] [DecidableEq X]

/-- **The rows of `lem:front12:reference`(i)** for the datum of a layer set: at every middle
value `b` with `ν(b) > 0`, `‖T_F^b - J‖ ≤ f r` and `‖T_E^b - J‖ ≤ h r` on `L²(ν^b)`. -/
def RowBounds {Λ : Type} [Fintype Λ] [DecidableEq Λ] (D : Datum (Λ → X)) (f h r : ℝ) : Prop :=
  ∀ b, D.nu.weight b ≠ 0 →
    NormBound (D.nub b) (D.TF b) (f * r) ∧ NormBound (D.nub b) (D.TE b) (h * r)

/-- **The root envelope of `lem:front12:reference`(ii)** at `ϑ₀`: `Π_L ⪰_{ϑ₀} -d r Π_{F₀}`. -/
def RootEnvelope {Λ : Type} [Fintype Λ] [DecidableEq Λ] (D : Datum (Λ → X)) (d r : ℝ) : Prop :=
  (chamberCut 0).Below (-(d * r) • D.compF 0) D.compL

theorem twoCoeff_nonneg (W : MiddleWeights) {r : ℝ} (hr : 0 ≤ r) (t : Ty) : 0 ≤ twoCoeff W r t :=
  mul_nonneg (W.w_nonneg _) (pow_nonneg hr _)

theorem oneCoeff_nonneg (W : MiddleWeights) {r : ℝ} (hr : 0 ≤ r) (t : Ty) : 0 ≤ oneCoeff W r t :=
  mul_nonneg (W.v_nonneg _) (pow_nonneg hr _)

/-- **The two-layer five-type measure is reflection positive at every chamber cut**, from the
first line of the thirteen inequalities, the rows at `j = 2` and the root envelope of L20
(`lem:front12:reference`(iii), via `lem:five-type`(b)). -/
theorem twoLayer_rpAll {Λ : Type} [Fintype Λ] [DecidableEq Λ] (D : Datum (Λ → X))
    (W : MiddleWeights) (I : MiddleInputs) {r : ℝ} (hr : 0 ≤ r) (hW : W.Completes I)
    (hf : 0 ≤ I.f₂) (hrows : RowBounds D I.f₂ I.h₂ r) (hroot : RootEnvelope D I.d r) :
    RPAll (D.Q (twoCoeff W r)) := by
  obtain ⟨hd, h1, h2, h3, -⟩ := hW
  refine D.full_norm_rp (twoCoeff W r) (twoCoeff_nonneg W hr) (mul_nonneg hf hr)
    (fun b hb => (hrows b hb).1) (fun b hb => (hrows b hb).2) ?_ ?_ ?_ (δ := I.d * r) ?_
  · simp only [twoCoeff, ofTy, Ty.deg, pow_one]
    exact mul_le_mul_of_nonneg_right h1 hr
  · simp only [twoCoeff, ofTy, Ty.deg, pow_one]
    have := mul_le_mul_of_nonneg_right h2 (sq_nonneg r)
    nlinarith [this]
  · simp only [twoCoeff, ofTy, Ty.deg]
    have := mul_le_mul_of_nonneg_right h3 (pow_nonneg hr 4)
    nlinarith [this]
  · refine Or.inr ⟨hroot, ?_⟩
    simp only [twoCoeff, ofTy, Ty.deg, pow_zero, pow_one, W.w_L, mul_one]
    exact mul_le_mul_of_nonneg_right hd hr

/-- **The one-layer five-type measure is reflection positive at every chamber cut**, from the
second line of the thirteen inequalities, the rows at `j = 1` and the root envelope of L10. -/
theorem oneLayer_rpAll {Λ : Type} [Fintype Λ] [DecidableEq Λ] (D : Datum (Λ → X))
    (W : MiddleWeights) (I : MiddleInputs) {r : ℝ} (hr : 0 ≤ r) (hW : W.Completes I)
    (hf : 0 ≤ I.f₁) (hrows : RowBounds D I.f₁ I.h₁ r) (hroot : RootEnvelope D I.d₁ r) :
    RPAll (D.Q (oneCoeff W r)) := by
  obtain ⟨-, -, -, -, hd, h1, h2, h3, -⟩ := hW
  refine D.full_norm_rp (oneCoeff W r) (oneCoeff_nonneg W hr) (mul_nonneg hf hr)
    (fun b hb => (hrows b hb).1) (fun b hb => (hrows b hb).2) ?_ ?_ ?_ (δ := I.d₁ * r) ?_
  · simp only [oneCoeff, ofTy, Ty.deg, Nat.reduceAdd]
    exact mul_le_mul_of_nonneg_right h1 (pow_nonneg hr _)
  · simp only [oneCoeff, ofTy, Ty.deg, Nat.reduceAdd]
    have := mul_le_mul_of_nonneg_right h2 (pow_nonneg hr 3)
    nlinarith [this]
  · simp only [oneCoeff, ofTy, Ty.deg, Nat.reduceAdd]
    have := mul_le_mul_of_nonneg_right h3 (pow_nonneg hr 6)
    nlinarith [this]
  · refine Or.inr ⟨hroot, ?_⟩
    simp only [oneCoeff, ofTy, Ty.deg, Nat.reduceAdd]
    have := mul_le_mul_of_nonneg_right hd (sq_nonneg r)
    nlinarith [this]

/-- **`lem:front12:reference`(iii) at the chamber cuts of the first coordinate**: the middle law is
reflection positive at every `ϑ_{0,a}`, given the datum hypotheses, the rows (i) and the root
envelopes (ii) at `ϑ₀` of both layer sets, and the thirteen inequalities. -/
theorem middleTilde_firstCut_positive (F : MiddleFieldLaws X)
    (h₂ : DatumHyp (F.two .E) (F.two .F) (F.two .L))
    (h₁ : DatumHyp (F.one .E) (F.one .F) (F.one .L))
    (W : MiddleWeights) (I : MiddleInputs) {r : ℝ} (hr : 0 ≤ r) (hW : W.Completes I)
    (hf₂ : 0 ≤ I.f₂) (hf₁ : 0 ≤ I.f₁)
    (hrows₂ : RowBounds (fieldDatum h₂) I.f₂ I.h₂ r)
    (hrows₁ : RowBounds (fieldDatum h₁) I.f₁ I.h₁ r)
    (hroot₂ : RootEnvelope (fieldDatum h₂) I.d r) (hroot₁ : RootEnvelope (fieldDatum h₁) I.d₁ r)
    (a : Chamber) : (firstChamberCut a).Positive (middleTilde F W r) := by
  rw [middleTilde_eq F h₂ h₁]
  refine ReflectionCut.Positive.add ?_ ?_
  · exact pushL_firstCut_positive (fun y p => y (layerFin p.2)) _ a
      (twoLayer_rpAll _ W I hr hW hf₂ hrows₂ hroot₂ a)
  · exact pushL_firstCut_positive (fun y _ => y 0) _ a
      (oneLayer_rpAll _ W I hr hW hf₁ hrows₁ hroot₁ a)

end FirstCut

/-! ## The datum hypotheses for the paper's block laws -/

section BlockDatum

variable {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]

/-- The weight of a tensor of laws is the product of the factor weights. -/
theorem tensor_weight {J V : Type*} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    {Y : J → Type*} [∀ j, Fintype (Y j)] [∀ j, DecidableEq (Y j)] (μ : ∀ j, FiniteLaw (V → Y j))
    (z : V → ∀ j, Y j) : (FiniteLaw.tensor μ).weight z = ∏ j, (μ j).weight (fun v => z v j) := by
  rw [weight_eq_expect, expect_tensor_eq_sum]
  rw [Finset.sum_eq_single (fun j v => z v j)]
  · simp
  · intro z' _ hz'
    have : (fun v j => z' j v) ≠ z := by
      intro h
      apply hz'
      funext j v
      rw [← h]
    simp [this]
  · intro h
    exact absurd (mem_univ _) h

/-- A relabelling of the vertices, as a bijection of labellings. -/
def relabelEquiv {W Y : Type*} (π : W ≃ W) : (W → Y) ≃ (W → Y) where
  toFun z := z ∘ π
  invFun z := z ∘ π.symm
  left_inv z := by funext w; simp
  right_inv z := by funext w; simp

/-- The weight of a block law is invariant under graph automorphisms. -/
theorem blockGraphLaw_weight_auto {W : Type} [Fintype W] [DecidableEq W] (G : OrientedGraph W)
    (hne : ∀ i, (injLabellings (ZMod (pr i)) G).Nonempty) (π : W ≃ W) (hπ : IsAutomorphism G π)
    (z : W → BlockLabel pr) :
    (blockGraphLaw pr G hne).weight (z ∘ π) = (blockGraphLaw pr G hne).weight z :=
  weight_comp_of_expect _ (relabelEquiv π) (fun f => blockGraphLaw_expect_auto pr G hne π hπ f) z

/-- **Exchangeability of the `E` law**, as a law of objects. -/
theorem objLaw_match_exch {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    (hne : ∀ i, (injLabellings (ZMod (pr i)) (matchGraph Λ)).Nonempty)
    (σ : Equiv.Perm (Fin 3)) (ω : Fin 3 → Λ → BlockLabel pr) :
    (objLaw (blockGraphLaw pr (matchGraph Λ) hne)).weight (ω ∘ σ) =
      (objLaw (blockGraphLaw pr (matchGraph Λ) hne)).weight ω := by
  rw [objLaw_weight, objLaw_weight]
  exact blockGraphLaw_weight_auto pr (matchGraph Λ) hne (Equiv.prodCongr σ (Equiv.refl Λ))
    (matchGraph_auto Λ _) (fun p => ω p.1 p.2)

/-- `Inj(G_F) ⊆ Inj(G_E)`: the `E` graph has no edges. -/
theorem fold_inj_sub_match {Λ : Type} [Fintype Λ] [DecidableEq Λ] {F' : Type*} [Field F']
    [Fintype F'] [DecidableEq F'] (y : Fin 3 × Λ → F') (hy : y ∈ injLabellings F' (foldGraph Λ)) :
    y ∈ injLabellings F' (matchGraph Λ) := by
  rw [mem_injLabellings_iff_feasible] at hy ⊢
  exact ⟨hy.1, fun e he => absurd he (Finset.notMem_empty e)⟩

theorem graphLaw_weight_ne_zero {W : Type*} [Fintype W] [DecidableEq W] {F' : Type*} [Field F']
    [Fintype F'] [DecidableEq F'] (G : OrientedGraph W) (hne : (injLabellings F' G).Nonempty)
    (y : W → F') : (graphLaw G hne).weight y ≠ 0 ↔ y ∈ injLabellings F' G := by
  change (if y ∈ injLabellings F' G then 1 / ((injLabellings F' G).card : ℝ) else 0) ≠ 0 ↔ _
  split_ifs with h
  · have : ((injLabellings F' G).card : ℝ) ≠ 0 := by exact_mod_cast (card_pos.mpr hne).ne'
    simp [h, this]
  · simp [h]

/-- **The `F` law is supported in the support of the `E` law**, as laws of objects. -/
theorem objLaw_fold_supp {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    (hF : ∀ i, (injLabellings (ZMod (pr i)) (foldGraph Λ)).Nonempty)
    (hE : ∀ i, (injLabellings (ZMod (pr i)) (matchGraph Λ)).Nonempty)
    (ω : Fin 3 → Λ → BlockLabel pr)
    (h : (objLaw (blockGraphLaw pr (foldGraph Λ) hF)).weight ω ≠ 0) :
    (objLaw (blockGraphLaw pr (matchGraph Λ) hE)).weight ω ≠ 0 := by
  rw [objLaw_weight] at h ⊢
  unfold blockGraphLaw at h ⊢
  rw [tensor_weight] at h ⊢
  rw [Finset.prod_ne_zero_iff] at h ⊢
  intro i _
  have hi := (graphLaw_weight_ne_zero _ _ _).mp (h i (mem_univ i))
  exact (graphLaw_weight_ne_zero _ _ _).mpr (fold_inj_sub_match _ hi)

/-- The elements of `𝒢₆` as bijections of `ℤ/6ℤ`. -/
noncomputable def g6Equiv (k : Fin 6) : ZMod 6 ≃ ZMod 6 := Equiv.ofBijective _ (g6_bijective k)

/-- **`𝒢₆` acts by automorphisms of the twelve-label root** (on the first coordinate). -/
theorem recordGraph_g6 (Λ : Type) [Fintype Λ] (k : Fin 6) :
    IsAutomorphism (recordGraph Λ) (Equiv.prodCongr (g6Equiv k) (Equiv.refl Λ)) := by
  have key : ∀ (k : Fin 6) (u v : ZMod 6), g6 k v = rot (g6 k u) ↔ v = rot u := by decide
  intro u v
  simp only [mem_recordGraph, Equiv.prodCongr_apply, Prod.map, g6Equiv, Equiv.ofBijective_apply]
  exact key k u.1 v.1

/-- **The uniform root is `𝒢₆`-invariant**, as a law of objects. -/
theorem objLaw_root_inv {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    (hne : ∀ i, (injLabellings (ZMod (pr i)) (recordGraph Λ)).Nonempty)
    (k : Fin 6) (Ψ : ZMod 6 → Λ → BlockLabel pr) :
    (objLaw (blockGraphLaw pr (recordGraph Λ) hne)).weight (Ψ ∘ g6 k) =
      (objLaw (blockGraphLaw pr (recordGraph Λ) hne)).weight Ψ := by
  rw [objLaw_weight, objLaw_weight]
  exact blockGraphLaw_weight_auto pr (recordGraph Λ) hne
    (Equiv.prodCongr (g6Equiv k) (Equiv.refl Λ)) (recordGraph_g6 Λ k) (fun p => Ψ p.1 p.2)

/-- **The datum hypotheses for the paper's middle block laws** with the uniform root: two layers. -/
theorem middleBlock_datumHyp₂ (hne : MiddleNonempty pr) :
    DatumHyp (blockGraphLaw pr (matchGraph (Fin 2)) hne.E2)
      (blockGraphLaw pr (foldGraph (Fin 2)) hne.F2) (uniformRoot pr hne) :=
  ⟨objLaw_match_exch pr hne.E2, objLaw_fold_supp pr hne.F2 hne.E2, objLaw_root_inv pr hne.L2⟩

/-- One layer. -/
theorem middleBlock_datumHyp₁ (hne : MiddleNonempty pr) :
    DatumHyp (blockGraphLaw pr (matchGraph (Fin 1)) hne.E1)
      (blockGraphLaw pr (foldGraph (Fin 1)) hne.F1)
      (blockGraphLaw pr (recordGraph (Fin 1)) hne.L1) :=
  ⟨objLaw_match_exch pr hne.E1, objLaw_fold_supp pr hne.F1 hne.E1, objLaw_root_inv pr hne.L1⟩

end BlockDatum

/-! ## Reflection positivity of the middle block law at every cut of the family -/

section Family

variable {ι : Type} [Fintype ι] [DecidableEq ι] (pr : ι → ℕ) [∀ i, Fact (pr i).Prime]

/-- **(R2) for the middle block law with the uniform root** (`lem:front12:reference`(iii) on the
pieces below `2³⁰`): reflection positive at every cut of the family `𝔉` — the chamber cuts of
both coordinates and `ι` — given the thirteen inequalities and, as hypotheses, the rows (i) at
`j = 1, 2`, the root envelopes (ii) of L20 and L10, and the layer caps (ii) at `ι`. -/
theorem middleBlockReference_uniform_familyPositive (hne : MiddleNonempty pr) (W : MiddleWeights)
    (I : MiddleInputs) {r : ℝ} (hr : 0 ≤ r) (hW : W.Completes I) (hf₂ : 0 ≤ I.f₂)
    (hf₁ : 0 ≤ I.f₁)
    (hrows₂ : RowBounds (fieldDatum (middleBlock_datumHyp₂ pr hne)) I.f₂ I.h₂ r)
    (hrows₁ : RowBounds (fieldDatum (middleBlock_datumHyp₁ pr hne)) I.f₁ I.h₁ r)
    (hroot₂ : RootEnvelope (fieldDatum (middleBlock_datumHyp₂ pr hne)) I.d r)
    (hroot₁ : RootEnvelope (fieldDatum (middleBlock_datumHyp₁ pr hne)) I.d₁ r)
    (hcap : MiddleLayerCaps (middleBlockFieldLaws pr hne (uniformRoot pr hne)) I.k r) :
    TheoremC.FamilyReflectionPositive
      (signedIntegral (middleBlockReference pr hne (uniformRoot pr hne) W hr).weight) := by
  have hdom : ∀ t, I.k t * W.w t ≤ W.v t := hW.2.2.2.2.2.2.2.2
  refine middleReference_familyPositive _ W I.k hr hcap hdom fun a => ?_
  rw [middleReference_eq]
  exact (middleTilde_firstCut_positive (middleBlockFieldLaws pr hne (uniformRoot pr hne))
    (middleBlock_datumHyp₂ pr hne) (middleBlock_datumHyp₁ pr hne) W I hr hW hf₂ hf₁
    hrows₂ hrows₁ hroot₂ hroot₁ a).smul
    (inv_nonneg.mpr (le_trans zero_le_one (one_le_midPoly W hr)))

end Family

end Sarkozy.PartV
