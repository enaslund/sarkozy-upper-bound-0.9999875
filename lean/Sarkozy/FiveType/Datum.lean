module

public import Sarkozy.Labellings.Patterns
public import Sarkozy.Reflection.ChamberIid




@[expose] public section

open scoped BigOperators

namespace Sarkozy.FiveType

open Sarkozy.Labellings

/-! ## The five types -/

/-- The five types `L, D, S, R, C` (root, folds, matchings, merges, constants) of
`def:patterns`. -/
inductive Ty
  | L
  | D
  | S
  | R
  | C
  deriving DecidableEq

instance : Fintype Ty where
  elems := {.L, .D, .S, .R, .C}
  complete := by intro t; cases t <;> decide

/-- The formal degrees `0, 1, 1, 2, 3` of the types (`def:patterns`). -/
def Ty.deg : Ty → ℕ
  | .L => 0
  | .D => 1
  | .S => 1
  | .R => 2
  | .C => 3

/-! ## The group `𝒢₆` -/

/-- The six elements of `𝒢₆`: `u ↦ u + 2k` for `k < 3`, and `u ↦ 2(k - 3) + 1 - u` for
`k ≥ 3`, that is `1 - u`, `3 - u`, `5 - u`. -/
def g6 (k : Fin 6) (u : ZMod 6) : ZMod 6 :=
  if (k : ℕ) < 3 then u + 2 * ((k : ℕ) : ZMod 6) else 2 * (((k : ℕ) - 3 : ℕ) : ZMod 6) + 1 - u

/-- A functional on configurations is invariant under `𝒢₆`. -/
def Inv6 {X : Type*} (L : ((ZMod 6 → X) → ℝ) →ₗ[ℝ] ℝ) : Prop :=
  ∀ (k : Fin 6) (f : (ZMod 6 → X) → ℝ), L (fun Ψ => f (Ψ ∘ g6 k)) = L f

/-- **Reflection positive at every chamber cut** `ϑ_i`, `i ∈ ℤ/6ℤ`. -/
def RPAll {X : Type*} (L : ((ZMod 6 → X) → ℝ) →ₗ[ℝ] ℝ) : Prop :=
  ∀ i : ZMod 6, (chamberCut i).Positive L

/-! ## Laws as functionals, and `L²(μ)` -/

variable {𝔛 : Type*} [Fintype 𝔛] [DecidableEq 𝔛]

/-- The integral against a finite law, as a linear functional. -/
noncomputable def lawL {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω) : (Ω → ℝ) →ₗ[ℝ] ℝ :=
  signedIntegral μ.weight

theorem lawL_apply {Ω : Type*} [Fintype Ω] (μ : FiniteLaw Ω) (f : Ω → ℝ) :
    lawL μ f = μ.expect f := rfl

/-- The inner product of `L²(μ)`. -/
noncomputable def ip (μ : FiniteLaw 𝔛) (U V : 𝔛 → ℝ) : ℝ := μ.expect (fun x => U x * V x)

/-- The (semi)norm of `L²(μ)`. -/
noncomputable def nrm (μ : FiniteLaw 𝔛) (U : 𝔛 → ℝ) : ℝ := Real.sqrt (ip μ U U)

/-- `⟨U, T V⟩_{L²(μ)}` for the kernel `T` relative to `μ ⊗ μ`, where
`T h(x) = ∑_y μ(y) T(x, y) h(y)`. -/
noncomputable def kf (μ : FiniteLaw 𝔛) (T : 𝔛 → 𝔛 → ℝ) (U V : 𝔛 → ℝ) : ℝ :=
  ∑ x, ∑ y, μ.weight x * μ.weight y * (U x * T x y * V y)

/-- The function `T𝟙`, `x ↦ ∑_y μ(y) T(x, y)`. -/
noncomputable def kone (μ : FiniteLaw 𝔛) (T : 𝔛 → 𝔛 → ℝ) (x : 𝔛) : ℝ :=
  ∑ y, μ.weight y * T x y

/-- The function `T*𝟙`, `y ↦ ∑_x μ(x) T(x, y)`. -/
noncomputable def kone' (μ : FiniteLaw 𝔛) (T : 𝔛 → 𝔛 → ℝ) (y : 𝔛) : ℝ :=
  ∑ x, μ.weight x * T x y

/-- The centred part `(I - J)h = h - E_μ h`. -/
noncomputable def cen (μ : FiniteLaw 𝔛) (h : 𝔛 → ℝ) (x : 𝔛) : ℝ := h x - μ.expect h

/-- **`‖A‖ ≤ e` on `L²(μ)`** for the operator with kernel `A`, as a bound of its form. -/
def FormBound (μ : FiniteLaw 𝔛) (A : 𝔛 → 𝔛 → ℝ) (e : ℝ) : Prop :=
  ∀ Φ Ψ : 𝔛 → ℝ, |kf μ A Φ Ψ| ≤ e * nrm μ Φ * nrm μ Ψ

/-- **`‖T - J‖ ≤ e` on `L²(μ)`**: `|⟨Φ, TΨ⟩ - E Φ E Ψ| ≤ e ‖Φ‖ ‖Ψ‖`. -/
def NormBound (μ : FiniteLaw 𝔛) (T : 𝔛 → 𝔛 → ℝ) (e : ℝ) : Prop :=
  ∀ Φ Ψ : 𝔛 → ℝ, |kf μ T Φ Ψ - μ.expect Φ * μ.expect Ψ| ≤ e * nrm μ Φ * nrm μ Ψ

/-- **`‖(I - J)T(I - J)‖ ≤ q` on `L²(μ)`**: the bound of the form on centred functions. -/
def PerpBound (μ : FiniteLaw 𝔛) (T : 𝔛 → 𝔛 → ℝ) (q : ℝ) : Prop :=
  ∀ Φ Ψ : 𝔛 → ℝ, μ.expect Φ = 0 → μ.expect Ψ = 0 → |kf μ T Φ Ψ| ≤ q * nrm μ Φ * nrm μ Ψ

/-- **`T` annihilates the constants on both sides**: `T𝟙 = T*𝟙 = 0` in `L²(μ)`. -/
def Annihilates (μ : FiniteLaw 𝔛) (T : 𝔛 → 𝔛 → ℝ) : Prop :=
  (∀ x, μ.weight x ≠ 0 → kone μ T x = 0) ∧ (∀ y, μ.weight y ≠ 0 → kone' μ T y = 0)

/-- **Exact marginals** `T𝟙 = T*𝟙 = 𝟙` in `L²(μ)`. -/
def ExactMarginals (μ : FiniteLaw 𝔛) (T : 𝔛 → 𝔛 → ℝ) : Prop :=
  (∀ x, μ.weight x ≠ 0 → kone μ T x = 1) ∧ (∀ y, μ.weight y ≠ 0 → kone' μ T y = 1)

/-- The quadratic form of `E = ½(T + T*) - J`: `⟨Φ, TΦ⟩ - (E Φ)²`. -/
noncomputable def eform (μ : FiniteLaw 𝔛) (T : 𝔛 → 𝔛 → ℝ) (Φ : 𝔛 → ℝ) : ℝ :=
  kf μ T Φ Φ - μ.expect Φ ^ 2

/-! ## The datum -/

/-- **`def:five-type-datum`.** A five-type datum on the finite set `𝔛`:
* (i) the middle law `ν` and the conditional references `ν^b`;
* (ii) the symmetric law `Γ` on `𝔛^{0,1}` with `Γ(ω) = ν(ω₁) ν^{ω₁}(ω₀)`;
* (iii) the exchangeable matching law `π_E` on `𝔛^{0,1,2}` with
  `π_E(ω) = ν(ω₁) ν^{ω₁}(ω₀) ν^{ω₁}(ω₂) T_E^{ω₁}(ω₀, ω₂)`;
* (iv) the fold law `π_F` with `π_F(ω) = ν(ω₁) ν^{ω₁}(ω₀) ν^{ω₁}(ω₂) T_F^{ω₁}(ω₀, ω₂)`;
* (v) the root `π_L` on `𝔛^{ℤ/6ℤ}`, invariant under `𝒢₆`;

with nonnegative kernels `T_E^b`, `T_F^b`. Exchangeability, symmetry and invariance are stated
on the weights: the weight is unchanged by every permutation of the objects (resp. by the swap,
by every `α ∈ 𝒢₆`). -/
structure Datum (𝔛 : Type*) [Fintype 𝔛] [DecidableEq 𝔛] where
  /-- (i) the middle law -/
  nu : FiniteLaw 𝔛
  /-- (i) the conditional references -/
  nub : 𝔛 → FiniteLaw 𝔛
  /-- (ii) the merge law -/
  Gam : FiniteLaw (Fin 2 → 𝔛)
  Gam_weight : ∀ ω, Gam.weight ω = nu.weight (ω 1) * (nub (ω 1)).weight (ω 0)
  Gam_symm : ∀ ω, Gam.weight (ω ∘ Equiv.swap 0 1) = Gam.weight ω
  /-- (iii) the matching law and its kernel -/
  piE : FiniteLaw (Fin 3 → 𝔛)
  TE : 𝔛 → 𝔛 → 𝔛 → ℝ
  TE_nonneg : ∀ b x y, 0 ≤ TE b x y
  piE_weight : ∀ ω, piE.weight ω =
    nu.weight (ω 1) * (nub (ω 1)).weight (ω 0) * (nub (ω 1)).weight (ω 2) * TE (ω 1) (ω 0) (ω 2)
  piE_exch : ∀ (σ : Equiv.Perm (Fin 3)) (ω : Fin 3 → 𝔛), piE.weight (ω ∘ σ) = piE.weight ω
  /-- (iv) the fold law and its kernel -/
  piF : FiniteLaw (Fin 3 → 𝔛)
  TF : 𝔛 → 𝔛 → 𝔛 → ℝ
  TF_nonneg : ∀ b x y, 0 ≤ TF b x y
  piF_weight : ∀ ω, piF.weight ω =
    nu.weight (ω 1) * (nub (ω 1)).weight (ω 0) * (nub (ω 1)).weight (ω 2) * TF (ω 1) (ω 0) (ω 2)
  /-- (v) the root -/
  piL : FiniteLaw (ZMod 6 → 𝔛)
  piL_inv : ∀ (k : Fin 6) (Ψ : ZMod 6 → 𝔛), piL.weight (Ψ ∘ g6 k) = piL.weight Ψ

namespace Datum

variable (D : Datum 𝔛)

/-- `ν` as a law on `𝔛^{0}`, for the constant pattern. -/
noncomputable def nu1 : FiniteLaw (Fin 1 → 𝔛) := D.nu.map (fun x _ => x)

/-- The constant pattern `0` (`C_0 = C_1`). -/
def constPat : ZMod 6 → Fin 1 := fun _ => 0

/-- The root component `Π_L = π_L`. -/
noncomputable def compL : ((ZMod 6 → 𝔛) → ℝ) →ₗ[ℝ] ℝ := lawL D.piL

/-- The fold component `Π_{F_j}(π_F)`. -/
noncomputable def compF (j : Fin 3) : ((ZMod 6 → 𝔛) → ℝ) →ₗ[ℝ] ℝ :=
  lawL (patternLaw (fold j) D.piF)

/-- The matching component `Π_{E_s}(π_E)`. -/
noncomputable def compE (s : Fin 2) : ((ZMod 6 → 𝔛) → ℝ) →ₗ[ℝ] ℝ :=
  lawL (patternLaw (matching s) D.piE)

/-- The merge component `Π_{G_{sk}}(Γ)`. -/
noncomputable def compG (s : Fin 2) (k : Fin 3) : ((ZMod 6 → 𝔛) → ℝ) →ₗ[ℝ] ℝ :=
  lawL (patternLaw (merge s k) D.Gam)

/-- The constant component `Π_{C_0} = Π_{C_1} = Π_0(ν)`. -/
noncomputable def compC : ((ZMod 6 → 𝔛) → ℝ) →ₗ[ℝ] ℝ :=
  lawL (patternLaw constPat D.nu1)

/-- `π_t`, the sum of the components of the type `t` (two copies `C_0, C_1` for `t = C`). -/
noncomputable def piT : Ty → ((ZMod 6 → 𝔛) → ℝ) →ₗ[ℝ] ℝ
  | .L => D.compL
  | .D => ∑ j, D.compF j
  | .S => ∑ s, D.compE s
  | .R => ∑ s, ∑ k, D.compG s k
  | .C => ∑ _k : Fin 2, D.compC

/-- **The five-type measure** `𝒬_a = ∑_t a_t π_t`. -/
noncomputable def Q (a : Ty → ℝ) : ((ZMod 6 → 𝔛) → ℝ) →ₗ[ℝ] ℝ := ∑ t, a t • D.piT t

end Datum

/-! ## Fold data and joint data at one middle value -/

/-- **The fold data of `lem:five-type`(c)** for `K = T_F^b` on `L²(μ)`, `μ = ν^b`:
`m = ⟨𝟙, K𝟙⟩ ∈ [H⁻¹, H]`, `‖(I-J)K𝟙‖, ‖(I-J)K*𝟙‖ ≤ β`, `‖(I-J)K(I-J)‖ ≤ q⊥`. -/
structure FoldData (μ : FiniteLaw 𝔛) (K : 𝔛 → 𝔛 → ℝ) (H β qperp : ℝ) : Prop where
  mass_lower : H⁻¹ ≤ kf μ K (fun _ => 1) (fun _ => 1)
  mass_upper : kf μ K (fun _ => 1) (fun _ => 1) ≤ H
  row : nrm μ (cen μ (kone μ K)) ≤ β
  col : nrm μ (cen μ (kone' μ K)) ≤ β
  perp : PerpBound μ K qperp

/-- **The joint data of `lem:five-type`(f)** for `K = T_F^b` and `T_E = T_E^b` on `L²(μ)`:
`K = m(φ₀ ⊗ φ₂ + C + R)` with `m ∈ [H⁻¹, H]`, `E φ₀ = E φ₂ = 1`, `‖φ_o - 𝟙‖ ≤ υ`, `C` and `R`
annihilating the constants on both sides, `‖R‖ ≤ ε_T`, and, with `E = ½(T_E + T_E*) - J`,
`E ⪰ -ε_E I` and `(E C; C* E) ⪰ -κ_J I` on `L²(μ) ⊕ L²(μ)`. -/
structure JointData (μ : FiniteLaw 𝔛) (TE K : 𝔛 → 𝔛 → ℝ) (H υ εT εE κJ : ℝ) where
  m : ℝ
  φ0 : 𝔛 → ℝ
  φ2 : 𝔛 → ℝ
  C : 𝔛 → 𝔛 → ℝ
  R : 𝔛 → 𝔛 → ℝ
  decomp : ∀ x y, K x y = m * (φ0 x * φ2 y + C x y + R x y)
  m_lower : H⁻¹ ≤ m
  m_upper : m ≤ H
  mean0 : μ.expect φ0 = 1
  mean2 : μ.expect φ2 = 1
  dev0 : nrm μ (fun x => φ0 x - 1) ≤ υ
  dev2 : nrm μ (fun x => φ2 x - 1) ≤ υ
  annC : Annihilates μ C
  annR : Annihilates μ R
  normR : FormBound μ R εT
  lowerE : ∀ Φ : 𝔛 → ℝ, -εE * nrm μ Φ ^ 2 ≤ eform μ TE Φ
  joint : ∀ Φ Ψ : 𝔛 → ℝ,
    -κJ * (nrm μ Φ ^ 2 + nrm μ Ψ ^ 2) ≤ eform μ TE Φ + 2 * kf μ C Φ Ψ + eform μ TE Ψ

/-- The joint row coefficient `f_J` of `lem:five-type`(f) (graded form):
`f_J = (H((k_J - h)_+ r + ε_T) + (H + H²/t_Y)υ²)/r`. -/
noncomputable def fJ (H kJ h r εT tY υ : ℝ) : ℝ :=
  (H * (max (kJ - h) 0 * r + εT) + (H + H ^ 2 / tY) * υ ^ 2) / r

end Sarkozy.FiveType
