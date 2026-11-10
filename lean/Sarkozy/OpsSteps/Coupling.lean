module

public import Sarkozy.EnvelopeSteps.Multiplicative
public import Sarkozy.Envelopes.OrbitCoupon

@[expose] public section

/-!
# The coupling expansion `D_ω = ∑_C c(C) C` of a lifted envelope (OPS-S)

`paper/sections/23_envelopes.tex`, `lem:oct24:mask-schur`(a), last assertion ("`Lift(D)` … is a
finite real combination `∑_C c(C) C` of tensor products `C` of the normalized nonnegative couplings
`M_{ab}, P₁₂, P₀₁, 𝒥` of a fold factor and `M_{ab}, 𝒥` of a matching factor, all with the actual
half marginals; after equal products are collected, `M(D) = ∑_C |c(C)|` is its coupling mass") and
its proof ("the expansions `V_a V_b^* = M_{ab} − 𝒥` and" the definition of `Q_{ij}`);
`lem:oct24:pure-pair-substitute` (`Q_{ij} = P_{ij} − (P_i + P_j)/(1 + ρ) + (1 − ρ)/(1 + ρ) 𝒥`,
`M_{ii} = P_i`); proof of `thm:envelopes`, Step 3 ("The chart unitaries conjugate the coupling basis
into itself … and `∑_C |c(C)| = M(D_{(ω)})`").

`Lift(D)` replaces, in every factor, a matrix unit `e_{ab}` of the label alphabet by an operator
`U_𝔟(a, b)` on `L²(m_𝔟)` (the *unit lift*), and every unit lift is a real combination of the basic
couplings of the factor. At the level of kernels relative to the product marginal
`m_ω = ⊗_𝔟 m_𝔟` (which is all the placement sees, `Step3.place_eq_of_kern`):

* `kern_sum_smul`: the kernel is linear in the operator;
* **`kern_lift_expand`**: if `kern(Lift D)(x, y) = ∑_{v,w} D_{vw} ∏_𝔟 kern(U_𝔟(v_𝔟, w_𝔟))(x_𝔟, y_𝔟)`
  and `kern(U_𝔟(a, b)) = ∑_k c_𝔟(a, b, k) kern(C_{𝔟,k})`, then
  `kern(Lift D) = ∑_κ c(κ) kern(⊗_𝔟 C_{𝔟,κ_𝔟})` over the coupling words `κ`, with the collected
  coefficient `c(κ) = ∑_{v,w} D_{vw} ∏_𝔟 c_𝔟(v_𝔟, w_𝔟, κ_𝔟)` (`liftCoef`); this is the input `hD`
  of `Step3.step3_orbit`, and `M(D) = ∑_κ |c(κ)|` (`couplingMass`);
* the paper's unit tables: `FoldCpl` (`M_{ab}` for `a, b ∈ {0,1,2}`, `P₁₂`, `P₀₁`, `𝒥`; twelve
  couplings), `foldUnit ρ` (`e_{ab} ↦ M_{ab} − 𝒥` for singleton labels, `e₃₃ ↦ Q₁₂`, `e₄₄ ↦ Q₀₁`,
  and `0` off the blocks `{0,1,2}, {3}, {4}` of `𝒜_F`); `MatchCpl`, `matchUnit`
  (`e_{ab} ↦ M_{ab} − 𝒥`); `foldUnit_singleton`, `foldUnit_33`, `foldUnit_44`, `matchUnit_apply`
  record the entries;
* `couplingMass_comp_equiv`: a relabelling of the couplings (the chart conjugations
  `𝒰_ω (·) 𝒰_ω^*`, which permute the coupling basis) does not change the coupling mass.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.OpsSteps

open Sarkozy.EnvelopeSteps Sarkozy.Envelopes

/-! ## The kernel is linear -/

section Linear

variable {O : Type*} [Fintype O] [DecidableEq O]

omit [Fintype O] in
/-- **The kernel is linear in the operator.** -/
theorem kern_sum_smul (m : O → ℝ) {ι : Type*} (s : Finset ι) (c : ι → ℝ)
    (K : ι → (O → ℝ) →ₗ[ℝ] (O → ℝ)) (x y : O) :
    kern m (∑ i ∈ s, c i • K i) x y = ∑ i ∈ s, c i * kern m (K i) x y := by
  unfold kern
  rw [LinearMap.sum_apply, Finset.sum_apply, mul_sum]
  refine sum_congr rfl fun i _ => ?_
  rw [LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul]
  ring

end Linear

/-! ## The expansion of a tensor lift over the coupling words -/

section Expand

variable {S : Type*} [Fintype S] [DecidableEq S]
  {O : S → Type*} [∀ b, Fintype (O b)] [∀ b, DecidableEq (O b)]
  {Lb : S → Type*} [∀ b, Fintype (Lb b)]
  {Kb : S → Type*} [∀ b, Fintype (Kb b)]

/-- **The collected coefficient of a coupling word** `κ`:
`c(κ) = ∑_{v,w} D_{vw} ∏_𝔟 c_𝔟(v_𝔟, w_𝔟, κ_𝔟)`. -/
noncomputable def liftCoef (cu : ∀ b, Lb b → Lb b → Kb b → ℝ) (Dm : (∀ b, Lb b) → (∀ b, Lb b) → ℝ)
    (κ : ∀ b, Kb b) : ℝ :=
  ∑ v, ∑ w, Dm v w * ∏ b, cu b (v b) (w b) (κ b)

omit [∀ b, Fintype (O b)] in
/-- **The coupling expansion of a tensor lift** (`lem:oct24:mask-schur`(a), last assertion), at the
level of kernels relative to the product marginal. If the kernel of `Lift(D)` is
`∑_{v,w} D_{vw} ∏_𝔟 kern(U_𝔟(v_𝔟, w_𝔟))(x_𝔟, y_𝔟)` (`hLift`, the definition of the lift by unit
replacement, the units acting on distinct tensor factors), every unit lift is a combination
`∑_k c_𝔟(a, b, k) C_{𝔟,k}` of basic couplings (`hU`), and `C_κ` is the tensor product of the
`C_{𝔟,κ_𝔟}` (`hCop`), then `kern(Lift D) = ∑_κ c(κ) kern(C_κ)`. -/
theorem kern_lift_expand (m : ∀ b, O b → ℝ)
    (U : ∀ b, Lb b → Lb b → (O b → ℝ) →ₗ[ℝ] (O b → ℝ))
    (Cpl : ∀ b, Kb b → (O b → ℝ) →ₗ[ℝ] (O b → ℝ)) (cu : ∀ b, Lb b → Lb b → Kb b → ℝ)
    (hU : ∀ b a a' x y, kern (m b) (U b a a') x y = ∑ k, cu b a a' k * kern (m b) (Cpl b k) x y)
    (Dm : (∀ b, Lb b) → (∀ b, Lb b) → ℝ) (Dop : ((∀ b, O b) → ℝ) →ₗ[ℝ] ((∀ b, O b) → ℝ))
    (hLift : ∀ x y, kern (prodWeight m) Dop x y =
      ∑ v, ∑ w, Dm v w * ∏ b, kern (m b) (U b (v b) (w b)) (x b) (y b))
    (Cop : (∀ b, Kb b) → ((∀ b, O b) → ℝ) →ₗ[ℝ] ((∀ b, O b) → ℝ))
    (hCop : ∀ κ x y, kern (prodWeight m) (Cop κ) x y = ∏ b, kern (m b) (Cpl b (κ b)) (x b) (y b))
    (x y : ∀ b, O b) :
    kern (prodWeight m) Dop x y = ∑ κ, liftCoef cu Dm κ * kern (prodWeight m) (Cop κ) x y := by
  rw [hLift]
  simp only [hU, hCop, liftCoef]
  have hprod : ∀ v w : ∀ b, Lb b,
      ∏ b, ∑ k, cu b (v b) (w b) k * kern (m b) (Cpl b k) (x b) (y b) =
        ∑ κ : ∀ b, Kb b, (∏ b, cu b (v b) (w b) (κ b)) *
          ∏ b, kern (m b) (Cpl b (κ b)) (x b) (y b) := by
    intro v w
    rw [Fintype.prod_sum]
    exact sum_congr rfl fun κ _ => prod_mul_distrib
  simp only [hprod, mul_sum, sum_mul]
  symm
  refine Finset.sum_comm.trans (sum_congr rfl fun v _ => ?_)
  refine Finset.sum_comm.trans (sum_congr rfl fun w _ => sum_congr rfl fun κ _ => ?_)
  ring

/-- **A relabelling of the couplings does not change the coupling mass** (the chart conjugations
permute the coupling basis, proof of `thm:envelopes`, Step 3). -/
theorem couplingMass_comp_equiv {ι : Type*} [Fintype ι] (c : ι → ℝ) (σ : ι ≃ ι) :
    couplingMass (c ∘ σ) = couplingMass c := by
  unfold couplingMass
  exact Equiv.sum_comp σ (fun i => |c i|)

end Expand

/-! ## The paper's unit tables -/

/-- **The normalized nonnegative couplings of a fold factor** (`lem:oct24:pure-pair-substitute`):
`M_{ab}` for `a, b ∈ {0, 1, 2}` (with `M_{aa} = P_a`), the pair couplings `P₁₂`, `P₀₁`, and `𝒥`. -/
inductive FoldCpl
  | M (a b : Fin 3)
  | P12
  | P01
  | J
  deriving DecidableEq, Fintype

/-- **The normalized nonnegative couplings of a matching factor**: `M_{ab}` and `𝒥`. -/
inductive MatchCpl
  | M (a b : Fin 3)
  | J
  deriving DecidableEq, Fintype

/-- The coefficients of the pure-pair substitute
`Q_{ij} = P_{ij} − (P_i + P_j)/(1 + ρ) + (1 − ρ)/(1 + ρ) 𝒥` in the couplings (`P_i = M_{ii}`). -/
noncomputable def qUnit (ρ : ℝ) (Pij : FoldCpl) (i j : Fin 3) (k : FoldCpl) : ℝ :=
  (if k = Pij then 1 else 0) - (if k = FoldCpl.M i i then 1 / (1 + ρ) else 0) -
    (if k = FoldCpl.M j j then 1 / (1 + ρ) else 0) +
      (if k = FoldCpl.J then (1 - ρ) / (1 + ρ) else 0)

/-- **The unit lifts of a fold factor in the couplings** (`lem:oct24:mask-schur`(a)): a unit
`e_{ab}` of two singleton labels `a, b ∈ {0,1,2}` is lifted to `V_a V_b^* = M_{ab} − 𝒥`, the scalar
units `e₃₃`, `e₄₄` to `Q₁₂`, `Q₀₁`; the other units are `0` (`𝒜_F` is block diagonal for
`{0,1,2}, {3}, {4}`, so an envelope has no coefficient there). -/
noncomputable def foldUnit (ρ : ℝ) (a b : Fin 5) (k : FoldCpl) : ℝ :=
  if ha : a.val < 3 then
    if hb : b.val < 3 then
      (if k = FoldCpl.M ⟨a.val, ha⟩ ⟨b.val, hb⟩ then 1 else 0) - (if k = FoldCpl.J then 1 else 0)
    else 0
  else if a = 3 ∧ b = 3 then qUnit ρ FoldCpl.P12 1 2 k
  else if a = 4 ∧ b = 4 then qUnit ρ FoldCpl.P01 0 1 k
  else 0

/-- **The unit lifts of a matching factor in the couplings**: `e_{ab} ↦ V_a V_b^* = M_{ab} − 𝒥`. -/
def matchUnit (a b : Fin 3) (k : MatchCpl) : ℝ :=
  (if k = MatchCpl.M a b then 1 else 0) - (if k = MatchCpl.J then 1 else 0)

section Tables

variable {O : Type*} (Cpl : FoldCpl → (O → ℝ) →ₗ[ℝ] (O → ℝ))

/-- The singleton units: `∑_k foldUnit(a, b, k) C_k = M_{ab} − 𝒥`. -/
theorem foldUnit_singleton (ρ : ℝ) (a b : Fin 3) :
    ∑ k, foldUnit ρ ⟨a.val, by omega⟩ ⟨b.val, by omega⟩ k • Cpl k =
      Cpl (FoldCpl.M a b) - Cpl FoldCpl.J := by
  have hk : ∀ k, foldUnit ρ ⟨a.val, by omega⟩ ⟨b.val, by omega⟩ k =
      (if k = FoldCpl.M a b then 1 else 0) - (if k = FoldCpl.J then 1 else 0) := by
    intro k
    simp [foldUnit, a.isLt, b.isLt]
  calc ∑ k, foldUnit ρ ⟨a.val, by omega⟩ ⟨b.val, by omega⟩ k • Cpl k =
      ∑ k, ((if k = FoldCpl.M a b then (1 : ℝ) else 0) • Cpl k -
        (if k = FoldCpl.J then (1 : ℝ) else 0) • Cpl k) :=
        sum_congr rfl fun k _ => by
          rw [hk]; exact sub_smul (R := ℝ) (M := (O → ℝ) →ₗ[ℝ] (O → ℝ)) _ _ _
    _ = _ := by
      rw [sum_sub_distrib]
      simp only [ite_smul, one_smul, zero_smul, sum_ite_eq', mem_univ, ↓reduceIte]

/-- The unit `e₃₃`: `∑_k foldUnit(3, 3, k) C_k = Q₁₂`. -/
theorem foldUnit_33 (ρ : ℝ) :
    ∑ k, foldUnit ρ 3 3 k • Cpl k = Cpl FoldCpl.P12 -
      (1 / (1 + ρ)) • (Cpl (FoldCpl.M 1 1) + Cpl (FoldCpl.M 2 2)) +
      ((1 - ρ) / (1 + ρ)) • Cpl FoldCpl.J := by
  have h3 : ¬ (3 : Fin 5).val < 3 := by decide
  simp only [foldUnit, h3, ↓reduceDIte, and_self, ↓reduceIte, qUnit, add_smul, sub_smul,
    sum_add_distrib, sum_sub_distrib, ite_smul, one_smul, zero_smul, sum_ite_eq', mem_univ,
    smul_add]
  abel

/-- The unit `e₄₄`: `∑_k foldUnit(4, 4, k) C_k = Q₀₁`. -/
theorem foldUnit_44 (ρ : ℝ) :
    ∑ k, foldUnit ρ 4 4 k • Cpl k = Cpl FoldCpl.P01 -
      (1 / (1 + ρ)) • (Cpl (FoldCpl.M 0 0) + Cpl (FoldCpl.M 1 1)) +
      ((1 - ρ) / (1 + ρ)) • Cpl FoldCpl.J := by
  have h4 : ¬ (4 : Fin 5).val < 3 := by decide
  have h43 : ¬ ((4 : Fin 5) = 3 ∧ (4 : Fin 5) = 3) := by decide
  simp only [foldUnit, h4, ↓reduceDIte, h43, and_self, ↓reduceIte, qUnit, add_smul, sub_smul,
    sum_add_distrib, sum_sub_distrib, ite_smul, one_smul, zero_smul, sum_ite_eq', mem_univ,
    smul_add]
  abel

/-- The matching units: `∑_k matchUnit(a, b, k) C_k = M_{ab} − 𝒥`. -/
theorem matchUnit_apply (CplE : MatchCpl → (O → ℝ) →ₗ[ℝ] (O → ℝ)) (a b : Fin 3) :
    ∑ k, matchUnit a b k • CplE k = CplE (MatchCpl.M a b) - CplE MatchCpl.J := by
  calc ∑ k, matchUnit a b k • CplE k =
      ∑ k, ((if k = MatchCpl.M a b then (1 : ℝ) else 0) • CplE k -
        (if k = MatchCpl.J then (1 : ℝ) else 0) • CplE k) :=
        sum_congr rfl fun k _ => by
          rw [matchUnit]; exact sub_smul (R := ℝ) (M := (O → ℝ) →ₗ[ℝ] (O → ℝ)) _ _ _
    _ = _ := by
      rw [sum_sub_distrib]
      simp only [ite_smul, one_smul, zero_smul, sum_ite_eq', mem_univ, ↓reduceIte]

end Tables

end Sarkozy.OpsSteps
