module

public import Sarkozy.IndexSupport.Main

/-!
# Conditional operators and mixtures

`def:mixing` and `lem:mixture` of `paper/sections/06_lifts_sectors.tex`.

For a finite joint law `κ` of a source label `a ∈ A` and a target label `b ∈ B`, the
*conditional operator* is `T^κ f(b) = E_κ[f(a) | b]`, from `L²(κ_A)` to `L²(κ_B)`
(`condMatrix`, `condOp`). Off the support of the target marginal `κ_B` a conditional
expectation is not determined; we use the source mean there (any choice is allowed: every
statement below involves `T^κ f` only through `κ_B`-weighted sums). With this version,
`T^κ` fixes the constants everywhere (`condMatrix_row_sum`), integrates against `κ_B` as `f`
against `κ_A` (`tgt_condOp`), and is a contraction (`condOp_contraction`, conditional
Jensen).

* `lem:mixture` (`mixture_condOp`, `mixture_energy_le`, `mixture_mixing`): for a mixture
  `κ = ∑_i ϖ_i κ_i` of joint laws with a common source marginal, `T^κ f = ∑_i h_i T^{κ_i} f`
  on the support of `κ_B` with `h_i = ϖ_i dκ_{i,B}/dκ_B`, `∑_i h_i = 1`, and
  `‖T^κ f‖² ≤ ∑_i ϖ_i ‖T^{κ_i} f‖²`; consequently mean-zero bounds `c_i` combine to
  `∑_i ϖ_i c_i²`.
* `def:mixing` (`blockJoint`, `blockOp`, `IsMixing`): for a law `ρ` on `V → X` and a block
  `Z ⊆ V`, the conditional operator `T^{ρ,Z}` from `z_Z` to `z_{V∖Z}`, and
  `(c, Z)`-mixing: `‖T^{ρ,Z} f‖ ≤ c ‖f‖` for `ρ_Z`-mean-zero `f`; `(γ, Z)`-mixing at a prime
  `p` is `c = p^{-γ}` (`IsGammaMixing`).
-/

@[expose] public section

open Finset
open scoped BigOperators Matrix

namespace Sarkozy.Mixing

section Joint

variable {A B : Type*} [Fintype A] [Fintype B]

/-- The source marginal `κ_A` of a joint law. -/
def srcWeight (κ : FiniteLaw (A × B)) (a : A) : ℝ := ∑ b, κ.weight (a, b)

/-- The target marginal `κ_B` of a joint law. -/
def tgtWeight (κ : FiniteLaw (A × B)) (b : B) : ℝ := ∑ a, κ.weight (a, b)

theorem srcWeight_nonneg (κ : FiniteLaw (A × B)) (a : A) : 0 ≤ srcWeight κ a :=
  Finset.sum_nonneg (fun _ _ => κ.nonneg _)

theorem tgtWeight_nonneg (κ : FiniteLaw (A × B)) (b : B) : 0 ≤ tgtWeight κ b :=
  Finset.sum_nonneg (fun _ _ => κ.nonneg _)

theorem sum_srcWeight (κ : FiniteLaw (A × B)) : ∑ a, srcWeight κ a = 1 := by
  simp only [srcWeight]
  rw [← Fintype.sum_prod_type']
  exact κ.total

theorem sum_tgtWeight (κ : FiniteLaw (A × B)) : ∑ b, tgtWeight κ b = 1 := by
  simp only [tgtWeight]
  rw [Finset.sum_comm, ← Fintype.sum_prod_type']
  exact κ.total

theorem weight_eq_zero_of_tgt {κ : FiniteLaw (A × B)} {b : B} (hb : tgtWeight κ b = 0)
    (a : A) : κ.weight (a, b) = 0 :=
  (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => κ.nonneg (a, b))).mp hb a (mem_univ a)

/-- The matrix of the conditional operator: `κ(a,b)/κ_B(b)` on the support of `κ_B`, the
source marginal off it. -/
noncomputable def condMatrix (κ : FiniteLaw (A × B)) : Matrix B A ℝ :=
  fun b a => if tgtWeight κ b = 0 then srcWeight κ a else κ.weight (a, b) / tgtWeight κ b

/-- The conditional operator `T^κ f(b) = E_κ[f(a) | b]`. -/
noncomputable def condOp (κ : FiniteLaw (A × B)) (f : A → ℝ) : B → ℝ := condMatrix κ *ᵥ f

theorem condOp_apply_of_ne (κ : FiniteLaw (A × B)) (f : A → ℝ) {b : B}
    (hb : tgtWeight κ b ≠ 0) :
    condOp κ f b = (∑ a, κ.weight (a, b) * f a) / tgtWeight κ b := by
  simp only [condOp, Matrix.mulVec, dotProduct, condMatrix, ite_eq_right hb, div_mul_eq_mul_div,
    Finset.sum_div]

/-- `κ_B(b) T^κ f(b) = ∑_a κ(a,b) f(a)` for every `b`. -/
theorem tgt_mul_condOp (κ : FiniteLaw (A × B)) (f : A → ℝ) (b : B) :
    tgtWeight κ b * condOp κ f b = ∑ a, κ.weight (a, b) * f a := by
  by_cases hb : tgtWeight κ b = 0
  · rw [hb, zero_mul]
    exact (Finset.sum_eq_zero (fun a _ => by rw [weight_eq_zero_of_tgt hb a, zero_mul])).symm
  · rw [condOp_apply_of_ne κ f hb]
    field_simp

theorem condMatrix_nonneg (κ : FiniteLaw (A × B)) (b : B) (a : A) : 0 ≤ condMatrix κ b a := by
  unfold condMatrix
  split_ifs
  · exact srcWeight_nonneg κ a
  · exact div_nonneg (κ.nonneg _) (tgtWeight_nonneg κ b)

/-- `T^κ` fixes the constants. -/
theorem condMatrix_row_sum (κ : FiniteLaw (A × B)) (b : B) : ∑ a, condMatrix κ b a = 1 := by
  unfold condMatrix
  by_cases hb : tgtWeight κ b = 0
  · simp only [ite_eq_left hb]
    exact sum_srcWeight κ
  · simp only [ite_eq_right hb]
    rw [← Finset.sum_div]
    exact div_self hb

/-- `∫ T^κ f dκ_B = ∫ f dκ_A`. -/
theorem tgt_condOp (κ : FiniteLaw (A × B)) (f : A → ℝ) :
    ∑ b, tgtWeight κ b * condOp κ f b = ∑ a, srcWeight κ a * f a := by
  simp only [tgt_mul_condOp, srcWeight, Finset.sum_mul]
  rw [Finset.sum_comm]

/-- The column form of `tgt_condOp`: `∑_b κ_B(b) T^κ(b,a) = κ_A(a)`. -/
theorem tgt_condMatrix (κ : FiniteLaw (A × B)) (a : A) :
    ∑ b, tgtWeight κ b * condMatrix κ b a = srcWeight κ a := by
  classical
  have h := tgt_condOp κ (fun a' => if a' = a then 1 else 0)
  simp only [condOp, Matrix.mulVec, dotProduct, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true] at h
  exact h

/-- Conditional Jensen: `T^κ` is a contraction from `L²(κ_A)` to `L²(κ_B)`. -/
theorem condOp_contraction (κ : FiniteLaw (A × B)) (f : A → ℝ) :
    ∑ b, tgtWeight κ b * condOp κ f b ^ 2 ≤ ∑ a, srcWeight κ a * f a ^ 2 := by
  have hb (b : B) : tgtWeight κ b * condOp κ f b ^ 2 ≤ ∑ a, κ.weight (a, b) * f a ^ 2 := by
    by_cases h0 : tgtWeight κ b = 0
    · rw [h0, zero_mul]
      exact Finset.sum_nonneg (fun a _ => mul_nonneg (κ.nonneg _) (sq_nonneg _))
    · have hpos : 0 < tgtWeight κ b := lt_of_le_of_ne (tgtWeight_nonneg κ b) (Ne.symm h0)
      have hcs := Finset.sum_mul_sq_le_sq_mul_sq univ (fun a => Real.sqrt (κ.weight (a, b)))
        (fun a => Real.sqrt (κ.weight (a, b)) * f a)
      have he1 (a : A) : Real.sqrt (κ.weight (a, b)) * (Real.sqrt (κ.weight (a, b)) * f a) =
          κ.weight (a, b) * f a := by
        rw [← mul_assoc, Real.mul_self_sqrt (κ.nonneg _)]
      have he2 (a : A) : Real.sqrt (κ.weight (a, b)) ^ 2 = κ.weight (a, b) :=
        Real.sq_sqrt (κ.nonneg _)
      have he3 (a : A) : (Real.sqrt (κ.weight (a, b)) * f a) ^ 2 = κ.weight (a, b) * f a ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (κ.nonneg _)]
      simp only [he1, he2, he3] at hcs
      have hT := tgt_mul_condOp κ f b
      have hkey : (tgtWeight κ b * condOp κ f b) ^ 2 ≤
          tgtWeight κ b * ∑ a, κ.weight (a, b) * f a ^ 2 := by
        rw [hT]
        exact hcs
      have h2 : tgtWeight κ b * (tgtWeight κ b * condOp κ f b ^ 2) ≤
          tgtWeight κ b * ∑ a, κ.weight (a, b) * f a ^ 2 := by
        calc _ = (tgtWeight κ b * condOp κ f b) ^ 2 := by ring
          _ ≤ _ := hkey
      exact le_of_mul_le_mul_left h2 hpos
  calc _ ≤ ∑ b, ∑ a, κ.weight (a, b) * f a ^ 2 := Finset.sum_le_sum (fun b _ => hb b)
    _ = _ := by
      rw [Finset.sum_comm]
      simp only [srcWeight, Finset.sum_mul]

/-- `c`-mixing of a joint law: `‖T^κ f‖_{L²(κ_B)} ≤ c ‖f‖_{L²(κ_A)}` for `κ_A`-mean-zero `f`
(squared form). -/
def ContractsMeanZero (κ : FiniteLaw (A × B)) (c : ℝ) : Prop :=
  ∀ f : A → ℝ, ∑ a, srcWeight κ a * f a = 0 →
    ∑ b, tgtWeight κ b * condOp κ f b ^ 2 ≤ c ^ 2 * ∑ a, srcWeight κ a * f a ^ 2

end Joint

section Mixture

variable {A B ι : Type*} [Fintype A] [Fintype B] [Fintype ι]

/-- `lem:mixture`, first part: on the support of `κ_B`, `T^κ f = ∑_i h_i T^{κ_i} f` with
`h_i = ϖ_i κ_{i,B}/κ_B`, and `∑_i h_i = 1`. -/
theorem mixture_condOp {κ : FiniteLaw (A × B)} {κs : ι → FiniteLaw (A × B)} {ϖ : ι → ℝ}
    (hκ : ∀ x, κ.weight x = ∑ i, ϖ i * (κs i).weight x) (f : A → ℝ) {b : B}
    (hb : tgtWeight κ b ≠ 0) :
    condOp κ f b = ∑ i, (ϖ i * tgtWeight (κs i) b / tgtWeight κ b) * condOp (κs i) f b ∧
      ∑ i, ϖ i * tgtWeight (κs i) b / tgtWeight κ b = 1 := by
  have htgt : tgtWeight κ b = ∑ i, ϖ i * tgtWeight (κs i) b := by
    simp only [tgtWeight, hκ, Finset.mul_sum]
    rw [Finset.sum_comm]
  constructor
  · rw [condOp_apply_of_ne κ f hb]
    have hnum : ∑ a, κ.weight (a, b) * f a = ∑ i, ϖ i * (tgtWeight (κs i) b * condOp (κs i) f b) := by
      simp only [tgt_mul_condOp, hκ, Finset.sum_mul, Finset.mul_sum]
      rw [Finset.sum_comm]
      apply sum_congr rfl
      intro a _
      apply sum_congr rfl
      intro i _
      ring
    rw [hnum, Finset.sum_div]
    apply sum_congr rfl
    intro i _
    ring
  · rw [← Finset.sum_div, ← htgt]
    exact div_self hb

/-- `lem:mixture`, energy inequality: `‖T^κ f‖²_{L²(κ_B)} ≤ ∑_i ϖ_i ‖T^{κ_i} f‖²_{L²(κ_{i,B})}`
for a mixture `κ = ∑_i ϖ_i κ_i`, `ϖ_i ≥ 0`. -/
theorem mixture_energy_le {κ : FiniteLaw (A × B)} {κs : ι → FiniteLaw (A × B)} {ϖ : ι → ℝ}
    (hϖ : ∀ i, 0 ≤ ϖ i) (hκ : ∀ x, κ.weight x = ∑ i, ϖ i * (κs i).weight x) (f : A → ℝ) :
    ∑ b, tgtWeight κ b * condOp κ f b ^ 2 ≤
      ∑ i, ϖ i * ∑ b, tgtWeight (κs i) b * condOp (κs i) f b ^ 2 := by
  have hb (b : B) : tgtWeight κ b * condOp κ f b ^ 2 ≤
      ∑ i, ϖ i * (tgtWeight (κs i) b * condOp (κs i) f b ^ 2) := by
    by_cases h0 : tgtWeight κ b = 0
    · rw [h0, zero_mul]
      exact Finset.sum_nonneg (fun i _ => mul_nonneg (hϖ i)
        (mul_nonneg (tgtWeight_nonneg _ _) (sq_nonneg _)))
    · have hpos : 0 < tgtWeight κ b := lt_of_le_of_ne (tgtWeight_nonneg κ b) (Ne.symm h0)
      obtain ⟨hrep, hsum⟩ := mixture_condOp hκ f h0
      set h : ι → ℝ := fun i => ϖ i * tgtWeight (κs i) b / tgtWeight κ b with hh
      have hh0 (i : ι) : 0 ≤ h i :=
        div_nonneg (mul_nonneg (hϖ i) (tgtWeight_nonneg _ _)) hpos.le
      let law : FiniteLaw ι := ⟨h, hh0, hsum⟩
      have hj := law.mean_sq_le_second_moment (fun i => condOp (κs i) f b)
      simp only [FiniteLaw.expect, law] at hj
      rw [hrep]
      calc tgtWeight κ b * (∑ i, h i * condOp (κs i) f b) ^ 2
          ≤ tgtWeight κ b * ∑ i, h i * condOp (κs i) f b ^ 2 :=
            mul_le_mul_of_nonneg_left hj hpos.le
        _ = _ := by
          rw [Finset.mul_sum]
          apply sum_congr rfl
          intro i _
          simp only [hh]
          field_simp
  calc _ ≤ ∑ b, ∑ i, ϖ i * (tgtWeight (κs i) b * condOp (κs i) f b ^ 2) :=
        Finset.sum_le_sum (fun b _ => hb b)
    _ = _ := by
      rw [Finset.sum_comm]
      simp only [Finset.mul_sum]

/-- `lem:mixture`, consequence: if every component contracts `m`-mean-zero functions by
`c_i` (common source marginal `m`), then the mixture contracts them by
`(∑_i ϖ_i c_i²)^{1/2}`; in particular a mixture of `c`-mixing laws with a common source
marginal is `c`-mixing (`mixture_contractsMeanZero`). -/
theorem mixture_mixing {κ : FiniteLaw (A × B)} {κs : ι → FiniteLaw (A × B)} {ϖ : ι → ℝ}
    (hϖ : ∀ i, 0 ≤ ϖ i) (hκ : ∀ x, κ.weight x = ∑ i, ϖ i * (κs i).weight x)
    (hsrc : ∀ i a, srcWeight (κs i) a = srcWeight κ a) {c : ι → ℝ}
    (hc : ∀ i, ContractsMeanZero (κs i) (c i)) (f : A → ℝ)
    (hf : ∑ a, srcWeight κ a * f a = 0) :
    ∑ b, tgtWeight κ b * condOp κ f b ^ 2 ≤
      (∑ i, ϖ i * c i ^ 2) * ∑ a, srcWeight κ a * f a ^ 2 := by
  apply (mixture_energy_le hϖ hκ f).trans
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i _
  have hfi : ∑ a, srcWeight (κs i) a * f a = 0 := by simp only [hsrc]; exact hf
  have h := hc i f hfi
  simp only [hsrc] at h
  calc ϖ i * ∑ b, tgtWeight (κs i) b * condOp (κs i) f b ^ 2
      ≤ ϖ i * (c i ^ 2 * ∑ a, srcWeight κ a * f a ^ 2) := mul_le_mul_of_nonneg_left h (hϖ i)
    _ = _ := by ring

theorem mixture_contractsMeanZero {κ : FiniteLaw (A × B)} {κs : ι → FiniteLaw (A × B)}
    {ϖ : ι → ℝ} (hϖ : ∀ i, 0 ≤ ϖ i) (hϖ1 : ∑ i, ϖ i = 1)
    (hκ : ∀ x, κ.weight x = ∑ i, ϖ i * (κs i).weight x)
    (hsrc : ∀ i a, srcWeight (κs i) a = srcWeight κ a) {c : ℝ}
    (hc : ∀ i, ContractsMeanZero (κs i) c) : ContractsMeanZero κ c := by
  intro f hf
  have h := mixture_mixing hϖ hκ hsrc hc f hf
  rwa [← Finset.sum_mul, hϖ1, one_mul] at h

end Mixture

section Blocks

variable {V X : Type*} [Fintype V] [DecidableEq V] [Fintype X] [DecidableEq X]

/-- The joint law of `(z_Z, z_{V∖Z})` under a law `ρ` on `V → X`. -/
noncomputable def blockJoint (ρ : FiniteLaw (V → X)) (Z : Finset V) :
    FiniteLaw (({w // w ∈ Z} → X) × ({w // w ∉ Z} → X)) :=
  ρ.map (Equiv.piEquivPiSubtypeProd (fun w => w ∈ Z) (fun _ => X))

/-- The conditional operator `T^{ρ,Z} f(y) = E_ρ[f(z_Z) | z_{V∖Z} = y]` of `def:mixing`. -/
noncomputable def blockOp (ρ : FiniteLaw (V → X)) (Z : Finset V) (f : ({w // w ∈ Z} → X) → ℝ) :
    ({w // w ∉ Z} → X) → ℝ :=
  condOp (blockJoint ρ Z) f

/-- `(c, Z)`-mixing: `‖T^{ρ,Z} f‖_{L²(λ)} ≤ c ‖f‖_{L²(ρ_Z)}` for every `f` with
`∫ f dρ_Z = 0`, with `ρ_Z` and `λ` the laws of `z_Z` and `z_{V∖Z}`. -/
def IsMixing (ρ : FiniteLaw (V → X)) (Z : Finset V) (c : ℝ) : Prop :=
  ContractsMeanZero (blockJoint ρ Z) c

/-- `(γ, Z)`-mixing at the prime `p` (`def:mixing`): `c = p^{-γ}`. -/
def IsGammaMixing (p : ℕ) (γ : ℝ) (ρ : FiniteLaw (V → X)) (Z : Finset V) : Prop :=
  IsMixing ρ Z ((p : ℝ) ^ (-γ))

/-- The weight of the block joint law is the `ρ`-mass of the corresponding configuration. -/
theorem blockJoint_weight (ρ : FiniteLaw (V → X)) (Z : Finset V)
    (x : ({w // w ∈ Z} → X) × ({w // w ∉ Z} → X)) :
    (blockJoint ρ Z).weight x =
      ρ.weight ((Equiv.piEquivPiSubtypeProd (fun w => w ∈ Z) (fun _ => X)).symm x) := by
  classical
  unfold blockJoint FiniteLaw.map
  simp only
  rw [Finset.sum_eq_single ((Equiv.piEquivPiSubtypeProd (fun w => w ∈ Z) (fun _ => X)).symm x)]
  · rw [ite_eq_left (Equiv.apply_symm_apply _ _)]
  · intro z _ hz
    rw [ite_eq_right]
    intro h
    exact hz (by rw [← h, Equiv.symm_apply_apply])
  · intro h
    exact absurd (mem_univ _) h

/-- `lem:mixture` for slot blocks: a mixture of `(c, Z)`-mixing laws with a common
`Z`-marginal is `(c, Z)`-mixing. -/
theorem IsMixing.mixture {ι : Type*} [Fintype ι] {ρ : FiniteLaw (V → X)}
    {ρs : ι → FiniteLaw (V → X)} {ϖ : ι → ℝ} (hϖ : ∀ i, 0 ≤ ϖ i) (hϖ1 : ∑ i, ϖ i = 1)
    (hρ : ∀ z, ρ.weight z = ∑ i, ϖ i * (ρs i).weight z) {Z : Finset V}
    (hsrc : ∀ i a, srcWeight (blockJoint (ρs i) Z) a = srcWeight (blockJoint ρ Z) a) {c : ℝ}
    (hc : ∀ i, IsMixing (ρs i) Z c) : IsMixing ρ Z c :=
  mixture_contractsMeanZero hϖ hϖ1 (fun x => by simp only [blockJoint_weight, hρ]) hsrc hc

end Blocks

end Sarkozy.Mixing
