module

public import Sarkozy.OpsFeature.Sector03
public import Sarkozy.OpsFeature.Frame

@[expose] public section

/-!
# The edge `03` in the actual block law, from the prime inputs
(`lem:oct24:feature-block`(a), proof Step 3)

`paper/sections/23_envelopes.tex`, `lem:oct24:feature-block`, proof Step 3, instantiated at the
actual fold law. At a prime: the law `β = m₁₂` of the pair `(x₁, x₂)` (`pairLaw`), the conditional
expectation `T` of a function of `x₀` given the pair (`condT`, the paper's `T_p`) and the
conditional expectation `T₂` given `x₂` alone (`condT2`, the paper's `T_{2,p} = P_{2,p} T_p`). They
fix the constants and preserve the means (`condT_row`, `condT_col`, `condT2_row`, `condT2_col`),
and the actual block law factors as `m_{0,𝔅}(x) = ∏_p m₁₂(x_{1,p}, x_{2,p}) T_p((x_{1,p}, x_{2,p}),
x_{0,p})` (`sum_m0B_pair`).

**`Edge03Prime`** collects the remaining prime inputs of Step 3 at every prime of the block (kind C
except `hT2a`, which is routine):
* `hprime`: the one-prime correlation of `𝓗₀` and the one-prime `𝒦₁₂` is at most `ϱ₀₃(p)` (the
  conditional-expectation formula `N_f` of Step 3 and its projection onto `𝒦₁₂`);
* `hTa`, `hT2a`, `hTd`: `‖T_p‖, ‖T_{2,p}‖ ≤ ϱ_{0|12}` and `‖T_p - T_{2,p}‖ ≤ ϱ̃₀₃` on the centred
  functions, with the constants at the least prime `b` of the block (the coarse estimates of
  Step 3, with the density comparison `e₀`).

**`edge03_of_prime`**: these give `Edge03Block F (ϱ₀₃(b))`, the input of `actual_hcor`;
the block assembly (sectors, telescoping, gates) is `edge03_sectors`, the gates are W2's
`step3_gates` (`cert:envelopes`(a)), and the prime constants are monotone (`rho_mono`).
**`actual_feature_frame_of_prime`**: `lem:oct24:feature-block`(b) in the actual block law from the
prime inputs. The prime inputs themselves are proved in `Sarkozy.OpsFeature.ExplicitT`
(`edge03Inputs_proved`; `condT2_bound` here proves `hT2a`).
-/

open Finset Matrix
open scoped BigOperators

namespace Sarkozy.OpsFeature

open Sarkozy.MiddleRecords Sarkozy.Mixing Sarkozy.EnvelopeSteps Sarkozy.Envelopes

section Prime

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

local notation "qF" => (Fintype.card F : ℝ)

/-- The law `m₁₂` of the pair `(x₁, x₂)` at one prime. -/
noncomputable def pairLaw (b : F × F) : ℝ := m12 b.1 b.2

/-- The conditional expectation of a function of `x₀` given the pair `(x₁, x₂)` (the paper's
`T_p`); on the null pairs the uniform law. -/
noncomputable def condT : Matrix (F × F) F ℝ := fun b u =>
  if ∑ u', oldW u' b.1 b.2 = 0 then 1 / qF else oldW u b.1 b.2 / ∑ u', oldW u' b.1 b.2

/-- The conditional expectation of a function of `x₀` given `x₂` (the paper's `T_{2,p}`). -/
noncomputable def condT2 : Matrix (F × F) F ℝ := fun b u => qF * m02 u b.2

theorem pairLaw_nonneg (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h7 : 7 ≤ qF)
    (b : F × F) : 0 ≤ pairLaw b :=
  div_nonneg (sum_nonneg fun _ _ => oldW_nonneg h7 _ _ _) (oldZ_pos hF h3 h7).le

theorem sum_pairLaw (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h7 : 7 ≤ qF) :
    ∑ b, pairLaw (F := F) b = 1 := by
  have h0 : qF ≠ 0 := by intro h; linarith
  simp only [pairLaw, Fintype.sum_prod_type, sum_m12_right hF h3 h7, sum_const, card_univ,
    nsmul_eq_mul]
  field_simp

theorem condT_row (h7 : 7 ≤ qF) (b : F × F) : ∑ u, condT b u = 1 := by
  have h0 : qF ≠ 0 := by intro h; linarith
  unfold condT
  by_cases hb : ∑ u', oldW u' b.1 b.2 = 0
  · simp only [hb, ↓reduceIte, sum_const, card_univ, nsmul_eq_mul]; field_simp
  · simp only [hb, ↓reduceIte]; rw [← sum_div, div_self hb]

theorem pairLaw_mul_condT (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h7 : 7 ≤ qF)
    (b : F × F) (u : F) : pairLaw b * condT b u = oldW u b.1 b.2 / oldZ (F := F) := by
  have hZ := (oldZ_pos hF h3 h7).ne'
  unfold pairLaw condT m12
  by_cases hb : ∑ u', oldW u' b.1 b.2 = 0
  · have hu : oldW u b.1 b.2 = 0 :=
      (sum_eq_zero_iff_of_nonneg (fun u' _ => oldW_nonneg h7 u' _ _)).mp hb u (mem_univ u)
    simp [hb, hu]
  · simp only [hb, ↓reduceIte]
    field_simp

theorem condT_col (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h7 : 7 ≤ qF) (u : F) :
    ∑ b, pairLaw b * condT b u = 1 / qF := by
  simp only [pairLaw_mul_condT hF h3 h7, Fintype.sum_prod_type]
  rw [← sum_m01 hF h3 h7 u]
  refine sum_congr rfl fun y _ => ?_
  rw [m01, sum_div]

theorem condT2_row (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h7 : 7 ≤ qF)
    (b : F × F) : ∑ u, condT2 b u = 1 := by
  have h0 : qF ≠ 0 := by intro h; linarith
  simp only [condT2, ← mul_sum, sum_m02_left hF h3 h7]
  field_simp

theorem condT2_col (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h7 : 7 ≤ qF) (u : F) :
    ∑ b, pairLaw b * condT2 b u = 1 / qF := by
  have h0 : qF ≠ 0 := by intro h; linarith
  simp only [pairLaw, condT2, Fintype.sum_prod_type]
  rw [sum_comm]
  have e : ∀ z, ∑ y, m12 y z * (qF * m02 u z) = m02 u z := by
    intro z
    rw [← sum_mul, sum_m12_left hF h3 h7]
    field_simp
  simp only [e]
  exact sum_m02_right hF h3 h7 u

/-- `m₀₂` is invariant under `(u, z) ↦ (-z, -u)` (the involution `ς`). -/
theorem m02_neg (u z : F) : m02 (-z) (-u) = m02 u z := by
  unfold m02
  congr 1
  rw [← Equiv.sum_comp (Equiv.neg F)]
  refine sum_congr rfl fun y _ => ?_
  exact EnvelopeSteps.oldW_varsigma u y z

/-- **`‖T_{2,p} f‖² = ϱ₀₂(p)² ‖f‖²`** on the centred functions (the transpose of
`lem:actual-features`(b), `norm_V0m_V2`, by `ς`). -/
theorem condT2_norm (hF : ringChar F ≠ 2) (h3 : Fintype.card F % 4 = 3) (h7 : 7 ≤ qF)
    (f : F → ℝ) (hf : ∑ a, f a = 0) :
    ∑ c : F × F, pairLaw c * (condT2 *ᵥ f) c ^ 2 = r02sq qF * ∑ a, (1 / qF) * f a ^ 2 := by
  have h0 : qF ≠ 0 := by intro h; linarith
  set ft : F → ℝ := fun v => f (-v) with hft
  have hft0 : ∑ v, ft v = 0 := by
    rw [hft, show (∑ v, f (-v)) = ∑ v, f v from Equiv.sum_comp (Equiv.neg F) f]; exact hf
  have hG : ∀ z, (condT2 *ᵥ f) ((0 : F), z) = MiddleRecords.condOp m02 ft (-z) := by
    intro z
    simp only [condT2, mulVec, dotProduct, MiddleRecords.condOp, hft, mul_sum]
    rw [← Equiv.sum_comp (Equiv.neg F)]
    refine sum_congr rfl fun u _ => ?_
    simp only [Equiv.neg_apply]
    rw [← m02_neg (-u) z, neg_neg]
    ring
  have hrow : ∀ y z, (condT2 *ᵥ f) (y, z) = (condT2 *ᵥ f) ((0 : F), z) := fun y z => rfl
  have e1 : ∑ c : F × F, pairLaw c * (condT2 *ᵥ f) c ^ 2 =
      ∑ z, (1 / qF) * MiddleRecords.condOp m02 ft (-z) ^ 2 := by
    rw [Fintype.sum_prod_type, sum_comm]
    refine sum_congr rfl fun z _ => ?_
    simp only [pairLaw, hrow _ z, hG z, ← sum_mul, sum_m12_left hF h3 h7]
  have e2 : ∑ z, MiddleRecords.condOp m02 ft (-z) ^ 2 =
      ∑ w, MiddleRecords.condOp m02 ft w ^ 2 :=
    Equiv.sum_comp (Equiv.neg F) (fun w => MiddleRecords.condOp m02 ft w ^ 2)
  have e3 : ∑ a, ft a ^ 2 = ∑ a, f a ^ 2 :=
    Equiv.sum_comp (Equiv.neg F) (fun a => f a ^ 2)
  rw [e1, ← mul_sum, e2, norm_V0m_V2 hF h3 h7 ft hft0, e3, ← mul_sum]
  unfold r02sq
  ring

end Prime

section Block

variable {P : Type*} [Fintype P] [DecidableEq P] {F : P → Type*} [∀ p, Field (F p)]
  [∀ p, Fintype (F p)] [∀ p, DecidableEq (F p)]

/-- The pair `(x₁, x₂)` of an object triple, prime by prime. -/
def pr (x : Tri F) : ∀ p, F p × F p := fun p => ((x p).2.1, (x p).2.2)

/-- **The actual block law factors through the pair**:
`∑_x m_{0,𝔅}(x) f(x₀) G(x₁, x₂) = ⟨(⊗_p T_p) f, G⟩_{⊗ m₁₂}`. -/
theorem sum_m0B_pair (hF : ∀ p, ringChar (F p) ≠ 2) (h3 : ∀ p, Fintype.card (F p) % 4 = 3)
    (h7 : ∀ p, (7 : ℝ) ≤ Fintype.card (F p)) (f : Lab F → ℝ) (G : (∀ p, F p × F p) → ℝ) :
    ∑ x, m0B x * f (c0 x) * G (pr x) =
      wip (fun p => pairLaw (F := F p)) (prodOp (fun p => condT (F := F p)) *ᵥ f) G := by
  let e : Tri F ≃ Lab F × (∀ p, F p × F p) :=
    { toFun := fun x => (c0 x, pr x)
      invFun := fun t p => (t.1 p, (t.2 p).1, (t.2 p).2)
      left_inv := fun x => rfl
      right_inv := fun t => rfl }
  rw [← e.symm.sum_comp, Fintype.sum_prod_type, sum_comm]
  unfold wip
  refine sum_congr rfl fun b _ => ?_
  simp only [mulVec, dotProduct, mul_sum, sum_mul]
  refine sum_congr rfl fun u _ => ?_
  have hm : m0B (e.symm (u, b)) = prodW (fun p => pairLaw (F := F p)) b *
      prodOp (fun p => condT (F := F p)) b u := by
    simp only [m0B, prodW, prodOp, ← prod_mul_distrib]
    refine prod_congr rfl fun p _ => ?_
    rw [pairLaw_mul_condT (hF p) (h3 p) (h7 p)]
    rfl
  rw [hm]
  change prodW (fun p => pairLaw (F := F p)) b * prodOp (fun p => condT (F := F p)) b u * f u * G b
    = _
  ring

theorem prodOp_condT_one (h7 : ∀ p, (7 : ℝ) ≤ Fintype.card (F p)) :
    prodOp (fun p => condT (F := F p)) *ᵥ (fun _ => (1 : ℝ)) = fun _ => 1 := by
  funext b
  simp only [mulVec, dotProduct, mul_one, prodOp]
  rw [← Fintype.prod_sum (fun p u => condT (F := F p) (b p) u)]
  exact prod_eq_one fun p _ => condT_row (h7 p) (b p)

/-- **The prime inputs of Step 3** at every prime of a block with least prime `b`. -/
structure Edge03Prime (F : P → Type*) [∀ p, Field (F p)] [∀ p, Fintype (F p)]
    [∀ p, DecidableEq (F p)] (b : ℝ) : Prop where
  /-- The one-prime correlation of `𝓗₀` and `𝒦₁₂` (kind C). -/
  hprime : ∀ p (g : F p → ℝ) (κ : F p × F p → ℝ), ∑ a, unifB p a * g a = 0 →
    (∀ h : F p → ℝ, ∑ c : F p × F p, pairLaw c * κ c * h c.1 = 0) →
    (∀ h : F p → ℝ, ∑ c : F p × F p, pairLaw c * κ c * h c.2 = 0) →
    |∑ c : F p × F p, pairLaw c * (condT *ᵥ g) c * κ c| ≤
      rho03 (1 / (Fintype.card (F p) : ℝ)) (1 / Real.sqrt (Fintype.card (F p))) *
        (Real.sqrt (∑ a, unifB p a * g a ^ 2) * Real.sqrt (∑ c : F p × F p, pairLaw c * κ c ^ 2))
  /-- `‖T_p‖ ≤ ϱ_{0|12}` on the centred functions (kind C). -/
  hTa : ∀ p (f : F p → ℝ), ∑ a, unifB p a * f a = 0 →
    ∑ c : F p × F p, pairLaw c * (condT *ᵥ f) c ^ 2 ≤
      rho0bar12 (1 / b) (1 / Real.sqrt b) ^ 2 * ∑ a, unifB p a * f a ^ 2
  /-- `‖T_{2,p}‖ ≤ ϱ_{0|12}` on the centred functions (kind R: `‖T_{2,p}‖ = ϱ₀₂`). -/
  hT2a : ∀ p (f : F p → ℝ), ∑ a, unifB p a * f a = 0 →
    ∑ c : F p × F p, pairLaw c * (condT2 *ᵥ f) c ^ 2 ≤
      rho0bar12 (1 / b) (1 / Real.sqrt b) ^ 2 * ∑ a, unifB p a * f a ^ 2
  /-- `‖T_p - T_{2,p}‖ ≤ ϱ̃₀₃` on the centred functions (kind C). -/
  hTd : ∀ p (f : F p → ℝ), ∑ a, unifB p a * f a = 0 →
    ∑ c : F p × F p, pairLaw c * ((condT - condT2) *ᵥ f) c ^ 2 ≤
      (1 / b * rho03tq (1 / b) (1 / Real.sqrt b)) ^ 2 * ∑ a, unifB p a * f a ^ 2

theorem rho02_le_rho0bar12 {q r : ℝ} (hq : 0 ≤ q) (hq8 : q ≤ 1 / 8) (hr : 0 ≤ r) :
    rho02 q r ≤ rho0bar12 q r := by
  unfold rho02 rho0bar12
  have h1 : 0 < 1 - q := by linarith
  have h3 : 0 < 1 - 3 * q := by linarith
  have h4 : 0 < 1 - 4 * q := by linarith
  have he0 : 0 ≤ e0 q := by unfold e0; positivity
  have he1 : e0 q < 1 := by
    unfold e0
    rw [div_lt_one (by positivity)]
    nlinarith
  have hs : 0 < Real.sqrt (1 - e0 q) := Real.sqrt_pos.2 (by linarith)
  have hs1 : Real.sqrt (1 - e0 q) ≤ 1 := by
    rw [Real.sqrt_le_one]; linarith
  have hnum : r * Real.sqrt (1 + q) / (1 - q) ≤
      (r * Real.sqrt (1 + q) + 2 * q) / (1 - 3 * q) + e0 q := by
    have a : r * Real.sqrt (1 + q) / (1 - q) ≤ r * Real.sqrt (1 + q) / (1 - 3 * q) :=
      div_le_div_of_nonneg_left (by positivity) h3 (by linarith)
    have b : r * Real.sqrt (1 + q) / (1 - 3 * q) ≤
        (r * Real.sqrt (1 + q) + 2 * q) / (1 - 3 * q) :=
      div_le_div_of_nonneg_right (by linarith) h3.le
    linarith
  have hnum0 : 0 ≤ r * Real.sqrt (1 + q) / (1 - q) := by positivity
  calc r * Real.sqrt (1 + q) / (1 - q)
      ≤ r * Real.sqrt (1 + q) / (1 - q) / Real.sqrt (1 - e0 q) := by
        rw [le_div_iff₀ hs]
        exact mul_le_of_le_one_right hnum0 hs1
    _ ≤ _ := div_le_div_of_nonneg_right hnum hs.le

omit [Fintype P] [DecidableEq P] in
/-- **The input `hT2a` of `Edge03Prime` is a theorem**: `‖T_{2,p}‖ = ϱ₀₂(p) ≤ ϱ₀₂(b) ≤ ϱ_{0|12}(b)`
on the centred functions. -/
theorem condT2_bound {b : ℝ} (hB : MiddleBlock F b) (p : P) (f : F p → ℝ)
    (hf : ∑ a, unifB p a * f a = 0) :
    ∑ c : F p × F p, pairLaw c * (condT2 *ᵥ f) c ^ 2 ≤
      rho0bar12 (1 / b) (1 / Real.sqrt b) ^ 2 * ∑ a, unifB p a * f a ^ 2 := by
  have h7 := hB.h7 p
  have hb7 : (7 : ℝ) ≤ b := by linarith [hB.hb]
  have hf' : ∑ a, f a = 0 := by
    simp only [unifB, ← mul_sum] at hf
    rcases mul_eq_zero.mp hf with h | h
    · exact absurd h (by have : (0 : ℝ) < Fintype.card (F p) := by linarith
                         positivity)
    · exact h
  rw [condT2_norm (hB.hF p) (hB.h3 p) h7 f hf']
  have hq8 : 1 / b ≤ 1 / 8 := one_div_le_one_div_of_le (by norm_num) (by linarith [hB.hb])
  have hb0 : 0 < b := by linarith
  have h02 : 0 ≤ rho02 (1 / b) (1 / Real.sqrt b) := (rho02_b_le hB.hb).1
  have hle : r02sq (Fintype.card (F p) : ℝ) ≤ rho0bar12 (1 / b) (1 / Real.sqrt b) ^ 2 := by
    refine (r02sq_b hb7 (hB.hbp p)).trans ?_
    exact pow_le_pow_left₀ h02 (rho02_le_rho0bar12 (by positivity) hq8 (by positivity)) 2
  have hs : 0 ≤ ∑ a, (1 / (Fintype.card (F p) : ℝ)) * f a ^ 2 :=
    sum_nonneg fun a _ => mul_nonneg (by positivity) (sq_nonneg _)
  exact mul_le_mul_of_nonneg_right hle hs

/-- **The prime inputs of Step 3 that remain** (kind C): `Edge03Prime` without its routine field
`hT2a`, which is `condT2_bound`. -/
structure Edge03Inputs (F : P → Type*) [∀ p, Field (F p)] [∀ p, Fintype (F p)]
    [∀ p, DecidableEq (F p)] (b : ℝ) : Prop where
  /-- The one-prime correlation of `𝓗₀` and `𝒦₁₂` is at most `ϱ₀₃(p)`. -/
  hprime : ∀ p (g : F p → ℝ) (κ : F p × F p → ℝ), ∑ a, unifB p a * g a = 0 →
    (∀ h : F p → ℝ, ∑ c : F p × F p, pairLaw c * κ c * h c.1 = 0) →
    (∀ h : F p → ℝ, ∑ c : F p × F p, pairLaw c * κ c * h c.2 = 0) →
    |∑ c : F p × F p, pairLaw c * (condT *ᵥ g) c * κ c| ≤
      rho03 (1 / (Fintype.card (F p) : ℝ)) (1 / Real.sqrt (Fintype.card (F p))) *
        (Real.sqrt (∑ a, unifB p a * g a ^ 2) * Real.sqrt (∑ c : F p × F p, pairLaw c * κ c ^ 2))
  /-- `‖T_p‖ ≤ ϱ_{0|12}(b)` on the centred functions. -/
  hTa : ∀ p (f : F p → ℝ), ∑ a, unifB p a * f a = 0 →
    ∑ c : F p × F p, pairLaw c * (condT *ᵥ f) c ^ 2 ≤
      rho0bar12 (1 / b) (1 / Real.sqrt b) ^ 2 * ∑ a, unifB p a * f a ^ 2
  /-- `‖T_p - T_{2,p}‖ ≤ ϱ̃₀₃(b)` on the centred functions. -/
  hTd : ∀ p (f : F p → ℝ), ∑ a, unifB p a * f a = 0 →
    ∑ c : F p × F p, pairLaw c * ((condT - condT2) *ᵥ f) c ^ 2 ≤
      (1 / b * rho03tq (1 / b) (1 / Real.sqrt b)) ^ 2 * ∑ a, unifB p a * f a ^ 2

omit [Fintype P] [DecidableEq P] in
theorem Edge03Inputs.toPrime {b : ℝ} (hB : MiddleBlock F b) (hI : Edge03Inputs F b) :
    Edge03Prime F b :=
  ⟨hI.hprime, hI.hTa, fun p f hf => condT2_bound hB p f hf, hI.hTd⟩

end Block

section Main

variable {P : Type*} [Fintype P] [DecidableEq P] {F : P → Type*} [∀ p, Field (F p)]
  [∀ p, Fintype (F p)] [∀ p, DecidableEq (F p)]

theorem rho03_ge {q r : ℝ} (hq : 0 ≤ q) (hq8 : q ≤ 1 / 8) (hr : 0 ≤ r) : q ≤ rho03 q r := by
  unfold rho03
  have a : 0 < 1 - 3 * q := by linarith
  have c : 0 < 1 - 6 * q := by linarith
  have d : 0 < 1 - 2 * q := by linarith
  have h1 : q ≤ q / (1 - 3 * q) := by
    rw [le_div_iff₀ a]; nlinarith
  have : 0 ≤ 2 * q ^ 2 / ((1 - 3 * q) * (1 - 6 * q)) := by positivity
  have : 0 ≤ 2 * q * r / ((1 - 6 * q) * (1 - 2 * q)) := by positivity
  linarith

/-- **`lem:oct24:feature-block`(a), the edge `03`, in the actual block law, from the prime
inputs of Step 3** (`Edge03Prime`): the input `Edge03Block F (ϱ₀₃(b))` of `actual_hcor`. -/
theorem edge03_of_prime {b : ℝ} (hB : MiddleBlock F b) (hP : Edge03Prime F b) :
    Edge03Block F (rho03 (1 / b) (1 / Real.sqrt b)) := by
  intro h k hh hk
  obtain ⟨f, hf0, hf⟩ := hh
  obtain ⟨⟨K, hK⟩, hk1, hk2⟩ := hk
  have hF := hB.hF
  have h3 := hB.h3
  have h7 := hB.h7
  have hb0 : 0 < b := by linarith [hB.hb]
  set Kt : (∀ p, F p × F p) → ℝ := fun c => K (fun p => (c p).1) (fun p => (c p).2) with hKt
  have e1 : ipm h k = wip (fun p => pairLaw (F := F p)) (prodOp (fun p => condT (F := F p)) *ᵥ f)
      Kt := by
    rw [← sum_m0B_pair hF h3 h7 f Kt]
    unfold ipm
    simp only [hf, hK]
    rfl
  have e2 : ipm h h = ∑ u, prodW unifB u * f u ^ 2 := by
    rw [ipm_self]; simp only [hf]; exact norm_actual_x0 hF h3 h7 f
  have hpair1 : ∀ G : (∀ p, F p × F p) → ℝ, ∑ x, m0B x * G (pr x) =
      ∑ c, prodW (fun p => pairLaw (F := F p)) c * G c := by
    intro G
    have := sum_m0B_pair hF h3 h7 (fun _ => 1) G
    rw [prodOp_condT_one h7] at this
    simp only [mul_one] at this
    rw [this]
    unfold wip
    exact sum_congr rfl fun c _ => by ring
  have e3 : ipm k k = ∑ c, prodW (fun p => pairLaw (F := F p)) c * Kt c ^ 2 := by
    rw [ipm_self, ← hpair1 (fun c => Kt c ^ 2)]
    simp only [hK]
    rfl
  -- the orthogonality of `Kt` to the functions of `x₁` and of `x₂`
  have hKη : ∀ G : (∀ p, F p × F p) → ℝ,
      (∀ c c', (∀ j, (c j).1 = (c' j).1) → G c = G c') →
      wip (fun p => pairLaw (F := F p)) Kt G = 0 := by
    intro G hG
    set g : Lab F → ℝ := fun y => G (fun p => (y p, y p))
    have hGg : ∀ c, G c = g (fun p => (c p).1) := fun c => hG _ _ fun j => rfl
    have := hk1 g
    unfold ipm at this
    rw [show (∑ x, m0B x * k x * g (c1 x)) = ∑ x, m0B x * (Kt (pr x) * g (fun p => (pr x p).1))
      from sum_congr rfl fun x _ => by rw [hK, mul_assoc]; rfl,
      hpair1 (fun c => Kt c * g (fun p => (c p).1))] at this
    unfold wip
    rw [← this]
    exact sum_congr rfl fun c _ => by rw [hGg c]; ring
  have hKζ : ∀ G : (∀ p, F p × F p) → ℝ,
      (∀ c c', (∀ j, (c j).2 = (c' j).2) → G c = G c') →
      wip (fun p => pairLaw (F := F p)) Kt G = 0 := by
    intro G hG
    set g : Lab F → ℝ := fun y => G (fun p => (y p, y p))
    have hGg : ∀ c, G c = g (fun p => (c p).2) := fun c => hG _ _ fun j => rfl
    have := hk2 g
    unfold ipm at this
    rw [show (∑ x, m0B x * k x * g (c2 x)) = ∑ x, m0B x * (Kt (pr x) * g (fun p => (pr x p).2))
      from sum_congr rfl fun x _ => by rw [hK, mul_assoc]; rfl,
      hpair1 (fun c => Kt c * g (fun p => (c p).2))] at this
    unfold wip
    rw [← this]
    exact sum_congr rfl fun c _ => by rw [hGg c]; ring
  -- the gates
  have hq0 : 0 ≤ 1 / b := by positivity
  have hq24 : 1 / b ≤ 1 / 2 ^ 24 := one_div_le_one_div_of_le (by norm_num) (by
    linarith [hB.hb])
  have hr0 : 0 ≤ 1 / Real.sqrt b := by positivity
  have hr12 : 1 / Real.sqrt b ≤ 1 / 2 ^ 12 := by
    apply one_div_le_one_div_of_le (by norm_num)
    rw [show (2 : ℝ) ^ 12 = Real.sqrt (2 ^ 24) by
      rw [show (2 : ℝ) ^ 24 = (2 ^ 12) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by linarith [hB.hb])
  obtain ⟨hg1, hg2⟩ := step3_gates hq0 hq24 hr0 hr12
  have hρa0 : 0 ≤ rho0bar12 (1 / b) (1 / Real.sqrt b) := by
    have he : 0 ≤ e0 (1 / b) := by
      unfold e0
      have : 0 < 1 - 3 * (1 / b) := by linarith
      have : 0 < 1 - 4 * (1 / b) := by linarith
      positivity
    unfold rho0bar12
    have : 0 < 1 - 3 * (1 / b) := by linarith
    positivity
  have ht0 : 0 ≤ rho03tq (1 / b) (1 / Real.sqrt b) := by
    unfold rho03tq
    have : 0 < 1 - 3 * (1 / b) := by linarith
    have : 0 < 1 - 4 * (1 / b) := by linarith
    have : 0 < 1 - 1 / b := by linarith
    positivity
  have hρb0 : 0 ≤ 1 / b * rho03tq (1 / b) (1 / Real.sqrt b) := mul_nonneg hq0 ht0
  have hq8 : 1 / b ≤ 1 / 8 := hq24.trans (by norm_num)
  have hc0 : 0 ≤ rho03 (1 / b) (1 / Real.sqrt b) := hq0.trans (rho03_ge hq0 hq8 hr0)
  have hgate : 2 * (1 / b * rho03tq (1 / b) (1 / Real.sqrt b)) *
      rho0bar12 (1 / b) (1 / Real.sqrt b) ≤ rho03 (1 / b) (1 / Real.sqrt b) := by
    have : 2 * (1 / b * rho03tq (1 / b) (1 / Real.sqrt b)) * rho0bar12 (1 / b) (1 / Real.sqrt b) =
        1 / b * (2 * rho03tq (1 / b) (1 / Real.sqrt b) * rho0bar12 (1 / b) (1 / Real.sqrt b)) := by
      ring
    rw [this]
    calc 1 / b * (2 * rho03tq (1 / b) (1 / Real.sqrt b) * rho0bar12 (1 / b) (1 / Real.sqrt b))
        ≤ 1 / b * 1 := mul_le_mul_of_nonneg_left hg2.le hq0
      _ = 1 / b := mul_one _
      _ ≤ _ := rho03_ge hq0 hq8 hr0
  -- the prime constants at the least prime
  have hmono : ∀ p, rho03 (1 / (Fintype.card (F p) : ℝ)) (1 / Real.sqrt (Fintype.card (F p))) ≤
      rho03 (1 / b) (1 / Real.sqrt b) := by
    intro p
    have hx : b ≤ (Fintype.card (F p) : ℝ) := hB.hbp p
    have hx0 : 0 < (Fintype.card (F p) : ℝ) := by linarith
    exact (rho_mono (by positivity) (one_div_le_one_div_of_le hb0 hx) hq8 (by positivity)
      (one_div_le_one_div_of_le (Real.sqrt_pos.2 hb0) (Real.sqrt_le_sqrt hx))).2.2.1
  have hmain := edge03_sectors (fun p => unifB (F := F) p) (fun p => pairLaw (F := F p))
    (fun p a => by have := h7 p; unfold unifB; positivity)
    (fun p => by
      have := h7 p
      have h0 : (Fintype.card (F p) : ℝ) ≠ 0 := by intro h; linarith
      simp only [unifB, sum_const, card_univ, nsmul_eq_mul]; field_simp)
    (fun p c => pairLaw_nonneg (hF p) (h3 p) (h7 p) c)
    (fun p => sum_pairLaw (hF p) (h3 p) (h7 p))
    (fun p => condT (F := F p)) (fun p => condT2 (F := F p))
    (fun p c => condT_row (h7 p) c) (fun p c => condT2_row (hF p) (h3 p) (h7 p) c)
    (fun p a => by rw [condT_col (hF p) (h3 p) (h7 p)]; rfl)
    (fun p a => by rw [condT2_col (hF p) (h3 p) (h7 p)]; rfl)
    (fun p => Prod.fst) (fun p => Prod.snd)
    (fun p c c' hcc a => by simp only [condT2, hcc])
    hc0 hρa0 hg1.le hρb0 hgate
    (fun p g κ hg hη hζ => (hP.hprime p g κ hg hη hζ).trans
      (mul_le_mul_of_nonneg_right (hmono p)
        (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))))
    (fun p f hf => hP.hTa p f hf) (fun p f hf => hP.hT2a p f hf) (fun p f hf => hP.hTd p f hf)
    f hf0 Kt hKη hKζ
  rw [e1]
  have hn1 : wNorm (prodW (fun p => unifB (F := F) p)) f = Real.sqrt (ipm h h) := by
    rw [e2]; rfl
  have hn2 : wNorm (prodW (fun p => pairLaw (F := F p))) Kt = Real.sqrt (ipm k k) := by
    rw [e3]; rfl
  rw [hn1, hn2] at hmain
  exact hmain

/-- **W2's `hcor` in the actual block law, from the prime inputs of Step 3.** -/
theorem actual_hcor_of_prime {b : ℝ} (hB : MiddleBlock F b) (hP : Edge03Prime F b)
    (h : Fin 5 → Tri F → ℝ) (hf : IsFoldFeat h) :
    ∀ i j, i ≠ j → |inner ℝ (emb (h i)) (emb (h j))| ≤ foldPattern (rho02 (1 / b)
      (1 / Real.sqrt b)) (rho01 (1 / b)) (rho03 (1 / b) (1 / Real.sqrt b))
        (rho34 (1 / b) (1 / Real.sqrt b)) i j * ‖emb (h i)‖ * ‖emb (h j)‖ :=
  actual_hcor hB (edge03_of_prime hB hP) h hf

/-- **`lem:oct24:feature-block`(b) in the actual block law, from the prime inputs of Step 3**:
`‖h₀ + ⋯ + h₄‖² ≤ Γ_F ∑_v ‖h_v‖²` in `L²(m_{0,𝔅})` at every block of primes `p ≡ 3 (mod 4)` with
least prime `b ≥ Q₃`. -/
theorem actual_feature_frame_of_prime {b : ℝ} (hB : MiddleBlock F b) (hP : Edge03Prime F b)
    (h : Fin 5 → Tri F → ℝ) (hf : IsFoldFeat h) :
    ipm (fun x => ∑ i, h i x) (fun x => ∑ i, h i x) ≤ (gammaF : ℝ) * ∑ i, ipm (h i) (h i) :=
  actual_feature_frame hB (edge03_of_prime hB hP) h hf

/-- **`lem:oct24:feature-block`(b) in the actual block law, from the remaining prime inputs**
(`Edge03Inputs`: the one-prime bound of the edge `03` and the two coarse estimates of Step 3). -/
theorem actual_feature_frame_of_inputs {b : ℝ} (hB : MiddleBlock F b) (hI : Edge03Inputs F b)
    (h : Fin 5 → Tri F → ℝ) (hf : IsFoldFeat h) :
    ipm (fun x => ∑ i, h i x) (fun x => ∑ i, h i x) ≤ (gammaF : ℝ) * ∑ i, ipm (h i) (h i) :=
  actual_feature_frame_of_prime hB (hI.toPrime hB) h hf

end Main

end Sarkozy.OpsFeature
