module

public import Sarkozy.PartVRecords.Eligible

@[expose] public section

/-!
# The signed whole-block fold record (`def:record:mixture`)

`paper/sections/21_middle_records.tex`, `def:record:mixture`.

At every prime `p` of a middle block the paper fixes the reference half law `m_{0,p} = g₀ ν_F`
of `lem:old-f-law` and three component densities `P_{++,p}`, `P_{-+,p}`, `P_{--,p}` of
`lem:signed-components`, relative to `m_{0,p} ⊗ m_{0,p}`. The **record of `F₁`** on the block is
the signed measure with density (`eq:signed-law`)

  `K_{t,𝔅} = ⊗_p P_{++,p} + (t/2) ⊗_p P_{-+,p} - (t/2) ⊗_p P_{--,p}`

relative to `m_{0,𝔅} ⊗ m_{0,𝔅}`, `m_{0,𝔅} = ⊗_p m_{0,p}`: the signed sum is taken after the three
products. The construction uses `t = 127/500`; here `t` is any real.

Here the per-prime data are parameters (`SignedComponents`): the half label sets `H p`, the laws
`m_{0,p}` and the three densities. `lem:old-f-law` and `lem:signed-components`, which construct
them and prove that each component is a probability density with both half marginals `m_{0,p}`,
are not formalized; those properties are the hypothesis `SignedComponents.Valid`.

**Proved** (`def:record:mixture`(c)), whatever the number of primes, under `Valid`:
* mass one (`Ksigned_mass`);
* both half marginals `m_{0,𝔅}`, i.e. the marginal densities relative to `m_{0,𝔅}` are `1`
  (`Ksigned_left_marginal`, `Ksigned_right_marginal`);
* total variation at most `1 + t` for `0 ≤ t` (`Ksigned_variation`);
and the same for the reflected transpose `K^ς`, the record of `F₂` (`def:record:mixture`(d)), for a
componentwise involution `ς` that preserves `m_{0,p}` (`Kreflected_mass`,
`Kreflected_left_marginal`, `Kreflected_right_marginal`).
(e), the placement by `F₁`, `F₂` with the weight `w_D r`, is how the record enters the
comparison law and is not formalized here.
-/

namespace Sarkozy.PartVRecords

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {H : ι → Type*} [∀ i, Fintype (H i)]

/-- **The per-prime data of `def:record:mixture`(a), (b)**: the reference half laws `m_{0,p}` and
the component densities `P_{++,p}`, `P_{-+,p}`, `P_{--,p}` relative to `m_{0,p} ⊗ m_{0,p}`. -/
structure SignedComponents (H : ι → Type*) [∀ i, Fintype (H i)] where
  m0 : ∀ i, FiniteLaw (H i)
  Ppp : ∀ i, H i → H i → ℝ
  Pmp : ∀ i, H i → H i → ℝ
  Pmm : ∀ i, H i → H i → ℝ

/-- A density `P` relative to `m ⊗ m` is a *probability density with both half marginals `m`*:
`P ≥ 0` and `∑_y m(y) P(x, y) = 1 = ∑_x m(x) P(x, y)`. -/
def IsMarginalDensity {A : Type*} [Fintype A] (m : FiniteLaw A) (P : A → A → ℝ) : Prop :=
  (∀ x y, 0 ≤ P x y) ∧ (∀ x, ∑ y, m.weight y * P x y = 1) ∧ (∀ y, ∑ x, m.weight x * P x y = 1)

/-- **The hypotheses on the components** (`lem:signed-components`, not formalized): each of the
three densities is a probability density with both half marginals `m_{0,p}`, at every prime. -/
def SignedComponents.Valid (C : SignedComponents H) : Prop :=
  ∀ i, IsMarginalDensity (C.m0 i) (C.Ppp i) ∧ IsMarginalDensity (C.m0 i) (C.Pmp i) ∧
    IsMarginalDensity (C.m0 i) (C.Pmm i)

/-- The block reference weight `m_{0,𝔅}(x) = ∏_p m_{0,p}(x_p)`. -/
noncomputable def blockWeight (m : ∀ i, FiniteLaw (H i)) (x : ∀ i, H i) : ℝ :=
  ∏ i, (m i).weight (x i)

/-- The product density `⊗_p P_p`. -/
noncomputable def prodDensity (P : ∀ i, H i → H i → ℝ) (x y : ∀ i, H i) : ℝ :=
  ∏ i, P i (x i) (y i)

/-- **The signed whole-block fold record** `K_{t,𝔅}` (`eq:signed-law`), as a density relative to
`m_{0,𝔅} ⊗ m_{0,𝔅}`. -/
noncomputable def Ksigned (C : SignedComponents H) (t : ℝ) (x y : ∀ i, H i) : ℝ :=
  prodDensity C.Ppp x y + t / 2 * prodDensity C.Pmp x y - t / 2 * prodDensity C.Pmm x y

/-- The marginal of a product density:
`∑_y m_{0,𝔅}(y) ⊗P(x, y) = ∏_p ∑_{y_p} m_{0,p}(y_p) P_p(x_p, y_p)`. -/
theorem sum_right_prod (m : ∀ i, FiniteLaw (H i)) (P : ∀ i, H i → H i → ℝ) (x : ∀ i, H i) :
    ∑ y, blockWeight m y * prodDensity P x y = ∏ i, ∑ y, (m i).weight y * P i (x i) y := by
  rw [Fintype.prod_sum]
  refine sum_congr rfl fun y _ => ?_
  unfold blockWeight prodDensity
  rw [← prod_mul_distrib]

theorem sum_left_prod (m : ∀ i, FiniteLaw (H i)) (P : ∀ i, H i → H i → ℝ) (y : ∀ i, H i) :
    ∑ x, blockWeight m x * prodDensity P x y = ∏ i, ∑ x, (m i).weight x * P i x (y i) := by
  rw [Fintype.prod_sum]
  refine sum_congr rfl fun x _ => ?_
  unfold blockWeight prodDensity
  rw [← prod_mul_distrib]

theorem prodDensity_right_marginal {m : ∀ i, FiniteLaw (H i)} {P : ∀ i, H i → H i → ℝ}
    (hP : ∀ i, IsMarginalDensity (m i) (P i)) (x : ∀ i, H i) :
    ∑ y, blockWeight m y * prodDensity P x y = 1 := by
  rw [sum_right_prod]
  exact prod_eq_one fun i _ => (hP i).2.1 (x i)

theorem prodDensity_left_marginal {m : ∀ i, FiniteLaw (H i)} {P : ∀ i, H i → H i → ℝ}
    (hP : ∀ i, IsMarginalDensity (m i) (P i)) (y : ∀ i, H i) :
    ∑ x, blockWeight m x * prodDensity P x y = 1 := by
  rw [sum_left_prod]
  exact prod_eq_one fun i _ => (hP i).2.2 (y i)

theorem blockWeight_total (m : ∀ i, FiniteLaw (H i)) : ∑ x, blockWeight m x = 1 := by
  unfold blockWeight
  rw [← Fintype.prod_sum]
  exact prod_eq_one fun i _ => (m i).total

omit [DecidableEq ι] in
theorem blockWeight_nonneg (m : ∀ i, FiniteLaw (H i)) (x : ∀ i, H i) : 0 ≤ blockWeight m x :=
  prod_nonneg fun i _ => (m i).nonneg _

/-- A product of probability densities has mass one. -/
theorem prodDensity_mass {m : ∀ i, FiniteLaw (H i)} {P : ∀ i, H i → H i → ℝ}
    (hP : ∀ i, IsMarginalDensity (m i) (P i)) :
    ∑ x, ∑ y, blockWeight m x * blockWeight m y * prodDensity P x y = 1 := by
  have h : ∀ x, ∑ y, blockWeight m x * blockWeight m y * prodDensity P x y = blockWeight m x := by
    intro x
    have := prodDensity_right_marginal hP x
    calc ∑ y, blockWeight m x * blockWeight m y * prodDensity P x y
        = blockWeight m x * ∑ y, blockWeight m y * prodDensity P x y := by
          rw [mul_sum]
          exact sum_congr rfl fun y _ => by ring
      _ = blockWeight m x := by rw [this, mul_one]
  simp only [h]
  exact blockWeight_total m

/-- **`def:record:mixture`(c): mass one.** -/
theorem Ksigned_mass {C : SignedComponents H} (hC : C.Valid) (t : ℝ) :
    ∑ x, ∑ y, blockWeight C.m0 x * blockWeight C.m0 y * Ksigned C t x y = 1 := by
  have e : ∀ x y, blockWeight C.m0 x * blockWeight C.m0 y * Ksigned C t x y =
      blockWeight C.m0 x * blockWeight C.m0 y * prodDensity C.Ppp x y +
        t / 2 * (blockWeight C.m0 x * blockWeight C.m0 y * prodDensity C.Pmp x y) -
        t / 2 * (blockWeight C.m0 x * blockWeight C.m0 y * prodDensity C.Pmm x y) := by
    intro x y
    unfold Ksigned
    ring
  simp only [e, sum_sub_distrib, sum_add_distrib, ← mul_sum]
  rw [prodDensity_mass (fun i => (hC i).1), prodDensity_mass (fun i => (hC i).2.1),
    prodDensity_mass (fun i => (hC i).2.2)]
  ring

/-- **`def:record:mixture`(c): the half marginal on the first half is `m_{0,𝔅}`**: the density of
the marginal relative to `m_{0,𝔅}` is one. -/
theorem Ksigned_left_marginal {C : SignedComponents H} (hC : C.Valid) (t : ℝ) (x : ∀ i, H i) :
    ∑ y, blockWeight C.m0 y * Ksigned C t x y = 1 := by
  have e : ∀ y, blockWeight C.m0 y * Ksigned C t x y =
      blockWeight C.m0 y * prodDensity C.Ppp x y +
        t / 2 * (blockWeight C.m0 y * prodDensity C.Pmp x y) -
        t / 2 * (blockWeight C.m0 y * prodDensity C.Pmm x y) := by
    intro y
    unfold Ksigned
    ring
  simp only [e, sum_sub_distrib, sum_add_distrib, ← mul_sum]
  rw [prodDensity_right_marginal (fun i => (hC i).1), prodDensity_right_marginal
    (fun i => (hC i).2.1), prodDensity_right_marginal (fun i => (hC i).2.2)]
  ring

/-- **`def:record:mixture`(c): the half marginal on the second half is `m_{0,𝔅}`.** -/
theorem Ksigned_right_marginal {C : SignedComponents H} (hC : C.Valid) (t : ℝ) (y : ∀ i, H i) :
    ∑ x, blockWeight C.m0 x * Ksigned C t x y = 1 := by
  have e : ∀ x, blockWeight C.m0 x * Ksigned C t x y =
      blockWeight C.m0 x * prodDensity C.Ppp x y +
        t / 2 * (blockWeight C.m0 x * prodDensity C.Pmp x y) -
        t / 2 * (blockWeight C.m0 x * prodDensity C.Pmm x y) := by
    intro x
    unfold Ksigned
    ring
  simp only [e, sum_sub_distrib, sum_add_distrib, ← mul_sum]
  rw [prodDensity_left_marginal (fun i => (hC i).1), prodDensity_left_marginal
    (fun i => (hC i).2.1), prodDensity_left_marginal (fun i => (hC i).2.2)]
  ring

omit [DecidableEq ι] [∀ i, Fintype (H i)] in
theorem prodDensity_nonneg {P : ∀ i, H i → H i → ℝ} (hP : ∀ i x y, 0 ≤ P i x y) (x y : ∀ i, H i) :
    0 ≤ prodDensity P x y :=
  prod_nonneg fun i _ => hP i _ _

/-- **`def:record:mixture`(c): total variation at most `1 + t`, whatever the number of primes**
(`0 ≤ t`): `|K| ≤ ⊗P_{++} + (t/2) ⊗P_{-+} + (t/2) ⊗P_{--}` and each product has mass one. -/
theorem Ksigned_variation {C : SignedComponents H} (hC : C.Valid) {t : ℝ} (ht : 0 ≤ t) :
    ∑ x, ∑ y, blockWeight C.m0 x * blockWeight C.m0 y * |Ksigned C t x y| ≤ 1 + t := by
  have hpt : ∀ x y, blockWeight C.m0 x * blockWeight C.m0 y * |Ksigned C t x y| ≤
      blockWeight C.m0 x * blockWeight C.m0 y * prodDensity C.Ppp x y +
        t / 2 * (blockWeight C.m0 x * blockWeight C.m0 y * prodDensity C.Pmp x y) +
        t / 2 * (blockWeight C.m0 x * blockWeight C.m0 y * prodDensity C.Pmm x y) := by
    intro x y
    have hw : 0 ≤ blockWeight C.m0 x * blockWeight C.m0 y :=
      mul_nonneg (blockWeight_nonneg _ _) (blockWeight_nonneg _ _)
    have h1 := prodDensity_nonneg (fun i => (hC i).1.1) x y
    have h2 := prodDensity_nonneg (fun i => (hC i).2.1.1) x y
    have h3 := prodDensity_nonneg (fun i => (hC i).2.2.1) x y
    have habs : |Ksigned C t x y| ≤ prodDensity C.Ppp x y + t / 2 * prodDensity C.Pmp x y +
        t / 2 * prodDensity C.Pmm x y := by
      unfold Ksigned
      rw [abs_le]
      constructor <;> nlinarith
    calc blockWeight C.m0 x * blockWeight C.m0 y * |Ksigned C t x y|
        ≤ blockWeight C.m0 x * blockWeight C.m0 y * (prodDensity C.Ppp x y +
          t / 2 * prodDensity C.Pmp x y + t / 2 * prodDensity C.Pmm x y) :=
          mul_le_mul_of_nonneg_left habs hw
      _ = _ := by ring
  calc ∑ x, ∑ y, blockWeight C.m0 x * blockWeight C.m0 y * |Ksigned C t x y|
      ≤ ∑ x, ∑ y, (blockWeight C.m0 x * blockWeight C.m0 y * prodDensity C.Ppp x y +
        t / 2 * (blockWeight C.m0 x * blockWeight C.m0 y * prodDensity C.Pmp x y) +
        t / 2 * (blockWeight C.m0 x * blockWeight C.m0 y * prodDensity C.Pmm x y)) :=
        sum_le_sum fun x _ => sum_le_sum fun y _ => hpt x y
    _ = 1 + t := by
        simp only [sum_add_distrib, ← mul_sum]
        rw [prodDensity_mass (fun i => (hC i).1), prodDensity_mass (fun i => (hC i).2.1),
          prodDensity_mass (fun i => (hC i).2.2)]
        ring

/-! ## The record of `F₂`: the reflected transpose (`def:record:mixture`(d)) -/

/-- **The record of `F₂`**, the reflected transpose `K^ς(x, y) = K(ς y, ς x)` taken componentwise
(`ς_p` an involution of the half labels at each prime). -/
noncomputable def Kreflected (C : SignedComponents H) (ς : ∀ i, H i ≃ H i) (t : ℝ)
    (x y : ∀ i, H i) : ℝ :=
  Ksigned C t (fun i => ς i (y i)) (fun i => ς i (x i))

/-- The componentwise reflection, as a bijection of block half labels. -/
def blockRefl (ς : ∀ i, H i ≃ H i) : (∀ i, H i) ≃ (∀ i, H i) := Equiv.piCongrRight ς

omit [DecidableEq ι] in
theorem blockWeight_refl {m : ∀ i, FiniteLaw (H i)} {ς : ∀ i, H i ≃ H i}
    (hς : ∀ i a, (m i).weight (ς i a) = (m i).weight a) (x : ∀ i, H i) :
    blockWeight m (blockRefl ς x) = blockWeight m x := by
  unfold blockWeight blockRefl
  exact prod_congr rfl fun i _ => hς i (x i)

/-- **`def:record:mixture`(d): the record of `F₂` has mass one** when `ς` preserves `m_{0,p}`
(`K₀^ς = K₀`). -/
theorem Kreflected_mass {C : SignedComponents H} (hC : C.Valid) {ς : ∀ i, H i ≃ H i}
    (hς : ∀ i a, (C.m0 i).weight (ς i a) = (C.m0 i).weight a) (t : ℝ) :
    ∑ x, ∑ y, blockWeight C.m0 x * blockWeight C.m0 y * Kreflected C ς t x y = 1 := by
  have h1 : ∑ x, ∑ y, blockWeight C.m0 x * blockWeight C.m0 y * Kreflected C ς t x y =
      ∑ y, ∑ x, blockWeight C.m0 (blockRefl ς y) * blockWeight C.m0 (blockRefl ς x) *
        Ksigned C t (blockRefl ς y) (blockRefl ς x) := by
    rw [sum_comm]
    refine sum_congr rfl fun y _ => sum_congr rfl fun x _ => ?_
    rw [blockWeight_refl hς, blockWeight_refl hς]
    unfold Kreflected blockRefl
    ring_nf
    rfl
  rw [h1]
  have h2 : ∀ y, ∑ x, blockWeight C.m0 (blockRefl ς y) * blockWeight C.m0 (blockRefl ς x) *
      Ksigned C t (blockRefl ς y) (blockRefl ς x) =
      ∑ x, blockWeight C.m0 (blockRefl ς y) * blockWeight C.m0 x *
        Ksigned C t (blockRefl ς y) x := fun y =>
    Fintype.sum_equiv (blockRefl ς) _ (fun x => blockWeight C.m0 (blockRefl ς y) *
      blockWeight C.m0 x * Ksigned C t (blockRefl ς y) x) fun _ => rfl
  simp only [h2]
  rw [Fintype.sum_equiv (blockRefl ς) _ (fun y => ∑ x, blockWeight C.m0 y * blockWeight C.m0 x *
    Ksigned C t y x) fun _ => rfl]
  exact Ksigned_mass hC t

/-- **`def:record:mixture`(d): the half marginals of the record of `F₂` are `m_{0,𝔅}`.** -/
theorem Kreflected_left_marginal {C : SignedComponents H} (hC : C.Valid) {ς : ∀ i, H i ≃ H i}
    (hς : ∀ i a, (C.m0 i).weight (ς i a) = (C.m0 i).weight a) (t : ℝ) (x : ∀ i, H i) :
    ∑ y, blockWeight C.m0 y * Kreflected C ς t x y = 1 := by
  have h : ∑ y, blockWeight C.m0 y * Kreflected C ς t x y =
      ∑ y, blockWeight C.m0 (blockRefl ς y) * Ksigned C t (blockRefl ς y) (blockRefl ς x) := by
    refine sum_congr rfl fun y _ => ?_
    rw [blockWeight_refl hς]
    rfl
  rw [h, Fintype.sum_equiv (blockRefl ς) _ (fun y => blockWeight C.m0 y *
    Ksigned C t y (blockRefl ς x)) fun _ => rfl]
  exact Ksigned_right_marginal hC t _

theorem Kreflected_right_marginal {C : SignedComponents H} (hC : C.Valid) {ς : ∀ i, H i ≃ H i}
    (hς : ∀ i a, (C.m0 i).weight (ς i a) = (C.m0 i).weight a) (t : ℝ) (y : ∀ i, H i) :
    ∑ x, blockWeight C.m0 x * Kreflected C ς t x y = 1 := by
  have h : ∑ x, blockWeight C.m0 x * Kreflected C ς t x y =
      ∑ x, blockWeight C.m0 (blockRefl ς x) * Ksigned C t (blockRefl ς y) (blockRefl ς x) := by
    refine sum_congr rfl fun x _ => ?_
    rw [blockWeight_refl hς]
    rfl
  rw [h, Fintype.sum_equiv (blockRefl ς) _ (fun x => blockWeight C.m0 x *
    Ksigned C t (blockRefl ς y) x) fun _ => rfl]
  exact Ksigned_left_marginal hC t _

end Sarkozy.PartVRecords
