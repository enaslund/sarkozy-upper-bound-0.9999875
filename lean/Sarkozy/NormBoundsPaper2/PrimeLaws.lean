module

public import Sarkozy.NormBoundsPaper.Merge2
public import Sarkozy.NormBoundsPaper2.PairAlgebra

@[expose] public section

/-!
# The source and first-coordinate couplings at one prime (NB2)

`paper/sections/21_middle_records.tex`, `lem:merge-repair` and its proof. At one prime `p`, a merge
record is read at the reserved cut on the two ordered pairs `x = (y_{(0,0)}, y_{(1,0)})` (layer
`0`) and `y = (y_{(0,1)}, y_{(1,1)})` (layer `1`). Its law of `(x, y)` is a coupling matrix on
`(𝔽_p × 𝔽_p)²`:

* `cm μ u₀ u₁ v₀ v₁`, the coupling matrix of a law of labellings read at two pairs of vertices;
  `cm_row`, `cm_col` (its marginals are the pair laws);
* **`srcC_eq`**: for V1's `E` law (the source of every merge record), the coupling is uniform on
  four distinct labels, `ind4 x y / (p(p − 1)(p − 2)(p − 3))`. The proof is the paper's "the source
  operator averages over ordered pairs disjoint from its input pair": every bijection of `𝔽_p`
  preserves the law, the distinct quadruples are one orbit (`Equiv.Perm.exists_extending_pair`),
  and the row sums are the pair law `p⁻¹ k_D` (`pw_match`);
* **`firstC_eq`**: V3's first-coordinate replacement has coupling
  `p⁻¹ k_P(y₀ − x₀) k_D(x₁ − x₀) k_D(y₁ − y₀)` (`firstWeight_eq`);
* `mP p x = p⁻¹ k_D(x₁ − x₀)`, the actual half law (uniform on ordered distinct pairs); both
  couplings have both marginals `mP` (`srcC_coupling`, `firstC_coupling`).
-/

open Finset Matrix
open scoped BigOperators

namespace Sarkozy.NormBoundsPaper2

open Sarkozy.PartV Sarkozy.Labellings Sarkozy.PartVRecords
open Sarkozy.NormBoundsPaper (kD kP pw pw_match sum_kP sum_kD p_gt_one firstWeight_eq
  firstLaw_weight)

section Coupling

variable {W : Type} [Fintype W] [DecidableEq W] {F : Type} [Fintype F] [DecidableEq F]

/-- The coupling matrix of a law of labellings read at the pairs `(u₀, u₁)` and `(v₀, v₁)`. -/
noncomputable def cm (μ : FiniteLaw (W → F)) (u₀ u₁ v₀ v₁ : W) : Matrix (F × F) (F × F) ℝ :=
  fun x y => ∑ z, μ.weight z *
    (if z u₀ = x.1 ∧ z u₁ = x.2 ∧ z v₀ = y.1 ∧ z v₁ = y.2 then 1 else 0)

theorem cm_nonneg (μ : FiniteLaw (W → F)) (u₀ u₁ v₀ v₁ : W) (x y : F × F) :
    0 ≤ cm μ u₀ u₁ v₀ v₁ x y :=
  sum_nonneg fun z _ => mul_nonneg (μ.nonneg z) (by split_ifs <;> norm_num)

theorem cm_row (μ : FiniteLaw (W → F)) (u₀ u₁ v₀ v₁ : W) (x : F × F) :
    ∑ y, cm μ u₀ u₁ v₀ v₁ x y = pw μ u₀ u₁ x.1 x.2 := by
  unfold cm pw
  rw [sum_comm]
  refine sum_congr rfl fun z _ => ?_
  rw [← mul_sum]
  congr 1
  rw [sum_eq_single (z v₀, z v₁)]
  · simp
  · intro y _ hy
    refine ite_eq_right fun h => hy ?_
    exact Prod.ext h.2.2.1.symm h.2.2.2.symm
  · exact fun h => absurd (mem_univ _) h

theorem cm_col (μ : FiniteLaw (W → F)) (u₀ u₁ v₀ v₁ : W) (y : F × F) :
    ∑ x, cm μ u₀ u₁ v₀ v₁ x y = pw μ v₀ v₁ y.1 y.2 := by
  unfold cm pw
  rw [sum_comm]
  refine sum_congr rfl fun z _ => ?_
  rw [← mul_sum]
  congr 1
  rw [sum_eq_single (z u₀, z u₁)]
  · simp
  · intro x _ hx
    refine ite_eq_right fun h => hx ?_
    exact Prod.ext h.1.symm h.2.1.symm
  · exact fun h => absurd (mem_univ _) h

end Coupling

/-! ## One prime -/

section Prime

variable {p : ℕ} [Fact p.Prime]

/-- The actual half law of a merge record at one prime: `p⁻¹ k_D(x₁ − x₀)`, uniform on ordered
distinct pairs. -/
noncomputable def mP (p : ℕ) [Fact p.Prime] (x : ZMod p × ZMod p) : ℝ :=
  (1 / (p : ℝ)) * kD p (x.2 - x.1)

theorem mP_nonneg (x : ZMod p × ZMod p) : 0 ≤ mP p x := by
  unfold mP kD
  have : (1 : ℝ) < p := p_gt_one
  split_ifs
  · simp
  · exact mul_nonneg (by positivity) (one_div_pos.mpr (by linarith)).le

theorem mP_eq_off (x : ZMod p × ZMod p) : mP p x = off x / ((p : ℝ) * ((p : ℝ) - 1)) := by
  unfold mP kD off
  have : (1 : ℝ) < p := p_gt_one
  have h0 : (p : ℝ) ≠ 0 := by linarith
  have h1 : (p : ℝ) - 1 ≠ 0 := by linarith
  by_cases h : x.1 = x.2
  · simp [h]
  · have h' : x.2 - x.1 ≠ 0 := sub_ne_zero.mpr (Ne.symm h)
    simp only [h', h, ↓reduceIte]
    field_simp

theorem sum_mP : ∑ x, mP p x = 1 := by
  have h := NormBoundsPaper.sum_kernel_pair (sum_kD (p := p))
  rw [← h, Fintype.sum_prod_type]
  rfl

/-! ### The source: V1's `E` law -/

variable (hne : (injLabellings (ZMod p) (matchGraph (Fin 2))).Nonempty)

/-- The source coupling of a merge record at one prime: the `E` law read at the objects `0, 1` of
layer `0` and of layer `1`. -/
noncomputable def srcC : Matrix (ZMod p × ZMod p) (ZMod p × ZMod p) ℝ :=
  cm (graphLaw (matchGraph (Fin 2)) hne) (0, 0) (1, 0) (0, 1) (1, 1)

theorem srcC_perm (σ : Equiv.Perm (ZMod p)) (x y : ZMod p × ZMod p) :
    srcC hne (σ x.1, σ x.2) (σ y.1, σ y.2) = srcC hne x y := by
  unfold srcC cm
  have hmem : ∀ z : Fin 3 × Fin 2 → ZMod p,
      (fun w => σ (z w)) ∈ injLabellings (ZMod p) (matchGraph (Fin 2)) ↔
        z ∈ injLabellings (ZMod p) (matchGraph (Fin 2)) := by
    intro z
    rw [mem_injLabellings_iff_feasible, mem_injLabellings_iff_feasible]
    constructor
    · rintro ⟨h1, -⟩
      exact ⟨fun x hx w hw hxw => h1 x hx w hw (congrArg σ hxw),
        fun e he => absurd he (Finset.notMem_empty _)⟩
    · rintro ⟨h1, -⟩
      exact ⟨fun x hx w hw hxw => h1 x hx w hw (σ.injective hxw),
        fun e he => absurd he (Finset.notMem_empty _)⟩
  refine (Fintype.sum_equiv (Equiv.piCongrRight fun _ => σ) _ _ fun z => ?_).symm
  change _ = (graphLaw (matchGraph (Fin 2)) hne).weight (fun w => σ (z w)) *
    (if σ (z (0, 0)) = σ x.1 ∧ σ (z (1, 0)) = σ x.2 ∧ σ (z (0, 1)) = σ y.1 ∧
      σ (z (1, 1)) = σ y.2 then (1 : ℝ) else 0)
  simp only [σ.injective.eq_iff]
  congr 1
  unfold graphLaw
  simp only [hmem]

/-- Off the distinct quadruples the source coupling vanishes. -/
theorem srcC_support {x y : ZMod p × ZMod p} (h : srcC hne x y ≠ 0) :
    x.1 ≠ x.2 ∧ y.1 ≠ y.2 ∧ y.1 ≠ x.1 ∧ y.1 ≠ x.2 ∧ y.2 ≠ x.1 ∧ y.2 ≠ x.2 := by
  obtain ⟨z, -, hz⟩ := exists_ne_zero_of_sum_ne_zero h
  have hw : (graphLaw (matchGraph (Fin 2)) hne).weight z ≠ 0 := fun h0 => hz (by rw [h0, zero_mul])
  have hc : z (0, 0) = x.1 ∧ z (1, 0) = x.2 ∧ z (0, 1) = y.1 ∧ z (1, 1) = y.2 := by
    by_contra hc
    exact hz (by rw [ite_eq_right hc, mul_zero])
  have hinj := (graphLaw_support (matchGraph (Fin 2)) hne hw).1
  obtain ⟨h1, h2, h3, h4⟩ := hc
  have d : ∀ u v : Fin 3 × Fin 2, u ≠ v → z u ≠ z v := fun u v huv e =>
    huv (hinj u (mem_univ _) v (mem_univ _) e)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← h1, ← h2]; exact d _ _ (by decide)
  · rw [← h3, ← h4]; exact d _ _ (by decide)
  · rw [← h3, ← h1]; exact d _ _ (by decide)
  · rw [← h3, ← h2]; exact d _ _ (by decide)
  · rw [← h4, ← h1]; exact d _ _ (by decide)
  · rw [← h4, ← h2]; exact d _ _ (by decide)

/-- The reference quadruple `(0, 1), (2, 3)`. -/
def q0 : (ZMod p × ZMod p) × (ZMod p × ZMod p) := ((0, 1), (2, 3))

theorem q0_distinct (hp : 5 ≤ p) :
    Function.Injective (![(0 : ZMod p), 1, 2, 3] : Fin 4 → ZMod p) := by
  have hval : ∀ k : Fin 4,
      (![(0 : ZMod p), 1, 2, 3] : Fin 4 → ZMod p) k = ((k.val : ℕ) : ZMod p) := by
    intro k
    fin_cases k <;> simp
  intro i j hij
  rw [hval, hval, ZMod.natCast_eq_natCast_iff'] at hij
  rw [Nat.mod_eq_of_lt (by omega : i.val < p), Nat.mod_eq_of_lt (by omega : j.val < p)] at hij
  exact Fin.ext hij

/-- **The source coupling is constant on the distinct quadruples.** -/
theorem srcC_const (hp : 5 ≤ p) {x y : ZMod p × ZMod p}
    (h : x.1 ≠ x.2 ∧ y.1 ≠ y.2 ∧ y.1 ≠ x.1 ∧ y.1 ≠ x.2 ∧ y.2 ≠ x.1 ∧ y.2 ≠ x.2) :
    srcC hne x y = srcC hne (0, 1) (2, 3) := by
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  have hinj : Function.Injective (![x.1, x.2, y.1, y.2] : Fin 4 → ZMod p) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [eq_comm]
  obtain ⟨σ, hσ⟩ := Equiv.Perm.exists_extending_pair _ _ (q0_distinct hp) hinj
  have e0 : σ 0 = x.1 := hσ 0
  have e1 : σ 1 = x.2 := hσ 1
  have e2 : σ 2 = y.1 := hσ 2
  have e3 : σ 3 = y.2 := hσ 3
  have := srcC_perm hne σ (0, 1) (2, 3)
  simp only [e0, e1, e2, e3] at this
  exact this

/-- **The source coupling**: `ind4 x y / (p(p − 1)(p − 2)(p − 3))`. -/
theorem srcC_eq (hp : 5 ≤ p) (x y : ZMod p × ZMod p) :
    srcC hne x y = ind4 x y / ((p : ℝ) * ((p : ℝ) - 1) * ((p : ℝ) - 2) * ((p : ℝ) - 3)) := by
  have hp' : (5 : ℝ) ≤ p := by exact_mod_cast hp
  set κ := srcC hne (0, 1) (2, 3)
  have hform : ∀ x y : ZMod p × ZMod p, srcC hne x y = κ * ind4 x y := by
    intro x y
    rw [ind4_eq]
    by_cases h : x.1 ≠ x.2 ∧ y.1 ≠ y.2 ∧ y.1 ≠ x.1 ∧ y.1 ≠ x.2 ∧ y.2 ≠ x.1 ∧ y.2 ≠ x.2
    · rw [ite_eq_left_of_eq_true _ _ (eq_true h), mul_one]
      exact srcC_const hne hp h
    · rw [ite_eq_right_of_eq_false _ _ (eq_false h), mul_zero]
      by_contra h0
      exact h (srcC_support hne h0)
  -- the row at `(0, 1)` is the pair law
  have hrow := cm_row (graphLaw (matchGraph (Fin 2)) hne) (0, 0) (1, 0) (0, 1) (1, 1)
    ((0 : ZMod p), (1 : ZMod p))
  rw [pw_match hne (by decide)] at hrow
  change ∑ y, srcC hne _ y = _ at hrow
  simp only [hform, ← mul_sum] at hrow
  have hcount := sum_ind4_row (X := ZMod p) (show (0 : ZMod p) ≠ 1 from zero_ne_one)
  rw [hcount, ZMod.card] at hrow
  have h10 : (1 : ZMod p) - 0 ≠ 0 := sub_ne_zero.mpr one_ne_zero
  simp only [kD, h10, ↓reduceIte] at hrow
  have h1 : (p : ℝ) - 1 ≠ 0 := by linarith
  have h2 : (p : ℝ) - 2 ≠ 0 := by linarith
  have h3 : (p : ℝ) - 3 ≠ 0 := by linarith
  have h0 : (p : ℝ) ≠ 0 := by linarith
  have hκ : κ = 1 / ((p : ℝ) * ((p : ℝ) - 1) * ((p : ℝ) - 2) * ((p : ℝ) - 3)) := by
    field_simp at hrow ⊢
    linarith
  rw [hform, hκ]
  ring

theorem srcC_coupling (x : ZMod p × ZMod p) :
    ∑ y, srcC hne x y = mP p x ∧ ∑ y, srcC hne y x = mP p x := by
  constructor
  · rw [srcC, cm_row, pw_match hne (by decide)]
    rfl
  · rw [srcC, cm_col, pw_match hne (by decide)]
    rfl

theorem srcC_nonneg (x y : ZMod p × ZMod p) : 0 ≤ srcC hne x y := cm_nonneg _ _ _ _ _ x y

/-! ### The first-coordinate replacement -/

variable (hF : ringChar (ZMod p) ≠ 2)

/-- The first-coordinate coupling at one prime. -/
noncomputable def firstC : Matrix (ZMod p × ZMod p) (ZMod p × ZMod p) ℝ :=
  cm (firstLaw (ZMod p) hF) (0, 0) (1, 0) (0, 1) (1, 1)

/-- **V3's first-coordinate coupling**: `p⁻¹ k_P(y₀ − x₀) k_D(x₁ − x₀) k_D(y₁ − y₀)`. -/
theorem firstC_eq (x y : ZMod p × ZMod p) :
    firstC hF x y = (1 / (p : ℝ)) * kP p (y.1 - x.1) * kD p (x.2 - x.1) * kD p (y.2 - y.1) := by
  unfold firstC cm
  rw [sum_eq_single (NormBoundsPaper.quadEquiv (x.1, x.2, y.1, y.2))]
  · obtain ⟨h1, h2, h3, h4⟩ := quadConfig_apply (x.1, x.2, y.1, y.2)
    change (firstLaw (ZMod p) hF).weight (quadConfig (x.1, x.2, y.1, y.2)) *
      (if quadConfig (x.1, x.2, y.1, y.2) (0, 0) = x.1 ∧ quadConfig (x.1, x.2, y.1, y.2) (1, 0) =
        x.2 ∧ quadConfig (x.1, x.2, y.1, y.2) (0, 1) = y.1 ∧
          quadConfig (x.1, x.2, y.1, y.2) (1, 1) = y.2 then (1 : ℝ) else 0) = _
    rw [firstLaw_weight]
    simp only [h1, h2, h3, h4, firstWeight_eq, and_self, ↓reduceIte, mul_one]
  · intro z _ hz
    have hc : ¬ (z (0, 0) = x.1 ∧ z (1, 0) = x.2 ∧ z (0, 1) = y.1 ∧ z (1, 1) = y.2) := by
      rintro ⟨h1, h2, h3, h4⟩
      refine hz ?_
      have e : z = quadConfig (z (0, 0), z (1, 0), z (0, 1), z (1, 1)) :=
        (NormBoundsPaper.quadEquiv.right_inv z).symm
      exact e.trans (by rw [h1, h2, h3, h4]; rfl)
    simp only [hc, ↓reduceIte, mul_zero]
  · exact fun h => absurd (mem_univ _) h

theorem firstC_nonneg (x y : ZMod p × ZMod p) : 0 ≤ firstC hF x y := cm_nonneg _ _ _ _ _ x y

theorem sum_shift {k : ZMod p → ℝ} (a : ZMod p) : ∑ c, k (c - a) = ∑ d, k d :=
  Fintype.sum_equiv (Equiv.subRight a) (fun c => k (c - a)) k (fun _ => rfl)

theorem sum_shift' {k : ZMod p → ℝ} (c : ZMod p) : ∑ a, k (c - a) = ∑ d, k d :=
  Fintype.sum_equiv ((Equiv.neg _).trans (Equiv.addLeft c)) (fun a => k (c - a)) k
    (fun a => by simp [sub_eq_add_neg])

theorem firstC_coupling (hp2 : p ≠ 2) (x : ZMod p × ZMod p) :
    ∑ y, firstC hF x y = mP p x ∧ ∑ y, firstC hF y x = mP p x := by
  constructor
  · simp only [firstC_eq, Fintype.sum_prod_type]
    have : ∀ a : ZMod p, ∑ b : ZMod p, (1 / (p : ℝ)) * kP p (a - x.1) * kD p (x.2 - x.1) *
        kD p (b - a) = (1 / (p : ℝ)) * kP p (a - x.1) * kD p (x.2 - x.1) := fun a => by
      rw [← mul_sum, sum_shift, sum_kD, mul_one]
    rw [sum_congr rfl fun a _ => this a, ← sum_mul, ← mul_sum, sum_shift, sum_kP hp2]
    unfold mP
    ring
  · simp only [firstC_eq, Fintype.sum_prod_type]
    have : ∀ a : ZMod p, ∑ b : ZMod p, (1 / (p : ℝ)) * kP p (x.1 - a) * kD p (b - a) *
        kD p (x.2 - x.1) = (1 / (p : ℝ)) * kP p (x.1 - a) * kD p (x.2 - x.1) := fun a => by
      rw [← sum_mul, ← mul_sum, sum_shift, sum_kD, mul_one]
    rw [sum_congr rfl fun a _ => this a, ← sum_mul, ← mul_sum, sum_shift', sum_kP hp2]
    unfold mP
    ring

end Prime

end Sarkozy.NormBoundsPaper2
