module

public import Sarkozy.Mixing.Differences
public import Sarkozy.IndexSupport.HalfFunctions

@[expose] public section

/-!
# The edge `03` at a block from the prime inputs (`lem:oct24:feature-block`(a), proof Step 3)

`paper/sections/23_envelopes.tex`, `lem:oct24:feature-block`, proof Steps 1 and 3. Abstract form:
coordinates `j` with laws `π_j` (of `x₀`) and `β_j` (of the pair `(x₁, x₂)`), the conditional
expectation `T_j` of a function of `x₀` given the pair and its projection `T₂_j` onto the
functions of `x₂` (rows depending only on `ζ_j`, the `x₂` coordinate of the pair); `η_j` is the
`x₁` coordinate. For `X` centred and `K` orthogonal to every function of the whole `x₁` and of the
whole `x₂` (the feature `𝒦₁₂`), **`edge03_sectors`** proves
`|⟨(⊗_j T_j) X, K⟩_β| ≤ c ‖X‖_π ‖K‖_β`, given

* `hprime` (one prime, the bound of Step 3 on the sectors of size one): the correlation of
  `𝓗₀` and the one-prime `𝒦₁₂` is at most `c`;
* `hTa`, `hT2a`, `hTd` (the coarse prime estimates of Step 3): `‖T_j‖, ‖T₂_j‖ ≤ ρa` and
  `‖T_j - T₂_j‖ ≤ ρb` on the centred functions;
* the gates `ρa ≤ 1/2`, `2 ρb ρa ≤ c` (`cert:envelopes`(a)).

The proof is the paper's: decompose `X` into its exact-support sectors (`lem:sector`(a));
`⊗T` maps the sector `S` of `L²(π)` into the sector `S` of `L²(β)` (Mixing's
`prodOp_maps_sector`); on a sector of size one the form reduces to one prime
(`singleton_form`); on a sector of size `k ≥ 2` the tensor of the `T₂_j` maps into the functions of
`x₂`, which `K` annihilates, and the telescoping bound of `lem:sector`(b) (Mixing's
`difference_telescoping`) gives `k ρb ρa^{k-1} ≤ 2 ρb ρa ≤ c`; Cauchy–Schwarz over the sectors and
Parseval on both sides conclude.
-/

open Finset Matrix
open scoped BigOperators

namespace Sarkozy.OpsFeature

open Sarkozy.Mixing Sarkozy.IndexSupport

section Sectors

variable {K : Type*} [Fintype K] [DecidableEq K] {A : K → Type*} [∀ j, Fintype (A j)]
  [∀ j, DecidableEq (A j)]

/-- No spectator coordinates. -/
def noSpec : K → Bool := fun _ => false

/-- The weighted inner product of `L²(⊗_j w_j)`. -/
noncomputable def wip (w : ∀ j, A j → ℝ) (G H : (∀ j, A j) → ℝ) : ℝ :=
  ∑ a, prodW w a * G a * H a

/-- The sector projections resolve the identity. -/
theorem sum_sectorProj (w : ∀ j, A j → ℝ) :
    ∑ l : K → Bool, wSectorProj w noSpec l = 1 := by
  simp only [wSectorProj, noSpec]
  rw [piKron_sum (fun j (s : Bool) => wProj (w j) false s)]
  have h : ∀ j, ∑ t : Bool, wProj (w j) false t = 1 := fun j => by
    rw [Fintype.sum_bool, add_comm]; exact wProj_sum (w j) false
  simp only [h]
  exact piKron_one

omit [∀ j, DecidableEq (A j)] in
/-- The entries of a coordinate projection are `w`-symmetric. -/
theorem wProj_symm {A' : Type*} [Fintype A'] [DecidableEq A'] (w : A' → ℝ) (s : Bool)
    (x y : A') :
    w x * wProj w false s x y = w y * wProj w false s y x := by
  cases s <;> simp only [wProj, Bool.false_eq_true, ite_false, ite_true, avgMatrix,
    Matrix.sub_apply, Matrix.one_apply]
  · ring
  · by_cases h : x = y
    · subst h; ring
    · rw [ite_eq_right h, ite_eq_right (Ne.symm h)]; ring

/-- **The sector projections are self-adjoint in `L²(⊗ w_j)`.** -/
theorem wip_sectorProj (w : ∀ j, A j → ℝ) (l : K → Bool) (G H : (∀ j, A j) → ℝ) :
    wip w (wSectorProj w noSpec l *ᵥ G) H = wip w G (wSectorProj w noSpec l *ᵥ H) := by
  have hsym : ∀ a a', prodW w a * wSectorProj w noSpec l a a' =
      prodW w a' * wSectorProj w noSpec l a' a := by
    intro a a'
    simp only [prodW, wSectorProj, piKron_apply, noSpec, ← prod_mul_distrib]
    exact prod_congr rfl fun j _ => wProj_symm (w j) (l j) (a j) (a' j)
  unfold wip
  simp only [mulVec, dotProduct, mul_sum, sum_mul]
  rw [sum_comm]
  refine sum_congr rfl fun a _ => sum_congr rfl fun a' _ => ?_
  have := hsym a' a
  calc prodW w a' * (wSectorProj w noSpec l a' a * G a) * H a'
      = (prodW w a' * wSectorProj w noSpec l a' a) * G a * H a' := by ring
    _ = (prodW w a * wSectorProj w noSpec l a a') * G a * H a' := by rw [this]
    _ = _ := by ring

/-- The sector projections are idempotent. -/
theorem sectorProj_idem (w : ∀ j, A j → ℝ) (hw1 : ∀ j, ∑ a, w j a = 1) (l : K → Bool)
    (X : (∀ j, A j) → ℝ) :
    wSectorProj w noSpec l *ᵥ (wSectorProj w noSpec l *ᵥ X) = wSectorProj w noSpec l *ᵥ X := by
  rw [mulVec_mulVec, wSectorProj, piKron_mul]
  congr 2
  funext j
  rw [wProj_mul (hw1 j), ite_eq_left rfl]

/-- The empty sector of a centred function vanishes. -/
theorem sectorProj_empty (w : ∀ j, A j → ℝ) (X : (∀ j, A j) → ℝ)
    (hX : ∑ a, prodW w a * X a = 0) :
    wSectorProj w noSpec (fun _ => false) *ᵥ X = 0 := by
  funext a
  simp only [mulVec, dotProduct, wSectorProj, piKron_apply, noSpec, wProj, Bool.false_eq_true,
    ite_false, avgMatrix, Pi.zero_apply]
  exact hX

/-- A sector component other than the empty one is centred. -/
theorem sectorProj_mean (w : ∀ j, A j → ℝ) (hw1 : ∀ j, ∑ a, w j a = 1) {l : K → Bool}
    {p : K} (hp : l p = true) (X : (∀ j, A j) → ℝ) :
    ∑ a, prodW w a * (wSectorProj w noSpec l *ᵥ X) a = 0 := by
  have h1 : wSectorProj w noSpec l *ᵥ (fun _ => (1 : ℝ)) = 0 := by
    funext a
    simp only [mulVec, dotProduct, mul_one, wSectorProj, piKron_apply, Pi.zero_apply]
    rw [← Fintype.prod_sum (fun j t => wProj (w j) (noSpec j) (l j) (a j) t)]
    refine prod_eq_zero (mem_univ p) ?_
    rw [show wProj (w p) (noSpec p) (l p) = 1 - avgMatrix (w p) by simp [wProj, noSpec, hp]]
    simp [Matrix.sub_apply, Matrix.one_apply, avgMatrix, sum_sub_distrib, hw1 p]
  have := wip_sectorProj w l X (fun _ => 1)
  simp only [wip, mul_one, h1, Pi.zero_apply, mul_zero, sum_const_zero] at this
  exact this

end Sectors

/-! ## Functions of one coordinate -/

section Single

variable {K : Type*} [Fintype K] [DecidableEq K] {A B : K → Type*} [∀ j, Fintype (A j)]
  [∀ j, Fintype (B j)]

omit [∀ j, Fintype (B j)] in
/-- **A tensor product acts on a function of one coordinate through that coordinate**:
`(⊗_j T_j)(g ∘ ev_p) = (T_p g) ∘ ev_p` when the other `T_j` fix the constants. -/
theorem prodOp_single (T : ∀ j, Matrix (B j) (A j) ℝ) (p : K)
    (hrow : ∀ j, j ≠ p → ∀ b, ∑ a, T j b a = 1) (g : A p → ℝ) (b : ∀ j, B j) :
    (prodOp T *ᵥ (fun a => g (a p))) b = (T p *ᵥ g) (b p) := by
  simp only [mulVec, dotProduct, prodOp]
  rw [← (Equiv.piSplitAt p A).symm.sum_comp, Fintype.sum_prod_type]
  have key : ∀ (t : A p) (r : ∀ j : {j // j ≠ p}, A j),
      (∏ j, T j (b j) ((Equiv.piSplitAt p A).symm (t, r) j)) *
        g ((Equiv.piSplitAt p A).symm (t, r) p) =
      T p (b p) t * g t * ∏ j : {j // j ≠ p}, T j (b j) (r j) := by
    intro t r
    rw [Fintype.prod_eq_mul_prod_subtype_ne _ p]
    have h1 : (Equiv.piSplitAt p A).symm (t, r) p = t := by
      rw [Equiv.piSplitAt_symm_apply]; simp
    have h2 : ∀ j : {j // j ≠ p}, (Equiv.piSplitAt p A).symm (t, r) j.1 = r j := by
      intro j; rw [Equiv.piSplitAt_symm_apply]; simp [j.2]
    rw [h1]
    simp only [h2]
    ring
  simp only [key]
  have hr : ∑ r : (∀ j : {j // j ≠ p}, A j), ∏ j : {j // j ≠ p}, T j (b j) (r j) = 1 := by
    rw [← Fintype.prod_sum (fun (j : {j // j ≠ p}) t => T j (b j) t)]
    exact prod_eq_one fun j _ => hrow j j.2 (b j)
  rw [sum_comm]
  simp only [← sum_mul]
  rw [← mul_sum, hr, mul_one]

end Single

/-! ## The singleton sectors -/

section SingleSector

variable {K : Type*} [Fintype K] [DecidableEq K] {A : K → Type*} [∀ j, Fintype (A j)]
  [∀ j, DecidableEq (A j)]

/-- The support `{p}`. -/
def single (p : K) : K → Bool := fun j => decide (j = p)

/-- A component in the sector `{p}` depends only on the coordinate `p`. -/
theorem sectorProj_single_eq (w : ∀ j, A j → ℝ) (p : K) (X : (∀ j, A j) → ℝ)
    (a a' : ∀ j, A j) (h : a p = a' p) :
    (wSectorProj w noSpec (single p) *ᵥ X) a = (wSectorProj w noSpec (single p) *ᵥ X) a' := by
  simp only [mulVec, dotProduct, wSectorProj, piKron_apply]
  refine sum_congr rfl fun a'' _ => ?_
  congr 1
  refine prod_congr rfl fun j _ => ?_
  by_cases hj : j = p
  · subst hj; rw [h]
  · simp [noSpec, single, hj, wProj, avgMatrix]

/-- A component in the sector `{p}` is a function of the coordinate `p`. -/
theorem sectorProj_single_fun [∀ j, Nonempty (A j)] (w : ∀ j, A j → ℝ) (p : K)
    (X : (∀ j, A j) → ℝ) :
    ∃ g : A p → ℝ, wSectorProj w noSpec (single p) *ᵥ X = fun a => g (a p) := by
  classical
  let a₀ : ∀ j, A j := fun j => Classical.arbitrary (A j)
  refine ⟨fun t => (wSectorProj w noSpec (single p) *ᵥ X) (Function.update a₀ p t), ?_⟩
  funext a
  exact sectorProj_single_eq w p X a _ (by simp)

/-- The projection onto the sector `{p}` of a function of the coordinate `p`:
`P_{{p}} (h ∘ ev_p) = (h - E h) ∘ ev_p`. -/
theorem sectorProj_single_coord (w : ∀ j, A j → ℝ) (hw1 : ∀ j, ∑ a, w j a = 1) (p : K)
    (h : A p → ℝ) :
    wSectorProj w noSpec (single p) *ᵥ (fun a => h (a p)) =
      fun a => h (a p) - ∑ t, w p t * h t := by
  funext a
  have e := prodOp_single (fun j => wProj (w j) (noSpec j) (single p j)) p (fun j hj b => by
    simp [noSpec, single, hj, wProj, avgMatrix, hw1 j]) h a
  rw [show wSectorProj w noSpec (single p) = prodOp (fun j => wProj (w j) (noSpec j)
    (single p j)) from rfl, e]
  have hw : wProj (w p) (noSpec p) (single p p) = 1 - avgMatrix (w p) := by
    simp [wProj, noSpec, single]
  rw [hw]
  simp only [mulVec, dotProduct, avgMatrix, Matrix.sub_apply, Matrix.one_apply, sub_mul, ite_mul,
    one_mul, zero_mul, sum_sub_distrib, sum_ite_eq, mem_univ, ite_true]

end SingleSector

/-! ## A numerical lemma -/

theorem nat_mul_pow_le {x : ℝ} (hx0 : 0 ≤ x) (hx : x ≤ 1 / 2) (n : ℕ) (hn : 2 ≤ n) :
    (n : ℝ) * x ^ (n - 1) ≤ 2 * x := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  clear hn
  have hm : ((m : ℝ) + 2) * (1 / 2) ^ m ≤ 2 := by
    induction m with
    | zero => norm_num
    | succ k ih =>
      have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
      calc ((↑(k + 1) : ℝ) + 2) * (1 / 2) ^ (k + 1)
          = ((k : ℝ) + 3) / 2 * (1 / 2) ^ k := by push_cast; ring
        _ ≤ ((k : ℝ) + 2) * (1 / 2) ^ k := by
            apply mul_le_mul_of_nonneg_right _ (by positivity); linarith
        _ ≤ 2 := ih
  have hpow : x ^ m ≤ (1 / 2) ^ m := pow_le_pow_left₀ hx0 hx m
  have e : m + 2 - 1 = m + 1 := by omega
  rw [e, pow_succ]
  push_cast
  calc ((m : ℝ) + 2) * (x ^ m * x) = (((m : ℝ) + 2) * x ^ m) * x := by ring
    _ ≤ (((m : ℝ) + 2) * (1 / 2) ^ m) * x := by
        apply mul_le_mul_of_nonneg_right _ hx0
        exact mul_le_mul_of_nonneg_left hpow (by positivity)
    _ ≤ 2 * x := mul_le_mul_of_nonneg_right hm hx0

/-! ## The block bound -/

section Block03

variable {K : Type*} [Fintype K] [DecidableEq K] {A B : K → Type*} [∀ j, Fintype (A j)]
  [∀ j, DecidableEq (A j)] [∀ j, Fintype (B j)] [∀ j, DecidableEq (B j)]

omit [∀ j, DecidableEq (A j)] in
theorem wip_comm (w : ∀ j, A j → ℝ) (G H : (∀ j, A j) → ℝ) : wip w G H = wip w H G := by
  unfold wip; exact sum_congr rfl fun a _ => by ring

omit [∀ j, DecidableEq (A j)] in
theorem abs_wip_le (w : ∀ j, A j → ℝ) (hw : ∀ j a, 0 ≤ w j a) (G H : (∀ j, A j) → ℝ) :
    |wip w G H| ≤ wNorm (prodW w) G * wNorm (prodW w) H := by
  unfold wip wNorm
  have h := sum_mul_sq_le_sq_mul_sq univ (fun a => Real.sqrt (prodW w a) * G a)
    (fun a => Real.sqrt (prodW w a) * H a)
  have hp : ∀ a, 0 ≤ prodW w a := fun a => prod_nonneg fun j _ => hw j (a j)
  have e1 : ∀ a, Real.sqrt (prodW w a) * G a * (Real.sqrt (prodW w a) * H a) =
      prodW w a * G a * H a := fun a => by
    have := Real.mul_self_sqrt (hp a)
    calc _ = (Real.sqrt (prodW w a) * Real.sqrt (prodW w a)) * G a * H a := by ring
      _ = _ := by rw [this]
  have e2 : ∀ (F : (∀ j, A j) → ℝ) a, (Real.sqrt (prodW w a) * F a) ^ 2 = prodW w a * F a ^ 2 :=
    fun F a => by rw [mul_pow, Real.sq_sqrt (hp a)]
  simp only [e1, e2] at h
  rw [← Real.sqrt_mul (sum_nonneg fun a _ => mul_nonneg (hp a) (sq_nonneg _))]
  exact Real.abs_le_sqrt h

/-- **`lem:oct24:feature-block`(a), proof Step 3, at a block, from the prime inputs.** See the
module docstring. -/
theorem edge03_sectors [∀ j, Nonempty (A j)] [∀ j, Nonempty (B j)] (π : ∀ j, A j → ℝ)
    (β : ∀ j, B j → ℝ)
    (hπ : ∀ j a, 0 ≤ π j a) (hπ1 : ∀ j, ∑ a, π j a = 1) (hβ : ∀ j b, 0 ≤ β j b)
    (hβ1 : ∀ j, ∑ b, β j b = 1) (T T2 : ∀ j, Matrix (B j) (A j) ℝ)
    (hrow : ∀ j b, ∑ a, T j b a = 1) (hrow2 : ∀ j b, ∑ a, T2 j b a = 1)
    (hcol : ∀ j a, ∑ b, β j b * T j b a = π j a) (hcol2 : ∀ j a, ∑ b, β j b * T2 j b a = π j a)
    {C D : K → Type*} (η : ∀ j, B j → C j) (ζ : ∀ j, B j → D j)
    (hT2ζ : ∀ j b b', ζ j b = ζ j b' → ∀ a, T2 j b a = T2 j b' a)
    {c ρa ρb : ℝ} (hc : 0 ≤ c) (hρa : 0 ≤ ρa) (hρa2 : ρa ≤ 1 / 2) (hρb : 0 ≤ ρb)
    (hgate : 2 * ρb * ρa ≤ c)
    (hprime : ∀ j (g : A j → ℝ) (κ : B j → ℝ), ∑ a, π j a * g a = 0 →
      (∀ h : C j → ℝ, ∑ b, β j b * κ b * h (η j b) = 0) →
      (∀ h : D j → ℝ, ∑ b, β j b * κ b * h (ζ j b) = 0) →
      |∑ b, β j b * (T j *ᵥ g) b * κ b| ≤
        c * (Real.sqrt (∑ a, π j a * g a ^ 2) * Real.sqrt (∑ b, β j b * κ b ^ 2)))
    (hTa : ∀ j f, ∑ a, π j a * f a = 0 →
      ∑ b, β j b * (T j *ᵥ f) b ^ 2 ≤ ρa ^ 2 * ∑ a, π j a * f a ^ 2)
    (hT2a : ∀ j f, ∑ a, π j a * f a = 0 →
      ∑ b, β j b * (T2 j *ᵥ f) b ^ 2 ≤ ρa ^ 2 * ∑ a, π j a * f a ^ 2)
    (hTd : ∀ j f, ∑ a, π j a * f a = 0 →
      ∑ b, β j b * ((T j - T2 j) *ᵥ f) b ^ 2 ≤ ρb ^ 2 * ∑ a, π j a * f a ^ 2)
    (X : (∀ j, A j) → ℝ) (hX : ∑ a, prodW π a * X a = 0) (Kf : (∀ j, B j) → ℝ)
    (hKη : ∀ G : (∀ j, B j) → ℝ, (∀ b b', (∀ j, η j (b j) = η j (b' j)) → G b = G b') →
      wip β Kf G = 0)
    (hKζ : ∀ G : (∀ j, B j) → ℝ, (∀ b b', (∀ j, ζ j (b j) = ζ j (b' j)) → G b = G b') →
      wip β Kf G = 0) :
    |wip β (prodOp T *ᵥ X) Kf| ≤ c * (wNorm (prodW π) X * wNorm (prodW β) Kf) := by
  set XI : (K → Bool) → (∀ j, A j) → ℝ := fun l => wSectorProj π noSpec l *ᵥ X with hXI
  set KO : (K → Bool) → (∀ j, B j) → ℝ := fun l => wSectorProj β noSpec l *ᵥ Kf with hKO
  have hβ' : ∀ j b, 0 ≤ β j b := hβ
  -- the decomposition of `X`
  have hdec : wip β (prodOp T *ᵥ X) Kf = ∑ l, wip β (prodOp T *ᵥ XI l) Kf := by
    have hX' : X = ∑ l, XI l := by
      conv_lhs => rw [← Matrix.one_mulVec X, ← sum_sectorProj π]
      rw [Matrix.sum_mulVec]
    conv_lhs => rw [hX', Matrix.mulVec_sum]
    unfold wip
    simp only [Finset.sum_apply, mul_sum, sum_mul]
    rw [sum_comm]
  -- each sector is mapped into the same sector
  have hidem : ∀ l, wSectorProj π noSpec l *ᵥ XI l = XI l := fun l => sectorProj_idem π hπ1 l X
  have hmaps : ∀ l, wSectorProj β noSpec l *ᵥ (prodOp T *ᵥ XI l) = prodOp T *ᵥ XI l :=
    fun l => prodOp_maps_sector π β T noSpec l (fun j _ b => hrow j b) (fun j _ a => hcol j a)
      (XI l) (hidem l)
  have hmaps2 : ∀ l, wSectorProj β noSpec l *ᵥ (prodOp T2 *ᵥ XI l) = prodOp T2 *ᵥ XI l :=
    fun l => prodOp_maps_sector π β T2 noSpec l (fun j _ b => hrow2 j b) (fun j _ a => hcol2 j a)
      (XI l) (hidem l)
  have hterm : ∀ l, wip β (prodOp T *ᵥ XI l) Kf = wip β (prodOp T *ᵥ XI l) (KO l) := by
    intro l
    conv_lhs => rw [← hmaps l]
    exact wip_sectorProj β l _ Kf
  -- the bound of every sector
  have hsec : ∀ l, |wip β (prodOp T *ᵥ XI l) Kf| ≤
      c * (wNorm (prodW π) (XI l) * wNorm (prodW β) (KO l)) := by
    intro l
    by_cases hl0 : l = fun _ => false
    · -- the empty sector
      have h0 : XI l = 0 := by rw [hXI]; simp only; rw [hl0]; exact sectorProj_empty π X hX
      rw [h0, Matrix.mulVec_zero]
      simp only [wip, Pi.zero_apply, mul_zero, zero_mul, sum_const_zero, abs_zero]
      exact mul_nonneg hc (mul_nonneg (wNorm_nonneg _ _) (wNorm_nonneg _ _))
    by_cases hl1 : ∃ p, l = single p
    · -- a sector of size one: one prime
      obtain ⟨p, rfl⟩ := hl1
      rw [hterm]
      obtain ⟨g, hg⟩ := sectorProj_single_fun π p X
      obtain ⟨κ, hκ⟩ := sectorProj_single_fun β p Kf
      have hXg : XI (single p) = fun a => g (a p) := hg
      have hKk : KO (single p) = fun b => κ (b p) := hκ
      have hT1 : prodOp T *ᵥ (fun a => g (a p)) = fun b => (T p *ᵥ g) (b p) :=
        funext (prodOp_single T p (fun j _ b => hrow j b) g)
      have hpp : single p p = true := by simp [single]
      -- the one-prime reductions
      have hw : wip β (prodOp T *ᵥ XI (single p)) (KO (single p)) =
          ∑ b, β p b * (T p *ᵥ g) b * κ b := by
        rw [hXg, hKk, hT1]
        unfold wip
        have := sum_prodW_single β hβ1 p (fun b => (T p *ᵥ g) b * κ b)
        simp only [mul_assoc] at this ⊢
        exact this
      have hnX : wNorm (prodW π) (XI (single p)) = Real.sqrt (∑ a, π p a * g a ^ 2) := by
        rw [hXg]; unfold wNorm
        rw [sum_prodW_single π hπ1 p (fun t => g t ^ 2)]
      have hnK : wNorm (prodW β) (KO (single p)) = Real.sqrt (∑ b, β p b * κ b ^ 2) := by
        rw [hKk]; unfold wNorm
        rw [sum_prodW_single β hβ1 p (fun t => κ t ^ 2)]
      have hg0 : ∑ a, π p a * g a = 0 := by
        rw [← sum_prodW_single π hπ1 p g]
        have := sectorProj_mean π hπ1 hpp X
        rw [show (wSectorProj π noSpec (single p) *ᵥ X) = XI (single p) from rfl, hXg] at this
        exact this
      -- the orthogonality of `κ` to the functions of one coordinate of the pair
      have horthC : ∀ (θ : B p → C p),
          (∀ h : C p → ℝ, wip β Kf (fun b => h (θ (b p))) = 0) →
          ∀ h : C p → ℝ, ∑ b, β p b * κ b * h (θ b) = 0 := by
        intro θ hK h
        have e1 : ∑ b, β p b * κ b * h (θ b) =
            wip β (KO (single p)) (fun b => h (θ (b p))) := by
          rw [hKk]; unfold wip
          have := sum_prodW_single β hβ1 p (fun b => κ b * h (θ b))
          simp only [mul_assoc] at this ⊢
          exact this.symm
        rw [e1, show KO (single p) = wSectorProj β noSpec (single p) *ᵥ Kf from rfl,
          wip_sectorProj, sectorProj_single_coord β hβ1 p (fun t => h (θ t))]
        have e2 : wip β Kf (fun b => h (θ (b p)) - ∑ t, β p t * h (θ t)) =
            wip β Kf (fun b => h (θ (b p))) -
              (∑ t, β p t * h (θ t)) * wip β Kf (fun _ => 1) := by
          unfold wip
          rw [mul_sum, ← sum_sub_distrib]
          exact sum_congr rfl fun b _ => by ring
        rw [e2, hK h, hK (fun _ => 1)]
        ring
      have horthD : ∀ (θ : B p → D p),
          (∀ h : D p → ℝ, wip β Kf (fun b => h (θ (b p))) = 0) →
          ∀ h : D p → ℝ, ∑ b, β p b * κ b * h (θ b) = 0 := by
        intro θ hK h
        have e1 : ∑ b, β p b * κ b * h (θ b) =
            wip β (KO (single p)) (fun b => h (θ (b p))) := by
          rw [hKk]; unfold wip
          have := sum_prodW_single β hβ1 p (fun b => κ b * h (θ b))
          simp only [mul_assoc] at this ⊢
          exact this.symm
        rw [e1, show KO (single p) = wSectorProj β noSpec (single p) *ᵥ Kf from rfl,
          wip_sectorProj, sectorProj_single_coord β hβ1 p (fun t => h (θ t))]
        have e2 : wip β Kf (fun b => h (θ (b p)) - ∑ t, β p t * h (θ t)) =
            wip β Kf (fun b => h (θ (b p))) -
              (∑ t, β p t * h (θ t)) * wip β Kf (fun _ => 1) := by
          unfold wip
          rw [mul_sum, ← sum_sub_distrib]
          exact sum_congr rfl fun b _ => by ring
        rw [e2, hK h, hK (fun _ => 1)]
        ring
      have hKη' : ∀ h : C p → ℝ, wip β Kf (fun b => h (η p (b p))) = 0 := by
        intro h
        refine hKη (fun b => h (η p (b p))) fun b b' hbb => ?_
        simp only [hbb p]
      have hKζ' : ∀ h : D p → ℝ, wip β Kf (fun b => h (ζ p (b p))) = 0 := by
        intro h
        refine hKζ (fun b => h (ζ p (b p))) fun b b' hbb => ?_
        simp only [hbb p]
      have hη : ∀ h : C p → ℝ, ∑ b, β p b * κ b * h (η p b) = 0 := horthC (η p) hKη'
      have hζ : ∀ h : D p → ℝ, ∑ b, β p b * κ b * h (ζ p b) = 0 := horthD (ζ p) hKζ'
      rw [hw, hnX, hnK]
      exact hprime p g κ hg0 hη hζ
    · -- a sector of size at least two: the telescoping bound
      set S := univ.filter (fun k => l k = true) with hS
      have hS2 : 2 ≤ S.card := by
        have hne : S.card ≠ 0 := by
          intro h0
          apply hl0
          funext j
          have : j ∉ S := by rw [Finset.card_eq_zero] at h0; rw [h0]; exact Finset.notMem_empty j
          simpa [hS] using this
        have hn1 : S.card ≠ 1 := by
          intro h1
          obtain ⟨p, hp⟩ := Finset.card_eq_one.mp h1
          apply hl1
          refine ⟨p, funext fun j => ?_⟩
          have hj : l j = true ↔ j = p := by
            have := congrArg (fun t => j ∈ t) hp
            simpa [hS] using this
          cases hlj : l j
          · have : ¬ j = p := fun h => by rw [← hj] at h; rw [hlj] at h; exact absurd h (by simp)
            simp [single, this]
          · simp [single, hj.mp hlj]
        omega
      -- the tensor of the `T₂_j` maps into the functions of `x₂`
      have hT2z : wip β (prodOp T2 *ᵥ XI l) Kf = 0 := by
        rw [wip_comm]
        refine hKζ _ fun b b' hbb => ?_
        simp only [mulVec, dotProduct, prodOp]
        refine sum_congr rfl fun a _ => ?_
        congr 1
        exact prod_congr rfl fun j _ => hT2ζ j _ _ (hbb j) (a j)
      have hdiff : wip β (prodOp T *ᵥ XI l) Kf =
          wip β ((prodOp T - prodOp T2) *ᵥ XI l) (KO l) := by
        have e1 : wip β (prodOp T *ᵥ XI l) Kf = wip β ((prodOp T - prodOp T2) *ᵥ XI l) Kf := by
          have : wip β ((prodOp T - prodOp T2) *ᵥ XI l) Kf =
              wip β (prodOp T *ᵥ XI l) Kf - wip β (prodOp T2 *ᵥ XI l) Kf := by
            unfold wip
            rw [← sum_sub_distrib]
            refine sum_congr rfl fun b _ => ?_
            rw [sub_mulVec, Pi.sub_apply]
            ring
          rw [this, hT2z, sub_zero]
        have e2 : (prodOp T - prodOp T2) *ᵥ XI l =
            wSectorProj β noSpec l *ᵥ ((prodOp T - prodOp T2) *ᵥ XI l) := by
          rw [sub_mulVec, mulVec_sub, hmaps l, hmaps2 l]
        rw [e1]
        conv_lhs => rw [e2]
        exact wip_sectorProj β l _ Kf
      -- the telescoping bound of `lem:sector`(b)
      have htel := difference_telescoping π β T2 T noSpec l hπ hπ1 hβ
        (fun j _ b _ => hrow2 j b) (fun j _ b _ => hrow j b) (fun j _ a => hcol2 j a)
        (fun j hj => by simp [noSpec] at hj) (fun _ => 0) (fun _ => ρa) (fun _ => ρb)
        (fun _ => le_rfl) (fun _ => hρa) (fun _ => hρb) (fun j hj => by simp [noSpec] at hj)
        (fun j _ f hf => ⟨hT2a j f hf, hTa j f hf⟩) (fun j _ f hf => hTd j f hf) (XI l) (hidem l)
      have hprod : ∀ k, l k = true →
          ∏ j : {j // j ≠ k}, diffWeight noSpec l (fun _ => (0 : ℝ)) (fun _ => ρa) j =
            ρa ^ (S.card - 1) := by
        intro k hk
        have hdw : ∀ j, diffWeight noSpec l (fun _ => (0 : ℝ)) (fun _ => ρa) j =
            if l j = true then ρa else 1 := by
          intro j; simp [diffWeight, noSpec]
        rw [← Finset.prod_subtype (univ.erase k) (fun j => by simp)
          (fun j => diffWeight noSpec l (fun _ => (0 : ℝ)) (fun _ => ρa) j)]
        simp only [hdw]
        rw [Finset.prod_ite, prod_const, prod_const_one, mul_one, Finset.filter_erase,
          Finset.card_erase_of_mem (by simp [hk])]
      have hcoef : (∑ k ∈ univ.filter (fun k => noSpec k = false ∧ l k = true),
          ρb * ∏ j : {j // j ≠ k}, diffWeight noSpec l (fun _ => (0 : ℝ)) (fun _ => ρa) j) ≤ c := by
        have hfil : univ.filter (fun k => noSpec k = false ∧ l k = true) = S := by
          rw [hS]; congr 1; funext k; simp [noSpec]
        rw [hfil, sum_congr rfl fun k hk => by rw [hprod k (by simpa [hS] using hk)], sum_const,
          nsmul_eq_mul]
        calc (S.card : ℝ) * (ρb * ρa ^ (S.card - 1)) = ρb * ((S.card : ℝ) * ρa ^ (S.card - 1)) := by
              ring
          _ ≤ ρb * (2 * ρa) := mul_le_mul_of_nonneg_left (nat_mul_pow_le hρa hρa2 _ hS2) hρb
          _ ≤ c := by linarith
      rw [hdiff]
      have hπP : ∀ j a, 0 ≤ π j a := hπ
      calc |wip β ((prodOp T - prodOp T2) *ᵥ XI l) (KO l)|
          ≤ wNorm (prodW β) ((prodOp T - prodOp T2) *ᵥ XI l) * wNorm (prodW β) (KO l) :=
            abs_wip_le β hβ _ _
        _ ≤ (c * wNorm (prodW π) (XI l)) * wNorm (prodW β) (KO l) := by
            apply mul_le_mul_of_nonneg_right _ (wNorm_nonneg _ _)
            exact htel.trans (mul_le_mul_of_nonneg_right hcoef (wNorm_nonneg _ _))
        _ = c * (wNorm (prodW π) (XI l) * wNorm (prodW β) (KO l)) := by ring
  -- Cauchy–Schwarz over the sectors and Parseval
  have hparπ := general_parseval π noSpec hπ hπ1 X
  have hparβ := general_parseval β noSpec hβ hβ1 Kf
  rw [hdec]
  calc |∑ l, wip β (prodOp T *ᵥ XI l) Kf|
      ≤ ∑ l, |wip β (prodOp T *ᵥ XI l) Kf| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ l, c * (wNorm (prodW π) (XI l) * wNorm (prodW β) (KO l)) := sum_le_sum fun l _ => hsec l
    _ = c * ∑ l, wNorm (prodW π) (XI l) * wNorm (prodW β) (KO l) := by rw [mul_sum]
    _ ≤ c * (Real.sqrt (∑ l, wNorm (prodW π) (XI l) ^ 2) *
          Real.sqrt (∑ l, wNorm (prodW β) (KO l) ^ 2)) := by
        apply mul_le_mul_of_nonneg_left _ hc
        have h := sum_mul_sq_le_sq_mul_sq univ (fun l => wNorm (prodW π) (XI l))
          (fun l => wNorm (prodW β) (KO l))
        rw [← Real.sqrt_mul (sum_nonneg fun l _ => sq_nonneg _)]
        exact (le_abs_self _).trans (Real.abs_le_sqrt h)
    _ = c * (wNorm (prodW π) X * wNorm (prodW β) Kf) := by
        have hπP : ∀ a, 0 ≤ prodW π a := fun a => prod_nonneg fun j _ => hπ j (a j)
        have hβP : ∀ b, 0 ≤ prodW β b := fun b => prod_nonneg fun j _ => hβ j (b j)
        simp only [wNorm_sq hπP, wNorm_sq hβP]
        rw [← hparπ, ← hparβ]
        rfl

end Block03

end Sarkozy.OpsFeature
