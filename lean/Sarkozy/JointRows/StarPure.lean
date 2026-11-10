module

public import Sarkozy.JointRows.StarOpsBounds

/-!
# The pure part of the star matrix: `T_pure = κ r 𝓕_X M(Φ̂) 𝓕_Y^*` (`prop:conditional-star`(b))

Source: `paper/sections/16_extraction.tex`, proof of `prop:conditional-star`, Step 2.

For product laws `ν_X = ⊗ν_i` on `𝔽_p^X` and `ν_Y = ⊗ν'_j` on `𝔽_p^Y`, `bform νp νq K f g` is the
bilinear form `E_{x∼ν_X, y∼ν_Y} f(x) K(x, y) g(y)` of a kernel relative to `ν_X ⊗ ν_Y`.
* `pair_form`: a single pair, `E f(x) χ(y_j - x_i) g(y) = r ⟨U_i^* f, Φ̂ U'^*_j g⟩`
  (`r = p^{-1/2}`, `Φ̂ = PaleyGauss.paley`);
* `rowStar_form`: the all-`φ` term of a row star, `E f(x) ∏_{j∈T} φ_{ν'_j}(x_i, y_j) g(y) =
  ⟨U_i^* f, W'^*_T g⟩`;
* `colStar_form`: the all-`φ` term of a column star, `E f(x) ∏_{i∈S} φ_{ν_i}(y_j, x_i) g(y) =
  ⟨W_S^* f, U'^*_j g⟩`;
* `pureKernel`: the pure kernel `∑ D_{ij} χ(y_j - x_i) + ∑ A_{iT} ∏_{j∈T} φ + ∑ B_{jS} ∏_{i∈S} φ`;
* `featU`, `featW`: the feature vector `𝓕_X^* f = ((U_i^* f/√κ)_i, (P_ℋ W_S^* f/(√κ r))_S)`;
* `mForm`: the form `⟨u, M(Φ̂) v⟩` of the block matrix `M(Φ̂)` (singleton block `D ⊗ Φ̂`, blocks
  `A ⊗ I` and `B^* ⊗ I`, zero between sets);
* **`pure_block_identity`**: for mean-zero `f`, `g` and `κ > 0`,
  `bform (pureKernel) f g = κ r ⟨𝓕_X^* f, M(Φ̂) 𝓕_Y^* g⟩`, i.e. `T_pure = κ r 𝓕_X M(Φ̂) 𝓕_Y^*`
  ("as one checks block by block").
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.JointRows.StarOps

open Sarkozy.FiveType Sarkozy.FiveType.Blocks Sarkozy.JointRows.PaleyGauss

variable {p : ℕ} [Fact p.Prime]
variable {X Y : Type*} [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]

/-- The bilinear form `E_{x∼ν_X, y∼ν_Y} f(x) K(x, y) g(y)`. -/
noncomputable def bform (νp : X → FiniteLaw (ZMod p)) (νq : Y → FiniteLaw (ZMod p))
    (K : (X → ZMod p) → (Y → ZMod p) → ℝ) (f : (X → ZMod p) → ℝ) (g : (Y → ZMod p) → ℝ) : ℝ :=
  (blockLaw νp).expect (fun x => (blockLaw νq).expect (fun y => f x * K x y * g y))

theorem expect_finset_sum {α ι : Type*} [Fintype α] (μ : FiniteLaw α) (s : Finset ι)
    (F : α → ι → ℝ) : μ.expect (fun z => ∑ k ∈ s, F z k) = ∑ k ∈ s, μ.expect (fun z => F z k) := by
  simp only [FiniteLaw.expect, Finset.mul_sum]
  exact Finset.sum_comm

/-- `Φ̂` is linear: `Φ̂(c h) = c Φ̂h`. -/
theorem paley_const_mul (c : ℝ) (h : ZMod p → ℝ) (a : ZMod p) :
    paley p (fun b => c * h b) a = c * paley p h a := by
  unfold paley
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => by ring

/-- `E_a U_i^* f(a) = E_{ν_X} f`. -/
theorem expect_uStar (νp : X → FiniteLaw (ZMod p)) (i : X) (f : (X → ZMod p) → ℝ) :
    (FiniteLaw.uniform (ZMod p)).expect (uStar νp i f) = (blockLaw νp).expect f := by
  have h := expect_eval_mul νp i (fun _ => 1) f
  simp only [one_mul] at h
  exact h.symm

/-- **A single pair**: `E f(x) χ(y_j - x_i) g(y) = r ⟨U_i^* f, Φ̂ U'^*_j g⟩`. -/
theorem pair_form (νp : X → FiniteLaw (ZMod p)) (νq : Y → FiniteLaw (ZMod p)) (i : X) (j : Y)
    (f : (X → ZMod p) → ℝ) (g : (Y → ZMod p) → ℝ) :
    bform νp νq (fun x y => chiR p (y j - x i)) f g =
      (Real.sqrt p)⁻¹ * (FiniteLaw.uniform (ZMod p)).expect
        (fun a => paley p (uStar νq j g) a * uStar νp i f a) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hin : ∀ x : X → ZMod p, (blockLaw νq).expect (fun y => f x * chiR p (y j - x i) * g y) =
      ((Real.sqrt p)⁻¹ * paley p (uStar νq j g) (x i)) * f x := by
    intro x
    rw [show (fun y => f x * chiR p (y j - x i) * g y) =
        fun y => f x * (chiR p (y j - x i) * g y) from funext fun y => by ring,
      FiniteLaw.expect_const_mul, expect_eval_mul νq j (fun b => chiR p (b - x i)) g,
      FiniteLaw.expect_uniform, ZMod.card, sum_chi_eq_paley]
    set s := Real.sqrt p with hsdef
    have hs : s * s = p := Real.mul_self_sqrt hp0.le
    have hs0 : s ≠ 0 := by rw [hsdef]; positivity
    rw [← hs]
    field_simp
  unfold bform
  calc (blockLaw νp).expect (fun x =>
        (blockLaw νq).expect (fun y => f x * chiR p (y j - x i) * g y))
      = (blockLaw νp).expect (fun x =>
          (fun a => (Real.sqrt p)⁻¹ * paley p (uStar νq j g) a) (x i) * f x) :=
        FiniteLaw.expect_congr _ hin
    _ = (FiniteLaw.uniform (ZMod p)).expect (fun a =>
          (fun a => (Real.sqrt p)⁻¹ * paley p (uStar νq j g) a) a * uStar νp i f a) :=
        expect_eval_mul νp i (fun a => (Real.sqrt p)⁻¹ * paley p (uStar νq j g) a) f
    _ = _ := by
        rw [← FiniteLaw.expect_const_mul]
        exact FiniteLaw.expect_congr _ fun a => by ring

/-- **The all-`φ` term of a row star**: `E f(x) ∏_{j∈T} φ_{ν'_j}(x_i, y_j) g(y) =
⟨U_i^* f, W'^*_T g⟩`. -/
theorem rowStar_form (νp : X → FiniteLaw (ZMod p)) (νq : Y → FiniteLaw (ZMod p)) (i : X)
    (T : Finset Y) (f : (X → ZMod p) → ℝ) (g : (Y → ZMod p) → ℝ) :
    bform νp νq (fun x y => ∏ j ∈ T, phi (νq j) (x i) (y j)) f g =
      (FiniteLaw.uniform (ZMod p)).expect (fun a => wStar νq T g a * uStar νp i f a) := by
  have hin : ∀ x : X → ZMod p,
      (blockLaw νq).expect (fun y => f x * (∏ j ∈ T, phi (νq j) (x i) (y j)) * g y) =
        wStar νq T g (x i) * f x := by
    intro x
    unfold wStar
    rw [← FiniteLaw.expect_mul_const]
    exact FiniteLaw.expect_congr _ fun y => by ring
  unfold bform
  calc _ = (blockLaw νp).expect (fun x => wStar νq T g (x i) * f x) :=
        FiniteLaw.expect_congr _ hin
    _ = _ := expect_eval_mul νp i (wStar νq T g) f

/-- **The all-`φ` term of a column star**: `E f(x) ∏_{i∈S} φ_{ν_i}(y_j, x_i) g(y) =
⟨W_S^* f, U'^*_j g⟩`. -/
theorem colStar_form (νp : X → FiniteLaw (ZMod p)) (νq : Y → FiniteLaw (ZMod p)) (j : Y)
    (S : Finset X) (f : (X → ZMod p) → ℝ) (g : (Y → ZMod p) → ℝ) :
    bform νp νq (fun x y => ∏ i ∈ S, phi (νp i) (y j) (x i)) f g =
      (FiniteLaw.uniform (ZMod p)).expect (fun b => wStar νp S f b * uStar νq j g b) := by
  have hin : ∀ y : Y → ZMod p,
      (blockLaw νp).expect (fun x => f x * (∏ i ∈ S, phi (νp i) (y j) (x i)) * g y) =
        wStar νp S f (y j) * g y := by
    intro y
    unfold wStar
    rw [← FiniteLaw.expect_mul_const]
  unfold bform
  rw [expect_swap]
  calc _ = (blockLaw νq).expect (fun y => wStar νp S f (y j) * g y) :=
        FiniteLaw.expect_congr _ hin
    _ = _ := expect_eval_mul νq j (wStar νp S f) g

/-- **The pure part of the star kernel** (Step 2): the single pairs `D_{ij} χ(y_j - x_i)`, and the
all-`φ` terms `A_{iT} ∏_{j∈T} φ_{ν'_j}(x_i, y_j)` of the row stars (`T ∈ 𝒯`) and
`B_{jS} ∏_{i∈S} φ_{ν_i}(y_j, x_i)` of the column stars (`S ∈ 𝒮`). -/
noncomputable def pureKernel (νp : X → FiniteLaw (ZMod p)) (νq : Y → FiniteLaw (ZMod p))
    (D : X → Y → ℝ) (𝒯 : Finset (Finset Y)) (A : X → Finset Y → ℝ) (𝒮 : Finset (Finset X))
    (B : Y → Finset X → ℝ) (x : X → ZMod p) (y : Y → ZMod p) : ℝ :=
  (∑ i, ∑ j, D i j * chiR p (y j - x i)) +
    (∑ i, ∑ T ∈ 𝒯, A i T * ∏ j ∈ T, phi (νq j) (x i) (y j)) +
    ∑ j, ∑ S ∈ 𝒮, B j S * ∏ i ∈ S, phi (νp i) (y j) (x i)

/-- The singleton features `U_i^* f/√κ`. -/
noncomputable def featU {Z : Type*} [Fintype Z] [DecidableEq Z] (νp : Z → FiniteLaw (ZMod p))
    (κ : ℝ) (f : (Z → ZMod p) → ℝ) (i : Z) (a : ZMod p) : ℝ :=
  (Real.sqrt κ)⁻¹ * uStar νp i f a

/-- The set features `P_ℋ W_S^* f/(√κ r)`, `r = p^{-1/2}`. -/
noncomputable def featW {Z : Type*} [Fintype Z] [DecidableEq Z] (νp : Z → FiniteLaw (ZMod p))
    (κ : ℝ) (f : (Z → ZMod p) → ℝ) (S : Finset Z) (t : ZMod p) : ℝ :=
  (Real.sqrt κ * (Real.sqrt p)⁻¹)⁻¹ * cen (FiniteLaw.uniform (ZMod p)) (wStar νp S f) t

/-- **The form of `M(Φ̂)`**: rows `X` and the sets `S ∈ 𝒮`, columns `Y` and the sets `T ∈ 𝒯`;
the singleton block `D ⊗ Φ̂`, the blocks `A ⊗ I` (rows `i`, columns `T`) and `B^* ⊗ I` (rows `S`,
columns `j`), and zero between sets. -/
noncomputable def mForm (D : X → Y → ℝ) (𝒯 : Finset (Finset Y)) (A : X → Finset Y → ℝ)
    (𝒮 : Finset (Finset X)) (B : Y → Finset X → ℝ) (u : X → ZMod p → ℝ)
    (uS : Finset X → ZMod p → ℝ) (v : Y → ZMod p → ℝ) (vT : Finset Y → ZMod p → ℝ) : ℝ :=
  (∑ i, ∑ j, D i j * ip (FiniteLaw.uniform (ZMod p)) (u i) (paley p (v j))) +
    (∑ i, ∑ T ∈ 𝒯, A i T * ip (FiniteLaw.uniform (ZMod p)) (u i) (vT T)) +
    ∑ j, ∑ S ∈ 𝒮, B j S * ip (FiniteLaw.uniform (ZMod p)) (uS S) (v j)

/-- **`T_pure = κ r 𝓕_X M(Φ̂) 𝓕_Y^*`** (Step 2), as bilinear forms on mean-zero functions:
`E f(x) K_pure(x, y) g(y) = κ r ⟨𝓕_X^* f, M(Φ̂) 𝓕_Y^* g⟩` for `κ > 0`, `r = p^{-1/2}`. -/
theorem pure_block_identity (νp : X → FiniteLaw (ZMod p)) (νq : Y → FiniteLaw (ZMod p))
    (D : X → Y → ℝ) (𝒯 : Finset (Finset Y)) (A : X → Finset Y → ℝ) (𝒮 : Finset (Finset X))
    (B : Y → Finset X → ℝ) {κ : ℝ} (hκ : 0 < κ) (f : (X → ZMod p) → ℝ) (g : (Y → ZMod p) → ℝ)
    (hf : (blockLaw νp).expect f = 0) (hg : (blockLaw νq).expect g = 0) :
    bform νp νq (pureKernel νp νq D 𝒯 A 𝒮 B) f g =
      κ * (Real.sqrt p)⁻¹ * mForm D 𝒯 A 𝒮 B (featU νp κ f) (featW νp κ f) (featU νq κ g)
        (featW νq κ g) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  -- the bilinear form of the pure kernel, term by term
  have h1 : ∀ x y, f x * pureKernel νp νq D 𝒯 A 𝒮 B x y * g y =
      (∑ i, ∑ j, D i j * (f x * chiR p (y j - x i) * g y)) +
      (∑ i, ∑ T ∈ 𝒯, A i T * (f x * (∏ j ∈ T, phi (νq j) (x i) (y j)) * g y)) +
      ∑ j, ∑ S ∈ 𝒮, B j S * (f x * (∏ i ∈ S, phi (νp i) (y j) (x i)) * g y) := by
    intro x y
    unfold pureKernel
    simp only [mul_add, add_mul, Finset.mul_sum, Finset.sum_mul]
    congr 1
    · congr 1
      · exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
      · exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun T _ => by ring
    · exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun S _ => by ring
  have hpair := fun (i : X) (j : Y) => pair_form νp νq i j f g
  have hrow := fun (i : X) (T : Finset Y) => rowStar_form νp νq i T f g
  have hcol := fun (j : Y) (S : Finset X) => colStar_form νp νq j S f g
  simp only [bform] at hpair hrow hcol
  unfold bform
  simp only [h1, FiniteLaw.expect_add, expect_finset_sum, FiniteLaw.expect_const_mul, hpair, hrow,
    hcol]
  -- the right-hand side
  have hU : ∀ (i : X) (j : Y), ip (FiniteLaw.uniform (ZMod p)) (featU νp κ f i)
      (paley p (featU νq κ g j)) = κ⁻¹ * (FiniteLaw.uniform (ZMod p)).expect
        (fun a => paley p (uStar νq j g) a * uStar νp i f a) := by
    intro i j
    unfold ip featU
    simp only [paley_const_mul]
    rw [← FiniteLaw.expect_const_mul]
    refine FiniteLaw.expect_congr _ fun a => ?_
    have hk : (Real.sqrt κ)⁻¹ * (Real.sqrt κ)⁻¹ = κ⁻¹ := by
      rw [← mul_inv, Real.mul_self_sqrt hκ.le]
    linear_combination (paley p (uStar νq j g) a * uStar νp i f a) * hk
  have hcen : ∀ (u w : ZMod p → ℝ), (FiniteLaw.uniform (ZMod p)).expect u = 0 →
      ip (FiniteLaw.uniform (ZMod p)) u (cen (FiniteLaw.uniform (ZMod p)) w) =
        (FiniteLaw.uniform (ZMod p)).expect (fun a => u a * w a) := by
    intro u w hu
    unfold ip cen
    rw [show (fun a => u a * (w a - (FiniteLaw.uniform (ZMod p)).expect w)) =
        fun a => u a * w a - (FiniteLaw.uniform (ZMod p)).expect w * u a from
        funext fun a => by ring, FiniteLaw.expect_sub, FiniteLaw.expect_const_mul, hu, mul_zero,
      sub_zero]
  have hκr : (Real.sqrt κ)⁻¹ * (Real.sqrt κ * (Real.sqrt p)⁻¹)⁻¹ = κ⁻¹ * Real.sqrt p := by
    rw [mul_inv, inv_inv, ← mul_assoc, ← mul_inv, Real.mul_self_sqrt hκ.le]
  have hW : ∀ (i : X) (T : Finset Y), ip (FiniteLaw.uniform (ZMod p)) (featU νp κ f i)
      (featW νq κ g T) = κ⁻¹ * Real.sqrt p * (FiniteLaw.uniform (ZMod p)).expect
        (fun a => wStar νq T g a * uStar νp i f a) := by
    intro i T
    have hu : (FiniteLaw.uniform (ZMod p)).expect (fun a => uStar νp i f a) = 0 := by
      rw [show (fun a => uStar νp i f a) = uStar νp i f from rfl, expect_uStar, hf]
    unfold featU featW
    rw [show (fun t => (Real.sqrt κ * (Real.sqrt p)⁻¹)⁻¹ *
        cen (FiniteLaw.uniform (ZMod p)) (wStar νq T g) t) =
        cen (FiniteLaw.uniform (ZMod p))
          (fun t => (Real.sqrt κ * (Real.sqrt p)⁻¹)⁻¹ * wStar νq T g t) from by
      funext t; unfold cen; rw [FiniteLaw.expect_const_mul]; ring]
    rw [show (fun a => (Real.sqrt κ)⁻¹ * uStar νp i f a) =
        fun a => (Real.sqrt κ)⁻¹ * uStar νp i f a from rfl]
    rw [hcen _ _ (by rw [FiniteLaw.expect_const_mul, hu, mul_zero]), ← hκr,
      ← FiniteLaw.expect_const_mul]
    exact FiniteLaw.expect_congr _ fun a => by ring
  have hcen' : ∀ (u w : ZMod p → ℝ), (FiniteLaw.uniform (ZMod p)).expect u = 0 →
      ip (FiniteLaw.uniform (ZMod p)) (cen (FiniteLaw.uniform (ZMod p)) w) u =
        (FiniteLaw.uniform (ZMod p)).expect (fun a => w a * u a) := by
    intro u w hu
    unfold ip cen
    rw [show (fun a => (w a - (FiniteLaw.uniform (ZMod p)).expect w) * u a) =
        fun a => w a * u a - (FiniteLaw.uniform (ZMod p)).expect w * u a from
        funext fun a => by ring, FiniteLaw.expect_sub, FiniteLaw.expect_const_mul, hu, mul_zero,
      sub_zero]
  have hW' : ∀ (j : Y) (S : Finset X), ip (FiniteLaw.uniform (ZMod p)) (featW νp κ f S)
      (featU νq κ g j) = κ⁻¹ * Real.sqrt p * (FiniteLaw.uniform (ZMod p)).expect
        (fun b => wStar νp S f b * uStar νq j g b) := by
    intro j S
    have hu0 := expect_uStar νq j g
    rw [hg] at hu0
    have hu : (FiniteLaw.uniform (ZMod p)).expect
        (fun a => (Real.sqrt κ)⁻¹ * uStar νq j g a) = 0 := by
      rw [FiniteLaw.expect_const_mul, hu0, mul_zero]
    have hfw : featW νp κ f S = cen (FiniteLaw.uniform (ZMod p))
        (fun t => (Real.sqrt κ * (Real.sqrt p)⁻¹)⁻¹ * wStar νp S f t) := by
      funext t; unfold featW cen; rw [FiniteLaw.expect_const_mul]; ring
    have hfu : featU νq κ g j = fun a => (Real.sqrt κ)⁻¹ * uStar νq j g a := rfl
    rw [hfw, hfu, hcen' _ _ hu, ← hκr, ← FiniteLaw.expect_const_mul]
    exact FiniteLaw.expect_congr _ fun a => by ring
  unfold mForm
  simp only [hU, hW, hW']
  have hsp : Real.sqrt p ≠ 0 := by positivity
  have hκ0 : κ ≠ 0 := hκ.ne'
  simp only [Finset.mul_sum, mul_add]
  congr 1
  · congr 1
    · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      field_simp
    · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun T _ => ?_
      field_simp
  · refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun S _ => ?_
    field_simp

end Sarkozy.JointRows.StarOps
