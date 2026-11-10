module

public import Sarkozy.L20Cap.Rectangle
public import Sarkozy.Spectral.GlueSupport
public import Sarkozy.Spectral.Blocks

/-!
# The L20 cut operator and its caps (`prop:l20-rectangular`(d), `prop:l20-collisions`(b))

`paper/sections/20_middle_reference.tex`, `prop:l20-rectangular`(d) (last display),
`prop:l20-collisions`(b) ("The caps"), with `lem:spec:tensorcomp`(b) for the blocks.
Notation of `Sarkozy.L20Cap.Rectangle`.

**The cut kernel.** Two halves `x = (C, b)`, `x' = (C', b')` are *disjoint* (`Disj`) if they
have no common label. With the soft kernel `K_soft(x, x') = 𝖱(C; b') 𝖱(C'; b)`
(`softKernel_swap`):
* `K0 = K_soft 𝟙_{Disj}` is the unnormalized cut kernel `K₀` of `lem:spec:expansion` (on
  disjoint halves the factor `(1 + D_ij χ(x'_j - x_i))/2 ∈ {0, 1}` is the indicator of the
  cross edge `ij`, so `2^{-16} K0` is the indicator of the twelve-label labellings of
  `G_{L,2}` with halves `x`, `x'`);
* `collK = K_soft 𝟙_{¬Disj}` is the collision part `T_coll`, so `K₀ = K_soft - T_coll`
  (`K0_eq`);
* `Z0 = ⟨𝟙, K₀ 𝟙⟩` and `cutT = K₀/Z₀`, the L20 cut operator `T = 𝖠_p` on `L²(μ_p)`.

Proved:
* **`cutT_lower`** (`prop:l20-rectangular`(d), `T ⪰ -C' I`): from `‖𝖱_c‖ ≤ c_R`,
  `‖𝔯‖ ≤ s`, `c_R ≤ s`, `‖T_coll‖ ≤ D_col` and `Z₀ ≥ 1 - ε_Z > 0`,
  `T ⪰ -((s c_R/h_p + D_col)/(1 - ε_Z)) I`. With `c_R = c_gap` (`prop:l20-pair-gap`) and
  `D_col = D_bal` (`prop:l20-collisions`(a)) this is `T ⪰ -C₂₀ I`, the lower cap of
  `prop:l20-collisions`(b) at the prime.
* **`block_cap`** (`prop:l20-collisions`(b), last display): if every prime `p` of a block has
  `-g p^{-1/2} ⪯ T_p ⪯ 1 + c⁺/p` with `g p^{-1/2} < 1`, all `p ≥ b ≥ P > 1` and
  `∑ log p ≤ L`, then `⊗_p T_p ⪰ -g exp(c⁺L/(P log P)) b^{-1/2}`.

Hypotheses (named inputs of the paper, not proved here): `‖𝖱_c‖ ≤ c_R` (`prop:l20-pair-gap`,
see `Sarkozy.L20Cap.Gap`), `‖𝔯‖ ≤ s_p` (`prop:l20-rectangular`(d)), `‖T_coll‖ ≤ D_bal`
(`prop:l20-collisions`(a), from `cor:incident-weights`), `Z₀ ≥ 1 - ε_Z` (`lem:l20-star-mean`
with the nonstar and collision caps); for the block, the upper cap `T_p ⪯ 1 + c⁺/p`
(`prop:l20-completion`).
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace Sarkozy.L20Cap

open Sarkozy Sarkozy.Recentering Sarkozy.Cuts

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-! ## Linearity of the kernel form in the kernel -/

section KernelLinear

variable {Ω : Type*} [Fintype Ω]

theorem kernelForm_sub_kernel (ν : FiniteLaw Ω) (K K' : Ω → Ω → ℝ) (f : Ω → ℝ) :
    kernelForm ν ν (fun x y => K x y - K' x y) f f =
      kernelForm ν ν K f f - kernelForm ν ν K' f f := by
  simp only [kernelForm, LinearMap.mk₂_apply, ← sum_sub_distrib]
  refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
  ring

theorem kernelForm_div_kernel (ν : FiniteLaw Ω) (K : Ω → Ω → ℝ) (Z : ℝ) (f : Ω → ℝ) :
    kernelForm ν ν (fun x y => K x y / Z) f f = kernelForm ν ν K f f / Z := by
  simp only [kernelForm, LinearMap.mk₂_apply, sum_div]
  refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
  ring

end KernelLinear

/-! ## The cut kernel -/

/-- The labels of a half `x = (C, b)`, in the order `a₀, a₁, b₀, b₁, c₀, c₁`. -/
def labels (x : CoreT F × PairT F) : Fin 6 → F := emb x.1.1 x.2.1

/-- `x` and `x'` have no common label. -/
def Disj (x x' : CoreT F × PairT F) : Prop := ∀ i j : Fin 6, labels x i ≠ labels x' j

instance (x x' : CoreT F × PairT F) : Decidable (Disj x x') := by unfold Disj; infer_instance

theorem Disj_symm {x x' : CoreT F × PairT F} (h : Disj x x') : Disj x' x :=
  fun i j hij => h j i hij.symm

/-- The soft kernel on the halves, `K_soft(x, x') = 𝖱(C; b') 𝖱(C'; b)`. -/
noncomputable def Ksoft (x x' : CoreT F × PairT F) : ℝ := Rk x.1 x'.2 * Rk x'.1 x.2

/-- `K_soft` is the soft kernel `∏(1 + (D₂₀)_ij χ(x'_j - x_i))` of the labels
(`prop:l20-rectangular`(c)). -/
theorem Ksoft_eq_softKernel (hm1 : quadraticChar F (-1) = -1) (x x' : CoreT F × PairT F) :
    Ksoft x x' = softKernel (labels x) (labels x') := by
  rw [labels, labels, softKernel_swap hm1]
  rfl

/-- The unnormalized cut kernel `K₀ = K_soft 𝟙_{Disj}`. -/
noncomputable def K0 (x x' : CoreT F × PairT F) : ℝ := if Disj x x' then Ksoft x x' else 0

/-- The collision part `T_coll = K_soft 𝟙_{¬Disj}`. -/
noncomputable def collK (x x' : CoreT F × PairT F) : ℝ := if Disj x x' then 0 else Ksoft x x'

/-- **`K₀ = K_soft - T_coll`** (`eq:record:root-kernel`). -/
theorem K0_eq (x x' : CoreT F × PairT F) : K0 x x' = Ksoft x x' - collK x x' := by
  unfold K0 collK
  split_ifs <;> ring

theorem Ksoft_symm (x x' : CoreT F × PairT F) : Ksoft x x' = Ksoft x' x := by
  unfold Ksoft; ring

theorem K0_symm (x x' : CoreT F × PairT F) : K0 x x' = K0 x' x := by
  unfold K0
  by_cases h : Disj x x'
  · simp only [h, Disj_symm h, ↓reduceIte, Ksoft_symm x x']
  · have h' : ¬ Disj x' x := fun h'' => h (Disj_symm h'')
    simp only [h, h', ↓reduceIte]

variable [Nonempty (CoreT F)] [Nonempty (PairT F)]

/-- The normalizer `Z₀ = ⟨𝟙, K₀𝟙⟩_{μ_p}`. -/
noncomputable def Z0 (h6 : 6 ≤ Fintype.card F) : ℝ :=
  kernelForm (halfLaw h6) (halfLaw h6) K0 (fun _ => 1) (fun _ => 1)

/-- **The L20 cut operator** `T = K₀/Z₀` on `L²(μ_p)`. -/
noncomputable def cutT (h6 : 6 ≤ Fintype.card F) (x x' : CoreT F × PairT F) : ℝ :=
  K0 x x' / Z0 h6

omit [Nonempty (CoreT F)] [Nonempty (PairT F)] in
theorem cutT_symm' (Z : ℝ) (x x' : CoreT F × PairT F) : K0 x x' / Z = K0 x' x / Z := by
  rw [K0_symm]

/-- `⟨f, Tf⟩ = (⟨f, K_soft f⟩ - ⟨f, T_coll f⟩)/Z₀`. -/
theorem cutT_form_eq (h6 : 6 ≤ Fintype.card F) (f g : CoreT F × PairT F → ℝ) :
    kernelForm (halfLaw h6) (halfLaw h6) (cutT h6) f g =
      (kernelForm (halfLaw h6) (halfLaw h6) Ksoft f g -
        kernelForm (halfLaw h6) (halfLaw h6) collK f g) / Z0 h6 := by
  simp only [kernelForm, LinearMap.mk₂_apply, cutT, K0_eq, sum_div, ← sum_sub_distrib]
  refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
  ring

/-- **`prop:l20-rectangular`(d), `T ⪰ -C' I`**, with
`C' = (s c_R/h_p + D_col)/(1 - ε_Z)`; with `c_R = c_gap`, `D_col = D_bal` it is the lower cap
`T ⪰ -C₂₀ I` of `prop:l20-collisions`(b). -/
theorem cutT_lower (hm1 : quadraticChar F (-1) = -1) (h6 : 6 ≤ Fintype.card F)
    {cR s D εZ : ℝ} (hcR : 0 ≤ cR)
    (hRc : ∀ h : PairT F → ℝ,
      nrm (coreLaw (F := F)) (recOp (pairLaw (F := F)) Rc h) ≤ cR * nrm (pairLaw (F := F)) h)
    (hs : nrm (coreLaw (F := F)) rmass ≤ s) (hcs : cR ≤ s) (hD0 : 0 ≤ D)
    (hD : ∀ f, |kernelForm (halfLaw h6) (halfLaw h6) collK f f| ≤ D * nrm (halfLaw h6) f ^ 2)
    (hεZ : εZ < 1) (hZ : 1 - εZ ≤ Z0 h6) (f : CoreT F × PairT F → ℝ) :
    -((s * cR / prob ((coreLaw (F := F)).product (pairLaw (F := F))) Avoid + D) / (1 - εZ)) *
        nrm (halfLaw h6) f ^ 2 ≤
      kernelForm (halfLaw h6) (halfLaw h6) (cutT h6) f f := by
  set hP := prob ((coreLaw (F := F)).product (pairLaw (F := F))) Avoid with hhP
  have hP0 : 0 < hP := hP_pos h6
  have hZ0 : 0 < Z0 h6 := by linarith
  have hsoft := soft_lower hm1 h6 hcR hRc hs hcs f
  have hcoll := hD f
  rw [cutT_form_eq]
  set N := nrm (halfLaw h6) f ^ 2 with hN
  have hN0 : 0 ≤ N := sq_nonneg _
  have hs0 : 0 ≤ s := le_trans hcR hcs
  set a := s * cR / hP + D with ha
  have ha0 : 0 ≤ a := add_nonneg (div_nonneg (mul_nonneg hs0 hcR) hP0.le) hD0
  have hnum : -(a * N) ≤ kernelForm (halfLaw h6) (halfLaw h6) Ksoft f f -
      kernelForm (halfLaw h6) (halfLaw h6) collK f f := by
    have h1 : kernelForm (halfLaw h6) (halfLaw h6) collK f f ≤ D * N :=
      (le_abs_self _).trans hcoll
    have h2 : -(s * cR / hP) * N ≤ kernelForm (halfLaw h6) (halfLaw h6) Ksoft f f := hsoft
    nlinarith
  have hεpos : 0 < 1 - εZ := by linarith
  rw [le_div_iff₀ hZ0]
  have : -(a / (1 - εZ)) * N * Z0 h6 ≤ -(a * N) := by
    have h3 : a * N / (1 - εZ) * (1 - εZ) = a * N := by field_simp
    have h4 : a * N / (1 - εZ) * (1 - εZ) ≤ a * N / (1 - εZ) * Z0 h6 :=
      mul_le_mul_of_nonneg_left hZ (div_nonneg (mul_nonneg ha0 hN0) hεpos.le)
    have h5 : -(a / (1 - εZ)) * N * Z0 h6 = -(a * N / (1 - εZ) * Z0 h6) := by ring
    linarith
  linarith

/-! ## The block cap (`lem:spec:tensorcomp`(b)) -/

/-- `∏_j (1 + c/p_j) ≤ exp(c L/(P log P))` when `p_j ≥ P > 1` and `∑_j log p_j ≤ L`
(`lem:spec:tensorcomp`(c)). -/
theorem prod_one_add_le_exp {ι : Type*} [Fintype ι] (p : ι → ℝ) {c P L : ℝ} (hc : 0 ≤ c)
    (hP : 1 < P) (hpP : ∀ i, P ≤ p i) (hL : ∑ i, Real.log (p i) ≤ L) :
    ∏ i, (1 + c / p i) ≤ Real.exp (c * L / (P * Real.log P)) := by
  have hpos : ∀ i, 0 < p i := fun i => by linarith [hpP i]
  calc ∏ i, (1 + c / p i) ≤ ∏ i, Real.exp (c / p i) :=
        prod_le_prod₀ (fun i _ => by have := div_nonneg hc (hpos i).le; linarith)
          (fun i _ => by have := Real.add_one_le_exp (c / p i); linarith)
    _ = Real.exp (∑ i, c / p i) := (Real.exp_sum _ _).symm
    _ ≤ Real.exp (c * L / (P * Real.log P)) := by
        apply Real.exp_le_exp.mpr
        have h1 := Sarkozy.Spectral.sum_inv_le_of_sum_log_le p hP hpP hL
        calc ∑ i, c / p i = c * ∑ i, 1 / p i := by
              rw [mul_sum]; exact sum_congr rfl fun i _ => by ring
          _ ≤ c * (L / (P * Real.log P)) := mul_le_mul_of_nonneg_left h1 hc
          _ = c * L / (P * Real.log P) := by ring

/-- **The L20 block cap** (`prop:l20-collisions`(b), last display; `lem:spec:tensorcomp`(b)):
on a block of primes (one field `Fi i` per prime), if every cut operator satisfies
`-g p^{-1/2} ⪯ T_p ⪯ 1 + c⁺/p` with `g p^{-1/2} < 1`, every `p ≥ b ≥ P > 1` and
`∑ log p ≤ L`, then the tensor product `T_𝔅 = ⊗_p T_p` (the cut operator of the block law)
satisfies `T_𝔅 ⪰ -g exp(c⁺ L/(P log P)) b^{-1/2}`. -/
theorem block_cap {ι : Type*} [Fintype ι] [DecidableEq ι] (Fi : ι → Type*) [∀ i, Field (Fi i)]
    [∀ i, Fintype (Fi i)] [∀ i, DecidableEq (Fi i)] [∀ i, Nonempty (CoreT (Fi i))]
    [∀ i, Nonempty (PairT (Fi i))] (h6 : ∀ i, 6 ≤ Fintype.card (Fi i)) {g cplus b P L : ℝ}
    (hg : 0 ≤ g) (hcplus : 0 ≤ cplus) (hP : 1 < P) (hPb : P ≤ b)
    (hbp : ∀ i, b ≤ Fintype.card (Fi i))
    (hL : ∑ i, Real.log (Fintype.card (Fi i)) ≤ L)
    (hgp : ∀ i, g * (√(Fintype.card (Fi i) : ℝ))⁻¹ < 1)
    (hlow : ∀ i (f : CoreT (Fi i) × PairT (Fi i) → ℝ),
      -(g * (√(Fintype.card (Fi i) : ℝ))⁻¹) * nrm (halfLaw (h6 i)) f ^ 2 ≤
        kernelForm (halfLaw (h6 i)) (halfLaw (h6 i)) (cutT (h6 i)) f f)
    (hup : ∀ i (f : CoreT (Fi i) × PairT (Fi i) → ℝ),
      kernelForm (halfLaw (h6 i)) (halfLaw (h6 i)) (cutT (h6 i)) f f ≤
        (1 + cplus / Fintype.card (Fi i)) * nrm (halfLaw (h6 i)) f ^ 2)
    (Fn : (∀ i, CoreT (Fi i) × PairT (Fi i)) → ℝ) :
    -(g * Real.exp (cplus * L / (P * Real.log P)) * (√b)⁻¹) *
        nrm (FiniteLaw.pi fun i => halfLaw (h6 i)) Fn ^ 2 ≤
      kernelForm (FiniteLaw.pi fun i => halfLaw (h6 i)) (FiniteLaw.pi fun i => halfLaw (h6 i))
        (fun x y => ∏ i, cutT (h6 i) (x i) (y i)) Fn Fn := by
  have hb : 0 < b := by linarith
  have h := Sarkozy.Spectral.tensorcomp_block_supp (fun i => halfLaw (h6 i))
    (fun i => cutT (h6 i)) (fun i x y => cutT_symm' _ x y) (fun i => (Fintype.card (Fi i) : ℝ))
    hg hcplus hb hbp hgp hlow hup Fn
  have hprod := prod_one_add_le_exp (fun i => (Fintype.card (Fi i) : ℝ)) hcplus hP
    (fun i => hPb.trans (hbp i)) hL
  have hN : 0 ≤ nrm (FiniteLaw.pi fun i => halfLaw (h6 i)) Fn ^ 2 := sq_nonneg _
  have hsb : 0 ≤ (√b)⁻¹ := inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hcmp : g * (√b)⁻¹ * ∏ i, (1 + cplus / (Fintype.card (Fi i) : ℝ)) ≤
      g * Real.exp (cplus * L / (P * Real.log P)) * (√b)⁻¹ := by
    have := mul_le_mul_of_nonneg_left hprod (mul_nonneg hg hsb)
    linarith
  have := mul_le_mul_of_nonneg_right hcmp hN
  linarith

end Sarkozy.L20Cap
