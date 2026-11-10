module

public import Sarkozy.L20Cap.Kernel
public import Sarkozy.Cuts.SwappedLower

/-!
# The soft L20 kernel as a swapped rectangle product (`prop:l20-rectangular`)

`paper/sections/20_middle_reference.tex`, `prop:l20-rectangular`. Notation of
`Sarkozy.L20Cap.Kernel`. `F` is a finite field with `χ(-1) = -1`, `p = |F|`, `q = 1/p`.

* `CoreT F` is the set of admissible cores `C = (a₀, a₁, c₀, c₁)` (distinct, `a_i → c_j`), with
  the uniform law `μ^core` (`coreLaw`); `PairT F` is the set of ordered distinct pairs
  `b = (b₀, b₁)`, with the uniform law `μ^pair` (`pairLaw`).
* `Rk C b = 𝖱(C; b) = 𝖪(b₀, C) 𝖪(b₁, C)` and its row mass `rmass C = 𝔯(C) = 𝖱𝟙(C)`.
* `crossD` is the signed cross matrix `D₂₀` of `eq:l20-cross-matrix`, `emb C b` the half
  `x = (a₀, a₁, b₀, b₁, c₀, c₁)`, and `softKernel x x' = ∏_{i,j} (1 + (D₂₀)_ij χ(x'_j - x_i))`
  the soft L20 kernel.
* `halfLaw` is `μ^core ⊗ μ^pair` conditioned on the event `Avoid` that the pair avoids the core;
  it is the uniform law on the admissible `x` (the labellings `λ_p(G_{F,2})` of the half, in the
  coordinates `(C, b)`), and `hP = P(Avoid)`.

Proved:
* (a) `rmass_eq`: `𝔯 = (\bar𝖪² - 16q\bar𝖪)/(1 - q)`; `colMass_const`: for every `φ` on the cores
  invariant under the square-affine maps, `𝖱^*φ` is constant on the ordered distinct pairs
  (in particular the column mass, and `𝖱^*𝔯 = ‖𝔯‖²𝟙`, `adj_rmass`);
* (c) `softKernel_swap`: `K_soft((C, b), (C', b')) = 𝖱(C; b') 𝖱(C'; b)` (`eq:l20-swap`);
* (d) `hP_eq`: `h_p = P(Avoid) = (1 - 4q)(1 - 5q)/(1 - q)`; **`soft_lower`**: if
  `‖𝖱_c‖ ≤ c_R` on `L²(μ^pair) → L²(μ^core)`, `𝖱_c = 𝖱 - 𝔯 ⊗ 𝟙`, and `‖𝔯‖ ≤ s`, `c_R ≤ s`, then
  `K_soft ⪰ -(s c_R/h_p) I` on `L²(halfLaw)`. The paper's `s_p` is any such `s`; the bound
  `‖𝔯‖ ≤ s_p` of (d) and the bound `‖𝖱_c‖ ≤ c_R` (from (b) or `prop:l20-pair-gap`) are
  hypotheses here.

Not here: (b) (the star/nonstar split of `𝖱_c`), the norm bound on `𝓘^⊥` of (d), and
`‖𝔯‖ ≤ s_p`.
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace Sarkozy.L20Cap

open Sarkozy Sarkozy.Recentering Sarkozy.Cuts

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The admissible cores. -/
abbrev CoreT (F : Type*) [Field F] [Fintype F] [DecidableEq F] := {C : Fin 4 → F // Adm C}

/-- The ordered distinct pairs. -/
abbrev PairT (F : Type*) [Field F] [Fintype F] [DecidableEq F] := {b : F × F // b.1 ≠ b.2}

/-- `𝖱(C; b) = 𝖪(b₀, C) 𝖪(b₁, C)`. -/
noncomputable def Rk (C : CoreT F) (b : PairT F) : ℝ := Kz b.1.1 C.1 * Kz b.1.2 C.1

/-! ## Sums over ordered distinct pairs -/

theorem sum_pairT (f : F × F → ℝ) :
    ∑ b : PairT F, f b.1 = ∑ y, ∑ y', f (y, y') - ∑ y, f (y, y) := by
  rw [← Finset.sum_subtype (univ.filter fun b : F × F => b.1 ≠ b.2) (by simp) f, sum_filter]
  rw [Fintype.sum_prod_type, ← sum_sub_distrib]
  refine sum_congr rfl fun y _ => ?_
  have e : ∀ y', (if (y, y').1 ≠ (y, y').2 then f (y, y') else 0) =
      f (y, y') - if y = y' then f (y, y') else 0 := by
    intro y'
    by_cases h : y = y' <;> simp [h]
  rw [sum_congr rfl fun y' _ => e y', sum_sub_distrib, sum_ite_eq univ y (fun y' => f (y, y'))]
  simp

theorem card_pairT :
    (Fintype.card (PairT F) : ℝ) = (Fintype.card F : ℝ) * (Fintype.card F - 1) := by
  have h := sum_pairT (F := F) (fun _ => (1 : ℝ))
  simp only [sum_const, card_univ, nsmul_eq_mul, mul_one] at h
  rw [h]
  ring

/-! ## The laws -/

variable [Nonempty (CoreT F)] [Nonempty (PairT F)]

/-- `μ^core`, the uniform law on the admissible cores. -/
noncomputable def coreLaw : FiniteLaw (CoreT F) := FiniteLaw.uniform _

/-- `μ^pair`, the uniform law on the ordered distinct pairs. -/
noncomputable def pairLaw : FiniteLaw (PairT F) := FiniteLaw.uniform _

/-- The row mass `𝔯(C) = 𝖱𝟙(C) = E_b 𝖱(C; b)`. -/
noncomputable def rmass (C : CoreT F) : ℝ := (pairLaw (F := F)).expect fun b => Rk C b

omit [Nonempty (CoreT F)] in
theorem pairLaw_expect (f : F × F → ℝ) :
    (pairLaw (F := F)).expect (fun b => f b.1) =
      (∑ y, ∑ y', f (y, y') - ∑ y, f (y, y)) /
        ((Fintype.card F : ℝ) * (Fintype.card F - 1)) := by
  rw [pairLaw, FiniteLaw.expect_uniform, sum_pairT, card_pairT]

omit [Nonempty (CoreT F)] in
/-- **`prop:l20-rectangular`(a), the row mass**: `𝔯(C) = (\bar𝖪² - 16q\bar𝖪)/(1 - q)`. -/
theorem rmass_eq (hm1 : quadraticChar F (-1) = -1) (C : CoreT F) :
    rmass C = (Kbar C.1 ^ 2 - 16 * (Fintype.card F : ℝ)⁻¹ * Kbar C.1) /
      (1 - (Fintype.card F : ℝ)⁻¹) := by
  have hp1 : (1 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.one_lt_card
  have hp0 : (0 : ℝ) < Fintype.card F := by linarith
  unfold rmass Rk
  rw [pairLaw_expect (fun b : F × F => Kz b.1 C.1 * Kz b.2 C.1)]
  simp only
  rw [← sum_mul_sum, sum_congr rfl fun y _ => (sq (Kz y C.1)).symm, sum_Kz_sq hm1 C.2, Kbar]
  field_simp

/-! ## (c) The swap form of the soft kernel -/

/-- **The signed cross matrix `D₂₀`** (`eq:l20-cross-matrix`), rows the coordinates
`a₀, a₁, b₀, b₁, c₀, c₁` of `x`, columns those of `x'`. -/
def crossD (i j : Fin 6) : ℝ :=
  ![![0, 0, -1, -1, 0, 0], ![0, 0, -1, -1, 0, 0], ![1, 1, 0, 0, -1, -1],
    ![1, 1, 0, 0, -1, -1], ![0, 0, 1, 1, 0, 0], ![0, 0, 1, 1, 0, 0]] i j

/-- `D₂₀` is antisymmetric. -/
theorem crossD_antisymm (i j : Fin 6) : crossD j i = -crossD i j := by
  fin_cases i <;> fin_cases j <;> simp [crossD]

/-- The half `x = (a₀, a₁, b₀, b₁, c₀, c₁)` with core `C` and pair `b`. -/
def emb (C : Fin 4 → F) (b : F × F) : Fin 6 → F := ![C 0, C 1, b.1, b.2, C 2, C 3]

/-- **The soft L20 kernel** `∏_{i,j} (1 + (D₂₀)_ij χ(x'_j - x_i))`, without the indicator that
`x`, `x'` have no common label. -/
noncomputable def softKernel (x x' : Fin 6 → F) : ℝ :=
  ∏ i, ∏ j, (1 + crossD i j * chi (x' j - x i))

omit [Nonempty (CoreT F)] [Nonempty (PairT F)] in
/-- **`prop:l20-rectangular`(c), `eq:l20-swap`**:
`K_soft((C, b), (C', b')) = 𝖱(C; b') 𝖱(C'; b)`. -/
theorem softKernel_swap (hm1 : quadraticChar F (-1) = -1) (C C' : Fin 4 → F) (b b' : F × F) :
    softKernel (emb C b) (emb C' b') =
      (Kz b'.1 C * Kz b'.2 C) * (Kz b.1 C' * Kz b.2 C') := by
  simp [softKernel, Fin.prod_univ_six, crossD, emb, Kz_four]
  rw [chi_sub_comm hm1 (C' 0) b.1, chi_sub_comm hm1 (C' 0) b.2, chi_sub_comm hm1 (C' 1) b.1,
    chi_sub_comm hm1 (C' 1) b.2, chi_sub_comm hm1 (C' 2) b.1, chi_sub_comm hm1 (C' 2) b.2,
    chi_sub_comm hm1 (C' 3) b.1, chi_sub_comm hm1 (C' 3) b.2]
  simp only [neg_neg, ← sub_eq_add_neg]
  ac_rfl

/-! ## (a) The column masses: square-affine invariance -/

omit [Nonempty (CoreT F)] [Nonempty (PairT F)] in
theorem quadraticChar_inv' {d : F} (hd : d ≠ 0) : quadraticChar F d⁻¹ = quadraticChar F d := by
  have h := map_mul (quadraticChar F) d d⁻¹
  rw [mul_inv_cancel₀ hd, map_one] at h
  rcases quadraticChar_dichotomy hd with h1 | h1 <;> rw [h1] at h ⊢ <;> linarith

omit [Nonempty (CoreT F)] [Nonempty (PairT F)] in
theorem quadraticChar_inv_eq_one {α : F} (hα : quadraticChar F α = 1) :
    quadraticChar F α⁻¹ = 1 := by
  have h0 := ne_zero_of_chi hα
  have h := map_mul (quadraticChar F) α α⁻¹
  rw [mul_inv_cancel₀ h0, map_one, hα, one_mul] at h
  exact h.symm

/-- The square-affine bijection `C ↦ αC + β` of the admissible cores (`χ(α) = 1`). -/
def affCoreEquiv {α : F} (hα : quadraticChar F α = 1) (β : F) : CoreT F ≃ CoreT F where
  toFun C := ⟨affCore α β C.1, Adm_affine hα β C.2⟩
  invFun C := ⟨affCore α⁻¹ (-(α⁻¹ * β)) C.1, Adm_affine (quadraticChar_inv_eq_one hα) _ C.2⟩
  left_inv C := by
    have h0 := ne_zero_of_chi hα
    apply Subtype.ext
    funext k
    simp only [affCore]
    field_simp
    ring
  right_inv C := by
    have h0 := ne_zero_of_chi hα
    apply Subtype.ext
    funext k
    simp only [affCore]
    field_simp
    ring

/-- The square-affine map on pairs. -/
def affPair (α β : F) (b : F × F) : F × F := (α * b.1 + β, α * b.2 + β)

/-- The square-affine bijection of the ordered distinct pairs (`α ≠ 0`). -/
def affPairEquiv {α : F} (hα : α ≠ 0) (β : F) : PairT F ≃ PairT F where
  toFun b := ⟨affPair α β b.1, fun h => b.2 (mul_left_cancel₀ hα (add_right_cancel h))⟩
  invFun b := ⟨affPair α⁻¹ (-(α⁻¹ * β)) b.1, fun h =>
    b.2 (mul_left_cancel₀ (inv_ne_zero hα) (add_right_cancel h))⟩
  left_inv b := by
    apply Subtype.ext
    simp only [affPair]
    ext <;> simp only <;> field_simp <;> ring
  right_inv b := by
    apply Subtype.ext
    simp only [affPair]
    ext <;> simp only <;> field_simp <;> ring

omit [Nonempty (CoreT F)] [Nonempty (PairT F)] in
theorem Rk_affine {α : F} (hα : quadraticChar F α = 1) (β : F) (C : CoreT F) (b : PairT F) :
    Rk (affCoreEquiv hα β C) (affPairEquiv (ne_zero_of_chi hα) β b) = Rk C b := by
  simp only [Rk, affCoreEquiv, affPairEquiv, Equiv.coe_fn_mk, affPair, Kz_affine hα]

/-- The exchange of the two pair labels. -/
def swapPair (b : PairT F) : PairT F := ⟨(b.1.2, b.1.1), fun h => b.2 h.symm⟩

omit [Nonempty (CoreT F)] [Nonempty (PairT F)] in
theorem Rk_swap (C : CoreT F) (b : PairT F) : Rk C (swapPair b) = Rk C b := by
  simp only [Rk, swapPair, mul_comm]

omit [Nonempty (PairT F)] in
/-- `𝖱^*φ` is invariant under the square-affine maps, for an invariant `φ`. -/
theorem adj_affine {φ : CoreT F → ℝ} {α : F} (hα : quadraticChar F α = 1) (β : F)
    (hφ : ∀ C, φ (affCoreEquiv hα β C) = φ C) (b : PairT F) :
    recAdj (coreLaw (F := F)) Rk φ (affPairEquiv (ne_zero_of_chi hα) β b) =
      recAdj (coreLaw (F := F)) Rk φ b := by
  unfold recAdj coreLaw
  rw [FiniteLaw.expect_uniform, FiniteLaw.expect_uniform]
  congr 1
  rw [← Equiv.sum_comp (affCoreEquiv hα β)]
  refine sum_congr rfl fun C _ => ?_
  rw [Rk_affine, hφ]

omit [Nonempty (PairT F)] in
theorem adj_swap (φ : CoreT F → ℝ) (b : PairT F) :
    recAdj (coreLaw (F := F)) Rk φ (swapPair b) = recAdj (coreLaw (F := F)) Rk φ b := by
  unfold recAdj
  simp only [Rk_swap]

omit [Nonempty (PairT F)] in
/-- **`prop:l20-rectangular`(a)**: for `φ` invariant under the square-affine maps, `𝖱^*φ` is
constant on the ordered distinct pairs: the maps are transitive on the pairs with a given
`χ(b₁ - b₀)`, `𝖱` is symmetric in `b₀, b₁`, and `χ(-1) = -1` exchanges the two orbits. -/
theorem adj_const (hm1 : quadraticChar F (-1) = -1) {φ : CoreT F → ℝ}
    (hφ : ∀ (α : F) (hα : quadraticChar F α = 1) (β : F) (C : CoreT F),
      φ (affCoreEquiv hα β C) = φ C) (b b' : PairT F) :
    recAdj (coreLaw (F := F)) Rk φ b = recAdj (coreLaw (F := F)) Rk φ b' := by
  -- transitivity on pairs with the same character of the difference
  have trans : ∀ c c' : PairT F,
      quadraticChar F (c'.1.2 - c'.1.1) = quadraticChar F (c.1.2 - c.1.1) →
      recAdj (coreLaw (F := F)) Rk φ c = recAdj (coreLaw (F := F)) Rk φ c' := by
    intro c c' hcc
    have hd : c.1.2 - c.1.1 ≠ 0 := sub_ne_zero.mpr (Ne.symm c.2)
    have hd' : c'.1.2 - c'.1.1 ≠ 0 := sub_ne_zero.mpr (Ne.symm c'.2)
    set α := (c'.1.2 - c'.1.1) / (c.1.2 - c.1.1) with hαdef
    have hα : quadraticChar F α = 1 := by
      rw [hαdef, div_eq_mul_inv, map_mul, hcc, quadraticChar_inv' hd]
      rcases quadraticChar_dichotomy hd with h | h <;> rw [h] <;> norm_num
    have himg : affPairEquiv (ne_zero_of_chi hα) (c'.1.1 - α * c.1.1) c = c' := by
      apply Subtype.ext
      simp only [affPairEquiv, Equiv.coe_fn_mk, affPair]
      ext
      · simp only; ring
      · simp only [hαdef]
        field_simp
        ring
    rw [← himg, adj_affine hα _ (hφ α hα _)]
  by_cases h : quadraticChar F (b'.1.2 - b'.1.1) = quadraticChar F (b.1.2 - b.1.1)
  · exact trans b b' h
  · rw [← adj_swap φ b]
    apply trans
    have hd : b.1.2 - b.1.1 ≠ 0 := sub_ne_zero.mpr (Ne.symm b.2)
    have hd' : b'.1.2 - b'.1.1 ≠ 0 := sub_ne_zero.mpr (Ne.symm b'.2)
    have hneg : quadraticChar F ((swapPair b).1.2 - (swapPair b).1.1) =
        -quadraticChar F (b.1.2 - b.1.1) := by
      simp only [swapPair]
      have e : b.1.1 - b.1.2 = (-1) * (b.1.2 - b.1.1) := by ring
      rw [e, map_mul, hm1, neg_one_mul]
    rw [hneg]
    rcases quadraticChar_dichotomy hd with h1 | h1 <;>
      rcases quadraticChar_dichotomy hd' with h2 | h2 <;> rw [h1, h2] at h ⊢ <;> simp_all

omit [Nonempty (CoreT F)] in
/-- `𝔯` is invariant under the square-affine maps. -/
theorem rmass_affine {α : F} (hα : quadraticChar F α = 1) (β : F) (C : CoreT F) :
    rmass (affCoreEquiv hα β C) = rmass C := by
  unfold rmass pairLaw
  rw [FiniteLaw.expect_uniform, FiniteLaw.expect_uniform]
  congr 1
  rw [← Equiv.sum_comp (affPairEquiv (ne_zero_of_chi hα) β)]
  refine sum_congr rfl fun b _ => ?_
  rw [Rk_affine]

/-- **`prop:l20-rectangular`(a)**: `𝖱^*𝔯 = ‖𝔯‖² 𝟙`. -/
theorem adj_rmass (hm1 : quadraticChar F (-1) = -1) (b : PairT F) :
    recAdj (coreLaw (F := F)) Rk rmass b = nrm (coreLaw (F := F)) rmass ^ 2 := by
  have hc := adj_const hm1 (φ := rmass) (fun α hα β C => rmass_affine hα β C)
  have hmean : (pairLaw (F := F)).expect (recAdj (coreLaw (F := F)) Rk rmass) =
      nrm (coreLaw (F := F)) rmass ^ 2 := by
    rw [nrm_sq_eq]
    unfold recAdj ip
    rw [Cuts.expect_comm]
    refine (coreLaw (F := F)).expect_congr fun C => ?_
    unfold rmass
    rw [FiniteLaw.expect_mul_const]
  rw [← hmean]
  have : recAdj (coreLaw (F := F)) Rk rmass = fun _ => recAdj (coreLaw (F := F)) Rk rmass b :=
    funext fun b' => (hc b b').symm
  rw [this, FiniteLaw.expect_const]

/-- **`prop:l20-rectangular`(a)**: the column mass `𝖱^*𝟙` is constant, equal to `E 𝔯`. -/
theorem adj_one (hm1 : quadraticChar F (-1) = -1) (b : PairT F) :
    recAdj (coreLaw (F := F)) Rk (fun _ => 1) b = (coreLaw (F := F)).expect rmass := by
  have hc := adj_const hm1 (φ := fun _ => (1 : ℝ)) (fun _ _ _ _ => rfl)
  have hmean : (pairLaw (F := F)).expect (recAdj (coreLaw (F := F)) Rk (fun _ => 1)) =
      (coreLaw (F := F)).expect rmass := by
    unfold recAdj
    rw [Cuts.expect_comm]
    refine (coreLaw (F := F)).expect_congr fun C => ?_
    unfold rmass
    simp only [mul_one]
  rw [← hmean]
  have : recAdj (coreLaw (F := F)) Rk (fun _ => 1) =
      fun _ => recAdj (coreLaw (F := F)) Rk (fun _ => 1) b :=
    funext fun b' => (hc b b').symm
  rw [this, FiniteLaw.expect_const]

/-! ## (d) The lower bound of the swapped rectangle -/

/-- The centred rectangle `𝖱_c = 𝖱 - 𝔯 ⊗ 𝟙`, `(𝔯 ⊗ 𝟙)h = (E h) 𝔯`. -/
noncomputable def Rc (C : CoreT F) (b : PairT F) : ℝ := Rk C b - rmass C

omit [Nonempty (CoreT F)] in
theorem recOp_Rc_one (C : CoreT F) : recOp (pairLaw (F := F)) Rc (fun _ => 1) C = 0 := by
  unfold recOp Rc
  simp only [mul_one]
  rw [FiniteLaw.expect_sub, FiniteLaw.expect_const]
  unfold rmass
  ring

theorem rmass_eq_zero_of_nrm (h : nrm (coreLaw (F := F)) rmass = 0) (C : CoreT F) :
    rmass C = 0 := by
  have h2 : (coreLaw (F := F)).expect (fun C => rmass C ^ 2) = 0 := by
    rw [← nrm_sq_expect, h]; ring
  unfold coreLaw at h2
  rw [FiniteLaw.expect_uniform, div_eq_zero_iff] at h2
  rcases h2 with h2 | h2
  · have := (sum_eq_zero_iff_of_nonneg (fun C _ => sq_nonneg (rmass C))).mp h2 C (mem_univ C)
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
  · exfalso
    have : (Fintype.card (CoreT F) : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    exact this h2

/-- **`prop:l20-rectangular`(d), the swapped rectangle**: if `‖𝖱_c‖ ≤ c_R`, `‖𝔯‖ ≤ s` and
`c_R ≤ s`, then `T[𝖱, 𝖱] ⪰ -s c_R I` on `L²(μ^core ⊗ μ^pair)`. From `lem:swapped-rectangle`(a)
(`Cuts.swap_lower`) with the singular pair `(𝔯/‖𝔯‖, 𝟙)` of (a). -/
theorem rect_lower (hm1 : quadraticChar F (-1) = -1) {cR s : ℝ} (hcR : 0 ≤ cR)
    (hRc : ∀ h : PairT F → ℝ,
      nrm (coreLaw (F := F)) (recOp (pairLaw (F := F)) Rc h) ≤ cR * nrm (pairLaw (F := F)) h)
    (hs : nrm (coreLaw (F := F)) rmass ≤ s) (hcs : cR ≤ s) (Fn : CoreT F × PairT F → ℝ) :
    -(s * cR) * nrm ((coreLaw (F := F)).product (pairLaw (F := F))) Fn ^ 2 ≤
      kernelForm ((coreLaw (F := F)).product (pairLaw (F := F)))
        ((coreLaw (F := F)).product (pairLaw (F := F))) (fun x x' => Rk x.1 x'.2 * Rk x'.1 x.2)
        Fn Fn := by
  set σ := nrm (coreLaw (F := F)) rmass with hσdef
  have hσ0 : 0 ≤ σ := nrm_nonneg _ _
  by_cases hσ : σ = 0
  · have hr0 := rmass_eq_zero_of_nrm hσ
    refine swap_lower coreLaw pairLaw Rk Rk (σ₀ := 0) (fun _ => 1) (fun _ => 1) (nrm_one _)
      (nrm_one _) le_rfl (fun C b => by ring) ?_ ?_ hcR ?_ (le_trans hcR hcs) hcs Fn
    · intro C
      unfold recOp
      simp only [mul_one]
      exact hr0 C
    · intro b
      rw [adj_one hm1]
      have : (rmass : CoreT F → ℝ) = fun _ => 0 := funext hr0
      rw [this, FiniteLaw.expect_const]
    · intro h
      have := hRc h
      unfold Rc at this
      simpa [hr0] using this
  · have hσp : 0 < σ := lt_of_le_of_ne hσ0 (Ne.symm hσ)
    refine swap_lower coreLaw pairLaw Rk Rc (σ₀ := σ) (fun C => σ⁻¹ * rmass C) (fun _ => 1)
      ?_ (nrm_one _) hσ0 ?_ ?_ ?_ hcR hRc hs hcs Fn
    · rw [nrm_smul, abs_of_pos (inv_pos.mpr hσp), ← hσdef, inv_mul_cancel₀ hσ]
    · intro C b
      unfold Rc
      field_simp
      ring
    · exact recOp_Rc_one
    · intro b
      unfold recAdj Rc
      have e : ∀ C, (Rk C b - rmass C) * (σ⁻¹ * rmass C) = σ⁻¹ * (Rk C b * rmass C - rmass C ^ 2) :=
        fun C => by ring
      rw [(coreLaw (F := F)).expect_congr e, FiniteLaw.expect_const_mul, FiniteLaw.expect_sub]
      have h1 := adj_rmass hm1 b
      unfold recAdj at h1
      rw [h1, ← nrm_sq_expect, ← hσdef]
      ring

/-! ## The half law: conditioning on the avoidance event -/

section Conditioning

variable {Ω : Type*} [Fintype Ω]

/-- The probability of an event. -/
noncomputable def prob (ν : FiniteLaw Ω) (E : Ω → Prop) [DecidablePred E] : ℝ :=
  ν.expect fun ω => if E ω then 1 else 0

/-- `ν` conditioned on the event `E` (of positive probability). -/
noncomputable def condLaw (ν : FiniteLaw Ω) (E : Ω → Prop) [DecidablePred E]
    (hE : 0 < prob ν E) : FiniteLaw Ω where
  weight ω := if E ω then ν.weight ω / prob ν E else 0
  nonneg ω := by
    split_ifs
    · exact div_nonneg (ν.nonneg ω) hE.le
    · exact le_rfl
  total := by
    have e : ∀ ω, (if E ω then ν.weight ω / prob ν E else 0) =
        (ν.weight ω * if E ω then 1 else 0) / prob ν E := by
      intro ω; split_ifs <;> simp
    rw [sum_congr rfl fun ω _ => e ω, ← sum_div]
    exact div_self hE.ne'

theorem condLaw_expect (ν : FiniteLaw Ω) (E : Ω → Prop) [DecidablePred E] (hE : 0 < prob ν E)
    (f : Ω → ℝ) :
    (condLaw ν E hE).expect f =
      (prob ν E)⁻¹ * ν.expect (fun ω => (if E ω then 1 else 0) * f ω) := by
  unfold FiniteLaw.expect condLaw
  simp only
  rw [mul_sum]
  refine sum_congr rfl fun ω _ => ?_
  split_ifs
  · field_simp
  · simp

theorem kernelForm_condLaw (ν : FiniteLaw Ω) (E : Ω → Prop) [DecidablePred E] (hE : 0 < prob ν E)
    (K : Ω → Ω → ℝ) (f : Ω → ℝ) :
    kernelForm (condLaw ν E hE) (condLaw ν E hE) K f f =
      (prob ν E)⁻¹ * (prob ν E)⁻¹ * kernelForm ν ν K (fun ω => (if E ω then 1 else 0) * f ω)
        (fun ω => (if E ω then 1 else 0) * f ω) := by
  simp only [kernelForm, LinearMap.mk₂_apply, condLaw]
  rw [mul_sum]
  refine sum_congr rfl fun x _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun y _ => ?_
  split_ifs
  · field_simp
  · simp
  · simp
  · simp

theorem nrm_condLaw (ν : FiniteLaw Ω) (E : Ω → Prop) [DecidablePred E] (hE : 0 < prob ν E)
    (f : Ω → ℝ) :
    nrm ν (fun ω => (if E ω then 1 else 0) * f ω) ^ 2 = prob ν E * nrm (condLaw ν E hE) f ^ 2 := by
  rw [nrm_sq_expect, nrm_sq_expect, condLaw_expect, ← mul_assoc, mul_inv_cancel₀ hE.ne', one_mul]
  refine ν.expect_congr fun ω => ?_
  split_ifs <;> ring

/-- **Conditioning a lower bound** (proof of `prop:l20-rectangular`(d)): if the kernel `K` is
`⪰ -c` on `L²(ν)`, it is `⪰ -c/P(E)` on `L²(ν | E)`. This is the isometry `Jf = 𝟙_E f/√h`. -/
theorem condLaw_lower (ν : FiniteLaw Ω) (E : Ω → Prop) [DecidablePred E] (hE : 0 < prob ν E)
    (K : Ω → Ω → ℝ) {c : ℝ} (hK : ∀ G : Ω → ℝ, -c * nrm ν G ^ 2 ≤ kernelForm ν ν K G G)
    (f : Ω → ℝ) :
    -(c / prob ν E) * nrm (condLaw ν E hE) f ^ 2 ≤
      kernelForm (condLaw ν E hE) (condLaw ν E hE) K f f := by
  rw [kernelForm_condLaw]
  have h := hK (fun ω => (if E ω then 1 else 0) * f ω)
  rw [nrm_condLaw ν E hE] at h
  have hP := hE
  have hinv : 0 < (prob ν E)⁻¹ * (prob ν E)⁻¹ := mul_pos (inv_pos.mpr hP) (inv_pos.mpr hP)
  have := mul_le_mul_of_nonneg_left h hinv.le
  calc -(c / prob ν E) * nrm (condLaw ν E hE) f ^ 2
      = (prob ν E)⁻¹ * (prob ν E)⁻¹ * (-c * (prob ν E * nrm (condLaw ν E hE) f ^ 2)) := by
        field_simp
    _ ≤ _ := this

end Conditioning

/-- The event that the pair avoids the core. -/
def Avoid (x : CoreT F × PairT F) : Prop := (∀ k, x.2.1.1 ≠ x.1.1 k) ∧ ∀ k, x.2.1.2 ≠ x.1.1 k

instance : DecidablePred (Avoid (F := F)) := fun x => by unfold Avoid; infer_instance

omit [Nonempty (CoreT F)] [Nonempty (PairT F)] in
theorem card_avoid (C : CoreT F) :
    (∑ y : F, if ∀ k, y ≠ C.1 k then (1 : ℝ) else 0) = Fintype.card F - 4 := by
  have hinj := C.2.1
  have e : ∀ y : F, (if ∀ k, y ≠ C.1 k then (1 : ℝ) else 0) =
      1 - if y ∈ univ.image C.1 then 1 else 0 := by
    intro y
    by_cases h : ∀ k, y ≠ C.1 k
    · have : y ∉ univ.image C.1 := by
        simp only [mem_image, mem_univ, true_and, not_exists]
        exact fun k hk => h k hk.symm
      simp [h, this]
    · have : y ∈ univ.image C.1 := by
        push Not at h
        obtain ⟨k, hk⟩ := h
        exact mem_image.mpr ⟨k, mem_univ _, hk.symm⟩
      simp only [h, ↓reduceIte, this]
      ring
  rw [sum_congr rfl fun y _ => e y, sum_sub_distrib, sum_boole]
  simp only [sum_const, card_univ, nsmul_eq_mul, mul_one]
  rw [filter_mem_eq_inter, univ_inter, card_image_of_injective _ hinj]
  simp

omit [Nonempty (CoreT F)] in
/-- `P(Avoid | C) = (p - 4)(p - 5)/(p(p - 1))` for every admissible core. -/
theorem prob_avoid_core (C : CoreT F) :
    (pairLaw (F := F)).expect (fun b => if Avoid (C, b) then 1 else 0) =
      ((Fintype.card F : ℝ) - 4) * (Fintype.card F - 5) /
        ((Fintype.card F : ℝ) * (Fintype.card F - 1)) := by
  have e : ∀ b : PairT F, (if Avoid (C, b) then (1 : ℝ) else 0) =
      (fun y : F × F => (if ∀ k, y.1 ≠ C.1 k then (1 : ℝ) else 0) *
        (if ∀ k, y.2 ≠ C.1 k then (1 : ℝ) else 0)) b.1 := by
    intro b
    simp only [Avoid]
    split_ifs <;> simp_all
  set g : F × F → ℝ := fun y => (if ∀ k, y.1 ≠ C.1 k then (1 : ℝ) else 0) *
    (if ∀ k, y.2 ≠ C.1 k then (1 : ℝ) else 0) with hg
  have e' : (pairLaw (F := F)).expect (fun b => if Avoid (C, b) then 1 else 0) =
      (pairLaw (F := F)).expect (fun b => g b.1) := (pairLaw (F := F)).expect_congr e
  rw [e', pairLaw_expect g]
  congr 1
  simp only [hg]
  have h1 : (∑ x : F, ∑ x' : F, (if ∀ k, x ≠ C.1 k then (1 : ℝ) else 0) *
      (if ∀ k, x' ≠ C.1 k then (1 : ℝ) else 0)) =
      (∑ x : F, if ∀ k, x ≠ C.1 k then (1 : ℝ) else 0) *
        (∑ x : F, if ∀ k, x ≠ C.1 k then (1 : ℝ) else 0) := by
    rw [sum_mul_sum]
  rw [h1, card_avoid]
  have e2 : ∀ y : F, (if ∀ k, y ≠ C.1 k then (1 : ℝ) else 0) * (if ∀ k, y ≠ C.1 k then 1 else 0) =
      if ∀ k, y ≠ C.1 k then 1 else 0 := fun y => by split_ifs <;> ring
  rw [sum_congr rfl fun y _ => e2 y, card_avoid]
  ring

/-- **`h_p = P(Avoid) = (1 - 4q)(1 - 5q)/(1 - q)`** (`prop:l20-rectangular`(d)). -/
theorem hP_eq :
    prob ((coreLaw (F := F)).product (pairLaw (F := F))) Avoid =
      ((Fintype.card F : ℝ) - 4) * (Fintype.card F - 5) /
        ((Fintype.card F : ℝ) * (Fintype.card F - 1)) := by
  unfold prob
  rw [FiniteLaw.expect_product]
  simp only [prob_avoid_core, FiniteLaw.expect_const]

theorem hP_pos (h6 : 6 ≤ Fintype.card F) :
    0 < prob ((coreLaw (F := F)).product (pairLaw (F := F))) Avoid := by
  rw [hP_eq]
  have : (6 : ℝ) ≤ Fintype.card F := by exact_mod_cast h6
  apply div_pos
  · apply mul_pos <;> linarith
  · apply mul_pos <;> linarith

/-- **The half law** `μ_p`: `μ^core ⊗ μ^pair` conditioned on `Avoid`, the uniform law on the
admissible halves `x = (a₀, a₁, b₀, b₁, c₀, c₁)` (the labellings of `G_{F,2}`, in the coordinates
`(C, b)`). -/
noncomputable def halfLaw (h6 : 6 ≤ Fintype.card F) : FiniteLaw (CoreT F × PairT F) :=
  condLaw ((coreLaw (F := F)).product (pairLaw (F := F))) Avoid (hP_pos h6)

/-- **`prop:l20-rectangular`(d), the soft kernel**: under the hypotheses of `rect_lower`,
`K_soft ⪰ -(s c_R/h_p) I` on `L²(μ_p)`, `h_p = P(Avoid) = (1 - 4q)(1 - 5q)/(1 - q)`
(`hP_eq`); the kernel is `𝖱(C; b') 𝖱(C'; b) = K_soft(x, x')` (`softKernel_swap`). -/
theorem soft_lower (hm1 : quadraticChar F (-1) = -1) (h6 : 6 ≤ Fintype.card F) {cR s : ℝ}
    (hcR : 0 ≤ cR)
    (hRc : ∀ h : PairT F → ℝ,
      nrm (coreLaw (F := F)) (recOp (pairLaw (F := F)) Rc h) ≤ cR * nrm (pairLaw (F := F)) h)
    (hs : nrm (coreLaw (F := F)) rmass ≤ s) (hcs : cR ≤ s) (f : CoreT F × PairT F → ℝ) :
    -(s * cR / prob ((coreLaw (F := F)).product (pairLaw (F := F))) Avoid) *
        nrm (halfLaw h6) f ^ 2 ≤
      kernelForm (halfLaw h6) (halfLaw h6) (fun x x' => Rk x.1 x'.2 * Rk x'.1 x.2) f f :=
  condLaw_lower _ Avoid (hP_pos h6) _ (fun G => rect_lower hm1 hcR hRc hs hcs G) f

/-- **`μ_p` is the uniform law on the admissible halves**: its weight is
`1/(|CoreT| (p - 4)(p - 5))` on the halves whose pair avoids the core, and `0` elsewhere; these
halves are the injective `(a₀, a₁, b₀, b₁, c₀, c₁)` with `a_i → c_j`, the labellings of
`G_{F,2}`. -/
theorem halfLaw_weight (h6 : 6 ≤ Fintype.card F) (x : CoreT F × PairT F) :
    (halfLaw h6).weight x = if Avoid x then
      ((Fintype.card (CoreT F) : ℝ) * (((Fintype.card F : ℝ) - 4) * (Fintype.card F - 5)))⁻¹
    else 0 := by
  have h6' : (6 : ℝ) ≤ Fintype.card F := by exact_mod_cast h6
  have hc : (0 : ℝ) < Fintype.card (CoreT F) := by exact_mod_cast Fintype.card_pos
  simp only [halfLaw, condLaw]
  split_ifs with h
  · rw [hP_eq]
    simp only [FiniteLaw.product, coreLaw, pairLaw, FiniteLaw.uniform]
    rw [card_pairT]
    have h4 : (Fintype.card F : ℝ) - 4 ≠ 0 := by linarith
    have h5 : (Fintype.card F : ℝ) - 5 ≠ 0 := by linarith
    have h1 : (Fintype.card F : ℝ) - 1 ≠ 0 := by linarith
    have hp : (Fintype.card F : ℝ) ≠ 0 := by linarith
    field_simp
  · rfl

end Sarkozy.L20Cap
