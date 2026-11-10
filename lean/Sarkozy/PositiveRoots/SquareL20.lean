module

public import Sarkozy.PositiveRoots.SquareSchur
public import Sarkozy.L20Cap.Mass
public import Sarkozy.L20Cap.PrimeCaps
public import Sarkozy.DLK.RawPair

@[expose] public section

/-!
# `lem:root-square` on W3's rectangle, with no remaining hypothesis

`paper/sections/20b_positive_roots.tex`, `lem:root-square`, first bound
`‖K_soft∘H_j² − (1 − 2q)²K_soft‖ ≤ 256c₀𝔯₊q`, on W3's objects (`Sarkozy.L20Cap`): the admissible
cores `CoreT F` with the uniform law `μ^core` (`coreLaw`), the ordered distinct pairs `PairT F`
with `μ^pair` (`pairLaw`), the rectangle `𝖱(C; b) = 𝖪(b₀, C)𝖪(b₁, C)` (`Rk`) and the soft kernel
`𝖱(C; b')𝖱(C'; b)` (`eq:l20-swap`, W3's `softKernel_swap`).

* `Rk_sq`: `𝖱² = 256𝖱` (`𝖱 ∈ {0, 256}`); `rect_row_sq`: `E_b𝖱(C; b)² = 256𝔯(C)`;
* `rmass_le`: **`𝔯(C) ≤ 𝔯₊ = (1 + η)²/(1 − q)`**, `η = 2q + 11r`, from W3's `rmass_eq` and
  `Kbar_dev` (Weil) — `prop:l20-rectangular`(d)'s `𝔯 ≤ 𝔯₊`;
* `root_square_first_L20`: the bound for the core score, given the Gram bounds of the residual
  pair maps of the core pairs on `L²(μ^core)`;
* `gram_le_of_map`: the Gram of a map of squared norm `≤ a` is `⪯ a`;
* `pair_residual_map`, `pair_residual_gram`: `cor:raw-pair-maps`(b) on `μ^pair`, from
  `DLK.raw_pair_remainder` (`thm:dl:K`): `E_b⟨ρ_b, G⟩² ≤ c₀q²‖G‖²`;
* `fibre_const`, `core_marginal`: **under `μ^core` the core pairs `a(C) = (C₀, C₁)` and
  `c(C) = (C₂, C₃)` are uniform ordered distinct pairs** (the square-affine maps act transitively
  on the pairs with a given `χ(b₁ − b₀)`, and the swap of the two labels, an automorphism of the
  admissible cores, exchanges the two orbits as `χ(−1) = −1`); `core_residual_gram`: hence the
  Gram bounds hold on `L²(μ^core)` — the step "under `μ^core` the pairs `a` and `c` of a core
  are uniform distinct pairs, so the same bound holds" of the proof;
* **`root_square_first_core`** (`H₀`), **`root_square_first_core2`** (`H₂`) and
  **`root_square_first_private`**
  (`H₁`, in the variables `(b, C)`, where the soft kernel is `T[𝖱^*, 𝖱^*]` and the column mass is
  the constant `E𝔯`, W3's `adj_one`): the first bound of `lem:root-square`,
  `≤ p·256𝔯₊·c₀q² = 256c₀𝔯₊q`, from `χ(−1) = −1`, Weil (H1) and `thm:dl:K` (H6) only;
* **the second bound** (`root_square_second_core`, `root_square_second_core2`,
  `root_square_second_private`, for `H₀, H₂, H₁`): `‖K_soft∘H_j² − K_soft‖ ≤ 4qs² + 256c₀𝔯₊q`,
  given `‖𝔯‖ ≤ s` and `‖𝖱_c‖ ≤ c ≤ s` (the paper's `𝔯₂ = s_p`; `prop:l20-rectangular`(b), (d),
  W3's `rmass_norm_le` and rectangle gap). The norm step is proved: `recOp_Rk_split`
  (`𝖱h = 𝖱_cP₀h + (Eh)𝔯`), `ip_RcOp_rmass` (`𝖱_c^*𝔯 = 0`, from W3's `adj_rmass`),
  `rect_norm_le` (`‖𝖱‖ ≤ s`) and `soft_norm_le` (`‖K_soft‖ ≤ s²`, `lem:swapped-rectangle`(a));
* **`soft_sq_price`**: the average `V = (H₀² + H₁² + H₂²)/3` on the pairs of halves,
  `‖K_soft∘V − K_soft‖ ≤ 4qs² + 256c₀𝔯₊q` — the first term of `ε^raw_sq` in
  `lem:root-normalization`(a) before the compression `1/h_p` (`H₁` is carried back from the
  variables `(b, C)` by `kernelForm_prodComm`, `nrm_prodComm`);
* **`actual_sq_price`**: the same in the fixed half chart `L²(μ_p)` (W3's `halfLaw`), at the cost
  `1/h_p` (`condLaw_abs`, `lem:restriction`(b)): the term `(4q𝔯₂² + 256c₀𝔯₊q)/h'_p` of `ε^raw_sq`;
* `rmass_norm_le_sP`, **`actual_sq_price_sP`**: with the paper's `𝔯₂ = s_p` (W3's `sP`), the
  remaining hypotheses being the mean bound `E(\bar𝖪 − 1) ≤ 𝔪₊` (`prop:l20-rank4`) and
  `‖𝖱_c‖ ≤ c ≤ s_p` (`prop:l20-rectangular`(b)).
-/

namespace Sarkozy.PositiveRoots

open Finset Sarkozy Sarkozy.Cuts Sarkozy.Recentering Sarkozy.L20Cap

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **`𝖱² = 256𝖱`** (`𝖱` takes the values `0` and `256`). -/
theorem Rk_sq (hm1 : quadraticChar F (-1) = -1) (C : CoreT F) (b : PairT F) :
    Rk C b ^ 2 = 256 * Rk C b := by
  unfold Rk
  rw [mul_pow, Kz_sq hm1 C.2, Kz_sq hm1 C.2]
  ring

theorem Kbar_nonneg (hm1 : quadraticChar F (-1) = -1) (C : CoreT F) : 0 ≤ Kbar C.1 := by
  unfold Kbar
  have hn : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  exact div_nonneg (sum_nonneg fun z _ => Kz_nonneg hm1 C.2 z) hn.le

variable [Nonempty (CoreT F)] [Nonempty (PairT F)]

omit [Nonempty (CoreT F)] in
/-- **The diagonal of `𝖱𝖱^*`**: `E_b𝖱(C; b)² = 256𝔯(C)`. -/
theorem rect_row_sq (hm1 : quadraticChar F (-1) = -1) (C : CoreT F) :
    (pairLaw (F := F)).expect (fun b => Rk C b ^ 2) = 256 * rmass C := by
  have e : (fun b => Rk C b ^ 2) = fun b => 256 * Rk C b := funext (Rk_sq hm1 C)
  rw [e, FiniteLaw.expect_const_mul]
  rfl

omit [Nonempty (CoreT F)] in
/-- **`𝔯 ≤ 𝔯₊ = (1 + η)²/(1 − q)`** (`prop:l20-rectangular`(d)), `η = 2q + 11r` (W3's `etaL`). -/
theorem rmass_le (hm1 : quadraticChar F (-1) = -1) (hF : ringChar F ≠ 2)
    (hW : Sarkozy.Labellings.WeilBound F) (C : CoreT F) :
    rmass C ≤ (1 + etaL F) ^ 2 / (1 - (Fintype.card F : ℝ)⁻¹) := by
  have hp1 : (1 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.one_lt_card
  have hq : 0 < 1 - (Fintype.card F : ℝ)⁻¹ := by
    have : (Fintype.card F : ℝ)⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp1
    linarith
  have hq0 : 0 ≤ (Fintype.card F : ℝ)⁻¹ := inv_nonneg.mpr (by linarith)
  rw [rmass_eq hm1 C]
  apply div_le_div_of_nonneg_right _ hq.le
  have h0 := Kbar_nonneg hm1 C
  have hdev := Kbar_dev hF hW C.2.1
  have hle : Kbar C.1 ≤ 1 + etaL F := by
    unfold etaL
    have := (abs_le.mp hdev).2
    linarith
  have h2 : Kbar C.1 ^ 2 ≤ (1 + etaL F) ^ 2 := pow_le_pow_left₀ h0 hle 2
  have h3 : 0 ≤ 16 * (Fintype.card F : ℝ)⁻¹ * Kbar C.1 := by positivity
  linarith

omit [Nonempty (PairT F)] in
theorem coreLaw_pos (C : CoreT F) : 0 < (coreLaw (F := F)).weight C := by
  change 0 < (Fintype.card (CoreT F) : ℝ)⁻¹
  exact inv_pos.mpr (by exact_mod_cast Fintype.card_pos)

/-- **`lem:root-square`, the first bound, on W3's rectangle** (core score `H₀`, pairing the pair
`a = (C₀, C₁)` of the first half with the pair `c' = (C'₂, C'₃)` of the second): with the Gram
bound `g` of the residual pair maps of the core pairs on `L²(μ^core)` (`cor:raw-pair-maps`(b)
transported; `g = c₀q²` in the paper), Weil's bound and `χ(−1) = −1`,
`|⟨F, (K_soft∘H₀² − (1 − 2q)²K_soft)H⟩| ≤ n·(256𝔯₊)·g‖F‖‖H‖`. -/
theorem root_square_first_L20 (hm1 : quadraticChar F (-1) = -1) (hF : ringChar F ≠ 2)
    (hW : Sarkozy.Labellings.WeilBound F) {g : ℝ} (hg : 0 ≤ g)
    (hWa : ∀ f, kernelForm (coreLaw (F := F)) coreLaw
      (fun C C' => ip (FiniteLaw.uniform (F × F)) (rhoV (C.1 0, C.1 1)) (rhoV (C'.1 0, C'.1 1)))
        f f ≤ g * nrm coreLaw f ^ 2)
    (hWc : ∀ f, kernelForm (coreLaw (F := F)) coreLaw
      (fun C C' => ip (FiniteLaw.uniform (F × F)) (rhoV (C.1 2, C.1 3)) (rhoV (C'.1 2, C'.1 3)))
        f f ≤ g * nrm coreLaw f ^ 2)
    (Fn Hn : CoreT F × PairT F → ℝ) :
    |kernelForm ((coreLaw (F := F)).product pairLaw) ((coreLaw (F := F)).product pairLaw)
        (fun p q => Rk p.1 q.2 * Rk q.1 p.2 * pairScore (p.1.1 0, p.1.1 1) (q.1.1 2, q.1.1 3) ^ 2 -
          (1 - 2 / (Fintype.card F : ℝ)) ^ 2 * (Rk p.1 q.2 * Rk q.1 p.2)) Fn Hn| ≤
      (Fintype.card F : ℝ) * (256 * ((1 + etaL F) ^ 2 / (1 - (Fintype.card F : ℝ)⁻¹)) * g) *
        nrm ((coreLaw (F := F)).product pairLaw) Fn *
        nrm ((coreLaw (F := F)).product pairLaw) Hn := by
  have hD : ∀ C : CoreT F, (pairLaw (F := F)).expect (fun b => Rk C b ^ 2) ≤
      256 * ((1 + etaL F) ^ 2 / (1 - (Fintype.card F : ℝ)⁻¹)) := by
    intro C
    rw [rect_row_sq hm1 C]
    have := rmass_le hm1 hF hW C
    linarith
  have haP : ∀ C : CoreT F, (C.1 0, C.1 1).1 ≠ (C.1 0, C.1 1).2 := fun C h =>
    absurd (C.2.1 h) (by decide)
  have hcP : ∀ C : CoreT F, (C.1 2, C.1 3).1 ≠ (C.1 2, C.1 3).2 := fun C h =>
    absurd (C.2.1 h) (by decide)
  exact root_square_first (coreLaw (F := F)) coreLaw_pos pairLaw Rk (fun C => (C.1 0, C.1 1))
    (fun C => (C.1 2, C.1 3)) haP hcP hD hg hWa hWc Fn Hn

/-! ## The Gram of a map, and the private score -/

/-- **The Gram of a map**: if `E_x⟨φ_x, G⟩² ≤ a‖G‖²` for all `G` (the map `G ↦ ⟨φ_·, G⟩` has
squared norm `≤ a`), then the Gram kernel `⟨φ_x, φ_{x'}⟩` is `⪯ a` on `L²(α)`. -/
theorem gram_le_of_map {X S : Type*} [Fintype X] [Fintype S] (α : FiniteLaw X) (π : FiniteLaw S)
    (φ : X → S → ℝ) {a : ℝ} (ha : 0 ≤ a)
    (hmap : ∀ G : S → ℝ, α.expect (fun x => ip π (φ x) G ^ 2) ≤ a * nrm π G ^ 2) (f : X → ℝ) :
    kernelForm α α (fun x x' => ip π (φ x) (φ x')) f f ≤ a * nrm α f ^ 2 := by
  have e : kernelForm α α (fun x x' => ip π (φ x) (φ x')) f f = nrm π (recAdj α φ f) ^ 2 := by
    rw [nrm_sq_expect]
    simp only [kernelForm, LinearMap.mk₂_apply, ip, recAdj, FiniteLaw.expect]
    calc ∑ x, ∑ x', α.weight x * α.weight x' * f x * (∑ s, π.weight s * (φ x s * φ x' s)) * f x'
        = ∑ x, ∑ x', ∑ s, π.weight s * ((α.weight x * (φ x s * f x)) *
            (α.weight x' * (φ x' s * f x'))) := by
          refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun x' _ => ?_
          rw [Finset.mul_sum, Finset.sum_mul]
          exact Finset.sum_congr rfl fun s _ => by ring
      _ = ∑ x, ∑ s, ∑ x', π.weight s * ((α.weight x * (φ x s * f x)) *
            (α.weight x' * (φ x' s * f x'))) := Finset.sum_congr rfl fun x _ => Finset.sum_comm
      _ = ∑ s, ∑ x, ∑ x', π.weight s * ((α.weight x * (φ x s * f x)) *
            (α.weight x' * (φ x' s * f x'))) := Finset.sum_comm
      _ = _ := by
          refine Finset.sum_congr rfl fun s _ => ?_
          rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [Finset.mul_sum]
  have hA : ∀ G, nrm α (recOp π φ G) ≤ Real.sqrt a * nrm π G := by
    intro G
    have h := hmap G
    have hsq : nrm α (recOp π φ G) ^ 2 ≤ (Real.sqrt a * nrm π G) ^ 2 := by
      rw [nrm_sq_expect, mul_pow, Real.sq_sqrt ha]
      exact h
    exact (abs_le_of_sq_le_sq' hsq (mul_nonneg (Real.sqrt_nonneg _) (nrm_nonneg _ _))).2
  have h2 := nrm_recAdj_le α π φ (Real.sqrt_nonneg a) hA f
  rw [e]
  have h3 : nrm π (recAdj α φ f) ^ 2 ≤ (Real.sqrt a * nrm α f) ^ 2 :=
    pow_le_pow_left₀ (nrm_nonneg _ _) h2 2
  rwa [mul_pow, Real.sq_sqrt ha] at h3

/-! ## The core pairs are uniform distinct pairs under `μ^core` -/

section CoreMarginal

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The fibre count `N(b) = #{C : pr(C) = b}`. -/
noncomputable def fibre (pr : CoreT F → PairT F) (b : PairT F) : ℝ :=
  ((univ.filter fun C : CoreT F => pr C = b).card : ℝ)

theorem fibre_equiv (pr : CoreT F → PairT F) (eC : CoreT F ≃ CoreT F) (eP : PairT F ≃ PairT F)
    (h : ∀ C, pr (eC C) = eP (pr C)) (b : PairT F) : fibre pr (eP b) = fibre pr b := by
  unfold fibre
  congr 1
  symm
  refine Finset.card_equiv eC (fun C => ?_)
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, h]
  exact ⟨fun hC => by rw [hC], fun hC => eP.injective hC⟩

/-- **The fibre count is constant** on the ordered distinct pairs, if `pr` commutes with the
square-affine maps and with a swap of the two labels (`χ(−1) = −1` exchanges the two orbits). -/
theorem fibre_const (hm1 : quadraticChar F (-1) = -1) (pr : CoreT F → PairT F)
    (haff : ∀ (α : F) (hα : quadraticChar F α = 1) (β : F) (C : CoreT F),
      pr (affCoreEquiv hα β C) = affPairEquiv (ne_zero_of_chi hα) β (pr C))
    (sw : CoreT F ≃ CoreT F) (hsw : ∀ C, pr (sw C) = swapPair (pr C)) (b b' : PairT F) :
    fibre pr b = fibre pr b' := by
  have hswP : ∀ c, fibre pr (swapPair c) = fibre pr c := by
    intro c
    exact fibre_equiv pr sw ⟨swapPair, swapPair, fun c => rfl, fun c => rfl⟩ hsw c
  have trans : ∀ c c' : PairT F,
      quadraticChar F (c'.1.2 - c'.1.1) = quadraticChar F (c.1.2 - c.1.1) →
      fibre pr c = fibre pr c' := by
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
    rw [← himg, fibre_equiv pr (affCoreEquiv hα (c'.1.1 - α * c.1.1))
      (affPairEquiv (ne_zero_of_chi hα) (c'.1.1 - α * c.1.1)) (haff α hα _) c]
  by_cases h : quadraticChar F (b'.1.2 - b'.1.1) = quadraticChar F (b.1.2 - b.1.1)
  · exact trans b b' h
  · rw [← hswP b]
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

variable [Nonempty (CoreT F)] [Nonempty (PairT F)]

/-- **The marginal of a core pair is uniform**: `E_{C∼μ^core} g(pr C) = E_{b∼μ^pair} g(b)`. -/
theorem core_marginal (hm1 : quadraticChar F (-1) = -1) (pr : CoreT F → PairT F)
    (haff : ∀ (α : F) (hα : quadraticChar F α = 1) (β : F) (C : CoreT F),
      pr (affCoreEquiv hα β C) = affPairEquiv (ne_zero_of_chi hα) β (pr C))
    (sw : CoreT F ≃ CoreT F) (hsw : ∀ C, pr (sw C) = swapPair (pr C)) (g : PairT F → ℝ) :
    (coreLaw (F := F)).expect (fun C => g (pr C)) = (pairLaw (F := F)).expect g := by
  obtain ⟨b₀⟩ := (inferInstance : Nonempty (PairT F))
  have hconst := fibre_const hm1 pr haff sw hsw
  -- `∑_C g(pr C) = ∑_b N(b) g(b)`
  have hsum : ∀ h : PairT F → ℝ, ∑ C, h (pr C) = ∑ b, fibre pr b * h b := by
    intro h
    unfold fibre
    rw [← Finset.sum_fiberwise univ pr (fun C => h (pr C))]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [Finset.sum_congr rfl fun C hC => by
      rw [(Finset.mem_filter.mp hC).2]]
    simp only [Finset.sum_const, nsmul_eq_mul]
  have hcard : (Fintype.card (CoreT F) : ℝ) = fibre pr b₀ * Fintype.card (PairT F) := by
    have := hsum (fun _ => 1)
    simp only [mul_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at this
    rw [this, Finset.sum_congr rfl fun b _ => hconst b b₀, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_comm]
  rw [coreLaw, pairLaw, FiniteLaw.expect_uniform, FiniteLaw.expect_uniform, hsum,
    Finset.sum_congr rfl fun b _ => by rw [hconst b b₀], ← Finset.mul_sum, hcard]
  have hP : (0 : ℝ) < Fintype.card (PairT F) := by exact_mod_cast Fintype.card_pos
  have hC : (0 : ℝ) < Fintype.card (CoreT F) := by exact_mod_cast Fintype.card_pos
  have hN : fibre pr b₀ ≠ 0 := by
    intro h0
    rw [hcard, h0, zero_mul] at hC
    exact lt_irrefl _ hC
  field_simp

end CoreMarginal

section Private

variable {p : ℕ} [Fact p.Prime]

/-- **The residual pair map on `μ^pair`** (`cor:raw-pair-maps`(b), from `thm:dl:K` through
`DLK.raw_pair_remainder`): `E_{b∼μ^pair}⟨ρ_b, G⟩² ≤ c₀q²‖G‖²`, `c₀ = 4/(1 − q) + 2q`. -/
theorem pair_residual_map (hDLK : Sarkozy.Target.FourCycle) (hp2 : p ≠ 2)
    [Nonempty (PairT (ZMod p))] (G : ZMod p × ZMod p → ℝ) :
    (pairLaw (F := ZMod p)).expect (fun b => ip (FiniteLaw.uniform (ZMod p × ZMod p))
      (rhoV b.1) G ^ 2) ≤
      (4 / (1 - 1 / (p : ℝ)) + 2 * (1 / (p : ℝ))) * (1 / (p : ℝ)) ^ 2 *
        nrm (FiniteLaw.uniform (ZMod p × ZMod p)) G ^ 2 := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hs : Real.sqrt p ≠ 0 := (Real.sqrt_pos.mpr hp0).ne'
  have h := DLK.raw_pair_remainder hDLK hp2 (fun s u => G (s, u))
  have hip : ∀ y : ZMod p × ZMod p, ip (FiniteLaw.uniform (ZMod p × ZMod p)) (rhoV y) G =
      (1 / (p : ℝ) ^ 2) * ∑ s, ∑ u, (SecondOrder.chiRe (s - y.1) * SecondOrder.chiRe (s - y.2) *
        (SecondOrder.chiRe (u - y.1) * SecondOrder.chiRe (u - y.2)) -
        (1 / Real.sqrt p) * (1 - 2 / (p : ℝ)) * (Real.sqrt p * (if s = u then 1 else 0))) *
          G (s, u) := by
    intro y
    unfold ip rhoV rhoP psiP
    rw [FiniteLaw.expect_uniform, Fintype.sum_prod_type, Fintype.card_prod, ZMod.card]
    rw [div_eq_mul_inv, mul_comm, one_div, Nat.cast_mul, ← sq]
    congr 1
    refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun u _ => ?_
    have : (1 / Real.sqrt p) * (1 - 2 / (p : ℝ)) * (Real.sqrt p * (if s = u then 1 else 0)) =
        (1 - 2 / (p : ℝ)) * (if s = u then 1 else 0) := by field_simp
    rw [this]
    rfl
  have hnrm : nrm (FiniteLaw.uniform (ZMod p × ZMod p)) G ^ 2 =
      (1 / (p : ℝ) ^ 2) * ∑ s, ∑ u, G (s, u) ^ 2 := by
    rw [nrm_sq_expect, FiniteLaw.expect_uniform, Fintype.sum_prod_type, Fintype.card_prod,
      ZMod.card]
    push_cast
    ring
  have hexp : (pairLaw (F := ZMod p)).expect (fun b => ip (FiniteLaw.uniform (ZMod p × ZMod p))
      (rhoV b.1) G ^ 2) = (1 / ((p : ℝ) * (p - 1))) *
        ∑ y ∈ univ.filter (fun y : ZMod p × ZMod p => y.1 ≠ y.2),
          ip (FiniteLaw.uniform (ZMod p × ZMod p)) (rhoV y) G ^ 2 := by
    rw [pairLaw, FiniteLaw.expect_uniform, card_pairT, ZMod.card]
    rw [Finset.sum_subtype (p := fun y : ZMod p × ZMod p => y.1 ≠ y.2)
      (univ.filter fun y : ZMod p × ZMod p => y.1 ≠ y.2) (fun y => by simp)
      (fun y => ip (FiniteLaw.uniform (ZMod p × ZMod p)) (rhoV y) G ^ 2)]
    ring
  rw [hexp, hnrm]
  simp only [hip]
  exact h

/-- **The Gram of the private residual map** on `L²(μ^pair)` is `⪯ c₀q²`. -/
theorem pair_residual_gram (hDLK : Sarkozy.Target.FourCycle) (hp2 : p ≠ 2)
    [Nonempty (PairT (ZMod p))] (f : PairT (ZMod p) → ℝ) :
    kernelForm (pairLaw (F := ZMod p)) pairLaw
        (fun b b' => ip (FiniteLaw.uniform (ZMod p × ZMod p)) (rhoV b.1) (rhoV b'.1)) f f ≤
      (4 / (1 - 1 / (p : ℝ)) + 2 * (1 / (p : ℝ))) * (1 / (p : ℝ)) ^ 2 * nrm pairLaw f ^ 2 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hq : 0 < 1 - 1 / (p : ℝ) := by
    have : 1 / (p : ℝ) < 1 := by rw [div_lt_one (by linarith)]; exact hp1
    linarith
  exact gram_le_of_map (pairLaw (F := ZMod p)) (FiniteLaw.uniform (ZMod p × ZMod p))
    (fun b => rhoV b.1) (by positivity) (pair_residual_map hDLK hp2) f

/-- **`lem:root-square`, the first bound, for the private score**
(`H₁ = H(b, b')`), in the variables `(b, C)` where the soft kernel is `T[𝖱^*, 𝖱^*]`
(`lem:swapped-rectangle`, last sentence): with `χ(−1) = −1`, Weil and `thm:dl:K`,
`|⟨F, (K_soft∘H₁² − (1 − 2q)²K_soft)H⟩| ≤ p·256𝔯₊·c₀q²‖F‖‖H‖ = 256c₀𝔯₊q‖F‖‖H‖`. No hypothesis
remains: the column mass of `𝖱` is the constant `E𝔯 ≤ 𝔯₊` (W3's `adj_one`), and the private
pairs are uniform distinct pairs, the law of `cor:raw-pair-maps`(b). -/
theorem root_square_first_private (hm1 : quadraticChar (ZMod p) (-1) = -1) (hp2 : p ≠ 2)
    (hW : Sarkozy.Labellings.WeilBound (ZMod p)) (hDLK : Sarkozy.Target.FourCycle)
    [Nonempty (CoreT (ZMod p))] [Nonempty (PairT (ZMod p))]
    (Fn Hn : PairT (ZMod p) × CoreT (ZMod p) → ℝ) :
    |kernelForm ((pairLaw (F := ZMod p)).product coreLaw) ((pairLaw (F := ZMod p)).product coreLaw)
        (fun P Q => Rk Q.2 P.1 * Rk P.2 Q.1 * pairScore P.1.1 Q.1.1 ^ 2 -
          (1 - 2 / (Fintype.card (ZMod p) : ℝ)) ^ 2 * (Rk Q.2 P.1 * Rk P.2 Q.1)) Fn Hn| ≤
      (Fintype.card (ZMod p) : ℝ) *
        (256 * ((1 + etaL (ZMod p)) ^ 2 / (1 - (Fintype.card (ZMod p) : ℝ)⁻¹)) *
          ((4 / (1 - 1 / (p : ℝ)) + 2 * (1 / (p : ℝ))) * (1 / (p : ℝ)) ^ 2)) *
        nrm ((pairLaw (F := ZMod p)).product coreLaw) Fn *
        nrm ((pairLaw (F := ZMod p)).product coreLaw) Hn := by
  have hF : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hq : 0 < 1 - 1 / (p : ℝ) := by
    have : 1 / (p : ℝ) < 1 := by rw [div_lt_one (by linarith)]; exact hp1
    linarith
  have hpos : ∀ b : PairT (ZMod p), 0 < (pairLaw (F := ZMod p)).weight b := by
    intro b
    change 0 < (Fintype.card (PairT (ZMod p)) : ℝ)⁻¹
    exact inv_pos.mpr (by exact_mod_cast Fintype.card_pos)
  have hD : ∀ b : PairT (ZMod p), (coreLaw (F := ZMod p)).expect (fun C => Rk C b ^ 2) ≤
      256 * ((1 + etaL (ZMod p)) ^ 2 / (1 - (Fintype.card (ZMod p) : ℝ)⁻¹)) := by
    intro b
    have e : (fun C => Rk C b ^ 2) = fun C => 256 * (Rk C b * 1) := by
      funext C; rw [Rk_sq hm1 C b]; ring
    rw [e, FiniteLaw.expect_const_mul]
    have h1 : (coreLaw (F := ZMod p)).expect (fun C => Rk C b * 1) =
        (coreLaw (F := ZMod p)).expect rmass := adj_one hm1 b
    rw [h1]
    have h2 : (coreLaw (F := ZMod p)).expect rmass ≤
        (coreLaw (F := ZMod p)).expect (fun _ => (1 + etaL (ZMod p)) ^ 2 /
          (1 - (Fintype.card (ZMod p) : ℝ)⁻¹)) :=
      FiniteLaw.expect_mono _ (fun C => rmass_le hm1 hF hW C)
    rw [FiniteLaw.expect_const] at h2
    linarith
  have hg : 0 ≤ (4 / (1 - 1 / (p : ℝ)) + 2 * (1 / (p : ℝ))) * (1 / (p : ℝ)) ^ 2 := by positivity
  exact root_square_first (pairLaw (F := ZMod p)) hpos coreLaw (fun b C => Rk C b)
    (fun b => b.1) (fun b => b.1) (fun b => b.2) (fun b => b.2) hD hg
    (pair_residual_gram hDLK hp2) (pair_residual_gram hDLK hp2) Fn Hn

end Private

/-! ## The core score with no remaining hypothesis -/

section CorePairs

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The core pair `a(C) = (C₀, C₁)` as an ordered distinct pair. -/
def aPr (C : CoreT F) : PairT F := ⟨(C.1 0, C.1 1), fun h => absurd (C.2.1 h) (by decide)⟩

/-- The core pair `c(C) = (C₂, C₃)` as an ordered distinct pair. -/
def cPr (C : CoreT F) : PairT F := ⟨(C.1 2, C.1 3), fun h => absurd (C.2.1 h) (by decide)⟩

theorem Adm_comp_swap {C : Fin 4 → F} (hC : Adm C) (i j : Fin 4)
    (hij : (i = 0 ∧ j = 1) ∨ (i = 2 ∧ j = 3)) : Adm (C ∘ Equiv.swap i j) := by
  obtain ⟨hinj, h20, h30, h21, h31⟩ := hC
  refine ⟨hinj.comp (Equiv.injective _), ?_⟩
  rcases hij with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have e0 : Equiv.swap (0 : Fin 4) 1 0 = 1 := Equiv.swap_apply_left _ _
    have e1 : Equiv.swap (0 : Fin 4) 1 1 = 0 := Equiv.swap_apply_right _ _
    have e2 : Equiv.swap (0 : Fin 4) 1 2 = 2 := Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)
    have e3 : Equiv.swap (0 : Fin 4) 1 3 = 3 := Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)
    simp only [Function.comp, e0, e1, e2, e3]
    exact ⟨h21, h31, h20, h30⟩
  · have e0 : Equiv.swap (2 : Fin 4) 3 0 = 0 := Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)
    have e1 : Equiv.swap (2 : Fin 4) 3 1 = 1 := Equiv.swap_apply_of_ne_of_ne (by decide) (by decide)
    have e2 : Equiv.swap (2 : Fin 4) 3 2 = 3 := Equiv.swap_apply_left _ _
    have e3 : Equiv.swap (2 : Fin 4) 3 3 = 2 := Equiv.swap_apply_right _ _
    simp only [Function.comp, e0, e1, e2, e3]
    exact ⟨h30, h20, h31, h21⟩

/-- The swap of two labels of a core, as a bijection of the admissible cores. -/
def swapCore (i j : Fin 4) (hij : (i = 0 ∧ j = 1) ∨ (i = 2 ∧ j = 3)) : CoreT F ≃ CoreT F where
  toFun C := ⟨C.1 ∘ Equiv.swap i j, Adm_comp_swap C.2 i j hij⟩
  invFun C := ⟨C.1 ∘ Equiv.swap i j, Adm_comp_swap C.2 i j hij⟩
  left_inv C := by
    apply Subtype.ext
    funext k
    simp [Function.comp]
  right_inv C := by
    apply Subtype.ext
    funext k
    simp [Function.comp]

theorem aPr_affine {α : F} (hα : quadraticChar F α = 1) (β : F) (C : CoreT F) :
    aPr (affCoreEquiv hα β C) = affPairEquiv (ne_zero_of_chi hα) β (aPr C) := by
  apply Subtype.ext
  simp [aPr, affCoreEquiv, affPairEquiv, affCore, affPair]

theorem cPr_affine {α : F} (hα : quadraticChar F α = 1) (β : F) (C : CoreT F) :
    cPr (affCoreEquiv hα β C) = affPairEquiv (ne_zero_of_chi hα) β (cPr C) := by
  apply Subtype.ext
  simp [cPr, affCoreEquiv, affPairEquiv, affCore, affPair]

theorem aPr_swap (C : CoreT F) :
    aPr (swapCore 0 1 (Or.inl ⟨rfl, rfl⟩) C) = swapPair (aPr C) := by
  apply Subtype.ext
  simp [aPr, swapCore, swapPair, Function.comp]

theorem cPr_swap (C : CoreT F) :
    cPr (swapCore 2 3 (Or.inr ⟨rfl, rfl⟩) C) = swapPair (cPr C) := by
  apply Subtype.ext
  simp [cPr, swapCore, swapPair, Function.comp]

end CorePairs

section CoreScore

variable {p : ℕ} [Fact p.Prime]

/-- **The residual pair maps of the two core pairs on `μ^core`** (`cor:raw-pair-maps`(b)
transported: under `μ^core` the pairs `a(C)` and `c(C)` are uniform ordered distinct pairs,
`core_marginal`): their Grams are `⪯ c₀q²` on `L²(μ^core)`. -/
theorem core_residual_gram (hm1 : quadraticChar (ZMod p) (-1) = -1) (hp2 : p ≠ 2)
    (hDLK : Sarkozy.Target.FourCycle) [Nonempty (CoreT (ZMod p))] [Nonempty (PairT (ZMod p))]
    (pr : CoreT (ZMod p) → PairT (ZMod p))
    (haff : ∀ (α : ZMod p) (hα : quadraticChar (ZMod p) α = 1) (β : ZMod p) (C : CoreT (ZMod p)),
      pr (affCoreEquiv hα β C) = affPairEquiv (ne_zero_of_chi hα) β (pr C))
    (sw : CoreT (ZMod p) ≃ CoreT (ZMod p)) (hsw : ∀ C, pr (sw C) = swapPair (pr C))
    (f : CoreT (ZMod p) → ℝ) :
    kernelForm (coreLaw (F := ZMod p)) coreLaw
        (fun C C' => ip (FiniteLaw.uniform (ZMod p × ZMod p)) (rhoV (pr C).1) (rhoV (pr C').1))
        f f ≤
      (4 / (1 - 1 / (p : ℝ)) + 2 * (1 / (p : ℝ))) * (1 / (p : ℝ)) ^ 2 * nrm coreLaw f ^ 2 := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hq : 0 < 1 - 1 / (p : ℝ) := by
    have : 1 / (p : ℝ) < 1 := by rw [div_lt_one (by linarith)]; exact hp1
    linarith
  refine gram_le_of_map (coreLaw (F := ZMod p)) (FiniteLaw.uniform (ZMod p × ZMod p))
    (fun C => rhoV (pr C).1) (by positivity) (fun G => ?_) f
  rw [core_marginal hm1 pr haff sw hsw (fun b => ip (FiniteLaw.uniform (ZMod p × ZMod p))
    (rhoV b.1) G ^ 2)]
  exact pair_residual_map hDLK hp2 G

/-- **`lem:root-square`, the first bound, for the core score** `H₀ = H(a(C), c(C'))`, with no
remaining hypothesis: under `χ(−1) = −1`, Weil and `thm:dl:K`,
`|⟨F, (K_soft∘H₀² − (1 − 2q)²K_soft)H⟩| ≤ p·256𝔯₊·c₀q²‖F‖‖H‖ = 256c₀𝔯₊q‖F‖‖H‖`.
(`H₂ = H(c(C), a(C'))` is the transpose.) -/
theorem root_square_first_core (hm1 : quadraticChar (ZMod p) (-1) = -1) (hp2 : p ≠ 2)
    (hW : Sarkozy.Labellings.WeilBound (ZMod p)) (hDLK : Sarkozy.Target.FourCycle)
    [Nonempty (CoreT (ZMod p))] [Nonempty (PairT (ZMod p))]
    (Fn Hn : CoreT (ZMod p) × PairT (ZMod p) → ℝ) :
    |kernelForm ((coreLaw (F := ZMod p)).product pairLaw) ((coreLaw (F := ZMod p)).product pairLaw)
        (fun P Q => Rk P.1 Q.2 * Rk Q.1 P.2 * pairScore (P.1.1 0, P.1.1 1) (Q.1.1 2, Q.1.1 3) ^ 2 -
          (1 - 2 / (Fintype.card (ZMod p) : ℝ)) ^ 2 * (Rk P.1 Q.2 * Rk Q.1 P.2)) Fn Hn| ≤
      (Fintype.card (ZMod p) : ℝ) *
        (256 * ((1 + etaL (ZMod p)) ^ 2 / (1 - (Fintype.card (ZMod p) : ℝ)⁻¹)) *
          ((4 / (1 - 1 / (p : ℝ)) + 2 * (1 / (p : ℝ))) * (1 / (p : ℝ)) ^ 2)) *
        nrm ((coreLaw (F := ZMod p)).product pairLaw) Fn *
        nrm ((coreLaw (F := ZMod p)).product pairLaw) Hn := by
  have hF : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hq : 0 < 1 - 1 / (p : ℝ) := by
    have : 1 / (p : ℝ) < 1 := by rw [div_lt_one (by linarith)]; exact hp1
    linarith
  have hg : 0 ≤ (4 / (1 - 1 / (p : ℝ)) + 2 * (1 / (p : ℝ))) * (1 / (p : ℝ)) ^ 2 := by positivity
  exact root_square_first_L20 hm1 hF hW hg
    (core_residual_gram hm1 hp2 hDLK aPr (fun α hα β C => aPr_affine hα β C)
      (swapCore 0 1 (Or.inl ⟨rfl, rfl⟩)) aPr_swap)
    (core_residual_gram hm1 hp2 hDLK cPr (fun α hα β C => cPr_affine hα β C)
      (swapCore 2 3 (Or.inr ⟨rfl, rfl⟩)) cPr_swap) Fn Hn

/-- **`lem:root-square`, the first bound, for the core score `H₂ = H(c(C), a(C'))`** ("`H₂` is its
transpose"), with no remaining hypothesis: the same bound `256c₀𝔯₊q`. -/
theorem root_square_first_core2 (hm1 : quadraticChar (ZMod p) (-1) = -1) (hp2 : p ≠ 2)
    (hW : Sarkozy.Labellings.WeilBound (ZMod p)) (hDLK : Sarkozy.Target.FourCycle)
    [Nonempty (CoreT (ZMod p))] [Nonempty (PairT (ZMod p))]
    (Fn Hn : CoreT (ZMod p) × PairT (ZMod p) → ℝ) :
    |kernelForm ((coreLaw (F := ZMod p)).product pairLaw) ((coreLaw (F := ZMod p)).product pairLaw)
        (fun P Q => Rk P.1 Q.2 * Rk Q.1 P.2 * pairScore (P.1.1 2, P.1.1 3) (Q.1.1 0, Q.1.1 1) ^ 2 -
          (1 - 2 / (Fintype.card (ZMod p) : ℝ)) ^ 2 * (Rk P.1 Q.2 * Rk Q.1 P.2)) Fn Hn| ≤
      (Fintype.card (ZMod p) : ℝ) *
        (256 * ((1 + etaL (ZMod p)) ^ 2 / (1 - (Fintype.card (ZMod p) : ℝ)⁻¹)) *
          ((4 / (1 - 1 / (p : ℝ)) + 2 * (1 / (p : ℝ))) * (1 / (p : ℝ)) ^ 2)) *
        nrm ((coreLaw (F := ZMod p)).product pairLaw) Fn *
        nrm ((coreLaw (F := ZMod p)).product pairLaw) Hn := by
  have hF : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hq : 0 < 1 - 1 / (p : ℝ) := by
    have : 1 / (p : ℝ) < 1 := by rw [div_lt_one (by linarith)]; exact hp1
    linarith
  have hg : 0 ≤ (4 / (1 - 1 / (p : ℝ)) + 2 * (1 / (p : ℝ))) * (1 / (p : ℝ)) ^ 2 := by positivity
  have hD : ∀ C : CoreT (ZMod p), (pairLaw (F := ZMod p)).expect (fun b => Rk C b ^ 2) ≤
      256 * ((1 + etaL (ZMod p)) ^ 2 / (1 - (Fintype.card (ZMod p) : ℝ)⁻¹)) := by
    intro C
    rw [rect_row_sq hm1 C]
    have := rmass_le hm1 hF hW C
    linarith
  exact root_square_first (coreLaw (F := ZMod p)) coreLaw_pos pairLaw Rk (fun C => (C.1 2, C.1 3))
    (fun C => (C.1 0, C.1 1)) (fun C => (cPr C).2) (fun C => (aPr C).2) hD hg
    (core_residual_gram hm1 hp2 hDLK cPr (fun α hα β C => cPr_affine hα β C)
      (swapCore 2 3 (Or.inr ⟨rfl, rfl⟩)) cPr_swap)
    (core_residual_gram hm1 hp2 hDLK aPr (fun α hα β C => aPr_affine hα β C)
      (swapCore 0 1 (Or.inl ⟨rfl, rfl⟩)) aPr_swap) Fn Hn

end CoreScore

/-! ## The second bound on W3's rectangle -/

section SecondL20

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [Nonempty (CoreT F)]
  [Nonempty (PairT F)]

omit [Nonempty (CoreT F)] in
/-- `𝖱h = 𝖱_c P₀h + (Eh)𝔯` (`𝖱 = 𝔯 ⊗ 1 + 𝖱_c`, `𝖱_c1 = 0`). -/
theorem recOp_Rk_split (h : PairT F → ℝ) (C : CoreT F) :
    recOp (pairLaw (F := F)) Rk h C =
      recOp (pairLaw (F := F)) Rc (center pairLaw h) C + rmass C * (pairLaw (F := F)).expect h := by
  unfold recOp Rc center
  have e : (fun b => (Rk C b - rmass C) * (h b - (pairLaw (F := F)).expect h)) =
      fun b => Rk C b * h b - (rmass C * h b + (pairLaw (F := F)).expect h * Rk C b) +
        rmass C * (pairLaw (F := F)).expect h := by
    funext b; ring
  rw [e, FiniteLaw.expect_add, FiniteLaw.expect_sub, FiniteLaw.expect_add,
    FiniteLaw.expect_const_mul, FiniteLaw.expect_const_mul, FiniteLaw.expect_const]
  have hr : (pairLaw (F := F)).expect (fun b => Rk C b) = rmass C := rfl
  rw [hr]
  ring

/-- **`𝖱_c^*𝔯 = 0`**: `⟨𝖱_c g, 𝔯⟩ = 0` (from W3's `adj_rmass`, `𝖱^*𝔯 = ‖𝔯‖²1`). -/
theorem ip_RcOp_rmass (hm1 : quadraticChar F (-1) = -1) (g : PairT F → ℝ) :
    ip (coreLaw (F := F)) (recOp (pairLaw (F := F)) Rc g) rmass = 0 := by
  rw [ip_comm, ← ip_recAdj]
  have h0 : recAdj (coreLaw (F := F)) Rc rmass = fun _ => 0 := by
    funext b
    have h1 := adj_rmass hm1 b
    unfold recAdj at h1 ⊢
    unfold Rc
    have e : (fun C => (Rk C b - rmass C) * rmass C) = fun C => Rk C b * rmass C - rmass C ^ 2 := by
      funext C; ring
    rw [e, FiniteLaw.expect_sub, h1, ← nrm_sq_expect]
    ring
  rw [h0]
  unfold ip
  simp only [zero_mul]
  exact FiniteLaw.expect_const _ 0

/-- **`‖𝖱‖ ≤ s`** from `‖𝔯‖ ≤ s` and `‖𝖱_c‖ ≤ c ≤ s` (proof of `lem:root-square`, second bound:
`𝖱` maps `1` to `𝔯` and `1^⊥` into `𝔯^⊥`). -/
theorem rect_norm_le (hm1 : quadraticChar F (-1) = -1) {c s : ℝ} (hc : 0 ≤ c) (hcs : c ≤ s)
    (hRc : ∀ h : PairT F → ℝ,
      nrm (coreLaw (F := F)) (recOp (pairLaw (F := F)) Rc h) ≤ c * nrm (pairLaw (F := F)) h)
    (hs : nrm (coreLaw (F := F)) rmass ≤ s) (h : PairT F → ℝ) :
    nrm (coreLaw (F := F)) (recOp (pairLaw (F := F)) Rk h) ≤ s * nrm (pairLaw (F := F)) h := by
  have hs0 : 0 ≤ s := hc.trans hcs
  set u := recOp (pairLaw (F := F)) Rc (center pairLaw h) with hu
  set a := (pairLaw (F := F)).expect h with ha
  have hsplit : recOp (pairLaw (F := F)) Rk h = fun C => u C + a * rmass C := by
    funext C; rw [recOp_Rk_split]; ring
  have horth : ip (coreLaw (F := F)) u rmass = 0 := ip_RcOp_rmass hm1 _
  have hsq : nrm (coreLaw (F := F)) (recOp (pairLaw (F := F)) Rk h) ^ 2 =
      nrm (coreLaw (F := F)) u ^ 2 + a ^ 2 * nrm (coreLaw (F := F)) rmass ^ 2 := by
    rw [hsplit, nrm_sq_eq, nrm_sq_eq, nrm_sq_eq]
    unfold ip at horth ⊢
    have e : (fun C => (u C + a * rmass C) * (u C + a * rmass C)) =
        fun C => u C * u C + (2 * a * (u C * rmass C) + a ^ 2 * (rmass C * rmass C)) := by
      funext C; ring
    rw [e, FiniteLaw.expect_add, FiniteLaw.expect_add, FiniteLaw.expect_const_mul,
      FiniteLaw.expect_const_mul, horth]
    ring
  have hu_le : nrm (coreLaw (F := F)) u ≤ c * nrm (pairLaw (F := F)) (center pairLaw h) := hRc _
  have hdec := nrm_sq_decomp (pairLaw (F := F)) h
  have h1 : nrm (coreLaw (F := F)) u ^ 2 ≤
      s ^ 2 * nrm (pairLaw (F := F)) (center pairLaw h) ^ 2 := by
    have := pow_le_pow_left₀ (nrm_nonneg _ _) hu_le 2
    have hcs2 : c ^ 2 ≤ s ^ 2 := pow_le_pow_left₀ hc hcs 2
    rw [mul_pow] at this
    nlinarith [sq_nonneg (nrm (pairLaw (F := F)) (center pairLaw h))]
  have h2 : a ^ 2 * nrm (coreLaw (F := F)) rmass ^ 2 ≤ a ^ 2 * s ^ 2 :=
    mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (nrm_nonneg _ _) hs 2) (sq_nonneg a)
  have htot : nrm (coreLaw (F := F)) (recOp (pairLaw (F := F)) Rk h) ^ 2 ≤
      (s * nrm (pairLaw (F := F)) h) ^ 2 := by
    rw [hsq, mul_pow, hdec, ← ha]
    nlinarith
  exact (abs_le_of_sq_le_sq' htot (mul_nonneg hs0 (nrm_nonneg _ _))).2

/-- **`‖K_soft‖ ≤ s²`** (`lem:swapped-rectangle`(a): `‖T[𝖱,𝖱]‖ = ‖𝖱‖²`). -/
theorem soft_norm_le (hm1 : quadraticChar F (-1) = -1) {c s : ℝ} (hc : 0 ≤ c) (hcs : c ≤ s)
    (hRc : ∀ h : PairT F → ℝ,
      nrm (coreLaw (F := F)) (recOp (pairLaw (F := F)) Rc h) ≤ c * nrm (pairLaw (F := F)) h)
    (hs : nrm (coreLaw (F := F)) rmass ≤ s) (Fn Hn : CoreT F × PairT F → ℝ) :
    |kernelForm ((coreLaw (F := F)).product pairLaw) ((coreLaw (F := F)).product pairLaw)
        (fun p q => Rk p.1 q.2 * Rk q.1 p.2) Fn Hn| ≤
      s ^ 2 * nrm ((coreLaw (F := F)).product pairLaw) Fn *
        nrm ((coreLaw (F := F)).product pairLaw) Hn := by
  have hs0 : 0 ≤ s := hc.trans hcs
  have e : kernelForm ((coreLaw (F := F)).product pairLaw) ((coreLaw (F := F)).product pairLaw)
      (fun p q => Rk p.1 q.2 * Rk q.1 p.2) Fn Hn =
      ip ((coreLaw (F := F)).product pairLaw) Fn (swapOp coreLaw pairLaw Rk Hn) := by
    rw [kernelForm_apply]
    rfl
  rw [e]
  have h1 := abs_ip_le ((coreLaw (F := F)).product pairLaw) Fn (swapOp coreLaw pairLaw Rk Hn)
  have h2 := nrm_swapOp_le (coreLaw (F := F)) pairLaw Rk hs0 (rect_norm_le hm1 hc hcs hRc hs) Hn
  calc _ ≤ _ := h1
    _ ≤ nrm ((coreLaw (F := F)).product pairLaw) Fn *
          (s ^ 2 * nrm ((coreLaw (F := F)).product pairLaw) Hn) :=
        mul_le_mul_of_nonneg_left h2 (nrm_nonneg _ _)
    _ = _ := by ring

end SecondL20

section SecondCore

variable {p : ℕ} [Fact p.Prime]

/-- **`lem:root-square`, the second bound, for the core score `H₀`**: with `‖𝔯‖ ≤ s`,
`‖𝖱_c‖ ≤ c ≤ s` (`prop:l20-rectangular`(b), (d): W3's `rmass_norm_le` with `s = s_p`, and the
rectangle gap), Weil and `thm:dl:K`,
`‖K_soft∘H₀² − K_soft‖ ≤ 4qs² + 256c₀𝔯₊q` (`q = 1/p`; the paper's `4q𝔯₂² + 256c₀𝔯₊q`). -/
theorem root_square_second_core (hm1 : quadraticChar (ZMod p) (-1) = -1) (hp2 : p ≠ 2)
    (hW : Sarkozy.Labellings.WeilBound (ZMod p)) (hDLK : Sarkozy.Target.FourCycle)
    [Nonempty (CoreT (ZMod p))] [Nonempty (PairT (ZMod p))] {c s : ℝ} (hc : 0 ≤ c) (hcs : c ≤ s)
    (hRc : ∀ h : PairT (ZMod p) → ℝ,
      nrm (coreLaw (F := ZMod p)) (recOp (pairLaw (F := ZMod p)) Rc h) ≤
        c * nrm (pairLaw (F := ZMod p)) h)
    (hs : nrm (coreLaw (F := ZMod p)) rmass ≤ s) (Fn Hn : CoreT (ZMod p) × PairT (ZMod p) → ℝ) :
    |kernelForm ((coreLaw (F := ZMod p)).product pairLaw) ((coreLaw (F := ZMod p)).product pairLaw)
        (fun P Q => Rk P.1 Q.2 * Rk Q.1 P.2 * pairScore (P.1.1 0, P.1.1 1) (Q.1.1 2, Q.1.1 3) ^ 2 -
          Rk P.1 Q.2 * Rk Q.1 P.2) Fn Hn| ≤
      (4 * (1 / (p : ℝ)) * s ^ 2 + (Fintype.card (ZMod p) : ℝ) *
        (256 * ((1 + etaL (ZMod p)) ^ 2 / (1 - (Fintype.card (ZMod p) : ℝ)⁻¹)) *
          ((4 / (1 - 1 / (p : ℝ)) + 2 * (1 / (p : ℝ))) * (1 / (p : ℝ)) ^ 2))) *
        nrm ((coreLaw (F := ZMod p)).product pairLaw) Fn *
        nrm ((coreLaw (F := ZMod p)).product pairLaw) Hn := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hq0 : (0 : ℝ) ≤ 1 / (p : ℝ) := by positivity
  have hq1 : 1 / (p : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  have hcard : (Fintype.card (ZMod p) : ℝ) = p := by rw [ZMod.card]
  refine root_square_second ((coreLaw (F := ZMod p)).product pairLaw)
    (fun P Q => Rk P.1 Q.2 * Rk Q.1 P.2)
    (fun P Q => pairScore (P.1.1 0, P.1.1 1) (Q.1.1 2, Q.1.1 3)) hq0 hq1
    (soft_norm_le hm1 hc hcs hRc hs) (fun f g => ?_) Fn Hn
  have h := root_square_first_core hm1 hp2 hW hDLK f g
  rw [hcard] at h
  rw [show (1 : ℝ) - 2 * (1 / (p : ℝ)) = 1 - 2 / (p : ℝ) by ring]
  rw [hcard]
  exact h

/-- **`lem:root-square`, the second bound, for `H₂ = H(c(C), a(C'))`**: as
`root_square_second_core`. -/
theorem root_square_second_core2 (hm1 : quadraticChar (ZMod p) (-1) = -1) (hp2 : p ≠ 2)
    (hW : Sarkozy.Labellings.WeilBound (ZMod p)) (hDLK : Sarkozy.Target.FourCycle)
    [Nonempty (CoreT (ZMod p))] [Nonempty (PairT (ZMod p))] {c s : ℝ} (hc : 0 ≤ c) (hcs : c ≤ s)
    (hRc : ∀ h : PairT (ZMod p) → ℝ,
      nrm (coreLaw (F := ZMod p)) (recOp (pairLaw (F := ZMod p)) Rc h) ≤
        c * nrm (pairLaw (F := ZMod p)) h)
    (hs : nrm (coreLaw (F := ZMod p)) rmass ≤ s) (Fn Hn : CoreT (ZMod p) × PairT (ZMod p) → ℝ) :
    |kernelForm ((coreLaw (F := ZMod p)).product pairLaw) ((coreLaw (F := ZMod p)).product pairLaw)
        (fun P Q => Rk P.1 Q.2 * Rk Q.1 P.2 * pairScore (P.1.1 2, P.1.1 3) (Q.1.1 0, Q.1.1 1) ^ 2 -
          Rk P.1 Q.2 * Rk Q.1 P.2) Fn Hn| ≤
      (4 * (1 / (p : ℝ)) * s ^ 2 + (Fintype.card (ZMod p) : ℝ) *
        (256 * ((1 + etaL (ZMod p)) ^ 2 / (1 - (Fintype.card (ZMod p) : ℝ)⁻¹)) *
          ((4 / (1 - 1 / (p : ℝ)) + 2 * (1 / (p : ℝ))) * (1 / (p : ℝ)) ^ 2))) *
        nrm ((coreLaw (F := ZMod p)).product pairLaw) Fn *
        nrm ((coreLaw (F := ZMod p)).product pairLaw) Hn := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hq0 : (0 : ℝ) ≤ 1 / (p : ℝ) := by positivity
  have hq1 : 1 / (p : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  have hcard : (Fintype.card (ZMod p) : ℝ) = p := by rw [ZMod.card]
  refine root_square_second ((coreLaw (F := ZMod p)).product pairLaw)
    (fun P Q => Rk P.1 Q.2 * Rk Q.1 P.2)
    (fun P Q => pairScore (P.1.1 2, P.1.1 3) (Q.1.1 0, Q.1.1 1)) hq0 hq1
    (soft_norm_le hm1 hc hcs hRc hs) (fun f g => ?_) Fn Hn
  have h := root_square_first_core2 hm1 hp2 hW hDLK f g
  rw [hcard] at h
  rw [show (1 : ℝ) - 2 * (1 / (p : ℝ)) = 1 - 2 / (p : ℝ) by ring]
  rw [hcard]
  exact h

/-- **`‖K_soft‖ ≤ s²` in the variables `(b, C)`** (`T[𝖱^*, 𝖱^*]`, `‖𝖱^*‖ = ‖𝖱‖ ≤ s`). -/
theorem soft_norm_le_private (hm1 : quadraticChar (ZMod p) (-1) = -1)
    [Nonempty (CoreT (ZMod p))] [Nonempty (PairT (ZMod p))] {c s : ℝ} (hc : 0 ≤ c) (hcs : c ≤ s)
    (hRc : ∀ h : PairT (ZMod p) → ℝ,
      nrm (coreLaw (F := ZMod p)) (recOp (pairLaw (F := ZMod p)) Rc h) ≤
        c * nrm (pairLaw (F := ZMod p)) h)
    (hs : nrm (coreLaw (F := ZMod p)) rmass ≤ s) (Fn Hn : PairT (ZMod p) × CoreT (ZMod p) → ℝ) :
    |kernelForm ((pairLaw (F := ZMod p)).product coreLaw) ((pairLaw (F := ZMod p)).product coreLaw)
        (fun P Q => Rk Q.2 P.1 * Rk P.2 Q.1) Fn Hn| ≤
      s ^ 2 * nrm ((pairLaw (F := ZMod p)).product coreLaw) Fn *
        nrm ((pairLaw (F := ZMod p)).product coreLaw) Hn := by
  have hs0 : 0 ≤ s := hc.trans hcs
  -- `‖𝖱^*‖ ≤ s`
  have hadj : ∀ g : CoreT (ZMod p) → ℝ, nrm (pairLaw (F := ZMod p))
      (recOp (coreLaw (F := ZMod p)) (fun b C => Rk C b) g) ≤ s * nrm (coreLaw (F := ZMod p)) g :=
    fun g => nrm_recAdj_le (coreLaw (F := ZMod p)) pairLaw Rk hs0 (rect_norm_le hm1 hc hcs hRc hs) g
  have e : kernelForm ((pairLaw (F := ZMod p)).product coreLaw)
      ((pairLaw (F := ZMod p)).product coreLaw) (fun P Q => Rk Q.2 P.1 * Rk P.2 Q.1) Fn Hn =
      ip ((pairLaw (F := ZMod p)).product coreLaw) Fn
        (swapOp pairLaw coreLaw (fun b C => Rk C b) Hn) := by
    rw [kernelForm_apply]
    rfl
  rw [e]
  have h1 := abs_ip_le ((pairLaw (F := ZMod p)).product coreLaw) Fn
    (swapOp pairLaw coreLaw (fun b C => Rk C b) Hn)
  have h2 := nrm_swapOp_le (pairLaw (F := ZMod p)) coreLaw (fun b C => Rk C b) hs0 hadj Hn
  calc _ ≤ _ := h1
    _ ≤ nrm ((pairLaw (F := ZMod p)).product coreLaw) Fn *
          (s ^ 2 * nrm ((pairLaw (F := ZMod p)).product coreLaw) Hn) :=
        mul_le_mul_of_nonneg_left h2 (nrm_nonneg _ _)
    _ = _ := by ring

/-- **`lem:root-square`, the second bound, for the private score `H₁ = H(b, b')`**. -/
theorem root_square_second_private (hm1 : quadraticChar (ZMod p) (-1) = -1) (hp2 : p ≠ 2)
    (hW : Sarkozy.Labellings.WeilBound (ZMod p)) (hDLK : Sarkozy.Target.FourCycle)
    [Nonempty (CoreT (ZMod p))] [Nonempty (PairT (ZMod p))] {c s : ℝ} (hc : 0 ≤ c) (hcs : c ≤ s)
    (hRc : ∀ h : PairT (ZMod p) → ℝ,
      nrm (coreLaw (F := ZMod p)) (recOp (pairLaw (F := ZMod p)) Rc h) ≤
        c * nrm (pairLaw (F := ZMod p)) h)
    (hs : nrm (coreLaw (F := ZMod p)) rmass ≤ s) (Fn Hn : PairT (ZMod p) × CoreT (ZMod p) → ℝ) :
    |kernelForm ((pairLaw (F := ZMod p)).product coreLaw) ((pairLaw (F := ZMod p)).product coreLaw)
        (fun P Q => Rk Q.2 P.1 * Rk P.2 Q.1 * pairScore P.1.1 Q.1.1 ^ 2 -
          Rk Q.2 P.1 * Rk P.2 Q.1) Fn Hn| ≤
      (4 * (1 / (p : ℝ)) * s ^ 2 + (Fintype.card (ZMod p) : ℝ) *
        (256 * ((1 + etaL (ZMod p)) ^ 2 / (1 - (Fintype.card (ZMod p) : ℝ)⁻¹)) *
          ((4 / (1 - 1 / (p : ℝ)) + 2 * (1 / (p : ℝ))) * (1 / (p : ℝ)) ^ 2))) *
        nrm ((pairLaw (F := ZMod p)).product coreLaw) Fn *
        nrm ((pairLaw (F := ZMod p)).product coreLaw) Hn := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hq0 : (0 : ℝ) ≤ 1 / (p : ℝ) := by positivity
  have hq1 : 1 / (p : ℝ) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
  have hcard : (Fintype.card (ZMod p) : ℝ) = p := by rw [ZMod.card]
  refine root_square_second ((pairLaw (F := ZMod p)).product coreLaw)
    (fun P Q => Rk Q.2 P.1 * Rk P.2 Q.1)
    (fun P Q => pairScore P.1.1 Q.1.1) hq0 hq1
    (soft_norm_le_private hm1 hc hcs hRc hs) (fun f g => ?_) Fn Hn
  have h := root_square_first_private hm1 hp2 hW hDLK f g
  rw [hcard] at h
  rw [show (1 : ℝ) - 2 * (1 / (p : ℝ)) = 1 - 2 / (p : ℝ) by ring]
  rw [hcard]
  exact h

end SecondCore

/-! ## The square price of the soft kernel: the average of the three scores -/

section SoftV

/-- **Swapping the two factors of a product law** preserves kernel forms. -/
theorem kernelForm_prodComm {X Y : Type*} [Fintype X] [Fintype Y] (α : FiniteLaw X)
    (β : FiniteLaw Y) (K : X × Y → X × Y → ℝ) (Fn Hn : X × Y → ℝ) :
    kernelForm (α.product β) (α.product β) K Fn Hn =
      kernelForm (β.product α) (β.product α) (fun P Q => K (P.2, P.1) (Q.2, Q.1))
        (fun P => Fn (P.2, P.1)) (fun P => Hn (P.2, P.1)) := by
  simp only [kernelForm, LinearMap.mk₂_apply]
  rw [← Equiv.sum_comp (Equiv.prodComm Y X)]
  refine Finset.sum_congr rfl fun P _ => ?_
  rw [← Equiv.sum_comp (Equiv.prodComm Y X)]
  refine Finset.sum_congr rfl fun Q _ => ?_
  simp only [Equiv.prodComm_apply, FiniteLaw.product, Prod.swap]
  ring

/-- The kernel form is linear in the kernel (three terms). -/
theorem kernelForm_add3 {X : Type*} [Fintype X] (ν : FiniteLaw X) (K L N : X → X → ℝ)
    (a b c : ℝ) (f g : X → ℝ) :
    kernelForm ν ν (fun x y => a * K x y + b * L x y + c * N x y) f g =
      a * kernelForm ν ν K f g + b * kernelForm ν ν L f g + c * kernelForm ν ν N f g := by
  simp only [kernelForm, LinearMap.mk₂_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring

theorem nrm_prodComm {X Y : Type*} [Fintype X] [Fintype Y] (α : FiniteLaw X) (β : FiniteLaw Y)
    (Fn : X × Y → ℝ) : nrm (β.product α) (fun P => Fn (P.2, P.1)) = nrm (α.product β) Fn := by
  unfold nrm ip
  congr 1
  simp only [FiniteLaw.expect, FiniteLaw.product]
  rw [← Equiv.sum_comp (Equiv.prodComm X Y)]
  refine Finset.sum_congr rfl fun P _ => ?_
  simp only [Equiv.prodComm_apply, Prod.fst_swap, Prod.snd_swap]
  ring

variable {p : ℕ} [Fact p.Prime]

/-- **The square price of the soft kernel** (`lem:root-square` averaged over the three scores, the
first term of `ε^raw_sq` in `lem:root-normalization`(a)): with `V = (H₀² + H₁² + H₂²)/3` on the
pairs of halves `(C, b), (C', b')`, `H₀ = H(a, c')`, `H₁ = H(b, b')`, `H₂ = H(c, a')`,
`‖K_soft∘V − K_soft‖ ≤ 4qs² + 256c₀𝔯₊q`, under the hypotheses of `root_square_second_core`. -/
theorem soft_sq_price (hm1 : quadraticChar (ZMod p) (-1) = -1) (hp2 : p ≠ 2)
    (hW : Sarkozy.Labellings.WeilBound (ZMod p)) (hDLK : Sarkozy.Target.FourCycle)
    [Nonempty (CoreT (ZMod p))] [Nonempty (PairT (ZMod p))] {c s : ℝ} (hc : 0 ≤ c) (hcs : c ≤ s)
    (hRc : ∀ h : PairT (ZMod p) → ℝ,
      nrm (coreLaw (F := ZMod p)) (recOp (pairLaw (F := ZMod p)) Rc h) ≤
        c * nrm (pairLaw (F := ZMod p)) h)
    (hs : nrm (coreLaw (F := ZMod p)) rmass ≤ s) (Fn Hn : CoreT (ZMod p) × PairT (ZMod p) → ℝ) :
    |kernelForm ((coreLaw (F := ZMod p)).product pairLaw) ((coreLaw (F := ZMod p)).product pairLaw)
        (fun P Q => Rk P.1 Q.2 * Rk Q.1 P.2 *
            ((1 / 3) * (pairScore (P.1.1 0, P.1.1 1) (Q.1.1 2, Q.1.1 3) ^ 2 +
              pairScore P.2.1 Q.2.1 ^ 2 + pairScore (P.1.1 2, P.1.1 3) (Q.1.1 0, Q.1.1 1) ^ 2)) -
          Rk P.1 Q.2 * Rk Q.1 P.2) Fn Hn| ≤
      (4 * (1 / (p : ℝ)) * s ^ 2 + (Fintype.card (ZMod p) : ℝ) *
        (256 * ((1 + etaL (ZMod p)) ^ 2 / (1 - (Fintype.card (ZMod p) : ℝ)⁻¹)) *
          ((4 / (1 - 1 / (p : ℝ)) + 2 * (1 / (p : ℝ))) * (1 / (p : ℝ)) ^ 2))) *
        nrm ((coreLaw (F := ZMod p)).product pairLaw) Fn *
        nrm ((coreLaw (F := ZMod p)).product pairLaw) Hn := by
  set B := (4 * (1 / (p : ℝ)) * s ^ 2 + (Fintype.card (ZMod p) : ℝ) *
    (256 * ((1 + etaL (ZMod p)) ^ 2 / (1 - (Fintype.card (ZMod p) : ℝ)⁻¹)) *
      ((4 / (1 - 1 / (p : ℝ)) + 2 * (1 / (p : ℝ))) * (1 / (p : ℝ)) ^ 2))) with hB
  set N := nrm ((coreLaw (F := ZMod p)).product pairLaw) Fn *
    nrm ((coreLaw (F := ZMod p)).product pairLaw) Hn with hN
  set μ := (coreLaw (F := ZMod p)).product (pairLaw (F := ZMod p)) with hμ
  set K0 : CoreT (ZMod p) × PairT (ZMod p) → CoreT (ZMod p) × PairT (ZMod p) → ℝ :=
    fun P Q => Rk P.1 Q.2 * Rk Q.1 P.2 *
      pairScore (P.1.1 0, P.1.1 1) (Q.1.1 2, Q.1.1 3) ^ 2 - Rk P.1 Q.2 * Rk Q.1 P.2 with hK0
  set K1 : CoreT (ZMod p) × PairT (ZMod p) → CoreT (ZMod p) × PairT (ZMod p) → ℝ :=
    fun P Q => Rk P.1 Q.2 * Rk Q.1 P.2 * pairScore P.2.1 Q.2.1 ^ 2 - Rk P.1 Q.2 * Rk Q.1 P.2
    with hK1
  set K2 : CoreT (ZMod p) × PairT (ZMod p) → CoreT (ZMod p) × PairT (ZMod p) → ℝ :=
    fun P Q => Rk P.1 Q.2 * Rk Q.1 P.2 *
      pairScore (P.1.1 2, P.1.1 3) (Q.1.1 0, Q.1.1 1) ^ 2 - Rk P.1 Q.2 * Rk Q.1 P.2 with hK2
  have e : (fun P Q => Rk P.1 Q.2 * Rk Q.1 P.2 *
            ((1 / 3) * (pairScore (P.1.1 0, P.1.1 1) (Q.1.1 2, Q.1.1 3) ^ 2 +
              pairScore P.2.1 Q.2.1 ^ 2 + pairScore (P.1.1 2, P.1.1 3) (Q.1.1 0, Q.1.1 1) ^ 2)) -
          Rk P.1 Q.2 * Rk Q.1 P.2) =
      fun P Q => (1 / 3 : ℝ) * K0 P Q + (1 / 3 : ℝ) * K1 P Q + (1 / 3 : ℝ) * K2 P Q := by
    funext P Q
    rw [hK0, hK1, hK2]
    ring
  rw [e, kernelForm_add3]
  have b0 := root_square_second_core hm1 hp2 hW hDLK hc hcs hRc hs Fn Hn
  have b2 := root_square_second_core2 hm1 hp2 hW hDLK hc hcs hRc hs Fn Hn
  have b1 : |kernelForm μ μ K1 Fn Hn| ≤ B * N := by
    rw [hμ, kernelForm_prodComm]
    have h := root_square_second_private hm1 hp2 hW hDLK hc hcs hRc hs
      (fun P => Fn (P.2, P.1)) (fun P => Hn (P.2, P.1))
    rw [nrm_prodComm, nrm_prodComm] at h
    have ek : (fun P Q : PairT (ZMod p) × CoreT (ZMod p) => K1 (P.2, P.1) (Q.2, Q.1)) =
        fun P Q => Rk Q.2 P.1 * Rk P.2 Q.1 * pairScore P.1.1 Q.1.1 ^ 2 -
          Rk Q.2 P.1 * Rk P.2 Q.1 := by
      funext P Q
      rw [hK1]
      ring
    rw [ek]
    calc _ ≤ _ := h
      _ = B * N := by rw [hB, hN]; ring
  have hb0 : |kernelForm μ μ K0 Fn Hn| ≤ B * N := by
    calc _ ≤ _ := b0
      _ = B * N := by rw [hB, hN]; ring
  have hb2 : |kernelForm μ μ K2 Fn Hn| ≤ B * N := by
    calc _ ≤ _ := b2
      _ = B * N := by rw [hB, hN]; ring
  have t := abs_add_le
    ((1 / 3 : ℝ) * kernelForm μ μ K0 Fn Hn + (1 / 3 : ℝ) * kernelForm μ μ K1 Fn Hn)
    ((1 / 3 : ℝ) * kernelForm μ μ K2 Fn Hn)
  have t2 := abs_add_le ((1 / 3 : ℝ) * kernelForm μ μ K0 Fn Hn)
    ((1 / 3 : ℝ) * kernelForm μ μ K1 Fn Hn)
  rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 3)] at t2
  rw [abs_mul (1 / 3 : ℝ), abs_of_pos (by norm_num : (0 : ℝ) < 1 / 3)] at t
  calc _ ≤ _ := t
    _ ≤ B * N := by linarith
    _ = _ := by rw [hB, hN]; ring

end SoftV

/-! ## The square price in the actual half chart -/

section Actual

/-- **Conditioning an absolute bound** (`lem:restriction`(b), the compression `1/h_p`): if
`|⟨G, KG⟩_ν| ≤ c‖G‖²_ν` for all `G`, then `|⟨f, Kf⟩_{ν(·|E)}| ≤ (c/P(E))‖f‖²_{ν(·|E)}`. -/
theorem condLaw_abs {Ω : Type*} [Fintype Ω] (ν : FiniteLaw Ω) (E : Ω → Prop) [DecidablePred E]
    (hE : 0 < prob ν E) (K : Ω → Ω → ℝ) {c : ℝ}
    (hK : ∀ G : Ω → ℝ, |kernelForm ν ν K G G| ≤ c * nrm ν G ^ 2) (f : Ω → ℝ) :
    |kernelForm (condLaw ν E hE) (condLaw ν E hE) K f f| ≤
      c / prob ν E * nrm (condLaw ν E hE) f ^ 2 := by
  rw [kernelForm_condLaw]
  have h := hK (fun ω => (if E ω then 1 else 0) * f ω)
  rw [nrm_condLaw ν E hE] at h
  have hinv : 0 < (prob ν E)⁻¹ * (prob ν E)⁻¹ := mul_pos (inv_pos.mpr hE) (inv_pos.mpr hE)
  rw [abs_mul, abs_of_pos hinv]
  calc (prob ν E)⁻¹ * (prob ν E)⁻¹ * |kernelForm ν ν K (fun ω => (if E ω then 1 else 0) * f ω)
        (fun ω => (if E ω then 1 else 0) * f ω)|
      ≤ (prob ν E)⁻¹ * (prob ν E)⁻¹ * (c * (prob ν E * nrm (condLaw ν E hE) f ^ 2)) :=
        mul_le_mul_of_nonneg_left h hinv.le
    _ = c / prob ν E * nrm (condLaw ν E hE) f ^ 2 := by
        field_simp

variable {p : ℕ} [Fact p.Prime]

/-- **The square price in the fixed half chart** (`lem:root-normalization`(a), "Squares", the
soft term): on `L²(μ_p)` (W3's `halfLaw`, `μ^core ⊗ μ^pair` conditioned on `b ∩ C = ∅`, of
probability `h_p`), `|⟨f, (K_soft∘V − K_soft)f⟩| ≤ ((4qs² + 256c₀𝔯₊q)/h_p)‖f‖²`. With
`h_p ≥ h'_p` this is the term `(4q𝔯₂² + 256c₀𝔯₊q)/h'_p` of `ε^raw_sq`. -/
theorem actual_sq_price (hm1 : quadraticChar (ZMod p) (-1) = -1) (hp2 : p ≠ 2)
    (hW : Sarkozy.Labellings.WeilBound (ZMod p)) (hDLK : Sarkozy.Target.FourCycle)
    [Nonempty (CoreT (ZMod p))] [Nonempty (PairT (ZMod p))] (h6 : 6 ≤ Fintype.card (ZMod p))
    {c s : ℝ} (hc : 0 ≤ c) (hcs : c ≤ s)
    (hRc : ∀ h : PairT (ZMod p) → ℝ,
      nrm (coreLaw (F := ZMod p)) (recOp (pairLaw (F := ZMod p)) Rc h) ≤
        c * nrm (pairLaw (F := ZMod p)) h)
    (hs : nrm (coreLaw (F := ZMod p)) rmass ≤ s) (f : CoreT (ZMod p) × PairT (ZMod p) → ℝ) :
    |kernelForm (halfLaw h6) (halfLaw h6)
        (fun P Q => Rk P.1 Q.2 * Rk Q.1 P.2 *
            ((1 / 3) * (pairScore (P.1.1 0, P.1.1 1) (Q.1.1 2, Q.1.1 3) ^ 2 +
              pairScore P.2.1 Q.2.1 ^ 2 + pairScore (P.1.1 2, P.1.1 3) (Q.1.1 0, Q.1.1 1) ^ 2)) -
          Rk P.1 Q.2 * Rk Q.1 P.2) f f| ≤
      (4 * (1 / (p : ℝ)) * s ^ 2 + (Fintype.card (ZMod p) : ℝ) *
        (256 * ((1 + etaL (ZMod p)) ^ 2 / (1 - (Fintype.card (ZMod p) : ℝ)⁻¹)) *
          ((4 / (1 - 1 / (p : ℝ)) + 2 * (1 / (p : ℝ))) * (1 / (p : ℝ)) ^ 2))) /
        prob ((coreLaw (F := ZMod p)).product (pairLaw (F := ZMod p))) Avoid *
        nrm (halfLaw h6) f ^ 2 := by
  unfold halfLaw
  refine condLaw_abs _ Avoid (hP_pos h6) _ (fun G => ?_) f
  have h := soft_sq_price hm1 hp2 hW hDLK hc hcs hRc hs G G
  calc _ ≤ _ := h
    _ = _ := by ring

end Actual

/-! ## The square price with the paper's `𝔯₂ = s_p` -/

section SquarePriceSp

variable {p : ℕ} [Fact p.Prime]

/-- `‖𝔯‖₂ ≤ s_p` (`prop:l20-rectangular`(d)): W3's `rmass_norm_le` with `η = 2q + 11r`
(`Kbar_dev`, Weil) and the mean bound `E(\bar𝖪 − 1) ≤ 𝔪₊` (`prop:l20-rank4`, a hypothesis). -/
theorem rmass_norm_le_sP (hm1 : quadraticChar (ZMod p) (-1) = -1) (hp2 : p ≠ 2)
    (hW : Sarkozy.Labellings.WeilBound (ZMod p)) [Nonempty (CoreT (ZMod p))]
    [Nonempty (PairT (ZMod p))] {m : ℝ}
    (hm : (coreLaw (F := ZMod p)).expect (fun C => Kbar C.1 - 1) ≤ m) :
    nrm (coreLaw (F := ZMod p)) rmass ≤ sP (ZMod p) m := by
  have hF : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  exact rmass_norm_le hm1 (η := etaL (ZMod p)) (fun C => Kbar_dev hF hW C.2.1) hm

/-- **The square price in the half chart with `𝔯₂ = s_p`** (`lem:root-normalization`(a),
"Squares", the soft term): under Weil, `thm:dl:K`, the mean bound `E(\bar𝖪 − 1) ≤ 𝔪₊` and the
rectangle bound `‖𝖱_c‖ ≤ c ≤ s_p` (`prop:l20-rectangular`(b), the paper's gate
`k₄r + N_A < 1 ≤ s_p`), on `L²(μ_p)`:
`|⟨f, (K_soft∘V − K_soft)f⟩| ≤ ((4q s_p² + 256c₀𝔯₊q)/h_p)‖f‖²`. -/
theorem actual_sq_price_sP (hm1 : quadraticChar (ZMod p) (-1) = -1) (hp2 : p ≠ 2)
    (hW : Sarkozy.Labellings.WeilBound (ZMod p)) (hDLK : Sarkozy.Target.FourCycle)
    [Nonempty (CoreT (ZMod p))] [Nonempty (PairT (ZMod p))] (h6 : 6 ≤ Fintype.card (ZMod p))
    {m c : ℝ} (hm : (coreLaw (F := ZMod p)).expect (fun C => Kbar C.1 - 1) ≤ m)
    (hc : 0 ≤ c) (hcs : c ≤ sP (ZMod p) m)
    (hRc : ∀ h : PairT (ZMod p) → ℝ,
      nrm (coreLaw (F := ZMod p)) (recOp (pairLaw (F := ZMod p)) Rc h) ≤
        c * nrm (pairLaw (F := ZMod p)) h)
    (f : CoreT (ZMod p) × PairT (ZMod p) → ℝ) :
    |kernelForm (halfLaw h6) (halfLaw h6)
        (fun P Q => Rk P.1 Q.2 * Rk Q.1 P.2 *
            ((1 / 3) * (pairScore (P.1.1 0, P.1.1 1) (Q.1.1 2, Q.1.1 3) ^ 2 +
              pairScore P.2.1 Q.2.1 ^ 2 + pairScore (P.1.1 2, P.1.1 3) (Q.1.1 0, Q.1.1 1) ^ 2)) -
          Rk P.1 Q.2 * Rk Q.1 P.2) f f| ≤
      (4 * (1 / (p : ℝ)) * sP (ZMod p) m ^ 2 + (Fintype.card (ZMod p) : ℝ) *
        (256 * ((1 + etaL (ZMod p)) ^ 2 / (1 - (Fintype.card (ZMod p) : ℝ)⁻¹)) *
          ((4 / (1 - 1 / (p : ℝ)) + 2 * (1 / (p : ℝ))) * (1 / (p : ℝ)) ^ 2))) /
        prob ((coreLaw (F := ZMod p)).product (pairLaw (F := ZMod p))) Avoid *
        nrm (halfLaw h6) f ^ 2 :=
  actual_sq_price hm1 hp2 hW hDLK h6 hc hcs hRc (rmass_norm_le_sP hm1 hp2 hW hm) f

end SquarePriceSp

end Sarkozy.PositiveRoots
