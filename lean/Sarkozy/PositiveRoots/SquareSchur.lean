module

public import Sarkozy.PositiveRoots.Square
public import Sarkozy.Cuts.Schur
public import Sarkozy.ProbabilityConstructions

@[expose] public section

/-!
# Square of a score on the rectangle, the first bound (`lem:root-square`)

`paper/sections/20b_positive_roots.tex`, `lem:root-square`, first bound:
`‖K_soft∘H_j² − (1 − 2q)²K_soft‖ ≤ 256c₀𝔯₊q`, for a core score. The proof of the paper, step by
step:

* the identity `H₀² = (1 − 2q)² + q^{-1}⟨ρ_a, ρ_{c'}⟩` (`Square.pairScore_sq_split`), so that
  `K_soft∘H₀² − (1 − 2q)²K_soft = q^{-1} T[𝖱,𝖱]∘⟨ρ_a, ρ_{c'}⟩`;
* `lem:swapped-rectangle`(d) (`Cuts.swap_multiplier_norm`): this is
  `q^{-1}(𝒴_a ⊗ I) Swap (𝒴_c^* ⊗ I)`, of norm `≤ q^{-1}‖𝒴_a‖‖𝒴_c‖`, where `𝒴_a` has the kernel
  `𝖱(C; b)ρ_{a(C)}(s)`;
* `prodMap_norm`: **`‖𝒴_a‖² ≤ D a`** by the positive Schur order of `lem:swapped-rectangle`(b)
  (`Cuts.schur_operator_le`): `𝒴_a𝒴_a^*` is the pointwise product of the positive semidefinite
  kernel `𝖱𝖱^*` (diagonal `E_b𝖱(C; b)² ≤ D`; in the paper `= 256𝔯(C) ≤ 256𝔯₊`) with the Gram of
  the residual pair map, which lies between `0` and `a` (in the paper `a = c₀q²`,
  `cor:raw-pair-maps`(b));
* **`root_square_first`**: hence
  `|⟨F, (K_soft∘H₀² − (1 − 2q)²K_soft)H⟩| ≤ n·D·a‖F‖‖H‖`, which is `256c₀𝔯₊q‖F‖‖H‖` at
  `D = 256𝔯₊`, `a = c₀q²`, `n = 1/q` (`root_square_first_paper`).

**Hypotheses.** The row bound `E_b𝖱(C; b)² ≤ D` (`hD`; the paper: `𝖱 ∈ {0, 256}` and
`𝔯 ≤ 𝔯₊`, `prop:l20-rectangular`(d)), and the Gram bound of the residual pair map on
`L²(μ^core)` (`hWa`, `hWc`): `cor:raw-pair-maps`(b) is proved from `thm:dl:K` in
`DLK.raw_pair_remainder` for a uniform distinct pair; its transport to `μ^core` (under which the
pairs `a` and `c` of a core are uniform distinct pairs) is not formalized. The law of the cores
must have full support (`hα`; the uniform law of the admissible cores does). The private score
is the same statement for the transposed rectangle `𝖱^*` (`lem:swapped-rectangle`, last
sentence), and is not repeated.
-/

namespace Sarkozy.PositiveRoots

open Finset Sarkozy Sarkozy.Cuts Sarkozy.Recentering Matrix

variable {X Y S : Type*} [Fintype X] [Fintype Y] [Fintype S]

/-- The Gram kernel of the rows of `A`: `Γ(x, x') = E_y A(x; y)A(x'; y)`. -/
noncomputable def rowGram (β : FiniteLaw Y) (A : X → Y → ℝ) (x x' : X) : ℝ :=
  β.expect (fun y => A x y * A x' y)

theorem rowGram_posSemidef (β : FiniteLaw Y) (A : X → Y → ℝ) :
    (Matrix.of (rowGram β A)).PosSemidef := by
  refine posSemidef_of_quad (fun i j => ?_) (fun v => ?_)
  · simp only [Matrix.of_apply, rowGram]
    exact β.expect_congr fun y => mul_comm _ _
  · have e : ∑ i, ∑ j, v i * Matrix.of (rowGram β A) i j * v j =
        ∑ y, β.weight y * (∑ i, v i * A i y) ^ 2 := by
      calc ∑ i, ∑ j, v i * Matrix.of (rowGram β A) i j * v j
          = ∑ i, ∑ j, ∑ y, β.weight y * (v i * A i y) * (v j * A j y) := by
            refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
            simp only [Matrix.of_apply, rowGram, FiniteLaw.expect, Finset.mul_sum, Finset.sum_mul]
            exact Finset.sum_congr rfl fun y _ => by ring
        _ = ∑ i, ∑ y, ∑ j, β.weight y * (v i * A i y) * (v j * A j y) :=
            Finset.sum_congr rfl fun i _ => Finset.sum_comm
        _ = ∑ y, ∑ i, ∑ j, β.weight y * (v i * A i y) * (v j * A j y) := Finset.sum_comm
        _ = ∑ y, β.weight y * (∑ i, v i * A i y) ^ 2 := by
            refine Finset.sum_congr rfl fun y _ => ?_
            rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl fun j _ => by ring
    rw [e]
    exact Finset.sum_nonneg fun y _ => mul_nonneg (β.nonneg y) (sq_nonneg _)

/-- `‖𝒴^*f‖² = ⟨f, (Γ∘W)f⟩` with `Γ = 𝖱𝖱^*` and `W = ⟨φ_x, φ_{x'}⟩`. -/
theorem nrm_prodAdj_sq (α : FiniteLaw X) (β : FiniteLaw Y) (π : FiniteLaw S) (A : X → Y → ℝ)
    (φ : X → S → ℝ) (f : X → ℝ) :
    nrm (β.product π) (recAdj α (fun x q => A x q.1 * φ x q.2) f) ^ 2 =
      kernelForm α α (fun x x' => rowGram β A x x' * ip π (φ x) (φ x')) f f := by
  rw [nrm_sq_expect]
  calc (β.product π).expect (fun q => recAdj α (fun x q => A x q.1 * φ x q.2) f q ^ 2)
      = ∑ y, ∑ s, ∑ x, ∑ x', (β.weight y * π.weight s) *
          ((α.weight x * (A x y * φ x s * f x)) * (α.weight x' * (A x' y * φ x' s * f x'))) := by
        simp only [FiniteLaw.expect, FiniteLaw.product, Fintype.sum_prod_type, recAdj]
        refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun s _ => ?_
        rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        rw [Finset.mul_sum]
    _ = ∑ x, ∑ x', ∑ y, ∑ s, (β.weight y * π.weight s) *
          ((α.weight x * (A x y * φ x s * f x)) * (α.weight x' * (A x' y * φ x' s * f x'))) := by
        set T : Y → S → X → X → ℝ := fun y s x x' => (β.weight y * π.weight s) *
          ((α.weight x * (A x y * φ x s * f x)) * (α.weight x' * (A x' y * φ x' s * f x')))
          with hT
        calc ∑ y, ∑ s, ∑ x, ∑ x', T y s x x' = ∑ y, ∑ x, ∑ s, ∑ x', T y s x x' :=
              Finset.sum_congr rfl fun y _ => Finset.sum_comm
          _ = ∑ y, ∑ x, ∑ x', ∑ s, T y s x x' :=
              Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun x _ => Finset.sum_comm
          _ = ∑ x, ∑ y, ∑ x', ∑ s, T y s x x' := Finset.sum_comm
          _ = ∑ x, ∑ x', ∑ y, ∑ s, T y s x x' :=
              Finset.sum_congr rfl fun x _ => Finset.sum_comm
    _ = _ := by
        simp only [kernelForm, LinearMap.mk₂_apply, rowGram, ip, FiniteLaw.expect]
        refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun x' _ => ?_
        rw [Finset.sum_mul_sum, Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [Finset.mul_sum, Finset.sum_mul]
        exact Finset.sum_congr rfl fun s _ => by ring

/-- **The product map** `𝒴: G ↦ E_{y,s}A(x; y)φ_x(s)G(y, s)` has `‖𝒴‖² ≤ D a` when
`E_yA(x; y)² ≤ D` and `0 ⪯ (⟨φ_x, φ_{x'}⟩) ⪯ a` on `L²(α)` (positive Schur order,
`lem:swapped-rectangle`(b)). -/
theorem prodMap_norm [DecidableEq X] (α : FiniteLaw X) (hα : ∀ x, 0 < α.weight x) (β : FiniteLaw Y)
    (π : FiniteLaw S) (A : X → Y → ℝ) (φ : X → S → ℝ) {D a : ℝ}
    (hD : ∀ x, β.expect (fun y => A x y ^ 2) ≤ D)
    (ha : 0 ≤ a)
    (hW : ∀ f, kernelForm α α (fun x x' => ip π (φ x) (φ x')) f f ≤ a * nrm α f ^ 2)
    (G : Y × S → ℝ) :
    nrm α (recOp (β.product π) (fun x q => A x q.1 * φ x q.2) G) ≤
      Real.sqrt (D * a) * nrm (β.product π) G := by
  have hD0 : 0 ≤ D := by
    obtain ⟨x⟩ : Nonempty X := by
      by_contra h
      have : (∑ x, α.weight x) = 0 := by
        rw [Finset.univ_eq_empty_iff.mpr (not_nonempty_iff.mp h)]; simp
      rw [α.total] at this
      exact one_ne_zero this
    exact (β.expect_nonneg fun y => sq_nonneg (A x y)).trans (hD x)
  -- the adjoint bound from the Schur order
  have hadj : ∀ f, nrm (β.product π) (recAdj α (fun x q => A x q.1 * φ x q.2) f) ≤
      Real.sqrt (D * a) * nrm α f := by
    intro f
    have h1 := nrm_prodAdj_sq α β π A φ f
    have hc : ∀ x, rowGram β A x x ≤ D := fun x => by
      have := hD x
      simp only [rowGram, ← sq]
      exact this
    have hWs : ∀ x x', ip π (φ x) (φ x') = ip π (φ x') (φ x) := fun x x' => ip_comm _ _ _
    have h2 := schur_operator_le α hα (rowGram β A) (fun x x' => ip π (φ x) (φ x'))
      (rowGram_posSemidef β A) hWs hc ha hW f
    rw [← h1] at h2
    have hsq : nrm (β.product π) (recAdj α (fun x q => A x q.1 * φ x q.2) f) ^ 2 ≤
        (Real.sqrt (D * a) * nrm α f) ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (mul_nonneg hD0 ha)]
      exact h2
    exact (abs_le_of_sq_le_sq' hsq (mul_nonneg (Real.sqrt_nonneg _) (nrm_nonneg _ _))).2
  -- transpose: `recOp β A = recAdj β Aᵀ`
  have ht := nrm_recAdj_le (β.product π) α (fun (q : Y × S) (x : X) => A x q.1 * φ x q.2)
    (Real.sqrt_nonneg (D * a)) (fun f => by
      have := hadj f
      have e : recOp α (fun (q : Y × S) (x : X) => A x q.1 * φ x q.2) f =
          recAdj α (fun x q => A x q.1 * φ x q.2) f := rfl
      rw [e]
      exact this) G
  have e2 : recAdj (β.product π) (fun (q : Y × S) (x : X) => A x q.1 * φ x q.2) G =
      recOp (β.product π) (fun x q => A x q.1 * φ x q.2) G := rfl
  rw [e2] at ht
  exact ht

/-- **The swapped product with a Gram multiplier** (`lem:swapped-rectangle`(b), (d)):
`|⟨F, (T[A,A]∘⟨φ, φ'⟩)H⟩| ≤ √(Da)√(Da')‖F‖‖H‖`. -/
theorem swap_gram_bound [DecidableEq X] (α : FiniteLaw X) (hα : ∀ x, 0 < α.weight x)
    (β : FiniteLaw Y)
    (π : FiniteLaw S) (A : X → Y → ℝ) (φ φ' : X → S → ℝ) {D a a' : ℝ}
    (hD : ∀ x, β.expect (fun y => A x y ^ 2) ≤ D) (ha : 0 ≤ a) (ha' : 0 ≤ a')
    (hW : ∀ f, kernelForm α α (fun x x' => ip π (φ x) (φ x')) f f ≤ a * nrm α f ^ 2)
    (hW' : ∀ f, kernelForm α α (fun x x' => ip π (φ' x) (φ' x')) f f ≤ a' * nrm α f ^ 2)
    (Fn Hn : X × Y → ℝ) :
    |kernelForm (α.product β) (α.product β)
        (fun p q => A p.1 q.2 * A q.1 p.2 * ip π (φ p.1) (φ' q.1)) Fn Hn| ≤
      Real.sqrt (D * a) * Real.sqrt (D * a') * nrm (α.product β) Fn * nrm (α.product β) Hn :=
  swap_multiplier_norm α β π A φ φ' (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    (prodMap_norm α hα β π A φ hD ha hW) (prodMap_norm α hα β π A φ' hD ha' hW') Fn Hn

/-! ## The core score -/

section Score

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The residual `ρ_y` as a function on `𝔽²`. -/
noncomputable def rhoV (y : F × F) : F × F → ℝ := fun s => rhoP y s.1 s.2

/-- `⟨ρ_y, ρ_{y'}⟩` in `L²(𝔽²)` with the uniform law is `n^{-2} ∑_{z,z'} ρ_y ρ_{y'}`. -/
theorem ip_rhoV (y y' : F × F) :
    ip (FiniteLaw.uniform (F × F)) (rhoV y) (rhoV y') =
      (∑ z, ∑ z', rhoP y z z' * rhoP y' z z') / (Fintype.card F : ℝ) ^ 2 := by
  unfold ip rhoV
  rw [FiniteLaw.expect_uniform, Fintype.sum_prod_type, Fintype.card_prod]
  push_cast
  ring

/-- **The square of a core score as a Gram multiplier**: for distinct pairs,
`H(y, y')² − (1 − 2q)² = n⟨ρ_y, ρ_{y'}⟩_{L²(𝔽²)}`. -/
theorem pairScore_sq_sub {y y' : F × F} (hy : y.1 ≠ y.2) (hy' : y'.1 ≠ y'.2) :
    pairScore y y' ^ 2 - (1 - 2 / (Fintype.card F : ℝ)) ^ 2 =
      (Fintype.card F : ℝ) * ip (FiniteLaw.uniform (F × F)) (rhoV y) (rhoV y') := by
  have hn : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  rw [pairScore_sq_split hy hy', ip_rhoV]
  field_simp
  ring

/-- **`lem:root-square`, the first bound** (core score): let `α` (the cores, full support), `β`
(the private pairs), `A = 𝖱` the rectangle, and `a(C)`, `c(C)` the two core pairs, which are
distinct pairs. If `E_b A(C; b)² ≤ D` and the Grams of the residual pair maps `C ↦ ρ_{a(C)}`,
`C ↦ ρ_{c(C)}` are `⪯ g` on `L²(α)`, then for the soft kernel
`K_soft((C,b),(C',b')) = A(C; b')A(C'; b)` and the score `H₀ = H(a(C), c(C'))`,
`|⟨F, (K_soft∘H₀² − (1 − 2q)²K_soft)H⟩| ≤ n·D·g‖F‖‖H‖`. -/
theorem root_square_first [DecidableEq X] (α : FiniteLaw X) (hα : ∀ x, 0 < α.weight x)
    (β : FiniteLaw Y)
    (A : X → Y → ℝ) (aP cP : X → F × F) (haP : ∀ x, (aP x).1 ≠ (aP x).2)
    (hcP : ∀ x, (cP x).1 ≠ (cP x).2) {D g : ℝ} (hD : ∀ x, β.expect (fun y => A x y ^ 2) ≤ D)
    (hg : 0 ≤ g)
    (hWa : ∀ f, kernelForm α α (fun x x' => ip (FiniteLaw.uniform (F × F)) (rhoV (aP x))
      (rhoV (aP x'))) f f ≤ g * nrm α f ^ 2)
    (hWc : ∀ f, kernelForm α α (fun x x' => ip (FiniteLaw.uniform (F × F)) (rhoV (cP x))
      (rhoV (cP x'))) f f ≤ g * nrm α f ^ 2)
    (Fn Hn : X × Y → ℝ) :
    |kernelForm (α.product β) (α.product β)
        (fun p q => A p.1 q.2 * A q.1 p.2 * pairScore (aP p.1) (cP q.1) ^ 2 -
          (1 - 2 / (Fintype.card F : ℝ)) ^ 2 * (A p.1 q.2 * A q.1 p.2)) Fn Hn| ≤
      (Fintype.card F : ℝ) * (D * g) * nrm (α.product β) Fn * nrm (α.product β) Hn := by
  have hn : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have e : (fun p q : X × Y => A p.1 q.2 * A q.1 p.2 * pairScore (aP p.1) (cP q.1) ^ 2 -
      (1 - 2 / (Fintype.card F : ℝ)) ^ 2 * (A p.1 q.2 * A q.1 p.2)) =
      fun p q => (Fintype.card F : ℝ) * (A p.1 q.2 * A q.1 p.2 *
        ip (FiniteLaw.uniform (F × F)) (rhoV (aP p.1)) (rhoV (cP q.1))) := by
    funext p q
    have := pairScore_sq_sub (haP p.1) (hcP q.1)
    linear_combination (A p.1 q.2 * A q.1 p.2) * this
  rw [e]
  have hsmul : ∀ (c : ℝ) (K : X × Y → X × Y → ℝ),
      kernelForm (α.product β) (α.product β) (fun p q => c * K p q) Fn Hn =
        c * kernelForm (α.product β) (α.product β) K Fn Hn := by
    intro c K
    simp only [kernelForm, LinearMap.mk₂_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring
  rw [hsmul, abs_mul, abs_of_pos hn]
  have hb := swap_gram_bound α hα β (FiniteLaw.uniform (F × F)) A (fun x => rhoV (aP x))
    (fun x => rhoV (cP x)) hD hg hg hWa hWc Fn Hn
  have hD0 : 0 ≤ D * g := by
    have hDx : 0 ≤ D := by
      by_cases hX : Nonempty X
      · obtain ⟨x⟩ := hX
        exact (β.expect_nonneg fun y => sq_nonneg (A x y)).trans (hD x)
      · have : (∑ x, α.weight x) = 0 := by
          rw [Finset.univ_eq_empty_iff.mpr (not_nonempty_iff.mp hX)]; simp
        rw [α.total] at this
        exact absurd this one_ne_zero
    exact mul_nonneg hDx hg
  have hss : Real.sqrt (D * g) * Real.sqrt (D * g) = D * g := Real.mul_self_sqrt hD0
  rw [hss] at hb
  calc (Fintype.card F : ℝ) * |kernelForm (α.product β) (α.product β)
        (fun p q => A p.1 q.2 * A q.1 p.2 *
          ip (FiniteLaw.uniform (F × F)) (rhoV (aP p.1)) (rhoV (cP q.1))) Fn Hn|
      ≤ (Fintype.card F : ℝ) * (D * g * nrm (α.product β) Fn * nrm (α.product β) Hn) :=
        mul_le_mul_of_nonneg_left hb hn.le
    _ = _ := by ring

/-- **The paper's constant**: at `D = 256𝔯₊`, `g = c₀q²` and `n = 1/q`, the bound `n·D·g` of
`root_square_first` is `256c₀𝔯₊q`. -/
theorem root_square_first_paper {n rp c0 : ℝ} (hn : 0 < n) :
    n * (256 * rp * (c0 * (1 / n) ^ 2)) = 256 * c0 * rp * (1 / n) := by
  field_simp

end Score

end Sarkozy.PositiveRoots
