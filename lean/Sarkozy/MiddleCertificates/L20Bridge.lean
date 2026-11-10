module

public import Sarkozy.MiddleCertificates.Caps
public import Sarkozy.L20Cap.PrimeCapsPaper
public import Sarkozy.L20Cap.CoreExists
public import Sarkozy.L20Cap.BalancedCollision
public import Sarkozy.JointRows.PaleyGauss

/-!
# The bridge from W3's L20 model to B6's L20 cut operator (`lem:front12:reference`(ii), L20)

`paper/sections/20_middle_reference.tex`, `subsec:middle-l20`: the cut L20 is the chamber cut `ϑ₀`
of `G_{L,2}`; its half graph is `G_{F,2}` (`lem:layer12-geometry`(b)); W3 (`L20Cap/`) models the
half as `x = (a₀, a₁, b₀, b₁, c₀, c₁)` (a core `C` and a pair `b`, `CoreT × PairT`), with the
half law `μ_p` (`halfLaw`) and the cut operator `T = K₀/Z₀` (`cutT`), `K₀ = 𝟙_{Disj} K_soft`,
`K_soft(x, x') = ∏_{i,j}(1 + (D₂₀)_{ij} χ(x'_j - x_i))`. W3 stated, but did not prove, that this is
the cut operator of the L20 cut (interpretation choice 2 of W3's report). Proved here:

* `l20Equiv : Fin 6 ≃ (recordData (Fin 2)).cut.Half`, `a_i ↦ (0, i)`, `b_m ↦ (1, m)`,
  `c_j ↦ (2, j)`: the half graph is `G6` (`l20Equiv_edges`) and the cross signs are `D₂₀`
  (`l20Equiv_sgn`);
* **`K0_eq_cutK`**: `K₀(x, x') = 2¹⁶ K(x, x')` for all halves (the indicator of the 16 cross
  conditions and of disjointness), where `K` is the cut kernel of B6's spectral data;
* `halfLaw_transport`: `μ_p` is the half law of the spectral data (through `labels` and
  `l20Equiv`); `cutZ_eq`: `Z = Z₀/2¹⁶`; **`cutForm_eq_cutT`**: the cut form of the spectral data
  is W3's `kernelForm μ_p μ_p T`;
* `kernelOp_bounds_of_form`: form bounds on `L²(μ)` give the operator bounds on
  `EuclideanSpace` (vectors off the support of `μ` are killed);
* **`rootCutCap_l20_of_cutT`**: B6's `RootCutCap (Fin 2) g B p` from W3-form bounds
  `-g p^{-1/2} ‖f‖² ≤ ⟨f, T f⟩ ≤ (1 + B/p)‖f‖²` on `L²(μ_p)`;
* **`middleRootCaps_l20_of_W3`**: B6's field `h20` from W3-form bounds at the ALLp constants.
* **`l20W3Bounds_of_target`**: those bounds from W3's `l20_prime_caps_target` and the two gates
  `C₂₀ ≤ allpG·p^{-1/2}`, `χ⁺_p/(1 - H₂₀) ≤ allpB/p` (`cert:l20-grid`, evaluated at `p`);
  **`l20W3Bounds_of_balanced`**: the same with the paper's `D_bal` (W3's `hD_balanced`), so that
  no collision input remains.
-/

@[expose] public section

namespace Sarkozy.MiddleCertificates

open Finset Sarkozy.Labellings Sarkozy.Cuts Sarkozy.Recentering Sarkozy.BlockAdapter
  Sarkozy.BlockSpecPaper.AllpData Sarkozy.PartV
open scoped BigOperators InnerProductSpace

/-! ## Operator bounds from form bounds -/

section General

variable {Ω : Type*} [Fintype Ω]

/-- **Form bounds on `L²(μ)` give the bounds of `kernelOp μ k` on `EuclideanSpace ℝ Ω`.** -/
theorem kernelOp_bounds_of_form (μ : FiniteLaw Ω) (k : Ω → Ω → ℝ) {a b : ℝ} (ha : 0 ≤ a)
    (hb : 0 ≤ b)
    (h : ∀ f : Ω → ℝ, -a * μ.expect (fun x => f x ^ 2) ≤ kernelForm μ μ k f f ∧
      kernelForm μ μ k f f ≤ b * μ.expect (fun x => f x ^ 2)) (v : EuclideanSpace ℝ Ω) :
    -a * ‖v‖ ^ 2 ≤ ⟪v, Spectral.kernelOp μ k v⟫_ℝ ∧
      ⟪v, Spectral.kernelOp μ k v⟫_ℝ ≤ b * ‖v‖ ^ 2 := by
  classical
  set f : Ω → ℝ := fun x => if μ.weight x = 0 then 0 else v.ofLp x / √(μ.weight x) with hf
  have hvf : ∀ x, v.ofLp x * √(μ.weight x) = μ.weight x * f x := by
    intro x
    by_cases h0 : μ.weight x = 0
    · simp [hf, h0]
    · have hs : 0 < √(μ.weight x) := Real.sqrt_pos.mpr (lt_of_le_of_ne (μ.nonneg x) (Ne.symm h0))
      have hss := Real.mul_self_sqrt (μ.nonneg x)
      simp only [hf, h0, ↓reduceIte]
      rw [mul_div_assoc', eq_div_iff hs.ne', mul_assoc, hss, mul_comm]
  have hform : ⟪v, Spectral.kernelOp μ k v⟫_ℝ = kernelForm μ μ k f f := by
    rw [Spectral.inner_kernelOp]
    simp only [kernelForm, LinearMap.mk₂_apply]
    refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun x' _ => ?_
    calc v.ofLp x * (√(μ.weight x) * k x x' * √(μ.weight x')) * v.ofLp x'
        = (v.ofLp x * √(μ.weight x)) * k x x' * (v.ofLp x' * √(μ.weight x')) := by ring
      _ = (μ.weight x * f x) * k x x' * (μ.weight x' * f x') := by rw [hvf, hvf]
      _ = _ := by ring
  have hnorm : μ.expect (fun x => f x ^ 2) ≤ ‖v‖ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    unfold FiniteLaw.expect
    refine Finset.sum_le_sum fun x _ => ?_
    by_cases h0 : μ.weight x = 0
    · simpa [hf, h0] using sq_nonneg (v.ofLp x)
    · have hs : 0 < √(μ.weight x) := Real.sqrt_pos.mpr (lt_of_le_of_ne (μ.nonneg x) (Ne.symm h0))
      have hss := Real.sq_sqrt (μ.nonneg x)
      simp only [hf, h0, ↓reduceIte, Real.norm_eq_abs, sq_abs]
      rw [div_pow, hss]
      field_simp
      exact le_refl _
  have hE0 : 0 ≤ μ.expect (fun x => f x ^ 2) :=
    Finset.sum_nonneg fun x _ => mul_nonneg (μ.nonneg x) (sq_nonneg _)
  obtain ⟨h1, h2⟩ := h f
  rw [hform]
  constructor
  · nlinarith [mul_le_mul_of_nonneg_left hnorm ha]
  · nlinarith [mul_le_mul_of_nonneg_left hnorm hb]

end General

/-! ## The coordinates of the L20 half -/

/-- The vertex of `G_{L,2}` of the coordinate `i` of W3's half `(a₀, a₁, b₀, b₁, c₀, c₁)`. -/
def l20Vertex (i : Fin 6) : ZMod 6 × Fin 2 :=
  (![0, 0, 1, 1, 2, 2] i, ![0, 1, 0, 1, 0, 1] i)

theorem l20Vertex_mem (i : Fin 6) : l20Vertex i ∈ (recordData (Fin 2)).cut.half := by
  rw [mem_recordHalf]
  revert i
  decide

/-- The coordinate `i` as a half vertex. -/
def l20Half (i : Fin 6) : (recordData (Fin 2)).cut.Half := ⟨l20Vertex i, l20Vertex_mem i⟩

theorem l20Half_bijective : Function.Bijective l20Half := by
  constructor
  · intro i j h
    have h' : l20Vertex i = l20Vertex j := congrArg Subtype.val h
    revert i j
    decide
  · intro v
    obtain ⟨⟨u, l⟩, hv⟩ := v
    have hu := (mem_recordHalf (Fin 2) (u, l)).mp hv
    revert u l
    decide

/-- **The coordinates of the L20 half**: `a_i ↦ (0, i)`, `b_m ↦ (1, m)`, `c_j ↦ (2, j)`. -/
noncomputable def l20Equiv : Fin 6 ≃ (recordData (Fin 2)).cut.Half :=
  Equiv.ofBijective l20Half l20Half_bijective

theorem l20Equiv_apply (i : Fin 6) : (l20Equiv i).1 = l20Vertex i := rfl

theorem rec2_mem (e : (ZMod 6 × Fin 2) × (ZMod 6 × Fin 2)) :
    e ∈ (recordData (Fin 2)).G.E ↔ e.2.1 = rot e.1.1 :=
  mem_recordGraph (Fin 2) e

/-- **`lem:layer12-geometry`(b) in W3's coordinates**: the half graph is `G6` (`a_i → c_j`). -/
theorem l20Equiv_edges (i j : Fin 6) :
    (i, j) ∈ L20Cap.G6.E ↔ (l20Equiv i, l20Equiv j) ∈ (recordData (Fin 2)).halfGraph.E := by
  rw [SpecData.mem_halfGraph, l20Equiv_apply, l20Equiv_apply, rec2_mem]
  revert i j
  decide

/-- The cross signs `D₂₀` as integers. -/
def crossDZ (i j : Fin 6) : ℤ :=
  ![![0, 0, -1, -1, 0, 0], ![0, 0, -1, -1, 0, 0], ![1, 1, 0, 0, -1, -1],
    ![1, 1, 0, 0, -1, -1], ![0, 0, 1, 1, 0, 0], ![0, 0, 1, 1, 0, 0]] i j

theorem crossDZ_cast (i j : Fin 6) : (crossDZ i j : ℝ) = L20Cap.crossD i j := by
  fin_cases i <;> fin_cases j <;> norm_num [crossDZ, L20Cap.crossD]

/-- **The cross signs of the L20 cut are `D₂₀`** (`eq:l20-cross-matrix`). -/
theorem l20Equiv_sgn (i j : Fin 6) :
    (recordData (Fin 2)).sgn (l20Equiv i) (l20Equiv j) = crossDZ i j := by
  simp only [SpecData.sgn, rec2_mem, l20Equiv_apply]
  revert i j
  decide

/-! ## The cut kernel in W3's coordinates -/

section Kernel

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- A labelling of W3's half coordinates as a labelling of the half of the spectral data. -/
noncomputable def toD (z : Fin 6 → F) : (recordData (Fin 2)).cut.Half → F :=
  fun h => z (l20Equiv.symm h)

omit [Field F] [Fintype F] [DecidableEq F] in
theorem toD_apply (z : Fin 6 → F) (i : Fin 6) : toD z (l20Equiv i) = z i := by
  simp [toD]

theorem crossDZ_cases (i j : Fin 6) : crossDZ i j = 0 ∨ crossDZ i j = 1 ∨ crossDZ i j = -1 := by
  revert i j
  decide

/-- The factor identity: `1 + d χ(t) = 2·𝟙{χ(d t) = 1}` for `d = ±1`, `t ≠ 0`, and `= 1` for
`d = 0`. -/
theorem factor_eq (hm1 : quadraticChar F (-1) = -1) {d : ℤ}
    (hd : d = 0 ∨ d = 1 ∨ d = -1) {t : F} (ht : t ≠ 0) :
    1 + (d : ℝ) * L20Cap.chi t = (if d ≠ 0 then (2 : ℝ) else 1) *
      (if d ≠ 0 then (if quadraticChar F ((d : F) * t) = 1 then (1 : ℝ) else 0) else 1) := by
  rcases hd with rfl | rfl | rfl
  · simp
  · rcases L20Cap.chi_of_ne ht with h | h <;> simp only [L20Cap.chi] at h
    · have h' : quadraticChar F t = 1 := by exact_mod_cast h
      simp [h', L20Cap.chi]
      norm_num
    · have h' : quadraticChar F t = -1 := by exact_mod_cast h
      simp [h', L20Cap.chi]
  · have hn : quadraticChar F (-t) = -quadraticChar F t := by
      have e : -t = (-1) * t := by ring
      rw [e, map_mul, hm1]
      ring
    rcases L20Cap.chi_of_ne ht with h | h <;> simp only [L20Cap.chi] at h
    · have h' : quadraticChar F t = 1 := by exact_mod_cast h
      simp [h', hn, L20Cap.chi]
    · have h' : quadraticChar F t = -1 := by exact_mod_cast h
      simp [h', hn, L20Cap.chi]
      norm_num

theorem prod_two_pow :
    (∏ i : Fin 6, ∏ j : Fin 6, (if crossDZ i j ≠ 0 then (2 : ℝ) else 1)) = 2 ^ 16 := by
  simp only [Fin.prod_univ_six, crossDZ]
  norm_num

/-- The cross product over `E_×` reindexed by W3's coordinates. -/
theorem prod_crossPairs (φ : (recordData (Fin 2)).cut.Half × (recordData (Fin 2)).cut.Half → ℝ) :
    ∏ q ∈ (recordData (Fin 2)).crossPairs, φ q =
      ∏ i : Fin 6, ∏ j : Fin 6, (if crossDZ i j ≠ 0 then φ (l20Equiv i, l20Equiv j) else 1) := by
  classical
  unfold SpecData.crossPairs
  rw [Finset.prod_filter, ← Fintype.prod_equiv (l20Equiv.prodCongr l20Equiv)
    (fun ij : Fin 6 × Fin 6 => if crossDZ ij.1 ij.2 ≠ 0 then φ (l20Equiv ij.1, l20Equiv ij.2)
      else 1) _ (fun ⟨i, j⟩ => by simp [l20Equiv_sgn]), Fintype.prod_prod_type]

theorem disj_iff (x x' : L20Cap.CoreT F × L20Cap.PairT F) :
    L20Cap.Disj x x' ↔ Disjoint (univ.image (toD (L20Cap.labels x)))
      (univ.image (toD (L20Cap.labels x'))) := by
  rw [Finset.disjoint_left]
  constructor
  · intro h a ha hb
    obtain ⟨u, -, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨w, -, hw⟩ := Finset.mem_image.mp hb
    exact h (l20Equiv.symm u) (l20Equiv.symm w) (by simpa [toD] using hw.symm)
  · intro h i j hij
    refine h (Finset.mem_image.mpr ⟨l20Equiv i, mem_univ _, rfl⟩)
      (Finset.mem_image.mpr ⟨l20Equiv j, mem_univ _, ?_⟩)
    rw [toD_apply, toD_apply, hij]

/-- **W3's unnormalized kernel is `2¹⁶` times the cut kernel of the L20 cut**:
`K₀(x, x') = 2¹⁶ K(x, x')` (`eq:spec:K`; `prop:l20-rectangular`(c)). -/
theorem K0_eq_cutK (hm1 : quadraticChar F (-1) = -1) (x x' : L20Cap.CoreT F × L20Cap.PairT F) :
    L20Cap.K0 x x' = 2 ^ 16 *
      (recordData (Fin 2)).cutK (toD (L20Cap.labels x)) (toD (L20Cap.labels x')) := by
  classical
  rw [SpecData.cutK_eq_prod]
  unfold L20Cap.K0
  by_cases hd : L20Cap.Disj x x'
  · simp only [hd, (disj_iff x x').mp hd, ↓reduceIte, one_mul]
    rw [L20Cap.Ksoft_eq_softKernel hm1, prod_crossPairs]
    unfold L20Cap.softKernel
    have hfac : ∀ i j : Fin 6, 1 + L20Cap.crossD i j *
        L20Cap.chi (L20Cap.labels x' j - L20Cap.labels x i) =
        (if crossDZ i j ≠ 0 then (2 : ℝ) else 1) *
          (if crossDZ i j ≠ 0 then (if quadraticChar F (((recordData (Fin 2)).sgn
            (l20Equiv i) (l20Equiv j) : F) * (toD (L20Cap.labels x') (l20Equiv j) -
              toD (L20Cap.labels x) (l20Equiv i))) = 1 then (1 : ℝ) else 0) else 1) := by
      intro i j
      rw [← crossDZ_cast, l20Equiv_sgn, toD_apply, toD_apply]
      exact factor_eq hm1 (crossDZ_cases i j) (sub_ne_zero.mpr (Ne.symm (hd i j)))
    simp only [hfac, Finset.prod_mul_distrib, prod_two_pow]
  · have hd' : ¬ Disjoint (univ.image (toD (L20Cap.labels x)))
        (univ.image (toD (L20Cap.labels x'))) := fun h => hd ((disj_iff x x').mpr h)
    simp only [hd, hd', ↓reduceIte, zero_mul, mul_zero]

end Kernel

/-! ## The laws and the cut form in W3's coordinates -/

section Laws

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
  [Nonempty (L20Cap.CoreT F)] [Nonempty (L20Cap.PairT F)]

/-- **`μ_p` is the half law of the L20 cut**: `E_{λ(G⁺)} Ψ = E_{μ_p} Ψ(labels x)`. -/
theorem halfLaw_transport (h6 : 6 ≤ Fintype.card F)
    (hne : (injLabellings F (recordData (Fin 2)).G).Nonempty)
    (Ψ : ((recordData (Fin 2)).cut.Half → F) → ℝ) :
    ((recordData (Fin 2)).halfLaw hne).expect Ψ =
      (L20Cap.halfLaw h6).expect (fun x => Ψ (toD (L20Cap.labels x))) := by
  unfold SpecData.halfLaw
  rw [graphLaw_iso L20Cap.G6 (recordData (Fin 2)).halfGraph l20Equiv l20Equiv_edges
    (L20Cap.injLabellings_G6_nonempty h6) ((recordData (Fin 2)).half_nonempty hne) Ψ]
  exact L20Cap.graphLaw_eq_halfLaw h6 (L20Cap.injLabellings_G6_nonempty h6) _

/-- **The normalizers**: `Z = Z₀/2¹⁶`. -/
theorem cutZ_eq (hm1 : quadraticChar F (-1) = -1) (h6 : 6 ≤ Fintype.card F)
    (hne : (injLabellings F (recordData (Fin 2)).G).Nonempty) :
    (recordData (Fin 2)).cutZ hne = L20Cap.Z0 h6 / 2 ^ 16 := by
  unfold SpecData.cutZ L20Cap.Z0
  rw [FiniteLaw.expect_product, kernelForm_apply, halfLaw_transport h6 hne]
  rw [← Sarkozy.Peyre.expect_div_const]
  refine (L20Cap.halfLaw h6).expect_congr fun x => ?_
  rw [halfLaw_transport h6 hne, one_mul, ← Sarkozy.Peyre.expect_div_const]
  refine (L20Cap.halfLaw h6).expect_congr fun x' => ?_
  rw [K0_eq_cutK hm1]
  ring

/-- **The cut form of the L20 cut is W3's form of `T = K₀/Z₀`**. -/
theorem cutForm_eq_cutT (hm1 : quadraticChar F (-1) = -1) (h6 : 6 ≤ Fintype.card F)
    (hne : (injLabellings F (recordData (Fin 2)).G).Nonempty)
    (Fn : ((recordData (Fin 2)).cut.Half → F) → ℝ) :
    kernelForm ((recordData (Fin 2)).halfLaw hne) ((recordData (Fin 2)).halfLaw hne)
        (fun x x' => (recordData (Fin 2)).cutK x x' / (recordData (Fin 2)).cutZ hne) Fn Fn =
      kernelForm (L20Cap.halfLaw h6) (L20Cap.halfLaw h6) (L20Cap.cutT h6)
        (fun x => Fn (toD (L20Cap.labels x))) (fun x => Fn (toD (L20Cap.labels x))) := by
  rw [kernelForm_apply, kernelForm_apply, halfLaw_transport h6 hne]
  refine (L20Cap.halfLaw h6).expect_congr fun x => ?_
  rw [halfLaw_transport h6 hne]
  congr 1
  refine (L20Cap.halfLaw h6).expect_congr fun x' => ?_
  rw [cutZ_eq hm1 h6 hne, L20Cap.cutT, K0_eq_cutK hm1]
  congr 1
  field_simp

theorem norm_transport (h6 : 6 ≤ Fintype.card F)
    (hne : (injLabellings F (recordData (Fin 2)).G).Nonempty)
    (Fn : ((recordData (Fin 2)).cut.Half → F) → ℝ) :
    ((recordData (Fin 2)).halfLaw hne).expect (fun x => Fn x ^ 2) =
      nrm (L20Cap.halfLaw h6) (fun x => Fn (toD (L20Cap.labels x))) ^ 2 := by
  rw [halfLaw_transport h6 hne, nrm, Real.sq_sqrt]
  · unfold ip
    exact (L20Cap.halfLaw h6).expect_congr fun x => sq _
  · unfold ip
    exact Finset.sum_nonneg fun x _ => mul_nonneg ((L20Cap.halfLaw h6).nonneg x)
      (mul_self_nonneg _)

end Laws

/-! ## B6's `RootCutCap (Fin 2)` from W3-form bounds -/

/-- **B6's per-prime L20 certificate from bounds on W3's operator**: if
`-g p^{-1/2}‖f‖² ≤ ⟨f, T f⟩ ≤ (1 + B/p)‖f‖²` on `L²(μ_p)` for W3's `T = K₀/Z₀`, then
`RootCutCap (Fin 2) g B p`. -/
theorem rootCutCap_l20_of_cutT {p : ℕ} [Fact p.Prime] [Nonempty (L20Cap.CoreT (ZMod p))]
    [Nonempty (L20Cap.PairT (ZMod p))] (hm1 : quadraticChar (ZMod p) (-1) = -1)
    (h6 : 6 ≤ Fintype.card (ZMod p)) {g B : ℝ} (hg : 0 ≤ g) (hB : 0 ≤ B)
    (h : ∀ f : L20Cap.CoreT (ZMod p) × L20Cap.PairT (ZMod p) → ℝ,
      -(g * (√(p : ℝ))⁻¹) * nrm (L20Cap.halfLaw h6) f ^ 2 ≤
          kernelForm (L20Cap.halfLaw h6) (L20Cap.halfLaw h6) (L20Cap.cutT h6) f f ∧
        kernelForm (L20Cap.halfLaw h6) (L20Cap.halfLaw h6) (L20Cap.cutT h6) f f ≤
          (1 + B / p) * nrm (L20Cap.halfLaw h6) f ^ 2) :
    RootCutCap (Fin 2) g B p := by
  intro hne v
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg _
  refine kernelOp_bounds_of_form ((recordData (Fin 2)).halfLaw hne)
    (fun x x' => (recordData (Fin 2)).cutK x x' / (recordData (Fin 2)).cutZ hne)
    (mul_nonneg hg (inv_nonneg.mpr (Real.sqrt_nonneg _)))
    (by positivity) (fun Fn => ?_) v
  rw [cutForm_eq_cutT hm1 h6 hne, norm_transport h6 hne]
  exact h _

/-! ## B6's field `h20` from W3's per-prime caps -/

/-- **W3-form bounds of the L20 cut at the ALLp constants of piece `i`**:
`-allpG·p^{-1/2}‖f‖² ≤ ⟨f, T f⟩ ≤ (1 + allpB/p)‖f‖²` for W3's `T = K₀/Z₀` on `L²(μ_p)`
(`prop:l20-collisions`(b) at `(g₂₀, c⁺₂₀)` of `cert:l20-grid`). *Hypothesis*; sufficient
conditions: `l20W3Bounds_of_target`. -/
def L20W3Bounds (i : Fin 33) (p : ℕ) [Fact p.Prime] : Prop :=
  ∀ (h6 : 6 ≤ Fintype.card (ZMod p)) [Nonempty (L20Cap.CoreT (ZMod p))]
    [Nonempty (L20Cap.PairT (ZMod p))] (f : L20Cap.CoreT (ZMod p) × L20Cap.PairT (ZMod p) → ℝ),
    -((allpG i 0 : ℝ) * (√(p : ℝ))⁻¹) * nrm (L20Cap.halfLaw h6) f ^ 2 ≤
        kernelForm (L20Cap.halfLaw h6) (L20Cap.halfLaw h6) (L20Cap.cutT h6) f f ∧
      kernelForm (L20Cap.halfLaw h6) (L20Cap.halfLaw h6) (L20Cap.cutT h6) f f ≤
        (1 + (allpB i 0 : ℝ) / p) * nrm (L20Cap.halfLaw h6) f ^ 2

theorem chi_neg_one_three {p : ℕ} [Fact p.Prime] (hp : p % 4 = 3) :
    quadraticChar (ZMod p) (-1) = -1 :=
  JointRows.PaleyGauss.chi_neg_one hp

/-- **B6's field `h20` on piece `i`** (`MiddleRootCaps (Fin 2) 0 i`) from W3-form bounds at every
class-three prime of the piece, through the bridge `rootCutCap_l20_of_cutT`. -/
theorem middleRootCaps_l20_of_W3 {i : Fin 33}
    (h : ∀ (p : ℕ) [Fact p.Prime], p % 4 = 3 → pieceStart i ≤ p → p < pieceStop i →
      L20W3Bounds i p) : MiddleRootCaps (Fin 2) 0 i := by
  intro p _ hp3 hX hY
  have hm1 := chi_neg_one_three hp3
  have hp36 : (36 : ℝ) < p := lt_of_lt_of_le (pieceStart_gt_36 i) (by exact_mod_cast hX)
  have hp11 : 11 ≤ p := by
    have : (11 : ℝ) < p := by linarith
    exact_mod_cast this.le
  have h6 : 6 ≤ Fintype.card (ZMod p) := by rw [ZMod.card]; omega
  have h11 : 11 ≤ Fintype.card (ZMod p) := by rw [ZMod.card]; exact hp11
  have h2 : ringChar (ZMod p) ≠ 2 := by
    rw [ZMod.ringChar_zmod_n]
    omega
  have := L20Cap.coreT_nonempty hm1 h2 h11
  have : Nonempty (L20Cap.PairT (ZMod p)) := L20Cap.pairT_nonempty
  exact rootCutCap_l20_of_cutT hm1 h6 (allpG_nonneg i 0 (by decide))
    (allpB_nonneg i 0 (by decide)) (h p hp3 hX hY h6)

/-- **`L20W3Bounds` from caps of W3's form** with constants below the ALLp ones. -/
theorem l20W3Bounds_of_caps (i : Fin 33) {p : ℕ} [Fact p.Prime] {C c : ℝ}
    (hcaps : ∀ (h6 : 6 ≤ Fintype.card (ZMod p)) [Nonempty (L20Cap.CoreT (ZMod p))]
      [Nonempty (L20Cap.PairT (ZMod p))] (f : L20Cap.CoreT (ZMod p) × L20Cap.PairT (ZMod p) → ℝ),
      -C * nrm (L20Cap.halfLaw h6) f ^ 2 ≤
          kernelForm (L20Cap.halfLaw h6) (L20Cap.halfLaw h6) (L20Cap.cutT h6) f f ∧
        kernelForm (L20Cap.halfLaw h6) (L20Cap.halfLaw h6) (L20Cap.cutT h6) f f ≤
          (1 + c) * nrm (L20Cap.halfLaw h6) f ^ 2)
    (hC : C ≤ (allpG i 0 : ℝ) * (√(p : ℝ))⁻¹) (hc : c ≤ (allpB i 0 : ℝ) / p) :
    L20W3Bounds i p := by
  intro h6 _ _ f
  obtain ⟨h1, h2⟩ := hcaps h6 f
  have hn := sq_nonneg (nrm (L20Cap.halfLaw h6) f)
  constructor
  · nlinarith [mul_le_mul_of_nonneg_right hC hn]
  · nlinarith [mul_le_mul_of_nonneg_right hc hn]

open L20Cap Sarkozy.Extraction Sarkozy.ExtractionK in
/-- **`L20W3Bounds` from W3's `l20_prime_caps_target`** (`prop:l20-collisions`(b) at `p`, with H1
and H6) and the two gates of `cert:l20-grid` evaluated at `p`: `C₂₀(p) ≤ allpG·p^{-1/2}`
(`hgateC`) and `χ⁺_p/(1 - H₂₀) ≤ allpB/p` (`hgateB`). The other hypotheses are W3's, verbatim:
the 42 class data of `N_A` and its value, `𝔪`, the orders and `D`, `N_ns`, `m_⋆`, `χ⁺_p` and the
gates `Δ_g > 0`, `c_gap ≤ s_p`, `ε_Z < 1`, `C₂₀ < 1`, `H₂₀ < 1`. -/
theorem l20W3Bounds_of_target (i : Fin 33) {p : ℕ} [Fact p.Prime] [Nonempty (CoreT (ZMod p))]
    [Nonempty (PairT (ZMod p))] (hm1 : quadraticChar (ZMod p) (-1) = -1) (hWeil : Target.Weil)
    (hFour : Target.FourCycle) (h6 : 6 ≤ Fintype.card (ZMod p))
    (h20 : (2 : ℝ) ^ 20 ≤ Fintype.card (ZMod p)) {m NA D mstar Nns χp : ℝ}
    (𝔓 : Finset (Finset (Fin 6 × Fin 6) × Finset (Fin 6 × Fin 6)))
    (h𝔓 : IsExactPartition Ex8 𝔓 (nonstars Ex8))
    (rec : Finset (Fin 6 × Fin 6) × Finset (Fin 6 × Fin 6) → LeafRecordData (Fin 6))
    (hrec : ∀ c ∈ 𝔓, (rec c).Valid Ex8 c) {Q : ℝ} (hQ : 64 ≤ Q) (hQp : Q ≤ p)
    (hNAle : ∑ c ∈ 𝔓, (Real.sqrt p)⁻¹ ^ (rec c).k * leafCoef G6 D20Z Q 6 Ex8 c (rec c) ≤ NA)
    (hm : (coreLaw (F := ZMod p)).expect (fun C => Kbar C.1 - 1) ≤ m) (hm0 : 0 ≤ m)
    (hΔ : 0 < 30 * (Fintype.card (ZMod p) : ℝ)⁻¹ -
      (2 * (Real.sqrt (Fintype.card (ZMod p)))⁻¹ + NA) ^ 2)
    (hgate : cGap (Fintype.card (ZMod p) : ℝ)⁻¹ (tauG (ZMod p) m)
      (2 * (Real.sqrt (Fintype.card (ZMod p)))⁻¹ + NA) (xPaper (ZMod p) m NA) ≤ sP (ZMod p) m)
    (hD0 : 0 ≤ D)
    (ord : Fin 6 → Fin 6 → Fin 6 → ℕ)
    (hord : ∀ i j, ∀ ℓ ℓ', ℓ ≠ i → ℓ' ≠ i → ord i j ℓ = ord i j ℓ' → ℓ = ℓ')
    (π : ℕ → Fin 6 → ℕ) (hπ : ∀ k, Function.Injective (π k))
    (hDle : ∀ x : CoreT (ZMod p) × PairT (ZMod p), Avoid x →
      collisionIncident1 G6 D20Z ord (Fintype.card (ZMod p)) 6 (labels x) +
        collisionIncident2 G6 D20Z π (Fintype.card (ZMod p)) 6 (labels x) ≤ D)
    (hNns0 : 0 ≤ Nns)
    (hXns : ∀ φ h : (Fin 6 → ZMod p) → ℝ,
      |(graphLaw G6 (injLabellings_G6_nonempty h6)).expect (fun z => φ z *
          (graphLaw G6 (injLabellings_G6_nonempty h6)).expect (fun z' => Kns z z' * h z'))| ≤
        Nns * Real.sqrt ((graphLaw G6 (injLabellings_G6_nonempty h6)).expect (fun z => φ z ^ 2)) *
          Real.sqrt ((graphLaw G6 (injLabellings_G6_nonempty h6)).expect (fun z => h z ^ 2)))
    (hstar : |kernelForm (halfLaw h6) (halfLaw h6)
      (fun x x' => starPart6 (labels x) (labels x')) (fun _ => 1) (fun _ => 1)| ≤ mstar)
    (hεZ : Nns + D + mstar < 1)
    (hχ0 : 0 ≤ χp)
    (hchi : nrm (halfLaw h6) (fun x => recOp (halfLaw h6) (cutT h6) (fun _ => 1) x - 1) ^ 2 ≤ χp)
    (hC1 : (sP (ZMod p) m * cGap (Fintype.card (ZMod p) : ℝ)⁻¹ (tauG (ZMod p) m)
        (2 * (Real.sqrt (Fintype.card (ZMod p)))⁻¹ + NA) (xPaper (ZMod p) m NA) /
      prob ((coreLaw (F := ZMod p)).product (pairLaw (F := ZMod p))) Avoid + D) /
        (1 - (Nns + D + mstar)) < 1)
    (hH1 : (Nns + D) / (1 - (Nns + D + mstar)) < 1)
    (hgateC : (sP (ZMod p) m * cGap (Fintype.card (ZMod p) : ℝ)⁻¹ (tauG (ZMod p) m)
        (2 * (Real.sqrt (Fintype.card (ZMod p)))⁻¹ + NA) (xPaper (ZMod p) m NA) /
        prob ((coreLaw (F := ZMod p)).product (pairLaw (F := ZMod p))) Avoid + D) /
          (1 - (Nns + D + mstar)) ≤
        (allpG i 0 : ℝ) * (√(p : ℝ))⁻¹)
    (hgateB : χp / (1 - (Nns + D) / (1 - (Nns + D + mstar))) ≤ (allpB i 0 : ℝ) / p) :
    L20W3Bounds i p :=
  l20W3Bounds_of_caps i (fun _ _ _ f => l20_prime_caps_target hm1 hWeil hFour h6 h20 𝔓 h𝔓 rec hrec
    hQ hQp hNAle hm hm0 hΔ hgate hD0 ord hord π hπ hDle hNns0 hXns hstar hεZ hχ0 hchi hC1 hH1 f)
    hgateC hgateB

open L20Cap Sarkozy.Extraction Sarkozy.ExtractionK in
/-- **`L20W3Bounds` with the paper's balanced collision constant** (`prop:l20-collisions`(a),(b)):
as `l20W3Bounds_of_target`, with `D = D_bal` (W3's `hD_balanced`, from Weil, for `p ≥ 2²⁰`), the
paper's `x_g` (`xG_le_xPaper`) and H1, H6 in the agreed form. Remaining: the class data of `N_A`
and its value at `Q`, `𝔪`, `N_ns` (X1's form), `m_⋆`, `χ⁺_p`, W3's gates and the two ALLp gates
at `p`. -/
theorem l20W3Bounds_of_balanced (i : Fin 33) {p : ℕ} [Fact p.Prime] [Nonempty (CoreT (ZMod p))]
    [Nonempty (PairT (ZMod p))] (hm1 : quadraticChar (ZMod p) (-1) = -1) (hWeil : Target.Weil)
    (hFour : Target.FourCycle) (h6 : 6 ≤ Fintype.card (ZMod p))
    (h20 : (2 : ℝ) ^ 20 ≤ Fintype.card (ZMod p)) {m NA mstar Nns χp : ℝ}
    (𝔓 : Finset (Finset (Fin 6 × Fin 6) × Finset (Fin 6 × Fin 6)))
    (h𝔓 : IsExactPartition Ex8 𝔓 (nonstars Ex8))
    (rec : Finset (Fin 6 × Fin 6) × Finset (Fin 6 × Fin 6) → LeafRecordData (Fin 6))
    (hrec : ∀ c ∈ 𝔓, (rec c).Valid Ex8 c) {Q : ℝ} (hQ : 64 ≤ Q) (hQp : Q ≤ p)
    (hNAle : ∑ c ∈ 𝔓, (Real.sqrt p)⁻¹ ^ (rec c).k * leafCoef G6 D20Z Q 6 Ex8 c (rec c) ≤ NA)
    (hm : (coreLaw (F := ZMod p)).expect (fun C => Kbar C.1 - 1) ≤ m) (hm0 : 0 ≤ m)
    (hΔ : 0 < 30 * (Fintype.card (ZMod p) : ℝ)⁻¹ -
      (2 * (Real.sqrt (Fintype.card (ZMod p)))⁻¹ + NA) ^ 2)
    (hgate : cGap (Fintype.card (ZMod p) : ℝ)⁻¹ (tauG (ZMod p) m)
      (2 * (Real.sqrt (Fintype.card (ZMod p)))⁻¹ + NA) (xPaper (ZMod p) m NA) ≤ sP (ZMod p) m)
    (hNns0 : 0 ≤ Nns)
    (hXns : ∀ φ h : (Fin 6 → ZMod p) → ℝ,
      |(graphLaw G6 (injLabellings_G6_nonempty h6)).expect (fun z => φ z *
          (graphLaw G6 (injLabellings_G6_nonempty h6)).expect (fun z' => Kns z z' * h z'))| ≤
        Nns * Real.sqrt ((graphLaw G6 (injLabellings_G6_nonempty h6)).expect (fun z => φ z ^ 2)) *
          Real.sqrt ((graphLaw G6 (injLabellings_G6_nonempty h6)).expect (fun z => h z ^ 2)))
    (hstar : |kernelForm (halfLaw h6) (halfLaw h6)
      (fun x x' => starPart6 (labels x) (labels x')) (fun _ => 1) (fun _ => 1)| ≤ mstar)
    (hεZ : Nns + Dbal (Real.sqrt (Fintype.card (ZMod p)))⁻¹ (Fintype.card (ZMod p) : ℝ)⁻¹ + mstar < 1)
    (hχ0 : 0 ≤ χp)
    (hchi : nrm (halfLaw h6) (fun x => recOp (halfLaw h6) (cutT h6) (fun _ => 1) x - 1) ^ 2 ≤ χp)
    (hC1 : (sP (ZMod p) m * cGap (Fintype.card (ZMod p) : ℝ)⁻¹ (tauG (ZMod p) m)
        (2 * (Real.sqrt (Fintype.card (ZMod p)))⁻¹ + NA) (xPaper (ZMod p) m NA) /
      prob ((coreLaw (F := ZMod p)).product (pairLaw (F := ZMod p))) Avoid + Dbal (Real.sqrt (Fintype.card (ZMod p)))⁻¹ (Fintype.card (ZMod p) : ℝ)⁻¹) /
        (1 - (Nns + Dbal (Real.sqrt (Fintype.card (ZMod p)))⁻¹ (Fintype.card (ZMod p) : ℝ)⁻¹ + mstar)) < 1)
    (hH1 : (Nns + Dbal (Real.sqrt (Fintype.card (ZMod p)))⁻¹ (Fintype.card (ZMod p) : ℝ)⁻¹) / (1 - (Nns + Dbal (Real.sqrt (Fintype.card (ZMod p)))⁻¹ (Fintype.card (ZMod p) : ℝ)⁻¹ + mstar)) < 1)     (hgateC : (sP (ZMod p) m * cGap (Fintype.card (ZMod p) : ℝ)⁻¹ (tauG (ZMod p) m)
        (2 * (Real.sqrt (Fintype.card (ZMod p)))⁻¹ + NA) (xPaper (ZMod p) m NA) /
        prob ((coreLaw (F := ZMod p)).product (pairLaw (F := ZMod p))) Avoid + Dbal (Real.sqrt (Fintype.card (ZMod p)))⁻¹ (Fintype.card (ZMod p) : ℝ)⁻¹) /
          (1 - (Nns + Dbal (Real.sqrt (Fintype.card (ZMod p)))⁻¹ (Fintype.card (ZMod p) : ℝ)⁻¹ + mstar)) ≤
        (allpG i 0 : ℝ) * (√(p : ℝ))⁻¹)
    (hgateB : χp / (1 - (Nns + Dbal (Real.sqrt (Fintype.card (ZMod p)))⁻¹ (Fintype.card (ZMod p) : ℝ)⁻¹) /
        (1 - (Nns + Dbal (Real.sqrt (Fintype.card (ZMod p)))⁻¹ (Fintype.card (ZMod p) : ℝ)⁻¹ + mstar))) ≤ (allpB i 0 : ℝ) / p) :
    L20W3Bounds i p := by
  have hp2 : p ≠ 2 := by
    have : 6 ≤ p := by rwa [ZMod.card] at h6
    omega
  have h64 : 64 ≤ Fintype.card (ZMod p) := by
    have : (64 : ℝ) ≤ Fintype.card (ZMod p) := le_trans (by norm_num) h20
    exact_mod_cast this
  have hW := Labellings.weilBound_of_target hWeil p hp2
  have hq0 : (0 : ℝ) ≤ (Fintype.card (ZMod p) : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  have hr0 : (0 : ℝ) ≤ (Real.sqrt (Fintype.card (ZMod p)))⁻¹ :=
    inv_nonneg.mpr (Real.sqrt_nonneg _)
  have hq1 : (Fintype.card (ZMod p) : ℝ)⁻¹ ≤ 2⁻¹ ^ 20 := by
    rw [inv_pow]
    exact inv_anti₀ (by positivity) h20
  have hr1 : (Real.sqrt (Fintype.card (ZMod p)))⁻¹ ≤ 2⁻¹ ^ 10 := by
    have h10 : (2 : ℝ) ^ 10 ≤ Real.sqrt (Fintype.card (ZMod p)) := by
      rw [show (2 : ℝ) ^ 10 = Real.sqrt (2 ^ 20) by
        rw [show (2 : ℝ) ^ 20 = (2 ^ 10) ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt h20
    rw [inv_pow]
    exact inv_anti₀ (by positivity) h10
  have hL : 0 < Lamc (Real.sqrt (Fintype.card (ZMod p)))⁻¹ (Fintype.card (ZMod p) : ℝ)⁻¹ := by
    rw [Lamc_eq]
    have h1 : 0 < 1 - ((Real.sqrt (Fintype.card (ZMod p)))⁻¹ +
        24 * (Fintype.card (ZMod p) : ℝ)⁻¹) := by
      have : (2 : ℝ)⁻¹ ^ 10 + 24 * 2⁻¹ ^ 20 < 1 := by norm_num
      linarith
    have h2 : 0 < 1 - 6 * (Fintype.card (ZMod p) : ℝ)⁻¹ := by
      have : 6 * (2 : ℝ)⁻¹ ^ 20 < 1 := by norm_num
      linarith
    positivity
  have hD0 := Dbal_nonneg hr0 hq0 hL
  exact l20W3Bounds_of_caps i (fun _ _ _ f => l20_prime_caps_X1ns hm1 hW
    (DLK.fourCycleBound hFour hp2) h6 𝔓 h𝔓 rec hrec (by linarith) hQp (SanityX1.leafEhat_G6_lt hQ)
    hNAle hm hm0 hΔ (xG_le_xPaper (ZMod p) hm0 NA h20) hgate hD0
    (fun g => hD_balanced hW hm1 h64 g) hNns0 hXns hstar hεZ hχ0 hchi hC1 hH1 f) hgateC hgateB

end Sarkozy.MiddleCertificates
