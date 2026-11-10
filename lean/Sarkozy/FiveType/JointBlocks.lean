module

public import Sarkozy.FiveType.Datum

/-!
# Joint rows of a block (`cor:joint-completion-blocks`)

Source: `paper/sections/17_completion_repair.tex`, `cor:joint-completion-blocks`; the inputs
`lem:joint-rows` (b), (c) are in `paper/sections/16_extraction.tex`.

**Setting.** A block `𝔅` is a finite index type `ι` (its primes), with finite label sets `X_p`,
laws `ν_p`, matching kernels `T_{E,p}` (self-adjoint couplings of `ν_p`) and fold kernels
`T_{F,p}` (mass one), all relative to `ν_p ⊗ ν_p`. The conditional reference is the product law
`ν^b = ⊗_p ν_p` (`blockLaw`), and the kernels at `b` are the products `T_E^b = ⊗_p T_{E,p}`,
`T_F^b = m_b ⊗_p T_{F,p}` (`prodKernel`). With `u_{L,p} = T_{F,p}𝟙`, `u_{R,p} = T_{F,p}*𝟙`:
* `C_{F,p} = T_{F,p} − u_{L,p} ⊗ u_{R,p}` (`foldCov`), `C_{E,p} = T_{E,p} − J_p` (`matchCov`);
* `C_𝔅 = ⊗_p (J_p + C_{F,p}) − J_𝔅` and `E_𝔅 = ⊗_p (J_p + C_{E,p}) − J_𝔅`, with kernels
  `∏_p (1 + C_p) − 1` (`sectorKernel`, `CB`, `EB`);
* `U_L = ⊗_p u_{L,p}`, `U_R = ⊗_p u_{R,p}` (`UL`, `UR`), `R_𝔅 = T_{F,𝔅} − U_L ⊗ U_R − C_𝔅`
  (`RB`), and `E_T = (2υ + υ²)(∏_p (1 + c_F r_p) − 1)` (`ET`).

The numbers `r_p` stand for `p^{-1/2}` and `r` for `P^{-1/2}`, `P` the least prime of `𝔅`; only
`r_p ≤ r`, `r ≥ 0` (and `r_p ≥ 0` for the exponential bound) are used.

**Proved.**
* The product Fubini identities: `⊗_p ν_p` is a probability law, `T𝟙` and `T*𝟙` of a product
  kernel are the products, and so on (`kone_prodKernel`, `kone_sectorKernel`, ...).
* `C_{F,p}` and `C_{E,p}` annihilate the constants (`foldCov_annihilates`,
  `matchCov_annihilates`); hence so do `C_𝔅` and `R_𝔅` (`CB_annihilates`, `RB_annihilates`);
  `E U_L = E U_R = 1`; `T_E^b` has exact marginals (`prodKernel_exactMarginals`); and
  `E_𝔅 = T_E^b − J` (`kf_EB`).
* `E_T ≤ (2υ + υ²)(e^{n c_F r} − 1)` if `𝔅` has at most `n` primes (`ET_le_exp`).
* **`blockJointData`, `joint_completion_blocks`**: the joint data of `lem:five-type`(f)
  (`JointData` of `FiveType/Datum.lean`) hold at `b` with `φ₀ = U_L`, `φ₂ = U_R`, `C_b = C_𝔅`,
  `R_b = R_𝔅`, `ε_E = hr`, `κ_J = k_J r`, `ε_T = E_T`.
* **`joint_completion_graded`**: the completion inequalities with `(d, M, f, h)`,
  `M ≥ H + t_Y`, `f ≥ f_J`, imply the graded conditions of `lem:five-type`(f).
* `JointData.transport`: transport along equalities of the conditional objects, to apply the
  corollary to a five-type datum whose objects at `b` are the block products.

**Hypotheses.** `lem:joint-rows`(b) (`JointRowsB`: the sector bound of the joint block of
`(E_𝔅, C_𝔅)`) and `lem:joint-rows`(c) (`JointRowsC`: the bound of `R_𝔅`), each stated for the
families of the block and used as a hypothesis; they belong to 16_extraction. All other steps
of the paper's proof are proved.

**Conventions.** Operator bounds are form bounds (`FormBound`, see `FiveType/Datum.lean`); the
joint block `(E C; C* E) ⪰ −k I` is `JointBlockLower`. The constants `c_F, c_E ≥ 0` and the
weight `w_D ≥ 0` are implicit in the paper.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.FiveType

section Transport

variable {𝔛 : Type*} [Fintype 𝔛]

/-- Transport of joint data along equalities of the conditional law and the kernels (to apply
`cor:joint-completion-blocks` to a five-type datum whose objects at `b` are block products). -/
def JointData.transport {μ μ' : FiniteLaw 𝔛} {TE TE' K K' : 𝔛 → 𝔛 → ℝ} {H υ εT εE κJ : ℝ}
    (J : JointData μ TE K H υ εT εE κJ) (hμ : μ = μ') (hTE : TE = TE') (hK : K = K') :
    JointData μ' TE' K' H υ εT εE κJ := by
  subst hμ hTE hK
  exact J

end Transport

/-! The rest of the file is in the namespace `Sarkozy.FiveType.Blocks`, to keep its helper
names apart from those of the other `FiveType` files. -/

namespace Blocks

/-! ## Generic kernel identities on one `L²(μ)` -/

section Generic

variable {𝔛 : Type*} [Fintype 𝔛]

/-- `C_{F,p} = T_{F,p} − u_{L,p} ⊗ u_{R,p}`, with `u_L = T𝟙`, `u_R = T*𝟙`. -/
noncomputable def foldCov (μ : FiniteLaw 𝔛) (T : 𝔛 → 𝔛 → ℝ) (x y : 𝔛) : ℝ :=
  T x y - kone μ T x * kone' μ T y

/-- `C_{E,p} = T_{E,p} − J_p`, whose kernel is `T − 1`. -/
def matchCov (T : 𝔛 → 𝔛 → ℝ) (x y : 𝔛) : ℝ := T x y - 1

/-- **The joint block `(E C; C* E) ⪰ −k I`** on `L²(μ) ⊕ L²(μ)`: its form at `(Φ, Ψ)` is
`⟨Φ, EΦ⟩ + 2⟨Φ, CΨ⟩ + ⟨Ψ, EΨ⟩`. -/
def JointBlockLower (μ : FiniteLaw 𝔛) (E C : 𝔛 → 𝔛 → ℝ) (k : ℝ) : Prop :=
  ∀ Φ Ψ : 𝔛 → ℝ, -k * (nrm μ Φ ^ 2 + nrm μ Ψ ^ 2) ≤ kf μ E Φ Φ + 2 * kf μ C Φ Ψ + kf μ E Ψ Ψ

theorem nrm_nonneg (μ : FiniteLaw 𝔛) (U : 𝔛 → ℝ) : 0 ≤ nrm μ U := Real.sqrt_nonneg _

theorem FormBound.mono {μ : FiniteLaw 𝔛} {A : 𝔛 → 𝔛 → ℝ} {e e' : ℝ} (h : FormBound μ A e)
    (he : e ≤ e') : FormBound μ A e' := by
  intro Φ Ψ
  have hn : 0 ≤ nrm μ Φ * nrm μ Ψ := mul_nonneg (nrm_nonneg μ Φ) (nrm_nonneg μ Ψ)
  calc |kf μ A Φ Ψ| ≤ e * nrm μ Φ * nrm μ Ψ := h Φ Ψ
    _ = e * (nrm μ Φ * nrm μ Ψ) := by ring
    _ ≤ e' * (nrm μ Φ * nrm μ Ψ) := mul_le_mul_of_nonneg_right he hn
    _ = e' * nrm μ Φ * nrm μ Ψ := by ring

theorem JointBlockLower.mono {μ : FiniteLaw 𝔛} {E C : 𝔛 → 𝔛 → ℝ} {k k' : ℝ}
    (h : JointBlockLower μ E C k) (hk : k ≤ k') : JointBlockLower μ E C k' := by
  intro Φ Ψ
  have hn : 0 ≤ nrm μ Φ ^ 2 + nrm μ Ψ ^ 2 := by positivity
  have := h Φ Ψ
  nlinarith

theorem kone_sub (μ : FiniteLaw 𝔛) (A B : 𝔛 → 𝔛 → ℝ) (x : 𝔛) :
    kone μ (fun x y => A x y - B x y) x = kone μ A x - kone μ B x := by
  simp only [kone, mul_sub, Finset.sum_sub_distrib]

theorem kone'_sub (μ : FiniteLaw 𝔛) (A B : 𝔛 → 𝔛 → ℝ) (y : 𝔛) :
    kone' μ (fun x y => A x y - B x y) y = kone' μ A y - kone' μ B y := by
  simp only [kone', mul_sub, Finset.sum_sub_distrib]

theorem kone_tensor (μ : FiniteLaw 𝔛) (a b : 𝔛 → ℝ) (x : 𝔛) :
    kone μ (fun x y => a x * b y) x = a x * μ.expect b := by
  simp only [kone, FiniteLaw.expect, Finset.mul_sum]
  exact Finset.sum_congr rfl fun y _ => by ring

theorem kone'_tensor (μ : FiniteLaw 𝔛) (a b : 𝔛 → ℝ) (y : 𝔛) :
    kone' μ (fun x y => a x * b y) y = μ.expect a * b y := by
  simp only [kone', FiniteLaw.expect, Finset.sum_mul]
  exact Finset.sum_congr rfl fun x _ => by ring

/-- `E_μ[T𝟙] = ⟨𝟙, T𝟙⟩`, the mass. -/
theorem expect_kone (μ : FiniteLaw 𝔛) (T : 𝔛 → 𝔛 → ℝ) :
    μ.expect (kone μ T) = kf μ T (fun _ => 1) (fun _ => 1) := by
  simp only [kf, kone, FiniteLaw.expect, Finset.mul_sum]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring

/-- `E_μ[T*𝟙] = ⟨𝟙, T𝟙⟩`, the mass. -/
theorem expect_kone' (μ : FiniteLaw 𝔛) (T : 𝔛 → 𝔛 → ℝ) :
    μ.expect (kone' μ T) = kf μ T (fun _ => 1) (fun _ => 1) := by
  simp only [kf, kone', FiniteLaw.expect, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring

/-- `⟨Φ, (T − J)Ψ⟩ = ⟨Φ, TΨ⟩ − E Φ E Ψ`. -/
theorem kf_sub_one (μ : FiniteLaw 𝔛) (T : 𝔛 → 𝔛 → ℝ) (Φ Ψ : 𝔛 → ℝ) :
    kf μ (fun x y => T x y - 1) Φ Ψ = kf μ T Φ Ψ - μ.expect Φ * μ.expect Ψ := by
  simp only [kf, FiniteLaw.expect, Finset.sum_mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => by ring

/-- **`C_{F,p}` annihilates the constants** when `T_{F,p}` has mass one. -/
theorem foldCov_annihilates (μ : FiniteLaw 𝔛) (T : 𝔛 → 𝔛 → ℝ)
    (hT : kf μ T (fun _ => 1) (fun _ => 1) = 1) :
    (∀ x, kone μ (foldCov μ T) x = 0) ∧ (∀ y, kone' μ (foldCov μ T) y = 0) := by
  refine ⟨fun x => ?_, fun y => ?_⟩
  · have h := kone_sub μ T (fun x y => kone μ T x * kone' μ T y) x
    rw [kone_tensor, expect_kone', hT] at h
    change kone μ (fun x y => T x y - kone μ T x * kone' μ T y) x = 0
    rw [h]
    ring
  · have h := kone'_sub μ T (fun x y => kone μ T x * kone' μ T y) y
    rw [kone'_tensor, expect_kone, hT] at h
    change kone' μ (fun x y => T x y - kone μ T x * kone' μ T y) y = 0
    rw [h]
    ring

/-- **`C_{E,p}` annihilates the constants** when `T_{E,p}` has exact marginals. -/
theorem matchCov_annihilates (μ : FiniteLaw 𝔛) (T : 𝔛 → 𝔛 → ℝ) (hT : ExactMarginals μ T) :
    Annihilates μ (matchCov T) := by
  refine ⟨fun x hx => ?_, fun y hy => ?_⟩
  · have h := kone_sub μ T (fun _ _ => 1) x
    change kone μ (fun x y => T x y - 1) x = 0
    rw [h, hT.1 x hx]
    simp [kone, μ.total]
  · have h := kone'_sub μ T (fun _ _ => 1) y
    change kone' μ (fun x y => T x y - 1) y = 0
    rw [h, hT.2 y hy]
    simp [kone', μ.total]

theorem kone_one_add (μ : FiniteLaw 𝔛) (C : 𝔛 → 𝔛 → ℝ) (x : 𝔛) :
    kone μ (fun a b => 1 + C a b) x = 1 + kone μ C x := by
  simp only [kone, mul_add, Finset.sum_add_distrib, mul_one, μ.total]

theorem kone'_one_add (μ : FiniteLaw 𝔛) (C : 𝔛 → 𝔛 → ℝ) (y : 𝔛) :
    kone' μ (fun a b => 1 + C a b) y = 1 + kone' μ C y := by
  simp only [kone', mul_add, Finset.sum_add_distrib, mul_one, μ.total]

theorem kone_one (μ : FiniteLaw 𝔛) (x : 𝔛) : kone μ (fun _ _ => 1) x = 1 := by
  simp only [kone, mul_one, μ.total]

theorem kone'_one (μ : FiniteLaw 𝔛) (y : 𝔛) : kone' μ (fun _ _ => 1) y = 1 := by
  simp only [kone', mul_one, μ.total]

end Generic

/-! ## The block: products over the primes -/

section Block

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {Xp : ι → Type*} [∀ i, Fintype (Xp i)]

/-- The product law `⊗_p ν_p` on the block space `∏_p X_p`. -/
noncomputable def blockLaw (νp : ∀ i, FiniteLaw (Xp i)) : FiniteLaw ((i : ι) → Xp i) where
  weight x := ∏ i, (νp i).weight (x i)
  nonneg x := Finset.prod_nonneg fun i _ => (νp i).nonneg (x i)
  total := by
    rw [← Fintype.prod_sum (fun i j => (νp i).weight j)]
    exact Finset.prod_eq_one fun i _ => (νp i).total

/-- The product kernel `⊗_p K_p`. -/
def prodKernel (K : ∀ i, Xp i → Xp i → ℝ) (x y : (i : ι) → Xp i) : ℝ := ∏ i, K i (x i) (y i)

/-- The kernel of `⊗_p (J_p + C_p) − J_𝔅`, that is `∏_p (1 + C_p) − 1`. -/
def sectorKernel (C : ∀ i, Xp i → Xp i → ℝ) (x y : (i : ι) → Xp i) : ℝ :=
  ∏ i, (1 + C i (x i) (y i)) - 1

theorem sum_blockWeight_prod (νp : ∀ i, FiniteLaw (Xp i)) (g : ∀ i, Xp i → ℝ) :
    ∑ y : (i : ι) → Xp i, (blockLaw νp).weight y * ∏ i, g i (y i) =
      ∏ i, ∑ j, (νp i).weight j * g i j := by
  rw [Fintype.prod_sum (fun i j => (νp i).weight j * g i j)]
  exact Finset.sum_congr rfl fun y _ => Finset.prod_mul_distrib.symm

theorem expect_blockLaw_prod (νp : ∀ i, FiniteLaw (Xp i)) (f : ∀ i, Xp i → ℝ) :
    (blockLaw νp).expect (fun x => ∏ i, f i (x i)) = ∏ i, (νp i).expect (f i) :=
  sum_blockWeight_prod νp f

theorem kone_prodKernel (νp : ∀ i, FiniteLaw (Xp i)) (K : ∀ i, Xp i → Xp i → ℝ)
    (x : (i : ι) → Xp i) :
    kone (blockLaw νp) (prodKernel K) x = ∏ i, kone (νp i) (K i) (x i) :=
  sum_blockWeight_prod νp (fun i j => K i (x i) j)

theorem kone'_prodKernel (νp : ∀ i, FiniteLaw (Xp i)) (K : ∀ i, Xp i → Xp i → ℝ)
    (y : (i : ι) → Xp i) :
    kone' (blockLaw νp) (prodKernel K) y = ∏ i, kone' (νp i) (K i) (y i) :=
  sum_blockWeight_prod νp (fun i j => K i j (y i))

theorem kone_sectorKernel (νp : ∀ i, FiniteLaw (Xp i)) (C : ∀ i, Xp i → Xp i → ℝ)
    (x : (i : ι) → Xp i) :
    kone (blockLaw νp) (sectorKernel C) x = ∏ i, (1 + kone (νp i) (C i) (x i)) - 1 := by
  change kone (blockLaw νp)
    (fun x y => prodKernel (fun i a b => 1 + C i a b) x y - (fun _ _ => (1 : ℝ)) x y) x = _
  rw [kone_sub, kone_prodKernel, kone_one]
  simp only [kone_one_add]

theorem kone'_sectorKernel (νp : ∀ i, FiniteLaw (Xp i)) (C : ∀ i, Xp i → Xp i → ℝ)
    (y : (i : ι) → Xp i) :
    kone' (blockLaw νp) (sectorKernel C) y = ∏ i, (1 + kone' (νp i) (C i) (y i)) - 1 := by
  change kone' (blockLaw νp)
    (fun x y => prodKernel (fun i a b => 1 + C i a b) x y - (fun _ _ => (1 : ℝ)) x y) y = _
  rw [kone'_sub, kone'_prodKernel, kone'_one]
  simp only [kone'_one_add]

theorem blockLaw_support {νp : ∀ i, FiniteLaw (Xp i)} {x : (i : ι) → Xp i}
    (hx : (blockLaw νp).weight x ≠ 0) (i : ι) : (νp i).weight (x i) ≠ 0 :=
  Finset.prod_ne_zero_iff.mp hx i (Finset.mem_univ i)

/-- A product of kernels with exact marginals has exact marginals (`T_E^b = ⊗_p T_{E,p}`). -/
theorem prodKernel_exactMarginals (νp : ∀ i, FiniteLaw (Xp i)) (T : ∀ i, Xp i → Xp i → ℝ)
    (hT : ∀ i, ExactMarginals (νp i) (T i)) : ExactMarginals (blockLaw νp) (prodKernel T) := by
  refine ⟨fun x hx => ?_, fun y hy => ?_⟩
  · rw [kone_prodKernel]
    exact Finset.prod_eq_one fun i _ => (hT i).1 (x i) (blockLaw_support hx i)
  · rw [kone'_prodKernel]
    exact Finset.prod_eq_one fun i _ => (hT i).2 (y i) (blockLaw_support hy i)

/-- If every `C_p` annihilates the constants, so does `∏_p (1 + C_p) − 1`. -/
theorem sectorKernel_annihilates (νp : ∀ i, FiniteLaw (Xp i)) (C : ∀ i, Xp i → Xp i → ℝ)
    (hC : ∀ i, Annihilates (νp i) (C i)) : Annihilates (blockLaw νp) (sectorKernel C) := by
  refine ⟨fun x hx => ?_, fun y hy => ?_⟩
  · rw [kone_sectorKernel, Finset.prod_eq_one fun i _ => by
      rw [(hC i).1 (x i) (blockLaw_support hx i), add_zero], sub_self]
  · rw [kone'_sectorKernel, Finset.prod_eq_one fun i _ => by
      rw [(hC i).2 (y i) (blockLaw_support hy i), add_zero], sub_self]

/-! ## The block objects of `cor:joint-completion-blocks` -/

/-- `U_L = ⊗_p u_{L,p}`, `u_{L,p} = T_{F,p}𝟙`. -/
noncomputable def UL (νp : ∀ i, FiniteLaw (Xp i)) (TFp : ∀ i, Xp i → Xp i → ℝ)
    (x : (i : ι) → Xp i) : ℝ :=
  ∏ i, kone (νp i) (TFp i) (x i)

/-- `U_R = ⊗_p u_{R,p}`, `u_{R,p} = T_{F,p}*𝟙`. -/
noncomputable def UR (νp : ∀ i, FiniteLaw (Xp i)) (TFp : ∀ i, Xp i → Xp i → ℝ)
    (y : (i : ι) → Xp i) : ℝ :=
  ∏ i, kone' (νp i) (TFp i) (y i)

/-- `C_𝔅 = ⊗_p (J_p + C_{F,p}) − J_𝔅`. -/
noncomputable def CB (νp : ∀ i, FiniteLaw (Xp i)) (TFp : ∀ i, Xp i → Xp i → ℝ) :
    ((i : ι) → Xp i) → ((i : ι) → Xp i) → ℝ :=
  sectorKernel (fun i => foldCov (νp i) (TFp i))

/-- `E_𝔅 = ⊗_p (J_p + C_{E,p}) − J_𝔅`. -/
def EB (TEp : ∀ i, Xp i → Xp i → ℝ) : ((i : ι) → Xp i) → ((i : ι) → Xp i) → ℝ :=
  sectorKernel (fun i => matchCov (TEp i))

/-- `R_𝔅 = T_{F,𝔅} − U_L ⊗ U_R − C_𝔅`. -/
noncomputable def RB (νp : ∀ i, FiniteLaw (Xp i)) (TFp : ∀ i, Xp i → Xp i → ℝ)
    (x y : (i : ι) → Xp i) : ℝ :=
  prodKernel TFp x y - UL νp TFp x * UR νp TFp y - CB νp TFp x y

/-- `E_T = (2υ + υ²)(∏_{p∈𝔅}(1 + c_F r_p) − 1)`. -/
noncomputable def ET (υ cF : ℝ) (rp : ι → ℝ) : ℝ := (2 * υ + υ ^ 2) * (∏ i, (1 + cF * rp i) - 1)

theorem expect_UL (νp : ∀ i, FiniteLaw (Xp i)) (TFp : ∀ i, Xp i → Xp i → ℝ)
    (hTF : ∀ i, kf (νp i) (TFp i) (fun _ => 1) (fun _ => 1) = 1) :
    (blockLaw νp).expect (UL νp TFp) = 1 := by
  change (blockLaw νp).expect (fun x => ∏ i, kone (νp i) (TFp i) (x i)) = 1
  rw [expect_blockLaw_prod]
  exact Finset.prod_eq_one fun i _ => by rw [expect_kone, hTF i]

theorem expect_UR (νp : ∀ i, FiniteLaw (Xp i)) (TFp : ∀ i, Xp i → Xp i → ℝ)
    (hTF : ∀ i, kf (νp i) (TFp i) (fun _ => 1) (fun _ => 1) = 1) :
    (blockLaw νp).expect (UR νp TFp) = 1 := by
  change (blockLaw νp).expect (fun x => ∏ i, kone' (νp i) (TFp i) (x i)) = 1
  rw [expect_blockLaw_prod]
  exact Finset.prod_eq_one fun i _ => by rw [expect_kone', hTF i]

theorem CB_annihilates (νp : ∀ i, FiniteLaw (Xp i)) (TFp : ∀ i, Xp i → Xp i → ℝ)
    (hTF : ∀ i, kf (νp i) (TFp i) (fun _ => 1) (fun _ => 1) = 1) :
    Annihilates (blockLaw νp) (CB νp TFp) :=
  sectorKernel_annihilates νp _ fun i =>
    ⟨fun x _ => (foldCov_annihilates _ _ (hTF i)).1 x,
      fun y _ => (foldCov_annihilates _ _ (hTF i)).2 y⟩

theorem RB_annihilates (νp : ∀ i, FiniteLaw (Xp i)) (TFp : ∀ i, Xp i → Xp i → ℝ)
    (hTF : ∀ i, kf (νp i) (TFp i) (fun _ => 1) (fun _ => 1) = 1) :
    Annihilates (blockLaw νp) (RB νp TFp) := by
  have hC := CB_annihilates νp TFp hTF
  refine ⟨fun x hx => ?_, fun y hy => ?_⟩
  · change kone (blockLaw νp) (fun x y => (prodKernel TFp x y - UL νp TFp x * UR νp TFp y) -
      CB νp TFp x y) x = 0
    rw [kone_sub, kone_sub (blockLaw νp) (prodKernel TFp), kone_tensor, kone_prodKernel,
      expect_UR νp TFp hTF, hC.1 x hx]
    simp only [UL, mul_one, sub_self]
  · change kone' (blockLaw νp) (fun x y => (prodKernel TFp x y - UL νp TFp x * UR νp TFp y) -
      CB νp TFp x y) y = 0
    rw [kone'_sub, kone'_sub (blockLaw νp) (prodKernel TFp), kone'_tensor, kone'_prodKernel,
      expect_UL νp TFp hTF, hC.2 y hy]
    simp only [UR, one_mul, sub_self]

/-- `E_𝔅 = T_E^b − J_𝔅` for `C_{E,p} = T_{E,p} − J_p`, so `⟨Φ, E_𝔅 Ψ⟩ = ⟨Φ, T_E^b Ψ⟩ − EΦ EΨ`. -/
theorem kf_EB (νp : ∀ i, FiniteLaw (Xp i)) (TEp : ∀ i, Xp i → Xp i → ℝ)
    (Φ Ψ : ((i : ι) → Xp i) → ℝ) :
    kf (blockLaw νp) (EB TEp) Φ Ψ =
      kf (blockLaw νp) (prodKernel TEp) Φ Ψ - (blockLaw νp).expect Φ * (blockLaw νp).expect Ψ := by
  have h : EB TEp = fun x y => prodKernel TEp x y - 1 := by
    funext x y
    simp only [EB, sectorKernel, matchCov, add_sub_cancel, prodKernel]
  rw [h, kf_sub_one]

theorem kf_EB_eform (νp : ∀ i, FiniteLaw (Xp i)) (TEp : ∀ i, Xp i → Xp i → ℝ)
    (Φ : ((i : ι) → Xp i) → ℝ) :
    kf (blockLaw νp) (EB TEp) Φ Φ = eform (blockLaw νp) (prodKernel TEp) Φ := by
  rw [kf_EB, eform, sq]

/-! ## `lem:joint-rows` (b), (c), as hypotheses -/

/-- **`lem:joint-rows`(b)** (`paper/sections/16_extraction.tex`), for the families `C_{E,p}`,
`C_{F,p}` on `L²(ν_p)`: if they annihilate the constants on both sides, `C_{E,p}` is
self-adjoint, `‖C_{F,p}‖ ≤ c < 1`, `‖C_{E,p}‖ ≤ h < 1` and the joint block at each prime is
`⪰ −k'_p I`, then the joint block of `(E_𝔅, C_𝔅)`, with `C_𝔅 = ⊗_p(J_p + C_{F,p}) − J_𝔅` and
`E_𝔅 = ⊗_p(J_p + C_{E,p}) − J_𝔅`, is `⪰ −K I` for every `K ≥ max(c² + h², max_p k'_p)`.

Used as a hypothesis (the paper proves it by the sector decomposition of `L²(⊗_p ν_p)`; not
formalized here). -/
def JointRowsB (νp : ∀ i, FiniteLaw (Xp i)) (CE CF : ∀ i, Xp i → Xp i → ℝ) : Prop :=
  ∀ (c h K : ℝ) (k' : ι → ℝ),
    (∀ i, Annihilates (νp i) (CF i)) → (∀ i, Annihilates (νp i) (CE i)) →
    (∀ i x y, CE i x y = CE i y x) →
    (∀ i, FormBound (νp i) (CF i) c) → c < 1 → (∀ i, FormBound (νp i) (CE i) h) → h < 1 →
    (∀ i, JointBlockLower (νp i) (CE i) (CF i) (k' i)) → c ^ 2 + h ^ 2 ≤ K → (∀ i, k' i ≤ K) →
    JointBlockLower (blockLaw νp) (sectorKernel CE) (sectorKernel CF) K

/-- **`lem:joint-rows`(c)** (`paper/sections/16_extraction.tex`): for kernels `T_{F,p}` of mass
one with marginal densities `u_{L,p} = T_{F,p}𝟙`, `u_{R,p} = T_{F,p}*𝟙` and
`C_{F,p} = T_{F,p} − u_{L,p} ⊗ u_{R,p}`, if `‖U_L − 𝟙‖, ‖U_R − 𝟙‖ ≤ υ` then
`‖T_{F,𝔅} − U_L ⊗ U_R − C_𝔅‖ ≤ (2υ + υ²)(∏_p (1 + ‖C_{F,p}‖) − 1)`. It is stated here for
numerical bounds `n_p ≥ ‖C_{F,p}‖`, which follows from the paper's form by monotonicity of the
product in each `‖C_{F,p}‖ ≥ 0`.

Used as a hypothesis (not formalized here). -/
def JointRowsC (νp : ∀ i, FiniteLaw (Xp i)) (TFp : ∀ i, Xp i → Xp i → ℝ) : Prop :=
  ∀ (υ : ℝ) (n : ι → ℝ), (∀ i, kf (νp i) (TFp i) (fun _ => 1) (fun _ => 1) = 1) →
    nrm (blockLaw νp) (fun x => UL νp TFp x - 1) ≤ υ →
    nrm (blockLaw νp) (fun x => UR νp TFp x - 1) ≤ υ →
    (∀ i, FormBound (νp i) (foldCov (νp i) (TFp i)) (n i)) →
    FormBound (blockLaw νp) (RB νp TFp) ((2 * υ + υ ^ 2) * (∏ i, (1 + n i) - 1))

omit [DecidableEq ι] in
/-- `E_T ≤ (2υ + υ²)(e^{n c_F r} − 1)` when the block has at most `n` primes
(`cor:joint-completion-blocks`; `1 + x ≤ eˣ`). -/
theorem ET_le_exp {υ cF r : ℝ} {rp : ι → ℝ} {n : ℕ} (hυ : 0 ≤ υ) (hcF : 0 ≤ cF) (hr : 0 ≤ r)
    (hrp : ∀ i, 0 ≤ rp i ∧ rp i ≤ r) (hn : Fintype.card ι ≤ n) :
    ET υ cF rp ≤ (2 * υ + υ ^ 2) * (Real.exp (n * cF * r) - 1) := by
  have hυ' : 0 ≤ 2 * υ + υ ^ 2 := by positivity
  apply mul_le_mul_of_nonneg_left _ hυ'
  apply sub_le_sub_right
  calc ∏ i, (1 + cF * rp i) ≤ ∏ i, Real.exp (cF * rp i) := by
        apply Finset.prod_le_prod₀
        · intro i _
          have := mul_nonneg hcF (hrp i).1
          linarith
        · intro i _
          have := Real.add_one_le_exp (cF * rp i)
          linarith
    _ = Real.exp (∑ i, cF * rp i) := (Real.exp_sum _ _).symm
    _ ≤ Real.exp (n * cF * r) := by
        apply Real.exp_le_exp.mpr
        calc ∑ i, cF * rp i ≤ ∑ _i : ι, cF * r :=
              Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hrp i).2 hcF
          _ = (Fintype.card ι : ℝ) * (cF * r) := by
              rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
          _ ≤ (n : ℝ) * (cF * r) := by
              apply mul_le_mul_of_nonneg_right _ (mul_nonneg hcF hr)
              exact_mod_cast hn
          _ = n * cF * r := by ring

/-! ## `cor:joint-completion-blocks` -/

/-- **`cor:joint-completion-blocks`: the joint data of `lem:five-type`(f) on a block.**

The block `𝔅` is the finite index type `ι`, with label sets `X_p`, conditional laws `ν_p`, and
`ν^b = ⊗_p ν_p` (`blockLaw`). The matching kernel is `T_E^b = ⊗_p T_{E,p}` with `T_{E,p}` a
self-adjoint coupling of `ν_p` with itself (exact marginals, symmetric kernel); the fold kernel is
`T_F^b = m_b T_{F,𝔅}`, `T_{F,𝔅} = ⊗_p T_{F,p}`, with `T_{F,p}` of mass one. The numbers
`r_p ≤ r` stand for `p^{-1/2} ≤ P^{-1/2}` (`P` the least prime of `𝔅`); only `r_p ≤ r` and
`r ≥ 0` are used. The per-prime hypotheses are `‖C_{F,p}‖ ≤ c_F r_p`, `‖C_{E,p}‖ ≤ c_E r_p` and
`(C_{E,p} C_{F,p}; C_{F,p}* C_{E,p}) ⪰ −k_J r_p I`, with `c_F r, c_E r < 1` and
`(c_F² + c_E²) r ≤ k_J`; the block hypotheses are `m_b ∈ [H⁻¹, H]`, `‖U_L − 𝟙‖, ‖U_R − 𝟙‖ ≤ υ`
and `E_𝔅 = T_E^b − J ⪰ −hr I`. `lem:joint-rows` (b), (c) enter as the hypotheses `hJRb`, `hJRc`.

The data: `φ₀ = U_L`, `φ₂ = U_R`, `C_b = C_𝔅`, `R_b = R_𝔅`, `ε_E = hr`, `κ_J = k_J r`,
`ε_T = E_T`. The constants `c_F, c_E ≥ 0` are implicit in the paper (they bound norms). Nothing
depends on the number of layers: the label sets `X_p` are arbitrary finite sets. -/
noncomputable def blockJointData (νp : ∀ i, FiniteLaw (Xp i)) (TEp TFp : ∀ i, Xp i → Xp i → ℝ)
    (rp : ι → ℝ) {r cF cE kJ h H υ mb : ℝ}
    (hTE : ∀ i, ExactMarginals (νp i) (TEp i)) (hTEsymm : ∀ i x y, TEp i x y = TEp i y x)
    (hTF : ∀ i, kf (νp i) (TFp i) (fun _ => 1) (fun _ => 1) = 1)
    (hr : 0 ≤ r) (hrp : ∀ i, rp i ≤ r) (hcF : 0 ≤ cF) (hcE : 0 ≤ cE)
    (hCF : ∀ i, FormBound (νp i) (foldCov (νp i) (TFp i)) (cF * rp i))
    (hCE : ∀ i, FormBound (νp i) (matchCov (TEp i)) (cE * rp i))
    (hJp : ∀ i, JointBlockLower (νp i) (matchCov (TEp i)) (foldCov (νp i) (TFp i)) (kJ * rp i))
    (hcFr : cF * r < 1) (hcEr : cE * r < 1) (hkJ : (cF ^ 2 + cE ^ 2) * r ≤ kJ)
    (hm0 : H⁻¹ ≤ mb) (hm1 : mb ≤ H)
    (hUL : nrm (blockLaw νp) (fun x => UL νp TFp x - 1) ≤ υ)
    (hUR : nrm (blockLaw νp) (fun x => UR νp TFp x - 1) ≤ υ)
    (hEB : ∀ Φ, -(h * r) * nrm (blockLaw νp) Φ ^ 2 ≤ kf (blockLaw νp) (EB TEp) Φ Φ)
    (hJRb : JointRowsB νp (fun i => matchCov (TEp i)) (fun i => foldCov (νp i) (TFp i)))
    (hJRc : JointRowsC νp TFp) :
    JointData (blockLaw νp) (prodKernel TEp) (fun x y => mb * prodKernel TFp x y) H υ
      (ET υ cF rp) (h * r) (kJ * r) where
  m := mb
  φ0 := UL νp TFp
  φ2 := UR νp TFp
  C := CB νp TFp
  R := RB νp TFp
  decomp x y := by simp only [RB]; ring
  m_lower := hm0
  m_upper := hm1
  mean0 := expect_UL νp TFp hTF
  mean2 := expect_UR νp TFp hTF
  dev0 := hUL
  dev2 := hUR
  annC := CB_annihilates νp TFp hTF
  annR := RB_annihilates νp TFp hTF
  normR := hJRc υ (fun i => cF * rp i) hTF hUL hUR hCF
  lowerE Φ := by
    rw [← kf_EB_eform]
    exact hEB Φ
  joint Φ Ψ := by
    have hkJ0 : 0 ≤ kJ := le_trans (by positivity) hkJ
    have hJ := hJRb (cF * r) (cE * r) (kJ * r) (fun i => kJ * rp i)
      (fun i => ⟨fun x _ => (foldCov_annihilates _ _ (hTF i)).1 x,
        fun y _ => (foldCov_annihilates _ _ (hTF i)).2 y⟩)
      (fun i => matchCov_annihilates _ _ (hTE i))
      (fun i x y => by simp only [matchCov, hTEsymm i x y])
      (fun i => FormBound.mono (hCF i) (mul_le_mul_of_nonneg_left (hrp i) hcF)) hcFr
      (fun i => FormBound.mono (hCE i) (mul_le_mul_of_nonneg_left (hrp i) hcE)) hcEr hJp
      (by nlinarith [mul_le_mul_of_nonneg_right hkJ hr])
      (fun i => mul_le_mul_of_nonneg_left (hrp i) hkJ0)
    have h2 : -(kJ * r) * (nrm (blockLaw νp) Φ ^ 2 + nrm (blockLaw νp) Ψ ^ 2) ≤
        kf (blockLaw νp) (EB TEp) Φ Φ + 2 * kf (blockLaw νp) (CB νp TFp) Φ Ψ +
          kf (blockLaw νp) (EB TEp) Ψ Ψ := hJ Φ Ψ
    rw [kf_EB_eform, kf_EB_eform] at h2
    exact h2

/-- **`cor:joint-completion-blocks`.** In the setting of `blockJointData` (with `0 ≤ r_p`):
* the matching kernel `T_E^b = ⊗_p T_{E,p}` has exact marginals, as `lem:five-type`(c), (f)
  require;
* the joint data of `lem:five-type`(f) hold at `b` with `φ₀ = U_L`, `φ₂ = U_R`, `C_b = C_𝔅`,
  `R_b = R_𝔅`, `ε_E = hr`, `κ_J = k_J r` and `ε_T = E_T`;
* `E_T ≤ (2υ + υ²)(e^{n c_F r} − 1)` whenever `𝔅` has at most `n` primes.

`lem:joint-rows` (b), (c) are hypotheses (`hJRb`, `hJRc`). -/
theorem joint_completion_blocks (νp : ∀ i, FiniteLaw (Xp i)) (TEp TFp : ∀ i, Xp i → Xp i → ℝ)
    (rp : ι → ℝ) {r cF cE kJ h H υ mb : ℝ}
    (hTE : ∀ i, ExactMarginals (νp i) (TEp i)) (hTEsymm : ∀ i x y, TEp i x y = TEp i y x)
    (hTF : ∀ i, kf (νp i) (TFp i) (fun _ => 1) (fun _ => 1) = 1)
    (hr : 0 ≤ r) (hrp : ∀ i, 0 ≤ rp i ∧ rp i ≤ r) (hcF : 0 ≤ cF) (hcE : 0 ≤ cE)
    (hCF : ∀ i, FormBound (νp i) (foldCov (νp i) (TFp i)) (cF * rp i))
    (hCE : ∀ i, FormBound (νp i) (matchCov (TEp i)) (cE * rp i))
    (hJp : ∀ i, JointBlockLower (νp i) (matchCov (TEp i)) (foldCov (νp i) (TFp i)) (kJ * rp i))
    (hcFr : cF * r < 1) (hcEr : cE * r < 1) (hkJ : (cF ^ 2 + cE ^ 2) * r ≤ kJ)
    (hm0 : H⁻¹ ≤ mb) (hm1 : mb ≤ H)
    (hUL : nrm (blockLaw νp) (fun x => UL νp TFp x - 1) ≤ υ)
    (hUR : nrm (blockLaw νp) (fun x => UR νp TFp x - 1) ≤ υ)
    (hEB : ∀ Φ, -(h * r) * nrm (blockLaw νp) Φ ^ 2 ≤ kf (blockLaw νp) (EB TEp) Φ Φ)
    (hJRb : JointRowsB νp (fun i => matchCov (TEp i)) (fun i => foldCov (νp i) (TFp i)))
    (hJRc : JointRowsC νp TFp) :
    ExactMarginals (blockLaw νp) (prodKernel TEp) ∧
    (∃ J : JointData (blockLaw νp) (prodKernel TEp) (fun x y => mb * prodKernel TFp x y) H υ
        (ET υ cF rp) (h * r) (kJ * r),
      J.m = mb ∧ J.φ0 = UL νp TFp ∧ J.φ2 = UR νp TFp ∧ J.C = CB νp TFp ∧ J.R = RB νp TFp) ∧
    ∀ n : ℕ, Fintype.card ι ≤ n → ET υ cF rp ≤ (2 * υ + υ ^ 2) * (Real.exp (n * cF * r) - 1) := by
  refine ⟨prodKernel_exactMarginals νp TEp hTE,
    ⟨blockJointData νp TEp TFp rp hTE hTEsymm hTF hr (fun i => (hrp i).2) hcF hcE hCF hCE hJp
      hcFr hcEr hkJ hm0 hm1 hUL hUR hEB hJRb hJRc, rfl, rfl, rfl, rfl, rfl⟩, fun n hn => ?_⟩
  exact ET_le_exp ((nrm_nonneg _ _).trans hUL) hcF hr hrp hn

end Block

/-- **`cor:joint-completion-blocks`, the completion inequalities.** If `t_Y ≤ H⁻¹`,
`M ≥ H + t_Y`, `f ≥ f_J` and `w_D ≥ 0`, the completion inequalities `w_D ≥ d w_L`,
`w_S ≥ M w_D`, `w_R ≥ f w_D + h w_S`, `w_C w_S ≥ w_R²` imply the graded conditions of
`lem:five-type`(f): `w_D ≥ d w_L`, `w_S ≥ (H + t_Y) w_D`, `w_R ≥ f_J w_D + h w_S`,
`w_C w_S ≥ w_R²`, together with `t_Y ≤ H⁻¹`. Here `f_J = fJ H k_J h r ε_T t_Y υ`, with
`ε_T = E_T` on a block. (The condition `t_Y > 0` of the corollary is needed by
`lem:five-type`(f) itself, not by this implication.) -/
theorem joint_completion_graded {w : Ty → ℝ} {d M f H h kJ r εT tY υ : ℝ}
    (htYH : tY ≤ H⁻¹) (hM : H + tY ≤ M) (hf : fJ H kJ h r εT tY υ ≤ f) (hwD : 0 ≤ w .D)
    (h1 : d * w .L ≤ w .D) (h2 : M * w .D ≤ w .S) (h3 : f * w .D + h * w .S ≤ w .R)
    (h4 : w .R ^ 2 ≤ w .C * w .S) :
    d * w .L ≤ w .D ∧ (H + tY) * w .D ≤ w .S ∧ fJ H kJ h r εT tY υ * w .D + h * w .S ≤ w .R ∧
      w .R ^ 2 ≤ w .C * w .S ∧ tY ≤ H⁻¹ := by
  refine ⟨h1, le_trans (mul_le_mul_of_nonneg_right hM hwD) h2, ?_, h4, htYH⟩
  have := mul_le_mul_of_nonneg_right hf hwD
  linarith

end Blocks

end Sarkozy.FiveType
