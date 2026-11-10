module

public import Sarkozy.SignedGram.Block
public import Sarkozy.SignedGram.Sector

@[expose] public section

/-!
# The block Gram of a middle block from the prime Grams and the sector bounds (SGA)

`paper/sections/24_matching_mean.tex`, `lem:record:asymmetric-gram`(b) at the paper's records:
the old block operator is `⊗_p T_{old,p}` (the kernel `K₀ = ⊗_p λ_p(G_{F,2})`), the new one is
`∑_c α_c ⊗_p T'_{c,p}` (B8's components `P_{c,p}` of `F₁`, `α = (1, t/2, -t/2)`), all couplings
with both half marginals `m_{0,p}` (`lem:signed-components`(d), B8's `FoldPrimeComponents.half`).

At the prime `p_i` of the block, on `A_i = (ℤ/p_i)³`:
* `mP i` = `m_{0,p_i}` (B8's `m0`), `oldP i` = the coupling `K₀(x, y)` (B8's `K0`), `compP C c i`
  = the coupling `P_{c,p_i}(x, y)`; `oldP_coupling`, `compP_coupling` (both marginals `m₀`).

* **`opGram_of_sectors`**: if the prime Gram `PrimeGram` holds at every prime of the block with
  the shifts `σ` and every sector of at least two primes has `MultiBound` with `a + n ≤ σ`, then
  `OpGram K₀ K'_{F₁} σ σ` (the block Gram on `L²(m_{0,𝔅})²`). This is
  `lem:record:asymmetric-gram`(b) with `σ_s = r_b max(c_s(X), c_{≥2}(X) r_X)`; the transport
  between the kernel forms on `(BlockLabel)^{3×2}` and the matrices on `∏_p (ℤ/p)³` is
  `kform_eq_dot`, `mform_eq_dot`.
-/

open Finset Matrix
open scoped BigOperators

namespace Sarkozy.SignedGram

open Sarkozy.PartV Sarkozy.Labellings Sarkozy.SignedComponents Sarkozy.MiddleComparison
open Sarkozy.IndexSupport Sarkozy.Mixing

section Block

variable {ι : Type} [Fintype ι] [DecidableEq ι] {pr : ι → ℕ} [∀ i, Fact (pr i).Prime]
  (hne : MiddleNonempty pr)

/-- The half triples at the prime `p_i`. -/
abbrev Ai (pr : ι → ℕ) (i : ι) : Type := Fin 3 → ZMod (pr i)

/-- The half marginal `m_{0,p_i}`. -/
noncomputable def mP (i : ι) : Ai pr i → ℝ := (m0 (hne.F2 i)).weight

/-- The coupling `K₀` of `T_{old}` at the prime `p_i`. -/
noncomputable def oldP (i : ι) : Matrix (Ai pr i) (Ai pr i) ℝ :=
  fun a b => (K0 (hne.F2 i)).weight (toY (a, b))

/-- The coupling `P_{c,p_i}` of the component `c` of `F₁` at the prime `p_i`. -/
noncomputable def compP (C : FoldComponents pr hne) (c : Fin 3) (i : ι) :
    Matrix (Ai pr i) (Ai pr i) ℝ :=
  fun a b => ((C i).law 0 c).weight (toY (a, b))

/-- Sums over two-layer labellings as sums over pairs of halves. -/
theorem sum_pair {F : Type} [Field F] [Fintype F] [DecidableEq F] (f : (Fin 3 × Fin 2 → F) → ℝ) :
    ∑ y, f y = ∑ a, ∑ b, f (toY (a, b)) := by
  rw [← Equiv.sum_comp pairEquiv, Fintype.sum_prod_type]
  rfl

omit [DecidableEq ι] in
theorem lay_toY_eq {F : Type} [Field F] (a b : Fin 3 → F) (ℓ : Fin 2) :
    lay (toY (a, b)) ℓ = if ℓ = 0 then a else b := by
  fin_cases ℓ
  · exact lay_toY_zero (a, b)
  · exact lay_toY_one (a, b)

/-- The two marginals of a law on two-layer labellings, as sums over pairs of halves. -/
theorem marg_row {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (μ : FiniteLaw (Fin 3 × Fin 2 → F)) (a : Fin 3 → F) :
    ∑ b, μ.weight (toY (a, b)) = μ.expect (fun y => if lay y 0 = a then 1 else 0) := by
  have h : ∀ a' : Fin 3 → F, (∑ b, μ.weight (toY (a', b)) *
      (if lay (toY (a', b)) 0 = a then 1 else 0)) =
      if a' = a then ∑ b, μ.weight (toY (a, b)) else 0 := by
    intro a'
    by_cases h : a' = a
    · subst h
      simp [lay_toY_zero]
    · simp [lay_toY_zero, h]
  unfold FiniteLaw.expect
  rw [sum_pair]
  simp only [h]
  simp

theorem marg_col {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (μ : FiniteLaw (Fin 3 × Fin 2 → F)) (b : Fin 3 → F) :
    ∑ a, μ.weight (toY (a, b)) = μ.expect (fun y => if lay y 1 = b then 1 else 0) := by
  have h : ∀ a' : Fin 3 → F, (∑ b', μ.weight (toY (a', b')) *
      (if lay (toY (a', b')) 1 = b then 1 else 0)) = μ.weight (toY (a', b)) := by
    intro a'
    simp [lay_toY_one]
  unfold FiniteLaw.expect
  rw [sum_pair]
  simp only [h]

theorem m0_weight_expect {F : Type} [Field F] [Fintype F] [DecidableEq F]
    (hF : (injLabellings F (foldGraph (Fin 2))).Nonempty) (a : Fin 3 → F) :
    (m0 hF).weight a = (K0 hF).expect (fun y => if lay y 0 = a then 1 else 0) := by
  change (∑ y, if lay y 0 = a then (K0 hF).weight y else 0) = _
  unfold FiniteLaw.expect
  refine sum_congr rfl fun y _ => ?_
  by_cases h : lay y 0 = a <;> simp [h]

omit [Fintype ι] [DecidableEq ι] in
/-- **`K₀` is a coupling with both marginals `m₀`.** -/
theorem oldP_coupling : IsCoupling (mP hne) (oldP hne) where
  row i a := by
    simp only [oldP, mP]
    rw [marg_row, m0_weight_expect]
  col i b := by
    simp only [oldP, mP]
    rw [marg_col]
    have h := m0_layer1 (hne.F2 i) b
    rw [← h]
    unfold FiniteLaw.expect
    refine sum_congr rfl fun y _ => ?_
    by_cases h' : lay y 1 = b <;> simp [h']

omit [Fintype ι] [DecidableEq ι] in
/-- **The components `P_{c,p}` are couplings with both marginals `m₀`**
(`lem:signed-components`(d), B8's `half`). -/
theorem compP_coupling (C : FoldComponents pr hne) (c : Fin 3) :
    IsCoupling (mP hne) (compP hne C c) where
  row i a := by
    simp only [compP, mP]
    rw [marg_row, m0_weight_expect]
    exact (C i).half 0 c 0 (fun x => if x = a then 1 else 0)
  col i b := by
    simp only [compP, mP]
    rw [marg_col, m0_weight_expect]
    exact (C i).half 0 c 1 (fun x => if x = b then 1 else 0)

omit [Fintype ι] [DecidableEq ι] in
theorem mP_nonneg (i : ι) (a : Ai pr i) : 0 ≤ mP hne i a := (m0 (hne.F2 i)).nonneg a

omit [Fintype ι] [DecidableEq ι] in
theorem mP_total (i : ι) : ∑ a, mP hne i a = 1 := (m0 (hne.F2 i)).total

/-! ## Kernel forms as matrix forms -/

omit [Fintype ι] [DecidableEq ι] [∀ i, Fact (pr i).Prime] in
/-- The block triple of a family of prime triples. -/
def eX (u : ∀ i, Ai pr i) : Fin 3 → BlockLabel pr := fun o i => u i o

/-- The two-layer block labelling of two families of prime triples. -/
def pairY (u u' : ∀ i, Ai pr i) : Fin 3 × Fin 2 → BlockLabel pr :=
  fun w i => toY (u i, u' i) w

/-- `pairY` as an equivalence. -/
def pairE : (∀ i, Ai pr i) × (∀ i, Ai pr i) ≃ (Fin 3 × Fin 2 → BlockLabel pr) where
  toFun p := pairY p.1 p.2
  invFun y := (fun i o => y (o, 0) i, fun i o => y (o, 1) i)
  left_inv p := by
    obtain ⟨u, u'⟩ := p
    ext i o
    · simp [pairY, toY]
    · simp [pairY, toY]
  right_inv y := by
    funext ⟨o, l⟩ i
    fin_cases l <;> simp [pairY, toY]

omit [Fintype ι] [DecidableEq ι] [∀ i, Fact (pr i).Prime] in
theorem lay2_pairY (u u' : ∀ i, Ai pr i) :
    lay2 (pairY u u') 0 = eX u ∧ lay2 (pairY u u') 1 = eX u' := by
  constructor
  · funext o i
    simp [lay2, pairY, eX, toY]
  · funext o i
    simp [lay2, pairY, eX, toY]

/-- The matrix of a weight on two-layer block labellings. -/
noncomputable def matW (W : (Fin 3 × Fin 2 → BlockLabel pr) → ℝ) :
    Matrix (∀ i, Ai pr i) (∀ i, Ai pr i) ℝ :=
  fun u u' => W (pairY u u')

theorem kform_eq_dot (W : (Fin 3 × Fin 2 → BlockLabel pr) → ℝ) (φ ψ : (Fin 3 → BlockLabel pr) → ℝ) :
    kform W φ ψ = (fun u => φ (eX u)) ⬝ᵥ (matW W *ᵥ fun u => ψ (eX u)) := by
  unfold kform
  rw [← Equiv.sum_comp pairE, Fintype.sum_prod_type]
  simp only [dotProduct, Matrix.mulVec, Finset.mul_sum]
  refine sum_congr rfl fun u _ => sum_congr rfl fun u' _ => ?_
  change W (pairY u u') * (φ (lay2 (pairY u u') 0) * ψ (lay2 (pairY u u') 1)) = _
  rw [(lay2_pairY u u').1, (lay2_pairY u u').2, matW]
  ring

theorem matW_lawF : matW (lawF pr hne).weight = piKron (oldP hne) := by
  ext u u'
  simp only [matW, lawF, blockGraphLaw, piKron_apply, oldP]
  rw [tensor_weight]
  rfl

theorem matW_newW (C : FoldComponents pr hne) (t : ℝ) :
    matW (newW C t 0) = ∑ c, signedCoef t c • piKron (compP hne C c) := by
  ext u u'
  simp only [matW, newW, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, piKron_apply, compP]
  refine sum_congr rfl fun c _ => ?_
  congr 1
  unfold foldLaw
  rw [tensor_weight]
  rfl

theorem mform_eq_dot (φ : (Fin 3 → BlockLabel pr) → ℝ) :
    mform (lawF pr hne).weight φ = (fun u => φ (eX u)) ⬝ᵥ
      (Matrix.diagonal (prodW (mP hne)) *ᵥ fun u => φ (eX u)) := by
  unfold mform
  rw [← Equiv.sum_comp pairE, Fintype.sum_prod_type]
  simp only [dotProduct, Matrix.mulVec_diagonal]
  refine sum_congr rfl fun u _ => ?_
  have hrow : ∑ u', (lawF pr hne).weight (pairY u u') = prodW (mP hne) u := by
    have h := congrFun (congrFun (matW_lawF hne) u)
    simp only [matW] at h
    simp only [h, piKron_apply, prodW]
    rw [← Fintype.prod_sum]
    exact prod_congr rfl fun i _ => (oldP_coupling hne).row i (u i)
  change ∑ u', (lawF pr hne).weight (pairY u u') *
    (φ (lay2 (pairY u u') 0) * φ (lay2 (pairY u u') 0)) = _
  simp only [(lay2_pairY u _).1]
  rw [← Finset.sum_mul, hrow]
  ring

/-- **`lem:record:asymmetric-gram`(b) at a middle block** (the sector argument): the prime Grams
of the signed record of `F₁` at every prime with the shifts `σ`, and the bounds `a + n ≤ σ` on the
sectors of at least two primes, give the block Gram `OpGram K₀ K'_{F₁} σ σ` on `L²(m_{0,𝔅})²`. -/
theorem opGram_of_sectors (C : FoldComponents pr hne) (t : ℝ) {σ : ℝ} (hσ : 0 ≤ σ)
    (hprime : ∀ i, PrimeGram (mP hne) (oldP hne) (compP hne C) (signedCoef t) σ σ i)
    (hmulti : ∀ l : ι → Bool, 2 ≤ (univ.filter fun j => l j = true).card →
      MultiBound (mP hne) (piKron (oldP hne)) (∑ c, signedCoef t c • piKron (compP hne C c)) σ l) :
    OpGram (lawF pr hne).weight (newW C t 0) σ σ := by
  intro φ ψ
  have h := block_gram_matrix (mP_nonneg hne) (mP_total hne) (sum_signedCoef t)
    (oldP_coupling hne) (compP_coupling hne C) hσ hprime hmulti (fun u => φ (eX u))
    (fun u => ψ (eX u))
  unfold gform at h
  rw [kform_eq_dot, kform_eq_dot, kform_eq_dot, mform_eq_dot, mform_eq_dot, matW_lawF hne,
    matW_newW hne]
  exact h

end Block

end Sarkozy.SignedGram
