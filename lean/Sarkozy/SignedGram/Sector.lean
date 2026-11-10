module

public import Sarkozy.Mixing.SectorLemma

@[expose] public section

/-!
# The block extension of a Gram over the sectors of a product space (SGA)

`paper/sections/24_matching_mean.tex`, `lem:record:asymmetric-gram`(b), the sector argument of its
proof; `lem:sector`(a) and `rem:signed-mixture-sectors` for products of couplings.

On a finite product `∏_j A_j` with probability weights `m_j`, operators are given by their
coupling matrices: a coupling `C_j` with both marginals `m_j` is the kernel of a Markov operator
`T_j` of `L²(m_j)` fixing the constants on both sides, and `⟨f, T_j g⟩_{m_j} = f ⬝ (C_j g)`. The
block operator of a product coupling is `piKron C`; the identity of `L²(⊗ m_j)` is
`diagonal (prodW m)`.

* `SP m l`: the projection onto the sector `H_S`, `S = {j : l_j}` (mean zero in the coordinates of
  `S`, constant in the others), the Kronecker product of MX's weighted coordinate projections;
  `sum_SP` (`∑_S P_S = 1`), `SP_mul_self`;
* **`SP_comm`**: a product of couplings with marginals `m_j` commutes with every `P_S` (as
  `P_Sᵀ C = C P_S`); **`dot_decomp`**: then `φ ⬝ (C ψ) = ∑_S (P_S φ) ⬝ (C (P_S ψ))`, the
  orthogonal sum over the sectors;
* `SP_congr`: `P_S φ` depends only on the coordinates in `S`; `dot_piKron_prod`: the form of a
  product coupling at product functions factorizes;
* **`block_gram_matrix`** (`lem:record:asymmetric-gram`(b) on `L²(⊗ m_j)²`): if the old operator
  is a product of couplings `C₀`, the new one a combination `∑_c α_c ⊗_j P_{c,j}` of products of
  couplings with `∑_c α_c = 1`, the prime Gram holds at every coordinate with shifts `σ_L, σ_R`
  (`PrimeGram`), and on every sector of at least two coordinates the restrictions of the old and
  new operators have norms `a, n` with `a + n ≤ σ_s` (`MultiBound`), then the block Gram holds with
  the shifts `σ_s I`.
-/

open Finset Matrix
open scoped BigOperators

namespace Sarkozy.SignedGram

open Sarkozy.IndexSupport Sarkozy.Mixing

section Coord

variable {B : Type} [Fintype B] [DecidableEq B]

omit [DecidableEq B] in
theorem avg_comm {μ : B → ℝ} {C : Matrix B B ℝ} (hrow : ∀ a, ∑ b, C a b = μ a)
    (hcol : ∀ b, ∑ a, C a b = μ b) : (avgMatrix μ)ᵀ * C = C * avgMatrix μ := by
  ext a b
  simp only [Matrix.mul_apply, Matrix.transpose_apply, avgMatrix]
  rw [← Finset.mul_sum, ← Finset.sum_mul, hcol, hrow]

theorem wProj_comm {μ : B → ℝ} {C : Matrix B B ℝ} (hrow : ∀ a, ∑ b, C a b = μ a)
    (hcol : ∀ b, ∑ a, C a b = μ b) (s : Bool) :
    (wProj μ false s)ᵀ * C = C * wProj μ false s := by
  have h := avg_comm hrow hcol
  cases s
  · simpa [wProj] using h
  · simp only [wProj, Bool.false_eq_true, ite_false, ite_true, Matrix.transpose_sub,
      Matrix.transpose_one, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, h]

end Coord

section Matrices

variable {K : Type} [Fintype K] [DecidableEq K] {A : K → Type} [∀ j, Fintype (A j)]
  [∀ j, DecidableEq (A j)] (m : ∀ j, A j → ℝ)

/-- The projection onto the sector `H_S`, `S = {j : l_j = true}`, of `L²(⊗_j m_j)`. -/
noncomputable def SP (l : K → Bool) : Matrix (∀ j, A j) (∀ j, A j) ℝ :=
  piKron (fun j => wProj (m j) false (l j))

theorem sum_SP : ∑ l, SP m l = 1 := by
  unfold SP
  rw [piKron_sum (fun j (s : Bool) => wProj (m j) false s)]
  have h : ∀ j, ∑ s : Bool, wProj (m j) false s = 1 := fun j => by
    rw [Fintype.sum_bool, add_comm, wProj_sum]
  simp only [h]
  exact piKron_one

theorem SP_mul_self (hm1 : ∀ j, ∑ a, m j a = 1) (l : K → Bool) : SP m l * SP m l = SP m l := by
  unfold SP
  rw [piKron_mul]
  congr 1
  funext j
  rw [wProj_mul (hm1 j)]
  simp

/-- **Couplings with both marginals `m_j`** (Markov operators of `L²(m_j)` fixing the constants on
both sides). -/
structure IsCoupling (C : ∀ j, Matrix (A j) (A j) ℝ) : Prop where
  row : ∀ j a, ∑ b, C j a b = m j a
  col : ∀ j b, ∑ a, C j a b = m j b

variable {m}

/-- **`lem:sector`(a)**: a product of couplings commutes with the sector projections. -/
theorem SP_comm {C : ∀ j, Matrix (A j) (A j) ℝ} (hC : IsCoupling m C) (l : K → Bool) :
    (SP m l)ᵀ * piKron C = piKron C * SP m l := by
  unfold SP
  rw [piKron_transpose, piKron_mul, piKron_mul]
  congr 1
  funext j
  exact wProj_comm (hC.row j) (hC.col j) (l j)

omit [Fintype K] [DecidableEq K] in
theorem diagonal_coupling : IsCoupling m (fun j => Matrix.diagonal (m j)) where
  row j a := by simp [Matrix.diagonal_apply]
  col j b := by simp [Matrix.diagonal_apply]

/-- **The orthogonal decomposition over the sectors**: if `M` commutes with every `P_S`, then
`φ ⬝ (M ψ) = ∑_S (P_S φ) ⬝ (M (P_S ψ))`. -/
theorem dot_decomp (hm1 : ∀ j, ∑ a, m j a = 1) {M : Matrix (∀ j, A j) (∀ j, A j) ℝ}
    (hM : ∀ l, (SP m l)ᵀ * M = M * SP m l) (φ ψ : (∀ j, A j) → ℝ) :
    φ ⬝ᵥ (M *ᵥ ψ) = ∑ l, (SP m l *ᵥ φ) ⬝ᵥ (M *ᵥ (SP m l *ᵥ ψ)) := by
  have key : ∀ l, (SP m l *ᵥ φ) ⬝ᵥ (M *ᵥ (SP m l *ᵥ ψ)) = φ ⬝ᵥ (M *ᵥ (SP m l *ᵥ ψ)) := by
    intro l
    rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, dotProduct_comm,
      Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hM l, Matrix.mul_assoc,
      SP_mul_self m hm1, ← Matrix.mulVec_mulVec]
  simp only [key]
  rw [← dotProduct_sum, ← Matrix.mulVec_sum, ← Matrix.sum_mulVec, sum_SP, Matrix.one_mulVec]

theorem comm_add {M N : Matrix (∀ j, A j) (∀ j, A j) ℝ} {l : K → Bool}
    (hM : (SP m l)ᵀ * M = M * SP m l) (hN : (SP m l)ᵀ * N = N * SP m l) :
    (SP m l)ᵀ * (M + N) = (M + N) * SP m l := by
  rw [Matrix.mul_add, Matrix.add_mul, hM, hN]

theorem comm_sum {ι : Type} (s : Finset ι) (α : ι → ℝ) (M : ι → Matrix (∀ j, A j) (∀ j, A j) ℝ)
    {l : K → Bool} (hM : ∀ c, (SP m l)ᵀ * M c = M c * SP m l) :
    (SP m l)ᵀ * (∑ c ∈ s, α c • M c) = (∑ c ∈ s, α c • M c) * SP m l := by
  rw [Matrix.mul_sum, Matrix.sum_mul]
  refine sum_congr rfl fun c _ => ?_
  rw [Matrix.mul_smul, Matrix.smul_mul, hM c]

/-- **`P_S φ` depends only on the coordinates in `S`** (it is constant in the others). -/
theorem SP_congr (l : K → Bool) (φ : (∀ j, A j) → ℝ) {x x' : ∀ j, A j}
    (h : ∀ j, l j = true → x j = x' j) : (SP m l *ᵥ φ) x = (SP m l *ᵥ φ) x' := by
  simp only [SP, Matrix.mulVec, dotProduct, piKron_apply]
  refine sum_congr rfl fun y _ => ?_
  congr 1
  refine prod_congr rfl fun j _ => ?_
  cases hj : l j
  · simp [wProj, avgMatrix]
  · rw [h j hj]

omit [∀ j, DecidableEq (A j)] in
/-- **The form of a product coupling at product functions factorizes.** -/
theorem dot_piKron_prod (C : ∀ j, Matrix (A j) (A j) ℝ) (u v : ∀ j, A j → ℝ) :
    (fun x => ∏ j, u j (x j)) ⬝ᵥ (piKron C *ᵥ fun y => ∏ j, v j (y j)) =
      ∏ j, (u j ⬝ᵥ (C j *ᵥ v j)) := by
  simp only [dotProduct, Matrix.mulVec, piKron_apply]
  simp only [Finset.mul_sum]
  rw [Fintype.prod_sum]
  refine sum_congr rfl fun x _ => ?_
  rw [Fintype.prod_sum]
  refine sum_congr rfl fun y _ => ?_
  rw [← prod_mul_distrib, ← prod_mul_distrib]

/-- The product function equal to `f` at the coordinate `i` and to `1` elsewhere. -/
noncomputable def single (i : K) (f : A i → ℝ) : ∀ j, A j → ℝ :=
  Function.update (fun _ _ => (1 : ℝ)) i f

omit [∀ j, Fintype (A j)] [∀ j, DecidableEq (A j)] in
theorem prod_single (i : K) (f : A i → ℝ) (x : ∀ j, A j) :
    ∏ j, single i f j (x j) = f (x i) := by
  rw [Finset.prod_eq_single i (fun j _ hj => by simp [single, Function.update_of_ne hj])
    (by simp), single, Function.update_self]

omit [Fintype K] [DecidableEq K] [∀ j, DecidableEq (A j)] in
theorem one_dot_one {C : ∀ j, Matrix (A j) (A j) ℝ} (hC : IsCoupling m C)
    (hm1 : ∀ j, ∑ a, m j a = 1) (j : K) : (fun _ => (1 : ℝ)) ⬝ᵥ (C j *ᵥ fun _ => (1 : ℝ)) = 1 := by
  simp only [dotProduct, Matrix.mulVec, one_mul, mul_one, hC.row j, hm1 j]

omit [∀ j, DecidableEq (A j)] in
/-- **A product coupling at two functions of the coordinate `i`** is the coupling `C_i` at
them. -/
theorem dot_piKron_single {C : ∀ j, Matrix (A j) (A j) ℝ} (hC : IsCoupling m C)
    (hm1 : ∀ j, ∑ a, m j a = 1) (i : K) (f g : A i → ℝ) :
    (fun x => f (x i)) ⬝ᵥ (piKron C *ᵥ fun y => g (y i)) = f ⬝ᵥ (C i *ᵥ g) := by
  have e1 : (fun x : ∀ j, A j => f (x i)) = fun x => ∏ j, single i f j (x j) :=
    funext fun x => (prod_single i f x).symm
  have e2 : (fun y : ∀ j, A j => g (y i)) = fun y => ∏ j, single i g j (y j) :=
    funext fun y => (prod_single i g y).symm
  rw [e1, e2, dot_piKron_prod]
  rw [Finset.prod_eq_single i (fun j _ hj => by
    simp only [single, Function.update_of_ne hj]
    exact one_dot_one hC hm1 j) (by simp)]
  simp [single]

omit [∀ j, DecidableEq (A j)] in
/-- The total mass of a product coupling is one. -/
theorem dot_piKron_const {C : ∀ j, Matrix (A j) (A j) ℝ} (hC : IsCoupling m C)
    (hm1 : ∀ j, ∑ a, m j a = 1) (a b : ℝ) :
    (fun _ => a) ⬝ᵥ (piKron C *ᵥ fun _ => b) = a * b := by
  have h := dot_piKron_prod C (fun _ _ => (1 : ℝ)) (fun _ _ => (1 : ℝ))
  simp only [Finset.prod_const_one] at h
  rw [Finset.prod_eq_one fun j _ => one_dot_one hC hm1 j] at h
  have e : ∀ c : ℝ, (fun _ : ∀ j, A j => c) = c • fun _ => (1 : ℝ) := fun c => by
    funext x
    simp
  rw [e a, e b, Matrix.mulVec_smul, smul_dotProduct, dotProduct_smul, h]
  simp only [smul_eq_mul, mul_one]

/-! ## The block Gram -/

/-- The block Gram form `⟨φ, O φ⟩ + σ_L ‖φ‖² + 2 ⟨φ, N ψ⟩ + ⟨ψ, O ψ⟩ + σ_R ‖ψ‖²`. -/
noncomputable def gform (O N Dm : Matrix (∀ j, A j) (∀ j, A j) ℝ) (σL σR : ℝ)
    (φ ψ : (∀ j, A j) → ℝ) : ℝ :=
  φ ⬝ᵥ (O *ᵥ φ) + σL * (φ ⬝ᵥ (Dm *ᵥ φ)) + 2 * (φ ⬝ᵥ (N *ᵥ ψ)) + ψ ⬝ᵥ (O *ᵥ ψ) +
    σR * (ψ ⬝ᵥ (Dm *ᵥ ψ))

theorem gform_decomp (hm1 : ∀ j, ∑ a, m j a = 1) {O N Dm : Matrix (∀ j, A j) (∀ j, A j) ℝ}
    (hO : ∀ l, (SP m l)ᵀ * O = O * SP m l) (hN : ∀ l, (SP m l)ᵀ * N = N * SP m l)
    (hD : ∀ l, (SP m l)ᵀ * Dm = Dm * SP m l) (σL σR : ℝ) (φ ψ : (∀ j, A j) → ℝ) :
    gform O N Dm σL σR φ ψ = ∑ l, gform O N Dm σL σR (SP m l *ᵥ φ) (SP m l *ᵥ ψ) := by
  unfold gform
  rw [dot_decomp hm1 hO φ φ, dot_decomp hm1 hD φ φ, dot_decomp hm1 hN φ ψ,
    dot_decomp hm1 hO ψ ψ, dot_decomp hm1 hD ψ ψ]
  simp only [Finset.mul_sum, ← Finset.sum_add_distrib]

variable (m) in
/-- **The prime Gram at the coordinate `i`** (first hypothesis of
`lem:record:asymmetric-gram`(b)): on `L²(m_i)²`,
`(T_old + σ_L I   T'_i ; ·   T_old + σ_R I) ⪰ 0`, with `T'_i = ∑_c α_c T_{c,i}`. -/
def PrimeGram (C₀ : ∀ j, Matrix (A j) (A j) ℝ) (P : Fin 3 → ∀ j, Matrix (A j) (A j) ℝ)
    (α : Fin 3 → ℝ) (σL σR : ℝ) (i : K) : Prop :=
  ∀ f g : A i → ℝ, 0 ≤ f ⬝ᵥ (C₀ i *ᵥ f) + σL * (f ⬝ᵥ (Matrix.diagonal (m i) *ᵥ f)) +
    2 * (f ⬝ᵥ ((∑ c, α c • P c i) *ᵥ g)) + g ⬝ᵥ (C₀ i *ᵥ g) +
      σR * (g ⬝ᵥ (Matrix.diagonal (m i) *ᵥ g))

variable (m) in
/-- **The bound on the sectors of at least two coordinates** (second hypothesis of
`lem:record:asymmetric-gram`(b)): on `H_S`, the restrictions of the old operator `O` and of the new
one `N` have norms `a` and `n` with `a + n ≤ σ` (`|⟨f, O f⟩| ≤ a ‖f‖²` and
`2 |⟨f, N g⟩| ≤ n (‖f‖² + ‖g‖²)` on `H_S`, which is `‖N|_{H_S}‖ ≤ n` by homogeneity). -/
def MultiBound (O N : Matrix (∀ j, A j) (∀ j, A j) ℝ) (σ : ℝ) (l : K → Bool) : Prop :=
  ∃ a n : ℝ, 0 ≤ a ∧ 0 ≤ n ∧ a + n ≤ σ ∧ ∀ φ ψ : (∀ j, A j) → ℝ,
    |(SP m l *ᵥ φ) ⬝ᵥ (O *ᵥ (SP m l *ᵥ φ))| ≤
        a * ((SP m l *ᵥ φ) ⬝ᵥ (Matrix.diagonal (prodW m) *ᵥ (SP m l *ᵥ φ))) ∧
      2 * |(SP m l *ᵥ φ) ⬝ᵥ (N *ᵥ (SP m l *ᵥ ψ))| ≤
        n * ((SP m l *ᵥ φ) ⬝ᵥ (Matrix.diagonal (prodW m) *ᵥ (SP m l *ᵥ φ)) +
          (SP m l *ᵥ ψ) ⬝ᵥ (Matrix.diagonal (prodW m) *ᵥ (SP m l *ᵥ ψ)))

variable (m) in
/-- **The prime Gram on the centred functions** (`prop:signed-sides`(i), proof: "On the centred
functions ..."): the form of `PrimeGram` is nonnegative at `m_i`-mean-zero `f, g`. -/
def PrimeGramC (C₀ : ∀ j, Matrix (A j) (A j) ℝ) (P : Fin 3 → ∀ j, Matrix (A j) (A j) ℝ)
    (α : Fin 3 → ℝ) (σL σR : ℝ) (i : K) : Prop :=
  ∀ f g : A i → ℝ, m i ⬝ᵥ f = 0 → m i ⬝ᵥ g = 0 →
    0 ≤ f ⬝ᵥ (C₀ i *ᵥ f) + σL * (f ⬝ᵥ (Matrix.diagonal (m i) *ᵥ f)) +
      2 * (f ⬝ᵥ ((∑ c, α c • P c i) *ᵥ g)) + g ⬝ᵥ (C₀ i *ᵥ g) +
        σR * (g ⬝ᵥ (Matrix.diagonal (m i) *ᵥ g))

omit [Fintype K] [DecidableEq K] [∀ j, DecidableEq (A j)] in
/-- **Centring a coupling**: if `M` has row and column sums `μ` (`∑ μ = 1`), then
`f ⬝ (M g) = (f - a) ⬝ (M (g - b)) + a b` with `a = μ ⬝ f`, `b = μ ⬝ g`. -/
theorem coupling_center {B : Type} [Fintype B] {μ : B → ℝ} {M : Matrix B B ℝ}
    (hrow : ∀ a, ∑ b, M a b = μ a) (hcol : ∀ b, ∑ a, M a b = μ b) (hμ1 : ∑ a, μ a = 1)
    (f g : B → ℝ) :
    f ⬝ᵥ (M *ᵥ g) = (f - (μ ⬝ᵥ f) • 1) ⬝ᵥ (M *ᵥ (g - (μ ⬝ᵥ g) • 1)) + (μ ⬝ᵥ f) * (μ ⬝ᵥ g) := by
  have h1 : M *ᵥ (1 : B → ℝ) = μ := by
    funext x
    simp [Matrix.mulVec, dotProduct, hrow]
  have h2 : (1 : B → ℝ) ⬝ᵥ (M *ᵥ g) = μ ⬝ᵥ g := by
    rw [Matrix.dotProduct_mulVec]
    congr 1
    funext y
    simp [Matrix.vecMul, dotProduct, hcol]
  have h3 : (1 : B → ℝ) ⬝ᵥ μ = 1 := by
    rw [one_dotProduct, hμ1]
  rw [Matrix.mulVec_sub, Matrix.mulVec_smul, h1, sub_dotProduct, dotProduct_sub, dotProduct_sub,
    smul_dotProduct, smul_dotProduct, dotProduct_smul, dotProduct_smul, h2, h3,
    dotProduct_comm f μ]
  simp only [smul_eq_mul]
  ring

omit [Fintype K] [DecidableEq K] [∀ j, DecidableEq (A j)] in
theorem center_mean {B : Type} [Fintype B] {μ : B → ℝ} (hμ1 : ∑ a, μ a = 1) (f : B → ℝ) :
    μ ⬝ᵥ (f - (μ ⬝ᵥ f) • 1) = 0 := by
  rw [dotProduct_sub, dotProduct_smul, dotProduct_one, hμ1, smul_eq_mul, mul_one, sub_self]

omit [Fintype K] [DecidableEq K] in
/-- **The prime Gram from its centred part** (`prop:signed-sides`(i), proof: on the constants it is
`[[1 + σ_L, 1], [1, 1 + σ_R]] ⪰ 0`, as `∑_c α_c = 1`). -/
theorem primeGram_of_centered (hm1 : ∀ j, ∑ a, m j a = 1)
    {C₀ : ∀ j, Matrix (A j) (A j) ℝ} {P : Fin 3 → ∀ j, Matrix (A j) (A j) ℝ} {α : Fin 3 → ℝ}
    (hα : ∑ c, α c = 1) (hC₀ : IsCoupling m C₀) (hP : ∀ c, IsCoupling m (P c)) {σL σR : ℝ}
    (hσL : 0 ≤ σL) (hσR : 0 ≤ σR) {i : K} (h : PrimeGramC m C₀ P α σL σR i) :
    PrimeGram m C₀ P α σL σR i := by
  intro f g
  have hD := (diagonal_coupling (m := m))
  have hNrow : ∀ a, ∑ b, (∑ c, α c • P c i) a b = m i a := fun a => by
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, (hP _).row i a, ← Finset.sum_mul, hα, one_mul]
  have hNcol : ∀ b, ∑ a, (∑ c, α c • P c i) a b = m i b := fun b => by
    simp only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, (hP _).col i b, ← Finset.sum_mul, hα, one_mul]
  rw [coupling_center (hC₀.row i) (hC₀.col i) (hm1 i) f f,
    coupling_center (hD.row i) (hD.col i) (hm1 i) f f,
    coupling_center hNrow hNcol (hm1 i) f g,
    coupling_center (hC₀.row i) (hC₀.col i) (hm1 i) g g,
    coupling_center (hD.row i) (hD.col i) (hm1 i) g g]
  have hc := h _ _ (center_mean (hm1 i) f) (center_mean (hm1 i) g)
  nlinarith [mul_self_nonneg (m i ⬝ᵥ f + m i ⬝ᵥ g), mul_nonneg hσL (mul_self_nonneg (m i ⬝ᵥ f)),
    mul_nonneg hσR (mul_self_nonneg (m i ⬝ᵥ g))]

theorem diag_nonneg (hm : ∀ j a, 0 ≤ m j a) (φ : (∀ j, A j) → ℝ) :
    0 ≤ φ ⬝ᵥ (Matrix.diagonal (prodW m) *ᵥ φ) := by
  simp only [dotProduct, Matrix.mulVec_diagonal]
  refine sum_nonneg fun x _ => ?_
  have : 0 ≤ prodW m x := prod_nonneg fun j _ => hm j (x j)
  nlinarith [mul_self_nonneg (φ x)]

/-- **`lem:record:asymmetric-gram`(b) on `L²(⊗_j m_j)²`** (the sector argument). -/
theorem block_gram_matrix (hm : ∀ j a, 0 ≤ m j a) (hm1 : ∀ j, ∑ a, m j a = 1)
    {C₀ : ∀ j, Matrix (A j) (A j) ℝ} {P : Fin 3 → ∀ j, Matrix (A j) (A j) ℝ} {α : Fin 3 → ℝ}
    (hα : ∑ c, α c = 1) (hC₀ : IsCoupling m C₀) (hP : ∀ c, IsCoupling m (P c)) {σ : ℝ}
    (hσ : 0 ≤ σ) (hprime : ∀ i, PrimeGram m C₀ P α σ σ i)
    (hmulti : ∀ l : K → Bool, 2 ≤ (univ.filter fun j => l j = true).card →
      MultiBound m (piKron C₀) (∑ c, α c • piKron (P c)) σ l)
    (φ ψ : (∀ j, A j) → ℝ) :
    0 ≤ gform (piKron C₀) (∑ c, α c • piKron (P c)) (Matrix.diagonal (prodW m)) σ σ φ ψ := by
  have hD : Matrix.diagonal (prodW m) = piKron fun j => Matrix.diagonal (m j) :=
    (piKron_diagonal m).symm
  rw [gform_decomp hm1 (SP_comm hC₀) (fun l => comm_sum univ α _ fun c => SP_comm (hP c) l)
    (fun l => by rw [hD]; exact SP_comm diagonal_coupling l)]
  refine sum_nonneg fun l _ => ?_
  set F := SP m l *ᵥ φ
  set G := SP m l *ᵥ ψ
  have hN : ∀ F G : (∀ j, A j) → ℝ, F ⬝ᵥ ((∑ c, α c • piKron (P c)) *ᵥ G) =
      ∑ c, α c * (F ⬝ᵥ (piKron (P c) *ᵥ G)) := by
    intro F G
    rw [Matrix.sum_mulVec, dotProduct_sum]
    refine sum_congr rfl fun c _ => ?_
    rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
  rcases Nat.lt_or_ge (univ.filter fun j => l j = true).card 2 with hlt | hge
  · rcases Nat.lt_or_ge (univ.filter fun j => l j = true).card 1 with h0 | h1
    · -- the constant sector
      have hl : ∀ j, l j = false := by
        intro j
        by_contra hj
        have : j ∈ univ.filter fun j => l j = true := by
          simp only [mem_filter, mem_univ, true_and]
          simpa using hj
        have := card_pos.mpr ⟨j, this⟩
        omega
      have hc : ∀ (χ : (∀ j, A j) → ℝ) (x x' : ∀ j, A j),
          (SP m l *ᵥ χ) x = (SP m l *ᵥ χ) x' := fun χ x x' =>
        SP_congr l χ (fun j hj => absurd hj (by simp [hl j]))
      obtain ⟨x₀⟩ : Nonempty (∀ j, A j) := by
        refine ⟨fun j => ?_⟩
        have : (univ : Finset (A j)).Nonempty := by
          by_contra hne
          rw [not_nonempty_iff_eq_empty] at hne
          have := hm1 j
          rw [hne, sum_empty] at this
          norm_num at this
        exact this.choose
      have hF : F = fun _ => F x₀ := funext fun x => hc φ x x₀
      have hG : G = fun _ => G x₀ := funext fun x => hc ψ x x₀
      unfold gform
      rw [hN, hF, hG, dot_piKron_const hC₀ hm1, dot_piKron_const hC₀ hm1, hD,
        dot_piKron_const diagonal_coupling hm1, dot_piKron_const diagonal_coupling hm1]
      simp only [dot_piKron_const (hP _) hm1]
      rw [show ∑ c, α c * (F x₀ * G x₀) = (∑ c, α c) * (F x₀ * G x₀) by rw [Finset.sum_mul], hα]
      nlinarith [mul_self_nonneg (F x₀ + G x₀), mul_self_nonneg (F x₀), mul_self_nonneg (G x₀)]
    · -- a sector of one coordinate `i`: the prime Gram
      have h1' : (univ.filter fun j => l j = true).card = 1 := by omega
      obtain ⟨i, hi⟩ := card_eq_one.mp h1'
      have hli : ∀ j, l j = true → j = i := by
        intro j hj
        have : j ∈ univ.filter fun j => l j = true := by simp [hj]
        rw [hi] at this
        exact mem_singleton.mp this
      obtain ⟨x₀⟩ : Nonempty (∀ j, A j) := by
        refine ⟨fun j => ?_⟩
        have : (univ : Finset (A j)).Nonempty := by
          by_contra hne
          rw [not_nonempty_iff_eq_empty] at hne
          have := hm1 j
          rw [hne, sum_empty] at this
          norm_num at this
        exact this.choose
      have hc : ∀ (χ : (∀ j, A j) → ℝ) (x : ∀ j, A j),
          (SP m l *ᵥ χ) x = (SP m l *ᵥ χ) (Function.update x₀ i (x i)) := by
        intro χ x
        refine SP_congr l χ fun j hj => ?_
        obtain rfl := hli j hj
        simp
      set f : A i → ℝ := fun a => F (Function.update x₀ i a)
      set g : A i → ℝ := fun a => G (Function.update x₀ i a)
      have hF : F = fun x => f (x i) := funext fun x => hc φ x
      have hG : G = fun x => g (x i) := funext fun x => hc ψ x
      have hP' : ∀ c, F ⬝ᵥ (piKron (P c) *ᵥ G) = f ⬝ᵥ (P c i *ᵥ g) := fun c => by
        rw [hF, hG]
        exact dot_piKron_single (hP c) hm1 i f g
      have hsum : ∑ c, α c * (f ⬝ᵥ (P c i *ᵥ g)) = f ⬝ᵥ ((∑ c, α c • P c i) *ᵥ g) := by
        rw [Matrix.sum_mulVec, dotProduct_sum]
        refine sum_congr rfl fun c _ => ?_
        rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul]
      have h := hprime i f g
      unfold gform
      rw [hN]
      simp only [hP']
      rw [hsum, hD, hF, hG, dot_piKron_single hC₀ hm1, dot_piKron_single hC₀ hm1,
        dot_piKron_single diagonal_coupling hm1, dot_piKron_single diagonal_coupling hm1]
      exact h
  · -- a sector of at least two coordinates
    obtain ⟨a, n, ha, hn, han, hb⟩ := hmulti l hge
    obtain ⟨hOF, hNF⟩ := hb φ ψ
    obtain ⟨hOG, -⟩ := hb ψ φ
    have dF := diag_nonneg hm F
    have dG := diag_nonneg hm G
    unfold gform
    have e1 := neg_abs_le (F ⬝ᵥ (piKron C₀ *ᵥ F))
    have e2 := neg_abs_le (G ⬝ᵥ (piKron C₀ *ᵥ G))
    have e3 := neg_abs_le (F ⬝ᵥ ((∑ c, α c • piKron (P c)) *ᵥ G))
    nlinarith [mul_le_mul_of_nonneg_right (show a + n ≤ σ from han) dF,
      mul_le_mul_of_nonneg_right (show a + n ≤ σ from han) dG]

end Matrices

end Sarkozy.SignedGram
