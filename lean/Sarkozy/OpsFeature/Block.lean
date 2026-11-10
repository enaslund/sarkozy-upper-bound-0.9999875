module

public import Sarkozy.OpsFeature.Edge34Prime
public import Sarkozy.OpsFeature.KernelTensor

@[expose] public section

/-!
# The five fold features in the actual block law, and the edge `34`
(`lem:oct24:feature-block`(a), proof Step 4)

`paper/sections/23_envelopes.tex`, `subsec:oct24:pure-features` and `lem:oct24:feature-block`(a).

**The features.** A block `𝔅` is a finite family of prime fields `F p`; a whole label is
`u : ∀ p, F p` (`Lab`), an object triple is `x : ∀ p, F p × F p × F p` (`Tri`), with the
coordinates `x₀, x₁, x₂` (`c0`, `c1`, `c2`), and the actual product marginal is B11's
`m_{0,𝔅} = m0B = ∏_p oldW_p/oldZ_p`. With the inner product `⟨h, k⟩ = ∑ m_{0,𝔅} h k` (`ipm`):
* `𝓗_a` (`IsH`): the functions `f(x_a)` with `f` mean-zero for the uniform law of one whole label
  (every coordinate of `m_{0,𝔅}` is uniform, B11's `norm_actual_x*`), the range of `V_a`;
* `𝒦_{ab}` (`IsK`): the functions of `(x_a, x_b)` orthogonal to every function of `x_a` and to
  every function of `x_b`, i.e. `ran(P_{ab} - 𝒥) ⊖ (𝓗_a + 𝓗_b)`; `𝒦₁₂ = IsK c1 c2`,
  `𝒦₀₁ = IsK c0 c1`.

**The edge `34`** (**`edge34_block`**): for `h ∈ 𝒦₁₂`, `k ∈ 𝒦₀₁`,
`|⟨h, k⟩| ≤ c √⟨h, h⟩ √⟨k, k⟩` for every `c ∈ [0, 1]` at least `ϱ₃₄(1/p, p^{-1/2})` at every prime.
The proof is the paper's: given the whole object `x₁ = y` the pairs `(x_{0,p}, x_{2,p})` are
conditionally independent with the kernels `oldW(·, y_p, ·)` (the sum over object triples factors,
`sum_tri`, `m0B_mk`); a function in `𝒦₀₁` has conditional mean zero given `x₁` (`condMean_K01`);
the prime bound `edge34_prime` tensorizes (`kernel_tensor_corr`, `cor:peyre-independent`), and
Cauchy–Schwarz over `y` (`cor:cond-decorrelation`) gives the block bound.
**`edge34_block_b`** takes `c = ϱ₃₄(1/b, b^{-1/2})` at the least prime `b ≥ Q₃` (`rho_mono`).
-/

open Finset
open scoped BigOperators

namespace Sarkozy.OpsFeature

open Sarkozy.MiddleRecords Sarkozy.Mixing Sarkozy.EnvelopeSteps Sarkozy.Envelopes

/-- Cauchy–Schwarz for a finite sum. -/
theorem abs_sum_mul_le' {ι : Type*} [Fintype ι] (φ ψ : ι → ℝ) :
    |∑ i, φ i * ψ i| ≤ Real.sqrt (∑ i, φ i ^ 2) * Real.sqrt (∑ i, ψ i ^ 2) := by
  have h := sum_mul_sq_le_sq_mul_sq univ φ ψ
  rw [← Real.sqrt_mul (sum_nonneg fun i _ => sq_nonneg _)]
  exact Real.abs_le_sqrt h

section Block

variable {P : Type*} [Fintype P] [DecidableEq P] {F : P → Type*} [∀ p, Field (F p)]
  [∀ p, Fintype (F p)] [∀ p, DecidableEq (F p)]

variable (F) in
/-- A whole label of the block. -/
abbrev Lab := ∀ p, F p

variable (F) in
/-- An object triple of the block. -/
abbrev Tri := ∀ p, F p × F p × F p

/-- The coordinate `x₀` of an object triple. -/
def c0 (x : Tri F) : Lab F := fun p => (x p).1

/-- The coordinate `x₁` of an object triple. -/
def c1 (x : Tri F) : Lab F := fun p => (x p).2.1

/-- The coordinate `x₂` of an object triple. -/
def c2 (x : Tri F) : Lab F := fun p => (x p).2.2

/-- The object triple with the coordinates `u, y, w`. -/
def mk (u y w : Lab F) : Tri F := fun p => (u p, y p, w p)

/-- The inner product of `L²(m_{0,𝔅})`. -/
noncomputable def ipm (h k : Tri F → ℝ) : ℝ := ∑ x, m0B x * h x * k x

/-- **The singleton feature `𝓗_a`**: `h = f(x_a)` with `f` mean-zero in the uniform law. -/
def IsH (π : Tri F → Lab F) (h : Tri F → ℝ) : Prop :=
  ∃ f : Lab F → ℝ, ∑ u, prodW unifB u * f u = 0 ∧ ∀ x, h x = f (π x)

/-- **The pure-pair feature `𝒦_{ab}`**: a function of `(x_a, x_b)` orthogonal in `L²(m_{0,𝔅})` to
every function of `x_a` and to every function of `x_b`. -/
def IsK (πa πb : Tri F → Lab F) (h : Tri F → ℝ) : Prop :=
  (∃ k : Lab F → Lab F → ℝ, ∀ x, h x = k (πa x) (πb x)) ∧
    (∀ g : Lab F → ℝ, ipm h (fun x => g (πa x)) = 0) ∧
    (∀ g : Lab F → ℝ, ipm h (fun x => g (πb x)) = 0)

/-- The normalization `∏_p 1/oldZ_p` of `m_{0,𝔅}`. -/
noncomputable def cz : ℝ := ∏ p, (oldZ (F := F p))⁻¹

omit [DecidableEq P] in
theorem m0B_mk (u y w : Lab F) :
    m0B (mk u y w) = cz (F := F) * ∏ p, oldW (u p) (y p) (w p) := by
  simp only [m0B, mk, cz, div_eq_mul_inv, prod_mul_distrib]
  ring

omit [∀ p, Field (F p)] [∀ p, DecidableEq (F p)] in
/-- The sum over object triples is the sum over their three coordinates. -/
theorem sum_tri (H : Tri F → ℝ) : ∑ x, H x = ∑ u, ∑ y, ∑ w, H (mk u y w) := by
  let e : Tri F ≃ Lab F × Lab F × Lab F :=
    { toFun := fun x => (c0 x, c1 x, c2 x)
      invFun := fun t => mk t.1 t.2.1 t.2.2
      left_inv := fun x => rfl
      right_inv := fun t => rfl }
  rw [← e.symm.sum_comp]
  simp only [Fintype.sum_prod_type]
  rfl

/-- **The sum in the actual block law, grouped by `x₁`**. -/
theorem sum_m0B (G : Lab F → Lab F → Lab F → ℝ) :
    ∑ x, m0B x * G (c0 x) (c1 x) (c2 x) =
      cz (F := F) * ∑ y, ∑ u, ∑ w, (∏ p, oldW (u p) (y p) (w p)) * G u y w := by
  rw [sum_tri]
  simp only [m0B_mk, mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun y _ => sum_congr rfl fun u _ => sum_congr rfl fun w _ => ?_
  show (cz (F := F) * ∏ p, oldW (u p) (y p) (w p)) * G u y w =
    cz (F := F) * ((∏ p, oldW (u p) (y p) (w p)) * G u y w)
  ring

omit [DecidableEq P] in
theorem cz_pos (hF : ∀ p, ringChar (F p) ≠ 2) (h3 : ∀ p, Fintype.card (F p) % 4 = 3)
    (h7 : ∀ p, (7 : ℝ) ≤ Fintype.card (F p)) : 0 < cz (F := F) :=
  prod_pos fun p _ => inv_pos.2 (oldZ_pos (hF p) (h3 p) (h7 p))

omit [DecidableEq P] in
theorem m0B_nonneg (h7 : ∀ p, (7 : ℝ) ≤ Fintype.card (F p)) (hF : ∀ p, ringChar (F p) ≠ 2)
    (h3 : ∀ p, Fintype.card (F p) % 4 = 3) (x : Tri F) : 0 ≤ m0B x :=
  prod_nonneg fun p _ => div_nonneg (oldW_nonneg (h7 p) _ _ _) (oldZ_pos (hF p) (h3 p) (h7 p)).le

/-- The product of the prime marginal sums. -/
theorem prod_marg0 (u y : Lab F) :
    ∑ w : Lab F, ∏ p, oldW (u p) (y p) (w p) = ∏ p, ∑ b, oldW (u p) (y p) b :=
  (Fintype.prod_sum (fun p b => oldW (u p) (y p) b)).symm

theorem prod_marg2 (y w : Lab F) :
    ∑ u : Lab F, ∏ p, oldW (u p) (y p) (w p) = ∏ p, ∑ a, oldW a (y p) (w p) :=
  (Fintype.prod_sum (fun p a => oldW a (y p) (w p))).symm

/-- **A function of `𝒦₀₁` has conditional mean zero given `x₁`**: for every whole label `y`,
`∑_u (∏_p W₀_p(u_p)) k(u, y) = 0`, `W₀_p(a) = ∑_b oldW(a, y_p, b)`. -/
theorem condMean_K01 (hF : ∀ p, ringChar (F p) ≠ 2) (h3 : ∀ p, Fintype.card (F p) % 4 = 3)
    (h7 : ∀ p, (7 : ℝ) ≤ Fintype.card (F p)) (k : Lab F → Lab F → ℝ)
    (hk : ∀ g : Lab F → ℝ, ipm (fun x => k (c0 x) (c1 x)) (fun x => g (c1 x)) = 0)
    (y : Lab F) :
    ∑ u, (∏ p, ∑ b, oldW (u p) (y p) b) * k u y = 0 := by
  have h := hk (fun y' => if y' = y then 1 else 0)
  unfold ipm at h
  have e := sum_m0B (F := F) (fun u y' _ => k u y' * (if y' = y then 1 else 0))
  simp only [mul_assoc] at h e
  rw [e] at h
  have hc := (cz_pos hF h3 h7).ne'
  have h1 : ∑ y' : Lab F, ∑ u : Lab F, ∑ w : Lab F,
      (∏ p, oldW (u p) (y' p) (w p)) * (k u y' * (if y' = y then 1 else 0)) =
      ∑ u : Lab F, ∑ w : Lab F, (∏ p, oldW (u p) (y p) (w p)) * k u y := by
    rw [Finset.sum_eq_single y]
    · simp
    · intro y' _ hy'
      simp [hy']
    · simp
  rw [h1] at h
  have h' : ∑ u : Lab F, ∑ w : Lab F, (∏ p, oldW (u p) (y p) (w p)) * k u y = 0 := by
    rcases mul_eq_zero.mp h with h | h
    · exact absurd h hc
    · exact h
  rw [← h']
  refine sum_congr rfl fun u _ => ?_
  rw [← prod_marg0, sum_mul]

/-- The prime constants `ϱ₃₄(p)` are at most the constant at the least prime `b`. -/
theorem rho34_le_b {x b : ℝ} (hb : 8 ≤ b) (hx : b ≤ x) :
    rho34 (1 / x) (1 / Real.sqrt x) ≤ rho34 (1 / b) (1 / Real.sqrt b) := by
  have hb0 : 0 < b := by linarith
  have hx0 : 0 < x := by linarith
  have hq : 1 / x ≤ 1 / b := one_div_le_one_div_of_le hb0 hx
  have hq8 : 1 / b ≤ 1 / 8 := one_div_le_one_div_of_le (by norm_num) hb
  have hr : 1 / Real.sqrt x ≤ 1 / Real.sqrt b :=
    one_div_le_one_div_of_le (Real.sqrt_pos.2 hb0) (Real.sqrt_le_sqrt hx)
  exact (rho_mono (by positivity) hq hq8 (by positivity) hr).2.2.2

/-- **`lem:oct24:feature-block`(a), the edge `34`, at a block**: for `h ∈ 𝒦₁₂` and `k ∈ 𝒦₀₁` in
the actual block law, `|⟨h, k⟩| ≤ c ‖h‖ ‖k‖` for every `c ∈ [0, 1]` with
`ϱ₃₄(1/p, p^{-1/2}) ≤ c` at every prime of the block. -/
theorem edge34_block (hF : ∀ p, ringChar (F p) ≠ 2) (h3 : ∀ p, Fintype.card (F p) % 4 = 3)
    (h7 : ∀ p, (7 : ℝ) ≤ Fintype.card (F p)) {c : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (hρc : ∀ p, rho34 (1 / (Fintype.card (F p) : ℝ)) (1 / Real.sqrt (Fintype.card (F p))) ≤ c)
    (h k : Tri F → ℝ) (hh : IsK c1 c2 h) (hk : IsK c0 c1 k) :
    |ipm h k| ≤ c * (Real.sqrt (ipm h h) * Real.sqrt (ipm k k)) := by
  obtain ⟨⟨K₁, hK₁⟩, -, -⟩ := hh
  obtain ⟨⟨K₀, hK₀⟩, -, hk1⟩ := hk
  have hk1' : ∀ g : Lab F → ℝ,
      ipm (fun x => K₀ (c0 x) (c1 x)) (fun x => g (c1 x)) = 0 := by
    intro g
    have := hk1 g
    unfold ipm at this ⊢
    simpa only [hK₀] using this
  have hcm := condMean_K01 hF h3 h7 K₀ hk1'
  -- the three sums in the block law, grouped by `x₁`
  set W : Lab F → Lab F → Lab F → ℝ := fun u y w => ∏ p, oldW (u p) (y p) (w p) with hWd
  have ehk : ipm h k = cz (F := F) * ∑ y, ∑ u, ∑ w, W u y w * K₀ u y * K₁ y w := by
    have e := sum_m0B (F := F) (fun u y w => K₁ y w * K₀ u y)
    unfold ipm
    simp only [hK₁, hK₀, mul_assoc]
    rw [e]
    congr 1
    exact sum_congr rfl fun y _ => sum_congr rfl fun u _ => sum_congr rfl fun w _ => by ring
  have ehh : ipm h h = cz (F := F) * ∑ y, ∑ w, (∏ p, ∑ a, oldW a (y p) (w p)) * K₁ y w ^ 2 := by
    have e := sum_m0B (F := F) (fun _ y w => K₁ y w ^ 2)
    unfold ipm
    simp only [hK₁, mul_assoc, ← sq]
    rw [e]
    congr 1
    refine sum_congr rfl fun y _ => ?_
    rw [sum_comm]
    refine sum_congr rfl fun w _ => ?_
    rw [← prod_marg2, sum_mul]
  have ekk : ipm k k = cz (F := F) * ∑ y, ∑ u, (∏ p, ∑ b, oldW (u p) (y p) b) * K₀ u y ^ 2 := by
    have e := sum_m0B (F := F) (fun u y _ => K₀ u y ^ 2)
    unfold ipm
    simp only [hK₀, mul_assoc, ← sq]
    rw [e]
    congr 1
    refine sum_congr rfl fun y _ => sum_congr rfl fun u _ => ?_
    rw [← prod_marg0, sum_mul]
  -- the conditional bound at every `y`
  have hy : ∀ y : Lab F, |∑ u, ∑ w, W u y w * K₀ u y * K₁ y w| ≤
      c * (Real.sqrt (∑ u, (∏ p, ∑ b, oldW (u p) (y p) b) * K₀ u y ^ 2) *
        Real.sqrt (∑ w, (∏ p, ∑ a, oldW a (y p) (w p)) * K₁ y w ^ 2)) := by
    intro y
    refine kernel_tensor_corr (fun p a b => oldW a (y p) b)
      (fun p a b => oldW_nonneg (h7 p) a (y p) b) (fun p => ?_) hc hc1 (fun p f g hf hg => ?_)
      (fun u => K₀ u y) (fun w => K₁ y w) (hcm y)
    · rw [sum_W0 (hF p) (h3 p) (y p)]
      have := h7 p
      have : 0 < (Fintype.card (F p) : ℝ) - 4 := by linarith
      have : 0 < (Fintype.card (F p) : ℝ) - 3 := by linarith
      have : 0 < (Fintype.card (F p) : ℝ) - 1 := by linarith
      positivity
    · have hb := edge34_prime (hF p) (h3 p) (h7 p) (y p) f g hf hg
      refine hb.trans (mul_le_mul_of_nonneg_right (hρc p) ?_)
      exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  -- Cauchy–Schwarz over `y`
  set A : Lab F → ℝ := fun y => ∑ u, (∏ p, ∑ b, oldW (u p) (y p) b) * K₀ u y ^ 2 with hA
  set B : Lab F → ℝ := fun y => ∑ w, (∏ p, ∑ a, oldW a (y p) (w p)) * K₁ y w ^ 2 with hB
  have hA0 : ∀ y, 0 ≤ A y := fun y => sum_nonneg fun u _ => mul_nonneg
    (prod_nonneg fun p _ => sum_nonneg fun b _ => oldW_nonneg (h7 p) _ _ _) (sq_nonneg _)
  have hB0 : ∀ y, 0 ≤ B y := fun y => sum_nonneg fun w _ => mul_nonneg
    (prod_nonneg fun p _ => sum_nonneg fun a _ => oldW_nonneg (h7 p) _ _ _) (sq_nonneg _)
  have hcs : ∑ y, Real.sqrt (A y) * Real.sqrt (B y) ≤
      Real.sqrt (∑ y, A y) * Real.sqrt (∑ y, B y) := by
    have h := abs_sum_mul_le' (fun y => Real.sqrt (A y)) (fun y => Real.sqrt (B y))
    simp only [Real.sq_sqrt (hA0 _), Real.sq_sqrt (hB0 _)] at h
    exact (le_abs_self _).trans h
  have hcz := cz_pos hF h3 h7
  have hsum : |∑ y, ∑ u, ∑ w, W u y w * K₀ u y * K₁ y w| ≤
      c * (Real.sqrt (∑ y, A y) * Real.sqrt (∑ y, B y)) :=
    (abs_sum_le_sum_abs _ _).trans ((sum_le_sum fun y _ => hy y).trans (by
      rw [← mul_sum]
      exact mul_le_mul_of_nonneg_left hcs hc))
  rw [ehk, ehh, ekk, abs_mul, abs_of_pos hcz]
  rw [Real.sqrt_mul hcz.le, Real.sqrt_mul hcz.le]
  have hsc : Real.sqrt (cz (F := F)) * Real.sqrt (cz (F := F)) = cz (F := F) :=
    Real.mul_self_sqrt hcz.le
  calc cz (F := F) * |∑ y, ∑ u, ∑ w, W u y w * K₀ u y * K₁ y w|
      ≤ cz (F := F) * (c * (Real.sqrt (∑ y, A y) * Real.sqrt (∑ y, B y))) :=
        mul_le_mul_of_nonneg_left hsum hcz.le
    _ = c * (Real.sqrt (cz (F := F)) * Real.sqrt (∑ y, B y) *
          (Real.sqrt (cz (F := F)) * Real.sqrt (∑ y, A y))) := by
        have e : c * (Real.sqrt (cz (F := F)) * Real.sqrt (∑ y, B y) *
            (Real.sqrt (cz (F := F)) * Real.sqrt (∑ y, A y))) =
            (Real.sqrt (cz (F := F)) * Real.sqrt (cz (F := F))) *
              (c * (Real.sqrt (∑ y, A y) * Real.sqrt (∑ y, B y))) := by ring
        rw [e, hsc]

/-- **The edge `34` with the paper's constant**: at a block whose least prime `b` is at least
`Q₃ = 19951586`, `c = ϱ₃₄(1/b, b^{-1/2})`. -/
theorem edge34_block_b (hF : ∀ p, ringChar (F p) ≠ 2) (h3 : ∀ p, Fintype.card (F p) % 4 = 3)
    {b : ℝ} (hb : 19951586 ≤ b) (hbp : ∀ p, b ≤ Fintype.card (F p))
    (h k : Tri F → ℝ) (hh : IsK c1 c2 h) (hk : IsK c0 c1 k) :
    |ipm h k| ≤ rho34 (1 / b) (1 / Real.sqrt b) * (Real.sqrt (ipm h h) * Real.sqrt (ipm k k)) := by
  have h7 : ∀ p, (7 : ℝ) ≤ Fintype.card (F p) := fun p => by linarith [hbp p]
  have hb0 : 0 < b := by linarith
  have hc0 : 0 ≤ rho34 (1 / b) (1 / Real.sqrt b) := by
    unfold rho34
    have hq : 1 / b ≤ 1 / 8 := one_div_le_one_div_of_le (by norm_num) (by linarith)
    have a : 0 < 1 - 4 * (1 / b) := by linarith
    have c : 0 < 1 - 6 * (1 / b) := by linarith
    have : 0 ≤ 4 * (1 / b) ^ 2 / (1 - 4 * (1 / b)) := by positivity
    have : 0 ≤ 1 / Real.sqrt b := by positivity
    have : 0 ≤ 1 / b := by positivity
    exact div_nonneg (by linarith) c.le
  have hc1 : rho34 (1 / b) (1 / Real.sqrt b) ≤ 1 := by
    have := (feature_table hb).2.2.2.1
    linarith
  exact edge34_block hF h3 h7 hc0 hc1 (fun p => rho34_le_b (by linarith) (hbp p)) h k hh hk

end Block

end Sarkozy.OpsFeature
