module

public import Sarkozy.L20Cap.Kernel
public import Sarkozy.Cuts.Tilt

@[expose] public section

/-!
# The score moments of the uniform root (`lem:root-normalization`(b))

`paper/sections/20b_positive_roots.tex`, `lem:root-normalization`(b) and its proof. `F` is a
finite field of odd characteristic, `n = |F|` (`n = p`, `q = 1/n`, `r = n^{-1/2}`), `χ` its
quadratic character read in `ℝ` (W3's `L20Cap.chi`). For an ordered pair `y = (y₀, y₁)` put
`ψ_y(z) = χ(z − y₀)χ(z − y₁)` (`psiP`), and for two pairs the normalized trace score
`H(y, y') = r ∑_z ψ_y(z)ψ_{y'}(z)` (`pairScore`), which is the score `H_j` of a base pair whose two
selected pairs are `y` and `y'` (`rootScore_eq_pairScore` in `ScoreKernel`).

**The exact moments** (sums over the `n(n − 1)` ordered distinct pairs, `distinctPairs`):
* `sum_psiP`: `∑_y ψ_y(z) = −(n − 1)`, i.e. `E_yψ_y(z) = −q`;
* `sum_psiP_sq`: `∑_y ψ_y(z)² = (n − 1)(n − 2)`, i.e. `E_yψ_y(z)² = 1 − 2q`;
* `sum_psiP_mul`: for `z ≠ z'`, `∑_y ψ_y(z)ψ_y(z') = −(n − 3)`, i.e.
  `E_yψ_y(z)ψ_y(z') = −q(1 − 3q)/(1 − q)`;
* **`pairScore_mean`**: for independent uniform distinct pairs `y, y'`, `E H = qr`;
* **`pairScore_sq_mean`**: `E H² = (1 − 2q)² + q(1 − 3q)²/(1 − q)` (in `n`:
  `(n − 2)²/n² + (n − 3)²/(n²(n − 1))`), and `≥ 1 − 4q` (`pairScore_sq_mean_ge`).

**Conditioning on global injectivity** (`cond_mean_abs_le`, `cond_sq_mean_ge`): for a finite law
`μ`, a good event `G` of probability `≥ 1 − ε > 0` and a function `X` with `|X| ≤ B` off `G`
except on a spike event `S` of mass `≤ s` where `|X| ≤ A`:
`|E[X | G]| ≤ (|E X| + εB + sA)/(1 − ε)` and `E[X² | G] ≥ E X² − εB² − sA²`.
With `E X = qr`, `ε = 36q`, `B = 2 + r`, `s = 2q²/(1 − q)`, `A = 1/r` this is the paper's
`h₀ = (qr + 36q(2 + r) + 2qr/(1 − q))/(1 − 36q)`, and with `A² = (1 − 2q)²/q` the bound
`E_{Γ_{p,0}}H_j² ≥ 1 − 4q − 36q(2 + r)² − 2q/(1 − q)` (`root_normalization_b`).

**What is assumed.** The paper's step "before global injectivity the root is the product of the
uniform laws of its two components, and each score pairs two independent uniform ordered distinct
pairs" (square-affine transitivity and the layer swap on the cyclic `K_{2,2,2}` components), and
the coincidence counts (`36q`, the spike mass `2q²/(1 − q)`, `|H_j| ≤ 2 + r` on a single
coincidence) are the hypotheses of `root_normalization_b`; the moments of the product law are
proved here exactly.
-/

namespace Sarkozy.PositiveRoots

open Finset Sarkozy.L20Cap

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The ordered distinct pairs of labels. -/
def distinctPairs (F : Type*) [Fintype F] [DecidableEq F] : Finset (F × F) :=
  univ.filter fun y => y.1 ≠ y.2

/-- The raw pair row `ψ_y(z) = χ(z − y₀)χ(z − y₁)`. -/
noncomputable def psiP (y : F × F) (z : F) : ℝ := chi (z - y.1) * chi (z - y.2)

omit [Field F] in
/-- `∑_{y₀ ≠ y₁} g(y₀)g(y₁) = (∑ g)² − ∑ g²`. -/
theorem sum_distinctPairs_mul (g : F → ℝ) :
    ∑ y ∈ distinctPairs F, g y.1 * g y.2 = (∑ t, g t) ^ 2 - ∑ t, g t ^ 2 := by
  have hall : ∑ y : F × F, g y.1 * g y.2 = (∑ t, g t) ^ 2 := by
    rw [sq, Finset.sum_mul_sum, ← Finset.sum_product']
    rfl
  have hdiag : ∑ y ∈ univ.filter (fun y : F × F => y.1 = y.2), g y.1 * g y.2 = ∑ t, g t ^ 2 := by
    refine Finset.sum_nbij' (fun y => y.1) (fun t => (t, t)) ?_ ?_ ?_ ?_ ?_
    · intro y _; simp
    · intro t _; simp
    · intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
      exact Prod.ext rfl hy
    · intro t _; rfl
    · intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
      rw [← hy, sq]
  have hsplit := Finset.sum_filter_add_sum_filter_not univ (fun y : F × F => y.1 = y.2)
    (fun y => g y.1 * g y.2)
  unfold distinctPairs
  rw [hall, hdiag] at hsplit
  linarith

theorem sum_chi_sub (hF : ringChar F ≠ 2) (z : F) : ∑ t, chi (z - t) = 0 := by
  have e : ∑ t, chi (z - t) = ∑ s, chi s :=
    Fintype.sum_equiv (Equiv.subLeft z) _ _ fun t => rfl
  rw [e]
  unfold chi
  rw [← Int.cast_sum, quadraticChar_sum_zero hF, Int.cast_zero]

omit [Field F] in
/-- `∑_t f(t)𝟙_{t ≠ a} = ∑_t f(t) − f(a)`. -/
theorem sum_ite_ne (a : F) (f : F → ℝ) :
    ∑ t, (if t = a then 0 else f t) = ∑ t, f t - f a := by
  rw [← Finset.sum_erase_add univ f (mem_univ a)]
  rw [← Finset.sum_erase_add univ (fun t => if t = a then 0 else f t) (mem_univ a)]
  simp only [↓reduceIte, add_zero]
  have : ∑ t ∈ univ.erase a, (if t = a then 0 else f t) = ∑ t ∈ univ.erase a, f t :=
    sum_congr rfl fun t ht => by simp only [ne_of_mem_erase ht, ↓reduceIte]
  rw [this]
  ring

theorem chi_sub_sq (z t : F) : chi (z - t) ^ 2 = if t = z then 0 else 1 := by
  by_cases h : t = z
  · subst h; simp [chi_zero]
  · simp only [h, ↓reduceIte]
    exact chi_sq_of_ne (sub_ne_zero.mpr (Ne.symm h))

theorem sum_chi_sub_sq (z : F) : ∑ t, chi (z - t) ^ 2 = (Fintype.card F : ℝ) - 1 := by
  rw [sum_congr rfl fun t _ => chi_sub_sq z t, sum_ite_ne]
  simp

theorem sum_chi_sub_pow4 (z : F) : ∑ t, (chi (z - t) ^ 2) ^ 2 = (Fintype.card F : ℝ) - 1 := by
  have e : ∀ t, (chi (z - t) ^ 2) ^ 2 = chi (z - t) ^ 2 := by
    intro t
    rw [chi_sub_sq]
    split_ifs <;> norm_num
  rw [sum_congr rfl fun t _ => e t, sum_chi_sub_sq]

/-- **`E_yψ_y(z) = −q`**: `∑_y ψ_y(z) = −(n − 1)`. -/
theorem sum_psiP (hF : ringChar F ≠ 2) (z : F) :
    ∑ y ∈ distinctPairs F, psiP y z = -((Fintype.card F : ℝ) - 1) := by
  unfold psiP
  rw [sum_distinctPairs_mul (fun t => chi (z - t)), sum_chi_sub hF, sum_chi_sub_sq]
  ring

/-- **`E_yψ_y(z)² = 1 − 2q`**: `∑_y ψ_y(z)² = (n − 1)(n − 2)`. -/
theorem sum_psiP_sq (z : F) :
    ∑ y ∈ distinctPairs F, psiP y z ^ 2 =
      ((Fintype.card F : ℝ) - 1) * ((Fintype.card F : ℝ) - 2) := by
  unfold psiP
  have e : ∀ y : F × F, (chi (z - y.1) * chi (z - y.2)) ^ 2 =
      chi (z - y.1) ^ 2 * chi (z - y.2) ^ 2 := fun y => by ring
  rw [sum_congr rfl fun y _ => e y, sum_distinctPairs_mul (fun t => chi (z - t) ^ 2),
    sum_chi_sub_sq, sum_chi_sub_pow4]
  ring

/-- `∑_t χ(z − t)χ(z' − t) = −1` for `z ≠ z'` (`eq:two-root`). -/
theorem sum_chi_sub_mul (hF : ringChar F ≠ 2) {z z' : F} (h : z ≠ z') :
    ∑ t, chi (z - t) * chi (z' - t) = -1 := by
  have e : ∀ t, chi (z - t) * chi (z' - t) = chi (t - z) * chi (t - z') := by
    intro t
    rw [← chi_mul, ← chi_mul]
    congr 1
    ring
  rw [sum_congr rfl fun t _ => e t, sum_chi_mul_chi hF z z']
  simp only [h, ↓reduceIte]

/-- **`E_yψ_y(z)ψ_y(z') = −q(1 − 3q)/(1 − q)`** for `z ≠ z'`:
`∑_y ψ_y(z)ψ_y(z') = −(n − 3)`. -/
theorem sum_psiP_mul (hF : ringChar F ≠ 2) {z z' : F} (h : z ≠ z') :
    ∑ y ∈ distinctPairs F, psiP y z * psiP y z' = -((Fintype.card F : ℝ) - 3) := by
  unfold psiP
  have e : ∀ y : F × F, chi (z - y.1) * chi (z - y.2) * (chi (z' - y.1) * chi (z' - y.2)) =
      (chi (z - y.1) * chi (z' - y.1)) * (chi (z - y.2) * chi (z' - y.2)) := fun y => by ring
  rw [sum_congr rfl fun y _ => e y,
    sum_distinctPairs_mul (fun t => chi (z - t) * chi (z' - t)), sum_chi_sub_mul hF h]
  have e2 : ∀ t, (chi (z - t) * chi (z' - t)) ^ 2 =
      (if t = z then 0 else 1) * (if t = z' then 0 else 1) := by
    intro t
    rw [mul_pow, chi_sub_sq, chi_sub_sq]
  rw [sum_congr rfl fun t _ => e2 t]
  have e3 : ∀ t : F, ((if t = z then (0 : ℝ) else 1) * (if t = z' then 0 else 1)) =
      1 - (if t = z then 1 else 0) - (if t = z' then 1 else 0) := by
    intro t
    by_cases h1 : t = z
    · subst h1; simp [h]
    · by_cases h2 : t = z'
      · subst h2; simp [h1]
      · simp [h1, h2]
  rw [sum_congr rfl fun t _ => e3 t, sum_sub_distrib, sum_sub_distrib,
    sum_ite_eq' univ z (fun _ => (1 : ℝ)), sum_ite_eq' univ z' (fun _ => (1 : ℝ))]
  simp only [mem_univ, ↓reduceIte, sum_const, card_univ, nsmul_eq_mul, mul_one]
  ring

omit [Field F] in
theorem card_distinctPairs :
    ((distinctPairs F).card : ℝ) = (Fintype.card F : ℝ) * ((Fintype.card F : ℝ) - 1) := by
  have h := sum_distinctPairs_mul (fun _ : F => (1 : ℝ))
  simp only [mul_one, sum_const, card_univ, nsmul_eq_mul, one_pow] at h
  rw [h]
  ring

/-! ## The score of two independent pairs -/

/-- **The normalized trace score of two pairs**, `H(y, y') = r ∑_z ψ_y(z)ψ_{y'}(z)`,
`r = n^{-1/2}`. -/
noncomputable def pairScore (y y' : F × F) : ℝ :=
  (∑ z, psiP y z * psiP y' z) / Real.sqrt (Fintype.card F)

/-- **`E H = qr`** for independent uniform ordered distinct pairs `y, y'`:
`(n(n − 1))^{-2} ∑_{y,y'} H(y, y') = n^{-1} · n^{-1/2}`. -/
theorem pairScore_mean (hF : ringChar F ≠ 2) :
    (∑ y ∈ distinctPairs F, ∑ y' ∈ distinctPairs F, pairScore y y') /
        ((distinctPairs F).card : ℝ) ^ 2 =
      1 / (Fintype.card F : ℝ) * (1 / Real.sqrt (Fintype.card F)) := by
  have hn : (2 : ℝ) ≤ Fintype.card F := by
    have := Fintype.one_lt_card (α := F)
    exact_mod_cast this
  have key : ∑ y ∈ distinctPairs F, ∑ y' ∈ distinctPairs F, ∑ z, psiP y z * psiP y' z =
      (Fintype.card F : ℝ) * ((Fintype.card F : ℝ) - 1) ^ 2 := by
    have e : ∑ y ∈ distinctPairs F, ∑ y' ∈ distinctPairs F, ∑ z, psiP y z * psiP y' z =
        ∑ z, (∑ y ∈ distinctPairs F, psiP y z) * (∑ y' ∈ distinctPairs F, psiP y' z) := by
      calc ∑ y ∈ distinctPairs F, ∑ y' ∈ distinctPairs F, ∑ z, psiP y z * psiP y' z
          = ∑ y ∈ distinctPairs F, ∑ z, ∑ y' ∈ distinctPairs F, psiP y z * psiP y' z :=
            Finset.sum_congr rfl fun y _ => Finset.sum_comm
        _ = ∑ z, ∑ y ∈ distinctPairs F, ∑ y' ∈ distinctPairs F, psiP y z * psiP y' z :=
            Finset.sum_comm
        _ = _ := by simp only [Finset.sum_mul_sum]
    rw [e]
    simp only [sum_psiP hF, sum_const, card_univ, nsmul_eq_mul]
    ring
  unfold pairScore
  simp only [← Finset.sum_div]
  rw [key, card_distinctPairs]
  have hs : 0 < Real.sqrt (Fintype.card F) := Real.sqrt_pos.mpr (by linarith)
  have hn1 : (Fintype.card F : ℝ) - 1 ≠ 0 := by linarith
  have hn0 : (Fintype.card F : ℝ) ≠ 0 := by linarith
  field_simp

/-- **`E H² = (1 − 2q)² + q(1 − 3q)²/(1 − q)`** for independent uniform ordered distinct pairs:
`(n(n − 1))^{-2} ∑_{y,y'} H(y, y')² = (n − 2)²/n² + (n − 3)²/(n²(n − 1))`. -/
theorem pairScore_sq_mean (hF : ringChar F ≠ 2) :
    (∑ y ∈ distinctPairs F, ∑ y' ∈ distinctPairs F, pairScore y y' ^ 2) /
        ((distinctPairs F).card : ℝ) ^ 2 =
      ((Fintype.card F : ℝ) - 2) ^ 2 / (Fintype.card F : ℝ) ^ 2 +
        ((Fintype.card F : ℝ) - 3) ^ 2 /
          ((Fintype.card F : ℝ) ^ 2 * ((Fintype.card F : ℝ) - 1)) := by
  set n : ℝ := (Fintype.card F : ℝ) with hn_def
  have hn : (2 : ℝ) ≤ n := by
    have := Fintype.one_lt_card (α := F)
    rw [hn_def]; exact_mod_cast this
  -- `∑_{y,y'} (∑_z ψ_y ψ_{y'})² = ∑_{z,z'} (∑_y ψ_y(z)ψ_y(z'))²`
  have e1 : ∑ y ∈ distinctPairs F, ∑ y' ∈ distinctPairs F, (∑ z, psiP y z * psiP y' z) ^ 2 =
      ∑ z, ∑ z', (∑ y ∈ distinctPairs F, psiP y z * psiP y z') ^ 2 := by
    have e : ∀ y y' : F × F, (∑ z, psiP y z * psiP y' z) ^ 2 =
        ∑ z, ∑ z', (psiP y z * psiP y z') * (psiP y' z * psiP y' z') := by
      intro y y'
      rw [sq, Finset.sum_mul_sum]
      exact sum_congr rfl fun z _ => sum_congr rfl fun z' _ => by ring
    simp_rw [e]
    have e' : ∀ z z' : F, (∑ y ∈ distinctPairs F, psiP y z * psiP y z') ^ 2 =
        ∑ y ∈ distinctPairs F, ∑ y' ∈ distinctPairs F,
          (psiP y z * psiP y z') * (psiP y' z * psiP y' z') := by
      intro z z'
      rw [sq, Finset.sum_mul_sum]
    simp_rw [e']
    calc ∑ y ∈ distinctPairs F, ∑ y' ∈ distinctPairs F, ∑ z, ∑ z',
          psiP y z * psiP y z' * (psiP y' z * psiP y' z')
        = ∑ y ∈ distinctPairs F, ∑ z, ∑ y' ∈ distinctPairs F, ∑ z',
            psiP y z * psiP y z' * (psiP y' z * psiP y' z') :=
          Finset.sum_congr rfl fun y _ => Finset.sum_comm
      _ = ∑ y ∈ distinctPairs F, ∑ z, ∑ z', ∑ y' ∈ distinctPairs F,
            psiP y z * psiP y z' * (psiP y' z * psiP y' z') :=
          Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun z _ => Finset.sum_comm
      _ = ∑ z, ∑ y ∈ distinctPairs F, ∑ z', ∑ y' ∈ distinctPairs F,
            psiP y z * psiP y z' * (psiP y' z * psiP y' z') := Finset.sum_comm
      _ = ∑ z, ∑ z', ∑ y ∈ distinctPairs F, ∑ y' ∈ distinctPairs F,
            psiP y z * psiP y z' * (psiP y' z * psiP y' z') :=
          Finset.sum_congr rfl fun z _ => Finset.sum_comm
  -- the diagonal and the off-diagonal values
  have e2 : ∀ z : F, ∑ z', (∑ y ∈ distinctPairs F, psiP y z * psiP y z') ^ 2 =
      ((n - 1) * (n - 2)) ^ 2 + (n - 1) * (n - 3) ^ 2 := by
    intro z
    rw [← Finset.sum_erase_add univ _ (mem_univ z)]
    have hd : (∑ y ∈ distinctPairs F, psiP y z * psiP y z) ^ 2 = ((n - 1) * (n - 2)) ^ 2 := by
      rw [← sum_psiP_sq z]
      simp only [sq]
    have ho : ∑ z' ∈ univ.erase z, (∑ y ∈ distinctPairs F, psiP y z * psiP y z') ^ 2 =
        (n - 1) * (n - 3) ^ 2 := by
      have hc : ∀ z' ∈ univ.erase z, (∑ y ∈ distinctPairs F, psiP y z * psiP y z') ^ 2 =
          (-((Fintype.card F : ℝ) - 3)) ^ 2 := fun z' hz' => by
        rw [sum_psiP_mul hF (Ne.symm (ne_of_mem_erase hz'))]
      rw [sum_congr rfl hc]
      rw [sum_const, card_erase_of_mem (mem_univ z), card_univ, nsmul_eq_mul]
      rw [Nat.cast_sub (Fintype.card_pos (α := F))]
      simp only [Nat.cast_one, neg_sq]
      rw [hn_def]
    rw [hd, ho]
    ring
  have key : ∑ y ∈ distinctPairs F, ∑ y' ∈ distinctPairs F, pairScore y y' ^ 2 =
      (n * (((n - 1) * (n - 2)) ^ 2 + (n - 1) * (n - 3) ^ 2)) / n := by
    have e3 : ∀ y y' : F × F, pairScore y y' ^ 2 = (∑ z, psiP y z * psiP y' z) ^ 2 / n := by
      intro y y'
      unfold pairScore
      rw [div_pow, Real.sq_sqrt (by linarith)]
    simp_rw [e3]
    simp only [← Finset.sum_div]
    rw [e1, sum_congr rfl fun z _ => e2 z, sum_const, card_univ, nsmul_eq_mul]
  rw [key, card_distinctPairs, ← hn_def]
  have hn1 : n - 1 ≠ 0 := by linarith
  have hn0 : n ≠ 0 := by linarith
  field_simp

/-- **`E H² ≥ 1 − 4q`**: `(1 − 2q)² + q(1 − 3q)²/(1 − q) ≥ 1 − 4q` for `q < 1`. -/
theorem pairScore_sq_mean_ge {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q < 1) :
    1 - 4 * q ≤ (1 - 2 * q) ^ 2 + q * (1 - 3 * q) ^ 2 / (1 - q) := by
  have : 0 ≤ q * (1 - 3 * q) ^ 2 / (1 - q) := div_nonneg (by positivity) (by linarith)
  nlinarith [sq_nonneg q]

/-- The moments in the paper's normalization: with `q = 1/n`,
`(n − 2)²/n² + (n − 3)²/(n²(n − 1)) = (1 − 2q)² + q(1 − 3q)²/(1 − q)`. -/
theorem sq_mean_eq_paper {n : ℝ} (hn : 2 ≤ n) :
    (n - 2) ^ 2 / n ^ 2 + (n - 3) ^ 2 / (n ^ 2 * (n - 1)) =
      (1 - 2 * (1 / n)) ^ 2 + (1 / n) * (1 - 3 * (1 / n)) ^ 2 / (1 - 1 / n) := by
  have hn0 : n ≠ 0 := by linarith
  have hn1 : n - 1 ≠ 0 := by linarith
  field_simp

/-! ## Conditioning on global injectivity -/

section Conditioning

open Sarkozy

variable {Ω : Type*} [Fintype Ω]

/-- **The conditional mean**: for a finite law `μ`, an event `G` with `μ(Gᶜ) ≤ ε < 1`, and `X` with
`∑_{Gᶜ} μ|X| ≤ m`, `|E[X 𝟙_G]/μ(G)| ≤ (|E X| + m)/(1 − ε)`. -/
theorem cond_mean_abs_le (μ : FiniteLaw Ω) (G : Ω → Prop) [DecidablePred G] (X : Ω → ℝ)
    {ε m : ℝ} (hε : ∑ ω ∈ univ.filter (fun ω => ¬ G ω), μ.weight ω ≤ ε) (hε1 : ε < 1)
    (hm : ∑ ω ∈ univ.filter (fun ω => ¬ G ω), μ.weight ω * |X ω| ≤ m) :
    |(∑ ω ∈ univ.filter G, μ.weight ω * X ω) / (∑ ω ∈ univ.filter G, μ.weight ω)| ≤
      (|μ.expect X| + m) / (1 - ε) := by
  have htot : ∑ ω, μ.weight ω = 1 := μ.total
  have hsplitW := Finset.sum_filter_add_sum_filter_not univ G (fun ω => μ.weight ω)
  have hsplitX := Finset.sum_filter_add_sum_filter_not univ G (fun ω => μ.weight ω * X ω)
  rw [htot] at hsplitW
  have hG : 1 - ε ≤ ∑ ω ∈ univ.filter G, μ.weight ω := by linarith
  have hGpos : 0 < ∑ ω ∈ univ.filter G, μ.weight ω := lt_of_lt_of_le (by linarith) hG
  have hE : μ.expect X = ∑ ω, μ.weight ω * X ω := rfl
  have hbad : |∑ ω ∈ univ.filter (fun ω => ¬ G ω), μ.weight ω * X ω| ≤ m := by
    refine (abs_sum_le_sum_abs _ _).trans (le_trans (le_of_eq ?_) hm)
    refine sum_congr rfl fun ω _ => ?_
    rw [abs_mul, abs_of_nonneg (μ.nonneg ω)]
  have hnum : |∑ ω ∈ univ.filter G, μ.weight ω * X ω| ≤ |μ.expect X| + m := by
    have : ∑ ω ∈ univ.filter G, μ.weight ω * X ω =
        μ.expect X - ∑ ω ∈ univ.filter (fun ω => ¬ G ω), μ.weight ω * X ω := by
      rw [hE]; linarith
    rw [this]
    exact (abs_sub _ _).trans (add_le_add le_rfl hbad)
  rw [abs_div, abs_of_pos hGpos]
  have hm0 : 0 ≤ |μ.expect X| + m := le_trans (abs_nonneg _) hnum
  calc _ ≤ (|μ.expect X| + m) / (∑ ω ∈ univ.filter G, μ.weight ω) :=
        div_le_div_of_nonneg_right hnum hGpos.le
    _ ≤ _ := div_le_div_of_nonneg_left hm0 (by linarith) hG

/-- **The conditional second moment**: if `∑_{Gᶜ} μX² ≤ m` then `E[X²𝟙_G]/μ(G) ≥ E X² − m`. -/
theorem cond_sq_mean_ge (μ : FiniteLaw Ω) (G : Ω → Prop) [DecidablePred G] (X : Ω → ℝ) {m : ℝ}
    (hG : 0 < ∑ ω ∈ univ.filter G, μ.weight ω)
    (hm : ∑ ω ∈ univ.filter (fun ω => ¬ G ω), μ.weight ω * X ω ^ 2 ≤ m) :
    μ.expect (fun ω => X ω ^ 2) - m ≤
      (∑ ω ∈ univ.filter G, μ.weight ω * X ω ^ 2) / (∑ ω ∈ univ.filter G, μ.weight ω) := by
  have htot : ∑ ω, μ.weight ω = 1 := μ.total
  have hsplitW := Finset.sum_filter_add_sum_filter_not univ G (fun ω => μ.weight ω)
  have hsplitX := Finset.sum_filter_add_sum_filter_not univ G (fun ω => μ.weight ω * X ω ^ 2)
  rw [htot] at hsplitW
  have hle1 : ∑ ω ∈ univ.filter G, μ.weight ω ≤ 1 := by
    have : 0 ≤ ∑ ω ∈ univ.filter (fun ω => ¬ G ω), μ.weight ω :=
      sum_nonneg fun ω _ => μ.nonneg ω
    linarith
  have hnum0 : 0 ≤ ∑ ω ∈ univ.filter G, μ.weight ω * X ω ^ 2 :=
    sum_nonneg fun ω _ => mul_nonneg (μ.nonneg ω) (sq_nonneg _)
  have hE : μ.expect (fun ω => X ω ^ 2) = ∑ ω, μ.weight ω * X ω ^ 2 := rfl
  have h1 : μ.expect (fun ω => X ω ^ 2) - m ≤ ∑ ω ∈ univ.filter G, μ.weight ω * X ω ^ 2 := by
    rw [hE]; linarith
  have h2 : ∑ ω ∈ univ.filter G, μ.weight ω * X ω ^ 2 ≤
      (∑ ω ∈ univ.filter G, μ.weight ω * X ω ^ 2) / (∑ ω ∈ univ.filter G, μ.weight ω) := by
    rw [le_div_iff₀ hG]
    calc _ = (∑ ω ∈ univ.filter G, μ.weight ω * X ω ^ 2) * 1 := by ring
      _ ≥ _ := mul_le_mul_of_nonneg_left hle1 hnum0
  linarith

/-- **`lem:root-normalization`(b)**, the conditioning step. Let `μ` be the root before global
injectivity (a finite law), `G` the event that the twelve labels are distinct, and `H` a score.
Suppose (the paper's coincidence counts) `μ(Gᶜ) ≤ 36q < 1`, that on `Gᶜ` the score has `|H| ≤ 2 + r`
outside the spike event `S` (the two selected pairs equal as sets), `μ(S) ≤ 2q²/(1 − q)`, and
`|H| ≤ 1/r`, `H² ≤ (1 − 2q)²/q` on `S`. If `E_μH = qr` and `E_μH² ≥ 1 − 4q` (`pairScore_mean`,
`pairScore_sq_mean`, `pairScore_sq_mean_ge`), then under `Γ_{p,0} = μ(· | G)`:
`|E H| ≤ h₀ = (qr + 36q(2 + r) + 2qr/(1 − q))/(1 − 36q)` and
`E H² ≥ 1 − 4q − 36q(2 + r)² − 2q/(1 − q)`. (Here `r > 0`, `q = r²`, `q < 1/2`.) -/
theorem root_normalization_b (μ : FiniteLaw Ω) (G S : Ω → Prop) [DecidablePred G] [DecidablePred S]
    (H : Ω → ℝ) {q r : ℝ} (hr : 0 < r) (hq : q = r ^ 2) (hq2 : q < 1 / 2) (hq36 : 36 * q < 1)
    (hGc : ∑ ω ∈ univ.filter (fun ω => ¬ G ω), μ.weight ω ≤ 36 * q)
    (hS : ∑ ω ∈ univ.filter (fun ω => ¬ G ω ∧ S ω), μ.weight ω ≤ 2 * q ^ 2 / (1 - q))
    (hB : ∀ ω, ¬ G ω → ¬ S ω → |H ω| ≤ 2 + r)
    (hA : ∀ ω, ¬ G ω → S ω → |H ω| ≤ 1 / r ∧ H ω ^ 2 ≤ (1 - 2 * q) ^ 2 / q)
    (hmean : μ.expect H = q * r) (hsq : 1 - 4 * q ≤ μ.expect (fun ω => H ω ^ 2)) :
    |(∑ ω ∈ univ.filter G, μ.weight ω * H ω) / (∑ ω ∈ univ.filter G, μ.weight ω)| ≤
        (q * r + 36 * q * (2 + r) + 2 * q * r / (1 - q)) / (1 - 36 * q) ∧
      1 - 4 * q - 36 * q * (2 + r) ^ 2 - 2 * q / (1 - q) ≤
        (∑ ω ∈ univ.filter G, μ.weight ω * H ω ^ 2) / (∑ ω ∈ univ.filter G, μ.weight ω) := by
  have hq0 : 0 < q := by rw [hq]; positivity
  have h1q : 0 < 1 - q := by linarith
  -- split the bad event into the ordinary part and the spikes
  have hsplit : ∀ g : Ω → ℝ, ∑ ω ∈ univ.filter (fun ω => ¬ G ω), g ω =
      ∑ ω ∈ univ.filter (fun ω => ¬ G ω ∧ ¬ S ω), g ω +
        ∑ ω ∈ univ.filter (fun ω => ¬ G ω ∧ S ω), g ω := by
    intro g
    rw [← Finset.sum_filter_add_sum_filter_not (univ.filter (fun ω => ¬ G ω)) S g,
      Finset.filter_filter, Finset.filter_filter, add_comm]
  have hW0 : ∀ ω, 0 ≤ μ.weight ω := μ.nonneg
  have hord : ∑ ω ∈ univ.filter (fun ω => ¬ G ω ∧ ¬ S ω), μ.weight ω ≤ 36 * q := by
    have := hsplit (fun ω => μ.weight ω)
    have h0 : 0 ≤ ∑ ω ∈ univ.filter (fun ω => ¬ G ω ∧ S ω), μ.weight ω :=
      sum_nonneg fun ω _ => hW0 ω
    linarith
  constructor
  · have hm : ∑ ω ∈ univ.filter (fun ω => ¬ G ω), μ.weight ω * |H ω| ≤
        36 * q * (2 + r) + 2 * q * r / (1 - q) := by
      rw [hsplit]
      have a1 : ∑ ω ∈ univ.filter (fun ω => ¬ G ω ∧ ¬ S ω), μ.weight ω * |H ω| ≤
          (∑ ω ∈ univ.filter (fun ω => ¬ G ω ∧ ¬ S ω), μ.weight ω) * (2 + r) := by
        rw [Finset.sum_mul]
        refine sum_le_sum fun ω hω => ?_
        simp only [mem_filter, mem_univ, true_and] at hω
        exact mul_le_mul_of_nonneg_left (hB ω hω.1 hω.2) (hW0 ω)
      have a2 : ∑ ω ∈ univ.filter (fun ω => ¬ G ω ∧ S ω), μ.weight ω * |H ω| ≤
          (∑ ω ∈ univ.filter (fun ω => ¬ G ω ∧ S ω), μ.weight ω) * (1 / r) := by
        rw [Finset.sum_mul]
        refine sum_le_sum fun ω hω => ?_
        simp only [mem_filter, mem_univ, true_and] at hω
        exact mul_le_mul_of_nonneg_left (hA ω hω.1 hω.2).1 (hW0 ω)
      have a3 := mul_le_mul_of_nonneg_right hord (by linarith : (0 : ℝ) ≤ 2 + r)
      have a4 := mul_le_mul_of_nonneg_right hS (by positivity : (0 : ℝ) ≤ 1 / r)
      have e : 2 * q ^ 2 / (1 - q) * (1 / r) = 2 * q * r / (1 - q) := by
        rw [hq]; field_simp
      linarith
    have h := cond_mean_abs_le μ G H hGc hq36 hm
    rw [hmean, abs_of_pos (by positivity : 0 < q * r)] at h
    calc _ ≤ _ := h
      _ = _ := by ring
  · have hm : ∑ ω ∈ univ.filter (fun ω => ¬ G ω), μ.weight ω * H ω ^ 2 ≤
        36 * q * (2 + r) ^ 2 + 2 * q * (1 - 2 * q) ^ 2 / (1 - q) := by
      rw [hsplit]
      have a1 : ∑ ω ∈ univ.filter (fun ω => ¬ G ω ∧ ¬ S ω), μ.weight ω * H ω ^ 2 ≤
          (∑ ω ∈ univ.filter (fun ω => ¬ G ω ∧ ¬ S ω), μ.weight ω) * (2 + r) ^ 2 := by
        rw [Finset.sum_mul]
        refine sum_le_sum fun ω hω => ?_
        simp only [mem_filter, mem_univ, true_and] at hω
        have hb := hB ω hω.1 hω.2
        have : H ω ^ 2 ≤ (2 + r) ^ 2 := by
          rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) hb 2
        exact mul_le_mul_of_nonneg_left this (hW0 ω)
      have a2 : ∑ ω ∈ univ.filter (fun ω => ¬ G ω ∧ S ω), μ.weight ω * H ω ^ 2 ≤
          (∑ ω ∈ univ.filter (fun ω => ¬ G ω ∧ S ω), μ.weight ω) * ((1 - 2 * q) ^ 2 / q) := by
        rw [Finset.sum_mul]
        refine sum_le_sum fun ω hω => ?_
        simp only [mem_filter, mem_univ, true_and] at hω
        exact mul_le_mul_of_nonneg_left (hA ω hω.1 hω.2).2 (hW0 ω)
      have a3 := mul_le_mul_of_nonneg_right hord (sq_nonneg (2 + r))
      have a4 := mul_le_mul_of_nonneg_right hS (by positivity : (0 : ℝ) ≤ (1 - 2 * q) ^ 2 / q)
      have e : 2 * q ^ 2 / (1 - q) * ((1 - 2 * q) ^ 2 / q) = 2 * q * (1 - 2 * q) ^ 2 / (1 - q) := by
        field_simp
      linarith
    have hGpos : 0 < ∑ ω ∈ univ.filter G, μ.weight ω := by
      have hsplitW := Finset.sum_filter_add_sum_filter_not univ G (fun ω => μ.weight ω)
      rw [μ.total] at hsplitW
      linarith
    have h := cond_sq_mean_ge μ G H hGpos hm
    have hsp : 2 * q * (1 - 2 * q) ^ 2 / (1 - q) ≤ 2 * q / (1 - q) := by
      apply div_le_div_of_nonneg_right _ h1q.le
      have : (1 - 2 * q) ^ 2 ≤ 1 := by nlinarith
      nlinarith
    linarith

end Conditioning

end Sarkozy.PositiveRoots
