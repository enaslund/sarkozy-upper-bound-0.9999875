module

public import Sarkozy.FiniteProbability

/-!
# `lem:push:localvariance` (b): averaging, linear part and assembly

`paper/sections/14_spectral.tex`, proof of `lem:push:localvariance` (b), last paragraph
(*Averaging*), in abstract form. The law `μ` is the uniform probability on `Φ_k`, the law `ν`
the uniform probability on the set `𝒵` of labellings of `R`, `H ω z = 𝓗(a, z)` the normalized
count and `A z = ∏_{i ∈ S} A_i(z) ≥ ∏_i α⁻_i`.

* `expect_comm`: Fubini for two finite laws.
* `variance_le_sq_dev`: `Var f ≤ E (f - c)²` for every constant `c`.
* `localvariance_averaging`: if `‖𝓗(·, z) - A(z)‖_{L²(μ)} ≤ ε^loc` for every `z`,
  `A(z) ≥ α⁻` and `ℓ^loc = α⁻ - ε^loc > 0`, then `C = c₀ E_z 𝓗(·, z)` (any `c₀ ≠ 0`) has
  relative variance at most `(ε^loc/ℓ^loc)²` (`eq:push:localvariance`). The paper uses
  Minkowski's inequality for the `z`-average; Jensen's inequality `(E_z g)² ≤ E_z g²`,
  used here, gives the same bound because the per-`z` bound is uniform.
* `l2_add_le`, `abs_prod_sub_prod_le`, `linear_part`: the *linear part* of the same proof,
  `‖∏_i q_i - ∏_i A_i‖ ≤ ∑_i L_i ∏_{j ≠ i} α⁺⁺_j` from `‖q_i - A_i‖ ≤ L_i` and
  `|q_j|, |A_j| ≤ α⁺⁺_j` (telescoping and Minkowski), on any finite law (in the paper, the
  uniform probability on `Φ_k` restricted to `E = Φ_k ∖ z(R)`, i.e. with the factors
  multiplied by `1_E`).
* `l2_le_of_density`, `L_bound`: the bound `L_i` on `‖q_i - A_i‖`, from the Gauss-sum bound for
  `f_i` (`lem:spec:gauss`, a hypothesis) and the density `κ_Φ`.
* `per_z_bound`, `localvariance_b`: the per-`z` bound `Lin + Pair + Coll + Exc` from its parts,
  and the assembled statement. The two-variable input of `Pair` is
  `Sarkozy.Spectral.two_variable_restricted`, the coincidence input of `Coll` is
  `Sarkozy.Spectral.coincidence_bound`.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.Spectral

open Sarkozy

variable {Ω Z : Type*} [Fintype Ω] [Fintype Z]

/-- Fubini for two finite laws. -/
theorem expect_comm (μ : FiniteLaw Ω) (ν : FiniteLaw Z) (g : Ω → Z → ℝ) :
    μ.expect (fun ω => ν.expect (fun z => g ω z)) =
      ν.expect (fun z => μ.expect (fun ω => g ω z)) := by
  simp only [FiniteLaw.expect, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun ω _ => by ring

/-- `Var f ≤ E (f - c)²`. -/
theorem variance_le_sq_dev (μ : FiniteLaw Ω) (f : Ω → ℝ) (c : ℝ) :
    μ.expect (fun ω => (f ω - μ.expect f) ^ 2) ≤ μ.expect (fun ω => (f ω - c) ^ 2) := by
  rw [μ.expect_sq_sub_mean]
  have e1 : μ.expect (fun ω => (f ω - c) ^ 2) =
      μ.expect (fun ω => f ω ^ 2) - 2 * c * μ.expect f + c ^ 2 := by
    calc _ = μ.expect (fun ω => (f ω ^ 2 - (2 * c) * f ω) + c ^ 2) :=
          μ.expect_congr (fun ω => by ring)
      _ = _ := by
          rw [FiniteLaw.expect_add, FiniteLaw.expect_sub, FiniteLaw.expect_const_mul,
            FiniteLaw.expect_const]
  rw [e1]
  nlinarith [sq_nonneg (μ.expect f - c)]

/-- **`lem:push:localvariance` (b), the averaging step** (`eq:push:localvariance`). -/
theorem localvariance_averaging (μ : FiniteLaw Ω) (ν : FiniteLaw Z) (H : Ω → Z → ℝ)
    (A : Z → ℝ) {αm ε c₀ : ℝ} (hc₀ : c₀ ≠ 0) (hA : ∀ z, αm ≤ A z)
    (hH : ∀ z, μ.expect (fun ω => (H ω z - A z) ^ 2) ≤ ε ^ 2) (hε : 0 ≤ ε)
    (hℓ : 0 < αm - ε) (C : Ω → ℝ) (hC : ∀ ω, C ω = c₀ * ν.expect (fun z => H ω z)) :
    μ.expect (fun ω => (C ω - μ.expect C) ^ 2) / μ.expect C ^ 2 ≤ (ε / (αm - ε)) ^ 2 := by
  obtain ⟨Hb, hHb⟩ : ∃ Hb : Ω → ℝ, ∀ ω, Hb ω = ν.expect (fun z => H ω z) := ⟨_, fun _ => rfl⟩
  have hC' : ∀ ω, C ω = c₀ * Hb ω := fun ω => by rw [hC, hHb]
  have hAb : αm ≤ ν.expect A := ν.const_le_expect hA
  -- the `L²` distance of the average from `E_z A`
  have hdev : μ.expect (fun ω => (Hb ω - ν.expect A) ^ 2) ≤ ε ^ 2 := by
    have h1 : ∀ ω, (Hb ω - ν.expect A) ^ 2 ≤ ν.expect (fun z => (H ω z - A z) ^ 2) := by
      intro ω
      have e : Hb ω - ν.expect A = ν.expect (fun z => H ω z - A z) := by
        rw [hHb]
        exact (ν.expect_sub _ _).symm
      rw [e]
      exact ν.mean_sq_le_second_moment _
    calc μ.expect (fun ω => (Hb ω - ν.expect A) ^ 2)
        ≤ μ.expect (fun ω => ν.expect (fun z => (H ω z - A z) ^ 2)) := μ.expect_mono h1
      _ = ν.expect (fun z => μ.expect (fun ω => (H ω z - A z) ^ 2)) := expect_comm μ ν _
      _ ≤ ε ^ 2 := ν.expect_le_const hH
  -- the mean
  have hmean : αm - ε ≤ μ.expect Hb := by
    have h1 := μ.mean_sq_le_second_moment (fun ω => Hb ω - ν.expect A)
    rw [μ.expect_sub, μ.expect_const] at h1
    have h2 := (abs_le_of_sq_le_sq' (h1.trans hdev) hε).1
    linarith
  have hm0 : 0 < μ.expect Hb := lt_of_lt_of_le hℓ hmean
  have hvar : μ.expect (fun ω => (Hb ω - μ.expect Hb) ^ 2) ≤ ε ^ 2 :=
    (variance_le_sq_dev μ Hb (ν.expect A)).trans hdev
  -- the scaling by `c₀`
  have hEC : μ.expect C = c₀ * μ.expect Hb := by
    rw [μ.expect_congr hC']
    exact μ.expect_const_mul _ _
  have hVC : μ.expect (fun ω => (C ω - μ.expect C) ^ 2) =
      c₀ ^ 2 * μ.expect (fun ω => (Hb ω - μ.expect Hb) ^ 2) := by
    rw [← μ.expect_const_mul (c₀ ^ 2) (fun ω => (Hb ω - μ.expect Hb) ^ 2)]
    refine μ.expect_congr fun ω => ?_
    rw [hEC, hC']
    ring
  rw [hVC, hEC, mul_pow, mul_div_mul_left _ _ (pow_ne_zero 2 hc₀), div_pow]
  exact div_le_div₀ (sq_nonneg ε) hvar (by positivity) (pow_le_pow_left₀ hℓ.le hmean 2)

/-! ### The linear part: telescoping and Minkowski -/

/-- The norm of `L²(μ)`. -/
noncomputable def l2 (μ : FiniteLaw Ω) (f : Ω → ℝ) : ℝ :=
  Real.sqrt (μ.expect (fun ω => f ω ^ 2))

/-- **Minkowski's inequality** in `L²(μ)`. -/
theorem l2_add_le (μ : FiniteLaw Ω) (f g : Ω → ℝ) :
    l2 μ (fun ω => f ω + g ω) ≤ l2 μ f + l2 μ g := by
  unfold l2
  have hF := μ.second_moment_nonneg f
  have hG := μ.second_moment_nonneg g
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  have e : μ.expect (fun ω => (f ω + g ω) ^ 2) = μ.expect (fun ω => f ω ^ 2) +
      2 * μ.expect (fun ω => f ω * g ω) + μ.expect (fun ω => g ω ^ 2) := by
    calc _ = μ.expect (fun ω => (f ω ^ 2 + 2 * (f ω * g ω)) + g ω ^ 2) :=
          μ.expect_congr (fun ω => by ring)
      _ = _ := by rw [FiniteLaw.expect_add, FiniteLaw.expect_add, FiniteLaw.expect_const_mul]
  have e2 : μ.expect (fun ω => f ω ^ 2) * μ.expect (fun ω => g ω ^ 2) =
      (Real.sqrt (μ.expect (fun ω => f ω ^ 2)) * Real.sqrt (μ.expect (fun ω => g ω ^ 2))) ^ 2 := by
    rw [mul_pow, Real.sq_sqrt hF, Real.sq_sqrt hG]
  have hcs := (abs_le_of_sq_le_sq' ((μ.cauchy_schwarz_sq f g).trans_eq e2) (by positivity)).2
  have hsF := Real.sq_sqrt hF
  have hsG := Real.sq_sqrt hG
  rw [e]
  nlinarith [hcs, hsF, hsG]

theorem l2_mono (μ : FiniteLaw Ω) {f g : Ω → ℝ} (h : ∀ ω, |f ω| ≤ g ω) : l2 μ f ≤ l2 μ g := by
  unfold l2
  refine Real.sqrt_le_sqrt (μ.expect_mono fun ω => ?_)
  rw [← sq_abs]
  exact pow_le_pow_left₀ (abs_nonneg _) (h ω) 2

theorem l2_sum_le (μ : FiniteLaw Ω) {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (f : ι → Ω → ℝ) : l2 μ (fun ω => ∑ i ∈ s, f i ω) ≤ ∑ i ∈ s, l2 μ (f i) := by
  induction s using Finset.induction_on with
  | empty => simp [l2]
  | @insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (l2_add_le μ _ _).trans (add_le_add le_rfl ih)

theorem l2_abs_mul (μ : FiniteLaw Ω) (f : Ω → ℝ) {c : ℝ} (hc : 0 ≤ c) :
    l2 μ (fun ω => |f ω| * c) = c * l2 μ f := by
  unfold l2
  rw [show (fun ω => (|f ω| * c) ^ 2) = (fun ω => c ^ 2 * f ω ^ 2) from
    funext fun ω => by rw [mul_pow, sq_abs]; ring]
  rw [μ.expect_const_mul, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq hc]

/-- **Telescoping**: `|∏_i q_i - ∏_i A_i| ≤ ∑_i |q_i - A_i| ∏_{j ≠ i} M_j` when
`|q_j|, |A_j| ≤ M_j`. -/
theorem abs_prod_sub_prod_le {ι : Type*} [DecidableEq ι] (s : Finset ι) (q A M : ι → ℝ)
    (hq : ∀ i ∈ s, |q i| ≤ M i) (hA : ∀ i ∈ s, |A i| ≤ M i) :
    |∏ i ∈ s, q i - ∏ i ∈ s, A i| ≤ ∑ i ∈ s, |q i - A i| * ∏ j ∈ s.erase i, M j := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha, Finset.sum_insert ha,
      Finset.erase_insert ha]
    have hq' : ∀ i ∈ s, |q i| ≤ M i := fun i hi => hq i (Finset.mem_insert_of_mem hi)
    have hA' : ∀ i ∈ s, |A i| ≤ M i := fun i hi => hA i (Finset.mem_insert_of_mem hi)
    have ih' := ih hq' hA'
    have hMa : 0 ≤ M a := (abs_nonneg _).trans (hq a (Finset.mem_insert_self a s))
    have hprodq : |∏ i ∈ s, q i| ≤ ∏ i ∈ s, M i := by
      rw [Finset.abs_prod]
      exact Finset.prod_le_prod₀ (fun i _ => abs_nonneg _) hq'
    have e : q a * ∏ i ∈ s, q i - A a * ∏ i ∈ s, A i =
        (q a - A a) * ∏ i ∈ s, q i + A a * (∏ i ∈ s, q i - ∏ i ∈ s, A i) := by ring
    have e2 : ∑ i ∈ s, |q i - A i| * ∏ j ∈ (insert a s).erase i, M j =
        M a * ∑ i ∈ s, |q i - A i| * ∏ j ∈ s.erase i, M j := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      have hai : a ≠ i := fun h => ha (h ▸ hi)
      rw [Finset.erase_insert_of_ne hai,
        Finset.prod_insert (fun h => ha (Finset.mem_of_mem_erase h))]
      ring
    rw [e, e2]
    refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
    · rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hprodq (abs_nonneg _)
    · rw [abs_mul]
      exact mul_le_mul (hA a (Finset.mem_insert_self a s)) ih' (abs_nonneg _) hMa

/-- **`lem:push:localvariance` (b), the linear part**: if `|q_j|, |A_j| ≤ α⁺⁺_j` pointwise and
`‖q_i - A_i‖ ≤ L_i`, then `‖∏_i q_i - ∏_i A_i‖ ≤ ∑_i L_i ∏_{j ≠ i} α⁺⁺_j = Lin_k`. -/
theorem linear_part (μ : FiniteLaw Ω) {ι : Type*} [DecidableEq ι] (s : Finset ι)
    (q A : ι → Ω → ℝ) (M L : ι → ℝ) (hq : ∀ i ∈ s, ∀ ω, |q i ω| ≤ M i)
    (hA : ∀ i ∈ s, ∀ ω, |A i ω| ≤ M i) (hL : ∀ i ∈ s, l2 μ (fun ω => q i ω - A i ω) ≤ L i) :
    l2 μ (fun ω => ∏ i ∈ s, q i ω - ∏ i ∈ s, A i ω) ≤ ∑ i ∈ s, L i * ∏ j ∈ s.erase i, M j := by
  have hne : Nonempty Ω := by
    by_contra h
    rw [not_nonempty_iff] at h
    have := μ.total
    rw [Finset.univ_eq_empty, Finset.sum_empty] at this
    exact zero_ne_one this
  obtain ⟨ω₀⟩ := hne
  have hM : ∀ i ∈ s, 0 ≤ M i := fun i hi => (abs_nonneg _).trans (hq i hi ω₀)
  have hc : ∀ i ∈ s, 0 ≤ ∏ j ∈ s.erase i, M j := fun i _ =>
    Finset.prod_nonneg fun j hj => hM j (Finset.mem_of_mem_erase hj)
  calc l2 μ (fun ω => ∏ i ∈ s, q i ω - ∏ i ∈ s, A i ω)
      ≤ l2 μ (fun ω => ∑ i ∈ s, |q i ω - A i ω| * ∏ j ∈ s.erase i, M j) :=
        l2_mono μ fun ω => abs_prod_sub_prod_le s (fun i => q i ω) (fun i => A i ω) M
          (fun i hi => hq i hi ω) (fun i hi => hA i hi ω)
    _ ≤ ∑ i ∈ s, l2 μ (fun ω => |q i ω - A i ω| * ∏ j ∈ s.erase i, M j) := l2_sum_le μ s _
    _ = ∑ i ∈ s, (∏ j ∈ s.erase i, M j) * l2 μ (fun ω => q i ω - A i ω) :=
        Finset.sum_congr rfl fun i hi => l2_abs_mul μ (fun ω => q i ω - A i ω) (hc i hi)
    _ ≤ ∑ i ∈ s, L i * ∏ j ∈ s.erase i, M j := Finset.sum_le_sum fun i hi => by
        rw [mul_comm]
        exact mul_le_mul_of_nonneg_right (hL i hi) (hc i hi)

/-! ### The bound `L_i` -/

/-- **Density transfer**: if `μ ≤ κ ν` pointwise, then `‖f‖_{L²(μ)} ≤ κ^{1/2} ‖f‖_{L²(ν)}`. -/
theorem l2_le_of_density (μ ν : FiniteLaw Ω) {κ : ℝ} (hκ : 0 ≤ κ)
    (hd : ∀ ω, μ.weight ω ≤ κ * ν.weight ω) (f : Ω → ℝ) : l2 μ f ≤ √κ * l2 ν f := by
  unfold l2
  rw [← Real.sqrt_mul hκ]
  refine Real.sqrt_le_sqrt ?_
  unfold FiniteLaw.expect
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun ω _ => ?_
  calc μ.weight ω * f ω ^ 2 ≤ κ * ν.weight ω * f ω ^ 2 :=
        mul_le_mul_of_nonneg_right (hd ω) (sq_nonneg _)
    _ = κ * (ν.weight ω * f ω ^ 2) := by ring

theorem l2_const_le (μ : FiniteLaw Ω) (g : Ω → ℝ) {c : ℝ} (hc : 0 ≤ c) (hg : ∀ ω, |g ω| ≤ c) :
    l2 μ g ≤ c := by
  refine (l2_mono μ (g := fun _ => c) hg).trans_eq ?_
  simp [l2, Real.sqrt_sq hc]

/-- **The bound `L_i`** of the linear part of `lem:push:localvariance` (b): on `Φ_k` (law `μ`,
density at most `κ_Φ` with respect to the uniform law `ν` on `𝔽_p`), `q_i = A_i + f_i - c 1`
with `c = 2^{m_i}/p`, a function `1` of modulus at most one, and `‖f_i‖_{L²(ν)} ≤ G`
(`lem:spec:gauss` gives `G² = 2^{m_i} A_i r²`). Then `‖q_i - A_i‖_{L²(μ)} ≤ κ_Φ^{1/2} G + c`,
which is `L_i = (κ_Φ 2^{m_i} α⁺_i)^{1/2} r + 2^{m_i} r²` when `A_i ≤ α⁺_i`. -/
theorem L_bound (μ ν : FiniteLaw Ω) {κ : ℝ} (hκ : 0 ≤ κ)
    (hd : ∀ ω, μ.weight ω ≤ κ * ν.weight ω) (q f ind : Ω → ℝ) {A c G : ℝ} (hc : 0 ≤ c)
    (hind : ∀ ω, |ind ω| ≤ 1) (hq : ∀ ω, q ω = A + f ω - c * ind ω) (hf : l2 ν f ≤ G) :
    l2 μ (fun ω => q ω - A) ≤ √κ * G + c := by
  have e : (fun ω => q ω - A) = fun ω => f ω + -(c * ind ω) := funext fun ω => by
    rw [hq]
    ring
  rw [e]
  have h1 : l2 μ f ≤ √κ * G :=
    (l2_le_of_density μ ν hκ hd f).trans (mul_le_mul_of_nonneg_left hf (Real.sqrt_nonneg _))
  have h2 : l2 μ (fun ω => -(c * ind ω)) ≤ c := l2_const_le μ _ hc fun ω => by
    rw [abs_neg, abs_mul, abs_of_nonneg hc]
    exact mul_le_of_le_one_right hc (hind ω)
  exact (l2_add_le μ _ _).trans (add_le_add h1 h2)

/-! ### The per-`z` bound and the assembled statement -/

theorem l2_sq (μ : FiniteLaw Ω) (f : Ω → ℝ) : l2 μ f ^ 2 = μ.expect (fun ω => f ω ^ 2) :=
  Real.sq_sqrt (μ.second_moment_nonneg f)

theorem l2_nonneg (μ : FiniteLaw Ω) (f : Ω → ℝ) : 0 ≤ l2 μ f := Real.sqrt_nonneg _

/-- The `L²` norm of a function bounded by `c` on a set of measure at most `δ²` and vanishing
off it is at most `c δ`. -/
theorem l2_le_of_support (μ : FiniteLaw Ω) (P : Ω → Prop) [DecidablePred P] (f : Ω → ℝ)
    {c δ : ℝ} (hc : 0 ≤ c) (hδ : 0 ≤ δ) (hf : ∀ ω, |f ω| ≤ if P ω then c else 0)
    (hP : μ.expect (fun ω => if P ω then 1 else 0) ≤ δ ^ 2) : l2 μ f ≤ c * δ := by
  have h1 : l2 μ f ≤ l2 μ (fun ω => if P ω then c else 0) := l2_mono μ hf
  have h2 : l2 μ (fun ω => if P ω then c else 0) ^ 2 ≤ (c * δ) ^ 2 := by
    rw [l2_sq]
    have e : ∀ ω, (if P ω then c else 0) ^ 2 = c ^ 2 * (if P ω then 1 else 0) := fun ω => by
      by_cases h : P ω <;> simp [h]
    rw [μ.expect_congr e, μ.expect_const_mul, mul_pow]
    exact mul_le_mul_of_nonneg_left hP (sq_nonneg c)
  exact h1.trans (abs_le_of_sq_le_sq' h2 (by positivity)).2

/-- **The per-`z` bound** of `lem:push:localvariance` (b) (*Averaging*, first sentences): on
`E = Φ_k ∖ z(R)`, `𝓗 - ∏ A_i = (∏ q_i - ∏ A_i) + (𝓗 - ∏ q_i)` with
`‖(∏ q_i - ∏ A_i) 1_E‖ ≤ Lin_k` and `|𝓗 - ∏ q_i| ≤ Pair_k + Coll_k` on `E`; off `E`,
`|𝓗 - ∏ A_i| ≤ ∏ α⁺_i` on a set of probability at most `δ²` (`δ = (|R| κ_Φ)^{1/2} r`). Then
`‖𝓗(·, z) - ∏ A_i‖ ≤ Lin_k + Pair_k + Coll_k + Exc_k`, `Exc_k = ∏ α⁺_i δ`. -/
theorem per_z_bound (μ : FiniteLaw Ω) (E : Ω → Prop) [DecidablePred E] (H Q : Ω → ℝ) (A : ℝ)
    {Lin PC Mplus δ : ℝ} (hPC : 0 ≤ PC) (hM : 0 ≤ Mplus) (hδ : 0 ≤ δ)
    (hlin : l2 μ (fun ω => if E ω then Q ω - A else 0) ≤ Lin)
    (hpair : ∀ ω, E ω → |H ω - Q ω| ≤ PC) (hout : ∀ ω, ¬ E ω → |H ω - A| ≤ Mplus)
    (hmeas : μ.expect (fun ω => if ¬ E ω then 1 else 0) ≤ δ ^ 2) :
    l2 μ (fun ω => H ω - A) ≤ Lin + PC + Mplus * δ := by
  have hsplit : ∀ ω, H ω - A = ((if E ω then Q ω - A else 0) + (if E ω then H ω - Q ω else 0)) +
      (if ¬ E ω then H ω - A else 0) := fun ω => by
    by_cases h : E ω <;> simp [h]
  have h2 : l2 μ (fun ω => if E ω then H ω - Q ω else 0) ≤ PC := by
    have := l2_mono μ (f := fun ω => if E ω then H ω - Q ω else 0) (g := fun _ => PC) fun ω => by
      by_cases h : E ω
      · simpa [h] using hpair ω h
      · simpa [h] using hPC
    refine this.trans_eq ?_
    simp [l2, Real.sqrt_sq hPC]
  have h3 : l2 μ (fun ω => if ¬ E ω then H ω - A else 0) ≤ Mplus * δ := by
    refine l2_le_of_support μ (fun ω => ¬ E ω) _ hM hδ (fun ω => ?_) hmeas
    by_cases h : E ω
    · simp [h]
    · simpa [h] using hout ω h
  calc l2 μ (fun ω => H ω - A)
      = l2 μ (fun ω => ((if E ω then Q ω - A else 0) + (if E ω then H ω - Q ω else 0)) +
          (if ¬ E ω then H ω - A else 0)) := congrArg (l2 μ) (funext hsplit)
    _ ≤ l2 μ (fun ω => (if E ω then Q ω - A else 0) + (if E ω then H ω - Q ω else 0)) +
          l2 μ (fun ω => if ¬ E ω then H ω - A else 0) := l2_add_le μ _ _
    _ ≤ (l2 μ (fun ω => if E ω then Q ω - A else 0) +
          l2 μ (fun ω => if E ω then H ω - Q ω else 0)) +
          l2 μ (fun ω => if ¬ E ω then H ω - A else 0) :=
        add_le_add (l2_add_le μ _ _) le_rfl
    _ ≤ (Lin + PC) + Mplus * δ := add_le_add (add_le_add hlin h2) h3
    _ = Lin + PC + Mplus * δ := rfl

/-- **`lem:push:localvariance` (b), assembled from its per-`z` inputs.** For every labelling
`z` of `R` (law `ν`, uniform on `𝒵` in the paper): the linear part `Lin`
(`Sarkozy.Spectral.linear_part`), the pair and coincidence terms `PC = Pair_k + Coll_k`
(pointwise on `E_z`; the pair terms are bounded by the matching bounds (i) and by the
two-variable bounds (ii), `Sarkozy.Spectral.two_variable_bound`), the excluded set
`Φ_k ∖ E_z` of probability at most `δ²` where `|𝓗 - ∏ A_i| ≤ ∏ α⁺_i`, and
`∏ A_i(z) ≥ ∏ α⁻_i = αm`. With `ε^loc = Lin + PC + ∏ α⁺_i δ` and
`ℓ^loc = αm - ε^loc > 0`, the count `C_k = c₀ E_z 𝓗(·, z)` has relative variance at most
`(ε^loc/ℓ^loc)²`. -/
theorem localvariance_b (μ : FiniteLaw Ω) (ν : FiniteLaw Z) (E : Z → Ω → Prop)
    [∀ z, DecidablePred (E z)] (H Q : Ω → Z → ℝ) (A : Z → ℝ)
    {αm Lin PC Mplus δ c₀ : ℝ} (hc₀ : c₀ ≠ 0) (hA : ∀ z, αm ≤ A z) (hLin : 0 ≤ Lin)
    (hPC : 0 ≤ PC) (hM : 0 ≤ Mplus) (hδ : 0 ≤ δ)
    (hlin : ∀ z, l2 μ (fun ω => if E z ω then Q ω z - A z else 0) ≤ Lin)
    (hpair : ∀ z ω, E z ω → |H ω z - Q ω z| ≤ PC)
    (hout : ∀ z ω, ¬ E z ω → |H ω z - A z| ≤ Mplus)
    (hmeas : ∀ z, μ.expect (fun ω => if ¬ E z ω then 1 else 0) ≤ δ ^ 2)
    (hℓ : 0 < αm - (Lin + PC + Mplus * δ)) (C : Ω → ℝ)
    (hC : ∀ ω, C ω = c₀ * ν.expect (fun z => H ω z)) :
    μ.expect (fun ω => (C ω - μ.expect C) ^ 2) / μ.expect C ^ 2 ≤
      ((Lin + PC + Mplus * δ) / (αm - (Lin + PC + Mplus * δ))) ^ 2 := by
  have hε : 0 ≤ Lin + PC + Mplus * δ := by positivity
  refine localvariance_averaging μ ν H A hc₀ hA (fun z => ?_) hε hℓ C hC
  have h := per_z_bound μ (E z) (fun ω => H ω z) (fun ω => Q ω z) (A z) hPC hM hδ (hlin z)
    (hpair z) (hout z) (hmeas z)
  have h2 := pow_le_pow_left₀ (l2_nonneg _ _) h 2
  rwa [l2_sq] at h2

end Sarkozy.Spectral
