module

public import Sarkozy.L20Cap.Completion

/-!
# The star terms vanish on `𝓘 ∩ 𝟙^⊥` (proof of `prop:l20-completion`)

`paper/sections/20_middle_reference.tex`, proof of `prop:l20-completion`: for
`h, h' ∈ 𝓘 ∩ 𝟙^⊥`, `E_{μ_p}[h | x_k] = 0` for every coordinate `k` (`lem:spec:affpair`(d)), so
`T_S h = 0` for every column star and `⟨h', T_S h⟩ = 0` for every row star (`lem:spec:stars`),
and `(𝟙 ⊗ 𝟙)h = 0`; hence `⟨h, K_soft h⟩ = ⟨h, T_ns h⟩`. Notation of
`Sarkozy.L20Cap.Completion`.

* `starPart6`: the complete star part of the soft kernel of `D₂₀` (the single pairs, the left
  stars `∏_{j∈S}(D₂₀)_ij χ(x'_j - x_i)` and the right stars `∏_{i∈S}(D₂₀)_ij χ(x'_j - x_i)`,
  `|S| ≥ 2`; S1's `softStarPart`, read with `χ` of `F`); `nonstar = K_soft - 1 - starPart6`, the
  nonstar part `T_ns` (by S1's `softStarPart_eq_sum_starSets` it is the sum of the nonstar subsets
  of the sixteen cross pairs).
* `cond_coord_zero`: for `f` translation invariant of mean zero, `E[f(x) g(x_k)] = 0`;
* `form_left_zero`, `form_right_zero`, **`star_form_zero`**: kernels depending on one side only
  through one coordinate have zero form on `𝓘 ∩ 𝟙^⊥`; the star part is a sum of such kernels;
* **`soft_eq_nonstar`**: `⟨f, K_soft f⟩ = ⟨f, T_ns f⟩` on `𝓘 ∩ 𝟙^⊥`;
* **`cutT_caps_ns`**: `cutT_caps` with the hypothesis on `𝓘 ∩ 𝟙^⊥` replaced by the paper's
  nonstar cap `‖T_ns‖ ≤ N_ns` on all of `L²(μ_p)`;
* **`Z0_lower`**: `Z₀ ≥ 1 - ε_Z` with `ε_Z = N_ns + D_col + m_⋆`, from the nonstar and collision
  caps and the star-mean bound `m_⋆` (`lem:l20-star-mean`).
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace Sarkozy.L20Cap

open Sarkozy Sarkozy.Recentering Sarkozy.Cuts

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The supports `S ⊆ Fin 6` with at least two elements. -/
def supports6 : Finset (Finset (Fin 6)) := univ.filter fun S => 2 ≤ S.card

/-- **The complete star part** of the soft kernel `∏_{i,j}(1 + (D₂₀)_ij χ(x'_j - x_i))`. -/
noncomputable def starPart6 (x x' : Fin 6 → F) : ℝ :=
  ∑ i, ∑ j, crossD i j * chi (x' j - x i) +
    ∑ i, ∑ S ∈ supports6, (∏ j ∈ S, crossD i j) * ∏ j ∈ S, chi (x' j - x i) +
    ∑ S ∈ supports6, ∑ j, (∏ i ∈ S, crossD i j) * ∏ i ∈ S, chi (x' j - x i)

/-- **The nonstar part** `T_ns = K_soft - 𝟙 ⊗ 𝟙 - (stars)`. -/
noncomputable def nonstar (x x' : CoreT F × PairT F) : ℝ :=
  Ksoft x x' - 1 - starPart6 (labels x) (labels x')

theorem labels_transl (y : F) (x : CoreT F × PairT F) (i : Fin 6) :
    labels (transl y x) i = labels x i + y := by
  obtain ⟨C, b⟩ := x
  fin_cases i <;> simp [labels, emb, transl, affCoreEquiv, affPairEquiv, affCore, affPair]

theorem kernelForm_sum_kernel {Ω ι : Type*} [Fintype Ω] (ν : FiniteLaw Ω) (s : Finset ι)
    (K : ι → Ω → Ω → ℝ) (f : Ω → ℝ) :
    kernelForm ν ν (fun x y => ∑ n ∈ s, K n x y) f f = ∑ n ∈ s, kernelForm ν ν (K n) f f := by
  simp only [kernelForm, LinearMap.mk₂_apply, Finset.mul_sum, Finset.sum_mul]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Finset.sum_comm]

variable [Nonempty (CoreT F)] [Nonempty (PairT F)]

/-- **`E[f | x_k] = 0`** for `f ∈ 𝓘 ∩ 𝟙^⊥` (`lem:spec:affpair`(d)), in the form
`E[f(x) g(x_k)] = 0` for every `g`: `y ↦ E[f(x)𝟙{x_k = y}]` is translation invariant, hence
constant, and sums to `E f = 0`. -/
theorem cond_coord_zero (h6 : 6 ≤ Fintype.card F) {f : CoreT F × PairT F → ℝ}
    (hf : Invariant (Multiplicative F) f) (hf0 : (halfLaw h6).expect f = 0) (k : Fin 6)
    (g : F → ℝ) : (halfLaw h6).expect (fun x => f x * g (labels x k)) = 0 := by
  set φ : F → ℝ := fun y => (halfLaw h6).expect (fun x => f x * if labels x k = y then 1 else 0)
    with hφ
  have hshift : ∀ y β : F, φ (y + β) = φ y := by
    intro y β
    simp only [hφ]
    unfold FiniteLaw.expect
    refine Fintype.sum_equiv (MulAction.toPerm (Multiplicative.ofAdd (-β))) _ _ fun x => ?_
    simp only [MulAction.toPerm_apply]
    have hw := halfLaw_transl h6 (Multiplicative.ofAdd (-β)) x
    have hfx := hf (Multiplicative.ofAdd (-β)) x
    rw [hw, hfx, smul_def, toAdd_ofAdd, labels_transl]
    have hiff : (labels x k = y + β) ↔ (labels x k + -β = y) := by
      constructor
      · intro h; rw [h]; ring
      · intro h; rw [← h]; ring
    simp only [hiff]
  have hconst : ∀ y, φ y = φ 0 := fun y => by
    have := hshift 0 y
    rw [zero_add] at this
    exact this
  have hsum : ∑ y, φ y = 0 := by
    simp only [hφ]
    unfold FiniteLaw.expect
    rw [sum_comm]
    have : ∀ x : CoreT F × PairT F, ∑ y : F, (halfLaw h6).weight x *
        (f x * if labels x k = y then 1 else 0) = (halfLaw h6).weight x * f x := by
      intro x
      rw [sum_eq_single (labels x k) (fun y _ hy => by simp [Ne.symm hy]) (by simp)]
      simp
    rw [sum_congr rfl fun x _ => this x]
    exact hf0
  have hφ0 : φ 0 = 0 := by
    rw [sum_congr rfl fun y _ => hconst y, sum_const, card_univ, nsmul_eq_mul] at hsum
    have hp : (Fintype.card F : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
    exact (mul_eq_zero.mp hsum).resolve_left hp
  have e : ∀ x : CoreT F × PairT F, f x * g (labels x k) =
      ∑ y, g y * (f x * if labels x k = y then 1 else 0) := by
    intro x
    rw [sum_eq_single (labels x k) (fun y _ hy => by simp [Ne.symm hy]) (by simp)]
    simp only [↓reduceIte, mul_one]
    ring
  rw [(halfLaw h6).expect_congr e]
  unfold FiniteLaw.expect
  simp only [mul_sum]
  rw [sum_comm]
  refine sum_eq_zero fun y _ => ?_
  have : φ y = 0 := by rw [hconst, hφ0]
  simp only [hφ, FiniteLaw.expect] at this
  calc ∑ x, (halfLaw h6).weight x * (g y * (f x * if labels x k = y then 1 else 0))
      = g y * ∑ x, (halfLaw h6).weight x * (f x * if labels x k = y then 1 else 0) := by
        rw [mul_sum]; exact sum_congr rfl fun x _ => by ring
    _ = 0 := by rw [this, mul_zero]

/-- A kernel depending on `x` only through the coordinate `x_i` (a row star) has zero form on
`𝓘 ∩ 𝟙^⊥`. -/
theorem form_left_zero (h6 : 6 ≤ Fintype.card F) {f : CoreT F × PairT F → ℝ}
    (hf : Invariant (Multiplicative F) f) (hf0 : (halfLaw h6).expect f = 0) (i : Fin 6)
    (A : F → CoreT F × PairT F → ℝ) :
    kernelForm (halfLaw h6) (halfLaw h6) (fun x x' => A (labels x i) x') f f = 0 := by
  simp only [kernelForm, LinearMap.mk₂_apply]
  rw [sum_comm]
  refine sum_eq_zero fun x' _ => ?_
  have h := cond_coord_zero h6 hf hf0 i (fun y => A y x')
  unfold FiniteLaw.expect at h
  calc ∑ x, (halfLaw h6).weight x * (halfLaw h6).weight x' * f x * A (labels x i) x' * f x'
      = (halfLaw h6).weight x' * f x' *
          ∑ x, (halfLaw h6).weight x * (f x * A (labels x i) x') := by
        rw [mul_sum]; exact sum_congr rfl fun x _ => by ring
    _ = 0 := by rw [h, mul_zero]

/-- A kernel depending on `x'` only through the coordinate `x'_j` (a column star) has zero form
on `𝓘 ∩ 𝟙^⊥`. -/
theorem form_right_zero (h6 : 6 ≤ Fintype.card F) {f : CoreT F × PairT F → ℝ}
    (hf : Invariant (Multiplicative F) f) (hf0 : (halfLaw h6).expect f = 0) (j : Fin 6)
    (B : CoreT F × PairT F → F → ℝ) :
    kernelForm (halfLaw h6) (halfLaw h6) (fun x x' => B x (labels x' j)) f f = 0 := by
  simp only [kernelForm, LinearMap.mk₂_apply]
  refine sum_eq_zero fun x _ => ?_
  have h := cond_coord_zero h6 hf hf0 j (fun y => B x y)
  unfold FiniteLaw.expect at h
  calc ∑ x', (halfLaw h6).weight x * (halfLaw h6).weight x' * f x * B x (labels x' j) * f x'
      = (halfLaw h6).weight x * f x *
          ∑ x', (halfLaw h6).weight x' * (f x' * B x (labels x' j)) := by
        rw [mul_sum]; exact sum_congr rfl fun x' _ => by ring
    _ = 0 := by rw [h, mul_zero]

theorem kernelForm_add_kernel {Ω : Type*} [Fintype Ω] (ν : FiniteLaw Ω) (K K' : Ω → Ω → ℝ)
    (f : Ω → ℝ) :
    kernelForm ν ν (fun x y => K x y + K' x y) f f =
      kernelForm ν ν K f f + kernelForm ν ν K' f f := by
  simp only [kernelForm, LinearMap.mk₂_apply, ← sum_add_distrib]
  refine sum_congr rfl fun x _ => sum_congr rfl fun y _ => ?_
  ring

/-- **The star terms vanish on `𝓘 ∩ 𝟙^⊥`** (`lem:spec:stars`(a),(b) with
`lem:spec:affpair`(d)). -/
theorem star_form_zero (h6 : 6 ≤ Fintype.card F) {f : CoreT F × PairT F → ℝ}
    (hf : Invariant (Multiplicative F) f) (hf0 : (halfLaw h6).expect f = 0) :
    kernelForm (halfLaw h6) (halfLaw h6)
      (fun x x' => starPart6 (labels x) (labels x')) f f = 0 := by
  have e : (fun x x' : CoreT F × PairT F => starPart6 (labels x) (labels x')) =
      fun x x' => (∑ i, ∑ j, crossD i j * chi (labels x' j - labels x i) +
        ∑ i, ∑ S ∈ supports6, (∏ j ∈ S, crossD i j) * ∏ j ∈ S, chi (labels x' j - labels x i)) +
        ∑ S ∈ supports6, ∑ j, (∏ i ∈ S, crossD i j) * ∏ i ∈ S, chi (labels x' j - labels x i) :=
    rfl
  rw [e, kernelForm_add_kernel, kernelForm_add_kernel]
  -- single pairs: column stars at `j`
  have t1 : kernelForm (halfLaw h6) (halfLaw h6)
      (fun x x' => ∑ i, ∑ j, crossD i j * chi (labels x' j - labels x i)) f f = 0 := by
    rw [kernelForm_sum_kernel]
    refine sum_eq_zero fun i _ => ?_
    rw [kernelForm_sum_kernel]
    refine sum_eq_zero fun j _ => ?_
    exact form_right_zero h6 hf hf0 j (fun x y => crossD i j * chi (y - labels x i))
  -- left stars: row stars at `i`
  have t2 : kernelForm (halfLaw h6) (halfLaw h6)
      (fun x x' => ∑ i, ∑ S ∈ supports6, (∏ j ∈ S, crossD i j) *
        ∏ j ∈ S, chi (labels x' j - labels x i)) f f = 0 := by
    rw [kernelForm_sum_kernel]
    refine sum_eq_zero fun i _ => ?_
    rw [kernelForm_sum_kernel]
    refine sum_eq_zero fun S _ => ?_
    exact form_left_zero h6 hf hf0 i
      (fun y x' => (∏ j ∈ S, crossD i j) * ∏ j ∈ S, chi (labels x' j - y))
  -- right stars: column stars at `j`
  have t3 : kernelForm (halfLaw h6) (halfLaw h6)
      (fun x x' => ∑ S ∈ supports6, ∑ j, (∏ i ∈ S, crossD i j) *
        ∏ i ∈ S, chi (labels x' j - labels x i)) f f = 0 := by
    rw [kernelForm_sum_kernel]
    refine sum_eq_zero fun S _ => ?_
    rw [kernelForm_sum_kernel]
    refine sum_eq_zero fun j _ => ?_
    exact form_right_zero h6 hf hf0 j
      (fun x y => (∏ i ∈ S, crossD i j) * ∏ i ∈ S, chi (y - labels x i))
  rw [t1, t2, t3]
  ring

/-- **`⟨f, K_soft f⟩ = ⟨f, T_ns f⟩` on `𝓘 ∩ 𝟙^⊥`** (proof of `prop:l20-completion`): the constant
term `𝟙 ⊗ 𝟙` and the star terms vanish there. -/
theorem soft_eq_nonstar (h6 : 6 ≤ Fintype.card F) {f : CoreT F × PairT F → ℝ}
    (hf : Invariant (Multiplicative F) f) (hf0 : (halfLaw h6).expect f = 0) :
    kernelForm (halfLaw h6) (halfLaw h6) Ksoft f f =
      kernelForm (halfLaw h6) (halfLaw h6) nonstar f f := by
  have e : (Ksoft : CoreT F × PairT F → CoreT F × PairT F → ℝ) =
      fun x x' => (1 + starPart6 (labels x) (labels x')) + nonstar x x' := by
    funext x x'
    unfold nonstar
    ring
  rw [e, kernelForm_add_kernel, kernelForm_add_kernel, star_form_zero h6 hf hf0]
  have h1 : kernelForm (halfLaw h6) (halfLaw h6) (fun _ _ => (1 : ℝ)) f f = 0 := by
    rw [kernelForm_apply]
    simp only [one_mul]
    rw [FiniteLaw.expect_mul_const, hf0, mul_zero]
  rw [h1]
  ring

/-- **The caps of L20 at a prime, with the nonstar cap** (`prop:l20-completion` with
`prop:l20-rectangular`(d)): `cutT_caps` with the hypothesis on `𝓘 ∩ 𝟙^⊥` replaced by the raw
nonstar cap `‖T_ns‖ ≤ N_ns` on `L²(μ_p)` (`cor:extraction-compressed`). -/
theorem cutT_caps_ns (hm1 : quadraticChar F (-1) = -1) (h6 : 6 ≤ Fintype.card F)
    {cR s D εZ Nns χp : ℝ} (hcR : 0 ≤ cR)
    (hRc : ∀ h : PairT F → ℝ,
      nrm (coreLaw (F := F)) (recOp (pairLaw (F := F)) Rc h) ≤ cR * nrm (pairLaw (F := F)) h)
    (hs : nrm (coreLaw (F := F)) rmass ≤ s) (hcs : cR ≤ s) (hD0 : 0 ≤ D)
    (hD : ∀ f, |kernelForm (halfLaw h6) (halfLaw h6) collK f f| ≤ D * nrm (halfLaw h6) f ^ 2)
    (hεZ : εZ < 1) (hZ : 1 - εZ ≤ Z0 h6) (hNns0 : 0 ≤ Nns)
    (hns : ∀ f, |kernelForm (halfLaw h6) (halfLaw h6) nonstar f f| ≤ Nns * nrm (halfLaw h6) f ^ 2)
    (hχ0 : 0 ≤ χp)
    (hchi : nrm (halfLaw h6) (fun x => recOp (halfLaw h6) (cutT h6) (fun _ => 1) x - 1) ^ 2 ≤ χp)
    (hC1 : (s * cR / prob ((coreLaw (F := F)).product (pairLaw (F := F))) Avoid + D) /
      (1 - εZ) < 1)
    (hH1 : (Nns + D) / (1 - εZ) < 1) (f : CoreT F × PairT F → ℝ) :
    -((s * cR / prob ((coreLaw (F := F)).product (pairLaw (F := F))) Avoid + D) / (1 - εZ)) *
        nrm (halfLaw h6) f ^ 2 ≤ kernelForm (halfLaw h6) (halfLaw h6) (cutT h6) f f ∧
      kernelForm (halfLaw h6) (halfLaw h6) (cutT h6) f f ≤
        (1 + χp / (1 - (Nns + D) / (1 - εZ))) * nrm (halfLaw h6) f ^ 2 :=
  cutT_caps hm1 h6 hcR hRc hs hcs hD0 hD hεZ hZ hNns0
    (fun f hf hf0 => by rw [soft_eq_nonstar h6 hf hf0]; exact hns f) hχ0 hchi hC1 hH1 f

/-- **`Z₀ ≥ 1 - ε_Z`, `ε_Z = N_ns + D_col + m_⋆`** (proof of `prop:l20-completion`, with
`lem:spec:expansion`): `Z₀ = ⟨𝟙, K₀𝟙⟩ = 1 + ⟨𝟙, (stars)𝟙⟩ + ⟨𝟙, T_ns𝟙⟩ - ⟨𝟙, T_coll𝟙⟩`, the star
means summing to at most `m_⋆` in modulus (`lem:l20-star-mean`, the hypothesis `hstar`). -/
theorem Z0_lower (h6 : 6 ≤ Fintype.card F) {Nns D mstar : ℝ}
    (hns : ∀ f, |kernelForm (halfLaw h6) (halfLaw h6) nonstar f f| ≤ Nns * nrm (halfLaw h6) f ^ 2)
    (hD : ∀ f, |kernelForm (halfLaw h6) (halfLaw h6) collK f f| ≤ D * nrm (halfLaw h6) f ^ 2)
    (hstar : |kernelForm (halfLaw h6) (halfLaw h6)
      (fun x x' => starPart6 (labels x) (labels x')) (fun _ => 1) (fun _ => 1)| ≤ mstar) :
    1 - (Nns + D + mstar) ≤ Z0 h6 := by
  have e : (K0 : CoreT F × PairT F → CoreT F × PairT F → ℝ) =
      fun x x' => ((1 + starPart6 (labels x) (labels x')) + nonstar x x') - collK x x' := by
    funext x x'
    rw [K0_eq]
    unfold nonstar
    ring
  have hsub : ∀ K K' : CoreT F × PairT F → CoreT F × PairT F → ℝ,
      kernelForm (halfLaw h6) (halfLaw h6) (fun x y => K x y - K' x y) (fun _ => 1) (fun _ => 1) =
        kernelForm (halfLaw h6) (halfLaw h6) K (fun _ => 1) (fun _ => 1) -
          kernelForm (halfLaw h6) (halfLaw h6) K' (fun _ => 1) (fun _ => 1) :=
    fun K K' => kernelForm_sub_kernel _ K K' _
  unfold Z0
  rw [e, hsub, kernelForm_add_kernel, kernelForm_add_kernel]
  have h1 : kernelForm (halfLaw h6) (halfLaw h6) (fun _ _ => (1 : ℝ)) (fun _ => 1)
      (fun _ => 1) = 1 := by
    rw [kernelForm_apply]
    simp
  rw [h1]
  have hn1 : nrm (halfLaw h6) (fun _ => (1 : ℝ)) = 1 := nrm_one _
  have a1 := hns (fun _ => 1)
  have a2 := hD (fun _ => 1)
  rw [hn1, one_pow, mul_one] at a1 a2
  have b1 := neg_abs_le (kernelForm (halfLaw h6) (halfLaw h6) nonstar (fun _ => 1) (fun _ => 1))
  have b2 := le_abs_self (kernelForm (halfLaw h6) (halfLaw h6) collK (fun _ => 1) (fun _ => 1))
  have b3 := neg_abs_le (kernelForm (halfLaw h6) (halfLaw h6)
    (fun x x' => starPart6 (labels x) (labels x')) (fun _ => 1) (fun _ => 1))
  linarith

end Sarkozy.L20Cap
