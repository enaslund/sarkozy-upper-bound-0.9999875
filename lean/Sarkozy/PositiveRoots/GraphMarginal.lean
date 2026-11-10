module

public import Sarkozy.PositiveRoots.Moments
public import Sarkozy.PartV.BlockLaw
public import Sarkozy.Labellings.GraphAutomorphism
public import Sarkozy.ProbabilityConstructions
public import Sarkozy.L20Cap.Rectangle

@[expose] public section

/-!
# The pair marginals of a graph law, and the score moments of the two components
(`lem:root-normalization`(b))

`paper/sections/20b_positive_roots.tex`, proof of `lem:root-normalization`(b): "each such pair is
a uniform ordered distinct pair: square-affine maps act transitively on each of the two orbits of
ordered distinct pairs and the layer swap exchanges them".

* `graphLaw_pair_marginal`: **for any graph law `λ_p(G)` and two vertices `v ≠ w` exchanged by an
  automorphism of `G`, the pair `(x_v, x_w)` is a uniform ordered distinct pair**:
  `E g(x_v, x_w) = (n(n − 1))^{-1} ∑_{y₀ ≠ y₁} g(y)`. The proof: the pair mass `Φ(b)` is invariant
  under the square-affine maps (`graphLaw_expect_affine`, V1) and under the swap
  (`graphLaw_expect_comp`), hence constant on the ordered distinct pairs (`pairMass_const`, the
  transitivity with `χ(−1) = −1`), and vanishes on the diagonal (`pairMass_diag`).
* `compGraph`: the cyclic `K_{2,2,2}` of one component of `G_{L,2}` (bases `0 → 1 → 2 → 0`, all
  four edges between consecutive bases); `compSwap_auto`: the layer swap is an automorphism.
* **`component_moments`**, `component_moment_hyps`: under the product of the two component laws,
  the score
  `H = H((x_i, x'_i), (y_{i'}, y'_{i'}))` of a base `i` of one component and a base `i'` of the
  other has `E H = qr` and `E H² = (n − 2)²/n² + (n − 3)²/(n²(n − 1))` — the exact moments of the
  proof, before global injectivity.

Not formalized: the identification of `Γ_{p,0} = λ_p(G_{L,2})` with the product of the two
component laws conditioned on global injectivity, and the coincidence counts (`36q`, the spike
mass), which are the hypotheses of `Moments.root_normalization_b`.
-/

namespace Sarkozy.PositiveRoots

open Finset Sarkozy Sarkozy.Labellings Sarkozy.L20Cap

section PairMarginal

variable {W : Type*} [Fintype W] [DecidableEq W] {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The pair mass `Φ(b) = P(x_v = b₀, x_w = b₁)` under the graph law. -/
noncomputable def pairMass (G : OrientedGraph W) (hne : (injLabellings F G).Nonempty) (v w : W)
    (b : F × F) : ℝ :=
  (graphLaw G hne).expect (fun x => if (x v, x w) = b then 1 else 0)

/-- `Φ` is invariant under the square-affine maps. -/
theorem pairMass_affine (G : OrientedGraph W) (hne : (injLabellings F G).Nonempty) (v w : W)
    {α : F} (hα : quadraticChar F α = 1) (β : F) (b : F × F) :
    pairMass G hne v w (α * b.1 + β, α * b.2 + β) = pairMass G hne v w b := by
  have hα0 : α ≠ 0 := by
    intro h; rw [h, quadraticChar_zero] at hα; exact zero_ne_one hα
  unfold pairMass
  rw [← Sarkozy.PartV.graphLaw_expect_affine G hne hα β
    (fun x => if (x v, x w) = (α * b.1 + β, α * b.2 + β) then (1 : ℝ) else 0)]
  refine FiniteLaw.expect_congr _ fun x => ?_
  have hiff : ((α * x v + β, α * x w + β) = (α * b.1 + β, α * b.2 + β)) ↔ ((x v, x w) = b) := by
    constructor
    · intro h
      simp only [Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := h
      have e1 : x v = b.1 := mul_left_cancel₀ hα0 (add_right_cancel h1)
      have e2 : x w = b.2 := mul_left_cancel₀ hα0 (add_right_cancel h2)
      rw [e1, e2]
    · intro h
      rw [← h]
  by_cases h : (x v, x w) = b
  · simp only [hiff.mpr h, h, ↓reduceIte]
  · have h' : ¬ (α * x v + β, α * x w + β) = (α * b.1 + β, α * b.2 + β) :=
      fun h'' => h (hiff.mp h'')
    simp only [h', h, ↓reduceIte]

/-- `Φ` is invariant under the swap, when an automorphism exchanges `v` and `w`. -/
theorem pairMass_swap (G : OrientedGraph W) (hne : (injLabellings F G).Nonempty) {v w : W}
    (π : W ≃ W) (hπ : IsAutomorphism G π) (hv : π v = w) (hw : π w = v) (b : F × F) :
    pairMass G hne v w (b.2, b.1) = pairMass G hne v w b := by
  unfold pairMass
  rw [← graphLaw_expect_comp G hne π hπ
    (fun x => if (x v, x w) = (b.2, b.1) then (1 : ℝ) else 0)]
  refine FiniteLaw.expect_congr _ fun x => ?_
  simp only [Function.comp_apply, hv, hw]
  have hiff : ((x w, x v) = (b.2, b.1)) ↔ ((x v, x w) = b) := by
    constructor
    · intro h; simp only [Prod.mk.injEq] at h; exact Prod.ext h.2 h.1
    · intro h; rw [← h]
  by_cases h : (x v, x w) = b
  · simp only [hiff.mpr h, h, ↓reduceIte]
  · have h' : ¬ (x w, x v) = (b.2, b.1) := fun h'' => h (hiff.mp h'')
    simp only [h', h, ↓reduceIte]

/-- **`Φ` is constant on the ordered distinct pairs** (`χ(−1) = −1`). -/
theorem pairMass_const (hm1 : quadraticChar F (-1) = -1) (G : OrientedGraph W)
    (hne : (injLabellings F G).Nonempty) {v w : W} (π : W ≃ W) (hπ : IsAutomorphism G π)
    (hv : π v = w) (hw : π w = v) {b b' : F × F} (hb : b.1 ≠ b.2) (hb' : b'.1 ≠ b'.2) :
    pairMass G hne v w b = pairMass G hne v w b' := by
  have trans : ∀ c c' : F × F, c.1 ≠ c.2 → c'.1 ≠ c'.2 →
      quadraticChar F (c'.2 - c'.1) = quadraticChar F (c.2 - c.1) →
      pairMass G hne v w c = pairMass G hne v w c' := by
    intro c c' hc hc' hcc
    have hd : c.2 - c.1 ≠ 0 := sub_ne_zero.mpr (Ne.symm hc)
    have hd' : c'.2 - c'.1 ≠ 0 := sub_ne_zero.mpr (Ne.symm hc')
    set α := (c'.2 - c'.1) / (c.2 - c.1) with hαdef
    have hα : quadraticChar F α = 1 := by
      rw [hαdef, div_eq_mul_inv, map_mul, hcc, quadraticChar_inv' hd]
      rcases quadraticChar_dichotomy hd with h | h <;> rw [h] <;> norm_num
    have himg : (α * c.1 + (c'.1 - α * c.1), α * c.2 + (c'.1 - α * c.1)) = c' := by
      ext
      · simp only; ring
      · simp only [hαdef]
        field_simp
        ring
    rw [← himg, pairMass_affine G hne v w hα]
  by_cases h : quadraticChar F (b'.2 - b'.1) = quadraticChar F (b.2 - b.1)
  · exact trans b b' hb hb' h
  · rw [← pairMass_swap G hne π hπ hv hw b]
    apply trans (b.2, b.1) b' (Ne.symm hb) hb'
    have hd : b.2 - b.1 ≠ 0 := sub_ne_zero.mpr (Ne.symm hb)
    have hd' : b'.2 - b'.1 ≠ 0 := sub_ne_zero.mpr (Ne.symm hb')
    have hneg : quadraticChar F ((b.2, b.1).2 - (b.2, b.1).1) = -quadraticChar F (b.2 - b.1) := by
      simp only
      have e : b.1 - b.2 = (-1) * (b.2 - b.1) := by ring
      rw [e, map_mul, hm1, neg_one_mul]
    rw [hneg]
    rcases quadraticChar_dichotomy hd with h1 | h1 <;>
      rcases quadraticChar_dichotomy hd' with h2 | h2 <;> rw [h1, h2] at h ⊢ <;> simp_all

/-- `Φ` vanishes on the diagonal (the labellings are injective). -/
theorem pairMass_diag (G : OrientedGraph W) (hne : (injLabellings F G).Nonempty) {v w : W}
    (hvw : v ≠ w) {b : F × F} (hb : b.1 = b.2) : pairMass G hne v w b = 0 := by
  unfold pairMass FiniteLaw.expect
  refine Finset.sum_eq_zero fun x _ => ?_
  by_cases hx : x ∈ injLabellings F G
  · have hinj := ((mem_injLabellings_iff_feasible G x).mp hx).1
    have : ¬ (x v, x w) = b := by
      intro h
      have h1 : x v = b.1 := by rw [← h]
      have h2 : x w = b.2 := by rw [← h]
      exact hvw (hinj v (mem_univ _) w (mem_univ _) (by rw [h1, h2, hb]))
    simp only [this, ↓reduceIte, mul_zero]
  · simp only [graphLaw, hx, ↓reduceIte, zero_mul]

/-- **The pair `(x_v, x_w)` is a uniform ordered distinct pair** under `λ_p(G)`, if `v ≠ w` are
exchanged by an automorphism of `G` (`χ(−1) = −1`). -/
theorem graphLaw_pair_marginal (hm1 : quadraticChar F (-1) = -1) (G : OrientedGraph W)
    (hne : (injLabellings F G).Nonempty) {v w : W} (hvw : v ≠ w) (π : W ≃ W)
    (hπ : IsAutomorphism G π) (hv : π v = w) (hw : π w = v) (g : F × F → ℝ) :
    (graphLaw G hne).expect (fun x => g (x v, x w)) =
      (∑ y ∈ distinctPairs F, g y) / ((distinctPairs F).card : ℝ) := by
  -- `E g(x_v, x_w) = ∑_b Φ(b) g(b)`
  have hsum : ∀ h : F × F → ℝ, (graphLaw G hne).expect (fun x => h (x v, x w)) =
      ∑ b, pairMass G hne v w b * h b := by
    intro h
    unfold pairMass FiniteLaw.expect
    have e : ∀ x : W → F, h (x v, x w) = ∑ b : F × F, (if (x v, x w) = b then 1 else 0) * h b := by
      intro x
      rw [Finset.sum_eq_single (x v, x w)]
      · simp
      · intro b _ hb; simp [Ne.symm hb]
      · simp
    simp only [e, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun x _ => by ring
  have hcard : (0 : ℝ) < ((distinctPairs F).card : ℝ) := by
    rw [card_distinctPairs]
    have h1 : (1 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.one_lt_card
    nlinarith
  -- the common value `Φ₀`
  obtain ⟨b₀, hb₀⟩ : ∃ b₀ : F × F, b₀.1 ≠ b₀.2 := by
    obtain ⟨a, b, hab⟩ := Fintype.exists_pair_of_one_lt_card (Fintype.one_lt_card (α := F))
    exact ⟨(a, b), hab⟩
  obtain ⟨Φ₀, hΦ₀⟩ : ∃ c : ℝ, pairMass G hne v w b₀ = c := ⟨_, rfl⟩
  have hΦ : ∀ b : F × F, pairMass G hne v w b = if b.1 ≠ b.2 then Φ₀ else 0 := by
    intro b
    split_ifs with hb
    · rw [← hΦ₀]
      exact pairMass_const hm1 G hne π hπ hv hw hb hb₀
    · exact pairMass_diag G hne hvw (not_not.mp hb)
  have hfilter : ∀ h : F × F → ℝ, ∑ b, (if b.1 ≠ b.2 then Φ₀ else 0) * h b =
      Φ₀ * ∑ y ∈ distinctPairs F, h y := by
    intro h
    unfold distinctPairs
    rw [Finset.sum_filter, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    split_ifs <;> ring
  -- total mass one fixes `Φ₀`
  have htot : Φ₀ * ((distinctPairs F).card : ℝ) = 1 := by
    have h1 := hsum (fun _ => 1)
    rw [FiniteLaw.expect_const] at h1
    have e1 : ∑ b, pairMass G hne v w b * (fun _ : F × F => (1 : ℝ)) b =
        ∑ b, (if b.1 ≠ b.2 then Φ₀ else 0) * (fun _ : F × F => (1 : ℝ)) b :=
      Finset.sum_congr rfl fun b _ => by rw [hΦ b]
    rw [e1, hfilter] at h1
    have h2 : ∑ y ∈ distinctPairs F, (fun _ : F × F => (1 : ℝ)) y =
        ((distinctPairs F).card : ℝ) := by
      simp
    rw [h2] at h1
    linarith
  have e2 : ∑ b, pairMass G hne v w b * g b = ∑ b, (if b.1 ≠ b.2 then Φ₀ else 0) * g b :=
    Finset.sum_congr rfl fun b _ => by rw [hΦ b]
  rw [hsum, e2, hfilter, eq_div_iff hcard.ne']
  calc Φ₀ * (∑ y ∈ distinctPairs F, g y) * ((distinctPairs F).card : ℝ)
      = (Φ₀ * ((distinctPairs F).card : ℝ)) * ∑ y ∈ distinctPairs F, g y := by ring
    _ = ∑ y ∈ distinctPairs F, g y := by rw [htot, one_mul]

end PairMarginal

/-! ## The product of two laws with uniform pair marginals -/

section Product

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The score moments under a product law with uniform pair marginals** (`F × F`-valued
projections): if `E_{μᵢ} g(πᵢ) = (n(n−1))^{-1} ∑_{y₀≠y₁} g(y)`, then under `μ₁ ⊗ μ₂`,
`E H(π₁, π₂) = qr` and `E H(π₁, π₂)² = (n − 2)²/n² + (n − 3)²/(n²(n − 1))`. -/
theorem product_moments_pairs (hF : ringChar F ≠ 2) {Ω₁ Ω₂ : Type*} [Fintype Ω₁] [Fintype Ω₂]
    (μ₁ : FiniteLaw Ω₁) (μ₂ : FiniteLaw Ω₂) (π₁ : Ω₁ → F × F) (π₂ : Ω₂ → F × F)
    (h₁ : ∀ g : F × F → ℝ, μ₁.expect (fun ω => g (π₁ ω)) =
      (∑ y ∈ distinctPairs F, g y) / ((distinctPairs F).card : ℝ))
    (h₂ : ∀ g : F × F → ℝ, μ₂.expect (fun ω => g (π₂ ω)) =
      (∑ y ∈ distinctPairs F, g y) / ((distinctPairs F).card : ℝ)) :
    (μ₁.product μ₂).expect (fun ω => pairScore (π₁ ω.1) (π₂ ω.2)) =
        1 / (Fintype.card F : ℝ) * (1 / Real.sqrt (Fintype.card F)) ∧
      (μ₁.product μ₂).expect (fun ω => pairScore (π₁ ω.1) (π₂ ω.2) ^ 2) =
        ((Fintype.card F : ℝ) - 2) ^ 2 / (Fintype.card F : ℝ) ^ 2 +
          ((Fintype.card F : ℝ) - 3) ^ 2 /
            ((Fintype.card F : ℝ) ^ 2 * ((Fintype.card F : ℝ) - 1)) := by
  have key : ∀ g : F × F → F × F → ℝ,
      (μ₁.product μ₂).expect (fun ω => g (π₁ ω.1) (π₂ ω.2)) =
        (∑ y ∈ distinctPairs F, ∑ y' ∈ distinctPairs F, g y y') /
          ((distinctPairs F).card : ℝ) ^ 2 := by
    intro g
    rw [FiniteLaw.expect_product]
    have e2 : ∀ ω₁ : Ω₁, μ₂.expect (fun ω₂ => g (π₁ (ω₁, ω₂).1) (π₂ (ω₁, ω₂).2)) =
        (∑ y' ∈ distinctPairs F, g (π₁ ω₁) y') / ((distinctPairs F).card : ℝ) :=
      fun ω₁ => h₂ (fun y' => g (π₁ ω₁) y')
    simp only [e2]
    rw [h₁ (fun y => (∑ y' ∈ distinctPairs F, g y y') / ((distinctPairs F).card : ℝ))]
    rw [← Finset.sum_div, div_div, sq]
  exact ⟨(key (fun y y' => pairScore y y')).trans (pairScore_mean hF),
    (key (fun y y' => pairScore y y' ^ 2)).trans (pairScore_sq_mean hF)⟩

end Product

/-! ## The two components of `G_{L,2}` -/

section Components

/-- **One component of `G_{L,2}`**: the cyclic `K_{2,2,2}` on `{0,1,2} × {0,1}`, with the four
edges `(i, ℓ) → (i + 1, ℓ')` between consecutive bases (`lem:root-normalization`(b), proof). -/
def compGraph : OrientedGraph (Fin 3 × Fin 2) where
  E := univ.filter fun e => e.2.1 = e.1.1 + 1
  loopless u := by
    simp only [mem_filter, mem_univ, true_and]
    revert u
    decide
  oriented u v := by
    simp only [mem_filter, mem_univ, true_and]
    revert u v
    decide

/-- The layer swap `(i, ℓ) ↦ (i, 1 − ℓ)`. -/
def compSwap : Fin 3 × Fin 2 ≃ Fin 3 × Fin 2 :=
  Equiv.prodCongr (Equiv.refl _) (Equiv.swap 0 1)

/-- **The layer swap is an automorphism of the component.** -/
theorem compSwap_auto : IsAutomorphism compGraph compSwap := by
  intro u v
  simp only [compGraph, mem_filter, mem_univ, true_and]
  exact Iff.rfl

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The base pairs of a component are uniform ordered distinct pairs** (`χ(−1) = −1`). -/
theorem comp_pair_marginal (hm1 : quadraticChar F (-1) = -1)
    (hne : (injLabellings F compGraph).Nonempty) (i : Fin 3) (g : F × F → ℝ) :
    (graphLaw compGraph hne).expect (fun x => g (x (i, 0), x (i, 1))) =
      (∑ y ∈ distinctPairs F, g y) / ((distinctPairs F).card : ℝ) :=
  graphLaw_pair_marginal hm1 compGraph hne
    (fun h => absurd (congrArg Prod.snd h) (by simp)) compSwap compSwap_auto
    (by simp [compSwap]) (by simp [compSwap]) g

/-- **`lem:root-normalization`(b), the moments before global injectivity**: under the product of
the two component laws, the score pairing the base `i` of the first component with the base `i'`
of the second has `E H = qr` and `E H² = (n − 2)²/n² + (n − 3)²/(n²(n − 1))
= (1 − 2q)² + q(1 − 3q)²/(1 − q)`. -/
theorem component_moments (hm1 : quadraticChar F (-1) = -1) (hF : ringChar F ≠ 2)
    (hne : (injLabellings F compGraph).Nonempty) (i i' : Fin 3) :
    ((graphLaw compGraph hne).product (graphLaw compGraph hne)).expect
        (fun ω => pairScore (ω.1 (i, 0), ω.1 (i, 1)) (ω.2 (i', 0), ω.2 (i', 1))) =
        1 / (Fintype.card F : ℝ) * (1 / Real.sqrt (Fintype.card F)) ∧
      ((graphLaw compGraph hne).product (graphLaw compGraph hne)).expect
        (fun ω => pairScore (ω.1 (i, 0), ω.1 (i, 1)) (ω.2 (i', 0), ω.2 (i', 1)) ^ 2) =
        ((Fintype.card F : ℝ) - 2) ^ 2 / (Fintype.card F : ℝ) ^ 2 +
          ((Fintype.card F : ℝ) - 3) ^ 2 /
            ((Fintype.card F : ℝ) ^ 2 * ((Fintype.card F : ℝ) - 1)) :=
  product_moments_pairs hF (graphLaw compGraph hne) (graphLaw compGraph hne)
    (fun x => (x (i, 0), x (i, 1))) (fun y => (y (i', 0), y (i', 1)))
    (comp_pair_marginal hm1 hne i) (comp_pair_marginal hm1 hne i')

/-- **The moment hypotheses of `root_normalization_b`, discharged before global injectivity**:
under the product of the two component laws, with `q = 1/n` and `r = n^{-1/2}`, the score of a
base pair has `E H = qr` and `E H² ≥ 1 − 4q` (`hmean`, `hsq` of `Moments.root_normalization_b`). -/
theorem component_moment_hyps (hm1 : quadraticChar F (-1) = -1) (hF : ringChar F ≠ 2)
    (hne : (injLabellings F compGraph).Nonempty) (i i' : Fin 3) :
    ((graphLaw compGraph hne).product (graphLaw compGraph hne)).expect
        (fun ω => pairScore (ω.1 (i, 0), ω.1 (i, 1)) (ω.2 (i', 0), ω.2 (i', 1))) =
        (1 / (Fintype.card F : ℝ)) * (1 / Real.sqrt (Fintype.card F)) ∧
      1 - 4 * (1 / (Fintype.card F : ℝ)) ≤
        ((graphLaw compGraph hne).product (graphLaw compGraph hne)).expect
          (fun ω => pairScore (ω.1 (i, 0), ω.1 (i, 1)) (ω.2 (i', 0), ω.2 (i', 1)) ^ 2) := by
  obtain ⟨h1, h2⟩ := component_moments hm1 hF hne i i'
  refine ⟨h1, ?_⟩
  rw [h2]
  have hn : (2 : ℝ) ≤ Fintype.card F := by
    have := Fintype.one_lt_card (α := F)
    exact_mod_cast this
  rw [sq_mean_eq_paper hn]
  have hq0 : (0 : ℝ) ≤ 1 / (Fintype.card F : ℝ) := by positivity
  have hq1 : 1 / (Fintype.card F : ℝ) < 1 := by
    rw [div_lt_one (by linarith)]; linarith
  exact pairScore_sq_mean_ge hq0 hq1

end Components

end Sarkozy.PositiveRoots
