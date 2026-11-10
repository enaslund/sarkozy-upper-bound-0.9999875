module

public import Sarkozy.PartV.TailSplit
public import Sarkozy.PartV.TailFamily
public import Sarkozy.TraceMixing.TailMixing
public import Sarkozy.Comparison.AnalyticStage

@[expose] public section

/-!
# Tail mixing (`lem:record:tail-mixing`)

`paper/sections/27_tail_index.tex`, `lem:record:tail-mixing`, with `lem:mixture`
(`paper/sections/06_lifts_sectors.tex`, `Sarkozy.Mixing.mixture_mixing`), `lem:trace-mixing`(d)
(`paper/sections/12_labellings.tex`, through WP-S's `Sarkozy.TraceMixing.tail_mixing_S` and
`tail_R4`) and `lem:tail-law`(iii) (V1's `tailTilde_split`, `tail_nonroot_mass`).

**The tail law as a mixture** (proof of the lemma, first paragraph). `μ̃_p = π_{LL,2} + ρ̃_p`, so
`μ_p = ϖ π_{LL,2} + (1 - ϖ) ρ_p` with `h_p = P_μ(r) - 1 > 0`, `ϖ = 1/(1 + h_p)` and
`ρ_p = ρ̃_p/h_p` (`tailLaw_mixture`, `tailRest`). The root component `π_{LL,2}` is the image of
`λ_p(G_{LL,2})` under the root emission `(u₀, u₁, ℓ) ↦ (u₀, u₁, ℓ)`, a bijection of the 72 slots
onto the vertices of `G_{LL,2}`, so it is the graph law of the pulled-back graph `slotRootGraph`
(`tailRootComponent_weight`). That graph has `72` vertices, degrees `≤ 20` (ten out- and ten
in-neighbours, `slotRootGraph_degree`) and contains the six queries of `𝓔₆`
(`query_mem_slotRootGraph`). `ρ_p` has uniform one-slot marginals (`tailRest_uniform`).

**The constant.** `h_p ≤ C₁ p^{-1/2} ≤ S₇₂(p) - 2⁹²/p` for `p ≥ P₄` (`tailH_le_S72`). Part (c):
`p^{2γ} S₇₂(p)` is strictly decreasing (`scaled_S72_strictAntiOn`), `2γ = 255/512`, and
`S₇₂(p) < p^{-2γ}` for every `p ≥ P₅ = 2^{65536}` (`S72_lt_rpow`).

**Results** (all assuming Weil's bound H1, `Target.Weil`, which `lem:trace-mixing` uses):
* (a) for `μ_p`, `p ≥ P₄`: `tailLaw_slot_S72`;
* (R4) for `μ_p`, `p ≥ P₅`: `tailLaw_R4`, and the field `mixing` of `TheoremC.Reference` for
  `μp := tailLawFamily` with `P5 := 2^{65536}`: `tailLawFamily_mixing`;
* (a), (b) for `ν̄_p`, `p ≥ P₄`: `tailAccepted_S72`; (R4) for `ν̄_p`, `p ≥ P₅`:
  `tailAccepted_R4`. The tail comparison law is not defined in Lean, so these take the facts the
  proof uses as the bundle `AcceptedTailData` (non-vacuity: `rootAcceptedTailData`).

**Interpretation choices.**
1. Conditional operators, norms and mixing are those of `Sarkozy.Mixing` (`condOp`,
   `ContractsMeanZero`, `IsGammaMixing`, `def:mixing`): squared norms from `L²` of the source
   marginal on the mean-zero functions to `L²` of the target marginal.
2. In part (c) the bound `S₇₂(p) < p^{-2γ}` is proved directly at every `p ≥ P₅` from the
   bounds on `C₁, C₂, C₃` (`tailC_bounds`), not from the monotonicity and the value at `P₅` of
   (S7); the monotonicity is proved as well.
3. Unif(`Ω`) of a pair is in the `srcWeight` form of `Sarkozy.TraceMixing` (`omegaWeight`), not
   `TheoremC.PairUniformOmega`.
4. At a prime where some labelling set of the tail law is empty, `tailLawFamily` is the uniform
   law (V1's convention); it is mixing there with every constant (`isMixing_uniform`). Under H1
   this happens only at finitely many primes (`tailNonempty_of_large`).
-/

namespace Sarkozy.PartVRecords

open Finset Sarkozy.Labellings Sarkozy.Mixing Sarkozy.PartV

/-! ## Pulling a graph back along a bijection of the vertices -/

section Comap

variable {W W' : Type*} [Fintype W] [DecidableEq W] [Fintype W'] [DecidableEq W']

/-- The graph on `W` whose edges are the preimages of the edges of `G` under a bijection
`e : W ≃ W'`. -/
def comapGraph (G : OrientedGraph W') (e : W ≃ W') : OrientedGraph W where
  E := univ.filter fun x => (e x.1, e x.2) ∈ G.E
  loopless u := by
    simp only [mem_filter, mem_univ, true_and]
    exact G.loopless (e u)
  oriented u v := by
    simp only [mem_filter, mem_univ, true_and]
    exact G.oriented (e u) (e v)

omit [DecidableEq W] [Fintype W'] in
theorem mem_comapGraph (G : OrientedGraph W') (e : W ≃ W') (x : W × W) :
    x ∈ (comapGraph G e).E ↔ (e x.1, e x.2) ∈ G.E := by
  simp only [comapGraph, mem_filter, mem_univ, true_and]

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

omit [DecidableEq W] in
/-- Feasibility is transported by the bijection. -/
theorem feasible_comap_iff (G : OrientedGraph W') (e : W ≃ W') (z : W → F) :
    Feasible F (comapGraph G e) univ z ↔ Feasible F G univ (z ∘ e.symm) := by
  constructor
  · rintro ⟨hinj, hedge⟩
    refine ⟨fun a _ b _ hab => e.symm.injective (hinj _ (mem_univ _) _ (mem_univ _) hab),
      fun x hx _ _ => ?_⟩
    have hx' : (e.symm x.1, e.symm x.2) ∈ (comapGraph G e).E := by
      rw [mem_comapGraph]
      simpa only [Equiv.apply_symm_apply] using hx
    exact hedge _ hx' (mem_univ _) (mem_univ _)
  · rintro ⟨hinj, hedge⟩
    refine ⟨fun a _ b _ hab => ?_, fun x hx _ _ => ?_⟩
    · have h := hinj (e a) (mem_univ _) (e b) (mem_univ _)
        (by simpa only [Function.comp_apply, Equiv.symm_apply_apply] using hab)
      exact e.injective h
    · rw [mem_comapGraph] at hx
      have h := hedge _ hx (mem_univ _) (mem_univ _)
      simpa only [Function.comp_apply, Equiv.symm_apply_apply] using h

theorem mem_injLabellings_comap (G : OrientedGraph W') (e : W ≃ W') (z : W → F) :
    z ∈ injLabellings F (comapGraph G e) ↔ z ∘ e.symm ∈ injLabellings F G := by
  rw [mem_injLabellings_iff_feasible, mem_injLabellings_iff_feasible]
  exact feasible_comap_iff G e z

/-- Relabelling by the bijection identifies the two labelling sets. -/
theorem card_injLabellings_comap (G : OrientedGraph W') (e : W ≃ W') :
    (injLabellings F (comapGraph G e)).card = (injLabellings F G).card := by
  refine Finset.card_equiv (Equiv.arrowCongr e (Equiv.refl F)) fun z => ?_
  rw [mem_injLabellings_comap]
  rfl

theorem injLabellings_comap_nonempty (G : OrientedGraph W') (e : W ≃ W')
    (hne : (injLabellings F G).Nonempty) : (injLabellings F (comapGraph G e)).Nonempty := by
  rw [← Finset.card_pos, card_injLabellings_comap]
  exact Finset.card_pos.mpr hne

/-- **The graph law of the pulled-back graph is the pullback of the graph law.** -/
theorem graphLaw_comap_weight (G : OrientedGraph W') (e : W ≃ W')
    (hne : (injLabellings F G).Nonempty) (z : W → F) :
    (graphLaw (comapGraph G e) (injLabellings_comap_nonempty G e hne)).weight z =
      (graphLaw G hne).weight (z ∘ e.symm) := by
  have hiff := mem_injLabellings_comap G e z
  simp only [graphLaw, card_injLabellings_comap]
  by_cases h : z ∘ e.symm ∈ injLabellings F G
  · simp only [hiff.mpr h, h, ↓reduceIte]
  · simp only [mt hiff.mp h, h, ↓reduceIte]

/-- The same, for any graph `G'` equal to the pullback and any proof of nonemptiness. -/
theorem graphLaw_comap_weight' (G : OrientedGraph W') (e : W ≃ W')
    (hne : (injLabellings F G).Nonempty) (G' : OrientedGraph W) (hG' : G' = comapGraph G e)
    (hne' : (injLabellings F G').Nonempty) (z : W → F) :
    (graphLaw G' hne').weight z = (graphLaw G hne).weight (z ∘ e.symm) := by
  subst hG'
  exact graphLaw_comap_weight G e hne z

/-- Out-neighbours are transported by the bijection. -/
theorem card_out_comap (G : OrientedGraph W') (e : W ≃ W') (v : W) :
    (univ.filter fun u => (v, u) ∈ (comapGraph G e).E).card =
      (univ.filter fun u' => (e v, u') ∈ G.E).card := by
  refine Finset.card_equiv e fun u => ?_
  simp only [mem_filter, mem_univ, true_and, mem_comapGraph]

/-- In-neighbours are transported by the bijection. -/
theorem card_in_comap (G : OrientedGraph W') (e : W ≃ W') (v : W) :
    (univ.filter fun u => (u, v) ∈ (comapGraph G e).E).card =
      (univ.filter fun u' => (u', e v) ∈ G.E).card := by
  refine Finset.card_equiv e fun u => ?_
  simp only [mem_filter, mem_univ, true_and, mem_comapGraph]

/-- The degree is at most the out-degree plus the in-degree. -/
theorem degree_le_out_add_in (G : OrientedGraph W) (v : W) :
    TraceMixing.degree G v ≤ (univ.filter fun u => (v, u) ∈ G.E).card +
      (univ.filter fun u => (u, v) ∈ G.E).card := by
  unfold TraceMixing.degree nbrCount
  calc _ ≤ ((univ.filter fun u => (v, u) ∈ G.E) ∪ (univ.filter fun u => (u, v) ∈ G.E)).card := by
        apply Finset.card_le_card
        intro u hu
        simp only [mem_filter, mem_erase, mem_univ, true_and, mem_union] at hu ⊢
        tauto
    _ ≤ _ := Finset.card_union_le _ _

end Comap

/-! ## The root graph on the 72 slots -/

/-- The root emission `(u₀, u₁, ℓ) ↦ (u₀, u₁, ℓ)` of the state `LL` (identity patterns in both
coordinates) as a bijection `V ≃ ℤ/6ℤ × ℤ/6ℤ × {0, 1}`. -/
def rootSlotEquiv : Slot ≃ ZMod 6 × ZMod 6 × Fin 2 where
  toFun := upEmission (fun u : ZMod 6 => u) (fun u => u)
  invFun w := (w.1, w.2.1, ((w.2.2 : ℕ) : ZMod 2))
  left_inv v := by
    obtain ⟨a, b, c⟩ := v
    fin_cases c <;> rfl
  right_inv w := by
    obtain ⟨a, b, c⟩ := w
    fin_cases c <;> rfl

/-- **The root graph on the slots**: `G_{LL,2}` (`rootGraph`) read through the root emission.
It is irreducible: membership in its edge `Finset` must not be evaluated by the unifier (the
`Finset` has `72²` candidate pairs); use `slotRootGraph_eq`. -/
@[irreducible] def slotRootGraph : OrientedGraph Slot := comapGraph rootGraph rootSlotEquiv

theorem slotRootGraph_eq : slotRootGraph = comapGraph rootGraph rootSlotEquiv := by
  unfold slotRootGraph
  rfl

/-- The root graph has `72` vertices. -/
theorem slotRootGraph_card : Fintype.card Slot = 72 := card_slot

theorem mem_rootGraph_iff (x : (ZMod 6 × ZMod 6 × Fin 2) × (ZMod 6 × ZMod 6 × Fin 2)) :
    x ∈ rootGraph.E ↔ twoLayerEdge (Λ := Fin 2) typeL typeL x.1 x.2 = true := by
  rw [rootGraph, mem_twoLayerGraph]

/-- **Every vertex of the root graph has degree at most `20`** (ten out- and ten in-neighbours,
`lem:upper-geometry`(a)). -/
theorem slotRootGraph_degree (v : Slot) : TraceMixing.degree slotRootGraph v ≤ 20 := by
  refine (degree_le_out_add_in slotRootGraph v).trans ?_
  rw [slotRootGraph_eq, card_out_comap, card_in_comap]
  have hout : (univ.filter fun u' => (rootSlotEquiv v, u') ∈ rootGraph.E).card = 10 := by
    have hf := Finset.filter_congr (s := univ) fun u' _ => mem_rootGraph_iff (rootSlotEquiv v, u')
    exact (congrArg Finset.card hf).trans (root_outDegree (rootSlotEquiv v))
  have hin : (univ.filter fun u' => (u', rootSlotEquiv v) ∈ rootGraph.E).card = 10 := by
    have hf := Finset.filter_congr (s := univ) fun u' _ => mem_rootGraph_iff (u', rootSlotEquiv v)
    exact (congrArg Finset.card hf).trans (root_inDegree (rootSlotEquiv v))
  exact (add_le_add hout.le hin.le).trans (le_of_eq rfl)

/-- **Each query of `𝓔₆` is an edge of the root graph**, oriented from `u_e = (0, j, 0)` to
`v_e = (2, rot j, 1)` (`lem:tail-law`(iii)). -/
theorem query_mem_slotRootGraph (j : Chamber) :
    (querySource j, queryTarget j) ∈ slotRootGraph.E := by
  rw [slotRootGraph_eq, mem_comapGraph, mem_rootGraph_iff]
  have h1 : rootSlotEquiv (queryTarget j) = ((2 : ZMod 6), rot j, (1 : Fin 2)) := by
    change ((2 : ZMod 6), chamberRotation j, layerFin 1) = _
    rw [layerFin_one, rot_eq_chamberRotation]
  have h2 : rootSlotEquiv (querySource j) = ((0 : ZMod 6), j, (0 : Fin 2)) := by
    change ((0 : ZMod 6), j, layerFin 0) = _
    rw [layerFin_zero]
  rw [h1, h2]
  exact query_edge_bool j

/-- An emission along a bijection: the weight of `z` is that of `z ∘ e⁻¹`. -/
theorem emit_equiv_weight {I X : Type*} [Fintype I] [DecidableEq I] [Fintype X] [DecidableEq X]
    (lam : FiniteLaw (I → X)) (e : Slot ≃ I) (z : Slot → X) :
    (emit lam e).weight z = lam.weight (z ∘ e.symm) := by
  unfold emit FiniteLaw.map
  simp only
  rw [Finset.sum_eq_single (z ∘ e.symm)]
  · have h : (z ∘ e.symm) ∘ e = z := by
      funext v
      simp only [Function.comp_apply, Equiv.symm_apply_apply]
    simp only [h, ↓reduceIte]
  · intro y _ hy
    have h : y ∘ e ≠ z := by
      intro h
      apply hy
      rw [← h]
      funext w
      simp only [Function.comp_apply, Equiv.apply_symm_apply]
    simp only [h, ↓reduceIte]
  · intro h
    exact absurd (mem_univ _) h

section Root

variable (p : ℕ) [Fact p.Prime]

/-- The labelling set of the root graph on the slots is nonempty when that of `G_{LL,2}` is. -/
theorem slotRoot_nonempty (hne : TailNonempty p) :
    (injLabellings (ZMod p) slotRootGraph).Nonempty := by
  rw [slotRootGraph_eq]
  exact injLabellings_comap_nonempty rootGraph rootSlotEquiv (hne.two .L .L)

/-- **The root component `π_{LL,2}` of the tail law is the graph law `λ_p` of the root graph on
the slots.** -/
theorem tailRootComponent_weight (hne : TailNonempty p) (z : Slot → ZMod p) :
    (tailRootComponent p hne).weight z =
      (graphLaw slotRootGraph (slotRoot_nonempty p hne)).weight z := by
  rw [graphLaw_comap_weight' rootGraph rootSlotEquiv (hne.two .L .L) slotRootGraph
    slotRootGraph_eq]
  exact emit_equiv_weight (graphLaw rootGraph (hne.two .L .L)) rootSlotEquiv z

end Root

/-! ## Mixtures with a common one-slot marginal -/

section MixtureTools

variable {V X : Type*} [Fintype V] [DecidableEq V] [Fintype X] [DecidableEq X]

omit [DecidableEq X] in
/-- The expectation of a two-component mixture. -/
theorem expect_of_mix {μ π ρ : FiniteLaw (V → X)} {ϖ : ℝ}
    (hμ : ∀ z, μ.weight z = ϖ * π.weight z + (1 - ϖ) * ρ.weight z) (f : (V → X) → ℝ) :
    μ.expect f = ϖ * π.expect f + (1 - ϖ) * ρ.expect f := by
  unfold FiniteLaw.expect
  simp only [hμ, add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]

omit [DecidableEq X] in
/-- **The second component of a mixture inherits uniform one-slot marginals** when the mixture
and the first component have them and `ϖ ≠ 1`. -/
theorem uniform_of_mix [Nonempty X] {μ π ρ : FiniteLaw (V → X)} {ϖ : ℝ} (hϖ : ϖ ≠ 1)
    (hμ : ∀ z, μ.weight z = ϖ * π.weight z + (1 - ϖ) * ρ.weight z)
    (hμu : HasUniformMarginals μ) (hπu : HasUniformMarginals π) : HasUniformMarginals ρ := by
  intro v g
  have h := expect_of_mix hμ (fun z => g (z v))
  rw [hμu v g, hπu v g] at h
  have h1 : (1 - ϖ) ≠ 0 := sub_ne_zero.mpr (Ne.symm hϖ)
  have h2 : (1 - ϖ) * ρ.expect (fun z => g (z v)) =
      (1 - ϖ) * (FiniteLaw.uniform X).expect g := by linarith
  exact mul_left_cancel₀ h1 h2

/-- A joint law with constant weight contracts every mean-zero function to zero. -/
theorem contractsMeanZero_of_const {A B : Type*} [Fintype A] [Fintype B] [Nonempty B]
    (κ : FiniteLaw (A × B)) (c₀ : ℝ) (hκ : ∀ x, κ.weight x = c₀) (c : ℝ) :
    ContractsMeanZero κ c := by
  intro f hf
  have hB : (Fintype.card B : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hsrc (a : A) : srcWeight κ a = c₀ * Fintype.card B := by
    simp only [srcWeight, hκ, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  have hsum : c₀ * ∑ a, f a = 0 := by
    simp only [hsrc] at hf
    rw [← Finset.mul_sum] at hf
    have h := mul_eq_zero.mp hf
    rcases h with h | h
    · rcases mul_eq_zero.mp h with h' | h'
      · rw [h', zero_mul]
      · exact absurd h' hB
    · rw [h, mul_zero]
  have hb (b : B) : tgtWeight κ b * condOp κ f b = 0 := by
    rw [tgt_mul_condOp]
    simp only [hκ]
    rw [← Finset.mul_sum]
    exact hsum
  have hzero : ∑ b, tgtWeight κ b * condOp κ f b ^ 2 = 0 := by
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [pow_two, ← mul_assoc, hb b, zero_mul]
  rw [hzero]
  exact mul_nonneg (sq_nonneg c)
    (Finset.sum_nonneg fun a _ => mul_nonneg (srcWeight_nonneg κ a) (sq_nonneg _))

/-- **The uniform law is mixing at every slot, with every constant**: its conditional operators
vanish on the mean-zero functions. -/
theorem isMixing_uniform [Nonempty X] (v : V) (c : ℝ) :
    IsMixing (FiniteLaw.uniform (V → X)) {v} c := by
  rw [isMixing_singleton_iff]
  refine contractsMeanZero_of_const _ (Fintype.card (V → X) : ℝ)⁻¹ (fun x => ?_) c
  rw [slotJoint_weight]
  rfl

end MixtureTools

/-! ## The tail law as a two-component mixture -/

section Mixture

variable (p : ℕ) [Fact p.Prime]

/-- **The nonroot mass** `h_p = P_μ(r) - 1` of the tail law (`lem:tail-law`(iii)). -/
noncomputable def tailH : ℝ := upPoly tailWeights (tailR p) - 1

theorem tailR_pos : 0 < tailR p :=
  Real.rpow_pos_of_pos (Nat.cast_pos.mpr (Fact.out : p.Prime).pos) _

omit [Fact p.Prime] in
theorem tailH_eq : tailH p = 5988 / 5 * tailR p + 15232626 / 25 * tailR p ^ 2 +
    24807984744 / 175 * tailR p ^ 3 + 50638290432 / 5 * tailR p ^ 4 +
    621170191872 / 5 * tailR p ^ 5 + 1877429977088 / 7 * tailR p ^ 6 +
    970455252992 / 7 * tailR p ^ 7 := by
  unfold tailH
  rw [tailPoly_eq]
  ring

/-- `h_p > 0`: the records of degree one have positive weight. -/
theorem tailH_pos : 0 < tailH p := by
  rw [tailH_eq]
  have := tailR_pos p
  positivity

/-- **The mixture weight of the root**, `ϖ = 1/(1 + h_p)`. -/
noncomputable def tailVarpi : ℝ := 1 / (1 + tailH p)

theorem tailVarpi_pos : 0 < tailVarpi p := by
  unfold tailVarpi
  have := tailH_pos p
  positivity

theorem tailVarpi_le_one : tailVarpi p ≤ 1 := by
  unfold tailVarpi
  rw [div_le_one (by linarith [tailH_pos p])]
  linarith [tailH_pos p]

/-- `1 - ϖ = h_p/(1 + h_p) ≤ h_p`. -/
theorem one_sub_tailVarpi_le : 1 - tailVarpi p ≤ tailH p := by
  unfold tailVarpi
  have hh := tailH_pos p
  rw [one_sub_div (by linarith), add_sub_cancel_left]
  exact div_le_self hh.le (by linarith)

theorem tailVarpi_ne_one : tailVarpi p ≠ 1 := by
  intro h
  have h' := one_sub_tailVarpi_le p
  unfold tailVarpi at h
  have hh := tailH_pos p
  rw [div_eq_one_iff_eq (by linarith)] at h
  linarith

omit [Fact p.Prime] in
theorem upCoeff_rootIdx (r : ℝ) : upCoeff tailWeights r rootIdx = 1 := by
  simp [rootIdx, upCoeff, PType.deg, tailWeights.w_LL]

omit [Fact p.Prime] in
theorem sum_erase_rootIdx :
    ∑ i ∈ univ.erase rootIdx, upCoeff tailWeights (tailR p) i = tailH p := by
  have h := Finset.add_sum_erase univ (upCoeff tailWeights (tailR p)) (mem_univ rootIdx)
  rw [sum_upCoeff, upCoeff_rootIdx] at h
  unfold tailH
  linarith

/-- The weight `ρ̃_p(z) = ∑_{i ≠ root} c_i Π_i(z)` of the nonroot records. -/
noncomputable def tailRestWeight (hne : TailNonempty p) (z : Slot → ZMod p) : ℝ :=
  ∑ i ∈ univ.erase rootIdx,
    upCoeff tailWeights (tailR p) i * (upComponent (tailFieldLaws p hne) i).weight z

theorem tailRestWeight_nonneg (hne : TailNonempty p) (z : Slot → ZMod p) :
    0 ≤ tailRestWeight p hne z :=
  sum_nonneg fun i _ =>
    mul_nonneg (upCoeff_nonneg _ (tailR_nonneg p) i) ((upComponent _ i).nonneg z)

theorem sum_tailRestWeight (hne : TailNonempty p) : ∑ z, tailRestWeight p hne z = tailH p := by
  unfold tailRestWeight
  rw [Finset.sum_comm, ← sum_erase_rootIdx p]
  refine sum_congr rfl fun i _ => ?_
  rw [← Finset.mul_sum, (upComponent _ i).total, mul_one]

/-- **The remainder law** `ρ_p = ρ̃_p / h_p` (`lem:record:tail-mixing`, proof: "the tail laws as
mixtures"). -/
noncomputable def tailRest (hne : TailNonempty p) : FiniteLaw (Slot → ZMod p) where
  weight z := tailRestWeight p hne z / tailH p
  nonneg z := div_nonneg (tailRestWeight_nonneg p hne z) (tailH_pos p).le
  total := by rw [← sum_div, sum_tailRestWeight, div_self (tailH_pos p).ne']

theorem tailLaw_weight (hne : TailNonempty p) (z : Slot → ZMod p) :
    (tailLaw p hne).weight z = (∑ i, upCoeff tailWeights (tailR p) i *
      (upComponent (tailFieldLaws p hne) i).weight z) / upPoly tailWeights (tailR p) := by
  change (∑ i, (upCoeff tailWeights (tailR p) i / ∑ j, upCoeff tailWeights (tailR p) j) *
    (upComponent (tailFieldLaws p hne) i).weight z) = _
  rw [sum_upCoeff, sum_div]
  exact sum_congr rfl fun i _ => by ring

/-- **The tail law as a two-component mixture** (`lem:record:tail-mixing`, from
`lem:tail-law`(iii)): `μ_p = ϖ λ_p(G_root) + (1 - ϖ) ρ_p` with `ϖ = 1/(1 + h_p)`, where the root
component `π_{LL,2}` is the graph law of the root graph on the slots. -/
theorem tailLaw_mixture (hne : TailNonempty p) (z : Slot → ZMod p) :
    (tailLaw p hne).weight z =
      tailVarpi p * (graphLaw slotRootGraph (slotRoot_nonempty p hne)).weight z +
        (1 - tailVarpi p) * (tailRest p hne).weight z := by
  rw [tailLaw_weight, ← Finset.add_sum_erase univ _ (mem_univ rootIdx), upCoeff_rootIdx,
    one_mul, ← tailRootComponent_weight p hne z]
  change ((tailRootComponent p hne).weight z + tailRestWeight p hne z) / _ = _
  have hP : upPoly tailWeights (tailR p) = 1 + tailH p := by unfold tailH; ring
  have hh := tailH_pos p
  change _ = tailVarpi p * _ + (1 - tailVarpi p) * (tailRestWeight p hne z / tailH p)
  rw [hP]
  unfold tailVarpi
  field_simp
  ring

theorem tailComponent_uniform (hne : TailNonempty p) (i : UpIdx) :
    HasUniformMarginals (upComponent (tailFieldLaws p hne) i) := by
  rcases i with ⟨b, t, φ⟩
  cases b
  · exact emit_uniform _ _ (graphLaw_vertex_uniform (fieldGraph _ _ (Fin 1)) (hne.one _ _))
  · exact emit_uniform _ _ (graphLaw_vertex_uniform (fieldGraph _ _ (Fin 2)) (hne.two _ _))

/-- **`ρ_p` has uniform one-slot marginals** (`μ_p` and the root have them,
`lem:tail-law`(ii)). -/
theorem tailRest_uniform (hne : TailNonempty p) : HasUniformMarginals (tailRest p hne) :=
  uniform_of_mix (tailVarpi_ne_one p) (tailLaw_mixture p hne) (tailLaw_uniform p hne)
    (fun v g => graphLaw_vertex_uniform slotRootGraph (slotRoot_nonempty p hne) v g)

end Mixture

/-! ## The constant `S₇₂(p)` (`eq:tail-coefficients`, `lem:record:tail-mixing`(c)) -/

section S72

theorem tailC_two_nonneg : (0 : ℚ) ≤ tailC 2 := by
  unfold tailC tailRho
  decide +kernel

theorem tailC_three_nonneg : (0 : ℚ) ≤ tailC 3 := by
  unfold tailC tailRho
  decide +kernel

/-- **`h_p ≤ C₁ p^{-1/2} ≤ S₇₂(p) - 2⁹²/p`** for a prime `p ≥ P₄` (`lem:tail-law`(iii) and
`eq:tail-coefficients`). -/
theorem tailH_le_S72 (p : ℕ) [Fact p.Prime] (hp : P4 ≤ p) :
    tailH p ≤ (tailC 1 : ℝ) / Real.sqrt p ∧ 2 ^ 92 / (p : ℝ) + tailH p ≤ S72 p := by
  have h1 : tailH p ≤ (tailC 1 : ℝ) / Real.sqrt p := by
    have h := (tail_nonroot_mass p hp).2
    calc tailH p = upPoly tailWeights (tailR p) - 1 := rfl
      _ ≤ (tailC 1 : ℝ) * tailR p := h
      _ = (tailC 1 : ℝ) / Real.sqrt p := by rw [tailR_eq]; ring
  refine ⟨h1, ?_⟩
  have hp0 : (0 : ℝ) < p := Nat.cast_pos.mpr (Fact.out : p.Prime).pos
  have h2 : (0 : ℝ) ≤ (tailC 2 : ℝ) / p := div_nonneg (by exact_mod_cast tailC_two_nonneg) hp0.le
  have h3 : (0 : ℝ) ≤ (tailC 3 : ℝ) / (p * Real.sqrt p) :=
    div_nonneg (by exact_mod_cast tailC_three_nonneg) (by positivity)
  unfold S72
  linarith

/-- `(2^{65536})^{1/512} = 2^{128}`. -/
theorem two_pow_65536_rpow : ((2 : ℝ) ^ 65536) ^ (1 / 512 : ℝ) = 2 ^ 128 := by
  have h : (2 : ℝ) ^ 65536 = ((2 : ℝ) ^ 128) ^ 512 := by rw [← pow_mul]
  rw [h, show (1 / 512 : ℝ) = ((512 : ℕ) : ℝ)⁻¹ by norm_num]
  exact Real.pow_rpow_inv_natCast (by positivity) (by norm_num)

/-- **`lem:record:tail-mixing`(c)**: `S₇₂(p) < p^{-2γ}`, `2γ = 255/512`, for every real
`p ≥ P₅ = 2^{65536}`. The paper proves that `p^{2γ} S₇₂(p)` decreases and checks the value at `P₅`
with (S7); here the bound is proved directly at every `p ≥ P₅` from the bounds on `C₁, C₂, C₃`
(`tailC_bounds`): with `t = p^{-1/512} ≤ 2^{-128}`,
`S₇₂(p) = t^{255} (2⁹² t^{257} + C₁ t + C₂ t^{257} + C₃ t^{513})
≤ t^{255} (2⁹² + C₁ + C₂ + C₃) t`. -/
theorem S72_lt_rpow {p : ℝ} (hp : (2 : ℝ) ^ 65536 ≤ p) :
    S72 p < p ^ (-(255 / 512 : ℝ)) := by
  have hp0 : 0 < p := lt_of_lt_of_le (by positivity) hp
  set t : ℝ := p ^ (-(1 / 512 : ℝ)) with ht
  have ht0 : 0 < t := Real.rpow_pos_of_pos hp0 _
  have htpow (n : ℕ) : t ^ n = p ^ (-((n : ℝ) / 512)) := by
    rw [ht, ← Real.rpow_natCast, ← Real.rpow_mul hp0.le]
    congr 1
    ring
  -- `t ≤ 2^{-128}`
  have hy : (2 : ℝ) ^ 128 ≤ p ^ (1 / 512 : ℝ) := by
    rw [← two_pow_65536_rpow]
    exact Real.rpow_le_rpow (by positivity) hp (by norm_num)
  have ht1 : t ≤ (2 ^ 128 : ℝ)⁻¹ := by
    have h : t = (p ^ (1 / 512 : ℝ))⁻¹ := by
      rw [ht, ← Real.rpow_neg hp0.le]
    rw [h]
    exact inv_anti₀ (by positivity) hy
  have ht1' : t ≤ 1 := ht1.trans (by norm_num)
  -- the terms of `S₇₂` as powers of `t`
  have hinv : (1 : ℝ) / p = t ^ 512 := by
    rw [htpow]
    norm_num
    rw [Real.rpow_neg_one]
  have hsq : (1 : ℝ) / Real.sqrt p = t ^ 256 := by
    rw [htpow, Real.sqrt_eq_rpow, one_div, ← Real.rpow_neg hp0.le]
    norm_num
  have hγ : p ^ (-(255 / 512 : ℝ)) = t ^ 255 := by
    rw [htpow]
    norm_num
  have hS : S72 p = t ^ 255 * ((2 : ℝ) ^ 92 * t ^ 257 + (tailC 1 : ℝ) * t +
      (tailC 2 : ℝ) * t ^ 257 + (tailC 3 : ℝ) * t ^ 513) := by
    unfold S72
    have e1 : (2 : ℝ) ^ 92 / p = 2 ^ 92 * (1 / p) := by ring
    have e2 : (tailC 1 : ℝ) / Real.sqrt p = (tailC 1 : ℝ) * (1 / Real.sqrt p) := by ring
    have e3 : (tailC 2 : ℝ) / p = (tailC 2 : ℝ) * (1 / p) := by ring
    have e4 : (tailC 3 : ℝ) / (p * Real.sqrt p) =
        (tailC 3 : ℝ) * ((1 / p) * (1 / Real.sqrt p)) := by
      field_simp
    rw [e1, e2, e3, e4, hinv, hsq]
    ring
  rw [hS, hγ]
  have hC := tailC_bounds
  have hC1 : (tailC 1 : ℝ) ≤ 1198 := by
    have : tailC 1 ≤ 1198 := le_of_lt (lt_of_lt_of_le hC.1 (by norm_num))
    exact_mod_cast this
  have hC2 : (tailC 2 : ℝ) ≤ 609306 := by
    have : tailC 2 ≤ 609306 := le_of_lt (lt_of_lt_of_le hC.2.1 (by norm_num))
    exact_mod_cast this
  have hC3 : (tailC 3 : ℝ) ≤ 141760000 := by
    have : tailC 3 ≤ 141760000 := le_of_lt hC.2.2
    exact_mod_cast this
  have hC10 : (0 : ℝ) ≤ (tailC 1 : ℝ) := by
    have : (0 : ℚ) ≤ tailC 1 := by unfold tailC tailRho; decide +kernel
    exact_mod_cast this
  have hC20 : (0 : ℝ) ≤ (tailC 2 : ℝ) := by exact_mod_cast tailC_two_nonneg
  have hC30 : (0 : ℝ) ≤ (tailC 3 : ℝ) := by exact_mod_cast tailC_three_nonneg
  have h257 : t ^ 257 ≤ t := pow_le_of_le_one ht0.le ht1' (by norm_num)
  have h513 : t ^ 513 ≤ t := pow_le_of_le_one ht0.le ht1' (by norm_num)
  have hinner : (2 : ℝ) ^ 92 * t ^ 257 + (tailC 1 : ℝ) * t + (tailC 2 : ℝ) * t ^ 257 +
      (tailC 3 : ℝ) * t ^ 513 < 1 := by
    have hsum : (2 : ℝ) ^ 92 * t ^ 257 + (tailC 1 : ℝ) * t + (tailC 2 : ℝ) * t ^ 257 +
        (tailC 3 : ℝ) * t ^ 513 ≤ ((2 : ℝ) ^ 92 + 1198 + 609306 + 141760000) * t := by
      have a1 : (2 : ℝ) ^ 92 * t ^ 257 ≤ 2 ^ 92 * t :=
        mul_le_mul_of_nonneg_left h257 (by positivity)
      have a2 : (tailC 1 : ℝ) * t ≤ 1198 * t := mul_le_mul_of_nonneg_right hC1 ht0.le
      have a3 : (tailC 2 : ℝ) * t ^ 257 ≤ 609306 * t :=
        (mul_le_mul_of_nonneg_left h257 hC20).trans (mul_le_mul_of_nonneg_right hC2 ht0.le)
      have a4 : (tailC 3 : ℝ) * t ^ 513 ≤ 141760000 * t :=
        (mul_le_mul_of_nonneg_left h513 hC30).trans (mul_le_mul_of_nonneg_right hC3 ht0.le)
      linarith
    refine lt_of_le_of_lt hsum ?_
    calc ((2 : ℝ) ^ 92 + 1198 + 609306 + 141760000) * t
        ≤ ((2 : ℝ) ^ 92 + 1198 + 609306 + 141760000) * (2 ^ 128 : ℝ)⁻¹ :=
          mul_le_mul_of_nonneg_left ht1 (by positivity)
      _ < 1 := by norm_num
  calc t ^ 255 * _ < t ^ 255 * 1 := mul_lt_mul_of_pos_left hinner (by positivity)
    _ = t ^ 255 := mul_one _

theorem S72_le_rpow {p : ℝ} (hp : (2 : ℝ) ^ 65536 ≤ p) : S72 p ≤ p ^ (-(255 / 512 : ℝ)) :=
  (S72_lt_rpow hp).le

/-- `p^{2γ} S₇₂(p) = 2⁹² p^{2γ-1} + C₁ p^{2γ-1/2} + C₂ p^{2γ-1} + C₃ p^{2γ-3/2}`, `2γ = 255/512`. -/
theorem scaled_S72_eq {p : ℝ} (hp : 0 < p) :
    p ^ (255 / 512 : ℝ) * S72 p = 2 ^ 92 * p ^ (-(257 / 512 : ℝ)) +
      (tailC 1 : ℝ) * p ^ (-(1 / 512 : ℝ)) + (tailC 2 : ℝ) * p ^ (-(257 / 512 : ℝ)) +
      (tailC 3 : ℝ) * p ^ (-(513 / 512 : ℝ)) := by
  have e1 : p ^ (-(257 / 512 : ℝ)) = p ^ (255 / 512 : ℝ) / p := by
    rw [show (-(257 / 512 : ℝ)) = 255 / 512 - 1 by norm_num, Real.rpow_sub_one hp.ne']
  have e2 : p ^ (-(1 / 512 : ℝ)) = p ^ (255 / 512 : ℝ) / Real.sqrt p := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_sub hp]
    norm_num
  have e3 : p ^ (-(513 / 512 : ℝ)) = p ^ (255 / 512 : ℝ) / (p * Real.sqrt p) := by
    have h32 : p * Real.sqrt p = p ^ (3 / 2 : ℝ) := by
      rw [Real.sqrt_eq_rpow, show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hp,
        Real.rpow_one]
    rw [h32, ← Real.rpow_sub hp]
    norm_num
  rw [e1, e2, e3]
  unfold S72
  ring

/-- **`lem:record:tail-mixing`(c), monotonicity**: `p^{2γ} S₇₂(p)` is strictly decreasing on
`p > 0` (nonnegative coefficients and negative exponents, since `2γ = 255/512 < 1/2`). -/
theorem scaled_S72_strictAntiOn :
    StrictAntiOn (fun p : ℝ => p ^ (255 / 512 : ℝ) * S72 p) (Set.Ioi 0) := by
  intro x hx y hy hxy
  simp only [Set.mem_Ioi] at hx hy
  show y ^ (255 / 512 : ℝ) * S72 y < x ^ (255 / 512 : ℝ) * S72 x
  rw [scaled_S72_eq hx, scaled_S72_eq hy]
  have h1 := Real.rpow_lt_rpow_of_neg hx hxy (by norm_num : (-(257 / 512 : ℝ)) < 0)
  have h2 := Real.rpow_le_rpow_of_nonpos hx hxy.le (by norm_num : (-(1 / 512 : ℝ)) ≤ 0)
  have h3 := Real.rpow_le_rpow_of_nonpos hx hxy.le (by norm_num : (-(513 / 512 : ℝ)) ≤ 0)
  have hC1 : (0 : ℝ) ≤ (tailC 1 : ℝ) := by
    have : (0 : ℚ) ≤ tailC 1 := by unfold tailC tailRho; decide +kernel
    exact_mod_cast this
  have hC2 : (0 : ℝ) ≤ (tailC 2 : ℝ) := by exact_mod_cast tailC_two_nonneg
  have hC3 : (0 : ℝ) ≤ (tailC 3 : ℝ) := by exact_mod_cast tailC_three_nonneg
  have a1 : (2 : ℝ) ^ 92 * y ^ (-(257 / 512 : ℝ)) < 2 ^ 92 * x ^ (-(257 / 512 : ℝ)) :=
    mul_lt_mul_of_pos_left h1 (by positivity)
  have a2 := mul_le_mul_of_nonneg_left h2 hC1
  have a3 := mul_le_mul_of_nonneg_left h1.le hC2
  have a4 := mul_le_mul_of_nonneg_left h3 hC3
  linarith

end S72

/-! ## (R4) for the tail laws -/

section Headline

variable (p : ℕ) [Fact p.Prime]

omit [Fact p.Prime] in
theorem two_pow_512_le_of_P4 (hp : P4 ≤ p) : (2 : ℝ) ^ 512 ≤ p := by
  unfold P4 at hp
  have h : ((2 ^ 512 : ℕ) : ℝ) ≤ (p : ℝ) := Nat.cast_le.mpr hp
  rwa [Nat.cast_pow, Nat.cast_ofNat] at h

omit [Fact p.Prime] in
theorem two_pow_65536_le_of_P5 (hp : P5 ≤ p) : (2 : ℝ) ^ 65536 ≤ p := by
  unfold P5 at hp
  have h : ((2 ^ 65536 : ℕ) : ℝ) ≤ (p : ℝ) := Nat.cast_le.mpr hp
  rwa [Nat.cast_pow, Nat.cast_ofNat] at h

omit [Fact p.Prime] in
theorem P4_le_of_P5 (hp : P5 ≤ p) : P4 ≤ p := by
  have h : (2 : ℝ) ^ 512 ≤ p :=
    (pow_le_pow_right₀ (by norm_num) (by norm_num)).trans (two_pow_65536_le_of_P5 p hp)
  have h' : ((2 ^ 512 : ℕ) : ℝ) ≤ (p : ℝ) := by rwa [Nat.cast_pow, Nat.cast_ofNat]
  unfold P4
  exact Nat.cast_le.mp h'

omit [Fact p.Prime] in
theorem ne_two_of_P4 (hp : P4 ≤ p) : p ≠ 2 := by
  have h2512 : (2 : ℝ) < 2 ^ 512 := lt_self_pow₀ (by norm_num) (by norm_num)
  have hp2R : (2 : ℝ) < p := lt_of_lt_of_le h2512 (two_pow_512_le_of_P4 p hp)
  intro h
  rw [h] at hp2R
  push_cast at hp2R
  exact lt_irrefl _ hp2R

/-- **`lem:record:tail-mixing`(a) for the tail law**: assuming Weil's bound (H1), at a prime
`p ≥ P₄` the conditional operator of `μ_p` from any slot `v` to the other `71` slots has squared
norm at most `S₇₂(p)` on the mean-zero functions. The proof is the paper's: `μ_p` is the mixture
`ϖ λ_p(G_root) + (1 - ϖ) ρ_p` (`tailLaw_mixture`), the root has squared norm at most `2²²/p`
(`lem:trace-mixing`(d), the root graph has `72` vertices and degrees `≤ 20`), `ρ_p` is a
contraction with the same (uniform) slot marginal, and `lem:mixture` gives
`ϖ 2²²/p + (1 - ϖ) ≤ 2⁹²/p + h_p ≤ S₇₂(p)`. -/
theorem tailLaw_slot_S72 (hWeil : Target.Weil) (hp : P4 ≤ p) (hne : TailNonempty p) (v : Slot)
    (f : ZMod p → ℝ) (hf : ∑ x, srcWeight (slotJoint (tailLaw p hne) v) x * f x = 0) :
    ∑ b, tgtWeight (slotJoint (tailLaw p hne) v) b *
        condOp (slotJoint (tailLaw p hne) v) f b ^ 2 ≤
      S72 p * ∑ x, srcWeight (slotJoint (tailLaw p hne) v) x * f x ^ 2 := by
  have hp2 := ne_two_of_P4 p hp
  have hW := weilBound_of_target hWeil p hp2
  obtain ⟨hslot, -⟩ := TraceMixing.tail_mixing_S hW hp2 slotRootGraph (slotRoot_nonempty p hne)
    card_slot slotRootGraph_degree (two_pow_512_le_of_P4 p hp) (tailVarpi_pos p).le
    (tailVarpi_le_one p) (one_sub_tailVarpi_le p) (tailH_le_S72 p hp).2 (tailLaw_mixture p hne)
  exact hslot v (fun x => srcWeight_slotJoint (tailRest_uniform p hne v) x) f hf

/-- **(R4) for the tail law** (`lem:record:tail-mixing`(c), with (a)): assuming Weil's bound
(H1), at every prime `p ≥ P₅ = 2^{65536}` the tail law `μ_p` is `(γ, v)`-mixing at every slot
`v`, `γ = 255/1024` (`def:mixing`). -/
theorem tailLaw_R4 (hWeil : Target.Weil) (hp : P5 ≤ p) (hne : TailNonempty p) (v : Slot) :
    IsGammaMixing p (255 / 1024) (tailLaw p hne) {v} := by
  have hP4 : P4 ≤ p := P4_le_of_P5 p hp
  exact (TraceMixing.tail_R4 hWeil (two_pow_512_le_of_P4 p hP4) slotRootGraph
    (slotRoot_nonempty p hne) card_slot slotRootGraph_degree (tailVarpi_pos p).le
    (tailVarpi_le_one p) (one_sub_tailVarpi_le p) (tailH_le_S72 p hP4).2
    (S72_le_rpow (two_pow_65536_le_of_P5 p hp)) (tailLaw_mixture p hne)
    (fun w x => srcWeight_slotJoint (tailRest_uniform p hne w) x)).1 v

end Headline

/-- **The field `mixing` of `TheoremC.Reference` for the tail family** (`(R4)` for `μ`, at the
paper's threshold `P₅ = 2^{65536}`): assuming Weil's bound (H1), for every prime `q ≥ P₅` and
every slot `v`, `tailLawFamily q` is `(γ, v)`-mixing with `γ = 255/1024`
(`Sarkozy.AnalyticStage.γ`). At a prime with nonempty labelling sets this is `tailLaw_R4`; at a
prime where some labelling set is empty (none, for large primes: `tailNonempty_of_large`) the
family is the uniform law, whose conditional operators vanish on the mean-zero functions. -/
theorem tailLawFamily_mixing (hWeil : Target.Weil) :
    ∀ (q : ℕ) [NeZero q], q.Prime → P5 ≤ q → ∀ v : Slot,
      IsGammaMixing q AnalyticStage.γ (tailLawFamily q) {v} := by
  intro q _ hq hle v
  have : Fact q.Prime := ⟨hq⟩
  rw [show AnalyticStage.γ = 255 / 1024 from rfl]
  by_cases h' : TailNonempty q
  · rw [tailLawFamily_eq q h']
    exact tailLaw_R4 q hWeil hle h' v
  · have hu : tailLawFamily q = FiniteLaw.uniform (Slot → ZMod q) := by
      unfold tailLawFamily
      rw [dite_eq_left hq, dite_eq_right h']
    rw [hu]
    exact isMixing_uniform v _

/-! ## The normalized accepted part of the comparison law -/

section Accepted

variable (p : ℕ) [Fact p.Prime]

/-- The uniform law on the strict-square pairs `Ω`, in the `srcWeight` form of
`Sarkozy.TraceMixing`: mass `2/(p(p-1))` on each pair `(x, x')` with `χ(x' - x) = 1`. -/
noncomputable def omegaWeight (x x' : ZMod p) : ℝ :=
  if quadraticChar (ZMod p) (x' - x) = 1 then 2 / ((p : ℝ) * ((p : ℝ) - 1)) else 0

/-- **What `lem:record:tail-mixing` uses of the normalized accepted part `ν̄_p`** of the comparison
law at a tail prime. The tail comparison law (`lem:tail-prices`, `def:upper-comparison`) is not
defined in Lean; these are the facts the proof of the lemma reads from it:
* `decomp`: `P_μ(r) ν_p = π_{LL,2} + ρ_p` with `ρ_p ≥ 0` (`ρt`) of mass `0 < h'_p ≤ h_p`
  (the comparison law keeps the root and the accepting records of degree one, and replaces or
  deletes the others), so that `ν̄_p = (π_{LL,2} + ρ_p)/(1 + h'_p)`;
* `uniform`, `pair` (`lem:tail-prices`(i)): `ν̄_p` has uniform one-slot marginals, and at each
  query `(u_e, v_e)` of `𝓔₆` its pair marginal is `Unif(Ω)`.
Field review against the proof of `lem:record:tail-mixing`: these are exactly the sentences "so
`P_μ(r)ν_p = π_{LL,2} + ρ_p` with `ρ_p ≥ 0` of mass `0 < h'_p ≤ h_p`", "one-slot marginals are
uniform (`lem:tail-prices`(i))" and "the queried pair of `ν̄_p` is uniform on `Ω`
(`lem:tail-prices`(i))". Non-vacuity: `rootAcceptedTailData` (the root itself, with
`ρ_p = h_p π_{LL,2}`). -/
structure AcceptedTailData (hne : TailNonempty p) (ν : FiniteLaw (Slot → ZMod p)) where
  /-- The nonroot mass `h'_p` of `P_μ(r) ν_p`. -/
  h' : ℝ
  /-- The nonroot part `ρ_p` of `P_μ(r) ν_p`. -/
  ρt : (Slot → ZMod p) → ℝ
  ρt_nonneg : ∀ z, 0 ≤ ρt z
  ρt_mass : ∑ z, ρt z = h'
  h'_pos : 0 < h'
  h'_le : h' ≤ tailH p
  decomp : ∀ z, ν.weight z = ((tailRootComponent p hne).weight z + ρt z) / (1 + h')
  uniform : HasUniformMarginals ν
  pair : ∀ (j : Chamber) (x x' : ZMod p),
    srcWeight (TraceMixing.pairJoint ν (querySource j) (queryTarget j)) (x, x') =
      omegaWeight p x x'

namespace AcceptedTailData

variable {p} {hne : TailNonempty p} {ν : FiniteLaw (Slot → ZMod p)}
  (D : AcceptedTailData p hne ν)

/-- The mixture weight `ϖ' = 1/(1 + h'_p)` of the root in `ν̄_p`. -/
noncomputable def varpi : ℝ := 1 / (1 + D.h')

theorem varpi_nonneg : 0 ≤ D.varpi := by
  unfold varpi
  have := D.h'_pos
  positivity

theorem varpi_le_one : D.varpi ≤ 1 := by
  unfold varpi
  have := D.h'_pos
  rw [div_le_one (by linarith)]
  linarith

theorem varpi_ne_one : D.varpi ≠ 1 := by
  unfold varpi
  have := D.h'_pos
  intro h
  rw [div_eq_one_iff_eq (by linarith)] at h
  linarith

/-- `1 - ϖ' = h'_p/(1 + h'_p) ≤ h'_p ≤ h_p`. -/
theorem one_sub_varpi_le : 1 - D.varpi ≤ tailH p := by
  unfold varpi
  have := D.h'_pos
  rw [one_sub_div (by linarith), add_sub_cancel_left]
  exact (div_le_self D.h'_pos.le (by linarith)).trans D.h'_le

/-- The normalized nonroot part `ρ_p/h'_p`. -/
noncomputable def rest : FiniteLaw (Slot → ZMod p) where
  weight z := D.ρt z / D.h'
  nonneg z := div_nonneg (D.ρt_nonneg z) D.h'_pos.le
  total := by rw [← sum_div, D.ρt_mass, div_self D.h'_pos.ne']

/-- **`ν̄_p = ϖ' λ_p(G_root) + (1 - ϖ') ρ_p/h'_p`.** -/
theorem mix (z : Slot → ZMod p) :
    ν.weight z = D.varpi * (graphLaw slotRootGraph (slotRoot_nonempty p hne)).weight z +
      (1 - D.varpi) * D.rest.weight z := by
  have := D.h'_pos
  rw [D.decomp z, ← tailRootComponent_weight p hne z]
  change _ = D.varpi * _ + (1 - D.varpi) * (D.ρt z / D.h')
  unfold varpi
  field_simp
  ring

/-- `ρ_p/h'_p` has uniform one-slot marginals. -/
theorem rest_uniform : HasUniformMarginals D.rest :=
  uniform_of_mix D.varpi_ne_one D.mix D.uniform
    (fun v g => graphLaw_vertex_uniform slotRootGraph (slotRoot_nonempty p hne) v g)

/-- **The queried pair of `ρ_p/h'_p` is uniform on `Ω`**: so are those of `ν̄_p` and of the root
(the root graph contains the query edge). -/
theorem rest_pair (hp2 : p ≠ 2) (j : Chamber) (x x' : ZMod p) :
    srcWeight (TraceMixing.pairJoint D.rest (querySource j) (queryTarget j)) (x, x') =
      omegaWeight p x x' := by
  have huv := query_mem_slotRootGraph j
  have huv' : querySource j ≠ queryTarget j := fun h => slotRootGraph.loopless _ (h ▸ huv)
  have h1 := TraceMixing.srcWeight_pairJoint slotRootGraph (slotRoot_nonempty p hne) hp2 huv x x'
  have h2 := D.pair j x x'
  have hsplit : srcWeight (TraceMixing.pairJoint ν (querySource j) (queryTarget j)) (x, x') =
      D.varpi * srcWeight (TraceMixing.pairJoint (graphLaw slotRootGraph (slotRoot_nonempty p hne))
        (querySource j) (queryTarget j)) (x, x') +
      (1 - D.varpi) * srcWeight (TraceMixing.pairJoint D.rest (querySource j) (queryTarget j))
        (x, x') := by
    unfold srcWeight
    simp only [TraceMixing.pairJoint_mix D.mix huv', Finset.sum_add_distrib, ← Finset.mul_sum]
  unfold omegaWeight at h2 ⊢
  rw [h1, h2] at hsplit
  have hne1 : (1 - D.varpi) ≠ 0 := sub_ne_zero.mpr (Ne.symm D.varpi_ne_one)
  apply mul_left_cancel₀ hne1
  linarith

end AcceptedTailData

/-- **`lem:record:tail-mixing`(a), (b) for `ν̄_p`**: assuming Weil's bound (H1), at a prime
`p ≥ P₄`, the conditional operators of `ν̄_p` from every slot `v`, and from every query pair
`(u_e, v_e)` of `𝓔₆`, have squared norm at most `S₇₂(p)` on the mean-zero functions (the pair
marginal is `Unif(Ω)` by hypothesis, `lem:tail-prices`(i)). -/
theorem tailAccepted_S72 (hWeil : Target.Weil) (hp : P4 ≤ p) {hne : TailNonempty p}
    {ν : FiniteLaw (Slot → ZMod p)} (D : AcceptedTailData p hne ν) :
    (∀ (v : Slot) (f : ZMod p → ℝ), ∑ x, srcWeight (slotJoint ν v) x * f x = 0 →
      ∑ b, tgtWeight (slotJoint ν v) b * condOp (slotJoint ν v) f b ^ 2 ≤
        S72 p * ∑ x, srcWeight (slotJoint ν v) x * f x ^ 2) ∧
    (∀ (j : Chamber) (f : ZMod p × ZMod p → ℝ),
      ∑ ω, srcWeight (TraceMixing.pairJoint ν (querySource j) (queryTarget j)) ω * f ω = 0 →
      ∑ r, tgtWeight (TraceMixing.pairJoint ν (querySource j) (queryTarget j)) r *
          condOp (TraceMixing.pairJoint ν (querySource j) (queryTarget j)) f r ^ 2 ≤
        S72 p * ∑ ω, srcWeight (TraceMixing.pairJoint ν (querySource j) (queryTarget j)) ω *
          f ω ^ 2) := by
  have hp2 := ne_two_of_P4 p hp
  have hW := weilBound_of_target hWeil p hp2
  obtain ⟨hslot, hpair⟩ := TraceMixing.tail_mixing_S hW hp2 slotRootGraph
    (slotRoot_nonempty p hne) card_slot slotRootGraph_degree (two_pow_512_le_of_P4 p hp)
    D.varpi_nonneg D.varpi_le_one D.one_sub_varpi_le (tailH_le_S72 p hp).2 D.mix
  exact ⟨fun v f hf => hslot v (fun x => srcWeight_slotJoint (D.rest_uniform v) x) f hf,
    fun j f hf => hpair _ _ (query_mem_slotRootGraph j) (D.rest_pair hp2 j) f hf⟩

/-- **(R4) for `ν̄_p`** (`lem:record:tail-mixing`(c) with (a), (b)): assuming Weil's bound (H1),
for `p ≥ P₅ = 2^{65536}` the normalized accepted part `ν̄_p` is `(γ, v)`-mixing at every slot and
`(γ, (u_e, v_e))`-mixing at every query of `𝓔₆`, `γ = 255/1024`. -/
theorem tailAccepted_R4 (hWeil : Target.Weil) (hp : P5 ≤ p) {hne : TailNonempty p}
    {ν : FiniteLaw (Slot → ZMod p)} (D : AcceptedTailData p hne ν) :
    (∀ v, IsGammaMixing p (255 / 1024) ν {v}) ∧
      ∀ j : Chamber, IsGammaMixing p (255 / 1024) ν {querySource j, queryTarget j} := by
  have hP4 : P4 ≤ p := P4_le_of_P5 p hp
  have hp2 := ne_two_of_P4 p hP4
  obtain ⟨hslot, hpair⟩ := TraceMixing.tail_R4 hWeil (two_pow_512_le_of_P4 p hP4) slotRootGraph
    (slotRoot_nonempty p hne) card_slot slotRootGraph_degree D.varpi_nonneg D.varpi_le_one
    D.one_sub_varpi_le (tailH_le_S72 p hP4).2 (S72_le_rpow (two_pow_65536_le_of_P5 p hp)) D.mix
    (fun w x => srcWeight_slotJoint (D.rest_uniform w) x)
  exact ⟨hslot, fun j => (hpair _ _ (query_mem_slotRootGraph j) (D.rest_pair hp2 j)).2⟩

/-- **Non-vacuity of `AcceptedTailData`**: the root law `π_{LL,2} = λ_p(G_root)` itself, written as
`(π_{LL,2} + h_p π_{LL,2})/(1 + h_p)`, satisfies all its fields at every prime `p ≥ P₄` with
nonempty labelling sets (every large prime under H1, `tailNonempty_of_large`). -/
noncomputable def rootAcceptedTailData (hp : P4 ≤ p) (hne : TailNonempty p) :
    AcceptedTailData p hne (graphLaw slotRootGraph (slotRoot_nonempty p hne)) where
  h' := tailH p
  ρt z := tailH p * (tailRootComponent p hne).weight z
  ρt_nonneg z := mul_nonneg (tailH_pos p).le ((tailRootComponent p hne).nonneg z)
  ρt_mass := by rw [← Finset.mul_sum, (tailRootComponent p hne).total, mul_one]
  h'_pos := tailH_pos p
  h'_le := le_rfl
  decomp z := by
    have := tailH_pos p
    rw [← tailRootComponent_weight p hne z]
    field_simp
  uniform v g := graphLaw_vertex_uniform slotRootGraph (slotRoot_nonempty p hne) v g
  pair j x x' := TraceMixing.srcWeight_pairJoint slotRootGraph (slotRoot_nonempty p hne)
    (ne_two_of_P4 p hp) (query_mem_slotRootGraph j) x x'

end Accepted

end Sarkozy.PartVRecords
