module

public import Sarkozy.PositiveRoots.GraphMarginal
public import Sarkozy.PositiveRoots.ScoreKernel

@[expose] public section

/-!
# The uniform root as a conditioned product of its two components (`lem:root-normalization`(b))

`paper/sections/20b_positive_roots.tex`, proof of `lem:root-normalization`(b): "before global
injectivity the root is the product of the uniform laws of its two components, each a cyclic
`K_{2,2,2}` on the bases of one parity".

* `splitC`, `joinC`, `joinEquiv`: a labelling of `G_{L,2}` (V1/Labellings' `recordGraph (Fin 2)`)
  is a pair of labellings of the two components, the even bases `0 → 2 → 4` and the odd bases
  `1 → 5 → 3` (the rotation `rot`);
* `mem_rec_iff`: **`x ∈ Inj(G_{L,2})` iff both components are in `Inj(K_{2,2,2})` and `x` is
  injective** (the edges of `G_{L,2}` lie inside the components);
* **`gamma0_expect`**: `E_{Γ_{p,0}} f = E_μ[f 𝟙_G]/μ(G)` for the product `μ` of the two component
  laws and the event `G` of global injectivity;
* **`gamma0_score_bounds`**: hence, with the moments of `GraphMarginal` (`E_μH_j = qr`,
  `E_μH_j² ≥ 1 − 4q`), `Moments.root_normalization_b` gives the two bounds of
  `lem:root-normalization`(b) for the actual `Γ_{p,0} = λ_p(G_{L,2})`:
  `|E_{Γ_{p,0}}H_j| ≤ h₀` and `E_{Γ_{p,0}}H_j² ≥ 1 − 4q − 36q(2 + r)² − 2q/(1 − q)`; the only
  remaining hypotheses are the coincidence counts of the proof (`μ(Gᶜ) ≤ 36q`, the spike mass
  `≤ 2q²/(1 − q)`, `|H_j| ≤ 2 + r` off the spikes and `≤ 1/r` on them).
-/

namespace Sarkozy.PositiveRoots

open Finset Sarkozy Sarkozy.Labellings

/-- The even bases `0, 2, 4` in the rotation order. -/
def evenBase (i : Fin 3) : ZMod 6 := ![0, 2, 4] i

/-- The odd bases `1, 5, 3` in the rotation order. -/
def oddBase (i : Fin 3) : ZMod 6 := ![1, 5, 3] i

theorem rot_evenBase : ∀ i : Fin 3, rot (evenBase i) = evenBase (i + 1) := by decide

theorem rot_oddBase : ∀ i : Fin 3, rot (oddBase i) = oddBase (i + 1) := by decide

theorem evenBase_injective : Function.Injective evenBase := by decide

theorem oddBase_injective : Function.Injective oddBase := by decide

theorem evenBase_ne_oddBase : ∀ i j : Fin 3, evenBase i ≠ oddBase j := by decide

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The two components of a labelling of `G_{L,2}`. -/
def splitC (x : ZMod 6 × Fin 2 → F) : (Fin 3 × Fin 2 → F) × (Fin 3 × Fin 2 → F) :=
  (fun a => x (evenBase a.1, a.2), fun a => x (oddBase a.1, a.2))

/-- The base of `ZMod 6` as a component and an index. -/
def baseIdx (u : ZMod 6) : Bool × Fin 3 :=
  match u.val with
  | 0 => (true, 0)
  | 2 => (true, 1)
  | 4 => (true, 2)
  | 1 => (false, 0)
  | 5 => (false, 1)
  | _ => (false, 2)

/-- The joined labelling of two component labellings. -/
def joinC (ω : (Fin 3 × Fin 2 → F) × (Fin 3 × Fin 2 → F)) (v : ZMod 6 × Fin 2) : F :=
  if (baseIdx v.1).1 then ω.1 ((baseIdx v.1).2, v.2) else ω.2 ((baseIdx v.1).2, v.2)

theorem baseIdx_even : ∀ i : Fin 3, baseIdx (evenBase i) = (true, i) := by decide

theorem baseIdx_odd : ∀ i : Fin 3, baseIdx (oddBase i) = (false, i) := by decide

theorem base_of_idx : ∀ u : ZMod 6,
    (if (baseIdx u).1 then evenBase (baseIdx u).2 else oddBase (baseIdx u).2) = u := by decide

omit [Field F] [Fintype F] [DecidableEq F] in
theorem split_join (ω : (Fin 3 × Fin 2 → F) × (Fin 3 × Fin 2 → F)) : splitC (joinC ω) = ω := by
  ext a
  · simp [splitC, joinC, baseIdx_even]
  · simp [splitC, joinC, baseIdx_odd]

omit [Field F] [Fintype F] [DecidableEq F] in
theorem join_split (x : ZMod 6 × Fin 2 → F) : joinC (splitC x) = x := by
  funext v
  obtain ⟨u, ℓ⟩ := v
  have h := base_of_idx u
  unfold joinC splitC
  by_cases hb : (baseIdx u).1
  · simp only [hb, ↓reduceIte] at h ⊢
    rw [h]
  · simp only [hb, ↓reduceIte, Bool.false_eq_true] at h ⊢
    rw [h]

/-- The bijection between pairs of component labellings and labellings of `G_{L,2}`. -/
def joinEquiv : (Fin 3 × Fin 2 → F) × (Fin 3 × Fin 2 → F) ≃ (ZMod 6 × Fin 2 → F) where
  toFun := joinC
  invFun := splitC
  left_inv := split_join
  right_inv := join_split

/-- **The labellings of `G_{L,2}` are the injective joins of component labellings.** -/
theorem mem_rec_iff (x : ZMod 6 × Fin 2 → F) :
    x ∈ injLabellings F (recordGraph (Fin 2)) ↔
      (splitC x).1 ∈ injLabellings F compGraph ∧ (splitC x).2 ∈ injLabellings F compGraph ∧
        Function.Injective x := by
  simp only [mem_injLabellings_iff_feasible, Feasible, mem_univ, forall_const]
  constructor
  · rintro ⟨hinj, hedge⟩
    have hx : Function.Injective x := fun a b h => hinj a b h
    refine ⟨⟨fun a b h => ?_, fun e he => ?_⟩, ⟨fun a b h => ?_, fun e he => ?_⟩, hx⟩
    · have := hx h
      simp only [Prod.mk.injEq] at this
      exact Prod.ext (evenBase_injective this.1) this.2
    · have he' : e.2.1 = e.1.1 + 1 := by simpa [compGraph] using he
      have := hedge ((evenBase e.1.1, e.1.2), (evenBase e.2.1, e.2.2)) (by
        rw [mem_recordGraph]; simp only; rw [he', rot_evenBase])
      exact this
    · have := hx h
      simp only [Prod.mk.injEq] at this
      exact Prod.ext (oddBase_injective this.1) this.2
    · have he' : e.2.1 = e.1.1 + 1 := by simpa [compGraph] using he
      have := hedge ((oddBase e.1.1, e.1.2), (oddBase e.2.1, e.2.2)) (by
        rw [mem_recordGraph]; simp only; rw [he', rot_oddBase])
      exact this
  · rintro ⟨⟨-, h1⟩, ⟨-, h2⟩, hx⟩
    refine ⟨fun a b h => hx h, fun e he => ?_⟩
    rw [mem_recordGraph] at he
    obtain ⟨⟨u, ℓ⟩, ⟨u', ℓ'⟩⟩ := e
    simp only at he ⊢
    have hu := base_of_idx u
    by_cases hb : (baseIdx u).1
    · simp only [hb, ↓reduceIte] at hu
      have hu' : u' = evenBase ((baseIdx u).2 + 1) := by rw [he, ← rot_evenBase, hu]
      have := h1 (((baseIdx u).2, ℓ), ((baseIdx u).2 + 1, ℓ')) (by simp [compGraph])
      simp only [splitC] at this
      rw [← hu, hu']
      exact this
    · simp only [hb, ↓reduceIte, Bool.false_eq_true] at hu
      have hu' : u' = oddBase ((baseIdx u).2 + 1) := by rw [he, ← rot_oddBase, hu]
      have := h2 (((baseIdx u).2, ℓ), ((baseIdx u).2 + 1, ℓ')) (by simp [compGraph])
      simp only [splitC] at this
      rw [← hu, hu']
      exact this

/-! ## `Γ_{p,0}` as the conditioned product -/

section Law

/-- The global injectivity event on a pair of component labellings. -/
def GInj (ω : (Fin 3 × Fin 2 → F) × (Fin 3 × Fin 2 → F)) : Prop := Function.Injective (joinC ω)

instance : DecidablePred (GInj (F := F)) := fun ω => by
  unfold GInj; infer_instance

/-- The weight of the product law on the injectivity event. -/
theorem compProd_weight_G (hneC : (injLabellings F compGraph).Nonempty)
    (ω : (Fin 3 × Fin 2 → F) × (Fin 3 × Fin 2 → F)) :
    (if GInj ω then ((graphLaw compGraph hneC).product (graphLaw compGraph hneC)).weight ω
      else 0) =
      if joinC ω ∈ injLabellings F (recordGraph (Fin 2)) then
        (1 / ((injLabellings F compGraph).card : ℝ)) ^ 2 else 0 := by
  have hm := mem_rec_iff (joinC ω)
  rw [split_join] at hm
  simp only [FiniteLaw.product, graphLaw]
  by_cases hR : joinC ω ∈ injLabellings F (recordGraph (Fin 2))
  · obtain ⟨h1, h2, h3⟩ := hm.mp hR
    have hG : GInj ω := h3
    simp only [hG, h1, h2, hR, ↓reduceIte]
    ring
  · simp only [hR, ↓reduceIte]
    by_cases hG : GInj ω
    · simp only [hG, ↓reduceIte]
      have : ¬ (ω.1 ∈ injLabellings F compGraph ∧ ω.2 ∈ injLabellings F compGraph) :=
        fun h => hR (hm.mpr ⟨h.1, h.2, hG⟩)
      by_cases h1 : ω.1 ∈ injLabellings F compGraph
      · have h2 : ω.2 ∉ injLabellings F compGraph := fun h2 => this ⟨h1, h2⟩
        simp only [h2, ↓reduceIte, mul_zero]
      · simp only [h1, ↓reduceIte, zero_mul]
    · simp only [hG, ↓reduceIte]

/-- **`Γ_{p,0}` is the product of the two component laws conditioned on global injectivity**:
`E_{Γ_{p,0}} f = E_μ[f 𝟙_G]/μ(G)`, `μ` the product of the component laws. -/
theorem gamma0_expect (hneR : (injLabellings F (recordGraph (Fin 2))).Nonempty)
    (hneC : (injLabellings F compGraph).Nonempty) (f : (ZMod 6 × Fin 2 → F) → ℝ) :
    (graphLaw (recordGraph (Fin 2)) hneR).expect f =
      (∑ ω ∈ univ.filter GInj,
          ((graphLaw compGraph hneC).product (graphLaw compGraph hneC)).weight ω * f (joinC ω)) /
        (∑ ω ∈ univ.filter GInj,
          ((graphLaw compGraph hneC).product (graphLaw compGraph hneC)).weight ω) := by
  set c := (1 / ((injLabellings F compGraph).card : ℝ)) ^ 2 with hc
  have hc0 : 0 < c := by
    have : (0 : ℝ) < (injLabellings F compGraph).card := by exact_mod_cast hneC.card_pos
    positivity
  have hsum : ∀ g : ((Fin 3 × Fin 2 → F) × (Fin 3 × Fin 2 → F)) → ℝ,
      ∑ ω ∈ univ.filter GInj,
          ((graphLaw compGraph hneC).product (graphLaw compGraph hneC)).weight ω * g ω =
        c * ∑ x ∈ injLabellings F (recordGraph (Fin 2)), g (splitC x) := by
    intro g
    rw [Finset.sum_filter]
    have e1 : ∀ ω, (if GInj ω then
        ((graphLaw compGraph hneC).product (graphLaw compGraph hneC)).weight ω * g ω else 0) =
        (if joinC ω ∈ injLabellings F (recordGraph (Fin 2)) then c else 0) * g ω := by
      intro ω
      rw [← compProd_weight_G hneC ω]
      split_ifs <;> ring
    rw [Finset.sum_congr rfl fun ω _ => e1 ω]
    rw [← Equiv.sum_comp joinEquiv.symm]
    simp only [joinEquiv, Equiv.coe_fn_symm_mk, join_split]
    simp only [ite_mul, zero_mul]
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.mul_sum]
  have hnum := hsum (fun ω => f (joinC ω))
  have hden := hsum (fun _ => 1)
  simp only [join_split, mul_one, Finset.sum_const, nsmul_eq_mul] at hnum hden
  rw [hnum, hden]
  have hR : (0 : ℝ) < (injLabellings F (recordGraph (Fin 2))).card := by
    exact_mod_cast hneR.card_pos
  unfold FiniteLaw.expect
  simp only [graphLaw, ite_mul, zero_mul]
  rw [Finset.sum_ite_mem, Finset.univ_inter, ← Finset.mul_sum]
  field_simp

end Law

/-! ## The bounds of (b) for the actual uniform root -/

section Scores

variable {p : ℕ} [Fact p.Prime]

/-- **The three scores on the joined labelling**: `H₀` pairs the base `0` of the even component
with the base `3` of the odd one (index `2` in the order `1, 5, 3`), `H₁` the base `4` (index `2`)
with the base `1` (index `0`), and `H₂` the base `2` (index `1`) with the base `5` (index `1`). -/
theorem rootScore_joinC (ω : (Fin 3 × Fin 2 → ZMod p) × (Fin 3 × Fin 2 → ZMod p)) :
    PartV.rootScore p 0 (joinC ω) =
        pairScore (ω.1 (0, 0), ω.1 (0, 1)) (ω.2 (2, 0), ω.2 (2, 1)) ∧
      PartV.rootScore p 1 (joinC ω) =
        pairScore (ω.1 (2, 0), ω.1 (2, 1)) (ω.2 (0, 0), ω.2 (0, 1)) ∧
      PartV.rootScore p 2 (joinC ω) =
        pairScore (ω.1 (1, 0), ω.1 (1, 1)) (ω.2 (1, 0), ω.2 (1, 1)) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [rootScore_eq_pairScore]; rfl
  · rw [rootScore_eq_pairScore, pairScore_comm]; rfl
  · rw [rootScore_eq_pairScore]; rfl

/-- The component indices of the two pairs of the score `H_j`. -/
def scoreIdx (j : Fin 3) : Fin 3 × Fin 3 := ![(0, 2), (2, 0), (1, 1)] j

theorem rootScore_joinC_idx (j : Fin 3)
    (ω : (Fin 3 × Fin 2 → ZMod p) × (Fin 3 × Fin 2 → ZMod p)) :
    PartV.rootScore p j (joinC ω) =
      pairScore (ω.1 ((scoreIdx j).1, 0), ω.1 ((scoreIdx j).1, 1))
        (ω.2 ((scoreIdx j).2, 0), ω.2 ((scoreIdx j).2, 1)) := by
  obtain ⟨h0, h1, h2⟩ := rootScore_joinC ω
  fin_cases j
  · exact h0
  · exact h1
  · exact h2

/-- **`lem:root-normalization`(b) for the actual uniform root `Γ_{p,0} = λ_p(G_{L,2})`**: with
`q = r² = 1/p`, `χ(−1) = −1` and the coincidence counts of the proof as hypotheses (on the product
`μ` of the two component laws and the event `G` of global injectivity, with the spike events
`S`), every score has `|E_{Γ_{p,0}}H_j| ≤ h₀` and
`E_{Γ_{p,0}}H_j² ≥ 1 − 4q − 36q(2 + r)² − 2q/(1 − q)`. The moments `E_μH_j = qr`,
`E_μH_j² ≥ 1 − 4q` are proved (`component_moment_hyps`). -/
theorem gamma0_score_bounds (hm1 : quadraticChar (ZMod p) (-1) = -1) (hp2 : p ≠ 2)
    (hneR : (injLabellings (ZMod p) (recordGraph (Fin 2))).Nonempty)
    (hneC : (injLabellings (ZMod p) compGraph).Nonempty) (j : Fin 3)
    (S : (Fin 3 × Fin 2 → ZMod p) × (Fin 3 × Fin 2 → ZMod p) → Prop) [DecidablePred S]
    {q r : ℝ} (hr : r = 1 / Real.sqrt p) (hq : q = r ^ 2) (hq2 : q < 1 / 2) (hq36 : 36 * q < 1)
    (hGc : ∑ ω ∈ univ.filter (fun ω => ¬ GInj ω),
      ((graphLaw compGraph hneC).product (graphLaw compGraph hneC)).weight ω ≤ 36 * q)
    (hS : ∑ ω ∈ univ.filter (fun ω => ¬ GInj ω ∧ S ω),
      ((graphLaw compGraph hneC).product (graphLaw compGraph hneC)).weight ω ≤
        2 * q ^ 2 / (1 - q))
    (hB : ∀ ω, ¬ GInj ω → ¬ S ω → |PartV.rootScore p j (joinC ω)| ≤ 2 + r)
    (hA : ∀ ω, ¬ GInj ω → S ω → |PartV.rootScore p j (joinC ω)| ≤ 1 / r ∧
      PartV.rootScore p j (joinC ω) ^ 2 ≤ (1 - 2 * q) ^ 2 / q) :
    |(graphLaw (recordGraph (Fin 2)) hneR).expect (PartV.rootScore p j)| ≤
        (q * r + 36 * q * (2 + r) + 2 * q * r / (1 - q)) / (1 - 36 * q) ∧
      1 - 4 * q - 36 * q * (2 + r) ^ 2 - 2 * q / (1 - q) ≤
        (graphLaw (recordGraph (Fin 2)) hneR).expect (fun x => PartV.rootScore p j x ^ 2) := by
  have hF : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hs : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp0
  have hr0 : 0 < r := by rw [hr]; positivity
  have hcard : (Fintype.card (ZMod p) : ℝ) = p := by rw [ZMod.card]
  have hqp : q = 1 / (p : ℝ) := by
    rw [hq, hr, div_pow, Real.sq_sqrt hp0.le, one_pow]
  obtain ⟨hm, hsq⟩ := component_moment_hyps hm1 hF hneC (scoreIdx j).1 (scoreIdx j).2
  rw [hcard] at hm hsq
  have hmean : ((graphLaw compGraph hneC).product (graphLaw compGraph hneC)).expect
      (fun ω => PartV.rootScore p j (joinC ω)) = q * r := by
    simp only [rootScore_joinC_idx j]
    rw [hm, hqp, hr]
  have hsq' : 1 - 4 * q ≤ ((graphLaw compGraph hneC).product (graphLaw compGraph hneC)).expect
      (fun ω => PartV.rootScore p j (joinC ω) ^ 2) := by
    simp only [rootScore_joinC_idx j]
    rw [hqp]
    exact hsq
  obtain ⟨b1, b2⟩ := root_normalization_b ((graphLaw compGraph hneC).product
    (graphLaw compGraph hneC)) GInj S (fun ω => PartV.rootScore p j (joinC ω)) hr0 hq hq2 hq36
    hGc hS hB hA hmean hsq'
  refine ⟨?_, ?_⟩
  · rw [gamma0_expect hneR hneC]
    exact b1
  · rw [gamma0_expect hneR hneC]
    exact b2

end Scores

end Sarkozy.PositiveRoots
