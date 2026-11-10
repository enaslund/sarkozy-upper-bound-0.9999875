module

public import Sarkozy.F7Repair.Counts
public import Sarkozy.TailPrices.RepairMain
public import Sarkozy.PartVLaws.Labellable
public import Sarkozy.ComparisonLawPaper.Tail

@[expose] public section

/-!
# The tail replacements with an explicit constant, proved from Weil's bound (K2's field 10)

At a tail prime `q ≥ P₄ = 2⁵¹²` every changed two-layer record `(t, φ)` is replaced by the law
`π^new = λ_q(G^new)` of its repaired graph (`newGraph`, with the projected `𝓔₆` queries
`queryPairs` as cross edges), *without* the additive marginal correction of `lem:tr:repair`. The
replacement:

* exists (`Inj_q(G^new) ≠ ∅`, `nonempty_of_large`), lies where `λ_H` is on both layers, accepts
  `𝓔₆` and is square-affine invariant (`NewGraph.lean`);
* has both half marginals within a factor `2` of the old half marginal `μ^old`
  (`layer_density_le`, from `lem:graphs:sequential` and H1: the old and the new graph have the
  same edges inside each layer);
* hence (Cauchy–Schwarz, `crude_change_bound`) its change of pair forms against the old record is
  at most `C_tail = 3` relative to `μ^old`: `|E_new[φ(x)ψ(y)]| ≤ 2‖φ‖‖ψ‖` and
  `|E_old[φ(x)ψ(y)]| ≤ ‖φ‖‖ψ‖`.

The constant is `crudeC = 3` for every record, symmetric and skew alike. It is not `O(r)`: the
paper's (F7) constant `C_ϱ r` needs the marginal correction and the correlation bounds (F2), (F6).
At the tail any explicit constant is enough (D1's redesign); the price of a changed record is then
`P_μ(r)⁻¹ c_ρ · 3` (`crude_sum_π_le`).

* **`crudeRepair hW h4 hne t φ : TailRepair q hne t φ`** and **`crudeRepairs hW`**: K2's field 10
  (`Cmp.Rp`) with `C = 3`, proved from `Target.Weil` alone;
* `crudeRepairs_C`: every constant is `3`;
* `crude_sum_π_le`: `∑_{changed} π_ρ^ε ≤ 3 ∑_{changed} c_ρ` (to regenerate the tail ledger).
-/

open Finset
open scoped BigOperators

namespace Sarkozy.F7Repair

open Sarkozy.TheoremC Sarkozy.RecordExpansion Sarkozy.Mixing Sarkozy.PartV Sarkozy.PartVRecords
  Sarkozy.Labellings Sarkozy.UpperComparison Sarkozy.Recentering Sarkozy.Structured
  Sarkozy.TailPrices

/-- **The explicit tail constant** `C_tail = 3`. -/
def crudeC : ℝ := 3

/-- The old graph `G_{φ₀φ₁,2}` and the new graph have the same feasible labellings of a layer. -/
theorem feasible_layerSet_iff {F : Type*} [Field F] [Fintype F] [DecidableEq F] (f₀ f₁ : FType)
    (Q : Finset ((f₀.Obj × f₁.Obj) × (f₀.Obj × f₁.Obj))) (k : Fin 2)
    (x : f₀.Obj × f₁.Obj × Fin 2 → F) :
    Feasible F (newGraph f₀ f₁ Q) (layerSet k) x ↔
      Feasible F (fieldGraph f₀ f₁ (Fin 2)) (layerSet k) x := by
  have hl : ∀ w ∈ (layerSet k : Finset (f₀.Obj × f₁.Obj × Fin 2)), w.2.2 = k :=
    fun w hw => (mem_filter.mp hw).2
  constructor
  · rintro ⟨hinj, hedge⟩
    refine ⟨hinj, fun e he h1 h2 => hedge e ?_ h1 h2⟩
    exact (mem_newEdges f₀ f₁ Q e).mpr (Or.inl ⟨he, by rw [hl _ h1, hl _ h2]⟩)
  · rintro ⟨hinj, hedge⟩
    refine ⟨hinj, fun e he h1 h2 => ?_⟩
    rcases (mem_newEdges f₀ f₁ Q e).mp he with ⟨he', _⟩ | ⟨q', _, hq⟩
    · exact hedge e he' h1 h2
    · have a := (crossEdge_layers q').1
      have b := (crossEdge_layers q').2
      rw [hq] at a b
      have h1' := hl _ h1
      have h2' := hl _ h2
      rw [a] at h1'
      rw [b] at h2'
      rw [← h1'] at h2'
      exact absurd h2' (by decide)

/-- A pointwise density bound between image laws bounds the norms. -/
theorem nrm_comp_le {Ω₁ Ω₂ Ξ : Type*} [Fintype Ω₁] [Fintype Ω₂] [Fintype Ξ] [DecidableEq Ξ]
    (lam₁ : FiniteLaw Ω₁) (lam₂ : FiniteLaw Ω₂) (a₁ : Ω₁ → Ξ) (a₂ : Ω₂ → Ξ) {B : ℝ}
    (hB : ∀ x, (lam₁.map a₁).weight x ≤ B * (lam₂.map a₂).weight x) (φ : Ξ → ℝ) :
    nrm lam₁ (fun ω => φ (a₁ ω)) ≤ Real.sqrt B * nrm lam₂ (fun ω => φ (a₂ ω)) := by
  unfold nrm ip
  have e1 : lam₁.expect (fun ω => φ (a₁ ω) * φ (a₁ ω)) = (lam₁.map a₁).expect (fun x => φ x * φ x) := by
    rw [FiniteLaw.expect_map]; rfl
  have e2 : lam₂.expect (fun ω => φ (a₂ ω) * φ (a₂ ω)) = (lam₂.map a₂).expect (fun x => φ x * φ x) := by
    rw [FiniteLaw.expect_map]; rfl
  rw [e1, e2, ← Real.sqrt_mul' _ ((lam₂.map a₂).expect_nonneg fun _ => mul_self_nonneg _)]
  apply Real.sqrt_le_sqrt
  unfold FiniteLaw.expect
  rw [mul_sum]
  exact sum_le_sum fun x _ => by
    have := mul_le_mul_of_nonneg_right (hB x) (mul_self_nonneg (φ x))
    linarith

variable {q : ℕ} [Fact q.Prime]

/-- The vertex count of a two-layer field graph is at most `72`. -/
theorem card_two_le (f₀ f₁ : FType) : Fintype.card (f₀.Obj × f₁.Obj × Fin 2) ≤ 72 := by
  have := PartVLaws.card_fieldVertices_le f₀ f₁ (Λ' := Fin 2) (by simp)
  exact_mod_cast this

theorem card_zmod_large (h4 : P4 ≤ q) : (2 : ℝ) ^ 512 ≤ Fintype.card (ZMod q) := by
  rw [ZMod.card]
  exact two_pow_512_le_of_P4 q h4

/-- The projected `𝓔₆` queries of a record. -/
noncomputable abbrev recQ (t : PType × PType) (φ : t.1.Pat × t.2.Pat) :
    Finset ((t.1.field.Obj × t.2.field.Obj) × (t.1.field.Obj × t.2.field.Obj)) :=
  queryPairs (t.1.pat φ.1) (t.2.pat φ.2)

theorem recQ_mem (t : PType × PType) (φ : t.1.Pat × t.2.Pat) (j : Chamber) :
    ((t.1.pat φ.1 0, t.2.pat φ.2 j), (t.1.pat φ.1 2, t.2.pat φ.2 (chamberRotation j))) ∈
      recQ t φ :=
  mem_image_of_mem (fun j : Chamber => ((t.1.pat φ.1 0, t.2.pat φ.2 j),
    (t.1.pat φ.1 2, t.2.pat φ.2 (chamberRotation j)))) (mem_univ j)

/-- `Inj_q(G^new) ≠ ∅` at a tail prime (H1). -/
theorem recN (hW : Target.Weil) (h4 : P4 ≤ q) (t : PType × PType) (φ : t.1.Pat × t.2.Pat) :
    (injLabellings (ZMod q) (newGraph t.1.field t.2.field (recQ t φ))).Nonempty :=
  nonempty_of_large (weilBound_of_target hW q (ne_two_of_P4 q h4)) _ (card_zmod_large h4)
    (card_two_le _ _)

/-- **The replacement law `λ_q(G^new)`** of a record. -/
noncomputable abbrev crudeLam (hW : Target.Weil) (h4 : P4 ≤ q) (t : PType × PType) (φ : t.1.Pat × t.2.Pat) :
    FiniteLaw (t.1.field.Obj × t.2.field.Obj × Fin 2 → ZMod q) :=
  graphLaw (newGraph t.1.field t.2.field (recQ t φ)) (recN hW h4 t φ)

/-- **The half marginals of the replacement are within a factor `2` of `μ^old`.** -/
theorem crude_density (hW : Target.Weil) (h4 : P4 ≤ q) (hne : TailNonempty q) (t : PType × PType) (φ : t.1.Pat × t.2.Pat) (k : Fin 2)
    (x : t.1.field.Obj × t.2.field.Obj → ZMod q) :
    ((crudeLam hW h4 t φ).map (fun y => layerOf y k)).weight x ≤
      2 * ((tailOld q hne t).map (fun y => layerOf y k)).weight x :=
  layer_density_le (weilBound_of_target hW q (ne_two_of_P4 q h4)) _ _ _ (hne.two _ _) k
    (fun x => feasible_layerSet_iff _ _ _ k x) (card_zmod_large h4) (card_two_le _ _) x

/-- **The change bound with `C_tail = 3`** (Cauchy–Schwarz and `crude_density`). -/
theorem crude_change_bound (hW : Target.Weil) (h4 : P4 ≤ q) (hne : TailNonempty q)
    (t : PType × PType) (φ : t.1.Pat × t.2.Pat)
    (φ' ψ' : (t.1.field.Obj × t.2.field.Obj → ZMod q) → ℝ) :
    |tailChangeForm q hne t (crudeLam hW h4 t φ) φ' ψ'| ≤
      crudeC * mnrm (tailHalf q hne t.1.field t.2.field) (tailU q hne t) φ' *
        mnrm (tailHalf q hne t.1.field t.2.field) (tailU q hne t) ψ' := by
  have hsN := newGraph_layersSupported hne t.1.field t.2.field (recQ t φ) (recN hW h4 t φ)
  have hsO := tail_layersSupported q hne t.1.field t.2.field
  unfold tailChangeForm centredForm
  rw [← pair_density_eq _ _ hsN φ' ψ', ← pair_density_eq _ _ hsO φ' ψ',
    F7Record.mnrm_eq hsO, F7Record.mnrm_eq hsO]
  set lamN := crudeLam hW h4 t φ
  set lamO := tailOld q hne t
  set μ := oldHalf lamO
  -- the norms under the two laws
  have hO0 : nrm lamO (fun y => φ' (lay0 y)) = nrm μ φ' := by
    unfold nrm ip
    rw [oldHalf_expect]
  have hO1 : nrm lamO (fun y => ψ' (lay1 y)) = nrm μ ψ' := by
    unfold nrm ip
    rw [oldHalf_expect, ← tailOld_symm hne t (fun x => ψ' x * ψ' x)]
  have hN0 : nrm lamN (fun y => φ' (lay0 y)) ≤ Real.sqrt 2 * nrm μ φ' := by
    rw [← hO0]
    exact nrm_comp_le lamN lamO lay0 lay0 (fun x => crude_density hW h4 hne t φ 0 x) φ'
  have hN1 : nrm lamN (fun y => ψ' (lay1 y)) ≤ Real.sqrt 2 * nrm μ ψ' := by
    rw [← hO1]
    exact nrm_comp_le lamN lamO lay1 lay1 (fun x => crude_density hW h4 hne t φ 1 x) ψ'
  have cN := abs_ip_le lamN (fun y => φ' (lay0 y)) (fun y => ψ' (lay1 y))
  have cO := abs_ip_le lamO (fun y => φ' (lay0 y)) (fun y => ψ' (lay1 y))
  unfold ip at cN cO
  have hn1 : 0 ≤ nrm μ φ' := Real.sqrt_nonneg _
  have hn2 : 0 ≤ nrm μ ψ' := Real.sqrt_nonneg _
  have hs2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hNb : nrm lamN (fun y => φ' (lay0 y)) * nrm lamN (fun y => ψ' (lay1 y)) ≤
      2 * nrm μ φ' * nrm μ ψ' := by
    calc nrm lamN (fun y => φ' (lay0 y)) * nrm lamN (fun y => ψ' (lay1 y))
        ≤ (Real.sqrt 2 * nrm μ φ') * (Real.sqrt 2 * nrm μ ψ') :=
          mul_le_mul hN0 hN1 (Real.sqrt_nonneg _) (by positivity)
      _ = (Real.sqrt 2 * Real.sqrt 2) * nrm μ φ' * nrm μ ψ' := by ring
      _ = 2 * nrm μ φ' * nrm μ ψ' := by rw [hs2]
  rw [hO0, hO1] at cO
  have e : ∀ A B c : ℝ, (A - c) - (B - c) = A - B := fun _ _ _ => by ring
  rw [e]
  unfold crudeC
  calc |lamN.expect (fun y => φ' (layerOf y 0) * ψ' (layerOf y 1)) -
        lamO.expect (fun y => φ' (layerOf y 0) * ψ' (layerOf y 1))|
      ≤ |lamN.expect (fun y => φ' (layerOf y 0) * ψ' (layerOf y 1))| +
        |lamO.expect (fun y => φ' (layerOf y 0) * ψ' (layerOf y 1))| := abs_sub _ _
    _ ≤ 2 * nrm μ φ' * nrm μ ψ' + nrm μ φ' * nrm μ ψ' := add_le_add (cN.trans hNb) cO
    _ = 3 * nrm μ φ' * nrm μ ψ' := by ring

/-- **The tail replacement of a record** (K2's field 10, one record), proved from H1, with
`C^s = C^a = 3`. -/
noncomputable def crudeRepair (hW : Target.Weil) (h4 : P4 ≤ q) (hne : TailNonempty q)
    (t : PType × PType) (φ : t.1.Pat × t.2.Pat) : TailRepair q hne t φ :=
  TailRepair.ofChangeBound (crudeLam hW h4 t φ)
    (newGraph_layersSupported hne t.1.field t.2.field (recQ t φ) (recN hW h4 t φ))
    (fun z hz j => newGraph_accepts _ _ (recQ t φ) _ _ (recQ_mem t φ) (recN hW h4 t φ) z hz j)
    (fun α β hα z => by
      have hα0 : α ≠ 0 := ne_zero_of_quadraticChar_eq_one hα
      exact map_weight_equivariant (crudeLam hW h4 t φ)
        (fun y => y ∘ upEmission (t.1.pat φ.1) (t.2.pat φ.2)) (affEquiv α β hα0)
        (affEquiv α β hα0)
        (fun y => newGraph_affine _ _ (recQ t φ) (recN hW h4 t φ) α β hα y) (fun _ => rfl) z)
    crudeC (by norm_num [crudeC]) (crude_change_bound hW h4 hne t φ)

theorem crudeRepair_C (hW : Target.Weil) (h4 : P4 ≤ q) (hne : TailNonempty q)
    (t : PType × PType) (φ : t.1.Pat × t.2.Pat) (e : ChangeType) :
    (crudeRepair hW h4 hne t φ).C e = crudeC := by
  cases e <;> rfl

/-- **K2's field 10 (`Cmp.Rp`), proved from H1**: the tail replacements of every changed record at
every tail prime, with constant `C_tail = 3`. -/
noncomputable def crudeRepairs (hW : Target.Weil) :
    ∀ (q : ℕ) [Fact q.Prime] (h4 : P4 ≤ q), TailRepairs q (ComparisonLawPaper.tailNe hW h4) :=
  fun _ _ h4 t φ _ => crudeRepair hW h4 _ t φ

theorem crudeRepairs_C (hW : Target.Weil) (q : ℕ) [Fact q.Prime] (h4 : P4 ≤ q) (t : PType × PType)
    (φ : t.1.Pat × t.2.Pat) (h : upperFate (true, ⟨t, φ⟩) = .changed) (e : ChangeType) :
    (crudeRepairs hW q h4 t φ h).C e = crudeC :=
  crudeRepair_C hW h4 _ t φ e

/-- **The tail repair prices with `C_tail = 3`**: `∑_{changed} π^ε_ρ ≤ 3 ∑_{changed} c_ρ(r)`. -/
theorem crude_sum_π_le (hW : Target.Weil) (q : ℕ) [Fact q.Prime] (h4 : P4 ≤ q) (e : ChangeType) :
    ∑ ρ ∈ univ.filter (fun ρ => upperFate ρ = .changed), (crudeRepairs hW q h4).π ρ e ≤
      crudeC * ∑ ρ ∈ univ.filter (fun ρ => upperFate ρ = .changed),
        upCoeff tailWeights (tailR q) ρ := by
  have hr : 0 < tailR q := tailR_pos q
  have h := (crudeRepairs hW q h4).sum_π_le (fun _ => crudeC / tailR q) e (fun t φ h => by
    rw [crudeRepairs_C, div_mul_cancel₀ _ hr.ne'])
  refine h.trans (le_of_eq ?_)
  rw [mul_sum]
  refine sum_congr rfl fun ρ _ => ?_
  rw [mul_assoc, div_mul_cancel₀ _ hr.ne', mul_comm]

end Sarkozy.F7Repair
