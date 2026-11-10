module

public import Sarkozy.OpsSteps.SymFine

@[expose] public section

/-!
# The input `hsymT` as a bound on the symmetric part of the difference (OPS-S)

`paper/sections/23_envelopes.tex`, proof of `lem:orbit-coupon`(i).

A choice `σ` of the category `e_s` has exactly one difference (`es_single`). If it sits on the
support, the `G`-free term vanishes (`catT_zero_of_support`). Otherwise, for an `R_h`-invariant
orbit average and `R_h`-invariant `Ñ^inv`, the term is the energy with the difference replaced by
its symmetric part (`SymSwap.catT_zero_sym`). So **`hsymT_of_sym`**: the input `hsymT` of
`SymFineSum.hsym_fine` / `Step3Fine.herr_hsym_of_tensor` follows from a bound on
`|Y_{κ̄ ⊗ ½(δ + R_{h*}δ) ⊗ O}|`, the statement of `lem:record:one-stage-folded-e`(e) at the
replaced record.
-/

namespace Sarkozy.OpsSteps

open Filter Finset Function
open scoped Topology BigOperators
open Sarkozy.BracketEnergy Sarkozy.EnvelopeSteps Sarkozy.Envelopes
  Sarkozy.BlockFrame Sarkozy.TheoremC Sarkozy.Comparison Sarkozy.RecordExpansion
  Sarkozy.RecordExpansion.Choice

variable {a : ℝ}
  {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

variable (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ) (A : Finset ℤ)
  (isG : ∀ b : BlockAtom Bk J L, D.GB.Iu L b → Bool) (S : Finset (BlockAtom Bk J L))

omit [DecidableEq P] in
/-- **A choice of the category `e_s` has exactly one difference.** -/
theorem es_single (s : D.FS.Tag) (σ : ∀ b, Option (D.FS.Ib L b))
    (hσ : countVec (D.FS.tag L) σ = Pi.single s 1) :
    ∃ b', (σ b').isSome ∧ ∀ b, b ≠ b' → σ b = none := by
  have h1 : countVec (D.FS.tag L) σ s = 1 := by rw [hσ]; simp
  unfold countVec at h1
  obtain ⟨b', hb'⟩ := Finset.card_eq_one.mp h1
  have hmem : b' ∈ univ.filter (fun b => (σ b).map (D.FS.tag L b) = some s) := by
    rw [hb']
    exact mem_singleton_self _
  have hb'σ : (σ b').map (D.FS.tag L b') = some s := (mem_filter.mp hmem).2
  refine ⟨b', ?_, fun b hb => ?_⟩
  · rcases h : σ b' with _ | i
    · simp [h] at hb'σ
    · simp
  · rcases h : σ b with _ | i
    · rfl
    · exfalso
      by_cases ht : D.FS.tag L b i = s
      · have hm : b ∈ univ.filter (fun b => (σ b).map (D.FS.tag L b) = some s) :=
          mem_filter.mpr ⟨mem_univ _, by simp [h, ht]⟩
        rw [hb'] at hm
        exact hb (mem_singleton.mp hm)
      · have h2 : countVec (D.FS.tag L) σ (D.FS.tag L b i) = 0 := by
          rw [hσ]
          simp [ht]
        unfold countVec at h2
        have hm : b ∈ univ.filter
            (fun c => (σ c).map (D.FS.tag L c) = some (D.FS.tag L b i)) :=
          mem_filter.mpr ⟨mem_univ _, by simp [h]⟩
        rw [Finset.card_eq_zero] at h2
        rw [h2] at hm
        simp at hm

omit [DecidableEq P] in
/-- **A difference on the support kills the term.** -/
theorem catT_zero_of_support (Q₁ Q₂ : ∀ b, TheoremCBlock.AtomMeasure m₀ blk p L b)
    (σ : ∀ b, Option (D.FS.Ib L b)) (b' : BlockAtom Bk J L) (hb' : b' ∈ S)
    (hsome : (σ b').isSome) (f : BlockAtom Bk J L → Bool) :
    catT D L A isG S Q₁ Q₂ σ f = 0 := by
  have hz : ∀ Q : ∀ b, TheoremCBlock.AtomMeasure m₀ blk p L b,
      tensorLaw (fun b => catLaw D L isG S Q σ b (f b)) = 0 := by
    intro Q
    apply LinearMap.ext
    intro F
    rw [tensorLaw_apply, LinearMap.zero_apply]
    refine sum_eq_zero fun z _ => ?_
    have h0 : lawDensity (catLaw D L isG S Q σ b' (f b')) (z b') = 0 := by
      obtain ⟨i, hi⟩ := Option.isSome_iff_exists.mp hsome
      simp only [catLaw, hi, Option.elim_some, hb', decide_true, ↓reduceIte]
      rfl
    rw [prod_eq_zero (mem_univ b') h0, zero_mul]
  unfold catT
  split_ifs
  · rw [hz Q₁, hz Q₂]
    change (1 / 2 : ℝ) * ((0 : ℝ) + 0) = 0
    ring
  · rfl

omit [DecidableEq P] in
/-- **`hsymT` from the symmetric part** (see the module docstring): for `σ ∈ e_s` with its
difference at `𝔅' ∉ S`, the bound `B_σ + r_σ` on `|Y_{κ̄ ⊗ ½(δ + R_{h*}δ) ⊗ O}|` gives the bound on
the `G`-free term `T_{σ,∅}`. -/
theorem hsymT_of_sym (Q₁ Q₂ : ∀ b, TheoremCBlock.AtomMeasure m₀ blk p L b) (s : D.FS.Tag)
    (hR : ZMod 6)
    (hκ : slotPush (slotREquiv hR) (orbitBar L S Q₁ Q₂) = orbitBar L S Q₁ Q₂)
    (hinvN : ∀ j : {b // b ∉ S},
      slotPush (slotREquiv hR) (ninvP D L isG j.1) = ninvP D L isG j.1)
    (B r : (∀ b, Option (D.FS.Ib L b)) → ℝ) (hBr : ∀ σ, 0 ≤ B σ + r σ)
    (hS : ∀ σ ∈ (univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none)).filter
        (fun σ => countVec (D.FS.tag L) σ = Pi.single s 1),
      ∀ b' : {b // b ∉ S}, (σ b'.1).isSome →
      |jointEnergy (orbitBar L S Q₁ Q₂)
          (tensorLaw (Function.update (catOut D L isG S σ) b'
            ((1 / 2 : ℝ) • (catOut D L isG S σ b' +
              slotPush (slotREquiv hR) (catOut D L isG S σ b')))))
          (fun z => blockLift m₀ blk p L A (merge S z))| ≤ B σ + r σ) :
    ∀ σ ∈ (univ.filter (fun σ : (∀ b, Option (D.FS.Ib L b)) => σ ≠ fun _ => none)).filter
        (fun σ => countVec (D.FS.tag L) σ = Pi.single s 1),
      |catT D L A isG S Q₁ Q₂ σ (fun _ => false)| ≤ B σ + r σ := by
  intro σ hσ
  obtain ⟨b', hsome, honly⟩ := es_single D L s σ (mem_filter.mp hσ).2
  by_cases hb' : b' ∈ S
  · rw [catT_zero_of_support D L A isG S Q₁ Q₂ σ b' hb' hsome, abs_zero]
    exact hBr σ
  · have hσS : ∀ j ∈ S, σ j = none := fun j hj => honly j (fun e => hb' (e ▸ hj))
    have hσo : ∀ j : {b // b ∉ S}, j ≠ ⟨b', hb'⟩ → σ j.1 = none :=
      fun j hj => honly j.1 fun e => hj (Subtype.ext e)
    rw [catT_zero_sym D L A isG S Q₁ Q₂ σ hσS ⟨b', hb'⟩ hσo hR hκ (fun j _ => hinvN j)]
    exact hS σ hσ ⟨b', hb'⟩ hsome

end Sarkozy.OpsSteps
