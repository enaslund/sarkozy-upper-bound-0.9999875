module

public import Sarkozy.OpsSteps.SymCat

@[expose] public section

/-!
# The `G`-free term of the category `e_s`: the difference may be symmetrized (OPS-S)

`paper/sections/23_envelopes.tex`, proof of `lem:orbit-coupon`(i) (ll. 1268–1280);
`rem:cut-symmetries`(a), `lem:reflection-averaging`(c).

The term `T_{σ,∅}` of `SymCat` (no `G` atom) is the energy `Y_{κ̄ ⊗ δ ⊗ O}` of the orbit average
`κ̄ = ½(⊗Q₁ + ⊗Q₂)` on `S`, the difference `δ` at one outside atom `𝔅'` and `Ñ^inv` at the
others (`catT_zero_eq`). If `κ̄` and the `Ñ^inv` are `R_h`-invariant, `δ` may be replaced by its
symmetric part `½(δ + R_{h*}δ)` (**`catT_zero_sym`**, from `Sym.sym_swap`). So the input `hterm`
of `hcat_of_terms` at `Z = ∅` is a bound on `|Y_{κ̄ ⊗ ½(δ + R_{h*}δ) ⊗ O}|`: the symmetric sharp
bound `s_fold(X) b^{-1}` of `lem:record:one-stage-folded-e`(e).

`jointEnergy_add_right`, `jointEnergy_smul_right`: the energy is linear in the outside law.
-/

namespace Sarkozy.OpsSteps

open Filter Finset Function
open scoped Topology BigOperators
open Sarkozy.BracketEnergy Sarkozy.EnvelopeSteps Sarkozy.Envelopes
  Sarkozy.BlockFrame Sarkozy.TheoremC Sarkozy.Comparison Sarkozy.RecordExpansion
  Sarkozy.RecordExpansion.Choice

section Linear

variable {V : Type*} [Fintype V] [DecidableEq V]
  {A B : Type} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]

omit [Fintype V] [DecidableEq V] [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B] in
theorem pairLaws_eq_update (κ : ((V → A) → ℝ) →ₗ[ℝ] ℝ) (O₁ O : ((V → B) → ℝ) →ₗ[ℝ] ℝ) :
    pairLaws κ O = Function.update (pairLaws κ O₁) false O := by
  funext b
  cases b
  · simp only [Function.update_self]
    rfl
  · simp only [ne_eq, Bool.true_eq_false, not_false_eq_true, Function.update_of_ne]
    rfl

/-- **The energy is additive in the outside law.** -/
theorem jointEnergy_add_right (κ : ((V → A) → ℝ) →ₗ[ℝ] ℝ) (O₁ O₂ : ((V → B) → ℝ) →ₗ[ℝ] ℝ)
    (F : (∀ b, pairFam A B b) → ℝ) :
    jointEnergy κ (O₁ + O₂) F = jointEnergy κ O₁ F + jointEnergy κ O₂ F := by
  unfold jointEnergy
  rw [pairLaws_eq_update κ O₁ (O₁ + O₂), tensorLaw_update_add, ← pairLaws_eq_update κ O₁ O₁,
    ← pairLaws_eq_update κ O₁ O₂]
  rfl

/-- **The energy is homogeneous in the outside law.** -/
theorem jointEnergy_smul_right (κ : ((V → A) → ℝ) →ₗ[ℝ] ℝ) (a : ℝ) (O : ((V → B) → ℝ) →ₗ[ℝ] ℝ)
    (F : (∀ b, pairFam A B b) → ℝ) :
    jointEnergy κ (a • O) F = a * jointEnergy κ O F := by
  unfold jointEnergy
  rw [pairLaws_eq_update κ O (a • O), tensorLaw_update_smul, ← pairLaws_eq_update κ O O]
  rfl

end Linear

variable {a : ℝ}
  {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

variable (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ) (A : Finset ℤ)
  (isG : ∀ b : BlockAtom Bk J L, D.GB.Iu L b → Bool) (S : Finset (BlockAtom Bk J L))

/-- The invariant background `Ñ^inv = μ + ∑_{¬isG} κu` of an atom. -/
noncomputable def ninvP (b : BlockAtom Bk J L) : TheoremCBlock.AtomMeasure m₀ blk p L b :=
  D.R.law p L b + ∑ i ∈ univ.filter (fun i => isG b i = false), D.GB.κu L b i

/-- The outside law of the `G`-free term: the difference at the chosen atoms, `Ñ^inv` elsewhere. -/
noncomputable def catOut (σ : ∀ b, Option (D.FS.Ib L b)) (j : {b // b ∉ S}) :
    TheoremCBlock.AtomMeasure m₀ blk p L j.1 :=
  (σ j.1).elim (ninvP D L isG j.1) (fun i => D.FS.κ' L j.1 i - D.FS.κ L j.1 i)

/-- The orbit average `κ̄ = ½(⊗Q₁ + ⊗Q₂)` on `S`. -/
noncomputable def orbitBar (Q₁ Q₂ : ∀ b, TheoremCBlock.AtomMeasure m₀ blk p L b) :
    ((Slot → PIn (m₀ := m₀) (blk := blk) (p := p) L S) → ℝ) →ₗ[ℝ] ℝ :=
  (1 / 2 : ℝ) • (tensorLaw (fun j : {b // b ∈ S} => Q₁ j.1) +
    tensorLaw (fun j : {b // b ∈ S} => Q₂ j.1))

omit [DecidableEq P] in
/-- **The `G`-free term is an energy of the orbit average.** -/
theorem catT_zero_eq (Q₁ Q₂ : ∀ b, TheoremCBlock.AtomMeasure m₀ blk p L b)
    (σ : ∀ b, Option (D.FS.Ib L b)) (hσS : ∀ j ∈ S, σ j = none) :
    catT D L A isG S Q₁ Q₂ σ (fun _ => false) =
      jointEnergy (orbitBar L S Q₁ Q₂) (tensorLaw (catOut D L isG S σ))
        (fun z => blockLift m₀ blk p L A (merge S z)) := by
  unfold catT
  have hmem : (fun _ => false : BlockAtom Bk J L → Bool) ∈ Fintype.piFinset (catSet D L S σ) := by
    refine Fintype.mem_piFinset.mpr fun b => ?_
    unfold catSet
    split_ifs
    · exact mem_singleton_self _
    · exact mem_univ _
  simp only [hmem, ↓reduceIte]
  have hk : ∀ Q : ∀ b, TheoremCBlock.AtomMeasure m₀ blk p L b,
      diagonalIntegral (tensorLaw fun b => catLaw D L isG S Q σ b false)
        (blockLift m₀ blk p L A) =
      jointEnergy (tensorLaw (fun j : {b // b ∈ S} => Q j.1)) (tensorLaw (catOut D L isG S σ))
        (fun z => blockLift m₀ blk p L A (merge S z)) := by
    intro Q
    rw [← jointEnergy_tensor S (fun b => catLaw D L isG S Q σ b false)]
    have h1 : (fun j : {b // b ∈ S} => catLaw D L isG S Q σ j.1 false) =
        fun j : {b // b ∈ S} => Q j.1 := by
      funext j
      simp [catLaw, hσS j.1 j.2, j.2]
    have h2 : (fun j : {b // b ∉ S} => catLaw D L isG S Q σ j.1 false) =
        catOut D L isG S σ := by
      funext j
      unfold catLaw catOut ninvP
      rcases σ j.1 with _ | i
      · simp [j.2]
      · simp [j.2]
    rw [h1, h2]
  rw [hk Q₁, hk Q₂]
  unfold orbitBar
  rw [← jointEnergyL_apply, ← jointEnergyL_apply, ← jointEnergyL_apply, map_smul, map_add,
    smul_eq_mul]

omit [DecidableEq P] in
/-- **The difference may be replaced by its symmetric part** (see the module docstring): if the
orbit average is `R_h`-invariant, `σ` has its only difference at the outside atom `𝔅'`, and `Ñ^inv`
is `R_h`-invariant at the other outside atoms, then
`T_{σ,∅} = Y_{κ̄ ⊗ ½(δ + R_{h*}δ) ⊗ O}`. -/
theorem catT_zero_sym (Q₁ Q₂ : ∀ b, TheoremCBlock.AtomMeasure m₀ blk p L b)
    (σ : ∀ b, Option (D.FS.Ib L b)) (hσS : ∀ j ∈ S, σ j = none) (b' : {b // b ∉ S})
    (hσ : ∀ j : {b // b ∉ S}, j ≠ b' → σ j.1 = none) (hR : ZMod 6)
    (hκ : slotPush (slotREquiv hR) (orbitBar L S Q₁ Q₂) = orbitBar L S Q₁ Q₂)
    (hinvN : ∀ j : {b // b ∉ S}, j ≠ b' →
      slotPush (slotREquiv hR) (ninvP D L isG j.1) = ninvP D L isG j.1) :
    catT D L A isG S Q₁ Q₂ σ (fun _ => false) =
      jointEnergy (orbitBar L S Q₁ Q₂)
        (tensorLaw (Function.update (catOut D L isG S σ) b'
          ((1 / 2 : ℝ) • (catOut D L isG S σ b' +
            slotPush (slotREquiv hR) (catOut D L isG S σ b')))))
        (fun z => blockLift m₀ blk p L A (merge S z)) := by
  rw [catT_zero_eq D L A isG S Q₁ Q₂ σ hσS]
  set Lo := catOut D L isG S σ with hLo
  set F := fun z => blockLift m₀ blk p L A (merge S z) with hF
  have hO : ∀ j, j ≠ b' → slotPush (slotREquiv hR) (Lo j) = Lo j := by
    intro j hj
    simp only [hLo, catOut, hσ j hj, Option.elim_none]
    exact hinvN j hj
  have hswap := sym_swap (slotREquiv hR) (orbitBar L S Q₁ Q₂) hκ Lo b' hO F
  have hupd : (fun j => if j = b' then slotPush (slotREquiv hR) (Lo j) else Lo j) =
      Function.update Lo b' (slotPush (slotREquiv hR) (Lo b')) := by
    funext j
    by_cases hj : j = b'
    · subst hj
      simp
    · simp [hj]
  rw [hupd] at hswap
  rw [tensorLaw_update_smul, tensorLaw_update_add, Function.update_eq_self,
    jointEnergy_smul_right, jointEnergy_add_right, ← hswap]
  ring

end Sarkozy.OpsSteps
