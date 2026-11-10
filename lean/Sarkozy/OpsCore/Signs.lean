module

public import Sarkozy.OpsCore.BracketOp

@[expose] public section

/-!
# The signs of the record operators, and the star form with the support proved (OPS-L)

`paper/sections/23_envelopes.tex`, Step 1 of the proof of `thm:envelopes` ("`Υ_ω` is
self-adjoint, the tensor having an even number of skew-adjoint factors");
`def:cp:records` (the symmetric and skew parts `½(ζ ± c_* ζ)`); (CP4)(c) (a selection has an even
number of skew types).

* **`density_reflect`**: the reflected law at `join(x, y)` is the law at `join(y, x)`;
  hence the matrices of `symPart` and `skewPart` are symmetric and antisymmetric
  (`density_changePart`).
* **`kern_Δhat_swap`**: at the selected marginals the record operator `Δ̂_𝔅` has an
  `ε_𝔅`-symmetric kernel, `ε_𝔅 = −1` for a skew record and `1` for a symmetric one (`selSign`).
* **`prod_selSign`**: `∏_{𝔅 ∈ X} ε_𝔅 = 1` for a selection (`IsSelection`: an even number of skew
  types).
* **`starOK_sel`**: `StarOK` for a selection at the selected marginals and signs, from `w > 0`,
  the two norm bounds of (N1)–(N3) and the `ε`-symmetry of the leading stars. Everything else
  (`PlusIn`, `m ≥ 0`, the signs, the parity, the symmetry of `Δ̂`) is proved.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.OpsCore

open Sarkozy.EnvelopeSteps Sarkozy.SignedComponents Sarkozy.TheoremC Sarkozy.RecordExpansion

section Generic

variable {V X : Type*} [Fintype V] [DecidableEq V] [Fintype X] [DecidableEq X]
  {c : ReflectionCut V}

omit [Fintype X] in
/-- The reflected law at `join(x, y)` is the law at `join(y, x)`. -/
theorem density_reflect (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ) (x y : c.Half → X) :
    lawDensity (reflect c L) (c.join x y) = lawDensity L (c.join y x) := by
  unfold lawDensity
  rw [reflect_apply]
  congr 1
  funext z
  have hiff : z ∘ c.flip = c.join x y ↔ z = c.join y x := by
    constructor
    · intro h
      calc z = (z ∘ c.flip) ∘ c.flip := by
            funext v
            simp only [Function.comp_apply, c.flip_flip]
        _ = c.join x y ∘ c.flip := by rw [h]
        _ = c.join y x := c.join_reflection x y
    · intro h
      rw [h, c.join_reflection]
  exact if_congr hiff rfl rfl

omit [Fintype X] in
theorem density_skewPart (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ) (x y : c.Half → X) :
    lawDensity (skewPart c L) (c.join y x) = -lawDensity (skewPart c L) (c.join x y) := by
  have e : ∀ u w : c.Half → X, lawDensity (skewPart c L) (c.join u w) =
      1 / 2 * (lawDensity L (c.join u w) - lawDensity L (c.join w u)) := by
    intro u w
    rw [← density_reflect L u w]
    rfl
  rw [e, e]
  ring

omit [Fintype X] in
theorem density_symPart (L : ((V → X) → ℝ) →ₗ[ℝ] ℝ) (x y : c.Half → X) :
    lawDensity (symPart c L) (c.join y x) = lawDensity (symPart c L) (c.join x y) := by
  have e : ∀ u w : c.Half → X, lawDensity (symPart c L) (c.join u w) =
      1 / 2 * (lawDensity L (c.join u w) + lawDensity L (c.join w u)) := by
    intro u w
    rw [← density_reflect L u w]
    rfl
  rw [e, e]
  ring

end Generic

section Paper

open Sarkozy.ClassInputsPaper Sarkozy.ClassBoundsPaper Sarkozy.TheoremCBlock
  Sarkozy.BlockFrame Sarkozy.RecordExpansion.Choice

variable {a : ℝ}
  {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

/-- The sign of the selected record at a block: `−1` for a skew record, `1` otherwise. -/
def selSign {L : ℕ} {T : BlockAtom Bk J L → Type} (ω : Choice T) (b : BlockAtom Bk J L) : ℝ :=
  if isSkewEntry (ω b) = true then -1 else 1

omit [DecidableEq P] in
/-- **The selected factor has an `ε`-symmetric matrix.** -/
theorem density_sel_swap (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E) (L : ℕ)
    (ω : Choice (D.CL.T L)) (b : BlockAtom Bk J L) (hb : b ∈ Choice.support ω)
    (x y : reservedCut.Half → BlockLabel m₀ blk p L b) :
    lawDensity (entryFactor (D.FS.lam L b) (D.CL.ζ L b) (ω b)) (reservedCut.join y x) =
      selSign ω b * lawDensity (entryFactor (D.FS.lam L b) (D.CL.ζ L b) (ω b))
        (reservedCut.join x y) := by
  have hs : (ω b).isSome := (mem_filter.mp hb).2
  obtain ⟨⟨t, e⟩, he⟩ := Option.isSome_iff_exists.mp hs
  unfold selSign
  rw [he]
  cases e
  · simp only [entryFactor, isSkewEntry, Bool.false_eq_true, ↓reduceIte, one_mul]
    exact density_symPart _ x y
  · simp only [entryFactor, isSkewEntry, ↓reduceIte, neg_mul, one_mul]
    exact density_skewPart _ x y

omit [DecidableEq Bk] [∀ L, DecidableEq (J L)] [DecidableEq P] in
/-- **The parity of a selection**: `∏_{𝔅 ∈ X} ε_𝔅 = 1`. -/
theorem prod_selSign {L : ℕ} {T : BlockAtom Bk J L → Type} (ω : Choice T) (hω : IsSelection ω) :
    ∏ b : {b // b ∈ Choice.support ω}, selSign ω b.1 = 1 := by
  rw [Finset.prod_coe_sort (Choice.support ω) (fun b => selSign ω b)]
  unfold selSign
  rw [prod_ite, prod_const_one, mul_one, prod_const]
  have e : (Choice.support ω).filter (fun b => isSkewEntry (ω b) = true) =
      univ.filter fun b => isSkewEntry (ω b) = true := by
    ext b
    simp only [mem_filter, Choice.support, mem_univ, true_and, and_iff_right_iff_imp]
    intro hb
    cases h : ω b with
    | none => rw [h] at hb; simp [isSkewEntry] at hb
    | some v => rfl
  rw [e]
  exact hω.2.neg_one_pow

/-- **The star data at the selected marginals and signs.** -/
noncomputable def StarData.ofSel' {D : TheoremCBlock.ComparisonData a m₀ blk p pr h E} {L : ℕ}
    {ω : Choice (D.CL.T L)} (w : {b // b ∈ Choice.support ω} → ℝ)
    (Lb : ∀ b : {b // b ∈ Choice.support ω},
      (HalfB (m₀ := m₀) (blk := blk) (p := p) L (Choice.support ω) b → ℝ) →ₗ[ℝ]
        (HalfB (m₀ := m₀) (blk := blk) (p := p) L (Choice.support ω) b → ℝ))
    (ℓ ρ : {b // b ∈ Choice.support ω} → ℝ) : StarData D L ω :=
  StarData.ofSel w Lb ℓ ρ fun b => selSign ω b.1

omit [DecidableEq P] in
/-- **The record operators at the selected marginals have `ε`-symmetric kernels.** -/
theorem kern_Δhat_swap {D : TheoremCBlock.ComparisonData a m₀ blk p pr h E} {L : ℕ}
    {ω : Choice (D.CL.T L)} (S : StarData D L ω) (hmB : ∀ b, S.mB b = selMarg D L ω b.1)
    (b : {b // b ∈ Choice.support ω}) (x y : reservedCut.Half → BlockLabel m₀ blk p L b.1) :
    kern (S.mB b) (S.Δhat b) y x = selSign ω b.1 * kern (S.mB b) (S.Δhat b) x y := by
  have hp : PlusIn reservedCut (S.mB b) (S.zeta b) := by
    rw [hmB]
    exact plusIn_sel D L ω b.1 b.2
  unfold StarData.Δhat
  rw [kern_smul, kern_smul, kern_recOp hp, kern_recOp hp]
  rw [density_sel_swap D L ω b.1 b.2 x y]
  ring

omit [DecidableEq P] in
/-- **`StarOK` for a selection** at the selected marginals and signs: the inputs are `w > 0`,
`‖L_𝔅‖ ≤ ℓ_𝔅`, `‖Δ̂_𝔅 − L_𝔅‖ ≤ ρ_𝔅` ((N1)–(N3), `prop:signed-bounds`(b),(e)) and the
`ε_𝔅`-symmetry of the leading stars. -/
theorem starOK_sel {D : TheoremCBlock.ComparisonData a m₀ blk p pr h E} {L : ℕ}
    {ω : Choice (D.CL.T L)} (hω : IsSelection ω) {w : {b // b ∈ Choice.support ω} → ℝ}
    {Lb : ∀ b : {b // b ∈ Choice.support ω},
      (HalfB (m₀ := m₀) (blk := blk) (p := p) L (Choice.support ω) b → ℝ) →ₗ[ℝ]
        (HalfB (m₀ := m₀) (blk := blk) (p := p) L (Choice.support ω) b → ℝ)}
    {ℓ ρ : {b // b ∈ Choice.support ω} → ℝ}
    (hw : ∀ b, 0 < w b)
    (hL : ∀ b, OpNormLE (selMarg D L ω b.1) (Lb b) (ℓ b))
    (hE : ∀ b, OpNormLE (selMarg D L ω b.1)
      ((StarData.ofSel' (D := D) w Lb ℓ ρ).Δhat b - Lb b) (ρ b))
    (hLs : ∀ b x y, kern (selMarg D L ω b.1) (Lb b) y x =
      selSign ω b.1 * kern (selMarg D L ω b.1) (Lb b) x y) :
    StarOK (StarData.ofSel' (D := D) w Lb ℓ ρ) :=
  starOK_of hw hL hE (prod_selSign ω hω) hLs
    (kern_Δhat_swap (StarData.ofSel' (D := D) w Lb ℓ ρ) (fun _ => rfl))

end Paper

end Sarkozy.OpsCore
