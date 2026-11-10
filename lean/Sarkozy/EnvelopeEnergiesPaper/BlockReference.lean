module

public import Sarkozy.EnvelopeEnergiesPaper.BlockCRT
public import Sarkozy.Structured.AffineInvariance
public import Sarkozy.PaperFrame.StepInvariance

@[expose] public section

/-!
# The block reference laws in cyclic coordinates: (R2), (R3) and the moments under the CRT

`hyp:record:reference` (R2), (R3) for the block laws `μ₀ β` (K0's `TheoremCBlock.Reference`, fields
`rp₀`, `inv₀`, `rpp`, `invp`) and the moment inputs `L^{72/ϑ}` of `lem:density:coupled` are
stated on the block alphabets `BlockRes β`. The density chain asks them on the cyclic coordinates
`ℤ/D_β` of `BlockCRT`. This file carries them through the CRT isomorphism:

* `pullFiniteLaw`, `expect_pullFiniteLaw`, `pullLaw_signedIntegral`: probability laws read through
  an alphabet equivalence;
* `positive_pullLaw`, `slotReflectionPositive_pullLaw`: (R2) is preserved;
* `mixedLpBound_pull`, `mixedLpBound_variationLaw_pull`: unit mixed `L^q` bounds are preserved
  (the uniform law of the alphabet is preserved by any bijection);
* `crtRef`, `crtLaws_blockRefLaws`: the reference of the block atoms in cyclic coordinates;
* **`crtRef_squareAffineInvariant`**: (R3) of the block laws (square units acting coordinate by
  coordinate on `BlockRes β`) gives (R3) on `ℤ/D_β` (square units of `ℤ/D_β`), because the CRT
  map is a ring isomorphism.
-/

open Finset Function
open scoped BigOperators

namespace Sarkozy.EnvelopeEnergiesPaper

open Sarkozy.FourierArithmetic Sarkozy.Functional Sarkozy.PaperFrame Sarkozy.BlockFrame
  Sarkozy.Structured

section Pull

variable {X X' : Type*} [Fintype X] [DecidableEq X] [Fintype X'] [DecidableEq X']

/-- A probability law on `Slot → X` read on `Slot → X'` through `e : X' ≃ X`. -/
noncomputable def pullFiniteLaw (e : X' ≃ X) (μ : FiniteLaw (Slot → X)) :
    FiniteLaw (Slot → X') where
  weight y := μ.weight (fun v => e (y v))
  nonneg _ := μ.nonneg _
  total := by
    rw [← μ.total]
    exact Fintype.sum_equiv (Equiv.arrowCongr (Equiv.refl Slot) e) _ _ fun y => rfl

omit [DecidableEq X] [DecidableEq X'] in
theorem expect_pullFiniteLaw (e : X' ≃ X) (μ : FiniteLaw (Slot → X)) (G : (Slot → X') → ℝ) :
    (pullFiniteLaw e μ).expect G = μ.expect (fun x => G (fun v => e.symm (x v))) := by
  unfold FiniteLaw.expect
  refine Fintype.sum_equiv (Equiv.arrowCongr (Equiv.refl Slot) e) _ _ fun y => ?_
  simp [pullFiniteLaw, Equiv.arrowCongr, Function.comp_def]

omit [DecidableEq X] [DecidableEq X'] in
/-- The pulled signed integral is the signed integral of the pulled law. -/
theorem pullLaw_signedIntegral (e : X' ≃ X) (μ : FiniteLaw (Slot → X)) :
    pullLaw e (signedIntegral μ.weight) = signedIntegral (pullFiniteLaw e μ).weight := by
  apply LinearMap.ext
  intro G
  rw [pullLaw_apply]
  exact (expect_pullFiniteLaw e μ G).symm

omit [Fintype X] [DecidableEq X] [Fintype X'] [DecidableEq X'] in
/-- Reflection positivity at a cut is preserved by relabelling the alphabet. -/
theorem positive_pullLaw (c : ReflectionCut Slot) (e : X' ≃ X)
    {Λ : ((Slot → X) → ℝ) →ₗ[ℝ] ℝ} (h : c.Positive Λ) : c.Positive (pullLaw e Λ) where
  symmetric F G := by
    unfold ReflectionCut.form
    rw [pullLaw_apply, pullLaw_apply]
    exact h.symmetric (fun x => F (fun v => e.symm (x v))) (fun x => G (fun v => e.symm (x v)))
  nonneg F := by
    unfold ReflectionCut.form
    rw [pullLaw_apply]
    exact h.nonneg (fun x => F (fun v => e.symm (x v)))

omit [Fintype X] [DecidableEq X] [Fintype X'] [DecidableEq X'] in
/-- (R2) at the sorting cuts is preserved by relabelling the alphabet. -/
theorem slotReflectionPositive_pullLaw (e : X' ≃ X) {Λ : ((Slot → X) → ℝ) →ₗ[ℝ] ℝ}
    (h : SlotReflectionPositive Λ) : SlotReflectionPositive (pullLaw e Λ) :=
  fun c hc => positive_pullLaw c e (h c hc)

omit [DecidableEq X] [DecidableEq X'] in
/-- Unit mixed `L^q` bounds are preserved by relabelling the alphabet. -/
theorem mixedLpBound_pull [Nonempty X] [Nonempty X'] (e : X' ≃ X) (ν : FiniteLaw (Slot → X))
    (ν' : FiniteLaw (Slot → X')) (hw : ∀ y, ν'.weight y = ν.weight (fun v => e (y v)))
    {q C : ℝ} (h : MixedLpBound ν q C) : MixedLpBound ν' q C := by
  intro f
  have h1 : ν'.expect (fun z => ∏ v, f v (z v)) =
      ν.expect (fun x => ∏ v, f v (e.symm (x v))) := by
    unfold FiniteLaw.expect
    refine Fintype.sum_equiv (Equiv.arrowCongr (Equiv.refl Slot) e) _ _ fun y => ?_
    simp [hw, Equiv.arrowCongr, Function.comp_def]
  have h2 : ∀ v, (FiniteLaw.uniform X').lpNorm q (f v) =
      (FiniteLaw.uniform X).lpNorm q (fun x => f v (e.symm x)) := by
    intro v
    unfold FiniteLaw.lpNorm FiniteLaw.moment
    rw [FiniteLaw.expect_uniform, FiniteLaw.expect_uniform, Fintype.card_congr e]
    congr 2
    exact Fintype.sum_equiv e _ _ fun y => by simp
  rw [h1]
  simp only [h2]
  exact h (fun v x => f v (e.symm x))

/-- The moment inputs `hatom` of the density chain transfer through the relabelling: unit mixed
`L^q` of `|Λ|/‖Λ‖` gives the same for the pulled law. -/
theorem mixedLpBound_variationLaw_pull [Nonempty X] [Nonempty X'] (e : X' ≃ X)
    (Λ : ((Slot → X) → ℝ) →ₗ[ℝ] ℝ) {q C : ℝ}
    (h : ∀ hb : 0 < totalVariation (lawDensity Λ), MixedLpBound (variationLaw _ hb) q C)
    (hb' : 0 < totalVariation (lawDensity (pullLaw e Λ))) :
    MixedLpBound (variationLaw _ hb') q C := by
  have htv : totalVariation (lawDensity (pullLaw e Λ)) = totalVariation (lawDensity Λ) :=
    sum_abs_lawDensity_pullLaw e Λ
  have hb : 0 < totalVariation (lawDensity Λ) := htv ▸ hb'
  refine mixedLpBound_pull e (variationLaw _ hb) (variationLaw _ hb') (fun y => ?_) (h hb)
  simp only [variationLaw, htv, lawDensity_pullLaw]

end Pull

/-! ## The reference of the block atoms in cyclic coordinates -/

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] (blk : J₀ → Bk)
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] (p : ∀ L, J L → ℕ)
  [∀ L j, NeZero (p L j)]

/-- The reference laws of the atoms as probability laws on their alphabets. -/
noncomputable def blockRefLaw (μ₀ : ∀ β, FiniteLaw (Slot → BlockRes m₀ blk β))
    (μp : ∀ (q : ℕ) [NeZero q], FiniteLaw (Slot → ZMod q)) (L : ℕ) :
    ∀ b : BlockAtom Bk J L, FiniteLaw (Slot → BlockLabel m₀ blk p L b)
  | .inl β => μ₀ β
  | .inr j => μp (p L j)

omit [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] [Fintype Bk] in
theorem blockRefLaws_eq (μ₀ : ∀ β, FiniteLaw (Slot → BlockRes m₀ blk β))
    (μp : ∀ (q : ℕ) [NeZero q], FiniteLaw (Slot → ZMod q)) (L : ℕ) (b : BlockAtom Bk J L) :
    blockRefLaws m₀ blk p μ₀ μp L b = signedIntegral (blockRefLaw blk p μ₀ μp L b).weight := by
  cases b <;> rfl

/-- The reference `μ_𝔟` of the block atoms in cyclic coordinates: `μ₀ β` read on `ℤ/D_β`,
`μ_{p_j}` at the tail primes. -/
noncomputable def crtRef (h0 : Pairwise fun i j => (m₀ i).Coprime (m₀ j))
    (μ₀ : ∀ β, FiniteLaw (Slot → BlockRes m₀ blk β))
    (μp : ∀ (q : ℕ) [NeZero q], FiniteLaw (Slot → ZMod q)) (L : ℕ) :
    ∀ b : BlockAtom Bk J L, FiniteLaw (Slot → ZMod (crtModuli m₀ blk p L b)) :=
  fun b => pullFiniteLaw (crtAtomEquiv blk h0 L b) (blockRefLaw blk p μ₀ μp L b)

omit [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] [Fintype Bk] in
/-- The reference read on the cyclic coordinates is `crtRef`. -/
theorem crtLaws_blockRefLaws (h0 : Pairwise fun i j => (m₀ i).Coprime (m₀ j))
    (μ₀ : ∀ β, FiniteLaw (Slot → BlockRes m₀ blk β))
    (μp : ∀ (q : ℕ) [NeZero q], FiniteLaw (Slot → ZMod q)) (L : ℕ) (b : BlockAtom Bk J L) :
    crtLaws blk h0 L (blockRefLaws m₀ blk p μ₀ μp L) b =
      signedIntegral (crtRef blk p h0 μ₀ μp L b).weight := by
  unfold crtLaws crtRef
  rw [blockRefLaws_eq, pullLaw_signedIntegral]

omit [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] [Fintype Bk] in
/-- (R2) of the block laws and of the tail laws gives (R2) of `crtRef`. -/
theorem crtRef_slotReflectionPositive (h0 : Pairwise fun i j => (m₀ i).Coprime (m₀ j))
    (μ₀ : ∀ β, FiniteLaw (Slot → BlockRes m₀ blk β))
    (μp : ∀ (q : ℕ) [NeZero q], FiniteLaw (Slot → ZMod q)) (L : ℕ)
    (rp₀ : ∀ β, SlotReflectionPositive (signedIntegral (μ₀ β).weight))
    (rpp : ∀ j, SlotReflectionPositive (signedIntegral (μp (p L j)).weight))
    (b : BlockAtom Bk J L) :
    SlotReflectionPositive (signedIntegral (crtRef blk p h0 μ₀ μp L b).weight) := by
  rw [← crtLaws_blockRefLaws]
  unfold crtLaws
  apply slotReflectionPositive_pullLaw
  rcases b with β | j
  · exact rp₀ β
  · exact rpp j

omit [Fintype Bk] in
/-- (R3) of one block law through `ℤ/D_β ≃ BlockRes β`: square-affine maps of `ℤ/D_β` act on
`BlockRes β` coordinate by coordinate through the CRT ring isomorphism. -/
theorem pullFiniteLaw_block_squareAffine (h0 : Pairwise fun i j => (m₀ i).Coprime (m₀ j))
    (β : Bk) (μ : FiniteLaw (Slot → BlockRes m₀ blk β))
    (inv : ∀ (a : ∀ i, (ZMod (blockModuli m₀ blk β i))ˣ) (b : BlockRes m₀ blk β),
      (∀ i, IsSquare ((a i : ZMod (blockModuli m₀ blk β i)))) →
        ∀ F : (Slot → BlockRes m₀ blk β) → ℝ,
          μ.expect (fun z => F (fun v => piAffineEquiv (blockModuli m₀ blk β) a b (z v))) =
            μ.expect F)
    (r t : ZMod (∏ i, blockModuli m₀ blk β i)) (hu : IsUnit r) (hs : IsSquare r)
    (F : (Slot → ZMod (∏ i, blockModuli m₀ blk β i)) → ℝ) :
    (pullFiniteLaw (ZMod.prodEquivPi (blockModuli m₀ blk β)
        (blockModuli_pairwise blk h0 β)).toEquiv μ).expect (fun w => F (fun v => r * w v + t)) =
      (pullFiniteLaw (ZMod.prodEquivPi (blockModuli m₀ blk β)
        (blockModuli_pairwise blk h0 β)).toEquiv μ).expect F := by
  rw [expect_pullFiniteLaw, expect_pullFiniteLaw]
  set e := ZMod.prodEquivPi (blockModuli m₀ blk β) (blockModuli_pairwise blk h0 β) with he
  change μ.expect (fun x => F (fun v => r * e.symm (x v) + t)) =
    μ.expect (fun x => F (fun v => e.symm (x v)))
  have hui : ∀ i, IsUnit (e r i) := fun i => (hu.map e).map (Pi.evalRingHom _ i)
  let a : ∀ i, (ZMod (blockModuli m₀ blk β i))ˣ := fun i => (hui i).unit
  have ha : ∀ i, (a i : ZMod (blockModuli m₀ blk β i)) = e r i := fun i => (hui i).unit_spec
  have hsq : ∀ i, IsSquare ((a i : ZMod (blockModuli m₀ blk β i))) := by
    intro i
    obtain ⟨s, hs'⟩ := hs
    exact ⟨e s i, by rw [ha i, hs', map_mul, Pi.mul_apply]⟩
  have key : ∀ x : BlockRes m₀ blk β,
      e.symm (piAffineEquiv (blockModuli m₀ blk β) a (e t) x) = r * e.symm x + t := by
    intro x
    apply e.injective
    rw [RingEquiv.apply_symm_apply, map_add, map_mul, RingEquiv.apply_symm_apply]
    funext i
    change (a i : ZMod (blockModuli m₀ blk β i)) * x i + e t i = _
    rw [ha i]
    rfl
  have h := inv a (e t) hsq (fun x => F (fun v => e.symm (x v)))
  simp only [key] at h
  exact h

omit [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] [Fintype Bk] in
/-- **(R3) through the CRT.** If every block law `μ₀ β` is invariant under the coordinatewise
square-affine maps `z_i ↦ a_i z_i + b_i` (`a_i` square units; K0's `Reference.inv₀`) and every tail
law under `z ↦ a z + b` (`Reference.invp`), then `crtRef` is square-affine invariant on the cyclic
coordinates `ℤ/D_β`, `ℤ/p_j` (`Structured.SquareAffineInvariant`), as the density chain asks. -/
theorem crtRef_squareAffineInvariant (h0 : Pairwise fun i j => (m₀ i).Coprime (m₀ j))
    (μ₀ : ∀ β, FiniteLaw (Slot → BlockRes m₀ blk β))
    (μp : ∀ (q : ℕ) [NeZero q], FiniteLaw (Slot → ZMod q)) (L : ℕ)
    (inv₀ : ∀ β (a : ∀ i, (ZMod (blockModuli m₀ blk β i))ˣ) (b : BlockRes m₀ blk β),
      (∀ i, IsSquare ((a i : ZMod (blockModuli m₀ blk β i)))) →
        ∀ F : (Slot → BlockRes m₀ blk β) → ℝ,
          (μ₀ β).expect (fun z => F (fun v => piAffineEquiv (blockModuli m₀ blk β) a b (z v))) =
            (μ₀ β).expect F)
    (invp : ∀ (q : ℕ) [NeZero q] (a : (ZMod q)ˣ) (b : ZMod q), IsSquare (a : ZMod q) →
      ∀ F : (Slot → ZMod q) → ℝ,
        (μp q).expect (fun z => F (fun v => affineEquiv a b (z v))) = (μp q).expect F) :
    SquareAffineInvariant (crtModuli m₀ blk p L) (crtRef blk p h0 μ₀ μp L) := by
  intro b r t hu hs F
  rcases b with β | j
  · exact pullFiniteLaw_block_squareAffine blk h0 β (μ₀ β) (inv₀ β) r t hu hs F
  · unfold crtRef
    rw [expect_pullFiniteLaw, expect_pullFiniteLaw]
    exact invp (p L j) hu.unit t hs F

end Sarkozy.EnvelopeEnergiesPaper
