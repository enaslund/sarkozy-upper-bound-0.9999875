module

public import Sarkozy.PartV.LayerCut
public import Sarkozy.PartV.Acceptance
public import Sarkozy.Construction.CliqueIidPrefix

@[expose] public section

/-!
# The reference of the construction, atom by atom (`def:construction`(b))

`paper/sections/18_design.tex`, `def:construction`(b) and `tab:ranges`;
`paper/sections/30_density_moment_upgrade.tex`, `thm:density:iid-prefix` (the prefix of the
upgraded route); `paper/sections/25_upper_reference.tex`, `def:record:upper-bands`(b).

`def:construction`(b): the reference is `μ = ⊗_𝔅 μ_𝔅` with
* at a prefix atom `{p}` the square-clique law (`def:clique-law`) — in the upgraded route of the
  main theorem, the independent-draw clique law at `p ≥ 2¹⁶` and the square-clique law below
  (`thm:density:iid-prefix`): `prefixLaw`, `baselinePrefixLaw`;
* on a middle block the twelve-label five-type completion of `lem:front12:reference`, with the
  root of its piece (`def:record:parameters`(f)): `middleBlockLaw`;
* on an upper block the 25-state completion with the weights of its band: `upperBlockLaw`;
* at a tail atom the tail law (`def:tail-law`): `tailLaw`.

Entered as parameters (`ConstructionWeights`): the completion weights of the 33 pieces
(`tab:data:middle-weights`) and of the 310 bands (`def:record:upper-bands`(d)), and the coherent
dictionary `𝒟₃₉` (`imp:local:filtered-coherent`). The block partitions of the pieces and bands
(`def:record:exact-blocks`(c),(d), `def:record:upper-bands`(b)) enter through the block
structures `MiddleBlock`, `UpperBlock`, whose fields are the properties every block of those
partitions has.

Proved: every atom law of the construction is a probability law with uniform one-slot marginals
(`prefixLaw_uniform`, `middleBlockLaw_uniform`, `upperBlockLaw_uniform`, `tailLaw_uniform`); the
prefix law is reflection positive at the seven sorting cuts (`prefixLaw_slotPositive`); the middle
law is positive at the second-coordinate chamber cuts (`middleBlockLaw_secondCut_positive`).
-/

namespace Sarkozy.PartV

open Finset Sarkozy.Labellings

/-! ## Prefix atoms -/

section Prefix

variable (p : ℕ) [Fact p.Prime]

/-- **The baseline prefix law** (`def:construction`(b), `def:clique-law`): the square-clique law
with `𝔪 = 8192` digit pairs on `ℤ/p^{2𝔪}ℤ`. -/
noncomputable def baselinePrefixLaw : FiniteLaw (Slot → ZMod (p ^ (2 * digitPairs))) :=
  cliqueLaw p digitPairs

/-- **The prefix law of the upgraded route** (`thm:density:iid-prefix`): for `p ≥ 2¹⁶`, 72
conditionally independent uniform draws from the random square clique; for `p < 2¹⁶`, the
square-clique law of `def:clique-law`. -/
noncomputable def prefixLaw : FiniteLaw (Slot → ZMod (p ^ (2 * digitPairs))) :=
  if 2 ^ 16 ≤ p then cliqueIidLaw p digitPairs else cliqueLaw p digitPairs

theorem prefixLaw_uniform : HasUniformMarginals (prefixLaw p) := by
  unfold prefixLaw
  split_ifs
  · exact cliqueIidLaw_uniformMarginals p digitPairs
  · exact cliqueLaw_uniformMarginals p digitPairs

/-- **The prefix law is reflection positive at the seven sorting cuts**
(`thm:density:iid-prefix`(a), `lem:frontier:iidlocal`). -/
theorem prefixLaw_slotPositive : SlotReflectionPositive (signedIntegral (prefixLaw p).weight) := by
  unfold prefixLaw
  split_ifs
  · exact cliqueIidLaw_slotReflectionPositive p digitPairs
  · exact cliqueLaw_slotReflectionPositive p digitPairs

end Prefix

/-! ## Upper blocks (`def:record:upper-bands`(b)) -/

/-- The band `i` as an interval `[X, Y)` (`upperBands`). -/
def bandOf (i : Fin 310) : ℕ × ℕ := upperBands.getD i.val (0, 0)

/-- **An upper block** (`def:record:upper-bands`(b)): a nonempty set of class-three primes of one
band, of logarithmic length at most the band budget `L_band ≤ 886`. The cells and the recorded
cardinalities `n_j` of each band are data not entered here. -/
structure UpperBlock where
  band : Fin 310
  primes : Finset ℕ
  nonempty : primes.Nonempty
  prime : ∀ p ∈ primes, p.Prime
  class3 : ∀ p ∈ primes, p % 4 = 3
  inBand : ∀ p ∈ primes, (bandOf band).1 ≤ p ∧ p < (bandOf band).2
  bandBudget : ℕ
  bandBudget_le : bandBudget ≤ 886
  budget : ∑ p ∈ primes, Real.log p ≤ bandBudget

/-- The primes of an upper block, as a finite type. -/
abbrev UpperBlock.Idx (B : UpperBlock) : Type := {p // p ∈ B.primes}

instance (B : UpperBlock) (p : B.Idx) : Fact (p.1).Prime := ⟨B.prime p.1 p.2⟩

/-- The prime labelling of an upper block. -/
abbrev UpperBlock.pr (B : UpperBlock) : B.Idx → ℕ := fun p => p.1

/-- `r = b_𝔅^{-1/2}`, `b_𝔅` the least prime of the block. -/
noncomputable def UpperBlock.r (B : UpperBlock) : ℝ :=
  ((B.primes.min' B.nonempty : ℕ) : ℝ) ^ (-(1 / 2 : ℝ))

theorem UpperBlock.r_nonneg (B : UpperBlock) : 0 ≤ B.r := Real.rpow_nonneg (Nat.cast_nonneg _) _

/-! ## The weights of the construction -/

/-- The prime labelling of a middle block. -/
abbrev MiddleBlock.pr (B : MiddleBlock) : B.Idx → ℕ := fun p => p.1

/-- **The recorded data of the construction that are entered as parameters**: the completion
weights of the 33 middle pieces and of the 310 upper bands, and the coherent dictionary `𝒟₃₉`. -/
structure ConstructionWeights where
  middle : Fin 33 → MiddleWeights
  upper : Fin 310 → UpperWeights
  D39 : Dictionary

/-! ## The atom laws -/

/-- **The root of a middle block** (`def:record:parameters`(f), `def:construction`(b)): uniform on
the pieces below `2³⁰`, the individual-square positive root on the six pieces from `2³⁰` to
`2⁴⁰`, the coherent root (with the dictionary of `C`) on `[2⁴⁵, P₃)`. -/
noncomputable def middleBlockRoot (C : ConstructionWeights) (B : MiddleBlock)
    (hne : MiddleNonempty B.pr) : FiniteLaw (ZMod 6 × Fin 2 → BlockLabel B.pr) :=
  match pieceRoot B.piece with
  | .uniform => uniformRoot B.pr hne
  | .individualSquare u => individualBlockRoot B.pr u hne.L2
  | .coherent u η =>
      if hη : 0 < η then coherentBlockRoot B.pr C.D39 u hη hne.L2 else uniformRoot B.pr hne

theorem middleBlockRoot_vertex_uniform (C : ConstructionWeights) (B : MiddleBlock)
    (hne : MiddleNonempty B.pr) (o : ZMod 6 × Fin 2) (g : BlockLabel B.pr → ℝ) :
    (middleBlockRoot C B hne).expect (fun y => g (y o)) =
      (FiniteLaw.uniform (BlockLabel B.pr)).expect g := by
  unfold middleBlockRoot
  split
  · exact uniformRoot_vertex_uniform B.pr hne o g
  · exact individualBlockRoot_vertex_uniform B.pr _ hne.L2 o g
  · split_ifs with hη
    · exact coherentBlockRoot_vertex_uniform B.pr C.D39 _ hη hne.L2 o g
    · exact uniformRoot_vertex_uniform B.pr hne o g

/-- **The reference law of a middle block** (`def:construction`(b), `lem:front12:reference`). -/
noncomputable def middleBlockLaw (C : ConstructionWeights) (B : MiddleBlock)
    (hne : MiddleNonempty B.pr) : FiniteLaw (Slot → BlockLabel B.pr) :=
  middleBlockReference B.pr hne (middleBlockRoot C B hne) (C.middle B.piece) B.r_nonneg

/-- **The reference law of an upper block** (`def:construction`(b), `def:upper-reference`). -/
noncomputable def upperBlockLaw (C : ConstructionWeights) (B : UpperBlock)
    (hne : UpperNonempty B.pr) : FiniteLaw (Slot → BlockLabel B.pr) :=
  upperBlockReference B.pr hne (C.upper B.band) B.r_nonneg

/-- **Every middle block law has uniform one-slot marginals**, on every piece (uniform,
individual-square and coherent roots). -/
theorem middleBlockLaw_uniform (C : ConstructionWeights) (B : MiddleBlock)
    (hne : MiddleNonempty B.pr) : HasUniformMarginals (middleBlockLaw C B hne) :=
  middleBlockReference_uniform B.pr hne _ (middleBlockRoot_vertex_uniform C B hne) _ _

/-- **Every middle block law is positive at the chamber cuts of the second coordinate.** -/
theorem middleBlockLaw_secondCut_positive (C : ConstructionWeights) (B : MiddleBlock)
    (hne : MiddleNonempty B.pr) (a : Chamber) :
    (secondChamberCut a).Positive (signedIntegral (middleBlockLaw C B hne).weight) :=
  middleReference_secondCut_positive _ _ B.r_nonneg a

/-- **Every upper block law has uniform one-slot marginals.** -/
theorem upperBlockLaw_uniform (C : ConstructionWeights) (B : UpperBlock)
    (hne : UpperNonempty B.pr) : HasUniformMarginals (upperBlockLaw C B hne) :=
  upperBlockReference_uniform B.pr hne _ _

/-- **The primes of an upper block are upper primes.** -/
theorem UpperBlock.isUpperPrime (B : UpperBlock) {p : ℕ} (hp : p ∈ B.primes) : IsUpperPrime p := by
  refine ⟨B.prime p hp, B.class3 p hp, ?_, ?_⟩
  · have h := (B.inBand p hp).1
    have hP : P3 ≤ (bandOf B.band).1 := by
      generalize B.band = i
      revert i
      unfold bandOf upperBands bandsA bandsB bandsC bandsD bandsDExponents P3
      decide +kernel
    omega
  · have h := (B.inBand p hp).2
    have hP : (bandOf B.band).2 ≤ P4 := by
      generalize B.band = i
      revert i
      unfold bandOf upperBands bandsA bandsB bandsC bandsD bandsDExponents P4
      decide +kernel
    omega

end Sarkozy.PartV
