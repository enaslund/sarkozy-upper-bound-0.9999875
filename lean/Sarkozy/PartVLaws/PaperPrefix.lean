module

public import Sarkozy.PartVLaws.FiberAssembly
public import Sarkozy.PartVLaws.Labellable
public import Sarkozy.CancellationSteps.Paper

@[expose] public section

/-!
# The prefix law `μ₀` for the paper's fixed coordinates (`def:cp1`, `def:construction`(b))

`paper/sections/18_design.tex`, `def:construction`(b) ("the reference is `μ = ⊗_𝔅 μ_𝔅`: at a
prefix atom `{p}` the square-clique law, on a middle block the five-type completion, on an upper
block the 25-state completion"); `paper/sections/06_lifts_sectors.tex`,
`def:record:functional`(a) (the fixed coordinates `𝒫₁ ∪ 𝒫₃`).

D1's `CancellationSteps.paperM0` fixes the coordinates of `μ₀`: `PaperJ0 = 𝒫₁ ∪ 𝒫₃`, the primes
`p < P₄` with `p ≡ 1 (4)` (modulus `p^{2𝔪}`) or `p ≡ 3 (4)`, `p ≥ Q₃` (modulus `p`). Its open
fields `μ₀`, `rp₀`, `inv₀`, `unif₀` (`MainAnchor.PaperData`) are built here from the **block
partition** of the class-three coordinates and the block laws:

* `paperAtomMap blockOf`: each prefix coordinate is an atom of its own (`.inl`), each class-three
  coordinate goes to its block `blockOf j : B` (`.inr`). `B` and `blockOf` are the partition data
  (`def:record:exact-blocks`, `def:record:upper-bands`(b)), arbitrary here.
* The **prefix atoms** are V1's `PartV.prefixLaw p` (`thm:density:iid-prefix`), carried to the
  modulus `paperM0 j` (equal to `p^{2𝔪}` only propositionally) by `ZMod.ringEquivCongr`
  (`prefixAtomLaw`). Their three properties are **proved** (`prefixAtom_rp`, `prefixAtom_inv`,
  `prefixAtom_unif`), with no hypothesis.
* The **block atoms** are supplied with their properties (`PaperBlockAtoms`): a law on
  `Slot → ∏_{j ∈ block} ℤ/p_j`, reflection positive at every cut of `𝔉`, square-affine invariant,
  with uniform marginals. For an upper block they are `upperBlockAtom`, from `upperBlock_R1R3`
  (given the band inputs); for a middle block V1's `middleBlockReference_*` results supply them in
  the same way (given V1's row and cap inputs).
* **`paperPrefixLaw`**, **`paperPrefix_rp`**, **`paperPrefix_inv`**, **`paperPrefix_unif`**: the
  four fields `μ₀`, `rp₀`, `inv₀`, `unif₀` of `MainAnchor.PaperData` for D1's `paperM0`, from the
  partition and the block atoms only.
-/

namespace Sarkozy.PartVLaws

open Finset Sarkozy.PartV Sarkozy.CancellationSteps

/-! ## The atoms of the paper's fixed coordinates -/

/-- The prefix coordinates `𝒫₁` (class one) among D1's fixed coordinates. -/
abbrev PrefixCoord : Type := {j : PaperJ0 // j.1 % 4 = 1}

/-- The atoms: one for each prefix coordinate, and the blocks `B` of the class-three coordinates. -/
abbrev PaperAtom (B : Type) : Type := PrefixCoord ⊕ B

/-- **The atom map** of a block assignment `blockOf` of the class-three coordinates. -/
def paperAtomMap {B : Type} (blockOf : PaperJ0 → B) (j : PaperJ0) : PaperAtom B :=
  if h : j.1 % 4 = 1 then .inl ⟨j, h⟩ else .inr (blockOf j)

variable {B : Type} (blockOf : PaperJ0 → B)

theorem paperAtomMap_inl {j : PaperJ0} {q : PrefixCoord} (h : paperAtomMap blockOf j = .inl q) :
    j = q.1 := by
  unfold paperAtomMap at h
  split_ifs at h with hj
  · exact congrArg Subtype.val (Sum.inl_injective h)

theorem paperAtomMap_inr {j : PaperJ0} {b : B} (h : paperAtomMap blockOf j = .inr b) :
    j.1 % 4 ≠ 1 := by
  unfold paperAtomMap at h
  split_ifs at h with hj
  exact hj

/-- The modulus of a prefix coordinate is `p^{2𝔪}`. -/
theorem paperM0_prefix (q : PrefixCoord) : paperM0 q.1 = q.1.1 ^ (2 * digitPairs) := by
  unfold paperM0 paperPP paperEP
  simp only [q.2, ↓reduceIte, prefixExponent]

/-- The modulus of a class-three coordinate is its prime. -/
theorem paperM0_cls3 {j : PaperJ0} (hj : j.1 % 4 ≠ 1) : paperM0 j = j.1 := by
  unfold paperM0 paperPP paperEP
  simp only [hj, ↓reduceIte, pow_one]

variable [Fintype B] [DecidableEq B]

omit [Fintype B] [DecidableEq B] in
/-- The modulus of every coordinate of a block is prime. -/
theorem paperM0_block_prime {b : B} (j : {j : PaperJ0 // paperAtomMap blockOf j = .inr b}) :
    (paperM0 j.1).Prime := by
  rw [paperM0_cls3 (paperAtomMap_inr blockOf j.2)]
  exact paperJ0_prime j.1

instance paperM0_block_fact {b : B} (j : {j : PaperJ0 // paperAtomMap blockOf j = .inr b}) :
    Fact (paperM0 j.1).Prime :=
  ⟨paperM0_block_prime blockOf j⟩

/-! ## The prefix atoms -/

section PrefixAtom

variable (q : PrefixCoord)

instance prefixCoord_fact : Fact (q.1.1).Prime := ⟨paperJ0_prime q.1⟩

/-- The one coordinate of a prefix atom. -/
def prefixPoint : {j : PaperJ0 // paperAtomMap blockOf j = .inl q} :=
  ⟨q.1, by simp only [paperAtomMap, q.2, ↓reduceDIte]⟩

omit [Fintype B] [DecidableEq B] in
theorem prefixPoint_unique (j : {j : PaperJ0 // paperAtomMap blockOf j = .inl q}) :
    j = prefixPoint blockOf q :=
  Subtype.ext (paperAtomMap_inl blockOf j.2)

/-- The ring isomorphisms from `ℤ/p^{2𝔪}` to the modulus of the coordinate. -/
noncomputable def prefixRingEquiv (j : {j : PaperJ0 // paperAtomMap blockOf j = .inl q}) :
    ZMod (q.1.1 ^ (2 * digitPairs)) ≃+* ZMod (paperM0 j.1) :=
  ZMod.ringEquivCongr (by rw [paperAtomMap_inl blockOf j.2, paperM0_prefix])

/-- **The prefix atom law**: V1's `prefixLaw p` (`thm:density:iid-prefix`) on the coordinate
`p ∈ 𝒫₁`, at the modulus `paperM0`. -/
noncomputable def prefixAtomLaw :
    FiniteLaw (Slot → AtomLabel paperM0 (paperAtomMap blockOf) (.inl q)) :=
  singletonAtomLaw (prefixRingEquiv blockOf q) (prefixLaw q.1.1)

omit [Fintype B] in
theorem prefixAtom_rp :
    TheoremC.FamilyReflectionPositive (signedIntegral (prefixAtomLaw blockOf q).weight) :=
  singletonAtomLaw_rp _ _ (prefixLaw_familyPositive q.1.1)

omit [Fintype B] in
theorem prefixAtom_unif : HasUniformMarginals (prefixAtomLaw blockOf q) :=
  singletonAtomLaw_unif _ (prefixPoint blockOf q) (prefixPoint_unique blockOf q) _
    (prefixLaw_uniform q.1.1)

omit [Fintype B] in
theorem prefixAtom_inv
    (α : ∀ j : {j : PaperJ0 // paperAtomMap blockOf j = .inl q}, (ZMod (paperM0 j.1))ˣ)
    (β : AtomLabel paperM0 (paperAtomMap blockOf) (.inl q))
    (hα : ∀ j, IsSquare (α j : ZMod (paperM0 j.1)))
    (H : (Slot → AtomLabel paperM0 (paperAtomMap blockOf) (.inl q)) → ℝ) :
    (prefixAtomLaw blockOf q).expect
        (fun z => H (fiberAffine paperM0 (paperAtomMap blockOf) α β z)) =
      (prefixAtomLaw blockOf q).expect H :=
  singletonAtomLaw_inv _ (prefixPoint blockOf q) (prefixPoint_unique blockOf q) _
    (fun u b hu H' => prefixLaw_invariant q.1.1 u b hu H') α β hα H

end PrefixAtom

/-! ## The block atoms -/

/-- **The block atoms** of a partition `blockOf`: for every block `b` a law on the labels of its
coordinates, with the three properties of (R1)–(R3) (`hyp:record:reference`): reflection
positivity at every cut of `𝔉`, square-affine invariance, uniform one-slot marginals. -/
structure PaperBlockAtoms where
  law : ∀ b : B, FiniteLaw (Slot → AtomLabel paperM0 (paperAtomMap blockOf) (.inr b))
  rp : ∀ b, TheoremC.FamilyReflectionPositive (signedIntegral (law b).weight)
  inv : ∀ b (α : ∀ j : {j : PaperJ0 // paperAtomMap blockOf j = .inr b}, (ZMod (paperM0 j.1))ˣ)
    (β : AtomLabel paperM0 (paperAtomMap blockOf) (.inr b)),
    (∀ j, IsSquare (α j : ZMod (paperM0 j.1))) →
      ∀ H : (Slot → AtomLabel paperM0 (paperAtomMap blockOf) (.inr b)) → ℝ,
        (law b).expect (fun z => H (fiberAffine paperM0 (paperAtomMap blockOf) α β z)) =
          (law b).expect H
  unif : ∀ b, HasUniformMarginals (law b)

/-! ## The prefix law -/

variable {blockOf}

/-- The atom laws: the prefix laws at the prefix coordinates, the given block laws on the blocks. -/
noncomputable def paperAtomLaw (Bk : PaperBlockAtoms blockOf) :
    ∀ a : PaperAtom B, FiniteLaw (Slot → AtomLabel paperM0 (paperAtomMap blockOf) a)
  | .inl q => prefixAtomLaw blockOf q
  | .inr b => Bk.law b

/-- **The prefix law `μ₀` of the paper's reference** (`def:cp1`, `def:construction`(b)): the
tensor of the prefix laws and the block laws, on `Slot → ResidueSpace paperM0`. -/
noncomputable def paperPrefixLaw (Bk : PaperBlockAtoms blockOf) :
    FiniteLaw (Slot → FourierArithmetic.ResidueSpace paperM0) :=
  fiberAssembly paperM0 (paperAtomMap blockOf) (paperAtomLaw Bk)

/-- **`rp₀`** (`MainAnchor.PaperData.rp₀`): `μ₀` is reflection positive at every cut of `𝔉`. -/
theorem paperPrefix_rp (Bk : PaperBlockAtoms blockOf) :
    TheoremC.FamilyReflectionPositive (signedIntegral (paperPrefixLaw Bk).weight) :=
  fiberAssembly_rp _ _ _ fun a => match a with
    | .inl q => prefixAtom_rp blockOf q
    | .inr b => Bk.rp b

/-- **`unif₀`**: `μ₀` has uniform one-slot marginals. -/
theorem paperPrefix_unif (Bk : PaperBlockAtoms blockOf) :
    HasUniformMarginals (paperPrefixLaw Bk) :=
  fiberAssembly_unif _ _ _ fun a => match a with
    | .inl q => prefixAtom_unif blockOf q
    | .inr b => Bk.unif b

/-- **`inv₀`**: `μ₀` is invariant under the square-affine maps of `ResidueSpace paperM0`. -/
theorem paperPrefix_inv (Bk : PaperBlockAtoms blockOf) (α : ∀ i, (ZMod (paperM0 i))ˣ)
    (β : FourierArithmetic.ResidueSpace paperM0) (hα : ∀ i, IsSquare ((α i : ZMod (paperM0 i))))
    (F : (Slot → FourierArithmetic.ResidueSpace paperM0) → ℝ) :
    (paperPrefixLaw Bk).expect (fun z => F (fun v => PaperFrame.piAffineEquiv paperM0 α β (z v))) =
      (paperPrefixLaw Bk).expect F :=
  fiberAssembly_inv _ _ _ (fun a => match a with
    | .inl q => fun α' β' hα' H => prefixAtom_inv blockOf q α' β' hα' H
    | .inr b => fun α' β' hα' H => Bk.inv b α' β' hα' H) α β hα F

/-! ## Upper blocks as block atoms -/

section Upper

variable {b : B}

omit [Fintype B] in
/-- **The square-affine invariance of a block law in the atom form**, from V1's form
(`χ_p(α_p) = 1`). -/
theorem blockAtom_inv_of_affine
    (μ : FiniteLaw (Slot → AtomLabel paperM0 (paperAtomMap blockOf) (.inr b)))
    (h : ∀ (α β : AtomLabel paperM0 (paperAtomMap blockOf) (.inr b)),
      (∀ j, quadraticChar (ZMod (paperM0 j.1)) (α j) = 1) →
      ∀ H : (Slot → AtomLabel paperM0 (paperAtomMap blockOf) (.inr b)) → ℝ,
        μ.expect (fun z => H (fun v j => α j * z v j + β j)) = μ.expect H)
    (α : ∀ j : {j : PaperJ0 // paperAtomMap blockOf j = .inr b}, (ZMod (paperM0 j.1))ˣ)
    (β : AtomLabel paperM0 (paperAtomMap blockOf) (.inr b))
    (hα : ∀ j, IsSquare (α j : ZMod (paperM0 j.1)))
    (H : (Slot → AtomLabel paperM0 (paperAtomMap blockOf) (.inr b)) → ℝ) :
    μ.expect (fun z => H (fiberAffine paperM0 (paperAtomMap blockOf) α β z)) = μ.expect H :=
  h (fun j => (α j : ZMod (paperM0 j.1))) β
    (fun j => (quadraticChar_one_iff_isSquare (α j).ne_zero).mpr (hα j)) H

end Upper

end Sarkozy.PartVLaws
