module

public import Sarkozy.PartVLaws.PrefixAssembly
public import Sarkozy.PartV.Construction
public import Sarkozy.Construction.CliqueInvariance

@[expose] public section

/-!
# The prefix law `μ₀` from atom laws on the fibres of an atom map (`def:cp1`, `def:construction`(b))

`paper/sections/09_comparison_theorem.tex`, `def:cp1`; `paper/sections/18_design.tex`,
`def:construction`(b); `paper/sections/30_density_moment_upgrade.tex`, `thm:density:iid-prefix`;
`paper/sections/19_prefix.tex`, `def:clique-law`, `lem:frontier:iidlocal`(i),(ii).

`PrefixAssembly.lean` assembles `μ₀` over the index set `Σ_a I a`. The consumers fix the index set
of the prefix coordinates in advance (D1's `CancellationSteps.paperM0` on `PaperJ0 = 𝒫₁ ∪ 𝒫₃`).
Here the atoms are the fibres of an arbitrary **atom map** `κ : J₀ → A`, so no reindexing is
needed:
* `AtomLabel m₀ κ a = ∏_{j ∈ κ⁻¹(a)} ℤ/m₀(j)`, `fiberEquiv : ∏_a AtomLabel a ≃ ResidueSpace m₀`
  (definitional in both directions up to the fibre);
* **`fiberAssembly κ μ`** `= ⊗_a μ_a` carried to `ResidueSpace m₀`; `fiberAssembly_rp`,
  `fiberAssembly_inv`, `fiberAssembly_unif` are the fields `rp₀`, `inv₀`, `unif₀` of
  `TheoremC.Reference`, from the same properties of the atom laws.

**Atoms with one coordinate.** `singletonAtomLaw e μ` carries a law `μ` on `Slot → R` to the
atom labels of a one-point fibre through ring isomorphisms `e_j : R ≃+* ℤ/m₀(j)` (the moduli of
the consumers are equal to the natural ones only propositionally, e.g. `p^{e_p}` with `e_p` an
`if`). Reflection positivity, square-affine invariance and uniform marginals pass to it
(`singletonAtomLaw_rp`, `_inv`, `_unif`).

**The prefix laws** (`def:construction`(b), `thm:density:iid-prefix`): V1's `PartV.prefixLaw p`
is reflection positive at **every** cut of `𝔉` (`prefixLaw_familyPositive`; V1 proved the seven
sorting cuts), and invariant under `z ↦ a z + b` for every unit `a` that is a square
(`prefixLaw_invariant`, from `cliqueLaw_invariant`, `cliqueIidLaw_invariant`).
-/

namespace Sarkozy.PartVLaws

open Finset Sarkozy.PartV

/-! ## Fibre assembly -/

section Fibre

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] (m₀ : J₀ → ℕ) [∀ j, NeZero (m₀ j)]
  {A : Type} [Fintype A] [DecidableEq A] (κ : J₀ → A)

/-- The labels of the atom `a`: one residue for each coordinate of its fibre. -/
abbrev AtomLabel (a : A) : Type := ∀ j : {j : J₀ // κ j = a}, ZMod (m₀ j.1)

/-- **The atoms' labels are the residues of all the coordinates.** -/
def fiberEquiv : (∀ a, AtomLabel m₀ κ a) ≃ FourierArithmetic.ResidueSpace m₀ where
  toFun x j := x (κ j) ⟨j, rfl⟩
  invFun y _ j := y j.1
  left_inv x := by
    funext a j
    obtain ⟨j, rfl⟩ := j
    rfl
  right_inv _ := rfl

/-- **The prefix law from atom laws on the fibres of `κ`**: `μ₀ = ⊗_a μ_a`, carried to
`ResidueSpace m₀`. -/
noncomputable def fiberAssembly (μ : ∀ a, FiniteLaw (Slot → AtomLabel m₀ κ a)) :
    FiniteLaw (Slot → FourierArithmetic.ResidueSpace m₀) :=
  (FiniteLaw.tensor μ).map fun z v => fiberEquiv m₀ κ (z v)

theorem fiberAssembly_expect (μ : ∀ a, FiniteLaw (Slot → AtomLabel m₀ κ a))
    (F : (Slot → FourierArithmetic.ResidueSpace m₀) → ℝ) :
    (fiberAssembly m₀ κ μ).expect F =
      (FiniteLaw.tensor μ).expect (fun z => F (fun v => fiberEquiv m₀ κ (z v))) := by
  unfold fiberAssembly
  rw [FiniteLaw.expect_map]
  rfl

/-- **`Reference.rp₀`** for the fibre assembly. -/
theorem fiberAssembly_rp (μ : ∀ a, FiniteLaw (Slot → AtomLabel m₀ κ a))
    (hμ : ∀ a, TheoremC.FamilyReflectionPositive (signedIntegral (μ a).weight)) :
    TheoremC.FamilyReflectionPositive (signedIntegral (fiberAssembly m₀ κ μ).weight) := by
  intro c hc
  have ht := FiniteLaw.tensor_positive μ c (fun a => hμ a c hc)
  have heq : signedIntegral (fiberAssembly m₀ κ μ).weight =
      pushFunctional (signedIntegral (FiniteLaw.tensor μ).weight)
        (fun z v => fiberEquiv m₀ κ (z v)) := by
    refine LinearMap.ext fun F => ?_
    rw [← FiniteLaw.expect_eq_signedIntegral, fiberAssembly_expect]
    rfl
  rw [heq]
  exact FiveType.TwoCoord.positive_push_halfLocal c ht _ (fun x w => fiberEquiv m₀ κ (x w))
    (fun _ => rfl) (fun _ => rfl)

/-- **`Reference.unif₀`** for the fibre assembly. -/
theorem fiberAssembly_unif (μ : ∀ a, FiniteLaw (Slot → AtomLabel m₀ κ a))
    (hμ : ∀ a, HasUniformMarginals (μ a)) : HasUniformMarginals (fiberAssembly m₀ κ μ) := by
  intro v f
  rw [fiberAssembly_expect]
  have h := tensor_uniform_marginals μ hμ v (fun x => f (fiberEquiv m₀ κ x))
  rw [h]
  exact uniform_expect_equiv' (fiberEquiv m₀ κ) f

/-- The square-affine map of one atom, coordinatewise. -/
def fiberAffine {a : A} (α : ∀ j : {j : J₀ // κ j = a}, (ZMod (m₀ j.1))ˣ)
    (β : AtomLabel m₀ κ a) : (Slot → AtomLabel m₀ κ a) ≃ (Slot → AtomLabel m₀ κ a) where
  toFun z v j := (α j : ZMod (m₀ j.1)) * z v j + β j
  invFun z v j := ((α j)⁻¹ : (ZMod (m₀ j.1))ˣ) * (z v j - β j)
  left_inv z := by
    funext v j
    simp only [add_sub_cancel_right, ← mul_assoc, Units.inv_mul, one_mul]
  right_inv z := by
    funext v j
    simp only [← mul_assoc, Units.mul_inv, one_mul, sub_add_cancel]

/-- **`Reference.inv₀`** for the fibre assembly: square-affine invariance passes from the atoms. -/
theorem fiberAssembly_inv (μ : ∀ a, FiniteLaw (Slot → AtomLabel m₀ κ a))
    (hμ : ∀ a (α : ∀ j : {j : J₀ // κ j = a}, (ZMod (m₀ j.1))ˣ) (β : AtomLabel m₀ κ a),
      (∀ j, IsSquare (α j : ZMod (m₀ j.1))) → ∀ H : (Slot → AtomLabel m₀ κ a) → ℝ,
        (μ a).expect (fun z => H (fiberAffine m₀ κ α β z)) = (μ a).expect H)
    (α : ∀ j, (ZMod (m₀ j))ˣ) (β : FourierArithmetic.ResidueSpace m₀)
    (hα : ∀ j, IsSquare (α j : ZMod (m₀ j)))
    (F : (Slot → FourierArithmetic.ResidueSpace m₀) → ℝ) :
    (fiberAssembly m₀ κ μ).expect
        (fun z => F (fun v => PaperFrame.piAffineEquiv m₀ α β (z v))) =
      (fiberAssembly m₀ κ μ).expect F := by
  rw [fiberAssembly_expect, fiberAssembly_expect]
  let T : ∀ a, (Slot → AtomLabel m₀ κ a) ≃ (Slot → AtomLabel m₀ κ a) :=
    fun a => fiberAffine m₀ κ (fun j => α j.1) (fun j => β j.1)
  have hT : ∀ a y, (μ a).weight (T a y) = (μ a).weight y := fun a y =>
    weight_comp_of_expect (μ a) (T a) (fun H => hμ a _ _ (fun j => hα j.1) H) y
  have h := expect_tensor_comp μ T hT (fun z => F (fun v => fiberEquiv m₀ κ (z v)))
  refine Eq.trans ?_ h
  rfl

end Fibre

/-! ## Atoms with one coordinate -/

section Singleton

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ j, NeZero (m₀ j)]
  {A : Type} [DecidableEq A] {κ : J₀ → A}
  {R : Type} [CommRing R] [Fintype R]

/-- **A law on `Slot → R` carried to the labels of an atom** by ring isomorphisms
`e_j : R ≃+* ℤ/m₀(j)`, one for each coordinate of the fibre. -/
noncomputable def singletonAtomLaw {a : A} (e : ∀ j : {j : J₀ // κ j = a}, R ≃+* ZMod (m₀ j.1))
    (μ : FiniteLaw (Slot → R)) : FiniteLaw (Slot → AtomLabel m₀ κ a) :=
  μ.map fun z v j => e j (z v)

theorem singletonAtomLaw_expect {a : A} (e : ∀ j : {j : J₀ // κ j = a}, R ≃+* ZMod (m₀ j.1))
    (μ : FiniteLaw (Slot → R)) (H : (Slot → AtomLabel m₀ κ a) → ℝ) :
    (singletonAtomLaw e μ).expect H = μ.expect (fun z => H (fun v j => e j (z v))) := by
  unfold singletonAtomLaw
  rw [FiniteLaw.expect_map]
  rfl

/-- Reflection positivity passes to the atom law (the label map acts slot by slot). -/
theorem singletonAtomLaw_rp {a : A} (e : ∀ j : {j : J₀ // κ j = a}, R ≃+* ZMod (m₀ j.1))
    (μ : FiniteLaw (Slot → R))
    (hμ : TheoremC.FamilyReflectionPositive (signedIntegral μ.weight)) :
    TheoremC.FamilyReflectionPositive (signedIntegral (singletonAtomLaw e μ).weight) := by
  intro c hc
  have heq : signedIntegral (singletonAtomLaw e μ).weight =
      pushFunctional (signedIntegral μ.weight) (fun z v j => e j (z v)) := by
    refine LinearMap.ext fun F => ?_
    rw [← FiniteLaw.expect_eq_signedIntegral, singletonAtomLaw_expect]
    rfl
  rw [heq]
  exact FiveType.TwoCoord.positive_push_halfLocal c (hμ c hc) _ (fun x w j => e j (x w))
    (fun _ => rfl) (fun _ => rfl)

/-- The label map of a one-point fibre is a bijection. -/
def singletonLabelEquiv {a : A} (e : ∀ j : {j : J₀ // κ j = a}, R ≃+* ZMod (m₀ j.1))
    (j₀ : {j : J₀ // κ j = a}) (hS : ∀ j : {j : J₀ // κ j = a}, j = j₀) :
    R ≃ AtomLabel m₀ κ a where
  toFun x j := e j x
  invFun y := (e j₀).symm (y j₀)
  left_inv x := by simp
  right_inv y := by
    funext j
    obtain rfl := hS j
    simp

/-- Uniform marginals pass to the atom law of a one-point fibre. -/
theorem singletonAtomLaw_unif {a : A} (e : ∀ j : {j : J₀ // κ j = a}, R ≃+* ZMod (m₀ j.1))
    (j₀ : {j : J₀ // κ j = a}) (hS : ∀ j : {j : J₀ // κ j = a}, j = j₀) (μ : FiniteLaw (Slot → R))
    (hμ : HasUniformMarginals μ) : HasUniformMarginals (singletonAtomLaw e μ) := by
  intro v f
  rw [singletonAtomLaw_expect]
  have h := hμ v (fun x => f (singletonLabelEquiv e j₀ hS x))
  refine Eq.trans ?_ (h.trans (uniform_expect_equiv' (singletonLabelEquiv e j₀ hS) f))
  rfl

/-- Square-affine invariance passes to the atom law of a one-point fibre. -/
theorem singletonAtomLaw_inv {a : A} (e : ∀ j : {j : J₀ // κ j = a}, R ≃+* ZMod (m₀ j.1))
    (j₀ : {j : J₀ // κ j = a}) (hS : ∀ j : {j : J₀ // κ j = a}, j = j₀) (μ : FiniteLaw (Slot → R))
    (hμ : ∀ (u : Rˣ) (b : R), IsSquare (u : R) → ∀ H : (Slot → R) → ℝ,
      μ.expect (fun z => H (fun v => (u : R) * z v + b)) = μ.expect H)
    (α : ∀ j : {j : J₀ // κ j = a}, (ZMod (m₀ j.1))ˣ) (β : AtomLabel m₀ κ a)
    (hα : ∀ j, IsSquare (α j : ZMod (m₀ j.1))) (H : (Slot → AtomLabel m₀ κ a) → ℝ) :
    (singletonAtomLaw e μ).expect (fun z => H (fiberAffine m₀ κ α β z)) =
      (singletonAtomLaw e μ).expect H := by
  rw [singletonAtomLaw_expect, singletonAtomLaw_expect]
  -- the affine map on `R` that corresponds to `(α j₀, β j₀)`
  let u : Rˣ := (Units.map (e j₀).symm.toMonoidHom) (α j₀)
  have hu' : (u : R) = (e j₀).symm (α j₀ : ZMod (m₀ j₀.1)) := rfl
  have hu : IsSquare (u : R) := by
    obtain ⟨x, hx⟩ := hα j₀
    refine ⟨(e j₀).symm x, ?_⟩
    rw [hu', hx, map_mul]
  have hcomm : ∀ z : Slot → R, (fun v j => (α j : ZMod (m₀ j.1)) * e j (z v) + β j) =
      fun v j => e j ((u : R) * z v + (e j₀).symm (β j₀)) := by
    intro z
    funext v j
    obtain rfl := hS j
    rw [map_add, map_mul, hu', RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply]
  have := hμ u ((e j₀).symm (β j₀)) hu (fun z => H (fun v j => e j (z v)))
  refine Eq.trans ?_ this
  refine FiniteLaw.expect_congr _ fun z => ?_
  change H (fun v j => (α j : ZMod (m₀ j.1)) * e j (z v) + β j) = _
  rw [hcomm z]

end Singleton

/-! ## The prefix laws at every cut, and their invariance -/

section Prefix

variable (p : ℕ) [Fact p.Prime]

/-- The clique law is reflection positive at every cut of `𝔉` (`lem:frontier:iidlocal`(i), all the
chamber cuts of both coordinates and `ι`, not only the seven sorting cuts). -/
theorem cliqueLaw_familyPositive (ℓ : ℕ) :
    TheoremC.FamilyReflectionPositive (signedIntegral (cliqueLaw p ℓ).weight) := by
  intro c hc
  have : Nonempty (unitSquares p ℓ) :=
    ⟨⟨(unitSquares_nonempty p ℓ).choose, (unitSquares_nonempty p ℓ).choose_spec⟩⟩
  have h := chamberIid_positive_cut _ (FiniteLaw.uniform _).nonneg
    (affineLabelLaw (unitSquares p ℓ) (clique p ℓ) (clique_nonempty p ℓ))
  have heq : signedIntegral (cliqueLaw p ℓ).weight =
      chamberIid (FiniteLaw.uniform
        (AffineData (R := ZMod (p ^ (2 * ℓ))) (CliqueData p ℓ) (unitSquares p ℓ))).weight
        (affineLabelLaw (unitSquares p ℓ) (clique p ℓ) (clique_nonempty p ℓ)) :=
    signedIntegral_chamberIidLaw _ _
  rw [heq]
  rcases hc with ⟨a, rfl⟩ | ⟨a, rfl⟩ | rfl
  · exact h.1 a
  · exact h.2.1 a
  · exact h.2.2

/-- **The prefix law is reflection positive at every cut of `𝔉`** (`thm:density:iid-prefix`(a),
`lem:frontier:iidlocal`(i)). -/
theorem prefixLaw_familyPositive :
    TheoremC.FamilyReflectionPositive (signedIntegral (prefixLaw p).weight) := by
  unfold prefixLaw
  split_ifs
  · exact fun c _ => cliqueIidLaw_positive p digitPairs c
  · exact cliqueLaw_familyPositive p digitPairs

/-- A unit that is a square is a unit square. -/
theorem mem_unitSquares_of_isSquare {ℓ : ℕ} (u : (ZMod (p ^ (2 * ℓ)))ˣ)
    (hu : IsSquare (u : ZMod (p ^ (2 * ℓ)))) : (u : ZMod (p ^ (2 * ℓ))) ∈ unitSquares p ℓ := by
  obtain ⟨x, hx⟩ := hu
  have hxu : IsUnit x := by
    refine IsUnit.of_mul_eq_one (x * ((u⁻¹ : (ZMod (p ^ (2 * ℓ)))ˣ) : ZMod (p ^ (2 * ℓ)))) ?_
    rw [← mul_assoc, ← hx, Units.mul_inv]
  obtain ⟨w, rfl⟩ := hxu
  refine mem_image.mpr ⟨w, mem_univ _, ?_⟩
  rw [hx, Units.val_pow_eq_pow_val, sq]

/-- **(R3) for the prefix law**: invariance under `z ↦ u z + b` for every unit `u` that is a
square and every `b`. -/
theorem prefixLaw_invariant (u : (ZMod (p ^ (2 * digitPairs)))ˣ) (b : ZMod (p ^ (2 * digitPairs)))
    (hu : IsSquare (u : ZMod (p ^ (2 * digitPairs))))
    (H : (Slot → ZMod (p ^ (2 * digitPairs))) → ℝ) :
    (prefixLaw p).expect (fun z => H (fun v => (u : ZMod (p ^ (2 * digitPairs))) * z v + b)) =
      (prefixLaw p).expect H := by
  have hmem := mem_unitSquares_of_isSquare p u hu
  unfold prefixLaw
  split_ifs
  · exact cliqueIidLaw_invariant p digitPairs hmem b H
  · exact cliqueLaw_invariant digitPairs hmem b H

end Prefix

end Sarkozy.PartVLaws
