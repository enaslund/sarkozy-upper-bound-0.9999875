module

public import Sarkozy.Reflection.ChamberIid
public import Sarkozy.ProbabilityConstructions
public import Sarkozy.Energy
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

/-!
# The square-clique law (`def:clique-law`, `lem:frontier:iidlocal` (i), (ii))

`paper/sections/19_prefix.tex`. At a prime `p ≡ 1 (mod 4)` the reference law of the prefix atom
`{p}` draws, given random *clique data*, six labels (one per chamber of the first coordinate)
independently and uniformly from a random square clique `𝒞_p ⊆ ℤ/p^{2ℓ}ℤ`, applies a uniform
square-affine map `x ↦ s x + c`, and copies the label of chamber `u₀` to every slot
`(u₀, u₁, ℓ)`.

* `chamberIidLaw w ν` is the general construction as a `FiniteLaw` on `Slot → X`: shared data
  `ω ∼ w`, one label per first chamber drawn independently from `ν ω`. Its signed integral is
  `Sarkozy.chamberIid` (`signedIntegral_chamberIidLaw`), so it is reflection positive at all
  seven sorting cuts (`chamberIidLaw_slotReflectionPositive`); its one-slot marginal is the
  mixture `∑_ω w_ω ν_ω` (`chamberIidLaw_marginal`).
* `affineChamberLaw`: the label law is uniform on `s · C(d) + c` with data `d`, a multiplier `s`
  from a set of units and a uniform shift `c` of a finite ring. Its one-slot marginals are
  uniform (`affineChamberLaw_uniformMarginals`), whatever the sets `C(d)`.
* `cliqueLaw p ℓ` is `def:clique-law`: the ring `ℤ/p^{2ℓ}ℤ`, the data of `ℓ` digit pairs
  `(a_j, b_j)` with `χ(b_j - a_j) = 1` and digits `k_j, k'_j`, the clique
  `{∑_j p^{2j} x_j : x_j ∈ {a_j + p k_j, b_j + p k'_j}}`, and multipliers the unit squares.
  `cliqueLaw_slotReflectionPositive` and `cliqueLaw_uniformMarginals` are
  `lem:frontier:iidlocal` (i) at the seven sorting cuts and the marginal statement of (ii).

Not formalized here: the full invariance of (ii), the clique arithmetic (iii) (`2^ℓ` elements,
differences `p^{2j}` times a unit square), the exception masses (iv), (v), and (vi).
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace Sarkozy

variable {Ω X : Type*} [Fintype Ω] [Fintype X] [DecidableEq X]

/-- Shared data and one label per chamber: the base law on `Ω × (Chamber → X)`. -/
noncomputable def chamberBase (w : FiniteLaw Ω) (ν : Ω → FiniteLaw X) :
    FiniteLaw (Ω × (Chamber → X)) where
  weight q := w.weight q.1 * ∏ i, (ν q.1).weight (q.2 i)
  nonneg q := mul_nonneg (w.nonneg _) (prod_nonneg fun _ _ => (ν q.1).nonneg _)
  total := by
    rw [Fintype.sum_prod_type]
    have h1 : ∀ ω, ∑ y : Chamber → X, ∏ i, (ν ω).weight (y i) = 1 := by
      intro ω
      have h := Fintype.prod_sum (fun (_ : Chamber) (x : X) => (ν ω).weight x)
      simp only [(ν ω).total, prod_const_one] at h
      exact h.symm
    simp_rw [← mul_sum, h1, mul_one]
    exact w.total

/-- **Chamber pullback of independent labels**, as a finite law on the slots. -/
noncomputable def chamberIidLaw (w : FiniteLaw Ω) (ν : Ω → FiniteLaw X) : FiniteLaw (Slot → X) :=
  (chamberBase w ν).map fun q => q.2 ∘ firstChamber

theorem expect_chamberIidLaw (w : FiniteLaw Ω) (ν : Ω → FiniteLaw X) (f : (Slot → X) → ℝ) :
    (chamberIidLaw w ν).expect f =
      ∑ ω, w.weight ω * ∑ y : Chamber → X, (∏ i, (ν ω).weight (y i)) * f (y ∘ firstChamber) := by
  unfold chamberIidLaw
  rw [FiniteLaw.expect_map]
  unfold FiniteLaw.expect
  rw [Fintype.sum_prod_type]
  refine sum_congr rfl fun ω _ => ?_
  rw [mul_sum]
  refine sum_congr rfl fun y _ => ?_
  simp only [chamberBase, Function.comp_apply]
  ring

theorem signedIntegral_chamberIidLaw (w : FiniteLaw Ω) (ν : Ω → FiniteLaw X) :
    signedIntegral (chamberIidLaw w ν).weight = chamberIid w.weight ν := by
  apply LinearMap.ext
  intro f
  rw [← FiniteLaw.expect_eq_signedIntegral, expect_chamberIidLaw]
  unfold chamberIid
  rw [LinearMap.sum_apply]
  refine sum_congr rfl fun ω _ => ?_
  rfl

/-- **`lem:frontier:iidlocal`(i), structural form**: chamber pullbacks of independent labels are
reflection positive at all seven sorting cuts. -/
theorem chamberIidLaw_slotReflectionPositive (w : FiniteLaw Ω) (ν : Ω → FiniteLaw X) :
    SlotReflectionPositive (signedIntegral (chamberIidLaw w ν).weight) := by
  rw [signedIntegral_chamberIidLaw]
  exact chamberIid_slotReflectionPositive w.weight w.nonneg ν

/-- The one-slot marginal of a chamber pullback is the mixture of the label laws. -/
theorem chamberIidLaw_marginal (w : FiniteLaw Ω) (ν : Ω → FiniteLaw X) (v : Slot)
    (f : X → ℝ) :
    (chamberIidLaw w ν).expect (fun z => f (z v)) = ∑ ω, w.weight ω * (ν ω).expect f := by
  rw [expect_chamberIidLaw]
  refine sum_congr rfl fun ω _ => ?_
  congr 1
  set j := firstChamber v
  have hprod : ∀ y : Chamber → X, (∏ i, (ν ω).weight (y i)) * f ((y ∘ firstChamber) v) =
      ∏ i, ((ν ω).weight (y i) * (if i = j then f (y i) else 1)) := by
    intro y
    rw [prod_mul_distrib, prod_ite_eq' univ j (fun i => f (y i))]
    simp only [mem_univ, ↓reduceIte]
    rfl
  simp_rw [hprod]
  rw [← Fintype.prod_sum (fun (i : Chamber) (x : X) => (ν ω).weight x * (if i = j then f x else 1))]
  rw [prod_eq_single j]
  · unfold FiniteLaw.expect
    simp only [↓reduceIte]
  · intro i _ hij
    simp only [hij, ↓reduceIte, mul_one]
    exact (ν ω).total
  · intro h; exact absurd (mem_univ j) h

/-- Uniform marginals of a chamber pullback when the mixture of label laws is uniform. -/
theorem chamberIidLaw_uniformMarginals [Nonempty X] (w : FiniteLaw Ω) (ν : Ω → FiniteLaw X)
    (h : ∀ f : X → ℝ, ∑ ω, w.weight ω * (ν ω).expect f = (FiniteLaw.uniform X).expect f) :
    HasUniformMarginals (chamberIidLaw w ν) := fun v f => by
  rw [chamberIidLaw_marginal, h]

/-! ## Affine randomization -/

/-- The uniform probability on a nonempty finite set. -/
noncomputable def uniformOn (A : Finset X) (hA : A.Nonempty) : FiniteLaw X where
  weight x := if x ∈ A then 1 / (A.card : ℝ) else 0
  nonneg x := by split_ifs <;> positivity
  total := by
    rw [sum_ite_mem, univ_inter, sum_const, nsmul_eq_mul]
    have : (A.card : ℝ) ≠ 0 := by exact_mod_cast (card_pos.mpr hA).ne'
    field_simp

theorem expect_uniformOn (A : Finset X) (hA : A.Nonempty) (f : X → ℝ) :
    (uniformOn A hA).expect f = (∑ x ∈ A, f x) / A.card := by
  unfold FiniteLaw.expect uniformOn
  simp only [ite_mul, zero_mul]
  rw [sum_ite_mem, univ_inter, sum_div]
  exact sum_congr rfl fun x _ => by ring

variable {R D : Type*} [CommRing R] [Fintype R] [DecidableEq R] [Fintype D]

/-- The data of an affine-randomized chamber law: shared data `d`, a multiplier `s` from a set
of units, a shift `c`. -/
abbrev AffineData (D : Type*) (S : Finset R) := D × S × R

/-- The label law `uniform(s · C(d) + c)`. -/
noncomputable def affineLabelLaw (S : Finset R) (C : D → Finset R) (hC : ∀ d, (C d).Nonempty)
    (q : AffineData (R := R) D S) : FiniteLaw R :=
  uniformOn ((C q.1).image fun y => (q.2.1 : R) * y + q.2.2) ((hC q.1).image _)

/-- **The affine-randomized chamber law**: data, multiplier and shift uniform; given them, one
label per first chamber uniform on `s · C(d) + c`. -/
noncomputable def affineChamberLaw [Nonempty D] (S : Finset R) (hS : S.Nonempty)
    (C : D → Finset R) (hC : ∀ d, (C d).Nonempty) : FiniteLaw (Slot → R) :=
  have : Nonempty S := ⟨⟨hS.choose, hS.choose_spec⟩⟩
  chamberIidLaw (FiniteLaw.uniform (AffineData (R := R) D S)) (affineLabelLaw S C hC)

/-- **Uniform marginals of the affine-randomized law**, for any sets `C(d)` and any set of unit
multipliers. -/
theorem affineChamberLaw_uniformMarginals [Nonempty D] (S : Finset R) (hS : S.Nonempty)
    (hSu : ∀ s ∈ S, IsUnit s) (C : D → Finset R) (hC : ∀ d, (C d).Nonempty) :
    HasUniformMarginals (affineChamberLaw S hS C hC) := by
  have : Nonempty S := ⟨⟨hS.choose, hS.choose_spec⟩⟩
  unfold affineChamberLaw
  apply chamberIidLaw_uniformMarginals
  intro f
  -- every label law averages `f` over `s·C(d) + c`; averaging over `c` gives the uniform mean
  have hinj : ∀ (s : S) (c : R), Function.Injective fun y : R => (s : R) * y + c := by
    intro s c y y' h
    have hu := hSu s s.2
    have : (s : R) * y = (s : R) * y' := by simpa using h
    exact hu.mul_left_cancel this
  have hlabel : ∀ q : AffineData (R := R) D S, (affineLabelLaw S C hC q).expect f =
      (∑ y ∈ C q.1, f ((q.2.1 : R) * y + q.2.2)) / (C q.1).card := by
    intro q
    unfold affineLabelLaw
    rw [expect_uniformOn, sum_image (fun y _ y' _ h => hinj q.2.1 q.2.2 h),
      card_image_of_injective _ (hinj q.2.1 q.2.2)]
  simp only [FiniteLaw.expect_uniform, hlabel]
  have hw : ∀ q, (FiniteLaw.uniform (AffineData (R := R) D S)).weight q =
      ((Fintype.card D : ℝ) * (Fintype.card S * Fintype.card R))⁻¹ := by
    intro q
    change (Fintype.card (AffineData (R := R) D S) : ℝ)⁻¹ = _
    rw [Fintype.card_prod, Fintype.card_prod]
    push_cast
    ring
  simp only [hw]
  -- sum over the data, the multiplier and the shift
  have hshift : ∀ (s : S) (y : R), ∑ c : R, f ((s : R) * y + c) = ∑ x : R, f x := fun s y =>
    Fintype.sum_equiv (Equiv.addLeft ((s : R) * y)) _ _ fun _ => rfl
  have hinner : ∀ (d : D) (s : S), ∑ c : R, (∑ y ∈ C d, f ((s : R) * y + c)) / (C d).card =
      ∑ x : R, f x := by
    intro d s
    rw [← sum_div, sum_comm]
    simp_rw [hshift s]
    rw [sum_const, nsmul_eq_mul]
    have : ((C d).card : ℝ) ≠ 0 := by exact_mod_cast (card_pos.mpr (hC d)).ne'
    field_simp
  rw [Fintype.sum_prod_type]
  simp_rw [Fintype.sum_prod_type]
  have hcard : (0 : ℝ) < Fintype.card R := by exact_mod_cast Fintype.card_pos
  have hD : (0 : ℝ) < Fintype.card D := by exact_mod_cast Fintype.card_pos
  have hS' : (0 : ℝ) < Fintype.card S := by exact_mod_cast Fintype.card_pos
  calc ∑ d : D, ∑ s : S, ∑ c : R, ((Fintype.card D : ℝ) * (Fintype.card S * Fintype.card R))⁻¹ *
          ((∑ y ∈ C d, f ((s : R) * y + c)) / (C d).card)
      = ∑ d : D, ∑ s : S, ((Fintype.card D : ℝ) * (Fintype.card S * Fintype.card R))⁻¹ *
          ∑ x : R, f x := by
        refine sum_congr rfl fun d _ => sum_congr rfl fun s _ => ?_
        rw [← mul_sum, hinner d s]
    _ = (∑ x : R, f x) / (Fintype.card R : ℝ) := by
        rw [sum_const, sum_const, card_univ, card_univ, nsmul_eq_mul, nsmul_eq_mul]
        field_simp

theorem affineChamberLaw_slotReflectionPositive [Nonempty D] (S : Finset R) (hS : S.Nonempty)
    (C : D → Finset R) (hC : ∀ d, (C d).Nonempty) :
    SlotReflectionPositive (signedIntegral (affineChamberLaw S hS C hC).weight) := by
  have : Nonempty S := ⟨⟨hS.choose, hS.choose_spec⟩⟩
  exact chamberIidLaw_slotReflectionPositive _ _

/-! ## The square clique -/

section Clique

variable (p : ℕ) [Fact p.Prime] (ℓ : ℕ)

/-- Ordered strict-square pairs `Ω = {(a, b) ∈ 𝔽_p² : χ(b - a) = 1}`. -/
abbrev StrictSquarePair := {ab : ZMod p × ZMod p // quadraticChar (ZMod p) (ab.2 - ab.1) = 1}

instance : Nonempty (StrictSquarePair p) :=
  ⟨⟨(0, 1), by simp⟩⟩

/-- The clique data: for each digit `j < ℓ`, a strict-square pair and two digits. -/
abbrev CliqueData := Fin ℓ → StrictSquarePair p × Fin p × Fin p

/-- The two candidate digits `A_j = a_j + p k_j`, `B_j = b_j + p k'_j` in `ℤ/p^{2ℓ}ℤ`. -/
def cliqueDigit (d : CliqueData p ℓ) (j : Fin ℓ) (choice : Bool) : ZMod (p ^ (2 * ℓ)) :=
  if choice then (((d j).1.1.2.val + p * (d j).2.2.val : ℕ) : ZMod (p ^ (2 * ℓ)))
  else (((d j).1.1.1.val + p * (d j).2.1.val : ℕ) : ZMod (p ^ (2 * ℓ)))

/-- The random square clique `𝒞_p = {∑_j p^{2j} x_j : x_j ∈ {A_j, B_j}}`. -/
noncomputable def clique (d : CliqueData p ℓ) : Finset (ZMod (p ^ (2 * ℓ))) :=
  (univ : Finset (Fin ℓ → Bool)).image fun x =>
    ∑ j : Fin ℓ, ((p : ZMod (p ^ (2 * ℓ))) ^ (2 * j.val)) * cliqueDigit p ℓ d j (x j)

theorem clique_nonempty (d : CliqueData p ℓ) : (clique p ℓ d).Nonempty :=
  univ_nonempty.image _

/-- The unit squares of `ℤ/p^{2ℓ}ℤ`. -/
noncomputable def unitSquares : Finset (ZMod (p ^ (2 * ℓ))) :=
  (univ : Finset (ZMod (p ^ (2 * ℓ)))ˣ).image fun u => ((u ^ 2 : (ZMod (p ^ (2 * ℓ)))ˣ) : ZMod _)

theorem unitSquares_nonempty : (unitSquares p ℓ).Nonempty := univ_nonempty.image _

theorem unitSquares_isUnit : ∀ s ∈ unitSquares p ℓ, IsUnit s := by
  intro s hs
  obtain ⟨u, _, rfl⟩ := mem_image.mp hs
  exact Units.isUnit _

instance : NeZero (p ^ (2 * ℓ)) := ⟨pow_ne_zero _ (Fact.out : p.Prime).ne_zero⟩

/-- **The square-clique law** `λ_p` of `def:clique-law`, on labellings of the slots by
`ℤ/p^{2ℓ}ℤ`. -/
noncomputable def cliqueLaw : FiniteLaw (Slot → ZMod (p ^ (2 * ℓ))) :=
  affineChamberLaw (unitSquares p ℓ) (unitSquares_nonempty p ℓ) (clique p ℓ) (clique_nonempty p ℓ)

/-- **`lem:frontier:iidlocal`(i)** at the seven sorting cuts. -/
theorem cliqueLaw_slotReflectionPositive :
    SlotReflectionPositive (signedIntegral (cliqueLaw p ℓ).weight) :=
  affineChamberLaw_slotReflectionPositive _ _ _ _

/-- **`lem:frontier:iidlocal`(ii), marginals**: the one-slot marginals of `λ_p` are uniform. -/
theorem cliqueLaw_uniformMarginals : HasUniformMarginals (cliqueLaw p ℓ) :=
  affineChamberLaw_uniformMarginals _ _ (unitSquares_isUnit p ℓ) _ _

end Clique

end Sarkozy
