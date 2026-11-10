module

public import Sarkozy.DensityMoments.DigitBijection
public import Sarkozy.DensityMoments.LawAlgebra
public import Sarkozy.Construction.CliqueIidPrefix

/-!
# The replacement prefix has unit mixed `L^{1200/17}` (`thm:density:iid-prefix`(b))

`paper/sections/30_density_moment_upgrade.tex`. At a large prefix prime the replacement prefix
`cliqueIidLaw p ℓ` (`Construction/CliqueIidPrefix.lean`) draws the clique data `d`, a unit square
`s` and a shift `c` uniformly, and then one label per slot, independently and uniformly from the
image `s · 𝒞(d) + c` of the square clique.

* `cliqueDrawLaw p ℓ T`: the same construction with draws indexed by any finite `T`, each draw a
  uniform choice vector `x ∈ {0,1}^ℓ` and label `s · cliqueElt d x + c` (`prefixLabel`).
  `cliqueCopyLaw p ℓ σ` fills the `72` slots from these draws through `σ : Slot → T`.
* `expect_cliqueIidLaw_prod`, `cliqueIidLaw_eq_copy`: `cliqueIidLaw p ℓ` is `cliqueCopyLaw p ℓ id`
  on product test functions (the clique has `2^ℓ` elements, `cliqueElt_injective`).
* `expect_tensor_copy`: **the digit identification**. Without the affine map, the copy law is
  the image under the digit bijection `digitEquiv p ℓ : (ℤ/p²ℤ)^ℓ ≅ ℤ/p^{2ℓ}ℤ` of the tensor, over
  the `ℓ` digit pairs, of the per-digit-pair copy laws `CliqueCopies.copyLaw` of the digit-pair
  law. (The paper writes this as "tensoring `m` independent digit pairs".)
* `cliqueCopyLaw_moment`: if each draw fills at most two slots, the copy law has unit mixed
  `L^{1200/17}`: `lem:density:clique36` (`clique36`), `lem:density:clique-copies`
  (`clique_copies_slots`, `clique_copies_tensor`), the bijection (`MixedLpBound.map_equiv`), and the
  average over the common square-affine map (as in `MixedLpBound.random_perm`).
* `cliqueIidLaw_moment`: **`thm:density:iid-prefix`(b) for the reference**:
  `cliqueIidLaw p ℓ` has unit mixed `L^{1200/17}` at every odd prime `2^16 ≤ p < 2^512` and every
  number `ℓ` of digit pairs (the paper's `m = 8192`). `cliqueCopyLaw_moment` with `σ` mapping the
  72 slots onto the 36 labels of the reserved half, each twice, is the diagonal copy of the
  reserved half; with `σ` identifying disjoint pairs of slots it is the law obtained by
  identifying disjoint pairs of independent labels.
* `tensor_cliqueIidLaw_moment`: the statements tensor over prefix atoms.

Here the interpolated centred bound of `lem:density:edge-moment` (`SquarePairInterpolation`) at
the band integer of each prime is a hypothesis; `Unconditional.lean` discharges it
(`cliqueIidLaw_moment_proved`). `p ≡ 1 (mod 4)` is not used.
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace Sarkozy.DensityMoments

open CliqueCopies

variable (p : ℕ) [hp : Fact p.Prime] (ℓ : ℕ)

instance instNonemptyUnitSquares : Nonempty (unitSquares p ℓ) :=
  ⟨⟨_, (unitSquares_nonempty p ℓ).choose_spec⟩⟩

/-- The data of the replacement prefix: clique data, a unit square and a shift. -/
abbrev PrefixData := AffineData (R := ZMod (p ^ (2 * ℓ))) (CliqueData p ℓ) (unitSquares p ℓ)

/-- The label of a draw with choice vector `x`: `s · cliqueElt d x + c`. -/
noncomputable def prefixLabel (q : PrefixData p ℓ) (x : Fin ℓ → Bool) : ZMod (p ^ (2 * ℓ)) :=
  (q.2.1 : ZMod (p ^ (2 * ℓ))) * cliqueElt ℓ q.1 x + q.2.2

/-- Conditionally independent uniform clique draws indexed by `T`, after the common
square-affine map. -/
noncomputable def cliqueDrawLaw (T : Type*) [Fintype T] [DecidableEq T] :
    FiniteLaw (T → ZMod (p ^ (2 * ℓ))) :=
  ((FiniteLaw.uniform (PrefixData p ℓ)).product (FiniteLaw.uniform (T → Fin ℓ → Bool))).map
    (fun q t => prefixLabel p ℓ q.1 (q.2 t))

/-- The 72 slots filled from the draws through `σ`. -/
noncomputable def cliqueCopyLaw {T : Type*} [Fintype T] [DecidableEq T] (σ : Slot → T) :
    FiniteLaw (Slot → ZMod (p ^ (2 * ℓ))) :=
  (cliqueDrawLaw p ℓ T).map (fun z v => z (σ v))

/-- The uniform law on the image `s · 𝒞(d) + c` of the clique is the image of the uniform choice
vector. -/
theorem expect_affineLabelLaw (q : PrefixData p ℓ) (f : ZMod (p ^ (2 * ℓ)) → ℝ) :
    (affineLabelLaw (unitSquares p ℓ) (clique p ℓ) (clique_nonempty p ℓ) q).expect f =
      (FiniteLaw.uniform (Fin ℓ → Bool)).expect (fun x => f (prefixLabel p ℓ q x)) := by
  unfold affineLabelLaw
  rw [expect_uniformOn, FiniteLaw.expect_uniform]
  have hinj : Function.Injective (fun x => prefixLabel p ℓ q x) := by
    intro x x' h
    have hu := unitSquares_isUnit p ℓ _ q.2.1.2
    unfold prefixLabel at h
    exact cliqueElt_injective ℓ q.1 (hu.mul_left_cancel (add_right_cancel h))
  have himg : (clique p ℓ q.1).image (fun y => (q.2.1 : ZMod (p ^ (2 * ℓ))) * y + q.2.2) =
      univ.image (fun x => prefixLabel p ℓ q x) := by
    unfold clique
    rw [Finset.image_image]
    rfl
  rw [himg, sum_image (fun x _ x' _ h => hinj h), card_image_of_injective _ hinj, card_univ]

/-- **The reference on product test functions**: data first, then one independent uniform
choice vector per slot. -/
theorem expect_cliqueIidLaw_prod (f : Slot → ZMod (p ^ (2 * ℓ)) → ℝ) :
    (cliqueIidLaw p ℓ).expect (fun z => ∏ v, f v (z v)) =
      (FiniteLaw.uniform (PrefixData p ℓ)).expect (fun q => ∏ v,
        (FiniteLaw.uniform (Fin ℓ → Bool)).expect (fun x => f v (prefixLabel p ℓ q x))) := by
  unfold cliqueIidLaw affineSlotLaw
  rw [expect_slotIidLaw]
  refine Finset.sum_congr rfl fun q _ => ?_
  congr 1
  simp_rw [← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun v x =>
    (affineLabelLaw (unitSquares p ℓ) (clique p ℓ) (clique_nonempty p ℓ) q).weight x * f v x)]
  refine Finset.prod_congr rfl fun v _ => ?_
  exact expect_affineLabelLaw p ℓ q (f v)

/-- The copy law on product test functions. -/
theorem expect_cliqueCopyLaw_prod {T : Type*} [Fintype T] [DecidableEq T] (σ : Slot → T)
    (f : Slot → ZMod (p ^ (2 * ℓ)) → ℝ) :
    (cliqueCopyLaw p ℓ σ).expect (fun z => ∏ v, f v (z v)) =
      (FiniteLaw.uniform (PrefixData p ℓ)).expect (fun q =>
        (FiniteLaw.uniform (T → Fin ℓ → Bool)).expect (fun x =>
          ∏ v, f v (prefixLabel p ℓ q (x (σ v))))) := by
  unfold cliqueCopyLaw cliqueDrawLaw
  rw [FiniteLaw.expect_map, FiniteLaw.expect_map, FiniteLaw.expect_product]
  rfl

/-- **`cliqueIidLaw` is the copy law with one draw per slot**, on product test functions. -/
theorem cliqueIidLaw_eq_copy (f : Slot → ZMod (p ^ (2 * ℓ)) → ℝ) :
    (cliqueIidLaw p ℓ).expect (fun z => ∏ v, f v (z v)) =
      (cliqueCopyLaw p ℓ (id : Slot → Slot)).expect (fun z => ∏ v, f v (z v)) := by
  rw [expect_cliqueIidLaw_prod, expect_cliqueCopyLaw_prod]
  refine FiniteLaw.expect_congr _ fun q => ?_
  rw [← pi_uniform (Ω := fun _ : Slot => Fin ℓ → Bool)]
  exact (FiniteLaw.expect_pi_product (fun _ : Slot => FiniteLaw.uniform (Fin ℓ → Bool))
    (fun v x => f v (prefixLabel p ℓ q x))).symm

/-- Splitting a vector of (digit data, coin vector) pairs. -/
def splitEquiv (T : Type*) :
    (Fin ℓ → DigitData p × (T → Bool)) ≃ (Fin ℓ → DigitData p) × (T → Fin ℓ → Bool) where
  toFun u := (fun j => (u j).1, fun t j => (u j).2 t)
  invFun q := fun j => (q.1 j, fun t => q.2 t j)
  left_inv _ := rfl
  right_inv _ := rfl

/-- **The digit identification**: without the affine map, the copy law is the digit-bijection
image of the tensor over the `ℓ` digit pairs of the per-digit-pair copy laws. -/
theorem expect_tensor_copy {T : Type*} [Fintype T] [DecidableEq T] (σ : Slot → T)
    (g : Slot → ZMod (p ^ (2 * ℓ)) → ℝ) :
    ((FiniteLaw.tensor (fun _ : Fin ℓ => copyLaw (digitPairLaw p) (pairB p) (pairA p) σ)).map
        (fun z v => digitEquiv p ℓ (z v))).expect (fun z => ∏ v, g v (z v)) =
      (FiniteLaw.uniform (CliqueData p ℓ)).expect (fun d =>
        (FiniteLaw.uniform (T → Fin ℓ → Bool)).expect (fun x =>
          ∏ v, g v (cliqueElt ℓ d (x (σ v))))) := by
  rw [FiniteLaw.expect_map]
  have hν : copyLaw (digitPairLaw p) (pairB p) (pairA p) σ =
      ((digitPairLaw p).product (coins T)).map
        (fun q v => label (pairB p) (pairA p) q.1 (q.2 (σ v))) := by
    unfold copyLaw drawLaw
    rw [map_map_law]
    rfl
  simp only [hν]
  rw [expect_tensor_map (fun _ : Fin ℓ => (digitPairLaw p).product (coins T))
    (fun _ q v => label (pairB p) (pairA p) q.1 (q.2 (σ v)))]
  have hlaw : FiniteLaw.pi (fun _ : Fin ℓ => (digitPairLaw p).product (coins T)) =
      FiniteLaw.uniform (Fin ℓ → DigitData p × (T → Bool)) := by
    unfold coins coin
    rw [pi_uniform (Ω := fun _ : T => Bool), FiniteLaw.uniform_product, pi_uniform]
  rw [hlaw]
  simp only [Function.comp_def, digitEquiv_label]
  have hR : (FiniteLaw.uniform (CliqueData p ℓ)).expect (fun d =>
      (FiniteLaw.uniform (T → Fin ℓ → Bool)).expect (fun x =>
        ∏ v, g v (cliqueElt ℓ d (x (σ v))))) =
      (FiniteLaw.uniform (CliqueData p ℓ × (T → Fin ℓ → Bool))).expect (fun q =>
        ∏ v, g v (cliqueElt ℓ q.1 (q.2 (σ v)))) := by
    rw [← FiniteLaw.uniform_product, FiniteLaw.expect_product]
  rw [hR, ← expect_uniform_equiv (splitEquiv p ℓ T)]
  rfl

/-- The square-affine bijection `y ↦ s y + c`. -/
noncomputable def affineEquiv (s : unitSquares p ℓ) (c : ZMod (p ^ (2 * ℓ))) :
    ZMod (p ^ (2 * ℓ)) ≃ ZMod (p ^ (2 * ℓ)) :=
  Equiv.ofBijective (fun y => (s : ZMod (p ^ (2 * ℓ))) * y + c)
    (Finite.injective_iff_bijective.mp
      (fun _ _ h => (unitSquares_isUnit p ℓ _ s.2).mul_left_cancel (add_right_cancel h)))

/-- **The copy laws of the replacement prefix** (`thm:density:iid-prefix`(b),
`lem:density:clique-copies` for `ℓ` digit pairs and the common square-affine map). If each draw
fills at most two of the 72 slots, the slot law has unit mixed `L^{1200/17}`. Named hypothesis:
the interpolated centred bound of `lem:density:edge-moment` (`SquarePairInterpolation`). -/
theorem cliqueCopyLaw_moment (hp2 : p ≠ 2) (h16 : 2 ^ 16 ≤ p) (h512 : p < 2 ^ 512)
    (hinterp : ∀ i : Fin 31, 2 ^ Certificates.clique36Band i ≤ p →
      p < 2 ^ (Certificates.clique36Band i + 16) →
      SquarePairInterpolation p hp2 (Certificates.clique36J i))
    {T : Type*} [Fintype T] [DecidableEq T] (σ : Slot → T)
    (hσ : ∀ t, (univ.filter (fun v => σ v = t)).card ≤ 2) :
    MixedLpBound (cliqueCopyLaw p ℓ σ) (1200 / 17) 1 := by
  have h36 := clique36 hp2 h16 h512 hinterp
  have hslot := clique_copies_slots (digitPairLaw p) (pairB p) (pairA p) h36 σ hσ
  have hM : MixedLpBound ((FiniteLaw.tensor
      (fun _ : Fin ℓ => copyLaw (digitPairLaw p) (pairB p) (pairA p) σ)).map
        (fun z v => digitEquiv p ℓ (z v))) (1200 / 17) 1 :=
    (clique_copies_tensor _ (by norm_num) (fun _ => hslot)).map_equiv (digitEquiv p ℓ)
  intro f
  rw [expect_cliqueCopyLaw_prod, one_mul]
  -- separate the clique data from the affine map
  rw [← FiniteLaw.uniform_product (X := CliqueData p ℓ)
    (Y := (unitSquares p ℓ) × ZMod (p ^ (2 * ℓ))), FiniteLaw.expect_product, expect_comm]
  refine (FiniteLaw.abs_expect_le _ _).trans (FiniteLaw.expect_le_const _ fun sc => ?_)
  have hg := hM (fun v y => f v (affineEquiv p ℓ sc.1 sc.2 y))
  have key := expect_tensor_copy p ℓ σ (fun v y => f v (affineEquiv p ℓ sc.1 sc.2 y))
  beta_reduce at key
  rw [key, one_mul] at hg
  have hnorm : ∀ v, (FiniteLaw.uniform (ZMod (p ^ (2 * ℓ)))).lpNorm (1200 / 17)
      (fun y => f v (affineEquiv p ℓ sc.1 sc.2 y)) =
      (FiniteLaw.uniform (ZMod (p ^ (2 * ℓ)))).lpNorm (1200 / 17) (f v) := fun v =>
    uniform_lpNorm_comp_equiv (affineEquiv p ℓ sc.1 sc.2) _ (f v)
  simp only [hnorm] at hg
  exact hg

/-- **`thm:density:iid-prefix`(b), the reference**: at every odd prime `2^16 ≤ p < 2^512` and for
every number `ℓ` of digit pairs, the replacement prefix law `cliqueIidLaw p ℓ` has unit mixed
`L^{1200/17}` norm. Named hypothesis: the interpolated centred bound of
`lem:density:edge-moment` (`SquarePairInterpolation`) at the band integer. -/
theorem cliqueIidLaw_moment (hp2 : p ≠ 2) (h16 : 2 ^ 16 ≤ p) (h512 : p < 2 ^ 512)
    (hinterp : ∀ i : Fin 31, 2 ^ Certificates.clique36Band i ≤ p →
      p < 2 ^ (Certificates.clique36Band i + 16) →
      SquarePairInterpolation p hp2 (Certificates.clique36J i)) :
    MixedLpBound (cliqueIidLaw p ℓ) (1200 / 17) 1 := by
  have h := cliqueCopyLaw_moment p ℓ hp2 h16 h512 hinterp (id : Slot → Slot)
    (fun t => by
      simp only [id]
      rw [Finset.filter_eq']
      simp)
  intro f
  rw [cliqueIidLaw_eq_copy]
  exact h f

/-- **Tensoring over prefix atoms** (`thm:density:iid-prefix`(b), last sentence): independent
replacement prefixes at several large primes have unit mixed `L^{1200/17}` on the product label
group. -/
theorem tensor_cliqueIidLaw_moment {J : Type*} [Fintype J] [DecidableEq J] (P : J → ℕ)
    [∀ j, Fact (P j).Prime] (L : J → ℕ) (hp2 : ∀ j, P j ≠ 2) (h16 : ∀ j, 2 ^ 16 ≤ P j)
    (h512 : ∀ j, P j < 2 ^ 512)
    (hinterp : ∀ j, ∀ i : Fin 31, 2 ^ Certificates.clique36Band i ≤ P j →
      P j < 2 ^ (Certificates.clique36Band i + 16) →
      SquarePairInterpolation (P j) (hp2 j) (Certificates.clique36J i)) :
    MixedLpBound (FiniteLaw.tensor (fun j => cliqueIidLaw (P j) (L j))) (1200 / 17) 1 :=
  clique_copies_tensor _ (by norm_num) fun j =>
    cliqueIidLaw_moment (P j) (L j) (hp2 j) (h16 j) (h512 j) (hinterp j)

end Sarkozy.DensityMoments
