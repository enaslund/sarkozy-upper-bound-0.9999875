module

public import Sarkozy.TheoremC.Main
public import Sarkozy.Functional.UnitSquares

@[expose] public section

/-!
# `lem:record:density-can` and the nonwrapping terms of `lem:record:wrap-expansion`

`paper/sections/08_scale_comparison.tex`, `lem:record:density-can` (accepted-pair
cancellation with a density factor), and the nonwrapping step of the proof of
`lem:record:wrap-expansion` (`paper/sections/10_comparison_lemmas.tex`).

* `DensityCancellation`: the statement of `lem:record:density-can` over the objects of
  `Sarkozy.PaperFrame`, an analytic input (WP-K is proving it in `Sarkozy/Cancellation/`).
* The unfolding of a coupled form: `form_productHalf` (the cut form of two product
  half-functions is the multilinear integral of the slot inputs `pairInputs`, the inputs of
  `X` on the plus half and those of `Y` on the minus half, `eq:cc:bilinear`) and
  `abs_multilinear_le_components` (the expansion of `ν = ⊗_𝔟 ∑_i c_{𝔟,i} ν_{𝔟,i}` into its
  product components).
* `ComparisonData.nonwrappingCancellation_of_densityCancellation`: the hypothesis
  `NonwrappingCancellation` of Theorem C follows from `DensityCancellation` and a bound for
  the coefficients of the product components; the acceptance, mixing and marginal clauses of
  (CP4)(a) and the nonvanishing square increments of (CP0)(d) are exactly the hypotheses of
  `lem:record:density-can` at every nonwrapping active query (the CRT combination of the
  coordinate increments is a nonvanishing square class, `isNonvanishingSquareClass_crt`;
  the next index is `(b + 1, s + r)`, `crtEquiv_symm_nextIndex`).
* `ComparisonData.coefficient_bound`: the coefficient bound `∏_𝔟 |ν|_𝔟 ≤ 𝔳_ν e^{P+S}` of the
  proof (the mass of `ν`, from (CP2)–(CP4)); hence
  `nonwrappingCancellation_of_densityCancellation'` and `theoremC_of_densityCancellation`
  (Theorem C with `lem:record:density-can` in place of `NonwrappingCancellation`).
-/

open Filter Finset Function
open scoped Topology BigOperators Matrix

namespace Sarkozy.TheoremC

open Sarkozy.FourierArithmetic Sarkozy.Functional Sarkozy.IndexSupport Sarkozy.Comparison
  Sarkozy.PaperFrame Sarkozy.RecordExpansion

/-! ## The statement of `lem:record:density-can` -/

section DensityCan

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] (m₀ : J₀ → ℕ) [∀ i, NeZero (m₀ i)]
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] (p : ∀ L, J L → ℕ)
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] (pr h : P → ℕ) [∀ q, NeZero (pr q ^ h q)]
  (hcop : Pairwise (Nat.Coprime on fun q => pr q ^ h q))

/-- The next index `(b + 1, s + r)` in the coordinates `ℤ/Kℤ × ∏_p ℤ/p^{h_p}ℤ` of
`IndexSupport.CoordSpace`: the interval coordinate is shifted by one, the residue coordinate
at `p` by the increment `r_p` (the CRT coordinates of `r ∈ ℤ/M₀ℤ`). -/
def nextIndex (η : ∀ j, CoordSpace blockScale pr h j) (r : ∀ q, ZMod (pr q ^ h q)) :
    ∀ j, CoordSpace blockScale pr h j
  | none => η none + 1
  | some q => η (some q) + r q

/-- The input `g^{I_b, M₀, s}` of `def:record:functional`(f) at the index
`(b, s) ∈ ℤ/Kℤ × ℤ/M₀ℤ` (`Sarkozy.Functional.indexedInput`), read on the atom labels. -/
noncomputable def indexInputAt (L : ℕ) (A : Finset ℤ)
    (ω : ZMod blockScale × ZMod (modulus pr h)) (x : ∀ b, AtomLabel m₀ p L b) : ℝ :=
  indexedInput (joinModuli m₀ (p L)) (paperCutoff (blockScale * L)) blockScale L (modulus pr h)
    A ω (atomGroupEquiv m₀ p L x)

omit [DecidableEq P] [∀ q, NeZero (pr q ^ h q)] in
/-- The query input in the CRT coordinates is the input at the index `(b, s)`. -/
theorem atomInput_eq_indexInputAt (L : ℕ) (A : Finset ℤ) {E : Type} (e : E)
    (η : ∀ j, CoordSpace blockScale pr h j) :
    atomInput m₀ p pr h hcop L A e η =
      indexInputAt m₀ p pr h L A ((crtEquiv blockScale pr h hcop).symm η) := rfl

/-- The inputs of `def:record:functional`(f) that occur in the coupled forms, read on the atom
labels: `F_A = g^{[N],1,0}` (`atomLift`), or `g^{I_b, M₀, s}` at an index `(b, s)`
(`indexInputAt`). -/
def IsQueryInput (L : ℕ) (A : Finset ℤ) (G : (∀ b, AtomLabel m₀ p L b) → ℝ) : Prop :=
  G = atomLift m₀ p L A ∨
    ∃ ω : ZMod blockScale × ZMod (modulus pr h), G = indexInputAt m₀ p pr h L A ω

/-- **`lem:record:density-can`** (accepted-pair cancellation with a density factor), over the
objects of `Sarkozy.PaperFrame`. There is a constant `C_can` with the following property.
Let `L ≥ L_*`, `N = KL`, let `A ⊆ [N]` be square-difference-free and `α = |A|/N`. Let
`ϱ = ⊗_𝔟 ϱ_𝔟` be a product of probability measures, each with uniform one-slot marginals.
Let `(u, v)` be an ordered pair of distinct slots such that
(a) at every tail prime `p ≥ P₅` the `(u,v)`-marginal of `ϱ_p` is uniform and `ϱ_p` is
`(γ, (u,v))`-mixing (the hypothesis of `lem:tr:pairsupport`, `γ = 255/1024`);
(b) at the atoms below `P₅` (the prefix and the tail primes `p < P₅`), `ϱ`-almost surely
`z_v − z_u` is accepted (`AcceptedPair`: a nonzero square at the primes with `e_p = 1`; at a
prefix prime nonzero, of even valuation `2j < e_p`, with a square unit part).
Let `1 ≤ b ≤ K − 1` (`b ≠ 0` in `ℤ/Kℤ`; `b = 0` is the interval `I_K`), `s ∈ ℤ/M₀ℤ`, and let
`r ∈ ℤ/M₀ℤ` be a nonvanishing square class (`def:nonvanishing-square-class`,
`IsNonvanishingSquareClass`). Let `G_u = g^{I_b, M₀, s}`, `G_v = g^{I_{b+1}, M₀, s+r}`, and
let `G_w` (`w ≠ u, v`) be inputs of `def:record:functional`. Then
`|∫ ∏_w G_w(z_w) dϱ(z)| ≤ 2 C_can L^{-σ} α`.

Specialisation (recorded in the report): the prefix blocks are merged into one atom
(`X_pre` is the prefix together with the tail primes below `P₅`), and the inputs `G_w` at the
other slots range over `IsQueryInput` (`F_A` and the `g^{I_b, M₀, s}`), which is all that the
coupled forms use; so the paper's lemma implies this statement. The paper's intermediate
bound `C_can N^{72δ} α (N^{-γ t_an} + N^{-1/120 + t_an(1/2−γ)})` is WP-K's
`Sarkozy.Cancellation.density_can_stage`. -/
def DensityCancellation (P5 : ℕ) (pp ep : J₀ → ℕ) : Prop :=
  ∃ Ccan : ℝ, 0 ≤ Ccan ∧ ∃ Lstar : ℕ, ∀ L : ℕ, Lstar ≤ L → ∀ A : Finset ℤ,
    Admissible (blockScale * L) A →
    ∀ ϱ : ∀ b : PaperAtom J L, FiniteLaw (Slot → AtomLabel m₀ p L b),
    (∀ b, HasUniformMarginals (ϱ b)) →
    ∀ u v : Slot, u ≠ v →
    (∀ j : J L, P5 ≤ p L j → PairUniformOmega (q := p L j) (ϱ (some j)) u v ∧
        Sarkozy.Mixing.IsGammaMixing (p L j) Sarkozy.AnalyticStage.γ (ϱ (some j)) {u, v}) →
    (∀ b : PaperAtom J L, (∀ j, b = some j → p L j < P5) → ∀ z, (ϱ b).weight z ≠ 0 →
        AcceptedPair m₀ p pp ep L b (z u) (z v)) →
    ∀ (bI : ZMod blockScale) (s r : ZMod (modulus pr h)), bI ≠ 0 →
    IsNonvanishingSquareClass (modulus pr h) r →
    ∀ G : Slot → (∀ b, AtomLabel m₀ p L b) → ℝ,
    G u = indexInputAt m₀ p pr h L A (bI, s) →
    G v = indexInputAt m₀ p pr h L A (bI + 1, s + r) →
    (∀ w, w ≠ u → w ≠ v → IsQueryInput m₀ p pr h L A (G w)) →
    |multilinearIntegral (tensorLaw fun b => signedIntegral (ϱ b).weight) G| ≤
      remainder (2 * Ccan) L A

end DensityCan

/-! ## Nonvanishing square classes in CRT coordinates -/

section CRT

variable {P : Type} [Fintype P] [DecidableEq P] (pr h : P → ℕ) [∀ q, NeZero (pr q ^ h q)]
  (hcop : Pairwise (Nat.Coprime on fun q => pr q ^ h q))

omit [DecidableEq P] in
/-- `v_{p_q}(M₀) = h_q` for distinct primes `p_q`. -/
theorem modulus_factorization (hprime : ∀ q, (pr q).Prime) (hinj : Injective pr) (q₀ : P) :
    (modulus pr h).factorization (pr q₀) = h q₀ := by
  unfold modulus
  rw [Nat.factorization_prod (fun q _ => NeZero.ne (pr q ^ h q)), Finsupp.finsetSum_apply]
  simp only [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
  rw [sum_eq_single q₀]
  · rw [(hprime q₀).factorization, Finsupp.single_eq_same, mul_one]
  · intro q _ hq
    rw [(hprime q).factorization, Finsupp.single_apply, ite_eq_right (fun h' => hq (hinj h')),
      mul_zero]
  · intro hq
    exact absurd (mem_univ q₀) hq

omit [DecidableEq P] [∀ q, NeZero (pr q ^ h q)] in
theorem mem_primeFactors_modulus (hprime : ∀ q, (pr q).Prime) {d : ℕ}
    (hd : d ∈ (modulus pr h).primeFactors) : ∃ q, d = pr q := by
  rw [Nat.mem_primeFactors] at hd
  obtain ⟨hdp, hdvd, _⟩ := hd
  unfold modulus at hdvd
  obtain ⟨q, _, hq⟩ := ((Nat.Prime.prime hdp).dvd_finsetProd_iff _).mp hdvd
  exact ⟨q, (Nat.prime_dvd_prime_iff_eq hdp (hprime q)).mp (hdp.dvd_of_dvd_pow hq)⟩

omit [DecidableEq P] in
theorem crt_val_mod (x : ZMod (modulus pr h)) (q : P) :
    ((ZMod.prodEquivPi (fun p => pr p ^ h p) hcop) x q).val = x.val % pr q ^ h q := by
  have : NeZero (modulus pr h) := ⟨Finset.prod_ne_zero_iff.mpr fun q _ => NeZero.ne _⟩
  rw [ZMod.prodEquivPi_apply, ZMod.castHom_apply, ZMod.cast_eq_val, ZMod.val_natCast]

omit [DecidableEq P] in
/-- The reduction of the CRT combination of `r = (r_q)_q` modulo `p_q^{h_q}` is `r_q`. -/
theorem coordinateRep_crt (hprime : ∀ q, (pr q).Prime) (hinj : Injective pr)
    (r : ∀ q, ZMod (pr q ^ h q)) (q : P) :
    coordinateRep (modulus pr h) (pr q) ((ZMod.prodEquivPi (fun p => pr p ^ h p) hcop).symm r) =
      (r q).val := by
  unfold coordinateRep
  rw [modulus_factorization pr h hprime hinj q, ← crt_val_mod pr h hcop,
    RingEquiv.apply_symm_apply]

omit [DecidableEq P] in
/-- **The CRT combination of coordinatewise nonvanishing square increments is a nonvanishing
square class** (`def:nonvanishing-square-class`), when `h₂ ≥ 3` ((CP0)(d)). -/
theorem isNonvanishingSquareClass_crt (hprime : ∀ q, (pr q).Prime) (hinj : Injective pr)
    (h2 : ∃ q, pr q = 2 ∧ 3 ≤ h q) (r : ∀ q, ZMod (pr q ^ h q))
    (hr : ∀ q, IsNonvanishingSquareCoord (pr q) (h q) (r q)) :
    IsNonvanishingSquareClass (modulus pr h)
      ((ZMod.prodEquivPi (fun p => pr p ^ h p) hcop).symm r) := by
  refine ⟨?_, fun d hd => ?_⟩
  · obtain ⟨q, hq2, hq3⟩ := h2
    rw [← hq2, modulus_factorization pr h hprime hinj q]
    exact hq3
  · obtain ⟨q, rfl⟩ := mem_primeFactors_modulus pr h hprime hd
    have hc := coordinateRep_crt pr h hcop hprime hinj r q
    rw [hc]
    obtain ⟨h1, h2', h3⟩ := hr q
    refine ⟨h1, h2', ?_⟩
    by_cases hq : pr q = 2
    · rw [ite_eq_left hq] at h3 ⊢
      have hc2 : coordinateRep (modulus pr h) 2
          ((ZMod.prodEquivPi (fun p => pr p ^ h p) hcop).symm r) = (r q).val := by
        rw [← hq]; exact hc
      have hf : (modulus pr h).factorization 2 = h q := by
        rw [← hq]; exact modulus_factorization pr h hprime hinj q
      rw [hc2, hf]
      exact h3
    · rw [ite_eq_right hq] at h3 ⊢
      exact h3

omit [DecidableEq P] [∀ q, NeZero (pr q ^ h q)] in
/-- The next index in CRT coordinates: `(b, s) ↦ (b + 1, s + r)`, `r` the CRT combination of
the coordinate increments. -/
theorem crtEquiv_symm_nextIndex (η : ∀ j, CoordSpace blockScale pr h j)
    (r : ∀ q, ZMod (pr q ^ h q)) :
    (crtEquiv blockScale pr h hcop).symm (nextIndex pr h η r) =
      (((crtEquiv blockScale pr h hcop).symm η).1 + 1,
        ((crtEquiv blockScale pr h hcop).symm η).2 +
          (ZMod.prodEquivPi (fun q => pr q ^ h q) hcop).symm r) := by
  show (η none + 1, (ZMod.prodEquivPi (fun q => pr q ^ h q) hcop).symm
      (fun q => η (some q) + r q)) =
    (η none + 1, (ZMod.prodEquivPi (fun q => pr q ^ h q) hcop).symm (fun q => η (some q)) +
      (ZMod.prodEquivPi (fun q => pr q ^ h q) hcop).symm r)
  rw [← map_add]
  rfl

end CRT

/-! ## Unfolding a coupled form -/

section Unfolding

variable {E : Type} {Ωi : Type} {X : Type}

open Classical in
/-- The slot function of a product half-function at the plus-half slot `v`: the input of the
query whose source is `v`, or `F` if there is none. -/
noncomputable def halfInput (u : E → reservedCut.Half) (φ : E → Ωi → X → ℝ) (F : X → ℝ)
    (ω : E → Ωi) (v : reservedCut.Half) : X → ℝ :=
  if hv : ∃ e, u e = v then φ hv.choose (ω hv.choose) else F

theorem halfInput_source {u : E → reservedCut.Half} (hu : Injective u) (φ : E → Ωi → X → ℝ)
    (F : X → ℝ) (ω : E → Ωi) (e : E) : halfInput u φ F ω (u e) = φ e (ω e) := by
  have hv : ∃ e', u e' = u e := ⟨e, rfl⟩
  unfold halfInput
  rw [dite_eq_left hv]
  have he : hv.choose = e := hu hv.choose_spec
  rw [he]

theorem halfInput_of_not {u : E → reservedCut.Half} (φ : E → Ωi → X → ℝ) (F : X → ℝ)
    (ω : E → Ωi) {v : reservedCut.Half} (hv : ¬ ∃ e, u e = v) : halfInput u φ F ω v = F := by
  unfold halfInput
  rw [dite_eq_right hv]

/-- Every slot function of a product half-function is `F` or an input of a query. -/
theorem halfInput_cases (u : E → reservedCut.Half) (φ : E → Ωi → X → ℝ) (F : X → ℝ)
    (ω : E → Ωi) (v : reservedCut.Half) :
    halfInput u φ F ω v = F ∨ ∃ e, halfInput u φ F ω v = φ e (ω e) := by
  by_cases hv : ∃ e, u e = v
  · refine Or.inr ⟨hv.choose, ?_⟩
    unfold halfInput
    rw [dite_eq_left hv]
  · exact Or.inl (halfInput_of_not φ F ω hv)

/-- A product half-function is the product of its slot functions. -/
theorem productHalf_eq_prod [Fintype E] {u : E → reservedCut.Half} (hu : Injective u)
    (φ : E → Ωi → X → ℝ) (F : X → ℝ) (ω : E → Ωi) (x : reservedCut.Half → X) :
    productHalf u φ F ω x = ∏ v, halfInput u φ F ω v (x v) := by
  unfold productHalf
  rw [← prod_sdiff (subset_univ (univ.image u))]
  rw [mul_comm]
  congr 1
  · apply prod_congr rfl
    intro v hv
    rw [halfInput_of_not]
    intro ⟨e, he⟩
    exact (mem_sdiff.mp hv).2 (mem_image.mpr ⟨e, mem_univ _, he⟩)
  · rw [prod_image (fun e _ e' _ he => hu he)]
    exact prod_congr rfl fun e _ => by rw [halfInput_source hu]

/-- The slot inputs of a pair of product half-functions: at a plus-half slot the slot
function of `X = productHalf u φ F ω`, at a minus-half slot `s` the slot function of
`Y = productHalf w ψ F ω'` at `ι s` (`eq:cc:bilinear`). -/
noncomputable def pairInputs (u w : E → reservedCut.Half) (φ ψ : E → Ωi → X → ℝ) (F : X → ℝ)
    (ω ω' : E → Ωi) : Slot → X → ℝ :=
  fun s => if hs : s ∈ reservedCut.half then halfInput u φ F ω ⟨s, hs⟩
    else halfInput w ψ F ω' ⟨reservedCut.flip s, (reservedCut.crosses s).mpr hs⟩

theorem pairInputs_plus (u w : E → reservedCut.Half) (φ ψ : E → Ωi → X → ℝ) (F : X → ℝ)
    (ω ω' : E → Ωi) (v : reservedCut.Half) :
    pairInputs u w φ ψ F ω ω' v = halfInput u φ F ω v := by
  unfold pairInputs
  rw [dite_eq_left v.2]

theorem pairInputs_minus (u w : E → reservedCut.Half) (φ ψ : E → Ωi → X → ℝ) (F : X → ℝ)
    (ω ω' : E → Ωi) (v : reservedCut.Half) :
    pairInputs u w φ ψ F ω ω' (reservedCut.flip v) = halfInput w ψ F ω' v := by
  unfold pairInputs
  rw [dite_eq_right (reservedCut.flip_not_mem v.2)]
  congr 1
  exact Subtype.ext (reservedCut.flip_flip v)

/-- Every slot input of a pair of product half-functions is `F` or an input of a query. -/
theorem pairInputs_cases (u w : E → reservedCut.Half) (φ ψ : E → Ωi → X → ℝ) (F : X → ℝ)
    (ω ω' : E → Ωi) (s : Slot) :
    pairInputs u w φ ψ F ω ω' s = F ∨ (∃ e, pairInputs u w φ ψ F ω ω' s = φ e (ω e)) ∨
      ∃ e, pairInputs u w φ ψ F ω ω' s = ψ e (ω' e) := by
  unfold pairInputs
  split_ifs with hs
  · rcases halfInput_cases u φ F ω ⟨s, hs⟩ with h1 | ⟨e, he⟩
    · exact Or.inl h1
    · exact Or.inr (Or.inl ⟨e, he⟩)
  · rcases halfInput_cases w ψ F ω' ⟨reservedCut.flip s, (reservedCut.crosses s).mpr hs⟩ with
      h1 | ⟨e, he⟩
    · exact Or.inl h1
    · exact Or.inr (Or.inr ⟨e, he⟩)

/-- **The cut form of two product half-functions is a multilinear integral**
(`eq:cc:bilinear`): `Q_κ(X_ω, Y_{ω'}) = ∫ ∏_s G_s(z_s) dκ(z)` with the slot inputs
`G = pairInputs`. -/
theorem form_productHalf [Fintype E] (κ : ((Slot → X) → ℝ) →ₗ[ℝ] ℝ)
    {u w : E → reservedCut.Half} (hu : Injective u) (hw : Injective w)
    (φ ψ : E → Ωi → X → ℝ) (F : X → ℝ) (ω ω' : E → Ωi) :
    reservedCut.form κ (productHalf u φ F ω) (productHalf w ψ F ω') =
      multilinearIntegral κ (pairInputs u w φ ψ F ω ω') := by
  rw [reservedCut.multilinear_eq_form κ (pairInputs u w φ ψ F ω ω')]
  have h1 : productHalf u φ F ω = reservedCut.halfProduct (pairInputs u w φ ψ F ω ω') := by
    funext x
    rw [productHalf_eq_prod hu]
    unfold ReflectionCut.halfProduct
    exact prod_congr rfl fun v _ => by rw [pairInputs_plus]
  have h2 : productHalf w ψ F ω' =
      reservedCut.halfProduct (pairInputs u w φ ψ F ω ω' ∘ reservedCut.flip) := by
    funext x
    rw [productHalf_eq_prod hw]
    unfold ReflectionCut.halfProduct
    exact prod_congr rfl fun v _ => by rw [Function.comp_apply, pairInputs_minus]
  rw [h1, h2]

end Unfolding

/-! ## Product components and the index kernels -/

section Components

variable {Jt : Type} [Fintype Jt] [DecidableEq Jt] {Xt : Jt → Type} [∀ b, Fintype (Xt b)]
  [∀ b, DecidableEq (Xt b)]

/-- **The expansion into product components** (nonwrapping step of the proof of
`lem:record:wrap-expansion`): if every product component `⊗_𝔟 ϱ_{𝔟,σ_𝔟}` satisfies
`|∫ ∏ G dϱ_σ| ≤ M`, then the signed law `⊗_𝔟 ∑_i c_{𝔟,i} ϱ_{𝔟,i}` satisfies
`|∫ ∏ G| ≤ (∏_𝔟 ∑_i |c_{𝔟,i}|) M`. -/
theorem abs_multilinear_le_components {I : Jt → Type} [∀ b, Fintype (I b)]
    (c : ∀ b, I b → ℝ) (ϱ : ∀ b, I b → FiniteLaw (Slot → Xt b))
    (G : Slot → (∀ b, Xt b) → ℝ) {M : ℝ}
    (hM : ∀ σ : ∀ b, I b,
      |multilinearIntegral (tensorLaw fun b => signedIntegral (ϱ b (σ b)).weight) G| ≤ M) :
    |multilinearIntegral (tensorLaw fun b => ∑ i, c b i • signedIntegral (ϱ b i).weight) G| ≤
      (∏ b, ∑ i, |c b i|) * M := by
  rw [tensorLaw_sum]
  have hsplit : ∀ σ : ∀ b, I b,
      tensorLaw (fun b => c b (σ b) • signedIntegral (ϱ b (σ b)).weight) =
        (∏ b, c b (σ b)) • tensorLaw (fun b => signedIntegral (ϱ b (σ b)).weight) := fun σ =>
    tensorLaw_smul (fun b => c b (σ b)) (fun b => signedIntegral (ϱ b (σ b)).weight)
  unfold multilinearIntegral at hM ⊢
  rw [LinearMap.sum_apply]
  simp only [hsplit, LinearMap.smul_apply, smul_eq_mul]
  calc |∑ σ : ∀ b, I b, (∏ b, c b (σ b)) *
        (tensorLaw fun b => signedIntegral (ϱ b (σ b)).weight) (fun z => ∏ v, G v (z v))|
      ≤ ∑ σ : ∀ b, I b, |∏ b, c b (σ b)| *
          |(tensorLaw fun b => signedIntegral (ϱ b (σ b)).weight) (fun z => ∏ v, G v (z v))| :=
        (abs_sum_le_sum_abs _ _).trans (le_of_eq (sum_congr rfl fun σ _ => abs_mul _ _))
    _ ≤ ∑ σ : ∀ b, I b, |∏ b, c b (σ b)| * M :=
        sum_le_sum fun σ _ => mul_le_mul_of_nonneg_left (hM σ) (abs_nonneg _)
    _ = (∏ b, ∑ i, |c b i|) * M := by
        rw [← sum_mul, Fintype.prod_sum]
        simp only [abs_prod]

end Components

section Kernels

/-- A tensor product of substochastic matrices is substochastic. -/
theorem piKron_substochastic {K : Type} [Fintype K] [DecidableEq K] {Ω : K → Type}
    [∀ j, Fintype (Ω j)] (A : ∀ j, Matrix (Ω j) (Ω j) ℝ) (h0 : ∀ j x y, 0 ≤ A j x y)
    (h1 : ∀ j x, ∑ y, A j x y ≤ 1) :
    (∀ x y, 0 ≤ piKron A x y) ∧ ∀ x, ∑ y, piKron A x y ≤ 1 := by
  refine ⟨fun x y => prod_nonneg fun j _ => h0 j (x j) (y j), fun x => ?_⟩
  have hs : ∑ y, piKron A x y = ∏ j, ∑ y, A j (x j) y :=
    (Fintype.prod_sum (fun j y => A j (x j) y)).symm
  rw [hs]
  exact prod_le_one₀ (fun j _ => sum_nonneg fun y _ => h0 j (x j) y) (fun j _ => h1 j (x j))

theorem meanMatrix_substochastic (Ω : Type) [Fintype Ω] :
    (∀ x y, 0 ≤ meanMatrix Ω x y) ∧ ∀ x, ∑ y, meanMatrix Ω x y ≤ 1 := by
  refine ⟨fun x y => inv_nonneg.mpr (Nat.cast_nonneg _), fun x => ?_⟩
  simp only [meanMatrix_apply, sum_const, card_univ, nsmul_eq_mul]
  by_cases hc : (Fintype.card Ω : ℝ) = 0
  · rw [hc]; norm_num
  · rw [mul_inv_cancel₀ hc]

theorem shiftMatrix_one_apply (K : ℕ) [NeZero K] (b b' : ZMod K) :
    shiftMatrix (1 : ZMod K) b b' = if b' = b + 1 then 1 else 0 := by
  unfold shiftMatrix convMatrix
  beta_reduce
  by_cases hb : b' = b + 1
  · rw [ite_eq_left hb, ite_eq_left (show b' - b = 1 by rw [hb]; ring)]
  · have hne : ¬ b' - b = 1 := fun h' => hb (by rw [sub_eq_iff_eq_add] at h'; rw [h', add_comm])
    rw [ite_eq_right hb, ite_eq_right hne]

theorem sum_shiftMatrix_one (K : ℕ) [NeZero K] (b : ZMod K) :
    ∑ b', shiftMatrix (1 : ZMod K) b b' = 1 := by
  simp only [shiftMatrix_one_apply, sum_ite_eq', mem_univ, ite_true]

theorem wrapShift_substochastic (K : ℕ) [NeZero K] :
    (∀ x y, 0 ≤ wrapShift K x y) ∧ ∀ x, ∑ y, wrapShift K x y ≤ 1 := by
  refine ⟨fun x y => ?_, fun x => ?_⟩
  · unfold wrapShift
    split_ifs
    · rw [shiftMatrix_one_apply]; split_ifs <;> norm_num
    · exact le_refl 0
  · unfold wrapShift
    by_cases hx : x = 0
    · simp only [hx, ite_true, sum_shiftMatrix_one, le_refl]
    · simp only [hx, ite_false, sum_const_zero, zero_le_one]

theorem nowrapShift_substochastic (K : ℕ) [NeZero K] :
    (∀ x y, 0 ≤ nowrapShift K x y) ∧ ∀ x, ∑ y, nowrapShift K x y ≤ 1 := by
  refine ⟨fun x y => ?_, fun x => ?_⟩
  · unfold nowrapShift
    split_ifs
    · exact le_refl 0
    · rw [shiftMatrix_one_apply]; split_ifs <;> norm_num
  · unfold nowrapShift
    by_cases hx : x = 0
    · simp only [hx, ite_true, sum_const_zero, zero_le_one]
    · simp only [hx, ite_false, sum_shiftMatrix_one, le_refl]

theorem convMatrix_substochastic {G : Type} [AddCommGroup G] [Fintype G] (μ : G → ℝ)
    (hμ : ∀ r, 0 ≤ μ r) (hμ1 : ∑ r, μ r = 1) :
    (∀ x y, 0 ≤ convMatrix μ x y) ∧ ∀ x, ∑ y, convMatrix μ x y ≤ 1 := by
  refine ⟨fun x y => hμ _, fun x => le_of_eq ?_⟩
  rw [← hμ1]
  exact Fintype.sum_equiv (Equiv.subRight x) _ _ (fun y => rfl)

variable {P : Type} [Fintype P] [DecidableEq P] (pr h : P → ℕ) [∀ q, NeZero (pr q ^ h q)]

theorem coordTransitionWith_substochastic {A : Matrix (ZMod blockScale) (ZMod blockScale) ℝ}
    (hA : (∀ x y, 0 ≤ A x y) ∧ ∀ x, ∑ y, A x y ≤ 1) {μe : ∀ q, ZMod (pr q ^ h q) → ℝ}
    (hμ : ∀ q r, 0 ≤ μe q r) (hμ1 : ∀ q, ∑ r, μe q r = 1) :
    (∀ x y, 0 ≤ piKron (coordTransitionWith blockScale pr h A μe) x y) ∧
      ∀ x, ∑ y, piKron (coordTransitionWith blockScale pr h A μe) x y ≤ 1 := by
  apply piKron_substochastic
  · intro j
    cases j with
    | none => exact hA.1
    | some q => exact (convMatrix_substochastic (μe q) (hμ q) (hμ1 q)).1
  · intro j
    cases j with
    | none => exact hA.2
    | some q => exact (convMatrix_substochastic (μe q) (hμ q) (hμ1 q)).2

omit [DecidableEq P] [∀ q, NeZero (pr q ^ h q)] in
/-- **The support of the nonwrapping transition**: a pair of indices `(x, y)` charged by the
nonwrapping coupled transition has `b = x_none ≠ 0` (the interval `I_b`, `1 ≤ b ≤ K − 1`)
and `y = (b + 1, s + r)` with an increment `r` in the support of the increment law. -/
theorem nowrap_support {μe : ∀ q, ZMod (pr q ^ h q) → ℝ} {x y : ∀ j, CoordSpace blockScale pr h j}
    (hxy : piKron (coordTransitionWith blockScale pr h (nowrapShift blockScale) μe) x y ≠ 0) :
    x none ≠ 0 ∧ y = nextIndex pr h x (fun q => y (some q) - x (some q)) ∧
      ∀ q, μe q (y (some q) - x (some q)) ≠ 0 := by
  have hj : ∀ j, coordTransitionWith blockScale pr h (nowrapShift blockScale) μe j (x j) (y j) ≠ 0 :=
    fun j => (prod_ne_zero_iff.mp hxy) j (mem_univ j)
  have h0 := hj none
  change nowrapShift blockScale (x none) (y none) ≠ 0 at h0
  unfold nowrapShift at h0
  by_cases hx : x none = 0
  · exact absurd (by rw [ite_eq_left hx]) h0
  · rw [ite_eq_right hx, shiftMatrix_one_apply] at h0
    have hy : y none = x none + 1 := by
      by_contra hne
      exact h0 (ite_eq_right hne)
    refine ⟨hx, ?_, fun q => ?_⟩
    · funext j
      cases j with
      | none => exact hy
      | some q => exact (add_sub_cancel (x (some q)) (y (some q))).symm
    · exact hj (some q)

end Kernels

/-! ## The nonwrapping terms are cancellation remainders -/

section Main

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  (hcop : Pairwise (Nat.Coprime on fun q => pr q ^ h q))
  {E : Type} [Fintype E] [DecidableEq E]

namespace ComparisonData

/-- **The nonwrapping terms of `lem:record:wrap-expansion` are cancellation remainders**
(the step "Nonwrapping terms" of its proof). If `lem:record:density-can` holds
(`DensityCancellation`, at the threshold `P₅` of (CP1) and the prefix data of (CP0)) and the
coefficients of the product components are bounded, `∏_𝔟 ∑_i |c_{𝔟,i}| ν_{𝔟,i}(1) ≤ C_ν` at
every scale (the paper bounds them by `𝔳_ν e^{P+S}`), then every coupled form
`I_{ν,𝒮,𝒲}` with `𝒲 ⊊ 𝒮` is at most `C_ν · 2 C_can L^{-σ} α`. The proof: pick a
nonwrapping active query `e ∈ 𝒮 \ 𝒲`; every pair of indices `(ω, ω')` charged by the
coupled transition has `1 ≤ b_e ≤ K − 1` and `ω'_e = (b_e + 1, s_e + r_e)` with `r_e` a
nonvanishing square class ((CP0)(d)); the cut form is the multilinear integral of the slot
inputs (`form_productHalf`), with `g^{I_{b_e}, M₀, s_e}` at `u_e` and
`g^{I_{b_e+1}, M₀, s_e + r_e}` at `v_e`; each product component of `ν` is a product of
probability laws satisfying (a), (b) of `lem:record:density-can` by (CP4)(a); and the
coupled transition is substochastic. -/
theorem nonwrappingCancellation_of_densityCancellation (D : ComparisonData m₀ p pr h E)
    (hDC : DensityCancellation m₀ p pr h D.R.P5 D.S.pp D.S.ep)
    (hcoef : ∃ Cν : ℝ, ∀ L, ∏ b, ∑ i, |D.CL.cc L b i| * D.CL.cmass L b i ≤ Cν) :
    D.NonwrappingCancellation hcop := by
  obtain ⟨Ccan, hCcan, Lstar, hDC⟩ := hDC
  obtain ⟨Cν, hCν⟩ := hcoef
  have hCν0 : 0 ≤ Cν := le_trans (prod_nonneg fun b _ => sum_nonneg fun i _ =>
    mul_nonneg (abs_nonneg _) (D.CL.cmass_pos 0 b i).le) (hCν 0)
  refine ⟨Cν * (2 * Ccan), mul_nonneg hCν0 (by positivity), ?_⟩
  unfold AtCounterexamples
  filter_upwards [eventually_ge_atTop Lstar] with L hL
  intro C _ _ A hA _ S W hWS hne
  obtain ⟨e, heS, heW⟩ :=
    Finset.exists_of_ssubset (Finset.ssubset_iff_subset_ne.mpr ⟨hWS, hne⟩)
  rw [remainder_mul]
  have hrem0 : 0 ≤ remainder (2 * Ccan) L A := remainder_nonneg (by positivity) L A
  have hB0 : 0 ≤ Cν * remainder (2 * Ccan) L A := mul_nonneg hCν0 hrem0
  -- the coupled transition is substochastic
  have hfac : ∀ e' : E,
      (∀ x y, 0 ≤ (if e' ∈ W then
          piKron (coordTransitionWith blockScale pr h (wrapShift blockScale) (D.S.index.μ e'))
        else if e' ∈ S then
          piKron (coordTransitionWith blockScale pr h (nowrapShift blockScale) (D.S.index.μ e'))
        else meanMatrix (∀ j, CoordSpace blockScale pr h j)) x y) ∧
      ∀ x, ∑ y, (if e' ∈ W then
          piKron (coordTransitionWith blockScale pr h (wrapShift blockScale) (D.S.index.μ e'))
        else if e' ∈ S then
          piKron (coordTransitionWith blockScale pr h (nowrapShift blockScale) (D.S.index.μ e'))
        else meanMatrix (∀ j, CoordSpace blockScale pr h j)) x y ≤ 1 := by
    intro e'
    split_ifs
    · exact coordTransitionWith_substochastic pr h (wrapShift_substochastic blockScale)
        (D.S.index.hμ e') (D.S.index.hμ1 e')
    · exact coordTransitionWith_substochastic pr h (nowrapShift_substochastic blockScale)
        (D.S.index.hμ e') (D.S.index.hμ1 e')
    · exact meanMatrix_substochastic _
  have hK := piKron_substochastic _ (fun e' => (hfac e').1) (fun e' => (hfac e').2)
  -- the bound at one pair of indices charged by the coupled transition
  have hbound : ∀ ω η : E → ∀ j, CoordSpace blockScale pr h j,
      piKron (fun e' => if e' ∈ W then
          piKron (coordTransitionWith blockScale pr h (wrapShift blockScale) (D.S.index.μ e'))
        else if e' ∈ S then
          piKron (coordTransitionWith blockScale pr h (nowrapShift blockScale) (D.S.index.μ e'))
        else meanMatrix (∀ j, CoordSpace blockScale pr h j)) ω η ≠ 0 →
      |reservedCut.form (tensorLaw (D.CL.ν L))
          (productHalf D.S.Q.u (fun e => atomInput m₀ p pr h hcop L A e) (atomLift m₀ p L A) ω)
          (productHalf D.S.Q.w (fun e => atomInput m₀ p pr h hcop L A e) (atomLift m₀ p L A) η)| ≤
        Cν * remainder (2 * Ccan) L A := by
    intro ω η hk
    have he := (prod_ne_zero_iff.mp hk) e (mem_univ e)
    beta_reduce at he
    rw [ite_eq_right heW, ite_eq_left heS] at he
    obtain ⟨hb, hη, hr⟩ := nowrap_support pr h he
    set r : ∀ q, ZMod (pr q ^ h q) := fun q => η e (some q) - ω e (some q) with hrdef
    have hrsq : ∀ q, IsNonvanishingSquareCoord (pr q) (h q) (r q) :=
      fun q => D.S.index.hsq e q _ (hr q)
    have hst : D.S.Q.source e ≠ D.S.Q.target e := by
      intro heq
      have h1 : D.S.Q.source e ∈ reservedCut.half := (D.S.Q.u e).2
      have h2 : D.S.Q.target e ∉ reservedCut.half := reservedCut.flip_not_mem (D.S.Q.w e).2
      exact h2 (heq ▸ h1)
    rw [form_productHalf _ D.S.Q.hu D.S.Q.hw]
    have hcomp := abs_multilinear_le_components (fun b i => D.CL.cc L b i * D.CL.cmass L b i)
      (D.CL.claw L)
      (pairInputs D.S.Q.u D.S.Q.w (fun e => atomInput m₀ p pr h hcop L A e)
        (fun e => atomInput m₀ p pr h hcop L A e) (atomLift m₀ p L A) ω η)
      (M := remainder (2 * Ccan) L A) (fun σ => by
        refine hDC L hL A hA (fun b => D.CL.claw L b (σ b)) (fun b => D.CL.unif L b (σ b))
          (D.S.Q.source e) (D.S.Q.target e) hst
          (fun j hj => (D.CL.mixing L j (σ (some j)) hj).2 e)
          (fun b _ z hz => D.CL.accept L b (σ b) z hz e)
          ((crtEquiv blockScale pr h hcop).symm (ω e)).1
          ((crtEquiv blockScale pr h hcop).symm (ω e)).2
          ((ZMod.prodEquivPi (fun q => pr q ^ h q) hcop).symm r) hb
          (isNonvanishingSquareClass_crt pr h hcop D.S.pr_prime D.S.pr_inj D.S.h_two r hrsq)
          _ ?_ ?_ ?_
        · show pairInputs D.S.Q.u D.S.Q.w _ _ _ ω η ((D.S.Q.u e : Slot)) = _
          rw [pairInputs_plus, halfInput_source D.S.Q.hu]
          rfl
        · show pairInputs D.S.Q.u D.S.Q.w _ _ _ ω η (reservedCut.flip (D.S.Q.w e : Slot)) = _
          rw [pairInputs_minus, halfInput_source D.S.Q.hw, atomInput_eq_indexInputAt, hη,
            crtEquiv_symm_nextIndex]
        · intro w' _ _
          rcases pairInputs_cases D.S.Q.u D.S.Q.w (fun e => atomInput m₀ p pr h hcop L A e)
              (fun e => atomInput m₀ p pr h hcop L A e) (atomLift m₀ p L A) ω η w' with
            h1 | ⟨e', h1⟩ | ⟨e', h1⟩
          · exact Or.inl h1
          · exact Or.inr ⟨(crtEquiv blockScale pr h hcop).symm (ω e'), h1⟩
          · exact Or.inr ⟨(crtEquiv blockScale pr h hcop).symm (η e'), h1⟩)
    refine hcomp.trans (mul_le_mul_of_nonneg_right ?_ hrem0)
    have habs : ∀ b, ∑ i, |D.CL.cc L b i * D.CL.cmass L b i| =
        ∑ i, |D.CL.cc L b i| * D.CL.cmass L b i := fun b =>
      sum_congr rfl fun i _ => by rw [abs_mul, abs_of_pos (D.CL.cmass_pos L b i)]
    simp only [habs]
    exact hCν L
  -- assemble: the expectation over the indices and the sum over the coupled indices
  unfold wrapForm
  apply FiniteLaw.abs_expect_le_const
  intro ω
  have hact : act (piKron (fun e' => if e' ∈ W then
          piKron (coordTransitionWith blockScale pr h (wrapShift blockScale) (D.S.index.μ e'))
        else if e' ∈ S then
          piKron (coordTransitionWith blockScale pr h (nowrapShift blockScale) (D.S.index.μ e'))
        else meanMatrix (∀ j, CoordSpace blockScale pr h j)))
        (productHalf D.S.Q.w (fun e => atomInput m₀ p pr h hcop L A e) (atomLift m₀ p L A)) ω =
      ∑ η, (piKron (fun e' => if e' ∈ W then
          piKron (coordTransitionWith blockScale pr h (wrapShift blockScale) (D.S.index.μ e'))
        else if e' ∈ S then
          piKron (coordTransitionWith blockScale pr h (nowrapShift blockScale) (D.S.index.μ e'))
        else meanMatrix (∀ j, CoordSpace blockScale pr h j)) ω η) •
        productHalf D.S.Q.w (fun e => atomInput m₀ p pr h hcop L A e) (atomLift m₀ p L A) η := by
    funext a
    simp only [act, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [hact, ← cutBilin_apply, map_sum]
  simp only [map_smul, cutBilin_apply, smul_eq_mul]
  calc |∑ η, _ * _| ≤ ∑ η : E → ∀ j, CoordSpace blockScale pr h j, |_ * _| :=
        abs_sum_le_sum_abs _ _
    _ ≤ ∑ η : E → ∀ j, CoordSpace blockScale pr h j,
          piKron (fun e' => if e' ∈ W then
            piKron (coordTransitionWith blockScale pr h (wrapShift blockScale) (D.S.index.μ e'))
          else if e' ∈ S then
            piKron (coordTransitionWith blockScale pr h (nowrapShift blockScale) (D.S.index.μ e'))
          else meanMatrix (∀ j, CoordSpace blockScale pr h j)) ω η *
            (Cν * remainder (2 * Ccan) L A) := by
        apply sum_le_sum
        intro η _
        rw [abs_mul, abs_of_nonneg (hK.1 ω η)]
        by_cases hk : piKron (fun e' => if e' ∈ W then
            piKron (coordTransitionWith blockScale pr h (wrapShift blockScale) (D.S.index.μ e'))
          else if e' ∈ S then
            piKron (coordTransitionWith blockScale pr h (nowrapShift blockScale) (D.S.index.μ e'))
          else meanMatrix (∀ j, CoordSpace blockScale pr h j)) ω η = 0
        · rw [hk, zero_mul, zero_mul]
        · exact mul_le_mul_of_nonneg_left (hbound ω η hk) (hK.1 ω η)
    _ = (∑ η : E → ∀ j, CoordSpace blockScale pr h j,
          piKron (fun e' => if e' ∈ W then
            piKron (coordTransitionWith blockScale pr h (wrapShift blockScale) (D.S.index.μ e'))
          else if e' ∈ S then
            piKron (coordTransitionWith blockScale pr h (nowrapShift blockScale) (D.S.index.μ e'))
          else meanMatrix (∀ j, CoordSpace blockScale pr h j)) ω η) *
            (Cν * remainder (2 * Ccan) L A) := by rw [sum_mul]
    _ ≤ 1 * (Cν * remainder (2 * Ccan) L A) := mul_le_mul_of_nonneg_right (hK.2 ω) hB0
    _ = Cν * remainder (2 * Ccan) L A := one_mul _

end ComparisonData

end Main

/-! ## The coefficients of the product components (the mass of `ν`) -/

section Coefficients

theorem form_one_one {X : Type} [Fintype X] (κ : SlotMeasure X) :
    reservedCut.form κ (fun _ => 1) (fun _ => 1) = mass κ := by
  unfold ReflectionCut.form mass
  simp only [mul_one]

/-- A bracket `(π D, K; K*, π D) ⪰_ι 0` with a probability law `D` bounds the mass of `K`:
`|K(1)| ≤ π` (the all-ones half-function in `lem:record:block-gram`(a)). -/
theorem abs_mass_le_of_bracket {X : Type} [Fintype X] {D K : SlotMeasure X} {π : ℝ}
    (hπ : 0 ≤ π) (hD : mass D = 1) (h : reservedCut.Bracket (π • D) K (π • D)) :
    |mass K| ≤ π := by
  have hcs := h.cauchy_schwarz_sq (fun _ => 1) (fun _ => 1)
  have hm : mass (π • D) = π := by
    unfold mass at hD ⊢
    rw [LinearMap.smul_apply, smul_eq_mul, hD, mul_one]
  simp only [form_one_one, hm] at hcs
  by_contra hlt
  push Not at hlt
  nlinarith [abs_nonneg (mass K)]

theorem mass_skewPart {X : Type} [Fintype X] (Δ : SlotMeasure X) :
    mass (skewPart reservedCut Δ) = 0 := by
  unfold skewPart mass
  rw [LinearMap.smul_apply, LinearMap.sub_apply, reflect_apply]
  simp

theorem mass_signedIntegral {X : Type} [Fintype X] (μ : FiniteLaw (Slot → X)) :
    mass (signedIntegral μ.weight) = 1 := by
  show ∑ z, μ.weight z * 1 = 1
  simp only [mul_one, μ.total]

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

namespace ComparisonData

variable (D : ComparisonData m₀ p pr h E)

omit [DecidableEq P] in
theorem one_le_selectionFactor (L : ℕ) (b : PaperAtom J L) :
    1 ≤ selectionFactor p D.S.selPre L b := by
  cases b with
  | none => exact D.S.one_le_selPre
  | some j =>
      exact Real.one_le_rpow (by exact_mod_cast (D.S.p_prime L j).one_lt.le)
        (mul_nonneg zero_le_two decay_pos.le)

omit [DecidableEq P] in
theorem mass_refLaw (L : ℕ) (b : PaperAtom J L) : mass (D.R.law p L b) = 1 := by
  cases b with
  | none => exact mass_signedIntegral D.R.μ₀
  | some j => exact mass_signedIntegral (D.R.μp (p L j))

omit [DecidableEq P] in
/-- On a first-stage atom `λ_𝔟(1) = 1 + (ρ_𝔟 − μ_𝔟)(1) ≤ 1 + p_𝔟`: the record differences of
(CP2)(b) have mass zero. -/
theorem mass_lam_le (L : ℕ) (b : PaperAtom J L) : mass (D.FS.lam L b) ≤ 1 + D.FS.pvar L b := by
  have hlam : mass (D.FS.lam L b) = mass (D.FS.ρ L b) := by
    unfold FirstStage.lam mass
    rw [LinearMap.add_apply, LinearMap.sum_apply]
    have h0 : ∀ i, (D.FS.κ' L b i - D.FS.κ L b i) (fun _ => 1) = 0 := fun i => by
      rw [LinearMap.sub_apply]
      exact sub_eq_zero.mpr (D.FS.mass_eq L b i)
    simp only [h0, sum_const_zero, add_zero]
  have hρ := congrArg mass (D.FS.ρ_sub L b)
  have hμ := D.mass_refLaw L b
  unfold mass at hρ hμ hlam ⊢
  rw [LinearMap.sub_apply, LinearMap.sum_apply, hμ] at hρ
  simp only [LinearMap.smul_apply, smul_eq_mul] at hρ
  rw [hlam]
  unfold FirstStage.pvar
  have hle : ∑ i, D.FS.ca L b i * D.FS.κa L b i (fun _ => 1) ≤
      ∑ i, |D.FS.ca L b i| * mass (D.FS.κa L b i) * selectionFactor p D.S.selPre L b := by
    apply sum_le_sum
    intro i _
    have hm : 0 ≤ mass (D.FS.κa L b i) := mass_nonneg_of_nonneg (D.FS.κa_pos L b i).1
    calc D.FS.ca L b i * D.FS.κa L b i (fun _ => 1)
        ≤ |D.FS.ca L b i| * mass (D.FS.κa L b i) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) hm
      _ ≤ |D.FS.ca L b i| * mass (D.FS.κa L b i) * selectionFactor p D.S.selPre L b :=
          le_mul_of_one_le_right (mul_nonneg (abs_nonneg _) hm) (D.one_le_selectionFactor L b)
  linarith

omit [DecidableEq P] in
/-- The mass of `ν_𝔟`: `ν_𝔟(1) ≤ 1 + p_𝔟 + s_𝔟` (the skew parts have mass zero and the
bracket of (CP4)(b) at the all-ones vector gives `|ζ^s_{𝔟,t}(1)| ≤ π̃^s_{𝔟,t}`). -/
theorem mass_nu_le (L : ℕ) (b : PaperAtom J L) :
    mass (D.CL.ν L b) ≤ 1 + D.FS.pvar L b + symTotal (D.CL.π L) b := by
  have hch := congrArg mass (D.CL.change L b)
  have hsum : mass (∑ t, D.CL.Δ L b t) = ∑ t, mass (D.CL.ζ L b t .sym) := by
    unfold mass
    rw [LinearMap.sum_apply]
    apply sum_congr rfl
    intro t _
    have h1 := symPart_add_skewPart reservedCut (D.CL.Δ L b t)
    have h2 := mass_skewPart (D.CL.Δ L b t)
    unfold mass at h2
    rw [← h1, LinearMap.add_apply, h2, add_zero]
    rfl
  have hν : mass (D.CL.ν L b) = mass (D.FS.lam L b) + ∑ t, mass (D.CL.ζ L b t .sym) := by
    rw [← hsum, ← hch]
    unfold mass
    rw [LinearMap.sub_apply]
    unfold ComparisonLaw.ν
    ring
  have hζ : ∀ t, mass (D.CL.ζ L b t .sym) ≤ D.CL.π L b t .sym := fun t => by
    have h1 := abs_mass_le_of_bracket (D.CL.πt_nonneg L b t .sym) (D.CL.D_prob L b t .sym).2
      (D.CL.bracket L b t .sym)
    calc mass (D.CL.ζ L b t .sym) ≤ D.CL.πt L b t .sym := (le_abs_self _).trans h1
      _ ≤ D.CL.π L b t .sym :=
          le_mul_of_one_le_right (D.CL.πt_nonneg L b t .sym) (D.one_le_selectionFactor L b)
  rw [hν]
  have := D.mass_lam_le L b
  have hs : ∑ t, mass (D.CL.ζ L b t .sym) ≤ symTotal (D.CL.π L) b := sum_le_sum fun t _ => hζ t
  linarith

omit [DecidableEq P] in
theorem mass_nu_eq (L : ℕ) (b : PaperAtom J L) :
    mass (D.CL.ν L b) = ∑ i, D.CL.cc L b i * D.CL.cmass L b i := by
  unfold ComparisonLaw.ν
  unfold mass
  rw [LinearMap.sum_apply]
  apply sum_congr rfl
  intro i _
  rw [LinearMap.smul_apply, smul_eq_mul]
  have h1 := mass_signedIntegral (D.CL.claw L b i)
  unfold mass at h1
  rw [h1, mul_one]

omit [DecidableEq P] in
/-- **The coefficients of the product components** (proof of `lem:record:wrap-expansion`,
"The mass of `ν`"): `∏_𝔟 |ν|_𝔟 ≤ 𝔳_ν ν(1) ≤ 𝔳_ν e^{P+S}`, at every scale. -/
theorem coefficient_bound (L : ℕ) :
    ∏ b, ∑ i, |D.CL.cc L b i| * D.CL.cmass L b i ≤ D.CL.vfac * Real.exp (D.FS.P + D.CL.S) := by
  have hpos : ∀ b, 0 < ∑ i, D.CL.cc L b i * D.CL.cmass L b i := D.CL.mass_pos L
  have hsplit : ∏ b, ∑ i, |D.CL.cc L b i| * D.CL.cmass L b i =
      (∏ b, (∑ i, |D.CL.cc L b i| * D.CL.cmass L b i) / (∑ i, D.CL.cc L b i * D.CL.cmass L b i)) *
        ∏ b, ∑ i, D.CL.cc L b i * D.CL.cmass L b i := by
    rw [← prod_mul_distrib]
    exact prod_congr rfl fun b _ => (div_mul_cancel₀ _ (hpos b).ne').symm
  rw [hsplit]
  have hratio0 : 0 ≤ ∏ b, (∑ i, |D.CL.cc L b i| * D.CL.cmass L b i) /
      (∑ i, D.CL.cc L b i * D.CL.cmass L b i) :=
    prod_nonneg fun b _ => div_nonneg (sum_nonneg fun i _ =>
      mul_nonneg (abs_nonneg _) (D.CL.cmass_pos L b i).le) (hpos b).le
  have hvfac0 : 0 ≤ D.CL.vfac := hratio0.trans (D.CL.vfac_bound L)
  have hsym0 : ∀ b, 0 ≤ symTotal (D.CL.π L) b := fun b => sum_nonneg fun t _ =>
    mul_nonneg (D.CL.πt_nonneg L b t .sym) (D.selectionFactor_nonneg L b)
  have hmass : ∏ b, ∑ i, D.CL.cc L b i * D.CL.cmass L b i ≤ Real.exp (D.FS.P + D.CL.S) := by
    calc ∏ b, ∑ i, D.CL.cc L b i * D.CL.cmass L b i
        ≤ ∏ b, Real.exp (D.FS.pvar L b + symTotal (D.CL.π L) b) := by
          apply prod_le_prod₀ (fun b _ => (hpos b).le)
          intro b _
          have h1 := D.mass_nu_le L b
          rw [D.mass_nu_eq L b] at h1
          have h2 := Real.add_one_le_exp (D.FS.pvar L b + symTotal (D.CL.π L) b)
          linarith
      _ = Real.exp (∑ b, (D.FS.pvar L b + symTotal (D.CL.π L) b)) := (Real.exp_sum _ _).symm
      _ ≤ Real.exp (D.FS.P + D.CL.S) := by
          apply Real.exp_le_exp.mpr
          rw [sum_add_distrib]
          exact add_le_add (D.FS.P_total L) (D.CL.S_total L)
  exact mul_le_mul (D.CL.vfac_bound L) hmass (prod_nonneg fun b _ => (hpos b).le) hvfac0

end ComparisonData

end Coefficients

section Corollaries

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  (hcop : Pairwise (Nat.Coprime on fun q => pr q ^ h q))
  {E : Type} [Fintype E] [DecidableEq E]

namespace ComparisonData

/-- **The nonwrapping terms from `lem:record:density-can` alone**: with the coefficient bound
`𝔳_ν e^{P+S}` of the proof of `lem:record:wrap-expansion` (`coefficient_bound`), the
hypothesis `NonwrappingCancellation` of Theorem C follows from `DensityCancellation`. -/
theorem nonwrappingCancellation_of_densityCancellation' (D : ComparisonData m₀ p pr h E)
    (hDC : DensityCancellation m₀ p pr h D.R.P5 D.S.pp D.S.ep) :
    D.NonwrappingCancellation hcop :=
  D.nonwrappingCancellation_of_densityCancellation hcop hDC ⟨_, D.coefficient_bound⟩

/-- **Theorem C with `lem:record:density-can` as the analytic input of the nonwrapping
terms** (`theoremC` with `NonwrappingCancellation` replaced by `DensityCancellation`). -/
theorem theoremC_of_densityCancellation (D : ComparisonData m₀ p pr h E) {𝓔 : ℝ}
    (h𝓔 : D.Ψ ≤ 𝓔) (hΘ : D.Theta 𝓔 < 1) (hE1 : D.EnvelopeBound) (hSF : D.SharpFirstTerms)
    (hDC : DensityCancellation m₀ p pr h D.R.P5 D.S.pp D.S.ep)
    (hwr : D.WrappingTerms hcop) (henv : D.EnvelopeEnergies hcop)
    (hunit : ∃ p₀ : ℕ, ∀ (q : ℕ) [NeZero q], q.Prime → p₀ ≤ q → MixedLpBound (D.R.μp q) 36 1) :
    PowerSavingBound :=
  D.theoremC hcop h𝓔 hΘ hE1 hSF (D.nonwrappingCancellation_of_densityCancellation' hcop hDC) hwr
    henv hunit

end ComparisonData

end Corollaries

end Sarkozy.TheoremC
