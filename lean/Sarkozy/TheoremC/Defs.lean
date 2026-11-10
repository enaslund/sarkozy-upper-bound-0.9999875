module

public import Sarkozy.PaperFrame.WrapSplit
public import Sarkozy.PaperFrame.Reference
public import Sarkozy.RecordExpansion.All
public import Sarkozy.Comparison.FoldedEnergy
public import Sarkozy.Comparison.AnalyticStage
public import Sarkozy.Mixing.Main

@[expose] public section

/-!
# The comparison data (CP0)–(CP8) of Theorem C

`paper/sections/09_comparison_theorem.tex`, `def:cp0` … `def:cp8`, with `def:price`,
`def:cp:records` and `def:robust`, as Lean structures over the paper's objects of
`Sarkozy.PaperFrame`: the atoms `PaperAtom J L` (the prefix and one atom per tail prime),
the lift `F_A = atomLift`, the inputs `g^{I_b,M₀,s} = atomInput`, the coupled index
`paperCoupledIndex` and the reference law `refLaws μ₀ μp` (whose tensor product is
`paperLaw`). The wording of each field follows the paper; deviations are listed here.

**Representation.**
* A finite signed measure on `X_𝔟^V` is a linear functional
  `SlotMeasure X = ((Slot → X) → ℝ) →ₗ[ℝ] ℝ` on functions of the 72 slot labels; products
  over atoms are `tensorLaw`; energies are `diagonalIntegral` (= the cut form at `X̄`).
  The laws attached to an atom are given at every scale (`∀ L b`); the paper's
  scale independence of the atom laws (CP0)(b) is not imposed, because Theorem C uses it
  only through the remark after `def:price`: a total over `𝒜` bounds the corresponding
  sum over `𝒜_N` at every scale. Accordingly every total (`P`, `d_j`, `v_j`, `U_0`, `S`,
  `A`, `T`) is a number that bounds the sum over the atoms of every scale.
* **Atoms.** All prefix blocks are merged into the single prefix atom of `PaperFrame`
  (alphabet `ResidueSpace m₀`); its selection factor is a parameter `selPre ≥ 1` (the
  paper's product of the factors of the merged blocks). This is a special case of the
  paper's atom partition, recorded in the report.
* **Exponents.** `a = decay`, `θ = densityExponent`, `d = 72`, `K = blockScale`,
  `γ = 255/1024` are the project's constants. Since 7 November 2026 `densityExponent = 1`
  (the baseline induction), so `thm:comparison`'s assumption `0 < θ ≤ 1` holds. (Before, it was
  the four-routes exponent `ϑ = 1.014587 > 1`.) The closing algebra of Theorem C does not use
  `θ ≤ 1`; the analytic inputs do (`prop:record:density-structured` uses Jensen with `θ ≤ 1`).
* **Robust bounds** (`def:robust`) are encoded as in `Sarkozy.Comparison.Criterion`
  (`RobustUpper`, `RobustLower`): at every least normalized counterexample of every large
  scale, uniformly in the induction constant `C ≥ 1`, the bound holds with a relative
  error `ε(L) → 0` and a density-linear remainder `c L^{-σ} α`.
* **Admissibility** (`def:admissible`, (CP8)(a)): (O1) is imposed on every law named in
  (CP2)–(CP6) (nonnegative, uniform one-slot marginals, `IsPositiveRecord`). (O2)–(O4)
  are conditions on the reductions inside the proofs of the analytic inputs and are not
  conditions on the data here.
-/

open Filter Finset Function
open scoped Topology BigOperators Matrix

namespace Sarkozy.TheoremC

open Sarkozy.FourierArithmetic Sarkozy.Functional Sarkozy.IndexSupport Sarkozy.Comparison
  Sarkozy.PaperFrame Sarkozy.RecordExpansion

/-! ## The exponents of (CP0)(b) -/

/-- (CP0)(b): the price exponent satisfies `0 < a < σ` (`a = decay`, `σ = 1/825`). -/
theorem decay_mem_Ioo : 0 < decay ∧ decay < cancellationDecay := by
  constructor <;> norm_num [decay, cancellationDecay]

/-- Since 7 November 2026 the project's density exponent is the baseline `ϑ = 1`, which lies in
the range `θ ≤ 1` of (CP0)(b). (Before, it was the four-routes exponent `ϑ = 1014587/10⁶ > 1`;
see the module docstring.) -/
theorem densityExponent_eq_one : densityExponent = 1 := rfl

/-! ## Measures, records and prices (`def:cp:records`, `def:price`) -/

section Measures

variable {X : Type} [Fintype X] [DecidableEq X]

/-- A finite signed measure on `X^V`, `V` the 72 slots. -/
abbrev SlotMeasure (X : Type) [Fintype X] : Type := ((Slot → X) → ℝ) →ₗ[ℝ] ℝ

/-- The mass `κ(1)`. -/
def mass (κ : SlotMeasure X) : ℝ := κ (fun _ => 1)

/-- The total variation `‖ζ‖_var = ∑_z |ζ({z})|`. -/
noncomputable def totalVar (ζ : SlotMeasure X) : ℝ := ∑ z, |lawDensity ζ z|

/-- A *record*: a nonnegative measure. -/
def IsNonneg (κ : SlotMeasure X) : Prop := ∀ f : (Slot → X) → ℝ, (∀ z, 0 ≤ f z) → 0 ≤ κ f

/-- A probability measure. -/
def IsProbability (κ : SlotMeasure X) : Prop := IsNonneg κ ∧ mass κ = 1

/-- All one-slot marginals are multiples of the uniform law. -/
def HasUniformSlotMarginals (κ : SlotMeasure X) : Prop :=
  ∀ (v : Slot) (g : X → ℝ), κ (fun z => g (z v)) = mass κ * ((∑ x, g x) / Fintype.card X)

/-- A *positive record* (`def:cp:records`): a record whose normalization is admissible; in
particular ((O1) of `def:admissible`) its one-slot marginals are uniform. -/
def IsPositiveRecord (κ : SlotMeasure X) : Prop := IsNonneg κ ∧ HasUniformSlotMarginals κ

/-- *Diagonal at a cut* `c` (`def:cp:records`): fixed samplewise by the reflection of `c`,
i.e. carried by the labellings `z` with `z ∘ c.flip = z`. At `ι = reservedCut`:
*reserved diagonal*. -/
def IsDiagonalAt (c : ReflectionCut Slot) (κ : SlotMeasure X) : Prop :=
  ∀ z, lawDensity κ z ≠ 0 → ∀ v, z (c.flip v) = z v

/-- `def:price`(b): `ζ` has *sharp bound* `d` relative to the nonnegative measure `κ` (of
mass `w`) at the cut `c`: for a probability law `π` on a finite set of shared labels,
`κ = w ∫ κ_s π(ds)` and `ζ = w ∫ K_s π(ds)` with probability measures `κ_s` and signed
measures `K_s` that satisfy `eq:record:sharp` at `c` relative to the half marginals of
`κ_s`, with the constant `d`, for every `s`. -/
def HasSharpBound (c : ReflectionCut Slot) (κ ζ : SlotMeasure X) (d : ℝ) : Prop :=
  ∃ (S : Type) (_ : Fintype S) (π : FiniteLaw S) (κs Ks : S → SlotMeasure X),
    (∀ s, IsProbability (κs s)) ∧
    κ = mass κ • ∑ s, π.weight s • κs s ∧ ζ = mass κ • ∑ s, π.weight s • Ks s ∧
    ∀ s, Sharp c (Ks s) (halfMarginalPlus c (κs s)) (halfMarginalMinus c (κs s)) d

/-- `def:price`(a): the *price* `‖ζ‖_var q_𝔟^{2a}` of a signed measure at an atom with
selection factor `sel = q_𝔟^{2a}`. -/
noncomputable def price (sel : ℝ) (ζ : SlotMeasure X) : ℝ := totalVar ζ * sel

/-- `def:price`(b): the *sharp price* `w d q_𝔟^{2a}` of a difference with sharp bound `d`
relative to a record of mass `w`. -/
noncomputable def sharpPrice (sel : ℝ) (κ : SlotMeasure X) (d : ℝ) : ℝ := mass κ * d * sel

/-- The joint law of `(z_u, z_v)` is uniform on `X × X`. Not used in the comparison data: at a
tail prime the paper requires uniformity on the strict-square pairs (`PairUniformOmega`), and
uniformity on `X × X` contradicts the acceptance of the query pairs (it charges the diagonal). -/
def PairUniform [Nonempty X] (ρ : FiniteLaw (Slot → X)) (u v : Slot) : Prop :=
  ∀ g : X → X → ℝ, ρ.expect (fun z => g (z u) (z v)) =
    (FiniteLaw.uniform (X × X)).expect (fun xy => g xy.1 xy.2)

end Measures

/-- The strict-square pairs `Ω_q = {(x, y) ∈ (ℤ/qℤ)² : y − x is a nonzero square}`. -/
def strictSquarePairs (q : ℕ) [NeZero q] : Finset (ZMod q × ZMod q) :=
  univ.filter (fun xy => xy.2 - xy.1 ≠ 0 ∧ IsSquare (xy.2 - xy.1))

/-- **The `(u, v)`-marginal is `Unif(Ω_q)`** (`(R4)` of `hyp:record:reference` for the accepted
parts, `lem:record:density-can`(a), `lem:tr:pairsupport`): the joint law of `(z_u, z_v)` is the
uniform law on the strict-square pairs `Ω_q`. -/
def PairUniformOmega {q : ℕ} [NeZero q] (ρ : FiniteLaw (Slot → ZMod q)) (u v : Slot) : Prop :=
  ∀ g : ZMod q → ZMod q → ℝ, ρ.expect (fun z => g (z u) (z v)) =
    (∑ xy ∈ strictSquarePairs q, g xy.1 xy.2) / (strictSquarePairs q).card

/-! ## The cuts, the queries and the index law (CP0) -/

/-- The family `𝔉` of cuts (`def:cp0`(a)): the chamber cuts of the two chamber
coordinates and the reserved cut `ι`. -/
def IsFamilyCut (c : ReflectionCut Slot) : Prop :=
  (∃ a, c = firstChamberCut a) ∨ (∃ a, c = secondChamberCut a) ∨ c = reservedCut

/-- The family contains the sorting sequence. -/
theorem isFamilyCut_of_sorting : ∀ c ∈ slotSortingCuts, IsFamilyCut c := by
  intro c hc
  simp only [slotSortingCuts, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with h | h | h | h | h | h | h <;> subst h
  · exact Or.inl ⟨0, rfl⟩
  · exact Or.inl ⟨4, rfl⟩
  · exact Or.inl ⟨0, rfl⟩
  · exact Or.inr (Or.inl ⟨0, rfl⟩)
  · exact Or.inr (Or.inl ⟨4, rfl⟩)
  · exact Or.inr (Or.inl ⟨0, rfl⟩)
  · exact Or.inr (Or.inr rfl)

/-- Reflection positivity at every cut of the family (`(R2)`). -/
def FamilyReflectionPositive {X : Type} [Fintype X] (κ : SlotMeasure X) : Prop :=
  ∀ c, IsFamilyCut c → c.Positive κ

theorem FamilyReflectionPositive.slot {X : Type} [Fintype X] {κ : SlotMeasure X}
    (h : FamilyReflectionPositive κ) : SlotReflectionPositive κ :=
  fun c hc => h c (isFamilyCut_of_sorting c hc)

/-- `def:cp0`(c): a family of `k = |E|` directed queries `e = (u_e, v_e)`, with sources
`u_e ∈ V_+` and reflected targets `ι v_e ∈ V_+` (`u e`, `w e` in the plus half of the
reserved cut). The `2k` endpoints are distinct: sources lie in `V_+` and targets in
`V_- = ι V_+`, and `u`, `w` are injective. (In Part V, `k = 6`.) -/
structure Queries (E : Type) where
  /-- The sources `u_e ∈ V_+`. -/
  u : E → reservedCut.Half
  /-- The reflected targets `ι v_e ∈ V_+`. -/
  w : E → reservedCut.Half
  hu : Function.Injective u
  hw : Function.Injective w

/-- The source slot `u_e`. -/
def Queries.source {E : Type} (Q : Queries E) (e : E) : Slot := (Q.u e : Slot)

/-- The target slot `v_e = ι(ι v_e)`. -/
def Queries.target {E : Type} (Q : Queries E) (e : E) : Slot := reservedCut.flip (Q.w e : Slot)

/-- A nonvanishing square increment at the coordinate `ℤ/p^hℤ` (the clause of
`def:nonvanishing-square-class`, `Sarkozy.Functional.IsNonvanishingSquareClass`, at one
prime): nonzero, of even valuation `2j`, with unit part a nonzero square modulo `p` (odd
`p`), resp. `≡ 1 (mod 8)` with `h - 2j ≥ 3` (`p = 2`). -/
def IsNonvanishingSquareCoord (q hq : ℕ) (r : ZMod (q ^ hq)) : Prop :=
  r.val ≠ 0 ∧ Even (padicValNat q r.val) ∧
    (if q = 2 then
      padicValNat 2 r.val + 3 ≤ hq ∧ r.val / 2 ^ padicValNat 2 r.val % 8 = 1
    else
      IsSquare ((r.val / q ^ padicValNat q r.val : ℕ) : ZMod q) ∧
        ((r.val / q ^ padicValNat q r.val : ℕ) : ZMod q) ≠ 0)

section Index

variable {P : Type} [Fintype P] [DecidableEq P] (pr h : P → ℕ) [∀ q, NeZero (pr q ^ h q)]

/-- `def:cp0`(d): the index law of `def:hyb:coupled` for the queries `E`: the fixed modulus
`M₀ = ∏_p p^{h_p}` (`modulus pr h`), a product convolution law on nonvanishing square
increments at these coordinates (`μ e q`), and independent conductor-depth envelopes
(the tails `t e q`) with moment `R_I`. Each exact-conductor space is preserved by the
coordinate transition (proved, `coordTransition_hypotheses`), and the norm of the
transition restricted to it is bounded by the corresponding decreasing depth tail
(`hnorm`). The interval transition is the cyclic shift (`coordTransition`). -/
structure IndexLaw (E : Type) where
  /-- The increment law of the query `e` at the prime `pr q`. -/
  μ : E → ∀ q, ZMod (pr q ^ h q) → ℝ
  hμ : ∀ e q r, 0 ≤ μ e q r
  hμ1 : ∀ e q, ∑ r, μ e q r = 1
  /-- The increments are nonvanishing square classes. -/
  hsq : ∀ e q r, μ e q r ≠ 0 → IsNonvanishingSquareCoord (pr q) (h q) r
  /-- The conductor-depth tails. -/
  t : E → ∀ q, Tails (Chain.residues (pr q) (h q)).depth
  /-- The transition norm on each exact-conductor space is at most the tail. -/
  hnorm : ∀ e q (l : Fin ((Chain.residues (pr q) (h q)).depth + 1)) f,
    (Chain.residues (pr q) (h q)).diff l *ᵥ f = f →
    (convMatrix (μ e q) *ᵥ f) ⬝ᵥ (convMatrix (μ e q) *ᵥ f) ≤ (t e q).tail l ^ 2 * (f ⬝ᵥ f)
  /-- The conductor moment `R_I = E_J (K sq(D_J))^{2a/d}` of one index
  (`def:hyb:coupled`(g); `Sarkozy.Functional.oneQueryMoment`). It enters Theorem C only
  through `lem:envelope-energy` and the wrapping terms, which are hypotheses here. -/
  R_I : ℝ
  hR_I : 0 ≤ R_I

end Index

section Standing

variable {J₀ : Type} [Fintype J₀] [DecidableEq J₀] (m₀ : J₀ → ℕ) [∀ i, NeZero (m₀ i)]
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] (p : ∀ L, J L → ℕ)
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] (pr h : P → ℕ) [∀ q, NeZero (pr q ^ h q)]

/-- **(CP0) Standing data** (`def:cp0`), over the objects of `Sarkozy.PaperFrame`.
(a) The slots `V = Slot` (`d = 72`) and the cut family `IsFamilyCut`, which contains the
sorting sequence (`isFamilyCut_of_sorting`), are fixed. (b) `K = blockScale`; at every
scale `L ≥ 1`, `N = KL`, the group `G_N = ResidueSpace (joinModuli m₀ (p L))`, its atoms
`PaperAtom J L` (the prefix and the tail primes `p L j`), the lift `F_A = atomLift` and the
inputs `g^{I,D_0,s}` (`atomInput`) are those of `def:record:functional`; the prefix
coordinates are `ℤ/p^{e_p}ℤ` with the fixed prefix exponents `e_p` (`pp`, `ep`); the
density exponent is `θ = densityExponent` and the price exponent `a = decay`. (c) The
queries. (d) The index law. -/
structure StandingData (E : Type) [Fintype E] [DecidableEq E] where
  /-- The prefix primes and exponents: `m₀ i = pp i ^ ep i`. -/
  pp : J₀ → ℕ
  ep : J₀ → ℕ
  pp_prime : ∀ i, (pp i).Prime
  ep_pos : ∀ i, 1 ≤ ep i
  m₀_eq : ∀ i, m₀ i = pp i ^ ep i
  /-- The tail coordinates are distinct primes. -/
  p_prime : ∀ L j, (p L j).Prime
  p_inj : ∀ L, Function.Injective (p L)
  /-- The selection factor of the (merged) prefix atom. -/
  selPre : ℝ
  one_le_selPre : 1 ≤ selPre
  /-- (c) The queries. -/
  Q : Queries E
  /-- (d) The index law; `M₀ = ∏_p p^{h_p}` with `h_2 ≥ 3`, coprime to every prime of
  `G_N`. -/
  index : IndexLaw pr h E
  pr_prime : ∀ q, (pr q).Prime
  pr_inj : Function.Injective pr
  h_two : ∃ q, pr q = 2 ∧ 3 ≤ h q
  modulus_coprime : ∀ L k, Nat.Coprime (modulus pr h) (joinModuli m₀ (p L) k)

/-- The selection factor `q_𝔟^{2a}` of an atom (`def:price`): `p^{2a}` at a tail prime
`p`, the given factor `selPre` at the prefix atom. -/
noncomputable def selectionFactor (selPre : ℝ) (L : ℕ) : PaperAtom J L → ℝ
  | none => selPre
  | some j => ((p L j : ℕ) : ℝ) ^ (2 * decay)

/-- The product of the primes of an atom with `e_p = 1` (the weight `q_𝔟` of (CP8)(c)). -/
noncomputable def oneWeight (pp ep : J₀ → ℕ) (L : ℕ) : PaperAtom J L → ℝ
  | none => ∏ i ∈ univ.filter (fun i => ep i = 1), (pp i : ℝ)
  | some j => (p L j : ℝ)

/-- The law of an atom at the scale `L`. -/
abbrev AtomMeasure (L : ℕ) (b : PaperAtom J L) : Type := SlotMeasure (AtomLabel m₀ p L b)

/-- Acceptance of a query pair at an atom (`(CP4)(a)`, `(R5)`): the difference
`y - x = z_{v_e} - z_{u_e}` is a nonzero square at a tail prime (`e_p = 1`), and at every
prefix prime it is nonzero, of even valuation `2j < e_p`, with a square unit part (for
`e_p = 1` this is a nonzero square). -/
def AcceptedPair (pp ep : J₀ → ℕ) (L : ℕ) : ∀ b : PaperAtom J L,
    AtomLabel m₀ p L b → AtomLabel m₀ p L b → Prop
  | none => fun x y => ∀ i, y i - x i ≠ 0 ∧ ∃ jj : ℕ, 2 * jj < ep i ∧
      ∃ r : ZMod (m₀ i), IsUnit r ∧ IsSquare r ∧ y i - x i = ((pp i : ℕ) : ZMod (m₀ i)) ^ (2 * jj) * r
  | some _ => fun x y => y - x ≠ 0 ∧ IsSquare (y - x)

end Standing

/-! ## Robust bounds (`def:robust`) -/

/-- A robust upper bound `Ξ ≤ (c + o(1)) Y` (`def:robust`), in the form of
`Sarkozy.Comparison.Criterion`: at every least normalized counterexample of every large
scale, uniformly in `C ≥ 1`, with a relative error `ε(L) → 0` and a density-linear
remainder `c' L^{-σ} α`. -/
def RobustUpper (Y Ξ : ℕ → Finset ℤ → ℝ) (c : ℝ) : Prop :=
  ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∃ c' : ℝ, 0 ≤ c' ∧
    AtCounterexamples Y fun L A => Ξ L A ≤ (c + ε L) * Y L A + remainder c' L A

/-- A robust lower bound `Ξ ≥ (c - o(1)) Y` (`def:robust`). -/
def RobustLower (Y Ξ : ℕ → Finset ℤ → ℝ) (c : ℝ) : Prop :=
  ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∃ c' : ℝ, 0 ≤ c' ∧
    AtCounterexamples Y fun L A => (c - ε L) * Y L A - remainder c' L A ≤ Ξ L A

end Sarkozy.TheoremC
