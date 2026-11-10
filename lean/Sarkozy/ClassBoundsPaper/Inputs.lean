module

public import Sarkozy.ClassBoundsPaper.Algebra
public import Sarkozy.ClassBoundsPaper.Coeff
public import Sarkozy.TheoremCBlock.Classes

@[expose] public section

/-!
# The class bounds of the construction (`CB`, `hCB`) and the class polynomial (`hΨ`)

`paper/sections/09_comparison_theorem.tex`, `def:cp5`, `def:robust`;
`paper/sections/23_envelopes.tex`, `cor:envelope-costs`, `thm:envelopes`(i), `lem:class-credit`;
`paper/sections/22_variance.tex`, `cor:var-classes`, `cor:variance:final`;
`paper/sections/28_closing.tex`, `prop:closing-data`(d).

For any comparison law `CL` (B2's construction or another), `ClassInputs CL` names the data of the
paper's classes and their robust class bounds:

* the replaced **degree classes** `𝒞_n`, `n ∈ N` (`lem:record:record-expansion`(v); in Part V the
  sixteen envelope classes of `cor:envelope-costs`, in the kinds of skew records `kind`), with the
  class costs `C_n ≥ 0` and the auxiliary raw-arm, leading and remainder prices `y^arm`, `y^lead`,
  `y^rem ≥ 0` (`lem:middle-comparison-prices`);
* the **variance classes** (`cor:variance:final`(i), (iii)): a class map `vcls` with costs `vcost ≥
  0` (in Part V `B − g`, `g` the variance gain);
* the robust class bounds of these classes with nonnegative remainders (`robust`), uniformly in the
  class (`def:cp5`, `def:robust`): `∑_{ω ∈ 𝒞} |I_ω| ≤ ∑_{ω ∈ 𝒞} ((φ_ω + ε π_ω) Y + r_ω)` with the
  class bound `φ_ω = C_n π^arm_ω + B'(∏(π^lead + π^rem) − ∏ π^lead)` on `𝒞_n` (`thm:envelopes`(i))
  and `φ_ω = vcost(ω) π_ω` on a variance class (`cor:var-classes`, `lem:var-gain`). **This is a
  hypothesis**: the analytic content of `cor:envelope-costs` and `cor:var-classes` for `CL`.

From it:

* `ClassInputs.toClassBounds`: **`CB`**, a `TheoremCBlock.ClassBounds` for `CL`. The classes are the
  degree classes (a selection of a degree class is in that class) and, outside them, the variance
  classes; the auxiliary prices are `Jaux 𝔟 = T_𝔟 × {s, a} × Fin 4` (price, arm, lead, remainder);
  the coefficients are those of `Sarkozy.ClassBoundsPaper.Coeff`. `phi_eq`: its class bound is
  WP-R's `replacedBound`.
* `ClassInputs.robustNonneg`: **`hCB`**.
* `ClassInputs.UpperData`, **`ClassInputs.sum_le_upper`**: `hΨ` at one scale, against `B'(e^Ŝ cosh Â
  − 1) − 𝒟(π̂) − ∑_n saving_n(π̂, ŷ)`, from upper prices and the completion polynomial `𝒟_sym` of
  the variance classes (`lem:record:record-expansion`(iii)–(v)).
-/

open Finset Filter
open scoped Topology BigOperators

namespace Sarkozy.ClassBoundsPaper

open Sarkozy.RecordExpansion Sarkozy.RecordExpansion.Choice Sarkozy.TheoremCBlock
open Sarkozy.TheoremC Sarkozy.BlockFrame
open Sarkozy.Param (Params)

attribute [local instance] TheoremCBlock.ClassBounds.ιFintype TheoremCBlock.ClassBounds.ιDecEq
  TheoremCBlock.ClassBounds.JauxFintype TheoremCBlock.ClassBounds.JauxDecEq
open Sarkozy.FourierArithmetic Sarkozy.Functional Sarkozy.IndexSupport Sarkozy.Comparison
  Sarkozy.PaperFrame

section Generic

variable {J : Type*} [Fintype J] [DecidableEq J] {T : J → Type*} [∀ b, Fintype (T b)]
  [∀ b, DecidableEq (T b)] {V : Type*}

open Classical in
/-- **The classes of the construction** (`prop:closing-data`(d)): a selection of a replaced degree
class `𝒞_n` (`n ∈ N`) is in the class `n`; a selection outside them is in the variance class `vcls
ω` (if any); a choice that is not a selection is in no class. -/
noncomputable def paperCls (N : Finset (Fin 3 → ℕ)) (kind : PriceVar T → Option (Fin 3))
    (vcls : Choice T → Option V) (ω : Choice T) : Option ({n // n ∈ N} ⊕ V) :=
  if IsSelection ω then
    if h : selMono ω ∈ N.biUnion (kindMonos kind) then
      some (Sum.inl ⟨degreeOf kind (selMono ω), by
        obtain ⟨n, hn, hm⟩ := mem_biUnion.mp h
        rw [degreeOf_of_mem hm]
        exact hn⟩)
    else (vcls ω).map Sum.inr
  else none

theorem paperCls_of_mem {N : Finset (Fin 3 → ℕ)} {kind : PriceVar T → Option (Fin 3)}
    {vcls : Choice T → Option V} {ω : Choice T} (hω : IsSelection ω)
    (h : selMono ω ∈ N.biUnion (kindMonos kind)) : paperCls N kind vcls ω ≠ none := by
  classical
  unfold paperCls
  simp [hω, h]

theorem paperCls_of_not_mem {N : Finset (Fin 3 → ℕ)} {kind : PriceVar T → Option (Fin 3)}
    {vcls : Choice T → Option V} {ω : Choice T} (hω : IsSelection ω)
    (h : selMono ω ∉ N.biUnion (kindMonos kind)) :
    paperCls N kind vcls ω = (vcls ω).map Sum.inr := by
  classical
  unfold paperCls
  simp [hω, h]

theorem paperCls_ne_none {N : Finset (Fin 3 → ℕ)} {kind : PriceVar T → Option (Fin 3)}
    {vcls : Choice T → Option V} {ω : Choice T} (h : paperCls N kind vcls ω ≠ none) :
    IsSelection ω ∧ (selMono ω ∈ N.biUnion (kindMonos kind) ∨ vcls ω ≠ none) := by
  classical
  by_cases hω : IsSelection ω
  · refine ⟨hω, ?_⟩
    by_cases hm : selMono ω ∈ N.biUnion (kindMonos kind)
    · exact Or.inl hm
    · right
      rw [paperCls_of_not_mem hω hm] at h
      intro hv
      rw [hv] at h
      exact h rfl
  · exfalso
    unfold paperCls at h
    simp [hω] at h

omit [DecidableEq J] in
/-- The number of atoms of a choice is the degree of its monomial. -/
theorem card_support_eq_sum_selMono (ω : Choice T) :
    (Choice.support ω).card = ∑ v, selMono ω v := by
  unfold Choice.support selMono
  rw [card_eq_sum_ones, sum_filter, Fintype.sum_sigma]
  apply sum_congr rfl
  intro b _
  change (if (ω b).isSome = true then 1 else 0) =
    ∑ q : T b × ChangeType, (if ω b = some q then 1 else 0)
  rcases ω b with _ | q
  · simp
  · simp

/-- **A selection of the degree class `𝒞_n` has `|n|` atoms** (`def:cp5`, `n_max`: at most six in
Part V). -/
theorem card_support_of_mem_kindMonos {L : Type*} [Fintype L] [DecidableEq L]
    {kind : PriceVar T → Option L} {n : L → ℕ} {ω : Choice T}
    (h : selMono ω ∈ kindMonos kind n) : (Choice.support ω).card = ∑ l, n l := by
  classical
  obtain ⟨h0, h1⟩ := mem_kindMonos.mp h
  rw [card_support_eq_sum_selMono, ← Finset.sum_fiberwise univ kind (selMono ω),
    Fintype.sum_option]
  have hnone : ∑ v ∈ univ with kind v = none, selMono ω v = 0 :=
    sum_eq_zero fun v hv => h0 v (mem_filter.mp hv).2
  rw [hnone, zero_add]
  apply sum_congr rfl
  intro l _
  exact h1 l

open Classical in
/-- The coefficients of the class bound: those of `C_n π^arm + B'(∏(π^lead + π^rem) − ∏ π^lead)` on
a degree class (`replCoeff`), those of `vcost(ω) π_ω` elsewhere (`costCoeff`). -/
noncomputable def paperCoeff (N : Finset (Fin 3 → ℕ)) (kind : PriceVar T → Option (Fin 3))
    (C : (Fin 3 → ℕ) → ℝ) (B' : ℝ) (vcost : Choice T → ℝ) (ω : Choice T)
    (m : ∀ b, Option (T b × ChangeType × Fin 4)) : ℝ :=
  if selMono ω ∈ N.biUnion (kindMonos kind) then
    replCoeff (C (degreeOf kind (selMono ω))) B' ω m
  else costCoeff (vcost ω) ω m

/-- **The class bound of the construction** is WP-R's `replacedBound`. -/
theorem sum_paperCoeff (N : Finset (Fin 3 → ℕ)) (kind : PriceVar T → Option (Fin 3))
    (C : (Fin 3 → ℕ) → ℝ) (B' : ℝ) (vcost : Choice T → ℝ) (π : ∀ b, T b → ChangeType → ℝ)
    (yarm ylead yrem : PriceVar T → ℝ) (ω : Choice T) :
    ∑ m : (∀ b, Option (T b × ChangeType × Fin 4)),
        paperCoeff N kind C B' vcost ω m *
          ∏ b, (m b).elim 1 (auxY (auxPrices π yarm ylead yrem) b) =
      replacedBound kind N C B' yarm ylead yrem vcost π ω := by
  classical
  unfold paperCoeff replacedBound
  by_cases h : selMono ω ∈ N.biUnion (kindMonos kind)
  · simp only [h, ↓reduceIte]
    exact sum_replCoeff _ _ π yarm ylead yrem ω
  · simp only [h, ↓reduceIte]
    exact sum_costCoeff _ π yarm ylead yrem ω

end Generic

variable {a : ℝ} {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {S₀ : Bk → ℝ} {pp ep : J₀ → ℕ} {E : Type} {Q : Queries E} {R : Reference m₀ blk}
  {FS : FirstStage a m₀ blk p S₀ R}

variable (CL : ComparisonLaw a m₀ blk p S₀ pp ep Q FS)

/-- **The inputs of the class bounds** (`def:cp5` for the construction; `cor:envelope-costs`,
`cor:var-classes`). See the module docstring. The fields `N`, `C`, `kind` and the auxiliary prices
are the data of `prop:closing-data`(d) and `lem:middle-comparison-prices`; `robust` is the robust
class bound (a hypothesis); `nmax_bound` is `n_max` of `def:cp5` (at most six atoms in Part V). -/
structure ClassInputs where
  /-- The replaced degree vectors (kinds `Fin 3`: fold, matching `E₀`, matching `E₁`). -/
  N : Finset (Fin 3 → ℕ)
  hN : ∀ n ∈ N, n ≠ 0 ∧ Even (∑ l, n l)
  /-- The class costs `C_n` of `def:closing-quantities`(7). -/
  C : (Fin 3 → ℕ) → ℝ
  C_nonneg : ∀ n ∈ N, 0 ≤ C n
  /-- The upper bound `B'` of the energy factor used in the class bounds. -/
  Bp : ℝ
  Bp_nonneg : 0 ≤ Bp
  /-- The prices of (CP4)(b) are nonnegative (`def:price`). -/
  π_nonneg : ∀ L b t e, 0 ≤ CL.π L b t e
  /-- The kinds of the skew records. -/
  kind : ∀ L, PriceVar (CL.T L) → Option (Fin 3)
  kind_skew : ∀ L v l, kind L v = some l → v.2.2 = .skew
  /-- The raw-arm, leading and remainder prices (`lem:middle-comparison-prices`). -/
  yarm : ∀ L, PriceVar (CL.T L) → ℝ
  ylead : ∀ L, PriceVar (CL.T L) → ℝ
  yrem : ∀ L, PriceVar (CL.T L) → ℝ
  yarm_nonneg : ∀ L v, 0 ≤ yarm L v
  ylead_nonneg : ∀ L v, 0 ≤ ylead L v
  yrem_nonneg : ∀ L v, 0 ≤ yrem L v
  /-- The variance classes (`cor:variance:final`(i), (iii)) and their costs. -/
  V : ℕ → Type
  [VFintype : ∀ L, Fintype (V L)]
  [VDecEq : ∀ L, DecidableEq (V L)]
  vcls : ∀ L, Choice (CL.T L) → Option (V L)
  vcost : ∀ L, Choice (CL.T L) → ℝ
  vcost_nonneg : ∀ L ω, 0 ≤ vcost L ω
  /-- `n_max` of `def:cp5`. -/
  nmax : ℕ
  nmax_bound : ∀ L (ω : Choice (CL.T L)), IsSelection ω →
    (selMono ω ∈ N.biUnion (kindMonos (kind L)) ∨ vcls L ω ≠ none) →
      (Choice.support ω).card ≤ nmax
  /-- **The robust class bounds with nonnegative remainders** (`def:cp5`, `def:robust`;
  `thm:envelopes`(i) and `cor:envelope-costs` on the degree classes, `cor:var-classes` on the
  variance classes), uniformly in the classes. *Hypothesis.* -/
  robust : ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∃ c : ℝ, 0 ≤ c ∧
    ∃ r : ∀ L, Finset ℤ → Choice (CL.T L) → ℝ, (∀ L A ω, 0 ≤ r L A ω) ∧
    Param.AtCounterexamples (Params.ofDecay a) (energyFirst (R.law p) (blockLift m₀ blk p))
        fun L A =>
      (∀ i, ∑ ω ∈ (univ.filter fun ω : Choice (CL.T L) => IsSelection ω).filter
          (fun ω => paperCls N (kind L) (vcls L) ω = some i),
            |term (FS.lam L) (CL.ζ L) (blockLift m₀ blk p L A) ω| ≤
        ∑ ω ∈ (univ.filter fun ω : Choice (CL.T L) => IsSelection ω).filter
            (fun ω => paperCls N (kind L) (vcls L) ω = some i),
          ((replacedBound (kind L) N C Bp (yarm L) (ylead L) (yrem L) (vcost L) (CL.π L) ω +
              ε L * monomial (CL.π L) ω) *
              energyFirst (R.law p) (blockLift m₀ blk p) L A + r L A ω)) ∧
      ∑ ω ∈ univ.filter (fun ω : Choice (CL.T L) => IsSelection ω), r L A ω ≤ remainder c L A

attribute [instance] ClassInputs.VFintype ClassInputs.VDecEq

namespace ClassInputs

variable {CL} (CI : ClassInputs CL)

/-- The auxiliary prices `y_{𝔟,(t,ε,k)}`. -/
noncomputable def auxAt (L : ℕ) (b : BlockAtom Bk J L) (x : CL.T L b × ChangeType × Fin 4) : ℝ :=
  auxY (auxPrices (CL.π L) (CI.yarm L) (CI.ylead L) (CI.yrem L)) b x

theorem auxAt_nonneg (L : ℕ) (b : BlockAtom Bk J L) (x : CL.T L b × ChangeType × Fin 4) :
    0 ≤ CI.auxAt L b x := by
  obtain ⟨t, e, k⟩ := x
  unfold auxAt auxY auxPrices
  fin_cases k
  · exact CI.π_nonneg L b t e
  · exact CI.yarm_nonneg L _
  · exact CI.ylead_nonneg L _
  · exact CI.yrem_nonneg L _

/-- The class bound of the construction, as the polynomial of `ClassBounds`. -/
theorem sum_coeff_eq (L : ℕ) (ω : Choice (CL.T L)) :
    ∑ m : (∀ b, Option (CL.T L b × ChangeType × Fin 4)),
        paperCoeff CI.N (CI.kind L) CI.C CI.Bp (CI.vcost L) ω m * ∏ b, (m b).elim 1 (CI.auxAt L b) =
      replacedBound (CI.kind L) CI.N CI.C CI.Bp (CI.yarm L) (CI.ylead L) (CI.yrem L) (CI.vcost L)
        (CL.π L) ω :=
  sum_paperCoeff CI.N (CI.kind L) CI.C CI.Bp (CI.vcost L) (CL.π L) (CI.yarm L) (CI.ylead L)
    (CI.yrem L) ω

theorem paperCoeff_nonneg (L : ℕ) (ω : Choice (CL.T L))
    (m : ∀ b, Option (CL.T L b × ChangeType × Fin 4)) :
    0 ≤ paperCoeff CI.N (CI.kind L) CI.C CI.Bp (CI.vcost L) ω m := by
  classical
  unfold paperCoeff
  split_ifs with h
  · obtain ⟨n, hn, hm⟩ := mem_biUnion.mp h
    rw [degreeOf_of_mem hm]
    exact replCoeff_nonneg (CI.C_nonneg n hn) CI.Bp_nonneg ω m
  · exact costCoeff_nonneg (CI.vcost_nonneg L ω) ω m

theorem paperCoeff_support (L : ℕ) (ω : Choice (CL.T L))
    (m : ∀ b, Option (CL.T L b × ChangeType × Fin 4))
    (h : paperCoeff CI.N (CI.kind L) CI.C CI.Bp (CI.vcost L) ω m ≠ 0) (b : BlockAtom Bk J L) :
    (m b).map auxAttach = ω b := by
  classical
  unfold paperCoeff at h
  split_ifs at h
  · exact replCoeff_support ω m h b
  · exact costCoeff_support ω m h b

/-- **`CB`: the class bounds of the construction** (`def:cp5`; `cor:envelope-costs`,
`cor:var-classes`), from `ClassInputs`. -/
noncomputable def toClassBounds : TheoremCBlock.ClassBounds a m₀ blk p CL where
  ι L := {n // n ∈ CI.N} ⊕ CI.V L
  cls L := paperCls CI.N (CI.kind L) (CI.vcls L)
  nmax := CI.nmax
  nmax_bound L ω i h := by
    have h' : paperCls CI.N (CI.kind L) (CI.vcls L) ω ≠ none := by
      rw [h]
      exact Option.some_ne_none i
    obtain ⟨hω, hc⟩ := paperCls_ne_none h'
    exact CI.nmax_bound L ω hω hc
  Jaux L b := CL.T L b × ChangeType × Fin 4
  y L b := CI.auxAt L b
  y_nonneg L b := CI.auxAt_nonneg L b
  attach L b := auxAttach
  coeff L := paperCoeff CI.N (CI.kind L) CI.C CI.Bp (CI.vcost L)
  coeff_nonneg L := CI.paperCoeff_nonneg L
  coeff_support L := CI.paperCoeff_support L
  robust := by
    obtain ⟨ε, hε, c, hc, r, -, h⟩ := CI.robust
    refine ⟨ε, hε, c, hc, r, ?_⟩
    simpa only [CI.sum_coeff_eq] using h

/-- The class bound `φ_ω` of `CB` is WP-R's `replacedBound`: `C_n π^arm_ω + B'(∏(π^lead + π^rem) − ∏
π^lead)` on a degree class `𝒞_n`, `vcost(ω) π_ω` elsewhere. -/
theorem phi_eq (L : ℕ) (ω : Choice (CL.T L)) :
    CI.toClassBounds.phi L ω =
      replacedBound (CI.kind L) CI.N CI.C CI.Bp (CI.yarm L) (CI.ylead L) (CI.yrem L) (CI.vcost L)
        (CL.π L) ω :=
  CI.sum_coeff_eq L ω

theorem phi_eq' (L : ℕ) (ω : Choice (CL.T L)) :
    ∑ m, CI.toClassBounds.coeff L ω m * ∏ b, (m b).elim 1 (CI.toClassBounds.y L b) =
      replacedBound (CI.kind L) CI.N CI.C CI.Bp (CI.yarm L) (CI.ylead L) (CI.yrem L) (CI.vcost L)
        (CL.π L) ω :=
  CI.sum_coeff_eq L ω

theorem cls_eq (L : ℕ) : CI.toClassBounds.cls L = paperCls CI.N (CI.kind L) (CI.vcls L) := rfl

/-- **`hCB`: the class bounds of the construction are robust with nonnegative remainders**
(`def:robust`), from `ClassInputs.robust`. -/
theorem robustNonneg : CI.toClassBounds.RobustNonneg := by
  obtain ⟨ε, hε, c, hc, r, hr, h⟩ := CI.robust
  refine ⟨ε, hε, c, hc, r, hr, ?_⟩
  simp only [TheoremCBlock.ClassBounds.phi, CI.phi_eq', CI.cls_eq]
  exact h

/-- The cost of a selection outside the degree classes, for the completion: `B'` in no class, the
variance cost in a variance class. -/
noncomputable def cost (L : ℕ) (ω : Choice (CL.T L)) : ℝ :=
  if CI.vcls L ω = none then CI.Bp else CI.vcost L ω

theorem cost_nonneg (L : ℕ) (ω : Choice (CL.T L)) : 0 ≤ CI.cost L ω := by
  unfold cost
  split_ifs
  · exact CI.Bp_nonneg
  · exact CI.vcost_nonneg L ω

/-- **The upper prices and the completion polynomial at one scale** (`prop:closing-data`(d);
`lem:record:record-expansion`(iii), (iv)): upper prices `π̂ ≥ π`, upper auxiliary prices `ŷ ≥ y`,
and the polynomial `𝒟_sym(x) = ∑_{m ∈ supp} d_m x^m` of the variance classes with `0 ≤ d_m`, `d_m =
0` on the degree classes, `d_m ≤ B' − c_ω` on the monomial of every selection outside the degree
classes (`cost`) and `d_m ≤ B' c_m` on every other monomial. *Hypotheses* (`cor:variance:final`(iv)
for `𝒟_sym`). -/
structure UpperData (L : ℕ) where
  πu : ∀ b, CL.T L b → ChangeType → ℝ
  le : ∀ b t e, CL.π L b t e ≤ πu b t e
  yarmu : PriceVar (CL.T L) → ℝ
  yleadu : PriceVar (CL.T L) → ℝ
  yremu : PriceVar (CL.T L) → ℝ
  arm_le : ∀ v, CI.yarm L v ≤ yarmu v
  lead_le : ∀ v, CI.ylead L v ≤ yleadu v
  rem_le : ∀ v, CI.yrem L v ≤ yremu v
  supp : Finset (PriceVar (CL.T L) → ℕ)
  d : (PriceVar (CL.T L) → ℕ) → ℝ
  d_nonneg : ∀ m, 0 ≤ d m
  d_zero : ∀ n ∈ CI.N, ∀ m ∈ kindMonos (CI.kind L) n, d m = 0
  d_sel : ∀ ω : Choice (CL.T L), IsSelection ω →
    (∀ n ∈ CI.N, selMono ω ∉ kindMonos (CI.kind L) n) → d (selMono ω) ≤ CI.Bp - CI.cost L ω
  d_oth : ∀ m, (∀ ω : Choice (CL.T L), IsSelection ω → selMono ω ≠ m) →
    d m ≤ CI.Bp * expCoeff m

namespace UpperData

variable {CI} {L : ℕ} (U : CI.UpperData L)

/-- The complete polynomial `Ψ(π̂, ŷ) = B'(e^Ŝ cosh Â − 1) − 𝒟_sym(π̂) − ∑_n saving_n(π̂, ŷ)` at the
upper prices. -/
noncomputable def Psi : ℝ :=
  CI.Bp * (Real.exp (∑ b, symTotal U.πu b) * Real.cosh (∑ b, skewTotal U.πu b) - 1) -
    ∑ m ∈ U.supp, U.d m * mono (priceVec U.πu) m -
    ∑ n ∈ CI.N, replacementSaving (CI.kind L) n (CI.C n) CI.Bp (priceVec U.πu) U.yarmu U.yleadu
      U.yremu

end UpperData

/-- **`hΨ` at one scale against the complete polynomial at upper prices** (`prop:closing-data`(d);
`lem:record:record-expansion`(ii)–(v)): for the class bounds of the construction and any energy
factor `B ≤ B'`, the sum of `hΨ` is at most `Ψ(π̂, ŷ)`. -/
theorem sum_le_upper {B : ℝ} (hB : B ≤ CI.Bp) {L : ℕ} (U : CI.UpperData L) :
    ∑ ω ∈ univ.filter (fun ω : Choice (CL.T L) => IsSelection ω),
      (if CI.toClassBounds.cls L ω = none then B * monomial (CL.π L) ω
        else CI.toClassBounds.phi L ω) ≤ U.Psi := by
  classical
  have h := sum_classTerm_le_upper (CI.π_nonneg L) U.le (CI.toClassBounds.cls L)
    (CI.toClassBounds.phi L) B (CI.kind L) (CI.kind_skew L) CI.N CI.hN CI.C CI.C_nonneg
    (CI.yarm_nonneg L) (CI.ylead_nonneg L) (CI.yrem_nonneg L) U.arm_le U.lead_le U.rem_le
    (CI.cost L) (fun ω _ _ => CI.cost_nonneg L ω) CI.Bp_nonneg U.supp U.d U.d_nonneg U.d_zero
    U.d_sel U.d_oth ?hnone ?hvar ?hrep
  · exact h
  case hnone =>
    intro ω hω hc
    rw [cls_eq] at hc
    have hm : selMono ω ∉ CI.N.biUnion (kindMonos (CI.kind L)) := fun hm =>
      paperCls_of_mem hω hm hc
    refine ⟨fun n hn hmn => hm (mem_biUnion.mpr ⟨n, hn, hmn⟩), ?_⟩
    rw [paperCls_of_not_mem hω hm] at hc
    have hc' : CI.vcls L ω = none := by
      rcases hv : CI.vcls L ω with _ | v
      · rfl
      · rw [hv] at hc
        exact absurd hc (by simp)
    unfold cost
    rw [ite_eq_left hc']
    exact hB
  case hvar =>
    intro ω hω hc hout
    rw [cls_eq] at hc
    have hm : selMono ω ∉ CI.N.biUnion (kindMonos (CI.kind L)) := fun hm => by
      obtain ⟨n, hn, hmn⟩ := mem_biUnion.mp hm
      exact hout n hn hmn
    rw [paperCls_of_not_mem hω hm] at hc
    have hv : CI.vcls L ω ≠ none := fun hv => hc (by rw [hv]; rfl)
    rw [phi_eq]
    unfold replacedBound cost
    rw [ite_eq_right hm, ite_eq_right hv]
  case hrep =>
    intro ω hω n hn hmn
    have hm : selMono ω ∈ CI.N.biUnion (kindMonos (CI.kind L)) := mem_biUnion.mpr ⟨n, hn, hmn⟩
    refine ⟨by rw [cls_eq]; exact paperCls_of_mem hω hm, ?_⟩
    rw [phi_eq]
    unfold replacedBound
    rw [ite_eq_left hm, degreeOf_of_mem hmn]

end ClassInputs

end Sarkozy.ClassBoundsPaper
