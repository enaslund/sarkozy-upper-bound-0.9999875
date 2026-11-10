module

public import Sarkozy.ClassBoundsPaper.Main

@[expose] public section

/-!
# The evaluated class bounds from the class bounds at energy level

`paper/sections/09_comparison_theorem.tex`, `def:cp5`, `def:robust`;
`paper/sections/23_envelopes.tex`, `thm:envelopes`(i), `cor:envelope-costs`;
`paper/sections/22_variance.tex`, `cor:var-classes`, `lem:var-gain`;
`paper/sections/10_comparison_lemmas.tex`, `lem:bracket-energy`;
`paper/sections/11_comparison_proof.tex`, `cor:joint-closing`.

B4's joint route has three class inputs: `CI : ClassInputs D.CL`, whose analytic content is the
robust **evaluated** class bound `robust`; `CE : ClassEnergyInputs D CI`, the class bounds **at
energy level** on labelled positive diagonals; and the upper prices (J3) of these diagonals in
`MeanAllocation.upper`. In the paper the evaluated form is not a separate statement: it is the
energy form with the energies of the diagonals evaluated at their upper prices
(`lem:bracket-energy`, (E1)). This file proves that.

* `ClassData CL`: the data fields of `ClassInputs CL` (the 49 degree vectors, the kinds, the
  class costs, the auxiliary prices, the variance classes, `n_max`), without `robust`.
  `ClassData.Robust` is the statement of `ClassInputs.robust`; `ClassData.toInputs`.
* `ClassEnergyData D cd`: the class bounds at energy level (`energy`, as `CE.energy`), their
  consistency with the class polynomial (`consistent`, as `CE.consistent`), nonnegative weights
  (`wc_nonneg`), and the upper prices of the diagonals (`upper`: `Z_j ≤ (u_j + ε₃ v_j) Y + r_j`
  with `∑_j w_j r_j ≤ c₃ L^{-σ} α`, `lem:bracket-energy`), with error weights dominated by the
  class prices (`errw`: `∑_j w_{ij} v_j ≤ K ∑_{ω ∈ 𝒞_i} π_ω`).
* **`ClassEnergyData.robust`**: `ClassData.Robust` (the robust evaluated class bounds, `def:cp5`,
  `def:robust`) is **proved** from these. The class remainders `∑_j w_{ij} r_j` are shared out
  equally among the selections of the class (`share`).
* `ClassEnergyData.toCI : ClassInputs D.CL` and `ClassEnergyData.toCE : ClassEnergyInputs D toCI`.
* `MeanData ED`: B4's `MeanAllocation` without `upper`; **`MeanData.toMA`** proves
  `MeanAllocation.upper` from the same `upper` (with `b ≥ 0`): one upper-price input serves both
  the class bounds and the mean allocation.
* **`MeanData.jointBound`**: `JB` from `ED`, `PD`, (E1), `hB` and `MD`.

So of B4's three analytic class inputs (`CI.robust`, `CE.energy`, `MA.upper`), `CI.robust` is no
longer an input, and `MA.upper` is replaced by `upper`, which carries remainders weighted by
`w_j` instead of `63 w_j − b_j`.
-/

open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.ClassInputsPaper

open Sarkozy.ClassBoundsPaper
open Sarkozy.TheoremC Sarkozy.TheoremCBlock Sarkozy.JointClosing
open Sarkozy.Param (Params)
open Sarkozy.BlockFrame
open Sarkozy.FourierArithmetic Sarkozy.Functional Sarkozy.IndexSupport Sarkozy.Comparison
  Sarkozy.PaperFrame Sarkozy.RecordExpansion Sarkozy.RecordExpansion.Choice
open Sarkozy.TargetLedger (targetLedger)

/-! ## Sharing a class remainder among the selections of the class -/

section Share

variable {X ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The share `R_i / |𝒞_i|` of the class remainder `R_i` carried by a selection of `𝒞_i`
(`0` off the classes). -/
noncomputable def share (sel : Finset X) (cls : X → Option ι) (R : ι → ℝ) (ω : X) : ℝ :=
  match cls ω with
  | some i => R i / ((sel.filter fun ω' => cls ω' = some i).card : ℝ)
  | none => 0

omit [Fintype ι] in
theorem share_nonneg (sel : Finset X) (cls : X → Option ι) {R : ι → ℝ} (hR : ∀ i, 0 ≤ R i)
    (ω : X) : 0 ≤ share sel cls R ω := by
  unfold share
  rcases cls ω with _ | i
  · exact le_rfl
  · exact div_nonneg (hR i) (Nat.cast_nonneg _)

omit [Fintype ι] in
theorem share_of_some (sel : Finset X) (cls : X → Option ι) (R : ι → ℝ) {ω : X} {i : ι}
    (h : cls ω = some i) :
    share sel cls R ω = R i / ((sel.filter fun ω' => cls ω' = some i).card : ℝ) := by
  unfold share
  rw [h]

omit [Fintype ι] in
/-- On a nonempty class the shares add up to the class remainder. -/
theorem sum_share_class (sel : Finset X) (cls : X → Option ι) (R : ι → ℝ) (i : ι)
    (hne : (sel.filter fun ω => cls ω = some i).Nonempty) :
    ∑ ω ∈ sel.filter (fun ω => cls ω = some i), share sel cls R ω = R i := by
  rw [sum_congr rfl fun ω hω => share_of_some sel cls R (mem_filter.mp hω).2, sum_const,
    nsmul_eq_mul]
  have hc : ((sel.filter fun ω => cls ω = some i).card : ℝ) ≠ 0 := by
    exact_mod_cast hne.card_pos.ne'
  field_simp

/-- The shares add up to at most the sum of the class remainders. -/
theorem sum_share_le (sel : Finset X) (cls : X → Option ι) {R : ι → ℝ} (hR : ∀ i, 0 ≤ R i) :
    ∑ ω ∈ sel, share sel cls R ω ≤ ∑ i, R i := by
  classical
  rw [sum_split_classes sel cls]
  have h0 : ∑ ω ∈ sel.filter (fun ω => cls ω = none), share sel cls R ω = 0 :=
    sum_eq_zero fun ω hω => by
      unfold share
      rw [(mem_filter.mp hω).2]
  rw [h0, zero_add]
  refine sum_le_sum fun i _ => ?_
  by_cases hne : (sel.filter fun ω => cls ω = some i).Nonempty
  · exact (sum_share_class sel cls R i hne).le
  · rw [not_nonempty_iff_eq_empty.mp hne, sum_empty]
    exact hR i

end Share

/-- `∑_S ((f + a g) Y + h) = (∑_S f) Y + a (∑_S g) Y + ∑_S h`. -/
theorem sum_affine {X : Type*} (S : Finset X) (f g k : X → ℝ) (a Y : ℝ) :
    ∑ ω ∈ S, ((f ω + a * g ω) * Y + k ω) =
      (∑ ω ∈ S, f ω) * Y + a * (∑ ω ∈ S, g ω) * Y + ∑ ω ∈ S, k ω := by
  have e : ∀ ω, (f ω + a * g ω) * Y + k ω = f ω * Y + (a * Y) * g ω + k ω := fun ω => by ring
  rw [sum_congr rfl fun ω _ => e ω, sum_add_distrib, sum_add_distrib, ← sum_mul, ← mul_sum]
  ring

/-! ## The data of the classes -/

section Data

variable {a : ℝ} {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {S₀ : Bk → ℝ} {pp ep : J₀ → ℕ} {E : Type} {Q : Queries E} {R : Reference m₀ blk}
  {FS : FirstStage a m₀ blk p S₀ R}

variable (CL : ComparisonLaw a m₀ blk p S₀ pp ep Q FS)

/-- **The data of the classes of (CP5)** (`def:cp5`, `prop:closing-data`(d),
`lem:middle-comparison-prices`, `cor:variance:final`(i), (iii)): the fields of B4's `ClassInputs CL`
other than the analytic `robust`. -/
structure ClassData where
  /-- The replaced degree vectors (kinds `Fin 3`: fold, matching `E₀`, matching `E₁`). -/
  N : Finset (Fin 3 → ℕ)
  hN : ∀ n ∈ N, n ≠ 0 ∧ Even (∑ l, n l)
  /-- The class costs `C_n` of `def:closing-quantities`(7). -/
  C : (Fin 3 → ℕ) → ℝ
  C_nonneg : ∀ n ∈ N, 0 ≤ C n
  /-- The upper bound `B'` of the energy factor used in the class bounds. -/
  Bp : ℝ
  Bp_nonneg : 0 ≤ Bp
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

attribute [instance] ClassData.VFintype ClassData.VDecEq

namespace ClassData

variable {CL} (cd : ClassData CL)

/-- The classes at scale `L`: the degree classes and the variance classes. -/
abbrev ι (L : ℕ) : Type := {n // n ∈ cd.N} ⊕ cd.V L

/-- The selections at scale `L`. -/
noncomputable abbrev sel (_cd : ClassData CL) (L : ℕ) : Finset (Choice (CL.T L)) :=
  univ.filter fun ω : Choice (CL.T L) => IsSelection ω

/-- The class map of the construction (`paperCls`). -/
noncomputable abbrev cls (L : ℕ) : Choice (CL.T L) → Option (cd.ι L) :=
  paperCls cd.N (cd.kind L) (cd.vcls L)

/-- The selections of the class `i` at scale `L`. -/
noncomputable abbrev clsSel (L : ℕ) (i : cd.ι L) : Finset (Choice (CL.T L)) :=
  (cd.sel L).filter fun ω => cd.cls L ω = some i

/-- The class bound `φ_ω` of the construction (WP-R's `replacedBound`). -/
noncomputable abbrev φ (L : ℕ) (ω : Choice (CL.T L)) : ℝ :=
  replacedBound (cd.kind L) cd.N cd.C cd.Bp (cd.yarm L) (cd.ylead L) (cd.yrem L) (cd.vcost L)
    (CL.π L) ω

/-- **The robust evaluated class bounds** (`def:cp5`, `def:robust`): the statement of
`ClassInputs.robust` for the data `cd`. -/
def Robust : Prop :=
  ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∃ c : ℝ, 0 ≤ c ∧
    ∃ r : ∀ L, Finset ℤ → Choice (CL.T L) → ℝ, (∀ L A ω, 0 ≤ r L A ω) ∧
    Param.AtCounterexamples (Params.ofDecay a) (energyFirst (R.law p) (blockLift m₀ blk p))
        fun L A =>
      (∀ i, ∑ ω ∈ cd.clsSel L i, |term (FS.lam L) (CL.ζ L) (blockLift m₀ blk p L A) ω| ≤
        ∑ ω ∈ cd.clsSel L i,
          ((cd.φ L ω + ε L * monomial (CL.π L) ω) *
              energyFirst (R.law p) (blockLift m₀ blk p) L A + r L A ω)) ∧
      ∑ ω ∈ cd.sel L, r L A ω ≤ remainder c L A

/-- B4's `ClassInputs` from the data and the robust evaluated class bounds. -/
noncomputable def toInputs (h : cd.Robust) : ClassInputs CL where
  N := cd.N
  hN := cd.hN
  C := cd.C
  C_nonneg := cd.C_nonneg
  Bp := cd.Bp
  Bp_nonneg := cd.Bp_nonneg
  π_nonneg := cd.π_nonneg
  kind := cd.kind
  kind_skew := cd.kind_skew
  yarm := cd.yarm
  ylead := cd.ylead
  yrem := cd.yrem
  yarm_nonneg := cd.yarm_nonneg
  ylead_nonneg := cd.ylead_nonneg
  yrem_nonneg := cd.yrem_nonneg
  V := cd.V
  vcls := cd.vcls
  vcost := cd.vcost
  vcost_nonneg := cd.vcost_nonneg
  nmax := cd.nmax
  nmax_bound := cd.nmax_bound
  robust := h

end ClassData

end Data

/-! ## The class bounds at energy level and the upper prices of the diagonals -/

section Energy

variable {a : ℝ}
  {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

/-- **The class bounds at energy level, with the upper prices of their diagonals**
(`thm:envelopes`(i), `cor:envelope-costs`, `cor:var-classes` at energy level;
`lem:bracket-energy` for the diagonals). The fields `Θ`, `Z`, `u`, `wc`, `ρ`, `energy` and
`consistent` are those of B4's `ClassEnergyInputs`; `wc_nonneg`, `v`, `errK`, `errw` and `upper`
are new. *Hypotheses*: `energy` (analytic: Sections 22–23 at energy level), `upper` (analytic:
`lem:bracket-energy`), `consistent` and `errw` (evaluations at the upper prices). -/
structure ClassEnergyData (D : TheoremCBlock.ComparisonData a m₀ blk p pr h E)
    (cd : ClassData D.CL) where
  /-- The labelled positive diagonals of the envelopes. -/
  Θ : ℕ → Type
  [ΘFintype : ∀ L, Fintype (Θ L)]
  /-- Their energies at a counterexample, and their upper prices. -/
  Z : ∀ L, Finset ℤ → Θ L → ℝ
  u : ∀ L, Θ L → ℝ
  /-- The weight of the class `i` on the diagonal `j`, nonnegative. -/
  wc : ∀ L, cd.ι L → Θ L → ℝ
  wc_nonneg : ∀ L i j, 0 ≤ wc L i j
  /-- The evaluated residual of a selection (the parts of its class bound not on a diagonal). -/
  ρ : ∀ L, Choice (D.CL.T L) → ℝ
  /-- **The class bounds at energy level**, robustly and uniformly in the classes. -/
  energy : ∃ ε : ℕ → ℝ, Tendsto ε atTop (𝓝 0) ∧ ∃ c : ℝ, 0 ≤ c ∧
    ∃ r : ∀ L, Finset ℤ → Choice (D.CL.T L) → ℝ, (∀ L A ω, 0 ≤ r L A ω) ∧
    Param.AtCounterexamples (Params.ofDecay a) D.Y fun L A =>
      (∀ i, ∑ ω ∈ cd.clsSel L i, |term (D.FS.lam L) (D.CL.ζ L) (blockLift m₀ blk p L A) ω| ≤
        ∑ j, wc L i j * Z L A j +
          ∑ ω ∈ cd.clsSel L i, ((ρ L ω + ε L * monomial (D.CL.π L) ω) * D.Y L A + r L A ω)) ∧
      ∑ ω ∈ cd.sel L, r L A ω ≤ remainder c L A
  /-- **The evaluation at the upper prices** is at most the class bound `φ`. -/
  consistent : ∀ L i, ∑ j, wc L i j * u L j + ∑ ω ∈ cd.clsSel L i, ρ L ω ≤
    ∑ ω ∈ cd.clsSel L i, cd.φ L ω
  /-- The error weights of the upper prices. -/
  v : ∀ L, Θ L → ℝ
  /-- The error weights of a class are dominated by its prices. -/
  errK : ℝ
  errw : ∀ L i, ∑ j, wc L i j * v L j ≤ errK * ∑ ω ∈ cd.clsSel L i, monomial (D.CL.π L) ω
  /-- **The upper prices of the diagonals** (`lem:bracket-energy`, (E1)), robustly, with
  nonnegative remainders weighted by `w_j = ∑_i w_{ij}`. -/
  upper : ∃ ε₃ : ℕ → ℝ, (∀ L, 0 ≤ ε₃ L) ∧ Tendsto ε₃ atTop (𝓝 0) ∧ ∃ c₃ : ℝ, 0 ≤ c₃ ∧
    ∃ r : ∀ L, Finset ℤ → Θ L → ℝ, (∀ L A j, 0 ≤ r L A j) ∧
    Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
      ∀ j, Z L A j ≤ (u L j + ε₃ L * v L j) * D.Y L A + r L A j) ∧
    Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
      ∑ j, (∑ i, wc L i j) * r L A j ≤ remainder c₃ L A)

attribute [instance] ClassEnergyData.ΘFintype

namespace ClassEnergyData

variable {D : TheoremCBlock.ComparisonData a m₀ blk p pr h E} {cd : ClassData D.CL}
  (ED : ClassEnergyData D cd)

/-- The diagonal weights `w_j = ∑_i w_{ij}`. -/
noncomputable def w (L : ℕ) (j : ED.Θ L) : ℝ := ∑ i, ED.wc L i j

include ED in
omit [DecidableEq P] in
/-- **The robust evaluated class bounds from the class bounds at energy level** (`def:cp5`,
`def:robust`; the evaluation of `thm:envelopes`(i), `cor:envelope-costs`, `cor:var-classes` at
the upper prices of `lem:bracket-energy`). On a class `𝒞_i`:
`∑_{𝒞_i} |I_ω| ≤ ∑_j w_{ij} Z_j + ∑ ((ρ + επ)Y + r)
  ≤ (∑_j w_{ij} u_j + ∑ ρ) Y + ε₃ (∑_j w_{ij} v_j) Y + ∑_j w_{ij} r_j + ∑ (επ Y + r)
  ≤ ∑ ((φ + (ε + K ε₃) π) Y + r + share)`. -/
theorem robust : cd.Robust := by
  classical
  obtain ⟨ε, hε, c, hc, r, hr0, hE⟩ := ED.energy
  obtain ⟨ε₃, hε₃0, hε₃, c₃, hc₃, r₃, hr₃0, hU, hUr⟩ := ED.upper
  set Rc : ∀ L, Finset ℤ → cd.ι L → ℝ := fun L A i => ∑ j, ED.wc L i j * r₃ L A j with hRc
  have hRc0 : ∀ L A i, 0 ≤ Rc L A i := fun L A i =>
    sum_nonneg fun j _ => mul_nonneg (ED.wc_nonneg L i j) (hr₃0 L A j)
  refine ⟨fun L => ε L + ED.errK * ε₃ L, ?_, c + c₃, add_nonneg hc hc₃,
    fun L A ω => r L A ω + share (cd.sel L) (cd.cls L) (Rc L A) ω,
    fun L A ω => add_nonneg (hr0 L A ω) (share_nonneg _ _ (hRc0 L A) ω), ?_⟩
  · simpa using hε.add (hε₃.const_mul ED.errK)
  filter_upwards [hE, hU, hUr] with L h1 h2 h3
  intro C hC hind A hA hcount
  obtain ⟨hcls, hrs⟩ := h1 C hC hind A hA hcount
  have hZ := h2 C hC hind A hA hcount
  have hR := h3 C hC hind A hA hcount
  have hY : 0 < D.Y L A := TheoremCParam.counterexample_pos hC hcount
  set Y := D.Y L A with hYdef
  refine ⟨fun i => ?_, ?_⟩
  · set S := cd.clsSel L i with hS
    by_cases hne : S.Nonempty
    · have hshare : ∑ ω ∈ S, share (cd.sel L) (cd.cls L) (Rc L A) ω = Rc L A i :=
        sum_share_class _ _ _ i hne
      -- the diagonals at their upper prices
      have hdiag : ∑ j, ED.wc L i j * ED.Z L A j ≤
          (∑ j, ED.wc L i j * ED.u L j) * Y + ε₃ L * (∑ j, ED.wc L i j * ED.v L j) * Y +
            Rc L A i := by
        have h := sum_le_sum fun j (_ : j ∈ (univ : Finset (ED.Θ L))) =>
          mul_le_mul_of_nonneg_left (hZ j) (ED.wc_nonneg L i j)
        refine h.trans (le_of_eq ?_)
        rw [hRc]
        simp only [Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
        exact sum_congr rfl fun j _ => by ring
      have herr : ε₃ L * (∑ j, ED.wc L i j * ED.v L j) * Y ≤
          ε₃ L * (ED.errK * ∑ ω ∈ S, monomial (D.CL.π L) ω) * Y :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (ED.errw L i) (hε₃0 L)) hY.le
      have hcons : (∑ j, ED.wc L i j * ED.u L j + ∑ ω ∈ S, ED.ρ L ω) * Y ≤
          (∑ ω ∈ S, cd.φ L ω) * Y :=
        mul_le_mul_of_nonneg_right (ED.consistent L i) hY.le
      have hi := hcls i
      rw [sum_affine] at hi
      have e2 : ∑ ω ∈ S, ((cd.φ L ω + (ε L + ED.errK * ε₃ L) * monomial (D.CL.π L) ω) * Y +
            (r L A ω + share (cd.sel L) (cd.cls L) (Rc L A) ω)) =
          (∑ ω ∈ S, cd.φ L ω) * Y +
            (ε L + ED.errK * ε₃ L) * (∑ ω ∈ S, monomial (D.CL.π L) ω) * Y +
            (∑ ω ∈ S, r L A ω + ∑ ω ∈ S, share (cd.sel L) (cd.cls L) (Rc L A) ω) := by
        rw [sum_affine, sum_add_distrib]
      change ∑ ω ∈ S, |term (D.FS.lam L) (D.CL.ζ L) (blockLift m₀ blk p L A) ω| ≤
        ∑ ω ∈ S, ((cd.φ L ω + (ε L + ED.errK * ε₃ L) * monomial (D.CL.π L) ω) * Y +
            (r L A ω + share (cd.sel L) (cd.cls L) (Rc L A) ω))
      rw [e2, hshare]
      nlinarith [hdiag, herr, hcons, hi]
    · rw [not_nonempty_iff_eq_empty.mp hne]
      simp
  · have hsh := sum_share_le (cd.sel L) (cd.cls L) (hRc0 L A)
    have hsw : ∑ i, Rc L A i = ∑ j, (∑ i, ED.wc L i j) * r₃ L A j := by
      rw [hRc, sum_comm]
      exact sum_congr rfl fun j _ => by rw [sum_mul]
    change ∑ ω ∈ cd.sel L, (r L A ω + share (cd.sel L) (cd.cls L) (Rc L A) ω) ≤
      remainder (c + c₃) L A
    rw [sum_add_distrib, JointClosing.remainder_add]
    linarith

/-- B4's `ClassInputs` of the construction, with `robust` proved. -/
noncomputable def toCI : ClassInputs D.CL := cd.toInputs ED.robust

/-- B4's `ClassEnergyInputs` of the construction. -/
noncomputable def toCE : ClassEnergyInputs D ED.toCI where
  Θ := ED.Θ
  ΘFintype := ED.ΘFintype
  Z := ED.Z
  u := ED.u
  wc := ED.wc
  ρ := ED.ρ
  energy := ED.energy
  consistent L i := (ED.consistent L i).trans_eq
    (sum_congr rfl fun ω _ => (ClassInputs.phi_eq ED.toCI L ω).symm)

omit [DecidableEq P] in
theorem toCE_w (L : ℕ) (j : ED.Θ L) : ED.toCE.w L j = ED.w L j := rfl

end ClassEnergyData

/-- **The joint mean allocation without its upper prices** (`cor:joint-closing`): B4's
`MeanAllocation` with `upper` replaced by `ClassEnergyData.upper` and the gate `V` on the error
weights; `b ≥ 0` (the retained mean coefficients are nonnegative, `prop:record:mean-credit`).
*Hypotheses*: `mean` (J2, `prop:record:mean-credit`), `resid` (`cert:four-routes-closing`),
`alloc` (`prop:joint-middle-mean`, `prop:joint-upper-mean`), `hV` (numerical). -/
structure MeanData {D : TheoremCBlock.ComparisonData a m₀ blk p pr h E} {cd : ClassData D.CL}
    (ED : ClassEnergyData D cd) where
  /-- The retained mean coefficients on the shared diagonals. -/
  b : ∀ L, ED.Θ L → ℝ
  b_nonneg : ∀ L j, 0 ≤ b L j
  /-- (J2) **The mean expansion** (`prop:record:mean-credit`, Steps 1–2). -/
  mean : ∃ ε₂ : ℕ → ℝ, Tendsto ε₂ atTop (𝓝 0) ∧ ∃ c₂ : ℝ, 0 ≤ c₂ ∧
    Param.AtCounterexamples (Params.ofDecay a) D.Y fun L A =>
      (targetLedger.m₁ - ε₂ L) * D.Y L A + ∑ j, b L j * ED.Z L A j - remainder c₂ L A ≤
        (energyMean (blockLift m₀ blk p) D.ME.ML L A +
          energyMean (blockLift m₀ blk p) D.ME.MR L A) / 2
  /-- The gate on the error weights of the upper prices. -/
  V : ℝ
  hV : ∀ L, ∑ j, (63 * ED.w L j - b L j) * ED.v L j ≤ V
  /-- **The residual gates** `63 w_j − b_j ≥ 0` (`cert:four-routes-closing`). -/
  resid : ∀ L j, b L j ≤ 63 * ED.w L j
  /-- **The joint mean allocations** (`prop:joint-middle-mean`, `prop:joint-upper-mean`). -/
  alloc : ∀ L, ledgerDelta targetLedger ≤ ∑ j, b L j * ED.u L j

namespace MeanData

variable {D : TheoremCBlock.ComparisonData a m₀ blk p pr h E} {cd : ClassData D.CL}
  {ED : ClassEnergyData D cd} (MD : MeanData ED)

omit [DecidableEq P] in
/-- **(J3) of the mean allocation from the upper prices of the diagonals**: since `0 ≤ b_j`,
`r_j ≥ 0`, `(63 w_j − b_j) r_j ≤ 63 w_j r_j`. -/
theorem upper : ∃ ε₃ : ℕ → ℝ, (∀ L, 0 ≤ ε₃ L) ∧ Tendsto ε₃ atTop (𝓝 0) ∧ ∃ V c₃ : ℝ, 0 ≤ c₃ ∧
    (∀ L, ∑ j, (63 * ED.toCE.w L j - MD.b L j) * ED.v L j ≤ V) ∧
    ∃ r : ∀ L, Finset ℤ → ED.Θ L → ℝ,
    Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
      ∀ j, ED.toCE.Z L A j ≤ (ED.toCE.u L j + ε₃ L * ED.v L j) * D.Y L A + r L A j) ∧
    Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
      ∑ j, (63 * ED.toCE.w L j - MD.b L j) * r L A j ≤ remainder c₃ L A) := by
  obtain ⟨ε₃, hε₃0, hε₃, c₃, hc₃, r, hr0, hU, hUr⟩ := ED.upper
  refine ⟨ε₃, hε₃0, hε₃, MD.V, 63 * c₃, by positivity, MD.hV, r, hU, ?_⟩
  filter_upwards [hUr] with L hL
  intro C hC hind A hA hcount
  have h := hL C hC hind A hA hcount
  have hle : ∑ j, (63 * ED.toCE.w L j - MD.b L j) * r L A j ≤
      63 * ∑ j, (∑ i, ED.wc L i j) * r L A j := by
    rw [mul_sum]
    refine sum_le_sum fun j _ => ?_
    have := mul_nonneg (MD.b_nonneg L j) (hr0 L A j)
    have e : ED.toCE.w L j = ∑ i, ED.wc L i j := rfl
    rw [e]
    nlinarith
  have e3 : remainder (63 * c₃) L A = 63 * remainder c₃ L A := by
    unfold remainder
    ring
  rw [e3]
  linarith

/-- B4's `MeanAllocation` from `MD` and the upper prices of `ED`. -/
noncomputable def toMA : MeanAllocation D ED.toCE where
  b := MD.b
  v := ED.v
  mean := MD.mean
  upper := MD.upper
  resid := MD.resid
  alloc := MD.alloc

include MD in
omit [DecidableEq P] in
/-- **`JB` from the class data at energy level** (`cor:joint-closing`,
`eq:final-joint-closing`): B4's `MeanAllocation.jointBound` at `ED.toCI`, `ED.toCE`,
`MD.toMA`. -/
theorem jointBound (hcard : Fintype.card E = 6) (PD : PolynomialData ED.toCI)
    (hE1 : D.EnvelopeBoundNonneg) (hB : D.B ≤ targetLedger.B) :
    JointBound D targetLedger.jointConstant :=
  MeanAllocation.jointBound hcard PD hE1 hB MD.toMA

end MeanData

end Energy

end Sarkozy.ClassInputsPaper
