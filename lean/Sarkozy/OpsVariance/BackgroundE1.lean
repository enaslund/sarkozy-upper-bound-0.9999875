module

public import Sarkozy.OpsVariance.Background
public import Sarkozy.OpsVariance.FrontCredit

@[expose] public section

/-!
# (E1) for the background diagonals of `X ∪ Z` from the subset terms

`paper/sections/22_variance.tex`, proof of `prop:background-variance`(a), "A background term"
(`Y[Diag_ι(m^X_s ⊗ m^Z_s)] ≤ (1 + o(1)) C_{X∪Z} Y`), "Exterior expansion" (the selected diagonal
`D_{E_s,𝔅} = Diag_ι(m_{E_s,𝔅})` of `E_s` at the background blocks); `def:cp4`(b) (the norm envelope
of a matching change is `Diag_ι` of the record's half marginal);
`paper/sections/10_comparison_lemmas.tex`, (E1).

The background terms of `prop:background-variance`(a) need (E1) with `μ` outside for
`Diag_X(m_s) ⊗ Diag_Z(m'_s)`, where on the background blocks `Z` the half marginals are those of the
matching record `E_s` (W1's `hDZ0`, `hDZ1` in `background_variance_a_blocks`;
`hres_of_background_rem`).
If the background record of `𝔅 ∈ Z` is the record `t 𝔅` of the comparison law with symmetric type,
this diagonal is the envelope of the **extended selection** `ω ⊕ (t, sym)|_Z` (`extSel`), and (E1)
for it is EC's subset term `E1Sub` at the extended selection and `f = ∅`:

* `extSel`, `support_extSel`, `isSelection_extSel` (symmetric entries keep the skew count even),
  `envM_extSel_of_not_mem`, `envM_extSel_of_mem`;
* `diagFamZ_eq_extSel`: `Diag_X(envM ω) ⊗ Diag_Z(m') ⊗ μ = Diag_{X∪Z}(envM ω') ⊗ μ` when `m'` is the
  half marginal of the norm envelopes of the records `t` on `Z`;
* **`e1Z_of_sub`**: `Y[Diag_X ⊗ Diag_Z ⊗ μ] ≤ (1 + ε_E) C_{X∪Z} Y + r0(ω', ∅)` at every least
  counterexample. At the obligations' data `E1Sub` holds with `ε_E = u_L` and `r0 = r0X` (EC).

**Remainder budget (finding).** The background remainders `r0(ω', ∅)` enter `hres` with the weight
of the selected price `γ₀ = π̃_ω` (times `k C_m C_r c_Z/(1 − k)`), not with `π̃_{ω'}` as in EC's
`E1Rem`. They are summed through the finiteness of the middle range (the paper: "The middle range
has finitely many blocks, so the `o(1)` below add up to `o(1)`"), with EC's per-term small-union
bound
(`e1SubSmallPT_proved`), not through `E1Rem`.
-/

open Filter Finset Function
open scoped Topology BigOperators

namespace Sarkozy.OpsVariance

open Sarkozy.ClassInputsPaper Sarkozy.ClassBoundsPaper Sarkozy.TheoremC Sarkozy.TheoremCBlock
  Sarkozy.BlockFrame Sarkozy.RecordExpansion Sarkozy.RecordExpansion.Choice Sarkozy.EnvelopeSteps
  Sarkozy.FourierArithmetic Sarkozy.Functional Sarkozy.IndexSupport Sarkozy.Comparison
  Sarkozy.PaperFrame Sarkozy.Variance
open Sarkozy.Param (Params)
open Sarkozy.Companion (E1Sub)

variable {a : ℝ}
  {J₀ : Type} [Fintype J₀] [DecidableEq J₀] {m₀ : J₀ → ℕ} [∀ i, NeZero (m₀ i)]
  {Bk : Type} [Fintype Bk] [DecidableEq Bk] {blk : J₀ → Bk}
  {J : ℕ → Type} [∀ L, Fintype (J L)] [∀ L, DecidableEq (J L)] {p : ∀ L, J L → ℕ}
  [∀ L j, NeZero (p L j)]
  {P : Type} [Fintype P] [DecidableEq P] {pr h : P → ℕ} [∀ q, NeZero (pr q ^ h q)]
  {E : Type} [Fintype E] [DecidableEq E]

variable {D : TheoremCBlock.ComparisonData a m₀ blk p pr h E}

/-- **The selection `ω` extended by the records `t` with symmetric type on `Z`.** -/
def extSel {L : ℕ} (ω : Choice (D.CL.T L)) (Z : Finset (BlockAtom Bk J L))
    (t : ∀ b, D.CL.T L b) : Choice (D.CL.T L) :=
  fun b => if b ∈ Z then some (t b, .sym) else ω b

omit [DecidableEq P] in
theorem support_extSel {L : ℕ} (ω : Choice (D.CL.T L)) (Z : Finset (BlockAtom Bk J L))
    (t : ∀ b, D.CL.T L b) : Choice.support (extSel ω Z t) = Choice.support ω ∪ Z := by
  ext b
  rw [mem_union]
  unfold Choice.support
  rw [mem_filter, mem_filter]
  unfold extSel
  by_cases hb : b ∈ Z
  · simp [hb]
  · simp [hb]

omit [DecidableEq P] in
/-- Symmetric entries on blocks outside the support keep a selection a selection. -/
theorem isSelection_extSel {L : ℕ} {ω : Choice (D.CL.T L)} (hω : IsSelection ω)
    (Z : Finset (BlockAtom Bk J L)) (hZ : Disjoint (Choice.support ω) Z)
    (t : ∀ b, D.CL.T L b) : IsSelection (extSel ω Z t) := by
  refine ⟨?_, ?_⟩
  · rw [← Choice.support_nonempty_iff, support_extSel]
    obtain ⟨b, hb⟩ := (Choice.support_nonempty_iff ω).mpr hω.1
    exact ⟨b, mem_union_left _ hb⟩
  · have e : Choice.skewCount (extSel ω Z t) = Choice.skewCount ω := by
      unfold Choice.skewCount
      congr 1
      ext b
      rw [mem_filter, mem_filter]
      unfold extSel
      by_cases hb : b ∈ Z
      · have hn : ω b = none := by
          have : b ∉ Choice.support ω := fun h => disjoint_left.mp hZ h hb
          simpa [Choice.support] using this
        simp only [hb, ↓reduceIte, hn, isSkewEntry]
      · simp only [hb, ↓reduceIte]
    rw [e]
    exact hω.2

omit [DecidableEq P] in
theorem envM_extSel_of_not_mem {L : ℕ} (ω : Choice (D.CL.T L)) {Z : Finset (BlockAtom Bk J L)}
    (t : ∀ b, D.CL.T L b) {b : BlockAtom Bk J L} (hb : b ∉ Z) :
    envM D L (extSel ω Z t) b = envM D L ω b := by
  unfold envM extSel
  simp [hb]

omit [DecidableEq P] in
theorem envM_extSel_of_mem {L : ℕ} (ω : Choice (D.CL.T L)) {Z : Finset (BlockAtom Bk J L)}
    (t : ∀ b, D.CL.T L b) {b : BlockAtom Bk J L} (hb : b ∈ Z) :
    envM D L (extSel ω Z t) b = halfMarginalPlus reservedCut (D.CL.D L b (t b) .sym) := by
  unfold envM extSel
  simp [hb]

omit [DecidableEq P] in
/-- **The background diagonal is the envelope diagonal of the extended selection**:
`Diag_X(envM ω) ⊗ Diag_Z(m') ⊗ μ = Diag_{X∪Z}(envM ω') ⊗ μ` for `X = supp ω` disjoint from `Z` and
`m'` the half marginals of the norm envelopes `D^s_{𝔅,t 𝔅}` on `Z`. -/
theorem diagFamZ_eq_extSel {L : ℕ} (ω : Choice (D.CL.T L)) (Z : Finset (BlockAtom Bk J L))
    (hZ : Disjoint (Choice.support ω) Z) (t : ∀ b, D.CL.T L b)
    (ms : ∀ b : BlockAtom Bk J L, (reservedCut.Half → BlockLabel m₀ blk p L b) → ℝ)
    (hms : ∀ b ∈ Z, ms b = halfMarginalPlus reservedCut (D.CL.D L b (t b) .sym)) :
    diagFamZ reservedCut (D.R.law p L) (Choice.support ω) Z (Choice.support ω) (envM D L ω) ms =
      diagFam reservedCut (D.R.law p L) (Choice.support (extSel ω Z t))
        (Choice.support (extSel ω Z t)) (envM D L (extSel ω Z t)) := by
  funext b
  unfold diagFamZ diagFam
  rw [support_extSel]
  by_cases hX : b ∈ Choice.support ω
  · have hbZ : b ∉ Z := fun h => disjoint_left.mp hZ hX h
    simp only [hX, ↓reduceIte, mem_union, true_or]
    rw [envM_extSel_of_not_mem ω t hbZ]
  · by_cases hbZ : b ∈ Z
    · simp only [hX, hbZ, ↓reduceIte, mem_union, or_true]
      rw [envM_extSel_of_mem ω t hbZ, hms b hbZ]
    · simp only [hX, hbZ, ↓reduceIte, mem_union, or_self]

omit [DecidableEq P] in
/-- **(E1) with `μ` outside for the background diagonals from the subset terms** (`E1Sub` at the
extended selection and `f = ∅`): for a selection `ω`, a set `Z` of blocks outside its support,
records `t` on `Z` and their norm-envelope half marginals `m'`,
`Y[Diag_X(envM ω) ⊗ Diag_Z(m') ⊗ μ] ≤ (1 + ε_E) C_{X∪Z} Y + r0(ω ⊕ (t, sym)|_Z, ∅)`. -/
theorem e1Z_of_sub {εE : ℕ → ℝ} {r0 : Companion.E1R0 D} (hsub : E1Sub D εE r0) :
    Param.AtCounterexamples (Params.ofDecay a) D.Y (fun L A =>
      ∀ ω : Choice (D.CL.T L), IsSelection ω → ∀ (Z : Finset (BlockAtom Bk J L)),
      Disjoint (Choice.support ω) Z → ∀ (t : ∀ b, D.CL.T L b)
      (ms : ∀ b : BlockAtom Bk J L, (reservedCut.Half → BlockLabel m₀ blk p L b) → ℝ),
      (∀ b ∈ Z, ms b = halfMarginalPlus reservedCut (D.CL.D L b (t b) .sym)) →
        diagonalIntegral (tensorLaw (diagFamZ reservedCut (D.R.law p L) (Choice.support ω) Z
          (Choice.support ω) (envM D L ω) ms)) (blockLift m₀ blk p L A) ≤
        (1 + εE L) * selProd D L (extSel ω Z t) * D.Y L A +
          r0 L A (extSel ω Z t) (fun _ => false)) := by
  filter_upwards [e1mu_of_sub hsub] with L hL
  intro C hC hind A hA hcount ω hω Z hZ t ms hms
  rw [diagFamZ_eq_extSel ω Z hZ t ms hms]
  exact hL C hC hind A hA hcount (extSel ω Z t) (isSelection_extSel hω Z hZ t)

end Sarkozy.OpsVariance
