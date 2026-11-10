module

public import Sarkozy.Peyre.Main
public import Mathlib.Data.ZMod.Basic

/-!
# Pinned influence, I: influence data (`def:mid:influence`)

Paper `13_cuts_correlations.tex`, Section `subsec:cuts:influence`, and the graph laws of
`12_labellings.tex` (`def:graphs:labeling`).

* `OrientedGraph U`: a relation `edge` on a finite vertex type, irreflexive and asymmetric
  (no loops, at most one edge on each unordered pair). `Adj` is adjacency in either
  orientation, and `deg` counts incoming and outgoing edges.
* `IsNzSq x`: `x ∈ Q_p`, the nonzero squares of `𝔽_p`. Strict-square and injective
  labellings, `injLabellings G p = Inj_p(G)`, and the graph law `graphLaw = λ_p(G)`, the
  uniform law on `Inj_p(G)`. It is a `FiniteLaw` on `U → ZMod p` that vanishes off
  `Inj_p(G)`.
* Pinnings `(S, s)`: the event `{y_S = s}` is `pinEvent S s`. The pinning is feasible when
  this event has positive probability. `Extends`, the free set `free S = U \ S`, and the
  maximal free degree `maxDeg G F = Δ_F`.
* `CountErrors`: the count-error conditions `eq:mid:standing`, stated as an explicit
  hypothesis structure.
* `influence G p w i j = ε_ij`, `eq:mid:epsij`. Here `r = rp p = p^{-1/2}` and
  `2^{(d_i+d_j-2)/2} = √2^{d_i+d_j-2}`; for an edge, `d_i, d_j ≥ 1`, so the natural-number
  subtraction is exact.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.Influence

open Sarkozy Sarkozy.Peyre

/-- An oriented graph (`def:graphs:labeling`): no loops and at most one edge on each unordered
pair of vertices. `edge u v` is the directed edge `(u, v)`. -/
structure OrientedGraph (U : Type*) where
  edge : U → U → Prop
  irrefl : ∀ u, ¬ edge u u
  asymm : ∀ u v, edge u v → ¬ edge v u

namespace OrientedGraph

variable {U : Type*} (G : OrientedGraph U)

/-- `u` and `v` are joined by an edge, in either orientation. -/
def Adj (u v : U) : Prop := G.edge u v ∨ G.edge v u

theorem adj_symm {u v : U} (h : G.Adj u v) : G.Adj v u := h.symm

theorem not_adj_self (u : U) : ¬ G.Adj u u := fun h => h.elim (G.irrefl u) (G.irrefl u)

open Classical in
/-- The degree `d_u`: the number of incoming and outgoing edges at `u`. -/
noncomputable def deg [Fintype U] (u : U) : ℕ := (Finset.univ.filter (fun v => G.Adj u v)).card

end OrientedGraph

/-- `x ∈ Q_p`: `x` is a nonzero square of `ZMod p`. -/
def IsNzSq {p : ℕ} (x : ZMod p) : Prop := x ≠ 0 ∧ IsSquare x

variable {U : Type*}

/-- A strict-square labelling: `z_v - z_u ∈ Q_p` for every edge `(u, v)`. -/
def IsStrictSquare (G : OrientedGraph U) {p : ℕ} (z : U → ZMod p) : Prop :=
  ∀ u v, G.edge u v → IsNzSq (z v - z u)

open Classical in
/-- `Inj_p(G)`, the injective strict-square labellings. -/
noncomputable def injLabellings [Fintype U] [DecidableEq U] (G : OrientedGraph U) (p : ℕ)
    [NeZero p] : Finset (U → ZMod p) :=
  Finset.univ.filter (fun z => Function.Injective z ∧ IsStrictSquare G z)

open Classical in
/-- The graph law `λ_p(G)`, the uniform probability on `Inj_p(G)` (when nonempty). -/
noncomputable def graphLaw [Fintype U] [DecidableEq U] (G : OrientedGraph U) (p : ℕ) [NeZero p]
    (h : (injLabellings G p).Nonempty) : FiniteLaw (U → ZMod p) where
  weight z := if z ∈ injLabellings G p then 1 / ((injLabellings G p).card : ℝ) else 0
  nonneg z := by
    split_ifs
    · positivity
    · exact le_refl 0
  total := by
    rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]
    have : ((injLabellings G p).card : ℝ) ≠ 0 := by
      exact_mod_cast (Finset.card_pos.mpr h).ne'
    field_simp

/-- The pinning event `{y_S = s}`; only the values of `s` on `S` matter. -/
def pinEvent {p : ℕ} (S : Finset U) (s : U → ZMod p) : (U → ZMod p) → Prop :=
  fun ω => ∀ v ∈ S, ω v = s v

/-- `(S', s')` extends `(S, s)`: `S ⊆ S'` and `s'|_S = s|_S`. -/
def Extends {p : ℕ} (S' : Finset U) (s' : U → ZMod p) (S : Finset U) (s : U → ZMod p) :
    Prop :=
  S ⊆ S' ∧ ∀ v ∈ S, s' v = s v

/-- The free vertices `F = U \ S` of a pinning. -/
def free [Fintype U] [DecidableEq U] (S : Finset U) : Finset U := Finset.univ \ S

/-- `Δ_F`, the maximal degree of a vertex of `F` (`0` if `F` is empty). -/
noncomputable def maxDeg [Fintype U] (G : OrientedGraph U) (F : Finset U) : ℕ := F.sup G.deg

open Classical in
/-- The count `N = #{x ∈ 𝔽_p \ E' : ε_m (x - a_m) ∈ Q_p for all m}` of `eq:mid:standing`. -/
noncomputable def standingCount {p : ℕ} [NeZero p] {t : ℕ} (a sg : Fin t → ZMod p)
    (E' : Finset (ZMod p)) : ℕ :=
  (Finset.univ.filter (fun x => x ∉ E' ∧ ∀ m, IsNzSq (sg m * (x - a m)))).card

/-- One inequality of `eq:mid:standing`: for all distinct roots `a_1, …, a_t` with
`t ≤ T`, all signs `ε_m = ±1` and every `E' ⊇ {a_m}` with `|E'| ≤ M`, `2^t N / p ≥ 1 - w`. -/
def StandingBound (p : ℕ) [NeZero p] (T M : ℕ) (w : ℝ) : Prop :=
  ∀ (t : ℕ) (a sg : Fin t → ZMod p) (E' : Finset (ZMod p)),
    Function.Injective a → (∀ m, sg m = 1 ∨ sg m = -1) → (∀ m, a m ∈ E') → t ≤ T →
      E'.card ≤ M → 1 - w ≤ (2 : ℝ) ^ t * (standingCount a sg E' : ℝ) / p

/-- Count errors for `(G, F)` at `p` (`def:mid:influence` (i), `eq:mid:standing`), with
`n = |U|`. -/
structure CountErrors [Fintype U] (G : OrientedGraph U) (p : ℕ) [NeZero p] (F : Finset U)
    (w wconn : ℝ) : Prop where
  w_nonneg : 0 ≤ w
  w_lt_one : w < 1
  wconn_nonneg : 0 ≤ wconn
  wconn_lt_one : wconn < 1
  first : StandingBound p (maxDeg G F) (Fintype.card U) w
  conn : StandingBound p (maxDeg G F + 1) (2 * Fintype.card U) wconn

/-- `r = p^{-1/2}`. -/
noncomputable def rp (p : ℕ) : ℝ := 1 / √(p : ℝ)

/-- `H_w = (1 + w) / (1 - w)²`. -/
noncomputable def Hw (w : ℝ) : ℝ := (1 + w) / (1 - w) ^ 2

open Classical in
/-- The influence entries `ε_ij` of `eq:mid:epsij` (`ε_ii = 0`). The influence matrix is
`(ε_ij)_{i,j ∈ F}`, i.e. this function restricted to the free set. -/
noncomputable def influence [Fintype U] (G : OrientedGraph U) (p : ℕ) (w : ℝ) (i j : U) : ℝ :=
  if i = j then 0
  else if G.Adj i j then Hw w * √2 ^ (G.deg i + G.deg j - 2) * (rp p + rp p ^ 2)
  else Hw w * √2 ^ (G.deg i + G.deg j) * rp p ^ 2

theorem rp_nonneg (p : ℕ) : 0 ≤ rp p := div_nonneg zero_le_one (Real.sqrt_nonneg _)

theorem Hw_nonneg {w : ℝ} (hw : -1 ≤ w) : 0 ≤ Hw w :=
  div_nonneg (by linarith) (sq_nonneg _)

theorem influence_nonneg [Fintype U] (G : OrientedGraph U) (p : ℕ) {w : ℝ} (hw : -1 ≤ w)
    (i j : U) : 0 ≤ influence G p w i j := by
  classical
  unfold influence
  have h2 : (0 : ℝ) ≤ √2 := Real.sqrt_nonneg _
  have hr := rp_nonneg p
  have hH := Hw_nonneg hw
  split_ifs
  · exact le_refl 0
  · exact mul_nonneg (mul_nonneg hH (pow_nonneg h2 _)) (add_nonneg hr (sq_nonneg _))
  · exact mul_nonneg (mul_nonneg hH (pow_nonneg h2 _)) (sq_nonneg _)

theorem influence_symm [Fintype U] (G : OrientedGraph U) (p : ℕ) (w : ℝ) (i j : U) :
    influence G p w i j = influence G p w j i := by
  classical
  unfold influence
  by_cases hij : i = j
  · subst hij
    rfl
  · have hji : j ≠ i := fun h => hij h.symm
    have hadj : G.Adj i j ↔ G.Adj j i := ⟨G.adj_symm, G.adj_symm⟩
    simp only [hij, hji, ite_false, hadj, add_comm (G.deg i)]

theorem influence_self [Fintype U] (G : OrientedGraph U) (p : ℕ) (w : ℝ) (i : U) :
    influence G p w i i = 0 := by
  classical
  simp [influence]

end Sarkozy.Influence
