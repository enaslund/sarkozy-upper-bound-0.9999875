module

public import Sarkozy.SpectralD.CxErrors

@[expose] public section

/-!
# The small pair constants (`lem:spec:small`)

`paper/sections/14_spectral.tex`, `lem:spec:small`. For the graph law `λ = λ_p(G)` of an oriented
graph `G` on `n` vertices and distinct non-adjacent vertices `u, v`:
`|E_λ χ(y_v − y_u)| ≤ δ_v = (e_{d_v} + e_{d_v+1})/(1 − e_{d_v})`, `e_t = e_t(p, n)`, `d_v` the
degree of `v` (`graph_pair_corr`). The proof is the paper's: given the other labels, `y_v` is
uniform on its admissible set `𝒜` (`condE_graph_erase`); the subset
`𝒜⁺ = {a ∈ 𝒜 : χ(a − y_u) = 1}` is the admissible set of `v` in `G` with the edge `(u, v)` added
(`vertexAdmissible_addEdge`), so `lem:extension` counts both (`sum_chi_adm_le`); then average.

* `addEdge`: `G` with one edge added between non-adjacent vertices;
* `sum_condE_erase`: `E_μ[E_μ[F | y_{U∖v}]] = E_μ[F]` (WP-K's `condE_tower`);
* `graph_pair_corr`: the bound above;
* `deltaMu_small`, `deltaMu_small_min`: `lem:spec:small`(b) for the half law `μ = λ_p(G⁺)`:
  `|Δ^μ_kl| ≤ min(δ^μ_k, δ^μ_l)` for distinct non-adjacent `k, l`; `norm_deltaMu_le_one`.

New material for this paper.
-/

namespace Sarkozy.SpectralD.Cx

open Finset Sarkozy.SpectralC Sarkozy.Characters
open scoped BigOperators

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} [Fact p.Prime] {V : Type*} [Fintype V] [DecidableEq V]

/-- `G` with the edge `(u, v)` added, for `u ≠ v` with `(v, u) ∉ E`. -/
def addEdge (G : Labellings.OrientedGraph V) {u v : V} (huv : u ≠ v) (hvu : (v, u) ∉ G.E) :
    Labellings.OrientedGraph V where
  E := insert (u, v) G.E
  loopless w := by
    rw [mem_insert]
    rintro (h | h)
    · simp only [Prod.mk.injEq] at h
      exact huv (h.1.symm.trans h.2)
    · exact G.loopless w h
  oriented a b hab hba := by
    rw [mem_insert] at hab hba
    rcases hab with h1 | h1 <;> rcases hba with h2 | h2
    · simp only [Prod.mk.injEq] at h1 h2
      exact huv (h1.1.symm.trans h2.2)
    · simp only [Prod.mk.injEq] at h1
      obtain ⟨rfl, rfl⟩ := h1
      exact hvu h2
    · simp only [Prod.mk.injEq] at h2
      obtain ⟨rfl, rfl⟩ := h2
      exact hvu h1
    · exact G.oriented a b h1 h2

/-- The admissible set of `v` in `G + (u, v)` is `{a ∈ 𝒜 : χ(a − y_u) = 1}`. -/
lemma vertexAdmissible_addEdge (G : Labellings.OrientedGraph V) {u v : V} (huv : u ≠ v)
    (hvu : (v, u) ∉ G.E) (y : V → ZMod p) :
    Labellings.vertexAdmissible (addEdge G huv hvu) (univ.erase v) y v =
      (Labellings.vertexAdmissible G (univ.erase v) y v).filter
        (fun c => quadraticChar (ZMod p) (c - y u) = 1) := by
  classical
  have hu : u ∈ univ.erase v := mem_erase.mpr ⟨huv, mem_univ _⟩
  ext c
  simp only [Labellings.vertexAdmissible, mem_filter, mem_univ, true_and, addEdge, mem_insert]
  constructor
  · rintro ⟨h0, h1, h2⟩
    exact ⟨⟨h0, fun w hw h => h1 w hw (Or.inr h), fun w hw h => h2 w hw (Or.inr h)⟩,
      h1 u hu (Or.inl rfl)⟩
  · rintro ⟨⟨h0, h1, h2⟩, h3⟩
    refine ⟨h0, fun w hw h => ?_, fun w hw h => ?_⟩
    · rcases h with h | h
      · simp only [Prod.mk.injEq] at h
        rw [h.1]; exact h3
      · exact h1 w hw h
    · rcases h with h | h
      · simp only [Prod.mk.injEq] at h
        exact absurd h.1.symm huv
      · exact h2 w hw h

/-- Adding a non-edge `(u, v)` raises the degree of `v` by one. -/
lemma nbrCount_addEdge (G : Labellings.OrientedGraph V) {u v : V} (huv : u ≠ v)
    (huv' : (u, v) ∉ G.E) (hvu : (v, u) ∉ G.E) :
    Labellings.nbrCount (addEdge G huv hvu) (univ.erase v) v =
      Labellings.nbrCount G (univ.erase v) v + 1 := by
  classical
  have hu : u ∈ univ.erase v := mem_erase.mpr ⟨huv, mem_univ _⟩
  unfold Labellings.nbrCount
  have hset : (univ.erase v).filter (fun w => (w, v) ∈ (addEdge G huv hvu).E ∨
      (v, w) ∈ (addEdge G huv hvu).E) =
      insert u ((univ.erase v).filter (fun w => (w, v) ∈ G.E ∨ (v, w) ∈ G.E)) := by
    ext w
    simp only [mem_filter, mem_insert, addEdge, Prod.mk.injEq]
    constructor
    · rintro ⟨hw, (⟨h1, -⟩ | h1) | (⟨h1, h2⟩ | h1)⟩
      · exact Or.inl h1
      · exact Or.inr ⟨hw, Or.inl h1⟩
      · exact absurd h1.symm huv
      · exact Or.inr ⟨hw, Or.inr h1⟩
    · rintro (rfl | ⟨hw, h1 | h1⟩)
      · exact ⟨hu, Or.inl (Or.inl (by simp))⟩
      · exact ⟨hw, Or.inl (Or.inr h1)⟩
      · exact ⟨hw, Or.inr (Or.inr h1)⟩
  rw [hset, card_insert_of_notMem]
  simp only [mem_filter, not_and, not_or]
  exact fun _ => ⟨huv', hvu⟩

/-- `p e_t(p, n) = 2^t(h_t √p + n)`. -/
lemma p_mul_coarseErr (t n : ℕ) :
    (p : ℝ) * TraceMixing.coarseErr p t n =
      2 ^ t * (((t : ℝ) / 2 - 1 + (1 / 2) ^ t) * Real.sqrt p + n) := by
  have hq0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  have hs1 : Real.sqrt p * Real.sqrt p = p := Real.mul_self_sqrt hq0.le
  have hsp : 0 < Real.sqrt p := Real.sqrt_pos.mpr hq0
  have hpinv : (p : ℝ) * (Real.sqrt p)⁻¹ = Real.sqrt p := by
    rw [eq_comm, eq_mul_inv_iff_mul_eq₀ hsp.ne', hs1]
  unfold TraceMixing.coarseErr
  calc (p : ℝ) * (2 ^ t * (((t : ℝ) / 2 - 1 + (1 / 2) ^ t) * (Real.sqrt p)⁻¹ + n / p))
      = 2 ^ t * (((t : ℝ) / 2 - 1 + (1 / 2) ^ t) * ((p : ℝ) * (Real.sqrt p)⁻¹) +
          n * ((p : ℝ) / p)) := by ring
    _ = _ := by rw [hpinv, div_self hq0.ne', mul_one]

/-- The constant `δ_v = (e_d + e_{d+1})/(1 − e_d)` of `lem:spec:small`. -/
noncomputable def smallConst (p : ℕ) (d n : ℕ) : ℝ :=
  (TraceMixing.coarseErr p d n + TraceMixing.coarseErr p (d + 1) n) /
    (1 - TraceMixing.coarseErr p d n)

lemma smallConst_nonneg {d n : ℕ} (he : TraceMixing.coarseErr p d n < 1) :
    0 ≤ smallConst p d n := by
  have hq0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  unfold smallConst
  have h0 := TraceMixing.coarseErr_nonneg hq0 d n
  have h1 := TraceMixing.coarseErr_nonneg hq0 (d + 1) n
  exact div_nonneg (by linarith) (by linarith)

/-- **The counting step**: `|∑_{a ∈ 𝒜} χ(a − y_u)| ≤ δ_v |𝒜|` for non-adjacent `u ≠ v`. -/
theorem sum_chi_adm_le (hW : Labellings.WeilBound (ZMod p)) (G : Labellings.OrientedGraph V)
    {u v : V} (huv : u ≠ v) (huv' : (u, v) ∉ G.E) (hvu : (v, u) ∉ G.E)
    {y : V → ZMod p} (hy : Labellings.Feasible (ZMod p) G (univ.erase v) y)
    (he : TraceMixing.coarseErr p (Labellings.nbrCount G (univ.erase v) v)
      (Fintype.card V) < 1) :
    |((∑ c ∈ Labellings.vertexAdmissible G (univ.erase v) y v,
        quadraticChar (ZMod p) (c - y u) : ℤ) : ℝ)| ≤
      smallConst p (Labellings.nbrCount G (univ.erase v) v) (Fintype.card V) *
        (Labellings.vertexAdmissible G (univ.erase v) y v).card := by
  classical
  set A := univ.erase v with hA
  set d := Labellings.nbrCount G A v with hd
  set Adm := Labellings.vertexAdmissible G A y v with hAdm
  set G' := addEdge G huv hvu with hG'
  set Adm' := Labellings.vertexAdmissible G' A y v with hAdm'
  have hu : u ∈ A := mem_erase.mpr ⟨huv, mem_univ _⟩
  -- the signs on `𝒜`
  have hne : ∀ c ∈ Adm, c - y u ≠ 0 := by
    intro c hc h0
    simp only [hAdm, Labellings.vertexAdmissible, mem_filter, mem_univ, true_and] at hc
    exact hc.1 (mem_image.mpr ⟨u, hu, (sub_eq_zero.mp h0).symm⟩)
  have hsplit : (∑ c ∈ Adm, quadraticChar (ZMod p) (c - y u) : ℤ) =
      2 * (Adm.filter (fun c => quadraticChar (ZMod p) (c - y u) = 1)).card - Adm.card := by
    have h1 : ∀ c ∈ Adm, (quadraticChar (ZMod p) (c - y u) : ℤ) =
        2 * (if quadraticChar (ZMod p) (c - y u) = 1 then 1 else 0) - 1 := by
      intro c hc
      rcases quadraticChar_dichotomy (hne c hc) with h | h <;> simp [h]
    rw [sum_congr rfl h1, sum_sub_distrib, ← mul_sum, sum_boole, sum_const, card_eq_sum_ones]
    simp
  have hAdm'eq : Adm' = Adm.filter (fun c => quadraticChar (ZMod p) (c - y u) = 1) :=
    vertexAdmissible_addEdge G huv hvu y
  have hd' : Labellings.nbrCount G' A v = d + 1 := nbrCount_addEdge G huv huv' hvu
  -- feasibility in `G + (u, v)`
  have hy' : Labellings.Feasible (ZMod p) G' A y := by
    refine ⟨hy.1, fun e he1 h1 h2 => ?_⟩
    rw [hG', addEdge, mem_insert] at he1
    rcases he1 with h | h
    · rw [h] at h2; exact absurd h2 (by simp [hA])
    · exact hy.2 e h h1 h2
  -- the counts
  have hc1 := Labellings.card_vertexAdmissible hW G hy v
  have hc2 := Labellings.card_vertexAdmissible hW G' hy' v
  rw [hd', ← hAdm', hAdm'eq] at hc2
  rw [ZMod.card] at hc1 hc2
  have hAcard : (A.card : ℝ) = (Fintype.card V : ℝ) - 1 := by
    rw [hA, card_erase_of_mem (mem_univ v), card_univ,
      Nat.cast_sub (Fintype.card_pos_iff.mpr ⟨v⟩), Nat.cast_one]
  rw [hAcard] at hc1 hc2
  set a : ℝ := (Adm.card : ℝ) with ha
  set b : ℝ := ((Adm.filter (fun c => quadraticChar (ZMod p) (c - y u) = 1)).card : ℝ) with hb
  set n : ℝ := (Fintype.card V : ℝ) with hn
  set P : ℝ := (p : ℝ) with hP
  have hq1 : (1 : ℝ) ≤ P := by rw [hP]; exact_mod_cast (Fact.out : p.Prime).one_lt.le
  have hq0 : (0 : ℝ) < P := by linarith
  have hs0 := Cuts.SpecData.softError_le hq1 d
  have hs1 := Cuts.SpecData.softError_le hq1 (d + 1)
  have h2 : (0 : ℝ) < 2 ^ d := by positivity
  have h2' : (2 : ℝ) ^ (d + 1) = 2 * 2 ^ d := by rw [pow_succ]; ring
  rw [div_le_iff₀ h2] at hs0
  rw [div_le_iff₀ (by positivity), h2'] at hs1
  rw [h2'] at hc2
  have hE0 := p_mul_coarseErr (p := p) d (Fintype.card V)
  have hE1 := p_mul_coarseErr (p := p) (d + 1) (Fintype.card V)
  rw [h2'] at hE1
  set e0 := TraceMixing.coarseErr p d (Fintype.card V) with he0
  set e1 := TraceMixing.coarseErr p (d + 1) (Fintype.card V) with he1
  set H0 : ℝ := (d : ℝ) / 2 - 1 + (1 / 2) ^ d with hH0
  set H1 : ℝ := ((d + 1 : ℕ) : ℝ) / 2 - 1 + (1 / 2) ^ (d + 1) with hH1
  have hH0' : 0 ≤ H0 := TraceMixing.coarseH_nonneg d
  have hH1' : 0 ≤ H1 := TraceMixing.coarseH_nonneg (d + 1)
  have hsq : 0 ≤ Real.sqrt P := Real.sqrt_nonneg _
  have he0' : 0 ≤ e0 := TraceMixing.coarseErr_nonneg hq0 d (Fintype.card V)
  have he1' : 0 ≤ e1 := TraceMixing.coarseErr_nonneg hq0 (d + 1) (Fintype.card V)
  -- the two estimates
  obtain ⟨hup0, hlow0⟩ := hc1
  obtain ⟨hup1, hlow1⟩ := hc2
  have hdev1 : (2 * b - a) * 2 ^ d ≤ P * (e0 + e1) := by nlinarith
  have hdev2 : (a - 2 * b) * 2 ^ d ≤ P * (e0 + e1) := by nlinarith
  have hdev : |2 * b - a| * 2 ^ d ≤ P * (e0 + e1) := by
    rcases abs_cases (2 * b - a) with ⟨h, -⟩ | ⟨h, -⟩
    · rw [h]; exact hdev1
    · rw [h]; linarith
  have hlowa : P * (1 - e0) ≤ 2 ^ d * a := by nlinarith
  -- conclusion
  have hδ : smallConst p d (Fintype.card V) * (1 - e0) = e0 + e1 := by
    unfold smallConst
    rw [← he0, ← he1]
    field_simp [show (1 : ℝ) - e0 ≠ 0 by linarith]
  have hδ0 : 0 ≤ smallConst p d (Fintype.card V) := smallConst_nonneg he
  have hcast : ((∑ c ∈ Adm, quadraticChar (ZMod p) (c - y u) : ℤ) : ℝ) = 2 * b - a := by
    rw [hsplit]; push_cast; rfl
  rw [hcast]
  have key : |2 * b - a| * 2 ^ d ≤ smallConst p d (Fintype.card V) * a * 2 ^ d := by
    calc |2 * b - a| * 2 ^ d ≤ P * (e0 + e1) := hdev
      _ = smallConst p d (Fintype.card V) * (P * (1 - e0)) := by rw [← hδ]; ring
      _ ≤ smallConst p d (Fintype.card V) * (2 ^ d * a) :=
          mul_le_mul_of_nonneg_left hlowa hδ0
      _ = smallConst p d (Fintype.card V) * a * 2 ^ d := by ring
  exact le_of_mul_le_mul_right key h2

lemma norm_chiC_le_one (t : ZMod p) : ‖chiC p t‖ ≤ 1 := by
  by_cases ht : t = 0
  · rw [ht, chiC_zero, norm_zero]; exact zero_le_one
  · rw [norm_chiC ht]

/-- **The law of total expectation** for `E_μ[· | y_{U∖j}]`. -/
lemma sum_condE_erase (μ : (V → ZMod p) → ℝ) (hμ0 : ∀ x, 0 ≤ μ x) (hμ1 : ∑ x, μ x = 1)
    (j : V) (F : (V → ZMod p) → ℂ) :
    ∑ x, (μ x : ℂ) * condE μ (univ.erase j) F x = ∑ x, (μ x : ℂ) * F x := by
  have hA : ∀ (H : (V → ZMod p) → ℂ) (x : V → ZMod p),
      condE μ ∅ H x = ∑ x', (μ x' : ℂ) * H x' := by
    intro H x
    have hag : ∀ x', agree (∅ : Finset V) x x' := fun x' i hi => absurd hi (Finset.notMem_empty i)
    unfold condE cmass
    simp only [hag, ↓reduceIte, hμ1, Complex.ofReal_one, div_one]
  have h := condE_tower μ hμ0 (empty_subset (univ.erase j)) F (fun _ => 0)
  rw [hA, hA] at h
  exact h

/-- Under the graph law, the conditional law of `y_v` given the other labels is uniform on the
admissible set (`lem:graphs:vertex`(dens)): `update y v t ∈ Inj ↔ t ∈ 𝒜(y)`. -/
lemma update_mem_inj_iff (G : Labellings.OrientedGraph V) {v : V} {y : V → ZMod p}
    (hy : y ∈ Labellings.injLabellings (ZMod p) G) (t : ZMod p) :
    Function.update y v t ∈ Labellings.injLabellings (ZMod p) G ↔
      t ∈ Labellings.vertexAdmissible G (univ.erase v) y v := by
  classical
  have hfe : Labellings.Feasible (ZMod p) G (univ.erase v) y :=
    feasible_mono (subset_univ _) ((Cuts.SpecData.mem_inj G y).mp hy)
  constructor
  · intro h
    have hf := (Cuts.SpecData.mem_inj G _).mp h
    simp only [Labellings.vertexAdmissible, mem_filter, mem_univ, true_and, mem_image,
      not_exists, not_and]
    refine ⟨fun w hw hwt => ?_, fun w hw he => ?_, fun w hw he => ?_⟩
    · have hwv : w ≠ v := ne_of_mem_erase hw
      have h1 : Function.update y v t w = Function.update y v t v := by
        rw [Function.update_of_ne hwv, Function.update_self, hwt]
      exact hwv (hf.1 w (mem_univ _) v (mem_univ _) h1)
    · have hwv : w ≠ v := ne_of_mem_erase hw
      have h1 := hf.2 (w, v) he (mem_univ _) (mem_univ _)
      simp only [Function.update_self, Function.update_of_ne hwv] at h1
      exact h1
    · have hwv : w ≠ v := ne_of_mem_erase hw
      have h1 := hf.2 (v, w) he (mem_univ _) (mem_univ _)
      simp only [Function.update_self, Function.update_of_ne hwv] at h1
      exact h1
  · intro hc
    have h1 := Labellings.feasible_insert hfe (fun h => (mem_erase.mp h).1 rfl) hc
    rw [insert_erase (mem_univ v)] at h1
    exact (Cuts.SpecData.mem_inj G _).mpr h1

/-- **The conditional expectation of `χ(y_v − y_u)`** given the labels off `v`, at `y ∈ Inj`:
the mean of `χ(a − y_u)` over the admissible set. -/
lemma condE_graph_erase (G : Labellings.OrientedGraph V)
    (hne : (Labellings.injLabellings (ZMod p) G).Nonempty) {u v : V} (huv : u ≠ v)
    {y : V → ZMod p} (hy : y ∈ Labellings.injLabellings (ZMod p) G) :
    condE (graphWeight G hne) (univ.erase v) (fun x => chiC p (x v - x u)) y =
      ((∑ c ∈ Labellings.vertexAdmissible G (univ.erase v) y v,
          quadraticChar (ZMod p) (c - y u) : ℤ) : ℂ) /
        ((Labellings.vertexAdmissible G (univ.erase v) y v).card : ℂ) := by
  classical
  set Inj := Labellings.injLabellings (ZMod p) G with hInj
  set Adm := Labellings.vertexAdmissible G (univ.erase v) y v with hAdm
  have hI : (Inj.card : ℝ) ≠ 0 := by exact_mod_cast (card_pos.mpr hne).ne'
  have hw : ∀ t, graphWeight G hne (Function.update y v t) =
      if t ∈ Adm then 1 / (Inj.card : ℝ) else 0 := by
    intro t
    have e : graphWeight G hne (Function.update y v t) =
        if Function.update y v t ∈ Inj then 1 / (Inj.card : ℝ) else 0 := rfl
    rw [e]
    by_cases h : t ∈ Adm
    · rw [ite_eq_left_of_eq_true _ _ (eq_true ((update_mem_inj_iff G hy t).mpr h)),
        ite_eq_left_of_eq_true _ _ (eq_true h)]
    · rw [ite_eq_right_of_eq_false _ _ (eq_false (fun h' => h ((update_mem_inj_iff G hy t).mp h'))),
        ite_eq_right_of_eq_false _ _ (eq_false h)]
  unfold condE
  rw [sum_agree_erase v y (fun x' => ((graphWeight G hne x' : ℝ) : ℂ) * chiC p (x' v - x' u)),
    cmass_erase]
  have hnum : ∑ t, ((graphWeight G hne (Function.update y v t) : ℝ) : ℂ) *
      chiC p (Function.update y v t v - Function.update y v t u) =
      (1 / (Inj.card : ℂ)) * ((∑ c ∈ Adm, quadraticChar (ZMod p) (c - y u) : ℤ) : ℂ) := by
    simp only [Function.update_self, Function.update_of_ne huv, hw]
    have e1 : ∀ x, (((if x ∈ Adm then 1 / (Inj.card : ℝ) else 0 : ℝ)) : ℂ) * chiC p (x - y u) =
        if x ∈ Adm then (1 / (Inj.card : ℂ)) * ((quadraticChar (ZMod p) (x - y u) : ℤ) : ℂ)
          else 0 := by
      intro x
      split_ifs
      · simp only [chiC, MulChar.ringHomComp_apply, eq_intCast]
        push_cast
        ring
      · simp
    rw [sum_congr rfl fun x _ => e1 x, ← sum_filter, filter_mem_eq_inter, univ_inter, ← mul_sum]
    push_cast
    rfl
  have hdenom : ∑ t, graphWeight G hne (Function.update y v t) = (Adm.card : ℝ) / Inj.card := by
    simp only [hw]
    rw [← sum_filter, filter_mem_eq_inter, univ_inter, sum_const, nsmul_eq_mul]
    ring
  have hA0 : (Adm.card : ℂ) ≠ 0 := by
    have hmem : y v ∈ Adm :=
      (update_mem_inj_iff G hy (y v)).mp (by rw [Function.update_eq_self]; exact hy)
    exact_mod_cast (card_pos.mpr ⟨_, hmem⟩).ne'
  have hIC : (Inj.card : ℂ) ≠ 0 := by exact_mod_cast hI
  rw [hnum, hdenom]
  push_cast
  field_simp

/-- **The pair correlation of a graph law** (the core of `lem:spec:small`): for distinct
non-adjacent `u, v`, `|E_λ χ(y_v − y_u)| ≤ δ_v = (e_{d_v} + e_{d_v+1})/(1 − e_{d_v})`. -/
theorem graph_pair_corr (hW : Labellings.WeilBound (ZMod p)) (G : Labellings.OrientedGraph V)
    (hne : (Labellings.injLabellings (ZMod p) G).Nonempty) {u v : V} (huv : u ≠ v)
    (huv' : (u, v) ∉ G.E) (hvu : (v, u) ∉ G.E)
    (he : TraceMixing.coarseErr p (Labellings.nbrCount G (univ.erase v) v)
      (Fintype.card V) < 1) :
    ‖∑ y, (graphWeight G hne y : ℂ) * chiC p (y v - y u)‖ ≤
      smallConst p (Labellings.nbrCount G (univ.erase v) v) (Fintype.card V) := by
  classical
  have hμ0 := graphWeight_nonneg G hne
  have hμ1 := graphWeight_total G hne
  rw [← sum_condE_erase (graphWeight G hne) hμ0 hμ1 v (fun x => chiC p (x v - x u))]
  set δ := smallConst p (Labellings.nbrCount G (univ.erase v) v) (Fintype.card V) with hδ
  have hb : ∀ y, ‖(graphWeight G hne y : ℂ) *
      condE (graphWeight G hne) (univ.erase v) (fun x => chiC p (x v - x u)) y‖ ≤
        graphWeight G hne y * δ := by
    intro y
    by_cases hy : y ∈ Labellings.injLabellings (ZMod p) G
    · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hμ0 y), condE_graph_erase G hne huv hy]
      refine mul_le_mul_of_nonneg_left ?_ (hμ0 y)
      have hfe : Labellings.Feasible (ZMod p) G (univ.erase v) y :=
        feasible_mono (subset_univ _) ((Cuts.SpecData.mem_inj G y).mp hy)
      have hmem : y v ∈ Labellings.vertexAdmissible G (univ.erase v) y v :=
        (update_mem_inj_iff G hy (y v)).mp (by rw [Function.update_eq_self]; exact hy)
      have hpos : (0 : ℝ) < (Labellings.vertexAdmissible G (univ.erase v) y v).card := by
        exact_mod_cast card_pos.mpr ⟨_, hmem⟩
      rw [norm_div, Complex.norm_natCast, Complex.norm_intCast, div_le_iff₀ hpos]
      exact sum_chi_adm_le hW G huv huv' hvu hfe he
    · have h0 : graphWeight G hne y = 0 := by
        have e : graphWeight G hne y = if y ∈ Labellings.injLabellings (ZMod p) G then
            1 / ((Labellings.injLabellings (ZMod p) G).card : ℝ) else 0 := rfl
        rw [e, ite_eq_right_of_eq_false _ _ (eq_false hy)]
      rw [h0]
      simp
  calc ‖∑ y, (graphWeight G hne y : ℂ) *
        condE (graphWeight G hne) (univ.erase v) (fun x => chiC p (x v - x u)) y‖
      ≤ ∑ y, ‖(graphWeight G hne y : ℂ) *
          condE (graphWeight G hne) (univ.erase v) (fun x => chiC p (x v - x u)) y‖ :=
        norm_sum_le _ _
    _ ≤ ∑ y, graphWeight G hne y * δ := sum_le_sum fun y _ => hb y
    _ = δ := by rw [← sum_mul, hμ1, one_mul]

variable {W : Type*} [Fintype W] [DecidableEq W] (D : Cuts.SpecData W)

/-- `|Δ^μ_kl| ≤ 1` for a probability `μ`. -/
lemma norm_deltaMu_le_one (μ : (D.cut.Half → ZMod p) → ℝ) (hμ0 : ∀ x, 0 ≤ μ x)
    (hμ1 : ∑ x, μ x = 1) (k l : D.cut.Half) : ‖deltaMu μ k l‖ ≤ 1 := by
  unfold deltaMu
  split_ifs
  · rw [norm_zero]; exact zero_le_one
  · calc ‖∑ x, (μ x : ℂ) * chiC p (x l - x k)‖ ≤ ∑ x, ‖(μ x : ℂ) * chiC p (x l - x k)‖ :=
          norm_sum_le _ _
      _ ≤ ∑ x, μ x := sum_le_sum fun x _ => by
          rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (hμ0 x)]
          calc μ x * ‖chiC p (x l - x k)‖ ≤ μ x * 1 :=
                mul_le_mul_of_nonneg_left (norm_chiC_le_one _) (hμ0 x)
            _ = μ x := mul_one _
      _ = 1 := hμ1

/-- `|Δ^μ_kl| = |Δ^μ_lk|` (`χ(x_k − x_l) = χ(−1)χ(x_l − x_k)`). -/
lemma norm_deltaMu_swap (μ : (D.cut.Half → ZMod p) → ℝ) (k l : D.cut.Half) :
    ‖deltaMu μ l k‖ = ‖deltaMu μ k l‖ := by
  unfold deltaMu
  by_cases hkl : k = l
  · subst hkl; rfl
  · have hlk : l ≠ k := fun h => hkl h.symm
    simp only [hkl, hlk, ↓reduceIte]
    have e : ∀ x : D.cut.Half → ZMod p, (μ x : ℂ) * chiC p (x k - x l) =
        chiC p (-1) * ((μ x : ℂ) * chiC p (x l - x k)) := by
      intro x
      rw [show x k - x l = -1 * (x l - x k) by ring, map_mul]
      ring
    rw [sum_congr rfl fun x _ => e x, ← mul_sum, norm_mul, norm_chiC (by
      intro h; exact one_ne_zero (neg_eq_zero.mp h)), one_mul]

/-- **`lem:spec:small`(b)** for the half law `μ = λ_p(G⁺)`: for distinct non-adjacent `k, l`,
`|Δ^μ_kl| ≤ δ^μ_l = (e_{d⁰_l} + e_{d⁰_l+1})/(1 − e_{d⁰_l})`, `e_t = e_t(p, |U⁺|)`. -/
theorem deltaMu_small (hW : Labellings.WeilBound (ZMod p))
    (hne : (Labellings.injLabellings (ZMod p) D.G).Nonempty) {k l : D.cut.Half} (hkl : k ≠ l)
    (h1 : (k, l) ∉ D.halfGraph.E) (h2 : (l, k) ∉ D.halfGraph.E)
    (he : TraceMixing.coarseErr p (Labellings.nbrCount D.halfGraph (univ.erase l) l)
      (Fintype.card D.cut.Half) < 1) :
    ‖deltaMu (D.halfLaw hne).weight k l‖ ≤
      smallConst p (Labellings.nbrCount D.halfGraph (univ.erase l) l)
        (Fintype.card D.cut.Half) := by
  unfold deltaMu
  simp only [hkl, ↓reduceIte]
  exact graph_pair_corr hW D.halfGraph (D.half_nonempty hne) hkl h1 h2 he

/-- **`lem:spec:small`(b)**, both bounds: `|Δ^μ_kl| ≤ min(δ^μ_k, δ^μ_l)`. -/
theorem deltaMu_small_min (hW : Labellings.WeilBound (ZMod p))
    (hne : (Labellings.injLabellings (ZMod p) D.G).Nonempty) {k l : D.cut.Half} (hkl : k ≠ l)
    (h1 : (k, l) ∉ D.halfGraph.E) (h2 : (l, k) ∉ D.halfGraph.E)
    (hek : TraceMixing.coarseErr p (Labellings.nbrCount D.halfGraph (univ.erase k) k)
      (Fintype.card D.cut.Half) < 1)
    (hel : TraceMixing.coarseErr p (Labellings.nbrCount D.halfGraph (univ.erase l) l)
      (Fintype.card D.cut.Half) < 1) :
    ‖deltaMu (D.halfLaw hne).weight k l‖ ≤
      min (smallConst p (Labellings.nbrCount D.halfGraph (univ.erase k) k)
          (Fintype.card D.cut.Half))
        (smallConst p (Labellings.nbrCount D.halfGraph (univ.erase l) l)
          (Fintype.card D.cut.Half)) := by
  refine le_min ?_ (deltaMu_small D hW hne hkl h1 h2 hel)
  rw [← norm_deltaMu_swap D]
  exact deltaMu_small D hW hne (fun h => hkl h.symm) h2 h1 hek

end Sarkozy.SpectralD.Cx
