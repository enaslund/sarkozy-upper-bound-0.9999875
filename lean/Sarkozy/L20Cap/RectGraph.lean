module

public import Sarkozy.L20Cap.RectNonstar
public import Sarkozy.Labellings.GraphAutomorphism

/-!
# The half law is X1's graph law of `G_{F,2}` (`prop:l20-rectangular`(b), the bridge)

`G6` is the half graph `G_{F,2}` of L20 on the six coordinates `(a₀, a₁, b₀, b₁, c₀, c₁)`: the
four edges `a_i → c_j`. Notation of `Sarkozy.L20Cap.RectNonstar`.

* `labels_mem`: `labels x ∈ Inj_p(G6)` iff the pair of `x` avoids its core;
* `sum_injLabellings`: the labellings of `G6` are exactly the `labels x`, `x` admissible
  (`toHalf`, a bijection);
* **`graphLaw_eq_halfLaw`**: `E_{λ_p(G6)}[Φ] = E_{μ_p}[Φ ∘ labels]` (X1's `graphLaw` is `μ_p`);
* **`hN_of_X1`**: X1's form of `cor:soft-kernels`(a) for the eight-edge nonstar class sum `K6` on
  `λ_p(G6)` (the conclusion of `sk_soft_extraction_leaf_*`, summed over a partition of
  `nonstars Ex8` into classes) gives the hypothesis `hN` of `l20_prime_caps_full`.
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace Sarkozy.L20Cap

open Sarkozy Sarkozy.Recentering Sarkozy.Cuts Sarkozy.Labellings Sarkozy.Extraction
  Sarkozy.ExtractionK

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- **The half graph `G_{F,2}` of L20** on `(a₀, a₁, b₀, b₁, c₀, c₁)`: the edges `a_i → c_j`. -/
def G6 : OrientedGraph (Fin 6) where
  E := {(0, 4), (0, 5), (1, 4), (1, 5)}
  loopless := by decide
  oriented := by decide

theorem labels_apply (x : CoreT F × PairT F) :
    labels x 0 = x.1.1 0 ∧ labels x 1 = x.1.1 1 ∧ labels x 2 = x.2.1.1 ∧ labels x 3 = x.2.1.2 ∧
      labels x 4 = x.1.1 2 ∧ labels x 5 = x.1.1 3 := by
  simp [labels, emb]

/-- `labels x` is a labelling of `G6` iff the pair of `x` avoids its core. -/
theorem labels_mem (x : CoreT F × PairT F) : labels x ∈ injLabellings F G6 ↔ Avoid x := by
  obtain ⟨⟨C, hC⟩, ⟨b, hb⟩⟩ := x
  obtain ⟨hinj, h20, h30, h21, h31⟩ := hC
  rw [mem_injLabellings_iff_feasible]
  have n01 : C 0 ≠ C 1 := hinj.ne (by decide)
  have n02 : C 0 ≠ C 2 := hinj.ne (by decide)
  have n03 : C 0 ≠ C 3 := hinj.ne (by decide)
  have n12 : C 1 ≠ C 2 := hinj.ne (by decide)
  have n13 : C 1 ≠ C 3 := hinj.ne (by decide)
  have n23 : C 2 ≠ C 3 := hinj.ne (by decide)
  constructor
  · rintro ⟨hz, -⟩
    refine ⟨fun k hk => ?_, fun k hk => ?_⟩
    · fin_cases k
      · exact absurd (hz 2 (mem_univ _) 0 (mem_univ _) (by simpa [labels, emb] using hk))
          (by decide)
      · exact absurd (hz 2 (mem_univ _) 1 (mem_univ _) (by simpa [labels, emb] using hk))
          (by decide)
      · exact absurd (hz 2 (mem_univ _) 4 (mem_univ _) (by simpa [labels, emb] using hk))
          (by decide)
      · exact absurd (hz 2 (mem_univ _) 5 (mem_univ _) (by simpa [labels, emb] using hk))
          (by decide)
    · fin_cases k
      · exact absurd (hz 3 (mem_univ _) 0 (mem_univ _) (by simpa [labels, emb] using hk))
          (by decide)
      · exact absurd (hz 3 (mem_univ _) 1 (mem_univ _) (by simpa [labels, emb] using hk))
          (by decide)
      · exact absurd (hz 3 (mem_univ _) 4 (mem_univ _) (by simpa [labels, emb] using hk))
          (by decide)
      · exact absurd (hz 3 (mem_univ _) 5 (mem_univ _) (by simpa [labels, emb] using hk))
          (by decide)
  · rintro ⟨ha, hb'⟩
    have a0 := ha 0
    have a1 := ha 1
    have a2 := ha 2
    have a3 := ha 3
    have b0 := hb' 0
    have b1 := hb' 1
    have b2 := hb' 2
    have b3 := hb' 3
    simp only at a0 a1 a2 a3 b0 b1 b2 b3 hb
    refine ⟨fun u _ v _ huv => ?_, fun e he _ _ => ?_⟩
    · fin_cases u <;> fin_cases v <;>
        simp [labels, emb] at huv ⊢ <;>
        first
        | exact absurd huv n01 | exact absurd huv n02 | exact absurd huv n03
        | exact absurd huv n12 | exact absurd huv n13 | exact absurd huv n23
        | exact absurd huv.symm n01 | exact absurd huv.symm n02 | exact absurd huv.symm n03
        | exact absurd huv.symm n12 | exact absurd huv.symm n13 | exact absurd huv.symm n23
        | exact absurd huv hb | exact absurd huv.symm hb
        | exact absurd huv a0 | exact absurd huv a1 | exact absurd huv a2 | exact absurd huv a3
        | exact absurd huv b0 | exact absurd huv b1 | exact absurd huv b2 | exact absurd huv b3
        | exact absurd huv.symm a0 | exact absurd huv.symm a1 | exact absurd huv.symm a2
        | exact absurd huv.symm a3 | exact absurd huv.symm b0 | exact absurd huv.symm b1
        | exact absurd huv.symm b2 | exact absurd huv.symm b3
    · simp only [G6, mem_insert, mem_singleton] at he
      rcases he with rfl | rfl | rfl | rfl <;> simp [labels, emb, h20, h30, h21, h31]

/-- The half with labels `z`, for `z ∈ Inj_p(G6)`. -/
def toHalf (z : Fin 6 → F) (hz : z ∈ injLabellings F G6) : CoreT F × PairT F :=
  (⟨![z 0, z 1, z 4, z 5], by
      rw [mem_injLabellings_iff_feasible] at hz
      obtain ⟨hinj, hedge⟩ := hz
      have e04 := hedge (0, 4) (by simp [G6]) (mem_univ _) (mem_univ _)
      have e05 := hedge (0, 5) (by simp [G6]) (mem_univ _) (mem_univ _)
      have e14 := hedge (1, 4) (by simp [G6]) (mem_univ _) (mem_univ _)
      have e15 := hedge (1, 5) (by simp [G6]) (mem_univ _) (mem_univ _)
      refine ⟨?_, by simpa using e04, by simpa using e05, by simpa using e14, by simpa using e15⟩
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;>
        first
        | exact absurd (hinj _ (mem_univ _) _ (mem_univ _) hij) (by decide)⟩,
    ⟨(z 2, z 3), by
      rw [mem_injLabellings_iff_feasible] at hz
      intro h
      exact absurd (hz.1 2 (mem_univ _) 3 (mem_univ _) h) (by decide)⟩)

theorem labels_toHalf (z : Fin 6 → F) (hz : z ∈ injLabellings F G6) : labels (toHalf z hz) = z := by
  funext i
  fin_cases i <;> rfl

theorem toHalf_labels (x : CoreT F × PairT F) (hx : labels x ∈ injLabellings F G6) :
    toHalf (labels x) hx = x := by
  obtain ⟨⟨C, hC⟩, ⟨b, hb⟩⟩ := x
  simp only [toHalf, labels, emb, Prod.mk.injEq]
  refine ⟨?_, ?_⟩
  · apply Subtype.ext
    funext k
    fin_cases k <;> rfl
  · rfl

noncomputable instance : DecidablePred (fun z : Fin 6 → F => z ∈ injLabellings F G6) := fun _ =>
  Finset.decidableMem _ _

/-- The labellings of `G6` are the `labels x` of the admissible halves. -/
theorem sum_injLabellings (Φ : (Fin 6 → F) → ℝ) :
    ∑ z ∈ injLabellings F G6, Φ z = ∑ x ∈ univ.filter (Avoid (F := F)), Φ (labels x) := by
  symm
  refine Finset.sum_bij' (fun x _ => labels x) (fun z hz => toHalf z hz) ?_ ?_ ?_ ?_ ?_
  · intro x hx
    exact (labels_mem x).mpr (mem_filter.mp hx).2
  · intro z hz
    refine mem_filter.mpr ⟨mem_univ _, ?_⟩
    have := (labels_mem (toHalf z hz)).mp (by rw [labels_toHalf]; exact hz)
    exact this
  · intro x hx
    exact toHalf_labels x _
  · intro z hz
    exact labels_toHalf z hz
  · intro x _
    rfl

variable [Nonempty (CoreT F)] [Nonempty (PairT F)]

theorem halfLaw_weight_off (h6 : 6 ≤ Fintype.card F) {x : CoreT F × PairT F} (hx : ¬ Avoid x) :
    (halfLaw h6).weight x = 0 := by
  rw [halfLaw_weight]
  simp only [hx, ↓reduceIte]

/-- Expectations under `μ_p` only see the admissible halves. -/
theorem halfLaw_expect_congr (h6 : 6 ≤ Fintype.card F) {f g : CoreT F × PairT F → ℝ}
    (hfg : ∀ x, Avoid x → f x = g x) : (halfLaw h6).expect f = (halfLaw h6).expect g := by
  unfold FiniteLaw.expect
  refine sum_congr rfl fun x _ => ?_
  by_cases hx : Avoid x
  · rw [hfg x hx]
  · rw [halfLaw_weight_off h6 hx, zero_mul, zero_mul]

/-- **X1's graph law of `G6` is the half law `μ_p`**: `E_{λ_p(G6)}[Φ] = E_{μ_p}[Φ ∘ labels]`. -/
theorem graphLaw_eq_halfLaw (h6 : 6 ≤ Fintype.card F) (hne : (injLabellings F G6).Nonempty)
    (Φ : (Fin 6 → F) → ℝ) :
    (graphLaw G6 hne).expect Φ = (halfLaw h6).expect (fun x => Φ (labels x)) := by
  -- `μ_p` is uniform on the admissible halves
  set c := ((Fintype.card (CoreT F) : ℝ) * (((Fintype.card F : ℝ) - 4) * (Fintype.card F - 5)))⁻¹
    with hc
  have hw : ∀ x, (halfLaw h6).weight x = if Avoid x then c else 0 := fun x => halfLaw_weight h6 x
  have htot : c * ((univ.filter (Avoid (F := F))).card : ℝ) = 1 := by
    have := (halfLaw h6).total
    rw [sum_congr rfl fun x _ => hw x, sum_ite, sum_const_zero, add_zero, sum_const,
      nsmul_eq_mul] at this
    linarith
  have hcard : (injLabellings F G6).card = (univ.filter (Avoid (F := F))).card := by
    have := sum_injLabellings (F := F) (fun _ => (1 : ℝ))
    simp only [sum_const, nsmul_eq_mul, mul_one] at this
    exact_mod_cast this
  unfold FiniteLaw.expect graphLaw
  simp only
  have e1 : ∑ z, (if z ∈ injLabellings F G6 then 1 / ((injLabellings F G6).card : ℝ) else 0) * Φ z =
      (1 / ((injLabellings F G6).card : ℝ)) * ∑ z ∈ injLabellings F G6, Φ z := by
    rw [mul_sum, ← sum_filter_add_sum_filter_not univ (fun z => z ∈ injLabellings F G6)]
    rw [filter_mem_eq_inter, univ_inter]
    have h0 : ∑ z ∈ univ.filter (fun z => z ∉ injLabellings F G6),
        (if z ∈ injLabellings F G6 then 1 / ((injLabellings F G6).card : ℝ) else 0) * Φ z = 0 :=
      sum_eq_zero fun z hz => by
        simp only [mem_filter] at hz
        simp [hz.2]
    rw [h0, add_zero]
    exact sum_congr rfl fun z hz => by simp [hz]
  have e2 : ∑ x, (halfLaw h6).weight x * Φ (labels x) =
      c * ∑ x ∈ univ.filter (Avoid (F := F)), Φ (labels x) := by
    rw [mul_sum, sum_filter]
    exact sum_congr rfl fun x _ => by rw [hw x]; split_ifs <;> ring
  rw [e1, e2, sum_injLabellings, hcard]
  have hpos : (0 : ℝ) < (univ.filter (Avoid (F := F))).card := by
    have := htot
    by_contra hle
    push Not at hle
    have h0 : ((univ.filter (Avoid (F := F))).card : ℝ) = 0 := le_antisymm hle (Nat.cast_nonneg _)
    rw [h0, mul_zero] at this
    exact zero_ne_one this
  have hc' : c = 1 / ((univ.filter (Avoid (F := F))).card : ℝ) := by
    field_simp
    linarith
  rw [hc']

/-- The eight-edge nonstar class sum of X1 at two labellings. -/
noncomputable def K6 (z z' : Fin 6 → F) : ℝ :=
  ∑ S ∈ nonstars Ex8, ∏ e ∈ S, ((1 : ℝ) * chiPair D20Z e z z')

/-- **`prop:l20-rectangular`(b), the bridge to X1** (`cor:soft-kernels`(a)): a bound
`|⟨φ, K₆h⟩_{λ_p(G6)}| ≤ N_A‖φ‖‖h‖` for X1's soft nonstar class sum of the eight cross pairs on
the graph law of `G6` (the form of X1's `sk_soft_extraction_leaf_*`, summed over a partition of
`nonstars Ex8`) gives the hypothesis `hN` of `l20_prime_caps_full`. -/
theorem hN_of_X1 (hm1 : quadraticChar F (-1) = -1) (h6 : 6 ≤ Fintype.card F)
    (hne : (injLabellings F G6).Nonempty) {NA : ℝ} (hNA : 0 ≤ NA)
    (hX1 : ∀ φ h : (Fin 6 → F) → ℝ,
      |(graphLaw G6 hne).expect (fun z => φ z * (graphLaw G6 hne).expect (fun z' =>
          K6 z z' * h z'))| ≤
        NA * Real.sqrt ((graphLaw G6 hne).expect (fun z => φ z ^ 2)) *
          Real.sqrt ((graphLaw G6 hne).expect (fun z => h z ^ 2)))
    (g : PairT F → ℝ) :
    nrm (coreLaw (F := F)) (fun C => (pairLaw (F := F)).expect (fun b => Nrect C b * g b)) ≤
      NA * nrm (pairLaw (F := F)) g := by
  refine hN_of_half hm1 h6 hNA (fun φ' h' => ?_) g
  -- transport `φ'`, `h'` to the labellings
  set φ : (Fin 6 → F) → ℝ := fun z => if hz : z ∈ injLabellings F G6 then φ' (toHalf z hz) else 0
    with hφ
  set h : (Fin 6 → F) → ℝ := fun z => if hz : z ∈ injLabellings F G6 then h' (toHalf z hz) else 0
    with hh
  have hφl : ∀ x, Avoid x → φ (labels x) = φ' x := by
    intro x hx
    have hm := (labels_mem x).mpr hx
    simp only [hφ, hm, ↓reduceDIte, toHalf_labels]
  have hhl : ∀ x, Avoid x → h (labels x) = h' x := by
    intro x hx
    have hm := (labels_mem x).mpr hx
    simp only [hh, hm, ↓reduceDIte, toHalf_labels]
  have hX := hX1 φ h
  -- the form
  have hform : (graphLaw G6 hne).expect (fun z => φ z * (graphLaw G6 hne).expect (fun z' =>
      K6 z z' * h z')) = kernelForm (halfLaw h6) (halfLaw h6) NrectH φ' h' := by
    rw [kernelForm_apply, graphLaw_eq_halfLaw h6 hne]
    refine halfLaw_expect_congr h6 fun x hx => ?_
    rw [hφl x hx, graphLaw_eq_halfLaw h6 hne]
    congr 1
    refine halfLaw_expect_congr h6 fun x' hx' => ?_
    simp only [K6]
    rw [nonstar_eq_Nrect hm1 x x', hhl x' hx']
  have hnφ : Real.sqrt ((graphLaw G6 hne).expect (fun z => φ z ^ 2)) = nrm (halfLaw h6) φ' := by
    rw [graphLaw_eq_halfLaw h6 hne]
    unfold nrm ip
    congr 1
    refine halfLaw_expect_congr h6 fun x hx => ?_
    rw [hφl x hx, sq]
  have hnh : Real.sqrt ((graphLaw G6 hne).expect (fun z => h z ^ 2)) = nrm (halfLaw h6) h' := by
    rw [graphLaw_eq_halfLaw h6 hne]
    unfold nrm ip
    congr 1
    refine halfLaw_expect_congr h6 fun x hx => ?_
    rw [hhl x hx, sq]
  rw [hform, hnφ, hnh] at hX
  exact hX

end Sarkozy.L20Cap
