module

public import Sarkozy.F7Repair.CountsFine
public import Sarkozy.F7Repair.TailCrude
public import Sarkozy.F7Repair.Densities

@[expose] public section

/-!
# The one-way data of the tail records from Weil's bound (the density part of (F7))

At a tail prime `q ≥ 2⁵¹²`, for the new law `π^new = λ_q(G^new)` of a changed record and the old
half marginal `μ^old`, this file proves from H1 the density and `L^∞` inputs of (F7):

* `dens`: `|μ^old − π^new_j| ≤ U_q π^new_j` on both halves, `U_q = R_q^{144} − 1 ≤ 2⁹⁹/√q`
  (`fineU_le`);
* `sup`: `dπ^new/d(π^new_X ⊗ π^new_Y) ≤ K²` with `K_∞ = 2¹⁴⁴` (`tail_sup`), from the product
  bounds with the cross edges counted at most `|Q| ≤ 6` times per vertex;
* **`tailOneWay`**: the `OneWayData` of `π^new` with targets `μ^old`, `U = U_q`, `K = 2¹⁴⁴`,
  given only the centred correlation bound `ρ_new ≤ 1/2` of `π^new` (*hypothesis*, (F2));
* **`TailF7.ofCorr`**: the `TailF7` of a changed record from the two correlation bounds alone:
  `ρ_new ≤ 1/2` for `π^new` and `ρ_old` for the old record (*hypotheses*, (F2) and (F6)).

So the (F7) repair at the tail is proved from H1 up to the two correlation bounds; its constant is
`C = ρ_old + ρ'` with `ρ' = (ρ_new(1 + 2F) + U²)/(1 − U)`, `U ≤ 2⁹⁹ r`, `F ≤ U(1 + 2¹⁴⁵)`.
-/

open Finset
open scoped BigOperators

namespace Sarkozy.F7Repair

open Sarkozy.TheoremC Sarkozy.RecordExpansion Sarkozy.Mixing Sarkozy.PartV Sarkozy.PartVRecords
  Sarkozy.Labellings Sarkozy.UpperComparison Sarkozy.Recentering Sarkozy.Structured
  Sarkozy.TailPrices

variable {W : Type*} [Fintype W] [DecidableEq W]

omit [Fintype W] in
theorem upperProd_append (G : OrientedGraph W) (q : ℝ) :
    ∀ (l l' : List W) (A : Finset W),
      upperProd G q A (l ++ l') = upperProd G q A l * upperProd G q (A ∪ l.toFinset) l'
  | [], l', A => by simp [upperProd]
  | v :: l, l', A => by
      simp only [List.cons_append, upperProd]
      rw [upperProd_append G q l l' (insert v A), List.toFinset_cons, union_insert, insert_union]
      ring

/-- The upper count of all labellings splits along the two layers. -/
theorem card_inj_le_upper {F : Type*} [Field F] [Fintype F] [DecidableEq F] (hW : WeilBound F)
    (G : OrientedGraph W) (l l' : List W) (hnd : (l ++ l').Nodup) (hcov : ∀ w, w ∈ l ∨ w ∈ l') :
    ((injLabellings F G).card : ℝ) ≤ upperProd G (Fintype.card F) ∅ l *
      upperProd G (Fintype.card F) l.toFinset l' := by
  classical
  have hfeas : Feasible F G ∅ (fun _ => (0 : F)) := ⟨by simp, by simp⟩
  have h := (extCount_bounds hW G le_rfl (l ++ l') ∅ (fun _ => (0 : F)) hnd
    (fun w => Or.inr (List.mem_append.mpr (hcov w))) (by simp) hfeas).2
  have he : extCount G ∅ (fun _ => (0 : F)) = (injLabellings F G).card := by
    unfold extCount
    congr 1
    exact filter_true_of_mem fun _ _ => by simp
  rw [he, upperProd_append, empty_union] at h
  exact h

variable {q : ℕ} [Fact q.Prime]

/-- The glued two-layer labelling with halves `x`, `y`. -/
def glue {O₀ O₁ Z : Type*} (x y : O₀ × O₁ → Z) : O₀ × O₁ × Fin 2 → Z :=
  fun w => if w.2.2 = 0 then x (w.1, w.2.1) else y (w.1, w.2.1)

theorem eq_glue {O₀ O₁ Z : Type*} (y' : O₀ × O₁ × Fin 2 → Z) :
    y' = glue (layerOf y' 0) (layerOf y' 1) := by
  funext w
  unfold glue layerOf
  rcases w with ⟨a, b, k⟩
  fin_cases k <;> rfl

/-- The pair law of the two layers is the law at the glued labelling. -/
theorem pairLaw_weight_glue {O₀ O₁ Z : Type*} [Fintype O₀] [DecidableEq O₀] [Fintype O₁]
    [DecidableEq O₁] [Fintype Z] [DecidableEq Z] (lam : FiniteLaw (O₀ × O₁ × Fin 2 → Z))
    (x y : O₀ × O₁ → Z) : (pairLaw lam lay0 lay1).weight (x, y) = lam.weight (glue x y) := by
  change (∑ y', if (lay0 y', lay1 y') = (x, y) then lam.weight y' else 0) = _
  rw [Finset.sum_eq_single (glue x y)]
  · have : (lay0 (glue x y), lay1 (glue x y)) = (x, y) := by
      refine Prod.ext ?_ ?_ <;> funext o <;> simp [lay0, lay1, layerOf, glue]
    simp only [this, ↓reduceIte]
  · intro y' _ hy'
    have : ¬ (lay0 y', lay1 y') = (x, y) := by
      intro h
      apply hy'
      rw [eq_glue y']
      simp only [Prod.mk.injEq] at h
      rw [show layerOf y' 0 = x from h.1, show layerOf y' 1 = y from h.2]
    simp only [this, ↓reduceIte]
  · intro h
    exact absurd (mem_univ _) h

omit [Fintype W] [DecidableEq W] in
theorem feasible_congr {F : Type*} [Field F] [Fintype F] [DecidableEq F] (G : OrientedGraph W)
    (A : Finset W) {x x' : W → F} (hxx : ∀ a ∈ A, x a = x' a) (h : Feasible F G A x) :
    Feasible F G A x' := by
  refine ⟨fun a ha b hb hab => h.1 a ha b hb ?_, fun e he h1 h2 => ?_⟩
  · rw [hxx a ha, hxx b hb]
    exact hab
  · rw [← hxx _ h1, ← hxx _ h2]
    exact h.2 e he h1 h2

/-- Cross neighbours: a vertex of layer `0` of `G^new` has at most `|Q|` neighbours in layer `1`. -/
theorem nbrCount_cross_le (f₀ f₁ : FType) (Q : Finset ((f₀.Obj × f₁.Obj) × (f₀.Obj × f₁.Obj)))
    (S : Finset (f₀.Obj × f₁.Obj × Fin 2)) (v : f₀.Obj × f₁.Obj × Fin 2) (hv : v.2.2 = 0) :
    nbrCount (newGraph f₀ f₁ Q) (layerSet 1 ∪ S) v ≤ nbrCount (newGraph f₀ f₁ Q) S v + Q.card := by
  classical
  unfold nbrCount
  rw [filter_union]
  refine (card_union_le _ _).trans ?_
  rw [add_comm]
  refine Nat.add_le_add_left ?_ _
  refine (card_le_card ?_).trans (card_image_le (f := fun q' => (q'.2.1, q'.2.2, (1 : Fin 2))))
  intro u hu
  rw [mem_filter] at hu
  obtain ⟨hu1, hadj⟩ := hu
  have hu1' : u.2.2 = 1 := (mem_filter.mp hu1).2
  rw [mem_image]
  rcases hadj with h | h
  · rcases (mem_newEdges f₀ f₁ Q _).mp h with ⟨_, hl⟩ | ⟨q', _, hq'⟩
    · simp only at hl
      rw [hu1', hv] at hl
      exact absurd hl (by decide)
    · have b := (crossEdge_layers q').2
      rw [hq'] at b
      simp only at b
      rw [hv] at b
      exact absurd b (by decide)
  · rcases (mem_newEdges f₀ f₁ Q _).mp h with ⟨_, hl⟩ | ⟨q', hq'Q, hq'⟩
    · simp only at hl
      rw [hu1', hv] at hl
      exact absurd hl (by decide)
    · refine ⟨q', hq'Q, ?_⟩
      have := congrArg Prod.snd hq'
      simp only [crossEdge] at this
      exact this

theorem card_recQ_le (t : PType × PType) (φ : t.1.Pat × t.2.Pat) : (recQ t φ).card ≤ 6 := by
  unfold recQ queryPairs
  exact card_image_le.trans (by simp)

theorem card_layerSet_le (f₀ f₁ : FType) (k : Fin 2) :
    (layerSet k : Finset (f₀.Obj × f₁.Obj × Fin 2)).card ≤ 36 := by
  classical
  have h : (layerSet k : Finset (f₀.Obj × f₁.Obj × Fin 2)).card ≤
      Fintype.card (f₀.Obj × f₁.Obj) := by
    refine card_le_card_of_injOn (fun w => (w.1, w.2.1)) (fun _ _ => mem_univ _) ?_
    intro a ha b hb hab
    have ha' : a.2.2 = k := (mem_filter.mp ha).2
    have hb' : b.2.2 = k := (mem_filter.mp hb).2
    simp only [Prod.mk.injEq] at hab
    exact Prod.ext hab.1 (Prod.ext hab.2 (ha'.trans hb'.symm))
  refine h.trans ?_
  rw [Fintype.card_prod]
  exact (Nat.mul_le_mul (PartVLaws.card_obj_le f₀) (PartVLaws.card_obj_le f₁)).trans (by norm_num)

/-- **The `L^∞` bound of the tail new law**: `π^new(x, y) ≤ (2¹⁴⁴)² π^new_X(x) π^new_Y(y)`. -/
theorem tail_sup (hW : Target.Weil) (h4 : P4 ≤ q) (t : PType × PType) (φ : t.1.Pat × t.2.Pat)
    (x y : t.1.field.Obj × t.2.field.Obj → ZMod q) :
    (pairLaw (crudeLam hW h4 t φ) lay0 lay1).weight (x, y) ≤
      ((2 : ℝ) ^ 144) ^ 2 * mX (pairLaw (crudeLam hW h4 t φ) lay0 lay1) x *
        mY (pairLaw (crudeLam hW h4 t φ) lay0 lay1) y := by
  classical
  set N := newGraph t.1.field t.2.field (recQ t φ)
  have hWeil := weilBound_of_target hW q (ne_two_of_P4 q h4)
  have hq := card_zmod_large h4
  have hcard := card_two_le t.1.field t.2.field
  set Q : ℝ := ((Fintype.card (ZMod q) : ℕ) : ℝ)
  set n := Fintype.card (t.1.field.Obj × t.2.field.Obj × Fin 2)
  set A₀ : Finset (t.1.field.Obj × t.2.field.Obj × Fin 2) := layerSet 0
  set A₁ : Finset (t.1.field.Obj × t.2.field.Obj × Fin 2) := layerSet 1
  set l₀ := A₀.toList
  set l₁ := A₁.toList
  have hlay : ∀ w : t.1.field.Obj × t.2.field.Obj × Fin 2, w.2.2 = 0 ∨ w.2.2 = 1 := by
    intro w
    rcases w with ⟨a, b, k⟩
    fin_cases k <;> simp
  have mem0 : ∀ w, w ∈ A₀ ↔ w.2.2 = 0 := fun w => by simp [A₀, layerSet]
  have mem1 : ∀ w, w ∈ A₁ ↔ w.2.2 = 1 := fun w => by simp [A₁, layerSet]
  have hnd : (l₀ ++ l₁).Nodup := by
    refine List.nodup_append.mpr ⟨nodup_toList _, nodup_toList _, ?_⟩
    intro a ha b hb hab
    rw [mem_toList, mem0] at ha
    rw [mem_toList, mem1] at hb
    rw [hab, hb] at ha
    exact absurd ha (by decide)
  have hcov : ∀ w, w ∈ l₀ ∨ w ∈ l₁ := by
    intro w
    rcases hlay w with h | h
    · exact Or.inl (mem_toList.mpr ((mem0 w).mpr h))
    · exact Or.inr (mem_toList.mpr ((mem1 w).mpr h))
  have hI := card_inj_le_upper hWeil N l₀ l₁ hnd hcov
  rw [show l₀.toFinset = A₀ from toList_toFinset _] at hI
  -- the two products
  have hD : ∀ S : Finset (t.1.field.Obj × t.2.field.Obj × Fin 2), ∀ v ∈ l₀,
      nbrCount N (A₁ ∪ S) v ≤ nbrCount N (∅ ∪ S) v + 6 := by
    intro S v hv
    rw [empty_union]
    have hv0 : v.2.2 = 0 := (mem0 v).mp (mem_toList.mp hv)
    exact (nbrCount_cross_le _ _ _ S v hv0).trans (Nat.add_le_add_left (card_recQ_le t φ) _)
  obtain ⟨hU₀, hL₁pos⟩ := prod_fine N hq le_rfl hcard 6 l₀ ∅ A₁ (empty_subset _) hD
  obtain ⟨hU₁, hL₀pos⟩ := prod_fine N hq le_rfl hcard 0 l₁ A₀ A₀ subset_rfl
    (fun _ _ _ => le_rfl)
  simp only [pow_zero, mul_one] at hU₁
  set L₁ := lowerProd N Q n A₁ l₀
  set L₀ := lowerProd N Q n A₀ l₁
  have hm₀ : l₀.length ≤ 36 := by rw [length_toList]; exact card_layerSet_le _ _ 0
  have hm₁ : l₁.length ≤ 36 := by rw [length_toList]; exact card_layerSet_le _ _ 1
  have hR1 := fineR_ge_one Q
  have hR2 := fineR_le_two hq
  have hK1 : (fineR Q * 2 ^ 6) ^ l₀.length ≤ 2 ^ 252 := by
    calc (fineR Q * 2 ^ 6) ^ l₀.length ≤ (2 * 2 ^ 6) ^ l₀.length :=
          pow_le_pow_left₀ (by positivity) (by nlinarith) _
      _ ≤ (2 * 2 ^ 6) ^ 36 := pow_le_pow_right₀ (by norm_num) hm₀
      _ = 2 ^ 252 := by norm_num
  have hK2 : fineR Q ^ l₁.length ≤ 2 ^ 36 :=
    (pow_le_pow_left₀ (by linarith) hR2 _).trans (pow_le_pow_right₀ (by norm_num) hm₁)
  have hInj : ((injLabellings (ZMod q) N).card : ℝ) ≤ ((2 : ℝ) ^ 144) ^ 2 * L₀ * L₁ := by
    have hu0 := upperProd_nonneg N (Nat.cast_nonneg _ : (0 : ℝ) ≤ Q) l₀ ∅
    calc ((injLabellings (ZMod q) N).card : ℝ)
        ≤ upperProd N Q ∅ l₀ * upperProd N Q A₀ l₁ := hI
      _ ≤ ((fineR Q * 2 ^ 6) ^ l₀.length * L₁) * (fineR Q ^ l₁.length * L₀) :=
          mul_le_mul hU₀ hU₁ (upperProd_nonneg N (Nat.cast_nonneg _) l₁ A₀)
            (by positivity)
      _ ≤ (2 ^ 252 * L₁) * (2 ^ 36 * L₀) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hK1 hL₁pos.le)
            (mul_le_mul_of_nonneg_right hK2 hL₀pos.le) (by positivity) (by positivity)
      _ = ((2 : ℝ) ^ 144) ^ 2 * L₀ * L₁ := by ring
  -- the pair weight and the marginals
  have hIpos : (0 : ℝ) < (injLabellings (ZMod q) N).card := by
    exact_mod_cast card_pos.mpr (recN hW h4 t φ)
  rw [pairLaw_weight_glue]
  change (if glue x y ∈ injLabellings (ZMod q) N then
    1 / ((injLabellings (ZMod q) N).card : ℝ) else 0) ≤ _
  split_ifs with hg
  swap
  · exact mul_nonneg (mul_nonneg (by positivity) (mX_nonneg _ _)) (mY_nonneg _ _)
  have hfe := (mem_injLabellings_iff_feasible N _).mp hg
  have hres : ∀ B : Finset (t.1.field.Obj × t.2.field.Obj × Fin 2), Feasible (ZMod q) N B (glue x y) :=
    fun B => ⟨fun a _ b _ hab => hfe.1 a (mem_univ _) b (mem_univ _) hab,
      fun e he _ _ => hfe.2 e he (mem_univ _) (mem_univ _)⟩
  have hx : Feasible (ZMod q) N A₀ (liftL x) := feasible_congr N A₀ (fun a ha => by
    have := (mem0 a).mp ha
    simp [glue, liftL, this]) (hres A₀)
  have hy : Feasible (ZMod q) N A₁ (liftL y) := feasible_congr N A₁ (fun a ha => by
    have := (mem1 a).mp ha
    simp [glue, liftL, this]) (hres A₁)
  have hcov0 : ∀ w, w ∈ A₀ ∨ w ∈ l₁ := fun w => by
    rcases hlay w with h | h
    · exact Or.inl ((mem0 w).mpr h)
    · exact Or.inr (mem_toList.mpr ((mem1 w).mpr h))
  have hdisj0 : ∀ w ∈ l₁, w ∉ A₀ := fun w hw h => by
    have a := (mem1 w).mp (mem_toList.mp hw)
    rw [(mem0 w).mp h] at a
    exact absurd a (by decide)
  have hcov1 : ∀ w, w ∈ A₁ ∨ w ∈ l₀ := fun w => by
    rcases hlay w with h | h
    · exact Or.inr (mem_toList.mpr ((mem0 w).mpr h))
    · exact Or.inl ((mem1 w).mpr h)
  have hdisj1 : ∀ w ∈ l₀, w ∉ A₁ := fun w hw h => by
    have a := (mem0 w).mp (mem_toList.mp hw)
    rw [(mem1 w).mp h] at a
    exact absurd a (by decide)
  have hcX := (extCount_bounds hWeil N le_rfl l₁ A₀ _ (nodup_toList _) hcov0 hdisj0 hx).1
  have hcY := (extCount_bounds hWeil N le_rfl l₀ A₁ _ (nodup_toList _) hcov1 hdisj1 hy).1
  rw [mX_pairLaw, mY_pairLaw]
  have e0 := graphLaw_layer_weight N (recN hW h4 t φ) 0 x
  have e1 := graphLaw_layer_weight N (recN hW h4 t φ) 1 y
  change ((graphLaw N (recN hW h4 t φ)).map (fun y => layerOf y 0)).weight x = _ at e0
  change ((graphLaw N (recN hW h4 t φ)).map (fun y => layerOf y 1)).weight y = _ at e1
  rw [show (crudeLam hW h4 t φ).map lay0 = (graphLaw N (recN hW h4 t φ)).map
    (fun y => layerOf y 0) from rfl, show (crudeLam hW h4 t φ).map lay1 =
    (graphLaw N (recN hW h4 t φ)).map (fun y => layerOf y 1) from rfl, e0, e1]
  set I : ℝ := ((injLabellings (ZMod q) N).card : ℝ)
  have hX : L₀ / I ≤ (extCount N (layerSet 0) (liftL x) : ℝ) / I :=
    div_le_div_of_nonneg_right hcX hIpos.le
  have hY : L₁ / I ≤ (extCount N (layerSet 1) (liftL y) : ℝ) / I :=
    div_le_div_of_nonneg_right hcY hIpos.le
  calc 1 / I ≤ ((2 : ℝ) ^ 144) ^ 2 * (L₀ / I) * (L₁ / I) := by
        rw [show ((2 : ℝ) ^ 144) ^ 2 * (L₀ / I) * (L₁ / I) = ((2 : ℝ) ^ 144) ^ 2 * L₀ * L₁ / (I * I)
          by ring, div_le_div_iff₀ hIpos (mul_pos hIpos hIpos), one_mul]
        calc I * I ≤ (((2 : ℝ) ^ 144) ^ 2 * L₀ * L₁) * I := mul_le_mul_of_nonneg_right hInj hIpos.le
          _ = _ := by ring
    _ ≤ _ := by
        have h0 : 0 ≤ L₀ / I := div_nonneg hL₀pos.le hIpos.le
        have h1 : 0 ≤ (extCount N (layerSet 0) (liftL x) : ℝ) / I :=
          div_nonneg (Nat.cast_nonneg _) hIpos.le
        gcongr

end Sarkozy.F7Repair
