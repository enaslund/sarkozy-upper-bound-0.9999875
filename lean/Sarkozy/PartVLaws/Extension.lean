module

public import Sarkozy.Labellings.TwoLayer
public import Sarkozy.Labellings.Sequential

@[expose] public section




namespace Sarkozy.PartVLaws

open Finset Sarkozy.Labellings

section Generic

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {W : Type*} [Fintype W] [DecidableEq W]

theorem nbrCount_le_univ (G : OrientedGraph W) (A : Finset W) (v : W) :
    nbrCount G A v ≤ nbrCount G univ v := by
  unfold nbrCount
  exact Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_univ A))

/-- **The lower product is positive** when every vertex has at most `D` neighbours and every
one-step lower bound with at most `D` earlier neighbours is positive. -/
theorem lowerProd_pos (G : OrientedGraph W) (q : ℝ) (n D : ℕ)
    (hdeg : ∀ v, nbrCount G univ v ≤ D) (hq : ∀ t ≤ D, 0 < q - softError q t - 2 ^ t * n) :
    ∀ (l : List W) (A : Finset W), 0 < lowerProd G q n A l
  | [], _ => by simp [lowerProd]
  | v :: l, A => by
      simp only [lowerProd]
      refine mul_pos ?_ (lowerProd_pos G q n D hdeg hq l _)
      unfold stepLower
      exact lt_max_of_lt_right
        (div_pos (hq _ ((nbrCount_le_univ G A v).trans (hdeg v))) (by positivity))

/-- **Every feasible partial labelling extends** (`lem:graphs:sequential`(a)): if the graph has
maximum degree at most `D` and `q - 𝔈_t - 2^t |W| > 0` for `t ≤ D`, every labelling feasible on
`A` agrees on `A` with some `y ∈ Inj_q(G)`. -/
theorem exists_extension (hW : WeilBound F) (G : OrientedGraph W) {D : ℕ}
    (hdeg : ∀ v, nbrCount G univ v ≤ D)
    (hq : ∀ t ≤ D, 0 < (Fintype.card F : ℝ) - softError (Fintype.card F) t -
      2 ^ t * (Fintype.card W : ℝ))
    {A : Finset W} {x : W → F} (hx : Feasible F G A x) :
    ∃ y ∈ injLabellings F G, ∀ a ∈ A, y a = x a := by
  classical
  set l := (univ \ A).toList with hl
  have hnd : l.Nodup := Finset.nodup_toList _
  have hcov : ∀ w, w ∈ A ∨ w ∈ l := fun w => by
    by_cases hw : w ∈ A
    · exact Or.inl hw
    · exact Or.inr (Finset.mem_toList.mpr (by simp [hw]))
  have hdisj : ∀ w ∈ l, w ∉ A := fun w hw => by
    have := Finset.mem_toList.mp hw
    simpa using this
  have hb := (extCount_bounds hW G (le_refl _) l A x hnd hcov hdisj hx).1
  have hpos := lowerProd_pos G (Fintype.card F) (Fintype.card W) D hdeg hq l A
  have hc : 0 < extCount G A x := by exact_mod_cast hpos.trans_le hb
  unfold extCount at hc
  obtain ⟨y, hy⟩ := Finset.card_pos.mp hc
  rw [Finset.mem_filter] at hy
  exact ⟨y, hy.1, hy.2⟩

end Generic

/-! ## The numerical threshold -/

theorem gradedA_le_642 {t : ℕ} (ht : t ≤ 8) : gradedA t ≤ 642 := by
  interval_cases t <;> norm_num [gradedA]

theorem gradedB_le_127 {t : ℕ} (ht : t ≤ 8) : gradedB t ≤ 127 := by
  interval_cases t <;> norm_num [gradedB]

/-- **The threshold for degree `8` and `36` vertices**: at every `q ≥ 2²⁰`,
`q - 𝔈_t - 2^t n > 0` for all `t ≤ 8` and `n ≤ 36`. -/
theorem threshold_eight {q : ℝ} (hq : 2 ^ 20 ≤ q) {n : ℝ} (hn0 : 0 ≤ n) (hn : n ≤ 36) :
    ∀ t ≤ 8, 0 < q - softError q t - 2 ^ t * n := by
  intro t ht
  have hq0 : 0 ≤ q := le_trans (by norm_num) hq
  have hs : (1024 : ℝ) ≤ Real.sqrt q := by
    have h1 : Real.sqrt ((2 : ℝ) ^ 20) = 1024 := by
      rw [show (2 : ℝ) ^ 20 = 1024 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    rw [← h1]
    exact Real.sqrt_le_sqrt hq
  have hsq : Real.sqrt q * Real.sqrt q = q := Real.mul_self_sqrt hq0
  have hA := gradedA_le_642 ht
  have hB := gradedB_le_127 ht
  have h2t : (2 : ℝ) ^ t ≤ 256 := by
    calc (2 : ℝ) ^ t ≤ 2 ^ 8 := pow_le_pow_right₀ (by norm_num) ht
      _ = 256 := by norm_num
  have hA' : gradedA t * Real.sqrt q ≤ 642 * Real.sqrt q :=
    mul_le_mul_of_nonneg_right hA (Real.sqrt_nonneg q)
  have h2n : (2 : ℝ) ^ t * n ≤ 256 * 36 :=
    mul_le_mul h2t hn hn0 (by norm_num)
  unfold softError
  nlinarith [mul_nonneg (sub_nonneg.mpr hs) (sub_nonneg.mpr hs)]

/-! ## Degrees of the matching graphs -/

section Degrees

variable {O₀ O₁ Λ : Type} [Fintype O₀] [DecidableEq O₀] [Fintype O₁] [DecidableEq O₁]
  [Fintype Λ] [DecidableEq Λ]

/-- The number of neighbours in a two-layer graph, as a Boolean count. -/
theorem nbrCount_twoLayer (c₀ : FieldType O₀) (c₁ : FieldType O₁) (h₀ : c₀.Proper)
    (h₁ : c₁.Proper) (v : O₀ × O₁ × Λ) :
    nbrCount (twoLayerGraph c₀ c₁ h₀ h₁ Λ) univ v =
      (univ.filter fun u => twoLayerEdge c₀ c₁ u v = true ∨
        twoLayerEdge c₀ c₁ v u = true).card := by
  unfold nbrCount
  congr 1
  exact Finset.filter_congr fun u _ => by rw [mem_twoLayerGraph, mem_twoLayerGraph]

theorem degree_EL_two : ∀ v : Fin 3 × ZMod 6 × Fin 2,
    (univ.filter fun u => twoLayerEdge typeE typeL u v = true ∨
      twoLayerEdge typeE typeL v u = true).card ≤ 8 := by
  unfold twoLayerEdge typeE typeL
  decide +kernel

theorem degree_EF_two : ∀ v : Fin 3 × Fin 3 × Fin 2,
    (univ.filter fun u => twoLayerEdge typeE typeF u v = true ∨
      twoLayerEdge typeE typeF v u = true).card ≤ 8 := by
  unfold twoLayerEdge typeE typeF
  decide +kernel

theorem degree_EE_two : ∀ v : Fin 3 × Fin 3 × Fin 2,
    (univ.filter fun u => twoLayerEdge typeE typeE u v = true ∨
      twoLayerEdge typeE typeE v u = true).card ≤ 8 := by
  unfold twoLayerEdge typeE
  decide +kernel

theorem degree_LE_two : ∀ v : ZMod 6 × Fin 3 × Fin 2,
    (univ.filter fun u => twoLayerEdge typeL typeE u v = true ∨
      twoLayerEdge typeL typeE v u = true).card ≤ 8 := by
  unfold twoLayerEdge typeE typeL
  decide +kernel

theorem degree_FE_two : ∀ v : Fin 3 × Fin 3 × Fin 2,
    (univ.filter fun u => twoLayerEdge typeF typeE u v = true ∨
      twoLayerEdge typeF typeE v u = true).card ≤ 8 := by
  unfold twoLayerEdge typeE typeF
  decide +kernel

theorem degree_EL_one : ∀ v : Fin 3 × ZMod 6 × Fin 1,
    (univ.filter fun u => twoLayerEdge typeE typeL u v = true ∨
      twoLayerEdge typeE typeL v u = true).card ≤ 8 := by
  unfold twoLayerEdge typeE typeL
  decide +kernel

theorem degree_EF_one : ∀ v : Fin 3 × Fin 3 × Fin 1,
    (univ.filter fun u => twoLayerEdge typeE typeF u v = true ∨
      twoLayerEdge typeE typeF v u = true).card ≤ 8 := by
  unfold twoLayerEdge typeE typeF
  decide +kernel

theorem degree_EE_one : ∀ v : Fin 3 × Fin 3 × Fin 1,
    (univ.filter fun u => twoLayerEdge typeE typeE u v = true ∨
      twoLayerEdge typeE typeE v u = true).card ≤ 8 := by
  unfold twoLayerEdge typeE
  decide +kernel

theorem degree_LE_one : ∀ v : ZMod 6 × Fin 3 × Fin 1,
    (univ.filter fun u => twoLayerEdge typeL typeE u v = true ∨
      twoLayerEdge typeL typeE v u = true).card ≤ 8 := by
  unfold twoLayerEdge typeE typeL
  decide +kernel

theorem degree_FE_one : ∀ v : Fin 3 × Fin 3 × Fin 1,
    (univ.filter fun u => twoLayerEdge typeF typeE u v = true ∨
      twoLayerEdge typeF typeE v u = true).card ≤ 8 := by
  unfold twoLayerEdge typeE typeF
  decide +kernel

end Degrees

end Sarkozy.PartVLaws
