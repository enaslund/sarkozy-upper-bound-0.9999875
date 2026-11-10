module

public import Sarkozy.PartVLaws.CountRatio
public import Sarkozy.PartVLaws.FoldMarginals

@[expose] public section

/-!
# The count-type inputs of the tail rows: the fold mass and the marginal ratios

`paper/sections/25_upper_reference.tex`, `def:record:upper-bands`, items (F3) and (F5)(b) (the
middle marginal ratio `ℓ_mid` and `H = exp(n̄ ℓ_mid)` of the Schur rows of the tail datum);
`paper/sections/12_labellings.tex`, `lem:graphs:sequential`(b).

The mass of the fold kernel of a row datum is the ratio of the middle laws of the `F` and `E`
rows (`kf_fold_one`). For the tail law at a prime `p ≥ P₄` these are laws of a restriction of
the uniform laws on `Inj_p(G_{F𝔣})` and `Inj_p(G_{E𝔣})`; both graphs have no edge inside a row,
so the same restrictions are feasible for both, and the completion counts of two feasible
restrictions differ by at most `ρ^k`, `ρ = 1 + 2²⁸/√p` (`extCount_le_ratio`,
`stepUpper_le_sqrt`). Hence:

* generic: `graphLaw_map_weight_extCount` (the law of a restriction is a completion count over
  `|Inj_p(G)|`), `weight_mul_card_le`, `one_le_mul_weight_mul_card` (normalization);
* **`tail_foldMass_bounds`**: at every prime `p ≥ P₄`, the fold-kernel mass of every two-layer
  row datum of the coordinate `0` of the tail law satisfies `ρ^{-144} ≤ m_b ≤ ρ^{144}`,
  `ρ = 1 + 2²⁸/√p`, so the mass fields of the fold data (`FoldData.mass_lower`, `mass_upper`;
  `SchurRowData`) hold with `H = ρ^{144} = 1 + O(p^{-1/2})`;
* **`tail_kone_bounds`**, **`tail_kone'_bounds`**: the row and column sums `T_F^b 𝟙` and
  `(T_F^b)^* 𝟙` (the pointwise marginal ratios of (F1)) lie in the same range.

This discharges, for the two-layer rows of the coordinate `0`, the count-type inputs (F1), (F3)
of the Schur rows (`TailSchur`); `RowFrame` and `TailRowsAll` do the same for all four row
families of the tail datum. The correlations (F4) remain hypotheses.
-/

namespace Sarkozy.PartVLaws

open Finset Sarkozy.Labellings Sarkozy.FiveType Sarkozy.PartV Sarkozy.FiveType.TwoCoord

/-! ## The law of a restriction under a graph law -/

section Restrict

variable {W : Type*} [Fintype W] [DecidableEq W] {F : Type*} [Field F] [Fintype F]
  [DecidableEq F] {Y : Type*} [Fintype Y] [DecidableEq Y]

/-- **A map of labellings that reads exactly the labels of `A`**: `φ y = b` if and only if `y`
agrees on `A` with the labelling `lift b`. -/
def ReadsSet (A : Finset W) (φ : (W → F) → Y) (lift : Y → W → F) : Prop :=
  ∀ y b, φ y = b ↔ ∀ a ∈ A, y a = lift b a

/-- **The law of a restriction is a completion count**: `P(φ = b) = C_A(lift b)/|Inj(G)|`. -/
theorem graphLaw_map_weight_extCount (G : OrientedGraph W) (hne : (injLabellings F G).Nonempty)
    {A : Finset W} {φ : (W → F) → Y} {lift : Y → W → F} (h : ReadsSet A φ lift) (b : Y) :
    ((graphLaw G hne).map φ).weight b =
      (extCount G A (lift b) : ℝ) / (injLabellings F G).card := by
  classical
  rw [map_weight_eq]
  have hw : ∀ y ∈ univ.filter (fun y => φ y = b), (graphLaw G hne).weight y =
      if y ∈ injLabellings F G then 1 / ((injLabellings F G).card : ℝ) else 0 := fun _ _ => rfl
  rw [sum_congr rfl hw, sum_ite_mem, sum_const, nsmul_eq_mul, mul_one_div]
  congr 1
  unfold extCount
  have hset : univ.filter (fun y => φ y = b) ∩ injLabellings F G =
      (injLabellings F G).filter (fun y => ∀ a ∈ A, y a = lift b a) := by
    ext y
    simp only [mem_inter, mem_filter, mem_univ, true_and]
    rw [h y b]
    tauto
  rw [hset]

end Restrict

/-! ## Normalization -/

section Normal

variable {Y : Type*} [Fintype Y] [DecidableEq Y]

omit [DecidableEq Y] in
/-- If `μ(b) ≤ c μ(b')` for every `b'` of a set `S` outside which `μ` vanishes, then
`μ(b) |S| ≤ c`. -/
theorem weight_mul_card_le (μ : FiniteLaw Y) (S : Finset Y) {c : ℝ} (b : Y)
    (hS : ∀ b' ∉ S, μ.weight b' = 0) (h : ∀ b' ∈ S, μ.weight b ≤ c * μ.weight b') :
    μ.weight b * S.card ≤ c := by
  have htot : ∑ b' ∈ S, μ.weight b' = 1 := by
    rw [← μ.total]
    exact sum_subset (subset_univ S) fun b' _ hb' => hS b' hb'
  calc μ.weight b * S.card = ∑ _b' ∈ S, μ.weight b := by rw [sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ ∑ b' ∈ S, c * μ.weight b' := sum_le_sum h
    _ = c := by rw [← mul_sum, htot, mul_one]

omit [DecidableEq Y] in
/-- If `μ(b') ≤ c μ(b)` for every `b'` of a set `S` outside which `μ` vanishes, then
`1 ≤ c μ(b) |S|`. -/
theorem one_le_mul_weight_mul_card (μ : FiniteLaw Y) (S : Finset Y) {c : ℝ} (b : Y)
    (hS : ∀ b' ∉ S, μ.weight b' = 0) (h : ∀ b' ∈ S, μ.weight b' ≤ c * μ.weight b) :
    1 ≤ c * μ.weight b * S.card := by
  have htot : ∑ b' ∈ S, μ.weight b' = 1 := by
    rw [← μ.total]
    exact sum_subset (subset_univ S) fun b' _ hb' => hS b' hb'
  calc (1 : ℝ) = ∑ b' ∈ S, μ.weight b' := htot.symm
    _ ≤ ∑ _b' ∈ S, c * μ.weight b := sum_le_sum h
    _ = c * μ.weight b * S.card := by rw [sum_const, nsmul_eq_mul, mul_comm]

end Normal

/-! ## Feasible restrictions -/

section Feasible

variable {W : Type*} [Fintype W] [DecidableEq W] {F : Type*} [Field F] [Fintype F]
  [DecidableEq F]

/-- A labelling with a completion is feasible on `A`. -/
theorem feasible_of_extCount_ne_zero (G : OrientedGraph W) {A : Finset W} {x : W → F}
    (h : extCount G A x ≠ 0) : Feasible F G A x := by
  classical
  unfold extCount at h
  obtain ⟨y, hy⟩ := Finset.card_pos.mp (Nat.pos_of_ne_zero h)
  rw [Finset.mem_filter, mem_injLabellings_iff_feasible] at hy
  obtain ⟨⟨hinj, hedge⟩, hxy⟩ := hy
  refine ⟨fun a ha b hb hab => hinj a (mem_univ _) b (mem_univ _) ?_, fun e he h1 h2 => ?_⟩
  · rw [hxy a ha, hxy b hb]
    exact hab
  · rw [← hxy _ h1, ← hxy _ h2]
    exact hedge e he (mem_univ _) (mem_univ _)

end Feasible

/-! ## The middle row of the tail laws -/

section TailRow

/-- The objects of a C1 field type from those of the V1 field type (the identity in each case). -/
def objUncast : (f : FieldTy) → (toFType f).Obj → f.Obj
  | .L => fun x => x
  | .F => fun x => x
  | .E => fun x => x

theorem objCast_objUncast (f : FieldTy) (o : (toFType f).Obj) : objCast f (objUncast f o) = o := by
  cases f <;> rfl

theorem objUncast_objCast (f : FieldTy) (o : f.Obj) : objUncast f (objCast f o) = o := by
  cases f <;> rfl

/-- The layers `Fin 2` as `ℤ/2ℤ`. -/
def layerUn (i : Fin 2) : ZMod 2 := i

theorem layerFin_layerUn (i : Fin 2) : layerFin (layerUn i) = i := rfl

theorem layerUn_layerFin (ℓ : ZMod 2) : layerUn (layerFin ℓ) = ℓ := rfl

variable (p : ℕ) [Fact p.Prime] (f' : FieldTy)

/-- The middle row `{1} × O × {0,1}` of the V1 labellings. -/
def row1 : Finset (Fin 3 × (toFType f').Obj × Fin 2) := univ.filter fun w => w.1 = 1

/-- A row labelling as a V1 labelling (its values off the middle row do not matter). -/
def liftRow (b : f'.Obj × ZMod 2 → ZMod p) (w : Fin 3 × (toFType f').Obj × Fin 2) : ZMod p :=
  b (objUncast f' w.2.1, layerUn w.2.2)

/-- The middle row of a V1 labelling, read in C1's coordinates. -/
def readRow1 (y : Fin 3 × (toFType f').Obj × Fin 2 → ZMod p) (q : f'.Obj × ZMod 2) : ZMod p :=
  y (1, objCast f' q.1, layerFin q.2)

omit [Fact p.Prime] in
theorem readsSet_row1 : ReadsSet (row1 f') (readRow1 p f') (liftRow p f') := by
  intro y b
  constructor
  · rintro rfl a ha
    have ha1 : a.1 = 1 := (mem_filter.mp ha).2
    obtain ⟨a1, a2, a3⟩ := a
    simp only at ha1
    subst ha1
    simp only [liftRow, readRow1, objCast_objUncast, layerFin_layerUn]
  · intro h
    funext q
    have := h (1, objCast f' q.1, layerFin q.2) (mem_filter.mpr ⟨mem_univ _, rfl⟩)
    simp only [liftRow, objUncast_objCast, layerUn_layerFin] at this
    exact this

/-- The fold graph `G_{F𝔣}` and the matching graph `G_{E𝔣}` on the same vertices. -/
abbrev graphF : OrientedGraph (Fin 3 × (toFType f').Obj × Fin 2) :=
  fieldGraph .F (toFType f') (Fin 2)

abbrev graphE : OrientedGraph (Fin 3 × (toFType f').Obj × Fin 2) :=
  fieldGraph .E (toFType f') (Fin 2)

theorem no_edge_row1_F (e : (Fin 3 × (toFType f').Obj × Fin 2) × (Fin 3 × (toFType f').Obj × Fin 2))
    (he : e ∈ (graphF f').E) (h1 : e.1.1 = 1) (h2 : e.2.1 = 1) : False := by
  rw [graphF, fieldGraph, mem_twoLayerGraph] at he
  simp only [twoLayerEdge, Bool.and_eq_true] at he
  have h := he.1.1
  change typeF.rel e.1.1 e.2.1 = true at h
  rw [h1, h2] at h
  exact absurd h (by decide)

theorem no_edge_row1_E (e : (Fin 3 × (toFType f').Obj × Fin 2) × (Fin 3 × (toFType f').Obj × Fin 2))
    (he : e ∈ (graphE f').E) (h1 : e.1.1 = 1) (h2 : e.2.1 = 1) : False := by
  rw [graphE, fieldGraph, mem_twoLayerGraph] at he
  simp only [twoLayerEdge, Bool.and_eq_true] at he
  have h := he.1.1
  change typeE.rel e.1.1 e.2.1 = true at h
  rw [h1, h2] at h
  exact absurd h (by decide)

/-- **Feasibility on the middle row is the same for `G_{F𝔣}` and `G_{E𝔣}`.** -/
theorem feasible_row1_FE (x : Fin 3 × (toFType f').Obj × Fin 2 → ZMod p) :
    Feasible (ZMod p) (graphF f') (row1 f') x ↔ Feasible (ZMod p) (graphE f') (row1 f') x := by
  constructor
  · intro h
    exact ⟨h.1, fun e he h1 h2 =>
      (no_edge_row1_E f' e he (mem_filter.mp h1).2 (mem_filter.mp h2).2).elim⟩
  · intro h
    exact ⟨h.1, fun e he h1 h2 =>
      (no_edge_row1_F f' e he (mem_filter.mp h1).2 (mem_filter.mp h2).2).elim⟩

end TailRow

/-! ## The mass of the fold kernel of the tail rows -/

section Mass

/-- The one-step ratio `ρ(q) = 1 + 2²⁸/√q` at the tail primes. -/
noncomputable def countRho (q : ℝ) : ℝ := 1 + 2 ^ 28 / Real.sqrt q

theorem one_le_countRho (q : ℝ) : 1 ≤ countRho q := by
  unfold countRho
  have : (0 : ℝ) ≤ 2 ^ 28 / Real.sqrt q := div_nonneg (by positivity) (Real.sqrt_nonneg q)
  linarith

variable (p : ℕ) [Fact p.Prime] (hne : TailNonempty p) (f' : FieldTy)

/-- The middle-row law of the `F` rows of the tail law is the law of the middle row of the
uniform law on `Inj_p(G_{F𝔣})`. -/
theorem tail_midF_eq :
    (((lam2 (tailFieldLaws p hne) .F f').map
      fun y => (rows0 y : Fin 3 → f'.Obj × ZMod 2 → ZMod p)).map fun ω => ω 1) =
      (graphLaw (graphF f') (hne.two .F (toFType f'))).map (readRow1 p f') := by
  unfold lam2
  rw [map_map', map_map']
  rfl

/-- The same for the `E` rows. -/
theorem tail_midE_eq :
    (((lam2 (tailFieldLaws p hne) .E f').map
      fun y => (rows0 y : Fin 3 → f'.Obj × ZMod 2 → ZMod p)).map fun ω => ω 1) =
      (graphLaw (graphE f') (hne.two .E (toFType f'))).map (readRow1 p f') := by
  unfold lam2
  rw [map_map', map_map']
  rfl

theorem sqrt_ge_of_P4 (hp : P4 ≤ p) : (2 : ℝ) ^ 256 ≤ Real.sqrt (Fintype.card (ZMod p)) := by
  rw [ZMod.card]
  have h512 : (2 : ℝ) ^ 512 ≤ p := by
    have := (Nat.cast_le (α := ℝ)).mpr hp
    rwa [show P4 = 2 ^ 512 from rfl, Nat.cast_pow, Nat.cast_ofNat] at this
  have h : ((2 : ℝ) ^ 256) ^ 2 ≤ p := by
    rw [← pow_mul]
    exact h512
  calc (2 : ℝ) ^ 256 = Real.sqrt (((2 : ℝ) ^ 256) ^ 2) := (Real.sqrt_sq (by positivity)).symm
    _ ≤ Real.sqrt p := Real.sqrt_le_sqrt h

theorem card_row_vertices_le :
    Fintype.card (Fin 3 × (toFType f').Obj × Fin 2) ≤ 72 := by
  have h6 := card_obj_le (toFType f')
  rw [Fintype.card_prod, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  nlinarith

/-- **Completion counts of two feasible labellings of a set are within `ρ^k`** at a tail prime,
for a graph of degree at most `20` on at most `72` vertices. -/
theorem tail_count_ratio {W : Type*} [Fintype W] [DecidableEq W] (hW : WeilBound (ZMod p))
    (hp : P4 ≤ p) (hW72 : Fintype.card W ≤ 72) (G : OrientedGraph W)
    (hdeg : ∀ v, nbrCount G univ v ≤ 20) {A : Finset W} {x x' : W → ZMod p}
    (hx : Feasible (ZMod p) G A x) (hx' : Feasible (ZMod p) G A x') :
    (extCount G A x : ℝ) ≤ countRho p ^ (univ \ A).card * extCount G A x' :=
  extCount_le_ratio hW G hdeg (le_trans zero_le_one (one_le_countRho p)) (fun _ ht => by
    have := stepUpper_le_sqrt (sqrt_ge_of_P4 p hp) hW72 ht
    rw [ZMod.card] at this ⊢
    exact this) hx hx'

/-- **The ratio of the laws of a restriction under two graph laws** with the same feasible
restrictions: at a tail prime, on the support, it lies in `[ρ^{-144}, ρ^{144}]`. -/
theorem restriction_ratio_bounds {W : Type*} [Fintype W] [DecidableEq W]
    {Y : Type*} [Fintype Y] [DecidableEq Y] (hW : WeilBound (ZMod p)) (hp : P4 ≤ p)
    (hW72 : Fintype.card W ≤ 72) (G1 G2 : OrientedGraph W)
    (hne1 : (injLabellings (ZMod p) G1).Nonempty) (hne2 : (injLabellings (ZMod p) G2).Nonempty)
    (hdeg1 : ∀ v, nbrCount G1 univ v ≤ 20) (hdeg2 : ∀ v, nbrCount G2 univ v ≤ 20)
    {A : Finset W} {φ : (W → ZMod p) → Y} {lift : Y → W → ZMod p} (hR : ReadsSet A φ lift)
    (hfeas : ∀ x, Feasible (ZMod p) G1 A x ↔ Feasible (ZMod p) G2 A x) (b : Y)
    (hb : ((graphLaw G2 hne2).map φ).weight b ≠ 0) :
    (countRho p ^ 144)⁻¹ ≤
        ((graphLaw G1 hne1).map φ).weight b / ((graphLaw G2 hne2).map φ).weight b ∧
      ((graphLaw G1 hne1).map φ).weight b / ((graphLaw G2 hne2).map φ).weight b ≤
        countRho p ^ 144 := by
  classical
  set μF := (graphLaw G1 hne1).map φ with hμF
  set μE := (graphLaw G2 hne2).map φ with hμE
  have wF : ∀ b', μF.weight b' = (extCount G1 A (lift b') : ℝ) / (injLabellings (ZMod p) G1).card :=
    fun b' => graphLaw_map_weight_extCount _ _ hR b'
  have wE : ∀ b', μE.weight b' = (extCount G2 A (lift b') : ℝ) / (injLabellings (ZMod p) G2).card :=
    fun b' => graphLaw_map_weight_extCount _ _ hR b'
  have hIF : (0 : ℝ) < (injLabellings (ZMod p) G1).card := by
    exact_mod_cast Finset.card_pos.mpr hne1
  have hIE : (0 : ℝ) < (injLabellings (ZMod p) G2).card := by
    exact_mod_cast Finset.card_pos.mpr hne2
  set S := univ.filter fun b' : Y => Feasible (ZMod p) G2 A (lift b') with hS
  have feasE : ∀ b', μE.weight b' ≠ 0 → b' ∈ S := by
    intro b' hb'
    rw [wE] at hb'
    have : extCount G2 A (lift b') ≠ 0 := by
      intro h0
      rw [h0, Nat.cast_zero, zero_div] at hb'
      exact hb' rfl
    exact mem_filter.mpr ⟨mem_univ _, feasible_of_extCount_ne_zero _ this⟩
  have feasF : ∀ b', μF.weight b' ≠ 0 → b' ∈ S := by
    intro b' hb'
    rw [wF] at hb'
    have : extCount G1 A (lift b') ≠ 0 := by
      intro h0
      rw [h0, Nat.cast_zero, zero_div] at hb'
      exact hb' rfl
    exact mem_filter.mpr ⟨mem_univ _, (hfeas _).mp (feasible_of_extCount_ne_zero _ this)⟩
  have hSE : ∀ b' ∉ S, μE.weight b' = 0 := fun b' hb' => by
    by_contra h0
    exact hb' (feasE b' h0)
  have hSF : ∀ b' ∉ S, μF.weight b' = 0 := fun b' hb' => by
    by_contra h0
    exact hb' (feasF b' h0)
  have hbS : b ∈ S := feasE b hb
  set k := (univ \ A).card with hk
  have hρ0 : 0 ≤ countRho p := le_trans zero_le_one (one_le_countRho p)
  have hρpos : 0 < countRho p := lt_of_lt_of_le zero_lt_one (one_le_countRho p)
  have ratioE : ∀ b₁ ∈ S, ∀ b₂ ∈ S, μE.weight b₁ ≤ countRho p ^ k * μE.weight b₂ := by
    intro b₁ h₁ b₂ h₂
    rw [wE, wE, ← mul_div_assoc]
    exact div_le_div_of_nonneg_right (tail_count_ratio p hW hp hW72 G2 hdeg2
      (mem_filter.mp h₁).2 (mem_filter.mp h₂).2) hIE.le
  have ratioF : ∀ b₁ ∈ S, ∀ b₂ ∈ S, μF.weight b₁ ≤ countRho p ^ k * μF.weight b₂ := by
    intro b₁ h₁ b₂ h₂
    rw [wF, wF, ← mul_div_assoc]
    exact div_le_div_of_nonneg_right (tail_count_ratio p hW hp hW72 G1 hdeg1
      ((hfeas _).mpr (mem_filter.mp h₁).2) ((hfeas _).mpr (mem_filter.mp h₂).2)) hIF.le
  have hN : (0 : ℝ) < S.card := by exact_mod_cast Finset.card_pos.mpr ⟨b, hbS⟩
  have hEpos : 0 < μE.weight b := lt_of_le_of_ne (μE.nonneg b) (Ne.symm hb)
  have hF0 : 0 ≤ μF.weight b := μF.nonneg b
  have hk72 : k ≤ 72 := (card_le_univ _).trans hW72
  have hpow : countRho p ^ (2 * k) ≤ countRho p ^ 144 :=
    pow_le_pow_right₀ (one_le_countRho p) (by omega)
  have hpk0 : 0 ≤ countRho p ^ k := pow_nonneg hρ0 k
  have h2k : countRho p ^ (2 * k) = countRho p ^ k * countRho p ^ k := by rw [two_mul, pow_add]
  constructor
  · have h1 := one_le_mul_weight_mul_card μF S b hSF (fun b' hb' => ratioF b' hb' b hbS)
    have h2 := weight_mul_card_le μE S b hSE (fun b' hb' => ratioE b hbS b' hb')
    have key : μE.weight b ≤ countRho p ^ (2 * k) * μF.weight b := by
      rw [h2k]
      have : μE.weight b * S.card ≤ countRho p ^ k * (countRho p ^ k * μF.weight b * S.card) :=
        h2.trans (le_mul_of_one_le_right hpk0 h1)
      have h3 : μE.weight b * S.card ≤ (countRho p ^ k * countRho p ^ k * μF.weight b) * S.card :=
        this.trans_eq (by ring)
      exact le_of_mul_le_mul_right h3 hN
    have hinv : 0 ≤ (countRho p ^ 144)⁻¹ := inv_nonneg.mpr (pow_nonneg hρ0 _)
    rw [le_div_iff₀ hEpos]
    calc (countRho p ^ 144)⁻¹ * μE.weight b
          ≤ (countRho p ^ 144)⁻¹ * (countRho p ^ (2 * k) * μF.weight b) :=
          mul_le_mul_of_nonneg_left key hinv
      _ ≤ (countRho p ^ 144)⁻¹ * (countRho p ^ 144 * μF.weight b) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hpow hF0) hinv
      _ = μF.weight b := by
          rw [← mul_assoc, inv_mul_cancel₀ (pow_pos hρpos _).ne', one_mul]
  · have h1 := weight_mul_card_le μF S b hSF (fun b' hb' => ratioF b hbS b' hb')
    have h2 := one_le_mul_weight_mul_card μE S b hSE (fun b' hb' => ratioE b' hb' b hbS)
    have key : μF.weight b ≤ countRho p ^ (2 * k) * μE.weight b := by
      rw [h2k]
      have : μF.weight b * S.card ≤ countRho p ^ k * (countRho p ^ k * μE.weight b * S.card) :=
        h1.trans (le_mul_of_one_le_right hpk0 h2)
      have h3 : μF.weight b * S.card ≤ (countRho p ^ k * countRho p ^ k * μE.weight b) * S.card :=
        this.trans_eq (by ring)
      exact le_of_mul_le_mul_right h3 hN
    rw [div_le_iff₀ hEpos]
    exact key.trans (mul_le_mul_of_nonneg_right hpow hEpos.le)

/-- **The mass of the fold kernel of the tail rows** (`def:record:upper-bands`, (F3); the mass
fields of the fold data of `rem:five-type-fold-data`): at every prime `p ≥ P₄`, under Weil's
bound, for every two-layer row datum of the coordinate `0` of the tail law and every middle value
`b`, `ρ^{-144} ≤ m_b ≤ ρ^{144}` with `ρ = 1 + 2²⁸/√p`. -/
theorem tail_foldMass_bounds (hW : WeilBound (ZMod p)) (hp : P4 ≤ p)
    (h : RowHyp0 (lam2 (tailFieldLaws p hne)) f') (b : f'.Obj × ZMod 2 → ZMod p)
    (hb : (rowD0 (lam2 (tailFieldLaws p hne)) f' h).nu.weight b ≠ 0) :
    (countRho p ^ 144)⁻¹ ≤ kf ((rowD0 (lam2 (tailFieldLaws p hne)) f' h).nub b)
        ((rowD0 (lam2 (tailFieldLaws p hne)) f' h).TF b) (fun _ => 1) (fun _ => 1) ∧
      kf ((rowD0 (lam2 (tailFieldLaws p hne)) f' h).nub b)
        ((rowD0 (lam2 (tailFieldLaws p hne)) f' h).TF b) (fun _ => 1) (fun _ => 1) ≤
        countRho p ^ 144 := by
  rw [rowD0_foldMass _ f' h b hb]
  have eF := tail_midF_eq p hne f'
  have eE : (rowD0 (lam2 (tailFieldLaws p hne)) f' h).nu =
      (graphLaw (graphE f') (hne.two .E (toFType f'))).map (readRow1 p f') := tail_midE_eq p hne f'
  rw [eF, eE]
  rw [eE] at hb
  exact restriction_ratio_bounds p hW hp (card_row_vertices_le f') (graphF f') (graphE f') _ _
    (fieldGraph_degree_two .F (toFType f')) (fieldGraph_degree_two .E (toFType f'))
    (readsSet_row1 p f') (feasible_row1_FE p f') b hb

end Mass

/-! ## Two rows: the left marginal density of the fold kernel -/

section TwoRows

variable (p : ℕ) [Fact p.Prime] (hne : TailNonempty p) (f' : FieldTy)

/-- The rows `{0, 1}` of the V1 labellings, i.e. all but the row `j`. -/
def rowsOff (j : Fin 3) : Finset (Fin 3 × (toFType f').Obj × Fin 2) := univ.filter fun w => w.1 ≠ j

/-- **On the rows off `j ∈ {0, 2}`, `G_{F𝔣}` and `G_{E𝔣}` have the same feasible labellings**
(`lem:upper-geometry`(d)). -/
theorem feasible_rowsOff_FE {j : Fin 3} (hj : j ≠ 1)
    (x : Fin 3 × (toFType f').Obj × Fin 2 → ZMod p) :
    Feasible (ZMod p) (graphF f') (rowsOff f' j) x ↔
      Feasible (ZMod p) (graphE f') (rowsOff f' j) x := by
  have hedge : ∀ e : (Fin 3 × (toFType f').Obj × Fin 2) × (Fin 3 × (toFType f').Obj × Fin 2),
      e.1 ∈ rowsOff f' j → e.2 ∈ rowsOff f' j → (e ∈ (graphF f').E ↔ e ∈ (graphE f').E) := by
    intro e h1 h2
    rw [graphF, graphE, fieldGraph, fieldGraph, mem_twoLayerGraph, mem_twoLayerGraph]
    have := edge_agree_left (toFType f').rel hj e.1 e.2 (mem_filter.mp h1).2 (mem_filter.mp h2).2
    change twoLayerEdge typeF _ e.1 e.2 = true ↔ twoLayerEdge typeE _ e.1 e.2 = true
    rw [this]
  constructor
  · intro h
    exact ⟨h.1, fun e he h1 h2 => h.2 e ((hedge e h1 h2).mpr he) h1 h2⟩
  · intro h
    exact ⟨h.1, fun e he h1 h2 => h.2 e ((hedge e h1 h2).mp he) h1 h2⟩

/-- The rows `0, 1` of a V1 labelling, read in C1's coordinates. -/
def readRows01 (y : Fin 3 × (toFType f').Obj × Fin 2 → ZMod p) (i : Fin 2)
    (q : f'.Obj × ZMod 2) : ZMod p :=
  y (i.castSucc, objCast f' q.1, layerFin q.2)

/-- Two row labellings as a V1 labelling (values on the row `2` do not matter). -/
def liftRows01 (c : Fin 2 → f'.Obj × ZMod 2 → ZMod p) (w : Fin 3 × (toFType f').Obj × Fin 2) :
    ZMod p :=
  if h : w.1 = Fin.last 2 then 0 else c (w.1.castPred h) (objUncast f' w.2.1, layerUn w.2.2)

theorem readsSet_rows01 : ReadsSet (rowsOff f' 2) (readRows01 p f') (liftRows01 p f') := by
  intro y c
  constructor
  · rintro rfl a ha
    have ha2 : a.1 ≠ Fin.last 2 := (mem_filter.mp ha).2
    obtain ⟨a1, a2, a3⟩ := a
    simp only [liftRows01, ha2, ↓reduceDIte, readRows01, Fin.castSucc_castPred,
      objCast_objUncast, layerFin_layerUn]
  · intro h
    funext i q
    have := h (i.castSucc, objCast f' q.1, layerFin q.2)
      (mem_filter.mpr ⟨mem_univ _, Fin.castSucc_ne_last i⟩)
    simp only [liftRows01, Fin.castSucc_ne_last, ↓reduceDIte, Fin.castPred_castSucc,
      objUncast_objCast, layerUn_layerFin] at this
    exact this

/-- The law of the rows `0, 1` of the `F` rows of the tail law. -/
theorem tail_gamF_eq :
    gamOf ((lam2 (tailFieldLaws p hne) .F f').map
      fun y => (rows0 y : Fin 3 → f'.Obj × ZMod 2 → ZMod p)) =
      (graphLaw (graphF f') (hne.two .F (toFType f'))).map (readRows01 p f') := by
  unfold gamOf lam2
  rw [map_map', map_map']
  rfl

theorem tail_gamE_eq :
    gamOf ((lam2 (tailFieldLaws p hne) .E f').map
      fun y => (rows0 y : Fin 3 → f'.Obj × ZMod 2 → ZMod p)) =
      (graphLaw (graphE f') (hne.two .E (toFType f'))).map (readRows01 p f') := by
  unfold gamOf lam2
  rw [map_map', map_map']
  rfl

/-- **The row sums of the fold kernel of the tail rows** (the pointwise marginal ratio of (F1)):
at every prime `p ≥ P₄`, under Weil's bound, on the support of `ν^b`,
`ρ^{-144} ≤ T_F^b 𝟙 (x) ≤ ρ^{144}`. -/
theorem tail_kone_bounds (hW : WeilBound (ZMod p)) (hp : P4 ≤ p)
    (h : RowHyp0 (lam2 (tailFieldLaws p hne)) f') (b : f'.Obj × ZMod 2 → ZMod p)
    (hb : (rowD0 (lam2 (tailFieldLaws p hne)) f' h).nu.weight b ≠ 0)
    (x : f'.Obj × ZMod 2 → ZMod p)
    (hx : ((rowD0 (lam2 (tailFieldLaws p hne)) f' h).nub b).weight x ≠ 0) :
    (countRho p ^ 144)⁻¹ ≤ kone ((rowD0 (lam2 (tailFieldLaws p hne)) f' h).nub b)
        ((rowD0 (lam2 (tailFieldLaws p hne)) f' h).TF b) x ∧
      kone ((rowD0 (lam2 (tailFieldLaws p hne)) f' h).nub b)
        ((rowD0 (lam2 (tailFieldLaws p hne)) f' h).TF b) x ≤ countRho p ^ 144 := by
  have hk := kone_fold _ _ h.supp hb hx
  have eF := tail_gamF_eq p hne f'
  have eE := tail_gamE_eq p hne f'
  have hg : (gamOf ((lam2 (tailFieldLaws p hne) .E f').map
      fun y => (rows0 y : Fin 3 → f'.Obj × ZMod 2 → ZMod p))).weight ![x, b] ≠ 0 := by
    have e := gamOf_weight ((lam2 (tailFieldLaws p hne) .E f').map
      fun y => (rows0 y : Fin 3 → f'.Obj × ZMod 2 → ZMod p)) ![x, b]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at e
    rw [e]
    exact mul_ne_zero hb hx
  rw [eF, eE] at hk
  rw [eE] at hg
  have := restriction_ratio_bounds p hW hp (card_row_vertices_le f') (graphF f') (graphE f')
    (hne.two .F (toFType f')) (hne.two .E (toFType f'))
    (fieldGraph_degree_two .F (toFType f')) (fieldGraph_degree_two .E (toFType f'))
    (readsSet_rows01 p f') (feasible_rowsOff_FE p f' (j := 2) (by decide)) ![x, b] hg
  have hk' : kone ((rowD0 (lam2 (tailFieldLaws p hne)) f' h).nub b)
      ((rowD0 (lam2 (tailFieldLaws p hne)) f' h).TF b) x =
      ((graphLaw (graphF f') (hne.two .F (toFType f'))).map (readRows01 p f')).weight ![x, b] /
        ((graphLaw (graphE f') (hne.two .E (toFType f'))).map (readRows01 p f')).weight ![x, b] :=
    hk
  rw [hk']
  exact this

end TwoRows

/-! ## Rows `1, 2`: the right marginal density of the fold kernel -/

section RowsOneTwo

variable (p : ℕ) [Fact p.Prime] (hne : TailNonempty p) (f' : FieldTy)

omit [Fact p.Prime] in
/-- The configurations with objects `1, 2` equal to `b, y` are the `![x, b, y]`. -/
theorem map_succ_weight_eq_sum {𝔛 : Type*} [Fintype 𝔛] [DecidableEq 𝔛]
    (π : FiniteLaw (Fin 3 → 𝔛)) (b y : 𝔛) :
    (π.map fun ω (i : Fin 2) => ω i.succ).weight ![b, y] = ∑ x, π.weight ![x, b, y] := by
  rw [map_weight_eq]
  have hfilt : (univ.filter fun ω : Fin 3 → 𝔛 => (fun i : Fin 2 => ω i.succ) = ![b, y]) =
      univ.image fun x => ![x, b, y] := by
    ext ω
    simp only [mem_filter, mem_univ, true_and, mem_image]
    constructor
    · intro h
      have h1 : ω 1 = b := by
        have := congrFun h 0
        simpa using this
      have h2 : ω 2 = y := by
        have := congrFun h 1
        simpa using this
      refine ⟨ω 0, ?_⟩
      funext i
      fin_cases i
      · rfl
      · simp [h1]
      · simp [h2]
    · rintro ⟨x, rfl⟩
      funext i
      fin_cases i <;> rfl
  rw [hfilt, sum_image]
  intro x _ x' _ h
  have := congrFun h 0
  simpa using this

/-- The rows `1, 2` of a V1 labelling, read in C1's coordinates. -/
def readRows12 (y : Fin 3 × (toFType f').Obj × Fin 2 → ZMod p) (i : Fin 2)
    (q : f'.Obj × ZMod 2) : ZMod p :=
  y (i.succ, objCast f' q.1, layerFin q.2)

/-- Two row labellings on the rows `1, 2` as a V1 labelling. -/
def liftRows12 (c : Fin 2 → f'.Obj × ZMod 2 → ZMod p) (w : Fin 3 × (toFType f').Obj × Fin 2) :
    ZMod p :=
  if h : w.1 = 0 then 0 else c (w.1.pred h) (objUncast f' w.2.1, layerUn w.2.2)

theorem readsSet_rows12 : ReadsSet (rowsOff f' 0) (readRows12 p f') (liftRows12 p f') := by
  intro y c
  constructor
  · rintro rfl a ha
    have ha0 : a.1 ≠ 0 := (mem_filter.mp ha).2
    obtain ⟨a1, a2, a3⟩ := a
    simp only [liftRows12, ha0, ↓reduceDIte, readRows12, Fin.succ_pred, objCast_objUncast,
      layerFin_layerUn]
  · intro h
    funext i q
    have := h (i.succ, objCast f' q.1, layerFin q.2)
      (mem_filter.mpr ⟨mem_univ _, Fin.succ_ne_zero i⟩)
    simp only [liftRows12, Fin.succ_ne_zero, ↓reduceDIte, Fin.pred_succ, objUncast_objCast,
      layerUn_layerFin] at this
    exact this

theorem tail_rows12F_eq :
    ((lam2 (tailFieldLaws p hne) .F f').map
      fun y => (rows0 y : Fin 3 → f'.Obj × ZMod 2 → ZMod p)).map (fun ω (i : Fin 2) => ω i.succ) =
      (graphLaw (graphF f') (hne.two .F (toFType f'))).map (readRows12 p f') := by
  unfold lam2
  rw [map_map', map_map']
  rfl

theorem tail_rows12E_eq :
    ((lam2 (tailFieldLaws p hne) .E f').map
      fun y => (rows0 y : Fin 3 → f'.Obj × ZMod 2 → ZMod p)).map (fun ω (i : Fin 2) => ω i.succ) =
      (graphLaw (graphE f') (hne.two .E (toFType f'))).map (readRows12 p f') := by
  unfold lam2
  rw [map_map', map_map']
  rfl

/-- **The column sums of the fold kernel of the tail rows**: at every prime `p ≥ P₄`, under Weil's
bound, on the support of `ν^b`, `ρ^{-144} ≤ (T_F^b)^* 𝟙 (y) ≤ ρ^{144}`. -/
theorem tail_kone'_bounds (hW : WeilBound (ZMod p)) (hp : P4 ≤ p)
    (h : RowHyp0 (lam2 (tailFieldLaws p hne)) f') (b : f'.Obj × ZMod 2 → ZMod p)
    (hb : (rowD0 (lam2 (tailFieldLaws p hne)) f' h).nu.weight b ≠ 0)
    (y : f'.Obj × ZMod 2 → ZMod p)
    (hy : ((rowD0 (lam2 (tailFieldLaws p hne)) f' h).nub b).weight y ≠ 0) :
    (countRho p ^ 144)⁻¹ ≤ kone' ((rowD0 (lam2 (tailFieldLaws p hne)) f' h).nub b)
        ((rowD0 (lam2 (tailFieldLaws p hne)) f' h).TF b) y ∧
      kone' ((rowD0 (lam2 (tailFieldLaws p hne)) f' h).nub b)
        ((rowD0 (lam2 (tailFieldLaws p hne)) f' h).TF b) y ≤ countRho p ^ 144 := by
  set πE := (lam2 (tailFieldLaws p hne) .E f').map
    fun z => (rows0 z : Fin 3 → f'.Obj × ZMod 2 → ZMod p) with hπE
  set πF := (lam2 (tailFieldLaws p hne) .F f').map
    fun z => (rows0 z : Fin 3 → f'.Obj × ZMod 2 → ZMod p) with hπF
  have hk := kone'_fold πE πF h.supp hb hy
  -- the numerator and the denominator as laws of the rows `1, 2`
  have hnum : ∑ x, πF.weight ![x, b, y] =
      ((graphLaw (graphF f') (hne.two .F (toFType f'))).map (readRows12 p f')).weight ![b, y] := by
    rw [← tail_rows12F_eq p hne f', map_succ_weight_eq_sum]
  have hden : (gamOf πE).weight ![y, b] =
      ((graphLaw (graphE f') (hne.two .E (toFType f'))).map (readRows12 p f')).weight ![b, y] := by
    rw [← tail_rows12E_eq p hne f', map_succ_weight_eq_sum, gamOf_weight_eq_sum]
    exact sum_congr rfl fun x _ => piE_swap02 πE h.exch y b x
  have hg : (gamOf πE).weight ![y, b] ≠ 0 := by
    have e := gamOf_weight πE ![y, b]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one] at e
    rw [e]
    exact mul_ne_zero hb hy
  rw [hnum, hden] at hk
  rw [hden] at hg
  have := restriction_ratio_bounds p hW hp (card_row_vertices_le f') (graphF f') (graphE f')
    (hne.two .F (toFType f')) (hne.two .E (toFType f'))
    (fieldGraph_degree_two .F (toFType f')) (fieldGraph_degree_two .E (toFType f'))
    (readsSet_rows12 p f') (feasible_rowsOff_FE p f' (j := 0) (by decide)) ![b, y] hg
  have hk' : kone' ((rowD0 (lam2 (tailFieldLaws p hne)) f' h).nub b)
      ((rowD0 (lam2 (tailFieldLaws p hne)) f' h).TF b) y =
      ((graphLaw (graphF f') (hne.two .F (toFType f'))).map (readRows12 p f')).weight ![b, y] /
        ((graphLaw (graphE f') (hne.two .E (toFType f'))).map (readRows12 p f')).weight ![b, y] :=
    hk
  rw [hk']
  exact this

end RowsOneTwo

end Sarkozy.PartVLaws
