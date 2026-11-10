module

public import Sarkozy.Extraction.CollisionBound

@[expose] public section

/-!
# Ordered coincidences, II: several coincidences and the natural bound
(`lem:oct24-collision`(b), (d), (e))

`paper/sections/16_extraction.tex`, `lem:oct24-collision`(b), (d), (e), with
`eq:oct24-collision` and `eq:collision-natural`; the definitions, (a) and (c) are in
`Sarkozy.Extraction.CollisionBound`, whose formal setting and normalization are used here: an
operator `T` on `L²(μ)` with kernel `K` relative to `μ ⊗ μ` is represented by its matrix
`K(x, x')/|𝓘⁺|` on `𝓘⁺ × 𝓘⁺`, and `OpBound 𝓘⁺ 𝓘⁺ (K/|𝓘⁺|) D` is `‖T‖ ≤ D`. `WeilBound F` is
Weil's theorem (`thm:weil`(a)), the only hypothesis from outside the paper.

Definitions: `collisionXi` (`Ξ = 2^{Δ⁺/2} q⁻¹ ∑_{i,j} a_{ij}`), `collisionKernel2` (`K_coll` on
the pairs with at least two common labels), `collisionD2` (`D_{≥2}`), `collisionKernelColl`
(`K_coll`), `collisionDord` (`D_ord`), `collisionDnat` (`D_nat`).

## Results

* (b) `collision_rowSum2_le`: `E_{x' ∼ μ}[K_coll,≥2(x, x')] ≤ D_{≥2}` for every injective `x`;
  `collision_opBound2`: `‖T_coll,≥2‖ ≤ D_{≥2}`.
* (d) `collisionD1_le`, `collisionD2_le` (the coarse forms) and `collision_opBound_natural`
  (`eq:collision-natural`: `‖T_coll‖ ≤ D_nat`); `collision_opBound_natural_specData` for
  spectral data.
* (e) `collision_opBound_inf'` (the minimum of finitely many valid bounds is a bound), with the
  bounds `collision_opBound_sum` (`D_1 + D_{≥2}`), `collision_opBound_tailForm` (the same with
  the tail of (c), via `collisionD2_le_tail`), `collision_opBound_ord` (`D_ord`) and
  `collision_opBound_natural` (`D_nat`); the endpoint monotonicity `collisionD1_endpoint`
  (`D_1/r²`), `collisionD2_endpoint` (`D_{≥2}/r⁴`), `collisionDord_endpoint`,
  `collisionDnat_endpoint` (`D_ord/r²`, `D_nat/r²`) and `collision_tail_endpoint` (the tail
  over `r⁴`): with the orders fixed, at every real `q ≥ P` the quantity is at most its value at
  `P` (`r² = 1/q`). These are proved directly (each count error is nonincreasing in `q`, and
  `q(e^{c/q} - 1 - c/q)` is nonincreasing by convexity of `exp`), not through the calculus of
  `lem:majorant`.

## Proofs

As in the paper. A stratum `(I, ψ)` is labelled by `coverRow_seq_upper` in the order "`I`
first, then the order `π_k`" (`collisionOrdI`), with the one-step sums of
`collision_oneStep_gen`, and `|𝓘⁺|` is bounded below along the same order
(`collision_card_lower_gen`); this replaces the paper's `|𝓘⁺| ≥ p^n 2^{-|E(G⁺)|} L_int` and
the identity `∑ t⁰ = |E(G⁺)| - e(I)`, and the factor `2^{e(I)}` appears as
`2^{∑_{v ∈ I} t'_v}` with `2 ∑_{v ∈ I} t'_v ≤ |I| Δ⁺` (`collision_handshake`). The count
`∑_{|I| = k} ∑_ψ ∏ a_{l,ψ(l)} ≤ (∑ a)^k/k!` is `collision_sum_strata` (from
`collision_esymm_le`); the strata are indexed by `I` and all maps `ψ : I → U⁺`
(`collisionKernel2_le_sum`), the non-injective ones contributing nonnegative extra terms.

## Deviations

* As in `Sarkozy.Extraction.CollisionBound`: coarse errors only; only `e_{d⁰_i}(p, n) < 1` is
  used (`collision_opBound_natural_specData` assumes `e_Δ(p, 2n) < 1`); `x` injective; any
  `n ≥ |U⁺|`; `Inj_p(G⁺) ≠ ∅` a hypothesis.
* In (e) the endpoint statements are for all real `q ≥ P > 0` (the paper: primes `p ≥ P > 1`),
  assuming `e_{d⁰_i}(P, n) < 1` (the paper: `e_Δ(P, 2n) < 1`); the tail statement assumes
  `k₀ ≥ 2` and `Ξ < k₀ + 1` at `P`.
-/

open scoped BigOperators
open Finset

namespace Sarkozy.Extraction

open Sarkozy.Labellings

/-! ## The coarse form of `D_1` (`lem:oct24-collision`(d)) -/

section CoarseD1

variable {U : Type*} [Fintype U] [DecidableEq U]

/-- `t^{ij}_ℓ ≤ d_ℓ = d⁰_ℓ + r_ℓ`. -/
theorem collisionT_le (G : OrientedGraph U) (ς : U → U → ℤ) (ord : U → U → U → ℕ)
    {i j ℓ : U} (hℓ : ℓ ≠ i) : collisionT G ς ord i j ℓ ≤ rowsDeg0 G ℓ + collisionR ς ℓ := by
  rw [← collision_t_eq G ς ord hℓ]
  have := coverRow_nbrCount_le G (coverRowEarlier univ (collisionOrd ord i j) ℓ) ℓ
  omega

/-- **`lem:oct24-collision`(d)**, the `D_1` half: for all orders,
`D_1 ≤ Υ L_int⁻¹ q⁻¹ ∑_{i,j} a_{ij}`. -/
theorem collisionD1_le (G : OrientedGraph U) (ς : U → U → ℤ) (ord : U → U → U → ℕ) {q : ℝ}
    (hq : 0 < q) {n : ℕ} (hS1 : ∀ v, coarseError (rowsDeg0 G v) q n < 1) :
    collisionD1 G ς ord q n ≤
      collisionUps G ς q n * (q * collisionLint G q n)⁻¹ * ∑ i, ∑ j, collisionA G ς i j := by
  have hn2 : (0 : ℝ) ≤ 2 * n := by positivity
  have hLpos : 0 < collisionLint G q n := prod_pos fun v _ => by linarith [hS1 v]
  have hc : 0 ≤ (q * collisionLint G q n)⁻¹ := inv_nonneg.mpr (mul_pos hq hLpos).le
  have he0 : ∀ t, 0 ≤ coarseError t q (2 * n) := fun t => coarseError_nonneg hn2 t
  have hP : ∀ i j, ∏ ℓ ∈ univ.erase i, (1 + coarseError (collisionT G ς ord i j ℓ) q (2 * n)) ≤
      collisionUps G ς q n := by
    intro i j
    calc ∏ ℓ ∈ univ.erase i, (1 + coarseError (collisionT G ς ord i j ℓ) q (2 * n))
        ≤ ∏ ℓ ∈ univ.erase i, (1 + coarseError (rowsDeg0 G ℓ + collisionR ς ℓ) q (2 * n)) :=
          prod_le_prod₀ (fun ℓ _ => by linarith [he0 (collisionT G ς ord i j ℓ)])
            (fun ℓ hℓ => by
              linarith [coarseError_mono (q := q) hn2
                (collisionT_le G ς ord (j := j) (mem_erase.mp hℓ).1)])
      _ ≤ (1 + coarseError (rowsDeg0 G i + collisionR ς i) q (2 * n)) *
            ∏ ℓ ∈ univ.erase i, (1 + coarseError (rowsDeg0 G ℓ + collisionR ς ℓ) q (2 * n)) :=
          le_mul_of_one_le_left (prod_nonneg fun ℓ _ => by linarith [he0 (rowsDeg0 G ℓ +
            collisionR ς ℓ)]) (by linarith [he0 (rowsDeg0 G i + collisionR ς i)])
      _ = collisionUps G ς q n := by
          unfold collisionUps
          rw [mul_prod_erase univ (fun ℓ => 1 + coarseError (rowsDeg0 G ℓ + collisionR ς ℓ) q
            (2 * n)) (mem_univ i)]
  unfold collisionD1
  rw [mul_comm (collisionUps G ς q n), mul_assoc]
  refine mul_le_mul_of_nonneg_left ?_ hc
  rw [mul_sum]
  refine sum_le_sum fun i _ => ?_
  rw [mul_sum]
  refine sum_le_sum fun j _ => ?_
  have ha : 0 ≤ collisionA G ς i j := by unfold collisionA; positivity
  calc collisionA G ς i j * ∏ ℓ ∈ univ.erase i,
        (1 + coarseError (collisionT G ς ord i j ℓ) q (2 * n))
      ≤ collisionA G ς i j * collisionUps G ς q n := mul_le_mul_of_nonneg_left (hP i j) ha
    _ = _ := mul_comm _ _

end CoarseD1

/-! ## At least two coincidences (`lem:oct24-collision`(b)) -/

section Multi

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {U : Type*} [Fintype U] [DecidableEq U]

/-- The order of a stratum with coincident set `I`: `I` first, then `U⁺ \ I`, each in the order
`p` (the paper's `π_k`; the order inside `I` is irrelevant). -/
def collisionOrdI (p : U → ℕ) (I : Finset U) : U → ℕ :=
  fun v => if v ∈ I then p v else p v + (univ.sup p + 1)

theorem collisionOrdI_injOn (p : U → ℕ) (hp : Function.Injective p) (I C : Finset U) :
    Set.InjOn (collisionOrdI p I) C := by
  intro a _ b _ h
  unfold collisionOrdI at h
  have ha := le_sup (f := p) (mem_univ a)
  have hb := le_sup (f := p) (mem_univ b)
  by_cases haI : a ∈ I <;> by_cases hbI : b ∈ I <;>
    simp only [haI, hbI, ↓reduceIte] at h
  · exact hp h
  · omega
  · omega
  · exact hp (by omega)

theorem collision_earlierI_sub (p : U → ℕ) (I : Finset U) (v : U) :
    coverRowEarlier univ (collisionOrdI p I) v ⊆ I ∪ univ.filter fun u => p u < p v := by
  intro u hu
  have hlt := (mem_filter.mp hu).2
  unfold collisionOrdI at hlt
  rw [mem_union, mem_filter]
  by_cases huI : u ∈ I
  · exact Or.inl huI
  · right
    refine ⟨mem_univ _, ?_⟩
    by_cases hvI : v ∈ I <;> simp only [huI, hvI, ↓reduceIte] at hlt
    · have := le_sup (f := p) (mem_univ u)
      omega
    · omega

theorem collision_I_sub_earlier (p : U → ℕ) (I : Finset U) {v : U} (hv : v ∉ I) :
    I ⊆ coverRowEarlier univ (collisionOrdI p I) v := by
  intro u hu
  refine mem_filter.mpr ⟨mem_univ _, ?_⟩
  unfold collisionOrdI
  have := le_sup (f := p) (mem_univ u)
  simp only [hu, hv, ↓reduceIte]
  omega

theorem collision_earlierI_of_mem (p : U → ℕ) (I : Finset U) {v u : U} (hv : v ∈ I)
    (hu : u ∈ coverRowEarlier univ (collisionOrdI p I) v) : u ∈ I ∧ p u < p v := by
  have hlt := (mem_filter.mp hu).2
  unfold collisionOrdI at hlt
  by_cases huI : u ∈ I <;> simp only [huI, hv, ↓reduceIte] at hlt
  · exact ⟨huI, hlt⟩
  · have := le_sup (f := p) (mem_univ v)
    omega

/-- The number `μ_v` of merges at `v ∉ I`: labelled neighbours `u ∈ I` of `v` with
`ψ(u) ∈ N(v)`. -/
def collisionMuI (G : OrientedGraph U) (ς : U → U → ℤ) (p : U → ℕ) (I : Finset U) (ψ : U → U)
    (v : U) : ℕ :=
  (((coverRowEarlier univ (collisionOrdI p I) v).filter fun u => (u, v) ∈ G.E ∨ (v, u) ∈ G.E).filter
    fun u => u ∈ I ∧ ψ u ∈ rowsN ς v).card

/-- The weights of the stratum `(I, ψ)`. -/
noncomputable def collisionPhiI (ς : U → U → ℤ) (p : U → ℕ) (x : U → F) (I : Finset U)
    (ψ : U → U) (v : U) (y : U → F) : ℝ :=
  if v ∈ I then (if y v = x (ψ v) then collisionW ς x v (y v) else 0)
  else if (∀ l ∈ I, y l = x (ψ l)) ∧ (∀ u ∈ coverRowEarlier univ (collisionOrdI p I) v,
      u ∉ I → y u ∉ univ.image x) ∧ y v ∉ univ.image x
    then collisionW ς x v (y v) else 0

/-- The one-step bounds of the stratum `(I, ψ)` with `|I| ≤ k`. -/
noncomputable def collisionMI (G : OrientedGraph U) (ς : U → U → ℤ) (p : U → ℕ) (I : Finset U)
    (ψ : U → U) (q : ℝ) (n k : ℕ) (v : U) : ℝ :=
  if v ∈ I then 2 ^ (collisionR ς v - if ψ v ∈ rowsN ς v then 1 else 0)
  else q * (2 : ℝ)⁻¹ ^ nbrCount G (coverRowEarlier univ (collisionOrdI p I) v) v *
    2 ^ collisionMuI G ς p I ψ v *
    (1 + coarseError (min (collisionR ς v + rowsDeg0 G v) (collisionR ς v + collisionB G p v + k))
      q (2 * n))

theorem collisionPhiI_nonneg (ς : U → U → ℤ) (p : U → ℕ) (x : U → F) (I : Finset U)
    (ψ : U → U) (v : U) (y : U → F) : 0 ≤ collisionPhiI ς p x I ψ v y := by
  unfold collisionPhiI
  split_ifs <;> first | exact collisionW_nonneg ς x v _ | exact le_rfl

theorem collisionMI_nonneg (G : OrientedGraph U) (ς : U → U → ℤ) (p : U → ℕ) (I : Finset U)
    (ψ : U → U) {q : ℝ} (hq : 0 ≤ q) (n k : ℕ) (v : U) : 0 ≤ collisionMI G ς p I ψ q n k v := by
  unfold collisionMI
  have := coarseError_nonneg (q := q) (by positivity : (0 : ℝ) ≤ 2 * n)
    (min (collisionR ς v + rowsDeg0 G v) (collisionR ς v + collisionB G p v + k))
  by_cases hv : v ∈ I
  · rw [ite_eq_left hv]
    positivity
  · rw [ite_eq_right hv]
    exact mul_nonneg (by positivity) (by linarith)

/-- **The stratum `(I, ψ)`, `|I| ≤ k`** (proof of `lem:oct24-collision`(b)): labelling `I` first
and the other vertices in the order `p = π_k`,
`∑_{x' ∈ 𝓘⁺ in the stratum} K_coll(x, x') ≤ ∏_v M_v`. -/
theorem collision_stratumI_le (hW : WeilBound F) (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1) (p : U → ℕ) (hp : Function.Injective p)
    (x : U → F) (hx : Function.Injective x) (n : ℕ) (I : Finset U) (ψ : U → U) {k : ℕ}
    (hk : I.card ≤ k) :
    ∑ y ∈ injLabellings F G,
        (if (∀ l ∈ I, y l = x (ψ l)) ∧ (∀ v, v ∉ I → y v ∉ univ.image x) then
          collisionKernel ς x y else 0) ≤
      ∏ v, collisionMI G ς p I ψ (Fintype.card F) n k v := by
  set X : Finset F := univ.image x with hX
  set ord' := collisionOrdI p I with hord'
  have hinj := collisionOrdI_injOn p hp I univ
  have hq0 : (0 : ℝ) ≤ Fintype.card F := Nat.cast_nonneg _
  have hloc : ∀ b ∈ (univ : Finset U), ∀ y y' : U → F,
      (∀ a ∈ (univ : Finset U), ord' a ≤ ord' b → y a = y' a) →
        collisionPhiI ς p x I ψ b y = collisionPhiI ς p x I ψ b y' := by
    intro b _ y y' h
    have e3 : y b = y' b := h b (mem_univ _) le_rfl
    unfold collisionPhiI
    by_cases hbI : b ∈ I
    · simp only [hbI, ↓reduceIte, e3]
    · have e1 : ∀ l ∈ I, y l = y' l := fun l hl => h l (mem_univ _)
        (mem_filter.mp (collision_I_sub_earlier p I hbI hl)).2.le
      have e2 : ∀ u ∈ coverRowEarlier univ ord' b, y u = y' u :=
        fun u hu => h u (mem_univ _) (mem_filter.mp hu).2.le
      simp only [hbI, ↓reduceIte]
      refine if_congr ?_ (by rw [e3]) rfl
      rw [e3]
      constructor
      · rintro ⟨h1, h2, h4⟩
        exact ⟨fun l hl => (e1 l hl) ▸ h1 l hl, fun u hu huI => (e2 u hu) ▸ h2 u hu huI, h4⟩
      · rintro ⟨h1, h2, h4⟩
        exact ⟨fun l hl => (e1 l hl).symm ▸ h1 l hl,
          fun u hu huI => (e2 u hu).symm ▸ h2 u hu huI, h4⟩
  have hstep : ∀ b ∈ (univ : Finset U), ∀ x' : U → F,
      Feasible F G (coverRowEarlier univ ord' b) x' →
        ∑ c ∈ vertexAdmissible G (coverRowEarlier univ ord' b) x' b,
          collisionPhiI ς p x I ψ b (Function.update x' b c) ≤
            collisionMI G ς p I ψ (Fintype.card F) n k b := by
    intro b _ x' hx'
    by_cases hbI : b ∈ I
    · have hupd : ∀ c, collisionPhiI ς p x I ψ b (Function.update x' b c) =
          if c = x (ψ b) then collisionW ς x b c else 0 := by
        intro c
        unfold collisionPhiI
        simp only [hbI, ↓reduceIte, Function.update_self]
      rw [sum_congr rfl fun c _ => hupd c]
      have hle : ∑ c ∈ vertexAdmissible G (coverRowEarlier univ ord' b) x' b,
          (if c = x (ψ b) then collisionW ς x b c else 0) ≤ collisionW ς x b (x (ψ b)) := by
        rw [sum_ite_eq']
        split_ifs
        · exact le_rfl
        · exact collisionW_nonneg ς x b _
      unfold collisionMI
      rw [ite_eq_left hbI]
      exact hle.trans (collisionW_at_le ς x b (ψ b))
    · have hu : ∀ c, ∀ u ∈ coverRowEarlier univ ord' b, Function.update x' b c u = x' u := by
        intro c u hu
        have hub : u ≠ b := by
          rintro rfl
          exact lt_irrefl _ (mem_filter.mp hu).2
        exact Function.update_of_ne hub _ _
      have hl : ∀ c, ∀ l ∈ I, Function.update x' b c l = x' l := by
        intro c l hlI
        have hlb : l ≠ b := by
          rintro rfl
          exact hbI hlI
        exact Function.update_of_ne hlb _ _
      have hupd : ∀ c, collisionPhiI ς p x I ψ b (Function.update x' b c) =
          if ((∀ l ∈ I, x' l = x (ψ l)) ∧ ∀ u ∈ coverRowEarlier univ ord' b, u ∉ I →
            x' u ∉ X) ∧ c ∉ X then collisionW ς x b c else 0 := by
        intro c
        unfold collisionPhiI
        simp only [hbI, ↓reduceIte]
        refine if_congr ?_ (by rw [Function.update_self]) rfl
        rw [Function.update_self]
        constructor
        · rintro ⟨h1, h2, h4⟩
          exact ⟨⟨fun l hlI => (hl c l hlI) ▸ h1 l hlI,
            fun u huE huI => (hu c u huE) ▸ h2 u huE huI⟩, h4⟩
        · rintro ⟨⟨h1, h2⟩, h4⟩
          exact ⟨fun l hlI => (hl c l hlI).symm ▸ h1 l hlI,
            fun u huE huI => (hu c u huE).symm ▸ h2 u huE huI, h4⟩
      rw [sum_congr rfl fun c _ => hupd c]
      by_cases hcond : (∀ l ∈ I, x' l = x (ψ l)) ∧
          ∀ u ∈ coverRowEarlier univ ord' b, u ∉ I → x' u ∉ X
      · have hc' : ∀ c, (if ((∀ l ∈ I, x' l = x (ψ l)) ∧ ∀ u ∈ coverRowEarlier univ ord' b,
            u ∉ I → x' u ∉ X) ∧ c ∉ X then collisionW ς x b c else 0) =
              if c ∉ X then collisionW ς x b c else 0 := by
          intro c
          by_cases hcX : c ∈ X
          · rw [ite_eq_right (fun h => h.2 hcX), ite_eq_right (fun h => h hcX)]
          · rw [ite_eq_left ⟨hcond, hcX⟩, ite_eq_left hcX]
        rw [sum_congr rfl fun c _ => hc' c, ← sum_filter]
        have h := collision_oneStep_gen hW G ς hς x hx (coverRowEarlier univ ord' b) b x' hx' I ψ
          (fun u _ huI => hcond.1 u huI) hcond.2 (n' := 2 * (n : ℝ)) (by positivity)
        refine h.trans ?_
        unfold collisionMI
        rw [ite_eq_right hbI]
        -- the number of distinct roots is at most `t^{(k)}_b`
        have ht0 : nbrCount G (coverRowEarlier univ ord' b) b ≤
            min (rowsDeg0 G b) (collisionB G p b + k) := by
          refine le_min (coverRow_nbrCount_le G _ b) ?_
          unfold nbrCount collisionB
          calc ((coverRowEarlier univ ord' b).filter
                fun u => (u, b) ∈ G.E ∨ (b, u) ∈ G.E).card
              ≤ (I ∪ (rowsAdj G b ∩ univ.filter fun u => p u < p b)).card := by
                refine card_le_card fun u hu => ?_
                have hu1 := (mem_filter.mp hu).1
                have hu2 := (mem_filter.mp hu).2
                rcases mem_union.mp (collision_earlierI_sub p I b hu1) with h | h
                · exact mem_union_left _ h
                · refine mem_union_right _ (mem_inter.mpr ⟨?_, h⟩)
                  simp only [rowsAdj, mem_filter, mem_univ, true_and]
                  exact hu2
            _ ≤ I.card + (rowsAdj G b ∩ univ.filter fun u => p u < p b).card := card_union_le _ _
            _ ≤ (rowsAdj G b ∩ univ.filter fun u => p u < p b).card + k := by omega
        have hroots : nbrCount G (coverRowEarlier univ ord' b) b + collisionR ς b -
            collisionMuI G ς p I ψ b ≤
              min (collisionR ς b + rowsDeg0 G b) (collisionR ς b + collisionB G p b + k) := by
          have := le_min_iff.mp ht0
          refine le_min ?_ ?_ <;> omega
        have hmono := coarseError_mono (q := (Fintype.card F : ℝ))
          (by positivity : (0 : ℝ) ≤ 2 * n) hroots
        have hpos : (0 : ℝ) ≤ Fintype.card F * (2 : ℝ)⁻¹ ^
            nbrCount G (coverRowEarlier univ ord' b) b * 2 ^ collisionMuI G ς p I ψ b := by
          positivity
        unfold collisionMuI at hmono hpos ⊢
        exact mul_le_mul_of_nonneg_left (by linarith) hpos
      · simp only [hcond, false_and, ↓reduceIte, sum_const_zero]
        exact collisionMI_nonneg G ς p I ψ hq0 n k b
  have hK : ∀ y : U → F, Feasible F G univ y → (extCount G univ y : ℝ) ≤ 1 := by
    intro y hy
    rw [extCount_univ G hy, Nat.cast_one]
  have hfe : Feasible F G (univ \ univ) (fun _ => (0 : F)) := by
    rw [Finset.sdiff_self]
    exact ⟨by simp, by simp⟩
  have hseq := coverRow_seq_upper G hinj (collisionPhiI ς p x I ψ)
    (collisionMI G ς p I ψ (Fintype.card F) n k) 1
    (fun b y => collisionPhiI_nonneg ς p x I ψ b y)
    (fun b => collisionMI_nonneg G ς p I ψ hq0 n k b) zero_le_one hloc hstep hK
    (univ : Finset U).card univ rfl subset_rfl (fun _ _ b' _ hb' => absurd (mem_univ b') hb')
    (fun _ => (0 : F)) hfe
  rw [one_mul, Finset.sdiff_self, coverRowExtSum_empty] at hseq
  refine le_trans (sum_le_sum fun y _ => ?_) hseq
  split_ifs with h1
  · rw [collisionKernel_eq_prod]
    refine le_of_eq (prod_congr rfl fun v _ => ?_)
    unfold collisionPhiI
    by_cases hvI : v ∈ I
    · rw [ite_eq_left hvI, ite_eq_left (h1.1 v hvI)]
    · rw [ite_eq_right hvI, ite_eq_left ⟨h1.1, fun u _ huI => h1.2 u huI, h1.2 v hvI⟩]
  · exact prod_nonneg fun v _ => collisionPhiI_nonneg ς p x I ψ v y

omit [Field F] [Fintype F] [DecidableEq F] in
/-- The merges of a stratum: `∑_{v ∉ I} μ_v ≤ ∑_{l ∈ I} mg(ψ(l), l)`. -/
theorem collision_sum_muI_le (G : OrientedGraph U) (ς : U → U → ℤ) (p : U → ℕ) (I : Finset U)
    (ψ : U → U) :
    ∑ v ∈ univ.filter (fun v => v ∉ I), collisionMuI G ς p I ψ v ≤
      ∑ l ∈ I, rowsMg G ς (ψ l) l := by
  have h1 : ∀ v, collisionMuI G ς p I ψ v ≤
      ∑ u ∈ I, if ((u, v) ∈ G.E ∨ (v, u) ∈ G.E) ∧ ψ u ∈ rowsN ς v then 1 else 0 := by
    intro v
    unfold collisionMuI
    rw [← card_filter]
    refine card_le_card fun u hu => ?_
    simp only [mem_filter] at hu ⊢
    exact ⟨hu.2.1, hu.1.2, hu.2.2⟩
  calc ∑ v ∈ univ.filter (fun v => v ∉ I), collisionMuI G ς p I ψ v
      ≤ ∑ v, collisionMuI G ς p I ψ v := sum_le_sum_of_subset (filter_subset _ _)
    _ ≤ ∑ v, ∑ u ∈ I, if ((u, v) ∈ G.E ∨ (v, u) ∈ G.E) ∧ ψ u ∈ rowsN ς v then 1 else 0 :=
        sum_le_sum fun v _ => h1 v
    _ = ∑ u ∈ I, ∑ v, if ((u, v) ∈ G.E ∨ (v, u) ∈ G.E) ∧ ψ u ∈ rowsN ς v then 1 else 0 :=
        sum_comm
    _ = ∑ l ∈ I, rowsMg G ς (ψ l) l := by
        refine sum_congr rfl fun u _ => ?_
        rw [← card_filter]
        unfold rowsMg rowsAdj
        rw [filter_filter]
        congr 1
        ext v
        simp only [mem_filter, mem_univ, true_and]
        constructor
        · rintro ⟨h1, h2⟩
          exact ⟨h1.symm, h2⟩
        · rintro ⟨h1, h2⟩
          exact ⟨h1.symm, h2⟩

omit [Field F] [Fintype F] [DecidableEq F] in
/-- **Edges inside `I`**: with `I` labelled first, the earlier neighbours of the vertices of `I`
number `e(I) ≤ |I| Δ⁺ / 2`; in the form `2 ∑_{v ∈ I} t'_v ≤ |I| Δ⁺`. -/
theorem collision_handshake (G : OrientedGraph U) (p : U → ℕ) (I : Finset U) :
    2 * ∑ v ∈ I, nbrCount G (coverRowEarlier univ (collisionOrdI p I) v) v ≤
      I.card * collisionDeltaPlus G := by
  set T : U → U → ℕ := fun u v =>
    if p u < p v ∧ ((u, v) ∈ G.E ∨ (v, u) ∈ G.E) then 1 else 0 with hT
  have h1 : ∀ v ∈ I, nbrCount G (coverRowEarlier univ (collisionOrdI p I) v) v ≤ ∑ u ∈ I, T u v := by
    intro v hv
    unfold nbrCount
    rw [hT, ← card_filter]
    refine card_le_card fun u hu => ?_
    have hu1 := (mem_filter.mp hu).1
    have hu2 := (mem_filter.mp hu).2
    obtain ⟨huI, hlt⟩ := collision_earlierI_of_mem p I hv hu1
    exact mem_filter.mpr ⟨huI, hlt, hu2⟩
  have hsym : ∑ v ∈ I, ∑ u ∈ I, T u v = ∑ v ∈ I, ∑ u ∈ I, T v u := sum_comm
  have h2 : ∀ v ∈ I, ∑ u ∈ I, (T u v + T v u) ≤ rowsDeg0 G v := by
    intro v _
    calc ∑ u ∈ I, (T u v + T v u)
        ≤ ∑ u, (if (u, v) ∈ G.E ∨ (v, u) ∈ G.E then 1 else 0) := by
          refine (sum_le_sum fun u _ => ?_).trans (sum_le_sum_of_subset (subset_univ I))
          simp only [hT]
          by_cases ha : (u, v) ∈ G.E ∨ (v, u) ∈ G.E
          · have ha' : (v, u) ∈ G.E ∨ (u, v) ∈ G.E := ha.symm
            simp only [ha, ha', and_true, ↓reduceIte]
            split_ifs <;> omega
          · have ha' : ¬((v, u) ∈ G.E ∨ (u, v) ∈ G.E) := fun h => ha h.symm
            simp [ha, ha']
      _ = rowsDeg0 G v := by
          unfold rowsDeg0 rowsAdj
          rw [card_filter]
  calc 2 * ∑ v ∈ I, nbrCount G (coverRowEarlier univ (collisionOrdI p I) v) v
      ≤ 2 * ∑ v ∈ I, ∑ u ∈ I, T u v := by
        have := sum_le_sum h1
        omega
    _ = ∑ v ∈ I, ∑ u ∈ I, (T u v + T v u) := by
        rw [two_mul]
        nth_rewrite 2 [hsym]
        rw [← sum_add_distrib]
        exact sum_congr rfl fun v _ => sum_add_distrib.symm
    _ ≤ ∑ v ∈ I, rowsDeg0 G v := sum_le_sum h2
    _ ≤ ∑ _v ∈ I, collisionDeltaPlus G := sum_le_sum fun v _ => le_sup (f := rowsDeg0 G) (mem_univ v)
    _ = I.card * collisionDeltaPlus G := by rw [sum_const, smul_eq_mul]

omit [Fintype U] [DecidableEq U] in
/-- `P^{m+1} + (m+1) a P^m ≤ (P + a)^{m+1}` for `P, a ≥ 0`. -/
theorem collision_bernoulli {P a : ℝ} (hP : 0 ≤ P) (ha : 0 ≤ a) :
    ∀ m : ℕ, P ^ (m + 1) + (m + 1) * a * P ^ m ≤ (P + a) ^ (m + 1)
  | 0 => by simp
  | m + 1 => by
      have ih := collision_bernoulli hP ha m
      have h1 : 0 ≤ P ^ m := pow_nonneg hP m
      have h2 : 0 ≤ (m + 1 : ℝ) * a * a * P ^ m := by positivity
      calc P ^ (m + 1 + 1) + ((m + 1 : ℕ) + 1 : ℝ) * a * P ^ (m + 1)
          = (P ^ (m + 1) + (m + 1) * a * P ^ m) * P + a * P ^ (m + 1) := by push_cast; ring
        _ ≤ (P + a) ^ (m + 1) * P + a * (P + a) ^ (m + 1) := by
            have h3 : P ^ (m + 1) ≤ (P + a) ^ (m + 1) := pow_le_pow_left₀ hP (by linarith) _
            nlinarith
        _ = (P + a) ^ (m + 1 + 1) := by ring

omit [Fintype U] in
/-- `∑_{|J| = k, J ⊆ S} ∏_{l ∈ J} A_l ≤ (∑_{l ∈ S} A_l)^k / k!` for `A ≥ 0`. -/
theorem collision_esymm_le (A : U → ℝ) (hA : ∀ l, 0 ≤ A l) (S : Finset U) :
    ∀ k : ℕ, ∑ J ∈ S.powersetCard k, ∏ l ∈ J, A l ≤ (∑ l ∈ S, A l) ^ k / (k.factorial : ℝ) := by
  induction S using Finset.induction_on with
  | empty =>
    intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    · rw [powersetCard_eq_empty.mpr (by simpa using hk), sum_empty, sum_empty,
        zero_pow hk.ne', zero_div]
  | insert a S haS ih =>
    intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    have hP : 0 ≤ ∑ l ∈ S, A l := sum_nonneg fun l _ => hA l
    have hdisj : Disjoint (S.powersetCard (m + 1)) ((S.powersetCard m).image (insert a)) := by
      rw [disjoint_left]
      intro J hJ hJ'
      obtain ⟨J', _, rfl⟩ := mem_image.mp hJ'
      exact haS ((mem_powersetCard.mp hJ).1 (mem_insert_self a J'))
    have hinj : Set.InjOn (insert a) (S.powersetCard m : Set (Finset U)) := by
      intro J hJ J' hJ' h
      have hJa : a ∉ J := fun h' => haS ((mem_powersetCard.mp hJ).1 h')
      have hJ'a : a ∉ J' := fun h' => haS ((mem_powersetCard.mp hJ').1 h')
      rw [← erase_insert hJa, ← erase_insert hJ'a, h]
    rw [powersetCard_succ_insert haS, sum_union hdisj, sum_image hinj, sum_insert haS]
    have hins : ∑ J ∈ S.powersetCard m, ∏ l ∈ insert a J, A l =
        A a * ∑ J ∈ S.powersetCard m, ∏ l ∈ J, A l := by
      rw [mul_sum]
      refine sum_congr rfl fun J hJ => ?_
      rw [prod_insert (fun h' => haS ((mem_powersetCard.mp hJ).1 h'))]
    rw [hins]
    have hb := collision_bernoulli hP (hA a) m
    have hfm : ((m + 1).factorial : ℝ) = (m + 1) * m.factorial := by
      rw [Nat.factorial_succ]
      push_cast
      ring
    have hfpos : (0 : ℝ) < m.factorial := by exact_mod_cast Nat.factorial_pos m
    calc ∑ J ∈ S.powersetCard (m + 1), ∏ l ∈ J, A l + A a * ∑ J ∈ S.powersetCard m, ∏ l ∈ J, A l
        ≤ (∑ l ∈ S, A l) ^ (m + 1) / ((m + 1).factorial : ℝ) +
            A a * ((∑ l ∈ S, A l) ^ m / (m.factorial : ℝ)) :=
          add_le_add (ih (m + 1)) (mul_le_mul_of_nonneg_left (ih m) (hA a))
      _ = ((∑ l ∈ S, A l) ^ (m + 1) + (m + 1) * A a * (∑ l ∈ S, A l) ^ m) /
            ((m + 1).factorial : ℝ) := by
          rw [hfm]
          field_simp
      _ ≤ (A a + ∑ l ∈ S, A l) ^ (m + 1) / ((m + 1).factorial : ℝ) := by
          refine div_le_div_of_nonneg_right ?_ (by positivity)
          rw [add_comm (A a)]
          exact hb

/-- **One stratum `(I, ψ)`, normalized** (proof of `lem:oct24-collision`(b)): with `k = |I|`
and the order `π_k`, the stratum sum of `K_coll(x, ·)` is at most
`L_int⁻¹ Υ_k q^{-k} 2^{kΔ⁺/2} ∏_{l ∈ I} a_{l, ψ(l)} · |𝓘⁺|`. -/
theorem collision_stratumI_ratio (hW : WeilBound F) (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1) (π : ℕ → U → ℕ)
    (hπ : ∀ k, Function.Injective (π k)) (x : U → F) (hx : Function.Injective x) {n : ℕ}
    (hn : Fintype.card U ≤ n) (hS1 : ∀ v, coarseError (rowsDeg0 G v) (Fintype.card F) n < 1)
    (I : Finset U) (ψ : U → U) :
    ∑ y ∈ injLabellings F G,
        (if (∀ l ∈ I, y l = x (ψ l)) ∧ (∀ v, v ∉ I → y v ∉ univ.image x) then
          collisionKernel ς x y else 0) ≤
      (collisionLint G (Fintype.card F) n)⁻¹ * collisionUpsK G ς π (Fintype.card F) n I.card *
        ((Fintype.card F : ℝ)⁻¹ ^ I.card * Real.sqrt 2 ^ (I.card * collisionDeltaPlus G) *
          ∏ l ∈ I, collisionA G ς l (ψ l)) * (injLabellings F G).card := by
  set q : ℝ := (Fintype.card F : ℝ) with hq
  have hq1 : (1 : ℝ) ≤ q := Nat.one_le_cast.mpr Fintype.card_pos
  have hq0 : (0 : ℝ) < q := by linarith
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  set k := I.card with hk
  set p := π k with hp
  set o := collisionOrdI p I with ho
  set t' : U → ℕ := fun v => nbrCount G (coverRowEarlier univ o v) v with ht'
  set eK : U → ℝ := fun v => coarseError (collisionTk G ς π k v) q (2 * n) with heK
  have het : ∀ v, coarseError (t' v) q n ≤ coarseError (rowsDeg0 G v) q n :=
    fun v => coarseError_mono hn0 (coverRow_nbrCount_le G _ v)
  have het1 : ∀ v, 0 < 1 - coarseError (t' v) q n := fun v => by linarith [het v, hS1 v]
  have heK0 : ∀ v, 0 ≤ eK v := fun v => coarseError_nonneg (by positivity : (0 : ℝ) ≤ 2 * n) _
  have hstr := collision_stratumI_le hW G ς hς p (hπ k) x hx n I ψ (le_refl k)
  have hlow := collision_card_lower_gen hW G o (collisionOrdI_injOn p (hπ k) I univ) hn hS1
  set ℓf : U → ℝ := fun v => q / 2 ^ t' v * (1 - coarseError (t' v) q n) with hℓf
  set num : U → ℝ := fun v => if v ∈ I then
      2 ^ (collisionR ς v - if ψ v ∈ rowsN ς v then 1 else 0) * 2 ^ t' v * q⁻¹
    else 2 ^ collisionMuI G ς p I ψ v * (1 + eK v) with hnum
  -- `M_v = (num_v / (1 - e_{t'_v})) ℓ_v`
  have hM : ∀ v, collisionMI G ς p I ψ q n k v = num v / (1 - coarseError (t' v) q n) * ℓf v := by
    intro v
    have h1 := (het1 v).ne'
    unfold collisionMI
    by_cases hv : v ∈ I
    · rw [ite_eq_left hv]
      simp only [hnum, hℓf, hv, ↓reduceIte]
      field_simp
    · rw [ite_eq_right hv]
      simp only [hnum, hℓf, hv, ↓reduceIte, heK, collisionTk, inv_pow]
      field_simp
      simp only [ht', hp, ho]
      ring
  have hprodM : ∏ v, collisionMI G ς p I ψ q n k v =
      (∏ v, num v) / (∏ v, (1 - coarseError (t' v) q n)) * ∏ v, ℓf v := by
    rw [prod_congr rfl fun v _ => hM v, prod_mul_distrib, prod_div_distrib]
  have hLle : collisionLint G q n ≤ ∏ v, (1 - coarseError (t' v) q n) :=
    prod_le_prod₀ (fun v _ => by linarith [hS1 v]) (fun v _ => by linarith [het v])
  have hLpos : 0 < collisionLint G q n := prod_pos fun v _ => by linarith [hS1 v]
  have hfilt : univ.filter (fun v => v ∈ I) = I := by
    ext v
    simp
  -- the numerator
  have hnum_le : ∏ v, num v ≤ collisionUpsK G ς π q n k *
      (q⁻¹ ^ k * Real.sqrt 2 ^ (k * collisionDeltaPlus G) * ∏ l ∈ I, collisionA G ς l (ψ l)) := by
    have hsplit : ∏ v, num v = (∏ v ∈ I, (2 ^ (collisionR ς v - if ψ v ∈ rowsN ς v then 1 else 0) *
        2 ^ t' v * q⁻¹)) * ∏ v ∈ univ.filter (fun v => v ∉ I),
          (2 ^ collisionMuI G ς p I ψ v * (1 + eK v)) := by
      simp only [hnum]
      rw [prod_ite, hfilt]
    have hI : ∏ v ∈ I, (2 ^ (collisionR ς v - if ψ v ∈ rowsN ς v then 1 else 0) * 2 ^ t' v * q⁻¹) =
        (∏ l ∈ I, (2 : ℝ) ^ (collisionR ς l - if ψ l ∈ rowsN ς l then 1 else 0)) *
          (2 : ℝ) ^ (∑ v ∈ I, t' v) * q⁻¹ ^ k := by
      rw [prod_mul_distrib, prod_mul_distrib, prod_const, ← prod_pow_eq_pow_sum]
    have hJ : ∏ v ∈ univ.filter (fun v => v ∉ I), (2 ^ collisionMuI G ς p I ψ v * (1 + eK v)) =
        (2 : ℝ) ^ (∑ v ∈ univ.filter (fun v => v ∉ I), collisionMuI G ς p I ψ v) *
          ∏ v ∈ univ.filter (fun v => v ∉ I), (1 + eK v) := by
      rw [prod_mul_distrib, prod_pow_eq_pow_sum]
    -- the pieces
    have hP1 : (2 : ℝ) ^ (∑ v ∈ I, t' v) ≤ Real.sqrt 2 ^ (k * collisionDeltaPlus G) := by
      have hh : 2 * ∑ v ∈ I, t' v ≤ k * collisionDeltaPlus G := collision_handshake G p I
      have h2 : (2 : ℝ) ^ (∑ v ∈ I, t' v) = Real.sqrt 2 ^ (2 * ∑ v ∈ I, t' v) := by
        rw [pow_mul, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      rw [h2]
      exact pow_le_pow_right₀ (Real.one_le_sqrt.mpr (by norm_num : (1 : ℝ) ≤ 2)) hh
    have hP2 : (2 : ℝ) ^ (∑ v ∈ univ.filter (fun v => v ∉ I), collisionMuI G ς p I ψ v) ≤
        ∏ l ∈ I, (2 : ℝ) ^ rowsMg G ς (ψ l) l := by
      rw [prod_pow_eq_pow_sum]
      exact pow_le_pow_right₀ (by norm_num) (collision_sum_muI_le G ς p I ψ)
    have hP3 : ∏ v ∈ univ.filter (fun v => v ∉ I), (1 + eK v) ≤ collisionUpsK G ς π q n k := by
      unfold collisionUpsK
      rw [← prod_filter_mul_prod_filter_not univ (fun v => v ∈ I)]
      refine le_mul_of_one_le_left (prod_nonneg fun v _ => by linarith [heK0 v]) ?_
      exact one_le_prod₀ fun v _ => by linarith [heK0 v]
    have hP4 : ∏ l ∈ I, collisionA G ς l (ψ l) =
        (∏ l ∈ I, (2 : ℝ) ^ (collisionR ς l - if ψ l ∈ rowsN ς l then 1 else 0)) *
          ∏ l ∈ I, (2 : ℝ) ^ rowsMg G ς (ψ l) l := by
      rw [← prod_mul_distrib]
      refine prod_congr rfl fun l _ => ?_
      unfold collisionA
      rw [pow_add]
    have hA0 : 0 ≤ ∏ l ∈ I, (2 : ℝ) ^ (collisionR ς l - if ψ l ∈ rowsN ς l then 1 else 0) := by
      positivity
    have hU0 : 0 ≤ ∏ v ∈ univ.filter (fun v => v ∉ I), (1 + eK v) :=
      prod_nonneg fun v _ => by linarith [heK0 v]
    have hq0' : 0 ≤ q⁻¹ ^ k := by positivity
    calc ∏ v, num v
        = ((∏ l ∈ I, (2 : ℝ) ^ (collisionR ς l - if ψ l ∈ rowsN ς l then 1 else 0)) *
            (2 : ℝ) ^ (∑ v ∈ I, t' v) * q⁻¹ ^ k) *
          ((2 : ℝ) ^ (∑ v ∈ univ.filter (fun v => v ∉ I), collisionMuI G ς p I ψ v) *
            ∏ v ∈ univ.filter (fun v => v ∉ I), (1 + eK v)) := by
          rw [hsplit, hI, hJ]
      _ ≤ ((∏ l ∈ I, (2 : ℝ) ^ (collisionR ς l - if ψ l ∈ rowsN ς l then 1 else 0)) *
            Real.sqrt 2 ^ (k * collisionDeltaPlus G) * q⁻¹ ^ k) *
          ((∏ l ∈ I, (2 : ℝ) ^ rowsMg G ς (ψ l) l) * collisionUpsK G ς π q n k) := by
          refine mul_le_mul ?_ ?_ (mul_nonneg (by positivity) hU0) (by positivity)
          · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hP1 hA0) hq0'
          · exact mul_le_mul hP2 hP3 hU0 (by positivity)
      _ = _ := by rw [hP4]; ring
  have hnum0 : 0 ≤ ∏ v, num v := prod_nonneg fun v _ => by
    by_cases hv : v ∈ I
    · simp only [hnum, hv, ↓reduceIte]
      positivity
    · simp only [hnum, hv, ↓reduceIte]
      exact mul_nonneg (by positivity) (by linarith [heK0 v])
  have hQpos : 0 < ∏ v, (1 - coarseError (t' v) q n) := prod_pos fun v _ => het1 v
  have hℓ0 : 0 ≤ ∏ v, ℓf v := prod_nonneg fun v _ => mul_nonneg (by positivity) (het1 v).le
  have hC0 : 0 ≤ (collisionLint G q n)⁻¹ * collisionUpsK G ς π q n k *
      (q⁻¹ ^ k * Real.sqrt 2 ^ (k * collisionDeltaPlus G) * ∏ l ∈ I, collisionA G ς l (ψ l)) := by
    have hU : 0 ≤ collisionUpsK G ς π q n k :=
      prod_nonneg fun v _ => by linarith [heK0 v]
    have hA : 0 ≤ ∏ l ∈ I, collisionA G ς l (ψ l) :=
      prod_nonneg fun l _ => by unfold collisionA; positivity
    exact mul_nonneg (mul_nonneg (inv_nonneg.mpr hLpos.le) hU) (by positivity)
  calc _ ≤ ∏ v, collisionMI G ς p I ψ q n k v := hstr
    _ = (∏ v, num v) / (∏ v, (1 - coarseError (t' v) q n)) * ∏ v, ℓf v := hprodM
    _ ≤ (∏ v, num v) / collisionLint G q n * ∏ v, ℓf v := by
        refine mul_le_mul_of_nonneg_right ?_ hℓ0
        exact div_le_div_of_nonneg_left hnum0 hLpos hLle
    _ ≤ (collisionLint G q n)⁻¹ * collisionUpsK G ς π q n k *
          (q⁻¹ ^ k * Real.sqrt 2 ^ (k * collisionDeltaPlus G) * ∏ l ∈ I, collisionA G ς l (ψ l)) *
          ∏ v, ℓf v := by
        refine mul_le_mul_of_nonneg_right ?_ hℓ0
        rw [div_eq_inv_mul, mul_assoc]
        exact mul_le_mul_of_nonneg_left hnum_le (inv_nonneg.mpr hLpos.le)
    _ ≤ _ := mul_le_mul_of_nonneg_left hlow hC0

/-- `Ξ = 2^{Δ⁺/2} q⁻¹ ∑_{i,j} a_{ij}`. -/
noncomputable def collisionXi (G : OrientedGraph U) (ς : U → U → ℤ) (q : ℝ) : ℝ :=
  Real.sqrt 2 ^ collisionDeltaPlus G * q⁻¹ * ∑ i, ∑ j, collisionA G ς i j

/-- The kernel of `T_coll,≥2`: `K_coll` on the pairs with at least two common labels. -/
noncomputable def collisionKernel2 (ς : U → U → ℤ) (x x' : U → F) : ℝ :=
  if 2 ≤ collisionCommon x x' then collisionKernel ς x x' else 0

/-- `D_{≥2} = L_int⁻¹ ∑_{k=2}^{|U⁺|} Υ_k Ξ^k/k!` (`eq:oct24-collision`). -/
noncomputable def collisionD2 (G : OrientedGraph U) (ς : U → U → ℤ) (π : ℕ → U → ℕ) (q : ℝ)
    (n : ℕ) : ℝ :=
  (collisionLint G q n)⁻¹ * ∑ k ∈ Icc 2 (Fintype.card U),
    collisionUpsK G ς π q n k * (collisionXi G ς q ^ k / (k.factorial : ℝ))

/-- A coincidence map `ψ : I → U⁺`, extended by the identity outside `I`. -/
def collisionExt (I : Finset U) (ψ : I → U) : U → U :=
  fun u => if h : u ∈ I then ψ ⟨u, h⟩ else u

omit [Field F] [Fintype F] [DecidableEq F] [Fintype U] in
theorem collisionExt_coe (I : Finset U) (ψ : I → U) (l : I) : collisionExt I ψ l = ψ l := by
  unfold collisionExt
  simp

omit [DecidableEq U] in
theorem collisionKernel2_nonneg (ς : U → U → ℤ) (x x' : U → F) :
    0 ≤ collisionKernel2 ς x x' := by
  unfold collisionKernel2
  split_ifs
  · exact collisionKernel_nonneg ς x x'
  · exact le_rfl

/-- Every pair with at least two common labels lies in a stratum `(I, ψ)`, `|I| ≥ 2`: `I` the
set of coincident `x'`-vertices and `x'_l = x_{ψ(l)}`. -/
theorem collisionKernel2_le_sum (ς : U → U → ℤ) (x y : U → F) (hy : Function.Injective y) :
    collisionKernel2 ς x y ≤ ∑ k ∈ Icc 2 (Fintype.card U),
      ∑ I ∈ (univ : Finset U).powersetCard k, ∑ ψ : (I → U),
        (if (∀ l ∈ I, y l = x (collisionExt I ψ l)) ∧ (∀ v, v ∉ I → y v ∉ univ.image x) then
          collisionKernel ς x y else 0) := by
  have hterm : ∀ (I : Finset U) (ψ : I → U), 0 ≤
      (if (∀ l ∈ I, y l = x (collisionExt I ψ l)) ∧ (∀ v, v ∉ I → y v ∉ univ.image x) then
        collisionKernel ς x y else 0) := fun I ψ => by
    split_ifs
    · exact collisionKernel_nonneg ς x y
    · exact le_rfl
  have hterm2 : ∀ I : Finset U, 0 ≤ ∑ ψ : (I → U),
      (if (∀ l ∈ I, y l = x (collisionExt I ψ l)) ∧ (∀ v, v ∉ I → y v ∉ univ.image x) then
        collisionKernel ς x y else 0) := fun I => sum_nonneg fun ψ _ => hterm I ψ
  unfold collisionKernel2
  split_ifs with h2
  · set I₀ := univ.filter (fun i => y i ∈ univ.image x) with hI₀
    have hmem : ∀ l : I₀, ∃ j, x j = y l := fun l => by
      have := (mem_filter.mp l.2).2
      obtain ⟨j, -, hj⟩ := mem_image.mp this
      exact ⟨j, hj⟩
    let ψ₀ : I₀ → U := fun l => (hmem l).choose
    have hψ₀ : ∀ l : I₀, x (ψ₀ l) = y l := fun l => (hmem l).choose_spec
    have hcard : collisionCommon x y = I₀.card := by
      unfold collisionCommon
      have hset : univ.image x ∩ univ.image y = I₀.image y := by
        ext z
        simp only [mem_inter, mem_image, mem_univ, true_and, hI₀, mem_filter]
        constructor
        · rintro ⟨⟨j, hj⟩, ⟨i, hi⟩⟩
          exact ⟨i, ⟨j, hj.trans hi.symm⟩, hi⟩
        · rintro ⟨i, ⟨j, hj⟩, hi⟩
          exact ⟨⟨j, hj.trans hi⟩, ⟨i, hi⟩⟩
      rw [hset, card_image_of_injective _ hy]
    have hcond : (∀ l ∈ I₀, y l = x (collisionExt I₀ ψ₀ l)) ∧
        (∀ v, v ∉ I₀ → y v ∉ univ.image x) := by
      refine ⟨fun l hl => ?_, fun v hv hmem' => hv (mem_filter.mpr ⟨mem_univ _, hmem'⟩)⟩
      rw [show l = ((⟨l, hl⟩ : I₀) : U) from rfl, collisionExt_coe]
      exact (hψ₀ ⟨l, hl⟩).symm
    have hk : I₀.card ∈ Icc 2 (Fintype.card U) := mem_Icc.mpr ⟨hcard ▸ h2, card_le_univ _⟩
    have hI : I₀ ∈ (univ : Finset U).powersetCard I₀.card :=
      mem_powersetCard.mpr ⟨subset_univ _, rfl⟩
    calc collisionKernel ς x y
        = (if (∀ l ∈ I₀, y l = x (collisionExt I₀ ψ₀ l)) ∧ (∀ v, v ∉ I₀ → y v ∉ univ.image x)
            then collisionKernel ς x y else 0) := (ite_eq_left hcond).symm
      _ ≤ ∑ ψ : (I₀ → U), (if (∀ l ∈ I₀, y l = x (collisionExt I₀ ψ l)) ∧
            (∀ v, v ∉ I₀ → y v ∉ univ.image x) then collisionKernel ς x y else 0) :=
          single_le_sum (f := fun ψ : (I₀ → U) => (if (∀ l ∈ I₀, y l = x (collisionExt I₀ ψ l)) ∧
            (∀ v, v ∉ I₀ → y v ∉ univ.image x) then collisionKernel ς x y else 0))
            (fun ψ _ => hterm I₀ ψ) (mem_univ ψ₀)
      _ ≤ ∑ I ∈ (univ : Finset U).powersetCard I₀.card, ∑ ψ : (I → U),
            (if (∀ l ∈ I, y l = x (collisionExt I ψ l)) ∧ (∀ v, v ∉ I → y v ∉ univ.image x) then
              collisionKernel ς x y else 0) :=
          single_le_sum (f := fun I : Finset U => ∑ ψ : (I → U),
            (if (∀ l ∈ I, y l = x (collisionExt I ψ l)) ∧ (∀ v, v ∉ I → y v ∉ univ.image x) then
              collisionKernel ς x y else 0)) (fun I _ => hterm2 I) hI
      _ ≤ _ := single_le_sum (f := fun k => ∑ I ∈ (univ : Finset U).powersetCard k,
            ∑ ψ : (I → U), (if (∀ l ∈ I, y l = x (collisionExt I ψ l)) ∧
              (∀ v, v ∉ I → y v ∉ univ.image x) then collisionKernel ς x y else 0))
            (fun k _ => sum_nonneg fun I _ => hterm2 I) hk
  · exact sum_nonneg fun k _ => sum_nonneg fun I _ => hterm2 I

omit [Field F] [Fintype F] [DecidableEq F] in
/-- `∑_{|I| = k} ∑_{ψ : I → U⁺} ∏_{l ∈ I} a_{l, ψ(l)} ≤ (∑_{i,j} a_{ij})^k / k!`: expanding
`(∑_{i,j} a_{ij})^k` counts every pair `(I, ψ)` with `|I| = k` exactly `k!` times. -/
theorem collision_sum_strata (G : OrientedGraph U) (ς : U → U → ℤ) (k : ℕ) :
    ∑ I ∈ (univ : Finset U).powersetCard k, ∑ ψ : (I → U),
        ∏ l ∈ I, collisionA G ς l (collisionExt I ψ l) ≤
      (∑ i, ∑ j, collisionA G ς i j) ^ k / (k.factorial : ℝ) := by
  have h1 : ∀ I : Finset U, ∑ ψ : (I → U), ∏ l ∈ I, collisionA G ς l (collisionExt I ψ l) =
      ∏ l ∈ I, ∑ j, collisionA G ς l j := by
    intro I
    rw [← prod_coe_sort I (fun l => ∑ j, collisionA G ς l j), Fintype.prod_sum]
    refine sum_congr rfl fun ψ _ => ?_
    rw [← prod_coe_sort I]
    refine prod_congr rfl fun l _ => ?_
    rw [collisionExt_coe]
  rw [sum_congr rfl fun I _ => h1 I]
  exact collision_esymm_le (fun l => ∑ j, collisionA G ς l j)
    (fun l => sum_nonneg fun j _ => by unfold collisionA; positivity) univ k

/-- **`lem:oct24-collision`(b), row sums**: for every injective `x`,
`E_{x' ∼ μ}[K_coll,≥2(x, x')] ≤ D_{≥2}`. -/
theorem collision_rowSum2_le (hW : WeilBound F) (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1) (hne : (injLabellings F G).Nonempty)
    {n : ℕ} (hn : Fintype.card U ≤ n)
    (hS1 : ∀ v, coarseError (rowsDeg0 G v) (Fintype.card F) n < 1) (π : ℕ → U → ℕ)
    (hπ : ∀ k, Function.Injective (π k)) (x : U → F) (hx : Function.Injective x) :
    (graphLaw G hne).expect (collisionKernel2 ς x) ≤ collisionD2 G ς π (Fintype.card F) n := by
  set q : ℝ := (Fintype.card F : ℝ) with hq
  set N : ℝ := ((injLabellings F G).card : ℝ) with hNdef
  rw [coverRow_expect_graphLaw]
  have hN : (0 : ℝ) < N := by
    rw [hNdef]
    exact_mod_cast card_pos.mpr hne
  have hLpos : 0 < collisionLint G q n := prod_pos fun v _ => by linarith [hS1 v]
  rw [div_le_iff₀ hN]
  set c : ℕ → ℝ := fun k => (collisionLint G q n)⁻¹ * collisionUpsK G ς π q n k *
    (q⁻¹ ^ k * Real.sqrt 2 ^ (k * collisionDeltaPlus G)) with hc
  have hc0 : ∀ k, 0 ≤ c k := fun k => by
    have hU : 0 ≤ collisionUpsK G ς π q n k := prod_nonneg fun v _ => by
      have := coarseError_nonneg (q := q) (by positivity : (0 : ℝ) ≤ 2 * n)
        (collisionTk G ς π k v)
      linarith
    exact mul_nonneg (mul_nonneg (inv_nonneg.mpr hLpos.le) hU) (by positivity)
  calc ∑ y ∈ injLabellings F G, collisionKernel2 ς x y
      ≤ ∑ y ∈ injLabellings F G, ∑ k ∈ Icc 2 (Fintype.card U),
          ∑ I ∈ (univ : Finset U).powersetCard k, ∑ ψ : (I → U),
            (if (∀ l ∈ I, y l = x (collisionExt I ψ l)) ∧ (∀ v, v ∉ I → y v ∉ univ.image x) then
              collisionKernel ς x y else 0) := by
        refine sum_le_sum fun y hy => collisionKernel2_le_sum ς x y fun a b h => ?_
        simp only [injLabellings, mem_filter, mem_univ, true_and] at hy
        exact hy.1 a (mem_univ _) b (mem_univ _) h
    _ = ∑ k ∈ Icc 2 (Fintype.card U), ∑ I ∈ (univ : Finset U).powersetCard k, ∑ ψ : (I → U),
          ∑ y ∈ injLabellings F G,
            (if (∀ l ∈ I, y l = x (collisionExt I ψ l)) ∧ (∀ v, v ∉ I → y v ∉ univ.image x) then
              collisionKernel ς x y else 0) := by
        rw [sum_comm]
        refine sum_congr rfl fun k _ => ?_
        rw [sum_comm]
        refine sum_congr rfl fun I _ => ?_
        rw [sum_comm]
    _ ≤ ∑ k ∈ Icc 2 (Fintype.card U), ∑ I ∈ (univ : Finset U).powersetCard k, ∑ ψ : (I → U),
          c k * (∏ l ∈ I, collisionA G ς l (collisionExt I ψ l)) * N := by
        refine sum_le_sum fun k _ => sum_le_sum fun I hI => sum_le_sum fun ψ _ => ?_
        have hIk : I.card = k := (mem_powersetCard.mp hI).2
        have h := collision_stratumI_ratio hW G ς hς π hπ x hx hn hS1 I (collisionExt I ψ)
        rw [hIk] at h
        refine h.trans (le_of_eq ?_)
        simp only [hc]
        ring
    _ = ∑ k ∈ Icc 2 (Fintype.card U), c k * N * (∑ I ∈ (univ : Finset U).powersetCard k,
          ∑ ψ : (I → U), ∏ l ∈ I, collisionA G ς l (collisionExt I ψ l)) := by
        refine sum_congr rfl fun k _ => ?_
        rw [mul_sum]
        refine sum_congr rfl fun I _ => ?_
        rw [mul_sum]
        refine sum_congr rfl fun ψ _ => ?_
        ring
    _ ≤ ∑ k ∈ Icc 2 (Fintype.card U), c k * N *
          ((∑ i, ∑ j, collisionA G ς i j) ^ k / (k.factorial : ℝ)) :=
        sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (collision_sum_strata G ς k)
          (mul_nonneg (hc0 k) hN.le)
    _ = collisionD2 G ς π q n * N := by
        unfold collisionD2 collisionXi
        rw [mul_sum, sum_mul]
        refine sum_congr rfl fun k _ => ?_
        simp only [hc]
        rw [mul_pow, mul_pow, ← pow_mul, mul_comm (collisionDeltaPlus G) k]
        ring

/-- **`lem:oct24-collision`(b)**: `‖T_coll,≥2‖ ≤ D_{≥2}` on `L²(μ)` (matrix normalization of
`collision_opBound`), by Schur's test. -/
theorem collision_opBound2 (hW : WeilBound F) (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1) (hanti : ∀ j k, ς k j = -ς j k)
    (hne : (injLabellings F G).Nonempty) {n : ℕ} (hn : Fintype.card U ≤ n)
    (hS1 : ∀ v, coarseError (rowsDeg0 G v) (Fintype.card F) n < 1) (π : ℕ → U → ℕ)
    (hπ : ∀ k, Function.Injective (π k)) :
    Sarkozy.Influence.OpBound (injLabellings F G) (injLabellings F G)
      (fun x x' => collisionKernel2 ς x x' / (injLabellings F G).card)
      (collisionD2 G ς π (Fintype.card F) n) := by
  have hN : (0 : ℝ) < (injLabellings F G).card := by exact_mod_cast card_pos.mpr hne
  have hsymm : ∀ x x' : U → F, collisionKernel2 ς x x' = collisionKernel2 ς x' x := by
    intro x x'
    unfold collisionKernel2
    rw [collisionCommon_symm, collisionKernel_symm ς hanti]
  have hrow : ∀ x ∈ injLabellings F G, ∑ x' ∈ injLabellings F G,
      collisionKernel2 ς x x' / (injLabellings F G).card ≤
        collisionD2 G ς π (Fintype.card F) n := by
    intro x hx
    have hxinj : Function.Injective x := fun a b h => by
      simp only [injLabellings, mem_filter, mem_univ, true_and] at hx
      exact hx.1 a (mem_univ _) b (mem_univ _) h
    have h := collision_rowSum2_le hW G ς hς hne hn hS1 π hπ x hxinj
    rw [coverRow_expect_graphLaw] at h
    rwa [← sum_div]
  have hcol : ∀ x' ∈ injLabellings F G, ∑ x ∈ injLabellings F G,
      collisionKernel2 ς x x' / (injLabellings F G).card ≤
        collisionD2 G ς π (Fintype.card F) n := by
    intro x' hx'
    calc ∑ x ∈ injLabellings F G, collisionKernel2 ς x x' / (injLabellings F G).card
        = ∑ x ∈ injLabellings F G, collisionKernel2 ς x' x / (injLabellings F G).card :=
          sum_congr rfl fun x _ => by rw [hsymm]
      _ ≤ _ := hrow x' hx'
  obtain ⟨x0, hx0⟩ := hne
  have hD : 0 ≤ collisionD2 G ς π (Fintype.card F) n :=
    le_trans (sum_nonneg fun x' _ => div_nonneg (collisionKernel2_nonneg ς x0 x') hN.le)
      (hrow x0 hx0)
  have h := Sarkozy.Influence.opBound_schur (R := injLabellings F G) (C := injLabellings F G)
    (fun x x' => div_nonneg (collisionKernel2_nonneg ς x x') hN.le) hD hD hrow hcol
  rwa [Real.sqrt_mul_self hD] at h

end Multi

/-! ## The coarse forms and the natural bound (`lem:oct24-collision`(d)) -/

section Natural

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {U : Type*} [Fintype U] [DecidableEq U]

/-- The kernel `K_coll`: `∏_{e ∈ E_×} (1 + χ_e)` on the pairs that share a label, `0`
elsewhere. -/
noncomputable def collisionKernelColl (ς : U → U → ℤ) (x x' : U → F) : ℝ :=
  if 1 ≤ collisionCommon x x' then collisionKernel ς x x' else 0

/-- The ordered single-coincidence bound `D_ord = D_1 + Υ L_int⁻¹ (e^Ξ - 1 - Ξ)`. -/
noncomputable def collisionDord (G : OrientedGraph U) (ς : U → U → ℤ) (ord : U → U → U → ℕ)
    (q : ℝ) (n : ℕ) : ℝ :=
  collisionD1 G ς ord q n + collisionUps G ς q n / collisionLint G q n *
    (Real.exp (collisionXi G ς q) - 1 - collisionXi G ς q)

/-- The natural bound `D_nat = (Υ/L_int)[q⁻¹ ∑_{i,j} a_{ij} + e^Ξ - 1 - Ξ]`
(`eq:collision-natural`). -/
noncomputable def collisionDnat (G : OrientedGraph U) (ς : U → U → ℤ) (q : ℝ) (n : ℕ) : ℝ :=
  collisionUps G ς q n / collisionLint G q n *
    (q⁻¹ * ∑ i, ∑ j, collisionA G ς i j + (Real.exp (collisionXi G ς q) - 1 - collisionXi G ς q))

omit [DecidableEq U] in
theorem collisionKernelColl_eq (ς : U → U → ℤ) (x x' : U → F) :
    collisionKernelColl ς x x' = collisionKernel1 ς x x' + collisionKernel2 ς x x' := by
  unfold collisionKernelColl collisionKernel1 collisionKernel2
  by_cases h0 : collisionCommon x x' = 0
  · simp [h0]
  · by_cases h1 : collisionCommon x x' = 1
    · simp [h1]
    · have h2 : 2 ≤ collisionCommon x x' := by omega
      have h1' : 1 ≤ collisionCommon x x' := by omega
      simp [h1, h2, h1']

/-- **`lem:oct24-collision`(d)**, the `D_{≥2}` half: for all orders,
`D_{≥2} ≤ Υ L_int⁻¹ (e^Ξ - 1 - Ξ)` (as `t^{(k)}_i ≤ d_i`, `Υ_k ≤ Υ`). -/
theorem collisionD2_le (G : OrientedGraph U) (ς : U → U → ℤ) (π : ℕ → U → ℕ) {q : ℝ}
    (hq : 0 < q) {n : ℕ} (hS1 : ∀ v, coarseError (rowsDeg0 G v) q n < 1) :
    collisionD2 G ς π q n ≤ collisionUps G ς q n / collisionLint G q n *
      (Real.exp (collisionXi G ς q) - 1 - collisionXi G ς q) := by
  have hn2 : (0 : ℝ) ≤ 2 * n := by positivity
  have hLpos : 0 < collisionLint G q n := prod_pos fun v _ => by linarith [hS1 v]
  have he0 : ∀ t, 0 ≤ coarseError t q (2 * n) := fun t => coarseError_nonneg hn2 t
  have hΞ : 0 ≤ collisionXi G ς q := by
    unfold collisionXi
    refine mul_nonneg (by positivity) (sum_nonneg fun i _ => sum_nonneg fun j _ => ?_)
    unfold collisionA
    positivity
  have hUk : ∀ k, collisionUpsK G ς π q n k ≤ collisionUps G ς q n := by
    intro k
    unfold collisionUpsK collisionUps
    refine prod_le_prod₀ (fun i _ => by linarith [he0 (collisionTk G ς π k i)]) fun i _ => ?_
    have ht : collisionTk G ς π k i ≤ rowsDeg0 G i + collisionR ς i := by
      unfold collisionTk
      omega
    linarith [coarseError_mono (q := q) hn2 ht]
  have hexp : ∑ k ∈ Icc 2 (Fintype.card U), collisionXi G ς q ^ k / (k.factorial : ℝ) ≤
      Real.exp (collisionXi G ς q) - 1 - collisionXi G ς q := by
    set N := Fintype.card U
    have hsub : Icc 2 N ⊆ Ico 2 (N + 2) := fun k hk => by
      rw [mem_Icc] at hk
      rw [mem_Ico]
      omega
    have hsplit := sum_range_add_sum_Ico (fun k => collisionXi G ς q ^ k / (k.factorial : ℝ))
      (show 2 ≤ N + 2 by omega)
    have hexpb := Real.sum_le_exp_of_nonneg hΞ (N + 2)
    have h2 : ∑ k ∈ range 2, collisionXi G ς q ^ k / (k.factorial : ℝ) =
        1 + collisionXi G ς q := by
      simp [sum_range_succ]
    have hle : ∑ k ∈ Icc 2 N, collisionXi G ς q ^ k / (k.factorial : ℝ) ≤
        ∑ k ∈ Ico 2 (N + 2), collisionXi G ς q ^ k / (k.factorial : ℝ) :=
      sum_le_sum_of_subset_of_nonneg hsub
        (fun k _ _ => div_nonneg (pow_nonneg hΞ k) (by positivity))
    have hexpb' : ∑ k ∈ range (N + 2), collisionXi G ς q ^ k / (k.factorial : ℝ) ≤
        Real.exp (collisionXi G ς q) := hexpb
    linarith
  unfold collisionD2
  have hLinv : 0 ≤ (collisionLint G q n)⁻¹ := inv_nonneg.mpr hLpos.le
  calc (collisionLint G q n)⁻¹ * ∑ k ∈ Icc 2 (Fintype.card U),
        collisionUpsK G ς π q n k * (collisionXi G ς q ^ k / (k.factorial : ℝ))
      ≤ (collisionLint G q n)⁻¹ * ∑ k ∈ Icc 2 (Fintype.card U),
          collisionUps G ς q n * (collisionXi G ς q ^ k / (k.factorial : ℝ)) := by
        refine mul_le_mul_of_nonneg_left (sum_le_sum fun k _ => ?_) hLinv
        exact mul_le_mul_of_nonneg_right (hUk k) (div_nonneg (pow_nonneg hΞ k) (by positivity))
    _ = (collisionLint G q n)⁻¹ * collisionUps G ς q n *
          ∑ k ∈ Icc 2 (Fintype.card U), collisionXi G ς q ^ k / (k.factorial : ℝ) := by
        rw [← mul_sum, mul_assoc]
    _ ≤ (collisionLint G q n)⁻¹ * collisionUps G ς q n *
          (Real.exp (collisionXi G ς q) - 1 - collisionXi G ς q) := by
        refine mul_le_mul_of_nonneg_left hexp (mul_nonneg hLinv ?_)
        unfold collisionUps
        exact prod_nonneg fun i _ => by linarith [he0 (rowsDeg0 G i + collisionR ς i)]
    _ = _ := by ring

theorem collisionD1_nonneg (G : OrientedGraph U) (ς : U → U → ℤ) (ord : U → U → U → ℕ)
    {q : ℝ} (hq : 0 < q) {n : ℕ} (hS1 : ∀ v, coarseError (rowsDeg0 G v) q n < 1) :
    0 ≤ collisionD1 G ς ord q n := by
  have hLpos : 0 < collisionLint G q n := prod_pos fun v _ => by linarith [hS1 v]
  unfold collisionD1
  refine mul_nonneg (inv_nonneg.mpr (mul_pos hq hLpos).le)
    (sum_nonneg fun i _ => sum_nonneg fun j _ => mul_nonneg ?_ (prod_nonneg fun ℓ _ => ?_))
  · unfold collisionA
    positivity
  · have := coarseError_nonneg (q := q) (by positivity : (0 : ℝ) ≤ 2 * n)
      (collisionT G ς ord i j ℓ)
    linarith

theorem collisionD2_nonneg (G : OrientedGraph U) (ς : U → U → ℤ) (π : ℕ → U → ℕ)
    {q : ℝ} (hq : 0 < q) {n : ℕ} (hS1 : ∀ v, coarseError (rowsDeg0 G v) q n < 1) :
    0 ≤ collisionD2 G ς π q n := by
  have hLpos : 0 < collisionLint G q n := prod_pos fun v _ => by linarith [hS1 v]
  have hΞ : 0 ≤ collisionXi G ς q := by
    unfold collisionXi
    refine mul_nonneg (by positivity) (sum_nonneg fun i _ => sum_nonneg fun j _ => ?_)
    unfold collisionA
    positivity
  unfold collisionD2
  refine mul_nonneg (inv_nonneg.mpr hLpos.le) (sum_nonneg fun k _ => mul_nonneg ?_
    (div_nonneg (pow_nonneg hΞ k) (by positivity)))
  unfold collisionUpsK
  exact prod_nonneg fun i _ => by
    have := coarseError_nonneg (q := q) (by positivity : (0 : ℝ) ≤ 2 * n) (collisionTk G ς π k i)
    linarith

/-- **`lem:oct24-collision`(d)**, the natural bound `eq:collision-natural`:
`‖T_coll‖ ≤ D_nat = (Υ/L_int)[q⁻¹ ∑_{i,j} a_{ij} + e^Ξ - 1 - Ξ]` on `L²(μ)` (matrix
normalization of `collision_opBound`), from `T_coll = T_coll,1 + T_coll,≥2`, (a), (b) and the
coarse forms of `D_1` and `D_{≥2}`, for any choices of the orders. -/
theorem collision_opBound_natural (hW : WeilBound F) (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1) (hanti : ∀ j k, ς k j = -ς j k)
    (hne : (injLabellings F G).Nonempty) {n : ℕ} (hn : Fintype.card U ≤ n)
    (hS1 : ∀ v, coarseError (rowsDeg0 G v) (Fintype.card F) n < 1) (ord : U → U → U → ℕ)
    (hord : ∀ i j, ∀ ℓ ℓ', ℓ ≠ i → ℓ' ≠ i → ord i j ℓ = ord i j ℓ' → ℓ = ℓ')
    (π : ℕ → U → ℕ) (hπ : ∀ k, Function.Injective (π k)) :
    Sarkozy.Influence.OpBound (injLabellings F G) (injLabellings F G)
      (fun x x' => collisionKernelColl ς x x' / (injLabellings F G).card)
      (collisionDnat G ς (Fintype.card F) n) := by
  have hq0 : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have h1 := collision_opBound hW G ς hς hanti hne hn hS1 ord hord
  have h2 := collision_opBound2 hW G ς hς hanti hne hn hS1 π hπ
  have hD1 := collisionD1_nonneg G ς ord hq0 hS1
  have hD2 := collisionD2_nonneg G ς π hq0 hS1
  have hsum := Sarkozy.Influence.OpBound.add h1 h2 hD1 hD2
  have heq : (fun (x x' : U → F) => collisionKernelColl ς x x' / (injLabellings F G).card) =
      (fun (x x' : U → F) => collisionKernel1 ς x x' / (injLabellings F G).card +
        collisionKernel2 ς x x' / (injLabellings F G).card) := by
    funext x x'
    rw [collisionKernelColl_eq, add_div]
  rw [heq]
  refine hsum.mono (add_nonneg hD1 hD2) ?_
  have hc1 := collisionD1_le G ς ord hq0 hS1
  have hc2 := collisionD2_le G ς π hq0 hS1
  have hL : 0 < collisionLint G (Fintype.card F) n := prod_pos fun v _ => by linarith [hS1 v]
  unfold collisionDnat
  have hrw : collisionUps G ς (Fintype.card F) n * ((Fintype.card F : ℝ) *
      collisionLint G (Fintype.card F) n)⁻¹ * ∑ i, ∑ j, collisionA G ς i j =
      collisionUps G ς (Fintype.card F) n / collisionLint G (Fintype.card F) n *
        ((Fintype.card F : ℝ)⁻¹ * ∑ i, ∑ j, collisionA G ς i j) := by
    field_simp
  rw [hrw] at hc1
  nlinarith [hc1, hc2]

/-- `‖T_coll‖ ≤ D_1 + D_{≥2}` (from (a), (b) and `T_coll = T_coll,1 + T_coll,≥2`). -/
theorem collision_opBound_sum (hW : WeilBound F) (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1) (hanti : ∀ j k, ς k j = -ς j k)
    (hne : (injLabellings F G).Nonempty) {n : ℕ} (hn : Fintype.card U ≤ n)
    (hS1 : ∀ v, coarseError (rowsDeg0 G v) (Fintype.card F) n < 1) (ord : U → U → U → ℕ)
    (hord : ∀ i j, ∀ ℓ ℓ', ℓ ≠ i → ℓ' ≠ i → ord i j ℓ = ord i j ℓ' → ℓ = ℓ')
    (π : ℕ → U → ℕ) (hπ : ∀ k, Function.Injective (π k)) :
    Sarkozy.Influence.OpBound (injLabellings F G) (injLabellings F G)
      (fun x x' => collisionKernelColl ς x x' / (injLabellings F G).card)
      (collisionD1 G ς ord (Fintype.card F) n + collisionD2 G ς π (Fintype.card F) n) := by
  have hq0 : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  have h1 := collision_opBound hW G ς hς hanti hne hn hS1 ord hord
  have h2 := collision_opBound2 hW G ς hς hanti hne hn hS1 π hπ
  have hsum := Sarkozy.Influence.OpBound.add h1 h2 (collisionD1_nonneg G ς ord hq0 hS1)
    (collisionD2_nonneg G ς π hq0 hS1)
  have heq : (fun (x x' : U → F) => collisionKernelColl ς x x' / (injLabellings F G).card) =
      (fun (x x' : U → F) => collisionKernel1 ς x x' / (injLabellings F G).card +
        collisionKernel2 ς x x' / (injLabellings F G).card) := by
    funext x x'
    rw [collisionKernelColl_eq, add_div]
  rw [heq]
  exact hsum

/-- `‖T_coll‖ ≤ D_ord = D_1 + Υ L_int⁻¹ (e^Ξ - 1 - Ξ)`, the ordered single-coincidence
bound of (e). -/
theorem collision_opBound_ord (hW : WeilBound F) (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1) (hanti : ∀ j k, ς k j = -ς j k)
    (hne : (injLabellings F G).Nonempty) {n : ℕ} (hn : Fintype.card U ≤ n)
    (hS1 : ∀ v, coarseError (rowsDeg0 G v) (Fintype.card F) n < 1) (ord : U → U → U → ℕ)
    (hord : ∀ i j, ∀ ℓ ℓ', ℓ ≠ i → ℓ' ≠ i → ord i j ℓ = ord i j ℓ' → ℓ = ℓ')
    (π : ℕ → U → ℕ) (hπ : ∀ k, Function.Injective (π k)) :
    Sarkozy.Influence.OpBound (injLabellings F G) (injLabellings F G)
      (fun x x' => collisionKernelColl ς x x' / (injLabellings F G).card)
      (collisionDord G ς ord (Fintype.card F) n) := by
  have hq0 : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  refine (collision_opBound_sum hW G ς hς hanti hne hn hS1 ord hord π hπ).mono
    (add_nonneg (collisionD1_nonneg G ς ord hq0 hS1) (collisionD2_nonneg G ς π hq0 hS1)) ?_
  unfold collisionDord
  linarith [collisionD2_le G ς π hq0 hS1]

/-- `D_{≥2}` with the tail of (c): for `2 ≤ k₀`, `Δ⁺ ≤ k₀` and `Ξ < k₀ + 1`,
`D_{≥2} ≤ L_int⁻¹ ∑_{2 ≤ k < k₀} Υ_k Ξ^k/k! + (Υ/L_int)(Ξ^{k₀}/k₀!)(1 - Ξ/(k₀ + 1))⁻¹`. -/
theorem collisionD2_le_tail (G : OrientedGraph U) (ς : U → U → ℤ) (π : ℕ → U → ℕ) {q : ℝ}
    (hq : 0 < q) {n : ℕ} (hS1 : ∀ v, coarseError (rowsDeg0 G v) q n < 1) {k₀ : ℕ}
    (h2 : 2 ≤ k₀) (hk₀ : collisionDeltaPlus G ≤ k₀) (hΞ : collisionXi G ς q < k₀ + 1) :
    collisionD2 G ς π q n ≤ (collisionLint G q n)⁻¹ * ∑ k ∈ Ico 2 k₀,
        collisionUpsK G ς π q n k * (collisionXi G ς q ^ k / (k.factorial : ℝ)) +
      collisionUps G ς q n / collisionLint G q n *
        (collisionXi G ς q ^ k₀ / (k₀.factorial : ℝ)) * (1 - collisionXi G ς q / (k₀ + 1))⁻¹ := by
  have hn2 : (0 : ℝ) ≤ 2 * n := by positivity
  have hLpos : 0 < collisionLint G q n := prod_pos fun v _ => by linarith [hS1 v]
  have hΞ0 : 0 ≤ collisionXi G ς q := by
    unfold collisionXi
    refine mul_nonneg (by positivity) (sum_nonneg fun i _ => sum_nonneg fun j _ => ?_)
    unfold collisionA
    positivity
  set f : ℕ → ℝ := fun k => collisionUpsK G ς π q n k * (collisionXi G ς q ^ k / (k.factorial : ℝ))
    with hf
  have hf0 : ∀ k, 0 ≤ f k := fun k => mul_nonneg (prod_nonneg fun i _ => by
    linarith [coarseError_nonneg hn2 (q := q) (collisionTk G ς π k i)])
    (div_nonneg (pow_nonneg hΞ0 k) (by positivity))
  set M := max k₀ (Fintype.card U + 1) with hM
  have hsub : Icc 2 (Fintype.card U) ⊆ Ico 2 M := fun k hk => by
    rw [mem_Icc] at hk
    rw [mem_Ico]
    omega
  have hle : ∑ k ∈ Icc 2 (Fintype.card U), f k ≤ ∑ k ∈ Ico 2 M, f k :=
    sum_le_sum_of_subset_of_nonneg hsub fun k _ _ => hf0 k
  have hsplit : ∑ k ∈ Ico 2 k₀, f k + ∑ k ∈ Ico k₀ M, f k = ∑ k ∈ Ico 2 M, f k :=
    sum_Ico_consecutive f h2 (le_max_left _ _)
  have htail := collision_tail_le G ς π (q := q) n hLpos hΞ0 hk₀ hΞ M
  unfold collisionD2
  have hLinv : 0 ≤ (collisionLint G q n)⁻¹ := inv_nonneg.mpr hLpos.le
  calc (collisionLint G q n)⁻¹ * ∑ k ∈ Icc 2 (Fintype.card U), f k
      ≤ (collisionLint G q n)⁻¹ * (∑ k ∈ Ico 2 k₀, f k + ∑ k ∈ Ico k₀ M, f k) := by
        rw [hsplit]
        exact mul_le_mul_of_nonneg_left hle hLinv
    _ = (collisionLint G q n)⁻¹ * ∑ k ∈ Ico 2 k₀, f k +
          (collisionLint G q n)⁻¹ * ∑ k ∈ Ico k₀ M, f k := by ring
    _ ≤ _ := add_le_add le_rfl htail

/-- `‖T_coll‖ ≤ D_1 + D_{≥2}` with the tail of (c) for `k ≥ k₀` (`2 ≤ k₀`, `Δ⁺ ≤ k₀`,
`Ξ < k₀ + 1`): one of the bounds whose minimum is taken in (e). -/
theorem collision_opBound_tailForm (hW : WeilBound F) (G : OrientedGraph U) (ς : U → U → ℤ)
    (hς : ∀ j k, ς j k = 0 ∨ ς j k = 1 ∨ ς j k = -1) (hanti : ∀ j k, ς k j = -ς j k)
    (hne : (injLabellings F G).Nonempty) {n : ℕ} (hn : Fintype.card U ≤ n)
    (hS1 : ∀ v, coarseError (rowsDeg0 G v) (Fintype.card F) n < 1) (ord : U → U → U → ℕ)
    (hord : ∀ i j, ∀ ℓ ℓ', ℓ ≠ i → ℓ' ≠ i → ord i j ℓ = ord i j ℓ' → ℓ = ℓ')
    (π : ℕ → U → ℕ) (hπ : ∀ k, Function.Injective (π k)) {k₀ : ℕ} (h2 : 2 ≤ k₀)
    (hk₀ : collisionDeltaPlus G ≤ k₀) (hΞ : collisionXi G ς (Fintype.card F) < k₀ + 1) :
    Sarkozy.Influence.OpBound (injLabellings F G) (injLabellings F G)
      (fun x x' => collisionKernelColl ς x x' / (injLabellings F G).card)
      (collisionD1 G ς ord (Fintype.card F) n +
        ((collisionLint G (Fintype.card F) n)⁻¹ * ∑ k ∈ Ico 2 k₀,
          collisionUpsK G ς π (Fintype.card F) n k *
            (collisionXi G ς (Fintype.card F) ^ k / (k.factorial : ℝ)) +
        collisionUps G ς (Fintype.card F) n / collisionLint G (Fintype.card F) n *
          (collisionXi G ς (Fintype.card F) ^ k₀ / (k₀.factorial : ℝ)) *
            (1 - collisionXi G ς (Fintype.card F) / (k₀ + 1))⁻¹)) := by
  have hq0 : (0 : ℝ) < Fintype.card F := by exact_mod_cast Fintype.card_pos
  refine (collision_opBound_sum hW G ς hς hanti hne hn hS1 ord hord π hπ).mono
    (add_nonneg (collisionD1_nonneg G ς ord hq0 hS1) (collisionD2_nonneg G ς π hq0 hS1)) ?_
  linarith [collisionD2_le_tail G ς π hq0 hS1 h2 hk₀ hΞ]

end Natural

/-! ## Minima and endpoint monotonicity (`lem:oct24-collision`(e)) -/

section Endpoint

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {U : Type*} [Fintype U] [DecidableEq U]

omit [Field F] [Fintype F] [DecidableEq F] [Fintype U] [DecidableEq U] in
/-- **`lem:oct24-collision`(e)**, minima: the minimum of finitely many valid bounds is a
bound. -/
theorem collision_opBound_inf' {ι : Type*} {R C : Finset (U → F)} {A : (U → F) → (U → F) → ℝ}
    {s : Finset ι} (hs : s.Nonempty) (Λ : ι → ℝ)
    (h : ∀ i ∈ s, Sarkozy.Influence.OpBound R C A (Λ i)) :
    Sarkozy.Influence.OpBound R C A (s.inf' hs Λ) := by
  obtain ⟨i, hi, he⟩ := s.exists_mem_eq_inf' hs Λ
  rw [he]
  exact h i hi

omit [Fintype U] [DecidableEq U] in
theorem collision_coarseH_nonneg (t : ℕ) : 0 ≤ coarseH t := by
  unfold coarseH
  rcases Nat.lt_or_ge t 2 with ht | ht
  · interval_cases t <;> norm_num
  · have h1 : (2 : ℝ) ≤ t := by exact_mod_cast ht
    have h2 : (0 : ℝ) ≤ (2 : ℝ)⁻¹ ^ t := by positivity
    linarith

omit [Fintype U] [DecidableEq U] in
/-- `e_t(q, n')` is nonincreasing in `q > 0` (a polynomial in `r = q^{-1/2}` with nonnegative
coefficients, `it:et:poly`). -/
theorem collision_coarseError_anti (t : ℕ) {n' : ℝ} (hn' : 0 ≤ n') {P q : ℝ} (hP : 0 < P)
    (hPq : P ≤ q) : coarseError t q n' ≤ coarseError t P n' := by
  unfold coarseError
  have hr : (Real.sqrt q)⁻¹ ≤ (Real.sqrt P)⁻¹ :=
    inv_anti₀ (Real.sqrt_pos.mpr hP) (Real.sqrt_le_sqrt hPq)
  have hr0 : 0 ≤ (Real.sqrt q)⁻¹ := by positivity
  have hh := collision_coarseH_nonneg t
  refine mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_left hr hh)
    (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hr0 hr 2) hn')) (by positivity)

omit [Fintype U] [DecidableEq U] in
theorem collision_prod_anti (s : Finset U) (t : U → ℕ) {n' : ℝ} (hn' : 0 ≤ n') {P q : ℝ}
    (hP : 0 < P) (hPq : P ≤ q) :
    ∏ i ∈ s, (1 + coarseError (t i) q n') ≤ ∏ i ∈ s, (1 + coarseError (t i) P n') :=
  prod_le_prod₀ (fun i _ => by linarith [coarseError_nonneg hn' (q := q) (t i)])
    (fun i _ => by linarith [collision_coarseError_anti (t i) hn' hP hPq])

theorem collision_Lint_mono (G : OrientedGraph U) {n : ℕ} {P q : ℝ} (hP : 0 < P) (hPq : P ≤ q)
    (hS1 : ∀ v, coarseError (rowsDeg0 G v) P n < 1) :
    0 < collisionLint G P n ∧ collisionLint G P n ≤ collisionLint G q n := by
  have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  refine ⟨prod_pos fun v _ => by linarith [hS1 v], prod_le_prod₀ (fun v _ => by
    linarith [hS1 v]) fun v _ => by
      linarith [collision_coarseError_anti (rowsDeg0 G v) hn0 hP hPq]⟩

omit [Fintype U] [DecidableEq U] in
/-- `q (e^{c/q} - 1 - c/q)` is nonincreasing in `q > 0` (convexity of `exp`). -/
theorem collision_expm_anti {c : ℝ} (hc : 0 ≤ c) {P q : ℝ} (hP : 0 < P) (hPq : P ≤ q) :
    q * (Real.exp (c / q) - 1 - c / q) ≤ P * (Real.exp (c / P) - 1 - c / P) := by
  have hq : 0 < q := lt_of_lt_of_le hP hPq
  rcases hc.eq_or_lt with rfl | hc'
  · simp
  set x := c / q with hx
  set y := c / P with hy
  have hx0 : 0 < x := div_pos hc' hq
  have hy0 : 0 < y := div_pos hc' hP
  have hxy : x ≤ y := div_le_div_of_nonneg_left hc hP hPq
  have ha0 : 0 ≤ x / y := (div_pos hx0 hy0).le
  have ha1 : x / y ≤ 1 := (div_le_one hy0).mpr hxy
  have hconv := convexOn_exp.2 (Set.mem_univ y) (Set.mem_univ 0) ha0 (by linarith : 0 ≤ 1 - x / y)
    (by ring)
  simp only [smul_eq_mul, mul_zero, add_zero, Real.exp_zero, mul_one] at hconv
  have hxy' : x / y * y = x := by field_simp
  rw [hxy'] at hconv
  -- `g(x) ≤ (x/y) g(y)`
  have hg : Real.exp x - 1 - x ≤ x / y * (Real.exp y - 1 - y) := by
    have : x / y * (Real.exp y - 1 - y) = x / y * Real.exp y + (1 - x / y) - 1 - x := by
      linear_combination (-1 : ℝ) * hxy'
    rw [this]
    linarith
  have hqx : q = c / x := by rw [hx]; field_simp
  have hPy : P = c / y := by rw [hy]; field_simp
  rw [hqx, hPy]
  calc c / x * (Real.exp x - 1 - x) ≤ c / x * (x / y * (Real.exp y - 1 - y)) :=
        mul_le_mul_of_nonneg_left hg (div_pos hc' hx0).le
    _ = c / y * (Real.exp y - 1 - y) := by field_simp

omit [Fintype U] [DecidableEq U] in
theorem collision_sq_mul_pow {c q' : ℝ} (hq' : 0 < q') (m : ℕ) :
    q' ^ 2 * (c / q') ^ (m + 2) = c ^ (m + 2) * q'⁻¹ ^ m := by
  have h1 : q' ^ 2 * q'⁻¹ ^ 2 = 1 := by rw [← mul_pow, mul_inv_cancel₀ hq'.ne', one_pow]
  rw [div_eq_mul_inv]
  calc q' ^ 2 * (c * q'⁻¹) ^ (m + 2) = c ^ (m + 2) * q'⁻¹ ^ m * (q' ^ 2 * q'⁻¹ ^ 2) := by ring
    _ = c ^ (m + 2) * q'⁻¹ ^ m := by rw [h1, mul_one]

/-- `Ξ = c/q` with `c = 2^{Δ⁺/2} ∑_{i,j} a_{ij} ≥ 0` independent of `q`. -/
theorem collisionXi_eq (G : OrientedGraph U) (ς : U → U → ℤ) (q : ℝ) :
    collisionXi G ς q = (Real.sqrt 2 ^ collisionDeltaPlus G * ∑ i, ∑ j, collisionA G ς i j) / q := by
  unfold collisionXi
  ring

theorem collision_c_nonneg (G : OrientedGraph U) (ς : U → U → ℤ) :
    0 ≤ Real.sqrt 2 ^ collisionDeltaPlus G * ∑ i, ∑ j, collisionA G ς i j :=
  mul_nonneg (by positivity) (sum_nonneg fun i _ => sum_nonneg fun j _ => by
    unfold collisionA; positivity)

/-- **`lem:oct24-collision`(e)** for `D_1`: with the orders fixed and `e_{d⁰_i}(P, n) < 1`,
`D_1/r² = q D_1` at every `q ≥ P` is at most its value at `P`. -/
theorem collisionD1_endpoint (G : OrientedGraph U) (ς : U → U → ℤ) (ord : U → U → U → ℕ)
    {n : ℕ} {P q : ℝ} (hP : 0 < P) (hPq : P ≤ q) (hS1 : ∀ v, coarseError (rowsDeg0 G v) P n < 1) :
    q * collisionD1 G ς ord q n ≤ P * collisionD1 G ς ord P n := by
  have hq : 0 < q := lt_of_lt_of_le hP hPq
  have hn2 : (0 : ℝ) ≤ 2 * n := by positivity
  obtain ⟨hLP, hLle⟩ := collision_Lint_mono G hP hPq hS1
  have hLq : 0 < collisionLint G q n := lt_of_lt_of_le hLP hLle
  have hS : ∀ q' : ℝ, 0 < q' → q' * collisionD1 G ς ord q' n = (collisionLint G q' n)⁻¹ *
      ∑ i, ∑ j, collisionA G ς i j *
        ∏ ℓ ∈ univ.erase i, (1 + coarseError (collisionT G ς ord i j ℓ) q' (2 * n)) := by
    intro q' hq'
    unfold collisionD1
    rw [mul_inv, ← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hq'.ne', one_mul]
  have hA0 : ∀ i j, 0 ≤ collisionA G ς i j := fun i j => by unfold collisionA; positivity
  have hT0 : ∀ i j ℓ, 0 ≤ 1 + coarseError (collisionT G ς ord i j ℓ) q (2 * n) := fun i j ℓ => by
    have := coarseError_nonneg hn2 (q := q) (collisionT G ς ord i j ℓ)
    linarith
  rw [hS q hq, hS P hP]
  refine mul_le_mul (inv_anti₀ hLP hLle) (sum_le_sum fun i _ => sum_le_sum fun j _ => ?_)
    (sum_nonneg fun i _ => sum_nonneg fun j _ => mul_nonneg (hA0 i j)
      (prod_nonneg fun ℓ _ => hT0 i j ℓ))
    (inv_nonneg.mpr hLP.le)
  exact mul_le_mul_of_nonneg_left (collision_prod_anti _ _ hn2 hP hPq) (hA0 i j)

/-- **`lem:oct24-collision`(e)** for `D_{≥2}`: `D_{≥2}/r⁴ = q² D_{≥2}` at `q ≥ P` is at most its
value at `P`. -/
theorem collisionD2_endpoint (G : OrientedGraph U) (ς : U → U → ℤ) (π : ℕ → U → ℕ)
    {n : ℕ} {P q : ℝ} (hP : 0 < P) (hPq : P ≤ q) (hS1 : ∀ v, coarseError (rowsDeg0 G v) P n < 1) :
    q ^ 2 * collisionD2 G ς π q n ≤ P ^ 2 * collisionD2 G ς π P n := by
  have hq : 0 < q := lt_of_lt_of_le hP hPq
  have hn2 : (0 : ℝ) ≤ 2 * n := by positivity
  obtain ⟨hLP, hLle⟩ := collision_Lint_mono G hP hPq hS1
  set c := Real.sqrt 2 ^ collisionDeltaPlus G * ∑ i, ∑ j, collisionA G ς i j with hc
  have hc0 : 0 ≤ c := collision_c_nonneg G ς
  -- `q'^2 Ξ(q')^k = c^k (q'⁻¹)^{k-2}` for `k ≥ 2`
  have hterm : ∀ q' : ℝ, 0 < q' → ∀ k ∈ Icc 2 (Fintype.card U),
      q' ^ 2 * collisionXi G ς q' ^ k = c ^ k * (q'⁻¹) ^ (k - 2) := by
    intro q' hq' k hk
    have hk2 : 2 ≤ k := (mem_Icc.mp hk).1
    rw [collisionXi_eq, ← hc]
    obtain ⟨m, rfl⟩ : ∃ m, k = m + 2 := ⟨k - 2, by omega⟩
    rw [Nat.add_sub_cancel]
    exact collision_sq_mul_pow hq' m
  have hS : ∀ q' : ℝ, 0 < q' → q' ^ 2 * collisionD2 G ς π q' n = (collisionLint G q' n)⁻¹ *
      ∑ k ∈ Icc 2 (Fintype.card U), collisionUpsK G ς π q' n k *
        (c ^ k * (q'⁻¹) ^ (k - 2) / (k.factorial : ℝ)) := by
    intro q' hq'
    unfold collisionD2
    rw [mul_left_comm, mul_sum]
    congr 1
    refine sum_congr rfl fun k hk => ?_
    rw [← hterm q' hq' k hk]
    ring
  rw [hS q hq, hS P hP]
  have hUk : ∀ k, collisionUpsK G ς π q n k ≤ collisionUpsK G ς π P n k := fun k =>
    collision_prod_anti univ (fun i => collisionTk G ς π k i) hn2 hP hPq
  have hinv : q⁻¹ ≤ P⁻¹ := inv_anti₀ hP hPq
  refine mul_le_mul (inv_anti₀ hLP hLle) (sum_le_sum fun k _ => ?_)
    (sum_nonneg fun k _ => mul_nonneg (prod_nonneg fun i _ => by
      linarith [coarseError_nonneg hn2 (q := q) (collisionTk G ς π k i)]) (by positivity))
    (inv_nonneg.mpr hLP.le)
  refine mul_le_mul (hUk k) ?_ (by positivity) (prod_nonneg fun i _ => by
    linarith [coarseError_nonneg hn2 (q := P) (collisionTk G ς π k i)])
  refine div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left ?_ (pow_nonneg hc0 k))
    (by positivity)
  exact pow_le_pow_left₀ (by positivity) hinv _

/-- `q Υ L⁻¹ (e^Ξ - 1 - Ξ)` is nonincreasing in `q`. -/
theorem collision_expPart_endpoint (G : OrientedGraph U) (ς : U → U → ℤ) {n : ℕ} {P q : ℝ}
    (hP : 0 < P) (hPq : P ≤ q) (hS1 : ∀ v, coarseError (rowsDeg0 G v) P n < 1) :
    q * (collisionUps G ς q n / collisionLint G q n *
        (Real.exp (collisionXi G ς q) - 1 - collisionXi G ς q)) ≤
      P * (collisionUps G ς P n / collisionLint G P n *
        (Real.exp (collisionXi G ς P) - 1 - collisionXi G ς P)) := by
  have hq : 0 < q := lt_of_lt_of_le hP hPq
  have hn2 : (0 : ℝ) ≤ 2 * n := by positivity
  obtain ⟨hLP, hLle⟩ := collision_Lint_mono G hP hPq hS1
  have hLq : 0 < collisionLint G q n := lt_of_lt_of_le hLP hLle
  have hc0 := collision_c_nonneg G ς
  have hU : collisionUps G ς q n ≤ collisionUps G ς P n :=
    collision_prod_anti univ (fun i => rowsDeg0 G i + collisionR ς i) hn2 hP hPq
  have hU0 : 0 ≤ collisionUps G ς q n := prod_nonneg fun i _ => by
    linarith [coarseError_nonneg hn2 (q := q) (rowsDeg0 G i + collisionR ς i)]
  have hg := collision_expm_anti hc0 hP hPq
  rw [collisionXi_eq, collisionXi_eq]
  have hg0 : 0 ≤ q * (Real.exp ((Real.sqrt 2 ^ collisionDeltaPlus G * ∑ i, ∑ j,
      collisionA G ς i j) / q) - 1 - (Real.sqrt 2 ^ collisionDeltaPlus G * ∑ i, ∑ j,
      collisionA G ς i j) / q) := by
    refine mul_nonneg hq.le ?_
    linarith [Real.add_one_le_exp ((Real.sqrt 2 ^ collisionDeltaPlus G * ∑ i, ∑ j,
      collisionA G ς i j) / q)]
  have hUL : collisionUps G ς q n / collisionLint G q n ≤
      collisionUps G ς P n / collisionLint G P n :=
    div_le_div₀ (hU0.trans hU) hU hLP hLle
  calc q * (collisionUps G ς q n / collisionLint G q n * (Real.exp ((Real.sqrt 2 ^
        collisionDeltaPlus G * ∑ i, ∑ j, collisionA G ς i j) / q) - 1 - (Real.sqrt 2 ^
        collisionDeltaPlus G * ∑ i, ∑ j, collisionA G ς i j) / q))
      = collisionUps G ς q n / collisionLint G q n * (q * (Real.exp ((Real.sqrt 2 ^
          collisionDeltaPlus G * ∑ i, ∑ j, collisionA G ς i j) / q) - 1 - (Real.sqrt 2 ^
          collisionDeltaPlus G * ∑ i, ∑ j, collisionA G ς i j) / q)) := by ring
    _ ≤ collisionUps G ς P n / collisionLint G P n * (P * (Real.exp ((Real.sqrt 2 ^
          collisionDeltaPlus G * ∑ i, ∑ j, collisionA G ς i j) / P) - 1 - (Real.sqrt 2 ^
          collisionDeltaPlus G * ∑ i, ∑ j, collisionA G ς i j) / P)) :=
        mul_le_mul hUL hg hg0 (div_nonneg (hU0.trans hU) hLP.le)
    _ = _ := by ring

/-- **`lem:oct24-collision`(e)** for `D_ord`: `D_ord/r² = q D_ord` at `q ≥ P` is at most its
value at `P`. -/
theorem collisionDord_endpoint (G : OrientedGraph U) (ς : U → U → ℤ) (ord : U → U → U → ℕ)
    {n : ℕ} {P q : ℝ} (hP : 0 < P) (hPq : P ≤ q) (hS1 : ∀ v, coarseError (rowsDeg0 G v) P n < 1) :
    q * collisionDord G ς ord q n ≤ P * collisionDord G ς ord P n := by
  unfold collisionDord
  rw [mul_add, mul_add]
  exact add_le_add (collisionD1_endpoint G ς ord hP hPq hS1)
    (collision_expPart_endpoint G ς hP hPq hS1)

/-- **`lem:oct24-collision`(e)** for `D_nat`: `D_nat/r² = q D_nat` at `q ≥ P` is at most its
value at `P`. -/
theorem collisionDnat_endpoint (G : OrientedGraph U) (ς : U → U → ℤ) {n : ℕ} {P q : ℝ}
    (hP : 0 < P) (hPq : P ≤ q) (hS1 : ∀ v, coarseError (rowsDeg0 G v) P n < 1) :
    q * collisionDnat G ς q n ≤ P * collisionDnat G ς P n := by
  have hq : 0 < q := lt_of_lt_of_le hP hPq
  have hn2 : (0 : ℝ) ≤ 2 * n := by positivity
  obtain ⟨hLP, hLle⟩ := collision_Lint_mono G hP hPq hS1
  have hU : collisionUps G ς q n ≤ collisionUps G ς P n :=
    collision_prod_anti univ (fun i => rowsDeg0 G i + collisionR ς i) hn2 hP hPq
  have hU0 : 0 ≤ collisionUps G ς q n := prod_nonneg fun i _ => by
    linarith [coarseError_nonneg hn2 (q := q) (rowsDeg0 G i + collisionR ς i)]
  have hUL : collisionUps G ς q n / collisionLint G q n ≤
      collisionUps G ς P n / collisionLint G P n :=
    div_le_div₀ (hU0.trans hU) hU hLP hLle
  have hA0 : 0 ≤ ∑ i, ∑ j, collisionA G ς i j :=
    sum_nonneg fun i _ => sum_nonneg fun j _ => by unfold collisionA; positivity
  have hsplit : ∀ q' : ℝ, 0 < q' → q' * collisionDnat G ς q' n =
      collisionUps G ς q' n / collisionLint G q' n * ∑ i, ∑ j, collisionA G ς i j +
        q' * (collisionUps G ς q' n / collisionLint G q' n *
          (Real.exp (collisionXi G ς q') - 1 - collisionXi G ς q')) := by
    intro q' hq'
    unfold collisionDnat
    field_simp
  rw [hsplit q hq, hsplit P hP]
  exact add_le_add (mul_le_mul_of_nonneg_right hUL hA0)
    (collision_expPart_endpoint G ς hP hPq hS1)

/-- **`lem:oct24-collision`(e)** for the tail of (c): if `Ξ < k₀ + 1` at `P` (and `k₀ ≥ 2`),
the tail bound `(Υ/L_int)(Ξ^{k₀}/k₀!)(1 - Ξ/(k₀ + 1))⁻¹` divided by `r⁴` (times `q²`) at
`q ≥ P` is at most its value at `P`. -/
theorem collision_tail_endpoint (G : OrientedGraph U) (ς : U → U → ℤ) {n : ℕ} {P q : ℝ}
    (hP : 0 < P) (hPq : P ≤ q) (hS1 : ∀ v, coarseError (rowsDeg0 G v) P n < 1) {k₀ : ℕ}
    (hk₀ : 2 ≤ k₀) (hΞ : collisionXi G ς P < k₀ + 1) :
    q ^ 2 * (collisionUps G ς q n / collisionLint G q n *
        (collisionXi G ς q ^ k₀ / (k₀.factorial : ℝ)) * (1 - collisionXi G ς q / (k₀ + 1))⁻¹) ≤
      P ^ 2 * (collisionUps G ς P n / collisionLint G P n *
        (collisionXi G ς P ^ k₀ / (k₀.factorial : ℝ)) * (1 - collisionXi G ς P / (k₀ + 1))⁻¹) := by
  have hq : 0 < q := lt_of_lt_of_le hP hPq
  have hn2 : (0 : ℝ) ≤ 2 * n := by positivity
  obtain ⟨hLP, hLle⟩ := collision_Lint_mono G hP hPq hS1
  set c := Real.sqrt 2 ^ collisionDeltaPlus G * ∑ i, ∑ j, collisionA G ς i j with hc
  have hc0 : 0 ≤ c := collision_c_nonneg G ς
  have hU : collisionUps G ς q n ≤ collisionUps G ς P n :=
    collision_prod_anti univ (fun i => rowsDeg0 G i + collisionR ς i) hn2 hP hPq
  have hU0 : 0 ≤ collisionUps G ς q n := prod_nonneg fun i _ => by
    linarith [coarseError_nonneg hn2 (q := q) (rowsDeg0 G i + collisionR ς i)]
  have hUL : collisionUps G ς q n / collisionLint G q n ≤
      collisionUps G ς P n / collisionLint G P n :=
    div_le_div₀ (hU0.trans hU) hU hLP hLle
  have hXq : collisionXi G ς q = c / q := by rw [collisionXi_eq]
  have hXP : collisionXi G ς P = c / P := by rw [collisionXi_eq]
  have hXle : c / q ≤ c / P := div_le_div_of_nonneg_left hc0 hP hPq
  have hXq0 : 0 ≤ c / q := div_nonneg hc0 hq.le
  have hk1 : (0 : ℝ) < k₀ + 1 := by positivity
  have hden : 0 < 1 - c / P / (k₀ + 1) := by
    rw [hXP] at hΞ
    rw [sub_pos, div_lt_one hk1]
    exact hΞ
  have hden' : 1 - c / P / (k₀ + 1) ≤ 1 - c / q / (k₀ + 1) := by
    have := div_le_div_of_nonneg_right hXle hk1.le
    linarith
  have hinv : (1 - c / q / (k₀ + 1))⁻¹ ≤ (1 - c / P / (k₀ + 1))⁻¹ := inv_anti₀ hden hden'
  -- `q² (c/q)^{k₀} = c^{k₀} (q⁻¹)^{k₀ - 2}`
  have hpow : ∀ q' : ℝ, 0 < q' → q' ^ 2 * (c / q') ^ k₀ = c ^ k₀ * (q'⁻¹) ^ (k₀ - 2) := by
    intro q' hq'
    obtain ⟨m, rfl⟩ : ∃ m, k₀ = m + 2 := ⟨k₀ - 2, by omega⟩
    rw [Nat.add_sub_cancel]
    exact collision_sq_mul_pow hq' m
  rw [hXq, hXP]
  have hfac : (0 : ℝ) < k₀.factorial := by exact_mod_cast Nat.factorial_pos k₀
  calc q ^ 2 * (collisionUps G ς q n / collisionLint G q n * ((c / q) ^ k₀ / (k₀.factorial : ℝ)) *
        (1 - c / q / (k₀ + 1))⁻¹)
      = collisionUps G ς q n / collisionLint G q n * (c ^ k₀ * (q⁻¹) ^ (k₀ - 2) /
          (k₀.factorial : ℝ)) * (1 - c / q / (k₀ + 1))⁻¹ := by
        rw [← hpow q hq]
        ring
    _ ≤ collisionUps G ς P n / collisionLint G P n * (c ^ k₀ * (P⁻¹) ^ (k₀ - 2) /
          (k₀.factorial : ℝ)) * (1 - c / P / (k₀ + 1))⁻¹ := by
        have hpq : (q⁻¹) ^ (k₀ - 2) ≤ (P⁻¹) ^ (k₀ - 2) :=
          pow_le_pow_left₀ (by positivity) (inv_anti₀ hP hPq) _
        have hdq : 0 < 1 - c / q / (k₀ + 1) := lt_of_lt_of_le hden hden'
        refine mul_le_mul (mul_le_mul hUL (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hpq (pow_nonneg hc0 _)) hfac.le) (by positivity)
          (div_nonneg (hU0.trans hU) hLP.le)) hinv (inv_nonneg.mpr hdq.le)
          (mul_nonneg (div_nonneg (hU0.trans hU) hLP.le) (by positivity))
    _ = _ := by
        rw [← hpow P hP]
        ring

end Endpoint

/-! ## Spectral data -/

section SpecDataForm

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **`eq:collision-natural` for spectral data**: `‖T_coll‖ ≤ D_nat` on `L²(μ)`, `μ = λ_p(G⁺)`,
under `e_Δ(p, 2n) < 1`, for any orders `π_k` (matrix normalization of `collision_opBound`). -/
theorem collision_opBound_natural_specData (hW : WeilBound F) (D : Cuts.SpecData V)
    (hne : (injLabellings F D.halfGraph).Nonempty)
    (hS1 : coarseError D.Delta (Fintype.card F) (2 * D.n) < 1)
    (ord : D.cut.Half → D.cut.Half → D.cut.Half → ℕ)
    (hord : ∀ i j, ∀ ℓ ℓ', ℓ ≠ i → ℓ' ≠ i → ord i j ℓ = ord i j ℓ' → ℓ = ℓ')
    (π : ℕ → D.cut.Half → ℕ) (hπ : ∀ k, Function.Injective (π k)) :
    Sarkozy.Influence.OpBound (injLabellings F D.halfGraph) (injLabellings F D.halfGraph)
      (fun x x' => collisionKernelColl D.sgn x x' / (injLabellings F D.halfGraph).card)
      (collisionDnat D.halfGraph D.sgn (Fintype.card F) D.n) := by
  refine collision_opBound_natural hW D.halfGraph D.sgn ?_ (fun j k => D.sgn_antisymm j k) hne
    ?_ ?_ ord hord π hπ
  · intro j k
    unfold Cuts.SpecData.sgn
    split_ifs <;> simp
  · exact le_of_eq (Fintype.card_coe _)
  · intro i
    have hdeg : rowsDeg0 D.halfGraph i ≤ D.Delta := by
      rw [coverRow_rowsDeg0_halfGraph]
      exact (Nat.le_add_right _ _).trans (Finset.le_sup (f := D.dk) (mem_univ i))
    have hn0 : (0 : ℝ) ≤ D.n := Nat.cast_nonneg _
    calc coarseError (rowsDeg0 D.halfGraph i) (Fintype.card F) D.n
        ≤ coarseError D.Delta (Fintype.card F) D.n := coarseError_mono hn0 hdeg
      _ ≤ coarseError D.Delta (Fintype.card F) (2 * D.n) :=
          coverRow_coarseError_mono_n _ (by linarith)
      _ < 1 := hS1

end SpecDataForm

end Sarkozy.Extraction
