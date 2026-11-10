module

public import Sarkozy.SpectralD.CxInputs
public import Sarkozy.TraceMixing.PairExplicit

@[expose] public section





namespace Sarkozy.SpectralD.Cx

open Finset Sarkozy.SpectralC
open scoped BigOperators

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} [Fact p.Prime]

/-- `ς b` is a nonzero square iff `χ(b) = χ(ς)` (for `ς ≠ 0`). -/
lemma sq_cond_iff {s : ZMod p} (hs : s ≠ 0) (b : ZMod p) :
    (s * b ≠ 0 ∧ IsSquare (s * b)) ↔ quadraticChar (ZMod p) b = quadraticChar (ZMod p) s := by
  have h2 : quadraticChar (ZMod p) s ^ 2 = 1 := quadraticChar_sq_one hs
  constructor
  · rintro ⟨hne, hsq⟩
    have h1 : quadraticChar (ZMod p) (s * b) = 1 := (quadraticChar_one_iff_isSquare hne).mpr hsq
    rw [map_mul] at h1
    calc quadraticChar (ZMod p) b = quadraticChar (ZMod p) s ^ 2 * quadraticChar (ZMod p) b := by
          rw [h2, one_mul]
      _ = quadraticChar (ZMod p) s * (quadraticChar (ZMod p) s * quadraticChar (ZMod p) b) := by
          ring
      _ = quadraticChar (ZMod p) s := by rw [h1, mul_one]
  · intro h
    have h3 : quadraticChar (ZMod p) (s * b) = 1 := by rw [map_mul, h, ← sq, h2]
    have hne : s * b ≠ 0 := by
      intro h0; rw [h0, quadraticChar_zero] at h3; exact zero_ne_one h3
    exact ⟨hne, (quadraticChar_one_iff_isSquare hne).mp h3⟩

/-- For nonzero `s, s'`, `χ(s s') ≠ −1` gives `χ(s) = χ(s')`. -/
lemma chi_eq_of_ne_neg {s s' : ZMod p} (hs : s ≠ 0) (hs' : s' ≠ 0)
    (h : quadraticChar (ZMod p) (s * s') ≠ -1) :
    quadraticChar (ZMod p) s = quadraticChar (ZMod p) s' := by
  rw [map_mul] at h
  rcases quadraticChar_dichotomy hs with h1 | h1 <;>
    rcases quadraticChar_dichotomy hs' with h2 | h2 <;> simp_all

/-- **`lem:extension`(coarse)** for an admissible set with the roots `x_j`, `j ∈ S` (`x`
injective), and the excluded set `x(U)`:
`|Φ| ∈ p2^{-|S|}[1 − e_{|S|}(p, |U|), 1 + e_{|S|}(p, |U|)]`. -/
theorem admissible_coarse {U : Type*} [Fintype U] [DecidableEq U]
    (hW : Labellings.WeilBound (ZMod p)) {x : U → ZMod p} (hxinj : Function.Injective x)
    (S : Finset U) (s : S → ℤ) (hs : ∀ j, s j = 1 ∨ s j = -1) :
    (p : ℝ) / 2 ^ S.card * (1 - TraceMixing.coarseErr p S.card (Fintype.card U)) ≤
        (Labellings.admissible (fun j : S => x j.1) s (univ.image x)).card ∧
      ((Labellings.admissible (fun j : S => x j.1) s (univ.image x)).card : ℝ) ≤
        (p : ℝ) / 2 ^ S.card * (1 + TraceMixing.coarseErr p S.card (Fintype.card U)) := by
  classical
  have hβ : Function.Injective (fun j : S => x j.1) := fun a b h => Subtype.ext (hxinj h)
  have hX : ∀ j : S, x j.1 ∈ univ.image x := fun j => mem_image_of_mem x (mem_univ _)
  have hb := Labellings.extension_bounds hW (fun j : S => x j.1) hβ s hs (univ.image x) hX
  rw [Fintype.card_coe, ZMod.card] at hb
  set t := S.card with ht
  set Φ := Labellings.admissible (fun j : S => x j.1) s (univ.image x) with hΦ
  have hq1 : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
  have hq0 : (0 : ℝ) < p := by linarith
  have hsoft := Cuts.SpecData.softError_le hq1 t
  unfold Labellings.softError at hsoft
  have h2 : (0 : ℝ) < 2 ^ t := by positivity
  have hXc : ((univ.image x).card : ℝ) ≤ Fintype.card U := by
    exact_mod_cast (card_image_le.trans (by rw [card_univ]))
  set n := Fintype.card U with hn
  set H := (t : ℝ) / 2 - 1 + (1 / 2) ^ t with hH
  have hs1 : Real.sqrt p * Real.sqrt p = p := Real.mul_self_sqrt hq0.le
  have hsp : 0 < Real.sqrt p := Real.sqrt_pos.mpr hq0
  have hpinv : (p : ℝ) * (Real.sqrt p)⁻¹ = Real.sqrt p := by
    rw [eq_comm, eq_mul_inv_iff_mul_eq₀ hsp.ne', hs1]
  have hE : (p : ℝ) * TraceMixing.coarseErr p t n = 2 ^ t * (H * Real.sqrt p + n) := by
    unfold TraceMixing.coarseErr
    rw [← hH]
    calc (p : ℝ) * (2 ^ t * (H * (Real.sqrt p)⁻¹ + n / p))
        = 2 ^ t * (H * ((p : ℝ) * (Real.sqrt p)⁻¹) + n * ((p : ℝ) / p)) := by ring
      _ = 2 ^ t * (H * Real.sqrt p + n) := by rw [hpinv, div_self hq0.ne', mul_one]
  have hsoft' : Labellings.gradedA t * Real.sqrt p + Labellings.gradedB t ≤
      2 ^ t * (H * Real.sqrt p) := by
    rw [div_le_iff₀ h2] at hsoft
    linarith
  obtain ⟨hup, hlow⟩ := hb
  constructor
  · rw [div_mul_eq_mul_div, div_le_iff₀ h2, mul_sub, mul_one, hE]
    nlinarith [mul_le_mul_of_nonneg_left hXc h2.le]
  · rw [div_mul_eq_mul_div, le_div_iff₀ h2, mul_add, mul_one, hE]
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    nlinarith [mul_nonneg h2.le hn0]

variable {W : Type*} [Fintype W] [DecidableEq W] (D : Cuts.SpecData W)

lemma sgnZ_ne_zero {j k : D.cut.Half} (hj : j ∈ D.Nset k) : sgnZ (p := p) D j k ≠ 0 := by
  have hs : D.sgn j k ≠ 0 := by
    simp only [Cuts.SpecData.Nset, mem_filter, mem_univ, true_and] at hj; exact hj
  have h1 : D.sgn j k = 1 ∨ D.sgn j k = -1 := by
    unfold Cuts.SpecData.sgn at hs ⊢
    split_ifs at hs ⊢ <;> simp_all
  unfold sgnZ
  rcases h1 with h | h <;> rw [h] <;> simp

/-- **`Φ_k(x)` is an admissible set** of `lem:extension`: roots `x_j` (`j ∈ N(k)`), signs
`χ(ς_jk)`, excluded set `x(U⁺)`. -/
theorem allowedSet_eq_admissible (x : D.cut.Half → ZMod p) (k : D.cut.Half) :
    allowedSet D.Nset (sgnZ D) k x =
      Labellings.admissible (fun j : D.Nset k => x j.1)
        (fun j : D.Nset k => quadraticChar (ZMod p) (sgnZ (p := p) D j.1 k)) (univ.image x) := by
  ext a
  simp only [allowedSet, Labellings.admissible, mem_filter, mem_univ, true_and]
  exact and_congr Iff.rfl ⟨fun h j => (sq_cond_iff (sgnZ_ne_zero D j.2) _).mp (h j.1 j.2),
    fun h j hj => (sq_cond_iff (sgnZ_ne_zero D hj) _).mpr (h ⟨j, hj⟩)⟩

/-- **`Φ_k(x) ∩ Φ_l(x)` is an admissible set** for a consistent pair: roots `x_j`
(`j ∈ N(k) ∪ N(l)`), signs `χ(ς_jk)` on `N(k)` and `χ(ς_jl)` off it. -/
theorem allowedSet_inter_eq_admissible (x : D.cut.Half → ZMod p) {k l : D.cut.Half}
    (hc : Consistent D.Nset (sgnZ (p := p) D) k l) :
    allowedSet D.Nset (sgnZ D) k x ∩ allowedSet D.Nset (sgnZ D) l x =
      Labellings.admissible (fun j : (D.Nset k ∪ D.Nset l : Finset D.cut.Half) => x j.1)
        (fun j => if j.1 ∈ D.Nset k then quadraticChar (ZMod p) (sgnZ (p := p) D j.1 k)
          else quadraticChar (ZMod p) (sgnZ (p := p) D j.1 l)) (univ.image x) := by
  ext a
  simp only [mem_inter, allowedSet, Labellings.admissible, mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨⟨hax, hk⟩, -, hl⟩
    refine ⟨hax, fun j => ?_⟩
    by_cases hj : j.1 ∈ D.Nset k
    · simp only [hj, ↓reduceIte]
      exact (sq_cond_iff (sgnZ_ne_zero D hj) _).mp (hk j.1 hj)
    · have hjl : j.1 ∈ D.Nset l := (mem_union.mp j.2).resolve_left hj
      simp only [hj, ↓reduceIte]
      exact (sq_cond_iff (sgnZ_ne_zero D hjl) _).mp (hl j.1 hjl)
  · rintro ⟨hax, h⟩
    refine ⟨⟨hax, fun j hj => ?_⟩, hax, fun j hj => ?_⟩
    · have h1 := h ⟨j, mem_union_left _ hj⟩
      simp only [hj, ↓reduceIte] at h1
      exact (sq_cond_iff (sgnZ_ne_zero D hj) _).mpr h1
    · have h1 := h ⟨j, mem_union_right _ hj⟩
      by_cases hjk : j ∈ D.Nset k
      · simp only [hjk, ↓reduceIte] at h1
        have e := chi_eq_of_ne_neg (sgnZ_ne_zero D hjk) (sgnZ_ne_zero D hj)
          (hc j (mem_inter.mpr ⟨hjk, hj⟩))
        rw [e] at h1
        exact (sq_cond_iff (sgnZ_ne_zero D hj) _).mpr h1
      · simp only [hjk, ↓reduceIte] at h1
        exact (sq_cond_iff (sgnZ_ne_zero D hj) _).mpr h1

/-- **The counts of `lem:extension`(coarse) at every `x ∈ 𝓘⁺`** (WP-K's `CountsOK`, with
`e_t = e_t(p, |U⁺|)`): single allowed sets and intersections for consistent pairs. -/
theorem countsOK_cut (hW : Labellings.WeilBound (ZMod p)) {x : D.cut.Half → ZMod p}
    (hx : x ∈ Labellings.injLabellings (ZMod p) D.halfGraph) :
    CountsOK D.Nset (sgnZ (p := p) D)
      (fun t => TraceMixing.coarseErr p t (Fintype.card D.cut.Half)) x := by
  rw [Cuts.SpecData.mem_inj_half] at hx
  have hxinj : Function.Injective x := fun a b h => hx.1 a (mem_univ _) b (mem_univ _) h
  refine ⟨fun k => ?_, fun k l _ hc => ?_⟩
  · rw [allowedSet_eq_admissible D x k]
    exact admissible_coarse hW hxinj (D.Nset k) _
      (fun j => quadraticChar_dichotomy (sgnZ_ne_zero D j.2))
  · rw [allowedSet_inter_eq_admissible D x hc]
    refine admissible_coarse hW hxinj (D.Nset k ∪ D.Nset l) _ (fun j => ?_)
    split_ifs with hj
    · exact quadraticChar_dichotomy (sgnZ_ne_zero D hj)
    · exact quadraticChar_dichotomy (sgnZ_ne_zero D ((mem_union.mp j.2).resolve_left hj))

/-- **The coarse count of `Φ_k(x)`** (`lem:extension`(coarse)): for `x ∈ 𝓘⁺`,
`p2^{-r_k}(1 − ê_k) ≤ |Φ_k(x)| ≤ p2^{-r_k}(1 + ê_k)`, `ê_k = e_{r_k}(p, |U⁺|)`. -/
theorem allowedSet_coarse (hW : Labellings.WeilBound (ZMod p)) {x : D.cut.Half → ZMod p}
    (hx : x ∈ Labellings.injLabellings (ZMod p) D.halfGraph) (k : D.cut.Half) :
    (p : ℝ) / 2 ^ (D.Nset k).card *
        (1 - TraceMixing.coarseErr p (D.Nset k).card (Fintype.card D.cut.Half)) ≤
        (allowedSet D.Nset (sgnZ D) k x).card ∧
      ((allowedSet D.Nset (sgnZ D) k x).card : ℝ) ≤ (p : ℝ) / 2 ^ (D.Nset k).card *
        (1 + TraceMixing.coarseErr p (D.Nset k).card (Fintype.card D.cut.Half)) :=
  (countsOK_cut D hW hx).1 k

variable (hne : (Labellings.injLabellings (ZMod p) D.G).Nonempty)
  (hρpos : ∀ x ∈ Labellings.injLabellings (ZMod p) D.halfGraph,
    0 < rhoK (D.halfLaw hne).weight (cutKn D hne) x)
  (c R : ℝ) (hc : 0 < c) (hR : 1 ≤ R)
  (hdens : ∀ x ∈ Labellings.injLabellings (ZMod p) D.halfGraph,
    c ≤ rhoK (D.halfLaw hne).weight (cutKn D hne) x ∧
      rhoK (D.halfLaw hne).weight (cutKn D hne) x ≤ R * c)
  (Rp : D.cut.Half → ℝ) (hRp : ∀ i, 1 ≤ Rp i)
  (hPdens : ∀ i, ∀ x ∈ Labellings.injLabellings (ZMod p) D.halfGraph,
    ∀ a ∈ allowedSet D.Nset (sgnZ D) i x,
      (Rp i)⁻¹ ≤ PA D hne i x a * (allowedSet D.Nset (sgnZ D) i x).card ∧
        PA D hne i x a * (allowedSet D.Nset (sgnZ D) i x).card ≤ Rp i)

include hρpos hc hR hdens hRp hPdens in
/-- **`hΓ` for the cut** (`lem:spec2:paley`(a) with the coarse counts):
`E_ν‖∑_k w_k E_k‖² ≤ Γ_E |w|²` with
`Γ_E = ∑_k (2^{r_k}(1 + ê_k) devConst(R'_k, ê_k)² + |U⁺| 4^{r_k}/p)`. -/
theorem gammaE_cut (hW : Labellings.WeilBound (ZMod p))
    (hê : ∀ k : D.cut.Half,
      TraceMixing.coarseErr p (D.Nset k).card (Fintype.card D.cut.Half) < 1)
    (w : D.cut.Half → ℂ) :
    ∑ x, nuA D hne x * l2sq (fun a => ∑ j, w j *
      ((p : ℂ) * (PA D hne j x a : ℂ) - starProd D.Nset (sgnZ (p := p) D) j x a)) ≤
      (∑ k, ((2 : ℝ) ^ (D.Nset k).card *
          (1 + TraceMixing.coarseErr p (D.Nset k).card (Fintype.card D.cut.Half)) *
          devConst (Rp k)
            (TraceMixing.coarseErr p (D.Nset k).card (Fintype.card D.cut.Half)) ^ 2 +
        (Fintype.card D.cut.Half : ℝ) * 4 ^ (D.Nset k).card / p)) * ∑ k, ‖w k‖ ^ 2 := by
  have hq0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  exact PaleyB.gammaE_of_deviation
    (couplingDataA D hne hρpos c R hc hR hdens Rp hRp hPdens)
    (fun k j hj => sgnZ_ne_zero D hj)
    (fun k => TraceMixing.coarseErr p (D.Nset k).card (Fintype.card D.cut.Half))
    (fun k => TraceMixing.coarseErr_nonneg hq0 _ _) hê
    (fun x hx k => allowedSet_coarse D hW hx k) w

include hρpos hc hR hdens hRp hPdens in
/-- **`hHt` for the cut** (`lem:spec2:gram`, WP-K's `gram_comparison`): `H̃ ⪯ 𝐇 + (ρ_β + ρ_X) I`
whenever `ρ_β`, `ρ_X` bound the row sums of `β` and `b^X` at `e_t = e_t(p, |U⁺|)`. -/
theorem hHt_cut (hW : Labellings.WeilBound (ZMod p))
    (hê : ∀ k : D.cut.Half,
      TraceMixing.coarseErr p (D.Nset k).card (Fintype.card D.cut.Half) < 1)
    {ρβ ρX : ℝ}
    (hrow : ∀ k, ∑ l, betaG D.Nset (sgnZ (p := p) D)
      (fun t => TraceMixing.coarseErr p t (Fintype.card D.cut.Half)) k l ≤ ρβ)
    (hrowX : ∀ k, ∑ l, bX D.Nset (sgnZ (p := p) D)
      (fun t => TraceMixing.coarseErr p t (Fintype.card D.cut.Half)) Rp k l ≤ ρX)
    (w : D.cut.Half → ℂ) :
    (qform (gramΓ (nuA D hne) (psiField (PA D hne))) w).re ≤
      (qform (PaleyB.modelHC D.Nset (sgnZ (p := p) D)) w).re + (ρβ + ρX) * ∑ j, ‖w j‖ ^ 2 := by
  have hq0 : (0 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).pos
  let DA := couplingDataA D hne hρpos c R hc hR hdens Rp hRp hPdens
  have hI : ∀ x, nuA D hne x ≠ 0 → x ∈ Labellings.injLabellings (ZMod p) D.halfGraph :=
    fun x hx => by
      by_contra h
      exact hx (DA.ν_supp x h)
  exact PaleyB.hHt_of_normLe (gram_comparison (nuA D hne) DA.ν_nonneg
    (PaleyB.couplingData_sum_ν DA) D.Nset (sgnZ (p := p) D) (fun k j hj => sgnZ_ne_zero D hj)
    (fun t => TraceMixing.coarseErr p t (Fintype.card D.cut.Half))
    (fun t => TraceMixing.coarseErr_nonneg hq0 _ _) hê
    (fun x hx => countsOK_cut D hW (hI x hx)) (PA D hne) Rp hRp
    (fun x hx k => DA.P_total k x (hI x hx)) (fun x hx k a ha => DA.P_supp k x (hI x hx) a ha)
    (fun x hx k a ha => DA.P_dens k x (hI x hx) a ha) hrow hrowX) w

end Sarkozy.SpectralD.Cx
