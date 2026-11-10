module

public import Sarkozy.SecondOrder.FibreMoments
public import Sarkozy.SecondOrder.OrderedOrthogonality

/-!
# Pinned half laws and the ordered star bound
(`def:pinned-law`, `lem:pivot-moments`, `prop:advance:ordered-star`)

`paper/sections/15_second_order.tex`, `subsec:advance:ordered-star`.

* `PinnedHalfLaw`: **`def:pinned-law`**. A law `μ` on injective maps `x : U → 𝔽_p` with in-half
  neighbourhoods `N(i) ∌ i`, nonzero signs `ς⁰_ij` and count errors `e_i ∈ [0, 1)`. For every
  `i` and every `x` in the support, the conditional law of `x_i` given `x_{-i}` is uniform on
  `Φ_i(x_{-i}) = {y ∉ x(U∖{i}) : χ(ς⁰_ij(y - x_j)) = 1 ∀ j ∈ N(i)}` (`pinnedPhi`), and
  `|Φ_i| ≥ (1 - e_i) p 2^{-d_i}`. The conditional statement is fibrewise:
  `μ(x[i↦z]) |Φ_i| = [z ∈ Φ_i] ∑_w μ(x[i↦w])`.
* Pivot groups: each support `T` (`|T| ≥ 3`) has its greatest vertex as pivot. `pivotF` is
  `F_i(x) = ∑_{i(T)=i} a_T τ_{x(T∖{i})}(x_i)`; `pivotD2` and `pivotK` are `D_i²` and `K_i` of
  `eq:pivot-sums`, with `s_T = |T| - 1`, `d = d_i` and `n = |U|`.
* `pivot_second_moment`, `pivot_first_moment`: **`lem:pivot-moments`** (a), (b), fibrewise:
  `∑_z μ(x[i↦z]) F_i(x[i↦z])² ≤ r² D_i² ∑_z μ(x[i↦z])` and
  `|∑_z μ(x[i↦z]) F_i(x[i↦z])| ≤ r² K_i ∑_z μ(x[i↦z])`, for every `x`.
* `ordered_star`: **`prop:advance:ordered-star`**:
  `E_μ(∑_i F_i)² ≤ M_⋆² = r²[∑_i D_i² + 2r ∑_i K_i ∑_{j<i} D_j]` and `|E_μ F_i| ≤ r² K_i`.

Inputs: Weil (`Target.Weil`) and the moving-root moments (H5, `Target.MovingRoot`).
-/

@[expose] public section

open scoped BigOperators
open Finset

namespace Sarkozy.SecondOrder

open Sarkozy.Target

variable {p : ℕ} [hp : Fact p.Prime] {U : Type*} [Fintype U] [DecidableEq U]

/-- The admissible set `Φ_i(x_{-i})` of `def:pinned-law`. -/
noncomputable def pinnedPhi (N : U → Finset U) (sign : U → U → ZMod p) (i : U)
    (x : U → ZMod p) : Finset (ZMod p) :=
  univ.filter fun y => y ∉ (univ.erase i).image x ∧
    ∀ j ∈ N i, quadraticChar (ZMod p) (sign i j * (y - x j)) = 1

omit hp [Fintype U] in
theorem image_erase_update (x : U → ZMod p) (i : U) (z : ZMod p) (T : Finset U) :
    (T.erase i).image (Function.update x i z) = (T.erase i).image x :=
  image_congr fun _ hj => Function.update_of_ne (ne_of_mem_erase hj) z x

theorem pinnedPhi_update (N : U → Finset U) (sign : U → U → ZMod p) (hN : ∀ i, i ∉ N i)
    (i : U) (x : U → ZMod p) (z : ZMod p) :
    pinnedPhi N sign i (Function.update x i z) = pinnedPhi N sign i x := by
  unfold pinnedPhi
  have h2 : ∀ j ∈ N i, Function.update x i z j = x j := fun j hj =>
    Function.update_of_ne (fun h : j = i => hN i (by have h' := hj; rw [h] at h'; exact h')) z x
  ext y
  simp only [mem_filter, mem_univ, true_and, image_erase_update]
  exact and_congr_right fun _ => forall₂_congr fun j hj => by rw [h2 j hj]

/-- **`def:pinned-law`** (fibrewise form). -/
structure PinnedHalfLaw (p : ℕ) [Fact p.Prime] (U : Type*) [Fintype U] [DecidableEq U] where
  /-- the in-half neighbourhoods `N⁰(i)` -/
  N : U → Finset U
  not_mem_N : ∀ i, i ∉ N i
  /-- the signs `ς⁰_ij` (`±1` in the paper; only `≠ 0` is used) -/
  sign : U → U → ZMod p
  sign_ne : ∀ i j, sign i j ≠ 0
  /-- the count errors `e_i ∈ [0, 1)` -/
  e : U → ℝ
  e_nonneg : ∀ i, 0 ≤ e i
  e_lt : ∀ i, e i < 1
  /-- the law -/
  μ : (U → ZMod p) → ℝ
  μ_nonneg : ∀ x, 0 ≤ μ x
  μ_sum : ∑ x, μ x = 1
  μ_inj : ∀ x, 0 < μ x → Function.Injective x
  /-- given `x_{-i}`, `x_i` is uniform on `Φ_i(x_{-i})` -/
  cond : ∀ i x, 0 < μ x → ∀ z, μ (Function.update x i z) * (pinnedPhi N sign i x).card =
    if z ∈ pinnedPhi N sign i x then ∑ w, μ (Function.update x i w) else 0
  /-- `|Φ_i(x_{-i})| ≥ (1 - e_i) p 2^{-d_i}` -/
  count : ∀ i x, 0 < μ x → (1 - e i) * p / 2 ^ (N i).card ≤ (pinnedPhi N sign i x).card

namespace PinnedHalfLaw

variable (L : PinnedHalfLaw p U)

theorem phi_card_pos (i : U) (x : U → ZMod p) (hx : 0 < L.μ x) :
    (0 : ℝ) < (pinnedPhi L.N L.sign i x).card := by
  have h := L.count i x hx
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.out.pos
  have he := L.e_lt i
  have : (0 : ℝ) < (1 - L.e i) * p / 2 ^ (L.N i).card :=
    div_pos (mul_pos (by linarith) hp0) (by positivity)
  linarith

/-- `γ_i = p 2^{-d_i}/|Φ_i| ≤ (1 - e_i)^{-1}`. -/
theorem gamma_le (i : U) (x : U → ZMod p) (hx : 0 < L.μ x) :
    (p : ℝ) / 2 ^ (L.N i).card / (pinnedPhi L.N L.sign i x).card ≤ 1 / (1 - L.e i) := by
  have h := L.count i x hx
  have hpos := L.phi_card_pos i x hx
  have he : 0 < 1 - L.e i := by linarith [L.e_lt i]
  rw [div_le_div_iff₀ hpos he, one_mul]
  have : (1 - L.e i) * p / 2 ^ (L.N i).card = (p : ℝ) / 2 ^ (L.N i).card * (1 - L.e i) := by
    ring
  linarith

/-- On a fibre of positive mass, the fibre sum of `G` is the fibre mass times the uniform average
of `G` over `Φ_i(x_{-i})`. -/
theorem fibre_sum (i : U) (x : U → ZMod p) (z₀ : ZMod p)
    (hz₀ : 0 < L.μ (Function.update x i z₀)) (G : ZMod p → ℝ) :
    ∑ z, L.μ (Function.update x i z) * G z =
      (∑ z, L.μ (Function.update x i z)) *
        ((1 / ((pinnedPhi L.N L.sign i x).card : ℝ)) * ∑ z ∈ pinnedPhi L.N L.sign i x, G z) := by
  have hupd : ∀ z, Function.update (Function.update x i z₀) i z = Function.update x i z :=
    fun z => Function.update_idem _ _ _
  have hΦ : pinnedPhi L.N L.sign i (Function.update x i z₀) = pinnedPhi L.N L.sign i x :=
    pinnedPhi_update L.N L.sign L.not_mem_N i x z₀
  have hpos := L.phi_card_pos i _ hz₀
  rw [hΦ] at hpos
  have hc := L.cond i _ hz₀
  simp only [hupd, hΦ] at hc
  have hμ : ∀ z, L.μ (Function.update x i z) =
      (if z ∈ pinnedPhi L.N L.sign i x then ∑ w, L.μ (Function.update x i w) else 0) /
        (pinnedPhi L.N L.sign i x).card := by
    intro z; rw [← hc z, mul_div_assoc, div_self hpos.ne', mul_one]
  calc ∑ z, L.μ (Function.update x i z) * G z
      = ∑ z, (if z ∈ pinnedPhi L.N L.sign i x then
          (∑ w, L.μ (Function.update x i w)) / (pinnedPhi L.N L.sign i x).card * G z
          else 0) := by
        refine sum_congr rfl fun z _ => ?_
        rw [hμ z]; split_ifs <;> simp
    _ = (∑ w, L.μ (Function.update x i w)) *
          ((1 / ((pinnedPhi L.N L.sign i x).card : ℝ)) * ∑ z ∈ pinnedPhi L.N L.sign i x, G z) := by
        rw [sum_ite_mem, univ_inter, mul_sum, mul_sum]
        exact sum_congr rfl fun z _ => by ring

theorem fibre_zero (i : U) (x : U → ZMod p) (h : ¬ ∃ z₀, 0 < L.μ (Function.update x i z₀)) :
    ∀ z, L.μ (Function.update x i z) = 0 := by
  simp only [not_exists, not_lt] at h
  exact fun z => le_antisymm (h z) (L.μ_nonneg _)

end PinnedHalfLaw

/-! ## Pivot groups -/

variable [LinearOrder U]

/-- The supports with pivot `i`, i.e. with greatest vertex `i`. -/
def pivotGroup (𝒯 : Finset (Finset U)) (i : U) : Finset (Finset U) :=
  𝒯.filter fun T => T.max = (i : WithBot U)

/-- The pivot group function `F_i(x) = ∑_{i(T)=i} a_T τ_{x(T∖{i})}(x_i)`. -/
noncomputable def pivotF (𝒯 : Finset (Finset U)) (a : Finset U → ℝ) (i : U)
    (x : U → ZMod p) : ℝ :=
  ∑ T ∈ pivotGroup 𝒯 i, a T * tau p ((T.erase i).image x) (x i)

/-- `D_i²` of `eq:pivot-sums`. -/
noncomputable def pivotD2 (L : PinnedHalfLaw p U) (𝒯 : Finset (Finset U)) (a : Finset U → ℝ)
    (i : U) : ℝ :=
  pivD2 (1 / Real.sqrt p) (L.N i).card (L.e i) (fun T : pivotGroup 𝒯 i => a T.1)
    (fun T => T.1.card - 1)

/-- `K_i` of `eq:pivot-sums`. -/
noncomputable def pivotK (L : PinnedHalfLaw p U) (𝒯 : Finset (Finset U)) (a : Finset U → ℝ)
    (i : U) : ℝ :=
  pivK (1 / Real.sqrt p) (L.N i).card (Fintype.card U) (L.e i)
    (fun T : pivotGroup 𝒯 i => a T.1) (fun T => T.1.card - 1)

omit [Fintype U] in
theorem mem_pivotGroup {𝒯 : Finset (Finset U)} {i : U} {T : Finset U} :
    T ∈ pivotGroup 𝒯 i ↔ T ∈ 𝒯 ∧ T.max = (i : WithBot U) := mem_filter

omit [Fintype U] in
theorem pivot_mem {𝒯 : Finset (Finset U)} {i : U} {T : Finset U} (hT : T ∈ pivotGroup 𝒯 i) :
    i ∈ T := mem_of_max (mem_pivotGroup.mp hT).2

omit [Fintype U] in
theorem le_pivot {𝒯 : Finset (Finset U)} {i : U} {T : Finset U} (hT : T ∈ pivotGroup 𝒯 i)
    {k : U} (hk : k ∈ T) : k ≤ i := le_max_of_eq hk (mem_pivotGroup.mp hT).2

omit [Fintype U] in
theorem pivotF_update (𝒯 : Finset (Finset U)) (a : Finset U → ℝ) (i : U) (x : U → ZMod p)
    (z : ZMod p) :
    pivotF 𝒯 a i (Function.update x i z) =
      ∑ T : pivotGroup 𝒯 i, a T.1 * tau p ((T.1.erase i).image x) z := by
  unfold pivotF
  rw [← Finset.sum_coe_sort (pivotGroup 𝒯 i)]
  refine sum_congr rfl fun T _ => ?_
  rw [image_erase_update, Function.update_self]

omit [Fintype U] in
/-- `F_i` depends only on the labels `x_k`, `k ≤ i`. -/
theorem pivotF_congr (𝒯 : Finset (Finset U)) (a : Finset U → ℝ) (i : U) (x x' : U → ZMod p)
    (h : ∀ k ≤ i, x k = x' k) : pivotF 𝒯 a i x = pivotF 𝒯 a i x' := by
  unfold pivotF
  refine sum_congr rfl fun T hT => ?_
  have himg : (T.erase i).image x = (T.erase i).image x' :=
    image_congr fun k hk => h k (le_pivot hT (mem_of_mem_erase hk))
  rw [himg, h i le_rfl]

/-- The fibre data of a pinned half law at `i` and an injective `x'` agreeing with `x` off `i`. -/
theorem fibre_data (L : PinnedHalfLaw p U) (𝒯 : Finset (Finset U)) (h𝒯 : ∀ T ∈ 𝒯, 3 ≤ T.card)
    (i : U) (x x' : U → ZMod p) (hx' : Function.Injective x') (hxx : ∀ k, k ≠ i → x k = x' k) :
    Function.Injective (fun j : L.N i => x j.1) ∧
      Function.Injective (fun T : pivotGroup 𝒯 i => (T.1.erase i).image x) ∧
      (∀ T : pivotGroup 𝒯 i, ((T.1.erase i).image x).card = T.1.card - 1) ∧
      (∀ T : pivotGroup 𝒯 i, 2 ≤ ((T.1.erase i).image x).card) ∧
      ((univ.erase i).image x).card = Fintype.card U - 1 ∧
      (∀ j : L.N i, x j.1 ∈ (univ.erase i).image x) ∧
      pinnedPhi L.N L.sign i x = univ.filter fun z => z ∉ (univ.erase i).image x ∧
        ∀ j : L.N i, quadraticChar (ZMod p) (L.sign i j.1 * (z - x j.1)) = 1 := by
  have hne : ∀ j : L.N i, j.1 ≠ i := fun j h =>
    L.not_mem_N i (by have h' := j.2; rw [h] at h'; exact h')
  have himg : ∀ s : Finset U, i ∉ s → s.image x = s.image x' := fun s hs =>
    image_congr fun k hk => hxx k (fun h : k = i => hs (by rw [← h]; exact hk))
  have hinjOn : ∀ s : Finset U, i ∉ s → (s.image x).card = s.card := fun s hs => by
    rw [himg s hs, card_image_of_injective _ hx']
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro j j' h
    simp only at h
    rw [hxx _ (hne j), hxx _ (hne j')] at h
    exact Subtype.ext (hx' h)
  · intro T T' h
    simp only at h
    rw [himg _ (notMem_erase i _), himg _ (notMem_erase i _)] at h
    have h' := image_injective hx' h
    have hT := pivot_mem T.2
    have hT' := pivot_mem T'.2
    apply Subtype.ext
    rw [← insert_erase hT, ← insert_erase hT', h']
  · intro T
    rw [hinjOn _ (notMem_erase i _), card_erase_of_mem (pivot_mem T.2)]
  · intro T
    rw [hinjOn _ (notMem_erase i _), card_erase_of_mem (pivot_mem T.2)]
    have := h𝒯 T.1 (mem_pivotGroup.mp T.2).1
    omega
  · rw [hinjOn _ (notMem_erase i _), card_erase_of_mem (mem_univ i), card_univ]
  · intro j
    exact mem_image_of_mem x (mem_erase.mpr ⟨hne j, mem_univ _⟩)
  · unfold pinnedPhi
    ext z
    simp only [mem_filter, mem_univ, true_and]
    exact and_congr_right fun _ => ⟨fun h j => h j.1 j.2, fun h j hj => h ⟨j, hj⟩⟩

/-- **`lem:pivot-moments`(a)**, fibrewise: `E_μ[F_i² | x_{-i}] ≤ r² D_i²`. -/
theorem pivot_second_moment (hM : Target.MovingRoot) (hp2 : p ≠ 2) (L : PinnedHalfLaw p U)
    (𝒯 : Finset (Finset U)) (h𝒯 : ∀ T ∈ 𝒯, 3 ≤ T.card) (a : Finset U → ℝ) (i : U)
    (x : U → ZMod p) :
    ∑ z, L.μ (Function.update x i z) * pivotF 𝒯 a i (Function.update x i z) ^ 2 ≤
      (1 / Real.sqrt p) ^ 2 * pivotD2 L 𝒯 a i * ∑ z, L.μ (Function.update x i z) := by
  by_cases h0 : ∃ z₀, 0 < L.μ (Function.update x i z₀)
  · obtain ⟨z₀, hz₀⟩ := h0
    have hx' := L.μ_inj _ hz₀
    have hxx : ∀ k, k ≠ i → x k = Function.update x i z₀ k := fun k hk =>
      (Function.update_of_ne hk z₀ x).symm
    obtain ⟨hy, hS, hcard, hS2, -, -, hΦ⟩ := fibre_data L 𝒯 h𝒯 i x _ hx' hxx
    rw [L.fibre_sum i x z₀ hz₀]
    simp_rw [pivotF_update]
    have hΦne : (pinnedPhi L.N L.sign i x).Nonempty := by
      have := L.phi_card_pos i _ hz₀
      rw [pinnedPhi_update L.N L.sign L.not_mem_N] at this
      exact card_pos.mp (by exact_mod_cast this)
    have hmom := fibre_second_moment hM hp2 (fun j : L.N i => x j.1) hy
      (fun j : L.N i => L.sign i j.1) ((univ.erase i).image x)
      (fun T : pivotGroup 𝒯 i => (T.1.erase i).image x) hS hS2
      (fun T : pivotGroup 𝒯 i => a T.1) (pinnedPhi L.N L.sign i x) hΦ hΦne
    have hγ := L.gamma_le i _ hz₀
    rw [pinnedPhi_update L.N L.sign L.not_mem_N] at hγ
    rw [Fintype.card_coe] at hmom
    have hfun : (fun T : pivotGroup 𝒯 i => ((T.1.erase i).image x).card) =
        fun T => T.1.card - 1 := funext hcard
    rw [hfun] at hmom
    set r := 1 / Real.sqrt p with hr
    have hr0 : 0 ≤ r := by positivity
    have hs1 : ∀ T : pivotGroup 𝒯 i, 1 ≤ T.1.card - 1 := fun T => by
      have := h𝒯 T.1 (mem_pivotGroup.mp T.2).1; omega
    have hA := pivA_nonneg (fun T : pivotGroup 𝒯 i => a T.1)
    have hE := pivE_nonneg hr0 (L.N i).card (fun T : pivotGroup 𝒯 i => a T.1) hs1
    have he : 0 < 1 - L.e i := by linarith [L.e_lt i]
    have hM0 : 0 ≤ ∑ z, L.μ (Function.update x i z) := sum_nonneg fun z _ => L.μ_nonneg _
    have hbr : 0 ≤ r ^ 2 * pivA (fun T : pivotGroup 𝒯 i => a T.1) +
        r ^ 3 * pivE r (L.N i).card (fun T : pivotGroup 𝒯 i => a T.1) (fun T => T.1.card - 1) := by
      positivity
    have hstep : (1 / ((pinnedPhi L.N L.sign i x).card : ℝ)) *
        ∑ z ∈ pinnedPhi L.N L.sign i x, (∑ T : pivotGroup 𝒯 i, a T.1 * tau p ((T.1.erase i).image x) z) ^ 2 ≤
        r ^ 2 * pivotD2 L 𝒯 a i := by
      refine hmom.trans ?_
      calc (p : ℝ) / 2 ^ (L.N i).card / (pinnedPhi L.N L.sign i x).card *
            (r ^ 2 * pivA (fun T : pivotGroup 𝒯 i => a T.1) +
              r ^ 3 * pivE r (L.N i).card (fun T : pivotGroup 𝒯 i => a T.1) (fun T => T.1.card - 1))
          ≤ 1 / (1 - L.e i) * (r ^ 2 * pivA (fun T : pivotGroup 𝒯 i => a T.1) +
              r ^ 3 * pivE r (L.N i).card (fun T : pivotGroup 𝒯 i => a T.1) (fun T => T.1.card - 1)) :=
            mul_le_mul_of_nonneg_right hγ hbr
        _ = r ^ 2 * pivotD2 L 𝒯 a i := by
            unfold pivotD2 pivD2
            rw [← hr]
            field_simp
    calc (∑ z, L.μ (Function.update x i z)) * ((1 / ((pinnedPhi L.N L.sign i x).card : ℝ)) *
          ∑ z ∈ pinnedPhi L.N L.sign i x,
            (∑ T : pivotGroup 𝒯 i, a T.1 * tau p ((T.1.erase i).image x) z) ^ 2)
        ≤ (∑ z, L.μ (Function.update x i z)) * (r ^ 2 * pivotD2 L 𝒯 a i) :=
          mul_le_mul_of_nonneg_left hstep hM0
      _ = r ^ 2 * pivotD2 L 𝒯 a i * ∑ z, L.μ (Function.update x i z) := by ring
  · have hz := L.fibre_zero i x h0
    simp [hz]

/-- **`lem:pivot-moments`(b)**, fibrewise: `|E_μ[F_i | x_{-i}]| ≤ r² K_i`. -/
theorem pivot_first_moment (hW : Target.Weil) (hM : Target.MovingRoot) (hp2 : p ≠ 2)
    (L : PinnedHalfLaw p U) (𝒯 : Finset (Finset U)) (h𝒯 : ∀ T ∈ 𝒯, 3 ≤ T.card)
    (a : Finset U → ℝ) (i : U) (x : U → ZMod p) :
    |∑ z, L.μ (Function.update x i z) * pivotF 𝒯 a i (Function.update x i z)| ≤
      (1 / Real.sqrt p) ^ 2 * pivotK L 𝒯 a i * ∑ z, L.μ (Function.update x i z) := by
  by_cases h0 : ∃ z₀, 0 < L.μ (Function.update x i z₀)
  · obtain ⟨z₀, hz₀⟩ := h0
    have hx' := L.μ_inj _ hz₀
    have hxx : ∀ k, k ≠ i → x k = Function.update x i z₀ k := fun k hk =>
      (Function.update_of_ne hk z₀ x).symm
    obtain ⟨hy, -, hcard, hS2, hEcard, hE, hΦ⟩ := fibre_data L 𝒯 h𝒯 i x _ hx' hxx
    rw [L.fibre_sum i x z₀ hz₀]
    simp_rw [pivotF_update]
    have hΦne : (pinnedPhi L.N L.sign i x).Nonempty := by
      have := L.phi_card_pos i _ hz₀
      rw [pinnedPhi_update L.N L.sign L.not_mem_N] at this
      exact card_pos.mp (by exact_mod_cast this)
    have hmom := fibre_first_moment hW hM hp2 (fun j : L.N i => x j.1) hy
      (fun j : L.N i => L.sign i j.1) (fun j => L.sign_ne i j.1) ((univ.erase i).image x) hE
      (fun T : pivotGroup 𝒯 i => (T.1.erase i).image x) hS2
      (fun T : pivotGroup 𝒯 i => a T.1) (pinnedPhi L.N L.sign i x) hΦ hΦne
    have hγ := L.gamma_le i _ hz₀
    rw [pinnedPhi_update L.N L.sign L.not_mem_N] at hγ
    rw [Fintype.card_coe] at hmom
    have hfun : (fun T : pivotGroup 𝒯 i => ((T.1.erase i).image x).card) =
        fun T => T.1.card - 1 := funext hcard
    rw [hfun, hEcard] at hmom
    set r := 1 / Real.sqrt p with hr
    have hr0 : 0 ≤ r := by positivity
    have hs1 : ∀ T : pivotGroup 𝒯 i, 1 ≤ T.1.card - 1 := fun T => by
      have := h𝒯 T.1 (mem_pivotGroup.mp T.2).1; omega
    have hn : 1 ≤ Fintype.card U := Fintype.card_pos_iff.mpr ⟨i⟩
    have hncast : ((Fintype.card U - 1 : ℕ) : ℝ) = (Fintype.card U : ℝ) - 1 := by
      rw [Nat.cast_sub hn, Nat.cast_one]
    rw [hncast] at hmom
    have he : 0 < 1 - L.e i := by linarith [L.e_lt i]
    have hM0 : 0 ≤ ∑ z, L.μ (Function.update x i z) := sum_nonneg fun z _ => L.μ_nonneg _
    have hK := pivK_nonneg hr0 (L.N i).card hn (L.e_lt i) (fun T : pivotGroup 𝒯 i => a T.1) hs1
    have hbrk : 0 ≤ r ^ 2 * 2 ^ (L.N i).card *
        (pivV (fun T : pivotGroup 𝒯 i => a T.1) (fun T => T.1.card - 1) +
          ((L.N i).card : ℝ) / 2 * pivU (fun T : pivotGroup 𝒯 i => a T.1) (fun T => T.1.card - 1) +
          r * (pivX (fun T : pivotGroup 𝒯 i => a T.1) (fun T => T.1.card - 1) +
            (((L.N i).card : ℝ) / 2 + ((Fintype.card U : ℝ) - 1)) *
              pivW (fun T : pivotGroup 𝒯 i => a T.1) (fun T => T.1.card - 1))) := by
      have hU := pivU_nonneg (fun T : pivotGroup 𝒯 i => a T.1) (fun T => T.1.card - 1)
      have hV := pivV_nonneg (fun T : pivotGroup 𝒯 i => a T.1) hs1
      have hWn := pivW_nonneg (fun T : pivotGroup 𝒯 i => a T.1) (fun T => T.1.card - 1)
      have hX := pivX_nonneg (fun T : pivotGroup 𝒯 i => a T.1) (fun T => T.1.card - 1)
      have hn' : (1 : ℝ) ≤ Fintype.card U := by exact_mod_cast hn
      have h1 : (0 : ℝ) ≤ (Fintype.card U : ℝ) - 1 := by linarith
      positivity
    have hstep : |(1 / ((pinnedPhi L.N L.sign i x).card : ℝ)) *
        ∑ z ∈ pinnedPhi L.N L.sign i x, ∑ T : pivotGroup 𝒯 i, a T.1 * tau p ((T.1.erase i).image x) z| ≤
        r ^ 2 * pivotK L 𝒯 a i := by
      refine hmom.trans ?_
      refine (mul_le_mul_of_nonneg_right hγ hbrk).trans (le_of_eq ?_)
      unfold pivotK pivK
      rw [← hr]
      field_simp
      ring
    rw [abs_mul, abs_of_nonneg hM0]
    calc (∑ z, L.μ (Function.update x i z)) * |(1 / ((pinnedPhi L.N L.sign i x).card : ℝ)) *
          ∑ z ∈ pinnedPhi L.N L.sign i x,
            ∑ T : pivotGroup 𝒯 i, a T.1 * tau p ((T.1.erase i).image x) z|
        ≤ (∑ z, L.μ (Function.update x i z)) * (r ^ 2 * pivotK L 𝒯 a i) :=
          mul_le_mul_of_nonneg_left hstep hM0
      _ = r ^ 2 * pivotK L 𝒯 a i * ∑ z, L.μ (Function.update x i z) := by ring
  · have hz := L.fibre_zero i x h0
    simp [hz]

/-- **`prop:advance:ordered-star`**: for a pinned half law, supports `T` with `|T| ≥ 3` and real
coefficients `a_T`, grouped by pivot,
`E_μ(∑_i F_i)² ≤ M_⋆² = r²[∑_i D_i² + 2r ∑_i K_i ∑_{j<i} D_j]` and `|E_μ F_i| ≤ r² K_i`. -/
theorem ordered_star (hW : Target.Weil) (hM : Target.MovingRoot) (hp2 : p ≠ 2)
    (L : PinnedHalfLaw p U) (𝒯 : Finset (Finset U)) (h𝒯 : ∀ T ∈ 𝒯, 3 ≤ T.card)
    (a : Finset U → ℝ) :
    ∑ x, L.μ x * (∑ i, pivotF 𝒯 a i x) ^ 2 ≤
        (1 / Real.sqrt p) ^ 2 * (∑ i, pivotD2 L 𝒯 a i + 2 * (1 / Real.sqrt p) *
          ∑ i, pivotK L 𝒯 a i * ∑ j ∈ univ.filter (· < i), Real.sqrt (pivotD2 L 𝒯 a j)) ∧
      ∀ i, |∑ x, L.μ x * pivotF 𝒯 a i x| ≤ (1 / Real.sqrt p) ^ 2 * pivotK L 𝒯 a i := by
  set r := 1 / Real.sqrt p with hr
  have hr0 : 0 ≤ r := by positivity
  have hs1 : ∀ i (T : pivotGroup 𝒯 i), 1 ≤ T.1.card - 1 := fun i T => by
    have := h𝒯 T.1 (mem_pivotGroup.mp T.2).1; omega
  have hD0 : ∀ i, 0 ≤ pivotD2 L 𝒯 a i := fun i => pivD2_nonneg hr0 _ (L.e_lt i) _ (hs1 i)
  have hK0 : ∀ i, 0 ≤ pivotK L 𝒯 a i := fun i =>
    pivK_nonneg hr0 _ (Fintype.card_pos_iff.mpr ⟨i⟩) (L.e_lt i) _ (hs1 i)
  have h2 : ∀ i x, ∑ z, L.μ (Function.update x i z) * pivotF 𝒯 a i (Function.update x i z) ^ 2 ≤
      (r * Real.sqrt (pivotD2 L 𝒯 a i)) ^ 2 * ∑ z, L.μ (Function.update x i z) := by
    intro i x
    rw [mul_pow, Real.sq_sqrt (hD0 i)]
    exact pivot_second_moment hM hp2 L 𝒯 h𝒯 a i x
  have h1 : ∀ i x, |∑ z, L.μ (Function.update x i z) * pivotF 𝒯 a i (Function.update x i z)| ≤
      r ^ 2 * pivotK L 𝒯 a i * ∑ z, L.μ (Function.update x i z) :=
    fun i x => pivot_first_moment hW hM hp2 L 𝒯 h𝒯 a i x
  have hoo := ordered_orthogonality L.μ L.μ_nonneg L.μ_sum (fun i x => pivotF 𝒯 a i x)
    (fun i x x' h => pivotF_congr 𝒯 a i x x' h)
    (fun i => r * Real.sqrt (pivotD2 L 𝒯 a i)) (fun i => r ^ 2 * pivotK L 𝒯 a i)
    (fun i => mul_nonneg hr0 (Real.sqrt_nonneg _)) (fun i => mul_nonneg (sq_nonneg _) (hK0 i))
    h2 h1
  constructor
  · refine hoo.trans (le_of_eq ?_)
    have e1 : ∑ i, (r * Real.sqrt (pivotD2 L 𝒯 a i)) ^ 2 = r ^ 2 * ∑ i, pivotD2 L 𝒯 a i := by
      rw [mul_sum]; exact sum_congr rfl fun i _ => by rw [mul_pow, Real.sq_sqrt (hD0 i)]
    have e2 : ∑ i, r ^ 2 * pivotK L 𝒯 a i *
          ∑ j ∈ univ.filter (· < i), r * Real.sqrt (pivotD2 L 𝒯 a j) =
        r ^ 3 * ∑ i, pivotK L 𝒯 a i * ∑ j ∈ univ.filter (· < i), Real.sqrt (pivotD2 L 𝒯 a j) := by
      rw [mul_sum]; exact sum_congr rfl fun i _ => by rw [← mul_sum]; ring
    rw [e1, e2]
    ring
  · intro i
    have hX : (0 : ℝ) < Fintype.card (ZMod p) := by exact_mod_cast Fintype.card_pos
    have havg : ∀ g : (U → ZMod p) → ℝ, ∑ x, g x =
        (Fintype.card (ZMod p) : ℝ)⁻¹ * ∑ x, ∑ z, g (Function.update x i z) := by
      intro g
      rw [sum_sum_update, ← mul_assoc, inv_mul_cancel₀ hX.ne', one_mul]
    rw [havg (fun x => L.μ x * pivotF 𝒯 a i x), abs_mul, abs_of_pos (inv_pos.mpr hX)]
    calc (Fintype.card (ZMod p) : ℝ)⁻¹ *
          |∑ x, ∑ z, L.μ (Function.update x i z) * pivotF 𝒯 a i (Function.update x i z)|
        ≤ (Fintype.card (ZMod p) : ℝ)⁻¹ *
            ∑ x, r ^ 2 * pivotK L 𝒯 a i * ∑ z, L.μ (Function.update x i z) :=
          mul_le_mul_of_nonneg_left
            ((abs_sum_le_sum_abs _ _).trans (sum_le_sum fun x _ => h1 i x)) (by positivity)
      _ = r ^ 2 * pivotK L 𝒯 a i *
            ((Fintype.card (ZMod p) : ℝ)⁻¹ * ∑ x, ∑ z, L.μ (Function.update x i z)) := by
          rw [← mul_sum]; ring
      _ = r ^ 2 * pivotK L 𝒯 a i := by rw [← havg L.μ, L.μ_sum, mul_one]

end Sarkozy.SecondOrder
