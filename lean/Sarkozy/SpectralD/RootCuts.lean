module

public import Sarkozy.Cuts.CutKernel
public import Sarkozy.Labellings.TwoLayer
public import Sarkozy.Slots







@[expose] public section

open scoped BigOperators
open Finset

namespace Sarkozy.SpectralD.Root

open Sarkozy Sarkozy.Labellings

/-! ### Boolean forms -/

/-- The edge relation of the root `G_{LL,2}` on the slots, as a Boolean function. -/
def edgeB (u w : Slot) : Bool := twoLayerEdge (Λ := Fin 2) typeL typeL u w

theorem mem_root (u w : Slot) :
    (u, w) ∈ @OrientedGraph.E Slot rootGraph ↔ edgeB u w = true :=
  mem_twoLayerGraph typeL typeL typeL_proper typeL_proper (u, w)

/-- The cross sign `ς_{jk}` of a cut with reflection `f`, in Boolean form: `+1` if
`j → f k`, `−1` if `f k → j`, else `0`. -/
def sgnB (f : Slot → Slot) (j k : Slot) : ℤ :=
  if edgeB j (f k) then 1 else if edgeB (f k) j then -1 else 0

/-- **The chamber reflection `ϑ_{0,0}` is an orientation-preserving automorphism of the root**
(`lem:upper-geometry`(b), checked over all ordered pairs). -/
theorem flip20_edge : ∀ u w : Slot,
    edgeB ((firstChamberCut 0).flip u) ((firstChamberCut 0).flip w) = edgeB u w := by
  decide +kernel

/-- **The layer swap `ι` is an orientation-preserving automorphism of the root**
(`lem:upper-geometry`(b), checked over all ordered pairs). -/
theorem flip22_edge : ∀ u w : Slot,
    edgeB (reservedCut.flip u) (reservedCut.flip w) = edgeB u w := by
  decide +kernel

/-- **Every slot has degree `20` in the root** (`lem:upper-geometry`(a): `10` out- and `10`
in-neighbours). -/
theorem root_degree :
    ∀ v : Slot, (univ.filter (fun w => edgeB v w = true ∨ edgeB w v = true)).card = 20 := by
  decide +kernel

/-! ### Deletion orders -/

/-- The slot with code `c = 12 u₀ + 2 u₁ + ℓ` (for `c < 72`). -/
def slotOfCode (c : ℕ) : Slot :=
  ((⟨c / 12 % 6, Nat.mod_lt _ (by norm_num)⟩ : Fin 6),
    (⟨c / 2 % 6, Nat.mod_lt _ (by norm_num)⟩ : Fin 6), (⟨c % 2, Nat.mod_lt _ (by norm_num)⟩ : Fin 2))

/-- The deletion order of LL20 as slot codes `12 u₀ + 2 u₁ + ℓ`: the greedy order of the paper's
certificate (least current degree first, ties to the least code). -/
def LL20_orderCodes : List ℕ :=
  [0, 16, 1, 17, 8, 24, 9, 25, 20, 21, 28, 29, 2, 34, 3, 35, 12, 13, 4, 32, 5, 33, 6, 26, 7, 27,
    18, 19, 10, 11, 14, 30, 15, 31, 22, 23]

theorem LL20_order_mem : ∀ i : Fin (firstChamberCut 0).half.card,
    slotOfCode (LL20_orderCodes.getD i.val 0) ∈ (firstChamberCut 0).half := by
  decide +kernel

/-- The deletion order of LL20 as a map `Fin n → U⁺`. -/
def LL20_orderFun (i : Fin (firstChamberCut 0).half.card) : (firstChamberCut 0).Half :=
  ⟨slotOfCode (LL20_orderCodes.getD i.val 0), LL20_order_mem i⟩

theorem LL20_orderFun_bijective : Function.Bijective LL20_orderFun := by
  decide +kernel

/-- The deletion order of LL22 as slot codes `12 u₀ + 2 u₁` (`ℓ = 0`): the greedy order of the
paper's certificate (least current degree first, ties to the least code). -/
def LL22_orderCodes : List ℕ :=
  [0, 16, 68, 36, 22, 26, 42, 52, 6, 58, 32, 62, 4, 48, 2, 18, 34, 54, 8, 24, 10, 14, 30, 38, 64,
    56, 40, 60, 46, 12, 20, 28, 44, 66, 50, 70]

theorem LL22_order_mem : ∀ i : Fin reservedCut.half.card,
    slotOfCode (LL22_orderCodes.getD i.val 0) ∈ reservedCut.half := by
  decide +kernel

/-- The deletion order of LL22 as a map `Fin n → U⁺`. -/
def LL22_orderFun (i : Fin reservedCut.half.card) : reservedCut.Half :=
  ⟨slotOfCode (LL22_orderCodes.getD i.val 0), LL22_order_mem i⟩

theorem LL22_orderFun_bijective : Function.Bijective LL22_orderFun := by
  decide +kernel

/-! ### Transfer from the Boolean forms -/

section Transfer

variable (D : Cuts.SpecData Slot) (hG : D.G = rootGraph)
include hG

theorem mem_E (u w : Slot) : (u, w) ∈ D.G.E ↔ edgeB u w = true := by
  rw [hG]
  exact mem_root u w

theorem sgn_eq (j k : D.cut.Half) : D.sgn j k = sgnB D.cut.flip j.1 k.1 := by
  unfold Cuts.SpecData.sgn sgnB
  simp only [mem_E D hG]

theorem Nset_card_eq (k : D.cut.Half) :
    (D.Nset k).card = (univ.filter (fun j : D.cut.Half => sgnB D.cut.flip j.1 k.1 ≠ 0)).card := by
  unfold Cuts.SpecData.Nset
  congr 1
  ext j
  simp only [mem_filter, mem_univ, true_and, sgn_eq D hG]

theorem adj_card_eq (v : Slot) :
    (univ.filter (fun w => (v, w) ∈ D.G.E ∨ (w, v) ∈ D.G.E)).card =
      (univ.filter (fun w => edgeB v w = true ∨ edgeB w v = true)).card := by
  congr 1
  ext w
  simp only [mem_filter, mem_univ, true_and, mem_E D hG]

theorem hdeg_of_root :
    ∀ v, (univ.filter (fun w => (v, w) ∈ D.G.E ∨ (w, v) ∈ D.G.E)).card ≤ 20 := by
  intro v
  rw [adj_card_eq D hG, root_degree]

theorem degree_eq_twenty (v : Slot) : D.degree v = 20 := by
  have h : D.degree v = (univ.filter (fun w => edgeB v w = true ∨ edgeB w v = true)).card := by
    unfold Cuts.SpecData.degree
    congr 1
    ext w
    simp only [mem_filter, mem_univ, true_and, Cuts.SpecData.Adj, mem_E D hG]
  rw [h, root_degree]

/-- `Δ = 20`. -/
theorem Delta_eq_twenty : D.Delta = 20 := by
  rw [← D.maxDegree_eq_Delta]
  have h : (univ.sup D.degree) = univ.sup (fun _ : Slot => 20) :=
    sup_congr rfl (fun v _ => degree_eq_twenty D hG v)
  rw [h, sup_const univ_nonempty]

theorem nbrCount_eq (j : D.cut.Half) :
    nbrCount D.halfGraph (univ.erase j) j =
      ((univ.erase j).filter
        (fun u : D.cut.Half => edgeB u.1 j.1 = true ∨ edgeB j.1 u.1 = true)).card := by
  unfold nbrCount
  congr 1
  ext u
  simp only [mem_filter, Cuts.SpecData.mem_halfGraph, mem_E D hG]

/-- The deletion degrees `t_i` in Boolean form. -/
theorem tdeg_eq (i : Fin D.cut.half.card) :
    D.tdeg i = (univ.filter (fun w : Slot =>
      (edgeB (D.order i).1 w = true ∨ edgeB w (D.order i).1 = true) ∧
        ∀ j : Fin D.cut.half.card, j < i → w ≠ (D.order j).1)).card := by
  unfold Cuts.SpecData.tdeg
  congr 1
  ext w
  simp only [mem_filter, mem_univ, true_and, Cuts.SpecData.Adj, mem_E D hG]

omit hG in
/-- `R_cut` along a deletion order with listed degrees `t_i`, as a product over `range 36`. -/
theorem Rcut_eq_range (tl : List ℕ) (h36 : D.cut.half.card = 36)
    (htd : ∀ i, D.tdeg i = tl.getD i.val 0) (e : ℕ → ℝ) :
    D.Rcut e = ∏ k ∈ range 36, (1 + e (tl.getD k 0)) / (1 - e (tl.getD k 0)) := by
  unfold Cuts.SpecData.Rcut
  simp only [htd]
  rw [Fin.prod_univ_eq_prod_range (fun k => (1 + e (tl.getD k 0)) / (1 - e (tl.getD k 0))), h36]

omit hG in
/-- `∑_l (2^{r_l} − 1)` in `ℝ` from its value in `ℕ`. -/
theorem sum_real_eq {S : ℕ}
    (hS : ∑ j : D.cut.Half, (2 ^ (D.Nset j).card - 1) = S) :
    ∑ j : D.cut.Half, ((2 : ℝ) ^ (D.Nset j).card - 1) = S := by
  rw [← hS, Nat.cast_sum]
  refine sum_congr rfl (fun j _ => ?_)
  rw [Nat.cast_sub Nat.one_le_two_pow, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]

omit hG in
/-- `ρ_row ≤ (2^R − 1) S` from `r_k ≤ R` and `∑_l (2^{r_l} − 1) = S`. -/
theorem rho_le {R S : ℕ} (hR : ∀ k, (D.Nset k).card ≤ R)
    (hS : ∑ j : D.cut.Half, (2 ^ (D.Nset j).card - 1) = S) (j : D.cut.Half) :
    ((2 : ℝ) ^ (D.Nset j).card - 1) * ∑ j', ((2 : ℝ) ^ (D.Nset j').card - 1) ≤
      ((2 : ℝ) ^ R - 1) * S := by
  rw [sum_real_eq D hS]
  have h : (2 : ℝ) ^ (D.Nset j).card ≤ 2 ^ R := pow_le_pow_right₀ (by norm_num) (hR j)
  have hS0 : (0 : ℝ) ≤ S := Nat.cast_nonneg S
  exact mul_le_mul_of_nonneg_right (by linarith) hS0

end Transfer

/-! ### LL20 -/

/-- **LL20** (`subsec:push:layer72spectral`): the root `G_{LL,2}` with the chamber cut `ϑ_{0,0}`
of coordinate `0` (plus half `{0, 1, 2}` in coordinate `0`), as spectral data
(`def:spec:data`), with the paper's greedy deletion order (`LL20_orderCodes`). -/
noncomputable def LL20 : Cuts.SpecData Slot where
  G := rootGraph
  cut := firstChamberCut 0
  aut u w := by
    rw [mem_root, mem_root, flip20_edge]
  order := Equiv.ofBijective LL20_orderFun LL20_orderFun_bijective

theorem LL20_G : LL20.G = rootGraph := rfl

theorem LL20_cut : LL20.cut = firstChamberCut 0 := rfl

/-- **(S0) degree bound for LL20**: every vertex has degree at most `Δ = 20`, in the form `hdeg`
of `Sarkozy.SpectralD.Cx`. -/
theorem LL20_hdeg :
    ∀ v, (univ.filter (fun w => (v, w) ∈ LL20.G.E ∨ (w, v) ∈ LL20.G.E)).card ≤ 20 :=
  hdeg_of_root LL20 LL20_G

/-- `Δ = 20` for LL20. -/
theorem LL20_Delta : LL20.Delta = 20 := Delta_eq_twenty LL20 LL20_G

/-- `n = |U⁺| = 36` for LL20. -/
theorem LL20_card_half : Fintype.card LL20.cut.Half = 36 := by
  decide +kernel

/-- `n = 36` for LL20, in the notation `D.n` of `def:spec:data`. -/
theorem LL20_n : LL20.n = 36 := by
  decide +kernel

theorem LL20_r_bool : ∀ k : LL20.cut.Half,
    (univ.filter (fun j : LL20.cut.Half => sgnB LL20.cut.flip j.1 k.1 ≠ 0)).card ≤ 12 := by
  decide +kernel

/-- **The cross degrees of LL20 are `r_k ≤ 12`** (`subsec:push:layer72spectral`). -/
theorem LL20_r_le : ∀ k : LL20.cut.Half, (LL20.Nset k).card ≤ 12 := by
  intro k
  rw [Nset_card_eq LL20 LL20_G]
  exact LL20_r_bool k

theorem LL20_d0_bool : ∀ j : LL20.cut.Half,
    ((univ.erase j).filter
      (fun u : LL20.cut.Half => edgeB u.1 j.1 = true ∨ edgeB j.1 u.1 = true)).card ≤ 10 := by
  decide +kernel

/-- **The internal degrees of LL20 are `d⁰_k ≤ 10`** (`subsec:push:layer72spectral`), in the
form used by `Sarkozy.SpectralD.Cx`. -/
theorem LL20_d0_le : ∀ j : LL20.cut.Half,
    Labellings.nbrCount LL20.halfGraph (univ.erase j) j ≤ 10 := by
  intro j
  rw [nbrCount_eq LL20 LL20_G]
  exact LL20_d0_bool j

theorem LL20_sum_bool :
    ∑ j : LL20.cut.Half,
      (2 ^ (univ.filter (fun i : LL20.cut.Half => sgnB LL20.cut.flip i.1 j.1 ≠ 0)).card - 1) =
      73692 := by
  decide +kernel

/-- `∑_l (2^{r_l} − 1) = 73692` for LL20. -/
theorem LL20_sum : ∑ j : LL20.cut.Half, (2 ^ (LL20.Nset j).card - 1) = 73692 := by
  simp only [Nset_card_eq LL20 LL20_G]
  exact LL20_sum_bool

/-- **`ρ_row` for LL20**: `(2^{r_j} − 1) ∑_l (2^{r_l} − 1) ≤ 4095 · 73692 = 301768740`, in the
form `hρ` of `cor:spec2:coupling` (`Sarkozy.SpectralD.Cx`). -/
theorem LL20_rho : ∀ j : LL20.cut.Half,
    ((2 : ℝ) ^ (LL20.Nset j).card - 1) * ∑ j', ((2 : ℝ) ^ (LL20.Nset j').card - 1) ≤
      301768740 := by
  intro j
  refine (rho_le LL20 LL20_r_le LL20_sum j).trans ?_
  norm_num

/-- The cross degrees of LL20 are exactly `10` or `12`. -/
theorem LL20_r_exact : ∀ k : LL20.cut.Half,
    (LL20.Nset k).card = 10 ∨ (LL20.Nset k).card = 12 := by
  intro k
  rw [Nset_card_eq LL20 LL20_G]
  revert k
  decide +kernel

/-- The internal degrees of LL20 are exactly `8` or `10`. -/
theorem LL20_d0_exact : ∀ j : LL20.cut.Half,
    Labellings.nbrCount LL20.halfGraph (univ.erase j) j = 8 ∨
      Labellings.nbrCount LL20.halfGraph (univ.erase j) j = 10 := by
  intro j
  rw [nbrCount_eq LL20 LL20_G]
  revert j
  decide +kernel

/-- The slot `(1, 0, 0)` of the plus half of LL20; its cross degree is `12`. -/
def LL20_top : LL20.cut.Half := ⟨(1, 0, 0), by decide +kernel⟩

/-- **`ρ_row` for LL20 is attained**: `(2^{12} − 1) · 73692 = 301768740` at `(1, 0, 0)`. -/
theorem LL20_rho_attained :
    ((2 : ℝ) ^ (LL20.Nset LL20_top).card - 1) * ∑ j', ((2 : ℝ) ^ (LL20.Nset j').card - 1) =
      301768740 := by
  have h12 : (LL20.Nset LL20_top).card = 12 := by
    rw [Nset_card_eq LL20 LL20_G]
    decide +kernel
  rw [sum_real_eq LL20 LL20_sum, h12]
  norm_num

/-- The deletion degrees `t_i` of LL20 along its deletion order. -/
def LL20_tList : List ℕ :=
  [20, 19, 19, 18, 18, 17, 17, 16, 16, 16, 16, 16, 16, 15, 15, 14, 16, 16, 16, 15, 15, 14, 16, 15,
    15, 14, 14, 14, 14, 14, 14, 13, 13, 12, 12, 12]

/-- **The deletion degrees of LL20** (`def:spec:data`, `t_i`). -/
theorem LL20_tdeg : ∀ i, LL20.tdeg i = LL20_tList.getD i.val 0 := by
  intro i
  rw [tdeg_eq LL20 LL20_G]
  revert i
  decide +kernel

theorem LL20_prod_tList (g : ℕ → ℝ) : ∏ k ∈ range 36, g (LL20_tList.getD k 0) =
    g 20 * g 19 ^ 2 * g 18 ^ 2 * g 17 ^ 2 * g 16 ^ 10 * g 15 ^ 6 * g 14 ^ 8 * g 13 ^ 2 *
      g 12 ^ 3 := by
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul, LL20_tList,
    List.getD_cons_zero, List.getD_cons_succ]
  ring

/-- **`R_cut` of LL20** (`eq:spec:Rcut`) for any error function `e`: the deletion degrees
`20, 19, 18, 17, 16, 15, 14, 13, 12` occur `1, 2, 2, 2, 10, 6, 8, 2, 3` times. -/
theorem LL20_Rcut (e : ℕ → ℝ) : LL20.Rcut e =
    (1 + e 20) / (1 - e 20) * ((1 + e 19) / (1 - e 19)) ^ 2 * ((1 + e 18) / (1 - e 18)) ^ 2 *
      ((1 + e 17) / (1 - e 17)) ^ 2 * ((1 + e 16) / (1 - e 16)) ^ 10 *
      ((1 + e 15) / (1 - e 15)) ^ 6 * ((1 + e 14) / (1 - e 14)) ^ 8 *
      ((1 + e 13) / (1 - e 13)) ^ 2 * ((1 + e 12) / (1 - e 12)) ^ 3 := by
  rw [Rcut_eq_range LL20 LL20_tList (by decide +kernel) LL20_tdeg]
  exact LL20_prod_tList (fun t => (1 + e t) / (1 - e t))

/-! ### LL22 -/

/-- **LL22** (`subsec:push:layer72spectral`): the root `G_{LL,2}` with the layer cut `ι`
(plus half the layer `ℓ = 0`), as spectral data (`def:spec:data`), with the paper's greedy
deletion order (`LL22_orderCodes`). -/
noncomputable def LL22 : Cuts.SpecData Slot where
  G := rootGraph
  cut := reservedCut
  aut u w := by
    rw [mem_root, mem_root, flip22_edge]
  order := Equiv.ofBijective LL22_orderFun LL22_orderFun_bijective

theorem LL22_G : LL22.G = rootGraph := rfl

theorem LL22_cut : LL22.cut = reservedCut := rfl

/-- **(S0) degree bound for LL22**: every vertex has degree at most `Δ = 20`, in the form `hdeg`
of `Sarkozy.SpectralD.Cx`. -/
theorem LL22_hdeg :
    ∀ v, (univ.filter (fun w => (v, w) ∈ LL22.G.E ∨ (w, v) ∈ LL22.G.E)).card ≤ 20 :=
  hdeg_of_root LL22 LL22_G

/-- `Δ = 20` for LL22. -/
theorem LL22_Delta : LL22.Delta = 20 := Delta_eq_twenty LL22 LL22_G

/-- `n = |U⁺| = 36` for LL22. -/
theorem LL22_card_half : Fintype.card LL22.cut.Half = 36 := by
  decide +kernel

/-- `n = 36` for LL22, in the notation `D.n` of `def:spec:data`. -/
theorem LL22_n : LL22.n = 36 := by
  decide +kernel

theorem LL22_r_bool : ∀ k : LL22.cut.Half,
    (univ.filter (fun j : LL22.cut.Half => sgnB LL22.cut.flip j.1 k.1 ≠ 0)).card ≤ 10 := by
  decide +kernel

/-- **The cross degrees of LL22 are `r_k ≤ 10`** (`subsec:push:layer72spectral`). -/
theorem LL22_r_le : ∀ k : LL22.cut.Half, (LL22.Nset k).card ≤ 10 := by
  intro k
  rw [Nset_card_eq LL22 LL22_G]
  exact LL22_r_bool k

theorem LL22_d0_bool : ∀ j : LL22.cut.Half,
    ((univ.erase j).filter
      (fun u : LL22.cut.Half => edgeB u.1 j.1 = true ∨ edgeB j.1 u.1 = true)).card ≤ 10 := by
  decide +kernel

/-- **The internal degrees of LL22 are `d⁰_k ≤ 10`** (`subsec:push:layer72spectral`), in the
form used by `Sarkozy.SpectralD.Cx`. -/
theorem LL22_d0_le : ∀ j : LL22.cut.Half,
    Labellings.nbrCount LL22.halfGraph (univ.erase j) j ≤ 10 := by
  intro j
  rw [nbrCount_eq LL22 LL22_G]
  exact LL22_d0_bool j

theorem LL22_sum_bool :
    ∑ j : LL22.cut.Half,
      (2 ^ (univ.filter (fun i : LL22.cut.Half => sgnB LL22.cut.flip i.1 j.1 ≠ 0)).card - 1) =
      36828 := by
  decide +kernel

/-- `∑_l (2^{r_l} − 1) = 36828` for LL22. -/
theorem LL22_sum : ∑ j : LL22.cut.Half, (2 ^ (LL22.Nset j).card - 1) = 36828 := by
  simp only [Nset_card_eq LL22 LL22_G]
  exact LL22_sum_bool

/-- **`ρ_row` for LL22**: `(2^{r_j} − 1) ∑_l (2^{r_l} − 1) ≤ 1023 · 36828 = 37675044`, in the
form `hρ` of `cor:spec2:coupling` (`Sarkozy.SpectralD.Cx`). -/
theorem LL22_rho : ∀ j : LL22.cut.Half,
    ((2 : ℝ) ^ (LL22.Nset j).card - 1) * ∑ j', ((2 : ℝ) ^ (LL22.Nset j').card - 1) ≤
      37675044 := by
  intro j
  refine (rho_le LL22 LL22_r_le LL22_sum j).trans ?_
  norm_num

/-- The cross degrees of LL22 are all exactly `10`. -/
theorem LL22_r_exact : ∀ k : LL22.cut.Half, (LL22.Nset k).card = 10 := by
  intro k
  rw [Nset_card_eq LL22 LL22_G]
  revert k
  decide +kernel

/-- The internal degrees of LL22 are all exactly `10`. -/
theorem LL22_d0_exact : ∀ j : LL22.cut.Half,
    Labellings.nbrCount LL22.halfGraph (univ.erase j) j = 10 := by
  intro j
  rw [nbrCount_eq LL22 LL22_G]
  revert j
  decide +kernel

/-- The slot `(0, 0, 0)` of the plus half of LL22; its cross degree is `10`. -/
def LL22_top : LL22.cut.Half := ⟨(0, 0, 0), by decide +kernel⟩

/-- **`ρ_row` for LL22 is attained**: `(2^{10} − 1) · 36828 = 37675044` at `(0, 0, 0)`. -/
theorem LL22_rho_attained :
    ((2 : ℝ) ^ (LL22.Nset LL22_top).card - 1) * ∑ j', ((2 : ℝ) ^ (LL22.Nset j').card - 1) =
      37675044 := by
  have h10 : (LL22.Nset LL22_top).card = 10 := by
    rw [Nset_card_eq LL22 LL22_G]
    decide +kernel
  rw [sum_real_eq LL22 LL22_sum, h10]
  norm_num

/-- The deletion degrees `t_i` of LL22 along its deletion order. -/
def LL22_tList : List ℕ :=
  [20, 19, 18, 18, 18, 18, 17, 17, 17, 16, 16, 16, 17, 16, 17, 16, 15, 15, 15, 15, 15, 15, 14, 14,
    13, 13, 13, 12, 13, 13, 13, 12, 12, 11, 11, 10]

/-- **The deletion degrees of LL22** (`def:spec:data`, `t_i`). -/
theorem LL22_tdeg : ∀ i, LL22.tdeg i = LL22_tList.getD i.val 0 := by
  intro i
  rw [tdeg_eq LL22 LL22_G]
  revert i
  decide +kernel

theorem LL22_prod_tList (g : ℕ → ℝ) : ∏ k ∈ range 36, g (LL22_tList.getD k 0) =
    g 20 * g 19 * g 18 ^ 4 * g 17 ^ 5 * g 16 ^ 5 * g 15 ^ 6 * g 14 ^ 2 * g 13 ^ 6 * g 12 ^ 3 *
      g 11 ^ 2 * g 10 := by
  simp only [Finset.prod_range_succ, Finset.prod_range_zero, one_mul, LL22_tList,
    List.getD_cons_zero, List.getD_cons_succ]
  ring

/-- **`R_cut` of LL22** (`eq:spec:Rcut`) for any error function `e`: the deletion degrees
`20, 19, …, 10` occur `1, 1, 4, 5, 5, 6, 2, 6, 3, 2, 1` times. -/
theorem LL22_Rcut (e : ℕ → ℝ) : LL22.Rcut e =
    (1 + e 20) / (1 - e 20) * ((1 + e 19) / (1 - e 19)) * ((1 + e 18) / (1 - e 18)) ^ 4 *
      ((1 + e 17) / (1 - e 17)) ^ 5 * ((1 + e 16) / (1 - e 16)) ^ 5 *
      ((1 + e 15) / (1 - e 15)) ^ 6 * ((1 + e 14) / (1 - e 14)) ^ 2 *
      ((1 + e 13) / (1 - e 13)) ^ 6 * ((1 + e 12) / (1 - e 12)) ^ 3 *
      ((1 + e 11) / (1 - e 11)) ^ 2 * ((1 + e 10) / (1 - e 10)) := by
  rw [Rcut_eq_range LL22 LL22_tList (by decide +kernel) LL22_tdeg]
  exact LL22_prod_tList (fun t => (1 + e t) / (1 - e t))

end Sarkozy.SpectralD.Root
