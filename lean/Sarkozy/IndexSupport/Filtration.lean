module

public import Sarkozy.IndexSupport.Abstract
public import Sarkozy.ProbabilityProducts

/-!
# Chains of conditional expectations, depth laws, and the Index-support lemma

This file instantiates the abstract index-support inequality
(`Sarkozy/IndexSupport/Abstract.lean`) in the setting of `lem:record:common-mean`
(Index-support lemma) of the paper.

* `Chain Ω`: a chain `E_0 ≤ E_1 ≤ ⋯ ≤ E_h = I` of orthogonal projections on the functions
  on a finite set `Ω` (symmetric matrices with `E_l E_{l'} = E_{min(l,l')}`), with `E_0`
  the projection onto the constants. A chain of conditional-expectation projections is
  such a chain (`Chain.ofLabels`: conditional expectations, for the uniform law, given
  a nested sequence of labelings; `Chain.residues`: conditioning a residue modulo `p^h`
  on its residues modulo `p^l`, `0 ≤ l ≤ h`; `Chain.whole`: the two-step chain of the
  constants and the identity, the whole-coordinate case).
  The paper's `h_j ≥ 1` is not needed and is not assumed.
* `Chain.diff`: `Π_0 = E_0`, `Π_l = E_l - E_{l-1}`, and `Chain.sectors`: the resulting
  sector system on `Ω` indexed by `Fin (h + 1)`.
* `Tails h`: tails `1 = δ_0 ≥ δ_1 ≥ ⋯ ≥ δ_h ≥ 0`, and `Tails.law`: the law of a depth
  `J ∈ {0,…,h}` with `Pr(J ≥ l) = δ_l` (`Tails.prob_ge`).
* For a finite family of coordinates: the product sectors
  `H_l = ⊗_j ran Π_{j,l_j}` (`productSectors`), independent depths `𝒥 = (J_j)_j`
  (`depthLaw`), the revealed projection `Z^𝒥 = (⊗_j E_{j,J_j}) Z` (`depthReveal`), and
  the energies `V_M(Z) = E_𝒥 E_ω ⟨Z^𝒥(ω), M Z^𝒥(ω)⟩` (`depthEnergy`).

Main theorem: `index_support_lemma` (`lem:record:common-mean`, in the paper's
generality, with chains of orthogonal projections in place of conditional
expectations): `V_L ≥ e_L ≥ 0`, `V_R ≥ e_R ≥ 0`, (a) and (b).
-/

@[expose] public section

open Finset
open scoped BigOperators Matrix

namespace Sarkozy.IndexSupport

/-- A chain `E_0 ≤ E_1 ≤ ⋯ ≤ E_h = I` of orthogonal projections on the real functions on a
finite set, with `E_0` the projection onto the constants. The matrices `cond l` for
`l > depth` are irrelevant. -/
structure Chain (Ω : Type*) [Fintype Ω] [DecidableEq Ω] where
  depth : ℕ
  cond : ℕ → Matrix Ω Ω ℝ
  transpose_cond : ∀ l, l ≤ depth → (cond l)ᵀ = cond l
  cond_mul_cond : ∀ l l', l ≤ depth → l' ≤ depth → cond l * cond l' = cond (min l l')
  cond_zero : cond 0 = meanMatrix Ω
  cond_top : cond depth = 1

namespace Chain

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω]

/-- The differences `Π_0 = E_0` and `Π_l = E_l - E_{l-1}` (the exact-depth projections). -/
def diff (C : Chain Ω) (l : ℕ) : Matrix Ω Ω ℝ :=
  if l = 0 then C.cond 0 else C.cond l - C.cond (l - 1)

theorem transpose_diff (C : Chain Ω) {l : ℕ} (hl : l ≤ C.depth) : (C.diff l)ᵀ = C.diff l := by
  unfold diff
  split_ifs with h
  · exact C.transpose_cond 0 (Nat.zero_le _)
  · rw [Matrix.transpose_sub, C.transpose_cond l hl, C.transpose_cond (l - 1) (by omega)]

theorem diff_mul_diff (C : Chain Ω) {l l' : ℕ} (hl : l ≤ C.depth) (hl' : l' ≤ C.depth) :
    C.diff l * C.diff l' = if l = l' then C.diff l else 0 := by
  have hm := C.cond_mul_cond
  rcases Nat.lt_trichotomy l l' with hlt | heq | hgt
  · rw [ite_eq_right (show l ≠ l' by omega)]
    unfold diff
    rw [ite_eq_right (show l' ≠ 0 by omega)]
    by_cases h0 : l = 0
    · rw [ite_eq_left h0, Matrix.mul_sub, hm 0 l' (Nat.zero_le _) hl',
        hm 0 (l' - 1) (Nat.zero_le _) (by omega), Nat.zero_min, Nat.zero_min, sub_self]
    · rw [ite_eq_right h0, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hm l l' hl hl',
        hm l (l' - 1) hl (by omega), hm (l - 1) l' (by omega) hl',
        hm (l - 1) (l' - 1) (by omega) (by omega), show min l l' = l by omega,
        show min l (l' - 1) = l by omega, show min (l - 1) l' = l - 1 by omega,
        show min (l - 1) (l' - 1) = l - 1 by omega]
      abel
  · subst heq
    rw [ite_eq_left rfl]
    unfold diff
    by_cases h0 : l = 0
    · rw [ite_eq_left h0, hm 0 0 (Nat.zero_le _) (Nat.zero_le _), min_self]
    · rw [ite_eq_right h0, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hm l l hl hl,
        hm l (l - 1) hl (by omega), hm (l - 1) l (by omega) hl,
        hm (l - 1) (l - 1) (by omega) (by omega), min_self, min_self,
        show min l (l - 1) = l - 1 by omega, show min (l - 1) l = l - 1 by omega]
      abel
  · rw [ite_eq_right (show l ≠ l' by omega)]
    unfold diff
    rw [ite_eq_right (show l ≠ 0 by omega)]
    by_cases h0' : l' = 0
    · rw [ite_eq_left h0', Matrix.sub_mul, hm l 0 hl (Nat.zero_le _),
        hm (l - 1) 0 (by omega) (Nat.zero_le _), Nat.min_zero, Nat.min_zero, sub_self]
    · rw [ite_eq_right h0', Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_sub, hm l l' hl hl',
        hm l (l' - 1) hl (by omega), hm (l - 1) l' (by omega) hl',
        hm (l - 1) (l' - 1) (by omega) (by omega), show min l l' = l' by omega,
        show min l (l' - 1) = l' - 1 by omega, show min (l - 1) l' = l' by omega,
        show min (l - 1) (l' - 1) = l' - 1 by omega]
      abel

/-- Telescoping: `∑_{l ≤ L} Π_l = E_L`. -/
theorem sum_diff (C : Chain Ω) {L : ℕ} (_hL : L ≤ C.depth) :
    ∑ l ∈ range (L + 1), C.diff l = C.cond L := by
  induction L with
  | zero => simp [diff]
  | succ L ih =>
    rw [Finset.sum_range_succ, ih (by omega), diff, ite_eq_right (Nat.succ_ne_zero L),
      Nat.add_sub_cancel]
    abel

/-- The sector system of a chain: sectors indexed by the exact depth `l ∈ {0,…,h}`,
with projections `Π_l`. -/
def sectors (C : Chain Ω) : SectorSystem Ω (Fin (C.depth + 1)) where
  proj l := C.diff l
  zero := 0
  transpose_proj l := C.transpose_diff (by omega)
  proj_mul_proj s t := by
    rw [C.diff_mul_diff (by omega) (by omega)]
    by_cases h : s = t
    · rw [ite_eq_left h, ite_eq_left (congrArg Fin.val h)]
    · rw [ite_eq_right h, ite_eq_right (fun h' => h (Fin.ext h'))]
  sum_proj := by
    rw [Fin.sum_univ_eq_sum_range (fun l => C.diff l) (C.depth + 1), C.sum_diff le_rfl,
      C.cond_top]
  proj_zero := by
    change C.diff 0 = _
    rw [diff, ite_eq_left rfl, C.cond_zero]

theorem sectors_proj (C : Chain Ω) (l : Fin (C.depth + 1)) : C.sectors.proj l = C.diff l := rfl

/-- `E_J = ∑_{l ≤ J} Π_l`, as a sum over sectors. -/
theorem sum_sectors_le (C : Chain Ω) (J : Fin (C.depth + 1)) :
    ∑ u ∈ univ.filter (fun u : Fin (C.depth + 1) => u ≤ J), C.sectors.proj u = C.cond J := by
  rw [Finset.sum_filter]
  have h := Fin.sum_univ_eq_sum_range (fun l => if l ≤ (J : ℕ) then C.diff l else 0)
    (C.depth + 1)
  simp only [sectors_proj]
  have he : (∑ u : Fin (C.depth + 1), if u ≤ J then C.diff u else 0) =
      ∑ u : Fin (C.depth + 1), if (u : ℕ) ≤ (J : ℕ) then C.diff u else 0 := by
    apply sum_congr rfl
    intro u _
    simp only [Fin.le_iff_val_le_val]
  rw [he, h, ← Finset.sum_filter]
  have hr : (range (C.depth + 1)).filter (fun l => l ≤ (J : ℕ)) = range ((J : ℕ) + 1) := by
    ext l
    simp only [mem_filter, mem_range]
    omega
  rw [hr, C.sum_diff (by omega)]

/-- The whole-coordinate chain `E_0 = average`, `E_1 = I` (Bernoulli inclusion). -/
noncomputable def whole (Ω : Type*) [Fintype Ω] [DecidableEq Ω] [Nonempty Ω] : Chain Ω where
  depth := 1
  cond l := if l = 0 then meanMatrix Ω else 1
  transpose_cond l _ := by
    split_ifs
    · exact meanMatrix_transpose Ω
    · exact Matrix.transpose_one
  cond_mul_cond l l' hl hl' := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hl with rfl | rfl <;>
      rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hl' with rfl | rfl <;>
      simp [meanMatrix_mul_self]
  cond_zero := by simp
  cond_top := by simp

end Chain

/-- Decreasing depth tails `1 = δ_0 ≥ δ_1 ≥ ⋯ ≥ δ_h ≥ 0`. -/
structure Tails (h : ℕ) where
  tail : ℕ → ℝ
  tail_zero : tail 0 = 1
  antitone : ∀ l, l < h → tail (l + 1) ≤ tail l
  nonneg : 0 ≤ tail h

namespace Tails

variable {h : ℕ}

/-- The tails extended by zero beyond `h` (the paper's `δ_{h+1} = 0`). -/
def ext (t : Tails h) (l : ℕ) : ℝ := if l ≤ h then t.tail l else 0

theorem ext_sub_nonneg (t : Tails h) (l : ℕ) (hl : l ≤ h) : 0 ≤ t.ext l - t.ext (l + 1) := by
  unfold ext
  rcases Nat.lt_or_ge l h with hlt | hge
  · rw [ite_eq_left hl, ite_eq_left (by omega)]
    linarith [t.antitone l hlt]
  · have hlh : l = h := le_antisymm hl hge
    subst hlh
    rw [ite_eq_left le_rfl, ite_eq_right (by omega)]
    linarith [t.nonneg]

/-- The law of a depth `J ∈ {0,…,h}` with `Pr(J = l) = δ_l - δ_{l+1}`. -/
noncomputable def law (t : Tails h) : FiniteLaw (Fin (h + 1)) where
  weight u := t.ext u - t.ext (u + 1)
  nonneg u := t.ext_sub_nonneg u (by omega)
  total := by
    rw [Fin.sum_univ_eq_sum_range (fun l => t.ext l - t.ext (l + 1)) (h + 1),
      Finset.sum_range_sub']
    simp [ext, t.tail_zero]

theorem sum_Ico_weight (t : Tails h) {l : ℕ} (hl : l ≤ h) :
    ∑ i ∈ Finset.Ico l (h + 1), (t.ext i - t.ext (i + 1)) = t.tail l := by
  have h1 := Finset.sum_range_sub' (fun i => t.ext i) (h + 1)
  have h2 := Finset.sum_range_sub' (fun i => t.ext i) l
  rw [Finset.sum_Ico_eq_sub _ (by omega), h1, h2]
  simp only [ext, ite_eq_left hl, ite_eq_right (show ¬ h + 1 ≤ h by omega)]
  ring

/-- `Pr(J ≥ l) = δ_l`. -/
theorem prob_ge (t : Tails h) (l : Fin (h + 1)) :
    t.law.expect (fun u => if l ≤ u then 1 else 0) = t.tail l := by
  have h1 : t.law.expect (fun u => if l ≤ u then 1 else 0) =
      ∑ u : Fin (h + 1),
        (fun i : ℕ => if (l : ℕ) ≤ i then t.ext i - t.ext (i + 1) else 0) (u : ℕ) := by
    simp only [FiniteLaw.expect, law]
    apply sum_congr rfl
    intro u _
    simp only [Fin.le_iff_val_le_val, mul_ite, mul_one, mul_zero]
  rw [h1, Fin.sum_univ_eq_sum_range
    (fun i => if (l : ℕ) ≤ i then t.ext i - t.ext (i + 1) else 0) (h + 1),
    ← Finset.sum_filter]
  have hset : (range (h + 1)).filter (fun i => (l : ℕ) ≤ i) = Ico (l : ℕ) (h + 1) := by
    ext i
    simp only [mem_filter, mem_range, mem_Ico]
    omega
  rw [hset, t.sum_Ico_weight (by omega)]

end Tails

section Product

variable {K : Type*} [Fintype K] [DecidableEq K] {Ω : K → Type*} [∀ j, Fintype (Ω j)]
  [∀ j, DecidableEq (Ω j)]

/-- The exact-depth sectors `H_l = ⊗_j ran Π_{j,l_j}` of a family of chains. -/
def productSectors (C : ∀ j, Chain (Ω j)) :
    SectorSystem (∀ j, Ω j) (∀ j, Fin ((C j).depth + 1)) :=
  SectorSystem.pi (fun j => (C j).sectors)

theorem productSectors_proj (C : ∀ j, Chain (Ω j)) (l : ∀ j, Fin ((C j).depth + 1)) :
    (productSectors C).proj l = piKron (fun j => (C j).diff (l j)) := rfl

/-- The law of independent depths `J_j` with `Pr(J_j ≥ l) = δ_{j,l}`. -/
noncomputable def depthLaw (C : ∀ j, Chain (Ω j)) (t : ∀ j, Tails (C j).depth) :
    FiniteLaw (∀ j, Fin ((C j).depth + 1)) :=
  FiniteLaw.pi (fun j => (t j).law)

/-- The revealed projection `Z^𝒥 = (⊗_j E_{j,J_j}) Z`. -/
def depthReveal {ι : Type*} (C : ∀ j, Chain (Ω j)) (J : ∀ j, Fin ((C j).depth + 1))
    (Z : (∀ j, Ω j) → ι → ℝ) : (∀ j, Ω j) → ι → ℝ :=
  act (piKron (fun j => (C j).cond (J j))) Z

/-- The random-inclusion (depth) energy `V_M(Z) = E_𝒥 E_ω ⟨Z^𝒥(ω), M Z^𝒥(ω)⟩`. -/
noncomputable def depthEnergy {ι : Type*} [Fintype ι] (C : ∀ j, Chain (Ω j))
    (t : ∀ j, Tails (C j).depth) (M : Matrix ι ι ℝ) (Z : (∀ j, Ω j) → ι → ℝ) : ℝ :=
  (depthLaw C t).expect (fun J => pairing M (depthReveal C J Z) (depthReveal C J Z))

/-- The sector weights `δ_l = ∏_j δ_{j,l_j}`. -/
def sectorWeight (C : ∀ j, Chain (Ω j)) (t : ∀ j, Tails (C j).depth)
    (l : ∀ j, Fin ((C j).depth + 1)) : ℝ :=
  ∏ j, (t j).tail (l j)

/-- The depth revelation: depth vector `𝒥` retains the sectors `l ≤ 𝒥`. -/
noncomputable def depthRevelation (C : ∀ j, Chain (Ω j)) (t : ∀ j, Tails (C j).depth) :
    Revelation (productSectors C) (∀ j, Fin ((C j).depth + 1)) where
  law := depthLaw C t
  retained J := univ.filter (fun l => ∀ j, l j ≤ J j)
  zero_mem J := by
    simp only [mem_filter, mem_univ, true_and]
    intro j
    exact Fin.zero_le _

theorem depthRevelation_reveal {ι : Type*} (C : ∀ j, Chain (Ω j)) (t : ∀ j, Tails (C j).depth)
    (J : ∀ j, Fin ((C j).depth + 1)) (Z : (∀ j, Ω j) → ι → ℝ) :
    (depthRevelation C t).reveal J Z = depthReveal C J Z := by
  have hset : univ.filter (fun l : ∀ j, Fin ((C j).depth + 1) => ∀ j, l j ≤ J j) =
      Fintype.piFinset (fun j => univ.filter (fun u => u ≤ J j)) := by
    ext l
    simp only [mem_filter, mem_univ, true_and, Fintype.mem_piFinset]
  unfold Revelation.reveal depthReveal
  congr 1
  change ∑ l ∈ univ.filter (fun l : ∀ j, Fin ((C j).depth + 1) => ∀ j, l j ≤ J j),
    (productSectors C).proj l = _
  rw [hset]
  simp only [productSectors_proj]
  rw [piKron_sum_piFinset (fun j => univ.filter (fun u => u ≤ J j))
    (fun j u => (C j).diff u)]
  congr 1
  funext j
  exact (C j).sum_sectors_le (J j)

theorem depthRevelation_energy {ι : Type*} [Fintype ι] (C : ∀ j, Chain (Ω j))
    (t : ∀ j, Tails (C j).depth) (M : Matrix ι ι ℝ) (Z : (∀ j, Ω j) → ι → ℝ) :
    (depthRevelation C t).energy M Z = depthEnergy C t M Z := by
  unfold Revelation.energy depthEnergy
  simp only [depthRevelation_reveal]
  rfl

/-- Independence gives `Pr(𝒥 ≥ l) = ∏_j δ_{j,l_j}`. -/
theorem depthRevelation_prob (C : ∀ j, Chain (Ω j)) (t : ∀ j, Tails (C j).depth)
    (l : ∀ j, Fin ((C j).depth + 1)) :
    (depthRevelation C t).prob l = sectorWeight C t l := by
  unfold Revelation.prob sectorWeight
  have he : (fun J : ∀ j, Fin ((C j).depth + 1) =>
      if l ∈ (depthRevelation C t).retained J then (1 : ℝ) else 0) =
      fun J => ∏ j, (if l j ≤ J j then (1 : ℝ) else 0) := by
    funext J
    rw [prod_indicator_forall]
    simp only [depthRevelation, mem_filter, mem_univ, true_and]
  rw [he]
  change (FiniteLaw.pi (fun j => (t j).law)).expect _ = _
  rw [FiniteLaw.expect_pi_product (fun j => (t j).law) (fun j u => if l j ≤ u then 1 else 0)]
  apply prod_congr rfl
  intro j _
  exact (t j).prob_ge (l j)

end Product

/-- **Index-support lemma** (`lem:record:common-mean`).

Let `𝒳_+ = ι` be a finite set and `M_L, M_R, Γ` real matrices on it with the joint Gram
matrix `[[M_L, Γ], [Γᵀ, M_R]] ⪰ 0` (`eq:record:joint-gram`; it forces `M_L, M_R`
symmetric). Let `Ω = ∏_j Ω_j` be a finite product of nonempty finite sets with the uniform
probability, and on each coordinate a chain `E_{j,0} ≤ ⋯ ≤ E_{j,h_j} = I` of orthogonal
projections with `E_{j,0}` the projection onto constants; `Π_{j,l}` the differences and
`H_l = ⊗_j ran Π_{j,l_j}`. Choose tails `1 = δ_{j,0} ≥ ⋯ ≥ δ_{j,h_j} ≥ 0`,
`δ_l = ∏_j δ_{j,l_j}`. Let `𝒯` preserve every `H_l`, act as the identity on `H_0`, and
have norm at most `δ_l` on `H_l`; it acts componentwise on vector-valued maps. With
independent depths `Pr(J_j ≥ l) = δ_{j,l}`, `Z^𝒥 = (⊗_j E_{j,J_j}) Z`,
`𝖩 = E_ω⟨X, Γ 𝒯 Y⟩`, `e_L = ⟨E X, M_L E X⟩`, `e_R = ⟨E Y, M_R E Y⟩`,
`V_L = E_𝒥 E_ω ⟨X^𝒥, M_L X^𝒥⟩`, `V_R = E_𝒥 E_ω ⟨Y^𝒥, M_R Y^𝒥⟩`:
`V_L ≥ e_L ≥ 0`, `V_R ≥ e_R ≥ 0`, (a) `|𝖩 - ⟨E X, Γ E Y⟩| ≤ ½[(V_L - e_L) + (V_R - e_R)]`,
(b) `|𝖩| ≤ V_L^{1/2} V_R^{1/2}`. -/
theorem index_support_lemma {K : Type*} [Fintype K] [DecidableEq K] {Ω : K → Type*}
    [∀ j, Fintype (Ω j)] [∀ j, DecidableEq (Ω j)] [∀ j, Nonempty (Ω j)]
    {ι : Type*} [Fintype ι]
    (C : ∀ j, Chain (Ω j)) (t : ∀ j, Tails (C j).depth)
    (T : Matrix (∀ j, Ω j) (∀ j, Ω j) ℝ)
    (hTmaps : ∀ l f, (productSectors C).proj l *ᵥ f = f →
      (productSectors C).proj l *ᵥ (T *ᵥ f) = T *ᵥ f)
    (hTid : ∀ f, (productSectors C).proj (fun _ => 0) *ᵥ f = f → T *ᵥ f = f)
    (hTnorm : ∀ l f, (productSectors C).proj l *ᵥ f = f →
      (T *ᵥ f) ⬝ᵥ (T *ᵥ f) ≤ sectorWeight C t l ^ 2 * (f ⬝ᵥ f))
    {ML Γ MR : Matrix ι ι ℝ} (hG : (Matrix.fromBlocks ML Γ Γᵀ MR).PosSemidef)
    (X Y : (∀ j, Ω j) → ι → ℝ) :
    vmean X ⬝ᵥ (ML *ᵥ vmean X) ≤ depthEnergy C t ML X ∧ 0 ≤ vmean X ⬝ᵥ (ML *ᵥ vmean X) ∧
    vmean Y ⬝ᵥ (MR *ᵥ vmean Y) ≤ depthEnergy C t MR Y ∧ 0 ≤ vmean Y ⬝ᵥ (MR *ᵥ vmean Y) ∧
    |pairing Γ X (act T Y) - vmean X ⬝ᵥ (Γ *ᵥ vmean Y)| ≤
      (1 / 2) * ((depthEnergy C t ML X - vmean X ⬝ᵥ (ML *ᵥ vmean X)) +
        (depthEnergy C t MR Y - vmean Y ⬝ᵥ (MR *ᵥ vmean Y))) ∧
    |pairing Γ X (act T Y)| ≤
      Real.sqrt (depthEnergy C t ML X) * Real.sqrt (depthEnergy C t MR Y) := by
  set V := depthRevelation C t
  have hT : SectorOperator (productSectors C) T (sectorWeight C t) :=
    ⟨hTmaps, hTid, hTnorm⟩
  have hδ0 (l : ∀ j, Fin ((C j).depth + 1)) : 0 ≤ sectorWeight C t l := by
    apply Finset.prod_nonneg
    intro j _
    have h1 := (t j).ext_sub_nonneg
    have hmono : ∀ m, m ≤ (C j).depth → 0 ≤ (t j).tail m := by
      intro m hm
      have hsum := (t j).sum_Ico_weight hm
      rw [← hsum]
      exact Finset.sum_nonneg (fun i hi => h1 i (by simp only [mem_Ico] at hi; omega))
    exact hmono _ (by omega)
  have hδ (l : ∀ j, Fin ((C j).depth + 1)) : sectorWeight C t l ≤ V.prob l :=
    (depthRevelation_prob C t l).symm.le
  have hML := joint_left hG
  have hMR := joint_right hG
  have hX := mean_le_energy V hML X
  have hY := mean_le_energy V hMR Y
  rw [depthRevelation_energy] at hX hY
  refine ⟨hX.1, hX.2, hY.1, hY.2, ?_, ?_⟩
  · have h := common_mean V hδ0 hδ hT hG X Y
    rwa [depthRevelation_energy, depthRevelation_energy] at h
  · have h := form_le_energies V hδ0 hδ hT hG X Y
    rwa [depthRevelation_energy, depthRevelation_energy] at h

end Sarkozy.IndexSupport
