module

public import Sarkozy.ExtractionK.SingletonRecords
public import Sarkozy.SpectralD.TailCounts

/-!
# Uniform extraction counts for halves with at most eighteen vertices

These bounds deliberately use only the size of the half. They apply to
the nine smaller tail cuts and leave ample room at p ≥ 2^512.
-/

@[expose] public section

namespace Sarkozy.SpectralD

open Finset Sarkozy.Extraction Sarkozy.ExtractionK Sarkozy.Labellings

variable {U : Type*} [Fintype U] [DecidableEq U]

theorem small_rowsDeg (G : OrientedGraph U) (hn : Fintype.card U ≤ 18) (i : U) :
    rowsDeg0 G i ≤ 18 := (card_le_univ _).trans hn

theorem small_cmpDeg (G : OrientedGraph U) (ς : U → U → ℤ)
    (hn : Fintype.card U ≤ 18) (i : U) : cmpDeg G ς i ≤ 36 := by
  have hd := small_rowsDeg G hn i
  have hr := (card_le_univ (rowsN ς i)).trans hn
  unfold cmpDeg
  omega

theorem small_rowsCU (G : OrientedGraph U) (ς : U → U → ℤ)
    (hn : Fintype.card U ≤ 18) (i j : U) : rowsCU G ς i j ≤ 18 :=
  (card_filter_le _ _).trans (small_rowsDeg G hn i)

theorem small_cmpJsp (G : OrientedGraph U) (ς : U → U → ℤ)
    (hn : Fintype.card U ≤ 18) : cmpJsp G ς ≤ 2 ^ 82 := by
  have hc : (Fintype.card U : ℝ) ≤ 18 := by exact_mod_cast hn
  have he : ∀ i j, cmpDeg G ς i + rowsCU G ς i j + rowsCU G ς j i ≤ 72 := by
    intro i j
    have := small_cmpDeg G ς hn i
    have := small_rowsCU G ς hn i j
    have := small_rowsCU G ς hn j i
    omega
  calc cmpJsp G ς ≤ ∑ _i : U, ∑ _j : U, (2 : ℝ) ^ 72 := by
          apply sum_le_sum
          intro i _
          exact sum_le_sum fun j _ => pow_le_pow_right₀ (by norm_num) (he i j)
    _ = (Fintype.card U : ℝ) * ((Fintype.card U : ℝ) * 2 ^ 72) := by
          simp only [sum_const, card_univ, nsmul_eq_mul]
    _ ≤ 18 * (18 * (2 : ℝ) ^ 72) :=
          mul_le_mul hc (mul_le_mul_of_nonneg_right hc (by positivity))
            (by positivity) (by norm_num)
    _ ≤ _ := by norm_num

theorem small_av_bound {n : ℕ} (hn : n ≤ 18) : av n ≤ 2 ^ 19 := by
  have hd : (1 : ℝ) ≤ n + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
  have hpow : (2 : ℝ) ^ (n + 1) ≤ 2 ^ 19 :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  unfold av
  apply (div_le_iff₀ (by positivity)).mpr
  have hm : (2 : ℝ) ^ 19 ≤ 2 ^ 19 * ((n : ℝ) + 1) :=
    le_mul_of_one_le_right (by positivity) hd
  linarith

theorem small_cmpOc_empty (G : OrientedGraph U) (hn : Fintype.card U ≤ 18)
    (V W : Finset U) : cmpOc G ∅ V W (univ \ V) (univ \ W) ≤ 2 ^ 25 := by
  have hsum : ∀ C : Finset U, ∑ i ∈ C, av (nbrCount G C i) ≤ 18 * (2 : ℝ) ^ 19 := by
    intro C
    have hc : (C.card : ℝ) ≤ 18 := by exact_mod_cast (card_le_univ C).trans hn
    calc _ ≤ ∑ _i ∈ C, (2 : ℝ) ^ 19 := sum_le_sum fun i _ =>
            small_av_bound ((coverRow_nbrCount_le G C i).trans (small_rowsDeg G hn i))
      _ = C.card * (2 : ℝ) ^ 19 := by rw [sum_const, nsmul_eq_mul]
      _ ≤ _ := mul_le_mul_of_nonneg_right hc (by positivity)
  unfold cmpOc cmpHx cmpHz
  simp only [union_sdiff_of_subset (subset_univ V), union_sdiff_of_subset (subset_univ W),
    sdiff_self]
  simp only [notMem_empty, filter_false, card_empty, pow_zero, one_mul]
  simp only [bot_eq_empty, sum_empty, add_zero]
  change (∑ i ∈ univ \ V, av (nbrCount G (univ \ V) i)) +
    (∑ i ∈ univ \ W, av (nbrCount G (univ \ W) i)) ≤ (2 : ℝ) ^ 25
  exact (add_le_add (hsum (univ \ V)) (hsum (univ \ W))).trans (by norm_num)

theorem small_cmp_edges (G : OrientedGraph U) (hn : Fintype.card U ≤ 18)
    (V C : Finset U) (hVC : ∀ v ∈ V, v ∉ C) :
    edgesIn G V + edgesBetween G V C ≤ V.card * 18 := by
  obtain ⟨ord, hi, h0, _, h2, _⟩ := cmp_exists_order G V C hVC (fun _ => 0)
  rw [← cmp_sum_ordT G V C ord hi hVC (fun a ha v hv => h0 a ha v (hVC v hv)) h2]
  calc _ ≤ ∑ _v ∈ V, 18 := sum_le_sum fun v _ =>
          (ordT_le_deg G ord v).trans (small_rowsDeg G hn v)
    _ = _ := by simp only [sum_const, smul_eq_mul]

theorem small_cmpEx_empty (G : OrientedGraph U) (hn : Fintype.card U ≤ 18)
    {S : Finset (U × U)} {w : Fin 2 → U × U} (hw : IsWitness S S ∅ w) :
    cmpEx G ∅ (witV w) (witW w) (univ \ witV w) (univ \ witW w) ≤ 72 := by
  have hV := small_cmp_edges G hn (witV w) (univ \ witV w)
    (fun v hv h => (mem_sdiff.mp h).2 hv)
  have hW := small_cmp_edges G hn (witW w) (univ \ witW w)
    (fun v hv h => (mem_sdiff.mp h).2 hv)
  rw [witness_card_fst hw] at hV
  rw [witness_card_snd hw] at hW
  simpa only [cmpEx, filter_empty, card_empty, zero_add] using add_le_add hV hW

end Sarkozy.SpectralD
