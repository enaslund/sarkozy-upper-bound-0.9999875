module

public import Sarkozy.TraceMixing.PairExplicit
public import Sarkozy.TraceMixing.SeventyTwo

/-!
# Seventy-two vertices, a pair (`lem:trace-mixing`(d), pair part; (R4))

`paper/sections/12_labellings.tex`, `lem:trace-mixing`(d): if `n = 72` and every degree is at
most `20`, then for every prime `p ≥ 2^512` and every edge `(u, v)` the squared norm of the
pair operator on the mean-zero functions is at most `2^92/p` (`trace_mixing_pair_72`).

As in the paper, (c) is applied with `e = e_{38}(p, 140)` (which bounds `e_t(p, 140)` and
`e_{s+1}(p, 72)` since `t ≤ 38` and `s + 1 ≤ 20`), and `d'_u, d'_v ≤ 19`
(`nbrCount_rest_le`). Instead of the certificate at `p = 2^512`
(`cert:trace-mixing-72`) the final inequality is proved for all `p ≥ 2^512` with the explicit
estimate `e ≤ 20 · 2^{38} p^{-1/2}` (`explicitBound_72`): the first term is at most
`(6561 · 2^{76} + 1444 · 2^{40})/p` and the second at most `2^{42}/p`.

`isGammaMixing_graphLaw_pair` is the pair half of (R4) for graph laws: assuming Weil's bound
(`Sarkozy.Target.Weil`), at every prime `p ≥ 2^512` the graph law of a graph with `72` vertices
and degrees at most `20` is `(255/1024, (u, v))`-mixing for every edge `(u, v)`
(`IsGammaMixing p (255/1024) λ {u, v}`, `def:mixing`), and its `(u, v)`-marginal is
`Unif(Ω)` (`srcWeight_pairJoint`).
-/

@[expose] public section

open Finset
open scoped BigOperators Matrix

namespace Sarkozy.TraceMixing

open Sarkozy.Mixing Sarkozy.Labellings

/-- **The final inequality of `lem:trace-mixing`(d) for a pair.** -/
theorem explicitBound_72 {p : ℝ} (hp : 2 ^ 512 ≤ p) {t s nx : ℕ}
    (hts : t - s ≤ 19) (ht : t + 1 ≤ 39) (hnx : nx ≤ 361) :
    coarseErr p 38 140 < 1 ∧ explicitBound p (coarseErr p 38 140) t s nx ≤ 2 ^ 92 / p := by
  have h2 : (2 : ℝ) ≤ 2 ^ 512 := le_self_pow₀ (by norm_num) (by norm_num)
  have hp2 : 2 ≤ p := le_trans h2 hp
  have hp0 : 0 < p := lt_of_lt_of_le two_pos hp2
  set r : ℝ := (Real.sqrt p)⁻¹ with hr
  have hsqrt0 : 0 < Real.sqrt p := Real.sqrt_pos.mpr hp0
  have hsq : Real.sqrt p * Real.sqrt p = p := Real.mul_self_sqrt hp0.le
  have hs256 : (2 : ℝ) ^ 256 ≤ Real.sqrt p := by
    rw [Real.le_sqrt (by positivity) hp0.le]
    calc ((2 : ℝ) ^ 256) ^ 2 = (2 : ℝ) ^ 512 := by rw [← pow_mul]
      _ ≤ p := hp
  have hs60 : (2 : ℝ) ^ 60 ≤ Real.sqrt p :=
    le_trans (pow_le_pow_right₀ (by norm_num) (by norm_num)) hs256
  clear hs256 hp h2
  have hr0 : 0 < r := inv_pos.mpr hsqrt0
  have hr60 : r ≤ 1 / 2 ^ 60 := by
    rw [hr, one_div]
    exact inv_anti₀ (by positivity) hs60
  have hrr : 1 / p = r ^ 2 := by
    rw [hr, inv_pow, Real.sq_sqrt hp0.le, one_div]
  set e := coarseErr p 38 140 with he
  have he0 : 0 ≤ e := coarseErr_nonneg hp0 38 140
  -- `e ≤ 20 · 2^38 r`
  have he_le : e ≤ 20 * 2 ^ 38 * r := by
    rw [he]
    unfold coarseErr
    have hh : ((38 : ℕ) : ℝ) / 2 - 1 + (1 / 2) ^ 38 ≤ 19 := by norm_num
    have h140 : ((140 : ℕ) : ℝ) / p = 140 * r ^ 2 := by rw [← hrr]; push_cast; ring
    rw [← hr, h140]
    have h1 : (((38 : ℕ) : ℝ) / 2 - 1 + (1 / 2) ^ 38) * r ≤ 19 * r :=
      mul_le_mul_of_nonneg_right hh hr0.le
    have h2 : 140 * r ^ 2 ≤ r := by
      have : 140 * r ≤ 1 := by
        have := mul_le_mul_of_nonneg_left hr60 (by norm_num : (0 : ℝ) ≤ 140)
        linarith [show (140 : ℝ) * (1 / 2 ^ 60) ≤ 1 by norm_num]
      nlinarith
    have h3 : (0 : ℝ) ≤ 2 ^ 38 := by positivity
    nlinarith
  have he_small : e ≤ 1 / 10 := by
    have : 20 * 2 ^ 38 * r ≤ 20 * 2 ^ 38 * (1 / 2 ^ 60) :=
      mul_le_mul_of_nonneg_left hr60 (by positivity)
    have h' : (20 : ℝ) * 2 ^ 38 * (1 / 2 ^ 60) ≤ 1 / 10 := by norm_num
    linarith
  have he1 : e < 1 := by linarith
  refine ⟨he1, ?_⟩
  have he1' : 0 < 1 - e := by linarith
  have hden : (3 : ℝ) / 4 ≤ (1 - e) ^ 2 := by nlinarith
  have hpm1 : p / 2 ≤ p - 1 := by linarith
  have hpm0 : 0 < p - 1 := by linarith
  have hinv : 1 / (p - 1) ≤ 2 * r ^ 2 := by
    rw [← hrr, div_le_iff₀ hpm0]
    rw [show 2 * (1 / p) * (p - 1) = 2 - 2 / p by field_simp]
    have : 2 / p ≤ 1 := by rw [div_le_one hp0]; exact hp2
    linarith
  -- the first term
  have hnxR : (nx : ℝ) ≤ 361 := by exact_mod_cast hnx
  have hpow1 : (2 : ℝ) ^ (t - s + 1) ≤ 2 ^ 20 := pow_le_pow_right₀ (by norm_num) (by omega)
  have hpow2 : (2 : ℝ) ^ (t - s) ≤ 2 ^ 19 := pow_le_pow_right₀ (by norm_num) hts
  have hpow3 : (2 : ℝ) ^ (t + 1) ≤ 2 ^ 39 := pow_le_pow_right₀ (by norm_num) ht
  have hη : (nx : ℝ) * 2 ^ (t - s + 1) / (p - 1) ≤ 722 * 2 ^ 20 * r ^ 2 := by
    rw [div_eq_mul_one_div]
    have h1 : (nx : ℝ) * 2 ^ (t - s + 1) ≤ 361 * 2 ^ 20 :=
      mul_le_mul hnxR hpow1 (by positivity) (by norm_num)
    have h2 : 0 ≤ 1 / (p - 1) := by positivity
    calc (nx : ℝ) * 2 ^ (t - s + 1) * (1 / (p - 1)) ≤ 361 * 2 ^ 20 * (2 * r ^ 2) :=
          mul_le_mul h1 hinv h2 (by norm_num)
      _ = 722 * 2 ^ 20 * r ^ 2 := by ring
  have hη0 : 0 ≤ (nx : ℝ) * 2 ^ (t - s + 1) / (p - 1) := by positivity
  have hA1 : 3 * e / (1 - e) ^ 2 ≤ 4 * e := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  have hηr : (1 + e) * ((nx : ℝ) * 2 ^ (t - s + 1) / (p - 1)) ≤ r := by
    have h1 : (1 + e) * ((nx : ℝ) * 2 ^ (t - s + 1) / (p - 1)) ≤ 2 * (722 * 2 ^ 20 * r ^ 2) :=
      mul_le_mul (by linarith) hη hη0 (by norm_num)
    have h2 : 2 * (722 * 2 ^ 20 * r ^ 2) ≤ r := by
      have : 2 * 722 * 2 ^ 20 * r ≤ 1 := by
        have := mul_le_mul_of_nonneg_left hr60 (by positivity : (0 : ℝ) ≤ 2 * 722 * 2 ^ 20)
        linarith [show (2 : ℝ) * 722 * 2 ^ 20 * (1 / 2 ^ 60) ≤ 1 by norm_num]
      nlinarith
    linarith
  have hφg : 3 * e / (1 - e) ^ 2 + (1 + e) * ((nx : ℝ) * 2 ^ (t - s + 1) / (p - 1)) ≤
      81 * 2 ^ 38 * r := by
    nlinarith
  have hφg0 : 0 ≤ 3 * e / (1 - e) ^ 2 + (1 + e) * ((nx : ℝ) * 2 ^ (t - s + 1) / (p - 1)) := by
    positivity
  have hφg2 : (3 * e / (1 - e) ^ 2 + (1 + e) * ((nx : ℝ) * 2 ^ (t - s + 1) / (p - 1))) ^ 2 ≤
      6561 * 2 ^ 76 * r ^ 2 := by
    have := pow_le_pow_left₀ hφg0 hφg 2
    calc _ ≤ (81 * 2 ^ 38 * r) ^ 2 := this
      _ = 6561 * 2 ^ 76 * r ^ 2 := by ring
  have hφx : 2 ^ (t - s) * (1 + e) / (1 - e) ^ 2 ≤ 2 ^ 20 := by
    rw [div_le_iff₀ (by positivity)]
    have h1 : (2 : ℝ) ^ (t - s) * (1 + e) ≤ 2 ^ 19 * (11 / 10) :=
      mul_le_mul hpow2 (by linarith) (by linarith) (by positivity)
    have h2 : (2 : ℝ) ^ 19 * (11 / 10) ≤ 2 ^ 20 * (3 / 4) := by norm_num
    nlinarith
  have hφx0 : 0 ≤ 2 ^ (t - s) * (1 + e) / (1 - e) ^ 2 := by positivity
  have hφx2 : (2 ^ (t - s) * (1 + e) / (1 - e) ^ 2) ^ 2 ≤ 2 ^ 40 := by
    have := pow_le_pow_left₀ hφx0 hφx 2
    calc _ ≤ ((2 : ℝ) ^ 20) ^ 2 := this
      _ = 2 ^ 40 := by norm_num
  have hcoef : 2 * (nx : ℝ) / (p - 1) ≤ 1444 * r ^ 2 := by
    rw [div_eq_mul_one_div]
    calc 2 * (nx : ℝ) * (1 / (p - 1)) ≤ 2 * 361 * (2 * r ^ 2) :=
          mul_le_mul (by linarith) hinv (by positivity) (by norm_num)
      _ = 1444 * r ^ 2 := by ring
  have hcoef0 : 0 ≤ 2 * (nx : ℝ) / (p - 1) := by positivity
  have hterm1 : (3 * e / (1 - e) ^ 2 + (1 + e) * ((nx : ℝ) * 2 ^ (t - s + 1) / (p - 1))) ^ 2 +
      2 * nx / (p - 1) * (2 ^ (t - s) * (1 + e) / (1 - e) ^ 2) ^ 2 ≤ 2 ^ 92 * r ^ 2 := by
    have h1 : 2 * (nx : ℝ) / (p - 1) * (2 ^ (t - s) * (1 + e) / (1 - e) ^ 2) ^ 2 ≤
        1444 * r ^ 2 * 2 ^ 40 :=
      mul_le_mul hcoef hφx2 (sq_nonneg _) (by positivity)
    have h2 : (6561 : ℝ) * 2 ^ 76 + 1444 * 2 ^ 40 ≤ 2 ^ 92 := by norm_num
    nlinarith [sq_nonneg r]
  -- the second term
  have hterm2 : (2 : ℝ) ^ (t + 1) / ((p - 1) * (1 - e) ^ 2) ≤ 2 ^ 92 * r ^ 2 := by
    rw [div_le_iff₀ (by positivity)]
    have h1 : (p - 1) * (1 - e) ^ 2 ≥ p / 2 * (3 / 4) :=
      mul_le_mul hpm1 hden (by norm_num) (by linarith)
    have hpr : p * r ^ 2 = 1 := by
      rw [← hrr]
      field_simp
    have h2 : 2 ^ 92 * r ^ 2 * (p / 2 * (3 / 4)) = 2 ^ 92 * (3 / 8) := by
      rw [show 2 ^ 92 * r ^ 2 * (p / 2 * (3 / 4)) = 2 ^ 92 * (3 / 8) * (p * r ^ 2) by ring, hpr,
        mul_one]
    have h3 : (2 : ℝ) ^ 39 ≤ 2 ^ 92 * (3 / 8) := by norm_num
    have h4 : 2 ^ 92 * r ^ 2 * (p / 2 * (3 / 4)) ≤ 2 ^ 92 * r ^ 2 * ((p - 1) * (1 - e) ^ 2) :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    linarith
  rw [div_eq_mul_one_div (2 ^ 92 : ℝ) p, hrr]
  unfold explicitBound
  exact max_le hterm1 hterm2

variable {W : Type*} [Fintype W] [DecidableEq W]

/-- `d'_u + 1 ≤ deg(u)` for an edge `(u, v)`: `v` is a neighbour of `u` outside `W'`. -/
theorem nbrCount_rest_le_u (G : OrientedGraph W) {u v : W} (huv : (u, v) ∈ G.E) :
    nbrCount G (restSet u v) u + 1 ≤ degree G u := by
  have huv' : u ≠ v := fun h' => G.loopless u (h' ▸ huv)
  unfold degree nbrCount
  have hsub : insert v ((restSet u v).filter fun a => (a, u) ∈ G.E ∨ (u, a) ∈ G.E) ⊆
      (univ.erase u).filter fun a => (a, u) ∈ G.E ∨ (u, a) ∈ G.E := by
    intro a ha
    rcases mem_insert.mp ha with rfl | ha'
    · simp only [mem_filter, mem_erase, mem_univ, and_true]
      exact ⟨Ne.symm huv', Or.inr huv⟩
    · simp only [mem_filter, mem_erase, mem_univ, and_true] at ha' ⊢
      exact ⟨(mem_restSet'.mp ha'.1).1, ha'.2⟩
  have hv : v ∉ (restSet u v).filter fun a => (a, u) ∈ G.E ∨ (u, a) ∈ G.E := by
    simp only [mem_filter, not_and]
    intro h
    exact absurd h (v_notMem_restSet u v)
  have := card_le_card hsub
  rw [card_insert_of_notMem hv] at this
  exact this

/-- `d'_v + 1 ≤ deg(v)` for an edge `(u, v)`. -/
theorem nbrCount_rest_le_v (G : OrientedGraph W) {u v : W} (huv : (u, v) ∈ G.E) :
    nbrCount G (restSet u v) v + 1 ≤ degree G v := by
  have huv' : u ≠ v := fun h' => G.loopless u (h' ▸ huv)
  unfold degree nbrCount
  have hsub : insert u ((restSet u v).filter fun a => (a, v) ∈ G.E ∨ (v, a) ∈ G.E) ⊆
      (univ.erase v).filter fun a => (a, v) ∈ G.E ∨ (v, a) ∈ G.E := by
    intro a ha
    rcases mem_insert.mp ha with rfl | ha'
    · simp only [mem_filter, mem_erase, mem_univ, and_true]
      exact ⟨huv', Or.inl huv⟩
    · simp only [mem_filter, mem_erase, mem_univ, and_true] at ha' ⊢
      exact ⟨(mem_restSet'.mp ha'.1).2, ha'.2⟩
  have hu : u ∉ (restSet u v).filter fun a => (a, v) ∈ G.E ∨ (v, a) ∈ G.E := by
    simp only [mem_filter, not_and]
    intro h
    exact absurd h (u_notMem_restSet u v)
  have := card_le_card hsub
  rw [card_insert_of_notMem hu] at this
  exact this

/-- `d'_u = deg(u) - 1` for an edge `(u, v)` (the paper's definition of `d'_u` in (c)). -/
theorem nbrCount_rest_add_one_u (G : OrientedGraph W) {u v : W} (huv : (u, v) ∈ G.E) :
    nbrCount G (restSet u v) u + 1 = degree G u := by
  have huv' : u ≠ v := fun h' => G.loopless u (h' ▸ huv)
  unfold degree nbrCount
  have heq : (univ.erase u).filter (fun a => (a, u) ∈ G.E ∨ (u, a) ∈ G.E) =
      insert v ((restSet u v).filter fun a => (a, u) ∈ G.E ∨ (u, a) ∈ G.E) := by
    ext a
    simp only [mem_filter, mem_erase, mem_univ, and_true, mem_insert]
    constructor
    · rintro ⟨hau, hadj⟩
      by_cases hav : a = v
      · exact Or.inl hav
      · exact Or.inr ⟨mem_restSet'.mpr ⟨hau, hav⟩, hadj⟩
    · rintro (rfl | ⟨ha, hadj⟩)
      · exact ⟨Ne.symm huv', Or.inr huv⟩
      · exact ⟨(mem_restSet'.mp ha).1, hadj⟩
  have hv : v ∉ (restSet u v).filter fun a => (a, u) ∈ G.E ∨ (u, a) ∈ G.E := by
    simp only [mem_filter, not_and]
    intro h
    exact absurd h (v_notMem_restSet u v)
  rw [heq, card_insert_of_notMem hv]

/-- `d'_v = deg(v) - 1` for an edge `(u, v)`. -/
theorem nbrCount_rest_add_one_v (G : OrientedGraph W) {u v : W} (huv : (u, v) ∈ G.E) :
    nbrCount G (restSet u v) v + 1 = degree G v := by
  have huv' : u ≠ v := fun h' => G.loopless u (h' ▸ huv)
  unfold degree nbrCount
  have heq : (univ.erase v).filter (fun a => (a, v) ∈ G.E ∨ (v, a) ∈ G.E) =
      insert u ((restSet u v).filter fun a => (a, v) ∈ G.E ∨ (v, a) ∈ G.E) := by
    ext a
    simp only [mem_filter, mem_erase, mem_univ, and_true, mem_insert]
    constructor
    · rintro ⟨hav, hadj⟩
      by_cases hau : a = u
      · exact Or.inl hau
      · exact Or.inr ⟨mem_restSet'.mpr ⟨hau, hav⟩, hadj⟩
    · rintro (rfl | ⟨ha, hadj⟩)
      · exact ⟨huv', Or.inl huv⟩
      · exact ⟨(mem_restSet'.mp ha).2, hadj⟩
  have hu : u ∉ (restSet u v).filter fun a => (a, v) ∈ G.E ∨ (v, a) ∈ G.E := by
    simp only [mem_filter, not_and]
    intro h
    exact absurd h (u_notMem_restSet u v)
  rw [heq, card_insert_of_notMem hu]

variable {p : ℕ} [Fact p.Prime]

/-- **`lem:trace-mixing`(d), a pair.** For a graph with `72` vertices and degrees at most `20`,
a prime `p ≥ 2^512` and an edge `(u, v)`: `‖T_{uv} f‖² ≤ (2^92/p) ‖f‖²` for every `f` with
mean zero under the (uniform on `Ω`) pair marginal. -/
theorem trace_mixing_pair_72 (hW : WeilBound (ZMod p)) (hp2 : p ≠ 2) (G : OrientedGraph W)
    (hne : (injLabellings (ZMod p) G).Nonempty) (hn : Fintype.card W = 72)
    (hdeg : ∀ w, degree G w ≤ 20) (hp : (2 : ℝ) ^ 512 ≤ p) {u v : W} (huv : (u, v) ∈ G.E)
    (f : ZMod p × ZMod p → ℝ)
    (hf : ∑ ω, srcWeight (pairJoint (graphLaw G hne) u v) ω * f ω = 0) :
    ∑ r, tgtWeight (pairJoint (graphLaw G hne) u v) r *
        condOp (pairJoint (graphLaw G hne) u v) f r ^ 2 ≤
      2 ^ 92 / (p : ℝ) * ∑ ω, srcWeight (pairJoint (graphLaw G hne) u v) ω * f ω ^ 2 := by
  have hp0 : (0 : ℝ) < p := lt_of_lt_of_le (by positivity) hp
  set du := nbrCount G (restSet u v) u with hdu
  set dv := nbrCount G (restSet u v) v with hdv
  have hdu19 : du ≤ 19 := by have := nbrCount_rest_le_u G huv; have := hdeg u; omega
  have hdv19 : dv ≤ 19 := by have := nbrCount_rest_le_v G huv; have := hdeg v; omega
  have hts : du + dv - max du dv ≤ 19 := by omega
  have ht : du + dv + 1 ≤ 39 := by omega
  have hnx : du * dv ≤ 361 := Nat.mul_le_mul hdu19 hdv19
  obtain ⟨he1, hbound⟩ := explicitBound_72 hp hts ht hnx
  have het : coarseErr p (du + dv) (2 * Fintype.card W - 4) ≤ coarseErr p 38 140 := by
    rw [hn]
    exact coarseErr_mono hp0 (by omega) (by norm_num)
  have hes : coarseErr p (max du dv + 1) (Fintype.card W) ≤ coarseErr p 38 140 := by
    rw [hn]
    exact coarseErr_mono hp0 (by omega) (by norm_num)
  have h := trace_mixing_explicit G hne hW hp2 huv he1 het hes f hf
  have hE : 0 ≤ ∑ ω, srcWeight (pairJoint (graphLaw G hne) u v) ω * f ω ^ 2 :=
    Finset.sum_nonneg (fun ω _ => mul_nonneg (srcWeight_nonneg _ _) (sq_nonneg _))
  exact h.trans (mul_le_mul_of_nonneg_right hbound hE)

/-- **(R4) for graph laws, a pair.** Assume Weil's bound (`Sarkozy.Target.Weil`). For a prime
`p ≥ 2^512`, a graph with `72` vertices and all degrees at most `20`, and an edge `(u, v)`,
the graph law `λ_p(G)` is `(255/1024, (u, v))`-mixing (`def:mixing`). -/
theorem isGammaMixing_graphLaw_pair (hWeil : Target.Weil) (hp : (2 : ℝ) ^ 512 ≤ p)
    (G : OrientedGraph W) (hn : Fintype.card W = 72) (hdeg : ∀ w, degree G w ≤ 20)
    (hne : (injLabellings (ZMod p) G).Nonempty) {u v : W} (huv : (u, v) ∈ G.E) :
    IsGammaMixing p (255 / 1024) (graphLaw G hne) {u, v} := by
  have h2512 : (2 : ℝ) < 2 ^ 512 := lt_self_pow₀ (by norm_num) (by norm_num)
  have hp2R : (2 : ℝ) < p := lt_of_lt_of_le h2512 hp
  have hp2 : p ≠ 2 := by
    intro h
    rw [h] at hp2R
    push_cast at hp2R
    exact lt_irrefl _ hp2R
  have hW := weilBound_of_target hWeil p hp2
  have hp0 : (0 : ℝ) < p := by linarith only [hp2R]
  have hp1 : (1 : ℝ) ≤ p := by linarith only [hp2R]
  have hsqrt : (2 : ℝ) ^ 256 ≤ Real.sqrt p := by
    rw [Real.le_sqrt (by positivity) hp0.le]
    calc ((2 : ℝ) ^ 256) ^ 2 = (2 : ℝ) ^ 512 := by rw [← pow_mul]
      _ ≤ (p : ℝ) := hp
  have h92 : (2 : ℝ) ^ 92 ≤ Real.sqrt p :=
    le_trans (pow_le_pow_right₀ (by norm_num) (by norm_num)) hsqrt
  have huv' : u ≠ v := fun h' => G.loopless u (h' ▸ huv)
  unfold IsGammaMixing IsMixing
  rw [contractsMeanZero_congr (pairEquiv huv') (Equiv.refl _)
    (fun a b => pairJoint_eq_blockJoint huv' (graphLaw G hne) a b)]
  intro f hf
  have h := trace_mixing_pair_72 hW hp2 G hne hn hdeg hp huv f hf
  clear hsqrt hp h2512
  -- `2^92/p ≤ p^{-255/512} = (p^{-255/1024})²`
  have hsq : ((p : ℝ) ^ (-(255 / 1024 : ℝ))) ^ 2 = (p : ℝ) ^ (-(255 / 512 : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hp0.le]
    norm_num
  have hhalf : Real.sqrt p ≤ (p : ℝ) ^ (257 / 512 : ℝ) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hp1 (by norm_num)
  have hsplit : (p : ℝ) ^ (-(255 / 512 : ℝ)) = (p : ℝ) ^ (257 / 512 : ℝ) / p := by
    rw [show (-(255 / 512 : ℝ)) = (257 / 512 : ℝ) - 1 by norm_num, Real.rpow_sub hp0,
      Real.rpow_one]
  have hstep : 2 ^ 92 / (p : ℝ) ≤ ((p : ℝ) ^ (-(255 / 1024 : ℝ))) ^ 2 := by
    rw [hsq, hsplit]
    exact div_le_div_of_nonneg_right (h92.trans hhalf) hp0.le
  have hE : 0 ≤ ∑ ω, srcWeight (pairJoint (graphLaw G hne) u v) ω * f ω ^ 2 :=
    Finset.sum_nonneg (fun ω _ => mul_nonneg (srcWeight_nonneg _ _) (sq_nonneg _))
  exact h.trans (mul_le_mul_of_nonneg_right hstep hE)

end Sarkozy.TraceMixing
