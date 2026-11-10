module

public import Sarkozy.PaperData.IndexLaw

@[expose] public section

/-!
# The finite conductor-depth envelope: residue-chain facts (`lem:imp:padic-envelope`)

General facts about the residue chain `Chain.residues p h` on `ℤ/p^hℤ` used for the
transition bound of `lem:imp:padic-envelope` (`paper/sections/27_tail_index.tex`):

* `cond_of_diff_ge`, `cond_of_diff_lt`: on the exact-depth space `ran Π_l`,
  `E_j f = f` for `j ≥ l` and `E_j f = 0` for `j < l`;
* `periodic_of_cond`: `E_l f = f` makes `f` invariant under translation by multiples of `p^l`;
* `sum_mul_eq_zero`: if `E_j f = 0` for all `j < l` and `p^l ∤ u`, then `∑_w f(s + u w) = 0`
  (the averaging that replaces the Gauss-sum evaluations of the paper's proof);
* `card_dvd_val`: `#{d : p^k ∣ d} = p^{h-k}`;
* `conv_squareIncrement_mulVec`: the transition of the square-increment law is
  `f ↦ |A|⁻¹ ∑_{x ∈ A} f(· + x²)`;
* `sq_sum_identity`: `∑_s (∑_x f(s + x²))² = ∑_d ∑_t f(t) ∑_x f(t + d² + 2dx)`;
* `sum_sub_sq_le`: the Cauchy–Schwarz step `‖a - βb‖ ≤ (α + β)‖b‖` from `‖a‖ ≤ α‖b‖`.
-/

namespace Sarkozy.IndexCert

open Finset Sarkozy.IndexSupport
open scoped Matrix BigOperators

section Residues

variable {p h : ℕ} [NeZero (p ^ h)]

omit [NeZero (p ^ h)] in
theorem dvd_val_mul {j : ℕ} (hj : j ≤ h) {a : ZMod (p ^ h)} (ha : p ^ j ∣ a.val)
    (b : ZMod (p ^ h)) : p ^ j ∣ (a * b).val := by
  rw [ZMod.val_mul, Nat.dvd_mod_iff (Nat.pow_dvd_pow p hj)]
  exact Dvd.dvd.mul_right ha _

theorem dvd_val_add_iff {j : ℕ} (hj : j ≤ h) (a b : ZMod (p ^ h)) :
    p ^ j ∣ (a + b).val ↔ p ^ j ∣ a.val + b.val := by
  rw [ZMod.val_add, Nat.dvd_mod_iff (Nat.pow_dvd_pow p hj)]

omit [NeZero (p ^ h)] in
theorem dvd_val_natCast_pow {j : ℕ} (hj : j ≤ h) :
    p ^ j ∣ (((p ^ j : ℕ) : ZMod (p ^ h))).val := by
  rw [ZMod.val_natCast, Nat.dvd_mod_iff (Nat.pow_dvd_pow p hj)]

theorem residueLabel_add_of_dvd {l : ℕ} (hl : l ≤ h) (s c : ZMod (p ^ h))
    (hc : p ^ l ∣ c.val) : residueLabel p h l (s + c) = residueLabel p h l s := by
  unfold residueLabel
  rw [ZMod.val_add, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow p hl)]
  obtain ⟨k, hk⟩ := hc
  rw [hk, Nat.add_mul_mod_self_left]

theorem dvd_of_mem_fibre {j : ℕ} (hj : j ≤ h) {s y : ZMod (p ^ h)}
    (hy : y ∈ fibre (residueLabel p h j) s) : p ^ j ∣ (y - s).val := by
  simp only [fibre, mem_filter, mem_univ, true_and] at hy
  have h1 : residueLabel p h j (s + (y - s)) = residueLabel p h j s := by
    rw [add_sub_cancel]
    exact hy
  unfold residueLabel at h1
  rw [ZMod.val_add, Nat.mod_mod_of_dvd _ (Nat.pow_dvd_pow p hj)] at h1
  have h2 : (s.val + (y - s).val) % p ^ j = (s.val + 0) % p ^ j := by rw [add_zero]; exact h1
  exact Nat.modEq_zero_iff_dvd.mp (Nat.ModEq.add_left_cancel' s.val h2)

theorem eq_pow_mul_of_dvd {j : ℕ} {c : ZMod (p ^ h)} (hc : p ^ j ∣ c.val) :
    c = ((p ^ j : ℕ) : ZMod (p ^ h)) * ((c.val / p ^ j : ℕ) : ZMod (p ^ h)) := by
  rw [← Nat.cast_mul, Nat.mul_div_cancel' hc, ZMod.natCast_zmod_val]

/-- `(E_l f)(s)` is the average of `f` over the residues `≡ s (mod p^l)`. -/
theorem cond_mulVec (l : ℕ) (f : ZMod (p ^ h) → ℝ) (s : ZMod (p ^ h)) :
    ((Chain.residues p h).cond l *ᵥ f) s =
      ((fibre (residueLabel p h l) s).card : ℝ)⁻¹ * ∑ y ∈ fibre (residueLabel p h l) s, f y := by
  rw [Chain.residues_cond, condExpMatrix_mulVec]

/-- On the exact-depth space `ran Π_l`, `E_j f = f` for `l ≤ j ≤ h`. -/
theorem cond_of_diff_ge {l j : ℕ} (hl : l ≤ h) (hlj : l ≤ j) (hj : j ≤ h)
    {f : ZMod (p ^ h) → ℝ} (hf : (Chain.residues p h).diff l *ᵥ f = f) :
    (Chain.residues p h).cond j *ᵥ f = f := by
  set C := Chain.residues p h
  have hjC : j ≤ C.depth := hj
  have hlC : l ≤ C.depth := hl
  have key : C.cond j * C.diff l = C.diff l := by
    unfold Chain.diff
    split_ifs with h0
    · rw [C.cond_mul_cond j 0 hjC (Nat.zero_le _), Nat.min_zero]
    · rw [Matrix.mul_sub, C.cond_mul_cond j l hjC hlC, C.cond_mul_cond j (l - 1) hjC (by omega),
        min_eq_right hlj, min_eq_right (by omega : l - 1 ≤ j)]
  rw [← hf, Matrix.mulVec_mulVec, key]

/-- On the exact-depth space `ran Π_l`, `E_j f = 0` for `j < l`. -/
theorem cond_of_diff_lt {l j : ℕ} (hl : l ≤ h) (hjl : j < l) {f : ZMod (p ^ h) → ℝ}
    (hf : (Chain.residues p h).diff l *ᵥ f = f) : (Chain.residues p h).cond j *ᵥ f = 0 := by
  set C := Chain.residues p h
  have hjC : j ≤ C.depth := by show j ≤ h; omega
  have hlC : l ≤ C.depth := hl
  have key : C.cond j * C.diff l = 0 := by
    unfold Chain.diff
    rw [ite_eq_right (by omega : l ≠ 0), Matrix.mul_sub, C.cond_mul_cond j l hjC hlC,
      C.cond_mul_cond j (l - 1) hjC (by omega), min_eq_left hjl.le,
      min_eq_left (by omega : j ≤ l - 1), sub_self]
  rw [← hf, Matrix.mulVec_mulVec, key, Matrix.zero_mulVec]

/-- **Periodicity**: `E_l f = f` makes `f` invariant under translations by multiples of `p^l`. -/
theorem periodic_of_cond {l : ℕ} (hl : l ≤ h) {f : ZMod (p ^ h) → ℝ}
    (hf : (Chain.residues p h).cond l *ᵥ f = f) (s c : ZMod (p ^ h)) (hc : p ^ l ∣ c.val) :
    f (s + c) = f s := by
  have h1 := congrFun hf (s + c)
  have h2 := congrFun hf s
  rw [cond_mulVec] at h1 h2
  rw [fibre_eq (residueLabel_add_of_dvd hl s c hc)] at h1
  exact h1.symm.trans h2

theorem fibre_sum_eq_zero {j : ℕ} {f : ZMod (p ^ h) → ℝ}
    (hf : (Chain.residues p h).cond j *ᵥ f = 0) (s : ZMod (p ^ h)) :
    ∑ y ∈ fibre (residueLabel p h j) s, f y = 0 := by
  have h1 := congrFun hf s
  rw [cond_mulVec, Pi.zero_apply] at h1
  have hc := fibre_card_pos (residueLabel p h j) s
  rcases mul_eq_zero.mp h1 with h | h
  · exact absurd h (inv_ne_zero hc.ne')
  · exact h

/-- **Averaging over a subgroup**: if `E_j f = 0` then `∑_w f(s + p^j w) = 0`. -/
theorem sum_pow_mul_eq_zero {j : ℕ} (hj : j ≤ h) {f : ZMod (p ^ h) → ℝ}
    (hf : (Chain.residues p h).cond j *ᵥ f = 0) (s : ZMod (p ^ h)) :
    ∑ w, f (s + ((p ^ j : ℕ) : ZMod (p ^ h)) * w) = 0 := by
  set P : ZMod (p ^ h) := ((p ^ j : ℕ) : ZMod (p ^ h)) with hP
  set g : ZMod (p ^ h) → ℝ := fun s => ∑ w, f (s + P * w) with hg
  have hPdvd : ∀ w, p ^ j ∣ (P * w).val := fun w => dvd_val_mul hj (dvd_val_natCast_pow hj) w
  have hginv : ∀ s t, g (s + P * t) = g s := by
    intro s t
    simp only [hg]
    exact Fintype.sum_equiv (Equiv.addLeft t) _ _ (fun w => by
      simp only [Equiv.coe_addLeft]
      rw [mul_add, add_assoc])
  set F := fibre (residueLabel p h j) s
  have hconst : ∀ y ∈ F, g y = g s := by
    intro y hy
    have h1 := eq_pow_mul_of_dvd (dvd_of_mem_fibre hj hy)
    have h2 : y = s + P * (((y - s).val / p ^ j : ℕ) : ZMod (p ^ h)) := by
      rw [← h1]; abel
    rw [h2, hginv]
  have hmem : ∀ w, ∀ y ∈ F, y + P * w ∈ F := by
    intro w y hy
    simp only [F, fibre, mem_filter, mem_univ, true_and] at hy ⊢
    rw [residueLabel_add_of_dvd hj y _ (hPdvd w), hy]
  have hmem' : ∀ w, ∀ y ∈ F, y - P * w ∈ F := by
    intro w y hy
    simp only [F, fibre, mem_filter, mem_univ, true_and] at hy ⊢
    rw [← hy, ← residueLabel_add_of_dvd hj (y - P * w) _ (hPdvd w), sub_add_cancel]
  have hshift : ∀ w, ∑ y ∈ F, f (y + P * w) = ∑ y ∈ F, f y := by
    intro w
    exact Finset.sum_nbij' (· + P * w) (· - P * w) (fun y hy => hmem w y hy)
      (fun y hy => hmem' w y hy) (fun y _ => by simp) (fun y _ => by simp) (fun y _ => rfl)
  have hz : ∑ y ∈ F, f y = 0 := fibre_sum_eq_zero hf s
  have htot : ∑ y ∈ F, g y = 0 := by
    simp only [hg]
    rw [Finset.sum_comm]
    simp only [hshift, hz, sum_const_zero]
  rw [sum_congr rfl hconst, sum_const, nsmul_eq_mul] at htot
  have hc := fibre_card_pos (residueLabel p h j) s
  rcases mul_eq_zero.mp htot with h0 | h0
  · exact absurd h0 hc.ne'
  · exact h0

/-- **The averaging lemma**: if `E_j f = 0` for every `j < l` and `p^l ∤ u`, then
`∑_w f(s + u w) = 0`. -/
theorem sum_mul_eq_zero (hp : p.Prime) {l : ℕ} (hl : l ≤ h) {f : ZMod (p ^ h) → ℝ}
    (hf : ∀ j < l, (Chain.residues p h).cond j *ᵥ f = 0) {u : ZMod (p ^ h)}
    (hu : ¬ p ^ l ∣ u.val) (s : ZMod (p ^ h)) : ∑ w, f (s + u * w) = 0 := by
  have hu0 : u.val ≠ 0 := fun h0 => hu (h0 ▸ dvd_zero _)
  have : Fact p.Prime := ⟨hp⟩
  set j := padicValNat p u.val with hjdef
  have hdvd : p ^ j ∣ u.val := pow_padicValNat_dvd
  have hjl : j < l := by
    by_contra hge
    exact hu ((Nat.pow_dvd_pow p (not_lt.mp hge)).trans hdvd)
  obtain ⟨m, hm⟩ := hdvd
  have hpm : ¬ p ∣ m := by
    rintro ⟨c, hc⟩
    have h1 : p ^ (j + 1) ∣ u.val := ⟨c, by rw [hm, hc, pow_succ]; ring⟩
    have h2 := (padicValNat_dvd_iff_le hu0).mp h1
    omega
  have hcop : Nat.Coprime m (p ^ h) :=
    Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpm).symm
  have hueq : u = ((p ^ j : ℕ) : ZMod (p ^ h)) * (m : ZMod (p ^ h)) := by
    rw [← Nat.cast_mul, ← hm, ZMod.natCast_zmod_val]
  rw [hueq]
  calc ∑ w, f (s + ((p ^ j : ℕ) : ZMod (p ^ h)) * (m : ZMod (p ^ h)) * w)
      = ∑ w, f (s + ((p ^ j : ℕ) : ZMod (p ^ h)) * w) :=
        Fintype.sum_equiv (Units.mulLeft (ZMod.unitOfCoprime m hcop)) _ _ (fun w => by
          simp only [Units.mulLeft_apply, ZMod.coe_unitOfCoprime, mul_assoc])
    _ = 0 := sum_pow_mul_eq_zero (by omega) (hf j hjl) s

/-- **Counting multiples**: `#{d ∈ ℤ/p^hℤ : p^k ∣ d} = p^{h-k}` for `k ≤ h`. -/
theorem card_dvd_val (hp : 0 < p) {k : ℕ} (hk : k ≤ h) :
    (univ.filter (fun d : ZMod (p ^ h) => p ^ k ∣ d.val)).card = p ^ (h - k) := by
  have hpk : p ^ h = p ^ k * p ^ (h - k) := by rw [← pow_add]; congr 1; omega
  have hpos : 0 < p ^ k := pow_pos hp k
  have hlt : ∀ t, t < p ^ (h - k) → p ^ k * t < p ^ h := fun t ht => by
    rw [hpk]; exact Nat.mul_lt_mul_of_pos_left ht hpos
  rw [← card_range (p ^ (h - k))]
  symm
  apply Finset.card_bij (fun t _ => ((p ^ k * t : ℕ) : ZMod (p ^ h)))
  · intro t ht
    rw [mem_range] at ht
    simp only [mem_filter, mem_univ, true_and]
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt (hlt t ht)]
    exact dvd_mul_right _ _
  · intro a ha b hb hab
    rw [mem_range] at ha hb
    have := congrArg ZMod.val hab
    rw [ZMod.val_natCast, ZMod.val_natCast, Nat.mod_eq_of_lt (hlt a ha),
      Nat.mod_eq_of_lt (hlt b hb)] at this
    exact Nat.eq_of_mul_eq_mul_left hpos this
  · intro d hd
    simp only [mem_filter, mem_univ, true_and] at hd
    refine ⟨d.val / p ^ k, ?_, ?_⟩
    · rw [mem_range, Nat.div_lt_iff_lt_mul hpos, mul_comm, ← hpk]
      exact ZMod.val_lt d
    · rw [Nat.mul_div_cancel' hd, ZMod.natCast_zmod_val]

/-- **The transition of the square-increment law**: `(T f)(s) = |A|⁻¹ ∑_{x ∈ A} f(s + x²)` with
`A = lowValuation p h v`. -/
theorem conv_squareIncrement_mulVec {v : ℕ} (hne : (PartV.lowValuation p h v).Nonempty)
    (f : ZMod (p ^ h) → ℝ) (s : ZMod (p ^ h)) :
    (convMatrix (PartV.squareIncrementLaw p h v hne).weight *ᵥ f) s =
      ((PartV.lowValuation p h v).card : ℝ)⁻¹ * ∑ x ∈ PartV.lowValuation p h v, f (s + x ^ 2) := by
  rw [convMatrix_mulVec]
  have h1 := FiniteLaw.expect_map (PartV.uniformOnSet (PartV.lowValuation p h v) hne)
    (fun x => x ^ 2) (fun r => f (s + r))
  unfold FiniteLaw.expect at h1
  change ∑ r, ((PartV.uniformOnSet (PartV.lowValuation p h v) hne).map (fun x => x ^ 2)).weight r *
    f (s + r) = _
  rw [h1]
  simp only [Function.comp, PartV.uniformOnSet, ite_mul, zero_mul, sum_ite_mem, univ_inter,
    mul_sum]

end Residues

section Algebra

/-- `∑_s (∑_x f(s + x²))² = ∑_d ∑_t f(t) ∑_x f(t + d² + 2dx)` on a finite commutative ring. -/
theorem sq_sum_identity {R : Type*} [CommRing R] [Fintype R] (f : R → ℝ) :
    ∑ s, (∑ x, f (s + x ^ 2)) ^ 2 = ∑ d, ∑ t, f t * ∑ x, f (t + d ^ 2 + 2 * d * x) := by
  have h1 : ∀ s, (∑ x, f (s + x ^ 2)) ^ 2 = ∑ x, ∑ y, f (s + x ^ 2) * f (s + y ^ 2) := by
    intro s
    rw [sq, sum_mul_sum]
  have h2 : ∀ x y : R, ∑ s, f (s + x ^ 2) * f (s + y ^ 2) =
      ∑ t, f t * f (t + (y ^ 2 - x ^ 2)) := by
    intro x y
    exact Fintype.sum_equiv (Equiv.addRight (x ^ 2)) _ _ (fun s => by
      simp only [Equiv.coe_addRight]
      congr 2
      ring)
  have h3 : ∀ x : R, ∑ y, ∑ t, f t * f (t + (y ^ 2 - x ^ 2)) =
      ∑ d, ∑ t, f t * f (t + d ^ 2 + 2 * d * x) := by
    intro x
    exact Fintype.sum_equiv (Equiv.addLeft (-x)) _ _ (fun y => by
      simp only [Equiv.coe_addLeft]
      refine sum_congr rfl fun t _ => ?_
      congr 2
      ring)
  calc ∑ s, (∑ x, f (s + x ^ 2)) ^ 2 = ∑ s, ∑ x, ∑ y, f (s + x ^ 2) * f (s + y ^ 2) :=
        sum_congr rfl fun s _ => h1 s
    _ = ∑ x, ∑ y, ∑ s, f (s + x ^ 2) * f (s + y ^ 2) := by
        rw [sum_comm]
        refine sum_congr rfl fun x _ => ?_
        rw [sum_comm]
    _ = ∑ x, ∑ d, ∑ t, f t * f (t + d ^ 2 + 2 * d * x) := by
        refine sum_congr rfl fun x _ => ?_
        rw [← h3 x]
        exact sum_congr rfl fun y _ => h2 x y
    _ = ∑ d, ∑ t, f t * ∑ x, f (t + d ^ 2 + 2 * d * x) := by
        rw [sum_comm]
        refine sum_congr rfl fun d _ => ?_
        rw [sum_comm]
        refine sum_congr rfl fun t _ => ?_
        rw [mul_sum]

/-- **The Cauchy–Schwarz step**: `‖a‖ ≤ α‖b‖` gives `‖a - βb‖ ≤ (α + β)‖b‖` (`α, β ≥ 0`). -/
theorem sum_sub_sq_le {ι : Type*} [Fintype ι] (a b : ι → ℝ) {α β : ℝ} (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (ha : ∑ i, a i ^ 2 ≤ α ^ 2 * ∑ i, b i ^ 2) :
    ∑ i, (a i - β * b i) ^ 2 ≤ (α + β) ^ 2 * ∑ i, b i ^ 2 := by
  set B := ∑ i, b i ^ 2
  have hB : 0 ≤ B := sum_nonneg fun i _ => sq_nonneg _
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq univ a b
  have hab : (∑ i, a i * b i) ^ 2 ≤ (α * B) ^ 2 := by
    calc (∑ i, a i * b i) ^ 2 ≤ (∑ i, a i ^ 2) * B := hcs
      _ ≤ (α ^ 2 * B) * B := mul_le_mul_of_nonneg_right ha hB
      _ = (α * B) ^ 2 := by ring
  have habs := abs_le_of_sq_le_sq' hab (mul_nonneg hα hB)
  have hexp : ∑ i, (a i - β * b i) ^ 2 =
      ∑ i, a i ^ 2 - 2 * β * ∑ i, a i * b i + β ^ 2 * B := by
    simp only [B, mul_sum, ← sum_sub_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun i _ => ?_
    ring
  rw [hexp]
  nlinarith [habs.1, mul_le_mul_of_nonneg_left habs.1 hβ]

end Algebra

end Sarkozy.IndexCert
