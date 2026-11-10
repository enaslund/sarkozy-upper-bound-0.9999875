module

public import Sarkozy.Certificates.Intervals

/-!
# Exponential and logarithm certificates

Taylor polynomials and their remainder bounds are rational computations.
Range reduction proves exp(q) = exp(q/k)^k, allowing logarithms of large
integers to be enclosed using short Taylor series near the origin.
-/

@[expose] public section

open scoped BigOperators

namespace Sarkozy.Certificates

def expSeries (q : ℚ) (n : ℕ) : ℚ := ∑ i ∈ Finset.range n, q ^ i / (i.factorial : ℚ)

def expRemainder (q : ℚ) (n : ℕ) : ℚ :=
  |q| ^ n * ((n + 1 : ℕ) : ℚ) / ((n.factorial : ℚ) * (n : ℚ))

theorem cast_expSeries (q : ℚ) (n : ℕ) :
    (expSeries q n : ℝ) = ∑ i ∈ Finset.range n, (q : ℝ) ^ i / (i.factorial : ℝ) := by
  simp [expSeries]

theorem cast_expRemainder (q : ℚ) (n : ℕ) :
    (expRemainder q n : ℝ) =
      |(q : ℝ)| ^ n * ((n + 1 : ℕ) : ℝ) / ((n.factorial : ℝ) * (n : ℝ)) := by
  simp [expRemainder]

structure ExpWitness where
  divisions : ℕ
  terms : ℕ
  lower : ℚ
  upper : ℚ
  deriving DecidableEq, Repr

/-- All fields are checked by rational arithmetic. The reduced exponential is
rounded before raising it to a power, keeping the certificate compact. -/
def ExpWitness.Valid (w : ExpWitness) (q : ℚ) (I : Interval) : Prop :=
  0 < w.divisions ∧ 0 < w.terms ∧ |q / (w.divisions : ℚ)| ≤ 1 ∧ 0 ≤ w.lower ∧
    w.lower ≤ expSeries (q / (w.divisions : ℚ)) w.terms -
      expRemainder (q / (w.divisions : ℚ)) w.terms ∧
    expSeries (q / (w.divisions : ℚ)) w.terms +
      expRemainder (q / (w.divisions : ℚ)) w.terms ≤ w.upper ∧
    I.lo ≤ w.lower ^ w.divisions ∧ w.upper ^ w.divisions ≤ I.hi

theorem ExpWitness.sound {w : ExpWitness} {q : ℚ} {I : Interval}
    (h : w.Valid q I) : I.Contains (Real.exp (q : ℝ)) := by
  obtain ⟨hk, hn, hsmall, hlo, hlow, hupp, htargetlo, htargethi⟩ := h
  have hs : |((q / (w.divisions : ℚ) : ℚ) : ℝ)| ≤ 1 := by
    exact_mod_cast hsmall
  have ht := Real.exp_bound hs hn
  rw [← cast_expSeries] at ht
  have herr : |((q / (w.divisions : ℚ) : ℚ) : ℝ)| ^ w.terms *
      ((w.terms.succ : ℝ) / ((w.terms.factorial : ℝ) * w.terms)) =
      (expRemainder (q / (w.divisions : ℚ)) w.terms : ℝ) := by
    rw [cast_expRemainder]
    simp only [Nat.succ_eq_add_one]
    ring
  rw [herr] at ht
  have hlow' : (w.lower : ℝ) ≤ (expSeries (q / (w.divisions : ℚ)) w.terms : ℝ) -
      (expRemainder (q / (w.divisions : ℚ)) w.terms : ℝ) := by exact_mod_cast hlow
  have hupp' : (expSeries (q / (w.divisions : ℚ)) w.terms : ℝ) +
      (expRemainder (q / (w.divisions : ℚ)) w.terms : ℝ) ≤ w.upper := by exact_mod_cast hupp
  have hl : (w.lower : ℝ) ≤ Real.exp ((q / (w.divisions : ℚ) : ℚ) : ℝ) := by
    have hh := (abs_le.mp ht).1
    linarith
  have hu : Real.exp ((q / (w.divisions : ℚ) : ℚ) : ℝ) ≤ (w.upper : ℝ) := by
    have hh := (abs_le.mp ht).2
    linarith
  have he : Real.exp (q : ℝ) =
      Real.exp ((q / (w.divisions : ℚ) : ℚ) : ℝ) ^ w.divisions := by
    rw [← Real.exp_nat_mul]
    congr 1
    push_cast
    have hk0 : (w.divisions : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
    field_simp [hk0]
  rw [he]
  constructor
  · have htl : (I.lo : ℝ) ≤ (w.lower : ℝ) ^ w.divisions := by exact_mod_cast htargetlo
    exact htl.trans (pow_le_pow_left₀ (by exact_mod_cast hlo) hl _)
  · have htu : (w.upper : ℝ) ^ w.divisions ≤ (I.hi : ℝ) := by exact_mod_cast htargethi
    exact (pow_le_pow_left₀ (Real.exp_pos _).le hu _).trans htu

/-- Monotonicity turns two point certificates into an interval certificate. -/
theorem Interval.exp_sound {I K : Interval} {x : ℝ}
    {lower upper : ExpWitness} {left right : Interval}
    (hx : I.Contains x) (hl : lower.Valid I.lo left) (hu : upper.Valid I.hi right)
    (hleft : K.lo ≤ left.lo) (hright : right.hi ≤ K.hi) : K.Contains (Real.exp x) := by
  constructor
  · have h : (K.lo : ℝ) ≤ left.lo := by exact_mod_cast hleft
    exact (h.trans (ExpWitness.sound hl).1).trans (Real.exp_le_exp.mpr hx.1)
  · have h : (right.hi : ℝ) ≤ K.hi := by exact_mod_cast hright
    exact (Real.exp_le_exp.mpr hx.2).trans ((ExpWitness.sound hu).2.trans h)

/-- Logarithm bounds are verified by exponentiating the proposed endpoints. -/
theorem Interval.log_sound {I K : Interval} {x : ℝ}
    {lower upper : ExpWitness} {left right : Interval}
    (hx : I.Contains x) (hxpos : 0 < I.lo)
    (hl : lower.Valid K.lo left) (hu : upper.Valid K.hi right)
    (hleft : left.hi ≤ I.lo) (hright : I.hi ≤ right.lo) : K.Contains (Real.log x) := by
  have hx0 := hx.pos hxpos
  constructor
  · apply (Real.le_log_iff_exp_le hx0).mpr
    have h : (left.hi : ℝ) ≤ I.lo := by exact_mod_cast hleft
    exact (ExpWitness.sound hl).2.trans (h.trans hx.1)
  · apply (Real.log_le_iff_le_exp hx0).mpr
    have h : (I.hi : ℝ) ≤ right.lo := by exact_mod_cast hright
    exact hx.2.trans (h.trans (ExpWitness.sound hu).1)

end Sarkozy.Certificates
