module

public import Sarkozy.DensityMoments.PacketGates



@[expose] public section

namespace Sarkozy.DensityMoments

open Sarkozy.Certificates

/-- One piece of the nonroot packet: start `X`, `r_X ≥ X^{-1/2}` and the coefficients of `h`. -/
structure NonrootRow where
  X : ℕ
  rX : ℚ
  a1 : ℚ
  a2 : ℚ
  a3 : ℚ
  a4 : ℚ
  deriving DecidableEq

namespace NonrootRow

/-- The bad fraction `a₄ r⁴ / (a₁ r + a₂ r² + a₃ r³ + a₄ r⁴)`. -/
noncomputable def frac (row : NonrootRow) (r : ℝ) : ℝ :=
  (row.a4 : ℝ) * r ^ 4 / ((row.a1 : ℝ) * r + row.a2 * r ^ 2 + row.a3 * r ^ 3 + row.a4 * r ^ 4)

def fracQ (row : NonrootRow) (r : ℚ) : ℚ :=
  row.a4 * r ^ 4 / (row.a1 * r + row.a2 * r ^ 2 + row.a3 * r ^ 3 + row.a4 * r ^ 4)

def Check (row : NonrootRow) : Prop :=
  0 < row.rX ∧ 1 ≤ row.rX ^ 2 * (row.X : ℚ) ∧ 0 < row.a1 ∧ 0 ≤ row.a2 ∧ 0 ≤ row.a3 ∧
    0 ≤ row.a4 ∧ row.fracQ row.rX ≤ 1661 / 200000000000000

instance (row : NonrootRow) : Decidable row.Check := by unfold Check; infer_instance

theorem frac_mono {row : NonrootRow} (h1 : 0 < row.a1) (h2 : 0 ≤ row.a2) (h3 : 0 ≤ row.a3)
    (h4 : 0 ≤ row.a4) {r r' : ℝ} (hr : 0 < r) (hrr : r ≤ r') : row.frac r ≤ row.frac r' := by
  have h1' : (0 : ℝ) < row.a1 := by exact_mod_cast h1
  have h2' : (0 : ℝ) ≤ row.a2 := by exact_mod_cast h2
  have h3' : (0 : ℝ) ≤ row.a3 := by exact_mod_cast h3
  have h4' : (0 : ℝ) ≤ row.a4 := by exact_mod_cast h4
  have hr' : 0 < r' := lt_of_lt_of_le hr hrr
  unfold frac
  have hD : 0 < (row.a1 : ℝ) * r + row.a2 * r ^ 2 + row.a3 * r ^ 3 + row.a4 * r ^ 4 := by
    positivity
  have hD' : 0 < (row.a1 : ℝ) * r' + row.a2 * r' ^ 2 + row.a3 * r' ^ 3 + row.a4 * r' ^ 4 := by
    positivity
  rw [div_le_div_iff₀ hD hD']
  -- `r^4 r'^k ≤ r'^4 r^k` for `k ≤ 4`
  have k1 : r ^ 4 * r' ≤ r' ^ 4 * r := by
    have : r ^ 3 ≤ r' ^ 3 := pow_le_pow_left₀ hr.le hrr 3
    nlinarith [mul_pos hr hr']
  have k2 : r ^ 4 * r' ^ 2 ≤ r' ^ 4 * r ^ 2 := by
    have : r ^ 2 ≤ r' ^ 2 := pow_le_pow_left₀ hr.le hrr 2
    nlinarith [mul_pos (pow_pos hr 2) (pow_pos hr' 2)]
  have k3 : r ^ 4 * r' ^ 3 ≤ r' ^ 4 * r ^ 3 := by
    nlinarith [mul_pos (pow_pos hr 3) (pow_pos hr' 3)]
  have e : (row.a4 : ℝ) * r ^ 4 * ((row.a1 : ℝ) * r' + row.a2 * r' ^ 2 + row.a3 * r' ^ 3 +
      row.a4 * r' ^ 4) = row.a4 * (row.a1 * (r ^ 4 * r') + row.a2 * (r ^ 4 * r' ^ 2) +
      row.a3 * (r ^ 4 * r' ^ 3) + row.a4 * (r ^ 4 * r' ^ 4)) := by ring
  have e' : (row.a4 : ℝ) * r' ^ 4 * ((row.a1 : ℝ) * r + row.a2 * r ^ 2 + row.a3 * r ^ 3 +
      row.a4 * r ^ 4) = row.a4 * (row.a1 * (r' ^ 4 * r) + row.a2 * (r' ^ 4 * r ^ 2) +
      row.a3 * (r' ^ 4 * r ^ 3) + row.a4 * (r' ^ 4 * r ^ 4)) := by ring
  rw [e, e']
  apply mul_le_mul_of_nonneg_left _ h4'
  have := mul_le_mul_of_nonneg_left k1 h1'.le
  have := mul_le_mul_of_nonneg_left k2 h2'
  have := mul_le_mul_of_nonneg_left k3 h3'
  nlinarith

/-- **Soundness**: at every least prime `b ≥ X`, the bad fraction at `r = b^{-1/2}` is at most
`8.305·10^{-12}`. -/
theorem sound {row : NonrootRow} (h : row.Check) {b : ℝ} (hb : (row.X : ℝ) ≤ b) :
    row.frac (1 / Real.sqrt b) ≤ 1661 / 200000000000000 := by
  obtain ⟨h0, hX, h1, h2, h3, h4, ht⟩ := h
  have hr := GateRow.rsqrt_le h0 hX hb
  have hX0 : (0 : ℝ) < row.X := by
    have hX' : (1 : ℝ) ≤ (row.rX : ℝ) ^ 2 * (row.X : ℝ) := by exact_mod_cast hX
    by_contra hcon
    push Not at hcon
    have : (row.X : ℝ) = 0 := le_antisymm hcon (Nat.cast_nonneg _)
    rw [this] at hX'
    linarith
  have hpos : 0 < 1 / Real.sqrt b := by
    have : 0 < b := lt_of_lt_of_le hX0 hb
    positivity
  have ht' : ((row.fracQ row.rX : ℚ) : ℝ) ≤ ((1661 / 200000000000000 : ℚ) : ℝ) := by
    exact_mod_cast ht
  have hcast : ((row.fracQ row.rX : ℚ) : ℝ) = row.frac (row.rX : ℝ) := by
    unfold fracQ frac
    push_cast
    ring
  rw [hcast] at ht'
  push_cast at ht'
  exact (frac_mono h1 h2 h3 h4 hpos hr).trans ht'

end NonrootRow

/-- The 33 nonroot pieces. -/
def nonrootRows : List NonrootRow := [
  ⟨19951586, (3125000000000000000 / 13958499454857244790607 : ℚ), (5996645968537 / 200000000000 : ℚ), (188138293491413 / 1000000000000 : ℚ), (168692947114042853533901821 / 685228963724750000000000 : ℚ), (1111121488761 / 50000000000 : ℚ)⟩,
  ⟨21757358, (100000000000000000000 / 466447832024118212644429 : ℚ), (3745665646007 / 125000000000 : ℚ), (37609578188027 / 200000000000 : ℚ), (26962874162309707668925609 / 109629456022300000000000 : ℚ), (2775978364549 / 125000000000 : ℚ)⟩,
  ⟨23726568, (20000000000000000000 / 97419850133327550710783 : ℚ), (7487059601383 / 250000000000 : ℚ), (46990508020989 / 250000000000 : ℚ), (33670359117892420679588403 / 137028592444600000000000 : ℚ), (1109697140017 / 50000000000 : ℚ)⟩,
  ⟨25429506, (12500000000000000000 / 63034596155603313264573 : ℚ), (29935131530313 / 1000000000000 : ℚ), (187896429480389 / 1000000000000 : ℚ), (336449728274479774308242433 / 1370225030558750000000000 : ℚ), (88733279521 / 4000000000 : ℚ)⟩,
  ⟨25874006, (1562500000000000000 / 7947890283649963672289 : ℚ), (29931930172993 / 1000000000000 : ℚ), (187880441941749 / 1000000000000 : ℚ), (336387868882612169420844153 / 1370210450891500000000000 : ℚ), (110903646269 / 5000000000 : ℚ)⟩,
  ⟨28215802, (100000000000000000000 / 531185485494473954569273 : ℚ), (14958181042277 / 500000000000 : ℚ), (23475363501893 / 125000000000 : ℚ), (84021970370686962837304793 / 342535297339750000000000 : ℚ), (11084079660857 / 500000000000 : ℚ)⟩,
  ⟨33554432, (100000000000000000000 / 579261875148019731989171 : ℚ), (29887301854981 / 1000000000000 : ℚ), (187659109667661 / 1000000000000 : ℚ), (335531678835405417034105301 / 1370019202730750000000000 : ℚ), (11072402079437 / 500000000000 : ℚ)⟩,
  ⟨39903170, (50000000000000000000 / 315844779915704796503039 : ℚ), (7465197814973 / 250000000000 : ℚ), (187529051657163 / 1000000000000 : ℚ), (670057532639262713376805369 / 2739832444814000000000000 : ℚ), (1382727351269 / 62500000000 : ℚ)⟩,
  ⟨47453134, (50000000000000000000 / 344431175998921444904277 : ℚ), (29836591440911 / 1000000000000 : ℚ), (37482261542383 / 200000000000 : ℚ), (334573615937465570928128099 / 1369829145100250000000000 : ℚ), (1381527267551 / 62500000000 : ℚ)⟩,
  ⟨56431604, (25000000000000000000 / 187802429430505504310237 : ℚ), (14907244869921 / 500000000000 : ℚ), (11706539356063 / 62500000000 : ℚ), (668322723359441902850604517 / 2739510786981000000000000 : ℚ), (5521751815383 / 250000000000 : ℚ)⟩,
  ⟨67108864, (1 / 8192 : ℚ), (7448573998591 / 250000000000 : ℚ), (93603958130917 / 500000000000 : ℚ), (133515079496560467326869349 / 547877129609400000000000 : ℚ), (2758897638863 / 125000000000 : ℚ)⟩,
  ⟨79806340, (100000000000000000000 / 893343942723070127158913 : ℚ), (5955167423573 / 200000000000 : ℚ), (187120176852399 / 1000000000000 : ℚ), (133379513062035068272852937 / 547855860564400000000000 : ℚ), (2205680199821 / 100000000000 : ℚ)⟩,
  ⟨94906266, (1562500000000000000 / 15221851102167649964573 : ℚ), (29758958131731 / 1000000000000 : ℚ), (187040527336347 / 1000000000000 : ℚ), (666282373884311843180105749 / 2739188773503000000000000 : ℚ), (1377733120403 / 62500000000 : ℚ)⟩,
  ⟨112863208, (100000000000000000000 / 1062370970988947909138547 : ℚ), (3717939807083 / 125000000000 : ℚ), (11685511316019 / 62500000000 : ℚ), (665723715976668610969636021 / 2739111573200500000000000 : ℚ), (11015920275347 / 500000000000 : ℚ)⟩,
  ⟨134217728, (100000000000000000000 / 1158523750296039463978343 : ℚ), (7432348121749 / 250000000000 : ℚ), (7476097456809 / 40000000000 : ℚ), (221738712670187755847582559 / 913015207458500000000000 : ℚ), (11010511530999 / 500000000000 : ℚ)⟩,
  ⟨159612678, (100000000000000000000 / 1263379111747538748264607 : ℚ), (7429116077499 / 250000000000 : ℚ), (93421332685589 / 500000000000 : ℚ), (18465409923295077300701953 / 76083032771500000000000 : ℚ), (11005589032837 / 500000000000 : ℚ)⟩,
  ⟨189812532, (6250000000000000000 / 86107793092437341829533 : ℚ), (14852314853681 / 500000000000 : ℚ), (186788298421067 / 1000000000000 : ℚ), (166083793590266134195008037 / 684735196394750000000000 : ℚ), (2750276712889 / 125000000000 : ℚ)⟩,
  ⟨225726414, (50000000000000000000 / 751209714394056541609577 : ℚ), (29693795204331 / 1000000000000 : ℚ), (186738829971521 / 1000000000000 : ℚ), (165988364398223657759458123 / 684724803580875000000000 : ℚ), (10997024828739 / 500000000000 : ℚ)⟩,
  ⟨268435456, (1 / 16384 : ℚ), (14841937140267 / 500000000000 : ℚ), (93346900585661 / 500000000000 : ℚ), (73734006373429421878879987 / 304318159553000000000000 : ℚ), (2198661187719 / 100000000000 : ℚ)⟩,
  ⟨319225356, (50000000000000000000 / 893343937126121654634397 : ℚ), (14837393853569 / 500000000000 : ℚ), (93326400454667 / 500000000000 : ℚ), (22109659475268821112321159 / 91294419455350000000000 : ℚ), (10989917191081 / 500000000000 : ℚ)⟩,
  ⟨379625064, (20000000000000000000 / 389679388215491839093069 : ℚ), (1854153995577 / 62500000000 : ℚ), (93307727871931 / 500000000000 : ℚ), (73666861541094699687007249 / 304311769654000000000000 : ℚ), (5493414110909 / 250000000000 : ℚ)⟩,
  ⟨451452826, (100000000000000000000 / 2124741927858534070397463 : ℚ), (1482941978657 / 50000000000 : ℚ), (186581430129807 / 1000000000000 : ℚ), (662739368052395226437878801 / 2738782849288000000000000 : ℚ), (2196802375197 / 100000000000 : ℚ)⟩,
  ⟨536870912, (50000000000000000000 / 1158523750296039463978343 : ℚ), (29651854951427 / 1000000000000 : ℚ), (46637605448809 / 250000000000 : ℚ), (662500282675544379851485779 / 2738762830124500000000000 : ℚ), (686340234413 / 31250000000 : ℚ)⟩,
  ⟨638450710, (50000000000000000000 / 1263379109768718631079197 : ℚ), (29645453738707 / 1000000000000 : ℚ), (186522155638189 / 1000000000000 : ℚ), (132456474494019452331033521 / 547749085771600000000000 : ℚ), (5489550692763 / 250000000000 : ℚ)⟩,
  ⟨759250126, (6250000000000000000 / 172215585958051427465573 : ℚ), (29639589543069 / 1000000000000 : ℚ), (37299276706263 / 200000000000 : ℚ), (132416743413548478418930949 / 547746054459600000000000 : ℚ), (10976964589637 / 500000000000 : ℚ)⟩,
  ⟨902905652, (100000000000000000000 / 3004838850920295193060529 : ℚ), (29634214638787 / 1000000000000 : ℚ), (186472880404767 / 1000000000000 : ℚ), (330951288143558356913268737 / 1369358521936250000000000 : ℚ), (5487507489699 / 250000000000 : ℚ)⟩,
  ⟨1073741824, (1 / 32768 : ℚ), (33696196200391 / 1000000000000 : ℚ), (93212315824119 / 500000000000 : ℚ), (165386769777358960567900921 / 684577916384500000000000 : ℚ), (10971657976001 / 500000000000 : ℚ)⟩,
  ⟨2147483648, (100000000000000000000 / 4634095001184157855913373 : ℚ), (1684347142043 / 50000000000 : ℚ), (186280591978811 / 1000000000000 : ℚ), (27520151919218648874751167 / 114048690875500000000000 : ℚ), (5480761027451 / 250000000000 : ℚ)⟩,
  ⟨4294967296, (1 / 65536 : ℚ), (16834427506151 / 500000000000 : ℚ), (37225935784009 / 200000000000 : ℚ), (131877031331383942686973823 / 547125844764500000000000 : ℚ), (2737871360939 / 125000000000 : ℚ)⟩,
  ⟨17179869184, (1 / 131072 : ℚ), (16813984765639 / 500000000000 : ℚ), (185832704371903 / 1000000000000 : ℚ), (657249016600306155276509899 / 2732067062527500000000000 : ℚ), (2733160916887 / 125000000000 : ℚ)⟩,
  ⟨68719476736, (1 / 262144 : ℚ), (16364980503943 / 500000000000 : ℚ), (185691869126389 / 1000000000000 : ℚ), (328118483272941697833011159 / 1365193938778500000000000 : ℚ), (2184738182251 / 100000000000 : ℚ)⟩,
  ⟨1099511627776, (1 / 1048576 : ℚ), (1995887069729 / 62500000000 : ℚ), (185561838794821 / 1000000000000 : ℚ), (218435538018039317944557123 / 909586851614000000000000 : ℚ), (10915556028129 / 500000000000 : ℚ)⟩,
  ⟨35184372088832, (50000000000000000000 / 296582080075786102778455911 : ℚ), (30041448793151 / 1000000000000 : ℚ), (92386169965551 / 500000000000 : ℚ), (324869664404184369976671227 / 1358612563702750000000000 : ℚ), (5434493551379 / 250000000000 : ℚ)⟩]

theorem nonrootRows_check : ∀ row ∈ nonrootRows, row.Check := by decide +kernel

theorem nonrootRows_length : nonrootRows.length = 33 := by decide +kernel

/-- Exponential witnesses for `e^{570(θ_*-1)}` (upper) and `e^{570(1-κ_*)}` (lower). -/
def nonrootW1 : ExpWitness := ⟨16, 25, (1681459010240857925982944104357 / 1000000000000000000000000000000 : ℚ), (840729505120428962991472052179 / 500000000000000000000000000000 : ℚ)⟩

def nonrootW2 : ExpWitness := ⟨8, 30, (2251366803490052070687766915861 / 1000000000000000000000000000000 : ℚ), (1125683401745026035343883457931 / 500000000000000000000000000000 : ℚ)⟩

theorem nonrootW1_valid : nonrootW1.Valid (570 * (thetaStar - 1))
    ⟨nonrootW1.lower ^ nonrootW1.divisions, nonrootW1.upper ^ nonrootW1.divisions⟩ := by
  decide +kernel

theorem nonrootW2_valid : nonrootW2.Valid (570 * (1 - kappaStar))
    ⟨nonrootW2.lower ^ nonrootW2.divisions, nonrootW2.upper ^ nonrootW2.divisions⟩ := by
  decide +kernel

theorem nonroot_coefficient_numeric :
    1 < kappaStar * nonrootW2.lower ^ nonrootW2.divisions ∧
      (nonrootW1.upper ^ nonrootW1.divisions - 1) /
        (kappaStar - 1 / nonrootW2.lower ^ nonrootW2.divisions) < 4200 ∧
      (1661 / 200000000000000 : ℚ) * (1 + 4200) < 1 := by
  decide +kernel

/-- **The mixture coefficient at `Q = e^{570}`** with `(θ_*, κ_*)` is below `4200`, and the
nonroot packet's gate `t (1 + C) < 1` holds with `t ≤ 8.305·10^{-12}`. -/
theorem nonroot_mixture_bound : mixtureBound 570 < 4200 ∧
    (1661 / 200000000000000 : ℝ) * (1 + mixtureBound 570) < 1 := by
  have he1 := (ExpWitness.sound nonrootW1_valid).2
  have he2 := (ExpWitness.sound nonrootW2_valid).1
  obtain ⟨hk, hc, hg⟩ := nonroot_coefficient_numeric
  have hk' : (1 : ℝ) < (kappaStar : ℝ) * ((nonrootW2.lower : ℝ) ^ nonrootW2.divisions) := by
    exact_mod_cast hk
  have hc' : (((nonrootW1.upper ^ nonrootW1.divisions - 1) /
      (kappaStar - 1 / nonrootW2.lower ^ nonrootW2.divisions) : ℚ) : ℝ) < ((4200 : ℚ) : ℝ) := by
    exact_mod_cast hc
  push_cast at he1 he2 hc'
  have hW0 : (0 : ℝ) < (nonrootW2.lower : ℝ) ^ nonrootW2.divisions := by
    have hκ : (0 : ℝ) < kappaStar := by norm_num [kappaStar]
    by_contra hcon
    push Not at hcon
    nlinarith
  have hθ : (0 : ℝ) ≤ (thetaStar : ℝ) - 1 := by norm_num [thetaStar]
  have hexpneg : Real.exp (-((570 : ℝ) * (1 - (kappaStar : ℝ)))) ≤
      1 / ((nonrootW2.lower : ℝ) ^ nonrootW2.divisions) := by
    rw [Real.exp_neg, one_div]
    exact inv_anti₀ hW0 he2
  have hinvW : 1 / ((nonrootW2.lower : ℝ) ^ nonrootW2.divisions) < kappaStar := by
    rw [div_lt_iff₀ hW0]
    linarith
  have hnum0 : 0 ≤ Real.exp ((570 : ℝ) * ((thetaStar : ℝ) - 1)) - 1 := by
    have := Real.add_one_le_exp ((570 : ℝ) * ((thetaStar : ℝ) - 1))
    nlinarith
  have hC : mixtureBound 570 ≤ ((nonrootW1.upper : ℝ) ^ nonrootW1.divisions - 1) /
      ((kappaStar : ℝ) - 1 / ((nonrootW2.lower : ℝ) ^ nonrootW2.divisions)) := by
    unfold mixtureBound
    apply div_le_div₀ (by linarith) (by linarith) (by linarith) (by linarith)
  have h1 : mixtureBound 570 < 4200 := lt_of_le_of_lt hC hc'
  refine ⟨h1, ?_⟩
  have hg' : ((1661 / 200000000000000 * (1 + 4200) : ℚ) : ℝ) < ((1 : ℚ) : ℝ) := by
    exact_mod_cast hg
  push_cast at hg'
  nlinarith

/-- **The whole middle nonroot packet** (`lem:density:packets`): at every least prime `b ≥ X` of
each piece, its bad fraction is at most `8.305·10^{-12}`, and with the mixture coefficient at
`Q = e^{570}` the gate is below one. -/
theorem nonroot_packet_gate : ∀ row ∈ nonrootRows, ∀ b : ℝ, (row.X : ℝ) ≤ b →
    row.frac (1 / Real.sqrt b) * (1 + mixtureBound 570) < 1 := by
  intro row hrow b hb
  have ht := NonrootRow.sound (nonrootRows_check row hrow) hb
  have hg := nonroot_mixture_bound.2
  have hC0 : 0 ≤ 1 + mixtureBound 570 := by
    have := nonroot_mixture_bound.1
    unfold mixtureBound
    have hθ : (0 : ℝ) ≤ (thetaStar : ℝ) - 1 := by norm_num [thetaStar]
    have hnum0 : 0 ≤ Real.exp ((570 : ℝ) * ((thetaStar : ℝ) - 1)) - 1 := by
      have := Real.add_one_le_exp ((570 : ℝ) * ((thetaStar : ℝ) - 1))
      nlinarith
    have hden : 0 < (kappaStar : ℝ) - Real.exp (-((570 : ℝ) * (1 - (kappaStar : ℝ)))) := by
      have he2 := (ExpWitness.sound nonrootW2_valid).1
      obtain ⟨hk, _, _⟩ := nonroot_coefficient_numeric
      have hk' : (1 : ℝ) < (kappaStar : ℝ) * ((nonrootW2.lower : ℝ) ^ nonrootW2.divisions) := by
        exact_mod_cast hk
      push_cast at he2
      have hW0 : (0 : ℝ) < (nonrootW2.lower : ℝ) ^ nonrootW2.divisions := by
        have hκ : (0 : ℝ) < kappaStar := by norm_num [kappaStar]
        by_contra hcon
        push Not at hcon
        nlinarith
      have hexpneg : Real.exp (-((570 : ℝ) * (1 - (kappaStar : ℝ)))) ≤
          1 / ((nonrootW2.lower : ℝ) ^ nonrootW2.divisions) := by
        rw [Real.exp_neg, one_div]
        exact inv_anti₀ hW0 he2
      have hinvW : 1 / ((nonrootW2.lower : ℝ) ^ nonrootW2.divisions) < kappaStar := by
        rw [div_lt_iff₀ hW0]
        linarith
      linarith
    have := div_nonneg hnum0 hden.le
    linarith
  calc row.frac (1 / Real.sqrt b) * (1 + mixtureBound 570)
      ≤ (1661 / 200000000000000 : ℝ) * (1 + mixtureBound 570) :=
        mul_le_mul_of_nonneg_right ht hC0
    _ < 1 := hg

end Sarkozy.DensityMoments
