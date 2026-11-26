module

public import Ruliology.CellularAutomata.Rule30DensityMixtures
public import Ruliology.CellularAutomata.Rule30DensityPolygon
public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Algebra.Order.Archimedean.Real.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum

/-!
# The exact real density region at one site

Real limiting frequencies of a black cell and a horizontal run end. From any prescribed right half,
the limiting pair is attainable exactly in the closed pentagon of the core `Rule30SourceDensityRegion`
(`real_density_region`), with squared count errors at most 210000(n + 1) at every tick
(`quantitative_realization`). The physical construction is the arbitrary controller schedule of the
core `Rule30DensityControl` and `Rule30DensityMixtures`.

Contributed by Gareth Herbert with Claude (Anthropic) and GPT (OpenAI).
-/

@[expose] public section

namespace Rule30Equivalents.RealDensityRegion

open Ruliology.CellularAutomata
open Rule30SourceDensityRegion Rule30DensityControl Rule30Realization
open Rule30SourceObservables (count source)
open Filter Topology

/-- The five closed half-planes, in black-frequency and run-end-frequency coordinates. -/
def InPentagon (c a : ℝ) : Prop :=
  0 ≤ a ∧ a ≤ c ∧ 3*c ≤ 1+5*a ∧ 2*c ≤ 1+2*a ∧ 6*c ≤ 5+a

private def numerator (runEnd : Bool) (m : Mode) := if runEnd then m.source else m.black

private noncomputable def rate (runEnd : Bool) (i : Fin 5) : ℝ :=
  (numerator runEnd (cornerMode i) : ℝ) / (cornerMode i).denominator

private def movie (x : ℤ → Bool) (runEnd : Bool) (t : ℕ) : Bool :=
  if runEnd then source (evol x t 0) (evol x t 1) else evol x t 0

private def tally (f : ℕ → Bool) (t : ℕ) : ℝ := (count f t : ℤ)

private theorem tally_range (f : ℕ → Bool) (n : ℕ) : 0 ≤ tally f n ∧ tally f n ≤ n := by
  induction n with
  | zero => simp [tally, count]
  | succ n ih =>
    have hb := Rule30SourceObservables.bit_bounds (f n)
    unfold tally at *
    simp only [count, Int.cast_add, Nat.cast_succ]
    constructor <;> linarith [show (0:ℝ) ≤ (Rule30SourceObservables.bit (f n) : ℝ) by exact_mod_cast hb.1,
      show (Rule30SourceObservables.bit (f n) : ℝ) ≤ 1 by exact_mod_cast hb.2, ih.1, ih.2]

private theorem tally_add (f : ℕ → Bool) (t n : ℕ) :
    tally f (t+n) = tally f t + tally (fun j => f (t+j)) n := by
  simp only [tally, Rule30SourceObservables.count_add, Int.cast_add]

private theorem tally_between (f : ℕ → Bool) {s t : ℕ} (h : s ≤ t) :
    0 ≤ tally f t - tally f s ∧ tally f t - tally f s ≤ (t:ℝ)-s := by
  obtain ⟨d,rfl⟩ := Nat.exists_eq_add_of_le h
  rw [tally_add, Nat.cast_add]
  obtain ⟨h₀,h₁⟩ := tally_range (fun j => f (s+j)) d
  constructor <;> linarith

private theorem mode_numbers (b : Bool) (i : Fin 5) :
    0 < (cornerMode i).denominator ∧ numerator b (cornerMode i) ≤ (cornerMode i).denominator ∧
    (cornerMode i).width ≤ 37 ∧ (cornerMode i).cap ≤ 12 := by
  fin_cases i <;> cases b <;> decide

private theorem rate_range (b : Bool) (i : Fin 5) : 0 ≤ rate b i ∧ rate b i ≤ 1 := by
  obtain ⟨hD, hp, _, _⟩ := mode_numbers b i
  unfold rate
  constructor
  · positivity
  · exact (div_le_one (by exact_mod_cast hD)).2 (by exact_mod_cast hp)

/-- Count error for an entire phase, including its steering prefix. -/
private theorem phase_error (x : ℤ → Bool) (b : Bool) (i : Fin 5) (t l : ℕ)
    (h : Near x (cornerMode i).denominator (cornerMode i).black (cornerMode i).source
       (cornerMode i).cap (t+(cornerMode i).width) l) :
    |tally (movie x b) (t+((cornerMode i).width+l)) - tally (movie x b) t - rate b i*l| ≤ 49 := by
  let m := cornerMode i
  have ints : -(m.cap:ℤ) ≤ (m.denominator:ℤ)*count (fun j => movie x b (t+m.width+j)) l -
        (numerator b m:ℤ)*(l:ℤ) ∧
      (m.denominator:ℤ)*count (fun j => movie x b (t+m.width+j)) l -
        (numerator b m:ℤ)*(l:ℤ) ≤ (m.cap:ℤ) := by
    rcases h with ⟨cl,ch,al,ah⟩
    cases b
    · exact ⟨cl,ch⟩
    · exact ⟨al,ah⟩
  let f := movie x b
  let v := tally (fun j => f (t+m.width+j)) l
  have hl : -(m.cap:ℝ) ≤ (m.denominator:ℝ)*v - (numerator b m:ℝ)*(l:ℝ) := by
    dsimp only [v, tally, f]
    exact_mod_cast ints.1
  have hh : (m.denominator:ℝ)*v - (numerator b m:ℝ)*(l:ℝ) ≤ (m.cap:ℝ) := by
    dsimp only [v, tally, f]
    exact_mod_cast ints.2
  obtain ⟨hd,_,hw,hk⟩ := mode_numbers b i
  have hd' : (1:ℝ) ≤ m.denominator := by exact_mod_cast hd
  have hk' : (m.cap:ℝ) ≤ 12 := by exact_mod_cast hk
  have hw' : (m.width:ℝ) ≤ 37 := by exact_mod_cast hw
  have rv : rate b i * (m.denominator:ℝ) = numerator b m :=
    div_mul_cancel₀ _ (by linarith : (m.denominator:ℝ) ≠ 0)
  have err : -12 ≤ v - rate b i*l ∧ v - rate b i*l ≤ 12 := by
    constructor
    · by_contra! bad
      nlinarith [mul_lt_mul_of_pos_left bad (by linarith : (0:ℝ)<m.denominator),
        congrArg (fun z : ℝ => z*l) rv]
    · by_contra! bad
      nlinarith [mul_lt_mul_of_pos_left bad (by linarith : (0:ℝ)<m.denominator),
        congrArg (fun z : ℝ => z*l) rv]
  change |tally f (t+(m.width+l)) - tally f t - rate b i*l| ≤ 49
  rw [← Nat.add_assoc, tally_add f (t+m.width), tally_add f t]
  have steering := tally_range (fun j => f (t+j)) m.width
  change -12 ≤ tally (fun j => f (t+m.width+j)) l - rate b i*l ∧ _ at err
  apply abs_le.mpr
  constructor <;> linarith [err.1, err.2, steering.1, steering.2]


private def index (k : ℕ) : Fin 5 := ⟨k%5, Nat.mod_lt _ (by decide)⟩
private noncomputable def duration (w : Fin 5 → ℝ) (k : ℕ) : ℕ := ⌊(k/5:ℕ) * w (index k)⌋₊
private noncomputable def clock (w : Fin 5 → ℝ) : ℕ → ℕ :=
  startTick (fun k => (cornerMode (index k)).width + duration w k)
private noncomputable def epoch (w : Fin 5 → ℝ) (e : ℕ) := clock w (5*e)
private noncomputable def target (w : Fin 5 → ℝ) (b : Bool) := ∑ i, w i * rate b i

private theorem index_at (e : ℕ) (i : Fin 5) : index (5*e+i) = i := by
  apply Fin.ext
  change (5*e+i.val)%5 = i.val
  omega

private theorem rounded (w : Fin 5 → ℝ) (hw : ∀ i, 0 ≤ w i) (e : ℕ) (i : Fin 5) :
    (duration w (5*e+i):ℝ) ≤ e*w i ∧ e*w i ≤ (duration w (5*e+i):ℝ)+1 := by
  simp only [duration, index_at, show (5*e+i.val)/5 = e by omega]
  exact ⟨Nat.floor_le (mul_nonneg (Nat.cast_nonneg _) (hw i)), (Nat.lt_floor_add_one _).le⟩

private theorem telescope_five (f : ℕ → ℝ) (e : ℕ) :
    ∑ i : Fin 5, (f (5*e+i+1) - f (5*e+i)) = f (5*(e+1))-f (5*e) := by
  simp [Fin.sum_univ_succ, Nat.mul_add, Nat.add_assoc]
  ring

private theorem clock_step (w : Fin 5 → ℝ) (k : ℕ) :
    clock w (k+1) = clock w k + ((cornerMode (index k)).width + duration w k) := rfl

private theorem epoch_duration (w : Fin 5 → ℝ) (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1) (e : ℕ) :
    (e:ℝ)+64 ≤ (epoch w (e+1):ℝ)-epoch w e ∧
    (epoch w (e+1):ℝ)-epoch w e ≤ e+69 := by
  have clockSum := telescope_five (fun k => (clock w k : ℝ)) e
  simp only [clock_step, Nat.cast_add, add_sub_cancel_left, index_at, Finset.sum_add_distrib] at clockSum
  have widths : ∑ i : Fin 5, ((cornerMode i).width:ℝ) = 69 := by
    rw [Fin.sum_univ_five]
    change (2:ℝ)+6+21+37+3=69
    norm_num
  have targetSum : ∑ i, (e:ℝ)*w i = e := by rw [← Finset.mul_sum, hs, mul_one]
  have lo := Finset.sum_le_sum (s := Finset.univ) (fun i _ => (rounded w hw e i).1)
  have hi := Finset.sum_le_sum (s := Finset.univ) (fun i _ => (rounded w hw e i).2)
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, Nat.cast_ofNat, mul_one] at hi
  unfold epoch
  constructor <;> linarith

private theorem target_range (w : Fin 5 → ℝ) (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1) (b : Bool) :
    0 ≤ target w b ∧ target w b ≤ 1 := by
  refine ⟨Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (rate_range b i).1), ?_⟩
  rw [← hs]
  exact Finset.sum_le_sum (fun i _ => mul_le_of_le_one_right (hw i) (rate_range b i).2)

private theorem epoch_count (w : Fin 5 → ℝ) (hw : ∀ i, 0 ≤ w i) (x : ℤ → Bool) (b : Bool)
    (sched : ∀ k, Near x (cornerMode (index k)).denominator (cornerMode (index k)).black
      (cornerMode (index k)).source (cornerMode (index k)).cap
      (clock w k + (cornerMode (index k)).width) (duration w k)) (e : ℕ) :
    |tally (movie x b) (epoch w (e+1)) - tally (movie x b) (epoch w e) - e*target w b| ≤ 250 := by
  let F (k : ℕ) := tally (movie x b) (clock w k)
  have step (i : Fin 5) : |(F (5*e+i+1)-F (5*e+i)) - (e:ℝ)*(w i*rate b i)| ≤ 50 := by
    let k := 5*e+i.val
    have h := phase_error x b (index k) (clock w k) (duration w k) (sched k)
    rw [← clock_step] at h
    change |F (k+1)-F k-rate b (index k)*duration w k| ≤ 49 at h
    have idx : index k = i := index_at e i
    rw [idx] at h
    have round := rounded w hw e i
    have rr := rate_range b i
    have low := mul_le_mul_of_nonneg_left round.1 rr.1
    have high := mul_le_mul_of_nonneg_left round.2 rr.1
    change |(F (k+1)-F k) - (e:ℝ)*(w i*rate b i)| ≤ 50
    change (duration w k:ℝ) ≤ _ ∧ _ ≤ (duration w k:ℝ)+1 at round
    apply abs_le.mpr
    rcases abs_le.mp h with ⟨h₁,h₂⟩
    constructor <;> dsimp only [k] at * <;> nlinarith [rr.2]
  have sumBound := (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum (s := Finset.univ) (fun i _ => step i))
  rw [Finset.sum_sub_distrib, telescope_five, ← Finset.mul_sum] at sumBound
  simpa only [target, F, epoch,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_ofNat,
    show (5:ℝ)*50=250 by norm_num] using sumBound


/-- Turn bounded error per epoch into a uniform estimate at every physical tick. -/
private theorem all_ticks (f : ℕ → Bool) (τ : ℕ → ℕ) (q : ℝ)
    (q₀ : 0 ≤ q) (q₁ : q ≤ 1) (initial : τ 0 = 0)
    (times : ∀ e : ℕ, (e:ℝ)+64 ≤ (τ (e+1):ℝ)-τ e ∧ (τ (e+1):ℝ)-τ e ≤ e+69)
    (counts : ∀ e : ℕ, |tally f (τ (e+1))-tally f (τ e)-e*q| ≤ 250) (n : ℕ) :
    (tally f n-q*n)^2 ≤ 210000*((n:ℝ)+1) := by
  have growth (e : ℕ) : ((e:ℝ)+1)^2 ≤ 2*(τ e:ℝ)+1 := by
    induction e with
    | zero => simp [initial]
    | succ e ih => push_cast; nlinarith [(times e).1]
  have bound (e : ℕ) : |tally f (τ e)-q*(τ e:ℝ)| ≤ 319*e := by
    induction e with
    | zero => simp [initial, tally, count]
    | succ e ih =>
      rcases times e with ⟨tlo,thi⟩
      have h₀ := mul_nonneg q₀ (show 0 ≤ (τ (e+1):ℝ)-τ e-e by linarith)
      have h₁ := mul_le_mul_of_nonneg_left (show (τ (e+1):ℝ)-τ e-e ≤ 69 by linarith) q₀
      rcases abs_le.mp (counts e) with ⟨cl,ch⟩
      rcases abs_le.mp ih with ⟨il,ih⟩
      rw [Nat.cast_succ]
      apply abs_le.mpr
      constructor <;> nlinarith
  have grows (e : ℕ) : τ e < τ (e+1) := by
    exact_mod_cast (show (τ e:ℝ) < τ (e+1) by linarith [(times e).1, Nat.cast_nonneg (α := ℝ) e])
  have locate (t : ℕ) : ∃ e, τ e ≤ t ∧ t < τ (e+1) := by
    induction t with
    | zero => exact ⟨0, by omega, by have := grows 0; omega⟩
    | succ t ih =>
      obtain ⟨e,lo,hi⟩ := ih
      by_cases h : t+1 < τ (e+1)
      · exact ⟨e, by omega, h⟩
      · exact ⟨e+1, by omega, by have := grows (e+1); omega⟩
  obtain ⟨e,lo,hi⟩ := locate n
  have lo' : (τ e:ℝ) ≤ n := by exact_mod_cast lo
  have hi' : (n:ℝ) ≤ τ (e+1) := by exact_mod_cast hi.le
  have gap : (n:ℝ)-τ e ≤ e+69 := by linarith [(times e).2]
  have gain := tally_between f lo
  have qgap := mul_le_mul_of_nonneg_right q₁ (sub_nonneg.mpr lo')
  have qpos := mul_nonneg q₀ (sub_nonneg.mpr lo')
  have lin : |tally f n-q*n| ≤ 320*((e:ℝ)+1) := by
    rcases abs_le.mp (bound e) with ⟨bl,bh⟩
    apply abs_le.mpr
    constructor <;> nlinarith [gain.1, gain.2]
  have sq := pow_le_pow_left₀ (abs_nonneg _) lin 2
  rw [sq_abs] at sq
  nlinarith [growth e, Nat.cast_nonneg (α := ℝ) n]

/-- The discrepancy bound is independent of the point and the chosen right half. -/
private theorem realize_weights (w : Fin 5 → ℝ) (hw : ∀ i, 0 ≤ w i) (hs : ∑ i, w i = 1)
    (r : ℕ → Bool) :
    ∃ x : ℤ → Bool, (∀ j : ℕ, evol x 0 j = r j) ∧ ∀ b n,
      (tally (movie x b) n-target w b*n)^2 ≤ 210000*((n:ℝ)+1) := by
  obtain ⟨x,right,sch⟩ := schedule (fun k => cornerMode (index k)) (fun _ => cornerMode_good _)
    (duration w) r
  refine ⟨x,right,fun b => all_ticks _ (epoch w) _ (target_range w hw hs b).1
    (target_range w hw hs b).2 rfl (epoch_duration w hw hs) ?_⟩
  exact epoch_count w hw x b (fun k => sch k _ le_rfl)

private theorem square_bound_limit (v : ℕ → ℝ) (q : ℝ)
    (h : ∀ n : ℕ, (v n-q*n)^2 ≤ 210000*((n:ℝ)+1)) :
    Tendsto (fun n : ℕ => v n/n) atTop (𝓝 q) := by
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨N,hN⟩ := exists_nat_gt (420000 / ε^2)
  refine ⟨N+1, fun n hn => ?_⟩
  have pn : 0 < (n:ℝ) := by exact_mod_cast (show 0 < n by omega)
  have un : 1 ≤ (n:ℝ) := by exact_mod_cast (show 1 ≤ n by omega)
  have pε : 0 < ε^2 := sq_pos_of_pos hε
  have base := (div_lt_iff₀ pε).mp hN
  have leN : (N:ℝ) ≤ n := by exact_mod_cast (show N ≤ n by omega)
  have big : 420000 < (n:ℝ)*ε^2 := by nlinarith [mul_le_mul_of_nonneg_right leN pε.le]
  have sq : (v n-q*n)^2 < (ε*n)^2 := by nlinarith [h n, mul_lt_mul_of_pos_right big pn]
  rw [Real.dist_eq, div_sub' (by linarith : (n:ℝ) ≠ 0), mul_comm (n:ℝ) q, abs_div, abs_of_pos pn, div_lt_iff₀ pn]
  by_contra! bad
  have sqbad := pow_le_pow_left₀ (mul_nonneg hε.le pn.le) bad 2
  rw [sq_abs] at sqbad
  linarith


private theorem weights_of_faces {c a : ℝ} (h : InPentagon c a) :
    ∃ w : Fin 5 → ℝ, (∀ i, 0 ≤ w i) ∧ (∑ i, w i) = 1 ∧ target w false = c ∧ target w true = a := by
  obtain ⟨ha,hac,h₁,h₂,h₃⟩ := h
  have make (v₀ v₁ v₂ v₃ v₄ : ℝ)
      (p₀ : 0 ≤ v₀) (p₁ : 0 ≤ v₁) (p₂ : 0 ≤ v₂) (p₃ : 0 ≤ v₃) (p₄ : 0 ≤ v₄)
      (sum : v₀+v₁+v₂+v₃+v₄=1) (C : v₁/3+3*v₂/4+9*v₃/10+v₄=c)
      (A : v₂/4+4*v₃/10+v₄=a) :
      ∃ w : Fin 5 → ℝ, (∀ i, 0 ≤ w i) ∧ (∑ i, w i)=1 ∧ target w false=c ∧ target w true=a := by
    let w : Fin 5 → ℝ := ![v₀,v₁,v₂,v₃,v₄]
    refine ⟨w, ?_, ?_, ?_, ?_⟩
    · intro i
      fin_cases i <;> assumption
    · rw [Fin.sum_univ_five]
      exact sum
    · change (∑ i, w i * rate false i) = c
      rw [Fin.sum_univ_five]
      norm_num [w, rate, numerator, cornerMode, zero, oneThird, threeQuarters, nineTenths, one]
      linarith
    · change (∑ i, w i * rate true i) = a
      rw [Fin.sum_univ_five]
      norm_num [w, rate, numerator, cornerMode, zero, oneThird, threeQuarters, nineTenths, one]
      linarith
  by_cases left : 3*a ≤ c
  · apply make (1-3*c+5*a) (3*c-9*a) (4*a) 0 0 <;> linarith
  by_cases mid : 9*a ≤ 4*c
  · apply make (1-2*c+2*a) 0 (16*c/3-12*a) (10*a-10*c/3) 0 <;> linarith
  · apply make ((5-6*c+a)/5) 0 0 (2*(c-a)) ((9*a-4*c)/5) <;> linarith

/-- From any prescribed right half, the same row realizes both target counts at every
time with a uniform square-root discrepancy. Zero weights and boundary points are allowed. -/
theorem quantitative_realization {c a : ℝ} (h : InPentagon c a) (r : ℕ → Bool) :
    ∃ x : ℤ → Bool, (∀ j : ℕ, evol x 0 j = r j) ∧ ∀ n : ℕ,
      ((black (evol x) 0 0 n:ℝ)-c*n)^2 ≤ 210000*((n:ℝ)+1) ∧
      ((ends (evol x) 0 0 n:ℝ)-a*n)^2 ≤ 210000*((n:ℝ)+1) := by
  obtain ⟨w,hw,hs,C,A⟩ := weights_of_faces h
  obtain ⟨x,right,est⟩ := realize_weights w hw hs r
  refine ⟨x,right,fun n => ?_⟩
  have mb : movie x false = fun t => evol x t 0 := rfl
  have ma : movie x true = fun t => source (evol x t 0) (evol x t 1) := rfl
  simpa only [C, A, tally, mb, ma, black, ends, Nat.zero_add, Int.zero_add] using And.intro (est false n) (est true n)

/-- Joint limiting densities in the usual real topology. -/
def HasDensities (x : ℤ → Bool) (c a : ℝ) : Prop :=
  Tendsto (fun n : ℕ => (black (evol x) 0 0 n:ℝ)/n) atTop (𝓝 c) ∧
  Tendsto (fun n : ℕ => (ends (evol x) 0 0 n:ℝ)/n) atTop (𝓝 a)

/-- For each point in the closed pentagon, a single physical orbit realizes both frequencies. -/
theorem limits_from_any_right_half {c a : ℝ} (h : InPentagon c a) (r : ℕ → Bool) :
    ∃ x : ℤ → Bool, (∀ j : ℕ, evol x 0 j = r j) ∧ HasDensities x c a := by
  obtain ⟨x,right,est⟩ := quantitative_realization h r
  exact ⟨x,right,square_bound_limit _ _ (fun n => (est n).1),
    square_bound_limit _ _ (fun n => (est n).2)⟩

/-- Every joint limit of an ordinary row satisfies all five faces. -/
theorem necessary {x : ℤ → Bool} {c a : ℝ} (h : HasDensities x c a) : InPentagon c a := by
  let C (n : ℕ) : ℝ := black (evol x) 0 0 n
  let A (n : ℕ) : ℝ := ends (evol x) 0 0 n
  obtain ⟨hc,ha⟩ := h
  change Tendsto (fun n : ℕ => C n/n) atTop (𝓝 c) at hc
  change Tendsto (fun n : ℕ => A n/n) atTop (𝓝 a) at ha
  have face (u v k d : ℝ) (bound : ∀ n : ℕ, u*C n+v*A n ≤ k*n+d) : u*c+v*a ≤ k := by
    have lh := (hc.const_mul u).add (ha.const_mul v)
    have rh : Tendsto (fun n : ℕ => k+d/n) atTop (𝓝 k) := by
      simpa using (tendsto_const_div_atTop_nhds_zero_nat d).const_add k
    apply le_of_tendsto_of_tendsto lh rh
    filter_upwards [eventually_ge_atTop 1] with n hn
    have pos : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
    change u*(C n/n)+v*(A n/n) ≤ k+d/n
    calc
      _ = (u*C n+v*A n)/n := by ring
      _ ≤ (k*n+d)/n := div_le_div_of_nonneg_right (bound n) pos.le
      _ = _ := by rw [add_div, mul_div_cancel_right₀ _ pos.ne']
  have bounds (n : ℕ) : 0 ≤ A n ∧ A n ≤ C n ∧ 3*C n ≤ n+5*A n+3 ∧
      2*C n ≤ n+2*A n+1 ∧ 6*C n ≤ 5*n+A n+5 := by
    have ⟨b₁,b₂,b₃⟩ := region (u := evol x) (fun _ _ => rfl) 0 0 n
    dsimp only [A, C]
    exact ⟨by exact_mod_cast ends_nonneg (evol x) 0 0 n,
      by exact_mod_cast ends_le_black (evol x) 0 0 n,
      by exact_mod_cast b₁, by exact_mod_cast b₂, by exact_mod_cast b₃⟩
  have f₀ := face 0 (-1) 0 0 (fun n => by linarith [(bounds n).1])
  have f₁ := face (-1) 1 0 0 (fun n => by linarith [(bounds n).2.1])
  have f₂ := face 3 (-5) 1 3 (fun n => by linarith [(bounds n).2.2.1])
  have f₃ := face 2 (-2) 1 1 (fun n => by linarith [(bounds n).2.2.2.1])
  have f₄ := face 6 (-1) 5 5 (fun n => by linarith [(bounds n).2.2.2.2])
  exact ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩

/-- Exact real limit region with the right half fixed before choosing a realizing row. -/
theorem real_density_region (r : ℕ → Bool) (c a : ℝ) :
    (∃ x : ℤ → Bool, (∀ j : ℕ, evol x 0 j = r j) ∧ HasDensities x c a) ↔ InPentagon c a :=
  ⟨fun ⟨_,_,h⟩ => necessary h, fun h => limits_from_any_right_half h r⟩

end Rule30Equivalents.RealDensityRegion

