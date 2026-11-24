module

public import Ruliology.CellularAutomata.Rule30Certificates.GateObserverTree
public import Ruliology.CellularAutomata.Rule30GateTrapWords

/-!
# One column shows the gate trap

Beside the alternating column, black first, read column `1` of a right half `R` at the white ticks: its *gate* `u R`. The
*trap* of `Rule30GateTrap` is a set of 829 windows of sixteen cells that no right half leaves. After entry the gate has gaps
three and five and avoids further words. Here is the converse: the gate alone shows that the window is in the trap. Every
statement is for every right half, of any support, and any start. A block of readings is *clean* if it holds none of
`00000`, `11`, `101`, `10001`, `1001001`.

* `factor_enters`: a gate that reads one of nine words of 20 to 38 readings ends it with the window in the trap.
* `sound_47_after_first`, `sound_48`: 47 clean readings, if one white sample came before them, end in the trap; from any
  sample 48 do.
* `clean_after_six`: from six samples after entry on, every block is clean. So `enter_iff_some_clean`: a right half enters
  the trap exactly when some block of 48 readings is clean. `dichotomy_iff_clean`: the right-half dichotomy, that every
  finitely supported right half enters the trap or has an eventually periodic gate, as a statement about the gate alone.
* `no_short_classifier`, `no_short_classifier_after_first`: 48 and 47 are least, for any rule on the readings that rejects
  every block ending outside the trap and accepts every block that starts ten samples or more after entry. A rule that need
  only signal each entry once does with 38 readings (`factor_after_entry`).
* `uniform_delay_48`, `uniform_delay_47`: after entry a clean block ends within 53, and 52, samples, and no bound is smaller.
* `singleton_observer`: the finite form on the single-cell pattern.

The proof is one table of sets of times on spatial prefixes, the mechanism of `Rule30TrappedRunMasks`. Eleven lines of time
stand one after another in a mask: the nine words, for rows outside the trap; `1001001` six samples after a row in the trap;
and `00000` for any row. One walk of the table against itself shows that the sets are closed under the double step, and the
last times stand on trap codes only, or on no row. Every clean word of 47 readings holds one of the nine words, but for two
that begin with four whites, and the black that must stand before them completes one.

The trap and its gaps are Bosdure's and collaborators'. For period four, L. Hallee proves that one word in one column forces
the lock (`lhallee/rule30-open`, `Columns.LockWord`).
-/

@[expose] public section

set_option maxRecDepth 100000
set_option maxHeartbeats 0
set_option Elab.async false
namespace Ruliology.CellularAutomata.Rule30GateObserver
open Rule30GateObserverTree Rule30GateTrapWords
open Rule30TrappedRunMasks (Tree)
open Rule30GateTrap Rule30DrivenPrefix Rule30Ether Rule30StripCertificates Rule30PeriodTwoCoupled Rule30PeriodTwoSideways
open Rule30ZeroBoundary

/-! ### From physical rows to the table -/

/-- The window of the right half is in the trap at the white sample `s`. -/
def InTrap (R : Nat → Bool) (s : Nat) : Prop := win R (2*s+1) ∈ trap

/-- The alternating column drives a packed row for as long as its light cone reaches. -/
theorem cone (R : Nat → Bool) (b x W : Nat) (start : ∀ j, j < W → x.testBit j = drv altCol R b (j+1)) :
    ∀ t j, j+t < W → (packed (fun k => altCol (b+k)) x t).testBit j = drv altCol R (b+t) (j+1) := by
  intro t
  induction t with
  | zero => exact start
  | succ t ih =>
    intro j hj
    rw [packed, step_bit, show b+(t+1) = b+t+1 by omega, drv_isR30 altCol R (b+t) j]
    unfold Rule30Jen.rule
    rw [ih j (by omega), ih (j+1) (by omega)]
    cases j with
    | zero => simp [drv_col0]
    | succ j => simp [ih j (by omega)]

theorem packed_twice (b x : Nat) (hb : b%2=1) : ∀ i, iterate x i = packed (fun k => altCol (b+k)) x (2*i) := by
  intro i
  induction i with
  | zero => rfl
  | succ i ih =>
    have ho : altCol (b+2*i) = false := by unfold altCol; simp; omega
    have he : altCol (b+(2*i+1)) = true := by unfold altCol; simp; omega
    rw [iterate, ih, show 2*(i+1)=2*i+1+1 by omega, packed, packed, ho, he, double]

theorem prefix_bit : ∀ (n : Nat) (f : Nat → Bool) (j : Nat), j < n → (encList (seg f n)).testBit j = f j
  | 0, _, _, h => absurd h (by omega)
  | _+1, f, 0, _ => by
    rw [Nat.testBit_zero]
    simp only [seg, encList]
    cases f 0 <;> simp <;> omega
  | n+1, f, j+1, h => by
    rw [Nat.testBit_succ]
    change (((if f 0 then 1 else 0) + 2 * encList (seg (fun i => f (i+1)) n)) / 2).testBit j = _
    have e (a : Nat) : ((if f 0 then 1 else 0) + 2*a) / 2 = a := by cases f 0 <;> simp <;> omega
    rw [e]
    exact prefix_bit n _ j (by omega)

/-- One number carries the right half from a white sample on, to any finite extent. -/
theorem packed_row (R : Nat → Bool) (s n : Nat) :
    ∃ x, ∀ i j, j + 2*i < n → (iterate x i).testBit j = drv altCol R (2*(s+i)+1) (j+1) := by
  refine ⟨encList (seg (fun j => drv altCol R (2*s+1) (j+1)) n), fun i j bound => ?_⟩
  rw [packed_twice (2*s+1) _ (by omega), show 2*(s+i)+1 = 2*s+1+2*i by omega]
  exact cone R (2*s+1) _ n (prefix_bit n _) _ _ bound

theorem gate_bit {R : Nat → Bool} {s n x : Nat}
    (h : ∀ i j, j + 2*i < n → (iterate x i).testBit j = drv altCol R (2*(s+i)+1) (j+1)) {i : Nat} (hi : 2*i < n) :
    (iterate x i).testBit 0 = u R (s+i) := h i 0 (by omega)

theorem win_code {R : Nat → Bool} {t q : Nat} (hq : ∀ j, j < 16 → q.testBit j = drv altCol R t (j+1)) :
    win R t = decode (q % 2^16) := by
  unfold win rowOf decode
  apply Rule30Ether.seg_congr
  intro j hj
  rw [Nat.testBit_mod_two_pow, Nat.zero_add]
  simp [hj, hq j hj]

theorem seg_at : ∀ (n : Nat) (f : Nat → Bool) (j : Nat), j<n → (seg f n).getD j false = f j
  | 0, _, _, h => absurd h (by omega)
  | _+1, _, 0, _ => rfl
  | n+1, f, j+1, h => seg_at n (fun i => f (i+1)) j (by omega)

theorem trap_bounds : trapCodes.all (fun n => n < 2^16) = true := by decide +kernel

theorem code_of_trap {R : Nat → Bool} {t q : Nat} (h : win R t ∈ trap)
    (hq : ∀ j, j < 16 → q.testBit j = drv altCol R t (j+1)) : q % 2^16 ∈ trapCodes := by
  obtain ⟨c, hc, eq⟩ := List.mem_map.mp h
  have bound : c < 2^16 := of_decide_eq_true (List.all_eq_true.mp trap_bounds c hc)
  suffices q % 2^16 = c by rwa [this]
  rw [win_code hq] at eq
  apply Nat.eq_of_testBit_eq
  intro j
  by_cases hj : j < 16
  · have e := congrArg (fun L : List Bool => L.getD j false) eq
    change (seg (fun i => c.testBit i) 16).getD j false = (seg (fun i => (q % 2^16).testBit i) 16).getD j false at e
    rw [seg_at _ _ _ hj, seg_at _ _ _ hj] at e
    exact e.symm
  · have big : (2:Nat)^16 ≤ 2^j := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le (Nat.mod_lt _ (by decide)) big),
      Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le bound big)]

/-! ### The factors, the settling law and the five whites -/

theorem factor_line {w : List Bool} (mem : w ∈ factors) : ∃ o, (o, w) ∈ lines ∧ 0 < w.length ∧ w.length ≤ 38 := by
  simp only [factors, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · exact ⟨0, by decide, by decide, by decide⟩
  · exact ⟨20, by decide, by decide, by decide⟩
  · exact ⟨43, by decide, by decide, by decide⟩
  · exact ⟨69, by decide, by decide, by decide⟩
  · exact ⟨98, by decide, by decide, by decide⟩
  · exact ⟨128, by decide, by decide, by decide⟩
  · exact ⟨158, by decide, by decide, by decide⟩
  · exact ⟨189, by decide, by decide, by decide⟩
  · exact ⟨222, by decide, by decide, by decide⟩

/-- **A factor certifies the trap.** Whatever the right half, a gate that reads one of the nine factors ends it with the
window in the trap. -/
theorem factor_enters {w : List Bool} (mem : w ∈ factors) {R : Nat → Bool} {s : Nat} (read : Reads (u R) s w) :
    InTrap R (s + (w.length - 1)) := by
  obtain ⟨o, line, pos, short⟩ := factor_line mem
  obtain ⟨x, hx⟩ := packed_row R s 100
  have code := line_ends line x (fun t ht => by
    have lt : t < w.length := ht
    rw [gate_bit hx (by omega)]
    exact read t lt) pos
  change iterate x (w.length - 1) % 2^16 ∈ trapCodes at code
  unfold InTrap
  rw [win_code (q := iterate x (w.length - 1)) (fun j hj => hx _ j (by omega))]
  exact List.mem_map.mpr ⟨_, code, rfl⟩

/-- Every five consecutive readings of any right half hold a black one. -/
theorem black_in_every_five (R : Nat → Bool) (s : Nat) : ∃ j, j < 5 ∧ u R (s+j) = true := by
  apply Classical.byContradiction
  intro none
  have white (j : Nat) (hj : j < 5) : u R (s+j) = false := by
    cases h : u R (s+j)
    · rfl
    · exact absurd ⟨j, hj, h⟩ none
  obtain ⟨x, hx⟩ := packed_row R s 32
  have bit (j : Nat) (hj : j < 5) : (iterate x j).testBit 0 = false := (gate_bit hx (by omega)).trans (white j hj)
  have all := march (o := 273) (n := 4) (row := x) (start_child table_whites.1 (bit 0 (by decide))) (fun t ht => by
    rw [bit (t+1) (by omega)]
    exact (by decide +kernel : ∀ i : Fin 4, (colourMask false).testBit (273 + (i.val+1)) = true) ⟨t, ht⟩)
  exact absurd (high_of_value (all 4 (by decide))) (by rw [table_whites.2]; decide)

/-- **Settling.** Six samples after entry the gate reads no two successive 3-gaps. -/
theorem no_33_after_six {R : Nat → Bool} {a s : Nat} (entry : InTrap R a) (late : a+6 ≤ s) :
    ¬ Reads (u R) s [true, false, false, true, false, false, true] := by
  intro read
  obtain ⟨b, rfl⟩ : ∃ b, s = b + 6 := ⟨s - 6, by omega⟩
  have at_b : win R (2*b+1) ∈ trap := by
    have h := win_mem_trap R (t0 := 2*a+1) (by omega) entry (b-a)
    rwa [show 2*a+1+2*(b-a) = 2*b+1 by omega] at h
  obtain ⟨x, hx⟩ := packed_row R b 64
  have code := code_of_trap at_b (q := x) (fun j hj => hx 0 j (by omega))
  have start : (table.value x 0).testBit 260 = true := by
    have base := List.all_eq_true.mp table_settle _ code
    rw [Tree.follow_mod] at base
    have bit := ((table.follow x 16).bounds (table.follow_valid table_valid x 16) x 16 260).1 base
    simpa only [Tree.follow_value] using bit
  have all := march (o := 260) (n := 12) (row := x) start (fun t ht => by
    by_cases early : t + 1 < 6
    · exact (by decide +kernel : ∀ c : Bool, ∀ i : Fin 5, (colourMask c).testBit (260 + (i.val+1)) = true) _ ⟨t, by omega⟩
    · have r := read (t+1-6) (by show t+1-6 < 7; omega)
      rw [show b + 6 + (t+1-6) = b + (t+1) by omega] at r
      rw [gate_bit hx (by omega), r]
      have k : ∀ i : Fin 7, (colourMask ([true, false, false, true, false, false, true].getD i.val false)).testBit
          (266 + i.val) = true := by decide +kernel
      have h := k ⟨t+1-6, by omega⟩
      simpa only [show 266 + (t+1-6) = 260 + (t+1) by omega] using h)
  exact absurd (high_of_value (all 12 (by decide))) (by rw [table_settled]; decide)

/-! ### Clean readings -/

/-- The five forbidden words. -/
def forbidden : List (List Bool) :=
  [[false,false,false,false,false], [true,true], [true,false,true], [true,false,false,false,true],
   [true,false,false,true,false,false,true]]

/-- No forbidden word lies wholly inside the `n` readings from `s`. -/
def Clean (g : Nat → Bool) (s n : Nat) : Prop :=
  ∀ off w, w ∈ forbidden → off + w.length ≤ n → ¬ Reads g (s+off) w

theorem Clean.sub {g : Nat → Bool} {s n : Nat} (h : Clean g s n) (k m : Nat) (hm : k + m ≤ n) : Clean g (s+k) m := by
  intro off w mem bound read
  exact h (k+off) w mem (by omega) (by rwa [show s + (k+off) = s+k+off by omega])

/-- From six samples after entry on, every block is clean. -/
theorem clean_after_six {R : Nat → Bool} {a s : Nat} (entry : InTrap R a) (late : a+6 ≤ s) (n : Nat) :
    Clean (u R) s n := by
  intro off w mem _ read
  have gap := gaps_of_entry R (t0 := 2*a+1) (by omega) entry (s+off) (by omega)
  simp only [forbidden, List.mem_cons, List.not_mem_nil, or_false] at mem
  rcases mem with rfl | rfl | rfl | rfl | rfl
  · obtain ⟨j, hj, black⟩ := black_in_every_five R (s+off)
    have white := read j hj
    rw [black] at white
    have zero : ∀ i : Fin 5, [false,false,false,false,false].getD i.val false = false := by decide
    rw [zero ⟨j, hj⟩] at white
    exact Bool.noConfusion white
  · rcases gap (read 0 (by decide)) with h | h <;> exact Bool.noConfusion (h.1.symm.trans (read 1 (by decide)))
  · rcases gap (read 0 (by decide)) with h | h <;> exact Bool.noConfusion (h.2.1.symm.trans (read 2 (by decide)))
  · rcases gap (read 0 (by decide)) with h | h
    · exact Bool.noConfusion (h.2.2.symm.trans (read 3 (by decide)))
    · exact Bool.noConfusion (h.2.2.2.1.symm.trans (read 4 (by decide)))
  · exact no_33_after_six entry (by omega : a+6 ≤ s+off) read

/-! ### Every clean word holds a factor -/

def hits (patterns : List (List Bool)) (suffix : List Bool) : Bool := patterns.any (·.isPrefixOf suffix)

/-- Grow a word towards its beginning and stop at the first recognised pattern. -/
def search (patterns : List (List Bool)) : Nat → List Bool → Bool
  | 0, suffix => hits patterns suffix
  | n+1, suffix => hits patterns suffix || (search patterns n (false::suffix) && search patterns n (true::suffix))

def readings (g : Nat → Bool) (s : Nat) : Nat → List Bool
  | 0 => []
  | n+1 => g s :: readings g (s+1) n

theorem readings_len (g s n) : (readings g s n).length = n := by
  induction n generalizing s with
  | zero => rfl
  | succ n ih => simpa only [readings, List.length_cons] using congrArg Nat.succ (ih (s+1))

theorem read_index (g s n i) (h : i<n) : (readings g s n).getD i false = g (s+i) := by
  induction n generalizing s i with
  | zero => omega
  | succ n ih =>
    cases i with
    | zero => rfl
    | succ i =>
      change (readings g (s+1) n).getD i false = _
      simpa only [show s+1+i=s+(i+1) by omega] using ih (s+1) i (by omega)

theorem hit_sound (patterns : List (List Bool)) (g s n) (hit : hits patterns (readings g s n) = true) :
    ∃ w ∈ patterns, w.length ≤ n ∧ Reads g s w := by
  obtain ⟨w, mem, h⟩ := List.any_eq_true.mp hit
  obtain ⟨rest, eq⟩ := List.isPrefixOf_iff_prefix.mp h
  have len := congrArg List.length eq
  simp only [List.length_append, readings_len] at len
  refine ⟨w, mem, by omega, ?_⟩
  intro j bound
  have h := congrArg (fun l : List Bool => l.getD j false) eq
  rw [read_index g s n j (by omega)] at h
  simpa only [List.getD_eq_getElem?_getD, List.getElem?_append_left bound] using h.symm

theorem search_sound (patterns : List (List Bool)) (g : Nat → Bool) (s n tail : Nat)
    (checked : search patterns n (readings g (s+n) tail) = true) :
    ∃ off w, w ∈ patterns ∧ off+w.length ≤ n+tail ∧ Reads g (s+off) w := by
  have here (yes : hits patterns (readings g (s+n) tail) = true) :
      ∃ off w, w ∈ patterns ∧ off+w.length ≤ n+tail ∧ Reads g (s+off) w := by
    obtain ⟨w, mem, bound, r⟩ := hit_sound patterns _ _ _ yes
    exact ⟨n, w, mem, by omega, r⟩
  induction n generalizing tail with
  | zero => exact here checked
  | succ n ih =>
    rcases Bool.or_eq_true_iff.mp checked with done | both
    · exact here done
    · have branches := Bool.and_eq_true_iff.mp both
      have sub : search patterns n (readings g (s+n) (tail+1)) = true := by
        change search patterns n (g (s+n) :: readings g (s+n+1) tail) = true
        cases g (s+n) <;> first | exact branches.1 | exact branches.2
      obtain ⟨off, w, mem, size, matchW⟩ := ih (tail+1) sub (by
        intro found
        obtain ⟨w, mem, bound, r⟩ := hit_sound patterns _ _ _ found
        exact ⟨n, w, mem, by omega, r⟩)
      exact ⟨off, w, mem, by omega, matchW⟩

/-- The two clean words of 47 readings that hold no factor. Both begin with four whites. -/
def options : List (List Bool) := [word 47 0x84842109090, word 47 0x210842109090]

theorem cover47 : search (forbidden ++ (options ++ factors)) 47 [] = true := by decide +kernel

/-- With the black that must stand before it, each of the two begins with a factor. -/
theorem options_factor : ∀ w ∈ options, w.length = 47 ∧ (∀ j : Fin 4, w.getD j.val false = false) ∧
    ∃ m ∈ factors, m.isPrefixOf (true :: w) = true := by decide +kernel

theorem reads_prefix {g : Nat → Bool} {s : Nat} {m l : List Bool} (pre : m.isPrefixOf l = true) (read : Reads g s l) :
    Reads g s m := by
  obtain ⟨rest, eq⟩ := List.isPrefixOf_iff_prefix.mp pre
  intro j hj
  have len := congrArg List.length eq
  simp only [List.length_append] at len
  rw [read j (by omega), ← eq]
  simp only [List.getD_eq_getElem?_getD, List.getElem?_append_left hj]

theorem later {R : Nat → Bool} {a s : Nat} (h : InTrap R a) (le : a ≤ s) : InTrap R s := by
  have e := win_mem_trap R (t0 := 2*a+1) (by omega) h (s-a)
  unfold InTrap
  rwa [show 2*a+1+2*(s-a) = 2*s+1 by omega] at e

/-- With one white sample gone by, 47 clean readings hold a factor, or complete one together with the sample before them. -/
theorem clean_47_factor (R : Nat → Bool) (s : Nat) (clean : Clean (u R) (s+1) 47) :
    ∃ off w, w ∈ factors ∧ off + w.length ≤ 48 ∧ Reads (u R) (s+off) w := by
  obtain ⟨off, w, member, bound, read⟩ := search_sound _ (u R) (s+1) 47 0 cover47
  rcases List.mem_append.mp member with bad | good
  · exact absurd read (clean off w bad bound)
  rcases List.mem_append.mp good with special | marked
  · obtain ⟨len, zeros, m, hm, pre⟩ := options_factor w special
    have start : off = 0 := by omega
    subst off
    have white (k : Nat) (hk : k < 4) : u R (s+1+k) = false := (read k (by omega)).trans (zeros ⟨k, hk⟩)
    have black : u R s = true := by
      obtain ⟨j, small, hit⟩ := black_in_every_five R s
      cases j with
      | zero => exact hit
      | succ j =>
        have e := white j (by omega)
        rw [show s+1+j = s+(j+1) by omega, hit] at e
        exact Bool.noConfusion e
    have whole : Reads (u R) s (true :: w) := by
      intro j hj
      cases j with
      | zero => exact black
      | succ j =>
        have e := read j (by simpa using hj)
        rw [show s+1+0+j = s+(j+1) by omega] at e
        exact e
    obtain ⟨o, -, -, short⟩ := factor_line hm
    exact ⟨0, m, hm, by omega, reads_prefix pre whole⟩
  · exact ⟨1+off, w, marked, by omega, by rwa [show s+(1+off) = s+1+off by omega]⟩

/-- **Forty-seven clean readings after the first white tick.** For every right half, if a white sample has gone by and the
next 47 readings are clean, the window at the last of them is in the trap. The earlier reading need not be known. -/
theorem sound_47_after_first (R : Nat → Bool) (s : Nat) (clean : Clean (u R) (s+1) 47) : InTrap R (s+47) := by
  obtain ⟨off, w, mem, bound, read⟩ := clean_47_factor R s clean
  obtain ⟨o, -, pos, -⟩ := factor_line mem
  exact later (factor_enters mem read) (by omega)

/-- **Forty-eight clean readings** put the window at the last of them in the trap, for every right half, from any sample. -/
theorem sound_48 (R : Nat → Bool) (s : Nat) (clean : Clean (u R) s 48) : InTrap R (s+47) :=
  sound_47_after_first R s (clean.sub 1 47 (by decide))

/-- **One column shows the trap.** A right half enters the trap exactly when some block of 48 readings is clean. -/
theorem enter_iff_some_clean (R : Nat → Bool) : (∃ a, InTrap R a) ↔ ∃ s, Clean (u R) s 48 :=
  ⟨fun ⟨a, h⟩ => ⟨a+6, clean_after_six h (Nat.le_refl _) 48⟩, fun ⟨s, h⟩ => ⟨s+47, sound_48 R s h⟩⟩

/-- **Thirty-eight readings signal every entry.** Within 53 samples of entry the gate completes a factor, and each factor
certifies the trap. So a rule on the last 38 readings signals every entry once; it does not accept every later block. -/
theorem factor_after_entry {R : Nat → Bool} {a : Nat} (entry : InTrap R a) :
    ∃ s w, w ∈ factors ∧ w.length ≤ 38 ∧ a ≤ s ∧ s + (w.length - 1) ≤ a+53 ∧ Reads (u R) s w ∧
      InTrap R (s + (w.length - 1)) := by
  obtain ⟨off, w, mem, bound, read⟩ := clean_47_factor R (a+6) (clean_after_six entry (by omega) 47)
  obtain ⟨o, -, pos, short⟩ := factor_line mem
  exact ⟨a+6+off, w, mem, short, by omega, by omega, read, factor_enters mem read⟩

/-- The right-half dichotomy, that every finitely supported right half enters the trap or has an eventually periodic gate, as
a statement about the gate alone. -/
theorem dichotomy_iff_clean :
    (∀ R : Nat → Bool, FinSupp R → (∃ t, t % 2 = 1 ∧ win R t ∈ trap) ∨ Rule30Jen.EventuallyPeriodic (u R)) ↔
      ∀ R : Nat → Bool, FinSupp R → ¬ Rule30Jen.EventuallyPeriodic (u R) → ∃ s, Clean (u R) s 48 := by
  constructor
  · intro h R fin aper
    rcases h R fin with ⟨t, odd, inside⟩ | per
    · refine (enter_iff_some_clean R).mp ⟨t/2, ?_⟩
      unfold InTrap
      rwa [show 2*(t/2)+1 = t by omega]
    · exact absurd per aper
  · intro h R fin
    by_cases per : Rule30Jen.EventuallyPeriodic (u R)
    · exact Or.inr per
    · obtain ⟨a, inside⟩ := (enter_iff_some_clean R).mpr (h R fin per)
      exact Or.inl ⟨2*a+1, by omega, inside⟩

/-! ### The two lengths are sharp, and so are the two delays -/

/-- A finite right half from a number: cell `j + 1` is bit `j`. -/
abbrev finite (x : Nat) : Nat → Bool := IntegerForm.rowOfNat x

theorem finite_bit (x t p : Nat) : drv altCol (finite x) t (p+1) = (packed altCol x t).testBit p :=
  (packed_sound altCol (finite x) x (fun _ => rfl) t p).symm

theorem finite_gate (x s : Nat) : u (finite x) s = (packed altCol x (2*s+1)).testBit 0 := finite_bit x (2*s+1) 0

theorem finite_win (x t : Nat) : win (finite x) t = decode (packed altCol x t % 2^16) :=
  win_code (fun j _ => (finite_bit x t j).symm)

def outerSeed : Nat := 0xa224d3200017fb5ccd115f23a59
def innerSeed : Nat := 0x4319fc9fcd612848b70077729985e4b9

theorem same_reading : ∀ j, j < 47 → u (finite outerSeed) j = u (finite innerSeed) (10+j) := by
  intro j hj
  rw [finite_gate, finite_gate]
  exact (by decide +kernel : ∀ i : Fin 47, (packed altCol outerSeed (2*i.val+1)).testBit 0 =
    (packed altCol innerSeed (2*(10+i.val)+1)).testBit 0) ⟨j, hj⟩

theorem outer_outside : ¬ InTrap (finite outerSeed) 46 := by
  unfold InTrap
  rw [finite_win]
  decide +kernel

theorem inner_inside : InTrap (finite innerSeed) 0 := by
  unfold InTrap
  rw [finite_win]
  decide +kernel

theorem no_rule {n k : Nat} (pos : 0 < n) (hk : k + n = 47) :
    ¬ ∃ f : (Fin n → Bool) → Bool,
      (∀ R : Nat → Bool, FinSupp R → ∀ s, k ≤ s → ¬ InTrap R (s+(n-1)) → f (fun j => u R (s+j.val)) = false) ∧
      (∀ R : Nat → Bool, FinSupp R → ∀ a s, InTrap R a → a+10 ≤ s → f (fun j => u R (s+j.val)) = true) := by
  rintro ⟨f, reject, accept⟩
  have same : (fun j : Fin n => u (finite outerSeed) (k+j.val)) = fun j : Fin n => u (finite innerSeed) (10+k+j.val) := by
    funext j
    have h := same_reading (k+j.val) (by have := j.isLt; omega)
    rwa [show 10+(k+j.val) = 10+k+j.val by omega] at h
  have no := reject (finite outerSeed) (IntegerForm.finSupp_rowOfNat _) k (Nat.le_refl _)
    (by rw [show k+(n-1) = 46 by omega]; exact outer_outside)
  have yes := accept (finite innerSeed) (IntegerForm.finSupp_rowOfNat _) 0 (10+k) inner_inside (by omega)
  rw [same, yes] at no
  exact Bool.noConfusion no

/-- **Forty-eight is least.** No rule on `n ≤ 47` readings rejects every block that ends outside the trap and accepts every
block that starts ten samples or more after entry, even on finitely supported right halves. -/
theorem no_short_classifier (n : Nat) (pos : 0 < n) (short : n ≤ 47) :
    ¬ ∃ f : (Fin n → Bool) → Bool,
      (∀ R : Nat → Bool, FinSupp R → ∀ s, ¬ InTrap R (s+(n-1)) → f (fun j => u R (s+j.val)) = false) ∧
      (∀ R : Nat → Bool, FinSupp R → ∀ a s, InTrap R a → a+10 ≤ s → f (fun j => u R (s+j.val)) = true) := by
  rintro ⟨f, reject, accept⟩
  exact no_rule (k := 47-n) pos (by omega) ⟨f, fun R fin s _ => reject R fin s, accept⟩

/-- **Forty-seven is least** for blocks that start after the first white tick. -/
theorem no_short_classifier_after_first (n : Nat) (pos : 0 < n) (short : n ≤ 46) :
    ¬ ∃ f : (Fin n → Bool) → Bool,
      (∀ R : Nat → Bool, FinSupp R → ∀ s, 1 ≤ s → ¬ InTrap R (s+(n-1)) → f (fun j => u R (s+j.val)) = false) ∧
      (∀ R : Nat → Bool, FinSupp R → ∀ a s, InTrap R a → a+10 ≤ s → f (fun j => u R (s+j.val)) = true) := by
  rintro ⟨f, reject, accept⟩
  exact no_rule (k := 47-n) pos (by omega) ⟨f, fun R fin s hs => reject R fin s (by omega), accept⟩

/-- A finite right half that is in the trap at its first white sample and reads `1001001` at samples 5 to 11. -/
def lateSeed : Nat := 0x7fffff80fc

theorem late_inside : InTrap (finite lateSeed) 0 := by
  unfold InTrap
  rw [finite_win]
  decide +kernel

theorem late_reads : Reads (u (finite lateSeed)) 5 [true, false, false, true, false, false, true] := by
  intro j hj
  rw [finite_gate]
  exact (by decide +kernel : ∀ i : Fin 7, (packed altCol lateSeed (2*(5+i.val)+1)).testBit 0 =
    [true, false, false, true, false, false, true].getD i.val false) ⟨j, hj⟩

theorem late_dirty {s n : Nat} (hs : s ≤ 5) (hn : 12 ≤ s + n) : ¬ Clean (u (finite lateSeed)) s n := by
  intro clean
  refine clean (5-s) _ (by decide : [true, false, false, true, false, false, true] ∈ forbidden) (by simp; omega) ?_
  rw [show s + (5-s) = 5 by omega]
  exact late_reads

/-- Five samples after entry a block need not be clean, so six is least in `clean_after_six`. -/
theorem six_is_least : ¬ ∀ (R : Nat → Bool) (a n : Nat), InTrap R a → Clean (u R) (a+5) n :=
  fun h => late_dirty (s := 5) (n := 7) (Nat.le_refl _) (Nat.le_refl _) (h (finite lateSeed) 0 7 late_inside)

/-- **The delay of the 48-reading test is 53 samples:** a clean block that starts at entry or later ends by then, and 52 is
too few for one finite right half. -/
theorem uniform_delay_48 (d : Nat) :
    (∀ (R : Nat → Bool) (a : Nat), InTrap R a → ∃ s, a ≤ s ∧ s+47 ≤ a+d ∧ Clean (u R) s 48) ↔ 53 ≤ d := by
  constructor
  · intro h
    obtain ⟨s, -, hd, clean⟩ := h _ 0 late_inside
    apply Classical.byContradiction
    intro small
    exact late_dirty (by omega) (by omega) clean
  · intro h R a entry
    exact ⟨a+6, by omega, by omega, clean_after_six entry (Nat.le_refl _) 48⟩

/-- **The delay of the 47-reading test is 52 samples.** -/
theorem uniform_delay_47 (d : Nat) :
    (∀ (R : Nat → Bool) (a : Nat), InTrap R a → ∃ s, a ≤ s ∧ 1 ≤ s ∧ s+46 ≤ a+d ∧ Clean (u R) s 47) ↔ 52 ≤ d := by
  constructor
  · intro h
    obtain ⟨s, -, -, hd, clean⟩ := h _ 0 late_inside
    apply Classical.byContradiction
    intro small
    exact late_dirty (by omega) (by omega) clean
  · intro h R a entry
    exact ⟨a+6, by omega, by omega, by omega, clean_after_six entry (Nat.le_refl _) 47⟩

/-! ### On a real history -/

/-- The positive columns of a rule 30 history follow the driven right half while column `0` keeps the clock. -/
theorem agree_positive {F : Nat → Nat → Bool} (hf : IsR30 F) (a h : Nat) (clock : ∀ j, j<h → F (a+j) 0 = altCol j) :
    ∀ k, k ≤ h → ∀ p, F (a+k) (p+1) = drv altCol (F a) k (p+1) := by
  intro k
  induction k with
  | zero => intro _ p; exact (drv_init _ _ _ (Nat.succ_pos p)).symm
  | succ k ih =>
    intro bound p
    rw [show a+(k+1) = a+k+1 by omega, hf, drv_isR30]
    have eq (q : Nat) : F (a+k) q = drv altCol (F a) k q := by
      cases q with
      | zero => exact (clock k (by omega)).trans (drv_col0 ..).symm
      | succ q => exact ih (by omega) q
    rw [eq p, eq (p+1), eq (p+2)]

/-- **On the single cell.** If the center alternates, black first, for the 95 ticks from age `a`, and the 48 readings of its
right neighbour at the white ticks are clean, the sixteen cells right of the center are then in the trap. -/
theorem singleton_observer (a : Nat) (clock : ∀ j, j < 95 → Rule30Jen.cell (a+j) 0 = altCol j)
    (clean : Clean (fun i => trueRight (a+(2*i+1)) 1) 0 48) : seg (fun i => trueRight (a+95) (i+1)) 16 ∈ trap := by
  have eq := agree_positive trueRight_isR30 a 95 clock
  have gate (i : Nat) (hi : i < 48) : u (trueRight a) i = trueRight (a+(2*i+1)) 1 := (eq (2*i+1) (by omega) 0).symm
  have same : Clean (u (trueRight a)) 0 48 := by
    intro off w mem bound read
    refine clean off w mem bound fun j hj => ?_
    have e := gate (0+off+j) (by omega)
    have r := read j hj
    rw [e] at r
    exact r
  have inside : InTrap (trueRight a) 47 := by simpa only [Nat.zero_add] using sound_48 (trueRight a) 0 same
  have at95 : win (trueRight a) 95 ∈ trap := inside
  have win_eq : win (trueRight a) 95 = seg (fun i => trueRight (a+95) (i+1)) 16 := by
    unfold win rowOf
    apply Rule30Ether.seg_congr
    intro j _
    rw [Nat.zero_add]
    exact (eq 95 (Nat.le_refl _) j).symm
  rwa [win_eq] at at95

end Ruliology.CellularAutomata.Rule30GateObserver
