module

public import Ruliology.CellularAutomata.Rule30Blocks
public import Ruliology.CellularAutomata.Rule30SidewaysLocks

/-!
# A finite right prefix and a recurring error at the singleton's left edge

Start with the single seed's positive right half at tick 364 and keep the
center alternating, black at the start. Its 30-cell window enters the
existing period-seven lock in class 6 after 95 ticks. The first 80 positive
cells of the start suffice for that entry, with arbitrary cells farther right.

From the entry onwards, the unique compatible left half agrees at every
depth with a cyclic spatial row of length 728 evolving in 14 time phases.
At every absolute age 459 + 2*n, one of its first seven readings at the
expected left edge differs from the genuine singleton at that age. Six
readings can all agree at age 991. These statements compare a driven
continuation with an independently evolved singleton. The singleton itself
breaks the proposed alternation at tick 366. Later potential onsets remain open.
-/

@[expose] public section

namespace Ruliology.CellularAutomata.Rule30LockedSeedEdge

open Rule30SidewaysLocks Rule30PeriodTwoSideways BusyBeaverLifetimes
open Rule30ZeroBoundary (zrow zrow_inv zrow_wall)

private theorem seed_eq (t : Nat) : Rule30Jen.cell t = TwoColor.cell 30 1 t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Rule30Blocks.cell_succ]
    funext j
    change Rule30Jen.rule (Rule30Jen.cell t (j-1)) (Rule30Jen.cell t j) (Rule30Jen.cell t (j+1)) = _
    rw [ih]
    rfl

-- The kit starts the alternating drive on black, one tick after white age 363.
def right364 (p : Nat) := Rule30Jen.cell 364 (p : Int)
/-- Sites +1 through +80 at age 364, least significant bit nearest the center. -/
def prefix364 : Nat := 248139127718118986536413

set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

private theorem seed_prefix (i : Nat) (hi : i < 80) :
    right364 (i+1) = prefix364.testBit i := by
  unfold right364
  rw [seed_eq, Rule30Blocks.cell_eq _ _ (by omega)]
  have h : ∀ j : Fin 80,
      (Rule30Blocks.plane 364).testBit (j.val+366) = prefix364.testBit j.val := by decide +kernel
  have arg : (((i+1 : Nat) : Int)+((364 : Nat) : Int)+1).toNat = i+366 := by omega
  exact Eq.trans (congrArg (Rule30Blocks.plane 364).testBit arg) (h ⟨i,hi⟩)

-- With an unknown right exterior, a black last known cell shields its output.
-- In that case we retain one more cell than the ordinary shrinking light cone.
private def fits : List Bool → (Nat → Bool) → Prop
  | [], _ => True
  | b :: bs, f => b = f 0 ∧ fits bs (fun i => f (i+1))

private def safe : List Bool → List Bool
  | a :: b :: c :: xs => Rule30Jen.rule a b c :: safe (b :: c :: xs)
  | [a,true] => [!a]
  | _ => []

private theorem safe_fits : ∀ xs f, fits xs f →
    fits (safe xs) (fun i => Rule30Jen.rule (f i) (f (i+1)) (f (i+2)))
  | [], _, _ => trivial
  | [_], _, _ => trivial
  | [a,false], _, _ => trivial
  | [a,true], f, h => by
    obtain ⟨ha,hb,_⟩ := h
    refine ⟨?_, trivial⟩
    change true = f 1 at hb
    change (!a) = Rule30Jen.rule (f 0) (f 1) (f 2)
    rw [← ha, ← hb]
    cases a <;> cases f 2 <;> rfl
  | a :: b :: c :: xs, f, h => by
    obtain ⟨ha,hb,hc,rest⟩ := h
    exact ⟨congrArg₂_rule ha hb hc,
      safe_fits (b::c::xs) (fun i => f (i+1)) ⟨hb,hc,rest⟩⟩
where
  congrArg₂_rule {a b c l m r : Bool} (ha : a=l) (hb : b=m) (hc : c=r) :
      Rule30Jen.rule a b c = Rule30Jen.rule l m r := by rw [ha,hb,hc]

private def advance : Nat → Nat → List Bool → List Bool
  | _,0,xs => xs
  | t,n+1,xs => advance (t+1) n (safe (Rule30PeriodTwoCoupled.altCol t :: xs))

private theorem advance_fits (R : Nat → Bool) : ∀ n t xs,
    fits xs (fun i => Rule30Ether.drv Rule30PeriodTwoCoupled.altCol R t (i+1)) →
    fits (advance t n xs) (fun i => Rule30Ether.drv Rule30PeriodTwoCoupled.altCol R (t+n) (i+1))
  | 0,_,_,h => h
  | n+1,t,xs,h => by
    have after := safe_fits (Rule30PeriodTwoCoupled.altCol t :: xs)
      (Rule30Ether.drv Rule30PeriodTwoCoupled.altCol R t) ⟨(Rule30Ether.drv_col0 _ _ t).symm,h⟩
    simpa only [advance,show t+(n+1) = (t+1)+n by omega] using
      advance_fits R n (t+1) _ after

open Rule30StripCertificates (seg)

private theorem fit_seg (n : Nat) (f g : Nat → Bool) (h : ∀ i, i<n → f i=g i) :
    fits (seg f n) g := by
  induction n generalizing f g with
  | zero => trivial
  | succ n ih => exact ⟨h 0 (by omega),ih _ _ (fun i hi => h (i+1) (by omega))⟩

private theorem read_fits (n : Nat) (xs : List Bool) (f : Nat → Bool)
    (h : fits xs f) (len : n ≤ xs.length) : seg f n = xs.take n := by
  induction n generalizing xs f with
  | zero => rfl
  | succ n ih =>
    cases xs with
    | nil => simp at len
    | cons x xs =>
      obtain ⟨head,tail⟩ := h
      change f 0 :: seg (fun i => f (i+1)) n = x :: xs.take n
      rw [← head, ih _ _ tail (by simpa using len)]

theorem prefix_enters_lock7 {R : Nat → Bool}
    (h : ∀ i, i < 80 → R (i+1) = prefix364.testBit i) :
    winW 30 R 95 ∈ cls 30 lock7Codes 6 := by
  let start := decodeW 80 prefix364
  have known : fits start (fun i => Rule30Ether.drv Rule30PeriodTwoCoupled.altCol R 0 (i+1)) :=
    fit_seg _ _ _ fun i hi => by rw [Rule30Ether.drv_init _ _ _ (by omega),h i hi]
  have out := read_fits 30 _ _ (advance_fits R 95 0 start known) (by decide +kernel)
  have mem : (advance 0 95 start).take 30 ∈ cls 30 lock7Codes 6 := by decide +kernel
  unfold winW Rule30Ether.rowOf
  simpa only [Nat.zero_add, ← out] using mem

theorem seed364_enters : winW 30 right364 95 ∈ cls 30 lock7Codes 6 :=
  prefix_enters_lock7 seed_prefix

theorem seed364_no_finite_left : ¬ Rule30ZeroBoundary.FinSupp (Psi right364) :=
  not_finSupp_Psi_of_lock (V := 29) lock7_ok (by decide) right364
    (s0 := 47) (k := 6) (by decide) seed364_enters

-- The entry-phase ring, indexed by depth. The local recurrence, the boundary
-- readings, and the seven-cell comparison below certify this witness. To find
-- it, start with the 14-bit temporal profiles at sites 0 and -1 fixed by
-- word7. Reconstruct each next column to the left using Rule 30 inversion.
-- The pair returns after 728 columns. Read off the class-6 white row.
private def ringStep (r : Nat) : Nat :=
  let left := (r >>> 1) ||| ((r % 2) <<< 727)
  let right := ((r <<< 1) % 2^728) ||| (r >>> 727)
  left ^^^ (r ||| right)

private def ringRow : Nat → Nat
  | 0 => 0x4a843e23d80b43315d28d22c4c8cbcb1c91d493e121ef07d82ace05d4af8cbd0613b58bbe5fa2a2c4fdca7049d4be6351f8a790202b9d3453633dc8a5b09704a8212362ae02b4013e0e9dda36caa799b42cd23359e17d53731864a
  | t+1 => ringStep (ringRow t)

private def planes : Array Nat := ((List.range 14).map ringRow).toArray

private def tile (t d : Nat) : Bool := (planes.getD (t%14) 0).testBit (d%728)

private theorem tile_inv (t d : Nat) :
    tile t (d+2) = xor (tile (t+1) (d+1)) (tile t (d+1) || tile t d) := by
  have check : ∀ i : Fin 14, ∀ j : Fin 728,
      tile i (j.val+2) = xor (tile (i.val+1) (j.val+1)) (tile i (j.val+1) || tile i j) := by
    decide +kernel
  have h := check ⟨t%14,by omega⟩ ⟨d%728,by omega⟩
  simpa only [tile,Nat.mod_add_mod,Nat.mod_mod] using h

private theorem wall_inv (t : Nat) :
    tile t 2 = xor (tile (t+1) 1) (tile t 1 || false) := by
  have check : ∀ i : Fin 14, tile i 2 = xor (tile (i.val+1) 1) (tile i 1 || false) := by decide +kernel
  simpa only [tile,Nat.mod_add_mod,Nat.mod_mod] using check ⟨t%14,by omega⟩

private theorem tile_even (q : Nat) : tile (2*q) 1 = !word7.getD ((6+q)%7) false := by
  have check : ∀ i : Fin 7, tile (2*i.val) 1 = !word7.getD ((6+i.val)%7) false := by decide +kernel
  have h := check ⟨q%7,by omega⟩
  change tile (2*(q%7)) 1 = !word7.getD ((6+q%7)%7) false at h
  unfold tile at h ⊢
  simpa only [show (2*(q%7))%14 = (2*q)%14 by omega, Nat.add_mod_mod] using h

private theorem tile_odd (q : Nat) : tile (2*q+1) 1 = true := by
  have check : ∀ i : Fin 7, tile (2*i.val+1) 1 = true := by decide +kernel
  have h := check ⟨q%7,by omega⟩
  change tile (2*(q%7)+1) 1 = true at h
  unfold tile at h ⊢
  simpa only [show (2*(q%7)+1)%14 = (2*q+1)%14 by omega] using h

private theorem near (R : Nat → Bool) (entry : winW 30 R 95 ∈ cls 30 lock7Codes 6)
    (t : Nat) : zrow (Psi R) (95+t) 1 = tile t 1 := by
  rw [Psi_col]
  by_cases h : t%2=0
  · obtain ⟨q,rfl⟩ : ∃ q, t=2*q := ⟨t/2,by omega⟩
    rw [tile_even,show 95+2*q=2*(47+q)+1 by omega, alt_odd]
    rw [u_of_lock (V:=29) lock7_ok (by decide) R (s0:=47) (k:=6) (by decide) entry]
  · obtain ⟨q,rfl⟩ : ∃ q, t=2*q+1 := ⟨t/2,by omega⟩
    rw [tile_odd,show 95+(2*q+1)=2*(48+q) by omega, alt_even]

private theorem locked_tile (R : Nat → Bool) (entry : winW 30 R 95 ∈ cls 30 lock7Codes 6)
    (d t : Nat) : zrow (Psi R) (95+t) (d+1) = tile t (d+1) := by
  have pair : ∀ k, (∀ s, zrow (Psi R) (95+s) (k+1) = tile s (k+1)) ∧
      (∀ s, zrow (Psi R) (95+s) (k+2) = tile s (k+2)) := by
    intro k
    induction k with
    | zero =>
      refine ⟨near R entry,fun s => ?_⟩
      rw [zrow_inv (Psi R) (95+s) 0, zrow_wall]
      simp only [Nat.zero_add]
      rw [show 95+s+1 = 95+(s+1) by omega, near R entry, near R entry, wall_inv]
    | succ k ih =>
      refine ⟨ih.2,fun s => ?_⟩
      rw [zrow_inv (Psi R) (95+s) (k+1), show 95+s+1 = 95+(s+1) by omega,
          ih.2, ih.2, ih.1, tile_inv s (k+1)]
  exact (pair d).1 t

-- The first seven cells of the genuine singleton at an odd age ≥3 are 1101111.
private def edge7 (j : Nat) := (123 : Nat).testBit j

private theorem phase_miss (n : Nat) : ∃ j : Fin 7,
    tile (2*n) (459+2*n-j.val) ≠ edge7 j.val := by
  have check : ∀ k : Fin 364, ∃ j : Fin 7, tile (2*k.val) (459+2*k.val-j.val) ≠ edge7 j := by
    decide +kernel
  obtain ⟨j,h⟩ := check ⟨n%364,by omega⟩
  refine ⟨j,?_⟩
  change tile (2*(n%364)) (459+2*(n%364)-j.val) ≠ edge7 j.val at h
  unfold tile at h ⊢
  have hj := j.isLt
  simpa only [show (2*(n%364))%14 = (2*n)%14 by omega,
    show (459+2*(n%364)-j.val)%728 = (459+2*n-j.val)%728 by omega] using h

private theorem seven_miss_word (R : Nat → Bool) (entry : winW 30 R 95 ∈ cls 30 lock7Codes 6)
    (n : Nat) : ∃ j : Fin 7,
    zrow (Psi R) (95+2*n) (459+2*n-j.val) ≠ edge7 j.val := by
  obtain ⟨j,h⟩ := phase_miss n
  have hj := j.isLt
  have eq := locked_tile R entry (459+2*n-j.val-1) (2*n)
  rw [show 459+2*n-j.val-1+1 = 459+2*n-j.val by omega] at eq
  exact ⟨j,fun e => h (eq.symm.trans e)⟩

private theorem low (x : Nat) :
    Rule30Blocks.F x % 2^8 = Rule30Blocks.F (x%2^8) % 2^8 := by
  simp only [Rule30Blocks.F, Nat.xor_mod_two_pow, Nat.or_mod_two_pow,
    Nat.shiftLeft_eq, Nat.mod_mul_mod, Nat.mod_mod]

private theorem odd_plane (n : Nat) : Rule30Blocks.plane (3+2*n) % 256 = 246 := by
  induction n with
  | zero => decide +kernel
  | succ n ih =>
    change Rule30Blocks.plane (3+2*(n+1)) % 256 = 246
    rw [show 3+2*(n+1) = (3+2*n)+1+1 by omega, Rule30Blocks.plane, Rule30Blocks.plane]
    have inner := low (Rule30Blocks.plane (3+2*n))
    change Rule30Blocks.F _ % 256 = Rule30Blocks.F (_ % 256) % 256 at inner
    rw [ih] at inner
    exact (low (Rule30Blocks.F (Rule30Blocks.plane (3+2*n)))).trans (by
      change Rule30Blocks.F (Rule30Blocks.F (Rule30Blocks.plane (3+2*n)) % 256) % 256 = 246
      rw [inner]
      decide +kernel)

private theorem true_edge (n : Nat) (j : Fin 7) :
    Rule30Jen.cell (459+2*n) ((j.val : Int) - ((459+2*n : Nat) : Int)) =
      edge7 j.val := by
  rw [seed_eq, Rule30Blocks.cell_eq _ _ (by omega)]
  have addr : (((j.val : Int) - ((459+2*n : Nat) : Int)) + ((459+2*n : Nat) : Int)+1).toNat = j.val+1 := by omega
  rw [addr]
  have lowbit := Nat.testBit_mod_two_pow (Rule30Blocks.plane (459+2*n)) 8 (j.val+1)
  have bb : j.val+1 < 8 := by have := j.isLt; omega
  simp [bb] at lowbit
  have p := odd_plane (228+n)
  rw [show 3+2*(228+n)=459+2*n by omega] at p
  have actual : (Rule30Blocks.plane (459+2*n) % 2^8).testBit (j.val+1) = (246 : Nat).testBit (j.val+1) :=
    congrArg (fun z : Nat => z.testBit (j.val+1)) p
  have table : ∀ i : Fin 7, (246 : Nat).testBit (i.val+1) = edge7 i.val := by decide +kernel
  exact lowbit.symm.trans (actual.trans (table j))

/-- The same edge exclusion holds for every right half having this prefix. -/
theorem prefix_misses_seven {R : Nat → Bool}
    (h : ∀ i, i < 80 → R (i+1) = prefix364.testBit i) (n : Nat) : ∃ j : Fin 7,
    zrow (Psi R) (95+2*n) (459+2*n-j.val) ≠
    Rule30Jen.cell (459+2*n) ((j.val : Int) - ((459+2*n : Nat) : Int)) := by
  obtain ⟨j,miss⟩ := seven_miss_word R (prefix_enters_lock7 h) n
  exact ⟨j, by rw [true_edge]; exact miss⟩

/-- Apply the prefix-family statement to the actual singleton right half at 364. -/
theorem seven_miss_singleton (n : Nat) : ∃ j : Fin 7,
    zrow (Psi right364) (95+2*n) (459+2*n-j.val) ≠
    Rule30Jen.cell (459+2*n) ((j.val : Int) - ((459+2*n : Nat) : Int)) :=
  prefix_misses_seven seed_prefix n

/-- At absolute age 991 the first six cells agree, so the bound seven is sharp. -/
theorem six_agree_991 (j : Fin 6) :
    zrow (Psi right364) 627 (991-j.val) = Rule30Jen.cell 991 ((j.val : Int) - 991) := by
  have hj := j.isLt
  let k : Fin 7 := ⟨j.val,by omega⟩
  have eq := locked_tile right364 seed364_enters (991-j.val-1) 532
  rw [show 991-j.val-1+1 = 991-j.val by omega] at eq
  have check : ∀ i : Fin 6, tile 532 (991-i.val) = edge7 i.val := by decide +kernel
  exact eq.trans ((check j).trans (true_edge 266 k).symm)

end Ruliology.CellularAutomata.Rule30LockedSeedEdge
