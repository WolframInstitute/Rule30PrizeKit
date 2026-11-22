module

public import Ruliology.CellularAutomata.Rule30FiniteBlackRuns

@[expose] public section

/-! # Carrying a black run across successive white endpoints

A run of n blacks ending in white at time e sends a white tick to (e+2k,m+2k).
If H(k) ticks build k alternating pairs, the new white tick is preceded by at
least n-H(k)+2k blacks. Repetition gives the finite agreement and period
bounds below. With the kit's nine-tick pair alone, 7j+2 ticks suffice for
a 4j-tick agreement horizon. The loss of seven in a single transfer is sharp.

The two-step motion of the alternating wall and its rectangular agreement
argument are from Renaud Bosdure, Rule30BlackRuns, kit commit 01677a0.
The finite-left step uses the kit's masked Jen theorem. -/

/-! The two-step moving wall and rectangular agreement proofs below adapt
Renaud Bosdure's public Rule30BlackRuns, commit 01677a0, to two arbitrary rows. -/
namespace Ruliology.CellularAutomata.Rule30PulseRelay.EchoGeometry
open Rule30Jen Rule30Realization Rule30FiniteConfigs Rule30FiniteMaskedJen
def WBAt (x : Int → Bool) (t : Nat) (m : Int) (j : Nat) :=
  ∀ i : Nat, 1 ≤ i → i ≤ j →
    evol x t (m + 2 * (i : Int) - 1) = false ∧ evol x t (m + 2 * (i : Int)) = true
variable {x y : Int → Bool}
theorem wbAt_step1 (t : Nat) (m : Int) (j : Nat) (hm : evol x t m = false)
    (h : WBAt x t m (j + 1)) :
    evol x (t + 1) (m + 1) = true ∧
    evol x (t + 1) (m + 2) = true ∧
    WBAt x (t + 1) (m + 2) j := by
  have h1 := h 1 (by omega) (by omega)
  have hm1 : evol x t (m + 1) = false := by
    rw [show m + 1 = m + 2 * ((1 : Nat) : Int) - 1 by omega]; exact h1.1
  have hm2 : evol x t (m + 2) = true := by
    rw [show m + 2 = m + 2 * ((1 : Nat) : Int) by omega]; exact h1.2
  refine ⟨?_, ?_, fun i hi1 hij => ⟨?_, ?_⟩⟩
  · show rule (evol x t (m + 1 - 1)) (evol x t (m + 1)) (evol x t (m + 1 + 1)) = true
    rw [show m + 1 - 1 = m by omega, show m + 1 + 1 = m + 2 by omega, hm, hm1, hm2]
    rfl
  · show rule (evol x t (m + 2 - 1)) (evol x t (m + 2)) (evol x t (m + 2 + 1)) = true
    rw [show m + 2 - 1 = m + 1 by omega, hm1, hm2]
    rfl
  · have hi := h i hi1 (by omega)
    have hi' := h (i + 1) (by omega) (by omega)
    show rule (evol x t (m + 2 + 2 * (i : Int) - 1 - 1))
        (evol x t (m + 2 + 2 * (i : Int) - 1))
        (evol x t (m + 2 + 2 * (i : Int) - 1 + 1)) = false
    rw [show m + 2 + 2 * (i : Int) - 1 - 1 = m + 2 * (i : Int) by omega,
      show m + 2 + 2 * (i : Int) - 1 = m + 2 * ((i + 1 : Nat) : Int) - 1 by omega,
      show m + 2 * ((i + 1 : Nat) : Int) - 1 + 1 = m + 2 * ((i + 1 : Nat) : Int) by omega,
      hi.2, hi'.1, hi'.2]
    rfl
  · have hi' := h (i + 1) (by omega) (by omega)
    show rule (evol x t (m + 2 + 2 * (i : Int) - 1))
        (evol x t (m + 2 + 2 * (i : Int)))
        (evol x t (m + 2 + 2 * (i : Int) + 1)) = true
    rw [show m + 2 + 2 * (i : Int) - 1 = m + 2 * ((i + 1 : Nat) : Int) - 1 by omega,
      show m + 2 + 2 * (i : Int) = m + 2 * ((i + 1 : Nat) : Int) by omega,
      hi'.1, hi'.2]
    rfl

/-- **Two-step self-shielding shift.** If `evol x t m = false` and `WBAt x t m (j + 1)`, then two steps
later at column `m + 2` we have `evol x (t + 2) (m + 2) = false` and `WBAt x (t + 2) (m + 2) j`. -/
theorem wbAt_step2 (t : Nat) (m : Int) (j : Nat) (hm : evol x t m = false)
    (h : WBAt x t m (j + 1)) :
    evol x (t + 2) (m + 2) = false ∧ WBAt x (t + 2) (m + 2) j := by
  obtain ⟨c1, c2, hwb1⟩ := wbAt_step1 t m j hm h
  refine ⟨?_, fun i hi1 hij => ⟨?_, ?_⟩⟩
  · show rule (evol x (t + 1) (m + 2 - 1)) (evol x (t + 1) (m + 2)) (evol x (t + 1) (m + 2 + 1)) = false
    rw [show m + 2 - 1 = m + 1 by omega, c1, c2]
    rfl
  · have hi := hwb1 i hi1 hij
    have hleft : evol x (t + 1) (m + 2 + 2 * (i : Int) - 1 - 1) = true := by
      by_cases hi0 : i = 1
      · subst hi0
        rw [show m + 2 + 2 * ((1 : Nat) : Int) - 1 - 1 = m + 2 by omega]
        exact c2
      · have hprev := hwb1 (i - 1) (by omega) (by omega)
        rw [show m + 2 + 2 * (i : Int) - 1 - 1 = m + 2 + 2 * ((i - 1 : Nat) : Int) by omega]
        exact hprev.2
    show rule (evol x (t + 1) (m + 2 + 2 * (i : Int) - 1 - 1))
        (evol x (t + 1) (m + 2 + 2 * (i : Int) - 1))
        (evol x (t + 1) (m + 2 + 2 * (i : Int) - 1 + 1)) = false
    rw [hleft, hi.1, show m + 2 + 2 * (i : Int) - 1 + 1 = m + 2 + 2 * (i : Int) by omega, hi.2]
    rfl
  · have hi := hwb1 i hi1 hij
    show rule (evol x (t + 1) (m + 2 + 2 * (i : Int) - 1))
        (evol x (t + 1) (m + 2 + 2 * (i : Int)))
        (evol x (t + 1) (m + 2 + 2 * (i : Int) + 1)) = true
    rw [hi.1, hi.2]
    rfl

/-- **Rightmost column of `(white black)^j` stays black for `2 j` steps, then turns white.** -/
theorem wbAt_right_wall : ∀ (j t : Nat) (m : Int), evol x t m = false → WBAt x t m j →
    (∀ s, s < 2 * j → evol x (t + s) (m + 2 * (j : Int)) = true) ∧
    evol x (t + 2 * j) (m + 2 * (j : Int)) = false
  | 0, t, m, hm, _ => ⟨fun _ hs => by omega, by simpa using hm⟩
  | j + 1, t, m, hm, h => by
    obtain ⟨hm2, hwb2⟩ := wbAt_step2 t m j hm h
    obtain ⟨ih_wall, ih_end⟩ := wbAt_right_wall j (t + 2) (m + 2) hm2 hwb2
    have htop0 : evol x t (m + 2 * ((j + 1 : Nat) : Int)) = true :=
      (h (j + 1) (by omega) (by omega)).2
    have htop1 : evol x (t + 1) (m + 2 * ((j + 1 : Nat) : Int)) = true := by
      by_cases hj : j = 0
      · subst hj
        have c2 := (wbAt_step1 t m 0 hm h).2.1
        simpa using c2
      · have hw1 := ((wbAt_step1 t m j hm h).2.2 j (by omega) (by omega)).2
        rwa [show m + 2 + 2 * (j : Int) = m + 2 * ((j + 1 : Nat) : Int) by omega] at hw1
    refine ⟨fun s hs => ?_, ?_⟩
    · rcases s with _ | _ | s'
      · simpa using htop0
      · exact htop1
      · have := ih_wall s' (by omega)
        rwa [show t + 2 + s' = t + (s' + 2) by omega,
          show m + 2 + 2 * (j : Int) = m + 2 * ((j + 1 : Nat) : Int) by omega] at this
    · rwa [show t + 2 + 2 * j = t + 2 * (j + 1) by omega,
        show m + 2 + 2 * (j : Int) = m + 2 * ((j + 1 : Nat) : Int) by omega] at ih_end

/-! #### Box agreement and the `4 j`-step horizon -/

/-- Agreement inside a box `[m + 1, m + W]` whose right boundary `m + W` stays `true` at steps
`< s` and agrees at step `s`. -/
theorem box_agree (t0 t1 : Nat) (m : Int) (W : Nat)
    (hdrv : ∀ s, evol x (t0 + s) m = evol y (t1 + s) m)
    (hinit : ∀ p : Int, m + 1 ≤ p → p ≤ m + (W : Int) → evol x t0 p = evol y t1 p) :
    ∀ s : Nat, (∀ q : Int, q = m + (W : Int) →
      (∀ s', s' < s → evol x (t0 + s') q = true ∧ evol y (t1 + s') q = true) ∧
      evol x (t0 + s) q = evol y (t1 + s) q) →
      ∀ p : Int, m + 1 ≤ p → p ≤ m + (W : Int) → evol x (t0 + s) p = evol y (t1 + s) p
  | 0, _, p, hp1, hp2 => by simpa using hinit p hp1 hp2
  | s + 1, hq, p, hp1, hp2 => by
    by_cases hpW : p = m + (W : Int)
    · exact (hq p hpW).2
    · have ih := box_agree t0 t1 m W hdrv hinit s (fun q hqW =>
        ⟨fun s' hs' => (hq q hqW).1 s' (by omega),
         by
           have hw := (hq q hqW).1 s (by omega)
           rw [hw.1, hw.2]⟩)
      have hleft : evol x (t0 + s) (p - 1) = evol y (t1 + s) (p - 1) := by
        by_cases hpm : p - 1 = m
        · rw [hpm]; exact hdrv s
        · exact ih (p - 1) (by omega) (by omega)
      have hmid : evol x (t0 + s) p = evol y (t1 + s) p := ih p hp1 (by omega)
      have hright : evol x (t0 + s) (p + 1) = evol y (t1 + s) (p + 1) :=
        ih (p + 1) (by omega) (by omega)
      show evol x (t0 + s + 1) p = evol y (t1 + s + 1) p
      show rule (evol x (t0 + s) (p - 1)) (evol x (t0 + s) p) (evol x (t0 + s) (p + 1)) =
        rule (evol y (t1 + s) (p - 1)) (evol y (t1 + s) p) (evol y (t1 + s) (p + 1))
      rw [hleft, hmid, hright]

/-- Shrinking light-cone agreement on `[m + 1, m + W - s']` driven by column `m`. -/
theorem cone_agree_gen (a0 a1 : Nat) (m : Int) (W : Nat)
    (hdrv : ∀ s', evol x (a0 + s') m = evol y (a1 + s') m)
    (hrow : ∀ p : Int, m + 1 ≤ p → p ≤ m + (W : Int) → evol x a0 p = evol y a1 p) :
    ∀ s' : Nat, ∀ p : Int, m + 1 ≤ p → p + s' ≤ m + (W : Int) →
      evol x (a0 + s') p = evol y (a1 + s') p
  | 0, p, hp1, hp2 => by simpa using hrow p hp1 (by omega)
  | s' + 1, p, hp1, hp2 => by
    have ih := cone_agree_gen a0 a1 m W hdrv hrow s'
    have hleft : evol x (a0 + s') (p - 1) = evol y (a1 + s') (p - 1) := by
      by_cases hpm : p - 1 = m
      · rw [hpm]; exact hdrv s'
      · exact ih (p - 1) (by omega) (by omega)
    have hmid := ih p hp1 (by omega)
    have hright := ih (p + 1) (by omega) (by omega)
    show evol x (a0 + s' + 1) p = evol y (a1 + s' + 1) p
    show rule (evol x (a0 + s') (p - 1)) (evol x (a0 + s') p) (evol x (a0 + s') (p + 1)) =
      rule (evol y (a1 + s') (p - 1)) (evol y (a1 + s') p) (evol y (a1 + s') (p + 1))
    rw [hleft, hmid, hright]
end Ruliology.CellularAutomata.Rule30PulseRelay.EchoGeometry

namespace Ruliology.CellularAutomata.Rule30PulseRelay
open Rule30Jen Rule30Realization EchoGeometry

/-- A run of H(k) black ticks forces k alternating pairs at its end. -/
def Builds (H : Nat → Nat) : Prop := ∀ (x : Int → Bool) (m : Int) (k s : Nat),
  (∀ u, u < H k → evol x (s+u) m = true) → WBAt x (s+H k) m k

/-- Consecutive moving walls, with initial width and total width measured in pairs. -/
inductive Chain (H : Nat → Nat) : Nat → Nat → Prop
  | stop (j) : Chain H j j
  | extend {j k total} : H k ≤ 2*j → Chain H k total → Chain H j (j+total)

variable {x y : Int → Bool}

def Box (x y : Int → Bool) (t u : Nat) (m : Int) (w : Nat) : Prop :=
  ∀ p : Int, m+1 ≤ p → p ≤ m+(w:Int) → evol x t p = evol y u p

def DriveEq (x y : Int → Bool) (t u : Nat) (m : Int) : Prop :=
  ∀ n, evol x (t+n) m = evol y (u+n) m

private theorem joinBox {t u w j : Nat} {m : Int} (box : Box x y t u m w)
    (a : WBAt x t (m+(w:Int)) j) (b : WBAt y u (m+(w:Int)) j) :
    Box x y t u m (w+2*j) := by
  intro p lo hi
  by_cases small : p ≤ m+(w:Int)
  · exact box p lo small
  · let e := m+(w:Int)
    have lower : e < p := by dsimp [e];omega
    have upper : p ≤ e+2*(j:Int) := by dsimp [e];omega
    by_cases even : (p-e)%2=0
    · have pos : p=e+2*((((p-e)/2).toNat:Nat):Int) := by omega
      rw [pos,(a _ (by omega) (by omega)).2,(b _ (by omega) (by omega)).2]
    · have pos : p=e+2*((((p-e+1)/2).toNat:Nat):Int)-1 := by omega
      rw [pos,(a _ (by omega) (by omega)).1,(b _ (by omega) (by omega)).1]

private theorem wall {z : Int → Bool} {t w j : Nat} {m : Int}
    (white : evol z t (m+(w:Int)) = false) (band : WBAt z t (m+(w:Int)) j) :
    (∀ s, s < 2*j → evol z (t+s) (m+((w+2*j:Nat):Int)) = true) ∧
    evol z (t+2*j) (m+((w+2*j:Nat):Int)) = false := by
  simpa only [show m+((w+2*j:Nat):Int)=m+(w:Int)+2*(j:Int) by omega]
    using wbAt_right_wall j t (m+(w:Int)) white band

private theorem buildAtEnd {H} (build : Builds H) {n k t : Nat} {m : Int}
    {z : Int → Bool} (enough : H k ≤ n)
    (black : ∀ s, s < n → evol z (t+s) m = true) : WBAt z (t+n) m k := by
  have h := build z m k (t+(n-H k)) (fun a ha => by
    rw [Nat.add_assoc]; exact black _ (by omega))
  rwa [show t+(n-H k)+H k=t+n by omega] at h

theorem wall_stage {j t u w : Nat} {m : Int}
    (d : DriveEq x y t u m) (a : Box x y t u m w)
    (v : evol x t (m+(w:Int))=false) (v' : evol y u (m+(w:Int))=false)
    (b : WBAt x t (m+(w:Int)) j) (b' : WBAt y u (m+(w:Int)) j) :
    ∀ s, s ≤ 2*j → Box x y (t+s) (u+s) m (w+2*j) := by
  intro s hs
  obtain ⟨bx,ex⟩ := wall v b
  obtain ⟨byr,ey⟩ := wall v' b'
  apply box_agree t u m (w+2*j) d (joinBox a b b') s
  intro q eq
  subst q
  refine ⟨fun n hn => ⟨bx n (by omega),byr n (by omega)⟩,?_⟩
  by_cases lt : s < 2*j
  · rw [bx s lt,byr s lt]
  · have e : s=2*j := by omega
    rw [e,ex,ey]

/-- The initial agreed box has w cells; at its right edge there is a white
cell followed by j alternating pairs. Each outgoing wall builds the next one.
The returning light cone traverses the full accumulated width. -/
theorem cascade_agreement {H : Nat → Nat} (build : Builds H) {j total}
    (chain : Chain H j total) (t u : Nat) (m : Int) (w : Nat)
    (drive : DriveEq x y t u m) (box : Box x y t u m w)
    (wx : evol x t (m+(w:Int))=false) (wy : evol y u (m+(w:Int))=false)
    (bx : WBAt x t (m+(w:Int)) j) (by' : WBAt y u (m+(w:Int)) j) :
    ∀ s, s < w+4*total → evol x (t+s) (m+1)=evol y (u+s) (m+1) := by
  induction chain generalizing t u w with
  | stop j =>
    intro s hs
    have init := wall_stage drive box wx wy bx by'
    by_cases early : s < 2*j
    · exact init s (by omega) _ (by omega) (by omega)
    · have z := cone_agree_gen (t+2*j) (u+2*j) m (w+2*j)
          (fun i => by simpa only [Nat.add_assoc] using drive (2*j+i))
          (init _ (by omega)) (s-2*j) (m+1) (by omega) (by omega)
      simpa only [show t+2*j+(s-2*j)=t+s by omega,show u+2*j+(s-2*j)=u+s by omega] using z
  | @extend j k total enough _ ih =>
    intro s hs
    have init := wall_stage drive box wx wy bx by'
    by_cases early : s < 2*j
    · exact init s (by omega) _ (by omega) (by omega)
    · obtain ⟨blackX,whiteX⟩ := wall wx bx
      obtain ⟨blackY,whiteY⟩ := wall wy by'
      have z := ih (t+2*j) (u+2*j) (w+2*j)
          (fun i => by simpa only [Nat.add_assoc] using drive (2*j+i))
          (init _ (by omega)) whiteX whiteY (buildAtEnd build enough blackX)
          (buildAtEnd build enough blackY) (s-2*j) (by omega)
      simpa only [show t+2*j+(s-2*j)=t+s by omega,show u+2*j+(s-2*j)=u+s by omega] using z
end Ruliology.CellularAutomata.Rule30PulseRelay

namespace Ruliology.CellularAutomata.Rule30PulseRelay
open Rule30Jen Rule30Realization EchoGeometry

/-- The n ticks immediately preceding e are black, and the tick at e is white. -/
def Pulse (x : Int → Bool) (e : Nat) (m : Int) (n : Nat) : Prop :=
  n ≤ e ∧ (∀ s, s < n → evol x (e-n+s) m = true) ∧ evol x e m = false

/-- An outgoing white tick carries the unused part of its black run, together
with the black time supplied by the moving wall itself. -/
theorem relay {H} (h : Builds H) {x : Int → Bool} {e n k : Nat} {m : Int}
    (pulse : Pulse x e m n) (pos : 0 < k) (enough : H k ≤ n) :
    WBAt x e m k ∧ Pulse x (e+2*k) (m+2*(k:Int)) (n-H k+2*k) := by
  obtain ⟨ht,black,white⟩ := pulse
  have sliding (i : Nat) (hi : i ≤ n-H k) : WBAt x (e-n+i+H k) m k :=
    h x m k (e-n+i) (fun u hu => by rw [Nat.add_assoc];exact black _ (by omega))
  have endBand := sliding (n-H k) (by omega)
  rw [show e-n+(n-H k)+H k=e by omega] at endBand
  obtain ⟨wallBlack,wallWhite⟩ := wbAt_right_wall k e m white endBand
  refine ⟨endBand,by omega,?_,wallWhite⟩
  intro s hs
  by_cases before : s<n-H k
  · have z := (sliding s (by omega) k pos (by omega)).2
    simpa only [show e+2*k-(n-H k+2*k)+s=e-n+s+H k by omega] using z
  · have z := wallBlack (s-(n-H k)) (by omega)
    simpa only [show e+2*k-(n-H k+2*k)+s=e+(s-(n-H k)) by omega] using z

/-- A sequence of legal relays, indexed by original black duration and total
number of pairs traversed. Every link reuses the unused black ticks. -/
inductive Relays (H : Nat → Nat) : Nat → Nat → Prop
  | done (n) : Relays H n 0
  | step {n k rest} : 0<k → H k≤n → Relays H (n-H k+2*k) rest → Relays H n (k+rest)

variable {x y : Int → Bool}
theorem relay_agreement {H} (h : Builds H) {n total} (chain : Relays H n total)
    (t u : Nat) (m : Int) (w : Nat) (d : DriveEq x y t u m) (b : Box x y t u m w)
    (px : Pulse x t (m+(w:Int)) n) (py : Pulse y u (m+(w:Int)) n) :
    ∀ s, s < w+4*total → evol x (t+s) (m+1) = evol y (u+s) (m+1) := by
  induction chain generalizing t u w with
  | done n =>
    intro s hs
    exact cone_agree_gen t u m w d b s _ (by omega) (by omega)
  | @step n k rest pos enough _ ih =>
    obtain ⟨bandX,nextX⟩ := relay h px pos enough
    obtain ⟨bandY,nextY⟩ := relay h py pos enough
    have nextSite : m+(w:Int)+2*(k:Int)=m+((w+2*k:Nat):Int) := by omega
    rw [nextSite] at nextX nextY
    have init := wall_stage d b px.2.2 py.2.2 bandX bandY
    intro s hs
    by_cases early : s < 2*k
    · exact init s (by omega) _ (by omega) (by omega)
    · have z := ih (t+2*k) (u+2*k) (w+2*k)
          (fun i => by simpa only [Nat.add_assoc] using d (2*k+i))
          (init _ (by omega)) nextX nextY (s-2*k) (by omega)
      simpa only [show t+2*k+(s-2*k)=t+s by omega,show u+2*k+(s-2*k)=u+s by omega] using z

/-- Using only the kit's nine-tick pair, seven ticks pay for each further pair. -/
theorem seven {H : Nat → Nat} (one : H 1 = 9) (j n : Nat) (enough : 7*j+2 ≤ n) : Relays H n j := by
  induction j generalizing n with
  | zero => exact .done _
  | succ j ih =>
    have next := ih (n-H 1+2*1) (by rw [one];omega)
    simpa only [Nat.add_comm 1 j] using (Relays.step (k:=1) (by decide) (by rw [one];omega) next)

theorem nineBuilds : Builds (fun k => 9*k) := fun x m k s h => Rule30FiniteBlackRuns.black_shield x m k s h
end Ruliology.CellularAutomata.Rule30PulseRelay

namespace Ruliology.CellularAutomata.Rule30PulseRelay
open Rule30Jen Rule30Realization Rule30FiniteConfigs Rule30FiniteMaskedJen EchoGeometry
variable {x : Int → Bool} {lo : Int}
local notation "col" => (fun (t : Nat) => evol x t 0)
theorem black_zero (H : Nat → Nat) (hshield : Builds H) (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false) (T P r t1 : Nat) (hper : ∀ t, T ≤ t → col (t + P) = col t)
    (ht1 : T ≤ t1) (hrP : r < P)
    (hrun : ∀ s, s < r → col (t1 + s) = true)
    (hw0 : col (t1 + r) = false)
    (j : Nat) (chain : Relays H r j) (span : P-r ≤ 4*j) : False := by
  have hP : 0 < P := by omega
  have hperk : ∀ k t, T ≤ t → col (t + k * P) = col t := periodic_mul (f := fun t => evol x t 0) hper
  have hblack : ∀ k s, s < r → evol x (t1 + k * P + s) 0 = true := by
    intro k s hs
    have := hperk k (t1 + s) (by omega)
    show col (t1 + k * P + s) = true
    rw [show t1 + k * P + s = t1 + s + k * P by omega, this]
    exact hrun s hs
  have hwhite0 : ∀ k, evol x (t1 + r + k * P) 0 = false := by
    intro k
    have := hperk k (t1 + r) (by omega)
    show col (t1 + r + k * P) = false
    rw [this]; exact hw0
  have pulse (k : Nat) : Pulse x (t1+r+k*P) 0 r := by
    refine ⟨by omega,?_,hwhite0 k⟩
    intro a ha
    rw [show t1+r+k*P-r+a=t1+k*P+a by omega]
    exact hblack k a ha
  have hdrv : ∀ k s, evol x (t1 + r + s) 0 = evol x (t1 + r + k * P + s) 0 := by
    intro k s
    have := hperk k (t1 + r + s) (by omega)
    show col (t1 + r + s) = col (t1 + r + k * P + s)
    rw [show t1 + r + k * P + s = t1 + r + s + k * P by omega, this]
  -- Column 1 agrees at every white time of the period.
  have hcol_masked : ∀ k s, s < P → evol x (t1 + r + k * P + s) 0 = false →
      evol x (t1 + r + s) 1 = evol x (t1 + r + k * P + s) 1 := by
    intro k s hs hcw
    by_cases hsPr : s < P - r
    · exact relay_agreement hshield chain (t1+r) (t1+r+k*P) 0 0 (hdrv k)
        (fun p a b => by omega) (by simpa using pulse 0) (pulse k) s (by omega)
    · -- For `P - r ≤ s < P`, `t1 + r + k * P + s` lies inside the `(k + 1)`-th black run.
      have hPk : (k + 1) * P = k * P + P := Nat.succ_mul k P
      have hb := hblack (k + 1) (s - (P - r)) (by omega)
      rw [hPk, show t1 + (k * P + P) + (s - (P - r)) = t1 + r + k * P + s by omega] at hb
      rw [hb] at hcw
      exact absurd hcw (by decide)
  -- Conclude by Masked Jen (`Rule30FiniteMaskedJen.masked_jen`) from time `t1 + r`.
  refine Rule30FiniteMaskedJen.masked_jen hlo hzero 0 (T := t1 + r) (P := P) hP (fun t ht => hper t (by omega)) (fun t ht hcw => ?_)
  rw [show (0 : Int) + 1 = 1 by rfl]
  have hdm := Nat.div_add_mod (t - (t1 + r)) P
  generalize (t - (t1 + r)) / P = q at hdm
  have hmod := Nat.mod_lt (t - (t1 + r)) hP
  generalize (t - (t1 + r)) % P = s at hdm hmod
  have hq1 : (q + 1) * P = q * P + P := Nat.succ_mul q P
  have hcomm : P * q = q * P := Nat.mul_comm P q
  have hcw_q : evol x (t1 + r + q * P + s) 0 = false := by
    rwa [show t1 + r + q * P + s = t by omega]
  have hcw_q1 : evol x (t1 + r + (q + 1) * P + s) 0 = false := by
    rw [hq1, show t1 + r + (q * P + P) + s = t + P by omega]
    have hp0 : evol x (t + P) 0 = evol x t 0 := hper t (by omega)
    rw [hp0, hcw]
  have e1 := hcol_masked q s hmod hcw_q
  have e2 := hcol_masked (q + 1) s hmod hcw_q1
  rw [hq1] at e2
  rw [show t + P = t1 + r + (q * P + P) + s by omega, ← e2, e1,
    show t1 + r + q * P + s = t by omega]

theorem white_zero (H : Nat → Nat) (hshield : Builds H) (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false) (T P s r t1 : Nat)
    (hper : ∀ t, T ≤ t → col (t + P) = col t)
    (ht1 : T ≤ t1) (hs : 9 ≤ s) (hsr : s + r < P)
    (hblk : ∀ i, i < s → col (t1 + i) = true)
    (hwht : ∀ i, i < r → col (t1 + s + i) = false)
    (hnextb : col (t1 + s + r) = true)
    (hr : 0<r) (j : Nat) (chain : Relays H r j) (span : P-s-r ≤ 4*j+2) : False := by
  have hP : 0 < P := by omega
  have hperk : ∀ k t, T ≤ t → col (t + k * P) = col t := periodic_mul (f := fun t => evol x t 0) hper
  have hMul : ∀ k, (k + 1) * P = k * P + P := fun k => Nat.succ_mul k P
  have cblk : ∀ k i, i < s → evol x (t1 + k * P + i) 0 = true := by
    intro k i hi
    have := hperk k (t1 + i) (by omega)
    show col (t1 + k * P + i) = true
    rw [show t1 + k * P + i = t1 + i + k * P by omega, this]; exact hblk i hi
  have cwht : ∀ k i, i < r → evol x (t1 + s + k * P + i) 0 = false := by
    intro k i hi
    have := hperk k (t1 + s + i) (by omega)
    show col (t1 + s + k * P + i) = false
    rw [show t1 + s + k * P + i = t1 + s + i + k * P by omega, this]; exact hwht i hi
  have cnextb : ∀ k, evol x (t1 + s + r + k * P) 0 = true := by
    intro k
    have := hperk k (t1 + s + r) (by omega)
    show col (t1 + s + r + k * P) = true
    rw [this]; exact hnextb
  -- Start of the white run of period k: column 1 white, column 2 black (Lemma A).
  have hstart : ∀ k, evol x (t1 + s + k * P) 1 = false ∧ evol x (t1 + s + k * P) 2 = true := by
    intro k
    have := Rule30FiniteBlackRuns.nine_black x (t1 + k * P + (s - 9)) 0 (fun i hi => by
      have := cblk k (s - 9 + i) (by omega)
      rwa [show t1 + k * P + (s - 9 + i) = t1 + k * P + (s - 9) + i by omega] at this)
    rw [show t1 + k * P + (s - 9) + 9 = t1 + s + k * P by omega] at this
    simpa using this
  -- Column 1 is black during the rest of the white run (steps 1..r).
  have hrun1 : ∀ k i, 1 ≤ i → i ≤ r → evol x (t1 + s + k * P + i) 1 = true := by
    intro k i hi1 hir
    have c1 : evol x (t1 + s + k * P + 1) 1 = true := by
      show rule (evol x (t1 + s + k * P) (1 - 1)) (evol x (t1 + s + k * P) 1)
        (evol x (t1 + s + k * P) (1 + 1)) = true
      have h0 := cwht k 0 (by omega)
      rw [show t1 + s + k * P + 0 = t1 + s + k * P by omega] at h0
      rw [show (1 : Int) - 1 = 0 by rfl, show (1 : Int) + 1 = 2 by rfl, h0, (hstart k).1,
        (hstart k).2]
      rfl
    have := Rule30FiniteBlackRuns.black_stays x 0 (t1 + s + k * P + 1) (r - 1) (fun i' hi' => by
      have := cwht k (1 + i') (by omega)
      rwa [show t1 + s + k * P + (1 + i') = t1 + s + k * P + 1 + i' by omega] at this) c1
      (i - 1) (by omega)
    rwa [show t1 + s + k * P + 1 + (i - 1) = t1 + s + k * P + i by omega] at this
  have hend1_col1 : ∀ k, evol x (t1 + s + r + k * P + 1) 1 = false := by
    intro k
    have hc1 : evol x (t1 + s + r + k * P) 1 = true := by
      have := hrun1 k r (by omega) (Nat.le_refl r)
      rwa [show t1 + s + k * P + r = t1 + s + r + k * P by omega] at this
    show rule (evol x (t1 + s + r + k * P) (1 - 1)) (evol x (t1 + s + r + k * P) 1)
      (evol x (t1 + s + r + k * P) (1 + 1)) = false
    rw [show (1 : Int) - 1 = 0 by rfl, cnextb k, hc1]
    rfl
  have pulse (k : Nat) : Pulse x (t1+s+r+k*P+1) 1 r := by
    refine ⟨by omega,?_,hend1_col1 k⟩
    intro a ha
    have z := hrun1 k (a+1) (by omega) (by omega)
    rwa [show t1+s+k*P+(a+1)=t1+s+r+k*P+1-r+a by omega] at z
  have hdrv : ∀ k s', evol x (t1 + s + r + 1 + s') 0 = evol x (t1 + s + r + k * P + 1 + s') 0 := by
    intro k s'
    have := hperk k (t1 + s + r + 1 + s') (by omega)
    show col (t1 + s + r + 1 + s') = col (t1 + s + r + k * P + 1 + s')
    rw [show t1 + s + r + k * P + 1 + s' = t1 + s + r + 1 + s' + k * P by omega, this]
  have hrem_agree : ∀ k s', s' < 4*j+1 →
      evol x (t1+s+r+1+s') 1 = evol x (t1+s+r+k*P+1+s') 1 := by
    intro k a ha
    apply relay_agreement hshield chain (t1+s+r+1) (t1+s+r+k*P+1) 0 1 (hdrv k) _ _ _ a (by omega)
    · intro p low high
      have one : p=1 := by omega
      subst p
      have z := hend1_col1 0
      simp only [Nat.zero_mul,Nat.add_zero] at z
      rw [z,hend1_col1 k]
    · simpa using pulse 0
    · exact pulse k
  -- Column 1 agrees at every white time of the period starting at `t1 + s`.
  have hcol_masked : ∀ k i, i < P → evol x (t1 + s + k * P + i) 0 = false →
      evol x (t1 + s + i) 1 = evol x (t1 + s + k * P + i) 1 := by
    intro k i hi hcw
    by_cases hi0 : i = 0
    · subst hi0
      have a := (hstart 0).1
      simp only [Nat.zero_mul, Nat.add_zero] at a
      simp only [Nat.add_zero]
      rw [a, (hstart k).1]
    by_cases hir : i ≤ r
    · have a := hrun1 0 i (by omega) hir
      simp only [Nat.zero_mul, Nat.add_zero] at a
      rw [a, hrun1 k i (by omega) hir]
    by_cases hi_r : i = r
    · omega
    by_cases hic : i < P - s
    · have := hrem_agree k (i - r - 1) (by omega)
      rwa [show t1 + s + r + 1 + (i - r - 1) = t1 + s + i by omega,
        show t1 + s + r + k * P + 1 + (i - r - 1) = t1 + s + k * P + i by omega] at this
    · -- For `P - s ≤ i < P`, `t1 + s + k * P + i` lies inside the `(k + 1)`-th black run.
      have hb := cblk (k + 1) (i - (P - s)) (by omega)
      rw [hMul k, show t1 + (k * P + P) + (i - (P - s)) = t1 + s + k * P + i by omega] at hb
      rw [hb] at hcw
      exact absurd hcw (by decide)
  -- Conclude by Masked Jen (`Rule30FiniteMaskedJen.masked_jen`) from time `t1 + s`.
  refine Rule30FiniteMaskedJen.masked_jen hlo hzero 0 (T := t1 + s) (P := P) hP (fun t ht => hper t (by omega)) (fun t ht hcw => ?_)
  rw [show (0 : Int) + 1 = 1 by rfl]
  have hdm := Nat.div_add_mod (t - (t1 + s)) P
  generalize (t - (t1 + s)) / P = q at hdm
  have hmod := Nat.mod_lt (t - (t1 + s)) hP
  generalize (t - (t1 + s)) % P = i at hdm hmod
  have hq1 : (q + 1) * P = q * P + P := Nat.succ_mul q P
  have hcomm : P * q = q * P := Nat.mul_comm P q
  have hcw_q : evol x (t1 + s + q * P + i) 0 = false := by
    rwa [show t1 + s + q * P + i = t by omega]
  have hcw_q1 : evol x (t1 + s + (q + 1) * P + i) 0 = false := by
    rw [hq1, show t1 + s + (q * P + P) + i = t + P by omega]
    have hp0 : evol x (t + P) 0 = evol x t 0 := hper t (by omega)
    rw [hp0, hcw]
  have e1 := hcol_masked q i hmod hcw_q
  have e2 := hcol_masked (q + 1) i hmod hcw_q1
  rw [hq1] at e2
  rw [show t + P = t1 + s + (q * P + P) + i by omega, ← e2, e1,
    show t1 + s + q * P + i = t by omega]

private theorem leftmost_shift (m : Int) (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false) :
    shiftConfig x m (lo-m) = true ∧ ∀ p, p < lo-m → shiftConfig x m p = false := by
  constructor
  · simpa only [shiftConfig, Int.sub_add_cancel] using hlo
  · intro p hp
    exact hzero (p+m) (by omega)

/-- No periodic column on a row with a leftmost black cell can contain this black run and following white. -/
theorem black_period (H : Nat → Nat) (shield : Builds H) (m : Int) (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false)
    (T P r t : Nat) (per : ∀ n, T ≤ n → evol x (n+P) m = evol x n m) (ht : T ≤ t)
    (hr : r < P) (run : ∀ s, s < r → evol x (t+s) m = true)
    (white : evol x (t+r) m = false) (j : Nat) (chain : Relays H r j) (span : P-r ≤ 4*j) : False := by
  obtain ⟨left,below⟩ := leftmost_shift m hlo hzero
  apply black_zero H shield left below T P r t _ ht hr _ _ j chain span
  · simpa only [evol_shiftConfig, Int.zero_add] using per
  · simpa only [evol_shiftConfig, Int.zero_add] using run
  · simpa only [evol_shiftConfig, Int.zero_add] using white

/-- The second exclusion applies when at least nine blacks precede the white run, with another black after it. -/
theorem white_period (H : Nat → Nat) (shield : Builds H) (m : Int) (hlo : x lo = true) (hzero : ∀ p, p < lo → x p = false)
    (T P s r t : Nat) (per : ∀ n, T ≤ n → evol x (n+P) m = evol x n m)
    (ht : T ≤ t) (hs : 9 ≤ s) (hsr : s+r < P)
    (black : ∀ a, a < s → evol x (t+a) m = true)
    (white : ∀ a, a < r → evol x (t+s+a) m = false)
    (nextBlack : evol x (t+s+r) m = true)
    (hr : 0<r) (j : Nat) (chain : Relays H r j) (span : P-s-r ≤ 4*j+2) : False := by
  obtain ⟨left,below⟩ := leftmost_shift m hlo hzero
  apply white_zero H shield left below T P s r t _ ht hs hsr _ _ _ hr j chain span
  · simpa only [evol_shiftConfig, Int.zero_add] using per
  · simpa only [evol_shiftConfig, Int.zero_add] using black
  · simpa only [evol_shiftConfig, Int.zero_add] using white
  · simpa only [evol_shiftConfig, Int.zero_add] using nextBlack


end Ruliology.CellularAutomata.Rule30PulseRelay

namespace Ruliology.CellularAutomata.Rule30PulseRelay
open Rule30Jen Rule30Realization

/-- Repeating any finite building block consumes H(k)-2k ticks per use,
with a fixed 2k-tick end correction. -/
theorem repeat_block {H : Nat → Nat} (k q n : Nat) (pos : 0<k) (cost : 2*k≤H k)
    (enough : (H k-2*k)*q+2*k≤n) : Relays H n (k*q) := by
  induction q generalizing n with
  | zero => simpa using (Relays.done (H:=H) n)
  | succ q ih =>
    rw [Nat.mul_succ] at enough
    have tail := ih (n-H k+2*k) (by omega)
    simpa only [Nat.mul_succ,Nat.add_comm k (k*q)] using
      (Relays.step (k:=k) pos (by omega) tail)

/-- A concrete ordinary right half realizes the exact loss of seven ticks
at this first relay for every initial black-run length of at least nine. -/
theorem exact_first_relay (n : Nat) (hn : 9≤n) :
    ∃ x : Int → Bool, Pulse x n 0 n ∧ Pulse x (n+2) 2 (n-7) ∧ evol x 8 2=false := by
  let rhs := fun p : Int => (19:Nat).testBit (p-1).toNat
  let c := fun t : Nat => decide (t<n)
  let x := conf rhs c
  have pulse : Pulse x n 0 n := by
    refine ⟨by omega,?_,?_⟩
    · intro s hs; simp only [Nat.sub_self,Nat.zero_add,x,(realize rhs c).2,c,decide_eq_true_eq];exact hs
    · simp only [x,(realize rhs c).2,c,Nat.lt_irrefl,decide_false]
  have moved := (relay nineBuilds pulse (k:=1) (by decide) (by omega)).2
  refine ⟨x,pulse,?_,?_⟩
  · rw [show n-9*1+2*1=n-7 by omega] at moved; simpa using moved
  · rw [show x=conf rhs c by rfl,evol_conf,ite_eq_left (by decide : (1:Int)≤2)]
    have eq := rh_congr rhs (c:=c) (c':=fun _ => true) 8 (fun t ht => by
      simp only [c,decide_eq_true_eq]; omega) 2
    rw [eq]
    exact (by decide +kernel : rh (fun p : Int => (19:Nat).testBit (p-1).toNat) (fun _ => true) 8 2 = false)

/-- In particular 7P+29 ≤ 11r excludes a black run of r ticks followed by white
in an eventual period P at any site of any row with a leftmost black cell. -/
theorem black_fraction {x : Int→Bool} {lo : Int} (m : Int)
    (left : x lo=true) (below : ∀ i, i<lo → x i=false)
    (T P r t : Nat) (per : ∀ n, T≤n → evol x (n+P) m=evol x n m)
    (ht : T≤t) (hr : r<P) (run : ∀ a, a<r → evol x (t+a) m=true)
    (white : evol x (t+r) m=false) (bound : 7*P+29≤11*r) : False := by
  let j := (P-r+3)/4
  exact black_period _ nineBuilds m left below T P r t per ht hr run white j
    (seven rfl j r (by dsimp [j];omega)) (by dsimp [j];omega)

theorem white_fraction {x : Int→Bool} {lo : Int} (m : Int)
    (left : x lo=true) (below : ∀ i, i<lo → x i=false)
    (T P s r t : Nat) (per : ∀ n, T≤n → evol x (n+P) m=evol x n m)
    (ht : T≤t) (hs : 9≤s) (fit : s+r<P)
    (blk : ∀ a, a<s → evol x (t+a) m=true)
    (wht : ∀ a, a<r → evol x (t+s+a) m=false) (last : evol x (t+s+r) m=true)
    (bound : 7*(P-s)+15≤11*r) : False := by
  let j := (P-s-r+1)/4
  exact white_period _ nineBuilds m left below T P s r t per ht hs fit blk wht last
    (by omega) j (seven rfl j r (by dsimp [j];omega)) (by dsimp [j];omega)
end Ruliology.CellularAutomata.Rule30PulseRelay

namespace Ruliology.CellularAutomata.Rule30PulseRelay
open Rule30Jen Rule30Realization

private theorem right_until {a b : Int → Bool} {N : Nat}
    (initial : ∀p, 1≤p → a p=b p) (drive : ∀t, t<N → evol a t 0=evol b t 0) :
    ∀ t, t≤N → ∀p, 1≤p → evol a t p=evol b t p := by
  intro t
  induction t with
  | zero => intro _ p hp;exact initial p hp
  | succ t ih =>
    intro ht p hp
    have left : evol a t (p-1)=evol b t (p-1) := by
      by_cases one : p=1
      · subst p;exact drive t (by omega)
      · exact ih (by omega) _ (by omega)
    simp only [evol,left,ih (by omega) p hp,ih (by omega) (p+1) (by omega)]

/-- Only the finite common drive up to the observation is needed. Two different
ordinary rows and different initial ages are allowed. -/
theorem finite_relay {H} (build : Builds H) {n j} (chain : Relays H n j)
    {x y : Int → Bool} {t u L : Nat} (px : Pulse x t 0 n) (py : Pulse y u 0 n)
    (same : ∀ a, a<L → evol x (t+a) 0=evol y (u+a) 0) :
    ∀ a, a<L → a<4*j → evol x (t+a) 1=evol y (u+a) 1 := by
  let c := fun k => if k<u then evol y k 0 else evol x (t+(k-u)) 0
  let z := conf y c
  have cz (k : Nat) : evol z k 0=c k := (realize y c).2 k
  have synced : DriveEq x z t u 0 := by
    intro a; rw [cz];simp [c, show ¬u+a<u by omega]
  have reproduces : ∀ k, k<u+L → evol y k 0=evol z k 0 := by
    intro k hk;rw [cz];dsimp [c]
    split
    · rfl
    · rename_i late
      have q := same (k-u) (by omega)
      rw [show u+(k-u)=k by omega] at q
      exact q.symm
  have pz : Pulse z u 0 n := by
    refine ⟨py.1,?_,?_⟩
    · intro a ha; rw [cz]; simp only [c,ite_eq_left (show u-n+a<u by have := py.1;omega)]
      exact py.2.1 a ha
    · rw [cz];simp [c,px.2.2]
  have carry := relay_agreement build chain t u 0 0 synced (fun p hp hq => by omega) px pz
  intro a ha bound
  have back := right_until (a:=y) (b:=z) (fun p hp=>((realize y c).1 p hp).symm) reproduces (u+a) (by omega) 1 (by decide)
  exact (carry a (by omega)).trans back.symm
/-- Every black run of length at least nine ending in white relays at least n−7 black
ticks to the second site to its right, immediately before the white tick at e+2. -/
theorem one_pair {x : Int → Bool} {e n : Nat} {m : Int}
    (hn : 9 ≤ n) (pulse : Pulse x e m n) : Pulse x (e+2) (m+2) (n-7) := by
  have moved := (relay nineBuilds (k := 1) pulse (by decide) hn).2
  change Pulse x (e+2) (m+2) (n-9+2) at moved
  rwa [show n-9+2=n-7 by omega] at moved
end Ruliology.CellularAutomata.Rule30PulseRelay
