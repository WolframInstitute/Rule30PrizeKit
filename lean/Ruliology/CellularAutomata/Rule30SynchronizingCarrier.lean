module
public import Ruliology.CellularAutomata.Rule30PeriodicGateTail

/-! A reusable periodic-carrier criterion for all finite inverse histories.
The finite certificate is one synchronizing spatial cycle for each phase.
The phase type need not be numeric. This does not assert the criterion for
arbitrary legal Gate futures. -/
@[expose] public section
namespace Ruliology.CellularAutomata.Rule30SynchronizingCarrier
open Rule30ZeroBoundary Rule30PeriodicGateTail
set_option maxRecDepth 10000
set_option maxHeartbeats 20000000

structure Carrier (Phase : Type) where
  width : Nat
  positive : 0 < width
  row : Phase → Nat → Bool
  prev : Phase → Phase
  row_mod : ∀ p k, row p (k % width) = row p k
  reference : ∀ p k, row (prev p) (k+2) =
    xor (row p (k+1)) (row (prev p) (k+1) || row (prev p) k)
  sync : ∀ p a b, scan (row p) width (a,b) =
    (row (prev p) (width-1), row (prev p) width)

variable {Phase : Type}

theorem row_add_multiple (C : Carrier Phase) (p : Phase) (k j : Nat) :
    C.row p (C.width*j+k) = C.row p k := by
  calc
    C.row p (C.width*j+k) = C.row p ((C.width*j+k)%C.width) :=
      (C.row_mod p _).symm
    _ = C.row p (k%C.width) := by simp
    _ = C.row p k := C.row_mod p k

/-- Alignment costs less than one cycle; one full synchronizing cycle then
fixes both inverse registers. No assumption is made on the finite prefix. -/
theorem back_tail_bound (C : Carrier Phase) (offset : Nat) (p : Phase)
    (y : Nat → Bool) (b : Bool) (N : Nat)
    (hy : ∀ k, N ≤ k → y k = C.row p (k+offset)) :
    ∀ k, N+2*C.width ≤ k → back b y k = C.row (C.prev p) (k+offset) := by
  let Q := (N+offset+1)/C.width
  let r := (N+offset+1)%C.width
  let m := N+C.width-r
  have hr : r<C.width := Nat.mod_lt _ C.positive
  have decomp : C.width*Q+r=N+offset+1 := Nat.div_add_mod _ _
  have ms : m+offset=C.width*Q+(C.width-1) := by dsimp [m];omega
  have hm : N≤m+1 := by dsimp [m];omega
  have driver : ∀ i, i<C.width → y (m+i+1)=C.row p i := by
    intro i hi
    rw [hy _ (by omega)]
    have index : m+i+1+offset=C.width*(Q+1)+i := by
      rw [Nat.mul_add,Nat.mul_one]
      omega
    rw [index]
    exact row_add_multiple C p i (Q+1)
  have eq := scan_congr (fun i => y (m+i+1)) (C.row p) C.width
    (back b y m,back b y (m+1)) driver
  rw [scan_back] at eq
  have synced := eq.trans (C.sync p (back b y m) (back b y (m+1)))
  let M := m+C.width
  have ref0 : C.row (C.prev p) (M+offset)=C.row (C.prev p) (C.width-1) := by
    have index : M+offset=C.width*(Q+1)+(C.width-1) := by
      dsimp [M]
      rw [Nat.mul_add,Nat.mul_one]
      omega
    rw [index]
    exact row_add_multiple C _ _ _
  have ref1 : C.row (C.prev p) (M+1+offset)=C.row (C.prev p) C.width := by
    have index : M+1+offset=C.width*(Q+1)+C.width := by
      dsimp [M]
      rw [Nat.mul_add,Nat.mul_one]
      omega
    rw [index]
    exact row_add_multiple C _ _ _
  have pair : back b y M=C.row (C.prev p) (M+offset) ∧
      back b y (M+1)=C.row (C.prev p) (M+1+offset) :=
    ⟨(congrArg Prod.fst synced).trans ref0.symm,
      (congrArg Prod.snd synced).trans ref1.symm⟩
  have prop : ∀ j, back b y (M+j)=C.row (C.prev p) (M+j+offset) ∧
      back b y (M+j+1)=C.row (C.prev p) (M+j+1+offset) := by
    intro j
    induction j with
    | zero => simpa using pair
    | succ j ih =>
        refine ⟨ih.2,?_⟩
        change xor (y (M+j+1)) (back b y (M+j+1) || back b y (M+j)) =
          C.row (C.prev p) (M+j+2+offset)
        rw [hy _ (by dsimp [M];omega),ih.1,ih.2]
        simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using
          (C.reference p (M+j+offset)).symm
  intro k hk
  have hkm : M≤k := by dsimp [M,m];omega
  simpa only [Nat.add_sub_of_le hkm] using (prop (k-M)).1

def pastPhase (C : Carrier Phase) (p : Phase) : Nat → Phase
  | 0 => p
  | n+1 => C.prev (pastPhase C p n)

theorem history_tail_bound (C : Carrier Phase) (offset : Nat) (p : Phase)
    (y : Nat → Bool) (N : Nat)
    (hy : ∀ k, N≤k → y k=C.row p (k+offset))
    (h : Nat → Bool) (n : Nat) :
    ∀ k, N+2*C.width*n≤k →
      history h n y k=C.row (pastPhase C p n) (k+offset) := by
  induction n with
  | zero => simpa [history,pastPhase] using hy
  | succ n ih =>
      have next := back_tail_bound C offset (pastPhase C p n) (history h n y)
        (h n) (N+2*C.width*n) ih
      simpa [history,pastPhase,Nat.mul_succ,Nat.add_assoc] using next

def gatePhase (C : Carrier Phase) (p : Phase) : Nat → Phase
  | 0 => p
  | n+1 => C.prev (C.prev (gatePhase C p n))

theorem gate_history_tail_bound (C : Carrier Phase) (offset : Nat) (p : Phase)
    (y : Nat → Bool) (N : Nat)
    (hy : ∀ k, N≤k → y k=C.row p (k+offset))
    (h : Nat → Bool) (n : Nat) :
    ∀ k, N+4*C.width*n≤k →
      gateHistory h n y k=C.row (gatePhase C p n) (k+offset) := by
  induction n with
  | zero => simpa [gateHistory,gatePhase] using hy
  | succ n ih =>
      have first := back_tail_bound C offset (gatePhase C p n) (gateHistory h n y)
        true (N+4*C.width*n) ih
      have second := back_tail_bound C offset (C.prev (gatePhase C p n))
        _ (!(h n)) (N+4*C.width*n+2*C.width) first
      have count : N+4*C.width*n+2*C.width+2*C.width=N+4*C.width*(n+1) := by
        rw [Nat.mul_succ]
        omega
      simpa only [gateHistory,gatePhase,count] using second

/-- Any two same-length pasts agree, independently of every chosen head bit. -/
theorem gate_pasts_agree_from (C : Carrier Phase) (offset : Nat) (p : Phase)
    (y : Nat → Bool) (N : Nat)
    (hy : ∀ k, N≤k → y k=C.row p (k+offset))
    (h g : Nat → Bool) (n k : Nat) (hk : N+4*C.width*n≤k) :
    gateHistory h n y k=gateHistory g n y k :=
  (gate_history_tail_bound C offset p y N hy h n k hk).trans
    (gate_history_tail_bound C offset p y N hy g n k hk).symm

/-- A carrier for an actual reconstructed physical trace yields the Gate
closing claim at every past length. Legality is unnecessary for the pasts. -/
theorem reconstructed_gate_pasts_agree_from (C : Carrier Phase)
    (offset : Nat) (p : Phase) (G : Nat → Bool) (N : Nat)
    (hy : ∀ k, N≤k → lam (oddTrace G) k=C.row p (k+offset))
    (h g : Nat → Bool) (n k : Nat) (hk : N+4*C.width*n≤k) :
    lam (oddTrace (gatePrepend h n G)) k=
      lam (oddTrace (gatePrepend g n G)) k := by
  rw [odd_trace_past,odd_trace_past,←gate_history_lam,←gate_history_lam]
  exact gate_pasts_agree_from C offset p _ N hy h g n k hk

/-- The original gap-five construction is an instance of this criterion. -/
def gapFiveCarrier : Carrier Nat where
  width := 155
  positive := by omega
  row := profileRow
  prev := fun p => p+9
  row_mod := by intro p k;simp [profileRow]
  reference := reference_rec
  sync := scan_sync

theorem gap_five_bound_recovered (h g : Nat → Bool) (n k : Nat)
    (hk : 1+620*n≤k) :
    lam (oddTrace (gatePrepend h n gapFiveGate)) k=
      lam (oddTrace (gatePrepend g n gapFiveGate)) k := by
  apply reconstructed_gate_pasts_agree_from gapFiveCarrier 153 0 gapFiveGate 1
    _ h g n k hk
  intro j hj
  rw [←boundary_odd_trace]
  change recon boundary j 0=profileRow 0 (j+153)
  rw [recon_periodic_profile]
  simp [periodicProfile,show j≠0 by omega]

end Ruliology.CellularAutomata.Rule30SynchronizingCarrier
