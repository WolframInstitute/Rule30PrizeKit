module
public import Ruliology.CellularAutomata.Rule30SynchronizingCarrier

/-! Arbitrary finite pasts of the periodic gap-three/five Gate future.
The actual reconstruction includes a39-state transient before a325-column
carrier. The conclusion quantifies every past length and every past bit,
but concerns this one periodic future, not all legal Gate futures. -/
@[expose] public section
namespace Ruliology.CellularAutomata.Rule30PeriodicThreeFive
open Rule30ZeroBoundary Rule30PeriodicGateTail
set_option maxRecDepth 30000
set_option maxHeartbeats 100000000

def packedCycle : Nat := 0xde1f6bc548798fa90a8c88e7ce3a63d2bd439472e71805eee54bb64a9a6ceb340dd6e15b3c68d74f918a9e88c0ce7e632bbdc8294f896aec3237d3d558196fc1a579390c91f7e150411f41c0617fb10199feed54a6443a76835bf992ae9220db3e6daba1cabc4cd760903c9fd6c1937e9d00c1fe7c2b57c8154fd96569b90d29e62dba368324f9840ee6f4b3509d1ce9c6097beca8378fd2e01cbfc89570e450a718b5ccd9765153619da115b116d99a4cc37778050ff1f55c0497f7915ade426a7b0b0dedf5b426a7c4c5440466c73365dd3141dc7d97569190de9e6acb4b724d0261f3bc1987eefaa0123ee38ba2f232a29b23ed32a1983cee874bfa48526f1335d9d16e9caa17339122de226a33a39839ef8eaaf4b204d3f6595b6e424a784b2e6dcbb40987cef0601fbeeaab48c88e0f8bcac8626fbb352dd1211dbcc6d77a1503d9f8692faccab708d0ce9f63153d11d59d96d69a64c3a47836af9b2ae8b20fd3e0583f6fd5a0913f1c8017ff10559f44ca77725a539259936ed9aa6eb34ad24b586d6e35a3d6bd1ad4c34778750f19f5e924acc7374525658436e7da3543d97811afc121713e59844df876a8502c5eb66bd30a9dec9434c7d6701b5fc240787fae0023ffbd00d4ff47aa70225f3b158dc5f576065af0435e79430e7df45450479c71161e13ea1d0b14ed97b4daa768c54e458b668830cfde6543b97d29a92d89b6ecd0375ed06b1f08d5ef64b547240527c5b566d93091de114b9972cc0277f3a51824efb7a0da3f528063ff0201e2feb30498f8efa8a28cbce6d4bb462a732c5db441d67c5b5769904e9f8ac18b7ecd0061febcab8722fa38282ece2b8b3209a28ec3ca0263c2b863afb2ca9808eecea3633d3d29d58916ecda376bd50d59e1693dacd6b710d0
def packedPrefix : Nat := 0xde1f6bc1487e4faa6123be39802efe20033efdab14c8e74f456505b9c69164e130a1dcb146d97b4c0277f851ae5e236abda3d53a962c9a20c33c7986aefb8a02e3f8b82e2fcb20083fcf8061ffbe0000

def row (p k : Nat) : Bool := Nat.testBit (packedCycle >>> (16*(k%325))) (p%16)
def boundary (t : Nat) : Bool := Nat.testBit 65470 (t%16)

theorem row_phase_mod (p : Nat) : row (p%16)=row p := by
  funext k
  simp only [row,Nat.mod_mod]

theorem row_phase_add_mod (p q : Nat) : row (p%16+q)=row (p+q) := by
  funext k
  unfold row
  have index : (p%16+q)%16=(p+q)%16 := by omega
  rw [index]

theorem row_phase_sixteen (p : Nat) : row (p+16)=row p := by
  funext k
  unfold row
  have index : (p+16)%16=p%16 := by omega
  rw [index]

private theorem reference_certificate : ∀p:Fin 16,∀k:Fin 325,
    row p.val (k.val+2)=xor (row (p.val+1) (k.val+1))
      (row p.val (k.val+1) || row p.val k.val) := by decide +kernel

private theorem sync_certificate : ∀p:Fin 16,∀a b:Bool,
    scan (row p.val) 325 (a,b)=(row (p.val+15) 324,row (p.val+15) 325) :=
  by decide +kernel

theorem row_step (p k : Nat) :
    row p (k+2)=xor (row (p+1) (k+1)) (row p (k+1) || row p k) := by
  have h := reference_certificate ⟨p%16,by omega⟩ ⟨k%325,by omega⟩
  simpa [row,Nat.add_mod] using h

theorem row_reference (p k : Nat) :
    row (p+15) (k+2)=xor (row p (k+1)) (row (p+15) (k+1) || row (p+15) k) := by
  have h := row_step (p+15) k
  rw [show p+15+1=p+16 by omega,row_phase_sixteen] at h
  exact h

theorem row_sync (p : Nat) (a b : Bool) :
    scan (row p) 325 (a,b)=(row (p+15) 324,row (p+15) 325) := by
  have h := sync_certificate ⟨p%16,by omega⟩ a b
  rw [row_phase_mod,row_phase_add_mod] at h
  exact h

def carrier : Rule30SynchronizingCarrier.Carrier Nat where
  width := 325
  positive := by omega
  row := row
  prev := fun p => p+15
  row_mod := by intro p k;simp [row]
  reference := row_reference
  sync := row_sync

def fullRow (k t : Nat) : Bool :=
  if k<40 then Nat.testBit (packedPrefix >>> (16*k)) (t%16)
  else row t (k+285)

private theorem initial_certificate : ∀t:Fin 16,
    fullRow 0 t.val=false ∧ fullRow 1 t.val=boundary t.val := by decide +kernel

private theorem transient_certificate : ∀k:Fin 40,∀t:Fin 16,
    fullRow (k.val+2) t.val=xor (fullRow (k.val+1) (t.val+1))
      (fullRow (k.val+1) t.val || fullRow k.val t.val) := by decide +kernel

theorem full_initial (t : Nat) : fullRow 0 t=false ∧ fullRow 1 t=boundary t := by
  have h := initial_certificate ⟨t%16,by omega⟩
  simpa [fullRow,boundary] using h

theorem full_step (k t : Nat) :
    fullRow (k+2) t=xor (fullRow (k+1) (t+1)) (fullRow (k+1) t || fullRow k t) := by
  by_cases small : k<40
  · have h := transient_certificate ⟨k,small⟩ ⟨t%16,by omega⟩
    simpa [fullRow,row,Nat.add_mod] using h
  · have k0 : ¬k<40 := small
    have k1 : ¬k+1<40 := by omega
    have k2 : ¬k+2<40 := by omega
    simp only [fullRow,ite_eq_right k0,ite_eq_right k1,ite_eq_right k2]
    simpa only [Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using row_step t (k+285)

/-- The complete transient-plus-cycle table is the official reconstructed
space-time diagram, not merely an abstract periodic carrier. -/
theorem recon_full (k t : Nat) : recon boundary k t=fullRow k t := by
  have key : ∀n,∀s,recon boundary n s=fullRow n s ∧
      recon boundary (n+1) s=fullRow (n+1) s := by
    intro n
    induction n with
    | zero =>
        intro s
        exact ⟨(full_initial s).1.symm,(full_initial s).2.symm⟩
    | succ n ih =>
        intro s
        refine ⟨(ih s).2,?_⟩
        rw [recon,(ih (s+1)).2,(ih s).1,(ih s).2]
        exact (full_step n s).symm
  exact (key k t).1

theorem lam_tail : ∀k,40≤k → lam boundary k=row 0 (k+285) := by
  intro k hk
  change recon boundary k 0=row 0 (k+285)
  rw [recon_full]
  simp only [fullRow,ite_eq_right (show ¬k<40 by omega)]

def gapThreeFiveGate (r : Nat) : Bool := decide (r%8=0 ∨ r%8=3)

def gateWindow (r : Nat) : Nat :=
  (List.range 8).foldl (fun v i => v+(if gapThreeFiveGate (r+i) then 2^i else 0)) 0

theorem gate_legal_eight_windows (r : Nat) :
    gateWindow r ∈ ([8,9,16,18,33,36,66,72,132,144] : List Nat) := by
  have cert : ∀i:Fin 8,gateWindow i.val ∈
      ([8,9,16,18,33,36,66,72,132,144] : List Nat) := by decide +kernel
  have bits : ∀i,gapThreeFiveGate (r%8+i)=gapThreeFiveGate (r+i) := by
    intro i
    simp [gapThreeFiveGate,Nat.add_mod]
  have eqwin : gateWindow (r%8)=gateWindow r := by simp only [gateWindow,bits]
  have h := cert ⟨r%8,by omega⟩
  simpa only [eqwin] using h

theorem boundary_odd_trace : boundary=oddTrace gapThreeFiveGate := by
  funext t
  have cert : ∀r:Fin 16,boundary r.val=oddTrace gapThreeFiveGate r.val := by decide +kernel
  have hp : (t%16)%2=t%2 := by omega
  have hd : (t%16)/2=(t/2)%8 := by omega
  have h := cert ⟨t%16,by omega⟩
  simpa [boundary,oddTrace,gapThreeFiveGate,hp,hd] using h

/-- A second periodic future has all-length past closing, with its actual
39-state transient retained. Past bits need not be admissible. -/
theorem arbitrary_gate_pasts_agree_from (h g : Nat → Bool) (n k : Nat)
    (hk : 40+1300*n≤k) :
    lam (oddTrace (gatePrepend h n gapThreeFiveGate)) k=
      lam (oddTrace (gatePrepend g n gapThreeFiveGate)) k := by
  apply Rule30SynchronizingCarrier.reconstructed_gate_pasts_agree_from
    carrier 285 0 gapThreeFiveGate 40 _ h g n k hk
  rw [←boundary_odd_trace]
  exact lam_tail

theorem arbitrary_gate_pasts_agree (h g : Nat → Bool) (n : Nat) :
    EventuallyEq (lam (oddTrace (gatePrepend h n gapThreeFiveGate)))
      (lam (oddTrace (gatePrepend g n gapThreeFiveGate))) :=
  ⟨40+1300*n,fun k hk => arbitrary_gate_pasts_agree_from h g n k hk⟩

theorem recon_shift (a : Nat → Bool) (p k t : Nat) :
    recon (fun s => a (p+s)) k t=recon a k (p+t) := by
  have key : ∀j,∀s,recon (fun u => a (p+u)) j s=recon a j (p+s) ∧
      recon (fun u => a (p+u)) (j+1) s=recon a (j+1) (p+s) := by
    intro j
    induction j with
    | zero => intro s;exact ⟨rfl,rfl⟩
    | succ j ih =>
        intro s
        refine ⟨(ih s).2,?_⟩
        rw [recon,recon,(ih (s+1)).2,(ih s).1,(ih s).2]
        simp only [Nat.add_assoc]
  exact (key k t).1

theorem temporal_phase_tail (p k : Nat) (hk : 40≤k) :
    lam (fun t => boundary (p+t)) k=row p (k+285) := by
  change recon (fun t => boundary (p+t)) k 0=row p (k+285)
  rw [recon_shift,recon_full]
  simp only [Nat.add_zero,fullRow,ite_eq_right (show ¬k<40 by omega)]

def shiftedGate (s r : Nat) : Bool := gapThreeFiveGate (s+r)

theorem boundary_shift_odd_trace (s : Nat) :
    (fun t => boundary (2*s+t))=oddTrace (shiftedGate s) := by
  funext t
  have cert : ∀a:Fin 8,∀b:Fin 16,
      boundary (2*a.val+b.val)=oddTrace (shiftedGate a.val) b.val := by decide +kernel
  have hs : (2*(s%8)+t%16)%16=(2*s+t)%16 := by omega
  have hp : (t%16)%2=t%2 := by omega
  have hd : (t%16)/2=(t/2)%8 := by omega
  have h := cert ⟨s%8,by omega⟩ ⟨t%16,by omega⟩
  simpa [boundary,oddTrace,shiftedGate,gapThreeFiveGate,hs,hp,hd,Nat.add_mod] using h

/-- All eight cyclic Gate phases share the same uniform bound. -/
theorem shifted_gate_pasts_agree_from (s : Nat) (h g : Nat → Bool) (n k : Nat)
    (hk : 40+1300*n≤k) :
    lam (oddTrace (gatePrepend h n (shiftedGate s))) k=
      lam (oddTrace (gatePrepend g n (shiftedGate s))) k := by
  apply Rule30SynchronizingCarrier.reconstructed_gate_pasts_agree_from
    carrier 285 (2*s) (shiftedGate s) 40 _ h g n k hk
  rw [←boundary_shift_odd_trace]
  exact temporal_phase_tail (2*s)

theorem prefixed_gate_tail (s : Nat) (q : Nat → Bool) (m k : Nat)
    (hk : 40+1300*m≤k) :
    lam (oddTrace (gatePrepend q m (shiftedGate s))) k=
      row (Rule30SynchronizingCarrier.gatePhase carrier (2*s) m) (k+285) := by
  rw [odd_trace_past,←gate_history_lam]
  apply Rule30SynchronizingCarrier.gate_history_tail_bound carrier 285 (2*s)
    (lam (oddTrace (shiftedGate s))) 40 _ q m k hk
  rw [←boundary_shift_odd_trace]
  exact temporal_phase_tail (2*s)

/-- Any finite prefix and any cyclic phase may precede this periodic tail.
The cutoff includes the prefix length m; it is not uniform over m. -/
theorem eventually_three_five_pasts_agree_from (s : Nat) (q h g : Nat → Bool)
    (m n k : Nat) (hk : 40+1300*(m+n)≤k) :
    lam (oddTrace (gatePrepend h n (gatePrepend q m (shiftedGate s)))) k=
      lam (oddTrace (gatePrepend g n (gatePrepend q m (shiftedGate s)))) k := by
  refine Rule30SynchronizingCarrier.reconstructed_gate_pasts_agree_from
    carrier 285 (Rule30SynchronizingCarrier.gatePhase carrier (2*s) m)
    (gatePrepend q m (shiftedGate s)) (40+1300*m) ?_ h g n k ?_
  · exact prefixed_gate_tail s q m
  · change 40+1300*m+1300*n≤k
    simpa only [Nat.mul_add,Nat.add_assoc] using hk

end Ruliology.CellularAutomata.Rule30PeriodicThreeFive
