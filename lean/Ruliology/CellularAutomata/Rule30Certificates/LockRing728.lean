module

public import Ruliology.CellularAutomata.Rule30SidewaysLocks

/-! The fourteen time slices of Troy Lowry’s 728-cell ring, from kit PR #378.
The kernel verifies the inverse recurrence, its boundary readings and the
comparison with all nine-site singleton edge words. -/
@[expose] public section

namespace Ruliology.CellularAutomata.Rule30LockRing728
open Rule30SidewaysLocks

/-- The fourteen time slices of Lowry’s periodic ring, bit zero first. -/
def planes : Array Nat := #[
  0x4a843e23d80b43315d28d22c4c8cbcb1c91d493e121ef07d82ace05d4af8cbd0613b58bbe5fa2a2c4fdca7049d4be6351f8a790202b9d3453633dc8a5b09704a8212362ae02b4013e0e9dda36caa799b42cd23359e17d53731864a,
  0xface6176141a66eb51ed9f6afbdba3ab3fb17fe13f3088c146ab90d17a85ba18d3e255a21d036b6af813bc8ff17a1d65b05bc78706a71e6de56e13dbd29f48fac73f656a906a603e118f11364babc77266b9f6e5713415e4eb4dfb,
  0x2b9d3453633dc8a5b09704a8212362ae02b4013e0e9dda36caa799b42cd23359e17d53731864a4a843e23d80b43315d28d22c4c8cbcb1c91d493e121ef07d82ace05d4af8cbd0613b58bbe5fa2a2c4fdca7049d4be6351f8a7902,
  0x6a71e6de56e13dbd29f48fac73f656a906a603e118f11364babc77266b9f6e5713415e4eb4dfbface6176141a66eb51ed9f6afbdba3ab3fb17fe13f3088c146ab90d17a85ba18d3e255a21d036b6af813bc8ff17a1d65b05bc787,
  0x8cbcb1c91d493e121ef07d82ace05d4af8cbd0613b58bbe5fa2a2c4fdca7049d4be6351f8a790202b9d3453633dc8a5b09704a8212362ae02b4013e0e9dda36caa799b42cd23359e17d53731864a4a843e23d80b43315d28d22c4c,
  0xdba3ab3fb17fe13f3088c146ab90d17a85ba18d3e255a21d036b6af813bc8ff17a1d65b05bc78706a71e6de56e13dbd29f48fac73f656a906a603e118f11364babc77266b9f6e5713415e4eb4dfbface6176141a66eb51ed9f6afb,
  0x12362ae02b4013e0e9dda36caa799b42cd23359e17d53731864a4a843e23d80b43315d28d22c4c8cbcb1c91d493e121ef07d82ace05d4af8cbd0613b58bbe5fa2a2c4fdca7049d4be6351f8a790202b9d3453633dc8a5b09704a82,
  0x3f656a906a603e118f11364babc77266b9f6e5713415e4eb4dfbface6176141a66eb51ed9f6afbdba3ab3fb17fe13f3088c146ab90d17a85ba18d3e255a21d036b6af813bc8ff17a1d65b05bc78706a71e6de56e13dbd29f48fac7,
  0xe05d4af8cbd0613b58bbe5fa2a2c4fdca7049d4be6351f8a790202b9d3453633dc8a5b09704a8212362ae02b4013e0e9dda36caa799b42cd23359e17d53731864a4a843e23d80b43315d28d22c4c8cbcb1c91d493e121ef07d82ac,
  0x90d17a85ba18d3e255a21d036b6af813bc8ff17a1d65b05bc78706a71e6de56e13dbd29f48fac73f656a906a603e118f11364babc77266b9f6e5713415e4eb4dfbface6176141a66eb51ed9f6afbdba3ab3fb17fe13f3088c146ab,
  0x799b42cd23359e17d53731864a4a843e23d80b43315d28d22c4c8cbcb1c91d493e121ef07d82ace05d4af8cbd0613b58bbe5fa2a2c4fdca7049d4be6351f8a790202b9d3453633dc8a5b09704a8212362ae02b4013e0e9dda36caa,
  0xc77266b9f6e5713415e4eb4dfbface6176141a66eb51ed9f6afbdba3ab3fb17fe13f3088c146ab90d17a85ba18d3e255a21d036b6af813bc8ff17a1d65b05bc78706a71e6de56e13dbd29f48fac73f656a906a603e118f11364bab,
  0x2c4fdca7049d4be6351f8a790202b9d3453633dc8a5b09704a8212362ae02b4013e0e9dda36caa799b42cd23359e17d53731864a4a843e23d80b43315d28d22c4c8cbcb1c91d493e121ef07d82ace05d4af8cbd0613b58bbe5fa2a,
  0x6af813bc8ff17a1d65b05bc78706a71e6de56e13dbd29f48fac73f656a906a603e118f11364babc77266b9f6e5713415e4eb4dfbface6176141a66eb51ed9f6afbdba3ab3fb17fe13f3088c146ab90d17a85ba18d3e255a21d036b]

def tile (t d : Nat) : Bool := (planes.getD (t%14) 0).testBit (d%728)

theorem tile_inv (t d : Nat) :
    tile t (d+2) = xor (tile (t+1) (d+1)) (tile t (d+1) || tile t d) := by
  have check : ∀ i : Fin 14, ∀ j : Fin 728,
      tile i (j.val+2) = xor (tile (i.val+1) (j.val+1)) (tile i (j.val+1) || tile i j) := by
    decide +kernel
  have h := check ⟨t%14,by omega⟩ ⟨d%728,by omega⟩
  simpa only [tile,Nat.mod_add_mod,Nat.mod_mod] using h

theorem wall_inv (t : Nat) :
    tile t 2 = xor (tile (t+1) 1) (tile t 1 || false) := by
  have check : ∀ i : Fin 14, tile i 2 = xor (tile (i.val+1) 1) (tile i 1 || false) := by decide +kernel
  simpa only [tile,Nat.mod_add_mod,Nat.mod_mod] using check ⟨t%14,by omega⟩

theorem tile_even (q : Nat) : tile (2*q) 1 = !word7.getD ((6+q)%7) false := by
  have check : ∀ i : Fin 7, tile (2*i.val) 1 = !word7.getD ((6+i.val)%7) false := by decide +kernel
  have h := check ⟨q%7,by omega⟩
  change tile (2*(q%7)) 1 = !word7.getD ((6+q%7)%7) false at h
  unfold tile at h ⊢
  simpa only [show (2*(q%7))%14 = (2*q)%14 by omega, Nat.add_mod_mod] using h

theorem tile_odd (q : Nat) : tile (2*q+1) 1 = true := by
  have check : ∀ i : Fin 7, tile (2*i.val+1) 1 = true := by decide +kernel
  have h := check ⟨q%7,by omega⟩
  change tile (2*(q%7)+1) 1 = true at h
  unfold tile at h ⊢
  simpa only [show (2*(q%7)+1)%14 = (2*q+1)%14 by omega] using h

def edgeWord (a : Nat) : Nat := #[550,758,38,246].getD (a%4) 0

set_option maxRecDepth 8192 in
set_option maxHeartbeats 20000000 in
theorem edge_table : ∀ e : Fin 7, ∀ a : Fin 728, ∃ j : Fin 9,
    tile (2*e.val) (728+a.val-j.val) ≠ (edgeWord a.val).testBit (j.val+1) := by decide +kernel

end Ruliology.CellularAutomata.Rule30LockRing728
