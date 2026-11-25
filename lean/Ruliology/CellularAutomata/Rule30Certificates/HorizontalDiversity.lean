module

public import Ruliology.CellularAutomata.Rule30HorizontalWords
public import Ruliology.CellularAutomata.Rule30MaskedJen
public import Ruliology.CellularAutomata.Rule30Realization

/-!
# A four-cell upper bound on masked futures for a prescribed Rule 30 center

The 16 bits in a state label describe allowed patterns at the four sites just
right of the center. The transition table has columns (clock, mask) in
lexicographic order, with state 0 unrestricted and state 1 empty. States
with the same language have been merged. Both soundness and the integer
potential certificate are verified below using the Lean kernel.
-/
@[expose] public section

namespace Ruliology.CellularAutomata.Rule30Certificates.HorizontalDiversity
open Ruliology.CellularAutomata Rule30Jen Rule30MaskedJen Rule30Realization

private def labels : Array Nat := #[65535, 0, 55753, 43690, 6473, 8738, 14231, 21845, 8736, 14230, 43176, 21588, 55745, 59078, 40992, 20496, 55488, 58837, 4369, 60616, 50372, 514, 10119, 8226, 4113, 16456, 33924, 2120, 1413, 20801, 10280, 5397, 17733, 17476, 39297, 26455, 5140, 17729, 33410, 8224, 34944, 5396, 26435, 9862, 4368, 59074, 39305, 26182, 9091, 59094, 52416, 6409, 9734, 4112, 257, 26198, 20544, 13203, 50645, 1285, 13202, 17472, 50388, 59335, 26178, 1028, 50629, 26439]

def edges : Array (Array Nat) := #[
  #[2, 3, 1, 0],
  #[1, 1, 1, 1],
  #[4, 5, 1, 6],
  #[1, 3, 1, 7],
  #[4, 8, 1, 9],
  #[1, 10, 1, 11],
  #[12, 3, 1, 0],
  #[2, 1, 1, 13],
  #[1, 14, 1, 15],
  #[16, 3, 1, 17],
  #[1, 5, 1, 18],
  #[19, 1, 1, 20],
  #[4, 21, 1, 22],
  #[10, 3, 1, 7],
  #[1, 23, 1, 24],
  #[25, 1, 1, 26],
  #[27, 21, 1, 28],
  #[2, 5, 1, 0],
  #[29, 1, 1, 3],
  #[30, 5, 1, 31],
  #[10, 21, 1, 32],
  #[1, 10, 1, 33],
  #[34, 3, 1, 35],
  #[1, 30, 1, 36],
  #[37, 1, 1, 38],
  #[30, 39, 1, 36],
  #[40, 21, 1, 37],
  #[30, 8, 1, 41],
  #[34, 21, 1, 42],
  #[4, 1, 1, 43],
  #[1, 8, 1, 44],
  #[12, 1, 1, 45],
  #[46, 1, 1, 47],
  #[10, 1, 1, 33],
  #[29, 21, 1, 48],
  #[2, 10, 1, 49],
  #[50, 1, 1, 50],
  #[51, 1, 1, 52],
  #[1, 3, 1, 32],
  #[1, 39, 1, 53],
  #[1, 21, 1, 54],
  #[16, 1, 1, 19],
  #[51, 10, 1, 55],
  #[40, 3, 1, 7],
  #[56, 1, 1, 10],
  #[30, 3, 1, 7],
  #[29, 5, 1, 57],
  #[10, 10, 1, 11],
  #[18, 3, 1, 35],
  #[19, 3, 1, 58],
  #[30, 21, 1, 59],
  #[29, 8, 1, 60],
  #[40, 10, 1, 11],
  #[61, 1, 1, 40],
  #[18, 1, 1, 5],
  #[19, 10, 1, 62],
  #[27, 1, 1, 26],
  #[29, 3, 1, 0],
  #[2, 21, 1, 63],
  #[34, 1, 1, 64],
  #[56, 3, 1, 17],
  #[30, 1, 1, 65],
  #[19, 21, 1, 66],
  #[46, 3, 1, 35],
  #[30, 10, 1, 11],
  #[40, 1, 1, 61],
  #[46, 21, 1, 67],
  #[46, 10, 1, 55]
]

def potentials : Array (Array Nat) := #[
  #[443, 0, 405, 116, 400, 100, 443, 328, 100, 310, 100, 144, 405, 196, 100, 136, 221, 412, 256, 165, 165, 100, 381, 100, 216, 160, 165, 160, 353, 320, 100, 328, 273, 100, 341, 408, 144, 269, 116, 100, 100, 195, 349, 196, 124, 196, 341, 160, 310, 259, 165, 336, 160, 100, 205, 224, 136, 372, 412, 273, 239, 100, 228, 381, 160, 100, 353, 353],
  #[477, 0, 409, 144, 400, 106, 477, 333, 100, 364, 100, 170, 409, 250, 100, 136, 243, 422, 243, 179, 195, 106, 426, 100, 193, 170, 195, 170, 371, 320, 100, 333, 282, 106, 332, 439, 170, 269, 144, 100, 100, 232, 375, 250, 140, 234, 332, 212, 336, 314, 179, 323, 212, 100, 192, 276, 154, 387, 422, 282, 264, 100, 259, 426, 196, 106, 371, 388],
  #[512, 0, 416, 180, 400, 111, 487, 349, 100, 372, 132, 180, 416, 274, 100, 136, 275, 463, 239, 212, 224, 111, 425, 100, 185, 160, 212, 192, 376, 303, 112, 324, 288, 111, 352, 460, 155, 241, 180, 100, 132, 208, 352, 260, 124, 260, 352, 221, 340, 344, 212, 336, 196, 100, 177, 291, 144, 402, 463, 262, 299, 100, 294, 451, 191, 100, 401, 398],
  #[446, 0, 381, 156, 371, 103, 412, 290, 100, 316, 116, 180, 381, 259, 100, 153, 289, 388, 191, 205, 211, 103, 364, 100, 191, 170, 196, 185, 304, 278, 100, 256, 236, 103, 292, 392, 149, 231, 156, 100, 116, 175, 333, 236, 111, 244, 292, 205, 300, 323, 205, 284, 183, 100, 144, 275, 174, 347, 388, 208, 249, 100, 295, 392, 190, 100, 336, 339],
  #[536, 0, 354, 224, 337, 164, 496, 312, 139, 465, 116, 214, 319, 378, 109, 109, 229, 428, 167, 199, 244, 164, 442, 100, 136, 170, 212, 179, 298, 239, 100, 273, 258, 164, 247, 470, 181, 192, 224, 100, 100, 241, 346, 345, 136, 304, 282, 328, 340, 432, 170, 265, 296, 100, 116, 378, 149, 391, 392, 218, 360, 100, 294, 482, 254, 132, 338, 412],
  #[522, 0, 436, 204, 378, 142, 488, 318, 122, 416, 138, 183, 404, 346, 116, 116, 260, 456, 221, 225, 248, 142, 428, 100, 190, 170, 208, 170, 329, 298, 100, 284, 272, 142, 327, 460, 155, 231, 204, 100, 106, 212, 372, 297, 136, 292, 359, 284, 348, 387, 193, 301, 235, 100, 144, 324, 155, 425, 424, 230, 340, 100, 288, 476, 229, 116, 378, 414],
  #[470, 0, 362, 195, 347, 116, 436, 276, 116, 386, 128, 157, 319, 310, 109, 109, 200, 404, 180, 208, 200, 116, 436, 100, 111, 160, 170, 189, 326, 238, 109, 241, 276, 116, 260, 391, 132, 238, 195, 100, 100, 192, 349, 280, 139, 275, 295, 231, 358, 352, 165, 288, 200, 100, 180, 272, 116, 358, 360, 241, 317, 100, 242, 470, 196, 100, 360, 391],
  #[365, 0, 340, 144, 332, 144, 322, 221, 119, 300, 119, 144, 301, 288, 116, 116, 218, 340, 156, 224, 224, 144, 322, 106, 103, 191, 169, 217, 258, 221, 112, 178, 221, 144, 236, 365, 100, 221, 144, 100, 100, 156, 365, 233, 122, 250, 275, 288, 300, 288, 186, 268, 233, 100, 156, 288, 138, 300, 301, 178, 266, 106, 224, 365, 250, 100, 301, 365],
  #[382, 0, 382, 267, 292, 136, 382, 200, 109, 338, 205, 156, 341, 267, 173, 156, 297, 382, 116, 267, 226, 100, 352, 136, 116, 136, 216, 186, 300, 200, 112, 188, 170, 100, 269, 252, 144, 170, 226, 100, 164, 144, 221, 267, 100, 267, 310, 136, 352, 338, 226, 212, 136, 100, 100, 208, 156, 382, 341, 157, 338, 100, 297, 352, 136, 100, 311, 221],
  #[410, 0, 390, 280, 298, 144, 410, 220, 123, 371, 192, 180, 340, 280, 153, 170, 301, 410, 144, 260, 231, 100, 368, 124, 144, 124, 193, 167, 282, 208, 100, 208, 177, 100, 272, 276, 170, 157, 231, 100, 142, 170, 233, 280, 106, 280, 322, 144, 368, 371, 210, 240, 144, 106, 100, 236, 170, 410, 361, 153, 371, 100, 321, 368, 144, 100, 319, 233],
  #[429, 0, 397, 255, 372, 172, 429, 303, 100, 365, 177, 199, 354, 255, 152, 170, 264, 429, 180, 228, 218, 132, 376, 145, 180, 145, 185, 193, 298, 276, 109, 244, 263, 132, 279, 346, 155, 237, 218, 100, 116, 180, 303, 255, 111, 255, 340, 172, 376, 340, 184, 288, 172, 100, 132, 236, 170, 429, 386, 204, 365, 106, 303, 376, 172, 100, 332, 303],
  #[376, 0, 349, 221, 309, 126, 376, 248, 100, 324, 144, 180, 349, 221, 100, 136, 261, 376, 156, 193, 221, 116, 313, 106, 156, 106, 191, 154, 292, 224, 112, 220, 231, 116, 287, 282, 149, 187, 221, 100, 144, 180, 231, 221, 103, 221, 287, 126, 313, 288, 193, 254, 126, 100, 116, 194, 136, 376, 376, 200, 324, 100, 288, 313, 126, 100, 313, 231],
  #[328, 0, 328, 176, 297, 144, 328, 224, 136, 328, 116, 185, 295, 176, 116, 173, 240, 328, 224, 167, 142, 100, 221, 136, 185, 136, 136, 136, 187, 224, 100, 224, 116, 100, 295, 297, 181, 116, 142, 100, 100, 214, 189, 176, 164, 176, 328, 144, 221, 289, 126, 297, 144, 132, 116, 257, 173, 328, 295, 116, 328, 100, 256, 221, 144, 100, 187, 189],
  #[344, 0, 344, 243, 292, 160, 344, 204, 136, 344, 144, 177, 301, 243, 144, 153, 239, 344, 204, 196, 211, 106, 277, 124, 177, 124, 190, 144, 243, 204, 100, 204, 138, 106, 301, 272, 155, 138, 211, 100, 106, 183, 189, 243, 142, 243, 344, 160, 277, 309, 164, 292, 160, 116, 138, 243, 153, 344, 301, 138, 344, 100, 266, 277, 160, 100, 243, 189],
  #[276, 0, 276, 180, 276, 148, 276, 195, 139, 276, 180, 169, 222, 180, 148, 152, 195, 276, 195, 180, 111, 100, 238, 145, 169, 145, 111, 172, 152, 195, 132, 195, 128, 100, 222, 248, 132, 128, 111, 106, 111, 157, 206, 180, 116, 180, 276, 148, 238, 241, 111, 276, 148, 100, 128, 213, 152, 276, 222, 128, 276, 100, 195, 238, 148, 100, 152, 206],
  #[221, 0, 221, 156, 221, 136, 221, 144, 122, 221, 156, 100, 191, 156, 136, 100, 132, 221, 144, 156, 103, 100, 199, 106, 100, 106, 103, 126, 165, 144, 116, 144, 119, 100, 191, 193, 100, 119, 103, 100, 103, 144, 171, 156, 144, 156, 221, 136, 199, 178, 103, 221, 136, 100, 119, 156, 100, 221, 191, 119, 221, 100, 132, 199, 136, 100, 165, 171]
]

abbrev State := Fin 68
abbrev Prefix := Fin 16

def next (s : State) (c o : Bool) : State :=
  Fin.ofNat 68 ((edges[s.val]!).getD (2*c.toNat + o.toNat) 1)

private def prefixCons (b : Bool) (q : Prefix) : Prefix :=
  Fin.ofNat 16 (8*b.toNat + q.val/2)

private def forecast : List Bool → Prefix
  | [] => 0
  | b::bs => prefixCons b (forecast bs)

private def W (q : Prefix) (s : State) : Nat := (potentials[q.val]!).getD s.val 0

private def accepts (s : State) (a b c d : Bool) : Bool :=
  (labels.getD s.val 0).testBit (a.toNat + 2*b.toNat + 4*c.toNat + 8*d.toNat)

set_option maxRecDepth 100000
set_option maxHeartbeats 10000000

private theorem transition_sound : ∀ (s : State) (c a b d e f : Bool),
    accepts s a b d e = true →
    accepts (next s c (c || a)) (rule c a b) (rule a b d) (rule b d e) (rule d e f) = true := by
  decide +kernel

private theorem initial_accepts : ∀ a b d e, accepts 0 a b d e = true := by decide +kernel
private theorem empty_rejects : ∀ a b d e, accepts 1 a b d e = false := by decide +kernel

private theorem potential_step : ∀ (s : State) (q : Prefix) (c : Bool),
    4*(W q (next s c false) + W q (next s c true)) ≤ 5*W (prefixCons c q) s := by
  decide +kernel

private theorem initial_potential : ∀ (q : Prefix), W q 0 ≤ 600 := by decide +kernel
private theorem terminal_potential : ∀ (s : State), s ≠ 1 → 100 ≤ W 0 s := by decide +kernel

/-- Candidate lists are indexed by the prescribed center word and the current strip state. -/
def words : List Bool → State → List (List Bool)
  | [], s => if s = 1 then [] else [[]]
  | c::bs, s =>
    (words bs (next s c false)).map (false :: ·) ++
    (words bs (next s c true)).map (true :: ·)

/-- Every listed path pays for its two possible mask extensions with the same fixed
center continuation. The right boundary of the four-cell strip is arbitrary. -/
private theorem bound (c : List Bool) (s : State) :
    100 * (words c s).length * 4^c.length ≤ W (forecast c) s * 5^c.length := by
  induction c generalizing s with
  | nil =>
    by_cases h : s = 1
    · simp [words,h]
    · simpa [words,h,forecast] using terminal_potential s h
  | cons b bs ih =>
    let t := next s b false
    let u := next s b true
    have h := Nat.add_le_add (ih t) (ih u)
    have budget := potential_step s (forecast bs) b
    simp only [words,List.length_append,List.length_map,List.length_cons,forecast,Nat.pow_succ]
    change 100 * ((words bs t).length + (words bs u).length) * (4^bs.length*4) ≤ _
    calc
      _ = 4 * (100 * (words bs t).length * 4^bs.length +
          100 * (words bs u).length * 4^bs.length) := by simp [Nat.mul_add,Nat.add_mul]; ac_rfl
      _ ≤ 4 * (W (forecast bs) t * 5^bs.length + W (forecast bs) u * 5^bs.length) :=
        Nat.mul_le_mul_left 4 h
      _ = (4*(W (forecast bs) t + W (forecast bs) u))*5^bs.length := by rw [Nat.mul_assoc, Nat.add_mul]
      _ ≤ (5*W (prefixCons b (forecast bs)) s)*5^bs.length := Nat.mul_le_mul_right _ budget
      _ = _ := by ac_rfl

theorem masked_word_count (c : List Bool) :
    (words c 0).length * 4^c.length ≤ 6 * 5^c.length := by
  have h := Nat.le_trans (bound c 0) (Nat.mul_le_mul_right (5^c.length) (initial_potential (forecast c)))
  rw [Nat.mul_assoc] at h
  omega

private theorem segment_length (f : Nat → Bool) (t n : Nat) :
    (segment f t n).length=n := by
  induction n generalizing t with
  | zero => rfl
  | succ n ih => simp [segment,ih]

private theorem mem_strip (x : Int → Bool) (t n : Nat) (s : State)
    (hs : accepts s (evol x t 1) (evol x t 2) (evol x t 3) (evol x t 4) = true) :
    segment (fun k => evol x k 0 || evol x k 1) t n ∈ words (segment (fun k => evol x k 0) t n) s := by
  induction n generalizing t s with
  | zero =>
    have h : s ≠ 1 := by
      rintro rfl
      rw [empty_rejects] at hs
      contradiction
    simp [segment,words,h]
  | succ n ih =>
    have hn := transition_sound s (evol x t 0) _ _ _ _ (evol x t 5) hs
    have hm := ih (t+1) _ hn
    simp only [segment,words,List.mem_append,List.mem_map]
    cases h : evol x t 0 || evol x t 1
    · exact Or.inl ⟨_, by simpa only [h] using hm, rfl⟩
    · exact Or.inr ⟨_, by simpa only [h] using hm, rfl⟩

/-- All actual Rule 30 histories are covered, for every initial row and start time. -/
theorem observations_mem (x : Int → Bool) (t n : Nat) :
    segment (fun k => evol x k 0 || evol x k 1) t n ∈ words (segment (fun k => evol x k 0) t n) 0 :=
  mem_strip x t n 0 (initial_accepts _ _ _ _)


/-- Uniform conditional support bound, directly quantified over genuine Rule 30 histories.
For each prescribed center word there is one list shared by every initial row and age. -/
theorem genuine_channel_bound (c : List Bool) :
    ∃ candidates : List (List Bool), candidates.length * 4^c.length ≤ 6 * 5^c.length ∧
      ∀ (x : Int → Bool) (t : Nat), segment (fun k => evol x k 0) t c.length = c →
        segment (fun k => evol x k 0 || evol x k 1) t c.length ∈ candidates := by
  refine ⟨words c 0, masked_word_count c, ?_⟩
  intro x t hc
  simpa only [hc] using observations_mem x t c.length

end Ruliology.CellularAutomata.Rule30Certificates.HorizontalDiversity
