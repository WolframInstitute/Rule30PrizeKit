module
public import Ruliology.CellularAutomata.Rule30RunEnvelopes
/-! Compositional ranked response laws. A natural rank can drop only finitely
many times; on rank-preserving blocks the masked output is prescribed. -/
@[expose] public section
namespace Ruliology.CellularAutomata.Rule30RankedWords
open Rule30StripCertificates Rule30RunEnvelopes Rule30Jen Rule30MaskedJen

abbrev code (K t : Nat) : Nat := encRow t 0 K

theorem enc_unique {K t a b : Nat} (ha : Enc K t 0 a) (hb : Enc K t 0 b) : a=b := by
  apply Nat.eq_of_testBit_eq
  intro i
  by_cases hi : i<K
  · rw [ha.2 i hi,hb.2 i hi]
  · have hp : 2^K≤2^i := Nat.pow_le_pow_right (by decide) (by omega)
    rw [Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le ha.1 hp),Nat.testBit_lt_two_pow (Nat.lt_of_lt_of_le hb.1 hp)]

def Reads (t : Nat) (w : List Bool) : Prop := ∀ i, i<w.length → cell (t+i) 0=w.getD i false

theorem code_word {K t A : Nat} {w : List Bool} (h : Reads t w)
    (hs : A.testBit (code K t)=true) :
    (applyWord K w A).testBit (code K (t+w.length))=true := by
  obtain ⟨r,he,hm⟩ := enc_applyWord w t (code K t) A (enc_encRow K t 0) hs h
  have hr := enc_unique he (enc_encRow K (t+w.length) 0)
  simpa [hr] using hm

theorem reads_left {t : Nat} {u v : List Bool} (h : Reads t (u++v)) : Reads t u := by
  intro i hi
  have hh := h i (by simp only [List.length_append];omega)
  simpa [List.getD_eq_getElem?_getD,List.getElem?_append,hi] using hh

theorem reads_right {t : Nat} {u v : List Bool} (h : Reads t (u++v)) : Reads (t+u.length) v := by
  intro i hi
  have hh := h (u.length+i) (by simp only [List.length_append];omega)
  simpa [List.getD_eq_getElem?_getD,List.getElem?_append,Nat.add_assoc,show ¬u.length+i<u.length by omega] using hh

/-- Endpoints stay in E, rank does not increase, and preserving rank fixes the output. -/
def Ranked (K E : Nat) (rank : Nat→Nat) (w : List Bool) (g : Nat→Nat→Bool) : Prop :=
  ∀ t, Reads t w → E.testBit (code K t)=true →
    E.testBit (code K (t+w.length))=true ∧
    rank (code K (t+w.length))≤rank (code K t) ∧
    (rank (code K (t+w.length))=rank (code K t) →
      ∀ i, i<w.length → orCol 0 (t+i)=g (rank (code K t)) i)

theorem ranked_nil (K E : Nat) (rank : Nat→Nat) (g : Nat→Nat→Bool) :
    Ranked K E rank [] g := by
  intro t h hs
  refine ⟨hs,Nat.le_refl _,fun he i hi => ?_⟩
  exact (Nat.not_lt_zero _ hi).elim

theorem ranked_append {K E : Nat} {rank : Nat→Nat} {u v : List Bool}
    {g h : Nat→Nat→Bool} (hu : Ranked K E rank u g) (hv : Ranked K E rank v h) :
    Ranked K E rank (u++v) (fun r i => if i<u.length then g r i else h r (i-u.length)) := by
  intro t ht hs
  obtain ⟨hmid,hle1,ho1⟩ := hu t (reads_left ht) hs
  obtain ⟨hend,hle2,ho2⟩ := hv (t+u.length) (reads_right ht) hmid
  have hend' : t+(u++v).length=(t+u.length)+v.length := by simp [Nat.add_assoc]
  rw [hend']
  refine ⟨hend,Nat.le_trans hle2 hle1,fun he i hi => ?_⟩
  have eq1 : rank (code K (t+u.length))=rank (code K t) := by omega
  have eq2 : rank (code K ((t+u.length)+v.length))=rank (code K (t+u.length)) := by omega
  by_cases hil : i<u.length
  · simpa [hil] using ho1 eq1 i hil
  · have hir : i-u.length<v.length := by simp only [List.length_append] at hi;omega
    have hh := ho2 eq2 (i-u.length) hir
    rw [eq1] at hh
    simpa [hil,show t+u.length+(i-u.length)=t+i by omega] using hh

/-- A ranked word excludes eventual repetition once its invariant has been entered. -/
theorem no_word_ranked (K E k : Nat) (rank : Nat→Nat) (w : List Bool) (g : Nat→Nat→Bool)
    (hw : 0<w.length) (warm : Sub (iterW K w k (fullSet K)) E)
    (hr : Ranked K E rank w g) : ¬ EventuallyWord w := by
  rintro ⟨T,hT⟩
  have hb : ∀ m, Reads (T+m*w.length) w := by
    intro m i hi
    rw [hT _ (by omega),show T+m*w.length+i-T=i+m*w.length by omega,
      Nat.add_mul_mod_self_right,Nat.mod_eq_of_lt hi]
  have hcper : ∀ t, T≤t → cell (t+w.length) 0=cell t 0 := by
    intro t ht
    rw [hT t ht,hT (t+w.length) (by omega),show t+w.length-T=(t-T)+w.length by omega,Nat.add_mod_right]
  have hfull : (fullSet K).testBit (code K T)=true := by
    simp only [fullSet,Nat.testBit_two_pow_sub_one]
    exact decide_eq_true (enc_encRow K T 0).1
  obtain ⟨s,he,hm⟩ := enc_iterW w k T _ _ (enc_encRow K T 0) hfull (fun m i _ hi => hb m i hi)
  have heq := enc_unique he (enc_encRow K (T+k*w.length) 0)
  have hstart : E.testBit (code K (T+k*w.length))=true := by simpa [heq] using warm s hm
  have hinv : ∀ n, k≤n → E.testBit (code K (T+n*w.length))=true := by
    intro n hn
    obtain ⟨j,rfl⟩ : ∃j,n=k+j := ⟨n-k,by omega⟩
    induction j with
    | zero => simpa using hstart
    | succ j ih =>
      have h := (hr _ (hb (k+j)) (ih (by omega))).1
      simpa [Nat.add_mul,Nat.mul_add,Nat.add_assoc] using h
  let R : Nat→Nat := fun n => rank (code K (T+n*w.length))
  have hmono : ∀ n,k≤n → R (n+1)≤R n := by
    intro n hn
    have h := (hr _ (hb n) (hinv n hn)).2.1
    simpa [R,Nat.add_mul,Nat.add_assoc] using h
  obtain ⟨N,hN,hconst⟩ := antitone_eventually_const R k hmono
  have hform : ∀ t,T+N*w.length≤t → orCol 0 t=g (R N) ((t-T)%w.length) := by
    intro t ht
    have hn : N≤(t-T)/w.length := (Nat.le_div_iff_mul_le hw).2 (by omega)
    have hp : (t-T)%w.length<w.length := Nat.mod_lt _ hw
    have hd : T+((t-T)/w.length)*w.length+(t-T)%w.length=t := by
      have := Nat.div_add_mod (t-T) w.length
      rw [Nat.mul_comm] at this;omega
    have eqr : rank (code K ((T+((t-T)/w.length)*w.length)+w.length))=
      rank (code K (T+((t-T)/w.length)*w.length)) := by
      have h1 := hconst ((t-T)/w.length+1) (by omega)
      have h0 := hconst ((t-T)/w.length) hn
      simpa [R,Nat.add_mul,Nat.add_assoc] using h1.trans h0.symm
    have hh := (hr _ (hb ((t-T)/w.length)) (hinv _ (by omega))).2.2 eqr _ hp
    rw [hd] at hh
    change orCol 0 t=g (R ((t-T)/w.length)) ((t-T)%w.length) at hh
    rw [hconst _ hn] at hh
    exact hh
  apply orCol_not_eventuallyPeriodic 0 ⟨T,w.length,hw,hcper⟩
  refine ⟨T+N*w.length,w.length,hw,fun t ht => ?_⟩
  change orCol 0 (t+w.length)=orCol 0 t
  rw [hform t ht,hform (t+w.length) (by omega),
    show t+w.length-T=(t-T)+w.length by omega,Nat.add_mod_right]

/-! ## Exact concatenation equivalence `Reads t (u ++ v) ↔ Reads t u ∧ Reads (t + u.length) v` -/

/-- **Exact Concatenation Equivalence for `Reads` (`reads_nil_and_append_iff`).** -/
theorem reads_nil_and_append_iff (t : Nat) (u v : List Bool) :
    Reads t [] ∧
    (Reads t (u ++ v) ↔ Reads t u ∧ Reads (t + u.length) v) := by
  refine ⟨fun i hi => (Nat.not_lt_zero _ hi).elim,
          ⟨fun h => ⟨reads_left h, reads_right h⟩, fun ⟨hu, hv⟩ i hi => ?_⟩⟩
  by_cases hiu : i < u.length
  · have h1 := hu i hiu
    simpa [List.getD_eq_getElem?_getD, List.getElem?_append, hiu] using h1
  · have hiv : i - u.length < v.length := by
      simp only [List.length_append] at hi; omega
    have h2 := hv (i - u.length) hiv
    rw [show t + u.length + (i - u.length) = t + i by omega] at h2
    simpa [List.getD_eq_getElem?_getD, List.getElem?_append, hiu] using h2

end Ruliology.CellularAutomata.Rule30RankedWords
