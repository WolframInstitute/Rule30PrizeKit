module

public import Ruliology.CellularAutomata.Rule30StripCertificateTable

/-!
# Rule 30: 324 more periodic words excluded by bitmask strip certificates

`Rule30StripCertificateTable` excludes thirty words of lengths `8 … 13`, the words a search over
those lengths certified at strip width `K ≤ 9`; rerun, the search finds exactly those thirty. Run
over lengths `14 … 18` with strip widths `K ≤ 10`, it certifies 324 further primitive words,
each written as its least rotation: 23 of length 14, 43 of length 15, 59 of length 16, 87 of
length 17 and 112 of length 18. Each entry `(n, bits, K, k)` is the word
`Rule30StripCertificateTable.wordOf n bits` with a strip width `K` and a number `k` of warm-up
periods for which `Rule30StripCertificates.stripCert` holds. The kernel evaluates every
certificate, six entries per theorem (`chunk0_ok` …), and soundness
(`Rule30StripCertificates.not_eventually_word_strip`) gives:

* `not_eventually_certTableTwo`: **for every entry, the center column is not eventually equal to
  the entry's word repeated**, whatever the transient and the phase.

Only the certificates are checked here, not the completeness of the search. Some entries may also
follow from general theorems such as `Rule30RunTransitions.not_eventuallyWord_of_good`.

Contributed by Katip Kurtuluş with Claude (Anthropic), ChatGPT (OpenAI) and Gemini (Google).
-/

@[expose] public section

namespace Ruliology.CellularAutomata
namespace Rule30StripCertificateTableTwo

open Rule30Jen Rule30StripCertificates Rule30StripCertificateTable

def chunk0 : List (Nat × Nat × Nat × Nat) := [
    (14, 1, 8, 2),
    (14, 3, 6, 2),
    (14, 5, 9, 2),
    (14, 11, 6, 3),
    (14, 15, 10, 3),
    (14, 19, 6, 2)]

theorem chunk0_ok :
    chunk0.all (fun e => decide (1 ≤ e.2.2.1) && decide (0 < e.1) &&
      stripCert (wordOf e.1 e.2.1) e.2.2.1 e.2.2.2) = true := by decide +kernel

def chunk1 : List (Nat × Nat × Nat × Nat) := [
    (14, 23, 8, 2),
    (14, 27, 6, 2),
    (14, 51, 9, 2),
    (14, 511, 5, 1),
    (14, 767, 6, 2),
    (14, 1023, 5, 1)]

theorem chunk1_ok :
    chunk1.all (fun e => decide (1 ≤ e.2.2.1) && decide (0 < e.1) &&
      stripCert (wordOf e.1 e.2.1) e.2.2.1 e.2.2.2) = true := by decide +kernel

def chunk2 : List (Nat × Nat × Nat × Nat) := [
    (14, 1535, 5, 1),
    (14, 2047, 5, 1),
    (14, 2815, 5, 2),
    (14, 3071, 5, 1),
    (14, 4091, 5, 1),
    (14, 4093, 5, 1)]

theorem chunk2_ok :
    chunk2.all (fun e => decide (1 ≤ e.2.2.1) && decide (0 < e.1) &&
      stripCert (wordOf e.1 e.2.1) e.2.2.1 e.2.2.2) = true := by decide +kernel

def chunk3 : List (Nat × Nat × Nat × Nat) := [
    (14, 4095, 5, 1),
    (14, 6143, 5, 1),
    (14, 7167, 5, 1),
    (14, 7679, 5, 1),
    (14, 8191, 5, 1),
    (15, 1, 8, 2)]

theorem chunk3_ok :
    chunk3.all (fun e => decide (1 ≤ e.2.2.1) && decide (0 < e.1) &&
      stripCert (wordOf e.1 e.2.1) e.2.2.1 e.2.2.2) = true := by decide +kernel

def chunk4 : List (Nat × Nat × Nat × Nat) := [
    (15, 3, 6, 2),
    (15, 5, 9, 2),
    (15, 11, 6, 2),
    (15, 13, 7, 2),
    (15, 15, 10, 3),
    (15, 19, 6, 2)]

theorem chunk4_ok :
    chunk4.all (fun e => decide (1 ≤ e.2.2.1) && decide (0 < e.1) &&
      stripCert (wordOf e.1 e.2.1) e.2.2.1 e.2.2.2) = true := by decide +kernel

def chunk5 : List (Nat × Nat × Nat × Nat) := [
    (15, 23, 8, 3),
    (15, 27, 6, 2),
    (15, 29, 9, 3),
    (15, 41, 8, 4),
    (15, 43, 6, 2),
    (15, 47, 6, 2)]

theorem chunk5_ok :
    chunk5.all (fun e => decide (1 ≤ e.2.2.1) && decide (0 < e.1) &&
      stripCert (wordOf e.1 e.2.1) e.2.2.1 e.2.2.2) = true := by decide +kernel

def chunk6 : List (Nat × Nat × Nat × Nat) := [
    (15, 51, 6, 2),
    (15, 67, 9, 3),
    (15, 91, 6, 3),
    (15, 107, 10, 5),
    (15, 123, 6, 2),
    (15, 379, 9, 3)]

theorem chunk6_ok :
    chunk6.all (fun e => decide (1 ≤ e.2.2.1) && decide (0 < e.1) &&
      stripCert (wordOf e.1 e.2.1) e.2.2.1 e.2.2.2) = true := by decide +kernel

def chunk7 : List (Nat × Nat × Nat × Nat) := [
    (15, 383, 10, 3),
    (15, 511, 5, 1),
    (15, 767, 5, 2),
    (15, 1023, 5, 1),
    (15, 1535, 5, 1),
    (15, 2047, 5, 1)]

theorem chunk7_ok :
    chunk7.all (fun e => decide (1 ≤ e.2.2.1) && decide (0 < e.1) &&
      stripCert (wordOf e.1 e.2.1) e.2.2.1 e.2.2.2) = true := by decide +kernel

def chunk8 : List (Nat × Nat × Nat × Nat) := [
    (15, 2559, 5, 1),
    (15, 3071, 5, 1),
    (15, 3583, 5, 1),
    (15, 4091, 5, 1),
    (15, 4095, 5, 1),
    (15, 5631, 5, 1)]

theorem chunk8_ok :
    chunk8.all (fun e => decide (1 ≤ e.2.2.1) && decide (0 < e.1) &&
      stripCert (wordOf e.1 e.2.1) e.2.2.1 e.2.2.2) = true := by decide +kernel

def chunk9 : List (Nat × Nat × Nat × Nat) := [
    (15, 6139, 6, 1),
    (15, 6143, 5, 1),
    (15, 7679, 5, 1),
    (15, 8187, 5, 1),
    (15, 8189, 5, 1),
    (15, 8191, 5, 1)]

theorem chunk9_ok :
    chunk9.all (fun e => decide (1 ≤ e.2.2.1) && decide (0 < e.1) &&
      stripCert (wordOf e.1 e.2.1) e.2.2.1 e.2.2.2) = true := by decide +kernel

def chunk10 : List (Nat × Nat × Nat × Nat) := [
    (15, 11775, 5, 1),
    (15, 12283, 5, 1),
    (15, 12287, 5, 1),
    (15, 14335, 5, 1),
    (15, 15359, 5, 1),
    (15, 16383, 5, 1)]

theorem chunk10_ok :
    chunk10.all (fun e => decide (1 ≤ e.2.2.1) && decide (0 < e.1) &&
      stripCert (wordOf e.1 e.2.1) e.2.2.1 e.2.2.2) = true := by decide +kernel

def chunk11 : List (Nat × Nat × Nat × Nat) := [
    (16, 1, 8, 2),
    (16, 3, 6, 2),
    (16, 5, 9, 2),
    (16, 11, 6, 2),
    (16, 13, 7, 2),
    (16, 15, 10, 2)]

theorem chunk11_ok :
    chunk11.all (fun e => decide (1 ≤ e.2.2.1) && decide (0 < e.1) &&
      stripCert (wordOf e.1 e.2.1) e.2.2.1 e.2.2.2) = true := by decide +kernel

def chunk12 : List (Nat × Nat × Nat × Nat) := [
    (16, 19, 6, 2),
    (16, 23, 8, 2),
    (16, 27, 6, 2),
    (16, 29, 9, 2),
    (16, 41, 8, 3),
    (16, 43, 9, 2)]

theorem chunk12_ok :
    chunk12.all (fun e => decide (1 ≤ e.2.2.1) && decide (0 < e.1) &&
      stripCert (wordOf e.1 e.2.1) e.2.2.1 e.2.2.2) = true := by decide +kernel

def chunk13 : List (Nat × Nat × Nat × Nat) := [
    (16, 47, 6, 2),
    (16, 51, 6, 2),
    (16, 55, 10, 3),
    (16, 67, 6, 2),
    (16, 83, 6, 2),
    (16, 91, 6, 2)]

theorem chunk13_ok :
    chunk13.all (fun e => decide (1 ≤ e.2.2.1) && decide (0 < e.1) &&
      stripCert (wordOf e.1 e.2.1) e.2.2.1 e.2.2.2) = true := by decide +kernel

def chunk14 : List (Nat × Nat × Nat × Nat) := [
    (16, 107, 10, 3),
    (16, 111, 7, 2),
    (16, 123, 6, 2),
    (16, 163, 7, 3),
    (16, 187, 9, 4),
    (16, 195, 9, 3)]

theorem chunk14_ok :
    chunk14.all (fun e => decide (1 ≤ e.2.2.1) && decide (0 < e.1) &&
      stripCert (wordOf e.1 e.2.1) e.2.2.1 e.2.2.2) = true := by decide +kernel

def chunk15 : List (Nat × Nat × Nat × Nat) := [
    (16, 219, 8, 3),
    (16, 367, 7, 3),
    (16, 379, 7, 3),
    (16, 383, 10, 3),
    (16, 511, 5, 1),
    (16, 767, 6, 2)]

theorem chunk15_ok :
    chunk15.all (fun e => decide (1 ≤ e.2.2.1) && decide (0 < e.1) &&
      stripCert (wordOf e.1 e.2.1) e.2.2.1 e.2.2.2) = true := by decide +kernel

def chunk16 : List (Nat × Nat × Nat × Nat) := [
    (16, 1023, 5, 1),
    (16, 1535, 5, 1),
    (16, 2047, 5, 1),
    (16, 2815, 5, 2),
    (16, 3071, 5, 1),
    (16, 4091, 5, 1)]

theorem chunk16_ok :
    chunk16.all (fun e => decide (1 ≤ e.2.2.1) && decide (0 < e.1) &&
      stripCert (wordOf e.1 e.2.1) e.2.2.1 e.2.2.2) = true := by decide +kernel

def chunk17 : List (Nat × Nat × Nat × Nat) := [
    (16, 4095, 5, 1),
    (16, 5119, 5, 1),
    (16, 6139, 6, 1),
    (16, 6143, 5, 1),
    (16, 6655, 5, 1),
    (16, 7167, 5, 1)]

theorem chunk17_ok :
    chunk17.all (fun e => decide (1 ≤ e.2.2.1) && decide (0 < e.1) &&
      stripCert (wordOf e.1 e.2.1) e.2.2.1 e.2.2.2) = true := by decide +kernel

def chunk18 : List (Nat × Nat × Nat × Nat) := [
    (16, 7679, 5, 1),
    (16, 8187, 5, 1),
    (16, 8191, 5, 1),
    (16, 11263, 5, 1),
    (16, 12283, 5, 1),
    (16, 12287, 5, 1)]

theorem chunk18_ok :
    chunk18.all (fun e => decide (1 ≤ e.2.2.1) && decide (0 < e.1) &&
      stripCert (wordOf e.1 e.2.1) e.2.2.1 e.2.2.2) = true := by decide +kernel

def chunk19 : List (Nat × Nat × Nat × Nat) := [
    (16, 15359, 5, 1),
    (16, 16379, 5, 1),
    (16, 16381, 5, 1),
    (16, 16383, 5, 1),
    (16, 23551, 5, 1),
    (16, 24571, 5, 1)]

theorem chunk19_ok :
    chunk19.all (fun e => decide (1 ≤ e.2.2.1) && decide (0 < e.1) &&
      stripCert (wordOf e.1 e.2.1) e.2.2.1 e.2.2.2) = true := by decide +kernel

def chunk20 : List (Nat × Nat × Nat × Nat) := [
    (16, 24575, 5, 1),
    (16, 28671, 5, 1),
    (16, 30719, 5, 1),
    (16, 32255, 5, 1),
    (16, 32767, 5, 1),
    (17, 1, 8, 2)]

theorem chunk20_ok :
    chunk20.all (fun e => decide (1 ≤ e.2.2.1) && decide (0 < e.1) &&
      stripCert (wordOf e.1 e.2.1) e.2.2.1 e.2.2.2) = true := by decide +kernel

def chunk21 : List (Nat × Nat × Nat × Nat) := [
    (17, 3, 6, 2),
    (17, 5, 9, 2),
    (17, 11, 6, 2),
    (17, 13, 7, 2),
    (17, 15, 10, 2),
    (17, 19, 6, 2)]

theorem chunk21_ok :
    chunk21.all (fun e => decide (1 ≤ e.2.2.1) && decide (0 < e.1) &&
      stripCert (wordOf e.1 e.2.1) e.2.2.1 e.2.2.2) = true := by decide +kernel

def chunk22 : List (Nat × Nat × Nat × Nat) := [
    (17, 23, 8, 2),
    (17, 27, 6, 2),
    (17, 29, 9, 2),
    (17, 41, 8, 2),
    (17, 43, 6, 2),
    (17, 47, 6, 2)]

theorem chunk22_ok :
    chunk22.all (fun e => decide (1 ≤ e.2.2.1) && decide (0 < e.1) &&
      stripCert (wordOf e.1 e.2.1) e.2.2.1 e.2.2.2) = true := by decide +kernel

def chunk23 : List (Nat × Nat × Nat × Nat) := [
    (17, 51, 6, 2),
    (17, 55, 8, 2),
    (17, 67, 6, 2),
    (17, 79, 10, 2),
    (17, 83, 6, 2),
    (17, 91, 6, 2)]

theorem chunk23_ok :
    chunk23.all (fun e => decide (1 ≤ e.2.2.1) && decide (0 < e.1) &&
      stripCert (wordOf e.1 e.2.1) e.2.2.1 e.2.2.2) = true := by decide +kernel

def chunk24 : List (Nat × Nat × Nat × Nat) := [
    (17, 111, 7, 2),
    (17, 123, 6, 2),
    (17, 163, 6, 2),
    (17, 167, 9, 4),
    (17, 185, 9, 3),
    (17, 187, 6, 2)]

theorem chunk24_ok :
    chunk24.all (fun e => decide (1 ≤ e.2.2.1) && decide (0 < e.1) &&
      stripCert (wordOf e.1 e.2.1) e.2.2.1 e.2.2.2) = true := by decide +kernel

def chunk25 : List (Nat × Nat × Nat × Nat) := [
    (17, 191, 8, 2),
    (17, 195, 6, 2),
    (17, 219, 6, 2),
    (17, 259, 9, 3),
    (17, 307, 9, 2),
    (17, 331, 6, 4)]

theorem chunk25_ok :
    chunk25.all (fun e => decide (1 ≤ e.2.2.1) && decide (0 < e.1) &&
      stripCert (wordOf e.1 e.2.1) e.2.2.1 e.2.2.2) = true := by decide +kernel

def chunk26 : List (Nat × Nat × Nat × Nat) := [
    (17, 347, 7, 3),
    (17, 355, 6, 2),
    (17, 367, 6, 3),
    (17, 379, 9, 3),
    (17, 383, 10, 2),
    (17, 419, 7, 3)]

theorem chunk26_ok :
    chunk26.all (fun e => decide (1 ≤ e.2.2.1) && decide (0 < e.1) &&
      stripCert (wordOf e.1 e.2.1) e.2.2.1 e.2.2.2) = true := by decide +kernel

def chunk27 : List (Nat × Nat × Nat × Nat) := [
    (17, 483, 6, 2),
    (17, 511, 5, 1),
    (17, 763, 7, 3),
    (17, 767, 5, 2),
    (17, 1023, 5, 1),
    (17, 1535, 5, 1)]

theorem chunk27_ok :
    chunk27.all (fun e => decide (1 ≤ e.2.2.1) && decide (0 < e.1) &&
      stripCert (wordOf e.1 e.2.1) e.2.2.1 e.2.2.2) = true := by decide +kernel

def chunk28 : List (Nat × Nat × Nat × Nat) := [
    (17, 2047, 5, 1),
    (17, 2559, 5, 1),
    (17, 3067, 6, 2),
    (17, 3071, 5, 1),
    (17, 3583, 5, 1),
    (17, 3839, 6, 2)]

theorem chunk28_ok :
    chunk28.all (fun e => decide (1 ≤ e.2.2.1) && decide (0 < e.1) &&
      stripCert (wordOf e.1 e.2.1) e.2.2.1 e.2.2.2) = true := by decide +kernel

def chunk29 : List (Nat × Nat × Nat × Nat) := [
    (17, 4091, 5, 1),
    (17, 4095, 5, 1),
    (17, 5631, 5, 1),
    (17, 6139, 6, 1),
    (17, 6143, 5, 1),
    (17, 7679, 5, 1)]

theorem chunk29_ok :
    chunk29.all (fun e => decide (1 ≤ e.2.2.1) && decide (0 < e.1) &&
      stripCert (wordOf e.1 e.2.1) e.2.2.1 e.2.2.2) = true := by decide +kernel

def chunk30 : List (Nat × Nat × Nat × Nat) := [
    (17, 8187, 5, 1),
    (17, 8191, 5, 1),
    (17, 10239, 5, 1),
    (17, 11775, 5, 1),
    (17, 12283, 5, 1),
    (17, 12287, 5, 1)]

theorem chunk30_ok :
    chunk30.all (fun e => decide (1 ≤ e.2.2.1) && decide (0 < e.1) &&
      stripCert (wordOf e.1 e.2.1) e.2.2.1 e.2.2.2) = true := by decide +kernel

def chunk31 : List (Nat × Nat × Nat × Nat) := [
    (17, 12799, 5, 1),
    (17, 13055, 6, 2),
    (17, 13311, 5, 1),
    (17, 13823, 5, 1),
    (17, 14335, 5, 1),
    (17, 15359, 5, 1)]

theorem chunk31_ok :
    chunk31.all (fun e => decide (1 ≤ e.2.2.1) && decide (0 < e.1) &&
      stripCert (wordOf e.1 e.2.1) e.2.2.1 e.2.2.2) = true := by decide +kernel

def chunk32 : List (Nat × Nat × Nat × Nat) := [
    (17, 16379, 5, 1),
    (17, 16383, 5, 1),
    (17, 22527, 5, 1),
    (17, 24063, 5, 1),
    (17, 24571, 5, 1),
    (17, 24575, 5, 1)]

theorem chunk32_ok :
    chunk32.all (fun e => decide (1 ≤ e.2.2.1) && decide (0 < e.1) &&
      stripCert (wordOf e.1 e.2.1) e.2.2.1 e.2.2.2) = true := by decide +kernel

def chunk33 : List (Nat × Nat × Nat × Nat) := [
    (17, 30719, 5, 1),
    (17, 32255, 5, 1),
    (17, 32763, 5, 1),
    (17, 32765, 5, 1),
    (17, 32767, 5, 1),
    (17, 47103, 5, 1)]

theorem chunk33_ok :
    chunk33.all (fun e => decide (1 ≤ e.2.2.1) && decide (0 < e.1) &&
      stripCert (wordOf e.1 e.2.1) e.2.2.1 e.2.2.2) = true := by decide +kernel

def chunk34 : List (Nat × Nat × Nat × Nat) := [
    (17, 48639, 5, 1),
    (17, 49147, 5, 1),
    (17, 49151, 5, 1),
    (17, 56831, 5, 1),
    (17, 57343, 5, 1),
    (17, 61439, 5, 1)]

theorem chunk34_ok :
    chunk34.all (fun e => decide (1 ≤ e.2.2.1) && decide (0 < e.1) &&
      stripCert (wordOf e.1 e.2.1) e.2.2.1 e.2.2.2) = true := by decide +kernel

def chunk35 : List (Nat × Nat × Nat × Nat) := [
    (17, 64511, 5, 1),
    (17, 65535, 5, 1),
    (18, 1, 8, 2),
    (18, 3, 6, 2),
    (18, 5, 9, 2),
    (18, 11, 6, 2)]

theorem chunk35_ok :
    chunk35.all (fun e => decide (1 ≤ e.2.2.1) && decide (0 < e.1) &&
      stripCert (wordOf e.1 e.2.1) e.2.2.1 e.2.2.2) = true := by decide +kernel

def chunk36 : List (Nat × Nat × Nat × Nat) := [
    (18, 13, 7, 2),
    (18, 15, 10, 2),
    (18, 19, 6, 2),
    (18, 23, 8, 2),
    (18, 27, 6, 2),
    (18, 29, 9, 2)]

theorem chunk36_ok :
    chunk36.all (fun e => decide (1 ≤ e.2.2.1) && decide (0 < e.1) &&
      stripCert (wordOf e.1 e.2.1) e.2.2.1 e.2.2.2) = true := by decide +kernel

def chunk37 : List (Nat × Nat × Nat × Nat) := [
    (18, 31, 10, 5),
    (18, 41, 8, 2),
    (18, 43, 6, 2),
    (18, 47, 6, 2),
    (18, 51, 6, 2),
    (18, 55, 8, 2)]

theorem chunk37_ok :
    chunk37.all (fun e => decide (1 ≤ e.2.2.1) && decide (0 < e.1) &&
      stripCert (wordOf e.1 e.2.1) e.2.2.1 e.2.2.2) = true := by decide +kernel

def chunk38 : List (Nat × Nat × Nat × Nat) := [
    (18, 67, 6, 2),
    (18, 79, 10, 2),
    (18, 83, 6, 2),
    (18, 91, 6, 2),
    (18, 105, 9, 4),
    (18, 107, 6, 2)]

theorem chunk38_ok :
    chunk38.all (fun e => decide (1 ≤ e.2.2.1) && decide (0 < e.1) &&
      stripCert (wordOf e.1 e.2.1) e.2.2.1 e.2.2.2) = true := by decide +kernel

def chunk39 : List (Nat × Nat × Nat × Nat) := [
    (18, 111, 7, 2),
    (18, 123, 6, 2),
    (18, 163, 6, 2),
    (18, 167, 8, 3),
    (18, 185, 6, 2),
    (18, 187, 6, 3)]

theorem chunk39_ok :
    chunk39.all (fun e => decide (1 ≤ e.2.2.1) && decide (0 < e.1) &&
      stripCert (wordOf e.1 e.2.1) e.2.2.1 e.2.2.2) = true := by decide +kernel

def chunk40 : List (Nat × Nat × Nat × Nat) := [
    (18, 191, 8, 2),
    (18, 195, 6, 2),
    (18, 219, 6, 2),
    (18, 259, 6, 2),
    (18, 307, 6, 2),
    (18, 331, 6, 3)]

theorem chunk40_ok :
    chunk40.all (fun e => decide (1 ≤ e.2.2.1) && decide (0 < e.1) &&
      stripCert (wordOf e.1 e.2.1) e.2.2.1 e.2.2.2) = true := by decide +kernel

def chunk41 : List (Nat × Nat × Nat × Nat) := [
    (18, 347, 6, 3),
    (18, 355, 6, 2),
    (18, 367, 6, 2),
    (18, 371, 6, 2),
    (18, 373, 10, 4),
    (18, 379, 6, 2)]

theorem chunk41_ok :
    chunk41.all (fun e => decide (1 ≤ e.2.2.1) && decide (0 < e.1) &&
      stripCert (wordOf e.1 e.2.1) e.2.2.1 e.2.2.2) = true := by decide +kernel

def chunk42 : List (Nat × Nat × Nat × Nat) := [
    (18, 383, 10, 2),
    (18, 419, 6, 2),
    (18, 443, 7, 3),
    (18, 447, 6, 2),
    (18, 483, 6, 2),
    (18, 511, 5, 1)]

theorem chunk42_ok :
    chunk42.all (fun e => decide (1 ≤ e.2.2.1) && decide (0 < e.1) &&
      stripCert (wordOf e.1 e.2.1) e.2.2.1 e.2.2.2) = true := by decide +kernel

def chunk43 : List (Nat × Nat × Nat × Nat) := [
    (18, 643, 7, 3),
    (18, 739, 6, 2),
    (18, 767, 6, 2),
    (18, 771, 9, 2),
    (18, 867, 8, 3),
    (18, 891, 9, 3)]

theorem chunk43_ok :
    chunk43.all (fun e => decide (1 ≤ e.2.2.1) && decide (0 < e.1) &&
      stripCert (wordOf e.1 e.2.1) e.2.2.1 e.2.2.2) = true := by decide +kernel

def chunk44 : List (Nat × Nat × Nat × Nat) := [
    (18, 1023, 5, 1),
    (18, 1531, 8, 2),
    (18, 1535, 5, 1),
    (18, 2047, 5, 1),
    (18, 2815, 5, 2),
    (18, 3067, 6, 2)]

theorem chunk44_ok :
    chunk44.all (fun e => decide (1 ≤ e.2.2.1) && decide (0 < e.1) &&
      stripCert (wordOf e.1 e.2.1) e.2.2.1 e.2.2.2) = true := by decide +kernel

def chunk45 : List (Nat × Nat × Nat × Nat) := [
    (18, 3071, 5, 1),
    (18, 4091, 5, 1),
    (18, 4095, 5, 1),
    (18, 5119, 5, 1),
    (18, 6139, 6, 1),
    (18, 6143, 5, 1)]

theorem chunk45_ok :
    chunk45.all (fun e => decide (1 ≤ e.2.2.1) && decide (0 < e.1) &&
      stripCert (wordOf e.1 e.2.1) e.2.2.1 e.2.2.2) = true := by decide +kernel

def chunk46 : List (Nat × Nat × Nat × Nat) := [
    (18, 6655, 5, 1),
    (18, 7167, 5, 1),
    (18, 7679, 5, 1),
    (18, 8187, 5, 1),
    (18, 8191, 5, 1),
    (18, 11263, 5, 1)]

theorem chunk46_ok :
    chunk46.all (fun e => decide (1 ≤ e.2.2.1) && decide (0 < e.1) &&
      stripCert (wordOf e.1 e.2.1) e.2.2.1 e.2.2.2) = true := by decide +kernel

def chunk47 : List (Nat × Nat × Nat × Nat) := [
    (18, 12283, 5, 1),
    (18, 12287, 5, 1),
    (18, 15359, 5, 1),
    (18, 16355, 5, 1),
    (18, 16379, 5, 1),
    (18, 16383, 5, 1)]

theorem chunk47_ok :
    chunk47.all (fun e => decide (1 ≤ e.2.2.1) && decide (0 < e.1) &&
      stripCert (wordOf e.1 e.2.1) e.2.2.1 e.2.2.2) = true := by decide +kernel

def chunk48 : List (Nat × Nat × Nat × Nat) := [
    (18, 20479, 5, 1),
    (18, 23551, 5, 1),
    (18, 24547, 6, 1),
    (18, 24571, 5, 1),
    (18, 24575, 5, 1),
    (18, 25599, 5, 1)]

theorem chunk48_ok :
    chunk48.all (fun e => decide (1 ≤ e.2.2.1) && decide (0 < e.1) &&
      stripCert (wordOf e.1 e.2.1) e.2.2.1 e.2.2.2) = true := by decide +kernel

def chunk49 : List (Nat × Nat × Nat × Nat) := [
    (18, 26111, 5, 1),
    (18, 26623, 5, 1),
    (18, 27647, 5, 1),
    (18, 28671, 5, 1),
    (18, 30719, 5, 1),
    (18, 32255, 5, 1)]

theorem chunk49_ok :
    chunk49.all (fun e => decide (1 ≤ e.2.2.1) && decide (0 < e.1) &&
      stripCert (wordOf e.1 e.2.1) e.2.2.1 e.2.2.2) = true := by decide +kernel

def chunk50 : List (Nat × Nat × Nat × Nat) := [
    (18, 32763, 5, 1),
    (18, 32767, 5, 1),
    (18, 45055, 5, 1),
    (18, 48127, 5, 1),
    (18, 49147, 5, 1),
    (18, 49151, 5, 1)]

theorem chunk50_ok :
    chunk50.all (fun e => decide (1 ≤ e.2.2.1) && decide (0 < e.1) &&
      stripCert (wordOf e.1 e.2.1) e.2.2.1 e.2.2.2) = true := by decide +kernel

def chunk51 : List (Nat × Nat × Nat × Nat) := [
    (18, 53247, 8, 3),
    (18, 61435, 5, 1),
    (18, 61439, 5, 1),
    (18, 64255, 5, 2),
    (18, 64511, 5, 1),
    (18, 65531, 5, 1)]

theorem chunk51_ok :
    chunk51.all (fun e => decide (1 ≤ e.2.2.1) && decide (0 < e.1) &&
      stripCert (wordOf e.1 e.2.1) e.2.2.1 e.2.2.2) = true := by decide +kernel

def chunk52 : List (Nat × Nat × Nat × Nat) := [
    (18, 65533, 5, 1),
    (18, 65535, 5, 1),
    (18, 94207, 5, 1),
    (18, 97279, 5, 1),
    (18, 98299, 5, 1),
    (18, 98303, 5, 1)]

theorem chunk52_ok :
    chunk52.all (fun e => decide (1 ≤ e.2.2.1) && decide (0 < e.1) &&
      stripCert (wordOf e.1 e.2.1) e.2.2.1 e.2.2.2) = true := by decide +kernel

def chunk53 : List (Nat × Nat × Nat × Nat) := [
    (18, 113663, 5, 1),
    (18, 114687, 5, 1),
    (18, 122879, 5, 1),
    (18, 129023, 5, 1),
    (18, 130559, 5, 1),
    (18, 131071, 5, 1)]

theorem chunk53_ok :
    chunk53.all (fun e => decide (1 ≤ e.2.2.1) && decide (0 < e.1) &&
      stripCert (wordOf e.1 e.2.1) e.2.2.1 e.2.2.2) = true := by decide +kernel

/-- All 324 entries, lengths 14 to 18, each word its least rotation. -/
def certTableTwo : List (Nat × Nat × Nat × Nat) :=
  chunk0 ++ chunk1 ++ chunk2 ++ chunk3 ++ chunk4 ++ chunk5 ++ chunk6 ++ chunk7 ++ chunk8 ++
    chunk9 ++ chunk10 ++ chunk11 ++ chunk12 ++ chunk13 ++ chunk14 ++ chunk15 ++ chunk16 ++
    chunk17 ++ chunk18 ++ chunk19 ++ chunk20 ++ chunk21 ++ chunk22 ++ chunk23 ++ chunk24 ++
    chunk25 ++ chunk26 ++ chunk27 ++ chunk28 ++ chunk29 ++ chunk30 ++ chunk31 ++ chunk32 ++
    chunk33 ++ chunk34 ++ chunk35 ++ chunk36 ++ chunk37 ++ chunk38 ++ chunk39 ++ chunk40 ++
    chunk41 ++ chunk42 ++ chunk43 ++ chunk44 ++ chunk45 ++ chunk46 ++ chunk47 ++ chunk48 ++
    chunk49 ++ chunk50 ++ chunk51 ++ chunk52 ++ chunk53

theorem certTableTwo_ok :
    certTableTwo.all (fun e => decide (1 ≤ e.2.2.1) && decide (0 < e.1) &&
      stripCert (wordOf e.1 e.2.1) e.2.2.1 e.2.2.2) = true := by
  simp only [certTableTwo, List.all_append, chunk0_ok, chunk1_ok, chunk2_ok, chunk3_ok,
    chunk4_ok, chunk5_ok, chunk6_ok, chunk7_ok, chunk8_ok, chunk9_ok, chunk10_ok, chunk11_ok,
    chunk12_ok, chunk13_ok, chunk14_ok, chunk15_ok, chunk16_ok, chunk17_ok, chunk18_ok,
    chunk19_ok, chunk20_ok, chunk21_ok, chunk22_ok, chunk23_ok, chunk24_ok, chunk25_ok,
    chunk26_ok, chunk27_ok, chunk28_ok, chunk29_ok, chunk30_ok, chunk31_ok, chunk32_ok,
    chunk33_ok, chunk34_ok, chunk35_ok, chunk36_ok, chunk37_ok, chunk38_ok, chunk39_ok,
    chunk40_ok, chunk41_ok, chunk42_ok, chunk43_ok, chunk44_ok, chunk45_ok, chunk46_ok,
    chunk47_ok, chunk48_ok, chunk49_ok, chunk50_ok, chunk51_ok, chunk52_ok, chunk53_ok,
    Bool.and_self]

/-- **Every word in the table is excluded** as an eventual repeating word of the center column. -/
theorem not_eventually_certTableTwo (e : Nat × Nat × Nat × Nat) (he : e ∈ certTableTwo) :
    ¬ EventuallyWord (wordOf e.1 e.2.1) := by
  have h := List.all_eq_true.mp certTableTwo_ok e he
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact not_eventually_word_strip (wordOf e.1 e.2.1) e.2.2.1 e.2.2.2 h.1.1
    (by rw [wordOf_length]; exact h.1.2) h.2

end Rule30StripCertificateTableTwo
end Ruliology.CellularAutomata
