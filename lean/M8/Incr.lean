import M8.Micro
import M8.Counter
namespace M8
open List

/-! # The increment: canonical checkpoint -> canonical checkpoint.
Checkpoint: `hc (Rr^k ++ Sr ds ++ Lt) (Lu^m ++ rtt bs ([f,f] ++ X))`:
counter `ds`, first block `B1 = k+1+m` (k units already R-phase, the carried unit, m L-phase),
then separators `1.` each followed by a block `b ∈ bs`, then the first `..` separator. -/

/-- the `1.`-separated blocks `bs` followed by `R` -/
def rtt : List Nat → List Bool → List Bool
  | [], R => R
  | b :: bs, R => [true, false] ++ pw Lu b ++ rtt bs R

/-- left list after the right sweep has passed the blocks `bs` (markers where the seps were) -/
def Q : List Nat → List Bool → List Bool
  | [], P => P
  | b :: bs, P => Q bs (pw Rr (b - 1) ++ Mr ++ P)

/-- the blocks after the increment: separators now `..` -/
def E : List Nat → List Bool
  | [] => []
  | b :: bs => [false, false] ++ pw Lu b ++ E bs

def swT : List Nat → Nat
  | [] => 0
  | b :: bs => 36 + 18 * b + swT bs

def lqT : List Nat → Nat
  | [] => 0
  | b :: bs => lqT bs + 4 * (b - 1) + 6

theorem swT_eq (bs : List Nat) : swT bs = 36 * bs.length + 18 * bs.sum := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [swT, ih]; omega

theorem lqT_eq (bs : List Nat) (hb : ∀ b ∈ bs, 1 ≤ b) : lqT bs = 4 * bs.sum + 2 * bs.length := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    have h1 := hb b (by simp)
    have := ih (fun x hx => hb x (by simp [hx]))
    simp [lqT, this]; omega

/-- right sweep through the `1.`-separated blocks -/
theorem swp (bs : List Nat) (hb : ∀ b ∈ bs, 1 ≤ b) (P R : List Bool) :
    run (swT bs) (hc (Rr ++ P) (rtt bs R)) = hc (Rr ++ Q bs P) R := by
  induction bs generalizing P with
  | nil => rfl
  | cons b bs ih =>
    obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by have := hb b (by simp); omega⟩
    have ih' := ih (fun x hx => hb x (by simp [hx]))
    simp only [swT, rtt, Q, Nat.add_sub_cancel]
    rw [run_add, run_add]
    have e : [true, false] ++ pw Lu (b' + 1) ++ rtt bs R
        = [true, false] ++ false :: ([true, true, true] ++ pw Lu b' ++ rtt bs R) := by
      simp [Lu]
    rw [e, pass]
    have e2 : false :: ([true, true, true] ++ pw Lu b' ++ rtt bs R) = pw Lu (b' + 1) ++ rtt bs R := by
      simp [Lu]
    rw [e2, rsweep, pw_succ, List.append_assoc, ih']
    simp [List.append_assoc]

/-- left sweep back over the passed blocks -/
theorem lqp (bs : List Nat) (hb : ∀ b ∈ bs, 1 ≤ b) (P R : List Bool) :
    run (lqT bs) (dc (Q bs P) R) = dc P (E bs ++ R) := by
  induction bs generalizing P R with
  | nil => rfl
  | cons b bs ih =>
    obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by have := hb b (by simp); omega⟩
    have ih' := ih (fun x hx => hb x (by simp [hx]))
    simp only [lqT, Q, E, Nat.add_sub_cancel]
    rw [run_add, run_add, ih', List.append_assoc, lsweep, lmark]
    simp [pw_succ, List.append_assoc]

/-- start of an increment: sweep the rest of block 1 and all `1.`-blocks -/
theorem start (bs : List Nat) (hb : ∀ b ∈ bs, 1 ≤ b) (k m n : Nat) (hn : m + k = n + 1)
    (S R : List Bool) :
    run (18 * m + swT bs) (hc (pw Rr k ++ S) (pw Lu m ++ rtt bs R))
      = hc (Rr ++ Q bs (pw Rr n ++ S)) R := by
  rw [run_add, rsweep, ← List.append_assoc, ← pw_add, hn, pw_succ, List.append_assoc, swp bs hb]

/-- end of an increment: left sweep, counter, restart, sweep `k'` units -/
theorem finish (bs : List Nat) (hb : ∀ b ∈ bs, 1 ≤ b) (ds : List Dg) (hok : lowOk ds = true)
    (k' m' : Nat) (Lt R : List Bool) :
    run (lqT bs + 4 * (k' + 1 + m') + (6 * tz ds + 5) + 1 + 18 * k')
        (dc (Q bs (pw Rr (k' + 1 + m') ++ (Sr ds ++ Lt))) R)
      = hc (pw Rr k' ++ (Sr (inc ds) ++ Lt)) (pw Lu m' ++ (E bs ++ R)) := by
  rw [run_add _ (18 * k'), run_add _ 1, run_add _ (6 * tz ds + 5), run_add (lqT bs), lqp bs hb,
    lsweep, cnt ds hok]
  rw [show k' + 1 + m' = (k' + m') + 1 by omega, pw_succ, List.append_assoc, restart, pw_add,
    List.append_assoc, rsweep]

/-- **Increment lemma** (first `..` separator after the blocks `bs`), for arbitrary `k`, `k'`. -/
theorem incr (ds : List Dg) (hok : lowOk ds = true) (bs : List Nat) (hb : ∀ b ∈ bs, 1 ≤ b)
    (k m k' m' : Nat) (hkm : k + m = k' + m' + 2) (Lt X : List Bool) :
    run (22 * m + 22 * bs.sum + 38 * bs.length + 4 * k + 30 + 6 * tz ds + 18 * k')
        (hc (pw Rr k ++ Sr ds ++ Lt) (pw Lu m ++ rtt bs ([false, false] ++ X)))
      = hc (pw Rr k' ++ Sr (inc ds) ++ Lt)
          (pw Lu m' ++ E bs ++ pw Lu 2 ++ [true, false] ++ X) := by
  have e : 22 * m + 22 * bs.sum + 38 * bs.length + 4 * k + 30 + 6 * tz ds + 18 * k'
      = (18 * m + swT bs) + (24 + (4 + (lqT bs + 4 * (k' + 1 + m') + (6 * tz ds + 5) + 1 + 18 * k'))) := by
    rw [swT_eq, lqT_eq bs hb]; omega
  rw [e, run_add, List.append_assoc, start bs hb k m (k' + 1 + m') (by omega), run_add, turn,
    run_add, lunit, finish bs hb ds hok k' m' Lt]
  simp [List.append_assoc, Lu]

/-- **Overflow lemma**: all separators are `1.`, the last one being the terminal `1.` followed by
blank (`[f,f] ++ X`); the ladder gains a block 2 and keeps a terminal `1.`. -/
theorem ovf (ds : List Dg) (hok : lowOk ds = true) (bs : List Nat) (hb : ∀ b ∈ bs, 1 ≤ b)
    (k m k' m' : Nat) (hkm : k + m = k' + m' + 2) (Lt X : List Bool) :
    run (22 * m + 22 * bs.sum + 38 * (bs.length + 1) + 4 * k + 30 + 6 * tz ds + 18 * k')
        (hc (pw Rr k ++ Sr ds ++ Lt) (pw Lu m ++ rtt bs ([true, false] ++ [false, false] ++ X)))
      = hc (pw Rr k' ++ Sr (inc ds) ++ Lt)
          (pw Lu m' ++ E bs ++ [false, false] ++ pw Lu 2 ++ [true, false] ++ X) := by
  have e : 22 * m + 22 * bs.sum + 38 * (bs.length + 1) + 4 * k + 30 + 6 * tz ds + 18 * k'
      = (18 * m + swT bs) + (36 + (24 + (6 + (lqT bs + 4 * (k' + 1 + m') + (6 * tz ds + 5) + 1 + 18 * k')))) := by
    rw [swT_eq, lqT_eq bs hb]; omega
  rw [e, run_add, List.append_assoc, start bs hb k m (k' + 1 + m') (by omega), run_add]
  rw [show [true, false] ++ [false, false] ++ X = [true, false] ++ false :: (false :: X) by rfl, pass,
    run_add, show false :: false :: X = [false, false] ++ X by rfl, turn, run_add, lmark,
    finish bs hb ds hok k' m' Lt]
  simp [List.append_assoc, Lu]

/-! ## Canonical form (m8/exact/NOTES.md): `k = 3 - min(z,3)`, `k' = 3 - min(tz,3)`, and the
step count `22W + 38j + 8 + 18 min(z,3) - 12 tz + 18 max(0, tz-3)`, `W = B1 + Σ bs`, `j = |bs|`. -/

/-- trailing zero digits -/
def zz : List Dg → Nat
  | .z :: r => zz r + 1
  | _ => 0

def kc (ds : List Dg) : Nat := 3 - min (zz ds) 3

/-- the canonical checkpoint with first block `B1` -/
def ck (ds : List Dg) (B1 : Nat) (T : List Bool) : Cfg :=
  hc (pw Rr (kc ds) ++ Sr ds ++ []) (pw Lu (B1 - kc ds - 1) ++ T)

theorem kc_inc (ds : List Dg) (hok : lowOk ds = true) : kc (inc ds) = 3 - min (tz ds) 3 := by
  unfold kc; congr 2
  induction ds with
  | nil => simp [lowOk] at hok
  | cons d r ih =>
    cases d with
    | z => rfl
    | o => rfl
    | t => simp only [lowOk] at hok; simp [inc, tz, zz, ih hok]

theorem incr_canon (ds : List Dg) (hok : lowOk ds = true) (bs : List Nat) (hb : ∀ b ∈ bs, 1 ≤ b)
    (B1 : Nat) (hB : 6 ≤ B1) (X : List Bool) :
    run (22 * (B1 + bs.sum) + 38 * bs.length + 8 + 18 * min (zz ds) 3 + 18 * (tz ds - 3) - 12 * tz ds)
        (ck ds B1 (rtt bs ([false, false] ++ X)))
      = ck (inc ds) (if bs = [] then B1 else B1 - 2)
          (E bs ++ (if bs = [] then [] else pw Lu 2) ++ [true, false] ++ X) := by
  have hk := kc_inc ds hok
  have h1 : kc ds ≤ 3 := by unfold kc; omega
  have h2 : kc (inc ds) ≤ 3 := by rw [hk]; omega
  have h := incr ds hok bs hb (kc ds) (B1 - kc ds - 1) (kc (inc ds)) (B1 - kc ds - 1 + kc ds - kc (inc ds) - 2)
    (by omega) [] X
  have et : 22 * (B1 + bs.sum) + 38 * bs.length + 8 + 18 * min (zz ds) 3 + 18 * (tz ds - 3) - 12 * tz ds
      = 22 * (B1 - kc ds - 1) + 22 * bs.sum + 38 * bs.length + 4 * kc ds + 30 + 6 * tz ds + 18 * kc (inc ds) := by
    rw [hk]; unfold kc; omega
  unfold ck; rw [et, h]
  by_cases hbs : bs = []
  · subst hbs
    simp only [if_true, E, List.nil_append, List.append_nil]
    rw [show B1 - kc (inc ds) - 1 = (B1 - kc ds - 1 + kc ds - kc (inc ds) - 2) + 2 by omega, pw_add]
    simp [List.append_assoc]
  · simp only [hbs, if_false, List.append_nil]
    rw [show B1 - 2 - kc (inc ds) - 1 = B1 - kc ds - 1 + kc ds - kc (inc ds) - 2 by omega]
    simp [List.append_assoc]

/-- canonical overflow: ladder `B1 :: bs`, all separators `1.` (the last = terminal, then blank);
`r = |bs| + 1` blocks; step count `22 Σblocks + 38 r + (same counter term)`. -/
theorem ovf_canon (ds : List Dg) (hok : lowOk ds = true) (bs : List Nat) (hb : ∀ b ∈ bs, 1 ≤ b)
    (B1 : Nat) (hB : 6 ≤ B1) (X : List Bool) :
    run (22 * (B1 + bs.sum) + 38 * (bs.length + 1) + 8 + 18 * min (zz ds) 3 + 18 * (tz ds - 3) - 12 * tz ds)
        (ck ds B1 (rtt bs ([true, false] ++ [false, false] ++ X)))
      = ck (inc ds) (B1 - 2) (E bs ++ [false, false] ++ pw Lu 2 ++ [true, false] ++ X) := by
  have hk := kc_inc ds hok
  have h1 : kc ds ≤ 3 := by unfold kc; omega
  have h2 : kc (inc ds) ≤ 3 := by rw [hk]; omega
  have h := ovf ds hok bs hb (kc ds) (B1 - kc ds - 1) (kc (inc ds)) (B1 - kc ds - 1 + kc ds - kc (inc ds) - 2)
    (by omega) [] X
  have et : 22 * (B1 + bs.sum) + 38 * (bs.length + 1) + 8 + 18 * min (zz ds) 3 + 18 * (tz ds - 3) - 12 * tz ds
      = 22 * (B1 - kc ds - 1) + 22 * bs.sum + 38 * (bs.length + 1) + 4 * kc ds + 30 + 6 * tz ds
        + 18 * kc (inc ds) := by
    rw [hk]; unfold kc; omega
  unfold ck; rw [et, h]
  rw [show B1 - 2 - kc (inc ds) - 1 = B1 - kc ds - 1 + kc ds - kc (inc ds) - 2 by omega]
  simp [List.append_assoc]

end M8
