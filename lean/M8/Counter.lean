import M8.Micro
namespace M8
open List

/-! # The left counter: ternary digits of 3 cells, `...` = 0, `11.` = 1, `1..` = 2 (MSB left).
Digit lists are LSB first; `rdig` is the digit's cells nearest-first (i.e. reversed). -/

inductive Dg | z | o | t
  deriving DecidableEq, Repr

def rdig : Dg → List Bool
  | .z => [false, false, false]
  | .o => [false, true, true]
  | .t => [false, false, true]

/-- counter cells as a left list (nearest first) -/
def Sr (ds : List Dg) : List Bool := ds.flatMap rdig

@[simp] theorem Sr_nil : Sr [] = [] := rfl
@[simp] theorem Sr_cons (d : Dg) (ds : List Dg) : Sr (d :: ds) = rdig d ++ Sr ds := by
  simp [Sr]

/-- ternary +1 (LSB first); the empty list is 0 -/
def inc : List Dg → List Dg
  | [] => [.o]
  | .z :: r => .o :: r
  | .o :: r => .t :: r
  | .t :: r => .z :: inc r

/-- number of trailing (low) digits 2 = carry length -/
def tz : List Dg → Nat
  | .t :: r => tz r + 1
  | _ => 0

/-- the counter has a digit that is not 2 (else pad with a leading `...` digit) -/
def lowOk : List Dg → Bool
  | [] => false
  | .t :: r => lowOk r
  | _ => true

def val : List Dg → Nat
  | [] => 0
  | d :: r => (match d with | .z => 0 | .o => 1 | .t => 2) + 3 * val r

theorem val_inc (ds : List Dg) : val (inc ds) = val ds + 1 := by
  induction ds with
  | nil => rfl
  | cons d r ih => cases d <;> simp [inc, val, ih] <;> omega

/-! ## digit events (kernel-checked windows) -/

/-- carry through a digit 2: `1..` -> `111`, continue left (3 steps) -/
theorem cdig2 (L R : List Bool) : run 3 (dc (rdig .t ++ L) R) = dc L ([true, true, true] ++ R) := by
  have h := frame (n := 2) (s := .D) (s' := .C) (L := [false, true]) (h := false)
    (R := []) (L' := []) (h' := true) (R' := [true, true]) L R (by decide)
  rw [show 3 = 2 + 1 from rfl, run_add]
  simp only [dc, rdig, List.cons_append, List.nil_append, List.tail_cons, List.headD_cons] at h ⊢
  rw [h, cstep]; rfl

/-- digit 0 absorbs the carry: `...` -> `11.`, A leaves to the right (5 steps) -/
theorem cdig0 (L R : List Bool) : run 5 (dc (rdig .z ++ L) R) = ac (rdig .o ++ L) R := by
  have h := frame (n := 4) (s := .D) (s' := .A) (L := [false, false]) (h := false)
    (R := []) (L' := [true, true]) (h' := true) (R' := []) L R (by decide)
  rw [show 5 = 4 + 1 from rfl, run_add]
  simp only [dc, rdig, List.cons_append, List.nil_append, List.tail_cons, List.headD_cons] at h ⊢
  rw [h, astep]

/-- digit 1 absorbs the carry: `11.` -> `1..` (5 steps) -/
theorem cdig1 (L R : List Bool) : run 5 (dc (rdig .o ++ L) R) = ac (rdig .t ++ L) R := by
  have h := frame (n := 4) (s := .D) (s' := .A) (L := [true, true]) (h := false)
    (R := []) (L' := [false, true]) (h' := true) (R' := []) L R (by decide)
  rw [show 5 = 4 + 1 from rfl, run_add]
  simp only [dc, rdig, List.cons_append, List.nil_append, List.tail_cons, List.headD_cons] at h ⊢
  rw [h, astep]

/-- A erases a carried `111` back to `...` (3 steps) -/
theorem erase (L R : List Bool) : run 3 (ac L ([true, true, true] ++ R)) = ac ([false, false, false] ++ L) R := by
  show run 1 (run 1 (run 1 ⟨.A, L, true, [true, true] ++ R⟩)) = _
  rfl

/-- the counter increment: from D on the last cell of the counter to A just right of it -/
theorem cnt (ds : List Dg) (hok : lowOk ds = true) (L R : List Bool) :
    run (6 * tz ds + 5) (dc (Sr ds ++ L) R) = ac (Sr (inc ds) ++ L) R := by
  induction ds generalizing R with
  | nil => simp [lowOk] at hok
  | cons d r ih =>
    cases d with
    | z => simpa [tz, inc, List.append_assoc] using cdig0 (Sr r ++ L) R
    | o => simpa [tz, inc, List.append_assoc] using cdig1 (Sr r ++ L) R
    | t =>
      simp only [lowOk] at hok
      simp only [tz, inc, Sr_cons, List.append_assoc]
      rw [show 6 * (tz r + 1) + 5 = 3 + (6 * tz r + 5) + 3 by omega, run_add, run_add, cdig2,
        ih hok, erase]
      rfl

/-- new top digit: an all-2 counter followed by (at least) 3 blank cells -/
theorem cnt_top (n : Nat) (L R : List Bool) :
    run (6 * n + 5) (dc (Sr (List.replicate n .t) ++ [false, false, false] ++ L) R)
      = ac (Sr (inc (List.replicate n .t)) ++ L) R := by
  have key : ∀ n, Sr (List.replicate n .t) ++ [false, false, false] = Sr (List.replicate n .t ++ [.z])
      ∧ tz (List.replicate n .t ++ [.z]) = n ∧ lowOk (List.replicate n .t ++ [.z]) = true
      ∧ inc (List.replicate n .t ++ [.z]) = inc (List.replicate n .t) := by
    intro n
    induction n with
    | zero => simp [Sr, rdig, tz, lowOk, inc]
    | succ n ih =>
      obtain ⟨h1, h2, h3, h4⟩ := ih
      refine ⟨?_, ?_, ?_, ?_⟩
      · simp only [List.replicate_succ, List.cons_append, Sr_cons, List.append_assoc] at h1 ⊢
        rw [h1]
      · simp [List.replicate_succ, tz, h2]
      · simp [List.replicate_succ, lowOk, h3]
      · simp [List.replicate_succ, inc, h4]
  obtain ⟨h1, h2, h3, h4⟩ := key n
  rw [h1, ← h4, ← cnt _ h3, h2]

end M8
