import M8.Machine
import M8.Frame
namespace M8
open List

/-! # Micro layer: units, sweeps, separator passes, the turn.
Tape order (left to right) of a unit: L-phase `.111` = `Lu`, R-phase `11..` (stored reversed in
left lists as `Rr`), marker `1111..` (reversed: `Mr`) = a passed `1.` separator. -/

def Lu : List Bool := [false, true, true, true]
def Rr : List Bool := [false, false, true, true]
def Mr : List Bool := [false, false, true, true, true, true]

/-- `n` copies of `l` -/
def pw (l : List Bool) : Nat → List Bool
  | 0 => []
  | n + 1 => l ++ pw l n

@[simp] theorem pw_zero (l : List Bool) : pw l 0 = [] := rfl
@[simp] theorem pw_succ (l : List Bool) (n : Nat) : pw l (n + 1) = l ++ pw l n := rfl

theorem pw_add (l : List Bool) (m n : Nat) : pw l (m + n) = pw l m ++ pw l n := by
  induction m with
  | zero => simp
  | succ m ih => rw [Nat.succ_add, pw_succ, pw_succ, ih, List.append_assoc]

theorem pw_succ' (l : List Bool) (n : Nat) : pw l (n + 1) = pw l n ++ l := by
  rw [pw_add]; simp

/-- right-sweep configuration: the carried unit `1111` with the head (state B) on its 2nd cell;
`P` = cells left of it (nearest first), `R` = cells after it -/
def hc (P R : List Bool) : Cfg := ⟨.B, true :: P, true, [true, true] ++ R⟩
/-- left-sweep configuration: state D on the first cell of `L` -/
def dc (L R : List Bool) : Cfg := ⟨.D, L.tail, L.headD false, R⟩
/-- state A on the first cell of `R` -/
def ac (L R : List Bool) : Cfg := ⟨.A, L, R.headD false, R.tail⟩

/-! ## last steps into unknown territory (hold for every tape) -/
theorem dstep (L R : List Bool) : run 1 ⟨.D, L, true, R⟩ = dc L (false :: R) := rfl
theorem cstep (L R : List Bool) : run 1 ⟨.C, L, true, R⟩ = dc L (true :: R) := rfl
theorem astep (L R : List Bool) : run 1 ⟨.A, L, true, R⟩ = ac (false :: L) R := rfl
theorem restart (L R : List Bool) : run 1 (ac L (Lu ++ R)) = hc L R := rfl

/-! ## kernel-checked windows -/

/-- right sweep, one unit: `1111 .111` -> `11.. 1111` (18 steps) -/
theorem unit (P R : List Bool) : run 18 (hc P (Lu ++ R)) = hc (Rr ++ P) R := by
  have h := frame (n := 18) (s := .B) (s' := .B) (L := [true]) (h := true)
    (R := [true, true, false, true, true, true]) (L' := [true, false, false, true, true]) (h' := true)
    (R' := [true, true]) P R (by decide)
  simpa [hc, Lu, Rr] using h

/-- right sweep passes a `1.` separator: `11.. 1111 1.` -> `1111 .. 1111` (36 steps);
it peeks at the cell after the separator, which must be `0` -/
theorem pass (P R : List Bool) :
    run 36 (hc (Rr ++ P) ([true, false] ++ false :: R)) = hc (Mr ++ P) (false :: R) := by
  have h := frame (n := 36) (s := .B) (s' := .B) (L := [true, false, false, true, true]) (h := true)
    (R := [true, true, true, false, false]) (L' := [true, false, false, true, true, true, true]) (h' := true)
    (R' := [true, true, false]) P R (by decide)
  simpa [hc, Mr, Rr] using h

/-- the turn at a `..` separator: `1111 ..` -> `.111 1.`, head back on the cell left of it (24 steps) -/
theorem turn (P X : List Bool) :
    run 24 (hc P ([false, false] ++ X)) = dc P (Lu ++ [true, false] ++ X) := by
  have h := frame (n := 23) (s := .B) (s' := .D) (L := [true]) (h := true)
    (R := [true, true, false, false]) (L' := []) (h' := true)
    (R' := [true, true, true, true, false]) P X (by decide)
  rw [show 24 = 23 + 1 from rfl, run_add]
  simp only [hc, List.cons_append, List.nil_append] at h ⊢
  rw [h, dstep]; rfl

/-- left sweep, one unit: `11..` -> `.111` (4 steps) -/
theorem lunit (L R : List Bool) : run 4 (dc (Rr ++ L) R) = dc L (Lu ++ R) := by
  have h := frame (n := 3) (s := .D) (s' := .D) (L := [false, true, true]) (h := false)
    (R := []) (L' := []) (h' := true) (R' := [true, true, true]) L R (by decide)
  rw [show 4 = 3 + 1 from rfl, run_add]
  simp only [dc, Rr, List.cons_append, List.nil_append, List.tail_cons, List.headD_cons] at h ⊢
  rw [h, dstep]; rfl

/-- left sweep over a marker: `1111..` -> `.. .111` (6 steps): the separator lands 2 units left -/
theorem lmark (L R : List Bool) : run 6 (dc (Mr ++ L) R) = dc L ([false, false] ++ Lu ++ R) := by
  have h := frame (n := 5) (s := .D) (s' := .D) (L := [false, true, true, true, true]) (h := false)
    (R := []) (L' := []) (h' := true) (R' := [false, false, true, true, true]) L R (by decide)
  rw [show 6 = 5 + 1 from rfl, run_add]
  simp only [dc, Mr, List.cons_append, List.nil_append, List.tail_cons, List.headD_cons] at h ⊢
  rw [h, dstep]; rfl

/-! ## sweeps -/

theorem rsweep (n : Nat) (P R : List Bool) :
    run (18 * n) (hc P (pw Lu n ++ R)) = hc (pw Rr n ++ P) R := by
  induction n generalizing P with
  | zero => rfl
  | succ n ih =>
    rw [Nat.mul_succ, Nat.add_comm, run_add, pw_succ, List.append_assoc, unit, ih,
      pw_succ', List.append_assoc]

theorem lsweep (n : Nat) (L R : List Bool) :
    run (4 * n) (dc (pw Rr n ++ L) R) = dc L (pw Lu n ++ R) := by
  induction n generalizing R with
  | zero => rfl
  | succ n ih =>
    rw [Nat.mul_succ, Nat.add_comm, run_add, pw_succ, List.append_assoc, lunit, ih, pw_succ', List.append_assoc]

end M8
