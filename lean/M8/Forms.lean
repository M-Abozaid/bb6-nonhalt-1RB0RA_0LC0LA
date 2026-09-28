import M8.Incr
import M8.Pad
namespace M8
open List

/-! # Counter forms and the counter phase (plan step 7)
Counter cells are a left list (nearest first). Forms:
* clean   `Sr ds`
* lone-1  `Sr lo ++ [t] ++ Sr hi`  (one extra cell `1` between the low digits `lo` and the high
  digits `hi`; the notes' "pad"/"lone leading 1" forms are this with an `f`-cell re-read, see `xf`).
Counter phase = from `D` on the first counter cell (left sweep arrived) to the next right-sweep
configuration.  Events:
* `cnt`          clean / low part has a non-2 digit (Counter.lean; frame the rest)
* `realign`      lone-1, `lo = 2^(n+1)`: the carry kills the lone cell, `hi` is incremented, the low
                 cells become zeros and one unit `11..` is released (B1 += 1)
* `realign0`     lone-1, `lo = []`: `hi` is incremented twice, lone cell becomes `f`. -/

/-- sequential composition of runs -/
theorem run_trans {a b : Nat} {c c' c'' : Cfg} (h1 : run a c = c') (h2 : run b c' = c'') :
    run (a + b) c = c'' := by rw [run_add, h1, h2]

theorem rep_add {α} (a : α) (m n : Nat) : List.replicate (m + n) a = List.replicate m a ++ List.replicate n a :=
  List.replicate_append_replicate.symm

def T3 : List Bool := [true, true, true]
def F3 : List Bool := [false, false, false]

/-- carry through `n` digits 2 -/
theorem carry2 (n : Nat) (L R : List Bool) :
    run (3 * n) (dc (Sr (List.replicate n Dg.t) ++ L) R) = dc L (pw T3 n ++ R) := by
  induction n generalizing R with
  | zero => rfl
  | succ n ih =>
    rw [show 3 * (n + 1) = 3 + 3 * n by omega, run_add, List.replicate_succ, Sr_cons,
      List.append_assoc, cdig2, ih, pw_succ', List.append_assoc]
    rfl

/-- the zipper: `A` on a hole followed by ones moves right one cell per 3 steps, leaving blanks -/
theorem zip1 (L R : List Bool) :
    run 3 ⟨.A, L, false, true :: R⟩ = ⟨.A, false :: L, false, R⟩ := rfl

theorem zip (n : Nat) (L R : List Bool) :
    run (3 * n) ⟨.A, L, false, List.replicate n true ++ R⟩
      = ⟨.A, List.replicate n false ++ L, false, R⟩ := by
  induction n generalizing L with
  | zero => rfl
  | succ n ih =>
    rw [show 3 * (n + 1) = 3 + 3 * n by omega, run_add, List.replicate_succ, List.cons_append, zip1, ih,
      List.replicate_succ', List.append_assoc]
    rfl

theorem pw_T3 (n : Nat) : pw T3 n = List.replicate (3 * n) true := by
  induction n with
  | zero => rfl
  | succ n ih => rw [pw_succ, ih, show 3 * (n + 1) = 3 + 3 * n by omega, rep_add]; rfl

theorem Sr_zeros (n : Nat) : Sr (List.replicate n Dg.z) = List.replicate (3 * n) false := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ, Sr_cons, ih, show 3 * (n + 1) = 3 + 3 * n by omega, rep_add]; rfl

/-- end of the realignment: `A` on the last zipped cell, three blanks behind it, a `Lu` ahead -/
theorem realign_end (L R : List Bool) :
    run 10 ⟨.A, F3 ++ L, false, Lu ++ R⟩ = hc (Rr ++ L) R := by
  have h := frame (n := 10) (s := .A) (s' := .B) (L := [false, false, false]) (h := false)
    (R := [false, true, true, true]) (L' := [true, false, false, true, true]) (h' := true)
    (R' := [true, true]) L R (by decide)
  simpa [hc, F3, Lu, Rr] using h

/-- **realignment** (lone-1 form, low part = `n+1` digits 2): one unit is released -/
theorem realign (n : Nat) (hi : List Dg) (hok : lowOk hi = true) (L R : List Bool) :
    run (3 * (n + 1) + (1 + ((6 * tz hi + 5) + (3 * (3 * (n + 1)) + 10))))
        (dc (Sr (List.replicate (n + 1) Dg.t) ++ [true] ++ Sr hi ++ L) (Lu ++ R))
      = hc (Rr ++ Sr (List.replicate n Dg.z) ++ Sr (inc hi) ++ L) R := by
  have s0 := carry2 (n + 1) ([true] ++ Sr hi ++ L) (Lu ++ R)
  have s1 : run 1 (dc ([true] ++ Sr hi ++ L) (pw T3 (n + 1) ++ (Lu ++ R)))
      = dc (Sr hi ++ L) (false :: (pw T3 (n + 1) ++ (Lu ++ R))) := rfl
  have s2 := cnt hi hok L (false :: (pw T3 (n + 1) ++ (Lu ++ R)))
  have e2 : ac (Sr (inc hi) ++ L) (false :: (pw T3 (n + 1) ++ (Lu ++ R)))
      = ⟨.A, Sr (inc hi) ++ L, false, List.replicate (3 * (n + 1)) true ++ (Lu ++ R)⟩ := by
    simp only [ac, List.headD_cons, List.tail_cons, pw_T3]
  have s3 := zip (3 * (n + 1)) (Sr (inc hi) ++ L) (Lu ++ R)
  have e3 : List.replicate (3 * (n + 1)) false ++ (Sr (inc hi) ++ L)
      = F3 ++ (Sr (List.replicate n Dg.z) ++ Sr (inc hi) ++ L) := by
    rw [Sr_zeros, show 3 * (n + 1) = 3 + 3 * n by omega, rep_add]; simp [F3]
  have s4 := realign_end (Sr (List.replicate n Dg.z) ++ Sr (inc hi) ++ L) R
  refine run_trans (by simpa [List.append_assoc] using s0) (run_trans s1 (run_trans s2 ?_))
  rw [e2]; refine run_trans s3 ?_
  rw [e3]; simpa [List.append_assoc] using s4

/-- **realignment, empty low part**: the high part is incremented twice -/
theorem realign0 (hi : List Dg) (hok : lowOk hi = true) (hok' : lowOk (inc hi) = true)
    (L R : List Bool) :
    run (1 + ((6 * tz hi + 5) + (3 + ((6 * tz (inc hi) + 5) + (1 + 1)))))
        (dc ([true] ++ Sr hi ++ L) (Lu ++ R))
      = hc ([false] ++ Sr (inc (inc hi)) ++ L) R := by
  have s1 : run 1 (dc ([true] ++ Sr hi ++ L) (Lu ++ R)) = dc (Sr hi ++ L) (false :: (Lu ++ R)) := rfl
  have s2 := cnt hi hok L (false :: (Lu ++ R))
  have s3 : run 3 (ac (Sr (inc hi) ++ L) (false :: (Lu ++ R)))
      = dc (Sr (inc hi) ++ L) ([true] ++ (Lu ++ R)) := rfl
  have s4 := cnt (inc hi) hok' L ([true] ++ (Lu ++ R))
  have s5 : run 1 (ac (Sr (inc (inc hi)) ++ L) ([true] ++ (Lu ++ R)))
      = ac ([false] ++ Sr (inc (inc hi)) ++ L) (Lu ++ R) := rfl
  have s6 := restart ([false] ++ Sr (inc (inc hi)) ++ L) R
  exact run_trans s1 (run_trans s2 (run_trans s3 (run_trans s4 (run_trans s5 s6))))

/-! ## the absorption micro-events (plan step 6) -/

/-- `A` lands on the cleared `..` separator: writes `1.` and re-enters the counter -/
theorem absHead (L X : List Bool) :
    run 3 (ac L ([false, false] ++ X)) = dc L ([true, false] ++ X) := rfl

/-- absorption tail, low digit 0 or 2 after the double increment (`c3` = its third cell) -/
theorem absTailZ (L R : List Bool) :
    run 11 ⟨.A, rdig .z ++ L, true, [false] ++ Lu ++ R⟩ = hc (Rr ++ [false] ++ L) R := by
  have h := frame (n := 11) (s := .A) (s' := .B) (L := [false, false, false]) (h := true)
    (R := [false, false, true, true, true]) (L' := [true, false, false, true, true, false]) (h' := true)
    (R' := [true, true]) L R (by decide)
  simpa [hc, rdig, Lu, Rr] using h

theorem absTailT (L R : List Bool) :
    run 11 ⟨.A, rdig .t ++ L, true, [false] ++ Lu ++ R⟩ = hc (Rr ++ [true] ++ L) R := by
  have h := frame (n := 11) (s := .A) (s' := .B) (L := [false, false, true]) (h := true)
    (R := [false, false, true, true, true]) (L' := [true, false, false, true, true, true]) (h' := true)
    (R' := [true, true]) L R (by decide)
  simpa [hc, rdig, Lu, Rr] using h

/-- low digit 1: the carry goes on into the next digits (third counter phase) -/
theorem absTailO1 (L R : List Bool) :
    run 8 ⟨.A, rdig .o ++ L, true, [false] ++ Lu ++ R⟩
      = dc L ([false, true, true, true, true] ++ Lu ++ R) := by
  have h := frame (n := 7) (s := .A) (s' := .D) (L := [false, true, true]) (h := true)
    (R := [false, false]) (L' := []) (h' := true)
    (R' := [true, true, true, true, false]) L ([true, true, true] ++ R) (by decide)
  rw [show 8 = 7 + 1 from rfl, run_add]
  simp only [rdig, Lu, List.cons_append, List.nil_append] at h ⊢
  rw [h, dstep]

theorem absTailO2 (L R : List Bool) :
    run 4 (ac L ([false, true, true, true, true] ++ R)) = hc ([false] ++ L) R := rfl

end M8
