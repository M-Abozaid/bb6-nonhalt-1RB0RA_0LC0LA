import M8.Absorb
namespace M8
open List

/-! # Absorption, generic tails, and absorption during an overflow (level change).
The tails only depend on `A` sitting on the cleared `s1` with the doubly incremented counter; the
rest `Y` of the tape is arbitrary. -/

theorem absGenZ (r : List Dg) (b : Nat) (hb1 : 1 ≤ b) (L Y : List Bool) :
    run 11 (ac (Sr (.z :: r) ++ L) ([true, false] ++ pw Lu b ++ Y))
      = hc (Rr ++ [false] ++ Sr r ++ L) (pw Lu (b - 1) ++ Y) := by
  have t := absTailZ (Sr r ++ L) (pw Lu (b - 1) ++ Y)
  have : ac (Sr (.z :: r) ++ L) ([true, false] ++ pw Lu b ++ Y)
      = ⟨.A, rdig .z ++ (Sr r ++ L), true, [false] ++ Lu ++ (pw Lu (b - 1) ++ Y)⟩ := by
    simp only [Sr_cons, ac, List.append_assoc, List.cons_append, List.nil_append, List.headD_cons,
      List.tail_cons]
    rw [pw_pos Lu b hb1]
  rw [this, t]; simp [List.append_assoc]

theorem absGenT (r : List Dg) (b : Nat) (hb1 : 1 ≤ b) (L Y : List Bool) :
    run 11 (ac (Sr (.t :: r) ++ L) ([true, false] ++ pw Lu b ++ Y))
      = hc (Rr ++ [true] ++ Sr r ++ L) (pw Lu (b - 1) ++ Y) := by
  have t := absTailT (Sr r ++ L) (pw Lu (b - 1) ++ Y)
  have : ac (Sr (.t :: r) ++ L) ([true, false] ++ pw Lu b ++ Y)
      = ⟨.A, rdig .t ++ (Sr r ++ L), true, [false] ++ Lu ++ (pw Lu (b - 1) ++ Y)⟩ := by
    simp only [Sr_cons, ac, List.append_assoc, List.cons_append, List.nil_append, List.headD_cons,
      List.tail_cons]
    rw [pw_pos Lu b hb1]
  rw [this, t]; simp [List.append_assoc]

theorem absGenO (r : List Dg) (h3 : lowOk r = true) (b : Nat) (hb1 : 1 ≤ b) (L Y : List Bool) :
    run (8 + ((6 * tz r + 5) + 4)) (ac (Sr (.o :: r) ++ L) ([true, false] ++ pw Lu b ++ Y))
      = hc ([false] ++ Sr (inc r) ++ L) (pw Lu b ++ Y) := by
  have t1 := absTailO1 (Sr r ++ L) (pw Lu (b - 1) ++ Y)
  have t2 := cnt r h3 L ([false, true, true, true, true] ++ Lu ++ (pw Lu (b - 1) ++ Y))
  have t3 := absTailO2 (Sr (inc r) ++ L) (Lu ++ (pw Lu (b - 1) ++ Y))
  have : ac (Sr (.o :: r) ++ L) ([true, false] ++ pw Lu b ++ Y)
      = ⟨.A, rdig .o ++ (Sr r ++ L), true, [false] ++ Lu ++ (pw Lu (b - 1) ++ Y)⟩ := by
    simp only [Sr_cons, ac, List.append_assoc, List.cons_append, List.nil_append, List.headD_cons,
      List.tail_cons]
    rw [pw_pos Lu b hb1]
  rw [this]
  refine run_trans t1 (run_trans t2 ?_)
  rw [List.append_assoc _ Lu, t3]
  have := pw_pos Lu b hb1 Y
  simp only [List.append_assoc] at this ⊢
  rw [this]

/-- overflow-coincident absorption, first part: `B1 = 2`, all separators `1.` (blocks `b :: bs`),
terminal `1.` then blank. -/
theorem absFirstOvf (ds : List Dg) (h1 : lowOk ds = true) (h2 : lowOk (inc ds) = true)
    (b : Nat) (bs : List Nat) (hb : ∀ x ∈ b :: bs, 1 ≤ x) (L X : List Bool) :
    ∃ n, 0 < n ∧ run n (hc (Sr ds ++ L) (Lu ++ rtt (b :: bs) ([true, false] ++ [false, false] ++ X)))
      = ac (Sr (inc (inc ds)) ++ L)
          ([true, false] ++ pw Lu b ++ (E bs ++ [false, false] ++ pw Lu 2 ++ [true, false] ++ X)) := by
  have s1 := start (b :: bs) hb 0 1 0 rfl (Sr ds ++ L) ([true, false] ++ [false, false] ++ X)
  simp only [pw_zero, List.nil_append, pw_succ, List.append_nil] at s1
  have s2 := pass (Q (b :: bs) (Sr ds ++ L)) (false :: X)
  have s3 := turn (Mr ++ Q (b :: bs) (Sr ds ++ L)) X
  have s4 := lmark (Q (b :: bs) (Sr ds ++ L)) (Lu ++ [true, false] ++ X)
  have s3' : run 24 (hc (Mr ++ Q (b :: bs) (Sr ds ++ L)) (false :: false :: X))
      = dc (Mr ++ Q (b :: bs) (Sr ds ++ L)) (Lu ++ [true, false] ++ X) := s3
  have s5 := lqp (b :: bs) hb (Sr ds ++ L) ([false, false] ++ Lu ++ (Lu ++ [true, false] ++ X))
  have s6 := cnt ds h1 L (E (b :: bs) ++ ([false, false] ++ Lu ++ (Lu ++ [true, false] ++ X)))
  have e6 : E (b :: bs) ++ ([false, false] ++ Lu ++ (Lu ++ [true, false] ++ X))
      = [false, false] ++ (pw Lu b ++ (E bs ++ [false, false] ++ pw Lu 2 ++ [true, false] ++ X)) := by
    simp [E, List.append_assoc, pw_succ]
  rw [e6] at s6 s5
  have s7 := absHead (Sr (inc ds) ++ L) (pw Lu b ++ (E bs ++ [false, false] ++ pw Lu 2 ++ [true, false] ++ X))
  have s8 := cnt (inc ds) h2 L ([true, false] ++ (pw Lu b ++ (E bs ++ [false, false] ++ pw Lu 2 ++ [true, false] ++ X)))
  have e1 : [true, false] ++ [false, false] ++ X = [true, false] ++ false :: (false :: X) := rfl
  rw [e1] at s1
  refine ⟨_, ?_, run_trans s1 (run_trans s2 (run_trans s3' (run_trans s4 (run_trans s5
    (run_trans s6 (run_trans s7 (s8.trans ?_)))))))⟩
  · omega
  · simp [List.append_assoc]

theorem absorbZo (ds : List Dg) (h1 : lowOk ds = true) (h2 : lowOk (inc ds) = true) (r : List Dg)
    (hr : inc (inc ds) = .z :: r) (b : Nat) (bs : List Nat) (hb : ∀ x ∈ b :: bs, 1 ≤ x) (L X : List Bool) :
    Reach1 (hc (Sr ds ++ L) (Lu ++ rtt (b :: bs) ([true, false] ++ [false, false] ++ X)))
      (hc (Rr ++ [false] ++ Sr r ++ L)
        (pw Lu (b - 1) ++ (E bs ++ [false, false] ++ pw Lu 2 ++ [true, false] ++ X))) := by
  obtain ⟨n, hn, e⟩ := absFirstOvf ds h1 h2 b bs hb L X
  refine ⟨n + 11, by omega, ?_⟩
  rw [run_add, e, hr, absGenZ r b (hb b (by simp))]

theorem absorbTo (ds : List Dg) (h1 : lowOk ds = true) (h2 : lowOk (inc ds) = true) (r : List Dg)
    (hr : inc (inc ds) = .t :: r) (b : Nat) (bs : List Nat) (hb : ∀ x ∈ b :: bs, 1 ≤ x) (L X : List Bool) :
    Reach1 (hc (Sr ds ++ L) (Lu ++ rtt (b :: bs) ([true, false] ++ [false, false] ++ X)))
      (hc (Rr ++ [true] ++ Sr r ++ L)
        (pw Lu (b - 1) ++ (E bs ++ [false, false] ++ pw Lu 2 ++ [true, false] ++ X))) := by
  obtain ⟨n, hn, e⟩ := absFirstOvf ds h1 h2 b bs hb L X
  refine ⟨n + 11, by omega, ?_⟩
  rw [run_add, e, hr, absGenT r b (hb b (by simp))]

theorem absorbOo (ds : List Dg) (h1 : lowOk ds = true) (h2 : lowOk (inc ds) = true) (r : List Dg)
    (hr : inc (inc ds) = .o :: r) (h3 : lowOk r = true)
    (b : Nat) (bs : List Nat) (hb : ∀ x ∈ b :: bs, 1 ≤ x) (L X : List Bool) :
    Reach1 (hc (Sr ds ++ L) (Lu ++ rtt (b :: bs) ([true, false] ++ [false, false] ++ X)))
      (hc ([false] ++ Sr (inc r) ++ L)
        (pw Lu b ++ (E bs ++ [false, false] ++ pw Lu 2 ++ [true, false] ++ X))) := by
  obtain ⟨n, hn, e⟩ := absFirstOvf ds h1 h2 b bs hb L X
  refine ⟨n + (8 + ((6 * tz r + 5) + 4)), by omega, ?_⟩
  rw [run_add, e, hr, absGenO r h3 b (hb b (by simp))]

end M8
