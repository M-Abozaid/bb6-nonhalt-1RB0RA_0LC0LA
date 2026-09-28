import M8.Forms
namespace M8
open List

/-! # Absorption (plan step 6)
Exhaustion of the first block: checkpoint with `B1 = 2` (`k = 0`, `m = 1`) and `s1 = 1`, the first
`..` separator after the `1.`-blocks `b :: bs`.  The increment runs as usual (all `1.` seps up to
the first `..` are cleared, the last block gains the 2 units of `B1`), but the counter's `A` then
lands on the cleared `..` of `s1`: it writes `1.` there and increments the counter a second time
(`absHead`); the cells around `p0` are then re-framed (`absTail*`), depending on the low digit
`d0` of `inc (inc ds)`:
* `d0 = 0`: new counter `Rr ++ [f] ++ Sr r`, carried unit = first unit of `b`   (`B1' = b + 1`)
* `d0 = 2`: new counter `Rr ++ [t] ++ Sr r`, carried unit = first unit of `b`   (`B1' = b + 1`)
* `d0 = 1`: third counter phase on `r`; new counter `[f] ++ Sr (inc r)`, `m' = b` (`B1' = b + 1`)
(`r` = the other digits).  Validated: all 1158 absorptions in 1e8..2e10 (tools/abs4.py). -/

def Reach1 (c c' : Cfg) : Prop := ∃ n, 0 < n ∧ run n c = c'

theorem Reach1.trans {c c' c'' : Cfg} (h : Reach1 c c') (h' : Reach1 c' c'') : Reach1 c c'' := by
  obtain ⟨a, ha, e⟩ := h
  obtain ⟨b, hb, e'⟩ := h'
  exact ⟨a + b, by omega, by rw [run_add, e, e']⟩

/-- common first part: from the checkpoint to `A` on the cleared `s1`, counter incremented twice
(the first `..` separator after `b :: bs` lies at the start of `X`). -/
theorem absFirst (ds : List Dg) (h1 : lowOk ds = true) (h2 : lowOk (inc ds) = true)
    (b : Nat) (bs : List Nat) (hb : ∀ x ∈ b :: bs, 1 ≤ x) (L X : List Bool) :
    ∃ n, 0 < n ∧ run n (hc (Sr ds ++ L) (Lu ++ rtt (b :: bs) ([false, false] ++ X)))
      = ac (Sr (inc (inc ds)) ++ L) ([true, false] ++ pw Lu b ++ E bs ++ pw Lu 2 ++ [true, false] ++ X) := by
  have s1 := start (b :: bs) hb 0 1 0 rfl (Sr ds ++ L) ([false, false] ++ X)
  have s2 := turn (Rr ++ Q (b :: bs) (pw Rr 0 ++ (Sr ds ++ L))) X
  have s3 := lunit (Q (b :: bs) (pw Rr 0 ++ (Sr ds ++ L))) (Lu ++ [true, false] ++ X)
  have s4 := lqp (b :: bs) hb (pw Rr 0 ++ (Sr ds ++ L)) (Lu ++ (Lu ++ [true, false] ++ X))
  have s5 := cnt ds h1 L (E (b :: bs) ++ (Lu ++ (Lu ++ [true, false] ++ X)))
  have s6 := absHead (Sr (inc ds) ++ L) (pw Lu b ++ E bs ++ (Lu ++ (Lu ++ [true, false] ++ X)))
  have s7 := cnt (inc ds) h2 L ([true, false] ++ (pw Lu b ++ E bs ++ (Lu ++ (Lu ++ [true, false] ++ X))))
  simp only [pw_zero, List.nil_append, pw_succ, List.append_nil] at s1 s2 s3 s4
  have e5 : E (b :: bs) ++ (Lu ++ (Lu ++ [true, false] ++ X))
      = [false, false] ++ (pw Lu b ++ E bs ++ (Lu ++ (Lu ++ [true, false] ++ X))) := by
    simp [E, List.append_assoc]
  rw [e5] at s5
  refine ⟨_, ?_, run_trans s1 (run_trans s2 (run_trans s3 (run_trans s4 (run_trans s5
    (run_trans s6 (s7.trans (by simp [List.append_assoc, pw_succ])))))))⟩
  omega

theorem pw_pos (l : List Bool) (b : Nat) (hb : 1 ≤ b) (R : List Bool) :
    pw l b ++ R = l ++ (pw l (b - 1) ++ R) := by
  obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
  simp [List.append_assoc]

/-- absorption, `d0 = 0` -/
theorem absorbZ (ds : List Dg) (h1 : lowOk ds = true) (h2 : lowOk (inc ds) = true) (r : List Dg)
    (hr : inc (inc ds) = .z :: r)
    (b : Nat) (bs : List Nat) (hb : ∀ x ∈ b :: bs, 1 ≤ x) (L X : List Bool) :
    Reach1 (hc (Sr ds ++ L) (Lu ++ rtt (b :: bs) ([false, false] ++ X)))
      (hc (Rr ++ [false] ++ Sr r ++ L) (pw Lu (b - 1) ++ E bs ++ pw Lu 2 ++ [true, false] ++ X)) := by
  obtain ⟨n, hn, e⟩ := absFirst ds h1 h2 b bs hb L X
  have hb1 : 1 ≤ b := hb b (by simp)
  have t := absTailZ (Sr r ++ L) (pw Lu (b - 1) ++ E bs ++ pw Lu 2 ++ [true, false] ++ X)
  refine ⟨n + 11, by omega, ?_⟩
  rw [run_add, e, hr, Sr_cons]
  have : ac ((rdig .z ++ Sr r) ++ L) ([true, false] ++ pw Lu b ++ E bs ++ pw Lu 2 ++ [true, false] ++ X)
      = ⟨.A, rdig .z ++ (Sr r ++ L), true,
          [false] ++ Lu ++ (pw Lu (b - 1) ++ E bs ++ pw Lu 2 ++ [true, false] ++ X)⟩ := by
    simp only [ac, List.append_assoc, List.cons_append, List.nil_append, List.headD_cons, List.tail_cons]
    rw [pw_pos Lu b hb1]
  rw [this, t]; simp [List.append_assoc]

/-- absorption, `d0 = 2` -/
theorem absorbT (ds : List Dg) (h1 : lowOk ds = true) (h2 : lowOk (inc ds) = true) (r : List Dg)
    (hr : inc (inc ds) = .t :: r)
    (b : Nat) (bs : List Nat) (hb : ∀ x ∈ b :: bs, 1 ≤ x) (L X : List Bool) :
    Reach1 (hc (Sr ds ++ L) (Lu ++ rtt (b :: bs) ([false, false] ++ X)))
      (hc (Rr ++ [true] ++ Sr r ++ L) (pw Lu (b - 1) ++ E bs ++ pw Lu 2 ++ [true, false] ++ X)) := by
  obtain ⟨n, hn, e⟩ := absFirst ds h1 h2 b bs hb L X
  have hb1 : 1 ≤ b := hb b (by simp)
  have t := absTailT (Sr r ++ L) (pw Lu (b - 1) ++ E bs ++ pw Lu 2 ++ [true, false] ++ X)
  refine ⟨n + 11, by omega, ?_⟩
  rw [run_add, e, hr, Sr_cons]
  have : ac ((rdig .t ++ Sr r) ++ L) ([true, false] ++ pw Lu b ++ E bs ++ pw Lu 2 ++ [true, false] ++ X)
      = ⟨.A, rdig .t ++ (Sr r ++ L), true,
          [false] ++ Lu ++ (pw Lu (b - 1) ++ E bs ++ pw Lu 2 ++ [true, false] ++ X)⟩ := by
    simp only [ac, List.append_assoc, List.cons_append, List.nil_append, List.headD_cons, List.tail_cons]
    rw [pw_pos Lu b hb1]
  rw [this, t]; simp [List.append_assoc]

/-- absorption, `d0 = 1` (third counter phase on the other digits `r`) -/
theorem absorbO (ds : List Dg) (h1 : lowOk ds = true) (h2 : lowOk (inc ds) = true) (r : List Dg)
    (hr : inc (inc ds) = .o :: r) (h3 : lowOk r = true)
    (b : Nat) (bs : List Nat) (hb : ∀ x ∈ b :: bs, 1 ≤ x) (L X : List Bool) :
    Reach1 (hc (Sr ds ++ L) (Lu ++ rtt (b :: bs) ([false, false] ++ X)))
      (hc ([false] ++ Sr (inc r) ++ L) (pw Lu b ++ E bs ++ pw Lu 2 ++ [true, false] ++ X)) := by
  obtain ⟨n, hn, e⟩ := absFirst ds h1 h2 b bs hb L X
  have hb1 : 1 ≤ b := hb b (by simp)
  have t1 := absTailO1 (Sr r ++ L) (pw Lu (b - 1) ++ E bs ++ pw Lu 2 ++ [true, false] ++ X)
  have t2 := cnt r h3 L ([false, true, true, true, true] ++ Lu ++
    (pw Lu (b - 1) ++ E bs ++ pw Lu 2 ++ [true, false] ++ X))
  have t3 := absTailO2 (Sr (inc r) ++ L) (Lu ++ (pw Lu (b - 1) ++ E bs ++ pw Lu 2 ++ [true, false] ++ X))
  refine ⟨n + (8 + ((6 * tz r + 5) + 4)), by omega, ?_⟩
  rw [run_add, e, hr, Sr_cons]
  have : ac ((rdig .o ++ Sr r) ++ L) ([true, false] ++ pw Lu b ++ E bs ++ pw Lu 2 ++ [true, false] ++ X)
      = ⟨.A, rdig .o ++ (Sr r ++ L), true,
          [false] ++ Lu ++ (pw Lu (b - 1) ++ E bs ++ pw Lu 2 ++ [true, false] ++ X)⟩ := by
    simp only [ac, List.append_assoc, List.cons_append, List.nil_append, List.headD_cons, List.tail_cons]
    rw [pw_pos Lu b hb1]
  rw [this]
  refine run_trans t1 (run_trans t2 ?_)
  rw [List.append_assoc _ Lu, t3]
  have := pw_pos Lu b hb1 (E bs ++ pw Lu 2 ++ [true, false] ++ X)
  simp only [List.append_assoc] at this ⊢
  rw [this]

end M8
