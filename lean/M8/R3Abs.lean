import M8.AbsOvf
namespace M8.R3
open List

/-! # The abstract model (round 3).  Mirror: tools/r3/am2.py (validated against the machine).
State `⟨k, C, m, L⟩`: tape `hc (Rr^k ++ ctape C) (Lu^m ++ lad L)`, first block `B1 = k+1+m`. -/

def dv : Dg → Nat
  | .z => 0
  | .o => 1
  | .t => 2

def dg : Nat → Dg
  | 0 => .z
  | 1 => .o
  | _ => .t

theorem val_cons (d : Dg) (r : List Dg) : val (d :: r) = dv d + 3 * val r := by
  cases d <;> rfl

/-- canonical digits (LSB first, no top zeros) -/
def dig (n : Nat) : List Dg :=
  if h : n = 0 then [] else dg (n % 3) :: dig (n / 3)
decreasing_by omega

theorem dv_dg (n : Nat) (h : n < 3) : dv (dg n) = n := by
  match n, h with
  | 0, _ => rfl
  | 1, _ => rfl
  | 2, _ => rfl

theorem val_dig (n : Nat) : val (dig n) = n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    unfold dig
    split
    · subst_vars; rfl
    · rw [val_cons, ih (n / 3) (by omega), dv_dg _ (Nat.mod_lt _ (by omega))]; omega

theorem dig_zero : dig 0 = [] := by unfold dig; simp

theorem dig_pos (n : Nat) (h : n ≠ 0) : dig n = dg (n % 3) :: dig (n / 3) := by
  rw [dig]; simp [h]

/-! ## trim of counters depends only on the value -/

theorem trim_Sr_dig (ds : List Dg) : trim (Sr ds) = trim (Sr (dig (val ds))) := by
  induction ds with
  | nil => show trim (Sr []) = trim (Sr (dig 0)); rw [dig_zero]
  | cons d r ih =>
    rw [val_cons]
    by_cases h0 : dv d + 3 * val r = 0
    · have hd : d = .z := by cases d <;> simp [dv] at h0 ⊢
      have hr : val r = 0 := by omega
      subst hd
      rw [h0, dig_zero, Sr_cons]
      rw [hr, dig_zero] at ih
      simp [rdig, ih, cons']
    · rw [dig_pos _ h0, Sr_cons, Sr_cons]
      have e1 : dg ((dv d + 3 * val r) % 3) = d := by
        cases d <;> simp [dv, dg] <;> omega
      have e2 : (dv d + 3 * val r) / 3 = val r := by cases d <;> simp [dv] <;> omega
      rw [e1, e2]
      exact trim_append_congr _ ih

theorem trim_Sr_val {ds ds' : List Dg} (h : val ds = val ds') : trim (Sr ds) = trim (Sr ds') := by
  rw [trim_Sr_dig ds, trim_Sr_dig ds', h]

theorem Sr_append (a b : List Dg) : Sr (a ++ b) = Sr a ++ Sr b := by
  simp [Sr]

theorem val_append (a b : List Dg) : val (a ++ b) = val a + 3 ^ a.length * val b := by
  induction a with
  | nil => simp [val]
  | cons d r ih =>
    rw [List.cons_append, val_cons, val_cons, ih, List.length_cons, Nat.pow_succ]
    have e : 3 * (3 ^ r.length * val b) = 3 ^ r.length * 3 * val b := by
      rw [Nat.mul_comm (3 ^ r.length) 3, Nat.mul_assoc]
    rw [Nat.mul_add, e, Nat.add_assoc]

/-! ## model definitions -/

inductive CF
  | cl (v : Nat)
  | lone (lo : List Dg) (hv : Nat)

/-- re-read of `[f] ++ Sr (dig n)` (n ≥ 1): low part and high value of the lone-1 form -/
def shl (n : Nat) : List Dg × Nat :=
  if h : n = 0 then ([], 0)
  else if n % 3 = 0 then (.z :: (shl (n / 3)).1, (shl (n / 3)).2)
  else if n % 3 = 1 then ([.t], n / 3) else ([.z], n / 3)
decreasing_by omega

def shv (n : Nat) : CF := if n = 0 then .cl 0 else .lone (shl n).1 (shl n).2

def ctape : CF → List Bool
  | .cl v => Sr (dig v)
  | .lone lo hv => Sr lo ++ [true] ++ Sr (dig hv)

/-- the ladder: separators (`true` = `1.`, `false` = `..`) each followed by a block; terminal `1.` -/
def lad : List (Bool × Nat) → List Bool
  | [] => [true, false]
  | (s, b) :: r => (if s then [true, false] else [false, false]) ++ pw Lu b ++ lad r

/-- ladder phase: new first block and new ladder -/
def linc : Nat → List (Bool × Nat) → Nat × List (Bool × Nat)
  | B, [] => (B - 2, [(false, 2)])
  | B, (false, c) :: r => (B, (true, c) :: r)
  | B, (true, c) :: r => (B - 2, (false, (linc c r).1 + 2) :: (linc c r).2)

/-- counter phase: (released units, new counter) -/
def cph : CF → Nat × CF
  | .cl v => (0, .cl (v + 1))
  | .lone lo hv =>
    if lowOk lo then (0, .lone (inc lo) hv)
    else if lo = [] then (0, shv (hv + 2))
    else (1, .cl (3 ^ (lo.length - 1) * (hv + 1)))

structure AS where
  k : Nat
  C : CF
  m : Nat
  L : List (Bool × Nat)

def absStep : CF → List (Bool × Nat) → AS
  | .cl v, (_, b) :: rest =>
    if (v + 2) % 3 = 0 then ⟨1, shv ((v + 2) / 3), b - 1, rest⟩
    else if (v + 2) % 3 = 2 then ⟨1, .lone [] ((v + 2) / 3), b - 1, rest⟩
    else ⟨0, shv ((v + 2) / 3 + 1), b, rest⟩
  | C, L => ⟨0, C, 0, L⟩

def mstep (S : AS) : AS :=
  match linc (S.k + 1 + S.m) S.L with
  | (0, L') => absStep S.C L'
  | (p + 1, L') => ⟨(cph S.C).1, (cph S.C).2, p, L'⟩

def tape (S : AS) : Cfg := hc (pw Rr S.k ++ ctape S.C) (pw Lu S.m ++ lad S.L)

/-! ## re-read lemma -/

theorem shl_eq (n : Nat) (hn : n ≠ 0) :
    [false] ++ Sr (dig n) = Sr (shl n).1 ++ [true] ++ Sr (dig (shl n).2) := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [dig_pos n hn, shl]
    simp only [hn, dite_false]
    by_cases h0 : n % 3 = 0
    · simp only [h0, if_true]
      have hn3 : n / 3 ≠ 0 := by omega
      have := ih (n / 3) (by omega) hn3
      simp only [Sr_cons, dg, rdig] at this ⊢
      simp only [List.cons_append, List.nil_append] at this ⊢
      rw [← this]
    · by_cases h1 : n % 3 = 1
      · simp [h0, h1, dg, rdig, Sr_cons]
      · have h2 : n % 3 = 2 := by omega
        simp [h0, h1, h2, dg, rdig, Sr_cons]

theorem sh_tape (n : Nat) : trim ([false] ++ Sr (dig n)) = trim (ctape (shv n)) := by
  by_cases hn : n = 0
  · subst hn; simp [shv, ctape, dig_zero, cons']
  · simp only [shv, hn, if_false, ctape]; rw [shl_eq n hn]

end M8.R3
