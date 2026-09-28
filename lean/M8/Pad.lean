import M8.Machine
namespace M8

/-! # Blank padding: trailing `false` cells of `L` / `R` are invisible.
`PE c d` : same state and scanned cell, and `L`, `R` equal up to trailing blanks.
`PE` is preserved by `step`, hence by `run`, and it preserves the state (so halting). -/

def cons' : Bool → List Bool → List Bool
  | false, [] => []
  | x, t => x :: t

/-- drop trailing `false`s -/
def trim : List Bool → List Bool
  | [] => []
  | x :: xs => cons' x (trim xs)

@[simp] theorem trim_nil : trim [] = [] := rfl
@[simp] theorem trim_cons (x : Bool) (xs : List Bool) : trim (x :: xs) = cons' x (trim xs) := rfl

theorem trim_headD (l : List Bool) : (trim l).headD false = l.headD false := by
  cases l with
  | nil => rfl
  | cons x xs =>
    simp only [trim_cons, List.headD_cons]
    cases x <;> cases trim xs <;> rfl

theorem trim_tail (l : List Bool) : trim l.tail = (trim l).tail := by
  cases l with
  | nil => rfl
  | cons x xs =>
    simp only [trim_cons, List.tail_cons]
    cases x <;> cases trim xs <;> simp [cons']

def PE (c d : Cfg) : Prop := c.st = d.st ∧ c.h = d.h ∧ trim c.L = trim d.L ∧ trim c.R = trim d.R

theorem PE.refl (c : Cfg) : PE c c := ⟨rfl, rfl, rfl, rfl⟩
theorem PE.symm {c d : Cfg} (h : PE c d) : PE d c := ⟨h.1.symm, h.2.1.symm, h.2.2.1.symm, h.2.2.2.symm⟩
theorem PE.trans {c d e : Cfg} (h : PE c d) (h' : PE d e) : PE c e :=
  ⟨h.1.trans h'.1, h.2.1.trans h'.2.1, h.2.2.1.trans h'.2.2.1, h.2.2.2.trans h'.2.2.2⟩

theorem PE_step {c d : Cfg} (h : PE c d) : PE (step c) (step d) := by
  obtain ⟨s, L, x, R⟩ := c
  obtain ⟨s', L', x', R'⟩ := d
  obtain ⟨h1, h2, h3, h4⟩ := h
  simp only at h1 h2 h3 h4
  subst h1 h2
  have hL0 : L.headD false = L'.headD false := by rw [← trim_headD, h3, trim_headD]
  have hR0 : R.headD false = R'.headD false := by rw [← trim_headD, h4, trim_headD]
  have hL1 : trim L.tail = trim L'.tail := by rw [trim_tail, h3, trim_tail]
  have hR1 : trim R.tail = trim R'.tail := by rw [trim_tail, h4, trim_tail]
  cases s <;> cases x <;>
    simp only [step, mR, mL, PE, trim_cons, hL0, hR0, hL1, hR1, h3, h4, and_self]

theorem PE_run (n : Nat) {c d : Cfg} (h : PE c d) : PE (run n c) (run n d) := by
  induction n generalizing c d with
  | zero => exact h
  | succ n ih => exact ih (PE_step h)

theorem trim_blank (l : List Bool) (hl : ∀ x ∈ l, x = false) : trim l = [] := by
  induction l with
  | nil => rfl
  | cons x xs ih =>
    have hx := hl x (by simp)
    subst hx
    rw [trim_cons, ih (fun y hy => hl y (by simp [hy]))]; rfl

theorem trim_append_blank (l p : List Bool) (hp : ∀ x ∈ p, x = false) : trim (l ++ p) = trim l := by
  induction l with
  | nil => exact trim_blank p hp
  | cons x xs ih => simp [ih]

theorem trim_append_repl (l : List Bool) (n : Nat) : trim (l ++ List.replicate n false) = trim l :=
  trim_append_blank l _ (fun x hx => (List.mem_replicate.1 hx).2)

/-- padding the left/right tape by blanks -/
theorem PE_pad (s : St) (L R : List Bool) (h : Bool) (a b : Nat) :
    PE ⟨s, L ++ List.replicate a false, h, R ++ List.replicate b false⟩ ⟨s, L, h, R⟩ :=
  ⟨rfl, rfl, trim_append_repl L a, trim_append_repl R b⟩

/-- halting is invariant under `PE` -/
theorem PE_halted {c d : Cfg} (h : PE c d) : halted c ↔ halted d := by
  unfold halted; rw [h.1]

/-- `trim` congruence under a common prefix -/
theorem trim_append_congr (p : List Bool) {l l' : List Bool} (h : trim l = trim l') :
    trim (p ++ l) = trim (p ++ l') := by
  induction p with
  | nil => exact h
  | cons x xs ih => simp [ih]

end M8
