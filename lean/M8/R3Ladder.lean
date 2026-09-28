import M8.R3Sim
namespace M8.R3
open List

/-! # Ladder closed forms (pure).  `Lam l N` = the level-`l` ladder after `N` increments. -/

def Lam : Nat → Nat → List (Bool × Nat)
  | 0, N => [(decide (N % 2 = 1), 2)]
  | l + 1, N => (decide (N % 2 = 1), 2 ^ (l + 1) + 2 * ((N + 2) / 4)) :: Lam l (N / 2)

/-- the all-ones ladder `[2^l, ..., 4, 2]` -/
def Ol : Nat → List (Bool × Nat)
  | 0 => []
  | l + 1 => (true, 2 ^ (l + 1)) :: Ol l

theorem two_le_pow (l : Nat) : 2 ≤ 2 ^ (l + 1) := by
  rw [Nat.pow_succ]; have := Nat.one_le_two_pow (n := l); omega

theorem linc_Lam (l N B : Nat) (hN : N + 1 < 2 ^ (l + 1)) (hB : 2 ≤ B) :
    linc B (Lam l N) = (if N % 2 = 1 then B - 2 else B, Lam l (N + 1)) := by
  induction l generalizing N B with
  | zero =>
    have : N = 0 := by simp at hN; omega
    subst this; rfl
  | succ l ih =>
    have hP := two_le_pow l
    have hpow : 2 ^ (l + 1 + 1) = 2 * 2 ^ (l + 1) := by rw [Nat.pow_succ]; omega
    by_cases hp : N % 2 = 1
    · have ih' := ih (N / 2) (2 ^ (l + 1) + 2 * ((N + 2) / 4)) (by omega) (by omega)
      simp only [Lam, hp, decide_true, linc, ih', if_true]
      have e1 : (N + 1) / 2 = N / 2 + 1 := by omega
      have e2 : decide ((N + 1) % 2 = 1) = false := by simp; omega
      rw [e1, e2]
      congr 3
      split <;> omega
    · simp only [Lam, hp, decide_false, linc, if_false]
      have e1 : (N + 1) / 2 = N / 2 := by omega
      have e2 : decide ((N + 1) % 2 = 1) = true := by simp; omega
      rw [e1, e2]
      congr 3
      omega

theorem linc_Ol (l B : Nat) (hB : 2 ≤ B) : linc B (Ol l) = (B - 2, Lam l 0) := by
  induction l generalizing B with
  | zero => rfl
  | succ l ih =>
    have hP := two_le_pow l
    simp only [Ol, linc, ih (2 ^ (l + 1)) hP, Lam]
    simp; omega

theorem Lam_top (l : Nat) : Lam l (2 ^ (l + 1) - 1) = Ol (l + 1) := by
  induction l with
  | zero => rfl
  | succ l ih =>
    have hP := two_le_pow l
    have hpow : 2 ^ (l + 1 + 1) = 2 * 2 ^ (l + 1) := by rw [Nat.pow_succ]; omega
    have e1 : (2 ^ (l + 1 + 1) - 1) / 2 = 2 ^ (l + 1) - 1 := by omega
    rw [Lam, e1, ih, Ol]
    have e2 : decide ((2 ^ (l + 1 + 1) - 1) % 2 = 1) = true := by simp only [decide_eq_true_eq]; omega
    rw [e2]
    congr 2
    omega

theorem Lam_even (l a : Nat) :
    Lam (l + 1) (2 * a) = (false, 2 ^ (l + 1) + 2 * ((a + 1) / 2)) :: Lam l a := by
  simp only [Lam]
  have e1 : 2 * a / 2 = a := by omega
  have e2 : (2 * a + 2) / 4 = (a + 1) / 2 := by omega
  rw [e1, e2]; simp

theorem Lam_blocks (l N : Nat) : ∀ x ∈ Lam l N, 2 ≤ x.2 := by
  induction l generalizing N with
  | zero => intro x hx; simp [Lam] at hx; subst hx; simp
  | succ l ih =>
    intro x hx
    simp only [Lam, List.mem_cons] at hx
    rcases hx with rfl | hx
    · have := two_le_pow l; simp; omega
    · exact ih _ x hx

theorem Ol_blocks (l : Nat) : ∀ x ∈ Ol l, 2 ≤ x.2 := by
  induction l with
  | zero => intro x hx; simp [Ol] at hx
  | succ l ih =>
    intro x hx
    simp only [Ol, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact two_le_pow l
    · exact ih x hx

/-! ## the ladder during an epoch -/

/-- ladder at step `i` of the epoch that starts with `Lam l a` (after the absorption) -/
def epL (l a i : Nat) : List (Bool × Nat) :=
  if a + i < 2 ^ (l + 1) then Lam l (a + i) else Lam (l + 1) (a + i - 2 ^ (l + 1))

theorem epL_blocks (l a i : Nat) : ∀ x ∈ epL l a i, 2 ≤ x.2 := by
  unfold epL; split
  · exact Lam_blocks _ _
  · exact Lam_blocks _ _

theorem linc_epL (l a i B : Nat) (ha : a < 2 ^ (l + 1)) (hi : i < 2 ^ (l + 1) + a + 1) (hB : 2 ≤ B) :
    linc B (epL l a i) = (if (a + i) % 2 = 1 then B - 2 else B, epL l a (i + 1)) := by
  have hP := two_le_pow l
  have hpow : 2 ^ (l + 1 + 1) = 2 * 2 ^ (l + 1) := by rw [Nat.pow_succ]; omega
  unfold epL
  by_cases h1 : a + i + 1 < 2 ^ (l + 1)
  · have c1 : a + i < 2 ^ (l + 1) := by omega
    have c2 : a + (i + 1) < 2 ^ (l + 1) := by omega
    rw [if_pos c1, if_pos c2, linc_Lam l _ B h1 hB, Nat.add_assoc]
  · by_cases h2 : a + i < 2 ^ (l + 1)
    · have e : a + i = 2 ^ (l + 1) - 1 := by omega
      have c2 : ¬ a + (i + 1) < 2 ^ (l + 1) := by omega
      have c3 : (a + i) % 2 = 1 := by omega
      rw [if_pos h2, if_neg c2, e, Lam_top, linc_Ol _ B hB, ← e, if_pos c3]
      have e4 : a + (i + 1) - 2 ^ (l + 1) = 0 := by omega
      rw [e4]
    · have c2 : ¬ a + (i + 1) < 2 ^ (l + 1) := by omega
      have c3 : a + i - 2 ^ (l + 1) + 1 < 2 ^ (l + 1 + 1) := by omega
      rw [if_neg h2, if_neg c2, linc_Lam (l + 1) _ B c3 hB]
      have e : (a + i - 2 ^ (l + 1)) % 2 = (a + i) % 2 := by omega
      have e4 : a + (i + 1) - 2 ^ (l + 1) = a + i - 2 ^ (l + 1) + 1 := by omega
      rw [e, e4]

end M8.R3
