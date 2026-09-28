import M8.R3Ladder
namespace M8.R3
open List

/-! # Epochs: from one pre-absorption state to the next (pure mathematics on the model).
Pre-absorption state `(l, a)`: `B1 = 2`, clean counter `v`, ladder `preL l a`; the epoch has
`E = 2^(l+1) + a + 1` ordinary steps.  Invariant `1 ≤ v`, `5 v ≤ 6 E`, `15 ≤ E`. -/

theorem val_lt (ds : List Dg) : val ds < 3 ^ ds.length := by
  induction ds with
  | nil => simp [val]
  | cons d r ih =>
    rw [val_cons, List.length_cons, Nat.pow_succ]
    have : dv d ≤ 2 := by cases d <;> simp [dv]
    omega

theorem lowOk_iff (ds : List Dg) : lowOk ds = true ↔ val ds + 1 < 3 ^ ds.length := by
  induction ds with
  | nil => simp [lowOk, val]
  | cons d r ih =>
    have hl := val_lt r
    rw [val_cons, List.length_cons, Nat.pow_succ]
    cases d with
    | z => simp [lowOk, dv]; omega
    | o => simp [lowOk, dv]; omega
    | t => simp only [lowOk, dv]; rw [ih]; omega

theorem length_inc (ds : List Dg) (h : lowOk ds = true) : (inc ds).length = ds.length := by
  induction ds with
  | nil => simp [lowOk] at h
  | cons d r ih =>
    cases d with
    | z => rfl
    | o => rfl
    | t => simp only [lowOk] at h; simp [inc, ih h]

/-! ## pending counters -/

/-- `C` realigns at the `j`-th counter phase from now, giving the clean value `Vr` -/
def Pend (C : CF) (j Vr : Nat) : Prop :=
  ∃ lo hv, C = .lone lo hv ∧ lo ≠ [] ∧ val lo + j = 3 ^ lo.length ∧ Vr = 3 ^ (lo.length - 1) * (hv + 1)

/-- also allowing the empty low part (one `realign0` phase first) -/
def PendX (C : CF) (j Vr : Nat) : Prop :=
  Pend C j Vr ∨ ∃ q j', C = .lone [] q ∧ j = j' + 1 ∧ Pend (shv (q + 2)) j' Vr

theorem Pend_pos {C : CF} {j Vr : Nat} (h : Pend C j Vr) : 1 ≤ j := by
  obtain ⟨lo, hv, _, _, h1, _⟩ := h
  have := val_lt lo; omega

theorem cph_pend2 {C : CF} {j Vr : Nat} (h : PendX C (j + 2) Vr) :
    ∃ C', cph C = (0, C') ∧ Pend C' (j + 1) Vr := by
  rcases h with ⟨lo, hv, rfl, hne, h1, h2⟩ | ⟨q, j', rfl, hj, hp⟩
  · have hok : lowOk lo = true := by rw [lowOk_iff]; omega
    refine ⟨.lone (inc lo) hv, by simp [cph, hok], inc lo, hv, rfl, inc_ne_nil lo, ?_, ?_⟩
    · rw [val_inc, length_inc lo hok]; omega
    · rw [length_inc lo hok]; exact h2
  · have hj' : j' = j + 1 := by omega
    subst hj'
    exact ⟨shv (q + 2), by simp [cph, lowOk], hp⟩

theorem cph_pend1 {C : CF} {Vr : Nat} (h : PendX C 1 Vr) : cph C = (1, .cl Vr) := by
  rcases h with ⟨lo, hv, rfl, hne, h1, h2⟩ | ⟨q, j', rfl, hj, hp⟩
  · have hok : lowOk lo = false := by
      cases h : lowOk lo with
      | false => rfl
      | true => rw [lowOk_iff] at h; omega
    simp [cph, hok, hne, h2]
  · have : j' = 0 := by omega
    subst this
    have := Pend_pos hp; omega

theorem cph_k (C : CF) : (cph C).1 ≤ 1 := by
  cases C with
  | cl v => simp [cph]
  | lone lo hv =>
    simp only [cph]
    by_cases h1 : lowOk lo = true
    · simp [h1]
    · by_cases h2 : lo = []
      · subst h2; simp [lowOk]
      · simp [h1, h2]

/-! ## the re-read gives a pending counter with explicit bounds -/

theorem shv_ne (n : Nat) (hn : n ≠ 0) : shv n = .lone (shl n).1 (shl n).2 := by simp [shv, hn]

theorem shl_pos (n : Nat) (hn : n ≠ 0) :
    shl n = if n % 3 = 0 then (.z :: (shl (n / 3)).1, (shl (n / 3)).2)
      else if n % 3 = 1 then ([.t], n / 3) else ([.z], n / 3) := by
  rw [shl]; simp [hn]

theorem shv_pend (n : Nat) (hn : 1 ≤ n) :
    ∃ j Vr, Pend (shv n) j Vr ∧ 2 * j ≤ 3 * n ∧ 3 * Vr ≤ 3 * j + n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    rw [shv_ne n (by omega), shl_pos n (by omega)]
    by_cases h0 : n % 3 = 0
    · rw [if_pos h0]
      obtain ⟨j', Vr', ⟨lo', hv', hc, hne, h1, h2⟩, b1, b2⟩ := ih (n / 3) (by omega) (by omega)
      rw [shv_ne _ (by omega)] at hc
      injection hc with e1 e2
      rw [e1, e2]
      obtain ⟨t, ht⟩ : ∃ t, lo'.length = t + 1 := ⟨lo'.length - 1, by
        cases lo' with
        | nil => exact absurd rfl hne
        | cons _ _ => simp⟩
      refine ⟨3 * j', 3 * Vr', ⟨.z :: lo', hv', rfl, by simp, ?_, ?_⟩, by omega, by omega⟩
      · rw [val_cons, List.length_cons, Nat.pow_succ]; simp [dv]; omega
      · rw [h2, List.length_cons, ht, Nat.add_sub_cancel, Nat.add_sub_cancel, Nat.pow_succ,
          Nat.mul_comm (3 ^ t) 3, Nat.mul_assoc]
    · rw [if_neg h0]
      by_cases h1 : n % 3 = 1
      · rw [if_pos h1]
        refine ⟨1, n / 3 + 1, ⟨[.t], n / 3, rfl, by simp, by simp [val], by simp⟩, by omega, by omega⟩
      · rw [if_neg h1]
        refine ⟨3, n / 3 + 1, ⟨[.z], n / 3, rfl, by simp, by simp [val], by simp⟩, by omega, by omega⟩

/-! ## epoch invariant -/

def preL (l a : Nat) : List (Bool × Nat) := if a = 0 then Ol (l + 1) else Lam (l + 1) (2 * a - 1)

def EE (l a : Nat) : Nat := 2 ^ (l + 1) + a + 1

/-- the pre-absorption invariant -/
def PreInv (S : AS) : Prop :=
  ∃ l a v, a < 2 ^ (l + 1) ∧ S.C = .cl v ∧ S.k + S.m = 1 ∧ S.k ≤ 1 ∧ S.L = preL l a ∧
    1 ≤ v ∧ 5 * v ≤ 6 * EE l a ∧ 15 ≤ EE l a

/-- state `i` of the epoch after absorption `(l, a)`; realignment after `R` phases, value `Vr` -/
def EpInv (l a R Vr i : Nat) (S : AS) : Prop :=
  S.L = epL l a i ∧ S.k ≤ 1 ∧
  ((i < R ∧ S.k + 1 + S.m = EE l a - i + (a + i) % 2 ∧ PendX S.C (R - i) Vr) ∨
   (R ≤ i ∧ S.k + 1 + S.m = EE l a - i + 1 + (a + i) % 2 ∧ S.C = .cl (Vr + i - R)))

theorem epoch_step (l a R Vr i : Nat) (S : AS) (ha : a < 2 ^ (l + 1)) (hR : R + 1 ≤ EE l a)
    (hi : i < EE l a) (h : EpInv l a R Vr i S) :
    okS S ∧ EpInv l a R Vr (i + 1) (mstep S) := by
  obtain ⟨hL, hk, hc⟩ := h
  have hP := two_le_pow l
  unfold EE at hR hi
  -- first block and phase result
  have hB : 2 ≤ S.k + 1 + S.m := by rcases hc with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ <;> unfold EE at h2 <;> omega
  have hlinc := linc_epL l a i (S.k + 1 + S.m) ha (by omega) hB
  rw [← hL] at hlinc
  have hp : 1 ≤ (if (a + i) % 2 = 1 then S.k + 1 + S.m - 2 else S.k + 1 + S.m) := by
    rcases hc with ⟨h1, h2, _⟩ | ⟨h1, h2, _⟩ <;> unfold EE at h2 <;> split <;> omega
  refine ⟨⟨by omega, hL ▸ epL_blocks l a i, fun h0 => by rw [hlinc] at h0; simp only at h0; omega⟩, ?_⟩
  obtain ⟨p, hpe⟩ : ∃ p, (if (a + i) % 2 = 1 then S.k + 1 + S.m - 2 else S.k + 1 + S.m) = p + 1 :=
    ⟨_, (Nat.sub_add_cancel hp).symm⟩
  have hms : mstep S = ⟨(cph S.C).1, (cph S.C).2, p, epL l a (i + 1)⟩ := by
    unfold mstep; rw [hlinc, hpe]
  rw [hms]
  refine ⟨rfl, cph_k _, ?_⟩
  simp only
  have hpar : (a + (i + 1)) % 2 = 1 - (a + i) % 2 := by omega
  rcases hc with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · by_cases hlast : i + 1 < R
    · obtain ⟨C', e, hC'⟩ := cph_pend2 (j := R - i - 2) (by rw [show R - i - 2 + 2 = R - i by omega]; exact h3)
      rw [e]
      refine Or.inl ⟨hlast, ?_, Or.inl (by rw [show R - (i + 1) = R - i - 2 + 1 by omega]; exact hC')⟩
      simp only; unfold EE at h2 ⊢; split at hpe <;> omega
    · have hR1 : R - i = 1 := by omega
      rw [hR1] at h3
      rw [cph_pend1 h3]
      refine Or.inr ⟨by omega, ?_, by simp only; congr 1; omega⟩
      simp only; unfold EE at h2 ⊢; split at hpe <;> omega
  · rw [h3]
    refine Or.inr ⟨by omega, ?_, by simp only [cph]; congr 1; omega⟩
    simp only [cph]; unfold EE at h2 ⊢; split at hpe <;> omega

end M8.R3
