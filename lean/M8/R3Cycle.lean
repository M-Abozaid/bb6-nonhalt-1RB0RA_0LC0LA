import M8.R3Epoch
namespace M8.R3
open List

/-! # The epoch theorem: `PreInv S → ∃ S', PreInv S' ∧ Adv (tape S) (tape S')` -/

theorem epL_zero (l a : Nat) (ha : a < 2 ^ (l + 1)) : epL l a 0 = Lam l a := by
  unfold epL; rw [if_pos (by omega), Nat.add_zero]

theorem preL_blocks (l a : Nat) : ∀ x ∈ preL l a, 2 ≤ x.2 := by
  unfold preL; split
  · exact Ol_blocks _
  · exact Lam_blocks _ _

theorem linc_preL (l a : Nat) (ha : a < 2 ^ (l + 1)) :
    linc 2 (preL l a) = (0, (false, 2 ^ (l + 1) + 2 * ((a + 1) / 2)) :: Lam l a) := by
  have hpow : 2 ^ (l + 1 + 1) = 2 * 2 ^ (l + 1) := by rw [Nat.pow_succ]; omega
  rw [← Lam_even]
  unfold preL
  split
  · subst_vars; rw [linc_Ol _ 2 (by omega)]
  · rw [linc_Lam (l + 1) (2 * a - 1) 2 (by omega) (by omega), if_pos (by omega)]
    congr 2; omega

/-- the absorption step starts an epoch -/
theorem epoch_start (S : AS) (h : PreInv S) :
    ∃ l a R Vr, a < 2 ^ (l + 1) ∧ okS S ∧ EpInv l a R Vr 0 (mstep S) ∧ R + 1 ≤ EE l a ∧
      5 * (Vr + EE l a - R) ≤ 6 * (EE l a + 1) ∧ 15 ≤ EE l a := by
  obtain ⟨l, a, v, ha, hC, hkm, hk, hL, hv1, hv2, hE⟩ := h
  have hP := two_le_pow l
  have hB : S.k + 1 + S.m = 2 := by omega
  have hl : linc (S.k + 1 + S.m) S.L = (0, (false, 2 ^ (l + 1) + 2 * ((a + 1) / 2)) :: Lam l a) := by
    rw [hB, hL]; exact linc_preL l a ha
  have hok : okS S := ⟨by omega, hL ▸ preL_blocks l a, fun _ => ⟨⟨v, hC⟩, _, _, by rw [hl], by omega⟩⟩
  have hms : mstep S = absStep (.cl v) ((false, 2 ^ (l + 1) + 2 * ((a + 1) / 2)) :: Lam l a) := by
    unfold mstep; rw [hl, hC]
  rw [hms]
  unfold EE at hv2 hE ⊢
  have hb : 2 ^ (l + 1) + 2 * ((a + 1) / 2) + 1 = 2 ^ (l + 1) + a + 1 + a % 2 := by omega
  by_cases h0 : (v + 2) % 3 = 0
  · obtain ⟨j, Vr, hp, b1, b2⟩ := shv_pend ((v + 2) / 3) (by omega)
    refine ⟨l, a, j, Vr, ha, hok, ⟨?_, ?_, Or.inl ⟨Pend_pos hp, ?_, Or.inl ?_⟩⟩, ?_, ?_, hE⟩
    · simp only [absStep, h0, if_true]; exact (epL_zero l a ha).symm
    · simp only [absStep, h0, if_true]; omega
    · simp only [absStep, h0, if_true]; (try unfold EE); omega
    · simp only [absStep, h0, if_true, Nat.sub_zero]; exact hp
    · (try unfold EE); omega
    · (try unfold EE); omega
  · by_cases h2 : (v + 2) % 3 = 2
    · obtain ⟨j, Vr, hp, b1, b2⟩ := shv_pend ((v + 2) / 3 + 2) (by omega)
      have hne : (v + 2) % 3 ≠ 0 := h0
      have h20 : ¬ ((2 : Nat) = 0) := by decide
      refine ⟨l, a, j + 1, Vr, ha, hok, ⟨?_, ?_, Or.inl ⟨by omega, ?_, Or.inr ?_⟩⟩, ?_, ?_, hE⟩
      · simp only [absStep, hne, h2, h20, if_false, if_true]; exact (epL_zero l a ha).symm
      · simp only [absStep, hne, h2, h20, if_false, if_true]; omega
      · simp only [absStep, hne, h2, h20, if_false, if_true]; (try unfold EE); omega
      · simp only [absStep, hne, h2, h20, if_false, if_true, Nat.sub_zero]
        exact ⟨_, j, rfl, rfl, hp⟩
      · (try unfold EE); omega
      · (try unfold EE); omega
    · have h1 : (v + 2) % 3 = 1 := by omega
      obtain ⟨j, Vr, hp, b1, b2⟩ := shv_pend ((v + 2) / 3 + 1) (by omega)
      have hne : (v + 2) % 3 ≠ 0 := h0
      refine ⟨l, a, j, Vr, ha, hok, ⟨?_, ?_, Or.inl ⟨Pend_pos hp, ?_, Or.inl ?_⟩⟩, ?_, ?_, hE⟩
      · simp only [absStep, hne, h2, if_false]; exact (epL_zero l a ha).symm
      · simp only [absStep, hne, h2, if_false]; omega
      · simp only [absStep, hne, h2, if_false]; (try unfold EE); omega
      · simp only [absStep, hne, h2, if_false, Nat.sub_zero]; exact hp
      · (try unfold EE); omega
      · (try unfold EE); omega

/-- `n` model steps -/
def itr : Nat → AS → AS
  | 0, S => S
  | n + 1, S => mstep (itr n S)

theorem epoch_iter (l a R Vr : Nat) (S0 : AS) (ha : a < 2 ^ (l + 1)) (hR : R + 1 ≤ EE l a)
    (h0 : EpInv l a R Vr 0 S0) :
    ∀ i, i ≤ EE l a → EpInv l a R Vr i (itr i S0) ∧
      (i = 0 ∨ Adv (tape S0) (tape (itr i S0))) := by
  intro i
  induction i with
  | zero => intro _; exact ⟨h0, Or.inl rfl⟩
  | succ i ih =>
    intro hi
    obtain ⟨h1, h2⟩ := ih (by omega)
    obtain ⟨hok, h3⟩ := epoch_step l a R Vr i _ ha hR (by omega) h1
    show EpInv l a R Vr (i + 1) (mstep (itr i S0)) ∧ (i + 1 = 0 ∨ Adv (tape S0) (tape (mstep (itr i S0))))
    refine ⟨h3, Or.inr ?_⟩
    rcases h2 with h2 | h2
    · subst h2; exact sim _ hok
    · exact h2.trans (sim _ hok)

theorem epoch_end (l a R Vr : Nat) (S : AS) (ha : a < 2 ^ (l + 1)) (hR : R + 1 ≤ EE l a)
    (hV : 5 * (Vr + EE l a - R) ≤ 6 * (EE l a + 1)) (hE : 15 ≤ EE l a)
    (h : EpInv l a R Vr (EE l a) S) : PreInv S := by
  obtain ⟨hL, hk, hc⟩ := h
  have hP := two_le_pow l
  have hpow : 2 ^ (l + 1 + 1) = 2 * 2 ^ (l + 1) := by rw [Nat.pow_succ]; omega
  rcases hc with ⟨h1, _, _⟩ | ⟨h1, h2, h3⟩
  · omega
  unfold EE at *
  have hL' : S.L = Lam (l + 1) (2 * a + 1) := by
    rw [hL]; unfold epL; rw [if_neg (by omega)]; congr 1; omega
  by_cases hlast : a + 1 < 2 ^ (l + 1)
  · refine ⟨l, a + 1, Vr + (2 ^ (l + 1) + a + 1) - R, hlast, h3, by omega, hk, ?_, by omega, ?_, ?_⟩
    · rw [hL']; unfold preL; rw [if_neg (by omega)]; congr 1
    · (try unfold EE); omega
    · (try unfold EE); omega
  · refine ⟨l + 1, 0, Vr + (2 ^ (l + 1) + a + 1) - R, by omega, h3, by omega, hk, ?_, by omega, ?_, ?_⟩
    · rw [hL']; unfold preL; rw [if_pos rfl, ← Lam_top]; congr 1; omega
    · (try unfold EE); omega
    · (try unfold EE); omega

/-- **Epoch theorem** -/
theorem epoch (S : AS) (h : PreInv S) : ∃ S', PreInv S' ∧ Adv (tape S) (tape S') := by
  obtain ⟨l, a, R, Vr, ha, hok, h0, hR, hV, hE⟩ := epoch_start S h
  obtain ⟨hEnd, hAdv⟩ := epoch_iter l a R Vr _ ha hR h0 (EE l a) (Nat.le_refl _)
  refine ⟨_, epoch_end l a R Vr _ ha hR hV hE hEnd, ?_⟩
  have a0 := sim S hok
  rcases hAdv with h1 | h1
  · unfold EE at h1; omega
  · exact a0.trans h1

/-! ## non-halting from a pre-absorption state -/

theorem tape_st (S : AS) : (tape S).st = .B := rfl

theorem nonhalt_from (c : Cfg) (S : AS) (hS : PreInv S) (hc : PE c (tape S)) :
    ∀ n, ¬ halted (run n c) := by
  have key : ∀ t, ∃ n, t ≤ n ∧ ∃ S, PreInv S ∧ PE (run n c) (tape S) := by
    intro t
    induction t with
    | zero => exact ⟨0, (Nat.le_refl _), S, hS, hc⟩
    | succ t ih =>
      obtain ⟨n, hn, S1, h1, h2⟩ := ih
      obtain ⟨S2, h3, d, hd, h4⟩ := epoch S1 h1
      refine ⟨n + d, by omega, S2, h3, ?_⟩
      rw [run_add]
      exact (PE_run d h2).trans h4
  intro n hn
  obtain ⟨N, hN, S1, _, h2⟩ := key n
  have e : run N c = run n c := by
    rw [show N = n + (N - n) by omega, run_add]
    exact run_H _ _ hn
  have := h2.1
  rw [e, hn] at this
  exact absurd this (by rw [tape_st]; decide)

end M8.R3
