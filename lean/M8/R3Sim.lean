import M8.R3Abs
namespace M8.R3
open List

/-! # Simulation: one abstract step `mstep` is realised by the machine (up to blank padding). -/

/-- `c` reaches (a configuration equal up to trailing blanks to) `d` in a positive number of steps -/
def Adv (c d : Cfg) : Prop := ∃ n, 0 < n ∧ PE (run n c) d

theorem Adv.trans {c d e : Cfg} (h1 : Adv c d) (h2 : Adv d e) : Adv c e := by
  obtain ⟨a, ha, e1⟩ := h1
  obtain ⟨b, hb, e2⟩ := h2
  exact ⟨a + b, by omega, by rw [run_add]; exact (PE_run b e1).trans e2⟩

theorem Adv_run {n : Nat} {c d : Cfg} (h : run n c = d) (hn : 0 < n) : Adv c d :=
  ⟨n, hn, h ▸ PE.refl _⟩

theorem Adv.pe_left {c c' d : Cfg} (h : PE c c') (h2 : Adv c' d) : Adv c d := by
  obtain ⟨n, hn, e⟩ := h2
  exact ⟨n, hn, (PE_run n h).trans e⟩

theorem Adv.pe_right {c d d' : Cfg} (h2 : Adv c d) (h : PE d d') : Adv c d' := by
  obtain ⟨n, hn, e⟩ := h2
  exact ⟨n, hn, e.trans h⟩

theorem PE_dc {L L' : List Bool} (h : trim L = trim L') (R : List Bool) : PE (dc L R) (dc L' R) := by
  refine ⟨rfl, ?_, ?_, rfl⟩
  · show L.headD false = L'.headD false
    rw [← trim_headD, h, trim_headD]
  · show trim L.tail = trim L'.tail
    rw [trim_tail, h, trim_tail]

theorem PE_hc {P P' : List Bool} (h : trim P = trim P') (R : List Bool) : PE (hc P R) (hc P' R) := by
  refine ⟨rfl, rfl, ?_, rfl⟩
  show trim (true :: P) = trim (true :: P')
  simp [h]

theorem PE_hcR (P : List Bool) {R R' : List Bool} (h : trim R = trim R') : PE (hc P R) (hc P R') := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  show trim ([true, true] ++ R) = trim ([true, true] ++ R')
  exact trim_append_congr _ h

theorem PE_dc_R {S R R' : List Bool} (h : R = R') : PE (dc S R) (dc S R') := h ▸ PE.refl _

theorem trim_zpad (l : List Bool) (ds : List Dg) (n : Nat) :
    trim (l ++ Sr (ds ++ List.replicate n .z)) = trim (l ++ Sr ds) := by
  rw [Sr_append, ← List.append_assoc, trim_append_blank]
  intro x hx
  simp [Sr, List.mem_flatMap, List.mem_replicate] at hx
  obtain ⟨_, ⟨_, rfl⟩, hx⟩ := hx
  simp [rdig] at hx; exact hx

/-! ## ladder algebra -/

def tl (bs : List Nat) : List (Bool × Nat) := bs.map (fun b => (true, b))

theorem lad_tl (bs : List Nat) (M : List (Bool × Nat)) : lad (tl bs ++ M) = rtt bs (lad M) := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [tl, lad, rtt] at ih ⊢; rw [ih]

theorem rtt_app (bs : List Nat) (R Y : List Bool) : rtt bs R ++ Y = rtt bs (R ++ Y) := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [rtt, ih]

def lincT : List Nat → List (Bool × Nat)
  | [] => []
  | [b] => [(false, b + 2)]
  | b :: b' :: bs => (false, b) :: lincT (b' :: bs)

theorem linc_split (bs : List Nat) (hb : ∀ b ∈ bs, 2 ≤ b) (c : Nat) (r : List (Bool × Nat)) (B : Nat) :
    linc B (tl bs ++ (false, c) :: r) = (if bs = [] then B else B - 2, lincT bs ++ (true, c) :: r) := by
  induction bs generalizing B with
  | nil => rfl
  | cons b bs ih =>
    have ih' := ih (fun x hx => hb x (by simp [hx])) b
    have hb0 := hb b (by simp)
    simp only [tl, List.map_cons, List.cons_append] at ih' ⊢
    rw [linc, ih']
    cases bs with
    | nil => simp [lincT]
    | cons b' bs => simp [lincT]; omega

theorem lad_lincT (bs : List Nat) (hbs : bs ≠ []) (M : List (Bool × Nat)) :
    lad (lincT bs ++ M) = E bs ++ pw Lu 2 ++ lad M := by
  induction bs with
  | nil => exact absurd rfl hbs
  | cons b bs ih =>
    cases bs with
    | nil =>
      simp only [lincT, List.cons_append, List.nil_append, lad, E, if_false]
      rw [pw_add]; simp [List.append_assoc]
    | cons b' bs =>
      have := ih (by simp)
      simp only [lincT, List.cons_append, lad, if_false] at this ⊢
      rw [this]; simp [E, List.append_assoc]

theorem linc_tl (bs : List Nat) (hb : ∀ b ∈ bs, 2 ≤ b) (B : Nat) :
    linc B (tl bs) = (B - 2, bs.map (fun b => (false, b)) ++ [(false, 2)]) := by
  induction bs generalizing B with
  | nil => rfl
  | cons b bs ih =>
    have ih' := ih (fun x hx => hb x (by simp [hx])) b
    have hb0 := hb b (by simp)
    simp only [tl, List.map_cons] at ih' ⊢
    rw [linc, ih']
    simp; omega

theorem lad_fl (bs : List Nat) (M : List (Bool × Nat)) :
    lad (bs.map (fun b => (false, b)) ++ M) = E bs ++ lad M := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp [lad, E, ih, List.append_assoc]

theorem lad_decomp (L : List (Bool × Nat)) :
    (∃ bs c r, L = tl bs ++ (false, c) :: r) ∨ ∃ bs, L = tl bs := by
  induction L with
  | nil => exact Or.inr ⟨[], rfl⟩
  | cons x r ih =>
    obtain ⟨s, b⟩ := x
    cases s with
    | false => exact Or.inl ⟨[], b, r, rfl⟩
    | true =>
      rcases ih with ⟨bs, c, r', rfl⟩ | ⟨bs, rfl⟩
      · exact Or.inl ⟨b :: bs, c, r', rfl⟩
      · exact Or.inr ⟨b :: bs, rfl⟩

/-! ## the ladder phase: from a checkpoint to `D` arriving at the counter -/

theorem lphase (k m : Nat) (hkm : 1 ≤ k + m) (S : List Bool) (L : List (Bool × Nat))
    (hL : ∀ x ∈ L, 2 ≤ x.2) :
    Adv (hc (pw Rr k ++ S) (pw Lu m ++ lad L))
      (dc S (pw Lu (linc (k + 1 + m) L).1 ++ lad (linc (k + 1 + m) L).2)) := by
  obtain ⟨n, hn⟩ : ∃ n, m + k = n + 1 := ⟨k + m - 1, by omega⟩
  rcases lad_decomp L with ⟨bs, c, r, rfl⟩ | ⟨bs, rfl⟩
  · have hb2 : ∀ b ∈ bs, 2 ≤ b := fun b hb => hL (true, b) (by simp [tl, hb])
    have hb1 : ∀ b ∈ bs, 1 ≤ b := fun b hb => by have := hb2 b hb; omega
    have eL : lad (tl bs ++ (false, c) :: r) = rtt bs ([false, false] ++ (pw Lu c ++ lad r)) := by
      rw [lad_tl]; simp [lad]
    rw [eL, linc_split bs hb2]
    have s1 := start bs hb1 k m n hn S ([false, false] ++ (pw Lu c ++ lad r))
    have s2 := turn (Rr ++ Q bs (pw Rr n ++ S)) (pw Lu c ++ lad r)
    have s3 := lunit (Q bs (pw Rr n ++ S)) (Lu ++ [true, false] ++ (pw Lu c ++ lad r))
    have s4 := lqp bs hb1 (pw Rr n ++ S) (Lu ++ (Lu ++ [true, false] ++ (pw Lu c ++ lad r)))
    have s5 := lsweep n S (E bs ++ (Lu ++ (Lu ++ [true, false] ++ (pw Lu c ++ lad r))))
    refine Adv_run (run_trans s1 (run_trans s2 (run_trans s3 (run_trans s4 s5)))) (by omega) |>.pe_right ?_
    refine PE_dc_R ?_
    by_cases hbs : bs = []
    · subst hbs
      simp only [if_true, E, List.nil_append, lincT]
      rw [show k + 1 + m = n + 2 by omega, pw_add]
      simp [lad, List.append_assoc]
    · simp only [hbs, if_false, lad_lincT bs hbs]
      rw [show k + 1 + m - 2 = n by omega]
      simp [lad, List.append_assoc]
  · have hb2 : ∀ b ∈ bs, 2 ≤ b := fun b hb => hL (true, b) (by simp [tl, hb])
    have hb1 : ∀ b ∈ bs, 1 ≤ b := fun b hb => by have := hb2 b hb; omega
    rw [linc_tl bs hb2, lad_fl]
    have ep : PE (hc (pw Rr k ++ S) (pw Lu m ++ lad (tl bs)))
        (hc (pw Rr k ++ S) (pw Lu m ++ rtt bs ([true, false] ++ false :: [false]))) := by
      apply PE_hcR
      rw [show lad (tl bs) = rtt bs [true, false] by simpa [lad] using lad_tl bs []]
      rw [show [true, false] ++ false :: [false] = [true, false] ++ [false, false] from rfl, ← rtt_app,
        ← List.append_assoc]
      exact (trim_append_blank _ [false, false] (by simp)).symm
    refine Adv.pe_left ep ?_
    have s1 := start bs hb1 k m n hn S ([true, false] ++ false :: [false])
    have s2 := pass (Q bs (pw Rr n ++ S)) [false]
    have s3 : run 24 (hc (Mr ++ Q bs (pw Rr n ++ S)) (false :: [false]))
        = dc (Mr ++ Q bs (pw Rr n ++ S)) (Lu ++ [true, false] ++ []) := turn _ []
    have s4 := lmark (Q bs (pw Rr n ++ S)) (Lu ++ [true, false] ++ [])
    have s5 := lqp bs hb1 (pw Rr n ++ S) ([false, false] ++ Lu ++ (Lu ++ [true, false] ++ []))
    have s6 := lsweep n S (E bs ++ ([false, false] ++ Lu ++ (Lu ++ [true, false] ++ [])))
    refine Adv_run (run_trans s1 (run_trans s2 (run_trans s3 (run_trans s4 (run_trans s5 s6)))))
      (by omega) |>.pe_right ?_
    rw [show k + 1 + m - 2 = n by omega]
    apply PE_dc_R
    simp [lad, pw_add, List.append_assoc]

/-! ## counter algebra -/

theorem lowOk_app_z (l : List Dg) : lowOk (l ++ [.z]) = true := by
  induction l with
  | nil => rfl
  | cons d r ih => cases d <;> simp [lowOk, ih]

theorem inc_app (l X : List Dg) (h : lowOk l = true) : inc (l ++ X) = inc l ++ X := by
  induction l with
  | nil => simp [lowOk] at h
  | cons d r ih =>
    cases d with
    | z => rfl
    | o => rfl
    | t => simp only [lowOk] at h; simp [inc, ih h]

theorem inc_ne_nil (l : List Dg) : inc l ≠ [] := by
  cases l with
  | nil => simp [inc]
  | cons d r => cases d <;> simp [inc]

theorem val_rep_z (n : Nat) : val (List.replicate n Dg.z) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => rw [List.replicate_succ, val_cons, ih]; rfl

theorem lowOk_false_rep (lo : List Dg) (h : lowOk lo = false) : lo = List.replicate lo.length .t := by
  induction lo with
  | nil => rfl
  | cons d r ih =>
    cases d with
    | z => simp [lowOk] at h
    | o => simp [lowOk] at h
    | t => simp only [lowOk] at h; simp [List.replicate_succ]; exact ih h

theorem val_inc2pad (v : Nat) :
    ∃ d0 r, inc (inc (dig v ++ [.z, .z, .z])) = d0 :: r ∧ lowOk r = true ∧ dv d0 + 3 * val r = v + 2 ∧
      lowOk (dig v ++ [.z, .z, .z]) = true ∧ lowOk (inc (dig v ++ [.z, .z, .z])) = true := by
  have e1 : inc (dig v ++ [.z, .z, .z]) = inc (dig v ++ [.z]) ++ [.z, .z] := by
    rw [show dig v ++ [.z, .z, .z] = (dig v ++ [.z]) ++ [.z, .z] by simp, inc_app _ _ (lowOk_app_z _)]
  have e2 : inc (inc (dig v ++ [.z]) ++ [.z, .z]) = inc (inc (dig v ++ [.z]) ++ [.z]) ++ [.z] := by
    rw [show inc (dig v ++ [.z]) ++ [.z, .z] = (inc (dig v ++ [.z]) ++ [.z]) ++ [.z] by simp,
      inc_app _ _ (lowOk_app_z _)]
  obtain ⟨d0, l2, hl2⟩ : ∃ d0 l2, inc (inc (dig v ++ [.z]) ++ [.z]) = d0 :: l2 := by
    cases h : inc (inc (dig v ++ [.z]) ++ [.z]) with
    | nil => exact absurd h (inc_ne_nil _)
    | cons d l => exact ⟨d, l, rfl⟩
  refine ⟨d0, l2 ++ [.z], ?_, lowOk_app_z _, ?_, ?_, ?_⟩
  · rw [e1, e2, hl2]; rfl
  · have hv : val (inc (inc (dig v ++ [.z, .z, .z]))) = v + 2 := by
      rw [val_inc, val_inc, val_append, val_dig]; simp [val]
    rw [e1, e2, hl2] at hv
    rw [← val_cons]; simpa [val_append, val] using hv
  · rw [show dig v ++ [.z, .z, .z] = (dig v ++ [.z, .z]) ++ [.z] by simp]; exact lowOk_app_z _
  · rw [e1, show inc (dig v ++ [.z]) ++ [.z, .z] = (inc (dig v ++ [.z]) ++ [.z]) ++ [.z] by simp]
    exact lowOk_app_z _

/-! ## the counter phase -/

theorem cphase (C : CF) (p : Nat) (R : List Bool) :
    Adv (dc (ctape C) (pw Lu (p + 1) ++ R)) (hc (pw Rr (cph C).1 ++ ctape (cph C).2) (pw Lu p ++ R)) := by
  have eR : pw Lu (p + 1) ++ R = Lu ++ (pw Lu p ++ R) := by simp [List.append_assoc]
  rw [eR]
  cases C with
  | cl v =>
    have hok := lowOk_app_z (dig v)
    have e0 : PE (dc (Sr (dig v)) (Lu ++ (pw Lu p ++ R))) (dc (Sr (dig v ++ [.z]) ++ []) (Lu ++ (pw Lu p ++ R))) := by
      apply PE_dc; simpa using (trim_zpad [] (dig v) 1).symm
    refine Adv.pe_left e0 ?_
    have s1 := cnt _ hok [] (Lu ++ (pw Lu p ++ R))
    have s2 := restart (Sr (inc (dig v ++ [.z])) ++ []) (pw Lu p ++ R)
    refine Adv_run (run_trans s1 s2) (by omega) |>.pe_right ?_
    apply PE_hc
    simp only [cph, ctape, pw_zero, List.nil_append, List.append_nil]
    apply trim_Sr_val
    rw [val_inc, val_append, val_dig, val_dig]; simp [val]
  | lone lo hv =>
    by_cases hok : lowOk lo = true
    · have s1 := cnt lo hok ([true] ++ Sr (dig hv)) (Lu ++ (pw Lu p ++ R))
      have s2 := restart (Sr (inc lo) ++ ([true] ++ Sr (dig hv))) (pw Lu p ++ R)
      refine Adv_run ?_ (show 0 < (6 * tz lo + 5) + 1 by omega)
      simp only [cph, hok, if_true, ctape, pw_zero, List.nil_append, List.append_assoc]
      exact run_trans s1 s2
    · have hok' : lowOk lo = false := by simpa using hok
      by_cases hlo : lo = []
      · subst hlo
        have h1 : lowOk (dig hv ++ [.z, .z]) = true := by
          rw [show dig hv ++ [.z, .z] = (dig hv ++ [.z]) ++ [.z] by simp]; exact lowOk_app_z _
        have h2 : lowOk (inc (dig hv ++ [.z, .z])) = true := by
          rw [show dig hv ++ [.z, .z] = (dig hv ++ [.z]) ++ [.z] by simp, inc_app _ _ (lowOk_app_z _)]
          exact lowOk_app_z _
        have e0 : PE (dc (ctape (.lone [] hv)) (Lu ++ (pw Lu p ++ R)))
            (dc ([true] ++ Sr (dig hv ++ [.z, .z]) ++ []) (Lu ++ (pw Lu p ++ R))) := by
          apply PE_dc; simp only [ctape, Sr_nil, List.nil_append, List.append_nil]
          exact (trim_zpad [true] (dig hv) 2).symm
        refine Adv.pe_left e0 ?_
        have s := realign0 _ h1 h2 [] (pw Lu p ++ R)
        refine Adv_run s (by omega) |>.pe_right ?_
        apply PE_hc
        have hc : cph (.lone [] hv) = (0, shv (hv + 2)) := by simp [cph, lowOk]
        rw [hc]; simp only [pw_zero, List.nil_append, List.append_nil]
        rw [← sh_tape]
        apply trim_append_congr
        apply trim_Sr_val
        rw [val_inc, val_inc, val_append, val_dig, val_dig]; simp [val]
      · obtain ⟨n, hn⟩ : ∃ n, lo.length = n + 1 := ⟨lo.length - 1, by
          cases lo with
          | nil => exact absurd rfl hlo
          | cons _ _ => simp⟩
        have hrep := lowOk_false_rep lo hok'
        rw [hn] at hrep
        have h1 := lowOk_app_z (dig hv)
        have e0 : PE (dc (ctape (.lone lo hv)) (Lu ++ (pw Lu p ++ R)))
            (dc (Sr (List.replicate (n + 1) Dg.t) ++ [true] ++ Sr (dig hv ++ [.z]) ++ []) (Lu ++ (pw Lu p ++ R))) := by
          apply PE_dc; simp only [ctape, List.append_nil]; rw [← hrep]
          have := trim_zpad (Sr lo ++ [true]) (dig hv) 1
          simp only [List.replicate] at this; exact this.symm
        refine Adv.pe_left e0 ?_
        have s := realign n _ h1 [] (pw Lu p ++ R)
        refine Adv_run s (by omega) |>.pe_right ?_
        apply PE_hc
        have hc : cph (.lone lo hv) = (1, .cl (3 ^ n * (hv + 1))) := by simp [cph, hok', hlo, hn]
        rw [hc]; simp only [pw_succ, pw_zero, List.append_nil, ctape]
        rw [List.append_assoc]
        apply trim_append_congr
        rw [← Sr_append]
        apply trim_Sr_val
        rw [val_append, val_rep_z, val_inc, val_append, val_dig, val_dig, List.length_replicate]
        simp [val]

/-! ## the absorption phase -/

theorem aphase (v b : Nat) (hb : 1 ≤ b) (rest : List (Bool × Nat)) :
    Adv (dc (ctape (.cl v)) (pw Lu 0 ++ lad ((false, b) :: rest)))
      (tape (absStep (.cl v) ((false, b) :: rest))) := by
  obtain ⟨d0, r, hr, hok, hval, h1, h2⟩ := val_inc2pad v
  have eY : pw Lu 0 ++ lad ((false, b) :: rest) = [false, false] ++ (pw Lu b ++ lad rest) := by
    simp [lad]
  rw [eY]
  have e0 : PE (dc (ctape (.cl v)) ([false, false] ++ (pw Lu b ++ lad rest)))
      (dc (Sr (dig v ++ [.z, .z, .z]) ++ []) ([false, false] ++ (pw Lu b ++ lad rest))) := by
    apply PE_dc; simpa [ctape] using (trim_zpad [] (dig v) 3).symm
  refine Adv.pe_left e0 ?_
  have s1 := cnt _ h1 [] ([false, false] ++ (pw Lu b ++ lad rest))
  have s2 := absHead (Sr (inc (dig v ++ [.z, .z, .z])) ++ []) (pw Lu b ++ lad rest)
  have s3 := cnt _ h2 [] ([true, false] ++ (pw Lu b ++ lad rest))
  rw [hr] at s3
  have hd : dv d0 ≤ 2 := by cases d0 <;> simp [dv]
  have hq : (v + 2) / 3 = val r := by omega
  cases d0 with
  | z =>
    have s4 := absGenZ r b hb [] (lad rest)
    rw [show [true, false] ++ pw Lu b ++ lad rest = [true, false] ++ (pw Lu b ++ lad rest) from
    List.append_assoc _ _ _] at s4
    have hm : (v + 2) % 3 = 0 := by simp [dv] at hval; omega
    refine Adv_run (run_trans s1 (run_trans s2 (run_trans s3 s4))) (by omega) |>.pe_right ?_
    simp only [absStep, hm, if_true, tape, pw_succ, pw_zero, List.append_nil]
    apply PE_hc
    rw [hq, List.append_assoc]
    apply trim_append_congr
    rw [← sh_tape]; exact trim_append_congr _ (trim_Sr_dig r)
  | t =>
    have s4 := absGenT r b hb [] (lad rest)
    rw [show [true, false] ++ pw Lu b ++ lad rest = [true, false] ++ (pw Lu b ++ lad rest) from
    List.append_assoc _ _ _] at s4
    have hm : (v + 2) % 3 = 2 := by simp [dv] at hval; omega
    refine Adv_run (run_trans s1 (run_trans s2 (run_trans s3 s4))) (by omega) |>.pe_right ?_
    simp only [absStep, hm, show (2:Nat) ≠ 0 by omega, if_false, if_true, tape, pw_succ, pw_zero,
      List.append_nil, ctape]
    apply PE_hc
    rw [hq, List.append_assoc]
    apply trim_append_congr
    exact trim_append_congr _ (trim_Sr_dig r)
  | o =>
    have s4 := absGenO r hok b hb [] (lad rest)
    rw [show [true, false] ++ pw Lu b ++ lad rest = [true, false] ++ (pw Lu b ++ lad rest) from
    List.append_assoc _ _ _] at s4
    have hm : (v + 2) % 3 = 1 := by simp [dv] at hval; omega
    refine Adv_run (run_trans s1 (run_trans s2 (run_trans s3 s4))) (by omega) |>.pe_right ?_
    simp only [absStep, hm, show (1:Nat) ≠ 0 by omega, show (1:Nat) ≠ 2 by omega, if_false, tape, pw_zero,
      List.nil_append, List.append_nil]
    apply PE_hc
    rw [hq, ← sh_tape]
    apply trim_append_congr
    apply trim_Sr_val
    rw [val_inc, val_dig]

/-! ## one abstract step -/

def okS (S : AS) : Prop :=
  1 ≤ S.k + S.m ∧ (∀ x ∈ S.L, 2 ≤ x.2) ∧
  ((linc (S.k + 1 + S.m) S.L).1 = 0 → (∃ v, S.C = .cl v) ∧
    ∃ b rest, (linc (S.k + 1 + S.m) S.L).2 = (false, b) :: rest ∧ 1 ≤ b)

theorem sim (S : AS) (h : okS S) : Adv (tape S) (tape (mstep S)) := by
  obtain ⟨h1, h2, h3⟩ := h
  have a1 := lphase S.k S.m h1 (ctape S.C) S.L h2
  show Adv (hc (pw Rr S.k ++ ctape S.C) (pw Lu S.m ++ lad S.L)) _
  unfold mstep
  revert h3 a1
  generalize linc (S.k + 1 + S.m) S.L = q
  obtain ⟨p, L'⟩ := q
  intro h3 a1
  cases p with
  | zero =>
    obtain ⟨⟨v, hv⟩, b, rest, hL, hb⟩ := h3 rfl
    simp only at hL; subst hL
    rw [hv] at a1 ⊢
    exact a1.trans (aphase v b hb rest)
  | succ p =>
    exact a1.trans (cphase S.C p (lad L'))

end M8.R3
