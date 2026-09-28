> Release note: these are the working notes of the development, kept verbatim apart from paths.
> The released proof is the R3 chain only (see "R3 FINAL" at the end). Files mentioned here that are
> not in `lean/` (M8/Ladder, Digits, Step, Inv, InvStep, Abs, Sim, the M8/R3/ folder, tools other than
> `sim/`) belong to an abandoned parallel attempt and are not part of the proof. `M8/Abs.lean` and
> `M8/Sim.lean` in the round-3 model description correspond to the released `M8/R3Abs.lean` and
> `M8/R3Sim.lean`; `tools/r3/*.py` are in `sim/`.

# M8 Lean proof — progress notes
Machine 1RB0RA_0LC0LA_1RF1LD_1LE0LD_1LC1LF_---1RA (F on 0 halts). Build:
`cd lean && lake build`. No Mathlib, toolchain v4.33.1.
Math source: exact-NOTES.md (this folder).

## Lean-level encoding (validated: val.py random instances, val2.py = real can3.txt checkpoints 299/299)
Cells Bool, Cfg = ⟨st, L (nearest first), h, R⟩ as in m7.
 Lu = .111 = [f,t,t,t] (tape order), Rr = reverse(11..) = [f,f,t,t], Mr = reverse(1111..) = [f,f,t,t,t,t].
 hc P R = ⟨B, t::P, t, [t,t]++R⟩   (H unit "1111", head on its 2nd cell)
 dc L R = ⟨D, L.tail, L.headD f, R⟩ (left sweep: D on last cell of the unit L starts with)
 ac L R = ⟨A, L, R.headD f, R.tail⟩
 counter digits LSB-first, rdig 0/1/2 = reverse(... / 11. / 1..) ; Sr ds = flatMap rdig ds.
 canonical checkpoint = hc (Rr^k ++ Sr ds ++ Lt) (Lu^m ++ tail), B1 = k+1+m,
 tail = rtt bs ([f,f] ++ X) with rtt bs = seps '1.' each followed by Lu^b (first 0-sep = '..').
## Micro events (exact step counts)
 unit  hc P (Lu++R) ->18 hc (Rr++P) R ;  pass '1.': hc (Rr++P) ([t,f]++R) ->36 hc (Mr++P) R
 turn  hc P ([f,f]++X) ->24 dc P (Lu++[t,f]++X)   (also the overflow end: H + blank = H + '..')
 left  dc (Rr++L) R ->4 dc L (Lu++R) ; marker dc (Mr++L) R ->6 dc L ([f,f]++Lu++R)  (the 2-unit drift)
 counter: D on digit 2 ->3 (becomes 111, carry left); digit 0/1 ->5 (+1, A at p0); A erases 111 in 3;
   restart ac L (Lu++R) ->1 hc L R.
## Increment (general k, k'; val.py 2000+ random instances exact):
 run (22m + 22Σbs + 38|bs| + 4k + 30 + 6 tz(ds) + 18k')
   (hc (Rr^k ++ Sr ds ++ Lt) (Lu^m ++ rtt bs ([f,f]++X)))
 = hc (Rr^k' ++ Sr (inc ds) ++ Lt) (Lu^m' ++ E bs ++ Lu^2 ++ [t,f] ++ X),  k+m = k'+m'+2, bs all ≥1,
   ds has a non-2 digit (pad a leading 0 digit = 3 blank cells for the new-top-digit case).
 E bs = flatMap ([f,f] ++ Lu^b). With k = 3-min(z,3), k' = 3-min(tz,3) this is exactly the notes formula
 22W + 38j + 8 + 18min(z,3) - 12tz + 18max(0,tz-3).
 Overflow = same lemma with bs ++ [0] and X = [f,f]++X' after the terminal '1.' (validated).

## Round 1 (2026-09-27): plan steps 1-5 DONE, all proven (no sorry/admit/native_decide)
Axioms of incr/ovf/incr_canon/ovf_canon/cnt_top: [propext, Quot.sound] (Check.lean). Full build ~3 s.
- M8/Machine.lean: exact model (F on 0 -> H), run_add, run_H.   M8/Frame.lean: runB/frame (mvDir for M8).
- M8/Micro.lean: unit (18), pass (36; peeks: cell after `1.` must be 0), turn (24), lunit (4), lmark (6),
  dstep/cstep/astep/restart, rsweep (18n), lsweep (4n) by induction.
- M8/Counter.lean: Dg, rdig, Sr, inc, tz, lowOk, val_inc; cdig2 (3), cdig0/cdig1 (5), erase (3);
  cnt : run (6 tz + 5) (dc (Sr ds ++ L) R) = ac (Sr (inc ds) ++ L) R  (lowOk ds);
  cnt_top: all-2 counter + 3 blank cells -> new top digit.
- M8/Incr.lean: rtt/Q/E, swp (right sweep through 1.-blocks), lqp (left sweep back), start/finish,
  incr (general k,k'), ovf (terminal `1.` + blank, new block 2), and canonical corollaries
  incr_canon / ovf_canon with ck ds B1 T := hc (Rr^kc ++ Sr ds) (Lu^(B1-kc-1) ++ T), kc = 3-min(zz,3),
  step count literally the notes formula 22(B1+Σbs)+38|bs|+8+18min(z,3)+18(tz-3)-12tz (Nat), B1 >= 6.
## Next (plan steps 6-9)
- blank normalisation: ck uses Lt = [] and allows leading `z` digits (3 explicit blank cells); prove
  LEq (lists equal up to trailing falses) is preserved by step/run, so padding is free (also right end X).
- Absorb (B1 in {2,4}), PadCounter (misaligned forms), Level, Base (decide +kernel), Main.

## Round 2 (2026-09-27, in progress)
- M8/Pad.lean: (a) DONE. `trim` (drop trailing blanks), `PE c d` (same st/h, L,R equal up to trailing
  blanks), `PE_step`, `PE_run`, `PE_pad`, `PE_halted`. Use: re-pad counters with top zero digits
  (`Sr (ds ++ [.z])` ~ `Sr ds`) so every `cnt` has `lowOk`; `cnt_top` no longer needed.
- tools/: ck1.c (k=0 checkpoints = first proper hc after the counter phase; right side must start
  with Lu / sep+Lu), ext.py (parse: max #Rr = k, counter clean 'C' or lone-1 'X'), an4.py (rule check),
  abs4.py (absorption rule check), epoch.py (realign delay vs epoch), lev.py (ladder at OVF/ABS).
  (ck0.c had detector artifacts in zipper phases -> use ck1.)
- EXACT EVENT TABLE, validated on ALL checkpoints 1e8..2e10 of the real run (974k; 0 exceptions):
  counter forms at checkpoints: clean `Sr ds` or lone-1 `Sr lo ++ [t] ++ Sr hi` (nearest-first);
  an extra `f` cell re-reads: [f]++rdig z = rdig z++[f], [f]++rdig o = rdig t++[t], [f]++rdig t = rdig z++[t].
  (lone-1 with lo=[2] == Rr ++ Sr hi, i.e. the same tape with k+1: parse with max k.)
  INC  (ladder part = incr/ovf lemmas; B1-2 if j>=2, s_j:=1, b_j+2):
   clean: ds -> inc ds ; lone-1, lo has non-2: lo -> inc lo ;
   realign n>=1 (lo = 2^n): -> clean zeros(n-1) ++ inc hi, plus one released unit Rr (B1 += 1)
   realign n=0  (lo = []):  -> [f] ++ Sr (inc (inc hi))  (then re-read), B1 unchanged.
  ABS (only ever at checkpoint B1=2, s1=1, clean counter; 1158/1158): increment runs, A lands on the
   cleared `..`, second counter inc, re-frame by d0 = low digit of inc(inc ds), r = rest:
   d0=0: Rr++[f]++Sr r, m'=b-1 ; d0=2: Rr++[t]++Sr r, m'=b-1 ; d0=1: [f]++Sr(inc r), m'=b
   (b = first block after s1 incl. its +2 if j=2); s1 and b are removed from the ladder; B1'=b+1.
- M8/Forms.lean: carry2, zip (A-zipper, 3 steps/cell), realign_end (10), `realign` (n+1 >= 1),
  `realign0`, absHead, absTailZ/T (11), absTailO1 (8)/O2 (4). All proven.
- M8/Absorb.lean: Reach1, absFirst, `absorbZ/absorbT/absorbO` for arbitrary counters (lowOk hyps)
  and arbitrary `1.`-blocks `b :: bs` before the first `..`. (b) DONE modulo the overflow-coincident
  absorption (all seps 1; not seen in data, but must be excluded or proven).
- Build clean, no sorry/admit/native_decide; axioms of new lemmas ⊆ [propext, Quot.sound].
- LADDER LEVEL STRUCTURE (tools/ladsim.py, abstract rules above, matches real run):
  OV(m,x) := B1=x, m seps all 1, blocks [2^m,...,4,2]. Cycle OV(m,x) -> OV(m,x+2) for x=2..2^(m+1),
  then OV(m,2^(m+1)+2) -> OV(m+1,2). One ABS per cycle, one realign per epoch (ABS -> realign -> ...).
  At level change (OV(m+1,2)) the ABS COINCIDES WITH THE OVERFLOW (B1=2, all seps 1): seen at
  t=16383799, 127044507, 1000300001, 7938247915 -> needs absorb*Ovf variants (ovf path + same tails).
## REMAINING (steps 6'-9)
 1. absorbZ/T/O for the overflow path (rtt bs ([t,f]++[f,f]++X)); same tails, easy.
 2. Ladder abstraction: `lad : List (Bool×Nat) -> List Bool`, `incL`, one-increment lemma from incr/ovf;
    binary-count lemma U(r) (2^r-1 increments from all-0 bits: bit j set 2^(r-j) times, B1 -= 2^r-2).
 3. Level/cycle theorem OV(m,x) -> OV(m,x+2) / OV(m+1,2) with counter kept abstract (form only).
 4. NUMERIC COUPLING IS NEEDED for the counter: the realign must occur before the next exhaustion
    (else a 2-extra-cell counter, which halts ~50% in random tests). Empirical margin: realign delay
    R <= 0.57 * epoch E (epoch.py, 1157 epochs). Proof sketch: after ABS, delay <= 1.5*val(hi'')+1
    (hi'' ~ V/3), E = b+1; potential V + (B1 - s1) is constant on ordinary increments; so need an
    invariant like V_abs <= 2*b_abs - c across cycles (fixed point ~1.5 b). Also V_abs >= 3 so the
    re-read lone cell exists (else B1 stays odd -> B1=1 absorption, not covered).
 5. Base: init -> first OV(m0,x) with counter satisfying the bound (decide +kernel chunks, as m7).
 6. Main: nonhalt via PE_halted + run_H + infinitely many OV checkpoints.

## Round 3 (2026-09-27, started)
Goal: absorb*Ovf, incrLone/incrRealign/incrRealign0 + reread, Inv + step theorem, time bound, Base, Main.

## Round 3 (2026-09-27)
- Disk: keep traces < 1 GB; only small outputs in tools/ (ck0_2e10/ck1_2e10 ~90 MB each are fine).
- M8/AbsOvf.lean: generic absorption tails (absGenZ/T/O: from `A` on cleared s1 with arbitrary
  tail Y) + absFirstOvf (overflow path: all seps `1.`, terminal `1.`, blank) + absorbZo/To/Oo.
KEY DISCOVERY (round 3): ladder is a pure function of N (bits s_i incl. terminal = top bit):
 lad 0 = [], lad N = sep(N%2) ++ Lu^(bk N) ++ lad (N/2), bk N = 2*((N/2+1)/2)  (= 2 floor((N+2)/4)),
 i.e. b_i = 2 floor((N+2^i)/2^(i+1)); checked on real data (all c_i = 0). B1 + 2(N/2) = K (clean),
 = K-1 (lone), K even, absorption at N = K-1, then N' = K/2, K' = K+2.  Counter value W:=val lo+3^|lo| val hi
 rises 1 per increment; realign lo=2^(n+1) -> clean 0^n ++ inc hi (value 3^n(val hi+1), divides by 3!).
 Hence V_abs' = V_R + K' - 1 - N_R ~ V_abs/9 + K/2 : strongly contracting.  Invariant plan:
 clean: V + (K-1-N) =: Vabs, 4 <= Vabs, 3 Vabs <= 2K ; lone (lo /= []): N + (3^|lo| - val lo) + 2 <= K,
 VR := 3^(|lo|-1)(val hi+1), NR := N + 3^|lo| - val lo, same bounds on VR + (K-1-NR).  K >= K0 (~24).
 Reread r = 0^a ++ d :: rest: P=3^a, X=P*val rest, d=1: R=P, VR=X+P, val r=P+3X; d=2: R=3P, VR=X+P, val r=2P+3X
 (linear in P,X -> omega).
- (1) DONE: absorption during overflow, M8/AbsOvf.lean (absGenZ/T/O generic tails, absFirstOvf,
  absorbZo/To/Oo). In the final architecture the ABS is handled generically after the ladder phase
  (dc counter (lad L') with L' = (false,b)::rest) so the overflow case needs no special treatment.
- ABSTRACT MODEL (tools/r3/am2.py = mirror of Lean M8/Abs.lean), VALIDATED exactly vs the real machine
  (render -> run -> render, PE-equality) for 2500 consecutive steps from the pre-ABS state at t=46083
  (and am.py list-version for 3000 steps from t=323):
  state S=(k, C, m, L), B1=k+1+m, tape = hc (Rr^k ++ ctape C) (Lu^m ++ lad L), lad [] = `1.` (+blank)
  C = cl v (Sr (dig v)) | lone lo hv (Sr lo ++ [t] ++ Sr (dig hv))
  linc B [] = (B-2,[(f,2)]); linc B ((f,c)::r) = (B,(t,c)::r);
  linc B ((t,c)::r) = (B-2, (f, (linc c r).1+2) :: (linc c r).2)        [ladder phase, p = new B1]
  step: (p,L') = linc B1 L; p>0: counter phase cph C (k'=1 iff realign) -> (k',C',p-1,L');
  p=0: ABS, L'=(f,b)::rest, C=cl v, W=v+2, q=W/3: W%3=0 -> (1, shv q, b-1, rest);
       W%3=2 -> (1, lone [] q, b-1, rest); W%3=1 -> (0, shv (q+1), b, rest).
  cph: cl v -> cl (v+1); lone lo hv: lowOk lo -> lone (inc lo) hv; lo=[] -> shv(hv+2) (realign0);
       lo=2^n (n>=1) -> k'=1, cl (3^(n-1)(hv+1)) (realign).   shv = re-read of [f] ++ Sr (dig v).
- LADDER CLOSED FORM (tools/r3/cyc.py, verified to level 12): Λ_0 N = [(odd N,2)],
  Λ_{l+1} N = (odd N, 2^(l+1)+2⌊(N+2)/4⌋) :: Λ_l (N/2);  O_0=[], O_{l+1}=(t,2^(l+1))::O_l.
  linc B (Λ_l N) = (B-2[odd N], Λ_l (N+1)) (N+1<2^(l+1)); linc B O_l = (B-2, Λ_l 0); Λ_l(2^(l+1)-1)=O_{l+1}.
  Pre-ABS state (l,a), a<2^l: B1=2, clean counter v, L = O_l (a=0) or Λ_l(2a-1). ABS gives
  Λ_l(2a) = (f,b)::Λ_{l-1}(a), b = 2^l+2⌊(a+1)/2⌋; then EXACTLY E = 2^l+a+1 ordinary steps to the
  pre-ABS state (l,a+1) (or (l+1,0) if a+1=2^l). s1 flips every step, Ψ = B1 - s1 = E - i + [realigned].
- COUNTER BOUND: invariant at pre-ABS: 1 <= v, 5v <= 6E, E >= 15.  Pending after ABS: Pend(C,j,Vr)
  (realign after j phases, clean value Vr after it); shv v (v>=1): 2j <= 3v, 3Vr <= 3j+v.
  => R <= 3(q+2)/2+1 <= E-1 and v' = Vr + E - R <= E + (q+2)/3 <= 6(E+1)/5.  Exhaustive check
  (epo.py): works for all E>=11. Base: pre-ABS (4,0) at t=46083 (v=17, E=17).
- M8/Ladder.lean DONE (proven): ladF/lad (fuelled, kernel-reducible), lad_pos/odd/even, `exc` (excursion
  over the odd ladder, strong induction, handles overflow via 2 blank cells), frontE (N even: dc S (Lu^(k+m+1) ++
  lad(N+1))), frontO (N odd: dc S (Lu^(k+m-1) ++ lad (N+1) ++ blanks)). Replaces rtt/Q/E + all *Ovf variants:
  absorption = frontO with k+m=1 then (lad K = [f,f] ++ Lu^(bk K) ++ lad (K/2)) + absHead/absTail*.
- M8/Abs.lean (model defs: CF, dig, shl/shv, ctape, lad, linc, cph, AS, absStep, mstep, tape;
  trim_Sr_val, sh_tape) and M8/Sim.lean: `sim : okS S → Adv (tape S) (tape (mstep S))`
  (Adv c d := ∃ n>0, PE (run n c) d), via lphase (generic ladder phase incl. overflow, any k,
  B1>=2), cphase (cl / lone lowOk / realign0 / realign, with zero-padding by PE), aphase (ABS,
  3 cases). ALL PROVEN, no sorry.
- M8/Digits.lean DONE: val_cons/val_lt/lowOk_iff/length_inc/lowOk_app(_z)/inc_app/val_app/val_zeros(_app)/
  val_twos/twos_of_not_lowOk/Sr_app(_zeros), `reread` ([f]++Sr x = Sr lo ++ [t] ++ Sr hi with P=3^a, X=P*val hi,
  (val lo=2P ∧ val x=P+3X) ∨ (val lo=0 ∧ val x=2P+3X)).
- M8/Step.lean DONE: PE_hcL/PE_hcR, Adv (positive run up to PE) + combinators, CP (counter phase) with
  cpClean/cpLone/cpRealign/cpRealign0, incStep (generic increment, any N>=1), absPre/absFront.
- M8/Inv.lean DONE so far: absZc/absTc/absOc (absorption incl. overflow-coincident, canonical output),
  cleanOK/loneOK/ClS/LoS/Inv (K>=24). Next: inv_step (M8/InvStep.lean).

!! COLLISION NOTICE (round-3 agent "R3", 22:25): two agents are working in this directory. My
`cat > M8/Ladder.lean` at 22:24:50 accidentally OVERWROTE the other agent's M8/Ladder.lean
(ladF/lad/exc/frontE/frontO). Its source is lost (olean also rebuilt) -- the other agent must
re-create it. Sorry. To avoid further clashes all my round-3 files are now prefixed `R3` and live
in `namespace M8.R3`: M8/AbsOvf.lean (namespace M8, harmless), M8/R3Abs.lean, M8/R3Sim.lean,
M8/R3Ladder.lean, (next) M8/R3Epoch.lean, M8/R3Base.lean, M8/R3Main.lean. Build mine with
`lake build M8.R3Main` (I do not edit M8.lean or the other agent's files).
- !! ROUND-3 COLLISION: another agent works concurrently in M8/ (Abs.lean, AbsOvf.lean, Sim.lean, and it
  overwrote M8/Ladder.lean with its own "Ladder closed forms"). To avoid clobbering, THIS agent's files now
  live in M8/R3/ (namespace M8.R3): Ladder, Digits, Step, Inv, InvStep (+ Base, Main to come).
  Build: `lake build M8.R3.Main`. The notes lines above about M8/Ladder.lean/Digits/Step/Inv refer to M8/R3/*.
- R3 progress: M8/R3Ladder.lean (Lam/Ol/epL, linc_Lam, linc_Ol, Lam_top, Lam_even, linc_epL),
  M8/R3Epoch.lean (val_lt, lowOk_iff, Pend/PendX, cph_pend2/1, shv_pend bounds, PreInv, EpInv,
  epoch_step), M8/R3Cycle.lean (epoch_start, epoch_iter, epoch_end, `epoch : PreInv S → ∃ S',
  PreInv S' ∧ Adv (tape S) (tape S')`, `nonhalt_from : PreInv S → PE c (tape S) → ∀ n, ¬halted (run n c)`)
  ALL PROVEN. Remaining: base case (run 46083 init PE tape ⟨0, cl 17, 1, Ol 4⟩, PreInv with l=3,a=0).
## R3 FINAL (2026-09-27): NONHALTING PROVEN
`M8.R3.nonhalt : ∀ n, ¬ halted (run n init)` in M8/R3Main.lean; `lake build M8.R3Main` (~3 s after deps).
#print axioms: [propext, Classical.choice, Quot.sound]. No sorry/admit/native_decide in the R3 chain
(Machine, Frame, Micro, Counter, Incr, Pad, Forms, Absorb, AbsOvf, R3Abs, R3Sim, R3Ladder, R3Epoch,
R3Cycle, R3Main). Base: `run 46083 init = c0` by decide +kernel, c0 PE tape ⟨0, cl 17, 1, Ol 4⟩ = PreInv
with (l,a)=(3,0), v=17, E=17. Then `epoch` (pre-ABS -> pre-ABS, E+1 >= 1 model steps, each `sim`)
+ `nonhalt_from`. M8.lean (root, edited by the other agent) does not import the R3 files.
