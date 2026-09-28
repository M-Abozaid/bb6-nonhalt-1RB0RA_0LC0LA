# M8 exact decode (2026-09-27) — working notes
Tools: tm.h (C sim + tokenizer), dump/turns/turns2 (tapes at reversals), lpos/rpos (L-/R-turn positions),
ovf/ovf2 (at ladder overflows), canon2/canon3 (CANONICAL checkpoints), cut.c (perturbation), mt.py (micro tracer).

## Canonical checkpoint (canon2.c)
First moment after each left-turn that head = state B on a 1 with pattern `1b11` followed by `.111`.
Tape then = S | (11..)^k H | L-phase ladder, where
 - S = left counter, 3-cell ternary digits, MSB left: `...`=0, `11.`=1, `1..`=2, occupying [p0-3n, p0).
 - k = R-phase units left of head = max(0, 3 - #trailing-zero-digits(S)); B1 := k+1+(L-units right of H).
 - ladder: B1 s1 b2 s2 ... b_r "1." (terminal). s_i in {0:'..', 1:'1.'}  (L-phase separators = bits, LSB = s1).
Example: `11.11.1..11.1..1.. | 410 0 512 0 256 0 ... 4 0 2 0 2 T:1.`

## Increment rule (verified on ~1e6 checkpoints, see below)
 j = first i with s_i = 0. Then s_1..s_{j-1} := 0 and each cleared sep moves LEFT by 2 units
 (b_i -= 2, b_{i+1} += 2 for i<j), s_j := 1. Counter S := S+1 (ternary, carry leftwards, new digit `11.` on overflow,
 l1 moves -3). Head sweeps right 18 steps/unit (H(.111)^k -> (11..)^k H), left 4 steps/unit.
 Step count dt = 22*U + 38*j + c(counter carry) where U = units from H to turn block (fit exact, see fit2.py).

## Ladder overflow (all s_i = 1): at overflow blocks are EXACTLY [x, 2^m, 2^(m-1), ..., 4, 3] (R-phase),
 x grows by 2 per overflow; after overflow ladder = [x-3, 2^m, ..., 4, 2, 2] + '1.' with all bits 0 (one new bit at right).
 New level when x reaches 2^(m+1): x becomes the new top block, fresh x=2. Level m lasts 2^m+1 overflows (33,65,129,257,...).

## Absorption (left event): when B1 is exhausted (B1 in {2,4}), s1 and the B1 remnant are swallowed at p0;
 old b2 becomes B1 (+2), one bit disappears (the "conveyor": bits born at right on overflow, die at left once per cycle).
 Counter: roughly drops its 2 low digits; for a while S is MISALIGNED (high digits left-aligned, low digits right-aligned
 at new p0, one pad cell between, len(S) = 1 mod 3). The misalignment is fixed when the counter's carry reaches the
 pad cell (p0 moves another 4 cells left). Net per cycle: p0 and l1 move 6 cells left.
 Fix delay = up to 3^L+3 increments (seen 0..732); epoch length ~ b2 (46..1366). Max observed delay/epoch ~0.65.

## Counter invariant within an epoch: V + B1 = C (constant) exactly (V = ternary value of S).
 Across absorption: C' ~ floor(C/9) + B_absorbed + delta (delta small, in [-73,1]); contracting => V ~ (9/8) B.
 => counter width ~ log3(B) + 1 digits, self-stabilizing.

## Perturbation test (cut.c): post-absorption with pending 732-delay fix, delete 1200 units of B1 so next absorption
 happens BEFORE the fix: machine survived 3e9 more steps; counter shrank (19 -> 13 cells) then renormalized.

## Exact step formula (canonical -> canonical), fit3.py / replay2.py
 dt = 22*W + 38*j + 8 + 18*min(z,3) - 12*tz + 18*max(0,tz-3)
   W = B1+b2+..+b_{j+1} (units from p0 through the block left of first 0-sep, j = 0-based index of that sep),
   z = trailing '...' digits of S, tz = trailing '1..' digits of S (carry length).
 OVERFLOW (all bits 1): dt = 22*sum(blocks) + 38*r + (same counter term); all seps cleared (drift -2), last block
   (2) +2 splits into 2 '..' 2, terminal kept; canonical pre-overflow ladder = [x, 2^m, ..., 4, 2] all ones.
 replay2.py on can3.txt (0..2e10): 959,998 increments + 13 double + 1,340 overflows EXACT (state+time);
   2,978 absorption/level resyncs, 7,496 non-canonical (absorption transients), 470 small-k anomalies (k=4, near
   absorption, small counters). can4.txt (0..4.5e10) run: see below.

## Overflow shape: all 1742 overflows to 4e10 have R-phase blocks EXACTLY [x, 2^m, ..., 8, 4, 3]; level m starts at
 overflow index 12,45,110,239,496,1009 (gaps 2^m+1), x = 4 + 2k within a level. Ladder is STRUCTURAL (forced).

## DANGER CONDITION (setS.c, setL.c, rtest*.py perturbation experiments)
 - The notes' "tiny ladder + big gap halts" is a MOD-3 ALIGNMENT effect, not size: counter '1'+k blanks halts
   iff k = 1 mod 3, at ALL ladder sizes (tested real ladders at levels 2..8, k up to 121).
 - Counter forms: clean digits / one pad cell ('.' between digit strings) / lone leading '1': 0 halts in ~2000 random
   trials on real ladders (levels 2-8) and on random ladders with >=5 blocks (blocks 1..8, random bits).
 - Two pad cells (pad2mid/padR2): ~50% halt quickly.
 - Only halts with 1-pad forms: lone-1 counters with TINY ladders (<=4 blocks, blocks <=6): 10/1200.
 - Pending re-alignment fix colliding with the next absorption (forced by cutting B1, cutq.c, all cut amounts for
   delays 30/84/246 cases): 0 halts.
 Natural counter forms at canonical checkpoints (classify.py): clean 964,858; pad1 3,934; lone1 365; absorption
 transients ~3,200 (D.D.11, D1D, D11, D1). Never a 2-pad.
 => safety needs NO numeric coupling between counter value/width and ladder size; only local form of S
    (<=1 pad) + ladder not tiny (>=5 bits), which the forced level structure gives from level ~5 on.
 can4.txt (0..4.5e10, 1.67M checkpoints): 1,655,163 increments + 17 double + 1,774 overflows EXACT (state + step
   count); 694 mismatches = k=4 checkpoints (a pending-pad counter that happens to parse as clean digits; dt off
   by 18/36 = one H-unit), 3,904 absorption resyncs, 9,658 absorption transients. No HALT.

## VERDICT: STRUCTURAL (in fact no numeric coupling is needed)
 Ladder at overflow is forced by level; counter value C is history-dependent (C' ~ C/9 + B) but safety does not
 depend on it: every clean / 1-pad / lone-1 counter is safe with any ladder of >=5 bits.
 Lean plan (mirror m7): Machine, Frame(runB), Micro (rsweep 18/unit, lsweep 4/unit, sep pass R/L with 2-unit drift,
 turn-at-'..'), Counter (ternary inc lemmas for digits 0/1/2 + new top digit, k=3-min(z,3) re-entry),
 Incr (canonical ->+ canonical, arbitrary blocks>=2 & digit string), Overflow (append block 2),
 Absorb (finite decide-table: B1 in {2,4} x s1 x low <=3 digits x pad/no-pad, arbitrary high part via frame),
 PadCounter (inc of misaligned form; fix lemma when carry hits pad), Level (ladder shape as fn of m,k; counter kept
 abstract as Form(S) predicate), Base (decide +kernel chunks to first level with >=5 bits), Main.
 Cheaper alternative: hand-built regular CTL = sanity DFA (counter: D* ('.' D*)? | 1 D*, D={...,11.,1..};
 blocks>=2; >=5 seps) intersected with the learned k-gram DFAs to kill the junk (2-pad) violations.
