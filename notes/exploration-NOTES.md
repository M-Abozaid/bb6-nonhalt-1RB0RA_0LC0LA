# M8 = 1RB0RA_0LC0LA_1RF1LD_1LE0LD_1LC1LF_---1RA
Halts iff F reads 0. Nonhalting proof attempt (2026-09-27).
## Quick attempts
- FAR mitm_dfa -l 12: no proof ([]), finished fast. direct -l 8: running.
- decide.py: u1e05_f k20/40 candidates (6.8k/18k states) fail with exactly 1 image violation (T=0,H,P ok);
  violation is junk short config (e.g. x=1..11..1b111..111.1111) whose run walks outside the learned language.
- my addw.cpp (union DFA with 0*w0*) + cegar.sh: forward CEGAR adds one witness per iteration (follows one junk run).
## Structure (from sweep.txt)
- left-record: C/f 1^k (k~5-11) then (0111)^n blocks separated by {00,10,0,11110}; right-record: phase-shifted
  (0110)-ish blocks "1100 1100 ... 1111 0011 ..." ending ...0011001B.
- right sweep is a zigzag: per cell pattern 1b -> a0 (B1=0LA, A1=0RA, A0=1RB), plus C going back left over 1110
  -> micro reversals every 1-5 steps; gcs rev K=1 needs all of them in the language (fine, regular).
- FAR direct -l 8: no proof ([]).
- forward CEGAR (cegar.sh, 318 its) and removal CEGAR (rcegar.sh/subw.cpp, 200 its) on sd k20 candidate: no convergence
  (junk short configs: learned DFA over-generalizes small-left-end configs; orbits wander).
## Macro dynamics (big.c turn points, snap.py)
- binary counter: head leaves left end, goes right converting (.111)^n blocks to shifted phase (11..)^n etc, turns at
  pattern 'd111.1111.' at a block boundary (ruler-sequence turn points), comes back rewriting phase; lower blocks grow by 2
  (64->66->68, 32->34...). Left end has a (1..1)^m / (..11)^m block growing, and junk prefix 1..11.1...
- all 4 rotations of both units appear at various times left of head.
## k-gram learning (kgram.py: tokens = maximal period-4 runs>=MINRUN + literal chars; strictly K-testable; + exactly-one-head
   + >=MR runs; nfa2dfa.cpp) -> gcs: T=0, but I violations from small-block (3,3,3) ladder combos never seen in samples.
   K=12: 21.5k states 66 viol; K=16: 28.7k states 34 viol.
- next: data augmentation: perturb run lengths of sampled configs (perturb.py) and simulate (aug.c), learn from those.
- sd window (w1e7, 317 states) / uniform-chunk from T0=2e6 (sd2.cpp adds T0; u8 k20 2187 st) : T=0, but I-violations
  always junk configs with tiny ladder next to left end (e.g. 1.....11....C11.111.1111..111.1111). Orbit-augmented CEGAR
  (ocegar.sh) grows 317->9400 states w/o closing. minspan.cpp (min tape span) doesn't fix it.
- NGramCPS (my ngcps.cpp, plain binary n-grams): spurious F0 halts for n=4..24 (n=20: 0^20 [F0] 1101110111...).
  Reason: left-end 1-run length is 3j+2 (2,5,8,11,14,17 seen) -> mod-3 info n-grams can't keep. DFA needed.
- WFAR (attempt-021/mitmwfar) -n=12 -m=0/1 default 4 states: nothing (15 s). Larger l/r running.
- Perturbation (perturb2.py, haltchk.c): period-4 run lengths U[2,8] + left 1-run 3j+2: 0/3960 halt (5e6 steps);
  lengths U[1,8]: 3/990 halt quickly (length-1 runs break it). => invariant ~ "runs >= 2".
- chunk-token K=3 k-gram (kg.cpp streaming grams; MINRUN=2, MR=6) from real + dense perturbed orbits: 14k states, 15
  I-viol; orbit-CEGAR (gcegar.sh) DIVERGES (14k->130k states) and the learned language starts containing HALTING
  configs, e.g. 11..11...11..11...11..1111..11...11..11..1111..11..1B (halts in 2545 steps). Learners are dead ends;
  the invariant needs exact structure -> hand decode.
## Decoded core mechanics (tr.py traces)
- L-phase unit '.111', R-phase unit '11..'. Right sweep: head pattern '1b11.' at an L-unit; 18 steps convert it to
  '11..' (zigzag B/A then C/D/E/F dance) with micro reversals. Separators in L-phase: '..' (bit 0) / '1.' (bit 1);
  in R-phase: '11'. Binary counter: right sweep passes '1.' bits (carry), stops at first '..' which becomes '1.',
  left sweep converts R-phase back to L-phase. Block lengths are free (any >=2); left end holds a 1-run of length 3j+2
  (and a 0-run after conversion) -> period-3 tokens needed.
- perturb3.py (random block lengths 2..8 AND random separator bits from same-unit-pair pool): 990/990 run 5e6.
  (small early seeds 2/2187 halted -- at the LEFT END, so left-end region is not freely perturbable.)
## Structured k-gram (kg3.cpp + kgram.py): units only {.111, 11..} (canonical), MINRUN=2, inner separators -> class
   tokens S<u1><u2> with pools {..,1.} / {11}; 1-runs>=5 -> Q<len%3> (min 5/6/7), 0-runs>=5 in first 24 cells ->
   Z<len%3>; first/last 10 cells literal. K=3 from real run 1e6..2e7: DFA 1832 states, gcs T=0, I 7 violations
   (non-canonical parses). ycegar.sh: add canonical grams of violation y's.
## Left end = second counter (important)
- Left region = 3-cell digits {11., 1.., ...} (e.g. 11.11.1..11., 1.....11.11.), a counter of ladder overflows:
  left 1-run at left records grows 8 (2.7e5) -> 11 (5.9e6) -> 17 (6.8e8): log-of-levels growth.
- kg4.cpp: left region tokenized as 3-cell digit tokens D..., first ladder run T (min 3), K=3 grams: 1816 grams,
  DFA ~960 states, gcs T=0, only 3 violation families (all tiny ladders). But generalization admits HALTING junk:
  '1' + 120 blanks + tiny ladder halts at step 101874 (ladder grows left into the gap and hits the far '1').
  Large real configs absorb extra left gaps fine (gap +3..+99: 100/100 run 4e8 steps; gapmon: gap closed by 1.5e8,
  normal shapes resume, runs 3e9). => safety couples left-region gap / left counter width with ladder size:
  looks NON-LOCAL (possibly non-regular as a relation, unless a constant-level guard suffices).
- Level guard (kgram MS=1: count separator tokens >= MR): kills tiny junk; ycegar5 (add canonical grams of y's)
  stagnates at 1.2k-4k states with ~180 violations (tokenization-boundary artefacts), no convergence in 60 its.
## Status 2026-09-27: NO certificate. Dead ends: FAR mitm12/direct8, WFAR n12(4st) n14(6st) m0/m1, NGramCPS n<=24,
   sd Moore-k + CEGAR (fwd/removal/orbit), chunk k-grams. WFAR n16 l8 r8 still running (3h timeout, wfar_n16l8r8m0.sc).
