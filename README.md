# Nonhalting proof: BB(6) holdout `1RB0RA_0LC0LA_1RF1LD_1LE0LD_1LC1LF_---1RA`

## Result

The machine

```
1RB0RA_0LC0LA_1RF1LD_1LE0LD_1LC1LF_---1RA
```

started in state A on the blank tape never halts. It is in the bbchallenge BB(6) holdout list of
2026-09-24 (815 classes), and it is alone in its equivalence class.

The proof is a single Lean 4 development (v4.33.1, no Mathlib). Its final theorem is

```lean
theorem M8.R3.nonhalt : ∀ n, ¬ M8.halted (M8.run n M8.init)
```

It has no hypotheses and no `sorry`. `#print axioms M8.R3.nonhalt` lists only `propext`,
`Classical.choice`, and `Quot.sound`. There is no `native_decide` anywhere. The 46,083-step base case
is checked by the Lean kernel itself with `decide +kernel`.

## How the machine behaves

The only undefined transition is F reading 0.

**A ladder that is a binary counter.** Right of a fixed point `p0` the tape is a *ladder*: a sequence
of blocks of units `.111`, separated by two-cell separators `1.` (bit 1) or `..` (bit 0). The
separators are the bits of a binary counter, least significant bit first. One increment of the ladder
is a sweep of the head to the right, past the leading `1.` separators, until it meets the first `..`,
which it flips to `1.`. Then it sweeps back to the left. Each cleared separator drifts two units to
the left, so the block lengths change by ±2 in a fully determined way.

**Block lengths halve along the ladder.** When all bits are 1, the ladder overflows and gains a new
top bit. At every overflow the block lengths are exactly `[x, 2^m, …, 8, 4, 2]`. In fact the whole
ladder is a closed-form function of its level `l` and the number `N` of increments (`Lam l N` in
`M8/R3Ladder.lean`).

**A base-3 counter on the left.** Left of `p0` sits a second counter, written in 3-cell ternary
digits (`...` = 0, `11.` = 1, `1..` = 2). It gains 1 on every ladder increment. The first block `B1`
shrinks by one unit per increment. When it is used up, the lowest bit and the first block are
*absorbed* into the left counter (once per *epoch*). The next block becomes `B1`. The absorption
shifts the counter by one cell, so its digits are *misaligned* for a while. The next carry that runs
through the pad cell *re-aligns* the counter.

## The only way to halt, and why it never happens

Halting (F reading 0) happens only when the left counter is misaligned by **two** cells at an
absorption. Perturbation experiments confirm this: clean or 1-pad counters never halted, while 2-pad
counters halt about half the time. This state can only arise if the next absorption comes before the
pending re-alignment has finished. The proof shows that re-alignment always finishes first.

- An epoch after the absorption at pre-absorption state `(l, a)` (level `l`, `a < 2^(l+1)`) lasts
  exactly `E = 2^(l+1) + a + 1` increments. `E` grows from one epoch to the next.
- After an absorption the counter value is about `v/3`, and the re-alignment takes at most
  `3(q+2)/2 + 1 ≤ E − 1` increments, where `q = (v+2)/3`.
- At every pre-absorption state the counter value `v` satisfies

  ```
  1 ≤ v,   5v ≤ 6E,   E ≥ 15
  ```

  and this invariant (`PreInv`) is preserved from one epoch to the next (`M8.R3.epoch`). The new value
  is `v' ≤ E + (q+2)/3 ≤ 6(E+1)/5`. The map is strongly contracting: the re-aligned value is about `v/9`, so `v' ≈ v/9 + E − R`, where `R` is the re-alignment delay.

The base case is the pre-absorption state `(l, a) = (3, 0)`, reached at real step 46,083. There the
ladder is `[16, 8, 4, 2]`, all bits are 1, `B1 = 2`, `v = 17` and `E = 17`.

## Proof structure (Lean)

1. **Tape model** (`Machine`, `Frame`, `Pad`). The machine has exact semantics on
   `Cfg = (state, L, head, R)`. `runB` is a bounded runner with a frame lemma for an arbitrary far
   tape. `PE` is equality up to trailing blanks, and it is preserved by `run`.
2. **Micro and increment lemmas** (`Micro`, `Counter`, `Incr`). These cover unit sweeps (18 steps
   per unit to the right, 4 to the left), separator passes, the turn, the ternary digit events, and
   the full ladder increment with its exact step count.
3. **Counter forms and absorption** (`Forms`, `Absorb`, `AbsOvf`). These cover the clean, lone-1
   and misaligned counter forms, the zipper and the re-alignment (`realign`, `realign0`), and the
   absorption. That includes an absorption that coincides with a ladder overflow.
4. **Abstract model** (`R3Abs`). The state is `S = ⟨k, C, m, L⟩`, with ladder bits and blocks `L` and
   counter form `C`. `mstep` is one increment, and `tape S` renders the state to a real tape. It is
   mirrored in `sim/am2.py`, which was checked against direct simulation for 2,500 consecutive
   abstract steps starting at step 46,083 (about 2.98·10⁶ machine steps).
5. **Simulation theorem** (`R3Sim`).
   ```lean
   theorem M8.R3.sim (S : AS) (h : okS S) : Adv (tape S) (tape (mstep S))
   ```
   Every abstract step is realised by a positive number of machine steps, up to blank padding.
   The proof is split into a ladder phase, a counter phase and an absorption phase.
6. **Ladder closed form** (`R3Ladder`). This proves `Lam`/`Ol`, `linc_Lam`, `linc_Ol` and `Lam_top`,
   and the ladder during an epoch.
7. **Epochs** (`R3Epoch`, `R3Cycle`). These prove the pending-realignment bounds, `EpInv`, and
   `epoch : PreInv S → ∃ S', PreInv S' ∧ Adv (tape S) (tape S')`. From that,
   `nonhalt_from : PreInv S → PE c (tape S) → ∀ n, ¬ halted (run n c)`.
8. **Base and final theorem** (`R3Main`). `run 46083 init = c0` is proved with `decide +kernel`.
   `c0` is PE-equal to `tape ⟨0, cl 17, 1, Ol 4⟩`, which satisfies `PreInv`. The halting state is
   absorbing, which covers `n < 46083`.

## Trust base

- The Lean 4 kernel (v4.33.1) and the standard axioms `propext`, `Classical.choice`, `Quot.sound`.
- No `native_decide`, `sorry`, `admit`, `implemented_by` or extra axioms. The base case uses
  `decide +kernel`, which the kernel evaluates itself.
- The statement only needs you to read `M8/Machine.lean`, about 65 lines: the transition table,
  `step`, `run`, `init`, and `halted`.

## Build and check

Requirements: [elan](https://github.com/leanprover/elan). The toolchain `leanprover/lean4:v4.33.1` is
pinned in `lean/lean-toolchain`. No other dependencies are needed.

```sh
cd lean
lake build                     # builds M8 (root imports M8.R3Main); about 10 s from scratch, peak RAM ~1.5 GB
lake env lean Axioms.lean      # prints the axioms of M8.R3.nonhalt, M8.R3.sim, M8.R3.epoch
```

Expected output of the second command:

```
'M8.R3.nonhalt' depends on axioms: [propext, Classical.choice, Quot.sound]
'M8.R3.sim' depends on axioms: [propext, Quot.sound]
'M8.R3.epoch' depends on axioms: [propext, Classical.choice, Quot.sound]
M8.R3.nonhalt : ∀ (n : Nat), ¬M8.halted (M8.run n M8.init)
```

The build prints some linter warnings (unused simp arguments). They are harmless.

## Layout

`lean/`: the Lean project (`lakefile.toml`, `lean-toolchain`, `M8.lean`, `Axioms.lean`)

| file | contents |
|---|---|
| `M8/Machine.lean` | the machine, exact one-step semantics, `run`, `init`, `halted`, `run_add`, `run_H` |
| `M8/Frame.lean` | bounded runner `runB` and the frame lemma |
| `M8/Micro.lean` | units, right/left sweeps, separator pass, turn |
| `M8/Counter.lean` | ternary left counter: digits, `inc`, `val`, digit events |
| `M8/Incr.lean` | ladder increment and overflow, canonical checkpoint to canonical checkpoint |
| `M8/Pad.lean` | `PE` (equality up to trailing blanks), preserved by `step`/`run` |
| `M8/Forms.lean` | counter forms, zipper, `realign`/`realign0`, absorption micro-events |
| `M8/Absorb.lean` | absorption lemmas `absorbZ/T/O` |
| `M8/AbsOvf.lean` | generic absorption tails, and absorption during an overflow |
| `M8/R3Abs.lean` | abstract model: `AS`, `CF`, `linc`, `cph`, `absStep`, `mstep`, `tape` |
| `M8/R3Sim.lean` | ladder/counter/absorption phases and `sim` |
| `M8/R3Ladder.lean` | ladder closed forms `Lam`, `Ol`, `epL` |
| `M8/R3Epoch.lean` | pending-realignment bounds, `PreInv`, `EpInv`, `epoch_step` |
| `M8/R3Cycle.lean` | `epoch` and `nonhalt_from` |
| `M8/R3Main.lean` | base case (`decide +kernel`, 46,083 steps) and `M8.R3.nonhalt` |
| `M8.lean` | root file: `import M8.R3Main` |
| `Axioms.lean` | `#print axioms` check |

Source comments that mention `m8/exact/NOTES.md` or `tools/r3/` refer to `notes/exact-NOTES.md` and
`sim/` in this package.

`notes/`: working notes, kept verbatim apart from paths. They are not needed to check the proof.

- `exploration-NOTES.md`: first exploration and the failed certificate attempts (FAR, WFAR, n-grams,
  learned DFAs), and the first decoding of the two counters.
- `exact-NOTES.md`: the exact decode. It covers the canonical checkpoints, the increment and overflow
  rules (replayed exactly over 1.65M checkpoints up to 4.5·10¹⁰ steps), absorption, and the
  danger-condition experiments.
- `lean-NOTES.md`: development notes for the Lean proof. The released chain is described in the
  "Round 3" and "R3 FINAL" sections. It also mentions files from an abandoned parallel attempt, which
  are not included here.

`sim/`: small tools referenced by the notes (Python 3, standard library only).

- `tm.py`: direct simulator. `am.py`, `am2.py`: the abstract model. `parse.py`: tape to abstract state.
- `python3 am2.py 2500`: checks 2,500 consecutive abstract steps from step 46,083 against the
  machine. It takes a few seconds.
- `python3 val1.py N`: the same check with the list-valued model, starting at step 323.
- `python3 epo.py 11 200`: for each `E`, it checks every `v` with realign delay `≤ E−2`, and that `5v ≤ 6E` gives `v' ≤ 6(E+1)/5`. The "first bad V" values it prints are all above `6E/5`.
- `python3 cyc.py L`: the ladder closed form up to level `L`, and the worst `v/E` and realign ratios.
- `findstart.py`, `leancfg.py`: find the pre-absorption states and print a configuration as a Lean
  term (used to build `c0`).

## SHA-256

See `SHA256SUMS` (check it with `sha256sum -c SHA256SUMS`). Key files:

```
3f33a807d08cdb17877189b7902bb8a0f1e09db69ee9797a9cb13c4af98410de  ./lean/Axioms.lean
3aac669c7a910ec2389f4e4f921b605adf6ebf2d1e0c9b9cd0be4d33f3f5db71  ./lean/lean-toolchain
a0321fa7787986562f6e757b13363f6c568ac489b904957b0b3bc570272c071b  ./lean/M8/Machine.lean
4e2ccc7493f827edb89bbc4d97b864f60586240e4f5fdabf1e9ec2947bd1cc63  ./lean/M8/R3Sim.lean
465020489b4258c032fa8e20f6c96c9a4a22a82168fa923a96e79ebacfd2a20d  ./lean/M8/R3Cycle.lean
8b6d54f9e676c20d1d946da867e73f95b3fbf22f6cdfb25ee555f39f0ff40024  ./lean/M8/R3Main.lean
```
