# Seal audits: Theorem 1.1 for the full range 0 < γ < 1

On 2026-11-09 five frozen theorems were sealed on main (decision D17 in [DECISIONS.md](../../DECISIONS.md)): Theorem
1.1 for every 0 < γ < 1 and the four statements its proof is assembled from. Sealing replaces each statement's
placeholder proof by a one-line reference to its formal proof, and tooling checks that the statement itself did not
change. A sealed theorem is recorded as **PROVED** only after two independent audits pass. This directory holds those
two audits.

**Status: both audits passed for all five theorems (completed 2026-11-10 UTC), which are recorded as PROVED.**

## What was sealed

| Theorem (Lean) | Paper | Seal commit | Frozen |
|---|---|---|---|
| `WaveTurbulence.layergardenFlower_v4` | the flower estimate, TARGET Prop `flowerest1` (corrected form; D16) | `4558dd65` | 2026-11-09 |
| `WaveTurbulence.layergarden` | TARGET Prop `layergarden` | `2e2c16ef` | 2026-11-04 |
| `WaveTurbulence.fixedpoint` | TARGET Prop `fixedpoint` | `008e27f9` | 2026-11-04 |
| `WaveTurbulence.propansatz` | TARGET Prop `propansatz` | `6f4a03d2` | 2026-11-04 |
| **`WaveTurbulence.main`** | **TARGET Theorem 1.1, 0 < γ < 1, as printed** | `bfbb5546` | 2026-11-03 |

TARGET is Deng–Hani, *Long time justification of wave turbulence theory*, arXiv:2311.10082v2. Each proof joins the
earlier, audited proof for 1/2 < γ < 1 ([`../v2-chain/`](../v2-chain/README.md)) and the new proof for 0 < γ ≤ 1/2
([GAMMA-LE-HALF.md](../../GAMMA-LE-HALF.md)): its provider applies the glue theorem for its statement (for example
`GammaLow.Glue.main_of_low`) to the closed γ ≤ 1/2 halves `GammaLow.Close.flower_low_closed` and
`GammaLow.Close.layergarden_low_closed`.

## How the audits work

Two auditors, keys A and B, are separate Claude Opus 5.5 sessions. They work separately and never see each other's
work, and neither wrote any part of the proof. Each audits all five theorems and records a verdict per theorem on every
item:

- (a) the frozen statement's bytes: only the proof body changed;
- (b) the provider: its statement is exactly the frozen one, and it does not depend on its own anchor;
- (c) the axioms: only `propext`, `Classical.choice` and `Quot.sound`;
- (d) hidden hypotheses and vacuity;
- (e) the ABI hashes of the frozen declarations;
- (f) a replay of the proof in Lean's kernel, in quick mode (below);
- (g) the status fields;
- (h) a table of every hypothesis, built from the paper's TeX source, which must show **zero excess hypotheses**: none
  beyond the source, the standing assumptions, typing data and approved rulings.

Each auditor replays the joint dependency closure of the five theorems once in the kernel, in quick mode: the 40,618
certificate theorems of `WaveTurbulenceVineParam` whose proofs use no constant outside that library are checked by
statement only (their proofs are kernel-checked by every build), and all library modules outside this project (Lean
core, Mathlib and its dependencies such as Batteries and Aesop) are inserted unchecked as the trusted base (KEY-A §1.2,
KEY-B §1.3). Both replays adapt the same tool (`Replay.lean`, `replay.sh`) and read the same build, so they are two runs
of one method, not two independent checks. Otherwise the two keys are given different primary refutation targets and
different methods, so that they do not share blind spots. A theorem is recorded as PROVED only if both keys pass it.

*In progress: a full kernel check of the release commit with the public tool lean4checker (`--fresh`).*

## Reports

| Key | Report | Verdict |
|---|---|---|
| A | [KEY-A.md](KEY-A.md) | PASS for all five theorems |
| B | [KEY-B.md](KEY-B.md) | PASS for all five theorems |

The reports are the auditors' complete working records, unedited apart from paths: `<work>/` stands for the auditor's local working files (scripts, logs, probe outputs), which are not part of the repository, and `<sources>/` for the pinned LaTeX sources of the papers. Both audits cover main at `5c19b015`, and Lean names in them refer to the repository at that commit. From there to commit
`f121830e`, 3,979 Lean files changed (`git diff --shortstat 5c19b015 f121830e -- '*.lean'`): 1,056 were deleted and
2,923 modified, with 1,393 lines added and 191,890 removed. Most of this is the removal of unused code (declarations and
imports that no proof of the sealed theorems uses); 29 files also had their proofs rewritten for speed, proof-only
(merge `facb1929`). No frozen statement, provider or manifest entry changed. Later commits add the two comparator files
(see the [README](../../../README.md#comparator)); `git diff --stat 5c19b015 HEAD -- '*.lean'` lists every Lean change
since the audits. The removed code remains in the git history at `5c19b015`.
Internal working records they cite (planning and audit records) were removed from the repository at publication and remain in the git history.
