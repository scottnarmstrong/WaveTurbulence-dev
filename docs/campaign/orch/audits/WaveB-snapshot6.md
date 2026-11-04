# Wave B snapshot 6 (with 6b) audit (Task 18)

Auditor: `wt-orch` (Opus), refute-first. Date: 2026-11-04.

## Subject

**Snapshot.** `/home/scott/wt-scratch/waveb-snap-6`, final as 6b. I copied it at 00:24:10 UTC, after the FixPat change
(`WaveB1-Flower.lean` 00:18:09, `SHA256SUMS` 00:21:17). All 15 entries of `SHA256SUMS` (`f6c4453194085b9b…`)
verify on my copy.

**Base.** Snapshot 5 (`/home/scott/wt-scratch/waveb-snap-5`).

**References.**
- My Task 13 audit `FLOWER-redraft.md`, with the audited `Flower-Gate.lean` (`52f11d66becc…`, my copy) and its
  recommended edits F1 and F2;
- FINDINGS F56;
- TARGET (sumintI1) L1608–L1611.

## Verdict: PASS. Snapshot 6b is ready to freeze.

| Check | Result |
|---|---|
| File hashes: 8 files unchanged from snapshot 5 | **PASS**: `Bridges 3f58ca3a…`, `Core 0b8477d9…`, `Core-probes 8932feb2…`, `Lemmas c7312be4…`, `Statements e72e32df…`, `Statements-probes d087ace3…`, `System 59365906…`, `System-probes b78d1835…` are byte-identical to snapshot 5 |
| `WaveB1-Sumint.lean` (`9750d760…`) | **PASS**: the textual diff from snapshot 5 is exactly the two added parentheses (L193 `(∏ i, …`, L203 `…))) *`) |
| `FreezeList.lean` (`66e02a8a…`) | **PASS**: adds `import WaveBDraft.Flower` and `WaveBDraft.Flower` to `frozenMods`, nothing else |
| B1.12 `WaveB1-Flower.lean` (`026ac386…`) is the audited Flower-Gate text with F1 and F2 | **PASS**: identical to the live `wt-scratch/flower/Flower-Gate.lean`; diff against the Task 13 text below |
| FixPat (6b): explicit `FixPat.decEq` and `instDecidableEqFixPat` | **PASS** |
| No other declaration changed (elaborated comparison) | **PASS**: only `SumintDatum.phase` differs |
| `phase` now multiplies the two products (F56) | **PASS** |
| FREEZE-LIST regeneration | **PASS**: 226 rows, matching my own regeneration; the four old sections are byte-identical to snapshot 5 |
| Independent big-operator sweep of the five frozen files | **PASS**: no body-extent error; all 6 flags are intended |
| Build | **PASS**: 0 errors; exactly the 12 anchors carry `sorry` |
| Hygiene | **PASS**: no `deriving`, `set_option`, `native_decide`, `admit` or `axiom` in the five frozen files; they import only `Frozen.Defs.*`, Mathlib and each other |

## Build (my own, from my copy)

**Setup.** One `lake env lean` at a time, in a fresh root on this worktree's sources (main `b1e8a86` merged). I built
Core, System, Statements, Lemmas, Sumint, Flower, the four probe files and Bridges.

**Result.**
- 0 errors in all eleven modules.
- `sorry` occurs only for the anchors, 12 in all: 10 in Statements (B1.1–B1.5, B1.7–B1.11), 1 in Sumint (B1.6) and 1 in
  Flower (B1.12).
- `FlowerProbes` and `Bridges` compile.

## B1.12 against the audited text

`diff` of my Task 13 copy of `Flower-Gate.lean` against snapshot 6b's `WaveB1-Flower.lean` has exactly four hunks.

**1. FixPat (6b).** `deriving DecidableEq` becomes `FixPat.decEq`, written by cases, plus
`@[instance_reducible, instance] def instDecidableEqFixPat`.
- The definition is correct by construction: each branch returns `isTrue`/`isFalse` with a proof, and `dChild i` /
  `dChild j` decides `i = j`.
- `Decidable` is a subsingleton, so every use (`if … = .plain`) has the same meaning as with the derived instance.

**2. F1 (range).**
- `∀ t ∈ Ioc p (p+1)` becomes `∀ t ∈ Ioo p (p+1)`, as I recommended. This is TARGET's range for the flower kernels
  (L2263).
- The hypothesis `((∃ j, pat j = .dRoot) → t < p + 1)` is removed. It is now redundant because `t < p+1` always
  holds, so the statement is strengthened only by dropping a premise it no longer needs.
- The docstring now reads `p < s < t < p+1`.

**3. F2 (bookkeeping).** Deviation D11 (per-tree `†` labels and patterns) is added, and the `M₁` sentence now reads
"also for derivative patterns".

**4.** No other change: the theorem's conclusion, every binder, `flowerSum` and `coupleSum` are unchanged.

## No other declaration changed

**Comparison.** `scratch/Task18-dump-decls.lean` (`1fa4e92bdedb…`) dumps every constant of
`WaveBDraft.{Core, System, Statements, Sumint}`: name, module, universe parameters, type, and value for definitions.
I ran it on my snapshot-5 and snapshot-6b builds.
- There are 483 constants in each, with the same names.
- After hygiene normalization, **exactly one** differs: `WaveTurbulence.SumintDatum.phase`.
- The anchor types do not change. B1.6 `sumint` refers to `phase` by name and therefore receives the correction.

**`phase`** (`scratch/Task18-phase-shape.lean` `6ab5ed3457f8…`).
- After the binders and `let`s, the elaborated body is `HMul.hMul (Finset.prod …) (Finset.prod …)`.
- The left factor contains 5 `Finset.prod` (the outer `∏ i` and its four inner `∏ j`). The right factor contains 2
  (`∏ i : Nor` and its inner `∏ c'`). That accounts for all 7 `∏` of the source text L186–L212.
- So the normal-block product is no longer repeated `I` times. This is TARGET (sumintI1)'s product of the two blocks,
  and closes F56.

## FREEZE-LIST

**Regeneration.** I ran `FreezeList.lean` on my build: 226 declarations.
- 12 theorems, 167 definitions, 33 instances (as literal `def`s), 5 structures, 5 inductives, 4 abbrevs. This matches
  the "Counts" paragraph of FREEZE-LIST.md and the 226 declarations in the snapshot-6 statement.
- Every row agrees with FREEZE-LIST.md in name, file and the *uses* column (0 mismatches).

**The four old sections** (Core 94, System 58, Statements 28, Sumint 22) are **byte-identical** to snapshot 5's
FREEZE-LIST.md. The new section is Flower, with 24 declarations, including `FixPat.decEq` and `instDecidableEqFixPat`.

**Caveat.** FREEZE-LIST rows do not hash declaration bodies. That is why the elaborated comparison above is needed: it
is what shows that `phase` is the only change.

## Independent big-operator sweep (all five frozen files)

**Elaborated sweep** (`scratch/Task18-bigop-sweep.lean` `56ae33f7ed10…`), run on the snapshot-6b build.
- **Method.** For each of the 452 user declarations, I walked the type and value. Every application of `Finset.prod`,
  `Finset.sum`, `tprod`, `tsum`, `integral`, `lintegral`, `iSup`, `iInf`, `finprod` or `finsum` to a lambda had its
  body split into top-level factors (`*`, `/`, `•`).
- **What it catches.** It reports every factor that does not contain the bound variable: the F56 shape, where an outer
  factor is swallowed by the body. For `∏`/`⨆` this changes the value; for `∑`/`∫` it does not, by linearity.
- **Results.** 3 flags:

| Declaration | Flag | Verdict |
|---|---|---|
| `Garden.zeta` | `∏ b, (I * ζ_b)`: `I` is independent of `b` | **intended**: TARGET's `ζ(𝒢) = ∏_𝔫 (iζ_𝔫)` takes one `i` per node |
| `treeTerm` | `∏ c, (I * ζ_c)` | **intended**: (defjt) takes one `iζ_𝔫` per branching node |
| `SumintDatum.phase` | the `Nor` product's body is `let`-bound, so the sweep cannot auto-check it | **inspected**: each factor `e(…)` and the inner `∏ c'` depend on `i` through `u`, `τ'`, `D.Λsel i.1`, `D.ξc i.1`; the outer split is verified above |

**Textual sweep** (`scratch/Task18-textsweep.py` `2477cef7f2f2…`).
- **What it catches.** It flags every `∑`/`∏`/`∫`/`⨆`/`⨅` whose body ends at a top-level binary `+` or `−`. The body is
  `term:67`, and `+`/`−` are 65, so a term meant to be inside would silently fall outside.
- **Results.** 3 flags, all in `WaveB1-Sumint.lean`, all intended:
  - L132 `kVec` and L136 `ℓVec`: `∑ v', T·x + ∑ c, H·efgh` is the sum of two sums, i.e. the affine form.
  - L151 (Admissible (ii)): `∑ v', σk·H₁ + σe` is the coefficient identity of `ℓ_v − ℓ_prev = ∑σk k + ∑σe(e,f,g,h)`.
    The `σe` term is correctly outside the sum.

No other big operator in Core, System, Statements, Sumint or Flower ends at `+`/`−`. No `∏`/`⨆` body contains a
factor that is independent of the bound variable, other than the intended `i`'s.

## Probes (untracked, `scratch/`)

`Task18-bigop-sweep.lean`, `Task18-textsweep.py`, `Task18-phase-shape.lean`, `Task18-dump-decls.lean`.

**Process note.** One short dump run overlapped my background snapshot-6 build; for a few seconds two `lean`
processes ran. All other runs were sequential.
