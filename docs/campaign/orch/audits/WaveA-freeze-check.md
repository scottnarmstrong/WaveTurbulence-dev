# Wave A freeze check (Task 3a)

Auditor: `wt-orch`. Date: 2026-11-03. Tree: `w/orch` after `git merge main` (main = `10daec8`; freeze commit
`8d1d2e3`, ruling D6).

**Verdict: PASS.** All 15 frozen files under `WaveTurbulence/Frozen/` contain exactly the declaration text of the
approved draft, `/home/scott/WaveTurbulence-dev/scratch/Draft.lean` (sha256
`938afa9744ec9b17d9d5e90dd0865169feae0702a27258cb8d0d87b98b361a57`). The index check and the ABI check both pass.

## 1. Approved draft against v2 (what I audited in Task 2)

`diff scratch/Draft-v2.lean <approved draft>` shows exactly O6–O8 and nothing else:

- **O6:** the header and docstring now say "Proposition 3.2" and "L598–L601".
- **O7:** the `wkelwp` blow-up clause adds `0 ≤ τ₀ ∧`. That is a hygiene strengthening, which I checked in Task 2.
- **O8:** the `weightedL2Norm` docstring now cites `Z_s` (L2515).

## 2. Declaration text

Method: a script compares each frozen file with the matching draft declaration.

- **Frozen side.** For each file, take the text between `namespace WaveTurbulence` and `end WaveTurbulence`, then
  drop the `-- FROZEN_ANCHOR_*` marker lines and `universe u`.
- **Draft side.** Take the blank-line-delimited draft block that contains `def|abbrev|theorem <name>`, docstring
  included.
- **Preamble checks.** Each file must:
  - contain both `open` lines of the draft;
  - use `@[expose] public section` plus `noncomputable section` for definitions, or `public section` for theorems;
  - declare `universe u` exactly when the declaration uses `Type u`;
  - have no other commands outside the declaration. I scanned for `set_option`, `attribute`, `notation`, extra
    declarations and similar: there are none.

| Anchor | Text | Preamble / opens / section / universe | File sha = manifest | Closure shas |
|---|---|---|---|---|
| `Mom` (abbrev) | byte-identical | ok | ok | ok |
| `latticePoint` | byte-identical | ok | ok | ok |
| `collisionOp` | byte-identical | ok | ok | ok |
| `IsWKESolution` | byte-identical | ok | ok | ok |
| `partialDeriv` | byte-identical | ok | ok | ok |
| `normLaplacian` | byte-identical | ok | ok | ok |
| `torusFourierCoeff` | byte-identical | ok | ok | ok |
| `IsSmoothNLSSolution` | byte-identical | ok | ok | ok |
| `stdComplexGaussian` | byte-identical | ok | ok | ok |
| `initialCoeff` | byte-identical | ok | ok | ok |
| `solvableEvent` | byte-identical | ok | ok | ok |
| `kineticTime` | byte-identical | ok | ok | ok |
| `weightedL2Norm` | byte-identical | ok | ok | ok |
| `main` | identical except the proof layout (draft: `:= by⏎ sorry`; frozen: `:=` ⏎ marker ⏎ `by sorry` ⏎ marker) | ok (`public section`, `universe u`) | n/a (theorem) | ok |
| `wkelwp` | identical except the same proof layout | ok | n/a (theorem) | ok |

The draft has 15 declarations and the manifest has 15 anchors. None is missing and none is extra.

**Imports.** Every file imports only `Mathlib` and frozen definitions; each theorem file also imports its provider.
Both providers, `Provider/Main.lean` and `Provider/Wkelwp.lean`, currently hold only imports, a module docstring and
an empty `public section`.

## 3. Scripts

- `git add -A` (nothing staged) then `scripts/check_index.sh`:
  `FROZEN-ANCHOR GUARD OK` and `check_lean_modules: PASS (19 Lean files, 0 comparator configurations)`. Exit 0.
- `python3 -I scripts/abi_hash.py --root . --manifest manifest/frozen.json` (check mode): **15/15 OK**, exit 0, and
  the manifest is unchanged.

Two notes on how I ran the ABI check:

- **How the modules were built.** The ABI probe needs built frozen modules, and the rules forbid `lake build`. I
  therefore compiled the 17 frozen and provider modules one at a time, in dependency order, with
  `nice -n 5 lake env lean -o <olean> -i <ilean> <file>` into this worktree's `.lake/build` (gitignored). All
  compiled with no warnings, except the expected `sorry` warnings in `Theorems/Main.lean` and `Theorems/Wkelwp.lean`.
- **Environment quirk.** In this worktree elan prints an override notice on stderr ("using toolchain 'wt-throttled'
  from override"). `abi_hash.py` treats any stderr as a probe failure, so the first run aborted on `Mom`. Rerunning
  with `ELAN_NO_OVERRIDE_NOTICE=1` gave 15/15 OK. Suggestion: have `abi_hash.py` set that variable, or ignore stderr
  lines that start with `note:`, so that worktrees with a throttled toolchain override can run it.
