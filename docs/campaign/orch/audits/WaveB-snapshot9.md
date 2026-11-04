# Build record: Wave B snapshot 9 (F80), against snapshot 8

Builder: `wt-orch`. Date: 2026-11-04 (Task 34b). **This is not an audit.** I built snapshot 9, so the delta's
audit is the independent auditor's. This file records what I built and checked, for that audit.

**Snapshot 9:** `/home/scott/wt-scratch/waveb-snap-9`, 15 files, `SHA256SUMS` digest `30263a992199…`. Its
`CHANGES-9.md` has the file table and the exact before/after text.

## 1. The change

**Base.** Snapshot 8 (`SHA256SUMS` `138033c99cab…`), as audited in `WaveB-snapshot8.md`.

**One change**, in `WaveB1-System.lean` (`59365906b84a…` → `cc53aad3acd7…`): `XNorm` takes the independent auditor's
text (`WaveB2-independent-audit.md`, "Norm measurability"; FINDINGS F80).
- The guard is `(∀ k, Integrable fun t => F t k) ∧ (Λ₁ = 0 ∨ ∀ᵐ lam, ContDiff ℝ Λ₁ (timeFT F lam))`.
- The per-frequency `if … then … else ⊤` inside `∫⁻` is gone; the integrand is
  `maxBracketPow θ lam * ⨆ k, ENNReal.ofReal (jbr k ^ Λ₂ * ‖iterPartial ρ (timeFT F lam) k‖)`.
- `open Classical in` is kept. The docstring states the a.e. guard and why (lower integral, no triangle inequality)
  and cites F80. The rest of the docstring is unchanged.

**Documentation only:** `DESIGN.md` (the norm reading and CL-23), `FREEZE-LIST.md` (regenerated; only its title
changes), and `CHANGES-9.md` replacing `CHANGES-8.md`. Every other file is byte-identical to snapshot 8.

## 2. Checks

**Builds.** All 11 B1 modules, in dependency order, in two fresh roots:
- on my Wave A glue root (`$SP/waveb9`);
- on dev's build (`$SP/waveb9dev`).

Both: 0 errors. The only warnings are the 12 anchor `sorry`s. On dev's build the 7 B2 modules of the final
candidate, probes included, also compile on snapshot 9, with the same `sorry`s (Regular 6, Molecules 1,
Statements 3).

**Elaborated comparison.** The constant dump of Tasks 22, 28 and 34 (`WaveBDraft.{Core, System, Statements,
Sumint, Flower}`, matchers and auxiliaries delta-expanded, proofs erased): 423 constants on each side, none on
one side only. **Exactly one differs: `XNorm`.**

**Freeze list.**
- `FreezeList.lean` gives the same 226 rows with the same uses. Only `XNorm`'s docstring and the source lines of
  the declarations below it in `WaveB1-System.lean` move.
- The meta table (`FreezeMeta.lean`) differs from snapshot 8's in the line column only.
- `FREEZE-LIST.md` was regenerated with wt-gauss-hc's snapshot-8 generator. On snapshot 8's build data it
  reproduces snapshot 8's list byte for byte; on snapshot 9's only the title changes.

**Dependents.**
- In B1, only the definition `XNormRestr`; no B1 theorem anchor uses `XNorm` or `XNormRestr`.
- `XNorm00`, `XNorm00Restr` (used by B1.6 `sumint`), `SNorm`, `SNormR`, `ZNorm`, `ZNormOn` and `ZSpace` do not
  use `XNorm` and are unchanged.
- In B2, `XNormRestr` occurs in B2.1 items (1), (2) and B2.2 items (1), (2). Their text is unchanged; their norm
  is now TARGET's (normX) with TARGET's guard.

## 3. What the audit should check

- That the new `XNorm` is the auditor's text, verbatim, and that the docstring is accurate.
- That nothing else changed (`CHANGES-9.md` §0; the dump above).
- That the guard is TARGET's: (normX), L581–L582 (the setup at L581, the display at L582), and the landed
  `Fourier.MixedFourierAdmissible`.

## 4. Consequences

**B2 final candidate** (`/home/scott/wt-scratch/waveb2-snap-final`). Its files are unchanged. Its README now names
snapshot 9 as the B1 base (`WaveB1-System.lean` `cc53aad3acd7…`), and `SHA256SUMS` was regenerated (digest
`b3db9c4367a8…`). `docs/review/WAVE-B-B2.md`'s header says the same.

**`w/freeze-b1`** was rebuilt from snapshot 9 (see `FREEZE-B1-PLAN.md`).
- Against the snapshot-8 freeze (`8b470ff`, kept in `w/freeze-b1-snap8`), **only one frozen file differs:
  `XNorm.lean`**, with the new text in its snapshot context.
- In the manifest, only `XNorm`'s file hash and ABI (`870fbcb1…`, was `ae1b198a…`) and `XNormRestr`'s definition
  closure change. `XNormRestr`'s ABI is unchanged.

**The `sumint` seal (B1.6).** Its statement does not involve `XNorm` and is unchanged. Its proof (wt-anfourier,
scratch `4700924`) was built on a local copy of snapshot 8's `System`, and its module `TimeBridge.lean` proves five
bridge lemmas about `XNorm` at `Λ₁ = 0` by unfolding it.
- Three of those proofs rewrote with the old guard and fail on snapshot 9. I repaired them in the port: proofs only,
  no statement changes (`FREEZE-B1-PLAN.md` §1, "Ported files").
- None of the five lemmas is used elsewhere in the 404-module closure, so the `sumint` proof does not depend on them.
- wt-anfourier's scratch still has the snapshot-8 proofs.
