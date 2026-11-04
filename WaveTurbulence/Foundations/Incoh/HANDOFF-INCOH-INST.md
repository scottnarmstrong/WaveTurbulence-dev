# INCOH-INST — complete

## Exact export and files

Scratch root: `/home/scott/wt-scratch/incoh-inst`.
Final entry: `src/IncohInst/IncoherentDecay.lean`.
Proved declaration: `WaveTurbulence.IncohInst.incoherentDecay`.
Its entire declaration header matches the pinned B2 final candidate verbatim, and its elaborated
Lean type is literally equal to `WaveTurbulence.incoherentDecay` in the reference environment.

Pinned statement: `/home/scott/wt-scratch/waveb2-snap-final/WaveB2-Statements.lean`, SHA256
`82e42b2bfa16289ef6fadc35f2fbc8375cf28eda18658b35faef2b89556d99a4`.

Principal scratch modules:
- `AllCoupleDecay`: all actual decoded incoherent couples, including the one-clock case.
- `TreeDecay`: all actual decoded incoherent regular trees.
- `CoupleKernelFromInputs`, `OneRootKernelFromInputs`, `TreeKernelFromInputs`: exact original B1
  kernel identities, with all lattice/time convergence discharged from actual input bounds.
- `ActualTreeSelection`, `TreeGraphBoundary`, `TreePhaseIntegral`: actual complete source links,
  computed clock fibers, null boundary changes and exact causal phase-integral transport.
- `DecodingObligations`: exact O1–O5, proved from REG-STRUCT rather than unfinished anchors.
- `InputBounds`, `PrefixBounds`, `PrefixAssembly`: uniform actual inputs, coefficient enlargement,
  and the complete exact parameter prefix.

The 264 scratch modules in the proof closure have local source copies under `src/`, with origin
and SHA256 in `SOURCE-PROVENANCE.tsv`. `clean-build-order.txt` records their dependency order.
`proof-imports.txt` records the source import closure; `SHA256SUMS` records all authored proof
modules and the 26 reusable Foundations modules added by this packet.

Reusable Foundations additions are committed on `w/wke-l2s` after the initial merge of main
(`7b8b80c`): c96fd55, 72e8480, b56ab5a, d28aeb5, 4240fb2, 06e7ab4. They provide cutoff-independent
couple coefficients, upper-box source agreement and printed rates for couples/one-clock/trees,
actual finite cutoffs, exact raw-source Fubini, selected coordinate constructions, null clock
hyperplanes, computed finite graph fibers, and convergence with the lone input omitted.
The complete filename list is `git diff --name-only 7b8b80c..HEAD -- WaveTurbulence/Foundations/Incoh`.
Root imports and frozen files were not edited.

## Approach

Construct all finite integer momentum fields from C2's actual link-coordinate equivalences.
Prove the node/input rows, root relation, leaf coverage, exact incoherence count and layer span.
Retain F62's squared per-link Wick factor and the original garden sign. Identify original
integer decorations, coset decorations, phase products and actual leaf products exactly.
The finite clock bijections preserve Lebesgue measure with unit Jacobian.

For couples, classify both roots. A trivial other tree gives the actual one-clock source;
the passive external clock is retained separately. For trees, select the root link and final
top-level spine link (one or two complete links). Actual path geometry orders their endpoints.
Compute interval fibers by finite maxima/minima of layer and parent-child constraints, proving
all carrier fields. Strict/closed source domains agree off proved null coordinate hyperplanes.
The extreme selected clocks are exactly the original root and the unique lone parent.

Absolute convergence from actual spatial input bounds justifies exact lattice/time Fubini.
For the omitted tree lone input, choose a nonzero smooth root partition value at fixed momentum,
prove augmented convergence and cancel that scalar. Apply the accepted abstract Prop 5.1
estimates on B2's exact external boxes. Choose a common C1 before nu, delta and D; use uniform
Schwartz control plus the actual remainder estimate; convert link count to n using source size.
The final coefficient includes the printed outside C1.

## Exact checks and outputs

All commands below ran from `/home/scott/WaveTurbulence-worktrees/wke-l2s`, serially through
`wt-throttled`, without budget overrides or rebuilding Mathlib.

1. Targeted `nice -n 5 lake build WaveTurbulence.Foundations.Incoh.<Module>` for each new
   Foundations milestone: PASS. Relevant logs/probes are retained in scratch.
2. `nice -n 5 lake env bash /home/scott/wt-scratch/incoh-inst/rebuild-clean.sh`:
   `CLEAN SCRATCH REBUILD: PASS` — all 264 scratch proof/dependency modules rebuilt serially
   into the new packet-owned `build-clean`. Project and Mathlib artifacts were reused.
3. `nice -n 5 lake env bash /home/scott/wt-scratch/incoh-inst/build-one.sh IncohInst.AuditFinal`:
   `'WaveTurbulence.IncohInst.incoherentDecay' depends on axioms: [propext, Classical.choice, Quot.sound]`.
4. `nice -n 5 lake env bash /home/scott/wt-scratch/incoh-inst/run-type-audit.sh`:
   `ELABORATED EXPR CHECK: PASS (literal Expr equality in independent environments)`;
   `REACHABLE SOURCE DEFINITION EXPR CHECK: PASS (214 declarations, types and values)`.
5. `python3 /home/scott/wt-scratch/incoh-inst/verify_source.py`:
   source-definition pin check PASS; complete theorem-header text check PASS;
   proof import quarantine PASS (870 source modules); own-file hygiene PASS (109 modules).
6. `git diff --check`: PASS.

Final logs: `rebuild-clean.log`, `build-final.log`, `type-expr-audit.log`, `source-audit.log`.
Component axiom logs: `axioms-all-couple.log`, `axioms-actual-tree.log`, `axioms-graph-fibers.log`,
`axioms-kernel-ingredients.log`, `axioms-time-domains.log`, `axioms-foundations.log`.
All audited results use only `[propext, Classical.choice, Quot.sound]`.

## Import quarantine and source fidelity

The initial proof did not use any unfinished theorem, as its axiom audit confirmed. The final
source audit nevertheless found six unused draft theorem declarations bundled in the shared
scratch `WaveB2Draft.Regular` module. The isolated local copy omits precisely that draft theorem
section, preserving every source definition and carrier body. Exact O1–O5 are actually proved
in `DecodingObligations`. The entire scratch proof closure was then rebuilt against this copy.
The final scripts use only `build-clean` plus the project Lake path; old shared scratch builds
are not used. See `CLEAN-DEFINITIONS.md` for the exact transformation and provenance.

The original draft Statements module is loaded only as the reference in the independent type
audit environment. It is never a proof import. Its source is byte-identical to the pinned final
candidate. Core/System copies are byte-identical to their pins; the complete Regular copy is
textually identical apart from the omitted draft theorem section. The 214 reachable source
declaration types and values also pass the elaborated comparison.

## Uncertainties, errata and deviations

None outstanding. No new suspected source erratum. No extra hypothesis and no restriction beyond
`0 < γ < 1` was introduced. F62's squared Wick factor is retained. Some component estimates are
stronger than the source's layer/order assumptions; the exported anchor preserves every binder
and premise verbatim. The largest scratch Lean module has 695 lines.

READY incoh-inst
