Independent read-only helper audit: W13 adjacent-cell clamped Fourier operator. You are Terra medium v5_w2; you did not author W13 clamp implementation. Finish/preserve a stable A4 checkpoint before switching, then resume A4 after this bounded review. Exact immutable operator snapshot will be sent by root; do not audit drifting live bytes. Read AGENTS.md, relevant lean-workflow/proof-patterns/learnings and W13 handoff. This is an internal analytic helper audit, not a manifest-bound frozen theorem/source closure audit.

Owned outputs: NEW /home/scott/wt-scratch/codex-takeover/audit-clamp-operator/** report/probes only. All sources, snapshots, frozen files, build caches and main are read-only. W13 continues native certificate work. Do not build in W13's active cache; if a fresh exact consumer is needed, use an isolated reviewer output and read-only pinned dependencies after coordinating. No source repairs, git staging/commits, extra agents or budget overrides.

Read exact Lean types and definitions first. Audit:
- auxiliary cutoff really equals1 on the FULL native+adjacent domains, with corners; actual compact support and the enlarged bump dependency rebuild, not the superseded narrower plateau;
- actual localClampMode is exp(i u clamp_[0,1](t)) times the cutoff, and Fourier normalization, Jacobian, tensor product, both cell translations and the center phase are exact;
- weighted1D and2D bounds quantify the constant before arbitrary frequencies/centers and depend only on the claimed exponents; global integrability is derived and no Bochner integral default-zero result is used;
- actual native timeBracket/weight, additive tensor norm and output exponent preserve the source input budget; eta specialization proves all a/epsilon/theta inequalities, including1−2eta +eta/2≤1−eta;
- actual mixture measurability and product integrability, Fourier inversion and exact extConst/Regref.rep pointwise identity throughout the entire consumed closed rectangle;
- source-adjacent restriction may clamp only the first clock. Do not infer agreement with the original native row outside its valid domain from agreement with the globally defined representative;
- helper and specialization import/axiom/pin hygiene, no new premise asserting the desired norm/equality or source conclusion.

Distinguish a helper theorem from the next actual row-consumer and TermCertW. A pass here does not certify the latter, the R58 modulation, kind-generic R57 target, source provider or canonical rebuild. Record any remaining natural input assumptions exactly (finite input norm, actual representative, eta range), how the helper consumes them and what the native consumer still must discharge.

Verify all supplied immutable source/audit/log pins. Check full dependency evidence sufficiently to catch stale narrow-cutoff modules or mismatched interfaces; do not silently reuse live audit command files that changed after their logs. Produce a bounded REPORT.md with PASS/FAIL, exact reviewed snapshot/pins, counterexample attempts, actual checks, axioms, scope limits and any defect/location. No mathematical/source closure claim and no source edits. End READY CLAMP-OPERATOR-AUDIT or STOPPED CLAMP-OPERATOR-AUDIT: reason.

Hard rules (verbatim):

1. **Never use `set_option maxHeartbeats`** or any other heartbeat, recursion-depth or synthesis-budget override.
   A default-budget failure is a design signal: refactor or split.
2. **No Lean file may exceed 1500 lines.** Split into focused modules before that point.
3. **Every `.lean` file is a Lean module.** File shape: copyright comment, `module`, imports (`public import` for the
   interface), module docstring, `public section`. Expose (`@[expose]`) definitions whose bodies must unfold, and every
   source-facing or frozen definition.
4. **No `axiom`, `admit`, `unsafe` or `opaque`.** `sorry` is allowed only as the manifest-bound body of an
   owner-approved frozen statement (`DRAFT_SORRY`). Placeholder definitions are forbidden.
5. **Frozen files are read-only.** If a frozen declaration looks wrong, stop and report. Never add a premise and never
   substitute a helper.
6. **No conclusion-shaped hypotheses.** A theorem may assume only source premises, standing assumptions, typing data
   and explicit owner rulings. A conditional helper gets a distinct name and never stands in for a source result.
7. **Providers are quarantined.** Only the frozen anchor may import a provider or a `DRAFT_SORRY` anchor.
8. **Builds.** One targeted `nice -n 5 lake build <Module>` (or `lake env lean <file>`) at a time, through the
   `wt-throttled` compile gate. Never build the whole library, never `lake clean`, never rebuild Mathlib. A wait on
   the gate is expected, not a hang. This is a shared machine.
9. **Errata.** Report every suspected defect in the pinned sources in your handoff (location, quoted text, why it is
   wrong), and every deviation you introduce.
