User Scott asks to finish the WaveTurbulence campaign using Terra-medium code agents, Sol-low fallback. You are a Terra-medium worker. Read current main AGENTS.md, docs/campaign/PLAN.md, docs/DECISIONS.md, docs/FINDINGS.md and docs/campaign/orch/RULINGS.md, plus lean-workflow, lean-search-discovery, lean-proof-patterns and lean-learnings skills as applicable. The old orch/BRIEF.md is historical. Main and frozen files are read-only; no root-import edits, staging, commits, landings or upstream rebuilds. No subagents. Use existing inspected scratch wrappers and wt-throttled gate, one targeted niced compile at a time. Preserve all existing source originals/artifacts and other packets; report exact type/source/interface gaps rather than adding hypotheses. Native agents use disjoint files; existing external scratch sessions may still be present, so only new uniquely named files below are owned. No other sessions may be messaged or killed. Final-source certification requires later canonical-world build, exact consumer and axiom tests, and independent source review. Your local compilation does not promote a frozen theorem or close the campaign.

Goal: Independent refute-first read-only review of the D12 certificate library port, after freezing your VINE-A actual-unit transport checkpoint. You did not author this source port or its proof repairs. Root arranged the library/interface; W13 owns proof/import repairs. No edits outside your new /home/scott/wt-scratch/codex-takeover/audit-port-vp/** report/tools. Do not run Lean/Lake until the build baton is explicitly released by root; static mapping/source/API inspection can proceed now.

Port worktree /home/scott/WaveTurbulence-worktrees/port-vp; branch w/port-vp, base main e8b9589. Read lakefile.lean, WaveTurbulenceVineParam.lean, main Foundations/Vine/Param.lean. All 1824 mapped modules originate /home/scott/wt-scratch/vineparam-u/src/WaveTurbulenceVineParam; initial hashes/source paths in /home/scott/wt-scratch/port-vp/SOURCE-MAP.json. Canonical main imports listed CANONICAL-IMPORTS.json. Old gen.py and drive.py are read-only evidence: gen.py rewrites/drops raw Molecule copies, and old drive.py bypassed the compile gate; do not execute either. New validation uses targeted niced gated Lake build, with fresh project outputs in the isolated worktree; root copied only canonical main cache, not scratch oleans.

Review scope: every copied source hash, exact generated mapping against orig/ and COPIED-SHA256SUMS, namespace/collision/module/line-cap hygiene, body semantics of IsBlockDeg/IsVineDeg compatibility and canonical VineRealization imports, all proof-repair diffs including exact statement headers and definition formulas, closed final consumers and axioms once available. The intended theorem exports are WaveTurbulence.Vine.Param.vineparam : VineParamContract.VINEPARAM and vineparam_grouped, not conditional vineparam_of_base or unproved catalogue hypotheses. Check all source-chart/full-group semantic fields and source watches F72/F79, with exact source/standing premises and no new connectedness hypothesis. This is a focused port/source-compatibility review; do not certify the whole manuscript or seal an anchor.

Check D12 layout and the dependency direction: separate WaveTurbulenceVineParam lean_lib, canonical main molecule modules reused, main root imports only the small source interface rather than enumerating catalogue leaves. Frozen bytes, Lake dependency pin/toolchain, Mathlib source/build artifacts and quarantine unchanged. Root will expand checker/root-generation coverage for the second library before landing; identify required changes instead of editing shared scripts.

Keep conditional and closed results distinct. Record exact failure/limits. No source regeneration, wholesale library builds, staging, commits, source edits, source-statement weakening or new axioms. Use static probes/reports in your own scratch; actual consumers/axioms later only with root's explicit baton. End READY audit-port-vp (with exact scope) or STOPPED audit-port-vp: exact reason.

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

Handoff: files; approach; exact checks and output; #print axioms; uncertainties; errata/deviations; evidence of consuming actual producer. End READY <packet> or STOPPED <packet>: exact reason.
