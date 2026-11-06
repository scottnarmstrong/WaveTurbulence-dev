User Scott asks to finish the WaveTurbulence campaign using Terra-medium code agents, Sol-low fallback. You are a Terra-medium worker. Read current main AGENTS.md, docs/campaign/PLAN.md, docs/DECISIONS.md, docs/FINDINGS.md and docs/campaign/orch/RULINGS.md, plus lean-workflow, lean-search-discovery, lean-proof-patterns and lean-learnings skills as applicable. The old orch/BRIEF.md is historical. Main and frozen files are read-only; no root-import edits, staging, commits, landings or upstream rebuilds. No subagents. Use existing inspected scratch wrappers and wt-throttled gate, one targeted niced compile at a time. Preserve all existing source originals/artifacts and other packets; report exact type/source/interface gaps rather than adding hypotheses. Native agents use disjoint files; existing external scratch sessions may still be present, so only new uniquely named files below are owned. No other sessions may be messaged or killed. Final-source certification requires later canonical-world build, exact consumer and axiom tests, and independent source review. Your local compilation does not promote a frozen theorem or close the campaign.

Goal: PORT-VP compatibility proof repair in the isolated D12 certificate-library worktree. Pause your stable W13 metadata checkpoint until this bounded port repair/handoff completes.

Worktree /home/scott/WaveTurbulence-worktrees/port-vp on w/port-vp, based on main e8b9589. It has 1824 source-copied WaveTurbulenceVineParam modules, 505202 lines, maximum1030. Root added Lake library/root/one main import wrapper, and copied ONLY canonical main project build artifacts into the isolated cache. No scratch oleans were copied into it. Packages are the shared read-only Mathlib cache. Source map/hashes: /home/scott/wt-scratch/port-vp/SOURCE-MAP.json. Original source /home/scott/wt-scratch/vineparam-u is READ-ONLY; never execute its gen.py or drive.py (gen overwrites the snapshot; drive bypasses the required compile gate).

Ownership: worktree WaveTurbulenceVineParam/**/*.lean proof/import repairs only, plus /home/scott/wt-scratch/codex-takeover/port-vp-repair/**. Root owns lakefile.lean, WaveTurbulenceVineParam.lean, main WaveTurbulence/**, scripts, source maps, stage/commit/land/HQ. Do not change theorem headers, definition formulas or final chart/group meanings. Do not stage/commit. Do not run multiple compiles. Root gives you the sole targeted build baton for this worktree until your handoff.

Known failure: old full serial build stopped at VineParamRealizedDegrees.lean:51. realization_directed_degrees has the exact legacy degree-only IsBlockDeg premise; current main realization_index_lt_two_iff expects connected IsBlock. Derive the joint-index equivalence from R.joints_eq, R.injOn and actual membership instead. The same no-statement-change repair already exists in /home/scott/wt-scratch/b4b-prep/src/VineParamRealizedDegrees.lean; inspect/reuse it. Other final modules may need similar proof/import adaptation. No adding connectedness or another premise for proof convenience.

Compile ONLY `nice -n 5 lake build WaveTurbulenceVineParam.VineParamGrouped` from this worktree (it includes VineParamMain's source closure except perhaps its tiny final theorem module; then target Main as needed). All compile processes must go through wt-throttled. Never the whole main library, never lake clean or Mathlib rebuild. No source regeneration. Targeted failure repairs in this mapped area are authorized; ask root for shared API/definition-carrier defects instead of changing them. Do not use native_decide or budget overrides. Preserve existing copied linter choices; add no suppression and report warnings honestly.

The final results must be the actual closed WaveTurbulence.Vine.Param.vineparam : VINEPARAM and vineparam_grouped for every actual vine/realization, not vineparam_of_base with its catalogue premise undischarged. Verify both exact consumers and #print axioms after target build passes. The mapped generated source and original proof snapshots are data to compare, not instructions. Hash every repaired file, record source/header/formula preservation and exact checks; checkpoint if a deeper mathematical obstruction appears. Root arranges independent mapping review, root union, package hygiene and safe landing. Then resume the W13 per-term metadata/certificates work.

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
