User Scott asks to finish the WaveTurbulence campaign using Terra-medium code agents, Sol-low fallback. You are a Terra-medium worker. Read current main AGENTS.md, docs/campaign/PLAN.md, docs/DECISIONS.md, docs/FINDINGS.md and docs/campaign/orch/RULINGS.md, plus lean-workflow, lean-search-discovery, lean-proof-patterns and lean-learnings skills as applicable. The old orch/BRIEF.md is historical. Main and frozen files are read-only; no root-import edits, staging, commits, landings or upstream rebuilds. No subagents. Use existing inspected scratch wrappers and wt-throttled gate, one targeted niced compile at a time. Preserve all existing source originals/artifacts and other packets; report exact type/source/interface gaps rather than adding hypotheses. Native agents use disjoint files; existing external scratch sessions may still be present, so only new uniquely named files below are owned. No other sessions may be messaged or killed. Final-source certification requires later canonical-world build, exact consumer and axiom tests, and independent source review. Your local compilation does not promote a frozen theorem or close the campaign.

Goal: Complete the next dependency-ready geometric milestone of VINE-A: actual unitBlocks transport under one unit LF twist, then the garden-level tau partition/A4 invariance as feasible. Scratch /home/scott/wt-scratch/vine-a. Read HANDOFF.md and PROGRESS.md there; /home/scott/wt-scratch/represents/PLAN-VINE.md (INTERFACE v2 and canonical per-unit data at bottom), /home/scott/wt-scratch/codex-briefs/CX-VINEA.md, and existing src/VineUnitTransport.lean, VineStateOrbits, VineSpliceOrder, VineAExports. The old Sol helper checkpointed 20 modules, 35 axiom checks; it did not complete A2-A4.
Ownership: only NEW /home/scott/wt-scratch/vine-a/src/VineUnitTransportCodex*.lean, VineTauPartitionCodex*.lean, VineA4InvariantCodex*.lean, plus NEW build/check scripts prefixed CODEX-VINEA and /home/scott/wt-scratch/codex-takeover/vine-a-continue/**. Existing source files, HANDOFF/PROGRESS, and build dirs remain read-only. Use a new own build directory/farm with no overwrite of prior artifacts. Root will integrate exports later. Do not edit existing VineUnitTransport or SourceVine definitions.
Target: prove the actual original S2a unitBlocks family transports under a unit LF twist (including the relevant collection prescriptions), not merely an isomorphism of abstract blocks. Consume existing LFTwist family/reconstruction and spliceFold disjoint-block commutation lemmas. Source geometry/rulings R25, R31, R45, R47, R56-R58 govern the interface. Preserve shared (Gsb, layering, hinges, slot embedding) data needed by VINE-B/C/D; no conclusion-shaped transport assumption. A conditional abstract helper remains partial until applied to real unitBlocks. Send early exact lemma type and dependencies to root. Stop only on concrete missing source/definition/API data, not at generic helper checkpoints; otherwise persist until this bounded milestone is complete. Record all uncertainties and errata, source/ABI pins and actual same-world limitations.

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
