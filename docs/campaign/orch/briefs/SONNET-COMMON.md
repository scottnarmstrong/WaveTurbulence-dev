## Hard rules (verbatim from /home/scott/WaveTurbulence-dev/AGENTS.md)
1. **Never use `set_option maxHeartbeats`** or any other heartbeat, recursion-depth or synthesis-budget override. A default-budget failure is a design signal: refactor or split.
2. **No Lean file may exceed 1500 lines.** Split into focused modules before that point.
3. **Every `.lean` file is a Lean module.** File shape: copyright comment, `module`, imports (`public import` for the interface), module docstring, `public section`. Expose (`@[expose]`) definitions whose bodies must unfold, and every source-facing or frozen definition.
4. **No `axiom`, `admit`, `unsafe` or `opaque`.** `sorry` is allowed only as the manifest-bound body of an owner-approved frozen statement (`DRAFT_SORRY`). Placeholder definitions are forbidden.
5. **Frozen files are read-only.** If a frozen declaration looks wrong, stop and report. Never add a premise and never substitute a helper.
6. **No conclusion-shaped hypotheses.** A theorem may assume only source premises, standing assumptions, typing data and explicit owner rulings. A conditional helper gets a distinct name and never stands in for a source result.
7. **Providers are quarantined.** Only the frozen anchor may import a provider or a `DRAFT_SORRY` anchor.
8. **Builds.** One targeted `nice -n 5 lake build <Module>` (or `lake env lean <file>`) at a time, through the `wt-throttled` compile gate. Never build the whole library, never `lake clean`, never rebuild Mathlib. A wait on the gate is expected, not a hang. This is a shared machine.
9. **Errata.** Report every suspected defect in the pinned sources in your handoff (location, quoted text, why it is wrong), and every deviation you introduce.
And: no `sorry` anywhere in your files.

## Operating rules
- **Builds.** Build scratch modules with `nice -n 5 lake env lean -o <scratch>/build/<Mod>.olean <file>` (LEAN_PATH extended with your build dir and the build dirs of the scratch packets you depend on; model it on an existing packet's build script, e.g. /home/scott/wt-scratch/lg-spine/lgbuild.sh), run from the worktree named below. Write a small `build.sh <Module>` for yourself first. One build at a time; check every exit status directly. The worktree is shared with other agents: never run `lake build` there except for a single missing project module, and only after `pgrep -af "lake build"` shows no other build in that worktree.
- **Copying other packets' work.** Never edit another packet's scratch directory. Copy the files you need into your own scratch with their sha256 (record them in COPIED-SHA256SUMS), or put the other build dir on LEAN_PATH read-only. Several of them are still being edited by other agents, so copy at first read.
- **Wave B context.** B1 (snapshot 9) and B2 (the final candidate) are frozen and being landed on main. The scratch packets you build on use the draft namespaces (`WaveBDraft`, `WaveB2Draft`); keep using them, since the port to the frozen modules is mechanical and done at seal time. Snapshot 9 is /home/scott/wt-scratch/waveb-snap-9 (System.lean cc53aad3; F80 `XNorm` guard); B2 final is /home/scott/wt-scratch/waveb2-snap-final. If your closure contains a snapshot-7/8 `WaveBDraft/System.lean` (59365906), switch it to snapshot 9's and repair proofs only, following /home/scott/WaveTurbulence-worktrees/orch/docs/campaign/orch/audits/INCOH-INST-snap9.md §2.
- **Prohibitions.** No tmux interaction, no codex/claude, no subagents, no push, no land, no `git stash`. Never edit /home/scott/WaveTurbulence-dev, the root WaveTurbulence.lean, frozen files or the manifest.
- **Search first.** Before proving a lemma, grep the scratch packets you depend on (and /home/scott/wt-scratch/lg-spine, vines, mole, molecpl, lftwist, clcn) for an existing statement.
- **Progress file.** Keep PROGRESS.md in your scratch dir current after every compiled module: what is proved (exact names), how it was checked, and the exact next step.
- **How to end.** End only with:
  - `READY <packet>`: done, with the final checks below;
  - `STOPPED <packet>: <reason>`: a genuine obstruction (a false statement with an explicit counterexample, a missing idea after two routes, or a defect in a frozen or spine statement);
  - `CHECKPOINT <packet>: <exact next step>`: only when your context is genuinely close to its limit; update PROGRESS.md first, and I will start a fresh agent from it.
  Do not stop at milestones; continue to the next step.
- **Final checks before READY.**
  - A FRESH rebuild of your closure (topological order, new build dir, exit codes logged).
  - `#print axioms` of the main results; expect only propext, Classical.choice, Quot.sound.
  - A hygiene grep (`sorry`/`admit`/`axiom`/`opaque`/`unsafe`/`maxHeartbeats`) over your files.
  - An exact-type check of each target statement: a transient `example : <pinned statement> := <your theorem>`, deleted afterwards.
  - HANDOFF.md, in AGENTS.md format: files; approach; exact checks and output; axioms; uncertainties; errata and deviations. Every source reading goes in it, with line numbers.
- **Final message.** Your handoff to me (wt-orch), ending with the READY/STOPPED/CHECKPOINT line. Never report a check you did not run.
