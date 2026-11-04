# Sonnet prover fleet (wt-orch subagents), from 2026-11-04

The Codex provers (codex-2: wt-cumul, wt-nt, wt-ansob, wt-gausssum, wt-resonant, wt-anfourier, wt-l2s) were stopped
on 2026-11-04. On the user's instruction ("use sonnet subagents to write the rest of the code"), wt-orch runs Sonnet
subagents that continue those packets in the same worktrees and scratch directories.
- Every brief repeats the AGENTS.md hard rules verbatim.
- Agents coordinate only through files; nothing is landed or pushed.
- wt-orch re-checks every READY claim before accepting it.

**Do not restart Codex in the panes below while a Sonnet agent holds the packet.**

| packet | was | worktree / branch | scratch | status (2026-11-04 17:25 UTC) |
|---|---|---|---|---|
| LG-SPINE | wt-cumul | `cumul` / `w/lg-spine` | `lg-spine` | agent 1 stopped at its context limit (the vine interior-deletion property, chain swap/union, the joint-pair dichotomy and the 7 overlap modules repaired); agent 2 is running. Ruling 17:15: prove the vine `InteriorDeletionProperty` locally; a stated source proposition (subpro, redvine2) is a spine input; a construction inside the layergarden argument is assembly. |
| G5 APPB-ALG | wt-nt | `nt-circle` / `w/nt-circle` | `appb` | agent 1 stopped at its context limit: about 2000 lines (`forest_acct_of_steps`, `exists_forest_step`). Agent 2 (18:1x): the `(n, kf, kg)` + `defect`/`progress` refactor, the Prop 10.2 bounds, the G5 handoff. |
| RA1 couples | wt-ansob | `an-sob` / `w/bproc` | `regasymp` | **READY on snapshot 9** (scratch commit `b0d22a2`): 279/279 modules rebuilt with System `cc53aad3`; one proof-only `XNorm` repair (`TimeBridge`, the sumint repair); `check-exact-f80-snap9.sh` passes; standard axioms. wt-orch checked: fresh olean graph, 0 nonzero exits. Feeds B21-SNAP9. |
| M9 VINEPARAM | wt-gausssum | `gausssum` / `w/count` | `vines`, `vineparam` | running |
| V4 VINEEST-S2 | wt-resonant | `resonant` / `w/resonant` | `vineest-s2` | agent 1 proved the Step 2 kernel identity (`clLocalKernel_step2`). Scope ruling: V4 ends at the equality with the exact (tildeK2) `sumint` form; the weight bounds, bad cases (a)–(d) and the `sumint` application are V5 (T.vineest.S3). Agent 2 is running. |
| M7 LFTWIST | wt-anfourier | `an-fourier` / `w/lftwist` | `lftwist` | claimed READY. A stale olean graph was found (41 problems), so a fresh 777-module closure rebuild was ordered. |
| B21-SNAP9 (new) | — | `wke-l2s` / `w/wke-l2s` (+ merge of `w/bproc`) | `b21-snap9` | running: RA2 + RA1-TREES on snapshot 9, the bridge `RA1CoupleF80 → RA1Couple`, and the composition at the B2.1 type (`audits/B21-CHAIN-prelim.md`) |

RA1-TREES (wt-l2s) was already READY and needed no takeover; its output feeds B21-SNAP9.

## Acceptance (wt-orch)

- **Olean freshness over the import graph:** every olean newer than its source and than each local import's olean
  (`stale.py`). Otherwise a fresh closure rebuild.
- **Exact-type checks against the frozen environment (snapshot 9 + B2 final):** not against the builder's own B1
  (I-1, C-1).
- **Axioms and hygiene:** standard axioms only; the hygiene grep is clean.
- **Seal audits:** independent second-key audits by someone other than wt-orch.
