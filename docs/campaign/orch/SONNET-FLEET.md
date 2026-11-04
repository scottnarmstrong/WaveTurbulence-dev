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
| LG-SPINE | wt-cumul | `cumul` / `w/lg-spine` | `lg-spine` | **`layergarden_of_spine (S : SpineInputs) (hcount : FinalCountGate) : LayergardenGate` compiles** (Session 10; standard axioms; `SpineInputs` published in SPINE.md). Inputs:
  - `leafCoherent`, `taylor`: PL23/PL4;
  - `leafDecay`: B2.2 leafwise;
  - `coarse`: S3, `CoarseSplicedAt`;
  - `ladder`: S3a, `LadderFourierAt`, PROVED;
  - `stage1`: `Stage1ReductionGate`, which S2a/S2/S4 provide; its class-count conjunct needs M8;
  - `FinalCountGate`, kept separate (γ-sensitive, F69b).

  Remaining: rebase onto snapshot 9 and the F72 universe (R8), the fresh rebuild and the verbatim type check. These wait on S2a and UNIVERSE. |
| G5 APPB-ALG | wt-nt | `nt-circle` / `w/nt-circle` | `appb` | **READY 20:1x**: `dh23_prop_10_2` (all three bounds). Fresh rebuild 809/809 into build-final; standard axioms (checked by wt-orch). Deviations: `GraphOk` size bound; decoration-dependent SG set; explicit η smallness. Open: `sourceRho` (F53) vs L1829's ρ = q + m′, to check in audit. |
| RA1 couples | wt-ansob | `an-sob` / `w/bproc` | `regasymp` | **READY on snapshot 9** (scratch commit `b0d22a2`): 279/279 modules rebuilt with System `cc53aad3`; one proof-only `XNorm` repair (`TimeBridge`, the sumint repair); `check-exact-f80-snap9.sh` passes; standard axioms. wt-orch checked: fresh olean graph, 0 nonzero exits. Feeds B21-SNAP9. |
| M9 VINEPARAM | wt-gausssum | `gausssum` / `w/count` | `vines`, `vineparam` | running |
| V4 VINEEST-S2 | wt-resonant | `resonant` / `w/resonant` | `vineest-s2` | **READY 19:25** (scratch commit `84a5ee3`): `vineChain_eq_sumintForm`. Fresh snapshot-9 rebuild: 709/709 OK, standard axioms. Named obligations: VINEPARAM, `SumintSigned`. The V5 obligation list is in its HANDOFF, including the open `hb1`/`hb2` (leaf lower children) and δ' = 2δ against τ* = Dδ. |
| M7 LFTWIST | wt-anfourier | `an-fourier` / `w/lftwist` | `lftwist` | claimed READY. A stale olean graph was found (41 problems), so a fresh 777-module closure rebuild was ordered. |
| B21-SNAP9 (new) | — | `wke-l2s` / `w/wke-l2s` (+ merge of `w/bproc`) | `b21-snap9` | running: RA2 + RA1-TREES on snapshot 9, the bridge `RA1CoupleF80 → RA1Couple`, and the composition at the B2.1 type (`audits/B21-CHAIN-prelim.md`) |

| M8 LAYERCNT (new) | — | `an-sob` (shared, `lake env` only) | `layercnt` | started 18:45: TARGET layerlad and layervine (L1501–L1532) for LG-SPINE (T.plg.ab) |
| S1 STAGE1-COMB (new) | — | `an-sob` (shared) | `stage1` | started 18:45: vinechainlem (DH23 Lemma 8.1), 𝒱 / congruence (equivalence; F20, F38), defdiff |
| S3 LADDER (new) | — | `an-sob` (shared) | `ladder` | started 18:45: LG-SPINE spine inputs `LadderDecayAt`, `LadderFourierAt`, `CoarseSplicedAt`, word for word |
| X2 FLOWER-SPINE (taken from wt-gauss-hc, never started) | wt-gauss-hc (Claude, waiting) | `an-sob` (shared) | `flower-spine` | **Restarted 21:20** (agent 2): `SpineInputs` is published, so this agent defines `FlowerSpineInputs` (shared fields word for word, plus the flower-specific adjustments) and does the flower assembly. |

RA1-TREES (wt-l2s) was already READY and needed no takeover; its output feeds B21-SNAP9.

| S3a LADDER-FOURIER | — | `an-sob` | `ladder` | **READY 21:1x**: `ladderFourier_prefix : WTPrefix LadderFourierAt` (= `LadderFourierGate`). Fresh 59-module rebuild, all exit 0; standard axioms; exact type against the pin `b8a8692f`, which equals the live lg-spine file (checked by wt-orch).
  - Deviations: no integer-offset classes; end rungs not paired; presentation fixed by the (u₀,u₁) signature.
  - Suspected errata: L2013–2014 (the double-bond Γ identity holds only at interior rungs); L2034/2036 (factorial exponent).
  - Port note: `LadderDisj` is a copy of the B2 Ladders file. |
| S3b LADDER-DECAY | — | `an-sob` | `ladder-decay` | running: ladder chart, then rung sums, then the different-layer gain |
| S2a REDSPLICE-DEF (new, R7) | — | `an-sob` | `redsplice` | started 19:20: the Stage 1 construction, the bridge to the choice data, `hingeOutsideFirst` |
| SUMINT-SIGNED | — | dev env | `sumint-signed` | **READY 21:0x**: `signed_of_sumint : VineEstS2.SumintSigned`. Fresh snapshot-9 build 407/407 OK (checked by wt-orch); standard axioms. The sign enters only through the affine time rescaling of the cubic Weyl sum; no reduction to the unsigned case exists, because the nonlinear determinant is not sign-invariant. Port note: this is a 404-module fork of Foundations/Sumint. At landing, prefer replacing Foundations/Sumint by the signed version and deriving `sumint` as the all-plus case, to avoid a second copy. |

Not held by Sonnet agents:
- **PL234 (wt-wke):** done. ISSUE-APPCONJ is ruled (RULINGS.md R1).
- **MOLEPROP4 + THEOREM-A (wt-torus):** done in scratch.
- **G-chain** (S2a, S4, G1, G2, G3, G8, F1, F3, S2, V5): waits on dependencies (S1, V4, PL4, M9).
- **F2 PLG = `layergarden` itself:** this is LG-SPINE.

## Acceptance (wt-orch)

- **Olean freshness over the import graph:** every olean newer than its source and than each local import's olean
  (`stale.py`). Otherwise a fresh closure rebuild.
- **Exact-type checks against the frozen environment (snapshot 9 + B2 final):** not against the builder's own B1
  (I-1, C-1).
- **Axioms and hygiene:** standard axioms only; the hygiene grep is clean.
- **Seal audits:** independent second-key audits by someone other than wt-orch.
