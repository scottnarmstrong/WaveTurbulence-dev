# WaveTurbulence-dev — campaign HQ

Lean 4 formalization of

> Y. Deng and Z. Hani, *Long time justification of wave turbulence theory*,
> [arXiv:2311.10082v2](https://arxiv.org/abs/2311.10082) (2024).

**Scope (D1):** everything proved in Lean, no black boxes. That covers the target paper and the results it uses from
Deng–Hani's earlier papers (DH21, DH23, parts of DH21-2 and DH19), the trilinear estimates of Germain–Ionescu–Tran
(GIT20), smooth-solution theory for cubic NLS on the torus, and the Gaussian/cumulant facts.
**Main theorem (D2):** Theorem 1.1 for `0 < γ < 1` on the square torus `[0,L]^d`, `d ≥ 3`.

## Status (2026-11-03 16:05 UTC)

Phase P1/P2: sources pinned; paper maps of DH21/DH21-2 and DH23 done, target-paper maps in progress; exact Lean draft
of Theorem 1.1 and its definitions elaborates and is under independent audit (wt-orch). No frozen statements yet.
Route-independent infrastructure packets started (PLAN.md).

```text
DRAFT_ANCHORS: 0
UNREGISTERED_SORRIES: 0
DRAFT_IMPORT_VIOLATIONS: 0
SEALED: 0
```

### Workers

| tmux | model / account | packet | brief |
|---|---|---|---|
| wt-orch | Claude Opus / claude-1 | statement audits, blueprint review | [orch/BRIEF.md](docs/campaign/orch/BRIEF.md) |
| wt-gauss-hc | Claude Opus / claude-10 | Gaussian hypercontractivity, large deviations (DH21 Lemma A.3) | [GAUSS-HC](docs/campaign/briefs/GAUSS-HC.md) |
| wt-torus | Claude Opus / claude-14 | Fourier series on the torus | [TORUS-FOURIER](docs/campaign/briefs/TORUS-FOURIER.md) |
| wt-wke | Claude Opus / claude-13 | collision operator, GIT20 trilinear estimate, Prop `wkelwp`, WKE Taylor bounds | [WKE](docs/campaign/briefs/WKE.md) |
| wt-cumul | GPT-6.1-Sol low / codex-3 | complex Gaussians, Isserlis, cumulants | [CUMUL](docs/campaign/briefs/CUMUL.md) |
| wt-nt | GPT-6.1-Sol low / codex-3 | circle problem (exponent 2/3), annulus counting | [NT-CIRCLE](docs/campaign/briefs/NT-CIRCLE.md) |

## Papers

| key | reference |
|---|---|
| target | Y. Deng, Z. Hani, *Long time justification of wave turbulence theory*, arXiv:2311.10082 |
| DH21 | Y. Deng, Z. Hani, *Full derivation of the wave kinetic equation*, Invent. Math. 233 (2023) 543–724, arXiv:2104.11204 |
| DH21-2 | Y. Deng, Z. Hani, *Propagation of chaos and higher order statistics in wave kinetic theory*, JEMS, arXiv:2110.04565 |
| DH23 | Y. Deng, Z. Hani, *Derivation of the wave kinetic equation: full range of scaling laws*, arXiv:2301.07063 |
| DH19 | Y. Deng, Z. Hani, *On the derivation of the wave kinetic equation for NLS*, Forum Math. Pi 9 (2021) e6, arXiv:1912.09518 |
| GIT20 | P. Germain, A. Ionescu, M.-B. Tran, *Optimal local well-posedness theory for the kinetic wave equation*, J. Funct. Anal. (2020), arXiv:1711.05587 |

## Documents

- [docs/DECISIONS.md](docs/DECISIONS.md) — rulings.
- [docs/FINDINGS.md](docs/FINDINGS.md) — source findings and candidate errata.
- [docs/campaign/PLAN.md](docs/campaign/PLAN.md) — phases, infrastructure packets, fleet.
