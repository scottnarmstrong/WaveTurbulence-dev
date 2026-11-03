# WaveTurbulence-dev — campaign HQ

Lean 4 formalization of

> Y. Deng and Z. Hani, *Long time justification of wave turbulence theory*,
> [arXiv:2311.10082v2](https://arxiv.org/abs/2311.10082) (2024).

**Scope (D1):** everything proved in Lean, no black boxes. That covers the target paper and the results it uses from
Deng–Hani's earlier papers (DH21, DH23, parts of DH21-2 and DH19), the trilinear estimates of Germain–Ionescu–Tran
(GIT20), smooth-solution theory for cubic NLS on the torus, and the Gaussian/cumulant facts.
**Main theorem (D2):** Theorem 1.1 for `0 < γ < 1` on the square torus `[0,L]^d`, `d ≥ 3`.

## Status (2026-11-03 16:05 UTC)

Blueprint v2 (after independent topology review): 275 nodes, 84 packets, ≈273k lines estimated, critical path weight 99.
Phase P1/P2: sources pinned; paper maps of DH21/DH21-2 and DH23 done, target-paper maps in progress; exact Lean draft
**Wave A frozen (D6, 2026-11-03):** Theorem 1.1 (`WaveTurbulence.main`) and Prop 3.2 (`WaveTurbulence.wkelwp`) as
`DRAFT_SORRY` anchors in `WaveTurbulence/Frozen/Theorems/`, 13 sealed definitions in `WaveTurbulence/Frozen/Defs/`,
manifest `manifest/frozen.json`. Route-independent infrastructure packets running (PLAN.md).

```text
DRAFT_ANCHORS: 2 (WaveTurbulence/Frozen/Theorems/Main.lean, WaveTurbulence/Frozen/Theorems/Wkelwp.lean)
SEALED DEFINITIONS: 13
UNREGISTERED_SORRIES: 0
DRAFT_IMPORT_VIOLATIONS: 0
SEALED THEOREMS: 0
```

### Workers

| tmux | model / account | packet | brief |
|---|---|---|---|
| wt-orch | Claude Opus / claude-1 | audits: Wave B stage audits (Task 4b); done: freeze check, figure defs, topology review, infra review | [orch/TASK4.md](docs/campaign/orch/TASK4.md) |
| wt-gauss-hc | Claude Opus / claude-10 | **Wave B drafts** (critical path): core carriers, system objects, B1 statements (GAUSS-HC landed f986d35) | [WAVEB-DRAFT](docs/campaign/briefs/WAVEB-DRAFT.md) |
| wt-torus | Claude Opus / claude-14 | NLS smooth-solution theory, reduction to the a_k system (TORUS-FOURIER landed 5beb902) | [NLS](docs/campaign/briefs/NLS.md) |
| wt-wke | Claude Opus / claude-13 | WKE-TAYLOR: power-series existence, τ_max characterization (`wkelwp` conjuncts 1–2), Taylor bound F10 | [WKE-TAYLOR](docs/campaign/briefs/WKE-TAYLOR.md) |
| wt-cumul | GPT-6.1-Sol low / codex-3 | complex Gaussians, Isserlis, cumulants, `propertycm` | [CUMUL](docs/campaign/briefs/CUMUL.md) |
| wt-nt | GPT-6.1-Sol low / codex-3 | van der Corput: circle problem with exponent < 2/3 (F3) | [NT-CIRCLE-v2](docs/campaign/briefs/NT-CIRCLE-v2.md) |
| wt-ansob | GPT-6.1-Sol low / codex-3 | N4: Sobolev/Morrey, simplex volumes, DH21 (10.5), DH21 Lemma 10.2 | [AN-SOB](docs/campaign/briefs/AN-SOB.md) |
| wt-gausssum | GPT-6.1-Sol low / codex-3 | NT1: Dirichlet approximation, quadratic Weyl/Gauss sums | [GAUSSSUM](docs/campaign/briefs/GAUSSSUM.md) |
| wt-resonant | GPT-6.1-Sol low / codex-3 | N5: resonant measure, p.v. 1/Ω, DH21 Lemma 6.3 | [RESONANT](docs/campaign/briefs/RESONANT.md) |
| wt-anfourier | GPT-6.1-Sol low / codex-3 | N1: Gevrey cutoff χ₀, time-Fourier norms 𝔛, restriction norms | [AN-FOURIER](docs/campaign/briefs/AN-FOURIER.md) |

Landed: TORUS-FOURIER (5beb902), GAUSS-HC (f986d35, off-route infrastructure, F34).

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
- [docs/blueprint/GRAPH.md](docs/blueprint/GRAPH.md) — node-level dependency graph (264 nodes, 76 packets, ≈266k lines est.); [docs/blueprint/WAVE-B.md](docs/blueprint/WAVE-B.md) — Wave B proposal.
