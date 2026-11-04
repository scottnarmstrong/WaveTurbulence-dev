# Decisions and rulings

Format: D<n> — date (UTC) — who — decision — reason.

- D1 — 2026-11-03 ~15:40 — Scott — Scope: **everything in Lean**, no black boxes: DH21, DH23 and the needed parts of
  DH21-2 / DH19, GIT20's trilinear estimates, NLS-on-torus smooth-solution theory, Gaussian/cumulant facts. External
  results become proved Lean, not hypotheses.
- D2 — 2026-11-03 ~15:40 — Scott — Main theorem covers **0 < γ < 1 on the square torus** `[0,L]^d` (Theorem 1.1 as
  stated). The γ = 1 generic rectangular torus case is out of scope.
- D3 — 2026-11-03 ~15:40 — Scott — Fleet: Claude Code workers now on claude-1/10/13/14; Codex provers on **codex-3**
  allowed for this project; add codex-1/2 after their resets. Never codex-4.
- D4 — 2026-11-03 ~15:40 — Scott — Private GitHub repo `scottnarmstrong/WaveTurbulence-dev` as campaign HQ.
- D5 — 2026-11-03 ~16:00 — Scott — Codex provers run **GPT-6.1-Sol, effort low, normal mode** (not fast).
- D6 — 2026-11-03 ~17:00 — Scott ("go with your recommendations on all four readings", in reply to the complete
  Wave A code shown for approval) — **Wave A approved and frozen**: Theorem 1.1 (`WaveTurbulence.main`) and
  Proposition 3.2 (`WaveTurbulence.wkelwp`) as `DRAFT_SORRY` anchors, and 13 sealed definitions (`Mom`,
  `latticePoint`, `collisionOp`, `IsWKESolution`, `partialDeriv`, `normLaplacian`, `torusFourierCoeff`,
  `IsSmoothNLSSolution`, `stdComplexGaussian`, `initialCoeff`, `solvableEvent`, `kineticTime`, `weightedL2Norm`),
  from draft sha256 938afa97… (audits: docs/campaign/orch/audits/WaveA-main-draft.md, WaveA-v2-delta.md). Readings
  adopted: E = E[1_F ·] (not conditional); `MeasurableSet F` asserted; Dirac deltas read as the hyperplane integral
  `(2|ℓ₁|)⁻¹∫_{ℓ₁^⊥}`; statement about smooth NLS solutions (not the Fourier-side system); plus the other recommended
  readings listed with the code (closed-interval WKE solution class, data through Fourier coefficients, selection
  device ∀ U, circular complex Gaussians, (log L)^{40d}, ⟨k⟩ = (1+|k|²)^{1/2}). Packaging (semantics-neutral): one
  declaration per file under `WaveTurbulence/Frozen/`, theorem bodies `by sorry` between anchor markers; the anchor
  checker accepts `abbrev` (for `Mom`) as a definition anchor.
- D7 — 2026-11-04 ~17:10 — Scott ("I approve all", in reply to wt-orch's list: approve D7 and D8 and land the two
  freeze branches; the complete Wave B tier-B1 code shown for approval in `docs/review/WAVE-B-B1.md`, snapshot 9,
  `/home/scott/wt-scratch/waveb-snap-9`, SHA256SUMS `30263a99…`) — **Wave B tier B1 approved and frozen**: 12
  `DRAFT_SORRY` theorem anchors (B1.1–B1.12: `propansatz`, `layergarden`, `fixedpoint`, `nlsAkBridge`, `wkeTaylor`,
  `sumint`, `countLemma`, `atomCountLemma`, `quadExpSum2`, `quadExpSum3`, `canonicalCharacterization`,
  `layergardenFlower`) and 214 sealed definitions (FREEZE-LIST.md of snapshot 9). Includes the F68 fix (`PatValid`'s
  `dChild` designation is a layer-`p` node), the F78 fix (`coupleSum`'s `∂_t` roots are layer-`p` branching nodes) and
  the F80 fix (`XNorm`'s a.e. `C^{Λ₁}` guard). Audits: `WaveB-snapshot6.md`, `WaveB-snapshot7.md`,
  `WaveB-snapshot8.md`, the independent audit of the snapshot-9 delta, and the earlier Wave B audits. Packaging
  (semantics-neutral): one declaration per file under `WaveTurbulence/Frozen/`, as D6; the guard accepts Lean Unicode
  identifiers. Landed by wt-orch on Scott's instruction ("land the freeze branches yourself", 2026-11-04 ~18:15)
  with seven seals (B1.4 `nlsAkBridge`, B1.6 `sumint`, B1.7–B1.11), whose second-key audits are pending.
