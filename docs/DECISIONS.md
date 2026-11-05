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
- D8 — 2026-11-04 ~17:10 — Scott ("I approve all", same reply as D7; the complete Wave B tier-B2 code shown for
  approval in `docs/review/WAVE-B-B2.md`: `/home/scott/wt-scratch/waveb2-snap-final`, SHA256SUMS `b3db9c43…`, on B1
  snapshot 9) — **Wave B tier B2 approved and frozen**: 7 `DRAFT_SORRY` theorem anchors (B2.1 `regularAsymptotics`,
  B2.2 `incoherentDecay`, and the decoding obligations O1 `RegCpl.exists_decodes`, O2 `existsUnique_regCpl_decodes`,
  O3 `RegChain.exists_decodesTree`, O4 `existsUnique_regChain_decodesTree`, O5 `RegCpl.size_eq_order`) and 69 sealed
  definitions (FREEZE-LIST.md, B2-CL-22; 89 declarations held out, B2.3 among them). Audits: `WaveB2-stage1.md`,
  `WaveB2-stage23.md`, `WaveB2-handoff.md` (addenda 1–7), `WaveB2-independent-audit.md` (re-checks 1–3). Packaging
  (semantics-neutral): one declaration per file under `WaveTurbulence/Frozen/`, except that each of nine `mutual`
  blocks is one file shared by its members' entries (guard change `a013926`, signed off by Scott 2026-11-04). Landed
  by wt-orch on Scott's instruction with six seals (O1–O5, B2.2), whose second-key audits are pending.
- D9 — 2026-11-04 ~21:50 — Scott (answer "Both (Recommended)" to wt-orch's question on the γ range, after FINDINGS
  F69b/F73/F75 and docs/review/ESCALATION-F69b.md) — **γ ≤ 1/2: restrict and research.** (1) wt-orch drafts versioned
  successors of the frozen statements restricted to γ ∈ (1/2, 1) (`main_v2` and the affected Wave B anchors) for
  Scott's approval of the exact text; (2) a research packet works on a repair for 0 < γ ≤ 1/2 in parallel; (3) the
  letter to Deng and Hani (draft `docs/review/LETTER-DENG-HANI-DRAFT.md`) is kept ready for Scott to send. The erratum
  (DH23 Prop 9.6 false for γ ≤ 1/2, necklace counterexample) is recorded in docs/ERRATA-AND-DEVIATIONS.md (E1).
- D10 — 2026-11-04 ~23:15 — Scott ("approve the five successors", in reply to the complete code on
  docs/review/GAMMA-HALF-SUCCESSORS.md, main 9c5ec0d) — **γ ∈ (1/2, 1) versioned successors approved and frozen**:
  `main_v2`, `propansatz_v2`, `layergarden_v2`, `fixedpoint_v2`, `layergardenFlower_v2` as DRAFT_SORRY anchors.
  Each is its original verbatim except: the name; `1 / 2 < P.γ →` at the head of the body (`hγ : γ ∈ Ioo (1 / 2) 1`
  for `main_v2`); one docstring paragraph. Packaging (semantics-neutral): each imports its own provider stub
  `Provider.<Name>V2`. The originals stay frozen and open (D9; erratum E1).
- D11 — 2026-11-05 ~15:58 — Scott ("I approve all, defer approvals now and just get this done", in reply to the open
  questions listed by wt-orch, including review page docs/review/GAMMA-LE-HALF-VINES.md) — **The enlarged vine family
  for 0 < γ ≤ 1/2 is approved as recommended.** The decision has three parts:
  - (a) The exact Lean text `TVineDefs.lean` (sha256 prefix `31242ecfe64dcdab`, the text on the review page)
    is the definition of the enlarged family (T-vines). It is to be frozen when a γ ≤ 1/2 extension starts, after
    the review page's small fixes, none of which changes the Lean text.
  - (b) The γ ≤ 1/2 extension starts only after the γ ∈ (1/2, 1) chain is sealed.
  - (c) The three open questions are settled:
    - Q1: the "no interior cut atom" clause stays out, and is proved later as a lemma.
    - Q2: γ-parametrised HV/VC/HVC/Chain are written as part of the extension, with the same review process.
    - Q3: the groups of a T-vine are its pieces.
- D12 — 2026-11-05 ~15:58 — Scott (same reply) — **Home of the VINEPARAM catalogue (PORT batch 4a):** option (iii) of
  PORT-PLAN.
  - The certificate catalogue (about 4.5k modules, ~878k lines) goes in a separate `lean_lib` of this package,
    `WaveTurbulenceVineParam`.
  - It is rebuilt on the canonical universe, with its ~580 Vine*/Molecule* copies dropped in favour of
    Foundations.Molecule.*.
  - The main library imports only `Vine.Param.vineparam` and `vineparam_grouped`.
  - Regenerating the catalogue with a smaller certificate format (option (ii)) is deferred. It is an optimization if
    the build cost blocks CI or the Palomar intake.
- Standing authorization — 2026-11-05 — Scott: "I approve all, defer approvals now and just get this done".
  - wt-orch makes the remaining campaign decisions itself, following its recommendations, and records each one here
    or in the orchestrator's RULINGS.md.
  - Frozen-statement changes still follow the versioned-successor and second-key-audit process, and are recorded as
    D-entries.
