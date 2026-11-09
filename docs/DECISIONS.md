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
- D13 — 2026-11-06 — wt-orch under the standing authorization (Scott, 2026-11-05: "I approve all, defer approvals now
  and just get this done"), after FLOWER-CUT (R62) and the independent statement audit
  (/home/scott/wt-scratch/audit-flower-v3/REPORT.md: FIDELITY PASS, CONSUMERS PASS) — **Flower cutoff successor
  `layergardenFlower_v3` frozen**:
  - What changed. `layergardenFlower_v3` is `layergardenFlower_v2` verbatim except `flowerSum` → `flowerSumP`
    (and the name, the provider import and the docstring). `flowerSumP` is `flowerSum` verbatim except that the
    weights `LG.cutWeight1/2` (a dyadic cutoff of a maximum) become `LG.cutWeight1P/2P`.
  - Four new SEALED definitions, in DH21's per-leaf / per-node product form (T L2283–L2285, DH21 L2731, L2735):
    `prodDyadicCut`, `LayeredGarden.cutWeight1P`, `LayeredGarden.cutWeight2P`, `flowerSumP`. The clauses without
    cutoffs are unchanged (`flowerSumP` agrees with `flowerSum` there by `rfl`).
  - Reason. The v2 max-form is not smooth and does not factor through the regular-object reduction; it
    mis-transcribes TARGET's "smooth cutoff function" (erratum/deviation E34).
  - `layergardenFlower_v2` stays frozen and open (`DRAFT_SORRY`); it is not deleted.
  - Packaging (semantics-neutral): the anchor imports its own provider stub `Provider.LayergardenFlowerV3`
    (quarantined in the lakefile); the audit's docstring fixes F1, F2, F4, F5 are applied. No Lean term differs from
    the audited text.
- Standing authorization — 2026-11-05 — Scott: "I approve all, defer approvals now and just get this done".
  - wt-orch makes the remaining campaign decisions itself, following its recommendations, and records each one here
    or in the orchestrator's RULINGS.md.
  - Frozen-statement changes still follow the versioned-successor and second-key-audit process, and are recorded as
    D-entries.
- D14 — 2026-11-07 ~10:30 — Scott ("I want you to stop the lean development now. I want you to write a report on what
  is problematic about formalizing the paper. What are the gap(s) in the proof? ... I am going to publish this repo
  with a full written report about why the formalization was not successful and an errata+deviations list") —
  **Lean development stopped.**
  - All proof, port and research agents were stopped at about 10:25 UTC. Nothing was landed or sealed after main
    5c6d256c.
  - The deliverables are `docs/FORMALIZATION-REPORT.md` and a publication-ready `docs/ERRATA-AND-DEVIATIONS.md`.
  - Work that existed only in scratch directories at the stop is described in the report and is not claimed as proved.
- D15 — 2026-11-07 ~12:00 — Scott ("let's land layergarden", "please land the layergarden proof and push to origin
  main", then "let's get moving on formalizing the completable sketch of the flower estimate! I want this proved!") —
  **Development restarted.**
  - Batch 4b-3 (the V5 proof closure) landed (68820285), and `layergarden_v2` was sealed.
  - An independent assessment of `flowerest1` (Astra, docs/research/astra-flowerest1-report.md) found the printed
    proof incomplete but completable with the paper's own mechanisms. It judged the formalization's difficulty
    largely architectural.
  - The flower work restarts on its recommended plan:
    1. a complete paper-level supplement first, refereed;
    2. the flower-top reduction ported to main (three named inputs remain);
    3. Lean packets built against the supplement's lemmas.
  - The public report and FLOWEREST1 note are held back and will be revised to match.
- D16 — 2026-11-09 — wt-orch under the standing authorization (Scott, 2026-11-05: "I approve all, defer approvals now
  and just get this done"; and 2026-11-09: "we aim for the full statement", "let's get the full range of gamma"),
  after GAMMA-HALF-SCOPE (R190) and the independent statement audit (gh-core/audits/AUDIT-V4.md: DECLARATION_FIDELITY
  PASS, EXCESS 0, RECOMMEND_FREEZE YES_WITH_FIXES) — **Full-range flower successor `layergardenFlower_v4` frozen; the
  T-vine text pinned**:
  - What changed. `layergardenFlower_v4` is `layergardenFlower_v3` verbatim minus the hypothesis `1 / 2 < P.γ →` (and
    the name, the provider import and the docstring). So it covers the full range 0 < γ < 1 of TARGET Theorem 1.1
    (`WTPrefixP` has `γ ∈ Ioo 0 1`). Its definition closure is v3's (107 sealed definitions). Its statement block is
    v3's after that single substitution (sha256 `4b29cdf4…`), and its type is v3's minus exactly one non-dependent
    hypothesis (`Expr` level, audit §6).
  - `layergardenFlower_v3` stays SEALED and PROVED (1/2 < γ < 1) and is not changed. v4 is a new `DRAFT_SORRY` anchor
    with its own contract and split group (`dh-long.b1.layergardenFlower.v4`). Its proof is to be glued from v3 and a
    γ ≤ 1/2 half (audit §8).
  - The T-vine text (implementing D11(a)). `WaveTurbulence/Foundations/TVine/Defs.lean` is the approved
    `TVineDefs.lean` (sha256 prefix `31242ecfe64dcdab`) with four non-semantic edits: the import path, the module
    title and two documentation paths. No Lean term changes. It is pinned by sha256 (`6f26a370016e607e…`) in
    `manifest/pinned-texts.json`; `scripts/check_pinned_texts.py`, run by `scripts/land_check.sh`, fails the landing
    on any change. It is pinned rather than frozen as an anchor, because no frozen statement mentions T-vines. Any
    change to it needs a versioned successor and a review.
  - The targets of the extension. The v1 anchors `main_v1`, `propansatz_v1`, `fixedpoint_v1` and `layergarden_v1`
    are the full-range targets and are discharged as printed (each is its sealed v2 minus exactly the γ restriction;
    audit §7). `layergardenFlower_v1` and `layergardenFlower_v2` (max-form cutoffs, E34) stay frozen and open.
  - Packaging (semantics-neutral): the anchor imports its own provider stub `Provider.LayergardenFlowerV4`
    (quarantined in the lakefile). The audit's docstring fixes F1–F3 and manifest fixes F4 are applied. No Lean term
    differs from the audited text.
- D17 — 2026-11-09 ~22:40 — the campaign orchestrator under the standing authorization (Scott, 2026-11-05: "I approve
  all, defer approvals now and just get this done"; 2026-11-09: "we aim for the full statement", "let's get the full
  range of gamma", "continue until we're at 100% and all theorems are sealed for the full range of gamma"), following
  rulings R190–R196 — **The full-range statements are sealed**:
  - What was sealed (main `5c19b015`). In one batch, in the order of the proof: `layergardenFlower_v4` (`4558dd65`),
    `layergarden` (`2e2c16ef`), `fixedpoint` (`008e27f9`), `propansatz` (`6f4a03d2`) and `main` (`bfbb5546`), i.e.
    the four originals of D6/D7 as printed, for 0 < γ < 1, and the flower successor of D16. No frozen statement
    changed; each proof body is now a one-line reference to its provider in `WaveTurbulence/Provider/`.
  - The proof. Each provider is a theorem of `WaveTurbulence/Foundations/GammaLow/Close/Final.lean`. It splits γ at
    1/2 (γ = 1/2 in the low half). The high half uses the sealed `layergarden_v2` and `layergardenFlower_v3`. The low
    half uses the closed γ ≤ 1/2 theorems `GammaLow.Close.layergarden_low_closed` and
    `GammaLow.Close.flower_low_closed`, which are built on the enlarged vine family of D11 (erratum E1, repair) and the
    ghost-step repair (erratum E20).
  - What the rulings settled.
    - R190: the target is the full statement. Discharge `main`, `propansatz`, `fixedpoint` and `layergarden` as
      printed, and freeze `layergardenFlower_v4` after an independent statement audit (D16). A partial range would
      need a new decision; it was not needed.
    - R191: all paper-level research for γ ≤ 1/2 was accepted by independent refute-first referees, including the
      ghost step for every 0 < γ < 1.
    - R192: the γ ≤ 1/2 Lean phase starts, with the T-vine text pinned by hash; the removal of unused code is
      deferred until after the seals.
    - R193: the order is the seals, then the dead-code sweep, then public readiness of this repository with its full
      history.
    - R194: in the γ ≤ 1/2 final count, the ghost repair is stated as a bound for the whole run, which uses an
      explicit count at the step that creates a ghost (itself proved). This is an internal interface only; no frozen
      or source statement changes.
    - R195: the five full-range theorems are proved in Lean with standard axioms only, each with exactly the type of
      its frozen statement.
    - R196: seal the five in one batch, keeping every per-statement check (exact type before and after, statement
      drift, axioms, ABI hash) and running the repository-wide checks once at the end. Audit them with two
      independent auditors, each covering all five statements with one kernel replay of their joint dependency
      closure.
  - Checks at the seal. Per statement: exact type equal to the frozen statement; the statement-drift checks; axioms
    `propext`, `Classical.choice`, `Quot.sound` only, with no `sorryAx`; ABI hash written and rechecked. At the end:
    the landing check, the ABI of all 328 frozen declarations, and the frozen-statement guard, all passing.
  - Status: PROVED. Both independent audits passed for all five statements; records in `docs/audits/full-range/`.
  - `layergardenFlower` (v1) and `layergardenFlower_v2` (max-form cutoffs, erratum E34) stay frozen and unproved.
    Nothing depends on them.
