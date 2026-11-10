# Wave turbulence in Lean 4

This repository is a formalization, in the [Lean 4](https://lean-lang.org) proof assistant, of

> Y. Deng and Z. Hani, *Long time justification of wave turbulence theory*,
> [arXiv:2311.10082v2](https://arxiv.org/abs/2311.10082) (2024),

together with the results it relies on from the authors' earlier papers and from the literature (listed under
[Papers](#papers) below). The main result, Theorem 1.1, is formalized for the full range of its scaling exponent,
0 < γ < 1. Every step is checked by Lean; nothing is assumed beyond Lean's standard axioms.

**Authors:** Scott Armstrong and Ahmed Bou-Rabee.

## At a glance

- ✅ **Theorem 1.1 is formally proved for the full range 0 < γ < 1.** The Lean statement (`WaveTurbulence.main`) is
  the printed one for 0 < γ < 1 on the square torus. It was frozen on 2026-11-03, before its proof was written, and
  never changed. The proof was sealed on 2026-11-09 and passed two audits by separate Claude Opus 5.5 sessions that
  had not written it ([records](docs/audits/full-range/README.md)); each audit also replayed the proof in Lean's
  kernel, in quick mode ([details](#how-to-verify)). It depends only on Lean's standard axioms (`propext`,
  `Classical.choice`, `Quot.sound`).
- ✅ **The earlier version for 1/2 < γ < 1** (`main_v2`; sealed on 2026-11-08, audited on 2026-11-09) is also proved.
  The full-range proof uses it for γ > 1/2.
- 🔧 **What it took for γ ≤ 1/2.** There the printed proof has a gap: it relies on a counting proposition (DH23
  Prop 9.6) that is false in that range. The repair enlarges the family of "vines" that the proof splices out,
  re-proves the counting proposition for the enlarged family, and corrects one step of the counting procedure (the
  "ghost" step). **→ [docs/GAMMA-LE-HALF.md](docs/GAMMA-LE-HALF.md)** explains the problem, the repair and where it
  is in Lean.
- 📄 **Errata and deviations.** Formalizing a long proof surfaces mistakes and gaps. Every defect we found in the
  published arguments, and every way our formal statements differ from the printed ones, is recorded with evidence
  and a repair. Every claimed error or gap has been confirmed by a refute-first check in a separate Claude Opus 5.5
  session that had not written the entry ([records](docs/audits/errata/README.md)).
  **→ [docs/ERRATA-AND-DEVIATIONS.md](docs/ERRATA-AND-DEVIATIONS.md)**

## What the theorem says, in brief

Wave turbulence theory predicts that, for a large system of weakly interacting waves, the distribution of energy
across frequencies evolves according to an effective *wave kinetic equation*. Deng and Hani's Theorem 1.1 proves this
rigorously for the cubic nonlinear Schrödinger equation on a large square torus in dimension d ≥ 3, with random
initial data, on long time scales.

### The statement in Lean

This is the frozen Lean statement of Theorem 1.1, verbatim from
[`WaveTurbulence/Frozen/Theorems/Main.lean`](WaveTurbulence/Frozen/Theorems/Main.lean) (namespace `WaveTurbulence`; its
proof follows the `:=`). In words: for every dimension d ≥ 3 and 0 < γ < 1 there is θ > 0 such that, for every
nonnegative Schwartz initial profile `φin`, every τ* > 0 and every solution `φ` of the wave kinetic equation on [0, τ*]
with initial data `φin`, and every large enough L, with α = L^(−γ) and T = τ* · T_kin: on any probability space carrying
independent standard complex Gaussians `g n` (the random initial data), the event F that the cubic NLS has a smooth
solution up to time T is measurable and has probability at least 1 − exp(−(log L)^(40d)); and for every such solution,
every t ∈ [0, T] and every n ∈ ℤ^d, the expectation E[1_F |û(t, n)|²] is within L^(−θ) of φ(t/T_kin, n/L).

```lean
/-- **Deng–Hani, Theorem 1.1** (case `0 < γ < 1`, square torus). -/
theorem main (d : ℕ) (hd : 3 ≤ d) (γ : ℝ) (hγ : γ ∈ Ioo (0 : ℝ) 1) :
    ∃ θ > (0 : ℝ), ∀ φin : 𝓢(Mom d, ℝ), (∀ k, 0 ≤ φin k) →
      ∀ τstar > (0 : ℝ), ∀ φ : ℝ → 𝓢(Mom d, ℝ), IsWKESolution φin τstar φ →
      ∃ L₀ : ℝ, ∀ L ≥ L₀, ∀ α T : ℝ, α = L ^ (-γ) → T = τstar * kineticTime α →
      ∀ (Ω : Type u) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (g : (Fin d → ℤ) → Ω → ℂ),
        (∀ n, Measurable (g n)) → iIndepFun g P → (∀ n, P.map (g n) = stdComplexGaussian) →
        MeasurableSet (solvableEvent L α T φin g) ∧
        1 - Real.exp (-(Real.log L ^ (40 * d))) ≤ P.real (solvableEvent L α T φin g) ∧
        ∀ U : Ω → ℝ → (Fin d → ℝ) → ℂ,
          (∀ ω ∈ solvableEvent L α T φin g,
            IsSmoothNLSSolution L α T (initialCoeff L φin g ω) (U ω)) →
          ∀ t ∈ Icc 0 T, ∀ n : Fin d → ℤ,
            |(∫ ω, (solvableEvent L α T φin g).indicator
                  (fun ω => ‖torusFourierCoeff L (U ω t) n‖ ^ 2) ω ∂P)
              - φ (t / kineticTime α) (latticePoint L n)| ≤ L ^ (-θ) :=
```

### The exponent γ, and the values that matter physically

The theorem involves two limits at once: the side length L of the torus tends to infinity, and the strength α of the
nonlinearity tends to zero. The exponent γ fixes how the two are linked: α = L^(−γ). The time scale on which the
kinetic equation describes the waves, the *kinetic time*, is then T_kin = 1/(2α²) = L^(2γ)/2. For a given box size L,
a smaller γ means a stronger nonlinearity and a shorter kinetic time.

- **Why 0 < γ < 1.** The kinetic description needs the resonance frequencies of the waves to be spread out evenly
  ("equidistributed") at the scale 1/T_kin. On the square torus these frequencies are multiples of 1/L², so they cannot
  be equidistributed at finer scales; this rules out γ ≥ 1. At the other end, γ = 0 (letting L → ∞ before α → 0) is
  not compatible with the continuum setting. Deng and Hani show that every γ in between is admissible, and that
  different values of γ correspond to genuinely different physical and mathematical regimes (DH23, §1.2).
- **γ = 1/2, the "ballistic" scaling law.** Here T_kin is of order L: the kinetic time equals the time a wave packet
  needs to cross the box. Deng and Hani point out that this is the wave analogue of the Boltzmann–Grad scaling used in
  Lanford's theorem for the Boltzmann equation (where the mean free path is equated with the transport length scale),
  and that it is the natural scaling law for spatially inhomogeneous problems. **The formal proof covers this value.**
  It lies in the range 0 < γ ≤ 1/2, where the printed proof needed the repair described in
  [docs/GAMMA-LE-HALF.md](docs/GAMMA-LE-HALF.md).
- **γ = 1, the endpoint.** Here T_kin is of order L², which matches the natural (parabolic) scaling of the Schrödinger
  equation, so results at this scaling translate into statements on a torus of fixed size. In three dimensions this
  connects to the open problem of whether the Gibbs measure (Φ⁴₃) is invariant under the cubic Schrödinger flow, and
  to energy cascades. On the square torus γ = 1 is not admissible. Theorem 1.1 covers it only on rectangular tori with
  generic side lengths, a case this project does not formalize (decision D2 in [docs/DECISIONS.md](docs/DECISIONS.md)).
  **So at γ = 1 our formal result is narrower than the printed Theorem 1.1.** This is listed among the deviations in
  [docs/ERRATA-AND-DEVIATIONS.md](docs/ERRATA-AND-DEVIATIONS.md).
- **γ ≤ 1/2 more broadly.** In this range the equidistribution the theory needs holds for essentially any dispersion
  relation, without number theory (DH23, §1.2). The difficulty we found there is of a different, combinatorial kind,
  and it is repaired (see [docs/GAMMA-LE-HALF.md](docs/GAMMA-LE-HALF.md)).

## How a result counts as "proved" here

1. **The statement is fixed first.** The exact Lean statement of each key theorem is written down and approved before
   its proof exists. It is then frozen (recorded with hashes in [`manifest/frozen.json`](manifest/frozen.json)), so
   the proof cannot quietly change what is being proved.
2. **No gaps.** Proofs contain no `sorry` and no added axioms. Automated checks enforce this on every change.
3. **Sealing.** When the proof is complete, the frozen statement's placeholder is replaced by a one-line reference to
   the proof. Tooling checks that the statement itself is byte-for-byte unchanged.
4. **Two audits.** Two auditors, separate Claude Opus 5.5 sessions that did not write the proof, each work
   separately:
   - re-derive the statement from the paper's source and check that no extra hypotheses were added;
   - check the axioms used;
   - replay the proof in Lean's kernel, in quick mode (see [How to verify](#how-to-verify)).

   The audit records for Theorem 1.1 for the full range are collected in
   [`docs/audits/full-range/`](docs/audits/full-range/README.md); those for the earlier 1/2 < γ < 1 version are in
   [`docs/audits/v2-chain/`](docs/audits/v2-chain/README.md).

## How to verify

You need git and [elan](https://github.com/leanprover/elan), which installs the Lean version pinned in
[`lean-toolchain`](lean-toolchain) (v4.35.0). In a clone of this repository:

```bash
lake exe cache get   # download Mathlib's prebuilt files (Mathlib v4.35.0)
lake build           # build the project: Lean checks every proof
```

`lake build` builds the library `WaveTurbulence`, including the five sealed full-range theorems (`WaveTurbulence.main`
and the four statements it is assembled from), and the two comparator files described [below](#comparator). It
succeeds only if Lean accepts every proof.

**Size.** The repository has 13,355 Lean files with about 1.80 million lines: the library `WaveTurbulence` (11,529
files including its root module, about 1.30 million lines), the certificate library `WaveTurbulenceVineParam`
(1,824 files, about 505,000 lines), and the two comparator files (258 lines).

**What a full build costs.** Even with Mathlib taken from its cache, building the project from scratch is heavy.
Measured in November 2026, before a clean-up removed about 191,000 lines of unused code (1,056 files):
- about 27 CPU-hours on an AMD Ryzen 7 7700 (8 cores, 16 threads);
- one file needs about 11 GB of RAM at its peak;
- the build writes about 73 GB to disk. Most of it is Lake's per-module `*.setup.json` files under `.lake/build/ir/`,
  which are not needed once their module is built and can be deleted as the build proceeds.

So a full build needs a workstation-class machine; it does not fit on a standard CI runner.

**Fast checks (minutes, no build needed; Python 3.9 or later).** These check the bookkeeping that guards the
statements:

```bash
python3 -I scripts/check_frozen_anchors.py --root . --manifest manifest/frozen.json
python3 -I scripts/check_lean_modules.py
python3 -I scripts/check_pinned_texts.py
scripts/check_index.sh
```

- `check_frozen_anchors.py`: every frozen statement and definition is byte-for-byte the approved text (hashes in
  [`manifest/frozen.json`](manifest/frozen.json)), its state is recorded, there is no `sorry` outside the registered
  unproved statements and the comparator Challenge (below), and those statements are imported by nothing else.
  About 2.5 minutes here.
- `check_lean_modules.py`: every Lean file is a Lean module and within the size limit. Under a second.
- `check_pinned_texts.py`: the approved T-vine definitions
  ([`WaveTurbulence/Foundations/TVine/Defs.lean`](WaveTurbulence/Foundations/TVine/Defs.lean)) are byte-for-byte
  the pinned text. Under a second.
- `check_index.sh`: the first two checks, run on exactly the committed tree.

**Kernel replays in the audits.** Each audit of the sealed theorems also replayed the proof in Lean's kernel, in quick
mode: the 40,618 certificate theorems of `WaveTurbulenceVineParam` whose proofs stay inside that library were checked by
statement only (their proofs are kernel-checked by every build), and Mathlib and Lean's core library were taken as the
trusted base. The two replays of the full-range theorems used the same replay tool on the same build, so they are two
runs of one method, not two independent checks. Records: [`docs/audits/full-range/`](docs/audits/full-range/README.md)
(full range) and [`docs/audits/v2-chain/`](docs/audits/v2-chain/README.md) (the earlier 1/2 < γ < 1 version).

*In progress: a full-mode replay, and an independent check of the proof with the NanoDa kernel through the comparator.*

### Comparator

[`WaveTurbulenceChallenge.lean`](WaveTurbulenceChallenge.lean) states Theorem 1.1 in one file of 129 lines that
imports only Mathlib. It repeats, verbatim, the twelve definitions the statement uses (from
[`WaveTurbulence/Frozen/Defs/`](WaveTurbulence/Frozen/Defs)) and the statement of `WaveTurbulence.main`, and leaves
the proof as `sorry`; to check what is proved, it is enough to read this file against the paper.
[`WaveTurbulenceSolution.lean`](WaveTurbulenceSolution.lean) has the same declarations, imports the library and proves
the theorem from `WaveTurbulence.main`. Lean's [comparator](https://github.com/leanprover/comparator), configured by
[`comparator.json`](comparator.json), builds and exports both files in a sandbox, checks that they state the same
theorem about the same definitions and that the Solution uses only the standard axioms, and then replays the
Solution's proof, with everything it depends on (Mathlib included), through Lean's kernel and the independent NanoDa
kernel.

To run it (requires [bubblewrap](https://github.com/containers/bubblewrap)):

```bash
lake exe cache get
lake build
PATH="$(lean --print-prefix)/bin:$PATH" lake comparator   # reads comparator.json
```

The `PATH` prefix makes `lake` and `nanoda_bin` the ones bundled with the pinned toolchain.
[`scripts/verify-comparator.sh`](scripts/verify-comparator.sh) runs the same check with the configuration the Palomar
registry uses, which adds the con-ron kernel. On Ubuntu 24.04, bubblewrap also needs
`sudo sysctl -w kernel.apparmor_restrict_unprivileged_userns=0`.

The comparator exports the Solution together with its whole dependency closure, about 24,200 modules. Reading them
takes about 73,000 memory mappings in one process, more than the Linux kernel's default `vm.max_map_count` of 65,530
(some distributions raise it); below that, the export stops with `failed to read file '….olean.private'`. Check the
limit with `sysctl vm.max_map_count` and, if needed, raise it: `sudo sysctl -w vm.max_map_count=262144`. The export of
the Solution is about 4.4 GB, and producing it takes about 16 GB of memory.

**What has been run.** The comparator's main check (the two files state the same theorem about the same definitions,
and the Solution's proof uses only `propext`, `Classical.choice` and `Quot.sound`) accepted the Solution at commit
`e753c825`, on the machine where the proof was developed. The full kernel replays of the Solution, by Lean's kernel
and by NanoDa, are to be run on a separate machine; their cost and result will be recorded here.

## Current status

- **Proved (sealed and audited):** Theorem 1.1 for the full range 0 < γ < 1, `main`, and the four statements it is
  assembled from: `propansatz`, `fixedpoint`, `layergarden` (all three as printed, for 0 < γ < 1) and the flower
  estimate `layergardenFlower_v4`. Sealed on 2026-11-09 (decision D17); both audits passed for all five
  ([records](docs/audits/full-range/README.md)). How the proof is put together:
  [docs/GAMMA-LE-HALF.md](docs/GAMMA-LE-HALF.md).
- **Sealed and audited:** Theorem 1.1 for 1/2 < γ < 1, `main_v2`, and the theorems it is assembled from
  (`propansatz_v2`, `fixedpoint_v2`, `layergarden_v2` and the flower estimate `layergardenFlower_v3`). The
  full-range proof uses these for γ > 1/2.
- **Sealed:** the other 16 frozen theorems (so 26 of the 28 frozen theorem statements are sealed), and all 300
  frozen definitions.
- **Not proved, by design:** the two original flower statements `layergardenFlower` (v1) and `layergardenFlower_v2`.
  Their cutoffs mis-transcribe the paper's (erratum E34); `layergardenFlower_v3` and `layergardenFlower_v4` replace
  them, and nothing depends on them.

<details><summary>Technical status fields</summary>

```text
DRAFT_ANCHORS: 2 theorem anchors at DRAFT_SORRY (the superseded flower statements layergardenFlower v1 and
               layergardenFlower_v2; erratum E34)
UNREGISTERED_SORRIES: 0 (frozen-anchor guard OK)
DRAFT_IMPORT_VIOLATIONS: 0
SEALED: 26 theorems + 300 definitions. Full range: main, propansatz, fixedpoint, layergarden, layergardenFlower_v4
        sealed 2026-11-09 (main 5c19b015), PROVED with two-key audits. 1/2 < γ < 1: main_v2 PROVED (two-key audits).
```
</details>

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

- [docs/GAMMA-LE-HALF.md](docs/GAMMA-LE-HALF.md): the range 0 < γ ≤ 1/2, what goes wrong in the printed proof, the
  repair, and where it is in Lean.
- [docs/ERRATA-AND-DEVIATIONS.md](docs/ERRATA-AND-DEVIATIONS.md): errata in the published arguments and deviations of
  the formal statements.
- [docs/audits/full-range/](docs/audits/full-range/README.md): the two-key seal audits of Theorem 1.1 for the full
  range 0 < γ < 1 and its chain.
- [docs/audits/v2-chain/](docs/audits/v2-chain/README.md): the two-key seal audits of Theorem 1.1 for 1/2 < γ < 1 and
  its chain.
- [docs/audits/errata/](docs/audits/errata/README.md): the independent verification of the errata (2026-11-10).
- [docs/research/](docs/research/INDEX.md): research notes, referee reports and scripts behind the errata.
- [docs/DECISIONS.md](docs/DECISIONS.md): the author's decisions (scope, statement versions, approvals).
- [docs/review/](docs/review/README.md): the approval pages behind these decisions (dated records).
- [docs/FINDINGS.md](docs/FINDINGS.md): the running ledger of source findings.
- [docs/THIRD-PARTY.md](docs/THIRD-PARTY.md): third-party code (Apache 2.0, attributed).

## How this was made

The Lean code was written by AI coding agents under the supervision of the authors, between 3 and 10 November 2026.
Claude Opus 5.5 directed the work, coordinated the other agents and wrote the hardest parts; Claude Sonnet 5.5 and
GPT-6.1 (sol, through Codex) wrote large parts of the code. The research notes behind the repairs, their referee
reports, the statement audits, the seal audits and the check of the errata were also written by AI models, mainly
Claude Opus 5.5; GPT-6 (astra) wrote an independent assessment of the printed flower estimate. Each review was done
by a session that had not written what it checked. In this repository, "independent" refers to such separate
sessions, not to human referees.

Scott Armstrong set the scope and approved the frozen statements of the main results, including Theorem 1.1
([DECISIONS.md](docs/DECISIONS.md), D1, D2 and D6–D11). Later, under his standing authorization of 5 November 2026,
the coordinating agent approved two successor statements, each after an independent statement audit (D13, D16), and
sealed the full-range theorems after two seal audits (D17). Lean's kernel checks every proof against the frozen
statements, and the comparator files let anyone check the statement of Theorem 1.1 independently.

## License

This repository is released under the Apache License 2.0; see [`LICENSE`](LICENSE). Third-party code that it includes
is listed, with its license and attribution, in [`docs/THIRD-PARTY.md`](docs/THIRD-PARTY.md).

## Citation

Citation metadata for this formalization is in [`CITATION.cff`](CITATION.cff). Please also cite the paper it
formalizes: Y. Deng and Z. Hani, *Long time justification of wave turbulence theory*,
[arXiv:2311.10082](https://arxiv.org/abs/2311.10082).
