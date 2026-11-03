# Packet WAVEB-DRAFT — exact Lean drafts of the Wave B (tier B1) definitions and statements

Read `COMMON.md` (same directory) first. This packet produces **drafts for author approval**, not landed code:
per the campaign's statement discipline, candidate source-facing declarations are never committed. Work in
**untracked** files under `/home/scott/wt-scratch/waveb/` (create it), elaborated from your worktree
`/home/scott/WaveTurbulence-worktrees/gauss-hc` with `nice -n 5 lake env lean /home/scott/wt-scratch/waveb/<File>.lean`
(they may import the frozen Wave A definitions and landed Foundations modules). Commit nothing to the repo in this
packet except, if useful, sorry-free *infrastructure lemmas* under new files in `WaveTurbulence/Foundations/Comb/**`
on a new branch `w/waveb-infra` (`git switch -c w/waveb-infra main`) — never a source-facing definition.

## Inputs

- The proposal `/home/scott/WaveTurbulence-dev/docs/blueprint/WAVE-B.md` (§0–§2 definitions, §4.1–§4.10 statements,
  §5 junk-value checklist, §6 open items) and `GRAPH.md`. Treat them as a careful but unaudited proposal: check every
  item against the TeX (`/home/scott/wave-turbulence/paper/source/WKE-Longer_times_Final_arXiv.tex`, and DH21/DH23/
  DH21-2 under `/home/scott/wave-turbulence/references/`) and record every disagreement.
- Frozen Wave A: `WaveTurbulence/Frozen/Defs/*` (namespace `WaveTurbulence`), statements `main`, `wkelwp` (D6).
- Landed infrastructure you may build on: `Foundations/Torus/**`, `Foundations/Gaussian/**`. The cumulant definition is
  being built by wt-cumul (`cumulant` in its DRAFT form in `docs/campaign/briefs/CUMUL.md`); use that exact body.
- FINDINGS F5 (constant hierarchy), F7/F27 (time parameter), F9 (conjugated leaves), F30 (propertycm ranges), F35
  (incomparable nodes), F36 (deterministic `layergarden`).

## Rules for the drafts

- Every definition must mean the source object on its whole carrier: no fallback/junk branches, no arbitrary
  choices, no `Classical.choose` from mere existence. Where the source defines something only implicitly, say so and
  propose the reading. `tsum`/`finsum`/Bochner integrals must come with a summability/finiteness/integrability lemma
  in the probe file (otherwise junk 0 can make a statement vacuous or false): WAVE-B §5.
- Constants: implement the parameter prefix (Π) of WAVE-B §1.2 exactly (check it against TARGET L605–L615 and the
  inductive scheme L685–L707); one reusable `structure` or a fixed quantifier prefix — your choice, argued in the memo.
- Keep `Fin d → ℤ` lattice indices and `Mom d` momentum vectors as in Wave A.
- Prefer simple, standard carriers that later proofs can work with (the D1 COMB-CORE packet and ~170 graph nodes depend
  on the tree/garden API); write a short design memo comparing at least two carrier choices for trees and gardens and
  justify yours.
- Each file must elaborate with no errors; theorem statements end in `:= by sorry` (drafts only); add sorry-free
  **non-vacuity probes** (e.g. small explicit trees/gardens/couples satisfy the predicates; the canonical-garden
  predicate holds for an explicit example from TARGET Fig. `CanonGarden.png`; K_G of the trivial couple equals F(k);
  the order-n sums are finite sums).

## Stages (report after each with `READY waveb-stage<k>` and then continue to the next unless told otherwise)

1. **Core carriers** (WAVE-B §2.1–§2.2): parameters, ternary trees, gardens/couples/irreducibility, decorations (lattice
   and coset versions), ε, Ω, layerings, canonical layered gardens (criterion form + the remark on incomparable nodes),
   truncation. File `WaveB1-Core.lean` + `WaveB1-Core-probes.lean` + `DESIGN.md`.
2. **System objects** (§2.3–§2.6): the a-system nonlinearity and solution class, symmetric events, K_G / K*_Q / K*_T,
   order-n sums, Duhamel tree terms 𝒥_𝒯, ℒ_0..ℒ_3, Z space, norms 𝔖/𝔛/restriction norms/Z^Λ, χ_0, WKE Taylor terms,
   ansatz predicate. File `WaveB1-System.lean` + probes.
3. **Statements** §4.1–§4.10 (`propansatz` with time parameter, `layergarden` deterministic with time parameter,
   `fixedpoint`, `nlsAkBridge`, `wkeTaylor`, `sumint`, `countLemma`, `atomCountLemma`, `quadExpSum2`, `quadExpSum3`),
   each with its source lines in the docstring and a list of deviations. File `WaveB1-Statements.lean`.

After each stage the orchestrator will have wt-orch audit it; you continue with the next stage meanwhile and fold in
audit fixes when they arrive.

## Stop conditions
Blocked on a genuine source ambiguity that changes a statement: write it into `DESIGN.md` §Questions with your
recommended reading, take that reading, and continue. Print `STOPPED waveb: <reason>` only if you cannot proceed at all.
