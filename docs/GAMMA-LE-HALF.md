# The range 0 < γ ≤ 1/2: what goes wrong, and how we plan to fix it

*Status: **work in progress.** This page explains why our formal proof of Theorem 1.1 currently covers only
1/2 < γ < 1, and what remains to be done for 0 < γ ≤ 1/2. Last revised 2026-11-09.*

## In short

- The target paper, Deng–Hani, *Long time justification of wave turbulence theory* (arXiv:2311.10082), states its
  main result, Theorem 1.1, for every scaling exponent 0 < γ < 1.
- Our Lean formalization **proves Theorem 1.1 for 1/2 < γ < 1**. The statement is frozen, sealed and independently
  audited (see the [README](../README.md)).
- For **0 < γ ≤ 1/2**, the printed proof does not go through. It relies on a counting estimate from the companion
  paper DH23 (Deng–Hani, *Derivation of the wave kinetic equation: full range of scaling laws*, arXiv:2301.07063),
  **Proposition 9.6**, and one case of that proposition is false in this range.
- **This is a gap in the proof, not a counterexample to the theorem.** Nobody has found a counterexample to Theorem 1.1
  for any γ, and we believe the theorem is true. We have a repair strategy, most of which is already checked on
  paper. Its last open research step now has a proposed solution under independent refereeing. The Lean work for
  this range has not started.

## What goes wrong

The proof bounds sums over large combinatorial objects, *molecules*, which encode the terms of the solution's
expansion. A key step (DH23 Prop 9.6) bounds the "final components" left after a reduction procedure. Its case (4)
claims that a certain kind of component must be a *vine*, a special structure whose sums are already controlled
elsewhere in the paper.

That claim is false: there are small components of this kind that are **not** vines. The smallest are a 4-atom
block, three 5-atom blocks, five 7-atom blocks and a 9-atom block. They repeat in an explicit infinite family
("necklaces"). For γ > 1/2 the paper's exponents leave enough room to absorb these components anyway: we found and
had refereed a new argument for that range, and it is now part of the Lean proof. **For γ ≤ 1/2 there is no such
room**, so the estimate of Prop 9.6 fails, and with it a few statements that rely on it (DH23 `kqmainest2`, the
target paper's `lgmolect` and its first final-count estimate).

Full technical details, with exact line references and a refereed counterexample, are in erratum **E1** of
[ERRATA-AND-DEVIATIONS.md](ERRATA-AND-DEVIATIONS.md#e1--dh23-prop-96-lgmolect-case-4-is-false-for-0--γ--12).
The same erratum file records every other defect we found, and every way our formal statements differ from the
printed ones.

## The repair strategy

**Idea.** The offending blocks behave like vines in the ways that matter. So we enlarge the family of vines to
include them, as *T-vines*. With this enlarged family the paper's vine machinery bounds them, and the remaining
components satisfy a corrected Prop 9.6.

**Where it stands:**

| Part of the repair | Status |
|---|---|
| Definition of the enlarged vine family (T-vines) | three research notes, **three independent referee rounds passed**; exact Lean definitions written and independently reviewed; adopted |
| The vine estimates for T-vines (the paper's Prop 9.4 and its parametrization) | proved on paper and refereed for blocks up to 17 atoms; an all-size write-up is in progress |
| Prop 9.6 and the related counting statements, re-proved for γ ≤ 1/2 with T-vines | proved on paper (2026-11-09), **referee in progress**; depends on the ghost step below |
| The "flower" estimate (a separate part of the proof) re-checked for γ ≤ 1/2 | done (2026-11-09): all 75 places that use γ > 1/2 checked, none fails, 13 needed a different justification; **refereed: accepted with minor (editorial) repairs** |
| **The "ghost" step of the counting procedure** (erratum **E20**) | **a proposed resolution for all 0 < γ < 1 (2026-11-09) is under independent refereeing**; until it passes, this step counts as open |

**The open step.** The counting procedure removes pieces of a molecule one at a time and keeps an exact tally of
the gains and losses. In one configuration two already-removed pieces ("ghosts") meet at a triangle. For γ > 1/2
the tally closes with room to spare, and our Lean proof for that range handles it. For γ ≤ 1/2 the tally as
written comes out short.

We tried three research approaches in parallel. One of them (2026-11-09) proposes a resolution valid for every
0 < γ < 1. It shows that the problematic configuration is never one the procedure has to charge, because of momentum
conservation, and it re-routes the remaining small deficit to a step that has room for it. The proposal is now being
checked by independent referees who try to refute it. **Until it passes, we treat this step as open.**

## The plan

1. **Paper-level research (now).** Referee the proposed ghost-step resolution and the re-proved counting statements.
   Every result goes to an independent, refute-first referee before we rely on it.
2. **Lean formalization.** Roughly 100–180 thousand new or modified lines, in about ten work packages. Much of the
   existing proof for 1/2 < γ < 1 carries over unchanged, since only a small part of it actually uses γ > 1/2. The
   main new pieces are:
   - the T-vine combinatorics, with a compact verified checker in place of a large generated catalogue;
   - the counting estimates for γ ≤ 1/2;
   - the flower estimate for γ ≤ 1/2.
3. **Sealing.** We then prove the original, full-range frozen statements as printed: the main theorem `main` and its
   intermediate theorems `propansatz`, `fixedpoint` and `layergarden`. We also prove one new full-range version of
   the flower estimate. Each goes through the same two-key independent audit as the 1/2 < γ < 1 result.

We will update this page as the research steps are refereed. If the ghost step can only be closed on part of the
range, we will say so here and state exactly what is proved.
