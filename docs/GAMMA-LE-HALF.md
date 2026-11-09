# The range 0 < γ ≤ 1/2: what goes wrong, and how we plan to fix it

*Status: **work in progress**: the mathematics is complete on paper; the Lean formalization has not started. This page explains why our formal proof of Theorem 1.1 currently covers only
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
  for any γ, and we believe the theorem is true. We have a repair whose every step is now proved on paper
  and checked by independent referees (2026-11-09). What remains is the Lean formalization for this range, which has
  not started yet.

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
| The vine estimates for T-vines (the paper's Prop 9.4 and its parametrization) | proved on paper for blocks of every size (2026-11-09); **refereed: accepted with minor repairs** |
| Prop 9.6 and the related counting statements, re-proved for γ ≤ 1/2 with T-vines | proved on paper (2026-11-09); **refereed: accepted with textual repairs** |
| The "flower" estimate (a separate part of the proof) re-checked for γ ≤ 1/2 | done (2026-11-09): all 75 places that use γ > 1/2 checked, none fails, 13 needed a different justification; **refereed: accepted with minor (editorial) repairs** |
| **The "ghost" step of the counting procedure** (erratum **E20**) | **resolved for all 0 < γ < 1** (2026-11-09); refereed, and confirmed independently by two other approaches |

**The ghost step, formerly open.** The counting procedure removes pieces of a molecule one at a time and keeps an
exact tally of the gains and losses. In one configuration two already-removed pieces ("ghosts") meet at a triangle.
For γ > 1/2 the tally closes with room to spare. For γ ≤ 1/2 the tally as written came out short.

The resolution (2026-11-09) rests on two observations:
- Because of momentum conservation, the problematic configuration is never one the procedure has to charge.
- The remaining small deficit can be paid for at an earlier step that has room for it.

The argument works for every 0 < γ < 1. An independent referee tried to refute it and confirmed it with minor
repairs, and two separate research approaches reached the same conclusion by different routes.

## The plan

1. **Paper-level research: done (2026-11-09).** Every step has passed an independent, refute-first referee. The
   referees' small repairs are being folded into the notes.
2. **Lean formalization (next).** Roughly 100–180 thousand new or modified lines, in about ten work packages. Much of the
   existing proof for 1/2 < γ < 1 carries over unchanged, since only a small part of it actually uses γ > 1/2. The
   main new pieces are:
   - the T-vine combinatorics, with a compact verified checker in place of a large generated catalogue;
   - the counting estimates for γ ≤ 1/2;
   - the flower estimate for γ ≤ 1/2.
3. **Sealing.** We then prove the original, full-range frozen statements as printed: the main theorem `main` and its
   intermediate theorems `propansatz`, `fixedpoint` and `layergarden`. We also prove one new full-range version of
   the flower estimate. Each goes through the same two-key independent audit as the 1/2 < γ < 1 result.

We will update this page as the Lean formalization of this range progresses.
