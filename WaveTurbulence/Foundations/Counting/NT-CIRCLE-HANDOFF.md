# NT-CIRCLE handoff — 2026-11-03

Status: blocked by a verified failure of the proposed exponent substitution.
The circle problem, annulus lattice count, and `estcross` have **not** been proved.
The committed Lean results concern numerical expressions only. They neither
assume nor supply a lattice-counting theorem.

## Files

- `WaveTurbulence/Foundations/Counting/ExponentAudit.lean`: eight proved numerical audit results, 147 lines.
- This handoff. No root, frozen file, shared API, manifest, or findings-ledger edits.

All source locations below refer to the local pinned DH23
`/home/scott/wave-turbulence/references/src-2301.07063/Revision_Submit.tex`.
The relevant displayed calculation is L2082 (the brief's line range is approximate).

## Main obstruction and suspected source erratum

DH23 L2029 gives a minimum of **two branches**, the second containing a sum of
three positive terms. After rescaling at gamma = 4/5 and replacing 7/11 by 2/3,
the numerical expression is

    F(L,Q) = min(L^(2/5) + Q^(2/3),
                 L^(1/5) + L^(8/5)/Q + L^(6/5)/Q^(1/3)).

At Q = L^(6/5), exactly

    F(L,Q) = L^(2/5) + L^(4/5).

This is an admissible annulus regime: Q*rho = L^(2/5), hence
rho = L^(-4/5), and Q^(-1) <= rho <= Q for L >= 1 (with asymptotic
separation for large L).

Lean proves that for every epsilon > 0 and every real C there exists L >= 1
with F(L,L^(6/5)) > C*L^(4/5-epsilon). Thus constants cannot turn this
expression into the required strict power saving. This does not assert that
actual lattice counts attain F, or that the source theorem is false.

The candidate source error is L2082, quoted:

    min(L^{2/5}+Q^{7/11}, L^{1/5}+L^{8/5}Q^{-1}, L^{6/5}Q^{-1/3}).

The comma before the last term should apparently be a plus when deducing
this expression from L2029. Bounds by B+C do not imply separate bounds by
B and C. Keeping the correct sum, the original 7/11 exponent still works:
split Q at L^(99/80). Below the split, Q^(7/11) <= L^(63/80); above it,
L^(8/5)/Q <= L^(29/80) and L^(6/5)/Q^(1/3) <= L^(63/80).
The remaining powers 2/5 and 1/5 are smaller, and
63/80 = 0.7875 < 4/5 - 1/10000. Hence this candidate typo does not invalidate
the original argument with its stated discrepancy input.

In contrast, F3's proposed 16/25 exponent comes from using the incorrectly
split three-entry minimum. Balancing Q^(2/3) with L^(8/5)/Q gives
Q = L^(24/25), but the omitted last summand then equals L^(22/25).
The orchestrator should reconsider F3; this worker has not edited that ledger.

A second candidate source typo is L2077, quoted: "with rho ~ L^{2-2gamma}".
The displayed rescaled expression corresponds to **Q*rho** ~ L^{2-2gamma},
where rho denotes the geometric radial width in L2029.

## Calculations for every annulus use in L2076–L2117

Write gamma = g, Q = L^q, L >= 1, and set a = (4-2g)/3.
For g >= 1/2 the two-branch expression with exponent 2/3 is bounded by
3*L^a, uniformly in Q > 0:

- If Q <= L^(2-g), use the first branch. Both 2-2g <= a and
  (2/3)(2-g) = a.
- If Q >= L^(2-g), use the second branch. Its three exponents are at most
  1-g, 2-2g, and a, all at most a.

This exponent is sharp for the numerical expression: at q = 2-g the largest
power in each branch is exactly a. The saved power relative to L is

    s = 1-a = (2g-1)/3.

**`basiccount0` (1), L2076–L2079.** The circle-dependent xi=x+y case has
L^(d+1-2g+O(eta)) choices for xi, and L^(d-2)*3*L^a choices for x.
The product is O(L^(2(d-g)-s+O(eta))). Thus it gives L^(-10eta) if eta
is sufficiently small relative to g-1/2, after absorbing the source's
unspecified O(eta) losses. The xi=x case uses `estcross`, so its proof does
not use the circle discrepancy exponent.

**`basiccount0` (2), L2081–L2086.** The same multiplication yields exponent
2d-1-2g+a+O(eta). The desired exponent is 2d-g-1-20eta. Even ignoring the
additional O(eta) losses, comparison requires

    a <= g-20eta  iff  g >= 4/5 + 12eta.

The source permits g > 4/5-10eta. In particular g=4/5 is permitted for any
positive eta, and the verified critical-value obstruction applies there.
This is the blocking use. The xi=x case is unchanged by the discrepancy
substitution, but does not resolve xi=x+y.

**`basiccount0` (3), L2088–L2091.** The zeta=x+y-v and x+y-v-z cases multiply
the L^(2(d-g)) choices already made by L^(d-2+a). For g>1/2, gamma0=1-g,
so this is O(L^(3(d-g)-gamma0-s)), giving the required L^(-10eta) when eta
is sufficiently small. The last case (called xi=x-v in the source proof)
uses `estcross`, with no change to that input.

**`basiccount` (5), L2117.** Set gamma0=min(g,1-g). The small-M area argument
does not use the discrepancy exponent. In the large-M case,
M >= L^(1-gamma0/10), Q=LM >= L^(2-gamma0/10), and Q*rho ~ L^(2-2g).
The geometric branch alone has exponents at most

    1-g,   2-3g+gamma0/10,   4/3-g+gamma0/30.

For 0<g<1 each is <= max(1,2-2g)-gamma0/10. The Lean result proves this
inequality (indeed under the weaker typing assumption 0 <= g). This use
survives independently of the circle discrepancy branch.

These are exponent calculations, not Lean proofs of the source counts.

## Exact proved statements and trust

All names are in namespace `WaveTurbulence.Counting`; their complete exact
Lean statements and proofs are in `ExponentAudit.lean`:

1. `annulus_two_thirds_critical_value`: the exact F(L,L^(6/5)) identity for every L>0.
2. `annulus_two_thirds_not_uniform_subpower`: the forall epsilon>0, forall C,
   exists L>=1 strict inequality described above.
3. `annulus_two_thirds_gain`: 1-(4-2g)/3=(2g-1)/3.
4. `annulus_two_thirds_exponent_le`: the uniform upper bound on the min/max
   of the two branches' exponents, for g>=1/2 and arbitrary real q.
5. `annulus_two_thirds_exponent_critical`: equality at q=2-g.
6. `annulus_seven_elevenths_exponent_le`: the correctly summed original
   expression's exponent is at most 63/80 at g=4/5, for arbitrary q.
7. `annulus_large_radius_exponent_le`: the three exponent comparisons for (5).
8. `annulus_two_thirds_target_exponent`: the exact iff g>=4/5+12eta above.

`#print axioms` reports exactly `[propext, Classical.choice, Quot.sound]` for
each of these eight results. No custom axioms or placeholders.

## Searches, checks, and output

Read NT-CIRCLE.md, COMMON.md, AGENTS.md, campaign PLAN, DECISIONS, and FINDINGS;
read the pinned DH23 counting statements and proofs in full for the cited uses.
Followed the Lean workflow/search/proof/naming skills. The repository's Euclidean
carrier convention takes precedence over the generic analysis skill; this audit
needs only real scalar arithmetic.

Searched Mathlib NumberTheory/Analysis for van der Corput, circle problem,
Sierpinski, exponential sums, and lattice-point estimates. Searched local
`/home/scott/KAM-dev` and `/home/scott/Balaban`, then shallow-cloned
`scottnarmstrong/eth-constants` and `scottnarmstrong/Frohlich-Spencer` into
`/home/scott/wt-scratch/nt-circle/` and searched their Lean sources.
No circle discrepancy or oscillatory second-derivative estimate was found.
KAM's `Fourier/ExpSums.lean` bounds absolutely decaying real exponentials;
Frohlich-Spencer's lattice balls bound counts by enclosing cubes. Neither
supplies the first packet goal. Frohlich-Spencer has Schwartz Poisson summation
infrastructure that may be relevant to a future analytic proof.

Exact successful checks (run from this worktree, through wt-throttled):

    nice -n 5 lake env lean /home/scott/wt-scratch/nt-circle/ExponentAudit.lean
    # exit 0, no Lean output or warnings

    nice -n 5 lake build WaveTurbulence.Foundations.Counting.ExponentAudit
    # ✔ [2075/2075] Built WaveTurbulence.Foundations.Counting.ExponentAudit (4.5s)
    # Build completed successfully (2075 jobs).

Only the one project module was built; the dependency jobs were cached.
No Mathlib build, whole-library build, cache deletion, or toolchain change.

    nice -n 5 lake env lean /home/scott/wt-scratch/nt-circle/Axioms.lean
    # exit 0; eight axiom reports, each [propext, Classical.choice, Quot.sound]

    git diff --check
    # exit 0, no output

    rg -n '\b(sorry|axiom|admit|unsafe|opaque)\b|set_option' WaveTurbulence/Foundations/Counting/ExponentAudit.lean
    # exit 1, no matches

An initial scratch compile failed because `tendsto_rpow_atTop` was incorrectly
qualified `Real.`; this was corrected before all checks above.

## Uncertainties, deviations, and proposed route

The proposed substitution fails to recover one required use; it does not show
that the circle bound or source counting statement is false. No work has been
claimed toward proving the circle discrepancy, the geometric annulus count, or
`estcross`. The deviation from the packet's proof order is this numerical audit
and blocked handoff, justified by the explicit requirement to check whether the
weaker exponent suffices. No source hypotheses have been changed.

Proposed routes for the orchestrator:

- Obtain a uniform circle discrepancy bound with an exponent strictly below
  2/3 and enough margin for the requested saving, proving that input in Lean.
  Balancing the circle term Q^alpha with L^(6/5)Q^(-1/3) at g=4/5 gives
  exponent (6/5)*alpha/(alpha+1/3), which is <4/5 precisely for alpha<2/3
  when alpha>0. The existing 7/11 gives 63/80. To meet the displayed fixed
  saving 1/10000 this balance needs alpha <= 7999/12003, before eta losses.
- Alternatively, prove a stronger local annulus count or exploit additional
  constraints in the xi=x+y counting problem. The two bounds stated in this
  packet alone do not supply the missing strict gain.
- Changing source thresholds would require an owner ruling and downstream
  campaign analysis; this worker has made no such change.

STOPPED nt-circle: the 2/3 substitution does not supply basiccount0 (2); the numerical obstruction is proved in Lean.
