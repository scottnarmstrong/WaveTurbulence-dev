# Referee report: γ ≤ 1/2 repair route (`research-gamma-half/NOTES.md`)

- **Who:** an independent refute-first referee (subagent), 2026-11-04. Transcribed by wt-orch from the referee's final
  message, because the referee's harness blocked report files.
- **Scripts and outputs:** in this directory. Pinned inputs are in `pinned/`, with hashes in `PINNED_SHA256.txt`;
  re-runs are in `rerun/`.

## Overall verdict

**The repair route is sound.**
- No counterexample was found, and nothing breaks the route.
- The analytic core is CONFIRMED. T-vines meet the hypotheses of DH23 `sumintest2`/`sumintest3` and TARGET `sumint`
  literally, with no new estimate.
- The combinatorial extensions are confirmed on all finite data up to 19 atoms. Beyond that they are heuristic.
- The note contains overstated or false side statements (E1–E5), and parts of claim 5 remain unverified.

## Verdict by claim

| # | Claim | Label |
|---|---|---|
| 1 | Theorem N: T-vines meet `sumintest2`/`sumintest3`/`sumint` with no new estimate ("Prop 7.6′") | **CONFIRMED.** Re-derived, plus an independent literal check of every hypothesis, including the integrality/unimodularity conditions. |
| 1′ | A "cosmetic generalization" is needed | **REFUTED as a need** (E4): not needed. |
| 2 | Lemmas C and D | **CONFIRMED.** The note's coordinate-free factorization argument is REFUTED (E3); the conclusion survives by DH23's own route. |
| 3 | The 4446 classes up to 15 atoms are exactly neutral | **CONFIRMED.** Re-run, and checked with independent code. |
| 4a | Infinite families, analytic piece data, via rung-locality | **CONFIRMED** as a sketch, which the referee re-derived. |
| 4b | Infinite families, combinatorial facts "PROVED" | **REFUTED as labelled** (E1): heuristic beyond 19 atoms. |
| 5 | Lemma 8.1′, `subsetvc`′, Props 9.1 and 9.5′, Step-1 deviation, case (4)′ of 9.6; TARGET `cohmol`, `layervine`, `subpro`, `finalmol`, `lgmolect` | **CONFIRMED** in logic and on all finite data up to 19 atoms. One side claim is false (E2). |
| 5′ | TARGET with R ≥ 2 gardens; DH23 Sec 11 / TARGET Sec 12 (flower trees, parametrix); Prop 9.6 case (5) via Prop 10.4(1) for T∖ℓ | **UNVERIFIED** |
| 6 | Q1: necklace size ≈ (Cδ^{1/2})ⁿ L^{−γ(2d−1)} | **CONFIRMED** as arithmetic. **UNVERIFIED** as asymptotics, which rest on F73 (a CANDIDATE). Caveats in E5. |

## "Exactly neutral" is the right notion

DH23 `red1step` (L1653) needs a loss of at most L^{η⁴} per normal vine-chain unit. The proof of `kqmainest2` from
`lgmolect` (L1823–L1826) pays for each unit with one cut at its hinge atom. TARGET does the same:
- L^{+η⁷ q_sk} in (redvine2), L1962;
- paid for by L^{−η⁶(ρ_sb + q_sk)} in (finalsbest2), L2078.

DH23's own normal vines are also only neutral up to L^{η⁴}. A spliced T-chain is consumed in exactly the same way.

## Errors in the note

- **E1 (overstated label).** The combinatorial finite facts are checked to 13 atoms by the note and to 19 by the referee.
  Beyond that they are heuristic, not "PROVED". §2.5 covers only the analytic piece data.
- **E2 (false side claim, harmless).** The note says a union of two σ = 1 vines sharing both joints "has its joints of
  degree 3, so it is the whole molecule". This is false.
  - Counterexample: two copies of the 5-atom σ = 1 T-vine glued along the bond 3→4, plus a degree-2 atom ρ with
    3→ρ→4.
  - Lemma 8.1's uniqueness proof does not use the claim, so the sentence should be deleted.
- **E3 (flawed argument; the conclusion survives).** The note's "Poisson summation in the original bond variables,
  Lemma C coordinate-free" does not factorize. Lemma D's splitting is not orthogonal, and its conditioning is not uniform
  along long ladders. The valid route is DH23 `sumintest1` Step 1 / TARGET `sumint` Step 1: change to piece variables
  and use product cutoffs. That route needs conditions (i)–(iii), which hold (see the checks below).
- **E4 (in the note's favour).** Rung ζ_j and core ξ always involve only the piece's own variables and r, with
  coefficients in {0, ±1}. Only intermediate-joint coefficients involve other units, and DH23 Cor `sumintest3` (L1374)
  already allows those. So no generalization of the estimate is needed.
- **E5 (minor).** The Q1 headline drops a fixed factor δ^{1/2−d}, and it holds only for m ≥ d/2.

## Old caveats that apply equally to the drawn vines

- **C1 (F79).** The core form holds only up to sign. Cases with no sign-consistent exact form:
  - (III): 136/420;
  - (IV): 74/148;
  - (V): 56/112;
  - (VII): 90/180;
  - (VIII): 160/320;
  - new T-vines: 934/1992.

  The bounds are blind to the sign (`lemcubic0` holds for both signs; A.2(3) allows an arbitrary β).
- **C2.** DH23 `sumintest1`/`sumintest2` assume |r| ≲ L^{−γ−η} (L1280, L1352), but they are applied with
  |r| ≤ L^{−γ+η}. This is harmless for γ ≤ 1/2.
- **C3.** The entries of T₁^{−1} lie in {0, ±1, ±2}, which is enough for DH23's "≲ 1". TARGET's literal "0 or ±1" is
  UNVERIFIED, for the drawn vines as well.

## Checks run

- **Literal hypothesis check (`refcheck.py`, new code).** Covers the pieces, the joint, the rung forms, ζ ≠ 0, the core
  forms, unimodularity, and TARGET (i) for T₁ and T₂.
  - Up to 15 atoms: 8892/8892 pass.
  - At 17 atoms: 14928/14928 pass.
  - Core form counts: u₁·u₃ in 4774 + 7920 cases; u₃·(u₁+u₂−u₃) in 4118 + 7008 cases.
- **Chains (`chaincheck*.py`, `chain_fail_probe.py`).**
  - Necklace bead runs: 60/60 pass.
  - Random mixed chains: 800 cases, of which 796 pass on the first search. The other 4 pass after a random-restart
    search.
- **Sub-objects (`subcheck.py`, `straddle.py`).** 30718 containers up to 19 atoms:
  - 0 failures of the `disjointlem` hypotheses;
  - sub-object gaps are always free;
  - connectivity survives removal of any one sub-object or any disjoint pair;
  - no sub-object uses a container joint.
- **Step-1 deviation, re-derived.** 𝔇 ≲ R^d L^γ (log L)^C, within the requirement.
- **Prop 9.6 case (4)′.** Confirmed, including the Step-2 β-atom case with gap ±r₁ ± r₂, which the note does not discuss.
- **`layervine` structure.**
  - 2596 cases have "no pendant";
  - 6296 cases have "ladder + (D)".
- **Twists, LF twists, `molecpl`:** unaffected.

## Still to be written or checked

1. **The vine family depends on γ:** enlarged for γ ≤ 1/2, original for γ > 1/2. Every statement about "vines" must name
   its family, or Prop 7.6 Step 2 must be redone for T-vines.
2. **A written proof of rung-locality** for the combinatorial facts.
3. **Unchecked sections:**
   - TARGET with R ≥ 2 gardens;
   - DH23 Sec 11 / TARGET Sec 12;
   - Prop 10.4(1) for T∖ℓ;
   - the explicit list for ylem1′.
4. **C1–C3,** which are old issues.
5. **Corrections E1–E5** in the note.
