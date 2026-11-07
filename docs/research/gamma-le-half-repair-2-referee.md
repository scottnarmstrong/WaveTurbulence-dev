# Referee report 2: does research note 2 close the γ ≤ 1/2 gaps?

The report is by an independent, refute-first referee (subagent), 2026-11-05. wt-orch transcribed it from the
referee's final message, because the harness refused the file write. All scripts and outputs are in this directory,
and `SHA256SUMS` covers every file except this report.

## Overall verdict

**Not all six items are closed soundly as written, but the repair route still stands.** No new obstruction was found.

| Item | Verdict |
|---|---|
| 2, 3, 4, 5 | Closed: CONFIRMED, with minor imprecisions |
| 1 | Closed only after two repairs: Theorem 1.15 is CONFIRMED, but two supporting claims are false as stated (R1, R2) |
| 6 | Not closed for all sizes: still a sketch; UNVERIFIED in general, CHECKED independently up to 21 atoms |

## Setup

- **Pinning.** The note's directory was copied to `pinned/rgh2/` at first read. NOTES.md has sha256 `ac936aed…e7cc`. The
  original was byte-identical to the copy at the end.
- **Independent code.** All referee code is new (`rlib.py` and the checkers).
- **Independent generator.** It closes T under single (Z1) moves on any bond, keeping at most 2 triple bonds, and does
  not rely on Lemma 1.7. Directed counts for 5–19 atoms are 8, 32, 120, 366, 1060, 2860, 7464 and 18808, summing to
  30718, which matches the note. A further 46352 vines appear at 21 atoms.

## Refuted items

### R1. Lemma 1.14(c), "rung deletion preserves type", is false as stated

**Counterexample** (`lemma114c_counterexample.py`):
- B = (I)∘Q-block∘(I) on atoms 0..5, with arcs 0→1, 1→0, 1→2, 2→4, 2⇄3, 3→1, 4→3, 4⇄5 and joints 0, 5.
- R = {2,3} is a 2-cut rung and not a cap.
- U = {1,2,3,4} is the Q-block (type II), with no joint in R.
- After deleting R, Φ(U) = {1,4} is a double bond, which is type I.

**Effect on Theorem 1.15.** The induction cannot exclude such a U inside a T-vine. The following patch, absent from the
note, closes it:
- The two new bonds form a 2-edge-cut of B/R.
- So Φ(U) has constant gap (Lemma 1.13).
- That contradicts (F4) for B/R by induction.

The theorem survives. No Q-type sub-object occurs in any T-vine up to 21 atoms.

### R2. Cor 1.16(1)'s exception, (3) and (4) are false under the note's own removal semantics

The note's removal also deletes a member's adjoint bond. Under that semantics, 109 HV families and 2880 DV′ families
disconnect (`cor116_counterexample.py`):
- **HV counterexample.** V is a σ=1 T-vine with joints 5, 6 and adjoint arc 5→6. The family is {5,6} together with
  W = {0..4}, a hyper T-vine with adjoint 3→4.
- **DV′ counterexample.** Two 5-atom T-beads share the joints 3, 4 and the bond 3→4. The family is the first vine
  together with W = {5,6,7}.

**The sources keep a hyper member's adjoint bond**: TARGET L2140 (footnote L2104), TARGET L2431 and DH23 L2128.
- Under that semantics, none of 3172 HV and 900 DV′ containers disconnects.
- The proof needs a parity step, which the referee supplies:
  - Suppose the joint bond j₁j₂ were a bridge after removal.
  - Lifting the cut back to V gives a cut of 1 + 2k bonds, which is odd.
  - But every degree in V is even, so every cut in V is even.

## Per-item labels

- **Item 1: CONFIRMED**, with the R1 patch and the R2 correction.
  - Lemmas 1.4–1.13 and Prop 1.17(a) are CONFIRMED.
  - Lemma 1.11 was checked on 415,232 cases with 0 exceptions.
  - Lemma 1.8 is tight at D = 0 (11 atoms) and D = 1 (13 atoms).
  - Lemma 1.14 (a), (b), (d) and (e) are CONFIRMED; (c) is REFUTED (R1).
  - Theorem 1.15 was checked on all 77,070 T-vines up to 21 atoms: 535,425 sub-objects, all of allowed types with free
    gaps; disjoint families exhaustively, including 2.93 M of size ≥ 3; 421,020 rung deletions and 2.65 M image
    transfers. No base-case mismatch.
  - Cor 1.16 (1), (2) and (5) are CONFIRMED.
- **Item 4: CONFIRMED.**
  - Lemma 4.1 matches DH23's L1960.
  - T∖ℓ gains δ^{−1/2}L^{−γ₀} via A.3(4).
  - Lemma 4.2 equals the closure set in both directions up to 19 closure atoms: 125 = 125.
  - The Q-branch argument ignores (Z) on a triple copy, a minor imprecision; the conclusion is unaffected.
- **Item 2: CONFIRMED.**
  - 𝔍 ≲ L^{η³}.
  - With B2 `IsLadder`: at most 3 maximal ladders and at most 13 atoms outside them, CHECKED to 21 atoms.
  - An O(1) bound holds for all sizes, and only O(1) is used.
- **Item 3: CONFIRMED.**
  - No use treats (I)–(VIII) as exhaustive.
  - The "at most 20 variables per vine" constant (TARGET L2297) becomes a constant C, which is absorbed.
- **Item 5: CONFIRMED.**
  - `IsTVine` matches Def 1.2.
  - Its "no interior cut atom" clause is redundant: closures that reduce to T are 2-connected.
  - Q-type blocks equal B2 `IsVine .II` up to 21 atoms.
  - Lemma 5.2 holds for every orientation up to 21 atoms.
  - Lemma 1.9(2) must be applied undirected.
- **Item 6: UNVERIFIED for all sizes, CHECKED up to 21 atoms** (154,140 cases pass TARGET's spine/pendant structure).
  - A possible all-size route: every cactus cycle has length ≤ 3, which is checked to 21 atoms and preserved by rung
    insertion, together with Lemma 1.6.
- **Side finding: CONFIRMED.** DH23 `subsetvc` omits the block VC:I+I, which occurs in drawn vine (IV).
