# Referee report 3: research note 3 (the γ ≤ 1/2 vine family)

The referee is independent and refute-first (subagent), 2026-11-05. wt-orch transcribed this report from the referee's
final message, because the harness refused the file write. Scripts and outputs are in this directory, with hashes in
`SHA256SUMS`.

## Verdict

**YES: the proposal can go to the author for approval, subject to the caveats at the end.**
- No counterexample was found to any of the five claims, and all five survive.
- Claims 1–3 and the Lean predicate are CONFIRMED, by re-derived proofs and independent checks.
- Two statements in note 3 are worded too broadly. Both are under claim 4: the "70 minimal base pairs" count, and "edge
  directions never needed".

## Setup

- **Pinning.** Note 3's directory was pinned at first read (42 files; NOTES.txt sha256 `92a9909a…5967`). The original
  was byte-identical to the pin at the end.
- **Independent code.** All code is new.
  - The generator closes T under (Z1) moves, keeping at most 2 triple bonds, and places the joints.
  - Membership is decided by exhaustive (Y2) search, so no confluence is assumed.
  - Canonical forms use colour refinement plus individualisation; 1790 random relabellings gave 0 mismatches.
- **Templates.** The drawn vines were parsed from the B2 draft `WaveB2-Molecules.lean`.
- **Compute:** about 6 minutes.

## Claim 1: Theorem 6 (`layervine`, every size)

**CONFIRMED** (proof re-derived), and **CHECKED** on all 1530 undirected shapes with at most 41 atoms, in both joint
labellings (3060 cases): 0 failures.

**(U0)–(U2) is all `layervine` uses.** The referee read L1500–L1532; the quoted lines L1519, L1523, L1525, L1527,
L1529 and L1531 are exact. Beyond (U0)–(U2), the proof uses only:
- facts that do not depend on the vine family: `block_clcn` (L1345), `canonequiv`, `sublayer` and `layerlad`;
- a bounded number of bonds between consecutive spine members (at most 2, by Theorem 6(ii)).

**The three lemmas.**
- **Lemma 6.1 (cactus):** correct.
- **Lemma 6.2 (no two disjoint pendants, re-proved along the given (Y2)-path):** correct in every step.
- **Lemma 6.3 and the translation to atoms:** correct. Internal connectivity of the pieces rests on note 2's
  piece-shape theorem, which referee 2 confirmed.

**Atom-level checks.** All of these pass:
- piece shape;
- (U1)(a), adjacency, and no bonds between non-consecutive spine members;
- the pendant peel: two single bonds per step, with inner ends in one group;
- the core is (B), (C) or (D);
- r = 0 exactly when σ = 1;
- Lemma 6.2 on every joint-free 2-cut side;
- cactus cycles: 21955 of length 2 and 715 of length 3, matching note 3;
- ladders: at most 3 maximal ladders, and at most 13 atoms outside them (13 is attained). This holds for both B2
  `IsLadder` versions.

**Controls.** Hand-built bad blocks are rejected.

**Counts.** The directed class counts up to 23 atoms match note 3 and referee 2: 188926 in total, 111856 at 23 atoms.

**Wording.** The digon-cut sentence in (iv) is not literal: the separating cut is δ(X − x). The conclusion holds.

## Claim 2: Lemma 1.14(c′)

**CONFIRMED.** Parts (i)–(iii) were re-derived, and the exclusion via (F4) is sound.

**CHECKED on 1586 directed T-vines with at most 13 atoms:**
- 924 all-in images, all type-preserving;
- no case (iii);
- every B/R is a T-vine;
- every sub-object has an (F3) type, with free gaps.

**CHECKED on 38670 directed chain blocks:**
- 96388 all-in images: 86296 preserved and 10092 case (iii);
- every case (iii) is a 4-atom Q-block that becomes (I), with constant gap;
- 0 unpredicted changes.

## Claim 3: Cor 1.16′ under the sources' semantics

**The semantics: CONFIRMED.** TARGET L2140 (with the footnote at L2104) and DH23 L1775 ("U minus a bond in case of HV or
HVC") keep the adjoint bond.

**The proof: CONFIRMED.** The referee re-derived Lemma P (odd-cut parity), the location cases (L-a)–(L-c), the list,
and connectivity, including the HVC parity case and the HV case with σ = 0.

**CHECKED.** 40611 containers (single 1646, HV 3292, DV′ 465, VC 17910, HVC 17298) and 360326 families:
- **Membership:** 0 unlocated members, and 0 list violations.
- **Sources' semantics:** 0 disconnections.
- **Note 2's semantics:** the old failures, HV 109 and DV′ 1488.
- **Overlaps:** every overlapping non-nested pair is either two double bonds sharing an atom, whose union is a member,
  or the DV′ pair.

## Claim 4: the minimal base set

**The lists are CHECKED and complete, given Lemma 1.8 plus the classification:**
- closures with at most 11 atoms: 23 (1 + 1 + 4 + 6 + 11);
- shapes with at most 13 atoms: 53;
- directed classes: 1586;
- D = 0: 13 shapes / 94 directed classes;
- D ≤ 1: 27 / 410.

Further checks:
- Lemma 1.8 is tight up to 25 atoms.
- The family base is empty.
- All 13 slot facts hold.
- Q-type blocks coincide with B2's (II) up to 24 atoms.

**Two imprecisions.**
- **Base pairs.** "70 minimal pairs" is a raw count. Up to automorphism it is **57** (37 + 20).
- **Directions.** "Directions unnecessary" is sound for the combinatorial facts: undirected (F1)–(F6) is CHECKED to
  25 atoms, and so is deletion with both matchings. It does NOT cover the analytic unit data of note 1's Theorem N,
  which depend on orientation and remain covered by the directed checks of note 1 and referee 1.

## Claim 5: the Lean proposal

**`IsTVine` without the "no interior cut atom" clause: CONFIRMED.** Lemma 4.1 was re-derived: (Z1) preserves
2-connectivity, and paths lift from the closure. CHECKED: 0 interior cut atoms among 12483 placements, up to 41 atoms.
- Caveat: "no confluence needed" holds only for Lemma 6.2. Note 2's Lemmas 1.5 and 1.9 still need Lemma 1.4
  (confluence) in Lean, and the piece-shape theorem and Theorem 1.15 depend on them.

**groups := pieces: CHECKED** on 847 drawn expansions (k ≤ 6 per slot). Pieces equal the `cohmol` groups recomputed from
TARGET L1489–L1496 and equal the B2 template groups. The argument for all k is CONFIRMED.

**The `IsVineGamma` split: CONFIRMED.** The drawn vines (III)–(VIII) are T-vines (CHECKED for k ≤ 6), so the γ > 1/2
family sits inside the γ ≤ 1/2 family.

**The Sec. 4.4 inventory.** Seventeen entries were spot-checked, all accurate. Two notes:
- `moleprop4`(2) must be read with the enlarged family for every γ, because its proof applies `ylem1`, which holds only
  for the enlarged family.
- The `layergarden` proof spans L2220–L2255. L2223–L2246 is only the range of vine mentions.

**New side finding.** DH23's `subsetvc` list also omits the **block vine (V)**, which occurs in drawn vine (VII) on
atoms {4,5,6,7,8}. This is in addition to the block VC:I+I that referee 2 found missing. Cor 1.16′ already includes
block T-vines.

## Exact remaining caveats

1. **Python checks with no kernel certificate.** These are:
   - the classification up to 13 atoms;
   - the 57 undirected (70 raw) or 459 directed base pairs;
   - the 13 D = 0 shapes;
   - the slot facts.

   Confluence (note 2 Lemma 1.4) is still a Lean obligation.
2. **Wording fixes for note 3:**
   - "70 base pairs" is a raw count (57 up to symmetry);
   - "directions unnecessary" should be limited to the combinatorial facts;
   - the digon-cut wording in Theorem 6(iv);
   - the `layergarden` line range;
   - the block vine (V) should be added to the DH23 `subsetvc` erratum.
3. **Unchanged, outside this packet:**
   - there is no uniform family for γ > 1/2; γ > 1/2 case (4) goes through F75;
   - the old caveats C1–C3;
   - the "20 variables" constant in `flowerest1` becomes a constant C (referee 2; not re-checked).
