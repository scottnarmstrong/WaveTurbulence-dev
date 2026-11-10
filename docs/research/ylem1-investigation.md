# DH23 `ylem1` vs the B2 vine family: independent investigation (2026-11-04)

Investigator: a fresh Opus agent commissioned by the orchestrator. Inputs: the counterexample in
`<scratch>/moleprop4/` (wt-ansob, MOLEPROP4); DH23 `Revision_Submit.tex`; TARGET; DH21; B2
`WaveB2-Molecules.lean`. The scripts, outputs and figure crops are in this directory (`enum/`, `vine*.png`).

## Verdict: (b) — a DH23 erratum, not our definitions

- **All eight B2 templates are correct.** `WaveB2-Molecules.lean` L506–L541 match `Vines.png` (DH23 L798–L800), read
  with Remark 5.2(c) L805: atom counts, multiplicities, joint positions and slots all agree. Neither DH23's family nor
  TARGET's contains a 7-atom vine.
- **The counterexample is valid.** A literal directed (Y2) simulation (L1929) gives one complete sequence to the doubled
  triangle T.
- **`ylem1` is false, with more than one omission.** An exhaustive inverse enumeration (all at most two (Y) sequences,
  against all B2 vine closures) finds four:
  - Q and T themselves, with zero sequences;
  - the 5-atom molecule (T₁, one sequence of length 1);
  - two infinite families with two triple bonds, both from the "(VI)" bullet (L1946). The smallest has 7 atoms, with
    two triple bonds in series.
- **No figure reading saves it.** The most generous reading, which allows a length-0 dashed pair between two double
  bonds, recovers Q, T₁ and one family, but still misses T and the other family.
- **There is a second, independent gap at L1885** (DH23 Prop 9.6, case (4)): "an enumeration shows 𝕄₀ must be a vine"
  fails even for drawn vines. A 9-atom example is given below.

## Evidence

### Q1 — vine sizes

Remark 5.2(c) only inserts ladders, so each drawn vine is the minimum of its type. TARGET's rule of at least two rungs
(F37) leaves the minima unchanged.

| Type | Atoms as drawn (= B2) | Slots | Closure atoms | Triple bonds in closure |
|---|---|---|---|---|
| I | 2 | 0 | — | — |
| II | 6 | 1 | 4 + 2k | 2 |
| III | 9 | 2 | 7 + 2Σk | 2 |
| IV | 9 | 2 | 7 + 2Σk | 2 |
| V | 9 | 1 | 7 + 2k | 1 (adjacent joints) |
| VI | 15 | 3 | 13 + 2Σk | 2 |
| VII | 11 | 3 | 9 + 2Σk | 2 |
| VIII | 11 | 2 | 9 + 2Σk | 1 (closure ≅ the (V) closure with one more rung) |

Every template was checked against full-resolution figure crops. The (VII) crossing agrees with WAVE-B §3.6(ii).

### Q2 — the 5-atom input

- It is a DH23 pseudomolecule (L633): 4-regular, 2-in/2-out, loop-free, connected, with one triple bond (3≡4).
- (Y2) applies literally: the far ends 0 and 1 are distinct, and the new bond 0→1 has matching directions. No new
  triple bond forms, so the sequence stops at T.
- The YOper figure draws only chains of length at least 2, but the text at L1929 allows length 1.
- The molecule genuinely occurs as 𝕄₁ in Prop 9.6 case (4). Five 7-atom components 𝕄₀, with no triple bond and no cut
  vertex, reduce to it; one is "(V) without its second rung".

### Q3 — completeness, and the errors in the proof

**Why the enumeration is complete.**
- Every step must be (Y2), since the end state is 4-regular.
- There are at most two sequences.
- Undoing one sequence is the source's (Z) with chain length n ≥ 1.

Brute force up to 15 atoms finds 22 missing classes. The parametrised families were checked for n₁, n₂ ≤ 6 (up to 27
atoms): 288 configurations, 0 mismatches.

**What each case maps to.**
- Q with one sequence → (II).
- T with one sequence: n ≥ 2 → (V), and also (VIII) for n ≥ 3; n = 1 is T₁, which the lemma misses.
- The bullets at L1943, L1944 and L1945 → (IV), (III) and (VII), all fully covered.
- The bullet at L1946 → (VI) only when the rail is interior and the second chain has at least 2 pairs. Rails next to
  the triple bond or next to the triangle are missed.

**Errors in the proof (L1939–L1948).**
- It never treats zero or one sequence.
- L1941's claim that the intermediate molecule comes from vines III, IV, V, VII or VIII is wrong.
- L1946 over-claims (VI).
- So DH23 L586's claim that the exceptional molecules "exactly correspond to vines (II)–(VIII)" is false.

**7-atom example.** It reduces to T in either order and is not a vine closure:
`1→0, 1→2, 2→1, 2→0, 0→2, 0→5, 5→6, 5→6, 6→5, 6→3, 3→4, 3→4, 4→3, 4→1`.

**9-atom example for the L1885 gap.** Start from the closure of V(0). One β-atom is forced onto the triple bond and the
other lies on e–f. The bonds, with joints 7 and 8, are:
`e=g, f=g, e–a₂, f–b₂, e–7, f–7, a₁–a₂, a₁=b₁, a₁–8, b₁–8, a₂=b₂, b₁–b₂`.
It has no triple bond and no cut vertex, and it is not a drawn vine.

**Related.** Prop 10.4(1) (L1959) has the same length-1 omission: a single triple bond on two atoms, arising from a
4-atom degenerate (II) block in case (5).

### Q4 — downstream

**Where the lemma is used.**
- `ylem1` is used only at L1961, in the proof of Prop 10.4(2).
- Prop 10.4(2) is used only at L1883, in Prop 9.6 case (4).
- TARGET uses Prop 9.6 as a black box at L2197 (`lgmolect`).

**Not harmless inside Prop 10.4.** DH23's own introduction (L579ff.) says Q has no good operation and T has one. With
`ylem2` the exceptional molecules get no gain, so they must be excluded by hypothesis; a direct count cannot absorb
them.

**Prop 9.6, case (4).**
- The source argument (vine ⇒ large gap ⇒ operation (c)) never uses the vine's shape. So it covers every 𝕄₀ whose
  β-gap is large, for example one coming from a Step-4 cut.
- **Open:** non-vine components whose two β-atoms both come from small-gap cuts. The smallest instances are the 4-atom
  Q-block, the three 5-atom T-blocks, the five 7-atom T₁-blocks, and the 9-atom block above.
- An unverified partial route uses operations (d)+(e) and the (opere) bound (L1871) when |r| ≳ L^{−γ−100η}. It does
  not cover T-blocks, the Q-block, or very small gaps.
- Closing this needs a mathematical decision, or the authors.

**Scratch that depends on the templates.** This matters only if the campaign enlarges the vine family instead:
`<scratch>/vines/src` (78 of 382 files use the template API). `moleprop13` and `degen` hold only
definitional snapshots. Under the repair below, nothing needs re-checking.

## Proposed repair

**Notation.**
- `Z_n(N, ℓ)` is the source's (Z) (L1939): remove one copy of a non-triple bond ℓ = u→v, and attach a chain
  a₁≡b₁, a_j=b_j (2 ≤ j ≤ n), with rails a_j–a_{j+1} and b_j–b_{j+1}, plus u→a_n and b_n→v.
- T is the triangle e, f, g of double bonds, and `T_n := Z_n(T, e→f)`.

**(R1) Lemma ylem1′**, replacing L1937–L1938:

> Suppose 𝕄 is a connected 4-regular pseudomolecule with at most two triple bonds, and 𝕄′ is formed from 𝕄 by (Y)
> sequences (possibly none). If 𝕄′ is a quadruple bond or a triangle of 3 double bonds, then 𝕄 is (1) the closure of a
> vine (II)–(VIII); or (2) Q or T itself; or (3) T₁ (a₁≡b₁, a₁–e, b₁–f, e–f, e=g, f=g); or (4) Z_m(T_n, ℓ′) for some
> n, m ≥ 1, where ℓ′ is the rail bond incident to a₁ (a₁–a₂, or a₁–e if n = 1) or the rail bond a_n–e.

**(R2) Prop 10.4(2)′.**
- Call 𝕄 *Y-exceptional* if some complete (Y)-reduction of it ends in Q or T.
- Replace the hypothesis "not formed from a vine" with "not Y-exceptional".
- At L1961, replace the sentence with:

  > Apply at most two (Y) sequences to get 𝕄′, which has no triple bond and no quadruple bond (a connected
  > pseudomolecule with a quadruple bond is a quadruple bond), and is not a triangle of 3 double bonds since 𝕄 is not
  > Y-exceptional.

- The rest of the proof (L1963–L1977) is unchanged and no longer uses `ylem1`.

**(R3) Prop 9.6 case (4), L1885 — new open gap.**
- To prove: if 𝕄₀ has V_α = 0, V_β = 2 and 𝕄₁ is Y-exceptional, then 𝔄₀ ≲ L^{−η²−η⁵ρ₀}.
- The source proves this only for large β-gaps; it is unproved for small-gap non-vine components.
- Add the parallel note on Prop 10.4(1)'s length-1 case.
- This is a candidate DH23 erratum inside TARGET's black box, to be escalated.

**(R4)** No change to B2 (`VineType.template`, `insertRungs`, `expand`, `IsVine`).

**(R5)** Update F69 as resolved as a DH23 erratum: the exception list above, R1/R2 as the repair, and F69b as a new
open gap to escalate.

**Status of G7 and G8.** G7 can go ahead on `ylem2`, Prop 10.4(1) with the length-1 note, Prop 10.4(2)′ and `ylem1′`.
G8 cannot close case (4) from the source text.

No Lean was compiled. All new claims are finite graph-isomorphism computations, and the prover's kernel checks already
cover the 5-atom facts.
