# Referee report on the T-vine blueprint note

## Reader's preface

This is the independent referee report on [the T-vine blueprint note](gamma-le-half-tvine-blueprint-notes.md).
**Verdict: accept with repairs** (R1–R6, collected in §3); no claim is GAP or FALSE, and there is no counterexample
and no new erratum. The referee re-derived the new proofs, re-ran all eight of the note's script runs (identical
output apart from timing lines), and wrote independent checks that generate T-vines from the definition (§0, §2, §5).
The repairs were applied in the Lean formalization and are not folded into the note's text. The abbreviations N2, N3,
REF2, REF3, ERRATA, TVineDefs and main are defined in the note's
[preface](gamma-le-half-tvine-blueprint-notes.md#readers-preface). Short Lean paths below are relative to
`WaveTurbulence/Foundations/` (those starting with `Frozen/` to `WaveTurbulence/`); `Contract.lean` is
`WaveTurbulenceVineParam/Contract.lean`.

*Provenance: independent refute-first referee report, November 2026. The referee did not write the note under
review.* The scripts named in the text are not included in this repository. Lean names refer to the repository at the
time of writing (the commits the report cites); a later clean-up removed some unused helpers, which remain in the git
history at the commits cited.

## 0. Setup

I did not write the work under review.

**Re-runs.** I re-ran all eight of the author's runs, from a fixed copy of the author's files.
- Every output is identical to the author's, apart from the timing line and a trailing `done` line that the author
  appended (`diff` in §5).

**Independent code.** None of it imports or copies `chartlib.py`, `g3lib.py` or the author's checkers.
- `ref_lib.py` generates T-vines **from the definition**:
  - The closures with C →* T are exactly the (Z1)-descendants of T.
  - Pruning to at most 2 triple pairs is safe: a (Z1) creates one triple pair and destroys at most one, so τ never
    decreases along the (Z1) direction.
  - Joints are placed (σ = 0 or 1), keeping multiplicity ≤ 2.
  - Canonical forms come from my own refinement-plus-individualization code.
  - This uses neither Lemma 1.7′ nor confluence.
- `ref_chart.py` rebuilds Theorem C's chart by a **global** solve, not the author's traversal. It checks the
  `FullVineChart` fields literally, together with Lemma A and the six-configuration claim.
- `ref_struct.py` gives counts, an independent F1 family, and Lemma E / 5′ / 5″ surgery replays.
- `ref_bad.py` checks the §9 remark on vine (II).

**Main.** Lean declarations were read on the main branch of this repository at commit `5a9aaac2`; Lean names and line
numbers below are as of that commit.

## 1. Verdict by claim

| # | Claim (the note, §) | Verdict |
|---|---|---|
| 1 | Statement sheet (§2): restatements of N2 1.4–1.14, Thm 1.15, Cor 1.16′, Prop 1.17, N3 Thm 6, Lemma 4.1, Lemma 5.2 | **CONFIRMED** (spot-checked against N2/N3; see §2.1) |
| 2 | B0 bridge (§2.1) | **CONFIRMED** (by unfolding; not Lean-checked) |
| 3 | Lemma A, attachment (§2.2) | **CONFIRMED**: proof re-derived; 0 violations in the independent check (≤ 17 atoms) |
| 4 | Lemma E (§5.2) | **CONFIRMED**: every case re-derived against `TVineDefs.Y2Step`; 0 failures independently |
| 5 | Lemma 5′ (§5.3) | **CONFIRMED** |
| 6 | Lemma 5″ (§5.3) | **CONFIRMED WITH REPAIR** (R3: the written proof is "mirror the cases"; I supply the cases) |
| 7 | Path-wise N2 Lemmas 1.5 and 1.9, and N3 1.14(c′) cap case (§5.3) | **CONFIRMED** |
| 8 | Lemma 1.7′, generation without confluence (§5.4) | **CONFIRMED WITH REPAIR** (R4: the "iff" in §2.2 has only ⇒ written; ⇐ is three lines) |
| 9 | Prop L for L1 and L2, by hand (§3.2) | **CONFIRMED** (both computations redone) |
| 10 | Prop L for L3–L6, CHECKED (§3.2) | **CONFIRMED WITH REPAIR** (R1: "bijection over every E" is not what the script checks; it follows from total unimodularity) |
| 11 | **Theorem C**, the piece chart for every T-vine (§3.2) | **CONFIRMED WITH REPAIR** (R1). L1–L6 are exhaustive; the triangle and σ = 1 cases are right. Independent global check: 0 failures on 23,550 directed cases (≤ 17 atoms), including det = ±1 |
| 12 | Corollary C′, `sumint` (i)–(iii) (§3.2) | **CONFIRMED** |
| 13 | Lemma LPC (§4): paper proof, and "in Lean on main, family-free" | **CONFIRMED** (paper proof checked; `clLocalOrigin_difference_coeffs` exists with exactly the stated hypotheses and no `VineType`) |
| 14 | C3 decision: keep unit decoding (§4) | **CONFIRMED** |
| 15 | Theorem S, spine code: completeness and count ≤ 2^{4N} (§6) | **CONFIRMED** (count arithmetic redone; independent shape counts match) |
| 16 | E2d sharpening: linear ⇔ anti-parallel; nonlinear ⇒ coreSign = −1 (§7) | **CONFIRMED** (independently CHECKED) |
| 17 | E4 transfer (§7) | **CONFIRMED WITH REPAIR** (R2: wrong Lean name; the correct lemma also closes open item 2) |
| 18 | E14, E24, E25, E26 transfer (§7) | **CONFIRMED** (garden- or `sumint`-level; no use of (I)–(VIII)) |
| 19 | Finite-fact list F1–F7 is complete; sizes 63 / 723 / 135 / 378 / 20 (§8) | **CONFIRMED WITH REPAIR** (R5: F4/F5 must state the removal semantics). Completeness was checked against every base used in N2/N3; all counts reproduced independently |
| 20 | §9 remark: vines (I) and (II) get their contract charts from L1 alone | **CONFIRMED** (CHECKED for m ≤ 6, every orientation) |
| 21 | Lean-facing plan for the chart: de-index `FullVineChart`, "keep every field with two changes" (§4) | **REPAIR** (R6: more fields mention `X`, and more consumers read `junction`). Lean engineering, not mathematics |

No claim is GAP or FALSE. I found no counterexample.

## 2. Detail, claim by claim

### 2.1 Statement sheet (claims 1–2)

I compared the restatements with N2 §1.3–1.7 and N3 §1.3–1.4:
- Lemma 1.8: |B| ≤ 11 + 2D.
- Lemma 1.9(1)(2).
- Lemma 1.10. The note's hyper-type form ("odd iff exactly one joint of U lies in X") is equivalent to N2's ("iff C
  contains the adjoint bond"), since the adjoint bond joins the two joints.
- Lemma 1.13.
- Theorem 1.15 (F1)–(F6).
- Theorem 6 (i)–(iv).

All are faithful. Each REFEREED attribution matches REF2 or REF3, including REF2's R1 patch for (c) and REF2/REF3's
sources' semantics for Cor 1.16′.

### 2.2 Lemma A (claim 3)

The proof is correct.
- The two C-edges at P form a 2-edge cut of Γ, hence of B.
- If both sat at one atom w, then cut(K ∪ {w}) = 4 − 2 = 2. That cut separates w from the other atom(s) of P.
- This needs |P| ≥ 2, from Prop 1.17(b), and deg w = 4.

The consequences listed in the note (atoms carrying the entry, exit and pendant bonds of R, J, B, C, D) follow by the
degree count. `ref_chart.py` checks Lemma A directly on every non-joint piece: 0 violations. It also checks that the
z-atom of a B core carries one entry and one exit bond: 0 violations.

### 2.3 Path surgery (claims 4–7)

All the steps below were checked against the exact `TVineDefs.Y2Step`: mult(a,b) = 3, exactly one further bond at
each of a and b, c ≠ d, and externals outside the pair.

**Lemma E.**
- (E0): a move never lowers a surviving multiplicity, so mult(a,b) ≥ 3 while both survive.
- Multiplicity 4 is a closed component that can never be removed.
- (E1): a vertex of a triple pair has degree 4, so it lies in only one triple pair. Hence Q = P_k exactly once.
- (E2) α: commutation (H/Q)/P₁ = (H/P₁)/Q.
- (E2) β: if q′ = d, then d has ≥ 2 bonds into Q. It can never be in a triple pair (it would need degree ≥ 5), so Q is
  never reducible. Otherwise (H/Q)/P₁ = H − Q − P₁ + dq′ = H₁/Q.
- (E2) γ: {p,q,a,b} is closed, and the move makes a≣b quadruple.
- All correct.

**Lemma 5′.**
- P₁ is disjoint from R, because a and b have multiplicity ≤ 2 to everything.
- (i) and (ii) commute with the same μ; I verified both matchings symbol by symbol.
- In (ii), y⁻ ∉ P₁: y⁻ = x⁻ = p would give deg p = 5, and y⁻ = q is case (iii). The pole K⁻ ∖ P₁ stays connected,
  because P₁ hangs from it by the single bond q–q′.
- (iii): K⁻ = P₁. Then Lemma E applies, and (C/R)/K⁻ = C − R − K⁻ + x⁺y⁺.
- Correct.

**Lemma 5″ (R3).** The conclusion is right, but the written proof is only "mirror the cases". The proof to record:
- In C/[μ]R every triple pair lies in one pole, since the poles are joined by only the two cross bonds.
- A move with no cross-bond external is mirrored verbatim.
- A move with exactly one cross-bond external, at p, is valid in the current C-graph. There p's external is the current
  rail end a or b, and the move adds the new rail a–q′; the commutation is the identity of 5′(ii).
- A move with both externals cross bonds has pair = the whole pole. This is the **collapse**.
  - In C it is valid: its externals are a ≠ b.
  - It leaves a≡b triple with externals x⁺, y⁺. These are distinct because the collapse was valid in C/[μ]R, where its
    externals are exactly x⁺, y⁺ for either μ.
  - R is then a (Y2) pair, and (C/P_j)/R = (C/[μ]R)/P_j.
- Before the collapse the cross bonds are a 2-edge cut with both sides nonempty, so the path cannot end at T′ (which is
  4-edge-connected). After the collapse no cross bond remains. So there is exactly one collapse.

**Lemmas 1.5, 1.9 and 1.14(c′).**
- With `IsClosure` = smoothing of the two joints, a non-cap 2-cut rung of B stays a 2-cut rung of cl(B).
  - A joint adjacent to both a and b would make its pole {j}, which is a cap.
  - A σ = 1 joint pair with ends a and b would make its pole {j₁, j₂}, also a cap.
  - Otherwise smoothing keeps each pole connected and nonempty.
- Hence cl(B/[μ]R) = cl(B)/[μ]R.
- For 1.9(2), "each side has an interior vertex" plus even cuts (no bridges) gives exactly two components.
- Correct.

**Independent replay (`ref_struct.py`).** Random maximal (Y2)-paths were drawn on every closure ≤ 21 atoms (8 per
closure, 1,360 paths). The checks:
- delete Q (Lemma E: 2,632 cases);
- delete R for both μ (5′: 12,736 cases);
- insert R right after it first becomes a (Y2) pair, on a fresh random path of C/[μ]R (5″: 12,736 cases).

Every new path was replayed. Result: **0 failures, and 0 stuck paths.** A stuck path, a maximal path not ending at T,
would have been a confluence counterexample. This matches the author's `pathwise_check.py` (21,078 surgeries).

### 2.4 Lemma 1.7′ (claim 8)

The proof is correct.

**τ-recursion.** A (Z1) creates one triple pair. It lowers only β, and β cannot have multiplicity 4: a quadruple pair is
a closed component that no (Y2) path to T can contain. Its new bonds go to fresh vertices. So the number of starts is
τ(C) ≤ 2.

**Reorder.**
- A start is by definition on a non-triple copy, so ladder 2 never touches ladder 1's triple.
- Ladder-1 operations change only ladder 1's current triple pair and fresh vertices. They therefore never change the
  multiplicity of the pair ℓ′, and ℓ′ cannot be a later ladder-1 triple (those pairs are fresh).
- So the swaps are valid, and ℓ′ is a non-triple copy of Z_k(T, ℓ).

**R4.** §2.2 states Lemma 1.7′ as an **iff**, but §5.4 proves only ⇒. The converse:
- If G is C ∈ {T, Z_k(T,ℓ), Z_{k′}(Z_k(T,ℓ),ℓ′)} with joints placed and multiplicity ≤ 2, then smoothing the joints
  returns C.
- The reversed (Z1)'s are valid (Y2) steps (fresh a, b; c ≠ d because C is loopless), so C →* T.
- G is connected with degrees 2, 2, 4, …, 4. So `IsTVineU` holds.

Only ⇒ is needed for the checker, because F1 only has to cover every T-vine.

**Independent check.** I implemented F1 myself (`gen_closures` and `gen_tvines`, exactly as §8 describes them):
- 63 closure instances and 723 T-vine instances, of which 135 have D = 0 and 378 have D ≤ 1. All four numbers equal
  the note's.
- Every instance is a T-vine.
- The family covers **all** definition-generated shapes for N ≤ 13: 3/3, 5/5, 10/10, 14/14, 21/21 (53 in all).

### 2.5 Prop L and Theorem C (claims 9–12)

**L1 and L2.** I recomputed both by hand: the labels, conservation at p and q, the exit relation, Γ_p = −2⟨x,y⟩, and
Σ_P Γ = 2⟨ρ,y⟩ (straight) or −2⟨ρ, ρ+x−y⟩ (turn). Correct.

**Sign conventions.** These were checked against `Contract.lean`:
- incidence = out − in, so flow = out − in;
- energy = Σ_in |k|² − Σ_out |k|²;
- g incoming and h = g − r outgoing at b;
- `rung_s_phase` sits at ySlot (the s-atom) and `rung_t_phase` at xSlot (the t-atom);
- the core phases sit at uSlot 0 and 1.

Theorem C's (C0)/(C4) match all of these.
- The entry relation k(into P) − k(out of P) = ρ, and the exit relation = −ρ, both follow from flow(far side) = −r when
  the far side contains a.
- In fact ρ = +r on **every** spine cut, not ±r. This is harmless.

**Exhaustiveness of L1–L6.**
- B and C cores occur only with H = ∅ (Thm 6(iii)), hence never on the P-b triangle.
- D has Γ-degree 2, so it ends the pendant.
- J (Γ-degree 6) exists only for P-a.
- The P-b triangle needs no configuration of its own, including the cases where b or a is a triangle corner (σ = 1, or a
  single-bond pair at a joint). The triangle's three cut relations are dependent, so step 2 of the gluing is consistent.

`ref_chart.py` classifies every non-joint piece from 2-edge cuts alone. It found 0 pieces outside L1–L6, and 0 junctions
without a D core.

**Gluing.** κ-freeness holds: nodeResonance(v) = 2⟨κ, Σ_in w − Σ_out w⟩ + local, and the first term vanishes by
conservation. The (C2) induction gives g-coefficient 1 and unit coefficients, because coordinate sets are disjoint and
x₀ appears with coefficient −1 in every label. (C5) holds: 2|S| − 2 = 2n.

**R1, a gap in wording only.** Prop L asserts that "the solution map … is an affine bijection over **every** E". The
proof of (C1) says the labels are "forced step by step (uniqueness in Prop L)". But `local_pieces.py` / `chartlib.solve`
only checks this over ℚ (Fraction elimination) and checks integrality of the solution. Over an E with torsion, unique
solvability over ℚ with an integral solution does **not** by itself give uniqueness: for example 2k = 2x.

Repair, to insert in Prop L and in (C1):
- The structural rows of a local system (conservation at P's atoms, and one exit relation per exit cycle) are exactly
  the incidence rows of the small digraph made of P's atoms plus one virtual vertex per exit cycle. Each exit relation
  is the conservation row of its virtual vertex. They are restricted to the unknown columns, so the matrix S is
  **totally unimodular**.
- Hence every nonzero elementary divisor of S is 1, and ker(S ⊗ E) = ker_ℤ(S) ⊗ E.
- The script's integral solution formula F satisfies S F_c = 0 and D F_c = I, where D is the coordinate rows. Unique
  solvability over ℚ forces rank ker_ℤ(S) = c_P.
- So D restricted to ker_ℤ(S) is a surjection between free modules of equal rank, hence an isomorphism over ℤ, hence
  over every E.
- Globally, the same argument applies to the incidence matrix of the vine. Equivalently, the square system (flow rows at
  b and the interior atoms, plus the n coordinate rows) is block-triangular along the gluing order with unimodular
  diagonal blocks. So **det = ±1**, and that is (C1) over every E.

The facts the script checks therefore suffice; the written argument has to say this. `ref_chart.py` tests det = ±1
directly (below).

**Independent end-to-end check (`ref_chart.py`).** It covers every directed T-vine with ≤ 17 atoms, generated from the
definition, both joint labellings, up to directed isomorphism with ordered joints: 12 + 62 + 228 + 720 + 2,080 +
5,664 + 14,784 = **23,550 cases** (8,766 of them with ≤ 15 atoms). The coordinate recipe is Theorem C's:
- x₀ = h − k_in(b);
- the local pair (o₁−i₁, o₁−i₂) at s for every 2-atom piece. This was run twice, with s = the first atom of every piece
  and with s = the second atom of every piece;
- the core: every (w_a, order, w_b, u₃, signs) until one passes.

The square integer system is solved **globally**. The checks, against `FullVineChart` read literally:
- **det M = ±1**;
- `decode_eq` with g-coefficient 1, and `free_unit`;
- `joint_phase`;
- `rung_s_phase` and `rung_t_phase`, with ζ unit including the r-coefficient;
- `core_first_phase`, `core_second_phase` and `core_sum_phase`, with ξ unit;
- `rung_bonds` / junction;
- `bond_count = 2n`.

Results:
- **0 failures**, and both s-choices work in every case (23,550 / 23,550 each).
- Configuration counts to 17 atoms: L1 92,168, L2 29,716, L3 6,138, L4 4,614, L5 1,538, L6 17,398 (`ref_chart_17.txt`).
- Joint-labelled shape counts: 3, 8, 15, 24, 35, 48, 63. These equal `classcode_check.py`'s.

The author's `chart_check.py` (0 failures on 23,820 cases to 17 atoms, re-run here) agrees. Its count is per
unordered class × 2 labellings; mine is per ordered-joint class, so swap-symmetric classes are counted once.

**Corollary C′.** (i) follows from (C2), from chaining (g of unit i is a label of unit i − 1; all units carry the same
r), and from LPC. (ii) is garden-level. (iii) follows from (C3). Correct.

### 2.6 LPC and the C3 decision (claims 13–14)

**Paper proof.** s(𝔫) = ζκ is additive over children, and leaf pairs cancel. An opposite difference is a sum of two of
the four signed labels, which equals ± the s-sum over a union of two child subtrees. So the coefficients are in
{0, ±1}. Correct.

**On main.**
- `VineEstS2.clLocalOrigin_difference_coeffs` (`CLLocalOriginCoefficients.lean:22`) has hypotheses `IsBlock`,
  `CLRegionData`, `IsPlain` and opposite `OriginAt` incidences. There is no `VineType`.
- `exists_chainInverseRow` (`CLChainInverseRows.lean:25`) has "no inverse-unit premise".

**Locality.** The note lists locality (C3) as a property of its chart. On main it is **not** a premise:
`clVineChart_hasLocalDifferences` (`CLVineLocalWitnesses.lean:70`) derives `HasLocalDifferences` from the
`joint`/`rung_s`/`core_first`/`core_second` phase fields of **any** `FullVineChart`. So Theorem C's phase fields alone
give T₁⁻¹ unit in Lean. This is stronger support for the C3 decision than the note claims.

The unit contract is therefore met, and no widening is needed.

### 2.7 Theorem S (claim 15)

**Completeness.** It follows from Thm 6, Prop 1.17(b) and Lemma A:
- every bond lies inside a piece or on a Γ-cycle;
- by Lemma A, each digon or triangle corner leaves one binary matching choice, absorbed by a β bit.

**Count, redone.**
- The three cases give (m+1)·2^{m+2}·[2 + (m+1) + 2(m+2)] = (m+1)(3m+7)·2^{m+2} ≤ 3(m+2)²·2^{m+2} ≤ N²·2^N.
- The bit counts are: m+2 without a pendant; m+2 for P-a; m+3 for P-b (r digons, 3 corners, s−1 pendant digons).
- With 2^{2N−2} orientation bits and the swap bit, the total is N²·2^{3N−1} ≤ 2^{4N}.
- At N = 5 the formula gives 8 + 0 + 8 = 16 codes, which equals `out_classcode_19.txt`.

My independent joint-labelled shape counts (3, 8, 15, 24, 35, 48, 63 for N = 5…17) confirm the reference set that
`classcode_check.py` compared against.

### 2.8 The `vineest` repairs (claims 16–18)

**E2d.** `out_local_pieces.txt` and my global check agree: across 47,100 charts (23,550 cases × 2 s-choices, ≤ 17 atoms; 25,088 linear and 22,012 nonlinear), linear
occurs exactly for anti-parallel doubles and nonlinear exactly for parallel ones, and every nonlinear chart has coreSign = −1.
For C and D, the two doubles are forced to be both anti-parallel or both parallel, because the middle atom has
internal degree 4. Main's contract carries `coreSign : ℤˣ`, so either sign is covered in any case. CONFIRMED.

**E4 (R2).** The note says the mixture hypothesis `SumintMixSignedDoubled` is "proved unconditionally on main
(namespace `DegenVine`, consumed by vineestStep3)". That is **not accurate as named**.
- On main, `DegenVine.SumintMixSignedDoubled` is only conditional:
  `sumintMixSignedDoubled_of (hS : SumintMixSigned)` (`Vine/DegenVine/SumintMixDoubled.lean:40`). No declaration
  proving `SumintMixSigned` exists in the tree.
- The **unconditional** lemma that the sealed chain uses is `DegenVinePar.sumintMixParDoubled : SumintMixParDoubled`
  (`Vine/DegenVinePar/SumintMixDoubled.lean:79`, from `sumintMix : SumintMixPar`, `SumintMix.lean:41`). It is consumed
  at `VineEst/VineEstS5C/P4/Final/Prefix.lean:33` and in the flower files.
- Its prefix `WTPrefixA` quantifies **γ ∈ Ioo 0 1** (`Frozen/Defs/WTPrefixA.lean:30`). `sumintMix`'s proof uses only
  that hypothesis.

Repair: cite `sumintMixParDoubled`. This also **closes** the note's open item 2 (the γ-range check for the vine
estimate): the range already includes γ ≤ 1/2. The substance of the E4 transfer (mixture of mass ≤ 3ⁿ, `sumint`
uniform in linear phases) is unaffected.

Side note, not the author's responsibility: ERRATA E4's sentence "the unconditional proof of that hypothesis is a
working note, not included" is out of date relative to main.

**E14, E24, E25 and E26.** I read all four errata.
- E14 is an order-0 time trace at the lower child.
- E24: its rescue rests on "every pair of the vine realization has type (q, j₁, j₁)", and on "operative members are
  bad" (E25).
- E25 counts only bad vines, (I)/(II), which are the same in 𝒱_{≤1/2}.
- E26 needs only the lower-joint clock t₀ⁱ, which is Theorem C's x₀-atom, plus `sumint`'s modulation tolerance.

None uses the list (I)–(VIII). CONFIRMED.

### 2.9 The finite facts (claim 19)

**Completeness of the list.** I traced every finite base in N2 and N3:
- N2 Thm 1.15 (F1)(i), base D = 0, is **F3**.
- N2 Thm 1.15 (F3)–(F5) for single members, base D ≤ 1, is **F4**.
- N2 (F5) for families, step 4 (N3 (B5): never reached), is **F5**.
- N2 Prop 1.17(b), base D = 0, is **F2**.
- N2 Lemma 5.2 is **F6**; its k = 0 part is Lean-proved in `TVineExamples.lean` (the check that accompanied
  TVineDefs; not included): `Draw{III..VIII}_isTVine`, fresh build OK and axioms standard per that check's progress
  record and build logs.
- N3 Theorem 6 has "no base of its own" (N3 §1.5; REF3).
- Lemmas 1.7′ and 1.8, Lemma 4.1, Lemma 6.2, Cor 1.16′ and Lemma P are all-size proofs.
- Theorem C needs only F7 (plus F2 through Thm 6).

No base is missing.

**Sizes.** These were reproduced independently:
- 23 closures (1/1/4/6/11), 53 shapes, D = 0 shapes 13, D ≤ 1 shapes 27;
- max |B| = 11 at D = 0 and 13 at D = 1 (Lemma 1.8 tight; 0 violations);
- raw counts 63 / 723 / 135 / 378.

**R5.** F4 says "X minus U is connected", and F5 says "families", without naming the removal semantics. REF2 R2 showed
that the semantics matter, for containers. State it in the checker spec:
- for F4, use N2's stronger single-member semantics (delete I(U) and every bond of U, adjoint included), which implies
  the sources' `rem`;
- for F5, use the reducibility statement exactly as written, with families of ≥ 2 members.

### 2.10 The §9 remark (claim 20)

**Checks.** `ref_bad.py` covers vine (II) as the ladder j₁ = R₁ = … = R_m = j₂, for m = 1…6 and all 252 balanced
orientations, both s-choices, with only the L1 rung recipe. Results:
- det = ±1, unit decoding, joint and rung phases exact, ζ unit: 0 failures;
- **`ζ_bad_nonzero` holds** in every case.

(I) is the case m = 0. CONFIRMED.

### 2.11 The Lean-facing plan for the chart (claim 21, R6)

"De-index `FullVineChart` from `VineType` and keep every field, with two changes (junction, junction_type)"
undercounts what has to change.

**Fields that also depend on `X`:**
- `Shape X` (`typeI`, `typeII`, and `n` via `X.IsBad`);
- `uSlot`'s `hn : X.IsBad = false`, and through it the `core_*` fields;
- `ζ_bad_nonzero`;
- `VINEPARAM`.

**Consumers that read `junction` besides VineEstS2:**
- `WaveTurbulence/Foundations/FinalCount/VCLadProd.lean`;
- `WaveTurbulence/Foundations/FinalCount/VCSpecial2.lean`;
- `WaveTurbulence/Foundations/VineEst/VineEstS3/ChartNormal.lean` (`junction_none` for `.II`).

Suggested: parametrize by a `bad : Bool` (or a family tag) in place of `X`, and list these files in the plan for the
chart. This is Lean engineering and changes no mathematics.

## 3. The repairs, collected

1. **R1 (Prop L, Theorem C (C1)).** Add the total-unimodularity argument of §2.5. Equivalently, state and prove det = ±1
   of the square system by block-triangularity. That is what makes "bijection over every abelian group E" true at all
   sizes from the script-checked facts.
2. **R2 (E4).** Cite `DegenVinePar.sumintMixParDoubled` (unconditional, γ ∈ (0,1)), not
   `DegenVine.SumintMixSignedDoubled` (conditional). Mark open item 2 (the γ-range check for the vine estimate)
   **closed**.
3. **R3 (Lemma 5″).** Write out the case analysis of §2.3; it is needed verbatim for the Lean `y2Path_insertRung`.
4. **R4 (Lemma 1.7′).** Either state only ⇒, or add the three-line converse of §2.4.
5. **R5 (F4, F5).** Name the removal semantics.
6. **R6 (Lean plan for the chart).** Complete the de-indexing list (§2.11).

Wording only:
- ρ = +r on every spine cut (§3.2 says ±r);
- the bad-vine and T₁⁻¹ claims could cite `clVineChart_hasLocalDifferences`, which makes locality a consequence rather
  than an obligation.

## 4. What I could not refute, and why that is informative

**Adversarial attempts that found nothing.**
- A Theorem C chart over a torsion group E failing uniqueness: det = ±1 in all 23,550 cases (≤ 17 atoms).
- A piece outside L1–L6, a junction without a D core, a Lemma A violation: none.
- A T-vine missed by the F1 family: none, to 13 atoms. The comparison is against the definition, not against Lemma 1.7′.
- A stuck (Y2) path, i.e. a confluence failure, among 1,360 random paths on closures ≤ 21 atoms: none.
- A surgery failure (E, 5′, 5″): none in 28,104 cases.
- A nonlinear core with coreSign = +1: none.
- A (II) rung with ζ = 0 in x and y: none.

**Not independently checked:**
- Theorem S's decoder; I checked only its target shape counts.
- The garden side, (ii) and LPC's tree check, which are Lean-proved on main.
- N2/N3's REFEREED proofs beyond the spot checks of §2.1.

## 5. Files

| file | content |
|---|---|
| `run_all.sh` and its outputs `out_*.txt` | the author's eight runs, re-run; `diff` against the author's outputs shows only timing and `done` lines |
| `ref_lib.py` | independent generator (closures from T by (Z1); joints; orientations), canonical forms, 2-cuts, pieces, D |
| `ref_chart.py MAX` | Theorem C / FullVineChart fields / Lemma A / L1–L6 / E2d, by global solve. `ref_chart_{13,15,17}.txt` |
| `ref_struct.py MAXV MAXC NPATH SEED` | counts, Lemma 1.8, the F1 family, and E / 5′ / 5″ surgery. `ref_struct_15_17.txt`, `ref_struct_13_21.txt` |
| `ref_bad.py MAXM` | the §9 vine (II) chart. `ref_bad_6.txt` |

**17-atom run of `ref_chart.py`:** 23,550 directed cases, TOTAL FAILURES 0 (`ref_chart_17.txt`).

## 6. Overall verdict

**ACCEPT WITH REPAIRS.**

Every claim marked PROVED or CHECKED survives a refute-first reading and an independent re-check. The new proofs are
correct:
- Lemma A;
- Lemmas E, 5′ and 5″;
- Lemma 1.7′;
- Theorem C with Prop L;
- LPC;
- Theorem S.

They settle the `sumint` hypotheses (i)–(iii) for T-vine charts at all sizes (C3: keep unit decoding), confluence of
the (Y)-reduction (N2 Lemma 1.4; replaced by path surgery) and stage 1 with T-vines (spine-code class count; the six
`vineest` repairs transfer). No counterexample and no new erratum.

The repairs R1–R6 are all local:
- R1 is a missing two-paragraph justification. The script-checked facts already imply it, and my independent check
  confirms det = ±1.
- R2 is a wrong Lean citation. The correct lemma exists and is unconditional for all γ ∈ (0,1), which also closes an
  open item.
- R3–R5 are expository precision.
- R6 is Lean planning.

None changes a statement, an exponent or the finite-fact list.
