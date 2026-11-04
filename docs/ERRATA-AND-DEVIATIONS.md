# Errata and deviations

This file records defects found in the pinned sources while formalizing them, and every deviation of the formal
statements from the sources. The working ledger is `docs/FINDINGS.md`; entries move here once confirmed. Repairs of
the project's own statements are not errata.

**Pinned sources (sha256 of the TeX):**
- TARGET: Deng–Hani, *Long time justification of wave turbulence theory*, arXiv:2311.10082v2,
  `WKE-Longer_times_Final_arXiv.tex`, `493eef6b7dec448b…`.
- DH23: Deng–Hani, *Full derivation of the wave kinetic equation* (arXiv:2301.07063), `Revision_Submit.tex`,
  `c7e47dfabf5a4cca…`.

Line numbers below refer to these files.

**Status legend:**
- CONFIRMED: the defect is established by an explicit counterexample or proof, and an independent refute-first
  verifier has checked it.
- CANDIDATE: written up, independent check pending.
- DEVIATION: a formal statement differs from the source by an approved reading or ruling.

---

## E1 — DH23 Prop 9.6 (`lgmolect`), case (4), is false for 0 < γ ≤ 1/2

**Status:** CONFIRMED. Ledger: FINDINGS F69b. Research note: `docs/research/dh23-prop96-case4.md`. Independent
adversarial referee report: `docs/research/dh23-prop96-referee.txt`.

**Statements affected.** All are false for 0 < γ ≤ 1/2.
- **DH23 Prop 9.6 `lgmolect`, estimate (finalcount), L1818–L1822.** Its proof, case (4), is at L1883–L1886.
- **DH23 Prop `kqmainest2`, L1681–L1690.** It is proved from Prop 9.6 (L1823–L1826) and fails on molecules of bounded
  size.
- **TARGET Prop `lgmolect`, L2192–L2197.** Its proof (L2197) says that for perfect components it "is exactly the same
  as Proposition 9.6 of [DH23]".
- **TARGET (finalcount1), L2114,** at R = 1.

TARGET claims its main theorem for all γ ∈ (0, 1) (L314). The physically distinguished value γ = 1/2 (L325) lies in the
failing range.

### The source text

DH23 Prop 9.6 (L1819–L1821) asserts, for each component 𝕄₀ of the final molecule 𝕄_fin:

> 𝔄₀ ≲ ∏_v^{(α)} L^{−(γ+3η)/2+κ_vη} R_v^{−1} · L^{(γ₀+2η²)V_β − (2γ₀+5η²)G} · L^{−η⁵ρ₀}.

For a component with V_α = 0 and V_β = 2 (an even component, G = 1), the right side is at most a negative power of L.
The required estimate is 𝔄₀ ≲ L^{−η²−η⁵ρ₀}.

Case (4) of the proof (L1883–L1886) reads:

> (4) If V_α=0 and V_β=2, then choose all the chains of β-atoms and perform operation (d) to them. The resulting
> molecule 𝕄₁ is 4-regular and has at most two triple bonds. Therefore, by Proposition [moleprop4] (2), we know that
> either 𝔄₁ ≲ L^{−η/5} or 𝕄₁ is formed by removing the two joints of a vine and adding one new bond between the pair
> of atoms connected to each joint. […] In the latter case, **an enumeration shows that 𝕄₀ must be a vine and is thus
> LG** due to Proposition [finalmole], so we may now perform operation (c) to the chains of β-atoms in 𝕄₀. […] we get
> that 𝔄₀ ≲ L^{−η/2}, so (finalcount) again follows by interpolation.

### What is wrong

The enumeration claim at L1885 is false: 𝕄₀ need not be a vine. The smallest non-vine case-(4) components are:
- the 4-atom Q-block;
- three 5-atom T-blocks;
- five 7-atom T₁-blocks;
- a 9-atom block.

The source argument (vine ⇒ large gap ⇒ operation (c) gains) uses only the large gap, not the vine shape. So it covers
every 𝕄₀ whose β-gap is large, but not a non-vine component whose two β-atoms come from small-gap cuts.

For γ ≤ 1/2 a small gap makes the β-constraints void, and the count of such a component is of order 1, not
L^{−η²}. The Q-block is repaired by reading vine (II) as including m = 1 (E3 below). The T-blocks give the
counterexample.

### The counterexample: the necklace N_m

**Molecule.** Take joints w₀, …, w_m.
- **T-bead B_i, for 1 ≤ i ≤ m.** It lies between a = w_{i−1} and b = w_i, with interior atoms e_i, g_i, f_i and bonds
  - a→e, b→e,
  - e→g (twice),
  - g→f (twice),
  - f→a, f→b.

  It is a triangle of double bonds with both copies of one double bond subdivided by the two joints.
- **Odd bead B₀.** It lies between w_m and w₀, with interior atoms o₁, o₂ and bonds
  - w_m→o₁, w₀→o₁,
  - o₁→o₂,
  - o₂→w_m, o₂→w₀.

N_m has n = 4m + 3 atoms and 8m + 5 = 2n − 1 bonds, and no triple bond. Two atoms have degree 3: o₁ with
(in, out) = (2, 1) and o₂ with (1, 2). Every other atom has (2, 2).

**Facts** (proofs in the research note, §3, each machine-checked):
1. **Prime couple (Lemma 3.2).** N_m is the molecule 𝕄(𝒬) of an explicit prime, non-degenerate couple 𝒬, directions
   included.
   - **Construction:** a spanning forest of two trees rooted at o₁, o₂ gives the PC bonds. The other bonds become LP
     bonds with a leaf at each end. Set ζ_v = + iff the parent bond points v → parent.
   - **Primality:** there is no triple bond.
   - **Mechanical check** (`necklace.py`, m ≤ 20): 𝕄(𝒬) is rebuilt from 𝒬 bond by bond, and non-degeneracy is checked.
   - **Referee check:** the referee re-derived this with randomized couple constructions up to m = 20. In TARGET,
     putting all nodes in layer 0 gives a canonical layered couple in 𝒞₁ satisfying (a)–(f) of L2096–L2109.
2. **No vine-like objects (Lemma 3.3).**
   - The blocks of N_m are exactly the runs B_i ∪ … ∪ B_j with joints w_{i−1}, w_j.
   - There are no hyper-blocks, and no block is isomorphic, even undirected, to any vine (I)–(VIII) with any number of
     rungs, or to the Q-block. One bead has 5 atoms and no vine has 5 atoms; a longer run has an interior cut atom,
     and no vine template has one.
   - Hence the vine collection 𝒞 is empty (DH23 Lemma 8.1), 𝒬_sub = 𝒬_sk = 𝒬, 𝕄(𝒬_sub) = N_m, Δ_sub = 0, and there
     are no hinge atoms.
   - **Mechanical check:** `vinefree.py` enumerates all atomic groups for m ≤ 4.
3. **Stage 2 (Lemma 3.4).** Take the decorations where every joint w_i is small-gap, with its designated pair the two
   bonds in the next bead and gap ±r, and every other atom large-gap. Then, for **every** order of Step 3:
   - Steps 1, 2 and 4 do nothing;
   - the first Step-3 cut is an α-cut and every later one is a β-cut;
   - the final components are the beads;
   - for m ≥ 3, some T-bead component has V_α = 0 and V_β = 2, so it falls in case (4).

   **Mechanical check** (`cuts.py`): all 24 orders for m = 3 and all 120 for m = 4. For m = 2 the conclusion fails, as
   expected.

**Count of one T-bead component (Lemma 4.1).** Fix d ≥ 3, 0 < γ ≤ 1/2, δ ∈ (0, 1/2], and the β-gap r = e₁/L. The
small-gap label is R = L^{−1}, which is allowed (DH23 L1752).

Let 𝕋 be the T-bead with:
- ε-atoms e, g, f and β-atoms b, b′;
- bonds b→e (x), b′→e (x′), e→g (p, p′), g→f (q, q′), f→b (y), f→b′ (y′);
- c_e = c_g = c_f = 0, c_b = r, c_{b′} = −r.

Then y = x − r, y′ = x′ + r, p′ = x + x′ − p and q′ = x + x′ − q. The vectors x, x′, p, q are free, so χ(𝕋) = 4.

The resonance factors are:
- Γ_e = 2(p − x)·(p − x′);
- Γ_e + Γ_g = 2(q − x)·(q − x′);
- Γ_b = 2x·r − |r|²;
- Γ_{b′} = −2x′·r − |r|²;
- ΣΓ = 0.

These identities are checked by `count_check.py`.

Draw x, x′, p, q from the balls of radius 1/4 around 0, 10e₁, 10e₂ and 10e₃.
- **Large-gap constraints hold.** Every opposite pair at e, g, f differs by at least 8.
- **The β-constraints hold automatically.** We have |Γ_b − β_b| = 2|(x − x⁰)·r| ≤ |r|/2, and likewise for b′.
  Moreover |r| = L^{−1} ≤ λ := δ^{−1}L^{−2γ} **exactly because γ ≤ 1/2**. So the width-λ β-constraints are void for
  the whole family.
- **Pigeonhole.** The family has at least cL^{4d} members, and (Γ_e, Γ_g) ranges over [−2000, 2000]². So some λ-cell
  contains at least c′δ^{−2}L^{4d−4γ} members. One more halving fixes β_f, since Γ_f = −ΣΓ_rest.

Hence 𝔠(𝕋) ≥ (c′/2)δ^{−2}L^{4(d−γ)} and

> **𝔄(𝕋) ≥ c_d (C⁺)^{−4},** a constant independent of L.

**Inheritance (Lemma 4.2).** Every member of this family is the restriction to 𝕋 = B₂ of a decoration of N₃ in the
class above, satisfying DH23 Remark `subcondition` and `kqmainest2` (i)–(ii):
- the other beads use the same construction shifted by 100·i·e₁;
- the odd bead uses, for example, s = 300e₁, s′ = 400e₁, t = s − r, t′ = s′ + r, u = s + s′ + 10e₂;
- non-resonance holds because every opposite pair has a nonzero gap.

**Contradiction with DH23 Prop 9.6 (Prop 4.3).** The T-bead component of N₃ is a case-(4) component of 𝕄_fin in every
Step-3 order, with 𝔄₀ ≥ c_d(C⁺)^{−4}. Prop 9.6 demands 𝔄₀ ≲ L^{−η²−η⁵ρ₀} with ρ₀ ≤ 5. This is impossible for L large.
The same component is a perfect component in TARGET, so TARGET `lgmolect` (L2193) fails too.

**Contradiction with `kqmainest2` (Prop 4.4).** Let m ≥ (3d+1)η^{−6}. Given r the beads are independent, so

> 𝔠(N_m) ≥ [(c′/2)δ^{−2}L^{4(d−γ)}]^m.

The right side of `kqmainest2` is (C⁺δ^{−1/2})^{4m+3} L^{(d−γ)(4m+3)} L^{−η⁶ρ}, with Δ_sub = 0, ∏𝔛 = 1 (there is no
ladder) and ρ ≥ m + 3. The ratio of left to right is at least

> [(c′/2)(C⁺)^{−4}]^m (C⁺)^{−3} δ^{3/2} L^{η⁶(m+3) − 3(d−γ)} ≥ c(m)·L → ∞.

TARGET (finalcount1) at R = 1 fails the same way. It also asks for L^{−4η⁶p_sb} with p_sb ≥ m + 1, so it fails once
4η⁶(5m+4) > 3(d−γ).

### Scope

- **Not refuted:** TARGET's main theorem, DH23's main theorem, and TARGET `layergarden` as a statement.
- **Why the necklaces do not refute them:** these couples are few (C^n of them), and their contribution per couple,
  hence per congruence class, is heuristically about (Cδ^{1/2})^n L^{−γ(2d−1)}. That is a fixed negative power of L.
  (The research note's earlier O(L^{γ−d}) is right only at γ = 1/2; corrected by the γ ≤ 1/2 research packet,
  /home/scott/wt-scratch/research-gamma-half/NOTES.md, Q1.)
- **What is broken:** the proof chain, at the intermediate statements listed above.
- **Why no repair inside stage 2 works:** the only slack in a necklace is that of the first α-cut, of size
  R^{d−2}L^{−3η}, and a necklace with ≫ η^{−6} beads exhausts it.

### Related findings

- **F73: the analytic per-class bounds fail too.** DH23 `kqmainest1` (L1632–L1640) and TARGET (finalsbest2) (L2078)
  also fail on the necklace couples for 0 < γ < 1/2, and for γ = 1/2 with δ small.
  - On these couples K_𝒬(t,t,k) = ζ(𝒬) 2^{−n} δ^{2m+2−d} L^{−γ(2d−1)} [A_m + o(1)], with n = 4m + 3 and A_m ≠ 0 for
    explicit data. There is no gain per bead.
  - TARGET (finalsbest2) fails once η⁶(4m+3) > γ(2d−1).
  - So no counting-only repair suffices.
  - Note: `docs/research/kqmainest1-necklace.txt`. Status: CANDIDATE (derived; error terms not fully explicit).
- **F75: the range γ ∈ (1/2, 1) is closed by a new argument,** confirmed by an independent referee
  (`docs/research/case4-gamma-above-half.txt` and `…-referee.txt`).
  - Operation (c) on the first β-chain, using DH23 Lemma A.3(1).
  - Operation (d) on the second β-chain.
  - At most two (Y)-sequences.
  - The γ > 1/2 branch of DH23 Lemma A.2(3).

  Together these give 𝔄₀ ≲ δ^{−1}(log L)^C L^{−10η}, for η ≪ γ − 1/2.
- **E3 (F72): the Q-block.** DH23 Def 5.1 / vine (II) (L1421) must include the one-double-bond case m = 1. Without it,
  Q-bead necklaces break the same four statements for all γ < 2/3.

### Consequence for the formalization (Scott, 2026-11-04)

Scott chose to do both:
- **Restrict the endpoint.** Restrict the formal endpoint to γ ∈ (1/2, 1) by versioned successors of the frozen
  statements, `main_v2` and the affected Wave B anchors. Their exact text is submitted for approval separately.
- **Research the repair** for γ ≤ 1/2 in a separate research packet.
- **Write to the authors.** The letter draft is `docs/review/LETTER-DENG-HANI-DRAFT.md`.

**Repair route (research, not yet independently refereed).** The γ ≤ 1/2 research packet
(/home/scott/wt-scratch/research-gamma-half/NOTES.md) proposes that the chain can be repaired without a new
analytic estimate:
- T-type blocks are exactly neutral and fit the hypotheses of the existing DH23 Cor `sumintest3` / TARGET Prop
  `sumint` (Theorem N; checked on all 4446 directed T-type classes up to 15 atoms).
- So they can be spliced in stage 1 as an enlarged vine family, after the combinatorial extensions of Lemma 8.1,
  `subsetvc`, Props 9.1, 9.5 and 9.6.

**Independent referee (2026-11-04, /home/scott/wt-scratch/research-gamma-half-referee/REPORT.md): the route is sound.**
No counterexample was found.
- **Analytic core: CONFIRMED.** T-vines meet the hypotheses of `sumintest2`/`sumintest3`/`sumint` literally:
  8892/8892 cases up to 15 atoms and 14928/14928 at 17 atoms; 800/800 mixed chains.
- **Combinatorial extensions:** confirmed on all data up to 19 atoms, heuristic beyond. A written rung-locality proof
  is still needed.
- **Still open:** TARGET with R ≥ 2 gardens, the flower/parametrix sections, and Prop 10.4(1) for T∖ℓ.
- **The note's own errors (E1–E5 of the referee report)** do not affect the route.

In the Lean development, the γ-sensitive input `FinalCountGate` (TARGET finalcount1) is a separate hypothesis of
`layergarden_of_spine` and `layergardenFlower_of_spine`, and it is proved only under 1/2 < γ.

---

## E4 — TARGET `vineest` Step 3, L1846: replacing ε by 1 "by trivial summation" fails for long vine chains

**Status:** CONFIRMED as a gap in the argument. The statement survives with a corrected argument, which is proved in
Lean.
- Found by the V5 vineest prover; confirmed by the DEGEN-VINE packet.
- Ledger: GAP.degenerate.vine / FINDINGS F21.
- Lean: `/home/scott/wt-scratch/degen-vine` (namespace `WaveTurbulence.DegenVine`, HANDOFF.md §6).

**Location.** TARGET L1846, in Step 3 of the proof of Prop `vineest`, just after (tildeK2). DH23 L1448 and
`extradegen` (DH23 L1979–L1989) make the same kind of claim: "treat the rest of the variables using the same arguments".

**Source text (TARGET L1846):**

> Here note that once we specify r = k_{u21} − k_{u22} = k_{u1} − k_{u11} ≠ 0, we may replace ε_x in (tildeK2) by 1,
> since if any ε factor is not 1, this would imply some restrictions on the relevant variables (such as x_j^i = 0 or
> y_j^i = 0, or u_1^i + u_2^i − u_3^i = 0 etc.), which allows us to sum over these variables trivially and gain an
> extra power L^{−0.1γ₀}.

**Why the stated argument fails.** Consider a vine chain with M vines, where some ε-factor equals 0 because one affine
constraint holds.
- Summing trivially (absolutely) over the remaining variables of the restricted subspace costs L^{(M−1)d}.
- The budget of (vineest2) for these variables is L^{M(d−γ)}.
- The trivial sum therefore exceeds the budget by L^{Mγ−d}, which grows once **M > d/γ**. For example, at d = 3 this
  is M ≥ 7 for γ = 1/2 and M ≥ 4 for γ = 0.9.
- Chains of this length do occur, since the vine-chain length M is up to order N_{p+1}^4.
- The loss comes from summing absolutely: that gives up the oscillatory gain L^{−γ} per variable, which the `sumint`
  bound needs.

**The gap cannot be closed by quoting `sumint`.**
- The indicator 1[x_v = 0] is not an admissible `sumint` weight: its S^{30d,30d} norm is about L^{31d}.
- Deleting the restricted rung breaks the invertibility of T₁ and `Admissible` (ii)/(iii).

**Correct argument (proved in Lean).**
1. Write ε = 1 − 1[k₂ = k₁] − 1[k₂ = k₃].
2. Each indicator of an affine constraint on the lattice ℤ_L^d is an average of characters (Fourier inversion on the
   finite group), so it is a mixture of linear input phases with total mass 1. Over n nodes, ε is a mixture of mass at
   most 3^n (`exists_eps_mix`).
3. The `sumint` kernel bound is uniform in the linear input phases: `exists_source_static_power_bound` holds for all
   p, ν, r. The norm `XNorm00` is a supremum over the output. So the recombination step of the `sumint` proof
   applies, multiplied by the mixture mass (`sumintMixSignedDoubled`, unconditional).
4. Conclusion (`clockedBoundEps_of_restr`): the Step 3 bound holds with ε, at a cost of a factor 3^{|I|} ≤ C^M. That
   factor is absorbed into C₁.

No L^{−0.1γ₀} gain is proved, and none is needed for (vineest2).

**Suggested rewording of L1846.** "ε_x is a combination of at most 3^n indicators of affine constraints. Each indicator
is an average of linear input phases, to which the proof of Proposition `sumint` applies verbatim, since its kernel
bound is uniform in the linear phases. So ε may be replaced by 1 at the cost of the constant 3^n ≤ C^M."

**Effect on the formalization.** None on any frozen statement. The V5 Step 3 endpoint is stated with ε, in the
literal form, using the corrected argument.

---

## E5 — TARGET (finalsbest1), L2075–L2079: "very easy with Proposition `ladderl1new`" does not follow from that proposition as stated

**Status:** CONFIRMED as a gap in the argument. The estimate itself is true, and a corrected proof is in Lean.
- Found by the S3c COARSE-SPLICED prover.
- Lean: `/home/scott/wt-scratch/coarse-spliced`:
  - `coarseSplicedGate : WTPrefix CoarseSplicedAt`, via a verbatim copy that is checked against the pinned statement;
  - `ladderL1Gate`, the intermediate bound described below.

**Location.** TARGET L2075–L2079. Estimate (finalsbest1) is
|K_{G_sb}| ≲₂ (C₁√δ)^{n_sb} L^{−η·g_sb + 80d(ρ_sb + q_sk)}.

**Source text (L2079):**

> The proof of (finalsbest1) is very easy with Proposition [ladderl1new], which we describe below.

**What is wrong.**
- Prop `ladderl1new` (redladder2, L1978–L1992) bounds a single ladder's local kernel. It holds with all outside times
  and boundary data fixed, over the time-ordered domain, uniformly in the outside times.
- Two ladders adjacent in the tree and lying in the same layer are coupled by the time-ordering indicator. So the
  integrand of K_{G_sb} does not factor over the maximal ladders.
- Hence a product of `ladderl1new` bounds, used as black boxes, does not bound K_{G_sb}. Fixing the outside times of
  one ladder fixes times inside the other's ordering constraint, and the uniform bound gives no way to integrate them
  out.

**Correct argument (proved in Lean).**
1. Use the intermediate quantity from inside the proof of `ladderl1new`: the integral over the unit time box, with the
   ordering dropped, of the modulus of the finite lattice sum (S3b's `kernel_core`).
2. Bound that quantity by the same right-hand side (`ladderL1Gate : WTPrefix LadderL1At`). It is multiplicative over
   disjoint ladders, since dropping the ordering decouples them.
3. Glue over disjoint, hinge-free maximal ladders (`splicedKernel_le_classes`), and count the classes.
4. Select the ladders combinatorially (`selection_claim`). This uses the pairwise disjointness of distinct maximal
   ladders under the B2 ladder definition.

**Effect on the formalization.** None on any frozen statement. LG-SPINE's `CoarseSplicedGate` input is proved.
`ladderL1Gate` should be merged with `ladderDecayGate` at the universe rebase.

---

## E2 — further errata (to be transcribed before release)

The remaining confirmed and candidate findings are in `docs/FINDINGS.md`:
- F61 (sign);
- F68, F78, F80 (fixed before the freeze);
- F70;
- F72, the m = 1 vine (II), see E3 above;
- the TARGET L1519 constant;
- the TARGET L2013–L2014 identity at end rungs;
- the TARGET L2034/L2036 exponent;
- the TARGET (sumintI1)/(tildeK2) factor 2 in the phase;
- the DH23 L1904 (increv3) sign;
- the DH23 L1912 operation count;
- DH23 Prop 10.2's missing size hypothesis.

They are moved here as each is confirmed by its writer and by an independent verifier.
