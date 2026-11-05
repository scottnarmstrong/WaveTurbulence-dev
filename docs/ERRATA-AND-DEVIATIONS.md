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

**Second research pass and second referee (2026-11-05).** Notes:
/home/scott/wt-scratch/research-gamma-half-2/NOTES.md. Report:
/home/scott/wt-scratch/research-gamma-half-referee-2/REPORT.md.
- **Confirmed:** the R ≥ 2 gardens, the flower and parametrix sections, Prop 9.6 case (5), the ylem1′ list, and a
  Lean-ready predicate `IsTVine` for the enlarged γ ≤ 1/2 vine family.
- **Rung-locality:** proved for all sizes after two repairs the referee supplied (a patch to Lemma 1.14(c), and a
  parity argument for hyper-member removal).
- **Still open for all sizes:** one structural fact used by `layervine`, checked up to 21 atoms.
- **Not yet in Lean:** the base cases need a verified enumeration of T-vines with at most 13 atoms.

**Third research pass and third referee (2026-11-05).** Notes:
/home/scott/wt-scratch/research-gamma-half-3/NOTES.txt. Report:
/home/scott/wt-scratch/research-gamma-half-referee-3/REPORT.md.
- **Proved for every size, and confirmed by the referee:** the `layervine` structure, i.e. spine, pendants and at most 3
  ladders. Each vine's pieces form a cactus with at most one triangle. Checked independently on all shapes with at
  most 41 atoms (3060 labelled cases).
- **Corrected statements written out in full:** Lemma 1.14(c′) and Cor 1.16′ (the sources keep the adjoint bond:
  TARGET L2140, DH23 L1775).
- **Referee verdict:** the γ-dependent vine family (`IsTVine` for γ ≤ 1/2) can go to the author for approval.
  Remaining caveats:
  - the base enumerations (classification up to 13 atoms; 57 base pairs up to symmetry) are Python checks, not yet
    kernel certificates;
  - confluence (note 2 Lemma 1.4) is still a Lean obligation.
- **DH23 `subsetvc` (L2128) is incomplete.** Its list of sub-objects omits two blocks:
  - the block VC:I+I, which occurs in drawn vine (IV) (referee 2);
  - the block vine (V), which occurs in drawn vine (VII) on atoms {4,…,8} (referee 3).
  The corrected list is Cor 1.16′.

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

## E6 — TARGET L2187 ("easy to check … preserved"): the invariant fails under the blanket Operation 2 cut

**Status:** CANDIDATE. The computation is explicit, and an independent check is pending. Found by the FINALCOUNT G3
prover (/home/scott/wt-scratch/finalcount-g3/HANDOFF.md).

**Location.** TARGET L2187: the invariant 4V − 2E − 2(V_α + V_β) is "easy to check" to be preserved under the stage-2
operations. Operation 2, the triangle cut, is stated as a blanket cut at L2142.

**Configuration.**
- Take a triangle (v₁, v₂, v₃) whose atom v₃ is a degree-2 β-atom created by an earlier cut.
- The blanket Operation 2 cuts all three triangle atoms. At v₃ this leaves v₃ intact and creates a fresh isolated
  β-atom of degree 0.
- Then ΔV = 0, ΔE = −3 and Δ(V_α + V_β) = −1 + 3 = +2.
- So Δ(4V − 2E − 2(V_α + V_β)) = 0 + 6 − 4 = **+2**, and an extra imperfect component appears.

**Repair.** DH23's own formulation (L1777, "if deg v_j ≥ 3 then we cut") avoids this. The Lean model follows DH23, and
deletes the degree-0 remainder (`Cls.ghost`).

**Effect on the formalization.** None on any frozen statement.

---

## E7 — DH23 L1794 (Prop 9.4, triangle with ΔF = 1): the pair count assumes a nonzero fixed difference

**Status:** CANDIDATE. The construction is analytic; it has not been checked in Lean. The final bound is unaffected.
Found by the FINALCOUNT G2 prover (/home/scott/wt-scratch/finalcount/HANDOFF.md).

**Location.** DH23 L1794: "(triangle1) holds for some j".

**Configuration.**
- The v₃ triple need not be SG; L1777 requires SG only for j ∈ {1, 2}.
- Take v₃ with k_{ℓ₁} = k_{ℓ₂} = k free in the unit ball.
- Then there are about L^d pairs. This exceeds the source's δ⁻¹L^{d+1−2γ} for γ > 1/2 and L large.
- For d ≥ 3 and R ≤ L^{−γ+η}, the final ΔF = 1 bound still holds, by exponent arithmetic alone.

The Lean proof assumes nonzero gaps at all three triangle atoms (`hnz`), a reading wider than the source's.

---

## E8 — DH23 L1862–L1874 (Prop 9.6, cases (1)–(3)): "operations (a), (b) only on ε-atoms" is incomplete

**Status:** CANDIDATE exposition gap; the statement is not false. Found by the FINALCOUNT-G8 prover.

**Problem.** The argument also needs degree-1 α- and β-atoms to be deleted at no cost. It is possible, since fixed
charges determine their bond, but the text does not say so.

**Effect on the formalization.** The Lean proof adds this free deletion.

---

## E9 — TARGET `finalmol` (L2185, L2187) fails as stated once tame-atom removals occur (remtame case (ii))

**Status:** CANDIDATE. The computation is explicit, and an independent check is pending. Found by the FINALCOUNT G3
prover (/home/scott/wt-scratch/finalcount-g3/HANDOFF.md, Session 4).

**Location.** TARGET L2185 (`finalmol`): the final molecule has "at most R imperfect components", and "no α- or β-atom is
ZG". Its proof at L2187 says the invariant 4V − 2E − 2(V_α + V_β) is preserved.

**What goes wrong.**
- **The invariant rises by 4.** A degree-4 ZG tame atom removed under Remark `remtame` case (ii) changes the invariant
  by **+4**: V − 1 and E − 4.
- **The imperfect-component bound fails.** With t such removals it becomes **R + 2t**, not R. TARGET's later remark
  `remtame2` (L2218) adds 2 imperfect components per removal, which is consistent with +4. So the source's own later
  bookkeeping contradicts L2185/L2187 as stated.
- **Degree invariant.** The "ε-atoms have degree ≥ 3" invariant fails for a neighbour joined to the removed atom by two
  bonds.
- **ZG α/β atoms.** `remtame` case (i) creates ZG α/β atoms, contradicting L2185's "no α- or β-atom is ZG".

The exact configuration is in the G3 HANDOFF.

**Assessment.** The final estimates may survive, because remtame2 accounts for the extra components. But `finalmol` as
stated is false in TARGET's setting with tame atoms.

**Effect on the formalization.** The counting chain models TARGET's setting with an explicit removal step and the bound
R + 2t. DH23's setting has no non-hinge ZG tame atoms (`DegenSG`), so remtame never fires there.

---

## E10 — DH23 L1814 (proof of Prop 9.5, vine components are LG): "the vine is not changed" although its joints are cut

**Status:** CANDIDATE exposition gap. Found by the FINALCOUNT G3 prover.

**The problem.** The proof says a final vine component is the vine from stage 1, "not changed". But its joints are cut
atoms. Identifying the component with an object of 𝕄₀ needs two arguments:
- **An identification argument.** The component's non-ε atoms are its two joints, and the cut halves map injectively
  to distinct ancestor atoms. The two joints cannot be the halves of one cut atom: the component would then be closed
  under adjacency, hence all of 𝕄_sub, which contradicts the two odd atoms.
- **The case of a hyper object.** When the joints' other halves are joined by a bond, the component is a hyper object
  (HV), not a VC.

The Lean proof adds both arguments.

---

## E11 — TARGET Remark `remtame` case (i) (L2152, L2218): "cut at v and proceed normally" / "modified trivially" is not trivial

**Status.** CANDIDATE. It has an exposition-gap part and an erratum part. The research, with mechanical checks, is in
/home/scott/wt-scratch/research-remtame-i/NOTES.txt. The ruling is R27.

**Location.** TARGET L2152, case (i) applies "if d(v) < 4, or if some component contains exactly one atom adjacent to
v". The text says: "the values of k_ℓ for ℓ↔v must all be fixed in the given decoration, so we always have enough gain
whether the resulting α- or β-atoms have zero gap. We then cut at v and proceed normally." TARGET L2218 adds: "In case
(i) the proof is modified trivially."

**What goes wrong.**
- **(a) "Values fixed" is false in one configuration.** A component of M − v can meet v only through an
  opposite-direction double bond to a single atom u. Conservation then puts no constraint on the shared value.
  - This is harmless. In that configuration M − v has c ≤ 2 components, so Δχ ≤ −2 and case (ii)'s gain applies.
  - The correct split is "pinned, or c ≤ 2". This is DH23 §10.5(4)'s "bridge, or Δχ ≤ −2".
- **(b) The pin does not survive the cut.** Where the values are pinned, they are pinned by the charges of the
  molecule before the cut. After the β-cut, the zero-gap half of v can lie in a component whose own charges do not pin
  them. TARGET's product over components (L2203) cannot use the pin.
- **(c) Prop 9.6 (`lgmolect`) is false for a component with an unpinned zero-gap β-atom.**
  - **Counterexample.** X = {a, b, c, v₁} with bonds c→a ×2, a→b, a→v₁, v₁→b, b→c ×2. It is perfect, with V_α = 0 and
    V_β = 1, and conservation forces gap(v₁) = 0.
  - A pigeonhole count gives 𝔄(X) ≥ c·C₁⁻⁴. But (finalcount) requires L^{−γ₀−3η²−η⁵ρ}.
  - So "cut and proceed normally" can feed Prop 9.6 a component it does not cover.

**Repair (used in Lean).** Erase v instead of cutting it, exactly as DH23 §10.5 does (L1985: "we shall not make any
cut at non-hinge degenerate atoms"). Then:
- the nonzero-gap property of β-atoms (N1) and the ι property (N2) hold as stated;
- the count of imperfect components becomes R + Σ(deg v_e − 2);
- an erasure-deviation lemma gives the gain: pinned, factor 1; unpinned, deg 4 and c ≤ 2.

The final bound (finalcount1) is unaffected.

---

## E12 — DH23 Prop 9.6 proof, case (1) (L1884): the odd-component argument is written for a degree-1 odd atom

**Status.** CANDIDATE exposition gap. Found by the FINALCOUNT-G8 prover; the details are in
/home/scott/wt-scratch/finalcount-g8/HANDOFF.md.

**Location.** DH23 L1884, case (1) of the proof of `lgmolect`.

**Configuration.**
- Take an odd component whose two odd atoms both have degree 3, with all other atoms of degree 2 or 4, and no α- or
  β-atom. So w = 0 and E = 2V − 1.
- Such components occur, because DH23 `subpro`(b) (L1734) has two degree-3 atoms that need not be cut.
- Here 𝔄 ≲ 1 (Prop 10.1) does not give (finalcount): its right side carries L^{−η⁵ρ₀}.

**Repair (used in Lean).** Use the first statement of Prop 10.2 (no triple bond and E = 2V − 1 give
𝔄 ≲ L^{−3γ₀/5}).

---

## E13 — TARGET L2101 (selection of C₂): a DV whose two vines are both SG

**Status.** CANDIDATE exposition gap. Found by the FINALCOUNT G3 prover; see /home/scott/wt-scratch/finalcount-g3/HANDOFF.md,
SESSION 6.

**Quote.** "if both vines (V) forming this DV are SG, then we select only one of them, plus all the maximal SG vine-like
proper subsets of the other."

**The gap.** The text does not say what happens if the selected vine is contained in a larger SG object. For example,
U could be an HV whose added bond is the shared joint bond. The unselected vine could then survive as an SG vine
component, contrary to L1806 and DH23 L1814.

**Reading used in Lean.** The DV rule is applied among the maximal objects (`UnselOK`): the partner of an unselected
vine is a VC member of C₂. No concrete counterexample is known.

---

## E14 — TARGET Prop `vineest` (L1742–L1752) and `sumint`: the time domain when a lower child is a leaf

**Status.** CANDIDATE erratum, minor. Found by the V5 VINEEST prover.

**The issue.** The domain 𝔅 is "the intersection of {t_{u₁} > max(t_{u₂₁}, t_{u₂₂})} with the product of three unit
intervals". That is not the actual domain of the kernel when u₂₁ or u₂₂ is a leaf, because a leaf carries no time
variable of its own.

**Repair (used in Lean).** Evaluate at the lower end of the unit interval, then take an order-0 time trace
(`XNorm00Restr_trace`). This costs a constant `traceR η`, which is absorbed into C₁.

---

## E15 — further exposition points (no false statement; recorded for completeness)

- **TARGET L1960 (redvine → redvine2).** The text records "a loss of at most C_0^n" for node centres, then omits it in
  (redvine2), whose prefactor is (C₁√δ)^{n−n_sb}. When n = n_sb the exponent is 0, so the loss cannot be absorbed
  there. The Lean interface carries C₁^{n_sb} explicitly (R24 D3).
- **TARGET L1846–L1847 (vineest Step 3, layer failure).** The time order t_{u4} < t_{u2} comes from layers, not from a
  parent–child relation. It holds up to a null set (R20).
- **DH23 L790 (closed ladder cells).** The text does not say which of the two parametrizations of a closed cell
  defines its gap (R26). This is harmless: DH23's Prop 10.4(2) proof (L1961–L1977) treats such a post under case (I).
- **DH23 L1802 (Prop 9.4, κ = 50).** The text does not say whether the ι ball is fixed. For a "sibling" hit (the first
  cut of the same triangle) it is centred at a variable. The relative-ball count still gives the same bound
  (G2-SIBLING).
- **DH23 L1861 (operc).** "𝔇 ≲ 1 + δ⁻¹R⁻¹L^{−γ}" is really L^{γ−1} + δ⁻¹R⁻¹L^{−γ}. This is an over-estimate, not an
  error.
- **TARGET L2424 (`treelemma` (1)).** "for each j there exists j′ < j" fails for j = 1. This is a trivial slip in a
  part that is not used.
- **TARGET Operation 3, after a tame-atom erasure.** A neighbour of the erased atom can become an SG ε-atom of
  degree 2, which Operation 3 (degree ≥ 3) never cuts. The text is silent on this (G3). It is being tracked under the
  DAMAGED ticket.
- **TARGET Operations 2/4, ι property ("dead hit").** If both halves of the earlier cut that gives κ_v = 50 are later
  deleted by triangle operations, the ι ball centre is no longer a parameter of the current molecule. The Lean step
  lemmas require the hitting cut to be carried by a present atom (G3).

---

## E16 — TARGET L2152: "a ZG v₃ in Operation 2 must be tame by subpro (3)" is false when v₃ is a hinge atom

**Status.** CANDIDATE. The prover wrote it, and an independent refute-first referee re-derived it (R29).
- Research: /home/scott/wt-scratch/research-damaged/NOTES.txt §3.2.
- Referee: /home/scott/wt-scratch/research-damaged-referee (`ref_hinge.py`).

**Location.** TARGET Remark `remtame`, L2152: "We will also assume that no atom v₃ in Operation 2 … is ZG; in fact, if
any such atom v is ZG, then it must be tame by Proposition subpro (3)".

**Counterexample.** Take a couple of order 6, with its skeleton molecule M(Q_sk) as follows:
- 6 atoms and 11 bonds;
- degrees (3, 3, 4, 4, 4, 4);
- no loop and no triple bond;
- prime, with no mini couple, mini tree or sibling pair.

**Why it is a counterexample.**
- **The vine.** The only block is {u1, u2}. It is a (CL) vine (I-a), non-root (joint degree sum 8 > 6), and SG
  under the decoration, so stage 1 merges it into a hinge h.
- **The decoration.** Take decorations with D = E. Then M(Q_sk) has no zero gap, so no atom is degenerate and h is not
  tame. The referee found this in 300 of 300 random decorations.
- **The triangle.** In M_sb the unique Operation-2-eligible triangle is (P, u21 | v₃ = h). Its pair at h is a crossing
  pair with gap ±(D − E) = 0.
- So v₃ is ZG but not tame.

**Consequence.**
- **The literal cut breaks a needed property.** Cutting h along that pair leaves a degree-2 β-atom with zero gap. At a
  charge-0 degree-4 atom, complementary pairs have opposite gaps, so this breaks the nonzero-gap property of β-atoms
  that DH23 Prop 9.6 needs.
- **DH23 has the same gap.** It appears in DH23 L1777 against L1985, under DH23's reading that "SG triples are fixed".
- **A related gap.** With 0 < |D − E| SG, Operation 2 cuts h along a crossing (non-designated) pair. DH23 L1815's
  argument that vines are LG assumes hinges are cut along designated pairs. This is a CANDIDATE exposition gap at DH23
  L1815 / TARGET L2187.

**Repair (R29).**
- A triangle is eligible only if its v₁ and v₂ triples are SG, its v₃ pair has nonzero gap, and at each hinge the
  triangle pair is a designated pair. Other triangles are skipped, and their v₁, v₂ are cut in Operation 3.
- Tame atoms are never cut. A final Operation 5 erases each maximal connected tame cluster.
- Components that still contain tame atoms, or were damaged by an erasure, get a separate bound (`prop96_damaged`).

(finalcount1) holds with TARGET's exponents for 1/2 < γ < 1.

---

## E17 — TARGET L2152/L2218 (remtame) and L2193/L2197 (finalmol, R = 1): single-atom erasure and "imperfect = odd"

**Status.** CANDIDATE. Refereed with R29.

**(a) Single-atom erasure leaves components with no usable bound.** Two graph-level examples:
- **C1.** The chain R1–e⇄u⇄v⇄f–R2, with all of e, u, v, f tame. Erasing e and f leaves an isolated tame double bond
  {u, v} whose shared value is unpinned. Then A ~ L^γ.
- **C0.** A similar chain isolates a degree-0 tame atom, so A = 1, while TARGET's R = 1 bound requires L^{−η⁵}.

The repair is cluster erasure at the end of the run (R29, E16).

**(b) TARGET L2193/L2197.** For R = 1 these lines set Z = 0 and call the imperfect components "odd". That
identification is false by TARGET's own text: L2189 says "exactly R if R=1", but L2218 says a case-(ii) removal
"increases the number of imperfect components by 2". The Z = 0 failure is shown at graph level only. Harmless.

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
