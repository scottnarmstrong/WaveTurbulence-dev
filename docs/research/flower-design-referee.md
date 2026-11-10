# Referee report on FLOWER design C (saved by wt-orch from the referee's final message, 2026-11-06)

## Referee report: design C ("stub excision with anchors")

**Verdict: ADOPT_WITH_FIXES.** The core of design C is right. The defects I found are local and each has a straightforward fix, but four of them must go into the AMEND-ST text before you hand out the work.

**REPORT.md was not written.** The harness blocks subagents from writing report files, so the full report is below. `<scratch>/research-flower-referee/` exists but is empty, and I edited nothing else.

**Pinned inputs.**
- I copied NOTES.md at first read (sha256 `6779f0a6…3c`, 263 lines); the hash was unchanged at the end.
- PendantBlock.lean is `05414d32…`. Gates, Defs, Stage1Interface, Stage1Gate and CLLocalTimes all match the packet's PINNED-INPUTS, so I audited the same versions it did.
- I re-ran the PendantBlock probe once with `nice -n 5 lake env lean`: it exits 0 and uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.
- Main moved from 657e877 to 05f0ab8 while I was working; the frozen definitions I read are read-only.

### 1. The excision identity: OK (exact for the plain clause without cutoffs), with two corrections
- **What I re-derived.** I checked it against `kDomainFix`, `fixPat`, `GenDecoration`, `zeta` and `epsDec`.
  - Cutting v_j's edges to its siblings turns the "children below s" constraint into caps s on the new sibling trees.
  - The edge from the stub's parent u to the stub keeps the floor τ_u > s, because exactly one end of that edge is free.
  - The branch set is unchanged and node signs are preserved, so ζ(G) and ε are unchanged. Anchors take the sign opposite to their slot.
  - The stub's phase and ε depend only on anchored labels, so they are constants of the outer sum. Excised roots and dChild nodes move their coupling, ε and phase to the outer sum.
  - Summing over the sibling labels κ gives a bijection between the decorations of Ĝ and those of the flower garden.
- **The floor claim is correct.** CLLocalTimes L74–79 keeps `t 1 < τ_b` only when the excluded child is a branch. Keeping f^pr as a branch stub therefore passes t1 = s to V5 as an external time, and the floor survives.
- **One obligation in this item.** V5's bound is an `XNorm00Restr` norm over the three external times, not a pointwise bound. A lemma that restricts it to t1 = s must be named in P5/P6.
- **Correction 1a: dParent.** If u is not the root, u has molecule degree 2 and its child v_j is a branch. So the proposed `Sound.stub_pendant` and the definition of the stub set are false for u. u is still in no block or ladder.
  - Fix: also cut the edge u–v_j. It carries no constraint, since both ends are fixed. v_j becomes a lone stub, and u becomes an ordinary stub with an anchored slot whose label is k_{v_j}, already determined, so no new sum.
- **Correction 1b.** When v_j or u is a child of an excised root, τ_r > s remains as a constraint on the outer τ_r integral.

### 2. Stubs are pendant: OK
- **Molecule structures.**
  - Blocks: shown by the probe.
  - Ladders: every rung is a double bond, so ladder atoms have degree ≥ 2.
  - Hyper-blocks: a hyper-block is a block after erasing one bond, so its atoms also have degree ≥ 2.
  - Garden molecule: leaf pairs with a root leaf give no bond, so the stub has degree 1, or 0 at a root.
- **Regular objects.**
  - Never in a regular couple: a subtree containing the stub has three leaves paired with three distinct anchors.
  - Never strictly inside a regular tree.
  - It can only be the lone-leaf position, which gives the two-time factor K*_T(·, s); no Dirac sits inside a regular object.
- I found no configuration that puts a stub inside a block, vine, ladder or regular object.

### 3. Canonicity and components: OK; REFUTATION for kind W
- **Canonicity.** `IsCanonG` and `CanonCriterion` transfer in both directions. Every newly incomparable pair is vacuous, because any leaf set containing a stub's subtree, or an anchor without its slot, is not completely paired.
- **Components.**
  - Each component has balanced signs and a connected molecule.
  - The kernel factors over components once the outer labels are fixed.
  - The count Bell(w)·(N+1)^w is absorbed for L large depending on Pm.
- **REFUTATION.** `GNode.IsDesc` is reflexive, so condition W-3 allows topOrder(U_j) = N_{p+1}+1. That violates `Stage1Carries.IsTrunc`, which requires every tree to have topOrder ≤ N_{p+1}.
  - Example: U_j has N_{p+1}+1 layer-p branches, T_j1 is trivial and T_j2 has one branch. Then W-1, W-2 and W-3 all hold, but U_j's component is outside LG's gate.
  - Fix: also excise the root for kind W.

### 4. Width: the count is wrong, but no widening is needed
- **Wrong count.** Kind Y with pattern dParent gives **12** trees per flower tree, not 8 (14 after fix 1a).
- **No widening needed.** Pm is fixed before L in `WTPrefixP`. Also R(p+1) ≥ ⌊(log L)^{40d}⌋, because the R sequence is monotone. So 14·Pm ≤ 10·R(p+1) for L ≥ L₀(Pm), and the flower adapter can simply choose that L₀.
- **Recommendation.** Drop the widening and leave LG's range alone. For the record, the only quantitative use of the constant 10 is in `NonregularNumericsP.GardenNum`, which is internal to LG. `FinalCountAt` has a genuine (R−1) term, but after normalization it nets to a gain, so extra anchors help.

### 5. Twists: OK, with one simplification
- Each component is a plain canonical garden, so it is a universe `CanonicalObject`. The universe's LF twist and `TwistClosed` therefore apply verbatim, which closes cx-flower's R53 gap.
- The component carriers are defined intrinsically, and `output_topOrder` preserves per-tree layer-p counts. Stubs and anchors are never touched by a twist (FT2/FT3), including the stub's sign.
- **FT4 is automatic.** Layers never increase from parent to child, every layer is ≤ p, and the stub sits in layer p, so every ancestor of a stub is in layer p. No TARGET (5) argument is needed.
- This is not literally TARGET's restricted flower twist: C uses the full twist relation on a different garden, which is legitimate and removes the special-node exclusions.
- V5 applies unchanged apart from the trace lemma in item 1. R58's lower-child slots simply take τ_c = s.

### 6. Couples by decapitation: OK, with a missing lemma and a misstatement
- **Correct.** The identity is exact, and the exponents check: loss δ²L^{2d+2γ} ≤ L^{100d}, δ²·δ^{2ν(N−2)} ≤ δ^{2νN}, and decay ⟨k⟩^{−4Λ} from the outer label sum.
- **The misstatement ("no Stage 1").** Decapitating a regular couple does not always give only regular couples.
  - Configuration: r_1 is a mini-tree top, with (a1, a2) paired and a3 continuing, and (a3, r_2) form a (1,1) mini couple. Then Q is regular.
  - Its decapitation contains an irreducible width-4 component {T_a3, T_b1, T_b2, T_b3}, which is not a couple.
  - That component has no vines, so it can go through LG's gate.
  - Recursive decapitation is not affordable: the depth can be about N, at L^{d+γ} per level.
- **The missing lemma.** P7 needs a regular-couple structure lemma: Q is regular exactly when its decapitation matches one of finitely many product patterns. Without it, the regular/nonregular split does not factor over components.

### 7. Cutoff weights: CONFIRMED (a defect of the FS9 gate statement)
- **Why the gate cannot be produced.** The spliced kernel multiplies per-bond edge amplitudes, each with a 30d-derivative bound and unit-ball support.
  - A smooth cutoff of the max over several leaves cannot be written as a finite-mass average of such products: its mixed second derivative is a singular measure.
  - On the lattice, exact representation costs L^{O(d)} per top leaf, and there are up to about 2N_{p+1} top leaves per tree.
  - The M₂ weight (`cutWeight2`, a max over stem Ω's) has the same structure.
  - Max-form cutoffs also break design C's own component factorization, because one original tree's max spans components.
- **Gate or frozen statement.** The frozen statement is not shown false. In practice, though, its TARGET-literal cutoff form is the problem.
  - DH21 Cor 11.3 states the same gains with per-leaf product cutoffs and single-node Ω cutoffs, which are routable.
  - The likely repair is a versioned frozen statement in that form, after FLOWER-CUT checks it against the fixedpoint consumer.

### 8. Errata
- **E-F1 to E-F5 are real gaps.**
  - E-F2: the "≤ L^{10d} values of Ω" claim checks out.
  - E-F3: the conflict is with Prop subpro (4) at L2045.
  - E-F5: add the DH21 Cor 11.3 comparison to the wording.
- **E-F6 is not established.** TARGET's `ladderl1old` is already stated for arbitrary centres, and its (log L)² weight absorbs DH23's extra argument. Downgrade it to an exposition note or drop it.

### Further findings
- **The AMEND-ST is larger than "two small interface additions".**
  - It omits the garden side of `Represents`: `LeafFamily.value`/`valueSel` still use `kDomain` with no fixed nodes.
  - S2a and S4 are not "unchanged": they must produce the stub set and prove `stub_pendant`.
  - State the amended gates as generalizations, with LG's current gates as proved specializations.
- **Decay is unscoped.**
  - Anchors carry profile 1, so the ⟨k − ζk′⟩^{−4ΛPm} decay must come from a flower version of P*'s weight identity, applied over the non-anchored leaves.
  - That is the flower analogue of AMEND6′(b), about 2k lines in LG.
  - It is in no packet in §10.

### Fixes (binding if you adopt the design)
- **X1.** Correct the count to ≤ 14 trees per flower tree, drop the 10→100 widening, and choose L₀(Pm) in the adapter.
- **X2.** Split the dParent edge u–v_j.
- **X3.** Excise the root for kind W so every tree satisfies `IsTrunc`.
- **X4.** AMEND-ST adds the garden-side stub kernel and the S2a/S4 obligations, and is written as generalizations with bridges to LG's current gates.
- **X5.** Scope the decay mirror, either as a new packet or inside P2.
- **X6.** Add the decapitation structure lemma to P7, route width-4 components through LG's gate, and strike "no Stage 1".
- **X7.** Name the V5 trace lemma for P5/P6, and prove FT4 from layer monotonicity.
- **X8.** Record E-F1 to E-F5, and drop or downgrade E-F6.
- **X9.** Rule the plain clause first, and give FLOWER-CUT the DH21-form cutoff option to evaluate.

VERDICT: ADOPT_WITH_FIXES (X1 width count, no widening because L₀(Pm) suffices; X2 dParent split; X3 W root excision for IsTrunc; X4 AMEND-ST garden-side kernel, S2a/S4 obligations, generalization with bridges; X5 decay mirror for anchored components; X6 decapitation structure lemma, width-4 components via LG's gate; X7 V5 trace lemma, FT4 from layer monotonicity; X8 errata E-F1–E-F5 kept, E-F6 dropped; X9 cutoffs to FLOWER-CUT with the DH21-form option)
