<!-- saved by wt-orch from the referee final message, 2026-11-06 -->
I approve the fiber lemma with three small fixes, none of which blocks it. I could not write `REPORT.md` because the harness blocks subagents from writing report files, so the full report is below and that path does not exist. I edited nothing outside `/home/scott/wt-scratch/research-cut2/fiber-referee/`. In that directory I placed byte-for-byte copies of the inputs in `pinned/` (taken at first read) and the Lean copy, my probe file and their logs in `lean/`.

## Scope and inputs

- **Pinned inputs.** All hashes were the same at the end as at first read:
  - `FIBER.md`: `636cb19568122473549cdc930e0eed24d766e7efbf5fa83c3db36c09d9f9c89f`
  - `FiberCore.lean`: `7c8f1a1fa2e1a8924939b81c72f28cf58407806a3102d3e77a2030840f85f2e7`
  - `FiberCore.log`: `07585a4a…7c970037`
  - `NOTES.md`: `6ec7a551…6e7be1a28`
  - `CX-CUT2-FIBER.md`: `dbffca34…c970037ed4f`
  - The P3 source and olean hashes match those listed in FIBER §6.
- **Main.** Main is at 4d145f6. Nothing under `Foundations/` or `Frozen/` changed since 55deb4a, the commit FIBER was checked against.
- **What I refereed.** The geometric fiber theorem, the repair, the six properties and the per-pin ledger, at the scope FIBER itself declares. The analytic route ruled on in R63 (spatial-Fourier cutoffs, integration by parts in the marked clocks) is not covered here.

## The repair: SOUND

**It is necessary.** I checked a small configuration by hand. Take one tree T (sign +) and three anchors A0, A1, A2:
- u1 is the root, with children u2 (+, left), u0 (−, middle leaf) and u11 (+, right leaf).
- u2 has children b = u21 (+), u22 (−, leaf) and u23 (+, leaf).
- b's three leaves are paired with A0, A1, A2. The other pairs are (u23, u0) and (u22, u11).
- This is a CL vine (I-a) in an irreducible width-4 canonical garden.

After the unit twist to (I-b), b keeps its sign, layer, owner, ordered children, anchors and parent u2. But its address moves from [0,0] to [1,1]. If the regular tree above u2 is replaced by one of a different height, b's depth changes too. So a fiber indexed by raw address or depth is not closed under twists.

**It is sufficient.**
- P3's `operation_stub_preserved` with `trace_anchor_pair_exists`, packaged as `FiberCore.operation_hasPin`, makes anchor-port indexing invariant under every twist.
- My probe proves that the pin's branch is determined by any single anchor index (`branch_of_anchor_unique`). So simultaneous tags are automatically consistent.
- It also proves the three anchor indices of a pin are forced to be distinct, not assumed (`hasPin_anchors_injective`).

**The repaired code can be summed at the claimed cost.**
- Its combinatorial part takes at most C_P values: at most 50P component trees, at most 8P tags, the roles, ports and incidence forest, the irreducible partition, and the region index sets.
- Numbering is deterministic from incidence and roles. Gluing and re-cutting returns the same code, so regrouping the marked gardens by code is exact.
- Root labels cost L^d each, with flux decay. No tree shape, address or depth enters the code.

**"Current parent" is safe, and more cautious than needed.** A unit twist never changes a stub's parent:
- Only u2's parent changes (between u3 and u4), and a stub cannot be u2, because u23 is paired with u0, which is not a root.
- A stub's parent is never inside the replaced regular tree or couple.

**V5 on each fiber.** Geometrically, yes: after fix F2 each per-component carrier is exactly LG's `TwistClosed`, including every exceptional coherent choice. The weights are separate obligations, and FIBER §3.4 says so itself:
- the cut2 stem cutoffs are invariant only on small-gap decorations (fix F3);
- the cut1 product weights are FC3/FT6;
- the V5 external-time trace is X7.

## The six properties

- **P1, closure under twists: OK.**
  - Pins are proved in Lean for every full `FamilyOperation`, with no avoidance hypothesis and with free coherent insertions.
  - Order, canonicity and truncation come from main's `output_*` lemmas.
  - Every glued constraint checks out by hand:
    - each original tree still has exactly one flower, at its flower port;
    - stems are in layer p;
    - the canonicity criterion holds;
    - attached orders are at most N ≤ N_{p+1}^4 ≤ N_p, using the frozen hypothesis N ≤ N(p+1)^4;
    - the kind predicates hold through region sums;
    - flower signs follow from the f^pr sign and the port;
    - the pattern adjacencies are restored.
- **P2, complete coherent families: OK.** Every member is closed forward under every skeleton choice and every coherent replacement allowed by `LFConstruction`, and no code datum restricts the exceptional set:
  - per-tree top order is preserved;
  - exceptional leaves are paired inside one tree, so region fluxes are unchanged.
  - Caveat (F2): to feed LG's per-component gate, the fiber has to be split into slices. That split is not written down yet.
- **P3, canonicity at glued boundaries: OK.**
  - `canonCriterion_iff_low` (Lean) reduces the criterion to pairs of nodes both below layer p.
  - Low subtrees contain no tags or anchors.
  - Incomparability is unchanged.
  - A detached root has parent layer p on both sides.
  - Pairs across components are vacuous, because a single subtree has an odd number of leaves.
- **P4, owners and marked order: OK as FIBER states it.**
  - Owners and the order among pins are preserved.
  - A stronger reading is false: an arbitrary twist can change the set of unmarked stem nodes. With a stem tag inside u21's subtree of a (II-c)/(II-d) vine, u4 leaves or joins the stem. A replaced regular tree above u2 also changes the stem.
  - This is harmless. In any cut forest each component tree carries at most one tag. That tag sits at the bottom of a stem segment, or it is a lone root star.
  - So the high-root, small-gap argument of NOTES §7 carries over unchanged, and the weights are invariant on small-gap decorations.
- **P5, kind and count predicates: OK with F1.**
  - Kind X, Y/L0 and the flower-sibling bound for W reduce to region sums correctly.
  - The W complement bound needs the wording fix in F1.
  - Every cut tree respects the N_{p+1} bound, rechecked for W with a mark between the root and f^pr.
- **P6, anchor labels: OK.** The literal root addresses are preserved (Lean `operation_hasPin`), anchor trees stay `.leaf` (P3 `outputs_anchor_tree`), and labels are root parameters.

## Per-pin ledger: OK

- **Pin count.**
  - At most 4 roles per original tree: f^pr, mark, one face neighbour (or the nonplain pattern node, which needs no mark), and the root. That gives s ≤ 8P.
  - Component trees number at most 50P, so the width condition holds once L ≥ L₀(P).
- **Time, L^{20d} per pin (ladderl1old, TARGET L2013–2032).** The pin's frequency enters only as a unimodular phase, so its sum costs at most |S_v| ≤ L^{20d}. Integration endpoints stay constant.
- **Labels, L^{3d} per pin.**
  - At most 3 child labels; the flower port and fixed-fixed ports are free.
  - Σ_z⟨z/L−c⟩^{−(2d+2)} ≤ C_d L^d, uniformly in c.
  - The flux weights only involve pairs crossing a region boundary, so they are compatible with twists.
  - Each pair profile is charged at most 16d+16, and 8Λ_{p+1}+200d < Λ_p.
- **Normalization.**
  - Components are plain gardens with χ = n−R+1 (rechecked including trivial trees), so LG's estimate gives a width gain.
  - Root stars contribute at most δL^{−(d−γ)}.
  - The total branch order equals N.
- **Arithmetic.** 23d·8P = 184dP; 184+160+80 = 424 and 2+1/9 < 3, so the total is below (424d+3)P < 1000d²P < (100d)³P for d ≥ 3. That is the frozen v2 exponent (100d)^3·Pm, with the j₁=0 and j₂=0 reserves included.
- No per-pin loss depends on N or on a momentum centre.

## Lean

- `FiberCore.lean` compiles: exit 0, no warnings. Every declaration uses only `propext`, `Classical.choice` and `Quot.sound` (`reserve_lt_flower` only `propext` and `Quot.sound`). A grep found no `sorry`, `axiom`, `opaque`, `unsafe` or heartbeat override.
- My probe `FiberProbe.lean` also compiles: exit 0, standard axioms.
- `HasPin` says exactly what FIBER §5 claims.
- The region-count theorems are one-line consequences of `output_topOrder`. They do not connect to the glued garden's `topCountBelow`.
- `cutFiber_unit`/`cutFiber_outputs` are specifications only, not proved. Also not formalized: the cut/glue construction, the canonicity transfer through gluing, and every analytic item. The summary in R64 is accurate.

## Fixes (for the C2-C/C2-E adapter text)

- **F1.** FIBER §3.3 says to count the region below f^pr as "its component tree as well as its detached descendants". That is wrong whenever f^pr's parent edge is not cut, because f^pr's tree then also holds the stem segment above it. The correct count is offset 1 plus the detached descendants. The W complement is the owner's total minus that. FIBER's later truncation paragraph already does this correctly.
- **F2.** State that the per-component `TwistClosed` carriers are slices at a fixed vector of per-component-tree top orders and component orders, at cost (N+1)^{O(P)}. Only then is the fiber a disjoint union of products of closed slices.
- **F3.** Record in the adapter three things:
  - twists can move the unmarked stem, so cut2 weight invariance holds only on small-gap decorations;
  - the one-tag-per-component-tree lemma, which is what lets NOTES §7 apply to cut forests;
  - the weighted dependencies outside this lemma: FC3/FT6, X7, X5, the multi-stub Stage-2 gates in AMEND-ST, the R47 extraction and R48 counting.

## Commands run

```
mkdir -p /home/scott/wt-scratch/research-cut2/fiber-referee/pinned ; cp <inputs> fiber-referee/pinned/ ; sha256sum fiber-referee/pinned/*
cd /home/scott/WaveTurbulence-dev; git diff --stat 55deb4a 4d145f6 -- WaveTurbulence/Foundations WaveTurbulence/Frozen   # empty
sha256sum /home/scott/wt-scratch/flower-p3/src/FlowerP3/{OperationStub,AnchorPairs}.lean /home/scott/wt-scratch/flower-p3/build/FlowerP3/{OperationStub,AnchorPairs}.olean
cp /home/scott/wt-scratch/research-cut2/fiber/lean/FiberCore.lean /home/scott/wt-scratch/research-cut2/fiber-referee/lean/FiberCore.lean
grep -n "sorry\|admit\|axiom \|maxHeartbeats\|opaque\|unsafe\|native_decide" .../fiber-referee/lean/FiberCore.lean   # none
cd /home/scott/WaveTurbulence-dev && LEAN_PATH=/home/scott/wt-scratch/flower-p3/build nice -n 5 lake env lean /home/scott/wt-scratch/research-cut2/fiber-referee/lean/FiberCore.lean   # exit 0
cd /home/scott/WaveTurbulence-dev && LEAN_PATH=/home/scott/wt-scratch/flower-p3/build nice -n 5 lake env lean /home/scott/wt-scratch/research-cut2/fiber-referee/lean/FiberProbe.lean  # exit 0
sha256sum <all audited inputs>   # unchanged at 17:59 UTC
```

Compiler output is in `/home/scott/wt-scratch/research-cut2/fiber-referee/lean/FiberCore.out` and `/home/scott/wt-scratch/research-cut2/fiber-referee/lean/FiberProbe.out`.

REPAIR: SOUND
P1: OK
P2: OK
P3: OK
P4: OK
P5: OK
P6: OK
LEDGER: OK
LEAN: FiberCore.lean compiles (exit 0, no warnings); axioms propext, Classical.choice, Quot.sound only (reserve_lt_flower: propext, Quot.sound); proves pin closure under actual FamilyOperation/batch/outputs, simultaneous tags, region-count invariance, attached-order bound, low-layer CanonCriterion reduction, exponent inequalities; NOT formalized: CutCode/Realization/glue, cutFiber_unit/outputs, gluing canonicity transfer, regionCount = topCountBelow, all analytic items; FIBER.md's description is accurate
VERDICT: ACCEPT_WITH_FIXES (F1 W region below f^pr = offset 1 + detached descendants, not "its component tree"; F2 state the per-tree topOrder/order slice decomposition so per-component carriers are TwistClosed; F3 record that arbitrary LF twists can move the unmarked stem, so cut2 weight invariance is small-gap-only, plus the one-tag-per-component-tree lemma for transferring NOTES §7)