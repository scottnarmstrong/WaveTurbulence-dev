# CX-CUT2-FIBER — tagged cut fibers and the local loss ledger

2026-11-06. Mathematical result with a checked Lean combinatorial core. This is not a completed Lean provider for cut2 or the flower theorem.

## Verdict

**PROVED-WITH-REPAIR:** name pins by distinct anchor-root indices and ordered ports in a fixed component gluing forest. Do not fix their raw node addresses, numerical depths, or the addresses of their parents. Keep each parent floor attached to the *current* parent of its tagged stub. This is a change in the indexing of the exact cut expansion, not a restriction of the coherent replacements allowed by LF twisting.

At this indexing, the admissible geometric fiber contains every full unit LF output, hence every actual `FamilyReconstruction.outputs` family. The proof includes canonical gluing, original-tree membership, relative marked order, the kind/count constraints, and prescribed anchor labels. The source-level per-pin loss is at most `C_d L^(23d)`: `L^(20d)` for a missing time integration and three `L^d` label sums. An intentionally redundant total reserve is `L^((424d+3)P)`, below `L^(1000d² P)` and hence below the requested `L^((100d)³P)` for `d≥3`.

The full excision/gluing construction and the analytic adapter are not formalized here. The Lean file proves tagged-pin closure under the **actual** `FamilyOperation`, simultaneous closure of all tags, batch/output closure, region-count preservation, and the low-layer characterization of `CanonCriterion`. No avoidance, closure, or transport hypothesis is assumed in the pin theorem.

## 1. Scope and fixed sources

Main was read at commit `55deb4a46046f5554f0d4e0e64baeaa8b4eef1a9`. All source references below are to:

- T: `/home/scott/wave-turbulence/paper/source/WKE-Longer_times_Final_arXiv.tex`.
- Main: `/home/scott/WaveTurbulence-dev` at the commit above; in particular `Foundations/Molecule/LFTwist/{FamilyState,FamilyBatch,FamilyOutputs}.lean` and frozen `LayeredGarden{CanonCriterion,ParentLayer,TopOrder,TreeKindOK,FlowerKindOK}`.
- P3: `/home/scott/wt-scratch/flower-p3/src/FlowerP3/{OperationStub,AnchorPairs,Stem}.lean` and its compiled leaf-map dependencies. P3's global STATUS remains RUNNING; this report uses particular compiled declarations, not that packet's completion status.
- Design C and its referee: `/home/scott/wt-scratch/research-flower/NOTES.md`, `/home/scott/wt-scratch/research-flower-referee/REPORT.md`.
- R47-FINAL (pair-type coefficient extraction), R48 (ordinary counting includes low-degree atoms), R61 (Design C), R63 (the present open lemma), in the orchestrator's `RULINGS.md`.

The ordinary regular, vine, ladder, and counting estimates are mathematical inputs from T, including its garden counting theorem with low-degree atoms. Their campaign implementation remains a shared dependency; this note does not prove G3-LOWDEG, FC3, or the complete Stage-1/2 chain.

## 2. Exact cut code

Write `P=Pm`, with `2P` original trees. Work in the frozen source range `p<D`, `d≥3`, `N≤N_(p+1)^4`, and the standing parameter hypotheses of the flower estimate (including the range required by the ordinary counting theorem). For a fixed mixed face term, merge coincident designated branches. There are at most four roles per original tree: flower parent, telescoping mark, one face neighbor (or the designated nonplain pattern neighbor), and root when a kind/pattern constraint requires it. Thus the number `s` of distinct designated branches is at most `8P`. Only nonzero terms need be considered; every designated branch is in layer `p`. A lower-layer neighbor contributes no interior face in a layer-p marked clock.

Use the following variant of Design C: **retain every designated branch**, including a designated root. Cut all its child edges. Replace its children by three leaves in layer `p`, pair these with three distinct fresh trivial root trees in layer `p`, and record the detached child subtrees as separately indexed trees. A flower child is recorded as the distinguished flower port instead of a new genuine subtree. Cut a fixed-fixed edge as well. A retained designated root becomes an isolated root-stub star; its value is treated explicitly. This removes the need to account for a discarded branch in the order.

A cut code includes the fixed source parameters, total order `N`, kind, pattern, flower-sign factor, and the following finite data:

1. Component-tree indices, their signs, original-tree owners, and original root indices. Fix an irreducible-component partition when using the plain-garden LF API; local indices have fixed embeddings into this global index set.
2. A finite tag set. A tag records its component-tree index, sign, clock, and its three **ordered distinct anchor-root indices**. Anchor indices are distinct across tags and disjoint from the genuine component trees.
3. A partial map from tag/child ports to detached component roots, plus one distinguished flower port per original tree. Its directed incidence is a forest. The ports also record roles: mark, flower parent, face neighbor, root; coincident roles share one tag.
4. Prescribed root momenta (including all anchor labels), component caps, and the retained inequalities at stub parents. At a root stub there is no parent floor. Edges between fixed nodes use the original face/trace convention, not a new free-coordinate equality set.
5. For each original-tree, root-child, flower-sibling, or complement region used by a kind predicate, the set of component-tree indices in that region and any completely removed branch offset. With the all-retained convention the offsets are zero.

The code does **not** contain an uncut tree shape, the address/depth of a pin, a fixed address for its free parent, or an individually frozen exceptional regular tree/couple. Such data would unnecessarily split the cancellation families.

A realization is a layered plain forest with exactly these artificial root anchors and a branch for each tag whose ordered children are leaves paired to the prescribed roots. All tag branches and their children are in layer `p`. A tag's branch is unique: its first child's partner is a specified root; pairing is an involution, and a leaf has one parent. Distinct tags cannot collide. Tags in the same component tree form an antichain, since all their children are leaves.

Glue by deleting the artificial anchor trees and replacing each tagged child leaf by the subtree at its recorded component root, working backwards in the finite incidence forest. At a flower port restore the original distinguished flower. Retain the prescribed original signs and genuine pairings. This reconstructs one original flower forest and all its designated branches. Cutting it again returns the same realization and code. In particular, this is an exact decomposition of the marked sum, with no multiplicity introduced by a freely chosen address. Component numbering can be made deterministic; alternative numberings cost only a constant depending on `P`.

The mark's position on the original stem is the relative position determined by this incidence forest. It is **not** a prescribed integer depth. The telescoping sum is over pointed trees `(tree, eligible mark)`, so grouping these pointed objects by the code is an exact regrouping. In an adjacent mark/face-neighbor pair, cutting the edge makes the lower pin a root-stub star; adjacency is therefore also recorded and preserved.

## 3. Fiber statement against the LF API

For a fixed code `c`, let `Fiber c` contain all realizations just described whose glued flower satisfies the required original top-order/kind constraints. Canonicality can equivalently be tested on the cut plain components, as proved below. Root momenta and caps are parameters, not varying fields in `FamilyReconstruction`. When only one irreducible component is operated on, the code also retains the fixed remaining components and the embedding of its local tree indices in the global cut forest.

Here is the Lean-ready full statement. `CutCode`, `Realization`, and `glue` in this display refer to the explicit finite data and construction in §2; they are implementation specifications, **not declarations claimed to exist on main**:

```lean
-- c contains data, not a field asserting twist closure.
-- A is one irreducible plain component, with its fixed embedding in c.
-- Other components are unchanged.
theorem cutFiber_unit
    (c : CutCode originalWidth width p)
    (A : FamilyReconstruction width ι)
    (r : Realization c A.layered)
    (i : ι)
    (op : FamilyOperation (p := p) (kind := kind) A i) :
    Nonempty (Realization c op.output.layered)

-- The actual finite family, in all source-list orders; no replacement by
-- arbitrary reachability, and no frozen choice of exceptional Q or T.
theorem cutFiber_outputs
    (c : CutCode originalWidth width p)
    (A : FamilyReconstruction width ι)
    (r : Realization c A.layered) (L : List ι)
    (h : LG ∈ A.outputs p kind L) :
    Nonempty (Realization c LG)
```

In `Realization`, the original kind predicates are evaluated on `glue`; they are not replaced by a promise that they will be preserved. No SG assumption is needed for this **geometric** statement. For cut2-weighted cancellation use the already identified high-root/SG decoration correspondence; arbitrary LG twists are not asserted to preserve stem resonances.

### 3.1 Full unit operation and complete coherent families

P3 `operation_stub_preserved` applies to every full `FamilyOperation`. It transports the surviving core branch, its layer and sign, and **each ordered child** under `op.LeafCorr`. Its proof establishes exceptional-slot exclusion from the intrinsic stub geometry, rather than assuming exclusion. It includes arbitrary newly chosen coherent tree/couple insertions.

P3 `trace_anchor_pair_exists`, applied to the one-step trace, and functionality of `LeafCorr` show that the transported child is paired with the same literal root address `(anchorIndex,[])`. The root is ordinary and its index cannot change. `LeafCorr.index` on a child also fixes the component-tree index of its parent stub. `LeafCorr.layer` retains the children's layer `p`. These are exactly the steps formalized in `operation_hasPin`.

Apply this independently to all tags. Uniqueness from the anchor indices makes the simultaneous choices consistent. Incidence, roles, original-tree owners, and root labels are fixed finite data; every operation therefore produces another realization of the same code. No new branch address is frozen. Main supplies `op.output_canonical`, `op.output_order`, and `op.output_topOrder` for **each** choice of the full construction.

Induction gives every `FamilyBatch` and every literal `A.outputs p kind L`. For V5, the stronger unit statement is the relevant point: whenever a carrier contains a source, it contains **both skeleton choices and every allowed coherent replacement**, with their original multiplicities. No coherent term has been selected out. For the paper's equivalence-class formulation, reverse a local replacement by choosing the old coherent objects and undoing the skeleton twist. The combined order/top-count constraints are symmetric; the inverse restores the old admissible layer intervals. The same argument applies backwards. Equivalently, fix the unchanged exterior of the local replacement: the pin code imposes no further condition on the full set `B` of exceptional coherent choices in T's `replaceterm1`. Thus a fiber is a union of complete local classes, not merely a set containing one convenient forward trace. We do not claim that main's `outputs` definition is itself the unrestricted equivalence closure.

### 3.2 Canonical gluing at layer p

Under the bound `layer≤p`, a pair with at least one node in layer `p` automatically satisfies the canonical inequality, since each parent layer is at most `p`. The Lean theorem `canonCriterion_iff_low` proves precisely this reduction from the frozen definition.

Consider instead nodes `a,b` with layers strictly below `p`. By monotonicity, neither subtree can contain a layer-p pin or a layer-p artificial anchor. Cutting and gluing therefore leave these entire subtrees, their genuine leaf pairings, and their layers unchanged. Their incomparability is unchanged as well: any changed ancestor path would cross a layer-p pin, impossible below a low node. A low node whose parent edge was cut becomes a component root; the frozen `parentLayer p` gives that root parent layer `p`, exactly its original cut-parent layer. All other parent layers are unchanged. Consequently the complete-pairing test and the canonical inequality for this pair are identical on the two sides.

This proves both directions of `CanonCriterion` under cutting/gluing, including pairs in different trees. When splitting into irreducible plain components, a completely paired union of two low subtrees cannot straddle distinct components: each individual ternary subtree has an odd number of leaves and cannot itself be completely paired. Hence componentwise canonicality is equivalent to the needed global criterion. Layer monotonicity across each new glued edge holds because its parent is in layer `p` and its child root has layer at most `p`.

The special flowers are restored only at layer-p ports; no low subtree contains one. P3's monotonicity argument gives layer `p` for every ancestor of each tagged pin. In particular all original root-to-flower paths have layer `p`, as required by `IsCanonH`. Original flower/plain/sign requirements follow from the explicit pairing/gluing construction, not from `CanonCriterion` alone.

### 3.3 Original regions and kind constraints

Every region boundary used by a kind predicate is cut: roots for `Y`/`L0`, flower parents for `W`, and the selected marks/face neighbors. Its layer-p branch count is therefore

`offset(region) + sum_{j in componentIndices(region)} topOrder(p,j)`.

If the flower-parent count itself is needed, include its component tree as well as its detached descendants. For `W`'s complementary region, subtract this count from the full original-tree count, exactly as in the frozen definition. Root stubs contribute one and their anchor trees zero. The graph determines all index sets before any twist; no branch below a moving raw path is being counted.

Main's per-tree `output_topOrder` preserves every sum. Hence it preserves the original-tree bounds and lower bounds for `X`, the three root-child bounds for `Y`/`L0`, the two flower-sibling bounds for `W`, and `W`'s complementary bound. `operation_regionCount` and `outputs_regionCount` formalize the sum invariant. The unformalized adapter is the exact equality between these sums and `glue`'s frozen `topCountBelow`, which follows from the disjoint branch partition above.

The cut components also satisfy the **input** top-order truncation of the ordinary garden estimate. For `X`, every component uses a subset of the original tree's branches. For `Y`/`L0`, cutting the root leaves a root-stub star and subtrees bounded by the three root-child constraints. For `W`, cut both the root and flower parent: detached flower siblings have their given bounds; components off the root-to-flower path lie in the complementary region. If root and flower parent differ, the component along that path contains the retained flower-parent branch but omits the original root, so its count is at most the complementary count (the added endpoint branch replaces the removed root branch). If they coincide, it is just the root-stub star. Further marked/face cuts only partition branch sets and cannot increase a component count. Thus every cut tree has top order at most `N_(p+1)`; root stars use `N_(p+1)≥1`. This is the reason for retaining the referee's W-root cut.

Attached-order truncation is not an extra invariant to assume. In the source range, `N_(p+1)^4≤N_p` by main's `N_fourth_le_pred` (which requires `p+1≤D`). Every attached garden has order at most the total order. All retained branches glue bijectively, and main preserves the total order of each operated component; thus the reconstructed total remains `N≤N_p`. Every attached-order constraint follows, even if individual lower attachment orders change. `outputs_attachedBound` checks this implication for actual LF outputs. Outside this source total-order range, no arbitrary attached-truncation fiber theorem is asserted.

The frozen `PatValid` conditions also survive: `dRoot` records a root tag distinct from the flower-parent tag; `dParent` and `dChild` record the appropriate adjacent edge between tags, with the latter's layer-p condition included. Cutting such an edge makes the lower tag a root stub, so gluing restores adjacency. Flower signs are the signs of the recorded flower ports, preserved by ordered-child leaf transport and the fixed original root signatures. These observations cover the non-count carrier clauses of the frozen `flowerSum`.

### 3.4 Labels, times, and the weighted class sum

An anchor is an existing fixed **root parameter**. Partner momentum equality fixes the corresponding pin child. The three ordered child labels and conservation fix the pin momentum, epsilon factor and resonance. The actual decoration correspondence fixes these roots and their partners; exchanging the internal `u2/u23` variables does not change them. Arbitrary momentum labels are allowed, with no center-dependent cost.

A stub's free parent need not have the same address after a coherent replacement. Keep the inequality `clock(currentParent)>clock(tag)` in the realized tree. If the parent is part of a regular chain, the tagged time is that chain's lower endpoint; if it is a CL lower child, it is the corresponding external V5 clock. Both estimates are uniform in these external clocks. Fixing one or several external clocks of a Fourier-L1 representation does not increase its Fourier mass: substitute the clocks in the exponent and integrate their frequencies in absolute value. This proves the required trace operation, also for the joint norm with an exterior momentum supremum, using a common representation.

This is not a claim that the original free parent branch is fixed. It is the intrinsic time-domain definition at each realization. Apply coherent cancellation with these endpoints present, then take its Fourier trace; the full exceptional sum is still present. In the remaining time forest, the same constraint is a constant floor on the current parent. Fixed-fixed faces retain the already recorded one-sided trace.

For cut2 upper weights the SG/high-root correspondence preserves the signed stem resonances and the relative marked order (previous NOTES §7, T `twistexplain(d)`). The geometric statement above does not substitute for that analytic fact. Localize/Fourier-expand upper weights in exterior as well as interior momenta as in previous NOTES §3; do not replace a common multiplier by a momentum-dependent family of unrelated Fourier representations. The present fiber theorem removes the carrier obstruction; it does not claim unweighted LF invariance of an arbitrary decoration-dependent weight.

## 4. Explicit per-pin ledger

This section derives costs, rather than assigning the old unsupported `L^(1000d)` allowance to a pin. All estimates are uniform in original order `N`, momentum centers, dyadic indices, and fixed clocks. Constants may depend on the prefix parameters chosen before `L0`.

### 4.1 No delta-profile charge

Artificial anchors are trivial root trees paired with direct children of a pendant stub. They cannot occur internally in a nontrivial regular couple or a vine. Nor can a stub occur internally in a regular tree: it can only be its lone endpoint. Thus prescribing an anchor label prescribes an existing external root/endpoint momentum. It does not introduce a Kronecker-delta profile inside a regular or vine estimate. A trivial anchored pair contributes `1` at its prescribed momentum; there is no free label or center sum for this pair. Genuine input pairs retain their genuine profiles.

This argument is essential. Replacing the anchors by arbitrary localized leaf profiles and charging their `S^(40d,40d)` norms would introduce unwanted center powers and would be a different proof.

### 4.2 Time loss: at most L^(20d) per pin

Use T `ladderl1old`, L1993–2036. In fixed unit momentum boxes each resonance takes at most `L^(20d)` values (L2013), so the allowed Fourier-frequency set `S_v` has measure at most `C L^(20d)`. This bound is a cardinality bound and is independent of the box centers; the intervals need not be close together.

A stub is in no ladder, so in that proof it belongs to `Y`, never to the ladder set `X`. With `t_v=τ_v`, its frequency factor has modulus one. Repeat the minimal-descendant elimination of Step 3 over the free coordinates `Y \ pins`. Every lower endpoint is still constant after the `X` times are fixed: a pinned child contributes the constant floor `τ_v`, and several such floors give their maximum. The upper endpoint is the free parent or a constant. The same four-term recursion and `sup_beta ∫_{S_u}<alpha_u+beta>^-1 ≤ C log L` apply to each remaining coordinate.

For a pinned coordinate, integrate its frequency trivially over `S_v`, costing at most `C L^(20d)` in place of its logarithmic bound. The elementary unit-box supremum reduction remains valid: its derivatives introduce powers of `τ_v-layer(v)`, bounded by one. The ladder localization relations, the `X` monotonicity sequences, and the factorial gains are unchanged. Therefore the fine time estimate loses at most `C^s L^(20ds)`. Fixing the pin's incident labels often eliminates this frequency sum altogether, but the stated bound safely does not use that improvement.

The coarse ladder estimate (T L2080–2084) is unchanged: it is uniform in external times and estimates all nonladder time intervals by one. Removing a nonladder integration has the same bound. Interpolation cannot increase the extra factor beyond `C^s L^(20ds)`.

Retain all stub atoms, all their momentum equations, and all their couplings in the counting problem. Pinning changes the time integral, not the graph. At fixed frequency boxes, extra fixed-label constraints only decrease the **positive** decoration count. In particular set the pin's frequency-window parameter from its prescribed resonance. Apply the ordinary garden counting result with low-degree atoms, as required by R48; a minimum-degree-three version is not sufficient.

### 4.3 Width/rank and coupling normalization

Apply the normalized estimates to each new irreducible anchored component with its own `n_c,R_c` and `chi_c=n_c-R_c+1`. These are the quantities used in T `defcounta`/`finalcount1`, L2110–2117. After normalization the width factor is a gain `L^(-(R_c-1)(1/4+1/60))` (or the corresponding stronger intermediate gain). Since each nontrivial plain component has even width `2R_c≥2`, discard this factor. **Do not** substitute the old flower width into that calculation. There is no rank-conversion loss.

All designated branches were retained, so their coupling factors were retained and the total branch order over the cut components equals the original order. At an isolated root-stub star the value, with labels prescribed, has modulus at most `δ/(2L^(d−γ))≤δ≤δ^(2ν)` for `2ν≤1`; no time integral or internal decoration sum remains. Trivial components have no branches and contribute a bounded genuine profile or the prescribed anchor value `1`. Regular components use the ordinary pointwise regular-family estimate.

There are at most `2P+6s≤50P` component trees. Splitting into irreducible components and summing order compositions costs at most a constant depending on `P` times `(N+1)^(50P)`. This is not an `L^(cN)` loss. The original width range is met by choosing `L0(P)` sufficiently large, as in the Design-C referee, without widening a frozen gate.

### 4.4 Outer labels: at most L^(3d) per pin

There are at most three new child-root labels per pin. Conservation and dagger conditions can reduce this number; use the upper bound `3s`. A cut-root label `κ_e` has the form

`κ_e = a_e k' + z_e`,

where `a_e` is zero or the signed flower coefficient and `z_e` is the signed sum of genuine nonflower leaves of its original subtree. Use the exact polynomial weight `⟨z_e⟩^q`, with `q=2d+2` even, and expand it by R47-FINAL's pair-type coefficient extraction **before** estimating the complex kernel. Do not infer a weighted oscillatory estimate from a pointwise absolute-value inequality.

Why this extraction respects the full coherent sum: each cut-root region is a union of whole component-tree indices in the recorded incidence forest. In its signed flux, the known boundary anchor charges cancel. Each freely inserted coherent tree/couple lies within one component tree; its paired internal leaves cancel in the signed flux. Only genuine pairs crossing the region boundary contribute. Their coefficients depend only on the fixed tree-pair type. Thus no exceptional replacement shape or individual exceptional leaf is marked. This is exactly the class-compatible form of R47, including when the two ends of a genuine pair belong to different original trees.

A genuine leaf belongs to at most one child subtree of each pin, hence at most four fluxes per original tree. A paired input profile has two ends and is charged at most `8q=16d+16`. Together with the existing cut1/root-decay extraction and derivative requirements, a reserve of `8Λ_(p+1)+200d` per genuine profile suffices; it is strictly smaller than `Λ_p=40dΛ_(p+1)` for `d≥3`, `Λ_(p+1)≥40d`. Expansion/finite coefficient extraction has a fixed-degree polynomial cost in `N+1` per original tree, not a power of `L` per leaf. The repeated-pair charge is included here; using only `4q` per profile would undercount.

Now sum the outside labels using

`sup_c sum_{z in Z^d} ⟨z/L-c⟩^(-(2d+2)) ≤ C_d L^d`,  `L≥1`.

For completeness, cover space by lattice cubes of side `1/L`; the bracket at a cube center is comparable to its value on the cube by a dimension-only constant. Summing their integrals gives `C_d L^d ∫ ⟨x⟩^(-(2d+2)) dx`. Translation of the cubes gives uniformity in `c`. Dropping the affine conservation restrictions only increases this positive majorant. Consequently all new labels cost at most `C_d^(3s) L^(3ds)`.

### 4.5 Total

| Item | Explicit cost |
|---|---:|
| Full tagged-fiber/class transport, anchors as root parameters | 1 |
| Nonladder fixed-time Fourier loss | `C^s L^(20ds)` |
| At most three outer label sums per pin | `C_d^(3s) L^(3ds)` |
| Component width/rank conversion | 1 after discarding gains |
| Restored root-star couplings | already supply the required delta-per-order gain |
| Marks, face choices, finite component partitions and flux expansions | `C_P C^N (N+1)^(C(d,D)P)` |

Thus the additional local polynomial cost is `L^(23ds)`, and `s≤8P` gives `L^(184dP)`. Constants `C^N` are absorbed using the ordinary proofs' unused delta-per-order margin, before retaining the requested `δ^(2νN)`. Since `N` is bounded by a fixed power of `log L`, constants depending on the prefix and the indicated polynomial factors fit `L^(2P)` by increasing `L0`; this also covers the finitely many outer IBP normalization constants. No such absorption is allowed to depend on the dyadic index or on exterior momenta.

For a conservative comparison with the previous flower route, reserve **another** `L^(160dP)` (`80d` per original flower) although the direct all-retained construction above already accounts for its local operations. Reserve `L^(80dP)` for `j1=0` and `L^(P/9)` for `j2=0`. Including the `L^(2P)` margin gives

`184dP + 160dP + 80dP + 2P + P/9 < (424d+3)P`.

For `d≥3`, `424d+3 < 1000d² < (100d)³`. These inequalities are also checked in Lean. This replaces the old unexplained `1000d per pin` budget by identifiable local estimates. The ledger is an adapter result using the ordinary mathematical estimates; it does not assert that the entire analytic adapter is already a compiled theorem.

## 5. Formalization and validation

`lean/FiberCore.lean` imports the current main LF API plus the compiled P3 stub/anchor modules. Its declarations are:

- `HasPin`: existential branch address, fixed owner, sign, top layer, and three ordered literal anchor-root addresses, with children also in the top layer.
- `operation_hasPin`, `operation_pins`: closure under **every actual full unit operation**.
- `batch_hasPin`, `outputs_hasPin`: the universe's batch/output closure.
- `regionCount`, `operation_regionCount`, `outputs_regionCount`: actual per-component top-order sums, with explicit removed-branch offsets.
- `outputs_attachedBound`: attached-order truncation in the source fourth-power range.
- `ledger_lt_reserve`, `reserve_lt_flower`: the explicit integer exponent comparisons.
- `parentLayer_le`, `canonCriterion_iff_low`: the frozen canonical criterion reduced exactly to low-layer pairs.

The missing Lean work is implementation of the explicit cut/glue forest and its node/leaf embeddings; the resulting frozen `topCountBelow` partition equalities and two-way gluing canonicality; and the analytic time/flux/normalization wrappers of §4. These are not passed as hypotheses to a claimed complete theorem. Momentum decorations and clocks are not fields of bare `FamilyReconstruction`, so the geometric theorem alone cannot formally assert their transport.

Check command, from `/home/scott/WaveTurbulence-dev`:

```sh
LEAN_PATH=/home/scott/wt-scratch/flower-p3/build nice -n 5 lake env lean /home/scott/wt-scratch/research-cut2/fiber/lean/FiberCore.lean
```

The extra search path reuses P3's compiled main-compatible modules; no dependency was rebuilt or modified. An initial attempt referred to P3's newly written unit anchor convenience theorem, which had not yet reached its compiled artifact. The final proof instead uses its already compiled trace theorem directly. A second attempt corrected a local equality-substitution issue. The final command exited 0 without errors or linter warnings. Final result and axiom checks are recorded in `lean/FiberCore.log`; only `propext`, `Classical.choice`, and `Quot.sound` occur in the checked core. No placeholder, custom axiom, heartbeat override, or source edit was used.

Independent refutation by the existing `refute_cut2` agent checked the tagged/gluing argument, time-frequency loss, pair-profile charge, root-parameter interpretation, positive-count restriction, and componentwise rank normalization. Its final verdict accepted the mathematical research proof at this scope, explicitly not the existence of a complete Lean gluing/Stage-2 adapter. In particular it required the componentwise rank calculation before accepting the numerical ledger; that calculation is included in §4.3.

No new contradiction to TARGET is claimed. The address/parent wording is a necessary precision in the proposed adapter, not an amendment of the frozen flower statement. Existing low-degree counting and pair-type extraction dependencies remain explicit.

## 6. Source/artifact fingerprints
SHA256, recorded after the final check (the complete P3 source may include additional declarations beyond the reused compiled interface):
- `/home/scott/wave-turbulence/paper/source/WKE-Longer_times_Final_arXiv.tex`: `493eef6b7dec448bc5f9f1c3974c0cad7a85eca9bc428f5b35e968aad76727cb`
- `/home/scott/wt-scratch/flower-p3/src/FlowerP3/OperationStub.lean`: `c5c2db076398046534298b21119f3e621350a5d05547c332ab62b92cfb7e52e1`
- `/home/scott/wt-scratch/flower-p3/src/FlowerP3/AnchorPairs.lean`: `23cd0185dd7be17c5daa692c055f18d21bfe05cf4bcf3d0f4edf54db4552fa86`
- `/home/scott/wt-scratch/flower-p3/build/FlowerP3/OperationStub.olean`: `830695acae78e7362ddb594c8ebbb54ae6d3e2a68146ebbe7773dc3b33dcc510`
- `/home/scott/wt-scratch/flower-p3/build/FlowerP3/AnchorPairs.olean`: `f291e7d5233bb23c95e88bee73a9eb7a662e7b70095898574dc36896c3895abc`
- P3 `src` tree aggregate (sorted relative paths and individual SHA256 values, newline delimited): `bc75cd5f32a060d6c05eae2a3379e46b57d0d1f6a0c13cc209ea40213f895831`.
- P3 `build` tree aggregate (sorted relative paths and individual SHA256 values, newline delimited): `e6831b9fbd487ff626b29e061939cc50e5042c345fb365a952133afda2c8dcc4`.
