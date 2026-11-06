# Flower Stage-1 source boundary — research notes, no interface amendment

Pinned input: TARGET local TeX lines 2259–2265, 2287–2306, 2312; Flower-S1 HANDOFF/OBSTRUCTION and its four checked modules. No new mathematical claim, gate, proof or source erratum is established here.

Required semantics for a successor analytic interface:

- Retain the actual flower-parent/root designated times; integrate only free branch coordinates, exactly as kernelGenLeavesTerm does. Fixing parent resonance values removes their phase factors, not their trace constraints.
- Admit zero-order reduced components and disconnected/reducible completions. TARGET explicitly drops irreducibility for flower moments. The ordinary positive-order irreducible Sound package cannot be reused verbatim.
- Keep marked leaves with their actual momenta and root-relative signs. A plain completion may pair consecutive flowers only after proving their opposite signs and a decoration equivalence. Returning the plain completion as the original marked garden is invalid.
- Lift LF operations with marking transport and special-node avoidance. Existing FamilyReconstruction inputs/outputs are plain and CanonicalObject excludes IsCanonH. Restricting its output relation by a predicate alone cannot create flower states.
- Preserve the pair-type input family, stem layers, cutoffs and R55/R56 mass/count amendments. Prove full-class closure/compatibility before applying any vine cancellation.

Possible analytic route to investigate, NOT approved as an exact statement or proved:

Use a literal marked trace spliced kernel, then derive its coarse bound with only O(width) fixed coordinates, using finite resonance partitions and source-uniform shifted resonance counting. To apply a Fourier/counting argument, additional dummy coordinates may be integrated over a fixed unit cube independently of the remaining trace domain; they cannot be put back into the ordinary order-dependent splicedTimeDomain. One must prove the exact integral identity, the count of possible parent resonance values on localized momenta (uniform in centres), the shifted-counting bound, and all Fourier mass estimates. The old ordinary-kernel representation and shrinking-box bound do not supply these.

The structural side separately needs a genuine marked/componentwise regular reduction, decomposition and splice construction. Exceptions at the special nodes must be counted explicitly and charged within the frozen L-power loss; no number of unproved exceptional-atom estimates may become a new standing input.

A first implementation packet should address one exact structural or analytic lemma and report an obstruction if current APIs do not suffice. Independent source review is required before replacing FS9.Gates and its consumers. Frozen B1.12 and its V2 successor remain read-only.

## Concrete next structural lemma: cut one fixed parent

This is a proposed proof route, not an established Lean identity or an approved API amendment.

For one actual flower tree, let v be the flower parent, i the flower child, and j,k its other children. Replace the subtree at v by one lone marked leaf to obtain the prefix tree, and retain the actual two sibling subtrees rooted at vj and vk. Use `TTree.setAt` and `subtreeAt` at these valid source paths. This is a pruning of the original tree; it must come with explicit original-path maps, not arbitrary reconstruction choices.

The original branch carrier with v removed should be equivalent to the disjoint sum of the branch carriers of the prefix and the two sibling subtrees. The original non-flower leaves should likewise be in bijection with their leaves, with original signs, layers and pairings transported. The root-prefix case is essential: if v is the root, the prefix has order zero, contributes no integrated branch time, and its new lone leaf has the original root momentum. A trivial sibling subtree must also remain an order-zero tree.

At the level of a FIXED ORIGINAL DECORATION, the free-time domain then has exactly these boundary conditions:

- the prefix root retains its original upper time t; if the prefix has branches, the parent of its new lone leaf has time greater than s;
- every branch of each sibling subtree has upper time s (the root inequality suffices together with the actual parent order, and can be extended to every branch);
- the deleted parent has time s, with its original layer and root/parent inequalities retained as explicit boundary indicators.

The first point uses the literal lone-parent clause of frozen `kDomain`; it does not turn a fixed parent back into an integrated branch. Under valid flower time assumptions the deleted parent's own layer/root inequalities must be proved, rather than omitted from a general identity. The branch-domain correspondence and the change of product measure are the first bounded formalization target.

After that correspondence, the fixed-decoration phase/epsilon product splits algebraically into the prefix and sibling products, the deleted-parent factor at time s, and one removed coupling factor: n_original = n_prefix + n_j + n_k + 1. The removed factor contains the actual `epsCoef` and `exp(pi*i*zeta_v*delta*L^(2gamma)*Omega_v*s)`. Keeping this as a bounded boundary amplitude may avoid differentiating its momentum dependence; an amplitude that requires Schwartz derivative bounds would NOT allow this shortcut. No epsilon replacement or omitted conservation equation is allowed.

For a whole garden, original non-flower leaf pairs can connect DIFFERENT new components. Therefore the fixed-decoration time factorization does not imply a product of separately summed kernels. The original decoration sum, the conservation relation at each removed parent, and those cross-component pairings must be carried explicitly. Moreover, the new prefix lone leaves carry the respective original parent momenta, which need not agree between trees. Frozen `GenDecoration` uses one shared marked-leaf label, so an unmodified global `kernelK` is not already this boundary forest. A literal per-boundary decoration carrier or a rigorously conditioned sum is needed. These are concrete reasons that an ordinary plain-garden `Sound` cannot simply be reused.

Subsequent work, only after the exact pruning lemma: prove source canonicity componentwise without irreducibility; prove a boundary-forest coarse/counting estimate with at most O(width) exceptional coordinates/atoms and the exact removed coupling costs; and lift LF moves away from the cut boundaries with actual marking/pairing transport and the source stem/cutoff invariants. The bound must be independent of the absolute momentum centres and D. No such estimate, marked twist lift, or replacement FLOWER-SPINE producer is claimed here.
