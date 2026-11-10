# TWIST-PROFILES research notes (research-twistprof), 2026-11-05

Main record. Newest material at the bottom of each section. Lean probes in ./lean/.

## Sources read (pinned by path; line numbers as of this session)
- TARGET <sources>/paper/source/WKE-Longer_times_Final_arXiv.tex:
  L1345-1418 (block_clcn, molecpl), L1429-1480 (Def twist, Rem twistexplain, Def lftwist), L1481-1488 (lftwistprop),
  L1720-1760 (regred, vineest), L2040-2075 (redcount0: the weights/derivatives paragraph L2062-2067), L609-613 (parameters).
- DH23 <sources>/references/src-2301.07063/Revision_Submit.tex L741-760 (block_clcn), L810, L852-856 (Def twist).
- lg-spine-u: Stage1Gate.lean (L57 Stage1ReductionAt), Stage1Interface.lean (LeafFamilyD L59, Represents L156),
  WeightedFamily.lean, WeightedFamilyValue.lean, NonregularGarden.lean, NonregularCouple.lean, NonregularFinal.lean,
  DecoratedWeightExpansion.lean (RootLeafSlots), RootWeightExpansion.lean, RootModifiedProfiles.lean,
  LeafDerivativeAssignments.lean, LeafwiseKernel.lean, LeafwiseLayerInputs.lean, LeafwiseAt.lean.
- RULINGS R40-R45; represents/HANDOFF.md top; lftwist-leafmap/HANDOFF.md; vineest-s3/PROGRESS.md top + HANDOFF.md top;
  vineest-s3/uni/src/VineEstS4/CanonStatement.lean; vineest-s3/uni/src/VineEstS5C/{LayerStatement,GateH}.lean (V5 drafts, 13:40/13:58);
  pl234/pinned/LeafwisePolarizedInputs.lean.0915, pl234/src/PL234Draft/{P4Leafwise,P4Gt,SliceApp}.lean.

## Q1. Can an LF twist move leaves between root trees?  NO.
- block_clcn (1a)(ii)-(iii) (TARGET L1348, DH23 L745): u2 is a descendant of u1 and the realization G[B] = desc(u1) minus
  desc(u11,u21,u22) is completely paired. molecpl (L1405-1413): (II-a,b) u3,u4 have the common ancestor u1; (II-c,d,e)
  u3 is a descendant of u1; (I) u2 is a child of u1. Def twist (L1431, DH23 L855): G' equals G outside the subtrees
  rooted at u3,u4 (u1 for vine I); free subtrees T1,T2,T3 keep their roots u21,u22,(free child) inside desc(u1).
- Def lftwist (L1466-1476): T'_(u2) replaces the node u2 and Q'_(u23,u0) the leaf pair (u23,u0); both attach inside desc(u1).
  n(T')+n(Q') = n(T)+n(Q), so every root tree keeps its order.
- Consequences used below:
  (a) every node/leaf keeps its root-tree index (the Fin w component of its address); the partner of an ordinary leaf keeps
      its root tree too; so the PAIR TYPE  type(a) := (layer a, tree of the + leaf, tree of the - leaf)  is preserved for
      every ordinary pair.
  (b) every leaf of the vine realization (all regional rows Q_(l,l'), T_(m), incl. the exceptional T_(u2), Q_(u23,u0)) is
      paired INSIDE desc(u1), i.e. inside one root tree j1: its type is (q, j1, j1). Every leaf of G lies in exactly one row
      (couples at skeleton pairs, trees at skeleton branches) and is paired inside that row.
  (c) the root momentum k_j = sum_{leaves in T_j} sigma k = sum over CROSS pairs (one leaf in T_j, the other elsewhere);
      same-tree pairs cancel. Hence root-weight data never needs a vine-region leaf.
- What is NOT preserved: individual exceptional leaves (F-EXC), per-layer leaf counts of T', Q' (only total order and the
  layer-p branching count are fixed), RootLeafSlots as sets (F-ROOT). So root-weight modifications indexed by individual
  leaves (RootWeightChoices) are not class compatible; modifications indexed by (layer, root tree of + leaf, root tree of
  - leaf) are.

## Q2. PL234 reality gate.
- `LeafwiseRealityGate` (pinned .0915 L52) is polarized over tuples H : Fin(2n+1) -> N -> Mom d -> R. Its proof
  (P4Leafwise.lean L49) is `polarize_im_zero` + `reality_all P.δ F ...` (P4Gt.lean L91), and `reality_all` holds for EVERY
  layer-indexed real F : N -> Mom d -> R with no hypothesis at all (not even a bound).
- So realness of sum_b Q_b conj(T_b) holds for layer-uniform profiles with an ARBITRARY real layer-indexed h: take F := h.
  For the leafwise kernels use PL234 SliceApp `sourceCouple_eq` (L205) / `sourceTree_eq` (L307):
  SourceApp.couple δ F LG = LeafApp.coherentCouple δ LG (layerProfiles LG F) (for coherent carriers), and
  `KQstar_eq_coupleLeaves` (L38). V5's GateH.lean already ports these.
- Only non-uniform leaf assignments are excluded ("does not assert realness for independently chosen summand profiles").
  Complex profiles are also excluded: LeafProfiles are R-valued and the realness argument is for real F.

## Q3. TARGET L2062-2067: genuine gap (in the proof, not in the result). CANDIDATE erratum E-TWPROF below.
(i) weights: "<k_j>^{4Λ} <= (3n_j)^{4Λ} <k_{l_j}>^{4Λ} for some leaf l_j" and then "include the extra factor into the input
    F_{L_{l_j}}": l_j depends on the decoration, so this is a pointwise inequality inside oscillatory sums (decoration sum and
    the twist-class sum of vineest), not a modification of an input function.
(ii) any decoration-independent leafwise placement (polynomial expansion = Lean RootWeightChoices; Leibniz distribution of
    d/dk over leaves = Lean LeafDerivativeChoices) produces terms with the modified leaf inside T_(u2) or Q_(u23,u0); in the
    LF-twisted G' these objects are replaced by T', Q' with different leaf sets, so the term has no class counterpart; vineest
    (class sum, identical inputs, realness (layerregest10) for the common input) does not apply term by term
    (S2 F-TWISTCLASS, LFTWIST-LEAFMAP F-EXC/F-ROOT, V5 F-LEAFREAL).
(iii) the result survives: the sums TARGET forms are symmetric in the leaves they range over and can be rewritten EXACTLY
    as real combinations of kernels with type-uniform inputs (design P* below).

## Candidate designs: refutation log
- (P) as posed: two defects.
  P-1 roots-of-unity extraction / complex Cauchy radius: evaluations at complex eps give COMPLEX profiles; LeafProfiles are
      R-valued and the vine cancellation needs realness of sum Q conj T for a real common input. Fix: REAL central differences
      (exact): for deg p <= 2M, p'(0) = sum_{i=1}^M (c_i/λ)(p(λi) - p(-λi)), c_i = (-1)^{i+1} C(2M,M+i)/(i C(2M,M)), |c_i| <= 1/i.
      (Proof: the 2M-th finite difference of a polynomial of degree < 2M vanishes; Mathlib fwdDiff_iter_eq_sum_shift +
      Polynomial.fwdDiff_iter_eq_zero_of_degree_lt.) Weights are polynomial in M: sum_i 2|c_i|/λ <= 2(1+log M)/λ.
      Non-central (one-sided / Lagrange on [0,ρ]) nodes give weights 2^{deg}, which raised to r <= 4Λ (or 8mΛ) is NOT
      absorbable (Λ, C_2 are chosen after δ: Λ_p = (40d)^{D-p+1}, D = τ*/δ).
  P-2 pure layer-uniform families cannot give the PRODUCT weight prod_j <k_j>^{-4Λ} for width 2m >= 4: one global cutoff only
      sees max_j |k_j| (decay Λ_p - 40d = 40Λ - 40d < 8mΛ for m > 5). Global nested bands make a single high pair carry all
      2m factors (profile norm blows up). The per-tree cutoff + real Lagrange extrapolation works only with A partitioned by
      tree-order vector (else weights 2^{(N+m)·2m}); it needs smooth bumps, a vanishing lemma and a partition. REJECTED in
      favour of exact linear-form polarization on CROSS pairs (below), which needs none of this.
- (A) V5 hybrid: needs φ (LFTWIST-LEAFMAP, F-TRACE), polarized tuples on exceptional rows, S2 rewriting weightedFamily into
      per-class polarized form, node-profile generalization of Steps 3/4 (R43), and still leaves F-ROOT. Most expensive. REJECT.
- (R) regrouping: derivative mass on an exceptional region must be applied JOINTLY to Q and T (realness only for the joint
      translation: d/dk of sum_b Q_b(k)conj T_b(k)); separately differentiated Q, T need realness of sum ∂Q conj T, not
      available. Joint jets on exceptional rows = (P) restricted to those rows, plus φ elsewhere. Root weights: the task's
      suspicion (x*, y* swap) is avoided if the root expansion is restricted to CROSS pairs (Q1 (c)): those are never in a
      vine region. So (R) is viable but strictly more infrastructure than P*. REJECT.
- P* (RECOMMENDED): pair-type-uniform families + exact real central-difference extraction for BOTH derivatives and
      root linear forms. See below.

## Design P*
Pair type of an input leaf a (the + leaf of a pair): (layer a, a.1, (pair a).1.1). Family profiles H LG i a = h_i(type a);
ι, sign, bound b_i independent of LG.
Operations on type-uniform h:
  D_i h(q,j,j')            := ∂_i h(q,j,j')                                   (coordinate derivative)
  M^{(j0)}_i h(q,j,j')     := ([j = j0] - [j' = j0]) · k^i · h(q,j,j')(k)        (root linear form; 0 on same-tree pairs)
First-order identities (per garden, exact):
  (D) ∂_{k^i} K_LG[h](k) = sum_a K_LG[D_i h at a]              (translation invariance; existing Leibniz, couples)
  (M) σ_{j0} k_{j0}^i · K_LG[h] = sum_a K_LG[M^{(j0)}_i h at a]  (sum_rule + partner has the same momentum)
  (L) sum_a K[v at a, h elsewhere] = [ε^1] K[h + ε v]  and deg_ε K[h + εv] <= #inputLeaves = N + R (all of A).
  (C) [ε^1]p = sum_{i=1}^M (c_i/λ)(p(λi) - p(-λi)), M = ceil((N+R)/2).
So for an operation O: X_O(h) = sum_{i=1}^M (c_i/λ_O)(V(h + λ_O i O h) - V(h - λ_O i O h)), V(h) := sum_{LG∈A} K_LG[typeProfiles h].
Couples: jbr(k)^{4Λ} ∂^word V(h0)(k) = sum_{c : Fin 2Λ -> Option (Fin d)} X_{word.map D ++ forms_0(c)}(h0)(k).
Gardens: prod_j jbr(k_j)^{4Λ} V(h0) = sum_{c : Fin 2m -> Fin 2Λ -> Option (Fin d)} X_{forms(c)}(h0).
Every evaluation is a REAL type-uniform family; on every vine region it is the layer-uniform jet (M's vanish there).
Bounds: λ_t = 1/(M u r (N+R) V), u = 40d + r + 1, V = max_{q<=p} ||F_q||_{S^{40d+4Λ, 40d+8Λ}}:
  ||h_θ(q,j,j')||_{S^{40d,40d}} <= C_1 + 2/(N+R)  =>  b^{N+R} <= e^2 C_1^{N+R};
  sum_θ |W_θ| <= (2(1+log M) M u r (N+R) V)^r,  r <= 8Λ (couples), 8mΛ (gardens).
Loss (C(N+m))^{O(mΛ)} V^{O(mΛ)}: same shape as the existing card(RootWeightChoices)·(#leaves)^{4Λ} budget, absorbed by
L^{-(m-1)/70} (m >= 2) / the θ-margin (couples) since N, R are polylog in L (TARGET (parameters2)) and L is chosen last.

## Coordinator constraint (14:1x): per-leaf bounds uniform across layers (R46 option A). CHECKED.
- TypeFamilyD carries ONE bound b_i per element (no layer, no pair-type, no garden dependence); premise U.Bounded p:
  ∀ i q j j', q ≤ p → ‖h_i(q,j,j')‖_{S^{40d,40d}} ≤ b_i.
- Every consumer evaluation family has b_θ = C₁ + 2/(N+R) for ALL layers q ≤ p and all types (step λ_t is a scalar,
  independent of layer/type/garden). On a vine region the input is h_θ(·,j1,j1) with the same b_θ, so V5's R46
  VineEstCanonLayer applies with B₀ := b_θ; region factor b_θ^{#region input leaves} is twist invariant.
- There is NO Cauchy-radius scaling in P*: the radius scheme (complex, and per-tree radii ρ_j) was rejected (P-1, P-2).
  (For the record, even the rejected real-cutoff variant had a layer-uniform bound C(d)C₁+3.)
- Input requirements are exactly the existing ones: couples ‖F_q‖_{S^{40d+4Λ,40d+4Λ}} ≤ U (existing hU), gardens
  ‖F_q‖_{S^{40d,40d+8Λ}} ≤ U (existing hhigh), ‖F_q‖_{S^{40d,40d}} ≤ C₁ (existing hlow), all uniform in q ≤ p.

## Lean checks (all transient, nice -n 5, one at a time, outputs not written to any build dir)
- lean/TwistProfProbe.lean vs lg-spine-u build-fresh-a5 (probe.sh): pairTrees, typeProfiles, TypeFamilyD, toLeafFamily,
  toLF, Bounded, typeProfiles_leaf, typeProfiles_layer (layer-uniform = special case, rfl-level), size_eq,
  Stage1ReductionAtT (AMEND6' form, R44(i) abstracted as a predicate), stage1ReductionAtT_of_old (old gate ⇒ new gate):
  exit 0, no sorry.
- lean/CentralDiff.lean (Mathlib only): cw, alt_choose_poly_eq_zero, cw_symm, cw_moment, first_coeff_extraction,
  abs_cw_le: exit 0, axioms [propext, Classical.choice, Quot.sound].
- lean/VineLeafProbe.lean in V5's S5C world (uni/probe5c.sh): VineEstCanonLeaf elaborates and
  `VineEstCanonLeaf P = VineEstCanonLayer P := rfl` against V5's R46 LayerStatement (14:15 olean): exit 0.
- sha256: lean/SHA256SUMS.

## Effort
- LG-SPINE AMEND6' (statement, Stage1Bound/GateMonotone plumbing F -> U.toLF): ~250 lines (definitions already probed).
- LG-SPINE POLAR consumer (replaces weightedFamily in NonregularGarden/NonregularCouple + late arithmetic):
  affine expansion ~300, slopes (D),(M) ~300, op recursion ~300, bounds ~400, two estimates ~400, late ~400,
  central differences 150 (done) => ~2.2k new lines.
- R44 (i) twist-closure of the actual A: unchanged owner/cost (needed in every design).
- S2: F := U.toLF; type pullback to native rows + "LF twists keep root-tree indices of attachment points": ~300-500.
- V5: nothing new (R46 statement = VineEstCanonLeaf); node-profile port of R43 NOT needed.
- LFTWIST-LEAFMAP: off the critical path.

## Finding V5-LAYER (V5 draft VineEstCanonLayer, LayerStatement.lean 13:40) -- independently found by V5 (F-LAYERCOST), resolved by R46
Bh : N -> R layer-dependent with regionLeafSize computed at the START state is not class invariant: the exceptional rows'
per-layer leaf counts vary over the LF-twist class (only the total order and the layer-p branching count are fixed).
Sketch of failure: h_r = 0, Bh r = 0 for r != r0; start G has one chain pair of the exceptional type-2 couple Q in a layer
r1 in (r0, q) (r1 < p), everything else of the region in r0; then RHS = 0, while the class contains G' with Q' of type 1
(all in layer q' = r0), whose kernel is nonzero; the class sum is generically nonzero. Use a layer-CONSTANT bound.

## Final recommendation: P* (see REPORT in the session answer; summary)
AMEND6' replaces R44 AMEND6 (ii): Stage1ReductionAt quantifies over `U : TypeFamily P (2R)` with `U.Bounded p` and uses
`U.toLF` in place of `F`; (i) twist-closed A unchanged. weightedFamily is replaced in nonregular_prefix by exact real
central-difference polarization: derivatives (couples) and root linear forms (all widths) are first-order slopes
D_i, M^{(j0)}_i of a type-uniform profile; each slope is extracted exactly by
  sum_a K[v at a] = sum_{k ≤ 2M, k ≠ M} (cw M k / λ) V(h + λ(k-M) v),  #inputLeaves = N+R ≤ 2M.
VineEstCanonLeaf = V5's R46 VineEstCanonLayer (rfl).
Candidate erratum E-TWPROF for TARGET L2065-L2067 (text in the session answer).

## CANDIDATE erratum E-TWPROF (TARGET §redcount0, L2065 and L2067)
Error in the proof, not in the result. L2065 places <k_{l_j}>^{4Λ_{p+1}} on "some leaf l_j ∈ T_j"; l_j depends on the
decoration, so this is a pointwise inequality inside oscillatory sums, not a change of input function. L2067
distributes ∂_k "exactly one ∂_{k_l} for some leaf l" and says the same arguments apply to each term. Any such
leaf-by-leaf term whose modified leaf lies in T_(u2) or Q_(u23,u0) (Def lftwist) has no counterpart in the LF twist G'
(T', Q' are free coherent objects with other leaf sets), so Prop vineest (a sum over the LF-twist class with identical
inputs, using the realness (layerregest10) of the common input) does not apply term by term.
Repair: modify inputs uniformly by leaf-pair TYPE (layer, root tree of the + leaf, root tree of the - leaf). LF twists
act inside the subtree of u_1, so types are twist invariant, and every pair of the realization G_sk[U] has type
(q, j_1, j_1). (a) ∂_{k^i} K = Σ_l K[∂_i F at l] = d/dε|_0 K[F + ε∂_iF]. (b) σ_j k_j^i K = d/dε|_0 K[F(k)(1 + ε c_j k^i)],
c_j = [+ leaf in T_j] − [− leaf in T_j] (zero on pairs inside one tree, so zero on every vine region); expand
(1+|k_j|²)^{2Λ} into products of such linear forms. (c) for a polynomial of degree ≤ 2M = n+R,
d/dε|_0 p = Σ_{k≤2M, k≠M} w_k p(λ(k−M))/λ with w_k = (−1)^{k+M+1} C(2M,k)/((k−M)C(2M,M)), |w_k| ≤ 1/|k−M|.
Every term is then a kernel with real type-uniform inputs, bounded by one constant C_1 + 2/(n+R) at every layer, to which
the Stage 1 reduction and vineest apply verbatim. Loss (C(n+R))^{O(RΛ_{p+1})}, absorbed as in L2065
(n, R polylog in L, (parameters2)).

## Exact AMEND6' statement (probed)
Stage1ReductionAt C₀ P :=
  ∀ p, p < P.D → ∀ R, 1 ≤ R → R ≤ 10 * P.R (p + 1) → ∀ N, 1 ≤ N → N ≤ P.N (p + 1) ^ 4 →
  ∀ A, (∀ LG ∈ A, Stage1Carries P p N LG) → TwistClosed p A →            -- R44 (i), unchanged
  ∀ tt, (∀ j, tt j ∈ Icc p (p+1)) → ∀ base roots,
  ∀ (U : TypeFamily P (2 * R)) (s : ℝ), 0 < s → U.Bounded p → (∀ LG ∈ A, U.toLF.size LG ≤ s) →
  ∃ S Cl hCl cls members sel, Stage1Partition roots A members cls sel ∧
    (∀ π, (S.piece π).Represents N tt base roots (members (cls π)) (sel π) U.toLF s (S.val π)) ∧
    (∀ π, (S.piece π).Sound p base roots) ∧ (∀ π, (S.piece π).Gsb.order ≤ N) ∧ Stage1Counts C₀ P R N S Cl hCl cls
(definitions: lean/TwistProfProbe.lean)
