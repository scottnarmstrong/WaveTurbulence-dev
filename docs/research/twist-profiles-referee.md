# Referee report on TWIST-PROFILES design P* (saved by wt-orch from the referee's final message, 2026-11-05)

The referee could not write this file itself (harness), so wt-orch saved its final message verbatim in substance below.
Probe copies and Python checks: probes/ in this directory.

Pinned inputs (hashed at first read 14:19 UTC and re-hashed at the end; no drift):
- NOTES.md c670ac84…, CentralDiff.lean a84c182d…, TwistProfProbe.lean eccbf1eb…, VineLeafProbe.lean 63d11489…
- V5 LayerStatement.lean bafd544e…
- lg-spine-u src/Stage1Interface.lean changed at 14:21 (AMEND5/R48 work, after the build-fresh-a5 olean); LeafFamilyD
  unchanged, so this does not matter.

## Items

1. Q1, no movement between root trees: OK.
   - For a CL block, u2 is a descendant of u1, and the realization desc(u1) \ desc(u11,u21,u22) is completely paired
     (TARGET L1348, DH23 L745). So every region row is a regular couple or tree paired internally, and every region
     input leaf has type (q,j1,j1).
   - Twists stay inside desc(u1): (I-a)/(I-b) only the subtree at u1; (II-a)/(II-b) the subtrees at u3, u4, which are
     under u1; (II-c)/(II-d) u3 is a descendant of u1; the free subtrees T1, T2, T3 likewise.
   - LF twists swap T_(u2) and Q_(u23,u0) with total order and layer-p count fixed. Both lie in one tree, so per-tree
     orders are preserved.
   - (II-e) and (III)-(VIII) are never twisted, and their regions are CL.
   - Only CN vines can span two trees. They are never twisted and never enter 𝒱 (defcong adds CL vines only); a VC in
     𝒱_0 is a chain of CL vines, which is CL.
   - Root CL blocks in cnblock (ii)/(iii) pair a free child with another tree's root, but that leaf is outside the
     realization.
   - Side point: LEAFMAP F-ROOT's "leaf counts per tree change under a twist" is literally false; only the leaf sets
     differ.
2. The identities: OK.
   - (a) partialMom_kernelLeaves_eq_sum (translation invariance). The leaf sum equals [ε¹] K(h + ε∂h), because
     typeProfiles is linear in h.
   - (b) sum_rule, decoration_positiveRepresentative and inputLeaves (the + unmarked leaves) give
     σ_{j0} k_{j0} = Σ_a ([a.1=j0] − [(pair a).1.1=j0]) k_a, exactly the pairTrees-built M^{(j0)} slope. A pair with
     both leaves in j0 gets 1 − 1 = 0.
   - (c) Each evaluation h + s·Oh is real and pair-type uniform, independent of the garden, with one bound; A is
     unchanged. On vine regions the M-terms vanish, so the input is the layer-uniform jet h(·,j1,j1); PL234's
     reality_all holds for any real F.
   - A numerical toy (5 typed pairs, 3 trees) reproduces (M) to ~1e-13, nested (M)(M) to ~3e-13, and (D) against a
     finite difference to ~6e-8.
3. Central differences and loss: OK, with fixes F1–F3.
   - first_coeff_extraction and abs_cw_le re-elaborate with standard axioms.
   - An exact-rational check confirms the extraction for M ≤ 7 and shows a nonzero leak at degree 2M+1, so the degree
     bound is essential. It holds: Stage1Carries fixes order = N on A.
   - Σ|w_k| = H_M exactly.
   - ‖k^i f‖ ≤ (1+a)‖f‖ with one more decay power, so u = 40d + r + 1 suffices. The bound C₁ + 2/(N+R) holds but
     needs V ≥ 1 (F1).
   - N, R and m are polylog in L (parameters2; N_quartic_le_log_pow). Λ, Cφ and C₁ are fixed before L, and the order
     of constants matches WTPrefix and prefix_late.
   - Absorption: C₁^N by δ^{6νN}; for gardens, the rest by L^{−(m−1)/70} when m ≥ 2; for couples, by the θ-margin as
     E2 does. The existing garden threshold E1 cannot absorb this as written (F3).
4. Gate change: OK.
   - represents_noVine accepts any Controlled LeafFamily with size ≤ s, so U.toLF fits.
   - The vine case is V5 with h = U.h i · j1 j1 and B0 = U.b i; region times outside gives b^{N+R} = size_eq.
   - S2 needs two lemmas: the pair-type pullback to native rows, and the root-tree index of attachment points (likely
     LEAFMAP's ordinary_couple_root_index / branches_index).
   - The consumer can apply the gate per evaluation: stage1_family_bound is linear in s; Represents and Stage1Counts
     are untouched.
   - stage1ReductionAtT_of_old re-elaborates. It only shows the new gate is weaker; the old gate is false. Whether the
     new gate is true rests on V5 plus S2, and no counterexample was found. TwistClosed is still abstract and must be
     pinned.
5. Couples (R = 1): OK.
   - <k>^{4Λ} = (1+|k|²)^{2Λ} expands into (d+1)^{2Λ} terms, each (k^i)² being two M^{(0)} operations.
   - Tree-0 forms suffice because σ0k0 + σ1k1 = 0.
   - Pair types: (q,0,1) gets +k^i h, (q,1,0) gets −k^i h, same-tree types get 0.
   - Derivatives must be innermost (F4).
6. VineEstCanonLeaf = VineEstCanonLayer (rfl): OK. regionLeafSize covers clRegionalPairs (both leaves internal, CL
   condition (iii)) and the interior branches, so no region leaf has another type or is paired outside. RowCoherent
   for h(·,j1,j1) comes from V5's GateH with a constant bound.
7. Erratum E-TWPROF: the gap is real; the description is accurate with the corrections in F6.
   - L2065 is a pointwise inequality inside an oscillatory sum.
   - L2067's Leibniz terms hit T_(u2) and Q_(u23,u0).

## Fixes
- F1: use max(1, V) in λ (or U = Cφ + 1). With V < 1 the higher-order terms scale like V^{1−|S|} and b fails.
- F2: per type (q,j,j′) only the forms of trees j and j′ act: at most 8Λ multiplications (4Λ for couples) and at most
  4Λ derivatives. This keeps the existing hU/hhigh bounds sufficient.
- F3: rewrite E1 for gardens as a log-type threshold uniform in 2 ≤ m ≤ 10R_{p+1} and N ≤ N_{p+1}^4, counting the
  (d+1)^{4mΛ} expansion terms. The current constant threshold relies on the per-tree Cb^w·2^N bound, which fails for
  the P* loss when N ≈ m is large.
- F4: X_{O::rest}(h) := Σ_k (w_k/λ) X_rest(h + λ(k−M)·Oh), with O innermost. The opposite order computes
  ∂^word(forms·V), which is wrong.
- F5: give a ℂ-valued version of first_coeff_extraction, since kernel values are complex.
- F6: E-TWPROF wording.
  - "2M = n+R" should be "2M ≥ n+R".
  - The loss is absorbed by the L-power margins with n, R polylog, not "as in L2065".
  - NOTES Q3(ii) overstates the root-weight obstruction; the real one is the class-uniform index.
  - Optional notes: (3n_j) fails for trivial trees, use 2n_j+1; "at most R input factors" should be 2R; for couples
    the weight is <k>^{4Λ}.
- F7 (scope): FLOWER-SPINE's FlowerStage1At (FS9/Gates.lean L100) and CoupleStage1At (L128) take arbitrary per-garden
  H and arbitrary A, and redistribute weights inside the gate "as in L2065". They have the same defect and must
  mirror P*, presumably with (M) over non-flower leaves (L2293). Not verified.

## Probes re-run
All with nice -n 5, one at a time, no maxHeartbeats.
- TwistProfProbeR.lean via research-twistprof/lean/probe.sh against lg-spine-u build-fresh-a5: exit 0, standard
  axioms.
- CentralDiff.lean via lake env lean in the cumul worktree: exit 0, two deprecation warnings, standard axioms.
- VineLeafProbeR.lean via vineest-s3/uni/probe5c.sh: exit 0; vineEstCanonLeaf_eq_layer by rfl; standard axioms.
- cw_check.py (exact rationals) and toy_identities.py.

VERDICT: ADOPT_WITH_FIXES (F1–F7)
