# research-flower — FLOWER-DESIGN study (for wt-orch), 2026-11-05/06

Scope: design of the flower Stage-1 chain behind `layergardenFlower_v2` (TARGET Prop flowerest1, L2279–L2306,
and L2312). Posture: refute first. Nothing outside this directory was edited.

Inputs read (hashes of the mutable ones in PINNED-INPUTS.sha256): TARGET L2180–2338 (flower section, fixedpoint);
TARGET L625–760, L824–905 (gardens, canonical, regular objects, structure thms), L1293–1370 (molecules, blocks),
L1723–1760 (redkg, vineest), L1926–2116 (Stage 1/2, subpro, finalsbest, finalcount1); DH23 L1992–2016 (flower
couples, special nodes, ladder extra argument); DH21 L2651–2700 (flower trees, Dirac cases (a)/(b));
flower-s1 HANDOFF/OBSTRUCTION/RULING-R53/PROGRESS; FS9 Defs/Gates/FlowerBound/Final; lg-spine-u Stage1Interface,
Stage1Gate, SourceSplicedKernel, SourceSplicedBounds, MolecularSpineAt, Stage1PieceBound, TypeFamily;
coarse-spliced and ladder HANDOFFs (incl. LADDER-TT addendum); represents HANDOFF; flower-reg HANDOFF;
V5 CanonStatement/Kernel; regred CLLocalTimes; main frozen FlowerSum, KernelKgen, KDomainFix, FixPat,
LayeredGardenFixPat, PatValid, FlowerKindOK, TreeKindOK, CutWeight1/2, SibWeight, DyadicCut, IsCanonH, CoupleSum;
main LFTwist/FamilyState; WaveB/Molecules (IsBlock, garden molecule); RULINGS R5, R11, R12, R23, R44, R53–R57;
codex-takeover/FLOWER-REPAIR-NOTES.md (unvetted; read late; re-derived, see §9).

## 0. Verdict in one paragraph

cx-flower's R11 finding is correct and is not repairable inside the present gate: a pinned time cannot be
represented by averages of all-times-integrated plain spliced kernels with a t-independent mass. But the right
response is not a separate fixed-time Stage-1 package (B), nor "f^pr as a root-like fixed node inside G_sb" (A in
its TARGET-literal form, which drags Dirac regular objects, untwisted exceptional vines and general fixed atoms
into every LG packet). The recommended design (C, "stub excision with anchors") cuts each flower tree at f^pr
*at the garden level*, before any skeleton: the two sibling subtrees become separate trees with root time s
(R33's per-tree caps), every leaf below f^pr becomes an *anchor* (a leaf paired with a fresh trivial tree whose
root label is prescribed), and f^pr itself stays as a *stub*: a branching node with fixed time s whose three
children are anchored leaves. The stub has molecule degree ≤ 1, so it is never in a block, vine, ladder or
regular object (Lean-checked lemma, §7), every flowerest1 carrier constraint becomes a per-tree `topOrder`
constraint (twist-invariant on main), and the resulting gardens are ordinary plain canonical gardens to which
LG's whole Stage-1 chain applies verbatim except for two small interface additions (anchored pairs with profile
1; pendant stubs with a fixed time). The couple clause (2) with ∂_t is handled by *decapitation* (cut the roots,
whose time is t) and needs no new analytic gate at all; `RegularCouplesDtAt` and `CoupleStage1At` disappear.

## 1. Re-derivation of TARGET's flower argument (flowerest1 (1)–(7))

Objects. Flower tree T: ternary tree, one marked leaf f (flower), f^pr its parent. Flower garden of width 2P:
non-flower leaves paired (layer-p pairs, ≥4-groups replaced by G_p gardens), stems in layer p, *no
irreducibility*. Kernel (kqflower): all branch times integrated except t_{f^pr} = s for each flower; decoration
fixes k_root = k, k_f = k'; no input factor at flowers. Frozen form: `kernelKgen` with `fix = fixPat`,
`kDomainFix` (constraints child<parent kept iff one side free), `GenDecoration … (fun _ => n) n'`.

Time structure (from kDomainFix): with f^pr pinned at s, the free children of f^pr have τ < s (a *cap*), and the
free parent of f^pr has τ > s (a *floor*). Everything else is standard. This floor is the entire difficulty: it
is not a root cap, and in V5's CL local kernel a lower boundary is kept only when the excluded child is a branch
(regred CLLocalTimes.lean L71–80: "Lower boundary inequalities are retained precisely when the excluded child is a
branch"). So the floor must be carried by a *branch* with time s — which is why the stub keeps f^pr as a node.

(1) Decay ⟨k−ζk'⟩^{−4ΛP}: non-flower leaves of each tree sum to k−ζk'; weight redistributed to leaves (FS9's
weightCost); M_1 gain from leaf decay. Correct; but see F-CUTWEIGHT (§6) for the cutoff itself.
(2) L^{80d} per flower: sources named by TARGET: S^{40d,40d} norm of 1_{k_f=k'}, atoms f/f^pr, and the Dirac,
"fix Ω_{f^pr} (≤ L^{10d} values once leaves are in unit balls) and drop its phase". Checked: given k' exact and
the two sibling momenta in unit balls, Ω_{f^pr} has ≤ (2L+1)^{2d} values, uniformly in |k'| (it is a function of
the lattice points, not of the range). True, but it does not say how the pinned *time* coordinate is handled in
Stage 2, and it is silent on f^pr inside a regular tree at the flower (DH21 Prop 11.2 proof (3)(a) treats that
case explicitly). Under design C the phase is a constant of the outer sum and no Ω-fixing is needed; the loss is
coupling × (sibling-label sums) ≈ δ·L^{d+γ} ≤ L^{2d} per flower.
(3) k, k' arbitrary: Stage-2 gates are uniform in centres/base/roots (LadderFourierAt is proved uniform, S3a),
so DH23's "extra argument with ladders" (L2013–2016) is not needed in the Lean chain.
(4) Special-node vines: needed in TARGET because the carrier constrains subtree orders at root children and f's
siblings (Y-2, W-2, W-3) and because f^pr carries the Dirac. Observed: (i) "each tree's layer-p order" is
invariant under *all* LF twists (TARGET lftwistprop; main `FamilyOperation.output_topOrder`, type checked §7),
so only (ii)/(iii) and the Dirac need special nodes. Under C, the sibling subtrees are separate trees and (for
kind Y / L0) the root is excised, so (ii)/(iii) become per-tree topOrders; the Dirac sits on a pendant stub. No
special-node exclusion remains.
(5) Stem layers preserved under twists: still needed (stem = ancestors of the stub); TARGET's argument stands;
becomes lemma FT4.
(6) M_2 gain: TARGET integrates t_j first (DH21 Cor 11.3). Not a Dirac issue; see F-CUTWEIGHT.
(7) SG CL vines don't split the stem when |k| ≥ M_1^{10}: needed only for cut2 weight invariance (FT5).

## 2. Why A (TARGET-literal) and B are worse

A (keep f^pr as a degree-3 fixed atom in G_sb). Consequences, each checked against the sources:
- f^pr can be inside a collapsed regular object. With unpaired flowers the prime skeleton must collapse a regular
  tree whose lone leaf is f (TARGET propstructure2: prime = no embedded mini-tree; a mini-tree with lone leaf f is
  embedded). Then the Dirac is inside K*_T: a "Dirac regular tree" (X^η norms of Props 6.x do not control ∂_b).
  With the footnote pairing (f_1 with f_2) it is worse: whole components collapse into regular couples (the
  two-corolla example is a (1,1) mini-couple) — the zero-order case cx-flower hit.
- f^pr can be the bottom joint u_2 of a CL vine (degree 3 atoms are joint-only, but u_2 is integrated inside
  K^U); V5 has no pinned interior time. → exceptional vines, untwisted, which then either stay unspliced in G_sb
  (violating subpro (4) / CountingGeometry → FINALCOUNT changes) or are spliced with a new crude vine bound.
- Stage 2 needs general fixed atoms (inside ladders, with floors and caps, Ω-value partitions).
B (separate fixed-time RepresentsInt/Sound) has all of A's analytic needs plus a second copy of the S2a/S4/S2
producers. Rejected.

## 3. Design C: stub excision with anchors

### 3.1 Construction (garden level, exact)
For flower garden LG (width 2P), tree j, v_j = f_j^pr with children (flower slot, sibling slots σ_j1, σ_j2):
- Detach the subtrees at σ_j1, σ_j2: new trees T_j1, T_j2 (possibly trivial), root labels κ_j1, κ_j2 (outer
  summation variables), root cap s (`tt`).
- v_j stays, fixed time s ("stub"); its three children become leaves, each paired with a fresh trivial tree
  ("anchor") with prescribed root label n' (flower slot), κ_j1, κ_j2, sign opposite to the slot, layer p.
- Kind Y (Y-2), couple kind L0, pattern dRoot: excise the root r_j ≠ v_j completely: its time τ_j is an outer
  variable (integrated over (p,t), or = t for dRoot), its children subtrees become trees with cap τ_j, labels
  outer. (Root excision creates no floor.)
- dParent: the parent u_j of v_j also becomes a stub at s (detach its other two children subtrees, cap s, anchor
  their slots); u_j–v_j is a pendant fixed path (u_j has degree ≤ 2, cannot be a block atom either: a joint
  needs both its block bonds, i.e. v_j in the block, impossible).
- dChild i: decapitate the detached tree T_ji at time s.
Result Ĝ: a plain garden (anchors are trivial trees), per-tree caps, stubs with fixed time s.

Identity (to prove, P1): flowerSum = Σ_{outer labels, outer times} [∏ couplings of excised roots × ε × unimodular
phases] × Σ_{Ĝ} kernelKgen(Ĝ; fix = stubs ↦ s; up = per-tree caps; profiles H on input leaves, 1 on anchor pairs;
wt = transported cut weights). Bookkeeping: order(LG) = order(Ĝ) + #excised roots; ε and ζ split; anchors
contribute no profile; the decoration carrier GenDecoration LG (n,…) n' ≃ Σ_κ GenDecoration Ĝ (labels) 0.
Codex's concern "GenDecoration has one shared marked label" is met by anchors (one label per trivial tree).
Dagger: sibWeight fixes κ_j1, κ_j2 = c j i (outer sum collapses); `offs` drops the stub's constant phase.

### 3.2 Why the stub is harmless
- Garden molecule (main WaveB/Molecules L229–233): leaf pairs with a root leaf give no bond, so a stub has degree
  1 (0 if it is the root). Lean: `not_mem_block_of_deg_le_one` (§7) ⇒ never in a block ⇒ never in a vine, VC,
  ladder, spliced region or twisted region.
- Never inside a regular couple (it has ≥2 anchors paired to distinct trivial trees) nor strictly inside a
  regular tree (its children are leaves paired outside). It can be the lone-leaf position m of a regular tree
  above it: factor K*_{T(m)}(t_{m^pr}, s) — the standard two-time regular tree kernel with second argument s.
  So *no Dirac regular object ever arises* (DH21 case (a) disappears).
- It can be u_21/u_22 of a CL block: V5's K^U takes the external time t 1 = s (a branch: the lower boundary is
  kept). V5 applies verbatim.
- Its momenta are all prescribed (anchors) ⇒ Ω_stub, ε_stub constant ⇒ in Stage 2 it is a constant phase plus a
  floor on its parent; in the count its restriction is satisfied by choosing β_v = Ω_v (countE takes ⨆ β).

### 3.3 Components
Ĝ is reducible in general (TARGET: moments, no irreducibility). The kernel factors over components; carrier
conditions (canon criterion, attached orders, topOrders, signs, PatValid, cut weights per tree) are
component-local except total order N; sum over set partitions and order compositions (≤ Bell(w)(N+1)^w terms,
absorbed by the slack: FS9 already gets δ^{8νN} L^{−η^7} against δ^{2νN} L^{(100d)^3P}).
Component types: (i) lone stub (v_j = r_j, all children anchored): closed form, no time integral;
(ii) trivial couples (two detached leaves paired): a profile value; (iii) regular couples (no stub can be in a
couple: a stub brings 3 anchors): LG/FLOWER-REG pointwise regular bounds (two-time, leafwise);
(iv) nonregular couples: LG Stage1ReductionAt at R = 1; (v) width ≥ 4 irreducible: LG Stage1ReductionAt with
anchors and stubs. Canonicity of components: canonequiv (i)+(ii) with anchors/stubs in layer p (lemma, P1).

### 3.4 Twists (R53 replacement)
FlowerTwist := the universe's LF twist of each Ĝ-component (it is plain and a CanonicalObject), i.e. R53's
"underlying plain garden" option, with the completion made precise (anchors, not flower-to-flower pairing).
No special-node restriction. Obligations:
- FT1 order data: per-tree topOrder, order, IsTrunc, canonical — on main (FamilyState output_*).
- FT2 anchors: the twist leaf map φ (LFTWIST-LEAFMAP) sends anchor pairs to anchor pairs (pairing and tree
  membership preserved — the same facts R47 P* TypeFamily relies on).
- FT3 stub rigidity: a stub (branch whose children are all anchored leaves) and its anchors are fixed by every
  LF twist (from §7's lemma + "twists act only on block realizations and regular replacements").
- FT4 stem layers: all ancestors of a stub are in layer p after the twist (TARGET (5)).
- FT5 (cut2 only): |k| ≥ M_1^{10} ⇒ SG twists preserve stem Ω's (TARGET (7)).
- FT6 weights: cut1 (per-tree max over top leaves) is φ-compatible (layer and tree preserved).
With FT1–FT4 the Ĝ-sets are TwistClosed under LG's *full* relation, so V5's class sums give the full
cancellation; no exceptional vines.

### 3.5 Irreducibility
LG uses it (Sound.irreducible, Coarse/FinalCount `G.Irreducible`, connected molecule, the (R−1) gain). C
replaces it by the component decomposition of §3.3; the (R−1) gain is unused (not needed for flowers).

## 4. Couples (clause (2)) and RegularCouplesDtAt (Q3)

`coupleSum … dt = true` pins both roots at t. Decapitation (∂_t J_T = coupling·Σ ε e^{iΩt} J_{T1}J_{T2}J_{T3}):
excise both roots (no floors), children trees get cap t, outer sums over children labels (2 free per root).
Result: sums over width-6 gardens (components of width 2, 4, 6) with caps t: LG Stage1ReductionAt (R33 caps
suffice) for nonregular components, regular-couple pointwise bounds K*_Q(t,t) (FLOWER-REG's
`regular_family_pointwise` form) for regular/trivial ones. Loss: coupling²·L^{4d}·C = δ²L^{2d+2γ}/4·C ≤
L^{100d}. Decay ⟨k⟩^{−4Λ}: ⟨k1−k2+k3⟩^{4Λ} ≤ 3^{4Λ} max⟨ki⟩^{4Λ}, redistributed onto the children trees.
δ^{2νN}: δ² from the two couplings × LG's δ^{c(N−2)}. For L0 with dt = false (root-children constraint) use the
same decapitation with τ_r outer-integrated (unequal caps: needs two-time pointwise regular bounds — to confirm
the leafwise gates are two-time). So:
- `RegularCouplesDtAt` needs no Dirac regular-object analysis and no Stage 1; R12's assignment to the flower
  Stage-1 machinery was mistaken (a regular couple has trivial skeleton; Stage 1 returns the excluded order-0
  piece — cx-flower's observation). Its exponents (δ^{2νN}, L^{100d}) are met.
- `CoupleStage1At` (dt couples) also disappears: same decapitation.
- `RegularCouplesL0At` (FLOWER-REG) stays as proved.

## 5. Interface changes (proposed ruling text)

LG-SPINE AMEND-ST (shared; LG instance = no anchors, no stubs, so LG's statements are special cases):
- `SplicedKernelData` gains `stubTime : GBranch G.tree → Option ℝ`; `splicedTimeDomain`/`splicedTimeIntegral`
  integrate over `{b // stubTime b = none}` with kDomainFix semantics (child<parent iff one side free).
  Bridge lemma: `stubTime = fun _ => none` gives the present definitions.
- `Stage1PieceD` gains `stubs : Finset (GBranch Gsb.tree)`; `RepresentsInt` gains the stub time `ts : ℝ`
  (data: stubTime b = if b ∈ stubs then some ts else none); mass bound unchanged.
- `Stage1Piece.Sound` gains `stub_pendant : ∀ b ∈ π.stubs, π.Gsb.molecule.deg b ≤ 1 ∧ every child of b is a leaf
  paired with a root leaf`.
- `TypeFamily`/`LeafFamily`: anchored pair types (partner is a trivial tree in a designated set `Anch`) carry
  profile ≡ 1, are exempt from `Bounded`, and are excluded from `size`; their labels are part of `roots`.
- `Stage1ReductionAt`: add `Anch` and the stub set (determined by the garden: branches all of whose children are
  anchored); `Stage1Carries`, `TwistClosed`, `Stage1Partition`, `Stage1Counts` unchanged.
- Stage-2 gates `CoarseSplicedAt`, `LadderFourierAt`: quantify over data with `stubTime` supported on pendant
  stubs (premise); conclusions unchanged. `FinalCountAt` unchanged (time-free). Proof routes: coarse — integrate
  over free coordinates, stubs are in no ladder (S3c Assembly1 only); Fourier — B_stub = e^{iπα_v s}(B − B_cap)
  with a cap s on the stub's parent (S3a engine already takes per-node caps, LADDER-TT addendum), stub σ fixed;
  fine assembly (Cover) chooses β_v = Ω_v at stubs.
- Width range: Ĝ has 6 trees per flower tree (U_j, T_j1, T_j2, 3 anchors), 8 with root excision, so components
  reach R = 8·Pm ≤ 80·R_{p+1}. Every LG gate quantifies `R ≤ 10 * P.R (p + 1)`: AMEND-ST must widen this to
  `R ≤ 100 * P.R (p + 1)` (to be checked by the S3a/S3c/FinalCount/S2 owners that the constant 10 is only a
  range; TARGET layergarden uses 10R_{p+1} for its own cumulant ranges). Pieces of Ĝ need no L-loss: anchors
  only add roots, which improves the (R−1) factors; the only loss is the crude κ-sum, ≤ C·L^{2d} per flower.
FS9: `FlowerSpineInputs` keeps `coarse`, `ladder`, `leafCoherent`, `leafDecay` and gains `stage1 :
Stage1ReductionGate` (AMEND-ST form, word for word LG's); DROPS `gardens`, `couples`, `regularDt`.
`FlowerStage1At`, `CoupleStage1At`, `RegularCouplesDtAt`, `Stage1PartitionG` are deleted; their content becomes
proved adapter theorems (P1, P2, P3, P7).

## 6. F-CUTWEIGHT (separate gap, independent of the Dirac)

Frozen cutWeight1 = ∏_j χ₀(max_{top leaves a of tree j} |k_a| / M)-type, cutWeight2 likewise over stem Ω's. For
decreasing χ₀, χ₀(max_a y_a) = min_a χ₀(y_a): a joint, non-factorizable, only Lipschitz decoration weight. The
spliced-kernel amplitude slots (per-bond smooth edge amplitudes, hinge K† on hinge darts, gap indicators) cannot
carry it, and coarse ladder bounds need smooth per-bond structure on ladder bonds (top leaves can be ladder
bonds). So FS9's current gate (weight inside `termSel`, M_1/M_2 gains inside the RepresentsInt mass) is not
producible as stated, with or without the Dirac. TARGET (1)/(6) treat the cutoff as harmless (gap). Candidate
routes for a separate research item: M_2 gain by an exact integration by parts in the time of the arg-max stem
node made an outer-time stub (derivatives of caps = decapitations, crude); weight via layer-cake
χ₀(max) = ∫∏_a 1{y_a<u} μ(du) needs indicator restrictions on bond momenta/Ω's in Stage 2. Recommend: rule the
plain clause (no cutoffs) first; open FLOWER-CUT as research with STOP authority.

## 7. Lean checks (transient, probe/PendantBlock.lean, sha in probe/SHA256SUMS; log logs/PendantBlock.log)

Run: `cd /home/scott/WaveTurbulence-dev && nice -n 5 lake env lean …/probe/PendantBlock.lean` → exit 0.
- `two_le_deg_of_mem_block : M.IsBlock S j₁ j₂ → v ∈ S → 2 ≤ M.deg v` and
  `not_mem_block_of_deg_le_one` (main `Foundations/WaveB/Molecules`); axioms propext, Classical.choice,
  Quot.sound.
- `#check FamilyOperation.output_topOrder : h.output.layered.topOrder p j = A.layered.topOrder p j` (main).
Not checked in Lean: the excision identity, canonicity transfer, FT2–FT6, the Stage-2 pendant proofs.

## 8. Errata / gaps in TARGET L2280–2312 (candidates)
E-F1 (L2261/L2287, gap): the skeleton of a flower garden is undefined; the footnote's flower-to-flower pairing is
not a valid completion for the skeleton (merges components, creates regular couples). CANDIDATE: "complete each
flower by pairing it with a trivial tree whose root carries k'; skeletons and twists are those of the completed
plain garden; the stub construction keeps f^pr outside every regular object and vine."
E-F2 (L2295 (2), gap): the Dirac's removal of the t_{f^pr} integration is called a bounded loss without saying
how Stage 2 (counting/Fourier, Props ladderl1old/finalcount1) handles a pinned coordinate, and without the case
f^pr inside a regular tree at the flower (treated in DH21 Prop 11.2 (3)(a)). The "≤ L^{10d} values of Ω" claim
is correct (≤ (2L+1)^{2d}, uniform in k').
E-F3 (L2297 (4), gap): untwisted special-node vines "treated trivially" are not compatible with Prop subpro (4)
if left unspliced; and (i) needs no special nodes (lftwistprop). CANDIDATE: replace (4) by the stub/decapitation
reduction, after which every LF twist preserves H^tr_{p+1}.
E-F4 (L2312, gap): "∂_t a^tr … same arguments as flowerest1" — for regular couples Stage 1 is vacuous; the
correct argument is decapitation (∂_t of a tree is the cubic term at time t) plus non-Dirac bounds, loss L^{2d+2γ}.
E-F5 (L2294 (1), L2299 (6), gap): cutoffs as smooth functions of maxima over many leaves/stem nodes do not factor
through the redvine representation; see §6.
E-F6 (L2296 (3), exposition): "all proofs translation invariant" contradicts DH23 L2013–2016; harmless in Lean
because LadderFourierAt is proved uniform in centres.

## 9. The Codex note (FLOWER-REPAIR-NOTES.md, unvetted)
Re-derived independently; agrees on: retain designated times; components/no irreducibility; one shared marked
label is insufficient; "cut one fixed parent" with the prefix floor "parent of the new lone leaf has time > s".
It leaves the floor as a constraint on an anchored *leaf*'s parent; that is exactly what V5's CL local kernel
drops (lower boundary only for branch children). The stub variant (keep v as a branch with time s, anchor its
children) is the fix. Its other claims (shifted counting, dummy coordinates) are not needed under C.

## 10. Packets and effort (honest, after LG's S2/V5/CLASSCOUNT are READY for the parts that consume them)
P0 LG AMEND-ST interface (LG-SPINE owner): 0.5–1k lines, 1–2 sessions. Do it now, before S2 finishes.
P1 FLOWER-EXCISE: construction (setAt/subtreeAt), anchors, stubs, decoration/time-measure bijection, kernel
   identity, carrier transfer (canonicity, kinds → topOrders, PatValid), patterns, root excision:
   3–5k lines, 6–10 sessions (Opus).
P2 FLOWER-COMP: components, order compositions, aggregation of piece bounds: 1–1.5k, 2–3 sessions.
P3 FLOWER-TWIST FT1–FT4 (+FT5/6 with cutoffs): 1.5–3k, 3–5 sessions.
P5 STAGE2-STUB (S3c, S3a, Cover owners): 1–2k, 2–4 sessions.
P6 S2 adaptation (stub time through redvine; anchored pairs in the centre-sum mass): 0.5–1.5k, 1–3 sessions.
P7 COUPLE-DECAP (clause 2): 1.5–2.5k, 3–4 sessions; replaces CoupleStage1At + RegularCouplesDtAt.
P8 FLOWER-CUT research (F-CUTWEIGHT, M_1/M_2): unknown; research first.
P9 FS9 rewiring: 0.8–1.5k, 2 sessions.
Total ≈ 10–18k lines, ≈ 20–35 sessions excluding P8. S2a, S4, V5, CLASSCOUNT, FinalCount: reused unchanged.
Order: P0 now; P1, P3, P7 in parallel with LG Stage 1 (structural, need only main's universe and the frozen
kernels); P5 after LG Stage-2 gates are frozen; P6 after S2 READY; P2, P9 last; P8 research in parallel.
Thin adapter: yes in the sense that no flower Stage-1 gate remains — the flower chain becomes LG's (amended)
gates plus proved adapters; but P1 (the excision identity) is a substantial packet, not "thin".
