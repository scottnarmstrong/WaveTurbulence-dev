# VINES scratch progress

COUNT landed; `w/count` merged main at `37c6fbb` before starting M4.
Lean work is under `/home/scott/wt-scratch/vines/`, with copied MOLE source
hashes in `COPIED-SHA256.txt`; no writes to `/home/scott/wt-scratch/mole/`.
See the scratch `HANDOFF.md` for current definitions and verification status.
M4 remains in progress; this is a checkpoint, not a completion claim.

The checked scratch interface now includes expanded atom/bond/group counts,
degree profiles, sigma, group partition, template and actual-vine connectivity,
ladder length, coherence index, and boundary conservation. The 12-result axiom
probe reports only standard axioms. `subsetvc` remains in progress.

The exhaustive block/hyper-block degree-mask checks now pass for all eight
base cores. The larger cores are split by joint pair to stay within default
budgets. Applying the tables to arbitrary rung expansions remains in progress;
this checkpoint does not claim `subsetvc`.

The actual-atom group partition/sizes/index, lattice gap-norm conservation,
and connectivity of all drafted vine-like classes are checked. A new actual
half-edge recurrence proves matched rung membership for arbitrary full-rung
sequences of length >=3, and constant membership for connected blocks larger
than a double bond. The 24-result axiom audit passes with standard axioms only.
The final `subsetvc` classification/removal theorem remains in progress.

The pinned realization now supplies actual full-rung sequences for every
expanded slot, with exact labels and no extra incidence hypotheses. This
proves constant membership/no fresh joints for connected blocks larger than
a double bond on every slot of length >=3. The two-cut direction fact is
also derived from actual block degree balance. The expanded interface and
50-result standard-axiom audit pass; subsetvc remains open, including the
short-slot and simultaneous-removal arguments. See the scratch HANDOFF for
exact checked modules and commands.

The zero-extra-rung classification now proves that proper VC subsets in
all eight cores are one/two concatenated double bonds; its decorated SG case
derives properness from gap separation. The source removal operation keeps
joints and removes non-joint atoms/bonds. Connectivity after any disjoint
family of adjoint removals is now proved using retained actual added bonds.
The interface and 74-result axiom audit pass with standard axioms only.
Arbitrary-rung classification and ordinary-block removal remain open; M4
continues. Main was merged at 1666da7.

`SG_VC_in_nonVII` now proves the ordinary inner-VC source classification
for seven outer vine types, with arbitrary rung counts and no extra witness
premises. Empty-stem propagation covers k=0,1,2 as well as long ladders.
Hyper-block full-rung masks have at most one transition. VineTools and the
99-result axiom audit pass with standard axioms only. Type VII side-ladder
recognition, hyper-vine/HVC containment, ingredient localization, DV and
mixed block-removal connectivity remain open; work continues.

Type VII now has a proved exact side-region characterization, joint pair,
and cardinality5+2kc. Actual branching at both side joints excludes the short
kc=0/1 cases for a VC. The remaining explicit type-V relabeling is in progress.
VineTools and a112-result axiom audit pass with standard axioms only.
Hyper/HVC containment, localization, DV, mixed removals and canonical
coherence-group independence remain open; this is not a READY claim.

## All eight ordinary VC-in-one-vine cases proved

`SG_VC_in_single_vine` now proves the ordinary VC clause for every outer
vine type with arbitrary rung counts. Its inputs are the source molecule,
containment, decoration, full-degree c=0 and SG versus LG/ZG gap premises.
The output is one double bond, two concatenated double bonds, or an actual
pinned type-V vine inside type VII. There is no side-shape or graph-isomorphism
premise in the source theorem.

The VII proof constructs an explicit natural-label bijection and inverse.
`typeVII_side_restrict_bonds` computes the induced side edge list exactly;
`sideEmbedding_bonds` and `sideInverse_bonds` identify all bond multiplicities
with the pinned V expansion. A side with m+2 full rungs corresponds to m
extra rungs of V. `selected_typeVII_side_isVine` transports the graph identity
to actual atoms and proves every witness of the unchanged IsVine predicate.
`typeVII_inner_VC_isVineV` obtains that construction from the proved side
closure and short-case exclusion, with no presupposed vine recognition.

New checked source modules: VineRestrictBonds, VineRestrictInsertion,
VineSideBaseRestriction, VineSideRestriction, VineSideRelabel,
VineSideBijection, VineRailReversal, VineSideRailLists, VineSideRailBonds,
VineTypeVEdges, VineSideGraph, VineSelectedBonds, VineExpansionEndpoints,
VineSideGraphInverse, VineSideRealization, VineSGSingleVine.
All compiled serially using the documented scratch command: exit0,
zero warnings. VineTools and validation/Axioms.lean also exit0 with zero
warnings. Complete lists for122 declarations in validation/Axioms.log
contain only propext, Classical.choice, Quot.sound (parsed including wrapped
lists). No new errata or deviations.

M4 remains open: hyper-vine/HVC containment, localization across ingredients,
DV, mixed ordinary-block simultaneous removal, and realization-independence
of the coherence grouping. Continuing directly with those goals.

## Arbitrary-rung hyper-block core classification and prefix/suffix checkpoint

`hyperBlock_core_mask_exhaustive` now proves that every actual hyper-block
subset of any expanded vine has exactly one of the nonempty finite hyper-core
masks. This holds for all rung counts. It follows from the source two-boundary-
bond bound, an exact boundary/cut-multiset bridge, and `expand_rawCut_le`: rung
insertion cannot reduce the original core cut. `hyperBlock_has_core_label`
excludes the empty mask by covering every fresh allocation interval and applying
the proved absent-port sequence lemma. No cap-shape, cut-budget or incidence
certificate is added as a source hypothesis.

`noncap_vine_no_hyperBlock_subset` rules out every hyper-block subset inside
types I--IV, independently of decorations and gap sizes. `hyperBlock_core_profile`
identifies the old atoms in all remaining cases as the explicit cap cores of
V, VI, VII and VIII. Fresh membership is still treated separately.

`hyperBlock_absent_interval` and `hyperBlock_sequence_prefix`/`suffix` prove
that an absent far port forces the actual selected rungs into one prefix or
suffix, including empty selections and all endpoint cases. The nonempty prefix
front is exactly the two hyper-block joints. The source type-II full-ladder
construction and exclusion were also checked independently before the cut route.

New source families: HyperJointExclusion, HyperEmptySequence, HyperExternalPairs,
ExtendSequence/Edges, SlotBoundaryEdges, RailEndpointInjectivity, SlotFullDistinct,
TypeIISequence, HyperBadTypes; CutWeights, RawCuts, ExpansionCuts, BinaryCuts,
Core{I,...,VIII}Cut, CoreCutClassification, HyperCoreCut, FoldAllocationCover,
HyperCoreNonempty, HyperCoreMasks, CoreMaskMembership, HyperCoreProfiles;
SliceSequence, HyperGapInterval, HyperPrefixSuffix (all prefixed Vine).
Every listed module compiled serially, exit0 zero warnings, without budget
changes. VineTools and the143-declaration axiom probe also exit0 zero warnings;
all complete parsed axiom lists contain only propext, Classical.choice, Quot.sound.
A duplicate template_slot_endpoints introduced in ExpansionEndpoints was removed
in favor of importing the existing declaration; affected consumers rebuilt cleanly.

Finite cut certificates use explicit three-unit integer flows. Naive global
arithmetic exceeded the default budget; a type-VI flow compile grew too large
and was terminated. Applying the lean-elaboration skill, clean-context flow
proofs reduced the one-declaration probe to2.35s and about1.9GB peak RSS versus
an interrupted baseline over one minute and about10GB. Logs: validation/
CutFlowBefore.log and CutFlowAfter.log. All eight final flow tables compile
cleanly within defaults; the largest is538 lines. No mathematical statement
changed, no new source erratum or deviation.

Remaining M4: recognize the full hyper caps and their adjoints, localize across
ingredients, handle DV, mixed ordinary-block simultaneous removal, and prove
realization-independence of coherence grouping. M4 is not ready; continuing.

## F69: relevant VINES evidence and exact dependence on the current B2 family

The orchestrator reports an independently checked Y2/ylem1 counterexample and
is investigating the figure/template reading. VINES has the following related
kernel-checked structural evidence; it does not settle which reading is correct.

1. `typeVII_inner_full_side` and `typeVII_inner_side_card` identify the full
   type-VII side as the triangle, its two old side joints, and kc full cyan
   rungs. It has exactly5+2kc atoms. In particular the literal side graphs at
   kc=0 and kc=1 have5 and7 atoms. `typeVII_selected_side_branches` proves two
   distinct neighbors at both joints for all kc, including those short cases.
   The graph definitions in VineSideBonds and the exact restriction theorem
   typeVII_side_restrict_bonds apply uniformly at kc=0,1. Recognition as the
   pinned type-V family is proved only for kc=m+2, i.e. at least9 atoms.
2. The normal triangle cap has3+2r atoms and its designated adjoint has the
   same atom set. With r=1 or2, these are five/seven-atom adjoint blocks with
   branching joints (`CapPrefixData.erased_front_branches`). The generic cap
   label/edge identities and actual bond-deletion identities include these
   values; they do not require those graphs to be excluded or to be vines.
3. Crucially, `typeVII_VC_side_length`, the short-cap exclusion
   `CapPrefixData.short_prefix_not_hyperLike`, and the source VC classification
   `SG_VC_in_single_vine` use `not_isVC_five_or_seven_of_branching`. That proof
   uses the CURRENT B2 minimum sizes (typeII at least6, normal types at least9)
   and chain-end counting. They are correct relative to the pinned B2 family;
   they are not independent evidence that the paper excludes five/seven-atom
   vines. If the approved family is enlarged, these exclusion theorems must
   be replaced, and the containment classification revisited.

A possible place to inspect is the distinction between the two fixed doubled
pairs in the current type-V core and the optional rung insertion: the present
expansion inserts extra pairs without removing or identifying either old pair,
so its9-atom minimum is built into the draft. VINES has not independently
resolved whether the source figure/Definition5.1 permits those pairs to vanish.
No claim of a new source erratum is made here.

Cheap parameterization is already retained: raw-cut monotonicity is for any
VineTemplate and valid insertion instruction list; four-dart, sequence, finite
label, cap-label, cap-edge and actual deletion lemmas are generic. Primitive
CapPrefixData includes r=0,1,2. Template-specific finite tables and size-based
recognition/exclusion results are kept separate. Continue pending the owner's
F69 ruling; no pinned draft is changed.

## Cap reconstruction and source type-VII hyper-object checkpoint

The new scratch modules `VineCap*.lean`, `VineHyperVIICapRegion.lean`,
`VineHyperVIICapData.lean`, `VineHyperVIIClassification.lean` and their
incidence/label/deletion helpers now reconstruct the complete cap bond multiset
from actual four-dart incidence rows. Deleting exactly the designated bond gives
a type-V realization for prefixes of at least three rungs. The zero-prefix case
gives two double bonds; prefixes of one/two rungs are excluded only using the
current B2 family, as recorded under F69.

`hyperLike_in_typeVII_adjoint` constructs every primitive cap field directly
from source containment in an arbitrary-rung type-VII vine and proves that an
HV/HVC has a designated adjoint which is two double bonds or a type-V vine.
It assumes no cap realization, mask, prefix, incidence witness or conclusion.
The generic cap reconstruction includes all short prefixes and remains separate
from the template-dependent exclusions. No pinned draft changed.

Checks: all new focused modules compiled with exit 0 and no warnings;
`VineTools` compiled with exit 0; the expanded `validation/Axioms.lean` printed
156 checked declarations with exit 0. All reported axioms are subsets of
`[propext, Classical.choice, Quot.sound]`. An initial audit used a misspelled
helper name, corrected to `capBonds_bondMultiset` before the successful rerun.
`git merge main` completed cleanly at 511cf7f (main 6ce6c6d).

Still required: source cap constructions V/VI/VIII, full hyper-object
classification, chain/DV localization, ordinary simultaneous removal and
realization-independent coherence. M4 is not complete. Continuing directly.

## All-eight-types hyper-object containment checkpoint; F69 resolution

`VineSideVData`, `VineSideVIData`, `VineSideVIIIData` construct their full
actual cap frames, including the old doubled pairs. `VineHyperVCapData`,
`VineHyperVICapData`, `VineHyperVIIICapData` construct selected cap prefixes
from source containment, excluding unrelated slot allocations by the actual
cut profile. Shared helpers: `VineSlotCoreSeparation`, `VineCapFamilyDistinct`,
`VinePrependDistinct`, `VineCapPrefixConstruction`.

`VineHyperSingleVine.hyperLike_in_single_vine_adjoint` now proves TARGET
subsetvc's hyper-object structural clause inside **any** single vine of the
eight types, for arbitrary inserted rung counts. The resulting designated
adjoint is two double bonds or Vine V. No gap premise, cap/mask premise or
realization-shaped auxiliary hypothesis occurs in this source theorem.

Checks: every new focused module compiled with exit 0, zero warnings. The
updated `VineTools` and `validation/Axioms.lean` both exited 0. The audit now
prints 172 declarations, all with only subsets of `[propext, Classical.choice,
Quot.sound]`.

Owner resolution of F69 (2026-11-04): the B2 templates are correct, independently
checked against all eight DH23 Vines.png templates and Remark 5.2(c); see
`/home/scott/WaveTurbulence-dev/docs/research/ylem1-investigation.md` (read).
The defect is DH23 ylem1, repaired as ylem1′ / Prop 10.4(2)′. No changes to
`VineType.template`, `insertRungs`, `expand` or `IsVine` are authorized or
needed. The earlier conditional warnings about possibly changing the family
are superseded by this ruling. Short-cap exclusions remain explicit valid
consequences of that confirmed family. This packet introduces no deviation.

Still required: chain/DV localization using gap separation, full simultaneous
ordinary/mixed removal, realization-independent coherence. M4 remains active;
continuing directly after this commit.

## Arbitrary-rung vertex connectivity and single-ingredient localization

New checked modules `VineAvoidPaths`, `VineRailAvoidPaths`,
`VineSubdivisionAvoidPaths`, `VineInsertionVertexConnected`, the eight
`VineCore*AvoidPaths`, `VineBaseVertexConnected`, `VineExpansionVertexConnected`
and `VineVertexConnected` prove that deleting any one atom leaves every
actual vine connected. The arbitrary-rung argument is generic edge subdivision,
with a separate proof that every surviving fresh atom reaches an old port.
All base witnesses are explicit kernel-checked paths, generated by the recorded
`validation/GenerateVertexPaths.py`; no native decision procedure is used.

`VineBlockSeparator` and `VineSeparatorLocalization` derive terminal-block
closure and single-vine localization across an actual chain junction.
`VineGroupDegreeUnion`, `VineChainBlock`, `VineChainIngredients` construct
prefix blocks, ingredient certificates and `vine_in_chain_ingredient`: every
single vine contained in a VC lies in an actual ingredient. No separator,
prefix-block or localization hypothesis is added to that source theorem.
Loops and orientation are handled explicitly in the shared-joint degree proof.

Checks: all focused modules compiled with exit 0, no warnings after corrections.
`VineTools` and the expanded `validation/Axioms.lean` exited 0; all 194 printed
results use only subsets of `[propext, Classical.choice, Quot.sound]`.
Remaining: SG whole-chain localization/transport, hyper-chain and DV cases,
simultaneous ordinary/mixed removal, realization-independent coherence.
Continuing directly; this is a partial checkpoint, not READY.

## Full inner-object classifications in an outer VC

`VineChainFlows`, `VineChainJointNorm`, `VineVCLocalization` prove conserved
flow transport through actual ingredient certificates. An inner VC meeting an
outer chain junction has the same gap norm as the outer VC; consequently
`SG_VC_in_VC_ingredient` localizes every SG inner VC in an LG/ZG outer VC.
`VineBlockGapExists` constructs the actual outgoing/incoming gap darts.
`VineSGVCInVC.SG_VC_in_VC` gives one double bond, two double bonds or Vine V.

`VineChainEraseEndpoints` proves that every surviving chain atom reaches a
surviving endpoint after any atom deletion. `VineHyperVertexConnected` uses
the designated closing bond to prove vertex connectivity of every HV/HVC.
`VineHyperInVC` then localizes any inner HV/HVC in one outer VC ingredient,
and `hyperLike_in_VC_adjoint` gives the designated-adjoint classification
(two double bonds or Vine V), with no gap premise needed for this clause.

Checks: each named focused module compiled exit 0, no warnings in its final
version, including rebuilds of flow consumers after removing an unnecessary
instance parameter. `VineTools` and `validation/Axioms.lean` exited 0. All 209
printed results use only subsets of `[propext, Classical.choice, Quot.sound]`.
No source erratum or deviation introduced. Still required: outer HV/HVC and
DV cases; full simultaneous ordinary/mixed removal; realization-independent
coherence. Continue directly, M4 is not yet READY.

## Connected interiors and both-joints hyper containment

`VineInteriorPaths`, `VineBaseInteriorConnected`,
`VineInsertionInteriorConnected`, `VineExpansionInteriorConnected`,
`VineInteriorConnected`, `VineChainInteriorConnected` prove that the nonjoint
region of every actual vine and VC is connected, including empty type-I
interiors. Explicit base paths are recorded in GenerateInteriorPaths.py;
generic rung insertion preserves them for every length.

`VineNestedDegreeClosure`, `VineLowDegreeJoints`, `VineHyperBothJoints` now
prove the outer HV/HVC both-joints reductions: an ordinary contained block
containing both outer joints has exactly those two atoms; a contained
hyper-block containing both joints equals the entire outer group. Source
incidence/degree/connectedness facts construct every closure premise.

Checks: all new focused targets compiled exit 0, no warnings. `VineTools` and
Axioms.lean exited 0; 223 printed results use only subsets of
`[propext, Classical.choice, Quot.sound]`. A duplicate of the existing
`eraseBond_induced_path` was removed from the newer HyperVertexConnected
module; that module now imports and reuses VineLikeConnected. All affected
consumers were rebuilt. A namespace-aware scan of public Vine declarations
found no duplicates. No pinned draft was changed.

Still needed: external closing-bond transport / outer hyper classification,
DV, simultaneous ordinary/mixed removal, realization-independent coherence.
M4 remains active and work continues after this checkpoint.

## Exact local-dart transport; designated-adjoint gap audit

New `VineEraseBondDegrees` and `VineEraseBondMolecule` prove exact filtered
degree deletion formulas and preservation of the full molecule axioms for a
nonloop bond deletion, including absence of saturated components.
`VineLocalDartEmbedding`, `VineLocalDartObjects`, `VineLocalDartErasure`,
`VineLocalDartChains`, `VineLocalDartHyper` identify actual internal darts,
preserving oriented degrees, bond multiplicities, blocks, pinned vines,
chains, double chains and designated hyper-adjoint objects.
`VineHyperMissingJoint.hyperLike_in_hyperLike_missing_joint_adjoint` proves
the full source structural classification for an inner HV/HVC missing either
outer HV/HVC joint. Its external closing-bond transport is constructed by the
canonical subtype injection, not assumed.

Owner ruling 2026-11-04: a hyper-block is the pair of its atom group and
its designated adjoint bond. Its gap and SG/LG class use that same designation
consistently. Different valid deletions on one atom group give distinct objects.
`VineHyperGapObjects.HyperLikeRealization` records these exact data and its
`IsGap` uses the specified erased molecule; the gap is unique for a fixed
object and ordered joint. The original existential shape predicates and all
pinned definitions are unchanged.

**Flagged for source audit:** `VineHyperGapAmbiguity` is a kernel-checked
triple-bond example. At L=16, gamma=1/2, any 0<=eta<=1/4, labels1,32,0 on two
forward/one backward bond give one designated type-I adjoint gap2 (LG) and
another gap1/16 (SG). Both satisfy the actual molecule and decoration premises;
there are no degree-four defects. No designated adjoint of this two-atom group
is two double bonds or Vine V. Thus atom-set inclusion alone cannot be the
containment relation for the full designated-object subsetvc theorem. The owner
has been asked whether containment also requires matched designations whenever
inner and outer atom groups are equal (same bond up to mates); that clarification
is pending. This is a source-reading question, not a change to B2 templates.
The example and owner reading are retained for independent statement audit.

Checks: all listed focused modules exit0 with no final warnings. VineTools and
Axioms.lean exit0; 261 printed declarations use only subsets of
`[propext, Classical.choice, Quot.sound]`, including the audit example. No new
Lean is committed to the repo (Wave B pre-freeze). Continuing independent
transport/decoration work while the containment reading is pending.

## All vine-like outer structural cases; compatible-containment ruling

Owner ruling 2026-11-04 (flagged for audit): hyper-blocks are designated
objects. For equal atom groups, containment requires the same deleted bond
up to mates; different designations on the same group are distinct, non-nested
objects. For different atom groups containment remains atom-set inclusion.
`HyperLikeRealization.IsContained` implements exactly that reading. The
kernel-checked triple-bond example explains why plain atom-set inclusion is
insufficient; it is audit evidence, not a claimed template defect. This ruling
supersedes the pending question in the preceding checkpoint.

`VineLocalDartGaps` preserves exact gap darts; mate deletion is identified by
`eraseBond_mate_local_embedding`. `VineEraseBondDecoration` constructs the
restricted source decoration with adjusted endpoint defects and proves all
full-degree defects remain zero. `VineHyperGapProperness` rules out equal
SG/LG-ZG hyper groups under compatible containment and proves the full inner
hyper-object clause for outer HV/HVC. `VineSGVCInHyperLike` proves the ordinary
inner-VC clause, using the checked both-joints or external-deletion reductions.

`VineLikeGapObjects` retains the source VC/hyper distinction and designation.
`VineSubsetVCVineLike.subsetvc_vineLike_classification` now proves **all**
structural classifications for an LG/ZG outer VC/HV/HVC and an SG contained
VC/HV/HVC, with arbitrary rung counts and no conclusion-shaped assumptions.
The separate DV and simultaneous-removal clauses are not yet claimed.

Checks: all focused targets exit0 with no final warnings; VineTools and the
expanded Axioms.lean exit0. All 274 printed declarations use only subsets of
`[propext, Classical.choice, Quot.sound]`. No pinned definition changed.
Remaining M4: DV structural case, simultaneous ordinary/mixed removal,
realization-independent coherence. Continuing directly.

## Complete subsetvc structural classification, including DV

`VineJointPairDegrees` transports exact two-joint degrees from the pinned
expanded graph, including the shared type-V joint bond. `VineDVDegrees`
proves DV joints have degree three and interiors degree four. The degree
inclusion-exclusion and nested-block recognition helpers are listed in the
new scratch module docstrings for deduplication.

`VineVCInTypeV`, `VineTwoJointSeparator`, `VineDVMissingJoint`,
`VineFullInteriorSelection`, `VineDVOrdinary` prove the full ordinary DV clause,
without a gap assumption. `VineSameJointProfile` and `VineDVHyper` prove the
hyper clause: a contained hyper-block selecting both DV joints would be the
whole DV; but a whole DV cannot be HV/HVC, since the earlier both-joints lemma
would force its type-V branch to have two atoms. Missing-joint cases localize
to one actual type-V branch and use the checked single-vine classification.

`VineSubsetVCClassification.subsetvc_classification` now proves TARGET
subsetvc's **full structural clause**, for all allowed outer objects and all
inner VC/HV/HVC forms, with source decoration, gap and compatible-containment
premises. There are no finite masks, cap witnesses, bounded-rung assumptions
or outcome hypotheses in that theorem. Simultaneous removal remains separate.

Checks: every new focused module exit0, no final warnings. VineTools and the
expanded Axioms.lean exit0; all299 printed declarations use only subsets of
`[propext, Classical.choice, Quot.sound]`. No pinned definition changed.
Remaining M4: simultaneous ordinary/mixed removal and realization-independent
coherence. Continue directly; not READY yet.

## F72: type-II Q-block endpoint extension (adaptation in progress)

Refreshed the copied `VineType.template` block verbatim from the updated
owner B2 draft: type II has four atoms, six bonds, group `[2,3]`, and
slot `((2,1),(3,1))`. The copied hashes are in `COPIED-SHA256.txt`;
the pre-F72 pin and 299-declaration axiom log are preserved in
`snapshots/f72-pre/`. In the new convention `m=1+k`, so type II has
`4+2k` atoms, `6+4k` bonds and `1+k` groups.

Statements changed: the type-I small-cardinality cutoff and double-chain
cutoff decrease from six to four; the branching-chain singleton cutoff
decreases from eleven to seven. The old five-or-seven branching exclusion
is false after F72 (two Q-blocks concatenate to seven atoms) and is replaced
by a five-atom branching exclusion plus a five/seven-atom exclusion requiring
actual connectivity after every one-atom deletion. The source short-side
and cap-adjoint proofs now construct that stronger graph property by finite
paths. Slot helpers use distinct endpoints on each rail; full cross-rail
distinctness is asserted only when the final ports differ. Interior
connectivity needs only the initial ports to be nonjoint. The type-II full
sequence now has `k+1` rungs and permits coincident final ports.

Validation: the serial focused scratch rebuild is running, with per-module
output in `validation/F72-Rebuild.log`. The refreshed template structure,
counts, basic paths and small-cardinality lemmas have passed; later modules
and the replacement short-graph proofs are still being checked. The old
299-declaration axiom audit is pre-F72 and is not claimed for the refreshed
pin. No new source erratum is alleged; this implements the owner's F72
correction. Remaining M4 goals also include simultaneous ordinary/mixed
removal and realization-independent coherence. Continuing; not READY.

## F72 resumed validation checkpoint

After the account move the old exec session no longer existed, so the serial
focused rebuild was restarted incrementally. Checked under the refreshed pin:
`VineCoherencePermutation`, `VineTypeIIMinimum`, the explicit five/seven-atom
side and cap path certificates, `VineFiniteLabelConnectivity`,
`VineShortGraphConnectivity`, `VineSingleRailCounts`, `VineTypeIISequence`,
all base one-atom-deletion certificates, expansion vertex connectivity,
`VineEraseChainIngredient`, `VineBranchingEnds`, base VC classification,
`VineStemStarts`, and `VineCentralII`. All compiled with exit0; generated
tactic warnings have been cleaned in source and await the final incremental
pass. Main structural consumers and the refreshed axiom audit are still
pending. No source result is claimed completed by this checkpoint.

## F72 adaptation checked and audited

The focused dependency rebuild now passes on all 432 targets. Last command:
`nice -n 5 lake env bash -c 'export LEAN_PATH="/home/scott/wt-scratch/vines/build:$LEAN_PATH"; python3 /home/scott/wt-scratch/vines/validation/RebuildF72.py'`.
Final incremental result: `1 compiled; 431 already current`, exit0, no warnings.
The integrated `subsetvc_classification`, both ordinary and hyper DV cases,
all single-vine and outer-VC/HV/HVC structural clauses, and simultaneous
adjoint removal are rechecked under the refreshed four-atom type-II pin.

The updated audit command is `nice -n 5 lake env bash -c 'export
LEAN_PATH="/home/scott/wt-scratch/vines/build:$LEAN_PATH"; lean -R
/home/scott/wt-scratch/vines/src /home/scott/wt-scratch/vines/validation/Axioms.lean
> /home/scott/wt-scratch/vines/validation/Axioms-F72.log 2>&1'`; exit0, no
errors or warnings, only subsets of `[propext, Classical.choice, Quot.sound]`.
It includes the kernel-checked triple-bond example motivating the owner's
designated-bond/compatible-containment reading (F71, still flagged for audit).

New removal ingredients checked: literal single-bond backbones of types
II–VIII (type III's entire core is connected by single bonds), exact single
rail pair degree, type-I removals keep all atoms and all single rails, and
a disjoint type-I family cannot remove two different neighbor attachments
at one center. These are helpers, not the remaining source removal theorem.
Next: simultaneous ordinary/mixed removal and realization-independent coherence.
Continuing directly; M4 is not yet READY.

## Ordinary double-bond removal: arbitrary-rung vine clause proved

`VineTypeIRemovalConnected.nontrivial_vine_typeI_removal_connected` proves
that any disjoint family of complete type-I removals preserves connectivity
of any type-II–VIII vine, at arbitrary rung counts. It assumes actual
source vine/removal data and disjointness, with no path witnesses, finite
masks, gap restrictions, or classification hypotheses. Type I is explicitly
excluded: deleting its own double bond would disconnect it; the source
LG/ZG versus SG clause rules out that situation at chain assembly.

Approach: `VineActualRailFrame`, `VineSingleRailPaths`, `VineSlotSinglePaths`,
`VineCoreSinglePaths`, `VineCoreSinglePathLift`, `VineActualSingleBackbones`
and `VineExpandedSingleBackbone` transport literal base single-edge paths
through every source slot, including zero rungs and shared type-II final
ports. Every fresh atom reaches a core starting port.
`VineDoubleRemovalRails` and `VineDoubleRemovalAttachments` retain the
backbone and at least one of each normal center's two attachments;
`VineBackboneCenter` supplies those attachments from finite source data.

Focused final theorem compile: `nice -n 5 lake env bash -c 'export
LEAN_PATH="/home/scott/wt-scratch/vines/build:$LEAN_PATH"; lean -R
/home/scott/wt-scratch/vines/src -o /home/scott/wt-scratch/vines/build/VineTypeIRemovalConnected.olean
/home/scott/wt-scratch/vines/src/VineTypeIRemovalConnected.lean'`: exit0,
no output/warnings. `validation/Axioms-TypeIRemoval.lean` compiled with
the same LEAN_PATH and gate, exit0; its ten printed declarations, including
the main result, use only `[propext, Classical.choice, Quot.sound]`
(`validation/Axioms-TypeIRemoval.log`).

Remaining M4: ordinary type-V and mixed removals, outer-chain/DV assembly,
and realization-independent coherence. No new source deviation. Continuing.
