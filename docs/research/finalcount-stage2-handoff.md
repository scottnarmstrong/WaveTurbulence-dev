# HANDOFF: FINALCOUNT-G3 (DH23 Prop 9.5 / TARGET finalmol), INTERIM (not READY) -- see SESSION 4 block at the end

Scratch: <scratch>/finalcount-g3 (namespace WaveTurbulence.FinalCountG3), build.sh / rebuild.sh, deps = main read-only lake env + lg-spine +
snapshot of <scratch>/finalcount build (G2). Sources: DH23 = references/src-2301.07063/Revision_Submit.tex (L1773-L1817), TARGET = WKE-Longer_times_Final_arXiv.tex (L2100-L2200).

## Files (all exit 0, no sorry; last full chain in rebuild.sh)
State/model: G3State, G3Steps (Step1..4, Run), G3Inv, G3CutDeg, G3InvCut, G3InvDel, G3Vine, G3Tri, G3Run (Inv/Clean/Good along Run), G3Init (SubHyp, Run.good),
G3Final1, G3CompBeta, G3CompStep, G3CompTri, G3CompVine, G3CompRun (CompBeta), G3Final2 (FinalStruct, Run.finalStruct), G3Rel/G3RelRun (DartRel), G3EpsLG (Run.eps_LG).
NEW this session: G3Hist (HSt = state + cut history + per-atom cut record; HStep1..4; HRun; HRun.toRun), G3HInv (HInv, N1 data), G3N12 (HInv.N1, HInv.N2),
G3Dart (HGap: dart-level gaps; cut_v2_gap; HStepk.gap), G3HRun (RunInv, HRun.runInv), G3NoTriple (EpsLe, Run.noTriple), Prop95Statement (Prop95Concl, published),
Prop95Core (Prop95Core, HRun.core).

## Approach
Algorithm Steps 1-4 as relations on states (`St`: molecule + dart inclusion into M_sub + atom classes). `HSt` adds the chronological list of cut dart pairs and, per
cut atom, its record (pair, earlier cuts). iota_v != 0 is `IotaHit` (some earlier cut with 0 < |r +- r'| <= L^{-50 eta} R_v), kappa_v = 50 iff iota_v != 0.
N1: `HInv.N1` (every beta-atom carries the record of a cut with nonzero gap). N2: `HInv.N2`: kappa_{v1} = kappa_{v2} = 0 and g_b = s1 g1 + s2 g2 imply
L^{-50 eta} min(R1,R2) <= |g_b| (hyp 1 <= L, 0 <= eta): the later of the two alpha cuts sees the earlier one in its history, so kappa = 0 excludes 0 < |g_b| <= L^{-50 eta} R.
Dart level (`HGap`, `cut_v2_gap`): for a cut degree-4 atom with charge 0 (c_v = 0 at degree-4 atoms), the two remaining darts have gap = -(gap of the cut), so
|gap(x,y)| ~ R_v at the two darts of every degree-2 alpha-atom (field `label`).

## Prop95Core (theorem `HRun.core`, hypotheses: `HRun`, `SubHyp R M0`, `DegenSG M0` [Prop 9.1(c),(d)], `h0` [charge 0 at degree-4 atoms of M_sub])
Proved: struct (degrees 1..4, 2R odd atoms of degree 1/3, classification, even components have a beta-atom, <= R imperfect components, one odd component if R = 1),
label (IsLabel, kappa in {0,50}, GapSim at the two darts of degree-2 alpha-atoms), eps_LG, no_triple, N1, N2.
NOT proved yet: `cycles` (double bond / length >= 4 / triangle with <= 1 alpha), `chains` (two distinct eps ends), vine_LG (not even stated, see below).
Axioms of HRun.core / HRun.runInv / HInv.N2: propext, Classical.choice, Quot.sound (AxCheck.lean).

## Findings (location, quote, why, configuration)
F1 CANDIDATE erratum. TARGET L2187: "It is easy to check that in each Operation 1--4, the value of 4V-2E-2(V_alpha+V_beta) is preserved." With TARGET's blanket Operation 2
(L2142-L2143: "We then cut the molecule at each v_j along the bonds (l_{j+1},l_{j+2}) ... This leaves 3 atoms v_j of degree at most 2") the quantity is NOT preserved when v_3 (or v_1, v_2) is an
atom already cut earlier (a degree-2 alpha/beta atom whose two darts are both triangle darts). Configuration: a triangle v1 v2 v3 where v3 is a degree-2 beta-atom produced by an earlier Operation 3
cut. Blanket cut at v3 along its two darts leaves v3 with both darts and creates a fresh isolated atom v3' (degree 0) classified beta. Then removing the triangle: V: -3 + 3 = 0, E: -3, V_alpha+V_beta: -1 (v3 removed)
+3 (v1',v2',v3' classified) = +2, so Delta(4V-2E-2(V_a+V_b)) = 0 + 6 - 4 = +2, and v3' is an isolated beta-atom (degree 0), i.e. an extra imperfect component. DH23 L1777 "If deg v_j >= 3, then we cut" avoids it
(with no cut at a degree-2 v3 the triangle atom v3 is just removed: V -3+2, E -3, Va+Vb -1+2: Delta = -4+6-2 = 0). The model follows DH23: no cut at an already cut atom; the remainder is a "ghost" (Cls.ghost, degree 0)
that is deleted at once (`triKeep`); the invariant is then preserved (G3Final1, `Inv.triSt`).
READINGS: (R-SubHyp) SubHyp: all degrees >= 3, no self-loops (irreducibility), bonds + R = 2 atoms (TARGET subpro (1)), connected, R >= 1. (R-deg) L1806 "degrees 1 and 3": both odd atoms
may have degree 3 (FinalStruct.odd_deg: each of the 2R odd atoms has degree 1 or 3). (R-tri) the SG triples of a triangle in Step 2 are taken by the triangle's own darts (a j, b j), not "as fixed in Remark subcondition".
(R-IOTA) iota_v is sequential: "a cutting operation happens before the cutting at v" (L1782): within Step 2 the cuts are in the order v1, v2, v3 (a cut sees the earlier cuts of the same triangle),
within Step 1 the joints in order. This is what N2 needs in the triangle case (v1,v2 alpha, v3 beta, the three gaps of a triangle sum to zero). CONSEQUENCE for G2: Prop94Statement
`prop94_triangle` assumes `kappa_1 = 50 -> IotaReading M ... (T.a 1) (T.b 1)` for a pre-state atom v'; if kappa_{v_2} = 50 only because of the cut at v_1 of the same triangle (gap r_2 in a ball of radius
L^{-50 eta} R_2 around +-r_1, r_1 free) G2's hypothesis is not available; the count would be R_1 L x (L^{1-50 eta} R_2)^d (relative ball, as in the DH23 proof "in the case iota_v != 0 ... fixed ball" read relative to the
already chosen r_1). Needs a G2 extension or orchestrator ruling. (R-twin) Step 1: the two joints have the same gap up to sign (htwin; "the gap r of VC", TARGET defdiff IsBlockGap).
(R-remtame) Step 2's v_3 and Step 4's atom are not ZG (nonzero cut gap): DH23 L1985 / TARGET Remark remtame; this gives N1 for those beta-atoms.
NOT COVERED: TARGET finalmol with ZG tame-atom removal (remtame): when the atom v_3 (Op 2) or the atom v (Op 4) is ZG, TARGET removes it (no alpha/beta atoms created) instead of cutting; case (ii)
d(v)=4 and no component with exactly one neighbour: Delta chi <= -2 (gain L^{-(d-2gamma-eta)}), case (i) cut proceeds with a zero gap. The model has no removal step. GRAPH notes +2 to 4V-2E-2(Va+Vb) per ZG
removal (the removed atom has contribution 4-d(v) = 0 and each removed bond ... ); to cover it one needs: a Step "remtame" (delete a ZG atom, its darts, keep the rest), the invariant statement with the
number of ZG removals t (4V-2E-2(Va+Vb) = 2R + 2t... sign per GRAPH), hence "at most R imperfect components" becomes "at most R + t" or the removed atoms counted separately, and N1/NoBetaCut restated for nonzero gaps
only (Step 4 here requires a nonzero gap; NoBetaCut still demands that NO cut exists, which is stronger than the source: ZG-cuttable atoms are excluded from runs).
(R-vine) vine_LG (Prop 9.5 last sentence) is NOT modelled: its proof (L1814) uses subpro (f) (an SG vine not collected in Step 1 contains a hinge atom, cut along bonds that break it) and a vine/block-gap
model for components of the final molecule; both are inputs outside the run model. (Component count) excessprop1 (3) "at most 2R-1 component-creating Operations 1" is the TARGET proof's use of Prop cnblock
(components <= 2R after the CN/root-CL vines, which are done first); not derivable from the run model without that stage-1 input.

## Not done
cycles, chains (see Next in PROGRESS.md), triangle <= 1 alpha, vine_LG, excessprop1 (1)-(3) packaging, final fresh rebuild after the last module, exact-type check of Prop95Concl.


# SESSION 4 STATUS (steps 1-3 done; 4-6 open; step 7 partly)
Built exit 0: see PROGRESS.md SESSION 4; fresh rebuild in build-fresh/ (rebuild.sh, BUILD=...), exits.log.
Step 1: `NoBetaCut L w κ s` (nonzero-gap cuts only), `chainEnds_of` takes `eps_LG` (LG => gap != 0). `HRun.chains` now needs `DegenSG`.
Step 2: `HRun.prop95 : Prop95Concl` (G3Prop95), new fields bal, noloop, alpha_sg, dartGap, noBetaCut. Premises: [Infinite V], SubHyp R M0, DegenSG, h0 (charge 0 at degree-4 atoms).
        DGS strengthened to vector level (dart gap = +-recorded gap), needed for the iota signs.
Step 3: G3FinalCopy (copy of G8 Cls/FinalShape/FinalDec, sha in COPIED-SHA256SUMS), `finalShape_comp` (all fields), `finalDec_comp_of_vine` (all fields except vineLG, which is the named
        conditional `VineLGAt`, a conclusion-shaped helper). alphaSG is the non-strict SG bound. Adm = {kappa o down | AdmRun kappa}.
  DEVIATION F-ODD: G8 `FinalShape.oddDeg` (deg u = 1 and deg w = 3) is not derivable: DH23 subpro(b) (L1734) has two atoms of degree 3 that need not be cut; (3,3) occurs
        (all-LG molecule). The copy weakens to `u != w, deg in {1,3}`. G8's Odd96/CycleCase96/Rough96 use `deg u = 1` (leaf): they need a repair or an extra case. Also the mapping is for R = 1.
  DEVIATION: component statements use `compMol` = restrictP to a component; NoBetaCut restriction needs a fresh-name path-lifting lemma (G3CutRestrict, proved).
Step 4 (vine_LG) OPEN, analysis:
  * DH23 L1814 proof sketch is incomplete as written: it says the SG vine "must exist in M_sub and is not changed", but its joints are cut atoms. Need an ancestor map anc (cut halves -> atom).
  * Identification: a final vine component C has exactly two non-eps atoms j1,j2 (degrees from the template, eps atoms have degree >= 3). If anc j1 = anc j2 (halves of ONE cut atom) then
    S = anc''C is closed under adjacency, so S = all of M_sub (connected); but the two odd atoms of M_sub (degree 3) would need a half in C of degree 2 or 3; C has only even degrees and only
    two non-eps atoms, both halves of a degree-4 atom: contradiction. So that configuration cannot occur (proof sketch, not formalized).
  * The case "other halves j1', j2' joined by a bond" gives a HYPER object (HV) in M_sub (shape .hyper with the added bond), not a VC.
  * The disjoint-from-hinges case needs subpro (d)/(4) (`contained`, with containment of an SG vine in an LG/ZG vine-like object or DV) and Step-1 completeness for C2; the hinge case needs `crossing`
    (subpro (f)) PLUS the model fact that Step 3 cuts a hinge along its designated pair (first v, second v), and that Step 2 triangle darts at a hinge coincide with it (R-tri reading). Not modelled.
Step 5 (excessprop1) OPEN: not started beyond reading. (1) needs glue HStep_k -> G2 prop94_* with Adm/P-inheritance side conditions and the sibling kappa=50 triangle count (G2 hball0/hball1
  hook in TriDev3/TriCount6, relative ball around +-r1), est. > 2000 lines; (2) VineCountInput word for word from vine-count; (3) cnblock bridge.
Step 6 (remtame): TEXT FINDINGS (TARGET L2152 remark remtame, L2218 remtame2, L2187):
  * per case-(ii) removal of a degree-4 ZG tame atom v (4 bonds, no self-loop): V-1, E-4, V_alpha+V_beta unchanged => 4V-2E-2(Va+Vb) increases by +4 (not +2). The "+2" in remtame2 is the
    number of imperfect components (each imperfect component contributes >= 2 to that sum), consistent with +4.
  * CANDIDATE ERRATUM: Prop finalmol L2185 "there are at most R imperfect components" and its proof L2187 ("value ... is preserved in each Operation 1-4") are false when case-(ii) removals occur:
    the value becomes 2R + 4t, imperfect components <= R + 2t (remtame2 itself says "increases the number of imperfect components by 2"). Configuration: v ZG tame, degree 4, four distinct
    epsilon neighbours of degree 4, M - v having components each with >= 2 neighbours: after removal the four neighbours are epsilon atoms of degree 3. The statement of Prop lgmolect
    (Z, G) does not account for it.
  * the invariant "epsilon-atoms have degree >= 3" also fails for neighbours: a neighbour joined to v by two bonds becomes an epsilon atom of degree 2 (contradicts "degree 1,2 atoms are alpha/beta").
  * case (i) cuts at a ZG atom with zero gap and creates ZG alpha/beta atoms, contradicting L2185 "no alpha or beta atom is ZG" and N1 unless that sentence is read as the assumption of remtame.
  * MODEL SCOPE: DegenSG (G3EpsLG) = DH23 Prop 9.1 (c),(d): every zero-gap atom of M_sub is SG. TARGET subpro (3) instead allows non-hinge ZG tame atoms; those are NOT in the model, so remtame never
    fires and the model is DH23's setting. Extending needs: DegenSG weakened to (SG or tame), a Step "eraseAtom" (new Molecule construction), Inv with eps degree >= 1 for neighbours, imperfect <= R + 2t.

# SESSION 5 (continuation; wt-orch ticket 'FINALCOUNT G3 steps 1-4'): vine_LG groundwork
Files (all exit 0, no sorry): G3Anc (AncRel: atom of down x = anc (atom x); anc maps into M0; anc b = b and uniqueness at eps atoms; down injective;
all M0-darts at an eps atom are in range down; HStep1..4.anc, HRun.ancRel), G3AncJoint (AncRel.dartsAt_eps/deg_eps, sum_deg_ne_four,
`anc_ne_joints`: E10 part 1, the two joints of a final component whose other atoms are eps of degree 4 have distinct ancestors; proof: four darts exhaust M0.dartsAt a,
ancestor set closed under bonds, M0 connected => all degrees 4, contradicting bonds+R=2n, R>=1), G3GroupIso (GroupIso: dart embedding of a whole molecule onto the group S' of M';
isBlock/isVine/groupBonds transfer). HSt got the field `anc` (G3Hist, G3Dart, G3HInv patched; full 47-module rebuild exit 0 after the patch; G3Anc* not yet in a fresh-dir rebuild).
## Plan for vine_LG (decided this session; NOT yet done)
 1. `comp_groupIso`: GroupIso (compMol hf.s.M a0) .. M0 (atoms.image anc) anc (down o val) from: injOn anc on the component (eps atoms: anc = id; joints: anc_ne_joints; joint vs eps: uniq),
    and the `range` hypothesis (extras).  Extras = M0-darts in group S' outside range(down): each extra bond joins a1 and a2 (noloop + surj at eps); m extra bonds, m in {0,1,2};
    m=2 => deg a_i = 4 and S' closed => contradiction by the closure argument of anc_ne_joints (factor it as `closed_deg4`); m=0 => VC (Chain.single of isVine); m=1 => HV (HyperLikeRealization with
    `added` = the extra dart, GroupIso into `eraseBond M0 added`).
 2. Obligations (generic copy of lg-spine SubproSupport over a Molecule M0, TARGET L2042-L2047): selectedSG-free, contained, crossing, hingeSG, hingeJoint, plus
    Step-1 completeness for C1 and C2 (TARGET L2101: C2 = maximal SG objects in DV/LG/ZG, for a DV with both vines SG only one is selected) and the designated pair of every hinge in HStep3.
    NOTE the DV case: the non-selected vine B of a DV: joints of B have M0-degree 4 (non-shared joint bond) => DV closed, contradiction by closed_deg4; shared joint bond => hyper-like leftovers.
 3. `vineLG_of_obligations` (final): P SG => not Outside C1 (Step-1 completeness removes interior eps atoms of C1/C2 members) / Outside & disjoint hinges (contained) / meets hinges (crossing + designated pair cut).
 N1 gives nonzero gap at beta joints, GapSim at alpha joints; remaining: SG excluded => gapKind = LG.

# SESSION 6 (continuation; wt-orch ticket 'FINALCOUNT G3 G3VineLG'): vine_LG PROVED (step 1 of the ruling)
Files (exit 0, no sorry): G3Range (St.Sub: range of down shrinks), G3DPInv/2/3, G3DPRun (DPInv: an atom with cut record p has dart set {p.1,p.2} or disjoint; HRun.dp), G3VineObj4 (final_vine_object': + ContainsDart facts),
G3VineLG1 (CollData, SubproOblG = literal copy of lg-spine SubproSupport.{contained,hingeSG,hingeJoint,crossing} for a generic Molecule [TARGET subpro (4),(5),(6), L2042-L2047, L2101]; InP; C2Of = L2101 as a definition; UnselOK; cover; isVine_symm),
G3VineLG2 (final_dart_contained, group_darts_joint), G3VineLG3 (residual_unsel), G3VineLG4 (hinge_interior, hinge_joint_xor, DesRec), G3VineLG5 (no_SG), G3VineLG6 (isVine_I), G3VineLG7 (HRunC), G3VineLG8 (joint_LG), G3VineLG9 (vineLG_of_run, finalDec_comp).
Approach per ruling: named obligations only the four TARGET subpro statements; Step1Removes = HRunC conjunct "after the Step-1 phase no dart of any C1/C2 member is in the state" plus proved range shrinking;
C2 is a definition (maximal pool elements minus unselected DV vines); DesignatedPairs = DPInv (proved) + DesRec (model: records at hinge-ancestor atoms are the designated pair).
Source readings: TARGET L2101 "select only one of them, plus all the maximal SG vine-like proper subsets of the other" -- we apply the DV rule among maximal objects (partner of an unselected vine is a VC member of C2);
 CANDIDATE exposition gap: if the chosen vine of a DV is contained in a larger SG object U (e.g. an HV with added bond = the shared joint bond), the text does not say what is selected; with the other reading the unselected vine can survive as an SG vine component.
 The non-shared-bond DV case is impossible by degree count (closed_deg4): a DV with no shared bond has all degrees 4 and would be a whole component of the connected M_sub.
Deviation: IsVine is symmetric in the joints (the set {f j1,f j2}={0,1}); used for the second joint.

# SESSION 7 (continuation; wt-orch ticket 'FINALCOUNT G3 remtame + excessprop1'): remtame / corrected finalmol DONE; excessprop1 NOT started

## Model definitions recorded (accepted by the orchestrator; keep them documented as definitions of TARGET's algorithm)
* `HRunC` (G3VineLG7) = `HRun` + `Step1Removes` + `DesRec`:
  - `Step1Removes`: after the Step-1 phase no dart of any member of C1/C2 remains in the state. Source: TARGET L2101 ("remove ... the VC of each selected object", Operation 1: the collected
    SG vine-like objects are removed from the molecule).
  - `DesRec`: the records at hinge-ancestor atoms are the designated pair (first v, second v). Source: Step 3 cuts a hinge along its designated pair (TARGET L2042-L2047 `subpro` (4)-(6), Operation 3 L2143-L2145).
* DV-rule reading `UnselOK` (G3VineLG1) at TARGET L2101: "for any DV, if both vines (V) forming this DV are SG, then we select only one of them, plus all the maximal SG vine-like proper subsets
  of the other". Candidate EXPOSITION GAP: if the selected vine of a DV lies inside a larger SG object U (e.g. an HV whose added bond is the shared joint bond) the text does not say what is selected;
  with the other reading the unselected vine can survive as an SG vine component. Our reading applies the DV rule among the MAXIMAL objects (partner of an unselected vine is a VC member of C2).

## Step 1 (fresh rebuild)
`BUILD=.../build-fresh3 ./rebuild.sh`: 70 modules, all exit 0 (before the session-7 refactor). After it: `BUILD=.../build-fresh4 ./rebuild.sh` (see PROGRESS.md for the result).

## Step 2: remtame (E9), corrected `finalmol` -- files (all exit 0, no sorry)
In-place changes to accepted modules (needed so that the invariants survive an erasure; backup of the old tree: <scratch>/finalcount-g3-backup-s7):
* `Inv` (G3InvCut): `eps : ε-atoms have 1 ≤ deg` (was `3 ≤ deg`), field `odd` removed (parity count is recovered from `Flat` below).
* `Step1..4`, `HStep1..4` got trailing hypotheses `h3a h3b` (Step 1: `3 ≤ deg` of both joints), `h3` (Step 2: `3 ≤ deg (t j)` for every ε triangle atom; Steps 3/4: `3 ≤ deg v`). Source: DH23 L1777
  "If deg v_j ≥ 3 then we cut", L1779, L1781 "degree 3 or 4". (Previously derived from `Inv.eps`; an ε-atom of degree 1 or 2 only exists after an erasure.)
* `CompBeta` (G3CompBeta): witness "odd degree" generalised to `contrib ≠ 0` (a perfect component contains a β-atom, TARGET finalmol L2185). Old consequences recovered via `Flat`.
* New G3Flat: `Flat s` (`contrib ≤ 1` everywhere), preserved by Steps 1-4 (`Step1..4.flat`); `Flat.odd_card` (exactly 2R odd atoms), `Flat.eps3`, `Flat.contrib_eq`. `FinalStruct.of_good` takes `Flat`; `Run.flat`.
* `cycles_of`, `chainEnds_of`, `cycle3_tri` generalised: weak degree hypotheses (`ab_deg`, `1 ≤ deg`), class-aware balance `BalS`, and for chains an abstract hypothesis "every ε-atom of the component
  admits only α-cuts" (old callers discharge it from NoBetaCut + LG, the new one from `NoBetaCutAll`).
New modules:
* G3Erase: `eraseAt M v` (darts of bonds not touching v), `mult`, `eraseAt_dartsAt_card` (deg' + mult = deg), `card_edart`, `sum_mult`, `sc_avoid`, `comp_to_v`.
* G3EraseSt: `St.eraseSt`, `ErasableAt` = TARGET Remark remtame case (ii) (L2152: d(v)=4 and no component of M - v contains exactly one atom adjacent to v),
  `Step5`, `Good.eraseSt : Good R s -> Good (R+2) (eraseSt s v)` (4V-2E-2(Va+Vb) rises by 4), `CompBeta.eraseSt`.
* G3HErase: `HStep5` (adds: v is ZG, every triple at v has zero gap), `HInv.eraseH`, `HGap.eraseH`, `DartRel.eraseSt`, `EpsLe.eraseSt`, `NoSGTriangle.eraseSt`.
* G3BalS: `BalS` (balance of degree-2 atoms only for α/β atoms; after an erasure a degree-2 ε neighbour can have two incoming darts).
* G3RunE: `InvE M0 R t ..` (Good (R+2t), HInv, HGap, Flat when t = 0, CompBeta, BalS, DartRel) and `InvE.step1..step5`.
* G3FinalE: `NoBetaCutAll`, `StepE2/StepE4`, `HRunE L γ η w κ h0 hf t` (Steps 2 and 4 interleaved with HStep5, t = number of erasures), `HRunE.inv`.
* G3FinalE2: `FinalStructE R t s`, `FinalStructE.of_inv`. G3FinalE3: `DegenSGT`, `HRunE.noTriple/noSGTri/eps_back`.
* G3FinalE4: **`Prop95ConclE L γ η w κ Tm R t hf`** and **`HRunE.prop95E`** (hyps: Infinite V, HRunE, SubHyp R M0, DegenSGT M0 .. Tm, charge 0 at degree-4 atoms of M_sub).
Corrected finalmol (what holds with t erasures): at most R+2t imperfect components; odd atoms <= 2(R+2t), exactly 2R and ε-degree >= 3 iff t = 0; ε-atoms LG or tame; no triple bond;
perfect component has a β-atom; cycles and chains for components whose ε-atoms all have degree >= 3; BalS; labels, N1, N2, alpha_sg, dartGap as before; Step 4 complete in the strong sense `NoBetaCutAll`.

## Readings / deviations of session 7
* (R-remtame) Remark remtame (L2152) is modelled as: case (ii) = `HStep5` erase (`ErasableAt`), in Operation 2 (atom v_3) and Operation 4. The Step-4 stopping condition is `NoBetaCutAll` = no ε-atom of degree >= 3 admits a
  β-cut of ANY gap (a zero-gap β-cut is case (i)).
* **NOT COVERED: remtame case (i)** (cut at a ZG tame atom with zero gap, "ZG α/β atoms"). A run that needs a case-(i) cut cannot satisfy `NoBetaCutAll`, so it is outside `HRunE`; runs with only case-(ii) are covered.
  To cover (i): add `HStep4Z`/`HStep2Z` (cut with `pgap = 0`, v ZG), weaken `AtomOK` for β to drop `pgap ≠ 0`, restate N1 (`g ≠ 0 ∨ ZG`) and N2 with the premise `gb ≠ 0`. Estimated 150-250 lines.
* Candidate exposition gap (new): after an erasure (case (ii)) the neighbours of v can be SG ε-atoms of degree <= 2 that Operation 3 (degree >= 3) never cuts; TARGET finalmol "every ε-atom is LG or ZG" is then
  only provable under NoSGLeft for all ε-atoms (the model's stopping condition), i.e. such runs are excluded, the text is silent.
* E9 as recorded is confirmed formally: `Good.eraseSt` shows R -> R+2 per erasure (value 2R+4t), hence `imperfect <= R+2t`. TARGET remtame2 (L2218) "increases the number of imperfect components by 2" is consistent.
* DH23 setting: `t = 0` and `DegenSGT` with `Tm = False` is `DegenSG`; the old `HRun.prop95` is unchanged (recompiled against the weakened Inv).

## Step 3 (excessprop1): NOT started (reading only). Findings for the next agent
* (1) The per-operation lemmas of G2 (`prop94_alpha/beta/triangle`, VINE-COUNT `prop94_vine_all`) take `Adm : (D -> Fin d -> Z) -> Prop`, `P : Finset V -> R`, hgap : forall kappa' in Adm, ||gap|| <= 2R and hlow,
  hι : kappa = 50 -> IotaReading M L w Adm x1 x2 (L^(-50 eta) R), hAdm' (Adm on the post-molecule) and ladder-scale heredity hP. The model keeps ONE decoration kappa. The glue needs:
  (a) Adm on a state: `AdmS Adm0 s := fun k' => exists k0, Adm0 k0 /\ k' = k0 ∘ s.down` (hAdm' then holds for cutSt, delSt, eraseSt by construction);
  (b) 'the run is valid for every admissible decoration' (Adm0 ⊆ {k0 | GapSim ... for all steps}); (c) IotaHit(kappa) => IotaReading(Adm): the earlier cut's gap is ± the charge of an atom still present (the kept half
      of the earlier cut; its charge is -gap(x1',x2') by definition, and for the other half by `cut_v2_gap`), independent of kappa' in Adm; (d) P inheritance (hPinh/hP1..hP3) from the ladder scale of M_sub;
  (e) n_sub <= (log L)^c (hn) for atoms; (f) the vine classification `SingleVineVC K ∨ Nonempty (DoubleShape K)` at each Step-1 application from the universe's `subsetvc_classification` + subpro (a),(e).
* (3) universe `cnblock_component_excess_bound` (<scratch>/universe/src/CNBlockExcess.lean) is stated for `removeBlockFamily G F` of a Garden over the Mole universe: a bridge to `HStep1` (new component <=> β) is needed.
* The remtame (ii) erasure also needs its own estimate (TARGET remtame2 L2218: extra gain L^{-(d-2γ-2η)-(2γ_0+5η²)}); not in G2.

## Session 7 checks run (exact)
* Fresh rebuild, topological order, new dir `build-fresh4` (`BUILD=.../build-fresh4 ./rebuild.sh`): `exits.log` 80 lines, all `exit 0` (includes the recompiled old chain, G3VineLG9, and the new G3Erase .. G3FinalE4).
* `#print axioms` (AxCheck7.lean against build-fresh4): HRunE.prop95E, FinalStructE.of_inv, Good.eraseSt, CompBeta.eraseSt, HRunE.inv, HRunE.noSGTri, HRunE.noTriple, HRun.prop95, finalDec_comp, vineLG_of_run,
  Flat.odd_card: all `[propext, Classical.choice, Quot.sound]`.
* Hygiene `grep sorry|admit|axiom|opaque|unsafe|maxHeartbeats` over G3*.lean Prop95*.lean: only the prose word "admits" in docstrings; no code hits.
* Exact-type check (ExactType7.lean, transient, kept in scratch): `example : Prop95Concl .. hf := hr.prop95 hS hdeg h0` and `example : Prop95ConclE .. hf := hr.prop95E hS hdeg h0` elaborate (exit 0).
  No pinned Lean statement of TARGET finalmol / excessprop1 exists; `Prop95ConclE` is the corrected statement (E9). Not checked: excessprop1 (not started).
* Consumer note (lg-spine `FinalCountAt`, MolecularSpineAt.lean L29-L42): it is the final COUNT bound `countA <= L^{-4 eta^6 (rho + numCriticalSG)} L^{(R-1)(d-gamma-1/4-1/40)}` for a Garden with
  `CountingChoices`, `SplicedKernelData` and an `Adm` implying `splicedCountingAdmissible`; it consumes finalmol only through G8's rigidity (`FinalShape` of B2 Statements: noTriple, abDeg, perfectBeta, cycle, chains,
  all for PERFECT components; DecorationHyp.epsLGTame is already 'LG or tame'). `Prop95ConclE` supplies: struct (imperfect <= R+2t), no_triple, perfect_beta, cycles, chains (components without damaged ε), eps_LG-or-Tm, label,
  N1, N2. The B2 `DecorationHyp.abNonzero` (α/β atoms with two bonds have nonzero gap) is NOT contradicted by HRunE (case (i) not modelled) but would be by case (i) cuts.

# SESSION 9 (continuation; wt-orch ticket FINALCOUNT G3 steps 1-6)

Build: `./b.sh <Module>` (build-fresh4, incremental), fresh closure rebuild `rebuild5.sh` -> `build-fresh5/`, `exits5.log`.
deps: `deps/s1-src` got the missing .server/.private oleans (deps/s1-src-extra-SHA256SUMS); `deps/fc-build2` got TriSib1-4 from <scratch>/g2-sibling (deps/fc-build2-sib-SHA256SUMS).
Pre-session-9 tree backup: <scratch>/finalcount-g3-backup-s9 (taken before the in-place R27 generalization).

## Readings recorded (accepted by wt-orch)
* **PinnedM0**: the charges (chargeAt M0 k0 a) are constant on Adm0; ASSEMBLY obligation: the final count fixes the external momenta (k1..k_2R), so the charges are fixed. Discharged by the FINAL ASSEMBLY.
* P heredity (`LadderHered M0 P`: P constant along inclusions of ladder atom sets of M0) and kappa = 50 via one uniform earlier cut (`IotaUnif`, still carried by a present atom).
* "Dead hit": kappa = 50 hit by a cut whose two halves were later deleted is a candidate source gap; the configuration is kept (not covered by IotaUnif).
* R28(3): `CollData.Outside`, `Host`, `C2Of` (G3VineLG1) are now ATOM-SET containment (`P.atoms ⊆ Q.atoms`); `cover` and `no_SG` re-proved; LG1..LG9 rebuilt. The designation-level form is no longer used anywhere; no configuration needed it.

## Files and results (all exit 0, no sorry)
* G3Ladder: `isLadder_lift`, `isLadderSet_lift`, `ladderGap_lift`, `LadderHered`, `exists_maximalLadder`, `hPinh_of_hered`, `ladderScaleLow_state`. G3Ctx: `LCtx` (preserved by cutSt/delSt/withCls), `LCtx.hPinh`. G3SrcGaps: `sourceGaps_state` (SourceLadderGaps M0 -> state; needs M0 molecule, k0 a decoration of M0 with c0 = 0 at degree 4).
* G3Ghost: `countA_restrict_dartless` (deleting dartless atoms: IsDeviation .. 1).
* **UStep2.excess** (G3Ex2: `tri_excess`, `sibU_reading`): via G2-SIBLING `triangle_excess_sibling`. UStep2's hι₁ is now `IotaUnif ∨ SibUnif` (first cut of the same triangle); the sibling bridge `sibU_reading : SibUnif -> T.SiblingReading` is proved (sign s = -sg). Bookkeeping is G2's (ΔF = F(T.kept) - F(pre), ΔVβ = 3 - #α); the ghost deletion of `triSt` (reading R-T1) is a dartless restriction with deviation 1, so when g triangle atoms were already cut (ghosts) the TARGET-literal RHS (ΔF, ΔVβ both smaller by g) would be smaller by L^{-(γ0+3η²)g}: NOT proved; candidate source gap (R-T1) unchanged.
* **UStep1.excess** (G3Ex1; α-case K.post.F <= K.pre.F, which equals ΔF = 0 by `vine_F_ge` in G3VineF): constants from VINE-COUNT. DEVIATION: the VINE-COUNT theorems take `IotaReading`, which cannot express the pinned constant shift of `IotaUnif.ball`; G3VineBall has verbatim copies `prop94_vine_final_ball/hyper_final_ball/vine_double_full_ball/vine_all_ball` with the hypothesis replaced by the fixed ball `IotaBall` (the proofs only use `ball_of_iota (hι _)`). Named inputs: `hcls : SingleVineVC K ∨ Nonempty (DoubleShape K)` (classification of the removed object: TARGET subsetvc + subpro (a),(e); S4 not READY, NOT derived here, and the bridge from lg-snap `subsetvc_classification` (namespace Vine) to the finalcount `SingleVineVC/DoubleShape` is not built); `hMol : M_cur.IsMolecule` (now proved for uniform runs: G3UMol `UReach.isMolecule` from CompBeta); `hSrc0` (SourceLadderGaps M0 k0), `hDec0` (k0 a decoration of M0, c0 = 0 at degree 4), `hne`, `LadderHered`.
* **excessprop1 (3)** (G3Ex3): `new_components_le`: #(Operations 1 with ΔF > 0) <= 2R-1 from F(start) = 1 and F(end) <= 2R, using `vine_F_ge`. The bridge F(end) <= 2R from `cnblock_component_excess_bound` (a Garden statement about `removeBlockFamily`) is NOT built: it is the named input `hend`. The "isolated β-atom when equal" clause is not proved.
* **excessprop1 (2)** (new-component Operation 1: I <= L^{γ0-η³}...): NOT done. It needs a new label count (k_{l1} ± k_{l2} in a fixed set, `L^{d-γ+γ0+η³}` pairs) that VINE-COUNT does not have (it assumes ΔF = 0).
* **R27 erasure.** In place (before the R29 HOLD): `Step5/HStep5 v` drop `ErasableAt` (zero gap, deg >= 3, eps); `St.eraseSt` also deletes former neighbours that become isolated ("ghost neighbours", keeps Inv.eps/ab); `Good.eraseSt : ∃ R' ≤ R + (deg v - 2), Good R' (eraseSt v)`; `InvE M0 R t` with t = Σ(deg v - 2) (`good0`, `good`); `FinalStructE R t`: imperfect <= R + t (was R + 2t); StepE2/E4 add weight. All E-chain modules rebuilt. Standalone erasure-deviation modules G3EraseDev1-6: component counts F(M) <= F(M-v) <= F(M)-1+|Cs|, flux identity, dichotomy (deg 3 pinned; deg 4 pinned or |Cs| <= 2), `countE_erase_le_pinned` (N=1) and `countE_erase_le_box` (N=(⌊2L⌋+1)^d), `circuitRank_erase` (Δχ = c - deg v), `erase0_isDeviation`, `erase_table` (case table, d >= 3). NOT done: ladder-weight ratio `hlad` (plan: copy CutLad4/5 with `IsLadderSet (eraseAt M v) S ↔ IsLadderSet M S ∧ v ∉ S`), the state-level UStep5.excess, the integration of erasure into UReach/UCtx. After the R29 HOLD none of this was extended; if R29 retires single-atom erasure, G3EraseSt/HErase/RunE/FinalE* revert to backup-s9 and G3EraseDev* (cluster erasure) may be reused.

## Session 9 checks run
* Fresh rebuild of the whole closure (103 modules in topological order) into a NEW dir `build-fresh5` (`./rebuild5.sh`, `exits5.log`): all `exit 0`.
* `#print axioms` (AxCheck9.lean against build-fresh5): UStep1.excess, UStep2.excess, tri_excess, UStep3.excess, UStep4.excess, new_components_le, countE_erase_le_pinned, countE_erase_le_box, erase0_isDeviation, erase_table, ladderScaleLow_state, sourceGaps_state, HRunE.prop95E, vineLG_of_run, prop94_vine_all_ball: all [propext, Classical.choice, Quot.sound]. (`UReach.isMolecule` omitted: G3UMol not imported by the script; module built exit 0.)
* Hygiene grep sorry/admit/axiom/opaque/unsafe/maxHeartbeats over G3*.lean: only a prose "admit" in a docstring.
* Exact-type checks against TARGET L2157 onward: NOT done. No pinned Lean statement of excessprop1 exists; (1) is delivered per step (UStep1/2/3/4.excess), (2) not done, (3) conditional.

# SESSION 11 (R29 implementation; wt-orch ticket FINALCOUNT G3 R29 steps 1-6) -- IN PROGRESS (see PROGRESS.md SESSION 11 for the exact state)

## Model definitions of this session (accepted by wt-orch)
* **Desig** (G3Elig): a pair `p` of darts of `M_sub` at an atom `a` is designated if `a` is not a hinge, or `{p} = {first a, second a}` or `{p}` = the complement of
  `{first a, second a}` among the darts of `a` in `M_sub` (`(M₀.dartsAt a) \ {f, s}`).  Cutting a degree-4 atom along a pair or its complement is the same cut.
* **DesRec as a model definition (not a SubproOblG field).** TARGET L2152 (Remark `remtame`/Operation 3): "the atom v in Operation 3 is SG with fixed (ℓ₁,ℓ₂)"; Operation 1 cuts the
  two joints along the two bonds of the vine (TARGET L2138-L2140, the vine's pairs; `hingeJoint`, `subpro` (5) second sentence); S4's `hingeSG` (R28(1): `hingePair` = lift of `hingeOrigPair`)
  makes the designated pair of a hinge SG.  Hence `HStep1C`/`HStep3C` (G3RunN) require `Desig` of the cut pair at a hinge ancestor; `Eligible` (G3Elig, R29 item 1, A1) requires it at the three
  triangle atoms.  Step 4 needs nothing: an `ε`-atom is never a hinge after `NoSGLeft` (`hinge_sgat`, from `SubproOblG.hingeSG`).  `DesRecN` is then THEOREM `HRunN.desRec` (G3RunN).
* **HRunN** (G3RunN): HStep1C* ; NoTripleBond ; HStep2C* ; NoEligibleTriangle ; HStep3C* ; NoSGLeft ; HStep4* ; NoBetaCut.  NoSGTriangle is gone from the run; `cycles` is proved from
  `NoEligibleTriangle` (G3CycN `HRunN.cycles`, via `desig_pair` = A1 hinge step: the pair `(x,y)` of two darts of a non-ε atom with recorded pair p is designated if p is (set-level transfer
  `desig_of_sub`, needs deg(anc) ≤ 4 and `f ≠ s`, `f,s` darts of the hinge, from hingeSG)).
* G3Cycle: `cycles_of_key` has the triangle hypothesis in the form it is used (no triangle with α at t0, t1 and non-ε t2); `cycles_of` is a corollary (old users unchanged).
* Prop95ConclAt (Prop95Statement): `Prop95Concl` relative to the tame atoms: `eps_LG` and `chains` only in components WITHOUT a tame ε-atom (`TameFree`, A2).  All Map/VineLG modules now take it;
  extra hypothesis `hT : TameFree hf Tm a₀` at the (few) leaf lemmas.  `hinge_joint_xor` generalized (complement case needs `deg j = 2`, `f ≠ s`).
* `finalShape_comp (hR : CompOdd hf a₀ → R = 1) (hT)`: for every component without tame atoms that is even, or odd with R = 1.  `finalDec_compN`, `vineLG_of_runN` (G3VineLG10).
* G3VineLG9 / G3VineLG7 `HRunC`/`DesRec` are LEGACY (kept on disk, dropped from the closure).

## Files and results of session 11 (all exit 0, no sorry; fresh rebuild below)
* G3Elig: `Desig`, `Eligible`, `NoEligibleTriangle`, `HStep2C`.  G3RunN: `HStep1C`, `HStep3C`, `HRunN`, `HRunN.invN`, `TriData.pull'`, `NoEligibleTriangle.cutH/step3/step4`,
  `DesRecN` (+init/step1-4), `NoEpsHinge`, `hinge_sgat`, `HRunN.desRec`.
* G3Cycle (`cycles_of_key`), G3CycN (`desig_of_sub`, `HRunN.dp`, `HRunN.noElig`, `desig_pair`, `InvE.alpha_sg`, `InvE.gap_ne`, `HRunN.cycles`).
* G3ConclN: `Prop95ConclN` (+`HRunN.noTriple`, `eps_back`, `prop95N`, `prop95At`).
* Prop95Statement: `TameFree`, `Prop95ConclAt`.  G3Map*/G3VineLG4,5,7,8 retargeted.  G3VineLG10: `HRunNC`, `RunDataN`, `vineLG_of_runN`, `finalDec_compN`.
* G3EraseSt: `Good.erase1`.  G3Op5a/b/c, G3Damaged: Operation 5 (see PROGRESS).
## Readings and deviations of session 11
* (R-op5) Operation 5 is modelled as erasing the SET T of tame ε-atoms at once (`St.eraseSetSt`); the TARGET/R29 sequential cluster-by-cluster erasure gives the same molecule up to isomorphism
  (named assembly bridge ITER-ERASE, not proved).  The index bound is `R5 ≤ R + e_T + int_T - 2|T|` (`Good.erase_set`, `tch_eq`) = `R + Σ_K (e_K + χ_K - 1 - s_K)` with `χ_K = int_K - s_K + 1`
  (additive over maximal clusters: no bond joins two clusters; the additivity is stated, not formalised).
* (R-classes) FINDING (candidate defect of the G8-DCB statement, to wt-orch): `DamagedShape.classes : deg ≤ 2 ↔ ¬IsEps` is false for the molecule after Operation 5 when an ε-atom had ≥ 2 bonds to
  erased atoms (deg ≤ 2, class ε; it is NOT turned into an α/β-atom by Operation 5).  `DamagedShapeW` has the provable form; `DamagedShapeW.toShape` converts under `∀ ε-atom, 3 ≤ deg`.
  Suggested fix on the G8 side: weaken `classes` to `¬IsEps → deg ≤ 2` (+ `IsEps → 1 ≤ deg`), if DCB's proof does not use the other direction.
* (R-untouched) `finalShape_comp`/`finalDec_compN` are stated for the state after Operations 1-4 (hf4) and components without tame atoms.  The components of the Operation-5 molecule that are perfect are
  tame-free components of hf4 (`Op5.perfect_tameFree`); the identification compMol(op5) a ≅ compMol(hf4) a for such components (isomorphism of molecules over nested dart subtypes, with the decoration
  `κ ∘ down`) is a NAMED ASSEMBLY BRIDGE (UNTOUCHED-ISO); all fields of FinalShape/FinalDec are invariant under it.
## Named inputs (owner) after session 11
* `SubproOblG C ..` (contained, hingeSG, hingeJoint, crossing): S4 (subpro) -- unchanged; only `hingeSG` is used by the new `HRunN.desRec`.  `UnselOK`: S4/DV selection.
* `DegenSGT M₀ ..`: S4 (subpro (3)).  `h0` (balance at degree-4 atoms): from the decoration.
* ITER-ERASE, UNTOUCHED-ISO: assembly (above).
* excessprop1 glue (UStep1/2/3/4.excess, `new_components_le`): unchanged from session 9 (`hcls`: S4 `subsetvc_classification`/SubproSupportA; `hend`: cnblock bridge F(end) ≤ 2R; `LadderHered`, `PinnedM0`).
## NOT DONE in session 11 (exact next steps in PROGRESS.md "CHECKPOINT (session 11)")
* step 4 `erase_cluster_deviation` (Pinned per A3) and the slack lemma; step 5 (ladder-weight ratio, hcls, cnblock bridge, excessprop1 (2) via VINE-COUNT `prop94_vine_newcomp`).
## Session 11 checks run
* `./rebuild11.sh`: fresh dir build-fresh6, 88 modules (closure11.txt), all `exit 0`.  `#print axioms` (AxCheck11.lean) of the 17 main results: all [propext, Classical.choice, Quot.sound].
* Hygiene grep over G3RunN, G3CycN, G3ConclN, G3VineLG10, G3Op5a/b/c, G3Damaged, G3Elig: no sorry/admit/axiom/opaque/unsafe/maxHeartbeats.
* Not run: exact-type examples (no pinned Lean statement of finalmol/excessprop1 exists), excessprop1 (1)-(3) re-check against the new run (UStep*.excess still stated for the old HStep1-4; unchanged).

# SESSION 12 (R29 implementation, steps 4 and part of 5; ticket FINALCOUNT G3 steps 1-6)
## Coordinator input consumed
* G8-DCB #2 READY: G8 `DamagedShape` now has `degPos`, `abLow` (our `DamagedShapeW` fields). G3Damaged.lean: `G8Copy.DamagedShape` is the new G8 form verbatim, `DamagedShapeW` an alias, `toShape` dropped.
  `Op5.damagedDec`/`Good.damagedShape` pass 1:1 to `prop96_damaged` (hashes SHA256SUMS-dcb: Damaged96Statement 910e175f, Damaged96 747453c7). The final call `prop96_damaged` itself is NOT yet instantiated here (cross-namespace G8 types: field-wise conversion).
## Files (all exit 0, no sorry; fresh rebuild below)
* Step 4 (cluster erasure; set version of G3EraseDev1-6, single-atom files kept): G3ClDev1 (`nbrS`,`cmpS`,`CsS`,`comp_to_K`,`numComponents_eraseSet_le`: F(M-K)+1 <= F(M)+|CsS| for K nonempty inside one component),
  G3ClDev2 (`crossDS`,`sgnCS`,`PinnedS` [A3, three clauses],`cEs`,`two_csS_le`,`sum_deg_K`,`circuitRank_eraseSet`: chi(M)=chi(M-K)+e+ib-m+1-c,
  `unpinned_rank`: not pinned => m+1 <= e+ib-m+1-c, `rank_drop_nonneg`), G3ClDev3 (`countE_eraseSet_le_of_vals`, `countE_eraseSet_le_box`, N=(2L+1)^d),
  G3ClDev4 (`flux_identityS`,`unbalanced_label`,`countE_eraseSet_le_pinned`, N=1), G3ClDev5 (`eraseSet_isDeviation`), G3ClDev6 (`polylog_pow_le`,`cluster_exponents`,`cluster_table`: slack lemma d>=3),
  G3ClConn (`card_le_ib_add_one`: connected K has |K| <= ib+1, via `LGSpine.circuitRank_nonneg`), G3ClDev7 (**`erase_cluster_deviation`**).
* **`erase_cluster_deviation`** (G3ClDev7): for a connected tame cluster K of a molecule with deg <= 4, L >= L0, d >= 3, eta <= gam0/1000, C0 eta^4 <= 1:
  `IsDeviation (M.countA ..) ((eraseSet M K).countA ..) (ofReal (clusterRHS L γ η C₀ |K| e_K j))`, `clusterRHS = L^{-η³ + a(m-j) - η e - C₀η⁵(m+e)}`, a = 2γ0+5η², j = e + ib - m + 1 - c (= chi(M)-chi(M-K));
  pinned (N=1, j >= 0) or unpinned (box N=(⌊2L⌋+1)^d, j >= m+1) is decided inside the proof by `PinnedS M K`.
* Step 2: **ITER-ERASE** = `iterIso M K₁ K₂ : DartIso (eraseSet (eraseSet M K₁) K₂) (eraseSet M (K₁ ∪ K₂))` (G3Iso; `DartIso` = dart bijection fixing atoms; invariants deg/adj/components/circuitRank/bondsBetween/Directed/ladders;
  `isDecoration_iff`, `countE_eq`, `DartIso.countA_eq` with `hA : Adm' κ' ↔ Adm (κ' ∘ e)`).
  **UNTOUCHED-ISO** = `untouchedIso hT ha5 : DartIso (compMol h.s.M a) (compMol (h.op5 Tm).s.M a)` for `TameFree h Tm a`, `a ∈ op5 atoms` (G3Untouched; `untouchedIso_down` is `rfl`).
  **Cluster additivity** = `cluster_index` (G3ClAdd): `2R'+4|T| <= 2R+tch T` with T = ⋃𝒦 (`Clusters M 𝒦`) gives `R' <= R + Σ_K (e_K + χ_K - 1 - s_K)`, χ_K = ib_K - s_K + 1.
## Readings, findings, deviations (session 12)
* FINDING (O3 constant): the ladder ratio of an erasure of a cluster with t ladder atoms is up to (log L)^{4t}, not a fixed (log L)^6. `erase_cluster_deviation` therefore takes
  `hlad : ∏_{M.max} X^z ≤ (log L)^{c₀ (|K| + e_K)} ∏_{(M-K).max} X^z` (c₀ any constant), and the slack lemma absorbs it (`polylog_pow_le`, margin (γ0/4) m). This is R29's O3 `(log L)^{C(s+e)}`.
* PinnedS clause 3 (some atom of K has deg < 4) is consumed as the named input `hfix` (subpro (3): such an atom has its label fixed); clause 1/2 are proved from the flux identities.
* Connectivity: `rank_drop_nonneg` needs |K| <= ib+1, proved from internal connectivity (`hKint`) by `card_le_ib_add_one`.  Chain over a family of clusters: each factor is `erase_cluster_deviation` applied to the
  CURRENT molecule (pinned/unpinned is re-decided there; no bond joins two clusters), the product telescopes by `iterIso`. The chain combinator (transfer of tameness/hKint/hfix to the nested molecules, Adm restriction compat) is NOT written.
## Named inputs (owner) after session 12
| input | owner |
|---|---|
| `hlad` (O3): ladder ratio of an erasure <= (log L)^{c₀(s+e)} (needs CutLad4/5 for sets: pieces of a ladder through t removed atoms) | assembly / R29 O3 |
| `hfix` (subpro (3)): label of an atom of K with deg < 4 is fixed | S4 |
| `htame` (all darts at atoms of a tame cluster carry one label), cluster connectivity `hKint` | assembly (from tame cluster definition + zero gaps, S4 subpro (3)) |
| `SubproOblG`, `UnselOK`, `DegenSGT` | S4 (unchanged) |
| chain combinator over the cluster family (nested transfer + Adm restriction) | assembly (O6) |
| `hcls` (SingleVineVC or DoubleShape), `DoubleShape K -> K.post.numComponents <= M.numComponents` (needs the S4 fact that the joints stay connected outside the VC: FALSE without it, e.g. a dumbbell M = A - a=x=b - B), `NewCompFixed`, `nu <= (log L)^{C2}` | S4 / assembly (step 5 NOT done) |
| `hend` (F(end) <= 2R): `new_components_le_of_cnblock` reduces it to `hiso : DartIso (removeBlockFamily G F) h₁.s.M` + `cnblock_component_excess_bound` | assembly |
| `LadderHered`, `PinnedM0` | assembly (unchanged) |

# SESSION 13 (steps 1-5 of the coordinator ticket)
Files (all exit 0, fresh rebuild build-fresh8, 125 modules, exits13.log; max file < 260 lines): G3ClFam1-3, G3LadErase1-3, G3Step5a/5b/5c, G3NewComp1/2, G3Ex1New, G3Prop96Dam (build with b2.sh: finalcount-g8 buildD/build8 + moleprop4-t/appb/clcn/mole builds read-only on LEAN_PATH).
* **erase_family_deviation** (G3ClFam3): FamData M 𝒦 (clusters, nl, deg<=4, nonempty, deg>=1, internal connectivity); ∃ j, χ(M)=χ(M-⋃𝒦)+Σj ∧ ∃L₀ ∀L≥L₀ ... FamTame M 𝒦 Adm → FamLad → IsDeviation (𝔄(M)) (𝔄(M-⋃𝒦) with Adm restricted by `resAdm Adm M ⋃𝒦`) (∏_K ofReal clusterRHS(|K|,e_K,j_K)). Adm iff: `resAdm_iter`; nested erasure = `iterIso` + `DartIso.countA_eq` (`iter_countA`).
* **O3 proved**: `famLad_of_hered` / `ladProd_erase_set` (copy of CutLad4/5 for one atom, iterated: loss <= (log L)^{4|E|}); remaining hypotheses: LadderHered M P (DH23 kqmainest2), P>=0, c0>=4, L>=e. No longer a named input.
* **Step 5a** DoubleShape connectivity: `vine_F_le_of_sc` (fa~fb in K.post => ΔF<=0), `VineOutsideConn K G`, `vineCut_F_le_of_outside`, `doubleShape_F_le`. Dumbbell: hypothesis fails, consistent with the ruling. Restated as: removed VC of C₂ with joints connected outside it.
  MISMATCH with the universe theorem `subsetvc_simultaneous_removal_connected` (universe/src/VineSubsetVCRemoval.lean): it yields SameComponent in universe `removeBlocks M U₂ ps` (universe-copy Molecule, WaveB2Draft/Molecules sha 5cc506 vs lg-spine copy 986e96) for the molecule M_sub with U₂ pieces. VineOutsideConn is exactly its adjacency chain read in M, but (i) the universe's types differ from the finalcount/lg-spine `Molecule` copy (port needed), (ii) G3's K lives on the CURRENT run molecule h.s.M after earlier cuts, so one needs U₂ atoms/bonds untouched by earlier operations (disjointness of C₁/C₂ objects, TARGET L2175), (iii) the theorem needs the gap hypotheses (hSG, houter: DV or LG/ZG outer object) from S4's SubproSupportA/step1_vc_shape. NOT derived here: remains hypothesis `hconn` of UStep1.excess_new (owner S4/assembly).
* **Step 5b/c**: `newCompFixed_exists` PROVES NewCompFixed (flux through bridge: boundary of the new component = {x1,x2}; ν=|A|+(m-2)<=|M.atoms|; needs hgap from SG (gapAt_ne_of_SG), no loops, deg<=4); ν<=(log L)^{C₂} via UCtx.card_atoms_le (hνat is the hypothesis `|atoms| <= ν`). `vine_F_le_succ` (ΔF<=1); `vc_block_of_new` (new component => ordinary VC shape). **UStep1.excess_new** (G3Ex1New) = excessprop1 (2) via VINE-COUNT prop94_vine_newcomp (αs=[], ΔF=1, ΔV_β=2; copies VCNew1..13 in deps/vc-build, sha in COPIED-SHA256SUMS).
* **Step 4**: G3Prop96Dam `damaged_component_bound` = G8 `prop96_damaged` via `g8Cls`, `DamagedShape.toG8`, `DamagedDec.toG8` (field-wise); named input MaxLadderGapAdm (ladder-gap clause of Adm) and |atoms| <= (1+log L)^m (from UCtx.card_atoms_le).
* Axioms (AxCheck13.out): all [propext, Classical.choice, Quot.sound]. Hygiene: clean. Exact-type: no pinned Lean statement of excessprop1/finalmol exists; `#check` of UStep1.excess (L2154 (1), excesseqn2 RHS literal) and UStep1.excess_new ((2), excessRHS2 = excesseqn2+ L2158-L2161) shown in AxCheck13.out (transient, file AxCheck13.lean not in the closure).
## Named inputs (owner), after session 13
| input | owner |
|---|---|
| `hfix` (subpro (3): label of atom of K with deg<4 fixed), `htame`/FamTame, FamData.int (cluster connectivity) | S4 / assembly |
| `LadderHered` (kqmainest2), `PinnedM0`, `SubproOblG`, `UnselOK`, `DegenSGT` | S4 / assembly |
| `hcls` (SingleVineVC ∨ DoubleShape), `hconn` (VineOutsideConn for DoubleShape; subsetvc output, see MISMATCH) | S4 / assembly |
| `hend` (F(end) <= 2R): `new_components_le_of_cnblock` + `hiso` + cnblock_component_excess_bound | assembly |
| MaxLadderGapAdm for damaged components, cluster-family construction of tameSet (`clOf`, Clusters/FamData facts) | assembly |
| `hlad` O3, `NewCompFixed`, chain combinator, DoubleShape F-bound: DISCHARGED here | -- |

# SESSION 14 (R37(b) triple, R38(2) charged ghost triangle, R38(4) DEAD-HIT) -- NOT READY: GhostTriInput still a named input
Files: build-fresh9 fresh rebuild of closure14.txt (135 modules, exits14.log all exit 0, `rebuild14.sh`); AxCheck14.out: noTripleBond_of_stop, HRunN.prop95N/prop95At, vineLG_of_runN, finalDec_compN, UStep2.excess, HInv.N2, HStep2.inv, UStep1.excess_new, damaged_component_bound all [propext, Classical.choice, Quot.sound]. Hygiene grep: only docstring words ("admit a cut"). Sources before: backup-s14/.
## Exact new/changed statements (all namespace WaveTurbulence.FinalCountG3)
* G3Hist: `HSt.alive h := h.hist.filter (carried by a present atom)`; `HSt.mem_alive`; `HSt.triVis1 h T := if cls (t 0)=eps then pr0 :: alive else alive`; `triVis2 h T := if cls (t 1)=eps then pr1 :: triVis1 else triVis1`. Record `vis` of a cut = alive list at that time (vine 2nd cut: `px :: h.alive`; tri f1: `triVis1`, f2: `triVis2`). HStep1/3/4 and HStep1C/3C: `kp = 50 <-> IotaHit L η w κ h.alive p R` (vine 2nd: `px :: h.alive`). HStep2: `h.s.cls (T.t 0) = .eps -> (kp 0 = 50 <-> IotaHit .. h.alive pr0 (Q 0))`, `cls (t 1) = eps -> (kp 1 = 50 <-> IotaHit .. (h.triVis1 T) pr1 (Q 1))` (ghosts are not cut: no iota condition for ghost positions). κ_v stored in the class `.alpha R kp` at creation.
* G3HInv: `HInv` fields now `mem : ∀ a ∈ atoms, crec a = some (p,vis) → p ∈ hist`, `cmp : ∀ a a' ∈ atoms, records (p,vis),(p',vis') → p = p' ∨ p ∈ vis' ∨ p' ∈ vis`, `ok` (suf removed). `HInv.cut_gen` generalized, `HSt.alive_cut_sub`. G3N12 `HInv.N2` RE-PROVED (same statement) from `cmp` (earlier cut alive at later one). `IotaUnif.hit` now gives `IotaHit .. h.alive ..`.
* G3UStep: UStep1/3 `hι0/hι'` use `h.alive`; UStep2: `hι₀ : cls (t 0)=eps -> kp 0=50 -> IotaUnif ..`, `hι₀' : cls (t 0)=eps -> kp 0=0 -> ∀ k0∈Adm0, ¬IotaHit k0 h.alive ..`, `hι₁ : cls (t 1)=eps -> kp 1=50 -> IotaUnif ∨ (cls (t 0)=eps ∧ SibUnif ..)`, `hι₁' : cls (t 1)=eps -> kp 1=0 -> ∀ k0, ¬IotaHit k0 (h.triVis1 T) ..`.
* G3Ex2 (R38(2)): `alphaGhostList h T`, `triAlphaNew h T Q kp`, `betaCount s`, `labelProd L γ η l = (l.map fun p => L^((γ+3η)/2 - p.2 η) * p.1).prod`; named input `GhostTriInput L γ η δ C₁ w Adm0 M₀ c : Prop` (statement = NOTES §3d, in G3 vocabulary, hypotheses UStep2's + (G-alpha) + (G-beta) + `8η ≤ 2γ-1`); 
  `theorem UStep2.excess {δ C₁} {c} (hGh : GhostTriInput ..) (hs : UStep2 L γ η w Adm0 h h') (hc : LCtx M₀ h.s) (hAR : AtomRelU Adm0 L w h) P hP0 hPh (hn : atoms.card ≤ (log L)^c) (hne : ∃ k0, Adm0 k0) (hRI : ∀ k0, Adm0 k0 → HInv .. k0 h ∧ HGap L w k0 h) (hγ : 8η ≤ 2γ-1) : ∃ T Q kp hcl, h' = h.triPost T Q kp hcl ∧ IsDeviation (countA h) (countA h') (ofReal (triConst d c η δ * excessRHS L γ η (triAlphaNew h T Q kp) (h'.numComponents - h.numComponents) (betaCount h'.s - betaCount h.s) / labelProd L γ η (alphaGhostList h T)))`; `ghost_alpha_gap`, `ghost_beta_gap`. Old `tri_excess` (ghost-free, kept-based) unchanged.
* R37(b): G3RunN `HStep1C.triple` (hypotheses of HStep3C.cut + `hhinge : h.anc v ∈ C.hinges`, `u ≠ v`, `3 ≤ bondsBetween v u`, `atom (mate x₁) = atom (mate x₂) = u`; post state IDENTICAL to HStep3C.cut, so UStep3 / `UStep3.excess` is its deviation bound); `HStep1C.cases : HStep1 ∨ HStep3C`; `NoTripleCut C L γ η w κ h` (no triple step applicable, gap-level: gapKind ≠ SG); `HRunN`/`HRunNC` Step-1 stop conjunct = `NoTripleCut C L γ η w κ h₁` (NoTripleBond assumption REMOVED); `TripleDesig C` (generic form of S4 `triple_in_designated`, `3 ≤ bondsBetween`; S4 proves `= 3`, the ≥4 case is a closed 2-atom component: assembly glue); **theorem** `noTripleBond_of_stop [Infinite V] (hS) (h0) (obl : SubproOblG C ..) (hT : TripleDesig C) (a1 : RTG (HStep1C ..) (HSt.init M₀) h₁) (n1 : NoTripleCut ..) : NoTripleBond h₁.s.M` (G3TripleThm). `HRunN.noTriple/prop95N/prop95At` take `hT3 : TripleDesig C`; `RunDataN` has the conjunct `TripleDesig C` after `SubproOblG`.
## Open (why not READY)
G2-GHOST became READY (`TriData.triangle_excess_ghost`, g2-ghost/GhostMain4.lean) after this build; `GhostTriInput` is not yet discharged from it. G3TriBridge.lean (copy of asm AsmTriBridge isA0_iff/isA1_iff, sha in COPIED-SHA256SUMS) is not compiled and not in the closure. See PROGRESS.md CHECKPOINT for the 3 bridges. Deviations: ghost-faithful sibling list (no hit from an uncut ghost); NoTripleCut is gap-level (label existence for an SG gap not proved, same convention as NoBetaCut); TripleDesig uses `3 ≤`.
Errata (candidates, per R37/R38): DH23 L1777/L1791-1795 and TARGET L2142/L2165 ghost-triangle bound; TARGET L2140 triple bonds not in C₁∪C₂; DH23 L1784/L1803, TARGET L2150 dead-hit ball centre.

# SESSION 15 (GhostTriInput discharged; TripleDesig >= 4 case) -- build dir build-fresh10, `./rebuild15.sh` (uses b3.sh = b2.sh + g2-ghost/build + g2-sibling/build read-only), closure15.txt (140 modules), exits15.log
## Files (new/changed, all in <scratch>/finalcount-g3, namespace WaveTurbulence.FinalCountG3)
* G3TriBridge.lean (compiled now; copy of finalcount-asm AsmTriBridge `isA0_iff`, `isA1_iff`; sha in COPIED-SHA256SUMS).
* G3Ex2G1.lean: `blobM_closed`, `not_all_alpha_of_compBeta` (hnot3), `ghostQ/ghostK(_eq)`, `labelProd_eq_ghostCharge`, `alphaLabels_eq_triAlphaNew`.
* G3Ex2G2.lean: `triSt_atoms_gen`, `triKeep_dartless`, `triSt_numComponents_ghost` (F(post)+g = F(kept)), `betaCount_pre/post`, `betaCount_incr` (= 3 - #newα - g - gβ).
* G3Ex2G.lean: **`UStep2.excess`** (PROVED from G2-GHOST `TriData.triangle_excess_ghost`; `GhostTriInput` deleted). G3Ex2.lean edited: the `GhostTriInput` def and the old `UStep2.excess` are removed (pre-edit copy backup-s14/G3Ex2.lean.pre-s15).
* G3TripleGe4.lean: `bondsBetween_lt_four`, `TripleDesig3` (S4's `= 3` form), `tripleDesig_of_eq3`.
## Exact final statement of `UStep2.excess`
```
theorem UStep2.excess {δ C₁ : ℝ} {c : ℕ} (H : TriReal d L γ η δ C₁) {h h' : HSt V D₀}
    (hs : UStep2 L γ η w Adm0 h h') (hc : LCtx M₀ h.s) (hCl : Clean h.s) (hCB : CompBeta h.s)
    (hAR : AtomRelU Adm0 L w h) (P : Finset V → ℝ) (hP0 : ∀ S, 0 ≤ P S) (hPh : LadderHered M₀ P)
    (hn : (h.s.M.atoms.card : ℝ) ≤ Real.log L ^ c) (hne : ∃ k0, Adm0 k0)
    (hRI : ∀ k0, Adm0 k0 → HInv L γ η w k0 h ∧ HGap L w k0 h) (hγ : 8 * η ≤ 2 * γ - 1) :
    ∃ (T : TriData h.s.M) (Q : Fin 2 → ℝ) (kp : Fin 2 → ℕ) (hcl : PClosed T.kept (triKeep h.s T)),
      h' = h.triPost T Q kp hcl ∧
      IsDeviation (h.s.M.countA L γ δ C₁ w (AdmS Adm0 h.s) P) (h'.s.M.countA L γ δ C₁ w (AdmS Adm0 h'.s) P)
        (ENNReal.ofReal (ghostConst d c η δ *
          (excessRHS L γ η (triAlphaNew h T Q kp) ((h'.s.M.numComponents : ℤ) - h.s.M.numComponents)
            (betaCount h'.s - betaCount h.s) / labelProd L γ η (alphaGhostList h T))))
```
Changes versus the session-14 named-input statement: (i) the constant is `ghostConst d c η δ` (G2-GHOST's; `ghostConst_ge_triConst`: triConst <= ghostConst, so the old `triConst` constant could not be derived); (ii) the explicit standing hypotheses `H : TriReal` (the old statement hid it inside the named input), `hCl : Clean h.s` (no ghost-class atom: needed so that a non-ε triangle atom is α or β) and `hCB : CompBeta h.s` (for `hnot3`; both hold along a run: `Good` and `UReach.compBeta`); (iii) `ΔV_β` and `ΔF` are the TRUE increments of the post state.
## Bridges (what was proved)
* hnot3: three α atoms of degree <= 2 form a closed set `image t` (`blobM_closed`), hence a component of `M` with no β atom and `contrib = 2 - 2 = 0`, contradicting `CompBeta`.
* `alphaLabels (Q 0) (Q 1) κ₀' κ₁' = triAlphaNew` with `κ_j' := if cls (t j) = ε then kp j else 0` (a ghost never creates an α atom: `not_isA0_of_ghost`, `not_isA1_of_ghost1`; `isA0_iff`, `isA1_iff`, `triCls_f0/f1`). The ghost positions of `triangle_excess_ghost` use `(R_j, κ_j) = (Q j, 0)`: `hgap0/1` come from `hsim`, `hball`/`hb1` are only needed when `κ_j' = 50`, i.e. `t j` is ε.
* ghost data: `gh j := cls (t j) ≠ ε`, `ag j := ∃ R k, cls (t j) = α R k`, `Qg = ghostQ`, `kg = ghostK`; `hgd` from `LCtx.eps`; `hQl/hQu` from `IsLabel`; `hlow` from `GapSim` of `ghost_alpha_gap`; `hnz` from `hsg` (j < 2) and `hnz` (j = 2) as in `tri_excess`.
* `numComponents post + g = numComponents kept` (`numComponents_restrictP_add` + dartless part); `betaCount post - betaCount pre = 3 - #newα - g - g_β` with `g_β = #{cls = β}` (= `#{gh ∧ ¬ag}` by `Clean`).
* ghost deletion: `countA_restrict_dartless` (factor 1), exactly as `tri_excess`.
## TripleDesig (≥ 4 case)
`bondsBetween_lt_four : SubHyp R M → a ∈ M.atoms → M.bondsBetween a b < 4` (>= 4 bonds fill all <= 8 darts of a and b, so {a,b} is a closed set, by `conn` it is all of M, and `bonds + R = 2·atoms` with `1 <= R` fails). Hence `tripleDesig_of_eq3 (hS : SubHyp R M₀) (h3 : TripleDesig3 C) : TripleDesig C`; the assembly feeds S4's `Subpro.triple_in_designated` (`= 3`) as `TripleDesig3 C`. `RunDataN` / `HRunN.*` keep the conjunct `TripleDesig C` (now derivable; no change to their statements).
## Uncertainties / deviations
* `UStep2.excess` assumes `8η ≤ 2γ-1` (R38 item 3; open for γ <= 1/2). `TripleDesig3` is stated for M₀ atoms of `CollData` exactly as S4's output but I did not re-check S4's exact types; consumers must instantiate it (type-level match is by the same field layout as `TripleDesig`).
* No new errata beyond R37/R38 candidates listed in SESSION 14.
## Checks run (session 15)
* `./rebuild15.sh` (fresh dir build-fresh10, closure15.txt in topological order, 140 modules): exits15.log, all 140 `exit 0`.
* AxCheck15.lean / AxCheck15.out (run against build-fresh10): all listed results `[propext, Classical.choice, Quot.sound]` (UStep2.excess, tripleDesig_of_eq3, bondsBetween_lt_four, not_all_alpha_of_compBeta, alphaLabels_eq_triAlphaNew, labelProd_eq_ghostCharge, triSt_numComponents_ghost, betaCount_incr, isA0_iff, isA1_iff, noTripleBond_of_stop, HRunN.prop95N, HRunN.prop95At, vineLG_of_runN, finalDec_compN, HInv.N2, HStep2.inv, UStep1.excess_new, damaged_component_bound). `#check @UStep2.excess` in AxCheck15.out equals the statement above.
* Hygiene grep (sorry|admit|axiom|opaque|unsafe|maxHeartbeats) over the 140 closure files: only two docstring words ("admit", "admits"). Max file 372 lines.
* Exact-type check: no pinned Lean statement of excessprop1/finalmol exists (as in earlier sessions); `#check` shown instead.
* NOTE for the assembly: the Lean path now needs g2-ghost/build and g2-sibling/build (read-only) besides the earlier ones (see b3.sh).

# SESSION 16 (ISSUE-G3-HCLS: hcls/hconn only for the step's own K) -- build dir build-fresh11, `./rebuild16.sh`, closure16.txt (= closure15, 140 modules), exits16.log
## Files changed: G3Ex1.lean (`UStep1.excess`), G3Ex1New.lean (`UStep1.excess_new`). Pre-edit copies: backup-s14/*.pre-s16. No other g3 module consumed them (only AxCheck files).
## Approach
The universally quantified hypotheses `hcls`/`hconn` (over every K', R', kp' with h' = h.vinePost K' R' kp') are REMOVED from the binders.  The conclusion now states the existential K (the one the `HStep1C.vine` step removes, obtained by `cases hs`) together with the implications `hcls K -> hconn K -> ...`, so they are required for that K only.  Proofs unchanged except that `hcls`/`hconn` are introduced after `refine ⟨K, R, kp, rfl, ...⟩`.
## Exact new conclusions (all binders before `∀ {h h'}` unchanged; `hcls`/`hconn` binders deleted)
UStep1.excess, after `h.s.M.IsMolecule →`:
```
∃ (K : VineCut h.s.M) (R : ℝ) (kp : ℕ), h' = h.vinePost K R kp ∧
  ((SingleVineVC K ∨ Nonempty (DoubleShape K)) →
   K.post.numComponents ≤ h.s.M.numComponents →
   IsDeviation (h.s.M.countA L γ δ C₁ w (AdmS Adm0 h.s) P) (h'.s.M.countA L γ δ C₁ w (AdmS Adm0 h'.s) P)
     (ENNReal.ofReal ((Cs * (2 ^ d * ((13 : ℝ) / (2 * η - η ^ 3)) ^ 13) * (1 + δ⁻¹)) * excessRHS L γ η [(R, kp), (R, kp)] 0 0)))
```
UStep1.excess_new, after `(h.s.M.atoms.card : ℝ) ≤ ν →` (the `∀ x, atom x ≠ atom (mate x)` binder is before it, unchanged):
```
∃ (K : VineCut h.s.M) (R : ℝ) (kp : ℕ), h' = h.vinePost K R kp ∧
  ((SingleVineVC K ∨ Nonempty (DoubleShape K)) →
   (Nonempty (DoubleShape K) → ∃ G : Finset h.s.D, (∀ z ∈ ({K.x₁, K.x₂, K.y₁, K.y₂} : Finset h.s.D), z ∈ G) ∧ VineOutsideConn K G) →
   K.post.numComponents = h.s.M.numComponents + 1 →
   IsDeviation (h.s.M.countA ...) (h'.s.M.countA ...)
     (ENNReal.ofReal ((Cs * ν * (1 + δ⁻¹) ^ 2 * (((4 + 8 : ℕ) : ℝ) / (η ^ 2 - η ^ 3)) ^ (4 + 8)) * excessRHS2 L γ η [] 1 2)))
```
(full text: `#check` in AxCheck16.out).  Consumer recipe: `obtain ⟨K, R, kp, hpost, key⟩ := ...; exact key (hcls_for_K) (hconn_for_K) hF` after rewriting by hpost.  Downstream NOT repaired here (other packet's scratch, rule: never edit): finalcount-asm/src/AsmEx1.lean (`ex1A_of_excess`, `ex1N_of_excess`) and its use in AsmPhase1b must change `Ex1A/Ex1N` shape / VFacts.hcls to per-K form (their `hcls` for all K' goes away; VFacts need hcls/hconn for the node's own K only).
## Checks
* `./rebuild16.sh`, fresh dir build-fresh11, 140 modules in topological order: all `exit 0` (exits16.log; rebuild16.out `total 140`, no failures).
* AxCheck16.out: UStep1.excess, UStep1.excess_new, UStep2.excess all [propext, Classical.choice, Quot.sound].
* Hygiene grep over 140 closure files: only docstring words "admit"/"admits" (β-cut); no sorry/axiom/opaque/unsafe/maxHeartbeats.
* No pinned Lean statement of excessprop1 exists; `#check` shown instead.
