# HANDOFF g3-lowdeg (G3-LOWDEG, R48), session 2 (final). Scratch <scratch>/g3-lowdeg

Files: `src/GL1..GL29`, `src/GM01..GM08`, `src/GV01..GV14` (ports), `src/Ex1`, `src/AxL1..AxL6`; `build.sh`, `chain.sh` (stop-at-first-failure), `rebuild.sh` (fresh
rebuild of the whole closure, `exits.log`); `port/mk3.py` (the sed/port generator); `COPIED-SHA256SUMS` (sha256 of every copied G3 source).
Namespace `WaveTurbulence.FinalCountG3`; G3 is imported UNCHANGED (no G3 module edited); finalcount-asm, finalcount-g3 and other packets untouched.
Session 1 (GL1..GL16, Ex1) is described in the older sections of PROGRESS.md; this file records the final state.

## What was done in session 2

### 1. Loops (GL17, GL18, GL20..GL28)
Design (decided, simpler than the AncRel-exception plan): the whole run is done on `M' = M.unloop` (`D0 := NonLoop M`, decoration `kappa' = kappa o val`), so every
`HRunL` theorem applies verbatim with `M0 := M'`; no `AncRel.surj` exception is needed.  What is proved:
* **Molecule level (GL17).** `Molecule.unloop`, `loopBonds`; `unloop_bonds_card`, `unloop_numComponents`, `unloop_circuitRank` (chi(M) = chi(M') + k),
  ladders and rho unchanged (`unloop_isLadder`, `unloop_maximalLadders`, `unloop_rho`); `countE_unloop_le`; **`countA_unloop_le`**:
  `M.countA L g d C1 w Adm P <= ofReal((L^(-(d-g)) * (C1^-1 * delta^(1/2)))^k) * M.unloop.countA L g d C1 w (unloopAdm M Adm) P`,
  hypotheses: `deg <= 4`, `0 < L, C1, delta`, and `hdet` (admissible labels are determined by their values off the loop darts: the eps-support, all four legs of a loop
  atom are equal, root leg fixed).  `unloopAdm M Adm kappa' := exists kappa, Adm kappa /\ kappa' = kappa o val`.
* **`countA_allLoops_le` (GL28): Example B reduces to Example A** (all darts loops: `M.unloop` is dartless, `countA_dartless_le_one`): `A(M) <= g^k`.
* **Standing hypothesis (GL18).** `SubHypLoop R M` (bounds, count, conn, 1<=R, every atom has a non-loop dart, automatic for >= 2 atoms: `nonloop_of_two_le`);
  **`SubHypLoop.unloop : SubHypLoop R M -> SubHypL (R + k) M.unloop`** (k = `M.loopBonds.card`), `h0_unloop`.
* **Transport of the producers' data M -> M.unloop (GL20..GL27).**  Group-embedding invariance `GEmb` (GL20: degIn/outIn/inIn, groupBonds, IsBlock, IsVine, Chain, IsVC,
  IsDV, IsBlockGap iff for a dart embedding onto the group darts); vines have no loops (`expand_noLoop`, `isVC_noLoop`, `Object.loopFree`, GL21/GL23); `Object.unloop`,
  `Object.lift` with `ContainsDart`/`HasGapKind` preserved (GL22/23); **`Object.noLoop_of_SG`** (GL25): an object of `M.unloop` with SG gap contains no loop atom of `M`
  (loop atom has degree <= 2 in `M.unloop`, so only a block joint; its gap is 0 by the eps-support; block gap conservation `source_block_lower_SG_gap` gives the other
  joint; hyper-objects: a joint has the added bond as a third dart); `CollData.unloop`, **`SubproOblG.unloop`**, `TripleDesig.unloop`, `DegenSGT.unloop` (GL26);
  the pool `C2` and **`UnselOK.unloop`** with `unloopSet` (GL27); `LoopCtx` bundles the named inputs (`hS`, `hb : deg<=4`, `hkappa` mate-invariance, `heq`, `h0`).
* **`runDataL_of_loop` (GL28)**: for each admissible kappa: producers' data on M (`C`, `Unsel`, `SubproOblG`, `TripleDesig`, `HingeNoLoop`, `UnselOK`) and a run
  `HRunLC` on `M.unloop` with `C.unloop`, `unloopSet M Unsel` give `RunDataL L g eta M.unloop hf (unloopAdm M Adm)`.  `loopStart` packages
  `SubHypL (R+k)`, `LoopCtx`, `DegenSGT M.unloop`, `h0'`.
* Net exponent (for the assembly): R -> R+k costs L^{kX}, X = d-g-1/4-1/40; the loop gains L^{-(d-g)} per loop: net L^{-k(1/4+1/40)}.

### 2. Port of the vine-LG / FinalShape chain (GL19, GM01..GM08, GV01..GV14)
SubHyp->SubHypL, HRunN->HRunL, InvE->InvL, FinalStruct->FinalStructM, Prop95ConclAt->Prop95ConclAtL, declared names get suffix `L` (no clash with the REG originals).
GM01..08 (MapShape..MapDec5) are full copies; GV01..14 contain only the declarations that change (AncJoint, VineObj..Obj4, VineExt, LG2..LG8, LG10); unchanged
declarations are used from the originals.  Hand fixes: `low_deg` -> `ab_cls` (non-eps atoms), `eps_deg`/`BalM` -> hypothesis **`LowFree hf a0`** (the component has no
eps-atom of degree < 3), `odd_card = 2R` -> parity (`card_odd_even`) + `odd_card_le`, `even_beta` -> `perfect_beta` on a perfect component, `finalJoints_of_vineL`, `HRunLC`
(with the D3 phase) and `RunDataL`.  **`RunDataL`, `vineLG_of_runL`, `finalDec_compL`, `finalShape_compL`, `Prop95ConclL.toAtL`** (GL19).  `FinalStructM`, `Prop95ConclAtL` (GL19).

### 3. Degree-2 hinge atoms (analysis, no new Lean beyond definitions)
A hinge is an SG atom with designated pair `(first v, second v)` (R37/R48); `hingeSG` gives `TripleAtM` (two distinct bonds of opposite directions), so a hinge has
degree >= 2, and degree 2 and 3 do occur in LOW (a unit whose joint has degree < 4).  Degree 2: `Desig C (anc v) p` then says `{p.1,p.2} = {first, second}` = all darts of `v`
(complement clause is empty), so the only opposite pair of `v` is the designated one and its gap is SG, hence nonzero.  (a) If `v` is not a joint of a collected object, **`HStepD3`
(D3 phase) covers it**: eps, degree 2, opposite pair, nonzero gap, `Desig`; `NoD3` then forces that no such hinge survives, and `NoEpsHinge`/`hinge_sgat` (GL9/GL12) is consistent.
(b) If it is a joint of a collected object, **`HStepD1` covers it** (twin, SG, `Desig` at both joints; `hingeJoint` puts both darts of the designated pair inside the object).
(c) Degree 3: ordinary Step 3 (`3 <= deg`).  Hinges of degree 2 are never ZG/tame (gap SG).  No configuration breaks TARGET's argument.
`hnew` of `HStepD1` is **proved** for every step the run takes: `vineCut_F_lt` (GL29): if `deg upper = 2 or deg lower = 2` then `F(M) < F(K.post)` (surjection
`post classes -> M classes` that identifies the classes of the isolated half `fa`/`fb` with the other joint half), and `HStepD1.mk'` is `HStepD1.vine` without `hnew`.

### 4. What the assembly consumes: the LOW analogue of `reg_class_bound`
Substitution table (finalcount-asm AsmTerm15c/15d/16c, AsmPhased): `SubHyp R M0 -> SubHypL R M0`; `RunDataN -> RunDataL`; `HRunNC -> HRunLC` (run: Step1L (C|D1)*; NoTripleCut;
D3*; NoD3; Step2C*; NoEligibleTriangle; Step3C*; NoSGLeft; Step4*; NoBetaCut; plus removal of the collected objects after Step 1); `Prop95ConclAt`
from `(hrC.toHRunL.prop95L hS obl hT3 hdeg h0).toAtL ghostfree`; `finalShape_comp -> finalShape_compL (.. hE)`; `finalDec_compN -> finalDec_compL (.. hE)` with the extra
hypothesis `hE : LowFree hf a`.  So `UntC hf Tm R a` must carry `LowFree hf a`; components with an eps-atom of degree < 3 (and tame ones) go to `Damaged96`/DCB
(low-degree eps allowed, `LG` vacuous).  The final numerics use `HRunL.inv : exists R' <= R, InvL ..` and `FinalStructL` (odd_card_le <= 2R, <= R imperfect components, perfect
component has a beta atom), NOT `odd_card = 2R`.
`FinalCountLowAt P = FinalCountAtWith P (fun G => not (RegGeom G))` (AsmGate L36) is NOT proved here (needs the asm); the exact inputs it needs from this packet, for a garden G
with `M := G.molecule`, `Adm kappa` for kappa in the admissible set:
1. `SubHypLoop R M` (or `SubHypL R M` if loop-free); `M.unloop` and `SubHypL (R+k) M.unloop` (`SubHypLoop.unloop`); if M has one atom: `countA_allLoops_le`/dartless case.
2. `hdet`, `heq` (eps-support: loop atom legs equal; root leg fixed) from `splicedCountingAdmissible` -- producer/asm input, NOT proved here.
3. `HingeNoLoop C` (S2a: `SpMap.od_range`, R48 producer obligation) -- named input.
4. The data `C, Unsel, SubproOblG, TripleDesig, UnselOK, DegenSGT, h0` for M (the same as REG), transported by GL26/GL27/GL28.
5. The run on `M.unloop` (`HRunLC`), existence/completeness (`exists_step`) is asm work; every step the run takes is covered by the relations here (D1, D3, 1-4);
   `hnew` is automatic (`HStepD1.mk'`).
6. Bound: `A(M) <= g^k A(M.unloop)`, then the LOW class bound on `M.unloop` with index R+k, ending with `RunDataL`/`finalDec_compL`/`finalShape_compL` per component.

## Errata (candidate, for transcription)
* **TARGET L2160-L2161 (excessprop1 accounting, degree-2 cuts), CANDIDATE exposition gap.**  Configuration (Lean-checked, Ex1 `GC_stepD3`, Example C: garden with R=2,
  n=3, atom `aC` of degree 2 with two opposite bonds, nonzero pair gap |c| ~ L^{-1}): D3 = cut at `aC` along both bonds, isolated half deleted.  With the TRUE increments after
  deleting the isolated half (Delta F = 0, Delta V_beta = 1) the per-step excess bound `A_pre <= L^{...} excessRHS(Delta F, Delta V_beta) A_post` is FALSE: each deleted isolated
  beta-atom costs a factor L^{gamma0 + 3 eta^2} that is not compensated (the cut atom's N-factor is not paid by a new component).  What holds is the TARGET-literal accounting
  Delta F = 1, Delta V_beta = 2 (the isolated beta-atom counted, `UStepD3.excess`, `UStepD1.excess_new`, excessRHS >= 1) together with the index drop `R -> R-1`
  (`InvL.stepD3`, `UCtx.stepD3/D1`), which pays the difference since X = d-gamma-1/4-1/40 >> gamma0 + 3 eta^2.  The text must say that the isolated half is counted in
  Delta F and Delta V_beta and that R drops.
* E23 (R48) confirmed: M_sb may have atoms of degree 0, 1, 2 and self-loops; DH23 9.5 "exactly 2R odd atoms" and "eps-atoms have degree >= 3" fail; TARGET finalmol L2185 ("perfect"
  component: all eps-atoms of degree 4) is the right notion.
* Loops (research-fcgeom Q3) confirmed: `unloop` is exact (chi drops by k, ladders/rho unchanged), the gain is exactly L^{-(d-gamma)} (C1^-1 delta^{1/2}) per loop given the eps-support.
* No false statement of TARGET found; nothing STOPPED.

## Deviations
* Order of the degree-2 cuts: D3 phase BEFORE Step 2 (TARGET does them inside Operations 2/3/4); the per-step bounds and final structure are unaffected (session 1).
* Loop start by changing the base molecule to `M.unloop` (no AncRel exception): all `HRunL` statements are about `M.unloop` (D0 = NonLoop M).
* `FinalStructM`/`Prop95ConclAtL` have no `odd_card = 2R`, no `eps_deg`, no `low_deg`, no `BalM`; the shape/dec lemmas take `LowFree hf a` (component hypothesis).
* `ghost-bookkeeping`: see Errata.

## Checks run (this session)
Fresh rebuild: see `exits.log` (topological, new dir `build-fresh1`, all `exit 0`, logs in `logs/`); `#print axioms` of all main results in `AxL4`, `AxL5`, `AxL6`, `AxL1/2`:
[propext, Classical.choice, Quot.sound] only; hygiene grep (`sorry|admit|axiom|opaque|unsafe|maxHeartbeats`) over `src/*.lean`: see below; max file < 330 lines.
No pinned Lean statement of `FinalCountLowAt` is targeted by a theorem here, hence no exact-type `example` (the `#check`s of `runDataL_of_loop`, `finalDec_compL`, `loopStart`,
`countA_unloop_le` are in AxL4/AxL5).

## Uncertainties
* `hdet`/`heq` (eps-support at loop atoms) and `HingeNoLoop` are named inputs (garden-level facts of the producers); everything else about loops is proved.
* The asm must split components by `LowFree` and supply the completeness of the run (existence of steps); `HRunL.inv` gives only `R' <= R`.
* `UnselOK.unloop` uses the identification `C2(M.unloop) = unloop '' C2(M)` (proved via `obl`: the pool is `{SG, Outside, Disjoint}`).
