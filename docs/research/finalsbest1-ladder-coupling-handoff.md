# S3c COARSE-SPLICED handoff

Packet: S3c COARSE-SPLICED. Target `WTPrefix CoarseSplicedAt` (`CoarseSplicedGate`), TARGET finalsbest1, L2075-L2077 of
<sources>/paper/source/WKE-Longer_times_Final_arXiv.tex (upstream redladder2 L1978-L1992, redvine3 L1976).
Pinned: <scratch>/ladder/in/SourceSplicedBounds.lean sha256 38b561144f7153faf94ef3c59bf1b3ebd80e15b8817e49cc3599a3037602d9ba;
live <scratch>/lg-spine/SourceSplicedBounds.lean has the identical hash (checked at start and at end).
Scratch: <scratch>/coarse-spliced (namespace WaveTurbulence.CoarseSpliced; three files in WaveTurbulence.LadderDecay).
Build: `./build.sh <Mod>` (env.sh); fresh closure `./build2.sh` into build2/ (logs build2-<Mod>.log).
Inputs are private snapshots taken at first read: lg-snap/ (lg-spine), sumint-snap/, ld-snap/ (ladder-decay build + merged);
COPIED-SHA256SUMS records the pinned file and the copied WaveB2-Ladders.lean.

## Main results
- `WaveTurbulence.CoarseSpliced.coarseSplicedGate : WTPrefix CoarseSplicedAtC` (Final2.lean).  `CoarseSplicedAtC` is a verbatim copy
  (Spec.lean; copies `SourceMaximalLadderDataC`, `SplicedSourcePremisesC`) of the pinned `CoarseSplicedAt`; the clash between
  lg-spine's `WaveBDraft.Sumint` and the sumint scratch's `WaveBDraft.SumintData` (both declare `SumintShape.TVar`) forbids importing
  the pinned file next to the S3b ladder scratch.  The exact-type check is PinCheck.lean in an lg-spine-only environment:
  `coarse_iff : CoarseSplicedAt P <-> CoarseSplicedAtC P` (structure by structure) and `coarseGate_of_copy : WTPrefix CoarseSplicedAtC -> CoarseSplicedGate`.
- `ladderL1Gate : WTPrefix LadderL1At` (LadderL1Gate.lean): the time-L1 form of redladder2 (see Approach).
- `selection_claim : SelectionClaim` (Selection2.lean): pure molecule combinatorics.
- `splicedKernel_le_classes` (Assembly3.lean): the analytic core (class sum x product of per-ladder time-L1 bounds).

## Approach
THE GAP IN TARGET AND ITS FIX.  TARGET says (finalsbest1) "is very easy with Proposition ladderl1new": apply redladder2 per maximal ladder, estimate the
rest trivially.  But redladder2/`LadderDecayAt` bounds, for FIXED outside times, the integral over the ORDERED domain of the lattice sum
(sup over outside times).  Two tree-adjacent ladders in the same layer are coupled by the ordering indicator 1[t_a < t_b], so the global
integrand does not factor over ladders and a black-box product of sup-bounds does not follow (abstractly it can fail: pseudo-measures
a, b with bounded Fourier transform and Heaviside coupling).  The fix is the intermediate bound inside S3b's proof (`kernel_core`): the integral over
the unit time BOX of the modulus of the finite lattice sum, |K| <= coupling^(2m+1) * int_box |sum_z w(z) phase(z,t)| dt.  This is a time-L1 statement
and survives dropping the ordering and multiplying over ladders.  LadderL1.lean / LadderL1Fixed.lean / LadderL1Gate.lean copy the tail of `kernel_core`,
the arithmetic of `ladder_fixed` and the parameter choice of `ladderDecayGate` (S3b) with that conclusion.  `LadderDecayAt` itself is not used as a black box.
(Recommend merging ladderL1Gate into LadderDecayFinal at the rebase.)

Steps (all compiled):
1. BlockInt: integral over a unit box of a product of functions of disjoint coordinate blocks (`prod_block_integral`).
2. Locality/Factor/RestInv: for pairwise disjoint hinge-free atom sets S_i, `splicedMomentumAmplitude = restAmp * prod_i ladderWeight_i`, the
   weights/phases are local to the darts at atoms of S_i, `restAmp` and the rest frequencies depend only on bond labels off the internal darts.
3. Glue/FibreFactor: gluing of decorations along disjoint atom sets (at the DecLab level via `decEquiv`), and
   `fibre_factor`: the fibre sum = restAmp*phase * prod_i Lam_i (local lattice sums).
4. Assembly1-3: K = c^n * int_dom sum_z ...; drop the ordering (`norm_sum_integral_indicator_le`); split the z-sum into classes (labels off internal
   darts); fibre bound; integrate with `prod_block_integral`; `splicedKernel_le_classes`:
   ||K|| <= ||c||^(n - sum(|S_i|-1)) * #classes * prod b_i.
5. Count: #classes <= (2L+1)^(d * (#bonds - sum internal bonds)); LadderCounts: a ladder has >= 4m+2 bonds in its group (the active `IsLadder` has no
   group-bond-count clause: chords between end atoms are allowed), |ladder atoms| = 2m+2.
6. Selection: the ACTIVE `Molecule.IsLadder` (WaveB2Draft/Molecules, B2-CL-3, no 4m+2 clause) makes maximal ladders pairwise disjoint
   (`LadderDisjoint.maximalLadders_pairwiseDisjoint`, MaxLadderDisjoint.lean = copy of <scratch>/waveb2-snap-final/WaveB2-Ladders.lean,
   sha256 in COPIED-SHA256SUMS).  Hinge atoms are removed one at a time (`Lad.remove_atom`): the affected ladder is replaced by at most two sub-ladders of
   consecutive rungs (`Lad.IsL.sub`), losing <= 6 atoms, <= 3 incoherency, creating <= 1 extra ladder.  Result `selection_claim`:
   Inc <= 4 sum(inc_i) + 20(rho+h), q' <= 2(rho+h), (n - sum(2m_i+2)) + q' <= 8(rho+h).
7. Arith.final_arith: the exponent arithmetic.  Parameter choice (Final2): eta0 = min(eta0 of ladderL1Gate, (gamma1/8)^2) (so 4 eta <= gamma1 - sqrt eta),
   C1 = Cg * 3^(2d) with Cg the constant of ladderL1Gate, nu0 from the gate, delta0 = min(delta0_gate, 1), C2 = 1, L0 = max(L0_gate, 2).
   Note the ladder bound has delta^m for 2m+2 atoms; the missing delta^1 is compensated by the leftover coupling factor of each ladder (coupling^(n - sum(2m_i+1))).

## Checks run
(see the end of this file for the logged output)

## Uncertainties, errata, deviations
- ERRATUM (TARGET proof gap, not a false statement): finalsbest1 passes from ladderl1new (fixed outside times, ordered domain, sup over outside times) to the
  product over ladders without addressing the cross-ladder ordering constraints; the correct input is the time-L1 form (see Approach).  L2075-L2077.
- Deviation: the pinned statement is proved for a verbatim COPY (`CoarseSplicedAtC`, copies of `SourceMaximalLadderData` and `SplicedSourcePremises`) because of the
  Sumint environment clash; exact-type equivalence is checked in PinCheck.lean.  At the universe rebase, replace the copy by the pinned names (mechanical).
- lg-spine currently uses `WaveBDraft/System.lean` of snapshots 7/8 (see SONNET-COMMON.md); this proof only uses `coupling` and the frozen WTParams, so the port to snapshot 9 is mechanical,
  but the rebuild against snapshot 9 was NOT done (deferred to the universe rebase).
- Premises unused by the proof: `SplicedSourcePremises.subpro`, `connected` (only passed to `selection_claim`), and `hirr`, `hbal` are only forwarded to the ladder gate.
- `selection_claim` uses the active B2 `IsLadder`; with the older 4m+2 variant maximal ladders can overlap (probe chordLadder) and the claim would need a different proof.

## Checks run (output)
- Fresh closure rebuild (build2.sh, new dir build2/, topological order, 28 modules): every module `exit 0` (build2-all.log, build2-<Mod>.log).
- `#print axioms` (CheckAxioms, build2-CheckAxioms.log): coarseSplicedGate, selection_claim, splicedKernel_le_classes, ladderL1Gate all
  `[propext, Classical.choice, Quot.sound]`.
- Hygiene grep (sorry/admit/axiom/opaque/unsafe/maxHeartbeats) over all scratch .lean files (incl. copied MaxLadderDisjoint.lean): no hit; every file < 1500 lines (max 737).
- Pin check (PinCheck.lean, lg-spine-only LEAN_PATH, `exit 0`, build-PinCheck.log): imports the pinned SourceSplicedBounds, repeats the Spec.lean
  copies, proves `coarse_iff : CoarseSplicedAt P <-> CoarseSplicedAtC P` and `coarseGate_of_copy : WTPrefix CoarseSplicedAtC -> CoarseSplicedGate`;
  axioms standard.  Text diff of the three copied declarations against the pin (modulo the suffix C): identical.
- Pinned hash re-checked at the end: ladder/in and lg-spine live both 38b561144f7153faf94ef3c59bf1b3ebd80e15b8817e49cc3599a3037602d9ba.
- NOT done: rebuild against snapshot 9 / universe rebase (deferred); the final theorem and its pinned form live in two environments that cannot be merged before the rebase
  (Sumint clash), connected by the structure-level iff above.
