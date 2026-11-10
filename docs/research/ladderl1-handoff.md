# HANDOFF S3 LADDER, LadderFourierAt side (w/ladder-fourier continuation) — READY ladder-fourier

## Result
`WaveTurbulence.Ladder.ladderFourier_prefix : WTPrefix LadderFourierAt` (file Final4c.lean), exact-type checked against the pinned
<scratch>/ladder/in/MolecularSpineAt.lean (sha256 b8a8692faa11c091e0b916a74efa46cfabf7032cf6478b43f85d978c7fba4700, equal to the live lg-spine copy at the end):
`example : LadderFourierGate := ladderFourier_prefix` and `example : WTPrefix LadderFourierAt := ladderFourier_prefix` (transient ExactCheck.lean, deleted after the final run).
The bare `LadderFourierAt P` is proved only under the analytic hypotheses `LFHyps P` (Final4a `ladder_fourier_param`); the gate chooses the thresholds:
C1 = 128*(180 d)*(64*(1+d*2^(d-1))) (depends on d only), nu0 = 1, delta0 = min 1 ((1/(2 tau*))^(1/(5 nu))), C2 = 1, L0 from `Filter.eventually_atTop`
(Final4c `eventually_conditions`, `Y_bound`, `delta_small`).

## Files (all in <scratch>/ladder, namespace WaveTurbulence.Ladder; < 1500 lines each, max 737)
Session 1: ElemIneq, TimeLemma..TimeLemma5, AlphaInt, KLemma, PhiFamily, BoxSup, TimeWeights, Core1 (core1 now with per-coordinate radii).
Generic bridge/sum: GenBridge1-5 (Th: iota->R ≃ᵐ Fin k->R × Fin m->R, Phi_eq_Bprod, gen_core), GenSum (sum_sup_le), GenSplit (exists_split(_with)), Valley (volume_Vset_le, NP_sub), GroupVol (volume_groups), GenClass1-4 (pattern partition, theta_bound, class_bound).
Algebra/geometry: LocAlg (loc_alg, loc_shift), LinMaxVolume/LinBoundedSpanning (copies of main LinAlg, lincomblem), LadderDisj (copy of waveb2 Ladders.lean: maximalLadders_pairwiseDisjoint), MolRung, MolGamma (rung identity), MolLadder (flux_const, flux_zero_eq_gap), MolTree (no_peak), MolPres (ladder_eq_of_two), SpecFacts, Count, Local (rung_sum_relation).
Glue: Glue1-9 (PF presentation families, clsPF classes, CD data, loc_S/loc_atom, exists_Sy, class_fourier), Final1-2 (box_sum_bound), Final3a-f (class_cond), Arith1-2 (per-ladder real inequalities), Final4a-c (gate).
Copies with hashes: COPIED-SHA256SUMS (lg-spine olean snapshot in ./lg, LadderDisj, LinMaxVolume, LinBoundedSpanning, pinned inputs).

## Approach (TARGET L1994-2038)
Step 1 (L2003-2008): sum over unit boxes -> 2^n 2^n sum_A ∫ over the 1-neighbourhood of the spectrum (GenSum, elementary_sup_le / elem_sup_Phi). Step 2 (L2018-2024): rung identity Γ_u+Γ_v = <ρ,Y> at interior rungs (MolGamma/Local), lincomblem selection (LocAlg), no interior local maximum of s_j=max(t_u,t_v) (MolTree.no_peak, non-root since degree 4 > 3), valley volume 2^N D^N/N! (Valley, GroupVol).
Steps 3-4 (L2025-2037): partial time integration Uintw_bound + alpha integration (Core1, GenBridge5), K-lemma with L^{5d} values (Count, Glue8). Final accounting (Arith1-2, Final3, Final4): per-ladder estimate (log L)^z D^z δ^{1+10ν}/z! <= L^{δ^{8ν}}-type, classes <= 4^n.

## Deviations from the paper's proof (all documented in PROGRESS.md SESSION 2)
1. No integer-offset classes: the rung-sum relation holds with an error O(X_S), giving radius C0*X_S for X-coordinates (same loss).
2. Only interior rungs 1..m-1 are paired (X/Y); end rungs and selected rungs go to Y. The source claim "Γ_v+Γ_w = 2 r·y_w for every double bond" is false at end rungs (end atoms have extra boundary/chord bonds; IsLadder has no 4m+2 clause). Cost absorbed.
3. The source says the decoration "restricts to |r_j|~P_j" without saying which presentation (u,v) of the ladder; presentations are not unique a priori. We split the spectrum by presentation signature (u0,u1) of each maximal ladder (PF.sig; ladder_eq_of_two shows a presentation is determined by it), at most prod_S |S|^2 <= 4^n classes.
4. Step 2 "no local maximum" at non-root atoms: formalized with deg 4 > 3 for roots (root_degree_le_three).
5. Constants: K = 2 arsinh(M)+1 with M = 2(⌊2L⌋+1)^{4d} instead of "C0 log L"; Y_bound gives 3(2K)<=180 d log L for log L >= 20.
## Errata / suspicious points in the sources
- TARGET L2013-2014 (Step 1): "Γ_v+Γ_w = 2r_j·y_w" only valid at interior rungs (see Deviation 2).
- TARGET L2034/L2036: exponent z_j-d in the factorial: our valley bound gives (2D)^{K}/K! with K >= z_j-1-d.
- Pinned LadderFourierAt is not provable for an arbitrary P (C1 free); the gate WTPrefix LadderFourierAt is (as pinned).
## Checks run (see fresh2-summary.txt, fresh2-*.log)
- FRESH rebuild of all 59 modules (+ transient ExactCheck, deleted) in topological order into build-fresh2 (script fresh2.sh): exit codes in fresh2-summary.txt (all 0 required).
- `#print axioms WaveTurbulence.Ladder.ladderFourier_prefix`: propext, Classical.choice, Quot.sound.
- Hygiene grep over *.lean (sorry|admit|axiom|opaque|unsafe|maxHeartbeats): clean (only the transient `#print axioms` line in ExactCheck.lean).
- Exact-type check: both `example`s above compile.
## Uncertainties
- lg-spine snapshot (./lg, hash in COPIED-SHA256SUMS) was copied at session start; the live lg-spine may change; the closure used only SplicedMoleculeDecoration/GardenIncidence/GardenMoleculeAxioms/GardenNodeCounts/MolecularSpineAt facts (spliced_molecule_Gamma, spliced_molecule_decoration, garden_molecule_deg_le_four, root_degree_le_three, garden_isMolecule, garden_card_atoms, gardenSource_eq_zero_of_deg_four).
- LadderDisj.lean (copied from waveb2/src/WaveB2Draft/Ladders.lean) compiled against the lg-spine Molecules (same definitions up to ParentDefs import); on landing merge with the main-branch version.

# LADDER-TT (AMEND3 / R33 F-TT) addendum, 2026-11-05
Rebased onto lg-spine-u build-fresh-a3 (SplicedKernelData.rootTime; splicedTimeDomain G layer rootTime truncated). Backups: pre-tt/ (ladder), ../ladder-decay/pre-tt, ../coarse-spliced/pre-tt.
No STOP: no lemma needs untruncated boxes.
- LadderFourierAt (this dir): the generic engine takes a cap function. GenBridge2: OmegaC/Rmod/Mset/NullBd/hiF gain `cap` (strict t_v<cap_v in OmegaC/Rmod; Y-limit hiF = fold min (min (ls+1) cap) over X-neighbours, i.e. the root constraint is one more fixed endpoint, Uint_bound uniform in (l,u)); GenBridge3-5, GenClass2-4 thread `cap`; Om0 ch ls cap; Final1 `splicedTimeDomain_eq_Om0` (cap = fun v => rootTime v.1.1); Final2/Glue9/Final3f/Final4a pass D.rootTime. Final4c statement unchanged: `ladderFourier_prefix : WTPrefix LadderFourierAt`.
- LadderDecayAt (../ladder-decay): unaffected: sourceLocalLadderKernel uses fixed `outside` times, no splicedTimeDomain. Sources unchanged; rebuilt all 56 modules against lg-spine-u (merged-tt = lg-spine-u + sumint symlinks, build-tt), exit 0; LadderDecayAt text in lg-spine-u identical to the copy; lg-only check chk-tt/ExactCheckTT.lean (`LadderDecayAt = LadderDecayAtCopy := rfl`, gate_of_copy) exit 0.
- CoarseSplicedAt (../coarse-spliced): only Assembly1 edited (D.rootTime threaded; the domain enters only via inclusion in the unit box ubox, true for the truncated domain). Two lg-spine modules not in lg-spine-u copied unchanged (SplicedAmplitudeSplit, SourceLadderGeometry; sha in COPIED-SHA256SUMS). All modules rebuilt (build-tt) exit 0; pin unchanged (same SourceSplicedBounds sha); PinCheck in lg-only env exit 0. FineSplicedAt is not in these packets.
- Checks: ladder fresh rebuild build-fresh-tt (60 modules + ExactCheck: `example : LadderFourierGate`, `WTPrefix LadderFourierAt`) all exit 0; axioms of ladderFourier_prefix, ladderDecayGate, coarseSplicedGate, selection_claim, splicedKernel_le_classes, ladderL1Gate: propext, Classical.choice, Quot.sound only; hygiene grep clean.
- Builds: ladder btt.sh/bfresh.sh; ladder-decay btt.sh env-tt.sh; coarse-spliced btt.sh.
