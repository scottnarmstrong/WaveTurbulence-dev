# V5 W2 core session 4 (after R78): remainder rows + Kb amendment -- `uniformTermCert` NOT yet proved -- CHECKPOINT vineest-W2

**Files** (uni/src/VineEstS5C/P4/W2/, namespace WaveTurbulence.VineEstS5C.P4.W2, `module`, build `uni/w2b.sh VineEstS5C.P4.W2.<M>`, all exit 0): `RemModes`, `RemShift`, `RemProd1`, `RemProd`, `RemRowsC`, `PieceRowsR`, `ExcGeoI` (new); edited Final (R78 item 2, authorized): `Final/Iface.lean`, `Final/Core.lean`, `Final/Prefix.lean` (originals in uni/scratch8/pre-kb/).
**Approach / results.**
1. F-REM-ORIENT (R78 item 1) DONE: `fs_expansion_C`/`rowModes3_of_restr_C` (remainder modes everywhere on a continuity set `Bc`), `remRowShiftMul` (shifted couple remainder times weight-0 multiplier), `remRowProd` (THREE-clock row `cutW(f(c0,c2,k+u r) g(c1,c2,k))`: modes = convolution in the shared clock; `snorm_tsum_le` via `iteratedFDeriv_tsum`, `maxBracketPow_merge_le` (sqrt2^theta), `fsPhase_merge`, Cauchy product regrouped along the bijection `mergeEquiv`; no 4-clock row is needed), `remRowMulDC`, `remRowC`, `oneRowC`; `PieceRowsR`: `RemC` (remainder structure: `ContinuousOn Bc`, `XNormRestr < ofReal CR`), `pieceRep_SR/RmS/RR/RmDS/RP` = the six remainder row shapes rA1..rB3 in both orientations (table in PROGRESS "V5 W2 CORE SESSION 4").
2. Kb amendment (R78 item 2) DONE: `UniformTermCertAt A Pe Km Kr Kb` with the factor `Kb ^ bb` (bb = card of bad vines) in the `Lp` slot; `UniformTermCertTarget`: `∀ ν δ D, 0<δ → τ=Dδ → ∃ Kb ≥ 1, ∀ C₂ L, ...`; Core: `hC₂ : countKp D * Kb ≤ C₂`, `wpF_classBM` applied with `Lp := Kb^bb * Lp`, `C₂ := C₂/Kb` (`div_pow; field_simp`); Prefix: `C₂ := max (..) (countKp D * Kb)`. Logged in PROGRESS "W2 TARGET CHANGE LOG 2".
**Checks run.** each module `uni/w2b.sh` exit 0; `#print axioms` of remRowProd, remRowShiftMul, remRowMulDC, remRowC, oneRowC, pieceRep_SR/RmS/RR/RmDS/RP = [propext, Classical.choice, Quot.sound] (uni/scratch8/Ax4.lean); Final/Iface, Core, Prefix rebuilt exit 0; no sorry in the new files.  NOT run: fresh rebuild with farm, exact-type example (theorem absent).
**Not done (see PROGRESS NEXT).** R78 item 3 (F-AUX-CONT corner), item 4 (ExcGeo type I/II geometry), and the assembly (c)(d): per-summand dispatch of `bundlePt`'s 12 constructors x case A/M to `pieceRep_*` (data: gate `SepTC`/`RemC` from `certC/certT` + `GateEnv`, identity set `V`, remainder `remQ/remT = rowQ - Qf`), the certificate over all operative levels (QNE records -> `hrow_of_rowwise_exc`, `freeDict_of_rowForm`, constraints, AmbW fields), `engine_rhs` for `beta'`.
**Findings / uncertainties.** (i) remainders are only `ContinuousOn Bc` in general (the gate approximants' time factors are clamped), hence the `Bc` forms of all remainder rows. (ii) F-AUX-CONT corner: the face `tt 0 = L4+1` (q = Lh = L4+1) is where the clamped time factor jumps; R78 says prove the bound on the box minus the face and extend by continuity; note `TermCertW` has `Bx = outBox` (closed) built in, so the extension must happen in Final (replace `Bx` by the box minus the face in `termBoundW/habsW` consumers + the X7 continuous-trace lemma `mixedRestrictionNorm00_continuous_trace_le`), or `TermCertW` must take `Bx ⊆ outBox` with `outBox \ face ⊆ Bx`: a design decision for wt-orch. No errata in pinned sources.

# V5 W2 CORE session 3 (Sonnet): PieceRep layer + record geometry -- `uniformTermCert` NOT proved -- CHECKPOINT vineest-W2

**Files** (uni/src/VineEstS5C/P4/W2/, namespace WaveTurbulence.VineEstS5C.P4.W2, `module`, build `uni/w2b.sh VineEstS5C.P4.W2.<M>`, all exit 0): `ExcGeo`, `PieceRep`, `PieceSp`, `PieceRows`, `PieceRowsJ`, `RemMulD` (new; AuxMul and the other Aux modules unchanged and imported).
**Approach / results.** See PROGRESS.md "V5 W2 CORE SESSION 3": `exc_low_ret_eps` (low = ret + eps (E0-E1), |eps| = 1), `clock_lower_piece`, `brSlot_spec`, `exc_vars`, `split_sb_b` (record geometry); `PieceRep` (two-row representation) with `pieceRep_sep`/`pieceRep_joint` on the slot-general Aux rows; all ten non-remainder shapes of `bundlePt` (A1, A2, KQ, KT, TQ, TT and case M MKQ, MKT, MTQ, MTT; case-M A1/A2 are case-A A2/A1) as `PieceRep` from raw SepTC data, with all spatial factors on the K row (`spS`, `spS_bound`); `remRowMulD`.
**Checks run.** each module `uni/w2b.sh` exit 0; `#print axioms` of exc_low_ret_eps, split_sb_b, exc_vars, brSlot_spec, pieceRep_KQ, pieceRep_MTT, pieceRep_joint, remRowMulD = [propext, Classical.choice, Quot.sound] (uni/scratch8/Ax3.lean); hygiene grep clean.  NOT run: fresh rebuild with farm, exact-type example (theorem absent).
**Findings / uncertainties** (details in PROGRESS): F-REM-ORIENT (remainder shapes in the twisted orientation need a shifted-remainder row and a product of two remainders in one 3-clock row); jointRowW's constant depends on Rb ~ D+1 (violates D-uniformity of Km, Kr unless time-translation invariance or C2^b absorption); F-AUX-CONT corner tt 0 = L4+1 for exterior clocks; qr = R.right (type II) and qb = qr (type I) geometric facts not yet proved.  No errata in pinned sources.  Deviation: `remRowMulD` is a copy-edit of AuxMul (different weight placement), recorded.

## W2 AUX (S-W2AUX, Sonnet; READY w2-aux)

**Files.** `uni/src/VineEstS5C/P4/W2/Aux{Ae,Rows,Mul,Cont,Cont2,Cont3,Cont4,Leaf,Leaf2,Leaf3}.lean` (1108 lines; all `module`; no existing module edited). Build `uni/w2b.sh VineEstS5C.P4.W2.<M>`; fresh `uni/fresh-w2aux.sh` -> `uni/buildS5C8aux`.  Statements: PROGRESS.md "W2 AUX EXPORT".

**Approach.**
1. `AuxAe.hasSum_of_ae_contOn`: an a.e. Fourier expansion of `g` on `B` (absolutely summable coefficients) holds at every point of `Bc ⊆ B` if `g` is `ContinuousOn Bc` and `Bc ⊆ closure (interior Bc)` (a.e.-zero continuous function vanishes on an open set, then on its closure).  `AuxRows`: `sepRowWS`, `jointRowWS` (the proofs of `sepRow2_exists`/`jointRow_exists` with the a.e.-clock step replaced by this lemma; slots `s : Fin k -> Slot D` arbitrary, no injectivity; the slot values must lie in `Bc`; for `jointRowWS` also `Bc3 ⊆ {τ 0 ≠ τ 1}` so that `|τ0-τ1|^{-(1-3η)}` is continuous), `remRowWS` (= `remRowS`, continuous `f`).  `AuxMul.remRowMul`: coefficients `ĉ_m(k) G(r,k)`, per-mode bound by `SNorm_mul_le` (`G r` at weight 0), constant `C * 2^Λ₁ d^Λ₁`.
2. `AuxCont*`: `SepTC` (SepT + continuity set).  The certified factors are `padJ (clampJ q ·)`; `clampJ q Jc` is continuous on each side of `ts 0 = q` only.  `certC_gate`/`certT_gate` identify `q ∈ {L4} ∪ [L4+1, Lh]`; consequently continuity on the whole HIGH window, and on the LOW window minus the line `t = L4 + 1` (the whole low window when the root layer is `≤ L4` or the index is trivial); `SepTC` packagings `cert{C,T}_{hi,lo}TC`; the `sffOf` instances in `AuxCont4`.
3. `AuxLeaf*`: `card_inputLeaves_add_marked` (2|in| + |marked| = 2 order + w), plain couple |in| = order+1, paired tree |in| = order; with `zp_sizes`/`size_eq_order`/`decodesTree_order'`: `zp_leafCard`, `native_leafCard` (both `2 zpN + 1`), `zp_leafCost_eq`, `native_leafCard_start`, `zp_leafCost_eq_native`, `zp_leafCost_eq_lvl` (the level form with `nativeCoupleLayered RD ..` at `p₀` and `nativeChainLayered RD ..` at the lower branch).

**Checks run (exit codes direct).** All 10 modules `w2b.sh` exit 0; fresh rebuild `fresh-w2aux.sh` all 10 exit 0 (`logs/fresh-w2aux.out`); `#print axioms` of 27 exports (`scratch8/AuxAx.lean`): all [propext, Classical.choice, Quot.sound]; hygiene grep (`sorry|admit|axiom|opaque|unsafe|maxHeartbeats|maxRecDepth`) over the Aux files: no hits; exact-type check (`scratch8/AuxCheck.lean`, `example : <posted statement> := <theorem>`) for `sepRowWS`, `jointRowWS`, `remRowMul`, `remRowWS`: passed; transient use check of `zp_leafCost_eq_native` at `lv.state` (now `zp_leafCost_eq_lvl`): passed.

**Uncertainties / findings.**
* F-AUX-CONT (important for the core): with an exterior clock the Fourier expansion is only usable where the time factor is continuous. For W1's terms the line `t = q` is a genuine discontinuity of `clampJ q Jc` (`Jc(q,s) ≠ 0` in general). It lies in the low window only at its right edge `t = L4+1` when `q = Lh = L4+1`; this point is outside the identity set `V` (`t ≠ q`), where `ObjExp.term` is the fallback. So an exterior slot clock `= L4 + 1` in that case cannot use the separated row; the core must either keep the clock `< L4+1` (hypothesis `slots ∈ Bc`) or treat that null line separately. No statement of W1 was changed.
* `remRowMul` has the extra hypothesis `1 ≤ P.d` (needed by `SNorm_mul_le`) and takes the multiplier with `⨆ r SNorm Λ₁ 0 (G r) ≤ ofReal Cg` (weight 0 on the multiplier, row weight on the remainder), i.e. `G` should already contain its `r`-cutoff (e.g. `spG`).
* The leaf-cost identity is an equality of `layerCost` for a constant layer bound `B₀` (value `B₀^{2 zpN + 1}`); it needs `B0` constant, as `VineEstCanonLayerC2M` uses `fun _ => B₀`.

**Errata / deviations.** None in the pinned sources. Deviation: none (new modules only).

READY w2-aux

# V5 W2 CORE session 2 (Sonnet): foundations of (b1)/(b2)/(c), `uniformTermCert` NOT proved -- CHECKPOINT vineest-W2

**Files** (uni/src/VineEstS5C/P4/W2/, namespace WaveTurbulence.VineEstS5C.P4.W2, all `module`, each < 85 lines, build `uni/w2b.sh VineEstS5C.P4.W2.<M>` into buildS5C8, all exit 0, no sorry/admit/axiom/opaque/unsafe/maxHeartbeats): `ExcMom`, `ExcMom2`, `RowSlot`, `SpaceG`, `RowAsm` (new this session); session 1: `NEStep`, `ExcRec`, `ExcInd`, `ExcFam`, `RowNE`, ....  Probe files in uni/scratch8/ (Ax.lean = the axioms run).
**Approach / results.**
* `ExcMom.cl_boundary_momentum_loc`, `ExcMom.split_gap_lattice`, `ExcMom2.region_lower_eq_of_subset`, `ExcMom2.split_low_ret`: the momentum relation low - ret = +-(E0 - E1) (finding 3) as a lemma for LOCAL decorations: `sigma_lower (latt x_lower - latt x_retained) = latt x_(b.child pos) - latt x_(b.child neg)` for the lower joint of any split, with `pos/neg` of ANY enclosing block with the same bottom.  Proof: `RegRed.cl_boundary_momentum` re-proved with `sum_slotSum_eq_externalSlots_local` (b4b-prep) applied to the lower block T of the split, `split_excluded_b` (T's excluded child = S's kept child = the retained leaf), nested-block slot uniqueness.
* `RowSlot.remRowS`: `RowData` (with `Ae`) for a time-continuous kernel with arbitrary clock slots (the constructor of the native rows).
* `SpaceG.spG`, `snorm_spG_le`: the generic spatial weight of a K row (shifted product of two r-dependent factors, decay from one).
* `RowAsm.hrow_of_rowwise_exc` (b2): the pair/branch row product with exceptional rows matched jointly.
**Checks run.** Each module built with `uni/w2b.sh` exit 0 (logs in uni/logs/buildS5C8-*.log); `#print axioms` of all seven new theorems: [propext, Classical.choice, Quot.sound] (uni/scratch8/Ax.lean, run with `uni/p8.sh`); hygiene grep over the five files: nothing.  NOT run: fresh rebuild with farm, exact-type example against `UniformTermCertTarget` (the theorem does not exist).
**Findings (details and the exact next steps are in PROGRESS.md "V5 W2 CORE SESSION 2").**
* F-TWIST-ORIENT: for TWISTED states the bundle summand has the couple at `low` and the tree at `ret` (verified from `rowVal_dict`), so P2's `piece_A2/KT/TT` (K at x) cannot be applied literally with K at the pair row (momentum ret) and L at the branch row (momentum low, r-independent); the recommended uniform design puts all spatial factors on the K row (shifted by 0 or eps r, `spG`) and only time factors on the L row.  Needs `remRowMul` for the remainder summands of the twisted family.
* F-EXT-CLOCK: s1, t1 may be exterior clocks (type I vines have no rung atoms); `sepRowW/jointRowW/remRowW` need TVar clocks; slot-general versions need continuity of the separated time factors (`SepT` forgets it).
* F-ROWS-GEN, F-M0, F-LEAFCOST: see PROGRESS (native rows via `remRowS`; M0 independent of bk/cons/g; leaf-count identity for the exceptional objects missing).
**Errata / deviations.** None found in the pinned sources.  Deviation: none (no statement changed this session; the earlier W2 TARGET amendment `(hinc : IncoherentGateH Pe)` stands).
**Uncertainties.** (i) Type-I operative vines: by `typeI_leaf_pair`/`typeI_parent` the lower joint b is a child of the upper joint a and the partner of the retained leaf is a child leaf of a, so `qb = qr = a` (as nodes): `s1 = t1` identically, the A1, A2, TQ, TT summands vanish identically (`s1 <= t0 < t1`, `Q(s1) - Q(t1) = 0`, ...) and only KQ/KT (kind 1, factor ||r||) and the remainders survive -- consistent with TARGET's remark that vines (I) always carry `|r|`.  A vanishing summand needs no rows (certify it with the native rows and an engine datum whose extra constraints are contradictory, so the engine time domain is empty a.e.), but this needs `qb = qr` as a lemma (not proved) and the clock `u a = tt 0` may be an exterior clock (F-EXT-CLOCK).  (ii) The hand-off of the K/L placement for type II twisted summands is a design correction (F-TWIST-ORIENT), not an obstruction.

# V5 FINAL (session 5, Final agent): prefix theorems, CONDITIONAL on W2 -- CHECKPOINT vineest-final

**Files** (uni/src/VineEstS5C/P4/Final/, namespace WaveTurbulence.VineEstS5C.P4.Final; build `uni/build5c8.sh VineEstS5C.P4.Final.<M>` into buildS5C8; all exit 0, no sorry, all `module`, each < 160 lines): `Iface`, `Mono`, `Trunc`, `Core`, `Prefix` (new); `BotCount`, `Class`, `ClassM` (session 4).
**Approach.** `Iface.UniformTermCertTarget` (W2's deliverable, posted verbatim in PROGRESS.md "W2 TARGET (from Final)") = prefix-form uniform beta' with `TermCertW` for every modPsi b lam psi, psi in Lvl.termsB, and ||c zeta||e beta' <= ofReal(Lambda ((Ns sqrt delta)^n2 Lp lf)), Ns = engNs eta c0 Km Kr (Km,Kr fixed before nu,delta,D,L). `Trunc`: F-trunc (finding 1): the modulated class integrand depends on F only at layers <= p (kernelK_congr_inputs on each native KQstar/KTstar factor, members' layers via Cont.reach_stateLayer_le), so h is replaced by truncF p h, which has full coset summability. `Mono.sumintMixPar_mono`: copy-edit of VineEstS3.sumintMix_mono for SumintMixParDoubledAt (moves the prefix input to engine params {P with C1 := c0}). `Core.vineEstCanonLayerC2M_core`: for Pe, GateEnv from the gate + ProfileBound of truncF p h, UniformTermCertAt gives beta'; `twistedRecenteredModC_eq_clsFnRM` + `wpF_classBM` (Bx = outBox, K = outSet of step3D, q = qOut) + `W2.termBoundW`/`habsW` give the literal bound. `Prefix.vineEstCanonLayerC2M_of_uniformCert (hU : UniformTermCertTarget) (hG : LeafwiseCoherentApproximationGate) (hR : RealityAll) : WTPrefix VineEstCanonLayerC2M` (pattern of vineestStep3Layer: c0 = max CS CG, C1 = max 1 ((cc+1) countKc Ns), C2 = max(.., countKp D), L0 = max LS LG) and `vineEstCanonLayerHalfM_of_uniformCert` via `vineEstCanonLayerHalfM_of_C2M`.
**Checks run.** Each module built singly (exit 0). Transient probe (deleted): `#print axioms` of vineEstCanonLayerC2M_of_uniformCert, vineEstCanonLayerHalfM_of_uniformCert, twistedRecenteredModC_congr_F, sumintMixPar_mono = [propext, Classical.choice, Quot.sound]; exact-type `example ... : WTPrefix VineEstCanonLayerHalfM := vineEstCanonLayerHalfM_of_uniformCert hU hG hR` compiles. Hygiene grep (sorry/admit/axiom/opaque/unsafe/maxHeartbeats) over Final/: clean. NOT yet run: fresh rebuild of Final (needs W2 READY first), unconditional composition.
**Remaining.** `Final/Export.lean` composing `uniformTermCert` (W2) into unconditional `vineEstCanonLayerC2M`/`vineEstCanonLayerHalfM`; fresh rebuild with farm; final checks.
**Uncertainties / deviations.** (1) The target quantifies over ALL engine params Pe with AmbP 6561 Pe, tau = D delta, 2 <= L (no other gate beyond GateEnv's CoherentGateH); if W2 needs IncoherentGateH or more it must be added to Iface (change-log in PROGRESS). (2) Named inputs of the prefix theorem beyond W2: LeafwiseCoherentApproximationGate (spine gate, as in Step3) and RealityAll (P1 Mix); hR is a statement-level input of bundleFamOf, not discharged here. (3) eta0 includes eta <= 1/5 to give AmbP's eta < 1/4, 6 eta^6 <= eta. (4) `TermCertW`'s box/set are the Par engDatum ones; the target states VineEstS3.Eng.outBox/outSet of step3D, so W2 proves their equality. No source errata found this session.

# HANDOFF FLAT-MOD (R60, F-W2-FLAT) -- READY flat-mod
## Files: uni/src/VineEstS5C/P4/FlatMod/*.lean (14 modules, new only; no existing module edited). Build: uni/build5c7.sh -> uni/buildS5C7 (farm5c7.sh); fresh: fresh5c7.sh -> buildS5C7f, log logs/fresh-flatmod.out.
## Approach: see PROGRESS.md "FLAT-MOD EXPORT". Statement of the main result there. No hypotheses beyond those of Lvl.classSum_eq_flat (hL, hF, hprime).
## Checks: see final message. Deviations: none; uncertainty: b is taken as the global lower joint of B (lv.hcb), as in R58.  No errata found.
# HANDOFF P4-W1W3 (V5 P4 W1 + W3, Claude Opus, 2026-11-06) -- READY vineest-W13 (exact statements: PROGRESS.md "P4-W1W3 EXPORT")

## Files (uni/src/VineEstS5C/P4/W13/, all `module`, no sorry, namespace `WaveTurbulence.VineEstS5C.P4.W13`, 13 files, each < 250 lines)
Analysis (null sets, a.e. congruence, `XNorm00Restr_trace_cross`, continuity of `SourceApp`, `leafwise_cont`), ObjExp (`ObjExp`, `ObjCert`, padding),
ZpGeo (parent layers / coherence of the objects of `Zp(A)`), ZpObj (`clampJ`, `VC`, `VT`, `zpQ_expand`, `zpT_expand`), Cert (window bounds, `ContExp`,
`ObjCert.ofCont`), SFF (`GateEnv`, `certC`, `certT`, `sepFamOf`), SFFam (`sffOf`, `sffOf_bounded`), WinLayers, Mem (`mem_certC_V`, `mem_certT_V`,
`zp_half_sizes`), BadCount (operative ⇒ bad, `card_core_le_bad`, `sum_zpN_le`), WPF (count, `wpF_absorb`, `wpF_top`), EngineRHS (`engine_rhs`),
ClassBound (`wpF_class`).  Scripts: uni/build5c4a.sh (BD overridable), uni/farm5c4a.sh, uni/fresh5c4a.sh, uni/probe5c4a.sh.  No existing module edited;
no other packet's file edited.  Codex leftovers in P4/W13 + buildS5C4a (reverted takeover) moved unchanged to uni/quarantine-CODEX-W13/ (README), unused.

## Approach
* **W1 (SepFamFam)** as planned in HANDOFF "Remaining work" (P4 session 3).  For an index `b ∈ bsA ∪ bsB` of the bundle at an operative member, each
  object (couple `zpQfam κ A b`, tree `zpTfam κ A b`) gets a gate level `q`: (i) root layer `≤ L₄` → `q = L₄`, coherence at `(L₄, L₂)` natively or, for a
  II-b state with both roots `≤ L₄`, through `ZpSurj.carrier` (`zp_coh_lowC/T`); (ii) root `> L₄` → `q = Lₕ = max(q₁,q₂)` (native parent, `zp_high_C/T`).
  The gate (`CoherentGateH`, LeafwiseSeparated) at `(q, L₂)` is taken with CONTINUOUS time factors (`leafwise_cont`: `restr_ae_cont` + continuity of
  `SourceApp` + `eqOn_zero_of_ae`).  The identity `zpQfam b t s = ∑ δⁿ Jᵢ(min t (q+1), s) Mᵢ` holds for `t > q` (P1 `couple_eq_ext` + `extConst`; R35:
  `t > q ≥ Lr` so the trivial exact kernel is the extension), and `zpQfam b t s = 0` for `L₄ < t ≤ Lr` (`couple_root_vanish`, the EMPTY expansion of
  (ii)); `clampJ q J := 0 below q, J(min t (q+1), ·) above`.  Window certificates (`P2.SepT`) on `timeBox L₄ L₂` and `timeBox Lₕ L₂` (`timeBoxGt`
  for trees) with one pair of constants: native window (`congr_on`), trace window `w ≥ q+1` (`XNorm00Restr_trace_cross`, trace at `t = q+1`, cost
  `TR(η) = traceConst(1-η) χ₀`), zero window `w+1 ≤ q` (a.e. zero).  `PtOK := True` with a fallback term off the identity set (`ObjExp.term`), since
  the tree gate covers only `s < t`.  `Bounded`: `m = max m₀ 1 ≤ 2ⁿ ≤ 2^{zpN}` (`zp_sizes`).
* **W3**: (a) every core vine is `IsCoreCLVine` (type I or II), hence bad (`core_kind_bad`); an operative vine is a core member, and directly
  `FamilyOperation.eligible` gives type I/II (`op_kind_bad`, any kind).  So the count's `4^p` per member gives `(192·4^𝔇)^{#core} ≤ (192·4^𝔇)^b`
  (`card_core_le_bad`), absorbed by `C₂^b` (R54).  NO STOP: an operative vine is never good.  (b) The `C^N` part: the exceptional pair of core vine `i`
  is the tree at its lower joint (an interior branch) and the couple at the pair of its retained leaf (a regional pair), pairwise distinct over `i`
  (`vineOf_lower`, `placement_pair_eq`), so `∑ 2 zpN_i ≤ n₍₂₎ - M` (`sum_zpN_le`) and `(32·12⁹)^{∑ N_i} ≤ (32·12⁹)^{n₍₂₎}` is absorbed by `C₁`.
  (c) `wpF_absorb`/`wpF_top`: `(cc+1)·#terms·β ≤ Λ (C₁√δ)^{n₍₂₎} Lp lf C₂^b` for `C₁ ≥ (ccη+1)·32·12⁹·Nₛ`, `C₂ ≥ 192·4^𝔇` (`cc_translate`: the cube's
  cutoff constant is `ccη η`).  (d) `engine_rhs`: the engine form of a term bound (`‖cζ‖ (ccη+1) mass engineConst3 maxPar^{η⁶} sumintRHS0 ∏L^{wg} ∏b_ρ`,
  i.e. `‖cζ‖ₑ · AmbW.pre · ∏ b_ρ`) → `Λ (Nₛ√δ)^{n₍₂₎} L^{-η⁸(M₀ˢ+M₁ˢ) - η²b + η⁷} lf` with explicit `Nₛ = engNs η c₀ Km Kr`, from the shape facts, the gain
  bookkeeping `M₀ˢ + M₁ˢ ≤ D.M₀ + D.M₁`, `mass ≤ Km^{M+1}`, `maxPar^{η⁶} ≤ Λ` and the row product `∏ b_ρ ≤ Kr^{2M}(2c₀²δ)^{Sₙ}L^{-w M₁(D)} lf`.
  (e) R58: `Λ` is a free factor ≥ 0 throughout; `Λ := (1+|λ|)^{6η⁶}` gives EXACTLY the RHS of W2's `VineEstCanonLayerC2M` (exact-type example run).
  (f) Invariance (R31(2)) in this framework: all unrolled terms live on the START region (`Lvl.top B`), so `n₍₂₎`, `M`, `b` are the start's; the
  exceptional orders of every twisted state equal the start's (`zp_half_sizes`, `zp_sizes`); `RowSizes` for the gates: `zpN ≤ RD.size/2 ≤ order ≤ N_{p+1}^4`
  (`zpN_start_le`); `n₍₃₎` enters through `hnum` of `engine_rhs` (W2 supplies `cohmolIndex + M₁(start) ≤ D.M₀ + D.M₁` for its datum).
* `wpF_class` assembles W1 + W3 with P4's `top_boundR` for the family `bundleFamOf hR (sffOf E hord)`.

## Source readings
TARGET L1880-L1935 (Step 4: replaceterm1 L1890-L1896; II-a/II-b readings L1898-L1903; (a)-(d) L1905-L1915; count `C₂ C₀^{n(Q)+n(T)}` L1919-L1922; the
constant extension L1913-L1919 "(i) if q > L_r then … constant in t … (ii) if q = L_r … equals 0 if t = L_r … with X^{1-η} weakened by X^{1-2η}";
the case `L_{u3} > L_{u4}` and `Bs''` L1923-L1933).  TARGET L1593-L1622 (sumint: modulations `e^{πiλt}` at every input time, (FourierboundI) loss
`[max ⟨λ⟩]^{η⁶}`), for R58.  RULINGS R30, R31, R35, R46, R51, R54, R57, R58, R60.

## Checks (exact) -- see the end of this section (filled after the fresh rebuild)

## Deviations (recorded)
* W1-D1: the gate is used through `CoherentGateH` + `leafwise_cont` (continuous time factors), not through `P2.couple_gate_data`, whose `SepFam` time
  factors are arbitrary: the constant extension past `q+1` needs the trace `J(q+1, ·)`, which the restriction norm controls only for continuous
  representatives.  Same bounds (`≤ C₁^{n+1}` on the gate box; strict `< 2 TR(η) C₁^{n+1}` on the windows).
* W1-D2: `PtOK := True` with a fallback term off the identity set (the bundle demands the tree identity at window points with `s ≥ t` when
  `L₂ ∈ {L₄, Lₕ}`, outside the tree gate's box); every piece of the bundle reads the terms on the identity sets (`mem_certC_V`, `mem_certT_V`), up to
  the null edges `t = L₄, L₄+1`, `s = L₂+1` of the closed window boxes.
* W1-D3: TARGET's weakening `𝔛^{1-η} → 𝔛^{1-2η}` (L1917) is not needed in Lean: the trace in the Fourier-`L¹` restriction norm costs the constant `TR(η)`.
* W3-D1: the count hypothesis of `wpF_top`/`card_le_count` is the `∏_{members} wtOf` form of P4 `card_terms_le_wt`; BOT-DECOMP's expanded multiset
  (R60) must supply its count in this form (its bottom bundle size `≤ wtOf` of the bottom core index).
* kind = true (R57): `Lvl.Op`, ZP-SURJ; `op_kind_bad` is kind-generic; the V5-KIND pass generalizes the rest.

## Uncertainties (for W2/W4)
* U1 (constants): `C₁ = (ccη+1)·32·12⁹·engNs η c₀ Km Kr` must not depend on δ, 𝔇, L: the row/mass constants `Kr`, `Km` of W2's certificates must be
  chosen from `(η, d, c₀)` only.  P2's `piece_*` give `∃ C` AFTER `AmbP A P` (which contains `P.L`, `P.δ`); the independence is not visible in the types.
* U2 (joint pieces across windows): when `Lₕ = L₄ + 1`, the TQ/TT pieces evaluate one object at clocks in two different unit windows; P2's
  `piece_TQ/TT` need both clock pairs in one cell box.  W1 provides continuous clamped factors and bounds on each window, not a bound on a two-cell box;
  W2 needs a variant (for `Lₕ ≥ L₄ + 2`, `|s₁ - t₁| ≥ 1`).
* U3: the remainder rows at the twin's window (II-b index `b ∈ bsA`) use `remQ κ Qf b` with `b`'s carrier objects; their gate is the twin's native one
  (W2/P1; not part of W1's `SepFamFam`).

## Errata
None new in TARGET (L1917's `𝔛^{1-2η}` is a valid but unnecessary weakening; R35 / E25 / E26 already recorded).

# HANDOFF BOT-DECOMP (V5 P4 sub-packet, R60 / F-W2-BOT, Sonnet 5.5) -- READY bot-decomp
## Files (uni/src/VineEstS5C/P4/Bot/, all `module`, no sorry, 1883 lines, each < 270; namespace `WaveTurbulence.VineEstS5C.P4.Bot`)
Idx (BT, botSet, BotSurj, BotLayers, botA/botB/botSigma, row lemmas, sum_botA_reindex, bot_carrier_sum_eq), Surj (BRel, opBT, bt_ext, bot_classify, bot_twin_state, `botSurj_of_state`, `botLayers_of_state`), Mix (botQfam/botTfam = mixFam, bot_hsub/hQ0/hT0/hreal, remainder = gate remainder), Dict (botFrame, botVars, psiBot_eq_dict, psiBot_eq_repl), Decomp (**bundle_decomp_bot**, **bundle_decomp_bot_mirror**), Win (bot_window_caseA/M), Exp (BotSepFam, BotWin, botWin_holds, botTerm, psiBot_eq_sum_terms, card_botCh), Terms (BotExp, BotExpFam, **Lvl.termsB**, WinOfExtBot, **Lvl.psiFuel_eq_termsB_ext**), Family (hup_of_max, botSurj_of_op, botLayers_of_op, BotSepFamFam, bundleBotExpOf, **bundleBotFamOf**, winOfExtBot_bundleBotFamOf, hq2_of_bot), Count (Lvl.card_termsB_le_prod), Unroll (mem_termsB_succ, termsB_induction, clsFn_eq_sum_termsB_ext, unrolled_boundR_extB, unrolled_boundR_extB_prod).  No existing module edited; nothing copied (ZP-SURJ build-fresh and the worlds on LEAN_PATH read-only).
## Approach
The bottom bundle `psiBot` (4d-B2) is `∑_{G ∈ canonFinset p A c0} ε_G · frame(c0) · rowVal_G · bFac`; `psiSB` is the same with the split block and no `bFac`.  `rowVal_dict` (generic) gives the signed sum of (replaceterm1) with `t₀ = u c0.b` (`psiBot_eq_dict`), `exact_eq_repl_add_rem` the pairing form (`psiBot_eq_repl`), `replSum_decomp_ext` (+ `replSum_mirror`) the decomposition, exactly as for `bundle_decomp`.  The index type is `BT = Σ Bs, ChainAt`, since at piece index 0 no `SplitAt` exists (`IsBlock` requires distinct joints, a split needs `tb.a = tb.b = lower`), so `ZpSurj` cannot be applied; ZP-SURJ's state-level construction is reused and only its last layer (`twin_state`, `zp_twin`, `zp_carrier`, `zp_coherent`, `zpLayers_of_start`: ~250 lines) is redone for `BT` (`mem_canonFinset_iff_bottom`, `Reach.region_unique` for `st_ext`, `opBT = ⟨opOut .., ChainAt.nextA ..⟩`).  The window (`win_of_domF` analogue) uses `chain_slow` (4d-B2) for `qb, qr ∈ c0.U`.  `Lvl.termsB` is `Lvl.terms` with the `psiBot` branch replaced by the map of the bottom summands; the unrolled identity is `psiFuel_eq_terms_ext` with the new branch.
## Checks run (exact)
* every module: single build `uni/build5c6.sh` exit 0 (logs/buildS5C6-VineEstS5C.P4.Bot.<M>.log), warnings only: deprecated `if_pos/if_neg/Set.mem_setOf_eq` (copied from the originals), unused section variables.
* FRESH rebuild `uni/fresh5c6.sh` -> `uni/buildS5C6f`, 11 modules in topological order, all 11 `exit 0` (uni/logs/fresh-bot.out: Idx Surj Mix Dict Decomp Win Exp Terms Family Count Unroll).
* `#print axioms` (transient AxProbe, deleted): bundle_decomp_bot, bundle_decomp_bot_mirror, botSurj_of_state, botLayers_of_state, psiBot_eq_sum_terms, bundleBotFamOf, winOfExtBot_bundleBotFamOf, card_bundleBotExpOf, Lvl.psiFuel_eq_termsB_ext, Lvl.card_termsB_le_prod, Lvl.termsB_induction, unrolled_boundR_extB_prod, bot_hreal, bot_remQ_eq, hq2_of_bot: all [propext, Classical.choice, Quot.sound].
* integrated `example` (transient, compiled): `Lvl.psiFuel_eq_termsB_ext .. (bundleFamOf .. hR SFF) (bundleBotFamOf .. hprime hR SFFB) (winOfExt_bundleFamOf ..) (winOfExtBot_bundleBotFamOf ..)` has the expected type.
* hygiene `grep -nE "sorry|admit|axiom|opaque|unsafe|maxHeartbeats"` over Bot/*.lean: no hits; `set_option` only `linter.unusedSectionVars false` (as P4/*.lean), no heartbeat/depth option.
## Named inputs
`P1.RealityAll` (PL234 `reality_all`), `BotSepFamFam` (W1: separated expansions of `botQfam`, `botTfam`), `hprime : IsPrimeGarden G`; no `ZpSurj`/`ZpLayers`/`hq2` input (discharged from `hop.some`, R51 deviation inherited: `hcan hel htc hcc` are fields of the operation).
## Uncertainties / errata / deviations
* `bundle_decomp_bot` is stated for `botVars` windows only; the factor `bFac` and the time domain of `b` (`bTimeOK`) stay in the term as a multiplier, so W2's certificate for a bottom term must account for `bFac` (spartFrame's domain, `bFac`'s two boundary-child time conditions).
* The case `e pstar = 0` with a non-bottom-sized chain (other operative members) is excluded by `hmax` + `hup_of_max` (as in `Lvl.classSum_flat`).
* No erratum in the sources.  Deviation: new `BotExpFam` is indexed by `(h0, hop, hmax)`; `Lvl.termsB` takes both `BE` and `BX`.
READY bot-decomp

# HANDOFF vineest-W2 session 2 ADDENDUM (Opus, after R60) -- CHECKPOINT vineest-W2 (read first; then the session-1 section below)
## New files: uni/src/VineEstS5C/P4/W2/Glue.lean (151 l.: `RowForm`, `rowForm_psiNat`, `rA_glue`, `rA_eq_glue`, `rB_glue`, `rowForm_step`), GlueLvl.lean (127 l.: `rowForm_idx`, `FrameShape`, `rowForm_terms`, `frameShape_bundleFamOf`).  Exact statements: PROGRESS "P4-W2 EXPORT", "N1 DONE".
## Approach: N1 (the glue identity) by `Lvl.terms_induction`: the row form `RowForm` (ε_U · 1_{Dm} · phase_U · ∏ pair weights · ∏ branch weights at every local decoration and EVERY clock) holds for the native summand (definitional) and is preserved by the split step: `splitLocalEquiv` writes every local decoration of S ∪ T as a glued pair, and `eps_split`/`phase_split`/`eps_S_glue`/`eps_T_glue`/`phase_S_glue`/`phase_T_glue`/`split_pairs`/`split_interior` (VineEstS4) do the rest; the exceptional factor of the bundle summand is carried whole at the exceptional pair (split into K/L rows in N2).  The psiBot-ending terms enter through the named input `hbot` (BOT-DECOMP, R60).
## Checks (exact): single builds of Glue, GlueLvl exit 0; FRESH rebuild `uni/fresh5c4b.sh` of all 6 W2 modules into a new farm buildS5C4bf: all exit 0 (logs/fresh-w2.out); `#print axioms` (transient probe, deleted) of rowForm_psiNat, rowForm_step, rowForm_idx, rowForm_terms, frameShape_bundleFamOf: [propext, Classical.choice, Quot.sound]; hygiene grep over P4/W2: no hits.
## Deviations/uncertainties: `hbot` is a named input (owner BOT-DECOMP), not a premise of any final statement yet.  No new errata.
## Next: N2 (FreeDict from RowForm), N3 (rows), N4 (AmbW), N5 (uniform β′): exact plan in PROGRESS "P4-W2 EXPORT" NEXT.

# HANDOFF vineest-W2 (V5 P4 W2, session 1, Opus) -- CHECKPOINT vineest-W2 (read first; exact statements in PROGRESS.md "P4-W2 EXPORT" and "R58 (F-LOWCLOCK) MODULATED STATEMENTS")
## Files (all `module`, no sorry; namespace `WaveTurbulence.VineEstS5C.P4.W2`, except ModStatement: `WaveTurbulence.VineEstS5C`)
uni/src/VineEstS5C/P4/W2/ModStatement.lean (182 l.: `VineEstCanonLayerC2M`, `VineEstCanonLayerHalfM` on V5-CONT's `Cont.twistedRecenteredModC`, `vineEstCanonLayerC2_of_M`, `vineEstCanonLayerHalf_of_M`, `vineEstCanonLayerHalfM_of_C2M`, `regionAbsM`, `memberAbs`), Free.lean (291 l.: `FreeDict`, `lkRaw_reindex`, `integral_free(_aux)`, `termFnR_eq_expr3_free`, `lkAbs_of_exprAbs_free`, `recBound_free`, `allRows_abs`, `AmbW`, `AmbW.pre`, `AmbW.bound`, `TermCertW`, `termBoundW`, `habsW`), Rows.lean (86 l.: `sepRowW`, `jointRowW`, `remRowW`), Terms.lean (102 l.: `Lvl.mem_terms_zero`, `Lvl.mem_terms_succ`, `Lvl.terms_induction`).  Scripts: uni/build5c4b.sh (BD overridable), uni/farm5c4b.sh, uni/fresh5c4b.sh.  No existing module edited; no other packet's file edited.
## Approach
R58/S2 requests first: VINEEST(λ) stated on V5-CONT's `twistedRecenteredModC` (wt-orch: no second definition; my earlier `twistedRecenteredM` was removed before any consumer), λ = 0 recovers the R54 statements, (ii) from (i) as in R54; the per-member interior absolute summability is `tsum_integral_norm_clLocalSummand_le` (VineEstS5C.AbsBase) with |lowModC| = 1.  Per-term certificates: a free-domain dictionary `FreeDict` (design point W2-D1: P2's dictionary assumes the native clock domain, false for the twin-ordered pieces), the multi-vine certificate `TermCertW` with one `RowData` per row (`allRows_bound`, W2-D3), and its two consequences `termBoundW`, `habsW` in exactly the form of `top_boundR`'s `TermBoundR`/`habs`; row-by-row exports of P2's piece rows; the case analysis of `Lvl.terms` for the induction of the glue identity.
## Checks run (exact)
* single builds `uni/build5c4b.sh VineEstS5C.P4.W2.{ModStatement,Free,Rows,Terms}`: exit 0 (logs/buildS5C4b-*.log).
* FRESH rebuild `uni/fresh5c4b.sh` (new farm uni/buildS5C4bf, topological order): ModStatement 0, Free 0, Rows 0, Terms 0 (logs/fresh-w2.out).
* transient probe (deleted) against buildS5C4bf: exact-type `example`s `VineEstCanonLayerC2M P → VineEstCanonLayerC2 P`, `VineEstCanonLayerHalfM P → VineEstCanonLayerHalf P`, `WTPrefix VineEstCanonLayerC2M → WTPrefix VineEstCanonLayerHalfM` compile; `#print axioms` of vineEstCanonLayerC2_of_M, vineEstCanonLayerHalf_of_M, vineEstCanonLayerHalfM_of_C2M, regionAbsM, memberAbs, termFnR_eq_expr3_free, lkAbs_of_exprAbs_free, recBound_free, allRows_abs, AmbW.bound, termBoundW, habsW, sepRowW, jointRowW, remRowW, Lvl.mem_terms_succ, Lvl.terms_induction: all [propext, Classical.choice, Quot.sound].
* hygiene grep (sorry|admit|axiom |opaque|unsafe|maxHeartbeats|set_option) over P4/W2/*.lean: no hits.
* NOT done: the construction of `TermCertW` for the unrolled terms (W2 (b)-(d)); no target statement exists for it yet.
## Source readings
TARGET L1595-L1618 (Prop sumint: 𝒟 has "(iii) any fixed collection of inequalities v < w" (L1612); parameters λ_jⁱ with loss max⟨λ⟩^{η⁶} in (FourierboundI)); L1850-L1935 (Step 4: (replaceterm1) has 1_{t₀<t₁} for II-a and 1_{t₀<s₁} for II-b; pieces (a) 1_{t₁<t₀<s₁}/1_{s₁<t₀<t₁}); R58 (F-LOWCLOCK), S2 INTERFACE v2 (represents/PLAN-VINE.md L98ff).
## Decisions / deviations
W2-D1 free-domain dictionary; W2-D3 one RowData per row (K row at the pair's sumint row, L row at the branch's); W2-D4 λ ∈ ℝ, loss (1+|λ|)^{6η⁶}, kind = true (R57 pass later); VINEEST(λ) on `twistedRecenteredModC`.
## Findings for wt-orch (details in PROGRESS "P4-W2 EXPORT")
F-W2-BOT: `Lvl.terms` keeps `psiBot` (operative member of piece index 0) unexpanded, so terms ending in psiBot have no certificate with the bottom vine's gain; needs a bottom decomposition packet (bottom analogues of `bundle_decomp`, `ZpSurj`, `BundleExp`) and an expanded term multiset (W3 count: the bottom member's bundle size).  F-W2-FLAT: the flattening `Lvl.classSum_eq_flat` must be redone with the multiplier e^{πiλ u_b} for `twistedRecenteredModC` (W4 needs it).  QUARANTINE: 9 files written into P4/W2 by the reverted codex takeover moved to uni/quarantine-codex-W2/ (with SHA256SUMS), unused.
## Uncertainties
`FreeDict`'s engine datum is `engDatum hM9 B' hG W ..` (P2's `modPiece (pieceDatum (sourceSumintDatum ..))`): the modulation and the operative vines' constraints must be expressible through `W.param`, `cons`, `bk`, `g`, `g'` (believed yes: `cons` is arbitrary); the TVar ↔ (u₂,u₃,u₄) identification of an operative vine's block is not yet located in the code.
## Errata
None new in TARGET.  (W2-D1 and F-W2-BOT are Lean-interface gaps, not source errors.)

# HANDOFF vineest-C P4 (session 3, Opus) -- CHECKPOINT vineest-C (read first; details in PROGRESS.md "VINEEST FINAL (R54)" and "P4 STATUS (session 3, Opus)")

## Named inputs of the eventual final theorem `WTPrefix VineEstCanonLayerC2` (owners)
* `SumintMixSignedDoubled` (sumint / B1.6, DEGEN-VINE) -- engine.
* the leafwise gates `LeafwiseCoherentApproximationGate`, `LeafwiseIncoherentDecayGate` (lg-spine-u / PL23-30D).
* PL234 `reality_all`, as `RealityAll` (exact type, P1 `probe5c1/RealityCheck.lean`) (PL234).
* VINEPARAM `hM9` is a binder of the statement itself (VINEPARAM-U).
* NO others: `ZpSurj`, `ZpLayers`, `hq2` are DISCHARGED (P4/Family, ZP-SURJ exports, from the `FamilyOperation` fields of the operative member); the code counts are proved in-world (`coupleCodeCount_le_pow`, `chainCodeCount_le_pow`, universe), not the sorry'd snapshot `regular_count_le`.

## Files added this session (uni/src/VineEstS5C/P4/, all `module`, no sorry, build `uni/build5c4.sh VineEstS5C.P4.<M>`, LEAN_PATH now includes <scratch>/zp-surj/build-fresh read-only)
UnrollR (design R), WinChain (top level + null boundary), Family (bundleFamOf, ZpSurj/ZpLayers/hq2 discharged), Statement (R54 statements + (ii) from (i)),
CohCount, CohCountTree, ZpCount, ChCount (count bridge), AllRows (engine bound with every row given; W2(a)).  2,700 lines.  Exact names: PROGRESS.md.

## Checks run (this session)
* every module above: single build exit 0 (logs/buildS5C4-VineEstS5C.P4.<M>.log).
* `#print axioms` (transient probe P4/AxS3.lean, deleted): unrolled_boundR_ext, top_boundR_prod, winOfExt_bundleFamOf, vineEstCanonLayerHalf_of_C2,
  ncard_coherentCouples_le, ncard_coherentTrees_le, card_zpFinset_le, card_terms_le_wt: all [propext, Classical.choice, Quot.sound].
* hygiene grep (sorry|admit|axiom |opaque|unsafe|maxHeartbeats) over the 8 new files: no hits.
* NOT yet run: fresh rebuild of the S5C closure, exact-type example of the final statement (the final theorem does not exist yet).

## Findings / decisions
* **F-COUNTGAIN** (ruled R54): the class count of an operative vine is <= 16 (N+1) (4*12^9)^N 4^p (`card_zpFinset_le`; the 4^p is TARGET's
  C_0^{|q-q'|} of layerreg2 for couple and tree, |q-q'| <= p <= D = tau*/delta).  TARGET L1919-L1922 covers C2 by "the L^{-eta^2} gain for this
  bad vine", but (vineest2) L1748 keeps L^{-eta^2 b}, and the engine (sumintRHS) gives exactly L^{-eta^2(b+M1)-eta^8 M0+eta^7}: no slack in general.
  ERRATUM CANDIDATE (TARGET L1748 vs L1919-L1922): (vineest2) should carry C2^b or L^{-eta^2 b/2}.  R54: prove `VineEstCanonLayerC2` (factor
  `P.C₂ ^ b`) and `VineEstCanonLayerHalf` (exponent -(eta^2/2) b); the latter follows from the former in prefix form (DONE:
  `vineEstCanonLayerHalf_of_C2`).
* **Design R (F-WINCHAIN)**: P3's `Lvl.terms` never reads `Win`, so no new structure was needed (no duplicate declarations); the unrolled identity
  holds under the exterior window of the top level only (`Lvl.psiFuel_eq_terms_ext`).
* **Deviation**: count weights `wtOf p i = 192 (N_i+1) (16*12^9)^{N_i} 4^p` depend on p; the 4^p per operative vine goes to C2^b (R54), the rest
  must be absorbed by C1 through the exceptional rows (W3 below).
* **R57 (kind)**: my new statements use `canonFinset` / `Lvl.Op` (FamilyOperation kind := true) / ZP-SURJ (`CanonicalObject p true`), so `kind` is NOT a
  free parameter there; the count bridge (CohCount, CohCountTree: `IsCoherentCoupleAt/TreeAt`, `IsCanonGC` ambient) and Statement's arithmetic are
  kind-agnostic.  Garden-only facts used: none directly in P4 (they enter through VineEstS4 `canonFinset`, `Lvl`, ZP-SURJ `zpSurj_of_state`).

## Remaining work (exact; each is a multi-module job)
* **W1 SFF** (`SepFamFam` + `SepFamFam.Bounded`, and the P2 `SepT` bounds the pieces need): per operative level, separated expansions of
  `zpQfam b`, `zpTfam b` (P1: `mixFam` = constant extension `extFam` of the ROOT-LAYER instance `SourceApp(Lr, L2)`; R35 `F 1_{t>Lr}` for
  trivial b) at (s1,t0) and (t1,t0), t0 in [L2,L2+1], t1 in (L4,L4+1] (case A; s1 in case M), the other clock in the window of a layer >= L4.
  Index sets (BundleState): `bsB` = all II-b states; `bsA` = II-b states with roots <= L4 (twin pairs, indexed by the II-b member) and II-a
  states with a root > L4.  Plan:
  (i) II-b b with roots <= L4: `ZpSurj.carrier` (MapsTo) gives `CoherentPairCarrier p L4 L2 ..` for (zpCodeC, zpCodeT, zpObjC, zpObjT), so
      P2's `couple_gate_data`/`tree_gate_data` apply AT (L4, L2) (box timeBox L4 L2 / timeBoxGt L4 L2, m <= 2^n, c = δ^n); P1
      `couple_eq_ext`/`tree_eq_ext` (q = L4 >= Lr) identify `SourceApp(L4,L2)` on [L4,L4+1] with the extension used by `zpQfam`; for the
      clock in a window of layer > L4 the extension is constant = value at L4+1: the separated terms are J_i(L4+1, ·) (order-0 trace,
      `XNorm00Restr_trace`, constant traceR η; TARGET L1917: X^{1-η} -> X^{1-2η}).
  (ii) b with a root > L4: the object with Lr > L4 >= L2 vanishes at every t <= Lr (P1 `couple_root_vanish`/`tree_root_vanish`, type 2 with a
      nonempty chain), so its expansion at t1 (and at s1 when its window is <= Lr) is the EMPTY sum (m = 0); the other object uses P2
      `zp_couple_gate`/`zp_tree_gate` at its native box; check every piece of `zpPieces`/`zpPiecesM` for evaluations outside these windows.
  (iii) `PtOK`/`dom`: from `window_caseA/M` (DomF windows); `Bounded`: m <= 2^n <= 2^zpN.  Hypothesis `q <= p` of `zp_tree_gate`: from the
      operation fields (`q2_le_p` of ZP-SURJ Num1, as used in P4/ZpCount).
* **W2 term certificates** (P2's "OPEN FOR P4"): for each ψ in `Lvl.terms (card ι + 1) (Lvl.top B)` a certificate: (a) DONE as
  `P4.allRows_bound` (all rows at once; the operative vines' rows are the `RowData` built inside P2's `piece_*`/`level_*` lemmas -- these must be
  exported as `RowData` + `Ae` rather than only through `PieceBound`, and P2's `TermCert` (one `PieceBound`) generalized to `allRows_bound`);
  the datum: fold `modPiece` + `badClauseP_modPiece` over the operative vines; (b) the glue identity ψ = clLocalSummandGen R Φ_ψ with
  Φ_ψ = native qRow/tRow (VineEstS5B/Frame `spartFrame`) except the exceptional rows of operative vines (piece weights), and `RowFactorizationR`
  for it, by induction over the levels (LevelFlat `psiStepSp`, `glueFactors_psiStepSp`); (c) `DictAll`/`DictHyp` per term (ε-mix, a.e. engine
  integrand identity incl. `kind2_cancel`, indicator constraints, R35 trivial b a.e.); (d) one β' for all terms (exceptional orders are constant
  on the class).
* **W3 WP-F**: (cc+1)·∏ wtOf·‖cζ‖·β' <= RHS·C2^b: the C^{N_i} part of wtOf into the C1-powers of the exceptional rows (N_i <= their row
  sizes; `order2_eq`), 4^{p·#members} <= C2^b (C2 := max(C2_inputs, 4^D); needs #operative members <= b: core vines are bad), traceR/ccη/
  finalCstar/trace_absorb as in `step3Layer_of_at`.
* **W4 prefix**: `WTPrefix VineEstCanonLayerC2` by the `vineestStep3Layer` pattern; no-twist case = `layerBound_noTwist` (BaseLayer), twisted
  case = `top_boundR_prod` + W1-W3; then `vineEstCanonLayerHalf_of_C2` (done) and the common-profile corollaries.
* **Final checks**: fresh rebuild of S5C + P1-P4 + zp-surj read-only, axioms, hygiene, exact-type example, this section updated.

CHECKPOINT vineest-C: next step = W1 (SFF construction), then W2(a) (multi-vine PieceBound fold).

# HANDOFF P2 (vineest-P2, SESSION 3, READY vineest-P2) -- files: uni/src/VineEstS5C/P2/*.lean (36 modules, 3823 lines)
Files added this session: KCont, PieceBound, PieceSS, PieceJoint, PieceRem, GateData, Gate1, ConjNeg, MirrorBound, Recentered, GenSumintR, Dict, Dict2, Dict3, Dict4, Final, TermBound; LevelSS/JS/R edited only to also return `K.Ae hI ∧ L.Ae hI`.  Names, exact statements and the list of what P4 must still supply: PROGRESS.md "P2 EXPORT (session 3)".
Approach: uniform `PieceBound` output per piece type from the earlier `level_*` theorems with constants independent of D (`AmbP` Prop split); gate data via `CoherentGateH`; mirrored pieces by `SepT.conj/RemT.conj` + `PieceBound.neg`; dictionary = r-dependent copy of V4's generic endpoint (compiled unchanged) + eps-mix/time-domain bridge + ExprAbs => LkAbs via measure-preserving clock equivalence.
Checks: fresh rebuild buildS5C2g (build5c2g.sh) of all 36 modules in topological order, every exit 0 (logs/fresh-p2s3.out); `#print axioms` of 21 key results = [propext, Classical.choice, Quot.sound] (probe5c2/Ax3.lean); hygiene grep (sorry|admit|axiom|opaque|unsafe|maxHeartbeats|set_option) over P2: no hits.  No exact-type `example` against a pinned target (none exists).
Findings/deviations: F-RECENTER (P3 termFn non-recentered vs engine recentered: bound proved for the recentered observable; P3 files untouched, `unrolled_bound_recentered` is the P2 replacement); the old `RowFactorization` lacks r (KQ/KT rows need it): `RowFactorizationR`; strict-inequality slack (`SepT.hJ` strict, `CJ = 2 C1^(n+1)`).  Uncertainties: `TermData`/`DictAll` hypotheses are the interface P4 must discharge for the product term (not derivable in P2: BundleExp is P4's); `zp_tree_gate` needs `q <= p` as input.  Errata: none found.
READY vineest-P2

# HANDOFF P2 (vineest-P2, SESSION 2, CHECKPOINT) -- files uni/src/VineEstS5C/P2/*.lean (19 modules, 2014 lines, namespace WaveTurbulence.VineEstS5C.P2; Abs in VineEstS3Par.Eng)
Files added this session: Pieces, Mono, FSAe, RemAe, RemCont, Abs, LevelAbs, LevelR, Datum (names and statements: PROGRESS.md "P2 SESSION 2 UPDATE").  Approach: row-level engine pieces (a.e. remainder rows, because `K* - app` is not continuous at t = Lr for trivial objects, R35), pointwise identities of the pieces, finite Minkowski and Fubini over the (b,i,j) sum, the concrete datum (`StructAdm`, `BadClauseP`).  Checks run: single builds of every module exit 0; fresh rebuild buildS5C2f of all 19 exit 0 (logs/fresh-p2s2.out); `#print axioms` (probe5c2/Ax.lean) standard only; hygiene grep clean.  Uncertainties: the combined export `vineLevel_piece_bounds` (step 7) and the instantiation of the datum with `sourceSumintDatum` are NOT done (exact next steps in PROGRESS.md); continuity of K* in time is delegated to `continuous_KQstar_time` (plain garden + coset summability still to be supplied).  Deviations: none from sources; no P1/P3 or existing module edited; P3's `unrolled_bound` (concurrent) expects `TermBound` per term: P2 supplies the clocked-expression bounds (`vineLevel_sum_bound`) and `ExprAbs` (`vineLevel_abs`); the `LkAbs <-> ExprAbs` and `termFn = clockedExprMul3` dictionaries are P3/P4's.  Errata: none found.

# HANDOFF P3 (vineest-P3: unrolling psiFuel over the levels) -- READY vineest-P3
Files (uni/src/VineEstS5C/P3/, namespace `WaveTurbulence.VineEstS5C.P3`, 444 lines; build `uni/build5c3.sh VineEstS5C.P3.<M>` -> uni/buildS5C3 (symlink farm `uni/farm5c3.sh` over buildS5C2, buildS5C1, buildS5C); fresh `uni/build5c3f.sh` -> `uni/buildS5C3f` (farm5c3f.sh), all four exit 0): `Linear` (XNorm00Restr_finsum_le, LkAbs, lkRaw_finsum), `Unroll` (BundleExp, BundleExpFam, Lvl.terms, Lvl.winOf, Lvl.psiFuel_eq_terms), `Count` (Lvl.card_terms_le), `Bound` (Lvl.cst, termFn, clsFn, clsFn_eq_sum_terms, unrolled_bound, unrolled_bound_pow, unrolled_bound_gain).
Approach: the nested `Lvl.psiFuel` is expanded as a Multiset of product terms (`Lvl.terms`, same dite recursion; operative step = bind over the finite bundle summands `Ch` times the terms of `Lvl.next`, with the exact shape of `psiStepSp`; base/inert/bottom = one term). The bundle expansion is an INPUT structure `BundleExp` (finite `Ch`, `term`, window `Win`, `eq : Win x u -> psiSB .. x u = sum_c term c x u`), to be built from `P1.bundle_decomp` (Ch = pieces (a)-(c) indexed by b,i,j plus remainder rows; Win = the time window h0,h0',h1,h1' of bundle_decomp at bundleVars). Not built here: P2's `vineLevel_piece_bounds` did not exist (PROGRESS "P2 EXPORT" unchanged), and the piece indexing needs P1's ReplaceAlgebra pieces.
Exact statements for P4 (all [propext, Classical.choice, Quot.sound]):
* `Lvl.psiFuel_eq_terms BE m lv x t u : winOf BE m lv x t u -> psiFuel .. m lv x t u = ((terms BE m lv).map fun psi => psi x t u).sum`.
* `Lvl.card_terms_le BE N (hN : 1 <= N) (hCh : forall lv pstar hk, Fintype.card (BE lv pstar hk).Ch <= N) : forall m lv, card lv.iota <= m -> card (terms BE m lv) <= N ^ card lv.iota`.
* `termFn B kappa0 lv psi s tt E = Lvl.cst B kappa0 lv * lkRaw lv.region kappa0.L kappa0.base psi tt (sumintBoundary s E)`; `clsFn B RD hG layer hLayer kappa0 lv s tt E = lv.classSum .. (tt 0) (tt 1) (tt 2) (sumintBoundary s E 0..3)`.
* `unrolled_bound` (hL, hF as in `Lvl.classSum_eq_flat`; theta >= 0, `Bx ⊆ cell q`, `K.Countable`; `hWin`: for tt in Bx, E in K, every decoration kappa, a.e. clock tau lies in `winOf BE (card lv.iota + 1) lv`; `habs`: every unrolled term satisfies `LkAbs` (integrable per decoration, summable integrals); `TermBound : forall psi in terms .., XNorm00Restr theta Bx K (termFn B kappa0 lv psi s) <= beta`) : `XNorm00Restr theta Bx K (clsFn .. lv s) <= (cutoffMultiplierConstant theta (cutQ q) + 1) * (card terms * beta)`.
* `unrolled_bound_pow`: same with `((N ^ card lv.iota : N) : ENNReal) * beta` (hN, hCh as above). `unrolled_bound_gain`: term bound `ofReal (Cterm * Lg ^ nbad)` gives `(cc+1) * ofReal (N ^ card lv.iota * (Cterm * Lg ^ nbad))` (Lg = L^(-eta^2), nbad = #bad vines, the same for every term; (N Lg)^... absorbing is real arithmetic for P4).
Top level use: `lv := Lvl.top B`, `Lvl.classSum` = canonFinset sum (`Lvl.top_classSum`); outBox ⊆ cell via `outBox_subset_cell`, `countable_outSet`.
Named inputs / uncertainties: (1) `BundleExp` family (P4/P1 construction); (2) `hWin` (R35: the bundle window holds a.e. on the vine time domain); (3) `habs` (absolute convergence of each unrolled term's local sum-integral; not exported by the engine, P2 note); (4) `TermBound` is the abstract engine bound per term and includes the constant c*zeta (peel with XNorm00Restr_const_mul_le); each term already carries its own (ccEta+1) from the engine, so the final constant is (cc+1)(ccEta+1) (cc = cc_theta of cutQ q, = ccEta by cc_translate when theta = 2 eta^8). Not done: instantiating TermBound from P2 (not available), the 4^b ∏|Bs_i| count from the concrete piece types (only the abstract N^#members).
Errata/deviations: none in sources. No existing module edited.
READY vineest-P3
# HANDOFF P2 (vineest-P2, PARTIAL -- CHECKPOINT)
Files: uni/src/VineEstS5C/P2/{Merge,Level,Cph,Admiss,TimeModes,Rows,ConjNorm,Space,LevelSS,LevelJS}.lean (971 lines).  Approach and statements: PROGRESS.md "P2 EXPORT".  Checks run: single builds of each (exit 0), fresh rebuild buildS5C2f of all 10 in order (exit 0), `#print axioms` of level_SS, level_JS, remRow_exists, snorm_prodDiff_le, hAdm_of_struct, hCph_of_q, XNorm00Restr_conj = [propext, Classical.choice, Quot.sound], hygiene grep clean.  Deviations: (iv) of the brief (coefBound_finsetSum_le over Bs) not used, since (Q,T) couples K and L rows; the sum over (b,i,j) is an outer triangle inequality.  Uncertainties: remainder continuity; wN lowering; no exact-type example (no pinned target statement).  Errata: none found.

# HANDOFF vineest-P1 (V5 Step 4d part C, sub-packet P1, session 7) -- READY vineest-P1
## Files (uni/src/VineEstS5C/P1/, all `module`, 660 lines total, each < 250): Ext (extension lemma), Mix (RealityAll, zpQfam/zpTfam, ZpLayers, hsub), Mix2 (hQ0, hT0, hreal), Decomp (**bundle_decomp**), Rem (gate-remainder identities for P2).  No existing module edited; no file copied.
## Approach
* TARGET (i) (L1893-L1925): the root-layer instance `SourceApp.couple … (Lr) q'` extended by constants equals `SourceApp.couple … q q'` on [q, q+1] for q >= Lr.  Proved directly on the `SourceApp` definitions: triv/type1 (all nodes in layer q', so Lr = q', both sides `Q.app δ q' (F q') (q'+1) s k`); type 2 (`q' <= Lr`, `chainSlice r Xp = nil` for r > Lr by `SpineMono`, `RegChain.app_nil' = 1`, product `Ioo q' q = Ioo q' Lr * (r = Lr)`; case Lr = q' via `TopAll`/`chainSlice_of_topAll`, closeCouple = type2 by wf); trees identical.  TARGET sources: L1893-L1925 (the extension paragraph), L899 (layerreg1).
* Qf := mixFam (R35 option 2).  `Q0` at the SECOND parent layer L2 = zpQ2 (not the native (zpQQ).2) so that on the carrier (coherent at (L4, L2) by `ZpSurj.carrier`) the extension is `SourceApp.couple … L4 L2` and PL234 `reality_all` applies verbatim; `carrier_sum_eq` turns the carrier finsum into the sum over `zpMinusFin`, which `zp_filter_eq` identifies with the filter of `replSum_decomp_ext`.
* Because of L2 <= L4 (`ZpLayers.le`), a couple/tree with root layer > L4 has Lr > q' and is therefore type 2 with a nonempty chain: the endpoint vanishing hQ0/hT0 is `couple_type2_lt_zero`/`tree_lt_zero` (SrcVanish), no trivial/type-1 case occurs for roots > L4.  So R35's trivial-case repair (Ex = F 1_{t>q}) is built in (`zpEx`) but is not needed for hQ0.
* `replSum_decomp_ext` (VineEstS4c) applied unchanged with eQ = eT = 0, Bs1 = bsA, Bs2 = bsB, Dq b s := b ∈ zpFinset /\ L4 < Lq b; `bundle_eq_repl` supplies the exact-rows expansion; the classical union instance is pinned by `zpBsU`.
## Checks (exact)
* Fresh rebuild: `uni/build5c1f.sh` (new dir buildS5C1f, farm over buildS5C/B2/B/A) Ext, Mix, Mix2, Decomp, Rem: all `exit 0`, 0 warnings (logs/fresh-p1.out).
* `#print axioms` (probe5c1/Ax.lean via probe5c1.sh): couple_eq_ext, tree_eq_ext, couple_root_vanish, tree_root_vanish, zp_hsub, zp_hQ0, zp_hT0, zp_hreal, bundle_decomp, zp_remQ_eq, zp_remT_eq: all [propext, Classical.choice, Quot.sound].
* Hygiene `grep -nE "sorry|admit|axiom|opaque|unsafe|maxHeartbeats|set_option"` over P1/*.lean: no hits.
* Exact-type check of the named input: probe5c1/RealityCheck.lean (compiled in pl234's world: `example : RealityAll := @WaveTurbulence.PL234.reality_all`) succeeds.
## Named inputs of bundle_decomp
`hZ : ZpSurj` (owner ZP-SURJ, R51), `hR : RealityAll` (owner PL234, R46), **`hL : ZpLayers` (NEW; layer numerals of TARGET L1900-L1910, see PROGRESS.md P1 EXPORT; owner: ZP-SURJ or the layering of the molecule; this is a typing identity, not a conclusion, but it is NOT proved)**.
## Uncertainties
* Whether `(zpQQ G).2 = zpQ2 A pstar` (second parent layer of the carrier-side couple is the layer of the lower joint u_2) holds in the Lean conventions of `zpPairQ` (orientation of first/second leaf of the retained pair) was not checked against the state geometry; if it fails for II-a states the fix is to take Q0 at (zpQQ b).2 for roots > L4 (then `couple_root_vanish` needs `Lr > (zpQQ).2` instead of `> L2`).
* The time window t1 in (L4, L4+1] is open at L4 (R35); `bundle_decomp` is an identity at such points, so the consumer integrates over the a.e. window.
## Errata / deviations
* TARGET L1913 (ii) (R35) already ruled; additionally observed: L1893-L1925 (i) is TRUE exactly as stated for q' <= q (no counterexample for any type); the case q < q' is not covered (not needed: gate/reality_all are q' <= q).
* Deviation: `Ex` is `F 1_{t>Lq}` realised as the indicator times the extension (equal to `F 1_{t>Lq}` for a trivial object), not the exact kernel `KQstar`; no computation of `KQstar (triv)` was done.
READY vineest-P1

# HANDOFF vineest-C session 6 ADDENDUM (read first)  --  CHECKPOINT vineest-C (not READY)
Done this session (R51; all `uni/build5c.sh VineEstS5C.<M>` exit 0, no sorry, axioms [propext, Classical.choice, Quot.sound], hygiene clean):
* `ZpSurjStmt` (145 lines): **`structure ZpSurj p pstar J A sp0 hA : Prop`** = the exact statement for packet ZP-SURJ (R51): fields `coherent`, `twin`, `carrier` (see PROGRESS.md top).  `<scratch>/zp-surj` did not exist at session start; ZP-SURJ should target `VineEstS5C.ZpSurj` verbatim (conjLayered-involution-free formulation).  Open question for ZP-SURJ: whether `coherent` (carrier-side objects coherent at (zpQQ, zpBranchQ) for every Zp state, including roots > L4) and the root-layer-lowering implicit in `twin`/`carrier` (II-a: Q at (L3,L2), T at (L4,L2); II-b: Q at (L4,L2), T at (L3,L2); carrier at (L4,L2)) hold; if not, ZP-SURJ STOPs with the mismatch (R51 option C).
* WP-B steps 1-3: `BundleAlg` (`psiSB_eq_dict`), `BundleAbs` (`exact_eq_repl_add_rem`), `BundleState` (**`bundle_eq_repl`**: the exact bundle in pairing form with remainder rows, for ANY approximant families; no approximant-conjugation theorem), `CarrierSum` (**`carrier_sum_eq`**: reality_all's carrier finsum = finite sum over states).
* NOT done: R35 case facts and `replSum_decomp_ext` application (see PROGRESS.md "R35 FINDINGS" and "REMAINING FOR WP-B"), remainder-row bounds, engine datum for the vine rows, unrolling over levels, WP-F, prefix theorem and `VineEstCanon` corollary, fresh rebuild, exact-type example.
* Named inputs so far (unchanged + new): `SumintMixSignedDoubled` (owner: sumint/B1), the leafwise gates `LeafwiseCoherentApproximationGate`, `LeafwiseIncoherentDecayGate` (owners: lg-spine-u / PL23-30D), `hreal` = type of PL234 `reality_all` (owner PL234), VINEPARAM `hM9` (owner VINEPARAM-U), and now **`hZpSurj : ZpSurj ..` (owner ZP-SURJ; must be discharged, not kept)**.
* Suggested split of the remaining work into parallel sub-packets: (P1) R35 facts + `replSum_decomp_ext` application + `hreal` (needs `SourceApp(q>=Lr)` = root-layer extension, per RegCpl type); (P2) remainder rows and the single-level engine datum for the pieces (a)-(d) (3-clock rows via `jointRow_modes`/`rowModes3_of_restr`, `Cph` via `kind2Factor_le_pow`, 29d weights per R30); (P3) unrolling `psiFuel` into a sum over piece-type choices + triangle inequality; (P4) WP-F constants, prefix theorem, `VineEstCanon` corollary, final checks.

# HANDOFF vineest-C session 5 ADDENDUM (read first)
Done this session (all `uni/build5c.sh VineEstS5C.<M>` exit 0, no sorry, axioms [propext, Classical.choice, Quot.sound] via uni/probe5c/AxA.lean with `uni/probe5b2c.sh`; probes of non-`module` files must start with `module`):
* `sbm`: AbsSb5 (`measurable_spartFrame`, `measurable_rowVal`, `measurable_rowQ_comp/rowT_comp`, `measurable_bundleKernel`, `measurable_psiSB`).
* 4d-B2 integration: LevelRecurse (imports VineEstS5B2.Bot19; `Lvl.bottom_hb0`, `Lvl.classSum_bottom`; `Lvl.psiFuel` bottom branch = `psiBot p kappa0 state lv.c pstar`; `hbot` DROPPED from `Lvl.classSum_flat`), LevelLoc2 (`psiFuel_congr` via `psiBot_congr`; `hbot_of_start` dropped), LevelAbs2 (`AbsLeaves` + fields `bot`, `botm`), BotAbs1..4 (`uAbs_psiBot`, `measT_psiBot`; the per-state pointwise identities `stBot_skip_eq/false_eq/true_eq` and the `UAbs` calculus incl. `uAbs_transport`), LevelAbs3 (`Lvl.absLeaves`, **`Lvl.classSum_eq_flat`**: unconditional flat identity, hypotheses only `hL`, `hF`, `hprime`).  `uni/build5c.sh` now has buildS5B2:buildS5B on its LEAN_PATH.  Rebuilt downstream: LevelAbs, AbsBase, AbsBase2, AbsSpart*, AbsSb1-4, LevelTop.
* Hygiene grep over the new/edited modules: clean; each new file < 190 lines.  No file outside uni/src/VineEstS5C edited.
NOT done: WP-B, WP-F, prefix theorem and corollary, fresh rebuild/final checks, exact-type example.  BLOCKER for WP-B: FINDING F-ZPSURJ in PROGRESS.md (state-level surjectivity/twin of the class onto the coherent carrier; needs a ruling or a new packet).  Named inputs so far: SumintMixSignedDoubled, LeafwiseCoherentApproximationGate, LeafwiseIncoherentDecayGate, hreal (type of PL234 `reality_all`; owner PL234), VINEPARAM hM9; plus the F-ZPSURJ decision.

# HANDOFF vineest-C session 4 ADDENDUM (read first): see PROGRESS.md top 'SESSION 4 UPDATE'.  New compiled modules beyond the list below: ExtSExt, AbsSpart, AbsSpart2, AbsSpart3, AbsSb1, AbsSb2, AbsSb3, AbsSb4 (sAbs_psiSB).  The WARNING about the form of `AbsLeaves.sb` below is obsolete (resolved by extS_ext_of_pairs).  Open: sbm, 4d-B2 integration (psiBot branch, UAbs/MeasT of psiBot), WP-B, WP-F, prefix theorem.

# HANDOFF vineest-4dB2 (V5 Step 4d part B2, Sonnet 5.5): the S-side twist identity at an operative BOTTOM vine (F-BOTTOM) -- READY vineest-4dB2

## Files (uni/src/VineEstS5B2/, 19 modules `Bot1`..`Bot19`, 1.7k lines, each < 180 lines; all `module`; build `uni/build5b2.sh VineEstS5B2.<M>` -> uni/buildS5B2, reading uni/buildS5B read-only; fresh rebuild `uni/fresh-5b2.sh` -> uni/buildS5B2f)
Bot1 `bFac`, `clLocalSummand_eq_spart_bFac`; Bot2 `chain_slow`, `chain_stw`; Bot3 `sign_naive_lowerChild`, `stw_positive_eq/negative_eq`; Bot4-6 `epsCoef_swap1/2`, `phaseAtom_neg`, `lower_labels`, `stw_bFac`; Bot5 `stw_label_pos/neg`, `stw_bTimeOK_iff`; Bot7-8 `stw_freeDec_iff`, `extCLEquiv`, `decEquiv`, `decEquiv_val`; Bot9 `summand_same`, `summand_tw`; Bot10 `BOKd`, `clLocalKernel_same`, `clLocalKernel_tw`; Bot11-14 `botKernel`, `stBot`, `BotGoal`, `botState_skip/false/true`; Bot15 `reach_single`; Bot16 `psiBot`, `botGoal_of_mem`, `tildeJ2_bundle_bottom`; Bot17 `psiBot_congr`; Bot18 `classSum_bottom`, `psiBot_static`; Bot19 `psiBot_BOKd`.  No file outside VineEstS5B2 was edited.

## Decision (the paper-and-Lean question of the brief): TARGET has NO gap, only the Lean framework did
For `p = 1` TARGET's `K̃^{U<p}(t_p,t',t'',e_p,f_p,g,h)` is the empty-chain factor: there is no lower block, and its only content is (a) the conservation at the bottom joint `u_2`, which ties `(e,f)` to the free-children momenta `(g,h)` (`k_{u2} - k_{u23} = ±(k_{u21}-k_{u22})`), and (b) the time conditions `t' < t_p`, `t'' < t_p` at the free children that are branches.  The twist exchanges `(e,f) <-> (f,e)` AND the positions of `u_21, u_22` (sign of `u_2` flips; the signs of `u_21`, `u_22` do not), so both are invariant (Lean: `stw_consAt_iff`, `stw_positive_eq/negative_eq`, `stw_bTimeOK_iff`).  Hence the role of `K̃` is played by the `b`-factor `bFac` (interaction coefficient `ε_b`, phase of `b`, the two time conditions: all of them twist invariant, `stw_bFac`; `ε_b` uses the conservation at `b`) together with the boundary constraint of `CLLocalDecoration R L base ![e,f,g,h]`; no extra lower factor is needed, and no ExtS/lower block appears: the whole region `R0 = clRegionData A.skeleton c0.block c0.cl` is treated at the level of its local decorations `CLLocalDecoration` (the twist is the bijection `decEquiv` of `CLLocalDecoration R0 .. ≃ CLLocalDecoration R0' ..`, `κ ↦ twistNodeLabels G P κ`, all four boundary momenta fixed) and of its times (`tEquivS`).

## EXACT STATEMENT part C should use to discharge `hbot0` (Bot18, exact-type `example` checked, probe5b2/Ax.lean)
```
theorem classSum_bottom (κ0 : KPar d) (A : FamilyReconstruction w ι) (c0 : ChainAt A.skeleton A.family)
    (hA : IsPrimeGarden A.skeleton) (hb0 : c0.b = (A.family.placement pstar).lower)
    (hup : ∀ j, j ≠ pstar → IsEmpty (FamilyOperation (p := p) (kind := true) A j)) (hL : κ0.L ≠ 0)
    (hF : ∀ k : ℕ, Summable fun n : Fin d → ℤ => |κ0.F k (κ0.base + latticePoint κ0.L n)|) (t0 t1 t2 : ℝ) (e f g h : Mom d) :
    ∑ z ∈ canonFinset p A c0, twistedLocalKernel z.1 z.2 κ0.L κ0.γ κ0.δ κ0.F κ0.base t0 t1 t2 e f g h =
      (coupling d κ0.L κ0.γ κ0.δ : ℂ) ^ clLocalOrder1 (botR A c0) * clLocalZeta (botR A c0) *
        ∑' κd : CLLocalDecoration (botR A c0) κ0.L κ0.base ![e, f, g, h], ∫ τ : CLInternalTime (botR A c0),
          psiBot p κ0 A c0 pstar (clExtendIndices (botR A c0) κd.1) ![t0, t1, t2] (clLocalClock (botR A c0) ![t0, t1, t2] τ)
```
(`botR A c0 = clRegionData A.skeleton c0.block c0.cl`, reducible.)  The right-hand side IS `c ζ * lkRaw (botR A c0) κ0.L κ0.base (psiBot p κ0 A c0 pstar) ![t0,t1,t2] ![e,f,g,h]` (S5C `lkRaw` unfolds to exactly this tsum-integral; `psiBot` has the S5C `PsiT` shape `x t u`).  `psiBot` depends only on `κ0.L γ δ F base` (`psiBot_static : psiBot p {κ0 with t0 := .., ..} = psiBot p κ0 := rfl`), as part C's design (i) requires.
`psiBot p κ A c0 pstar x t u = ∑_{z ∈ canonFinset p A c0} epsOf A pstar z.1 * botKernel κ A c0 pstar (decide (twAt A z.1 pstar)) (nuOf z.1 pstar) (rowQ κ z.1 pstar) (rowT κ z.1 pstar) x t u`, and `botKernel κ A c0 pstar tw ν rq rt x t u = spartFrame A.data .. c0.U c0.a c0.b p0 x u * (rowVal ν rq rt (u c0.b) p p' Lq M * bFac (botR A c0) κ.L κ.γ κ.δ κ.base x t u)` with `(p, p', Lq, M) = (u qb, u qr, base+lat(x retained), base+lat(x lower))` untwisted (`tw = false`) and `(u qr, u qb, base+lat(x lower), base+lat(x retained))` twisted (`tw = true`): the exceptional pair rows `rowQ`, `rowT` of the state with the twisted clock slots and labels exchanged, exactly as in `bundleKernel` (S5C) but with no lower factor.
Further facts for part C (all in VineEstS5B2, axioms [propext, Classical.choice, Quot.sound]):
* `psiBot_congr κ A c0 hb0 x t (h : ∀ v ∈ c0.U, u v = u' v) : psiBot p κ A c0 pstar x t u = psiBot p κ A c0 pstar x t u'` (the locality hypothesis `hlocPsi` of `Lvl.classSum_flat` for the bottom branch).
* `psiBot_BOKd` (same hypotheses as `classSum_bottom`): `BOKd (botR A c0) κ0.L κ0.base ![e,f,g,h] (fun κd τ => psiBot p κ0 A c0 pstar (ext κd) ![t0,t1,t2] (clock τ))`: integrable in the clock for every decoration, summable `L¹` norms in the decorations (per-state `BotGoal` from `clLocalSummand` bounds, `HF_of_all`).
* `tildeJ2_bundle_bottom` is the same theorem with the structure `κ : KPar d` (dynamic fields inside `κ`).

## How to plug into `Lvl` (S5C; NOT edited by me)
1. `Lvl.psiFuel`: in the branch `m+1`, `h : ∃ j, lv.Op j`, `hk : ¬ 1 ≤ (lv.e (choose ..)).1.val`, replace `lv.psiBase` by `psiBot p κ0 (lv.state ..) lv.c (choose (lv.exists_top ..))` (all other branches unchanged; `psiBase` stays for `¬ ∃ j, lv.Op j`).
2. `Lvl.classSum_flat`: delete `hbot`.  In the new case (`hk` false, i.e. `(lv.e pstar).1.val = 0`): `hup : ∀ j, j ≠ pstar → IsEmpty (FamilyOperation .. (lv.state ..) j)` is the same argument as `hA0` (every operative `j` has `(lv.e j).1.val ≤ 0`, so `lv.e j = lv.e pstar`, `lv.he`); `hb0` and the class-sum identity for a level are VERIFIED in uni/probe5b2/Lvl.lean (compiled against the existing uni/buildS5C oleans, read-only, with `probe5b2c.sh`; copy verbatim into S5C): `Lvl.bottom_hb0 B RD hG layer hLayer lv pstar (h0 : (lv.e pstar).1.val = 0) : lv.c.b = ((lv.state ..).family.placement pstar).lower` (proof: `corePlacement_at`, `piece_lower_eq_jointAt`, `jointAt_zero`, `lv.hcb`) and `Lvl.classSum_bottom κ0 hL hF hprime lv pstar h0 hup t0 t1 t2 e f g h : lv.classSum .. = c^{n1(lv.region)} ζ(lv.region) * lkRaw lv.region κ0.L κ0.base (psiBot p κ0 (lv.state ..) lv.c pstar) ![t0,t1,t2] ![e,f,g,h]` (`Lvl.region lv = botR lv.state lv.c` holds by `rfl`).  `hup` is the same argument as `hA0` (every operative `j` has `(lv.e j).1.val ≤ 0`, so `lv.e j = lv.e pstar`, `lv.he`). `hlocPsi` in this branch: `psiBot_congr`.  `hbot0` and `Lvl.hbot_of_start` become unnecessary.
3. Open for part C as before: `hAbs` (GlueAbsConv of the glued summand `psiStep .. psiBot` one level up) is WP-B; `psiBot_BOKd` gives only the absolute convergence of the bottom summand itself.

## Approach (what was proved, and why it is not a copy of 4d-B)
4d-B needs a lower block `T` because the lower factor `K̃` is the class sum of `T`; here the whole region `U` has bottom joint `b = P.lower` and boundary `(g,h)` at its two excluded children, so the S-side machinery `sSum`/`ExtS` (which drops the two boundary children of `b`) is not used.  Instead (all at the level of `CLLocalDecoration` of the whole region):
* A1 (`Bot1`): `clLocalSummand = spart U a b * bFac` (the `S = U` part of the summand times the factor of the atom `b`; the time domain of `clLocalTimeDomain` is `DomS ∧ bTimeOK`).
* Geometry (`Bot2`-`Bot3`): `chain_slow` (kept slot of a chain region whose bottom joint is the lower joint of `i` is `(placement i).keep`, from `designated`), `chain_stw` (same for `c.next i true`), so the existing `SLow`/`STw` apply to `S = c.U`; the twisted boundary slots are `freeSwap` of the original ones (sign bookkeeping `sign_naive_lowerChild`).
* Twist invariance (`Bot4`-`Bot6`): `stw_bFac` (`ζ_b' = -ζ_b`, `Ω_b' = -Ω_b`, `ε_b' = ε_b` under the conservation at `b` by `epsCoef_swap1/2`, boundary time conditions via `branching_naive`).
* Decorations (`Bot7`-`Bot8`): `decEquiv` (support, conservation incl. `b`, leaf pairing, 4 boundary values), the Dec-level twin of 4d-B's `extEquiv`.
* Pointwise (`Bot9`): `summand_same` (skip, FALSE: frame of the source, `spartExc` of the output, `bFac`), `summand_tw` (TRUE: `spartFrame_tw` + `exc_tw` + `stw_bFac`); `Bot10`: `clLocalKernel_same`, `clLocalKernel_tw` (sign `-1` from `STw.zeta`; sum/integral transported by `decEquiv`, `tEquivS`); `BOKd` transport by `sok_transport`.
* State level (`Bot11`-`Bot14`, `Bot15`): `botState_skip/false/true` (FALSE/TRUE as in 4d-B's `sSumAt_false/true`, with `clLocalKernel_idx` to pass from `ChainAt.nextA` to the region data); `botGoal_of_mem` for every `z ∈ canonFinset` via `mem_canonFinset_iff_bottom` and `reach_single`.
* Assembly (`Bot16`): sum over `canonFinset`, `Summable.tsum_finsetSum`, `integral_finsetSum`.

## Checks run (exact)
* Fresh rebuild `uni/fresh-5b2.sh` (new dir uni/buildS5B2f, topological order Bot1..Bot19): ALL-OK (logs/fresh-buildS5B2f.out).
* `#print axioms` (probe5b2/Ax.lean) of `tildeJ2_bundle_bottom`, `classSum_bottom`, `psiBot_congr`, `stw_bFac`, `decEquiv`, `clLocalKernel_tw`, `botState_true/false/skip`, `clLocalSummand_eq_spart_bFac`, `psiBot_BOKd`: all `[propext, Classical.choice, Quot.sound]`.
* Exact-type check: a transient `example` with the statement above, closed by `classSum_bottom`, elaborates (probe5b2/Ax.lean, kept as a record).
* Hygiene `grep -n "sorry|admit|axiom|opaque|unsafe|maxHeartbeats|set_option" src/VineEstS5B2/*.lean`: no hits.  No file over 180 lines.
## Hypotheses of the theorem (none smuggled)
`hA` (prime skeleton, as everywhere in 4b), `hb0` (the chain's bottom joint is the lower joint of `pstar`: this IS the bottom-piece hypothesis), `hup` (every other member inert at `A`: situation of `tildeJ2_assembly_bottom`), `hL : L ≠ 0`, `hF` (summability of the inputs on the base coset, as in `tildeJ2_bundle`).
## Uncertainties / errata / deviations
No erratum in TARGET: Step 4 for `p = 1` is stated implicitly (`U^{<p}` empty); the argument is the same, and the empty-chain factor is the one described above.  Deviations: none outside VineEstS5B2 (no edit of S5B, S5C or other packets; `Bot1`-`Bot19` live in the new namespace `WaveTurbulence.VineEstS5B2`).  Not done (belongs to part C): the bookkeeping that instantiates `classSum_bottom` for `Lvl` (item 2 above), and `hAbs` for the glued summand one level up.
READY vineest-4dB2

# HANDOFF vineest-C (V5 Step 4d part C), session 4 (Sonnet 5.5): CHECKPOINT -- hAbs reduced to ONE leaf obligation (S-side bound of the bundle); WP-B, WP-F, prefix theorem NOT started; 4d-B2 (hbot0) not READY at this time (no uni/src/VineEstS5B2 exists)

## Files added this session (uni/src/VineEstS5C/, all `module`, each < 200 lines, 818 lines total; build `uni/build5c.sh VineEstS5C.<M>`, all exit 0, no sorry; hygiene grep clean; axioms [propext, Classical.choice, Quot.sound] via probe5c/Ax4.lean)
AbsGlue (UAbs/SAbs, measurability of the clock), AbsGlue2 (**glueAbs_of_bounds**: SAbs + UAbs + measurability => GlueAbsConv, total <= CS*CT), AbsGlue3 (uAbs_idx/uAbs_congr/sAbs_congr, **uAbs_glue**), LevelAbs (MeasT, measT_psiStepSp, StepHyp: .glue/.uAbs/.glueAbsConv), LevelAbs2 (Lvl.stepHyp, Lvl.uAbs_step, Lvl.measT_step, **AbsLeaves**, **Lvl.absFuel**, **Lvl.hAbs_of_leaves** = hypothesis `hAbs` of `Lvl.classSum_flat` given `AbsLeaves`), AbsBase (baseConst, tsum_integral_norm_clLocalSummand_le, uAbs_psiNat), AbsBase2 (measurable_parentClock_top, measurableSet_ClDom, measT_psiNat, **Lvl.abs_base** = AbsLeaves.base/basem, DISCHARGED).
## What `AbsLeaves.sb/sbm` (the only open part of hAbs) is, and a WARNING about its exact form
`sb`: a uniform `SAbs` bound (sum over ExtS RS L base e f of the integral of |psiSB x (clock)| <= CS, uniform in t, e, f); `sbm`: measurability of psiSB x in the clock.  `sbm` is routine (frame: DomF set, KQ/KT rows via measurable_KQstar_comp; rowVal: indicator and rows at clock values; sum over zpFinset).  `sb` is NOT routine and its STATEMENT MAY NEED CHANGING: the S-side decoration `x : ExtS` has the node label x(b) (b the lower joint, in S but not in S.erase b, so no conservation at b in S) and the fibre structure of the glue (T-conservation at b ties E = x(b) to F_r = x(retained) and the T-labels) means the S-side alone need not be summable if x(b) is not tied to the pair labels of S by the top boundary (e,f).  Which holds depends on molecule geometry (is the tree parent of b in S?  T-side top joint b has its parent edge EXTERNAL; for S the joint b has two internal darts: probably the parent edge and the retained pair, which would tie x(b) to the labels by conservation at the ancestors, but this was NOT verified: `IsBlock` is molecule-level (WaveB2Draft/Molecules.lean L131), not tree-contiguity).  If x(b) is tied: new lemma `extS_ext_of_pairs` (x |-> labels at first leaves of pairs of S, for fixed (e,f)) is needed, proved by bottom-up (nodes whose children are determined) plus a top-down step along the ancestors of b; then bound each term of psiSB by 1_box * prod_p pairBound(label) * prod_v chainBound (skip/false: native S-part of A / opOut state via the `hfun` identities of StateInt4 bok_skip/bok_false; true: bundleInt(Phi=1) = twInt = sInt of the twisted garden at (extEquiv x, tEquivS sigma), `twInt_true_eq`/`sInt_tw`, bijection + measure-preserving change of time).  If x(b) is NOT tied: replace SAbs/UAbs by the two directional bounds (T-side: sum over E at fixed F, and sum over F at fixed E, each uniform; S-side fibre bounds over (E,F)); `glueAbs_of_bounds` then needs the fibre version (the proof structure of AbsGlue2 carries over).  A 15-minute check of the geometry (is b.parent in S for every split of the vine chain?  use mkSplitAt/NestGeom `iregion`, `lower_block`, `interval_block`) decides which.
## Deviations
`@[expose]` added to `epsOf` and `stInt` in uni/src/VineEstS5B/Final3.lean (accepted by ruling; needed to unfold them downstream).  No other file outside uni/src/VineEstS5C touched.
## Remaining (not started): `AbsLeaves.sb/sbm`; WP-B (replSum_decomp_ext on psiSB, pairing Bs1/Bs2 by conjugation with `hreal` as named input, datum with extra time constraint, Admissible, R35 cases, lift to the flat expression); WP-F (constants (C1 sqrt delta)^n2, L^(-eta^8 n3 - eta^2 b + eta^7), piece count, invariance of RowSizes/n2/n3/b); `WTPrefix VineEstCanonLayer` and the `VineEstCanon` corollary; discharge `hbot0` with 4d-B2 when READY; final fresh rebuild, axioms, hygiene, exact-type example, named-input list.
CHECKPOINT vineest-C: next step = decide the exact form of AbsLeaves.sb by the geometry check above, then prove `sbm` and `sb`; then `Lvl.classSum_flat` gets its `hAbs` from `Lvl.hAbs_of_leaves`.

# HANDOFF vineest-C (V5 Step 4d part C), session 3 (Sonnet 5.5): CHECKPOINT -- WP-I (induction over the core vines) DONE modulo two named items; WP-B/WP-F/final theorem NOT started; NEW FINDING F-BOTTOM

## Files (uni/src/VineEstS5C/, all `module`, each < 400 lines, 1964 lines total; build `uni/build5c.sh VineEstS5C.<M>` into uni/buildS5C; all exit 0, no sorry)
RestrictState, NestGeom, LevelStep, GenMerge, LevelBundle, LevelBase, LevelRec, LevelFlat, LevelRecurse, LevelLoc, LevelLoc2, LevelTop (dependency order as listed; LevelLoc2 imports LevelRecurse).  Only edit outside VineEstS5C: `uni/src/VineEstS5B/Final3.lean` got `@[expose]` on `epsOf` and `stInt` (needed to unfold them downstream); Final3 and the S5C modules depending on it were rebuilt.
## Approach and main statements (exact names; details in PROGRESS.md top)
* F-CHAINATOM: `ChainAt` requires the atoms of EVERY family member, so the lower block is not a chain of the full family; the notes' "tildeJ2_canon at the sub-chain" does not apply directly.  Fix: restricted families.  `restrictState`, `chainOfSplit`, **`sum_yA_eq_canon`** (class sum of the lower blocks = canon class sum of the restricted problem), **`Ktil_eq_canon`**.
* Geometry: `iregion`, `jointAt`, **`iregion_chain`** (pieces [i,j) form a vine chain), `iregion_upper_block`, `lower_block`, `interval_block`, **`mkSplitAt`** (SplitAt of the chain region of pieces < k0 of a restricted family at the member of piece index k).
* Merge: **`lkRaw_split_fubini`** (abstract clock-based summands; copy-generalisation of `clLocalKernel_split_fubini`), `flat_merge`, `psiSB` / `sum_stInt_eq` (bundle of the S-side), `psiNat` / `clLocalKernel_eq_lkRaw` (native summand), `canonFinset_of_noop`.
* Induction: `Lvl` (level), `Lvl.next`, `Lvl.classSum_nested` (one level of TARGET Step 4), `Lvl.classSum_flat_step`, `Lvl.psiFuel`, **`Lvl.classSum_flat`**: class sum of every level = `coupling^n1 zeta * lkRaw region kappa0.L kappa0.base (psiFuel (m+1) lv) ![t0,t1,t2] ![e,f,g,h]`.  Locality: `psiSB_congr`, `Lvl.psiFuel_congr`.  Top: `Lvl.top`, `Lvl.top_classSum` (rfl).
## Checks run
Each module built with `uni/build5c.sh` (exit 0).  `#print axioms` (probe5c/Ax3.lean) of sum_yA_eq_canon, mkSplitAt, iregion_chain, Ktil_eq_canon, lkRaw_split_fubini, sum_stInt_eq, clLocalKernel_eq_lkRaw, canonFinset_of_noop, Lvl.classSum_nested, flat_merge, Lvl.classSum_flat_step, Lvl.classSum_flat, psiSB_congr, Lvl.psiFuel_congr, Lvl.hbot_of_start: all [propext, Classical.choice, Quot.sound].  Hygiene grep (sorry|admit|axiom|opaque|unsafe|maxHeartbeats|set_option) over the 12 new modules: no hits.  NOT run: fresh rebuild in a new directory, exact-type example for the corollary (no final theorem exists yet).
## Hypotheses left in `Lvl.classSum_flat` (named, not smuggled): `hAbs` (GlueAbsConv of every `Lvl.psiStep`: absolute convergence of the glued flat integrand, to be derived from the row decay bounds in WP-B) and `hbot0` via `Lvl.hbot_of_start` (no operation at the piece-0 member of the start state; see F-BOTTOM).
## FINDING F-BOTTOM (needs a ruling or a new sub-packet "4d-B2")
`tildeJ2_assembly`/`tildeJ2_bundle` (and all of VineEstS5B) need a split with a lower block, i.e. a member of piece index >= 1.  For an operative member at piece 0 only the class (`tildeJ2_assembly_bottom`) is known, there is no kernel identity (S-side twist with fixed bottom boundary `(g,h)`, no lower block, conservation at the bottom joint `b` becomes a constraint of the S-side, roles of the two children of `b` exchanged).  The induction reaches this case whenever the bottom vine of the chain (at any level) is operative.  Nothing in TARGET (Def lftwist L1466-1480) excludes it.  Until this is done, `VineEstCanonLayer` can only be proved for chains whose bottom vine is inert (or via a new development).
## Remaining work (not started)
WP-B (bundle pieces (a)-(d) from `replSum_decomp_ext` applied to `psiSB`: pairing Bs1 <-> Bs2 by conjugation (`hQb` via `KQstar_conj/KTstar_conj` + defect rows), `hreal` (named input of the type of PL234 `reality_all`), R35 cases, rows -> `ClockedRows3`, datum with the extra time constraint for clause (a), `Admissible`, `hAbs`), WP-F (constants, invariance of RowSizes/n_(2)/n_(3)/b), `WTPrefix VineEstCanonLayer`, corollary.  Exact next steps: PROGRESS.md "NEXT (exact), revised".
## Named inputs of the eventual theorem (provisional, owners): unchanged from session 2 (SumintMixSignedDoubled; LeafwiseCoherentApproximationGate; LeafwiseIncoherentDecayGate; `reality_all`-typed hreal; VINEPARAM hM9) plus none new.
## Errata / deviations: none in the sources; deviation: `@[expose]` added to `epsOf`, `stInt` in VineEstS5B/Final3.lean (own packet).
CHECKPOINT vineest-C: next step = (1) derive `hAbs` and WP-B for a single operative vine (replSum_decomp_ext on `psiSB`), (2) decide F-BOTTOM.

# HANDOFF vineest-C (V5 Step 4d part C), session 2 (Sonnet 5.5): STOPPED vineest-C -- finding F-LAYERCOST (ruling needed); steps 1, 2 and the base case DONE

## Files (uni/src/VineEstS5C/, all `module`, each < 230 lines; build `uni/build5c.sh VineEstS5C.<M>` into uni/buildS5C)
GateH (CoherentGateH, IncoherentGateH, coherentGateH_of, incoherentGateH_of; ProfileBound, layerCost), GateRowsH, ConjRowsH, NativeRowsH, Step3AtH (step3AtLeafH), Step3FinalH (prod_rowCostH_eq: product of row leaf costs = regionLeafSize; step3BoundH_eq), LeafMono (leafwiseCoherentAt_largeConstantMonotone), Step3PrefixH (Step3StatementLayer, step3Layer_of_at, **vineestStep3Layer : SumintMixSignedDoubled -> LeafwiseCoherentApproximationGate -> LeafwiseIncoherentDecayGate -> WTPrefix Step3StatementLayer**), PosLimit (0 < Bh to 0 <= Bh), BaseLayer (**layerBound_noTwist**: Step3StatementLayer + CoreVinesNoTwist => the VineEstCanonLayer conclusion, any Bh >= 0).  Copied: 43 PL234Draft modules (trimmed imports; script uni/cp-pl234.py, build uni/buildpl.sh, order uni/pl234-order.txt) + patched TimeBoxGeometry, sha256 in uni/COPIED-SHA256SUMS-s5c.
## Approach
Step 1: the equality LeafApp.coherentCouple (layerProfiles) = SourceApp.couple (PL234 `sourceCouple_eq`, `sourceTree_eq`, `KQstar_eq_coupleLeaves`) did not exist in the uni world; ported by copying the SliceApp closure of pl23-30d/final (snapshot-9 build) with `SpineInputs`/`AnchorTypes` imports cut (not importable: WaveBDraft.Sumint) and recompiled in the uni world.  Steps 2: copy-and-edit of GateRows/NativeRows/Step3AtLeaf/Step3Prefix onto the H-gates; every bound gains `layerCost`; row bounds `rowBoundH = rowBound * rowCostH`; leaf costs of the conjugate couple via `Conj.inputs_eq`; engine strictness needs `0 < Bh` (PosLimit removes it by an eps perturbation).
## Checks run
`uni/build5c.sh` of each of the 10 modules in dependency order, exit 0 (this session, re-run at the end); axioms of layerBound_noTwist, coherentGateH_of, incoherentGateH_of, vineestStep3Layer, couple_row_leaf_le_both = [propext, Classical.choice, Quot.sound] (uni/probe5c/Ax1.lean, Ax2.lean); hygiene grep (sorry|admit|axiom|opaque|unsafe|maxHeartbeats|set_option) over uni/src/VineEstS5C (non-Copied): no hits.  NOT run: fresh rebuild in a new dir, exact-type example for the corollary (no final theorem exists).
## Finding F-LAYERCOST (PROGRESS.md top): `VineEstCanonLayer`'s RHS `regionLeafSize` (start state's rows, arbitrary Bh) is not twist invariant for non-constant Bh; repair options (A) constant B (recommended), (B), (C).  No change to LayerStatement.lean was made (needs your ruling).
## Findings also relevant to the next agent
* hQb needs no app halves (defect rows with remainders, 4c DefectRows) -- ISSUE-APPCONJ and `coupleCohSwap_of_gate` are not needed.
* hreal = PL234 `reality_all` (any real F, so F := h); not ported (33 modules, ~7.5k lines, needs LayerRegDraft.Part2, MexpDraft.RegCancelB2, SpineInputs); plan: named input with exactly the type of `PL234.reality_all` (owner PL234).
## Named inputs of the eventual VineEstCanonLayer prefix theorem (provisional, owners)
SumintMixSignedDoubled (DEGEN-VINE, proved unconditionally `sumintMixSignedDoubled`), LeafwiseCoherentApproximationGate (PL234/PL23-30D + RA1-LEAFWISE), LeafwiseIncoherentDecayGate (INCOH-LEAFWISE), reality (iii): exact type of `PL234.reality_all` (P4Gt.lean): forall {d} (δ) (F : N -> Mom d -> R) {p q q'} (q' <= q) (q <= p) (n) (b : Option N) (ts ∈ timeBoxGt q q') (k), (∑ᶠ (Q X LQ LX) (_ : CoherentPairCarrier p q q' n b Q X LQ LX), SourceApp.couple δ F LQ Q q q' (ts 0) (ts 1) k * star (SourceApp.tree δ F LX X q q' (ts 0) (ts 1) k)).im = 0 (PL234, proved; discharged by reality_all at assembly), VINEPARAM (hM9, universe), the 4c/4d-A/4d-B results (proved in uni).
## Remaining after the ruling (not started): WP-I (unrolled identity of the nested class sums), WP-B (bundle rows, R35 cases, Admissible, engine calls), WP-F (constants), final prefix theorem + VineEstCanon corollary; est. 4-5k lines.  Exact next steps in PROGRESS.md top ("NEXT (exact)").
RULING R46 (option A) received and applied to LayerStatement.lean (single constant B₀); see PROGRESS.md top.

# HANDOFF vineest-C (V5 Step 4d part C), session 1 (Sonnet 5.5): STOPPED vineest-C -- interface gap F-LEAFREAL (see PROGRESS.md top)

## Files / environment
No Lean for the statement was written (see below).  Environment prepared in uni/: buildS5C farm, scripts build5c.sh, buildcp.sh, probe5c.sh, buildpatch.sh; patched GateDefs src/VineEstS5C/Patch/VineEstS3/GateDefs.lean; copies of lftwist-leafmap `Leaf{Native,Corr,Corr2,Corr3,Op,Op2,Batch,Map,Exc}` in src/VineEstS5C/Copied (sha256 uni/COPIED-SHA256SUMS-s5c).  Probe uni/probe5c/P1.lean shows lg-spine's `LeafwiseAt` (leafwise gates) co-imports with VineEstS4.CanonStatement and VineEstS5B.Final3.
## Checks run
Patched GateDefs: exit 0; the 9 copied Leaf* modules: exit 0 each (buildcp.sh); probe P1: elaborates, `#check` of LGSpine.LeafwiseCoherentApproximationAt, VineEstS4.VineEstCanon, VineEstS5B.tildeJ2_bundle succeed.  No theorem was proved this session, so no axioms/hygiene/exact-type checks apply.
## Finding (details and options A/B/C in PROGRESS.md top)
F-LEAFREAL: LF twists replace the exceptional tree/couple by freely chosen coherent objects (TARGET Def lftwist L1466-1480), so the leaf bijection phi (LFTWIST-LEAFMAP, `FamilyBatchTrace.LeafCorr`) exists only on ordinary leaves; and the cancellation hypothesis `hreal` (layerregest10 realness of Sum Q conj T over Bs0) is available leafwise only as PL234's POLARIZED `LeafwiseRealityGate` ("does not assert realness for independently chosen summand profiles").  Hence "H transported along phi + the three leafwise gates" (R43/R44 wording) does not yield the vine estimate for per-leaf profiles at the exceptional leaves.  Interface gap, not a TARGET error (TARGET L2065-L2067 is fine for symmetric families, which S2's weightedFamily sums are).  Second point: the right-hand side `leafSizeProduct` over the whole garden needs `1 <= B` (K^U only sees the leaves of the rows in U).
## Named inputs of the eventual VineEstCanonLeaf (provisional, owners)
`LeafwiseCoherentApproximationGate` (PL234/RA1-LEAFWISE, READY), `LeafwiseIncoherentDecayGate` (INCOH-LEAFWISE, READY), `LeafwiseRealityGate` (PL234, READY, polarized), CoherentRealityGate (i)/(ii) app halves `ISSUE-APPCONJ` (PL234, open; the leafwise conj-swap route is RepConj3 `coupleCohSwap_of_gate`, S2 represents), `VINEPARAM` (hM9, universe), LFTWIST-LEAFMAP (leaf correspondence, in progress), regred-leaf node kernels (READY).
STOPPED vineest-C: needs a ruling on F-LEAFREAL (options A/B/C).
# HANDOFF vineest-4dB (V5 Step 4d part B, Sonnet 5.5): S-side twist at p*  -- READY vineest-4dB

## Files
uni/src/VineEstS5B/{Frame,Geom,Dec,Fac1,Fac2,Fac3,Sum,Same,Low,StateOps,Exc,StateInt1..4,Transport,Final1,Final2,Final3}.lean (19 modules, each < 300 lines).  Build: uni/build5b.sh VineEstS5B.<M> (-> buildS5B); fresh: uni/fresh-5b.sh (-> buildS5Bf).

## Approach
Upper block S (pieces >= p*) has the lower joint b = P.lower of p* as BOTTOM joint, so the twist is not rigid on S.  spart = spartFrame * spartExc (exceptional factor: parent-clock condition at b, couple row of the retained pair, tree row at b).  Decorations correspond by twistNodeLabels (lower<->retained labels exchanged; child labels of every atom != lower unchanged, which handles the exchanged u3/u4 slots); realization/splitA correspond (STw); clocks by tEquivS; zeta' = -zeta; frame equal (spartFrame_tw).  States of Zp(A): skip / FALSE op use the same chart (sSum_same), TRUE op uses sSum_tw.

## Exact statements (Final3.lean)
* `zp_state` : G in Zp(A) -> sSumAt kappa G.1 G.2 (ktilde G) = coupling^n1 * zeta_S * tsum_x int_sigma stInt kappa A sp0 hA G.1 x sigma  /\  BOK (integrable in sigma, summable L1 norms in x).
* `tildeJ2_bundle` : sum_{G in Zp(A)} sSumAt G (ktilde G) = coupling^n1 * zeta_S(A) * tsum_{x : ExtS sp0.RS} int_{sigma} sum_{G in Zp(A)} stInt G x sigma  (hyp: hA prime, hA0, hL, hF as in tildeJ2_of_split).
* stInt G = epsOf G (-1 iff twAt) * bundleInt kappa A sp0 Ktil (decide twAt) (nuOf G p*) (rowQ G p*) (rowT G p*); bundleInt = spartFrame(A) * (rowVal nu rq rt (u b) p p' Lq M * Ktil(u b, E, F_r)); (p,p',Lq,M) = (u qb, u qr, F_r, E) untwisted, (u qr, u qb, E, F_r) twisted; E, F_r = base+lat(x lower), base+lat(x retained); rowVal nu rq rt t0 p p' Lq M = [t0<p] * (rq t0 p' Lq if nu=1 else rq p' t0 Lq) * rt p t0 M; rowQ/rowT = KQstar/KTstar of sigStar G p* (chart-free).
* Feeding replSum_decomp_ext (part C): with Bs1 = {G : nuOf G = 1}, Bs2 = {nuOf G = -1}, Q = Qb := rowQ G, T = Tb := rowT G, (t0,s1,t1) = (u b, u qr, u qb) and (x,y) = (E,F_r) if nu(A)=1 (resp. (t1,s1) swapped, (x,y) = (F_r,E) if nu(A)=-1), the integrand sum is zeta+-normalized replSum (+ for nu=1, - for nu=-1; zeta+ = zeta*nu(A)).  Remaining for C: pairing Bs1 <-> Bs2 by conjugation (hQb), not done here.
* Profile-genericity (R43): rows enter only as abstract functions rowQ/rowT; F (kappa.F) is used only through the all-layer summability hF. A node-profile version needs KQstar/KTstar/KPar to take a profile argument; not done (not free).

## Checks
Fresh rebuild uni/fresh-5b.sh: ALL-OK (logs/fresh-buildS5Bf.out).  Axioms of tildeJ2_bundle, zp_state, sSum_tw: [propext, Classical.choice, Quot.sound] (probe5b/Ax.lean).  Hygiene grep sorry|admit|axiom|opaque|unsafe|maxHeartbeats|set_option over src/VineEstS5B: none.  No pinned exact-type target exists.

## Uncertainties / errata
None found.  Unproved glue: Bs1<->Bs2 conjugation pairing; the rows' identification with the layerreg objects (part C).
READY vineest-4dB

# HANDOFF vineest-4dA (V5 Step 4d part A, Sonnet 5.5): READY

## Files (uni/src/VineEstS5A/, 18 modules, 2029 lines, each < 300 lines)
PhasePhCph Kind2Bound ExprMulCph ClockedBoundMixCph (item 1); A3Clock A3Expand A3Modes A3Bounds A3Engine A3Scalar A3Joint A3Ae A3Coef A3Embed A3Rows (item 2); GenKernel GenSumint GenStar (item 3).  Exact statements: top of PROGRESS.md "4d-A".

## Approach
1. Kind 2: only the mode INTERCHANGE used unimodularity of the phase (continuity and the pointwise bound); the per-mode bound (`mode_bound_mix`) already allows every badKind (modeDatum keeps D's phase).  So `clockedBoundMix_Cph` has the same conclusion/constant; new hypotheses `3 eta <= 1` (continuity of |x|^(1-3 eta)) and `kind2Factor <= Cph` on timeDom (all integrability/bounds are restrict-timeDom a.e.).
2. Joint 3-clock factor: the engine was re-done with three clocks per row (arity-3 copy of ClockPhase/ClockedExpr/Expand/Modes/ModeBounds/ClockedBoundMix; constants recomputed: engineConst3, eta <= 1/2).  The row's time factor H = |t0-t1|^(-(1-3eta)) (J(t0,t2)-J(t1,t2)) is expanded jointly: 4c `timeDiff_extraction` (XNorm00Restr, V := Unit) then a new scalar Fourier-series expansion a.e. on a box (`scalar_fs_hasSum_ae`: expands the continuous representative `Regref.rep g` of an extension g of finite X^theta norm, so no continuity of H on the diagonal is required; the sum bound is a direct kernel/lintegral computation `hcoef_sum_le` with `weight_kern_tsum_le`).  The spatial part is a separated factor M(r,k) (coefBound_sep_le uses SNorm_smul_le), 2-clock rows embed with a zero third mode (embed2/embedMode), and an a.e. statement on three distinct internal slots pulls back to internal times via measure-preserving coordinate splitting (`ae_pullback_coords`).  hser of the engine is a.e. in tau for this reason.
3. Generic rows: copied RegRedDraft CLLocalKernel(+Recentering) / CLKernelReindex / VineChainSumintForm with `clLocalStarProduct` replaced by an abstract `Phi` and the weights by abstract `WKg WLg` under the hypothesis `RowFactorization` (shape of `clLocalStarProduct_eq_weights`); specialization to the original theorem compiled (`vineChain_eq_sumintForm_of_gen`).

## Checks run
* each module: `uni/build5a.sh VineEstS5A.<M>` -> exit 0.  FRESH rebuild `uni/fresh-s5a.sh buildS5Af` (log uni/logs/fresh-buildS5Af.out) = ALL-OK for the 18 modules (reads buildS5f, the fresh 32-module engine, read-only).
* `#print axioms` (uni/probe5a/Ax.lean, run via probe5a/run.sh): clockedBoundMix_Cph, clockedBoundMix3, jointTime_modes, jointRow_modes, rowModes3_of_restr, coefBound_sep_le, coefBound_finsetSum_le, ae_clock_of_ae, ae_pullback_coords, embed lemmas, vineChainGen_eq_sumintForm, vineChain_eq_sumintForm_of_gen, kind2Factor_le_pow, abs_sub_le_of_mem_timeDom: all only [propext, Classical.choice, Quot.sound].
* hygiene grep (sorry|admit|axiom|opaque|unsafe|maxHeartbeats|set_option) over uni/src/VineEstS5A: no hits.
* exact-type check: `vineChain_eq_sumintForm_of_gen` (GenStar) is the exact type of `vineChain_eq_sumintForm` (compiled).  No exact-type example for VineEstCanon (not part of 4d-A).

## Uncertainties / deviations / errata
* `clockedBoundMix3` needs `P.η <= 1/2` (was `<= 1`) and has a different explicit constant `engineConst3` (arity 3); both harmless since eta < 1/4 everywhere.  The existing 2-clock engine is untouched; part C may use either (arity 3 for the bundle vine datum).
* `hser` of the arity-3 engine is a.e. in tau (restrict timeDom).  Rows other than the joint row are pointwise.
* `jointTime_modes` requires `eta < 1/4` and `theta <= eta` (from 4c timeDiff_extraction); `theta = 6 eta^6` qualifies for eta < 1/4.
* Gen endpoint: `hΦ` is a PRODUCT over sumint rows; the bundle (a finite SUM over (Q,T) in Bs of products with indicator constraints) must be split by linearity (sum of Gen kernels) or its indicator pieces handled as time-domain changes (clause (a)) by part C.  I did not formalize this splitting (it is part C / B-bundle).
* Sandbox: another agent builds in uni/buildS4c; I only read buildS5f and wrote buildS5A/buildS5Af (no edits to other scratch, universe, stage1, vineest-s4c).
* No source errata found in this part.

READY vineest-4dA

# HANDOFF vineest-full (V5 Step 4d), session 1 (Sonnet 5.5): CHECKPOINT, NOT READY

## Files (scratch <scratch>/vineest-s3/uni; new this session)
* uni/src/VineEstS4c/{TimeDiffKernel,TimeDiffNorm,TimeDiff,TimeDiffRestr,DefectRows,Bs2Vanish,SourceAppVanish}.lean: the 4c frozen-world modules, ported into the uni (draft) world by IMPORT SUBSTITUTION ONLY (sha256 orig/ported: uni/COPIED-SHA256SUMS-s4c).  The draft-world 4c modules (SumintPar/*, ReplaceAlgebra, TimeDiffGauss, TimeDiffScalar, WeightDiff, LeibnizPack, RowForms, CoordinateDerivativeBound) are used read-only from <scratch>/vineest-s4c/build.
* uni/src/DegenVinePar/{MixLocalized,MixNorm,MixCounted,MixRecomb,MixSumint,SumintMix,SumintMixDoubled,ScaledSumintMix,ClockedExprMul,ClockedBoundMix}.lean: DEGEN-VINE character-mixture layer and engine over `SumintPar.SumintDatum` (r-dependent K weights).
* uni/src/VineEstS3Par/{SignedParam,SignedBound,ClockPhase,ClockedExpr,TimeDomMeas,DecaySum,DecayX,ClockedExpand,ClockedExpand2,ScaledSumint,ClockedModes,ModeBounds,ModeBounds2,EngineAux,ClockedBound}.lean: the clocked engine over SumintPar (ClockedModes rewritten with the r-sup inside the mode sum).
* Scripts: uni/build4d.sh (one module; LEAN_PATH buildS4c:buildS4b:buildN:stage1/build-fresh4:vineest-s4c/build), uni/fresh-s5.sh (fresh rebuild of all 32 new modules into a new dir), uni/portpar.py (mechanical porting helper), probes uni/probe5/{Co2,Ax1,Ax2}.lean.  PROGRESS.md top has the architecture and the exact next steps.

## Approach
(1) Reconcile the two worlds: the frozen-world 4c modules only clashed on `import WaveTurbulence.Frozen.Defs.*` (same constants as WaveBDraft.System/Core) and on Foundations.Sumint.Norm* (draft copies SumintSigned.Norm*, namespace WaveTurbulence.SumintSigned): substitution only, no proof edits.  (2) The `SumintPar` fork (r-dependent weights) had no engine above it: DEGEN-VINE's mixture layer (8 modules) and the clocked engine (~15 modules) were ported; the only semantic edits are the extra argument r = E 0 - E 1 of wK, the r-free majorant `coefMajor` in MixNorm/MixCounted (as in SumintPar.XNorm00_localizedSourceExtension_le), `summedCellFourierFactor d (d+1)`, the |r|^{#badKind=1} prefactor carried by clockedExpr/clockedExprMul (so badKind 1 is allowed), the mode-family sup over r in ClockedModes, and `hreg : d < wDec` instead of the hard-coded 30d.

## Checks run (exact)
* each new module: `uni/build4d.sh <Module> buildS4c` -> exit 0 (logs uni/logs/buildS4c-<Module>.log).  Co-import probe `uni/probe5/Co2.lean` (SumintPar.Final + 4c modules + VineEstS4.CanonStatement + VineEstS3.Step3Prefix in one file): elaborates.
* `#print axioms` (probe5/Ax1.lean, Ax2.lean): DegenVinePar.sumintMixParDoubled, XNorm00_mixLocalized_le, scaledSumintMixAt_of, clockedBoundMix, VineEstS3Par.Eng.clockedExpr_hasSum, VineEstS4c.TimeDiff.timeDiff_extraction, replSum_decomp_ext, hQb_of_halves: all [propext, Classical.choice, Quot.sound].
* hygiene grep (sorry|admit|axiom|opaque|unsafe|maxHeartbeats|set_option) over uni/src/{DegenVinePar,VineEstS3Par,VineEstS4c}: no hits.
* fresh rebuild: `uni/fresh-s5.sh buildS5f` (log uni/logs/fresh-buildS5f.out) -- see the last line of PROGRESS.md for its result.
* NOT done: no exact-type example for VineEstCanon (the theorem is not proved), no fresh rebuild of the Step 3/4b closure (untouched).

## Uncertainties / findings
* vm.max_map_count (65530): a NON-module probe file importing the Step 3/4b closure fails with `failed to read file ...olean.private` (not a missing file); start probes with `module`.
* `clockedBoundMix` still assumes `badKind <> 2`; clause (c) needs the phase bound instead of unimodularity (PROGRESS item 2a).
* The S-side twist at pstar (WP-S) is the genuinely new geometry; it is not covered by Tw1..Tw10 (T-block below the lower joint) nor by sSum_op_true (members below the split).  A reduction observed: split U = S_up u T' with S_up = the pieces above pstar; sSum_op_true then makes S_up identical for all class members, so the twist analysis is confined to T' whose TOP vine is the twisted one.  No mathematical obstruction found; TARGET L1913 (ii) is a candidate erratum already ruled (R35), see PROGRESS 'R35 notes'.
* No source errata found this session beyond R35.  Deviations: none to the pinned statements (nothing pinned was touched).

CHECKPOINT vineest-full: exact next step = PROGRESS.md item 2(a) (kind-2 phase bound in the Par engine), then 2(b) (joint 3-clock factor), then WP-G (generic rows endpoint) and WP-S.

# HANDOFF vineest-s4b (session 4b-8): class assembly (tildeJ2), TARGET Prop `vineest` Step 4

## Files (scratch <scratch>/vineest-s3/uni/src/VineEstS4/, all < 200 lines)
27 new modules, in build order (uni/build-s4b.sh): Cls4Ext Cls5Inj Cls6Zp Cls7Inj Bl1Reach Sp2Split Sp3State Sp4Rigid Sp5Reach Sp6KT Sp7Comb
Sp8Fib Sp9Fib Sp10KT Sp11Lin Sp12Sok Sp13Rig Sp14Op Sp15SokOp Sp16Main Sp17Suffix and (this session) Sp18Comb Sp18Geom Sp19Canon Sp19Bottom Sp19Final.

## Approach
- Sp18Comb `exists_split_assembly`: induction on the CLChainAssembly gives, for 1 <= k < n, Sk (pieces >= k, block a -> bk), Tk (Vine.Chain bk -> b of k pieces),
  Sk ∩ Tk = {bk}, Sk ∪ Tk = U, atoms/lowers of the pieces.  Sp18Geom `exists_assemblySplit`: Tk is a block by `chain_suffix_currentBlock`; builds a
  `SplitAt` of `chainStart B` with J = `belowSet B pstar` = {j | j.1 < pstar.1}.
- Sp19Canon `sum_canonSp_eq_canon` (canonSpFinset ≃ canonFinset, forgetting the split) and `tildeJ2_canon` (tildeJ2_of_split restated over canonFinset).
- Sp19Bottom `mem_canonFinset_iff_bottom`: if every member ≠ pstar has no operation at A, canonFinset = states reached by [pstar] (= Zp(A); Y(A) = {A}, K~ trivial; Step 3 form).
- Sp19Final: `tildeJ2_assembly` (p* not bottom, k >= 1) and `tildeJ2_assembly_bottom` (p* bottom piece).

## Exact statement: see top of PROGRESS.md (also validation/AxS4b8.lean, an exact-type `example` that elaborates).

## Checks run
- Fresh rebuild: uni/build-s4b.sh (buildS4b recreated), log uni/logs/fresh-s4b-8.out: 85 modules `exit 0`, final line ALL-OK.
- Axioms (uni/p4c.sh validation/AxS4b8.lean -> validation/AxS4b8.log): tildeJ2_assembly, tildeJ2_assembly_bottom, tildeJ2_canon, tildeJ2_of_split,
  exists_assemblySplit, chain_suffix_currentBlock, zp_eq_of_sigStar, sum_canon, sum_yG_eq_yA, kT_rel: all only [propext, Classical.choice, Quot.sound].
- Hygiene grep (sorry|admit|axiom|opaque|unsafe|maxHeartbeats|maxRecDepth) over the 27 modules: no hits.
- Exact-type example: validation/AxS4b8.lean compiles (rc 0).

## Uncertainties / deviations
- Hypotheses of tildeJ2_assembly: `hup` (members not below pstar and ≠ pstar carry no FamilyOperation at the start state; TARGET: p = largest vine satisfying the
  assumptions), L ≠ 0, all-layer summability of κ.F on the lattice (HF).  These are the premises of TARGET's setting, not conclusions.
- The split is existential (sp0 with sp0.c = chainStart B); the left side is split-free (canonFinset); the RHS depends on sp0 only through the (unique up to the construction) blocks.
- k = 0 handled by `tildeJ2_assembly_bottom` (reduction to Zp(A) = canon; no S/T factorization needed), not by the SplitAt form.
- Existing-state caveat: Cls/Sp modules use uni/build (symlinked) for modules outside the build-s4b.sh list.
No source errata found this session.

READY vineest-s4b

# HANDOFF vineest-s3 -- STEP 4b, SESSION 4b-6 (Sonnet 5.5): STEP 4 (class assembly tildeJ2) PARTIALLY DONE -- CHECKPOINT vineest-s4b (READY NOT claimed)

## Files (new, uni/src/VineEstS4/, all `module`, each < 270 lines, hygiene grep clean: no sorry/admit/axiom/opaque/unsafe/maxHeartbeats)
Tw11Data, Rg1Geom, Rg2Dec, Rg3Fac, Rg4Time, Rg5SSum, Cls1State, Sp1Geom, Op1Step, Cls2Comb, Cls3Inv (1,393 lines).  Each was compiled with uni/buildp.sh (Cls2Comb/Cls3Inv need stage1: uni/buildc.sh = build4c.sh); all appended to uni/build-s4b.sh (which now calls build4c.sh).

## What was proved (exact names; statement of the target and the work packages are at the top of PROGRESS.md)
* K^T at the member p* for BOTH choices: `clLocalKernel_false_LF`, `kernelT_op_true` (e,f exchanged), `kernelT_op_false`; general `clLocalKernel_congr_data` (kernel reads D only through native rows/atom layers).
* S-side of (tildeJ2): `sSum` (S-part with an arbitrary lower factor) and its invariance under a unit twist at a member BELOW the split: `spart_rigid`, `extSEquiv`, `tEquivS`, `sSum_rigid`, `sSum_rigid_LF`, `sSum_op_true`; FALSE operations: `spart_congr_data`, `sSum_false_LF`, `sSum_op_false`; rigidity from geometry: `rigidAt_of_split`.
* Per state: `clLocalKernel_eq_sSum` (K^U = sSum with Phi = K^T), from `clLocalKernel_split_KT`.
* Class combinatorics: `familyBatch_moveLeft`, `Reach.append`, `canonReps_decomp` / `mem_canonReps_of_decomp` (canonical class = union over states y reached by one operation at pstar of the canonical reps of the batches over the other members), `sigStar` + `sigStar_batch` (invariant signature of a member under batches avoiding it).
## Checks run (exact)
Each module: `buildp.sh/buildc.sh <M>` -> `exit 0`, no warnings of substance (logs/buildS4b-VineEstS4.<M>.log).  `#print axioms` of all main results: validation/AxS4b6.log (propext, Classical.choice, Quot.sound only).  Hygiene grep: clean.  A FRESH rebuild of the whole closure (uni/build-s4b.sh) was NOT run in this session (the machine was loaded, ~2 min per module); the modules were built one after the other against the previous ones, and Rg2Dec's later change (kept_eq_rigid) was followed by a rebuild of its dependents Rg3Fac..Sp1Geom (exit 0).  An exact-type `example` for (tildeJ2) was NOT written: the statement is not yet formalized (see below).
## NOT done (blocking READY)
1. (tildeJ2) itself: injectivity of (G, y) |-> x (Cls4Ext: INJ via Stage1.layered_eq_of_classes, plan in PROGRESS.md), the transport of the split data (S,T) and RigidAt along Reach batches (WP-D), the Summable/Integrable interchange (WP-E), the common factor Y(G) ~ Y(A) (WP-5).
2. The brief's step 1 ("sibling lemma": K^T invariance for a TRUE twist at a member whose lower joint is not T's upper joint) was NOT proved and is not needed when pstar is the top member carrying operations; the S-side analogue for members below IS proved (rigid lemma).
## Uncertainties / deviations / errata
* The statement design assumes: every operation-carrying member other than pstar lies in the lower block T (members above pstar have no operation; to be justified by moveLeft + eligibility), and that Su/Tl are given as geometric data (blocks of the START state) because 'union of consecutive pieces is a block' is not available for suffixes of the assembly.  No new premise on the analytic side.  Possible subtlety: eligibility of below members at the states G in Zp(A) (Diamond gives it when both are eligible at A); if it failed the common-factor claim (K~ at A) would need K~ per G.
* No errata found in this session.
* Lean gotchas recorded in PROGRESS.md (write twisted regions with `eB P`, not `coreBranchEquiv`; `rw` fails on `Finset.mem_erase` for `coreTwistForest` typed membership).
CHECKPOINT vineest-s4b: next exact step = Cls4Ext (INJ), see the top of PROGRESS.md.

# HANDOFF vineest-s3 -- STEP 4b, SESSION 4b-5 (Sonnet 5.5): dedup DONE, STEP 3 (K^T twist invariance) DONE, STEP 4 (tildeJ2) NOT STARTED -- CHECKPOINT vineest-s4b

## Dedup (ruling on the build-world clash)
1. `VineEstS3.GateDefs` defined `timeBox`, `timeBoxGt`, `InputRemainder`, `regBound` as verbatim copies; diff against universe `WaveB2Draft.Statements` (lines 36-49): byte-identical.  2. Deleted the copies, `public import WaveB2Draft.Statements` added (`SourceSeparated` kept).  Rebuilt the 41 dependent modules into `uni/buildN` (merged symlink dir built by `uni/linkN.sh`; scripts build4b.sh, p4b.sh, build-s4b.sh now use `$S/$BD:$S/buildN`; originals `*.pre-unify`), then the fresh Step-4b rebuild: ALL-OK (`logs/fresh-s4b-unify.out`).  `uni/p4c.sh` probes with stage1's `build-fresh4`: `import VineEstS4.BaseCase` + `import S1Final` works and `Stage1.opsCommute_all` is importable (so Step 4 needs no `_of_opsCommute` premise).  4. Duplicate scan (name-level, uni/src vs universe/src vs stage1/src): only `Vine.chain_joints_mem` (port shim VineEstS2.SourceVineObjects vs universe VineChainConnected), identical statement and proof, and a co-import probe shows no clash.  The old copy is saved as vineest-s3/GateDefs.lean.pre-unify.  `uni/rdeps.py` computes reverse dependencies.

## Step 3 (new modules uni/src/VineEstS4/Tw1Geom ... Tw10Final, 1,350 lines total, each < 300)
Main result `clLocalKernel_twist_LF` (exact statement at the top of PROGRESS.md): K^{T'} of the twisted garden (true-choice LF construction at a placement whose lower joint is the upper joint of the CL block T) = K^T of the source with the first two boundary momenta exchanged; no premise beyond block/CL pattern/region data and the two layering specs.  Approach: node bijection `twNode` = naiveNodeEquiv o swap(lower,retained) carries local decorations (decEquiv), eps (eps_lower via epsCoef_exchange), the signed phase (sign_omega_at), clocks (tEquiv, piCongrLeft, parentClock_corr via parentClock_child), the time domain (twDomain_iff), regional leaf pairs (tp, tp_first), and the native layered couples/trees (ordinary rows, `ordinaryCoupleLayers/ordinaryTreeLayers`); only the lower joint and the retained leaf are special.
Checks (exact): `uni/build-s4b.sh` fresh (logs/fresh-s4b-session5.out) ALL-OK, all 46 modules exit 0; `validation/AxS4b5.log`: `#print axioms` of clLocalKernel_twist_LF, clLocalKernel_twist, summand_twist, native_couple_eq, native_tree_eq, coreLayer_eq, twDomain_iff, dec_iff, support_iff, region_eq: standard axioms only (see log); hygiene grep sorry|admit|axiom|opaque|unsafe|maxHeartbeats|set_option over Tw*.lean: no hits.  No exact-type check of a pinned statement (Step 4 statement not yet written).
Uncertainties: (1) K^T invariance is proved for a twist AT the lower joint of T (TARGET twistexplain (d)); the invariance of K^T under twists at members ABOVE p* whose lower joint is not a_T (T moves rigidly, no label swap) is NOT proved and is needed for Step 4.  (2) R31(3) slot labels: boundary (a_T, a_T.child excluded) are exchanged, (g,h) fixed (region_eq).
Errata: none found.  Deviation: none (no new premise).
Lean gotcha recorded: terms `(coreBranchEquiv G P b).child i` have type in `coreTwistForest`, not `(unitTwistGarden G P).tree`; use the `eB/eL/eLow` abbreviations and `exact`/Eq.trans rather than `rw` (the "not type-correct at implicit transparency" error).
CHECKPOINT vineest-s4b: see the top of PROGRESS.md (Step 4 design notes).

# HANDOFF vineest-s3 -- STEP 4b, SESSION 4b-4 (Sonnet 5.5): AbsConv discharged (step 1) and the K^T form of the Fubini identity (step 2) DONE; steps 3-4 OPEN (see PROGRESS.md top)

## Files (new, uni/src/VineEstS4/, all `module`, each < 200 lines, hygiene grep clean: no sorry/admit/axiom/opaque/unsafe/maxHeartbeats/set_option)
AbsNative (kernel bound `norm_kernelK_le`, uniform majorant bound `majSum_le`, `joint_injective`, `summable_majSum`), AbsLocal (`clLocalDecoration_ext_of_pairs`), AbsMeas (`HF`, native input summability, measurability of KQstar/KTstar along clocks), AbsBound (measurable time domain, unit box), AbsSummand (`pairBound/chainBound/localBound`, `norm_clLocalSummand_le`, `measurable_clLocalSummand`), AbsConvLocal (`integrable_clLocalSummand`, `integral_norm_clLocalSummand_le`, `summable_integral_norm_clLocalSummand`), SplitFubiniInputs (`fU_eq`, `absConv_of_inputs`, `clLocalKernel_split_fubini_of_inputs`, `clLocalKernel_split_KT`).

## Approach (step 1)
|summand| <= 1_{box} * prod_p (|c|^n_p * M_p(x_p)) * prod_v C_v, M_p(x) = sum_rho input-majorant at the attachment coset (summable in x for a plain couple by the JOINT injectivity (x, rho) -> (x + rho_l)_l of the input labels; uniformly bounded by prod_l sum_n |F_l| by translation invariance of the lattice sum); the local decoration is determined by the labels of the first leaves of the regional pairs (conservation + pairing + boundary); so sum_kappa prod_p M_p(x_p(kappa)) is dominated by prod_p sum_x M_p(x) (summable_pi_prod over an injective map).  Integrability: measurable (finite products of continuous kernels composed with measurable clocks, indicator of a measurable domain) and bounded on the unit box.  Transfer to the glued decorations by the equivalence `splitLocalEquiv` and `summand_split`.

## Checks (exact)
`uni/build-s4b.sh` (fresh, 3m05s): ALL-OK, all 36 modules exit 0 (logs/fresh-s4b-session4.out).  `validation/AxS4b3.log`: `#print axioms` of norm_kernelK_le, majSum_le, joint_injective, summable_majSum, clLocalDecoration_ext_of_pairs, measurableSet_localTimeDomain, norm_clLocalSummand_le, measurable_clLocalSummand, integrable_clLocalSummand, summable_integral_norm_clLocalSummand, absConv_of_inputs, clLocalKernel_split_fubini_of_inputs, clLocalKernel_split_KT: all [propext, Classical.choice, Quot.sound].
No exact-type check was run for steps 3-4 (not done).

## Deviation / premises
New premise HF (source premise: input summability on the base coset at every input leaf of D.garden hG; derived from InputRemainder by `summable_inputsF_of_InputRemainder`; the layers occurring are <= p in VineEstFull).  L != 0.

## Open: steps 3 and 4.  READY is NOT claimed.  CHECKPOINT vineest-s4b: see PROGRESS.md top (exact local claim for K^T twist invariance and exact class-assembly statement, with the S1 import obstruction).

# HANDOFF vineest-s3 -- STEP 4b, SESSION 4b-3 (Sonnet 5.5): RowSizes ruling applied; STEP 1 (M1 / RowCoherent of twisted rows) DONE; steps 2-4 see PROGRESS.md top

## Change recorded for S2 (RULING on RowSizes)
`VineEstFull`, `VineEstFullPrime`, `VineEstCanon` now carry `(RD.garden hG).order <= P.N (p+1)^4` (TARGET L806-L810 standing garden-order bound) in place of `RowSizes ...`.
`RowOrder.lean`: `rowSizes_of_dataSize`, `rowSizes_of_order` (start), `rowSizes_of_state` (any state Bs and any assembly of its skeleton, from `Bs.layered.garden.order <= Nb`), `Reach.order_eq` (LF batches preserve the order via `FamilyBatch.order`).
`BaseCase.lean`: `step3_of_full` replaced by `Step3StatementOrd` (Step3Statement with the order premise), `step3Ord_of_step3`, `step3Ord_of_full`.  The induction base of S2 is `Step3StatementOrd` (from `Step3Statement` by `step3Ord_of_step3`).

## Step 1 (new modules, uni/src/VineEstS4/)
RowBridge, RowSum, RowCoh, RowCanon, RowStep, RowReach (descriptions at the top of PROGRESS.md).  Approach: (a) the native layered couple/tree inherits its layering from the reconstructed garden, so its incoherency index is the global link count (`incoherency_native_couple/_tree`), (b) rows are in bijection with regional pairs / interior branches (`step3D_M1`, `rowCoherent_iff` are chart-free), (c) a canonical reconstructed garden has all count-0 rows coherent, witnessed by the garden itself (`rowsCoh_of_canonical`; parent-core layers `pairQ`/`branchQ` = the clock-slot layers), (d) along `Reach` either nothing was applied or the state is canonical (`Reach.canonical_or_eq`); ordinary row counts are LF-invariant (`ordinaryCoupleLayers/ordinaryTreeLayers`) and the source exceptional objects are coherent, so `M1` does not decrease (`Reach.m1_ge`).
DEVIATION: `Reach.m1_ge` is `>=`, not `=` (the bound only needs `>=`).  `Reach.rowCoherent` holds for ANY assembly B1 of the reached region.

# HANDOFF vineest-s3 -- STEP 4b, SESSION 4b-2 (Sonnet 5.5): R31(2) invariants + P2.2 + P2.3 splitting lemma (see "Open" for what remains)

## Files (new, `uni/src/VineEstS4/`, all `module`, each < 360 lines)
AtomLayers, RealizationIso, AssemblyReach, TwistedKernelForm, TwistCohmol (R31(2), P2.2); SplitGeom, SplitGeom2, SplitDec, SplitFactor, SplitSummand, SplitKernel (P2.3).
`uni/build-s4b.sh` (fresh rebuild of all 19 Step-4b modules, output `ALL-OK`, 1m34s), `uni/validation/AxS4b2.lean/.log`.

## Decision on the chart issue (ruling R31(2) addendum)
V4's `vineChain_eq_sumintForm'` is stated for EVERY chain assembly B, so P2.2 applies it to the iterated twist B1 of the source assembly with B1's own default VINEPARAM charts: no chart transport and no generalization of V4 to arbitrary charts was needed.
Every R31(2) invariant is proved chart-free: `b` depends only on vine types (`nor i = !IsBad`), the cohmol groups are intrinsic (`realizedGroupSets_eq`) and transported along the actual garden isomorphism, the atom layers are preserved (`LFConstruction.coreLayers`).

## Results (exact names)
* `AsmCorr B0 B1 e` (AssemblyReach): the pieces of two assemblies correspond under a branch bijection e (same vine type, atom sets by e, joints by e, and the cohmol group sets correspond under `Finset.image e`).  `AsmCorr.twist`: one unit twist of an assembly (`CLChainAssembly.twist`).  `Reach.exists_asm`: along any `Reach` the source assembly of the start region is carried to an assembly B1 of the reached skeleton and region, with e c.a = c'.a, e c.b = c'.b, the region by e, and the atom layers (`atomLayer` with `stateLayer`) preserved.
* P2.2 `twistedKernel_sumintForm` (TwistedKernelForm): at any reached state the recentered twisted kernel (factor e^{-pi i delta L^{2 gamma} t0 Gamma} with the sign of the START garden times `twistedLocalKernel Bs c'`) is V4's sumint form for B1 with the data `(Bs.data, stateLayer Bs)`; `recentered_twisted`, `Reach.sign_a` (the sign of the upper joint is unchanged: `coreBranchEquiv_sign`, lower joint != a).
* R31(2): `bad_card_eq` (b), `cohmolIndex_twisted` (vine part of n_(3)); n_(1), n_(2) from session 4b-1.
* P2.3 `clLocalKernel_split_sigma` (SplitKernel), exact statement at the top of PROGRESS.md.  Supporting: `order1_split`, `zeta_split`, `split_support`, `split_overlap`, `splitDecEquiv`, `domain_iff`, `summand_split`.

## Checks (exact)
* `./build-s4b.sh`: Region PrimeState Canon CanonStatement Invariants OrderCore OrderStep AssemblyTwist AtomLayers RealizationIso AssemblyReach TwistedKernelForm TwistCohmol SplitGeom SplitGeom2 SplitDec SplitFactor SplitSummand SplitKernel, all `exit 0`, `ALL-OK`.
* `validation/AxS4b2.log`: `#print axioms` of AsmCorr.twist, Reach.exists_asm, atomLayer_step, Reach.sign_a, recentered_twisted, twistedKernel_sumintForm, bad_card_eq, groups_of_corr, cohmolIndex_twisted, split_support, split_overlap, splitDecEquiv, domain_iff, summand_split, order1_split, zeta_split, clLocalKernel_split_sigma: all `[propext, Classical.choice, Quot.sound]`.
* Hygiene grep `sorry|admit|axiom|opaque|unsafe|maxHeartbeats|set_option` over the 11 new files: no hits.

## Findings (read these)
* FINDING (RowSizes is not LF-invariant as stated). `LFConstruction` fixes only the COMBINED order `newTree.size + newCouple.size`.  Hence at a twisted garden the two exceptional regular objects satisfy `size/2 <= 2*Nb` (not `<= Nb`) from the source `RowSizes ... Nb`.  TARGET's actual standing bound is on the TOTAL garden order `n <= N_{p+1}^4` (TARGET L806-L810), which the LF twist preserves (`FamilyOperation.output_order`).  Recommendation: the premise of `VineEstFull` should be the garden-order bound (then every row of every twist satisfies it), not `RowSizes` of the source.
* The recentering factor of (vineest1) uses the sign of the ORIGINAL upper joint; it equals the sign in every twisted garden (`Reach.sign_a`).
* In the split, the epsilon and phase factors of the joint `b` belong to the lower block `T` (its summand includes the upper joint), not to the upper block `S`; TARGET (tildeJ2) is written that way (the explicit S-part product stops before b).

## Open (not done in this session)
1. M_1 = sum of the row incoherency indices (the second part of n_(3)), RowSizes and RowCoherent of the twisted rows.  Plan: (a) bridge `layerAt (nativeCoupleLayered D hG layer hLayer p) (i, r) = layerAt (layeredReconstruction ..) (addrExt (coupleRoot D hG p i) r)` (nodeEmbedding of `twoRootSubforest` is `root ++ path`) and the analogue for `nativeChainLayered`; (b) `incoherency_eq_count_of`; (c) ordinary rows: `LFConstruction.ordinaryCoupleLayers/ordinaryTreeLayers`; (d) exceptional rows: coherent on both sides (source: `FamilyOperation.coupleCoherent/treeCoherent`; output: `CoherentCoupleInsertion.pattern`, `OutAgree`); then M_1 is equal and RowCoherent follows from `IsCoherentCoupleAt` witnessed by the output canonical garden.
2. (B) Fubini form of P2.3: K^U = coupling^{n_1(S)} zeta_S * sum_{xS} int_{tau_S} spartS * K^T(tau_S(b), t1, t2; E(xS), F(xS), g, h).  Needs (count x volume) integrability of the summand as an explicit absolute-convergence hypothesis; measure-preserving equivalence `CLInternalTime RU ~ (S.erase a -> R) x (T.erase b -> R)`, and locality of `spart` in the clock (reads only the atoms of S and their parents).
3. (C) Twist invariance of K^T (the claim that K~^{U<p} is common to all unit twists at U^p): K^{T'}_{G_p}(t; E, F, g, h) = K^T_G(t; F, E, g, h) when the twist is at a vine of S (the sign of the upper joint of T flips, T is relocated by `coreBranchEquiv`).

READY is NOT claimed: items 1-3 are open.
CHECKPOINT vineest-s4b: see PROGRESS.md top.

# HANDOFF vineest-s3 -- STEP 4b (R31 + twisted-kernel sum form, session 4b-1, Sonnet 5.5): CHECKPOINT vineest-s4b (R31 done; P2.1 done; P2.2/P2.3 open)

## Files (new, `uni/src/VineEstS4/`, all `module`, <= 190 lines each)
PrimeState, Region, Canon, CanonStatement (R31(1)); Invariants, OrderCore, OrderStep (R31(2) n_(1), n_(2); R31(3)); AssemblyTwist (P2.1).
Infrastructure (not Lean sources of the packet): `uni/c3merge` (symlinks to universe SkeletonDraft oleans + SKELETON oleans + 43 rebuilt modules), `uni/c3src`, `uni/c3order.txt`, `uni/c3build.sh`, `uni/c3.sh`, `uni/build4b.sh`,
`uni/build-s4b.sh` (fresh rebuild, exit ALL-OK), `uni/run-ax4b.sh`, `uni/validation/AxS4b.lean/.log`, `COPIED-SHA256SUMS-c3`.
Nothing outside `uni/src/VineEstS4/{PrimeState,Region,Canon,CanonStatement,Invariants,OrderCore,OrderStep,AssemblyTwist}.lean`, these scripts, PROGRESS.md, HANDOFF.md was touched (backups `*.pre-s4b`). Universe, lftwist, stage1, vineest-s4c untouched.

## Results (exact names)
R31(1). TARGET `propstructure2` (L870) = SKELETON's `SkeletonDraft.SourceStructure.existsUnique_prime_with_replacements` (unique prime skeleton and unique replacement data; includes the L833 general-couple uniqueness). REG-STRUCT alone does NOT give it (its HANDOFF: "No C3
general-skeleton uniqueness claim"); the universe src omits SKELETON's C3 chain, so I imported it from <scratch>/skeleton and rebuilt the 43 modules downstream of `SkeletonDraft.PrimeGraph` against the universe's `PrimeGardenDefs` (one change: PrimeGraph's `IsPrimeGarden` def deleted in favour of `public import PrimeGardenDefs`, the two defs are identical).
* `batch_prime` / `prime_output` / `Reach.prime`: LF twists preserve a prime skeleton (`unitTwist_prime`).
* `eq_of_prime_layered`: two nodup-batch outputs from a prime-skeleton start with equal LAYERED garden are the same state (skeleton, family, data, layered). `Reach.region_unique`: they also carry the same transported region (order of the batch irrelevant; via `ChainAt.heq_of_raw`, `doubleBranch_comm`, `foldR_perm`).
* `canonReps_unique`, `classSection_eq_canonReps`, `canonReps_finite`, `canonFinset`, `classSection_canonFinset`, `classSection_eq`: exactly one canonical (state, region) per garden of the class and every `ClassSection` equals `canonFinset`.
* `VineEstCanon P` (CanonStatement.lean) is the literal TARGET form: extra premise `_hprime : IsPrimeGarden G` (TARGET's G is its skeleton, prime by definition; this is a source premise, not a conclusion-shaped one), sum over `canonFinset`, no section quantifier. `vineEstFullPrime_iff_canon`, `vineEstCanon_of_full`: the earlier forall-sections form (with hprime) is equivalent, so it is NOT stronger than TARGET. `VineEstFull` (no prime premise) is kept unchanged and implies both.
R31(2). `clLocalOrder1_twisted` (n_(1)) and `clLocalOrder2_twisted` (n_(2)) hold along any `Reach` (the twist keeps the interior size; regional leaf pairs transport `regional_iff`; the only changed data are the lower tree and the exceptional couple, equal combined order; the exceptional pair is regional on both sides `exceptional_internal`). NOT done: RowSizes, RowCoherent, n_(3), b, which are functions of a chain assembly: P2.1 `CLChainAssembly.twist` now gives the twisted assembly with transported pieces (`assemblyPieceAt_twist`: same vine types, atoms/joints by `coreBranchEquiv`) but `assemblyShape hM9 B'` also uses VINEPARAM-chosen charts of the twisted pieces; their shape equality with the source charts is unproved (open; needs chart shape determined by vine type and rung count).
R31(3). `slot_signs`: the slots (g,h) of `twistedLocalKernel` at any state of the class are the excluded children of the transported lower joint with sign +/- of the twisted garden's own signs (structure fields `CLRegionData.positive_sign/negative_sign`): exactly TARGET's footnote convention (L1431, "u21 = child of u2 other than u23 with sign +"), same variables (e,f,g,h) for every G'. TARGET Remark twistexplain (a)-(e) (L1447-1457) are consistent with this: (b) zeta_{u2} flips, all other signs fixed.
P2.1. Done as above. P2.2/P2.3: NOT done (see PROGRESS.md top for the exact next steps and the design observation about assembly order: U^{>=p} is an assembly prefix, U^{<p} the terminal sub-chain).

## Checks (exact)
* `uni/build-s4b.sh` fresh rebuild (new dir uni/buildS4b; the other VineEstS4 modules symlinked from uni/build): Region, PrimeState, Canon, CanonStatement, Invariants, OrderCore, OrderStep, AssemblyTwist all `exit 0`, ALL-OK. The 43 C3 dependents were freshly rebuilt by `uni/c3build.sh` (all exit 0, logs uni/c3logs).
* `validation/AxS4b.log`: `#print axioms` of batch_prime, eq_of_prime_layered, Reach.region_unique, canonReps_unique, classSection_eq, classSection_canonFinset, vineEstFullPrime_iff_canon, vineEstCanon_of_full, clLocalOrder1_twisted, slot_signs, Reach.order2, clLocalOrder2_twisted, CLChainAssembly.twist, assemblyPieceAt_twist, chain_twistedAtoms: all `[propext, Classical.choice, Quot.sound]`.
* Exact-type check (transient `example`, in validation/AxS4b.lean, compiled): `VineEstFull P -> VineEstCanon P := vineEstCanon_of_full`, `VineEstFullPrime P <-> VineEstCanon P := vineEstFullPrime_iff_canon P`.
* Hygiene grep `sorry|admit|axiom|opaque|unsafe|maxHeartbeats|set_option` over the 8 new files: no hits. No linter warnings in the 8 build logs.

## Uncertainties / deviations / errata
* Deviation: `VineEstCanon` adds the premise `IsPrimeGarden G` (see above); the statement of `VineEstFull` is unchanged.
* Environment finding (important for the port/landing): the universe `src` lacks SKELETON's C3 chain (`SourceStructure`, `PrimeSkeletonUniqueness`, `GeneralReconstructionUniqueness`, ...); importing it clashes with `PrimeGardenDefs` (both define `Reg.Skeleton.IsPrimeGarden`), which is why 43 modules were rebuilt. The landing must put one of the two on the main line.
* Environment finding: a NON-module probe file importing `VineEstS4.Class` loads `.olean.private`/`.ir` of the whole closure and fails with "failed to read file" because the process exceeds vm.max_map_count (65530); probes must start with `module`.
* TARGET reading: n_(2), n_(3), b in (vineest2) are those of G; the transport of n_(1), n_(2) shows the bound for G' is the same number. Whether n_(3)(G') = n_(3)(G) holds is not claimed (atom layers are preserved by `LFConstruction.coreLayers` and the cohmol groups are intrinsic, but the chart-based `cohmolIndex` of the twisted assembly is not related yet).
* No TARGET errata found in this step.
CHECKPOINT vineest-s4b: see PROGRESS.md top.

# HANDOFF vineest-s3 -- STEP 4a (statement + transport + base case), Sonnet 5.5: READY vineest-s4a

Files (all new, `uni/src/VineEstS4/`): RegionUnique (earlier), PieceFamily, InnerCL, Transport, Kernel, Class, Statement, BaseCase; validation `uni/validation/AxS4a.lean` (+ `.log`); fresh-build script `uni/build-s4a.sh` (dir `uni/buildS4a`, all 8 modules exit 0 in topological order).
Nothing outside `uni/src/VineEstS4`, `uni/validation/AxS4a*`, `uni/build-s4a.sh`, PROGRESS.md, HANDOFF.md was touched (backups `*.pre-s4a`). Universe, lftwist, stage1, vineest-s4c untouched.

## Result
`VineEstS4.VineEstFull P` (exact statement at the top of PROGRESS.md) and `VineEstS4.step3_of_full : VineEstFull P → Step3Statement P` (base case: with `CoreVinesNoTwist` the twist class is the singleton `{G}`). `exists_classSection` : sections exist for every start (non-vacuity). `clParentPattern_twistedAtoms_chain` is the requested inner-piece CL transport (`_inner` from `internalPositions_twist_other` at both joints; `_lower` for `b = P.lower` needs only `P.keep.succ ∈ internalPositions G U P.lower`, which follows from the piece placement by monotonicity).

## Approach
1. Family: `assemblySourceFamily B : SourceVineFamily G n` from `assemblyPieceAt` (vine, CL by `assemblyPiece_cl`, separation `assemblyPiece_separated` from `S ∩ T = {b}`); its `.coreFamily` over `CoreIndex` is exactly TARGET's "each vine in U that is core". `startState B RD hG layer hLayer : FamilyReconstruction` has skeleton G, data RD, layered = `layeredReconstruction`.
2. Transport: `ChainAt S F` = connected CL region (U,a,b) with `atoms_sub` (every family member inside U) and `lower_ne` (every lower joint ≠ a). `ChainAt.next` transports along a unit twist (twistedAtoms/coreBranchEquiv; CL by `_chain`; invariants via `CoreFamily.twist` and `nextPlacement_lower`). `Reach` = `FamilyBatch` with the region carried; `batch_reach` : every batch transports (total, no hypotheses).
3. Kernel: `twistedLocalKernel Bs c` uses `clRegionData` from the region and the layering `stateLayer Bs` (unique by `layeredReconstruction_inj`; the layered garden equals the reconstruction by `existsUnique_decodes`). `regionData_subsingleton` is used in `twistedLocalKernel_start`.
4. Sum over gardens: `ClassSection` (Finset of (state, region) pairs, batch-reached, `layered` injective, image = `allCoreOutputs`, which S1's `congruent_layered_iff` identifies with the congruence class). The exponential e^{-πiδL^{2γ}t_{u1}Γ} is factored out front with the ORIGINAL sign `G.sign a.toNode` (as in (vineest1)); `clRecenteredLocalKernel = exp * clLocalKernel` unfolds to it.

## Checks run (exact)
* `./build-s4a.sh VineEstS4.<M> buildS4a` for RegionUnique, PieceFamily, InnerCL, Transport, Kernel, Class, Statement, BaseCase: all `exit 0`.
* `./probe.sh validation/AxS4a.lean`: `#print axioms` of step3_of_full, exists_classSection, clParentPattern_twistedAtoms_chain/_inner, assemblyPiece_separated, batch_reach, twistedLocalKernel_start, classSection_start, regionData_subsingleton, layeredReconstruction_inj, VineEstFull: all `[propext, Classical.choice, Quot.sound]`.
* Hygiene grep `sorry|admit|axiom|opaque|unsafe|maxHeartbeats|set_option` over `uni/src/VineEstS4`: only the word "admits" in a docstring. Largest file 117 lines.
* Exact-type check: `step3_of_full` is literally stated `VineEstFull P → Step3Statement P`.

## Uncertainties / deviations (read these)
* INDEPENDENCE NOT PROVED, by design. The brief asks for uniqueness of (skeleton, reconstruction data) of a layered garden, or distinctness of twist outcomes, to be proved if needed. In this universe a `FamilyReconstruction` carries an arbitrary plain skeleton `S` and `ReconstructionData` decoding to the layered garden; `Decodes` only forces the decoded garden (`existsUnique_decodes`), and `S` is NOT required to be the maximal collapse of the regular objects (the TARGET `G_sk`). So two states with equal layered garden but different (S, data) are not excluded by anything in the tree, and their kernels `K^U_{(G')}` (different n_(1), native objects) need not agree syntactically; I did not find a proof or a counterexample. To avoid assuming it I quantified over ALL sections (one state per garden): `VineEstFull` is then stronger than or equal to TARGET's statement and equal if independence holds. Consequence for P2/P4: the induction must work with any section (it organizes naturally by the skeleton-subset T of `skeleton_subset`, but then needs either independence or the section to be chosen with `B.familyState = familyBatch T`). The skeleton-level count `SourceVineFamily.twists_ncard = 2^|core|` (universe) already says distinct subsets give distinct skeletons; the missing step is skeleton recoverability from the decoded garden.
* `CanonicalObject` is not a hypothesis of `VineEstFull` (Step3Statement has none). For a non-canonical start every `FamilyOperation` is impossible (`canonical` is a field), so the class is `{G}` and the statement reads as Step 3; `allCoreOutputs_finite` is proved in both cases. TARGET's G is canonical, so this is a harmless extension.
* The premises RowSizes, RowCoherent, `clLocalOrder1 R ≤ N_1^4` and the bound's constants (`cohmolIndex`, `M₁`, `clLocalOrder2`, `b`) are those of the SOURCE garden (same as Step3Statement, needed for `step3_of_full`). TARGET's `n_(2)`, `n_(3)` for G' may differ from G's when the twist changes the regular objects in U; whether the source values bound all G' (or the bound must be per G') is a P2 question and may force the exponent/premises to be restated.
* `ChainAt.lower_ne`/`atoms_sub` are invariants I added to carry the transport; they hold at the start (`chainStart`: `lower_mem_interior`, `assemblyPiece_subset`). The region of a state is determined by `Reach`, never chosen.
* Kernel slot convention: `clLocalKernel`'s four momentum slots are labelled by the CL region data of G' (positive/negative children by sign), as for G; I did not check that these agree with TARGET's u_21/u_22 labelling after a twist at the lower joint (it is the same convention as the single-garden Step 3).
* Errata: none found in TARGET in this step. TARGET L1737 "satisfies the assumptions in Definition lftwist" is read as `FamilyOperation` (canonical + source layer eligibility + both coherences), matching S1/M7.
# HANDOFF vineest-s3 -- STEP 4 (session S4-1, Sonnet 5.5): CHECKPOINT, groundwork only
Read: AGENTS/COMMON/SONNET-COMMON, RULINGS R2,R8,R10,R13,R20,R22, HANDOFF 0/8, PROGRESS, TARGET L1724-L1935 (Prop vineest Steps 1-4), LFTwist/Twist/S1 APIs.
Done: `uni/src/VineEstS4/RegionUnique.lean` (`regionData_subsingleton`), compiled, axioms [propext, Classical.choice, Quot.sound], no sorry.
Not done: `vineestFull` statement, transport, twisted-kernel sum, Step 4 analysis. See top of PROGRESS.md for design and plan P1-P4.
TARGET reading notes (no erratum found): the induction/factorisation of K~^{U<p} (L1877-1883) and the case split L_u3 vs L_u4 (L1909-1923) were read and appear coherent; not yet formalised, so not verified.
Nothing was edited outside uni/src/VineEstS4, PROGRESS.md (backup PROGRESS.md.pre-s4), this file.
# HANDOFF vineest-s3 -- SESSION 8 (V5 part 1, TARGET `vineest` Step 3, no twist) -- READ THIS SECTION FIRST

Environment: `uni/` (universe-ported tree). `uni/run.sh VineEstS3.Step3Prefix` = DONE 458 bad 0 (log `uni/drv.out`); fresh rebuild in `uni/buildS8` (log `uni/drvS8.out`, see 8.6).
Read-only external build dirs on LEAN_PATH (build.sh, probe.sh, drv.py): `<scratch>/vineparam-groups/build` (sha256s in that dir's `FINAL-SHA256SUMS`; `Contract.lean` sha cd16890b... identical to uni's) and `<scratch>/vineparam/current/build`.
Copied sources (sha256 in `uni/COPIED-SHA256SUMS`): CONJ-COH `NormSwapConj, CodeConj, CodeConjPairs, GardenConj, ConjCanon, ConjEmbed, ConjCoherent, CoupleRowConj, PL234Draft/P4KConj`.
Originals of every edited V4/V5 file: `uni/port-orig/*.s7pre-align.lean`, `NativeRows.s8pre-conj.lean`, `LayerFacts.s8pre-conj.lean`, `Step3Prefix.s8pre-cohmol.lean`, `ChainChartIndexing.v4-pre-normalize.lean`, `M9ChosenChart.v4-pre-normalize.lean`.

## 8.1 What was done (brief steps 1-5)
1. **Aligned enumerations** (all compile, no sorry).
   * `VineEstS2/CLOrderedRows.lean`: `structure CLIntOrder hU R` (`e : interior ≃ Fin n1`, `prev` : predecessor-monotone); `clInteriorEnumeration` is now the default `CLIntOrder`; `clPairEnumeration` the default pair bijection.  The orders `Ei`/`Ep` are explicit arguments of `clOrderedPrev/Budget/BranchValue/PairValue/Coeff/BranchBond/PairBond`, `clSourceOriginValue`, `clRealizedNode_sourceOrigin`, `clBond_sourceOrigin`, `clOrigin_sourceOrigin`, `clRealizedNode_interiorOrigin`, `clBond_interiorOrigin`, `clOrigin_chartSourceTag`, `clOrdered_predecessor_identity(_local)`, `clOrdered_coeff_count_le`, `nodeOrigin(_spec)`; B-level files (CLSumintPredecessors/Rows/Matrices/MatrixValues, CLInverseMatrixApply/Data, CLStep2Momenta/Weights, CLCoordinate*, CLChartSourceAffineRows, CLNormalizedCoordinates, CLFrozenFormRows, CLAffineBoundaryRows, EpsLabels, Step3Facts) supply `assemblyIntOrder hM9 B` and `assemblyPairOrder hG B hM9`.
   * New `VineEstS2/CLAssemblyRowEquiv.lean` (`assemblyRowEquiv` split out + `assemblyRowEquiv_symm_lt`).
   * New `VineEstS3/RowAlign.lean`: `exists_sorted_equiv`; `clInteriorPredecessor_isDesc`; `assemblyPiece_lower_isDesc` (lower joints strictly descending along the chain); `assemblyBranchBij` (block `vineOf z`, decreasing depth in the block), `assemblyIntOrder` (key (vineOf, -depth); predecessor monotonicity from `vineOf_desc_le`); `vineAnchor` (pair of the retained leaf of a selected core placement `IsPlacementAt` at the lower joint of piece `i`, if regional), `vineAnchor_inj` (via `placement_pair_eq`: comparable lower joints + `paired_outside`), `exists_equiv_extending`, `assemblyPairBij`/`assemblyPairOrder` (anchor of vine `i` in block `i`).  New `VineEstS3/RowAlignRows.lean`: `vineOf_assemblyBranchOf`, `assemblyPairOf_anchor` (rows of block `i` carry branches of vine `i` / the anchor pair).
2. **Grouped charts and (e)**.
   * `VineEstS2/ChartNormalizeGroups.lean`: `chartAtomGroups_reindex`, `chartAtomGroups_normalizeChart`.
   * `chosenVineChart` / `chainPieceChart` now choose from the PROVED `vineparam_grouped` (`chosenRealization`), with `chosenVineChart_groups`, `chainPieceChart_groups`.  `hM9 : VINEPARAM` is kept as a (now vestigial) argument to leave all V4 signatures unchanged; it is provable (`vineparam`).  There were no V4 `obtain`s on `exists_physical_*` (V4 consumes only `hM9`); the grouped chain is used through its build dir.
   * `VineEstS3/CohmolBound.lean`: `cohmolIndex B RD hG layer` (= sum over the vines of `Vine.realizedIncoherencyIndex` of the chosen realization for the atom layer `v |-> layer (RD.coreBranch hG v).toNode`), `clockAtom_x/y/u`, `vine_cohmol_le` (uses `realizedIncoherencyIndex_le_chartGroups`), `cohmolIndex_le_M0`.  `Step3Statement` now has the exponent `-(eta^8 (cohmolIndex + M1)) - eta^2 b + eta^7`, TARGET's `n_(3)` (vine cohmol + regular objects); `step3_of_at` weakens from `M0 + M1` by `cohmolIndex <= M0`.
3. **BadClause** (replaced by the L1841 premise).
   * `BadGeom.lean` (`rung0_typeII`, `rung0_piece`: the normalized rung 0 is `{R.left, R.right}`, `parent b = R.left`); `BadClauseA.lean` (`badConstr`, `AClause`, `aClause_of_rung0`, `child_mem_rung`, `aClause_typeII`: a (II-e) vine, or a core type-II vine with `not(L_b <= min(L_left, L_right))`, satisfies clause (a): `t_right < t_b < t_left` from parent constraints and `layerOrderPairs`); `BadPlacement.lean` (`core_placement_internal`: selected placement with internal retained leaf); `BadClauseD.lean` (`CoreVinesNoTwist` = TARGET L1841 premise; `lower_mem_interior`, `vineOf_lower`, `exists_tree_row`, `vineAnchor_isSome`, `bad_d`); `BadClause.lean` (`canonBadKind`, `badClause_canon`).
   * `Step3Statement`: the premises `badKind`, `hbk`, `BadClause` are gone; new premise `CoreVinesNoTwist B RD hG layer hLayer`; the bad kind is `canonBadKind` (0 iff clause (a) holds, else 3).
4. **Orientation q < q'**: CONJ-COH consumed (`NativeRows.coupleRow_le` uses `ConjCoh.couple_row_le_both`); `CoupleEligible`/`RowCoherent` couple clause is `rowCoupleG = 0 -> IsCoherentCoupleAt p q q' ...` for both orientations.  No named inputs for orientation.
5. Final checks: below.

## 8.2 Premises of `Step3Statement` that remain (all TARGET-sourced)
`RowSizes` (n_rho <= N_{p+1}^4, L951), `RowCoherent` (regular couple/tree of incoherency index 0 is coherent, L946-L951 standing assumption), `clLocalOrder1 R <= N_1^4`, `CoreVinesNoTwist` (L1841).  `vineestStep3` still takes the three prefix statements `SumintMixSignedDoubled`, `CoherentApproximationGate30d`, `IncoherentDecayGate` (proved elsewhere).

## 8.3 Exact-type comparison with TARGET `vineest2` (L1742-L1752) and Step 3 (L1841-L1848)
Unchanged from 0.5 except: (i) exponent `n_(3)` is now literally `cohmolIndex + M1` (TARGET L1752 `n_(3)` = sum of all incoherency indices of the vines (cohmol, Def at L1489) and of the regular couples/trees); L1848 says `M0 + M1 = n_(3)`; we prove only `cohmolIndex <= M0` (enough, `L >= 1`); (ii) the case premise L1841 is stated as `CoreVinesNoTwist` (core = `IsCoreCLVine`; the twist assumptions = `SourceLayerEligible` and `CohOn` of the tree at `P.lower` and of the couple at `pairOfLeaf P.retained`, exactly the fields of `LFTwist.LFSource`); (iii) the bad kind is chosen canonically instead of quantified.

## 8.4 Uncertainties / deviations
* `hM9` vestigial (above).  * The cohmol realization is `Classical.choice` of `isVine_iff_realization`; independence of the choice is `realizedGroupSets_eq` (not needed).
* Anchors: the anchor pair of a vine exists only for vines with a selected core placement; bad vines are core or (II-e), and the (II-e) ones satisfy (a) (so need no anchor).
* TARGET L1846-L1847 reading (also in 0.4): for a core vine with `L_{u2} > min(L_{u3}, L_{u4})` the two constraints `t_{u3} < t_{u2}` (parent) and `t_{u4} < t_{u2}` come from DIFFERENT sources (parent bond vs. unit-interval order `q_{u4}+1 <= q_{u2}`, i.e. `layerOrderPairs`); the text says both follow from `u2` being a child of `u3` or `u4`.  Not an error of substance (step3W's domain carries the layer-order pairs; null-set lemma `DomainLayerOrder`).
* Hypothesis `hLayer`-dependence: none new.

## 8.5 Checks (exact)
* `uni/run.sh VineEstS3.Step3Prefix`: DONE 458 bad 0.
* `uni/validation/AxS8.lean` (module-mode import, `uni/validation/AxS8.log`): `#print axioms` of `vineestStep3, badClause_canon, bad_d, aClause_typeII, cohmolIndex_le_M0, core_placement_internal, assemblyIntOrder, assemblyPairOrder, vineAnchor_inj, vineOf_assemblyBranchOf, assemblyPairOf_anchor, ConjCoh.couple_row_le_both, chosenVineChart_groups, chartAtomGroups_normalizeChart`: all `[propext, Classical.choice, Quot.sound]`.
* Hygiene grep `sorry|admit|axiom|opaque|unsafe|maxHeartbeats|set_option` over `uni/src/VineEstS2, uni/src/VineEstS3` and the CONJ-COH copies: no matches.  All new files < 350 lines.
* Source readings: TARGET `WKE-Longer_times_Final_arXiv.tex` L1489 (Def cohmol), L1742-L1752 (Prop vineest, (vineest2)), L1841-L1848 (Step 3), L946-L951 (standing coherence).

# HANDOFF vineest-s3 (V5 part 1, TARGET `vineest` Step 3, no twist) — session 3 (Sonnet, continuing the plan)

## 0. SESSION 5 (Sonnet 5.5): steps (a), (d) done; (b), (e) blocked on an interface ruling; (c) q<q' open

Environment: the universe-ported tree `uni/` (`uni/run.sh VineEstS3.Step3Prefix` = DONE 432 bad 0; probe any file with `uni/probe.sh file.lean`;
LEAN_PATH = uni/build : universe/build : dev lake, see uni/build.sh).  Namespace `WaveTurbulence.VineEstS3` (+ `.Eng`).

### 0.1 What changed in `Step3Statement` (final form, `VineEstS3/Step3Prefix.lean`)
* `qOut` is no longer a free parameter: `qOutOf RD hG layer a b R = ![layer (core a), layer (attached (b.child positive)), layer (attached (b.child negative))]`.
* Layer facts of the rows (q, q' <= p; root layers <= q, q'; trees q' <= q; lone-leaf layer = q') are DERIVED (`LayerFacts`: `eligible_of`), from `IsLayering`,
  `core_child_position` (`attached_child_eq`), `LFTwist.inducedPrelayer_isBranchPrelayering` (`layer_core_le`) and `chainContextNode_lone`.
* New premises (documented standing data, TARGET L946-L951, L1724ff): `RowSizes` (n_rho <= N_{p+1}^4), `RowCoherent` (a regular couple/tree of incoherency index 0 is coherent, i.e. `IsCoherentCoupleAt`/`IsCoherentTreeAt`,
  and for couples q' <= q), `clLocalOrder1 R <= N_1^4`, `BadClause`.
* `hb1 hb2` (the excluded lower children are branching) are GONE: leaf lower children are proved (see 0.3).
* The constant: `P.C1 = finalCstar d eta c0 = traceR eta * numCstar ..`, `traceR eta = (traceConst(2 eta^8, chi0)^2).toReal` (cost of the two time traces).
* `vineestStep3 : SumintMixSignedDoubled -> CoherentApproximationGate30d -> IncoherentDecayGate -> WTPrefix Step3Statement`, axioms [propext, Classical.choice, Quot.sound].

### 0.2 New modules (all `module`, no sorry; hashes via `sha256sum VineEstS3/*.lean`)
`LayerFacts` (step a), `LeafChild` (kernel independent of a leaf child's time; V4's `integral_clockDomain_eq` / `vineChain_eq_sumintForm` / `kernel_eq_clockedExprEps` without hb1/hb2),
`TraceBox` (`XNorm00Restr_trace`, cube-uniform; Regref `mixedRestrictionNorm00_trace_le` from the dev lake + `XNorm00_shift` copied from RegrefDraft.NormShift; geometry `update_mem_closure_interior_outBox`),
`LeafTrace` (`XNorm00Restr_leaf`: Tietze extension from the closed cube + one trace per leaf child, factor traceConst^2), `ClockedCont` (`continuousOn_clockedExprEps`, `continuousOn_timeDom_integral`),
`PointwiseDecay` (`norm_le_decay_of_XNormRestr`), `LeafWire` (`rows_clock_mem_cube`), `Step3AtLeaf` (`step3AtLeaf`).  `OrderZeroFromMixed` (lg-spine) was repaired for the snapshot-9 `XNorm` guard (uni/src; original in uni/port-orig).

### 0.3 Step (d) mathematics (leaf lower child)
TARGET Step 3 (L1826-L1870) and `sumint` impose t_0^1 > max(t', t''); for an excluded lower child that is a LEAF the kernel K^U does not depend on its time (`clLocalClock_congr`, CLLocalKernel L47-L53 doc), the true domain is larger.
Route: evaluate the effective kernel at t' := qOut 1 (lower end of the unit interval; qOut 1 <= q_b by `qOutOf_one_le`, so tau_b > q_b >= t' by the strict window), where the source domain equals the sumint domain a.e.
(`integral_clockDomain_eq'`); the extra dependence is removed by the order-0 time trace (continuity of the clocked expression on the closed output cube, `continuousOn_clockedExprEps`).  Cost traceConst(2 eta^8)^2 (<= 2 traces), absorbed in C_1.
ERRATUM CANDIDATE (TARGET L1846-L1848 and sumint L1612, (ii)): the domain condition t_0^1 > max(t',t'') is not the actual domain when u_21 or u_22 is a leaf; a trace estimate (or a dummy-time convention) is needed.

### 0.4 What is NOT done, and exactly why
* (b) `BadClause`.  BLOCKED by the M9 interface, not by analysis.  (i) `FullVineChart` (Contract.lean) pins `atom x0 = b` but not WHICH rung is rung 0: `BadClause` (a) needs the chart's rung 0 = the end rung (p,q) of
  `Molecpl.IsTypeIIE`/`EndRungData` adjacent to `b` (p parent of b, b parent of q; TARGET names t_1 = t_{f_4}, s_1 = t_{f_3}).  An arbitrary chosen chart (V4's `chosenVineChart` = Classical.choice) need not have that numbering,
  so (a) is not derivable.  Proposed amendment of VINEPARAM (a field of `FullVineChart`): `firstRung_adjacent : X = .II -> forall h : 0 < shape.m, bondsBetween b (atom (xSlot 0)) = 1 /\ bondsBetween b (atom (ySlot 0)) = 1`.
  (Alternative without amending: reorder rungs in `assemblyChartAt`: needs that the end rung pair is a chart rung -- degree-4 count with `rung_bonds` -- and a garden-level CL pattern per piece for `molecpl_typeII`.)
  (ii) the layer-failure case (core vine, L_{u2} > min(L_{u3}, L_{u4}), TARGET L1846-L1847) needs t_{u4} < t_{u2} which is a unit-interval fact (t_{u4} <= q_4+1 <= q_2 < t_{u2} a.e.), NOT a parent constraint; `W.constraints` is
  `assemblyTimeConstraints` (V4's `vineChain_eq_sumintForm` needs `hc`), so either `W.constraints` gets the layer-order pairs (null-set domain change, new lemma) or `sumint` clause (a) accepts the q-order.
  (iii) clause (d) needs `rowCoupleG/rowTreeG >= 1` from `not (CohOn ...)` of `LFTwist.LFSource.treeCoherent/coupleCoherent`: the dictionary between `LayeredGarden.incoherency` of the native rows and `CohOn` is not in the tree and the slot of T_{u2}/Q_{(u23,u0)} must be identified.
  The TARGET case premise (L1841) would read: for every core vine i, for every `P : CorePlacement G` with `IsPlacementAt`, `not (SourceLayerEligible LG D hS hd P X T a /\ treeCoherent /\ coupleCoherent)` (LFTwist/SourceExpandedUnit.lean L22, LFSource.lean L29-L36).  Not added, since it cannot be consumed.
* (e) `n_(3)`: `D.M0 + D.M1`.  `M1 = sum (g + g')` is the regular-objects part.  `M0` counts the chart groups {xSlot j, ySlot j} (rung pairs) and {uSlot 0,1,2}; the cohmol index is `Vine.realizedIncoherencyIndex R layer` (VineCoherence.lean) over a `VineRealization`.
  Equality needs the chart's groups = the realization's groups (as atom sets: `Vine.realizedGroups`), which `FullVineChart` does not carry.  Proposed field: `groups_eq : exists R : VineRealization M X S a b, (realizedGroups R).map List.toFinset ~ chart groups`.
  (Inequality `cohmol <= M0` would already suffice for the exponent -eta^8 n_(3).)
* (c) the q < q' orientation of coherent couples: `PL234.KQstar_conj` (P4KConj.lean L323: `KQstar LH t s k = star (KQstar LG s t k)`, `IsConjugateCouple`) is available, but nothing in the tree gives (1) invariance of `XNormRestr` under (coordinate swap + complex conjugation),
  (2) the conjugate object `Q^c` with `Decodes`, `size`, `incoherency` and `IsCoherentCoupleAt p q' q`, so `RowCoherent` still demands `q' <= q` and `IsCoherentCoupleAt p q q'` (the 0814 gate is stated for q' <= q only).  Exact steps: swap/conj lemma for `XNorm`/`XNormRestr`; conj-coherence of `IsCoherentCoupleAt` (CoherentConjugacyData); then `couple_row_le_conj`.

### 0.5 Exact-type check of the final form against TARGET `vineest2` (L1742-L1752)
TARGET: `||1_{H_{u1}}(k_{u1}) .. 1_{H_{u22}}(k_{u22}) K~^U||_{X^{2 eta^8,0,0}(B)} <~_1 (C_1 sqrt(delta))^{n_(2)} L^{-eta^8 n_(3) - eta^2 b + eta^7}` (L1748), `B = {t_{u1} > max(t_{u21},t_{u22})} ∩ prod [L_x, L_x+1]` (L1745-L1746),
`K~^U = e^{-pi i delta L^{2 gamma} t_{u1} Gamma} sum_{G'} K^U_{(G')}` (L1743, over LF twists G' of G at U), fixed `w` with `k_n - w ∈ Z_L^d` (L1744).
Lean (`Step3Statement`): norm `XNorm00Restr (2 η⁸)` over `outBox D` = {tt : qOut c <= tt c <= qOut c + 1, max (tt 1) (tt 2) < tt 0} (= B, with qOut = layers: `qOutOf`);
vector variables `E ∈ outSet D L γ η` = boundary vectors `w + Z_L^d`-valued with `E 0 - E 1 = E 3 - E 2` in unit balls around `centre` (the uniform sup over unit balls is the `centre` parameter), `r ≠ 0`, `|r| <= L^{-γ+η}` (the sumint output set, not literal TARGET: it is the domain of the consumer);
bound `ofReal ((C₁ √δ)^{n_(2)} L^{-η⁸ (M₀+M₁) - η² b + η⁷})` with `n_(2) = clLocalOrder2` (V4: n_(1) + sum of the orders of the native objects = TARGET n_(2) = n_(1) + n_(0), L1848),
`b = card {i : not nor i}` = |Bad|, `M₀ + M₁` = `n_(3)` modulo (e).  DEVIATIONS: (1) kernel = the single-garden recentered kernel `clRecenteredLocalKernel` (the no-twist case, Step 3, L1826-L1848), not the LF-twist sum (vineest1) -- Step 4 (L1850ff) is the twist case and is not in this packet;
(2) `ε` kept (DEGEN-VINE, R13); (3) `BadClause`, `RowCoherent`, `RowSizes` are premises (above); (4) the constant `C₁` is chosen large (TARGET: "C_1 an arbitrary large constant"), and the prefix form `WTPrefix` supplies `C_2, L`.


Scratch `<scratch>/vineest-s3`, namespace `WaveTurbulence.VineEstS3` (+ `.Eng`, `.FS`), modules `VineEstS3.*`, copies in `src/`.
Previous sessions' handoff (engine, FS route, sumint): `validation/HANDOFF-previous-sessions.md` (still valid).
**Single environment** (new): `build-v4.sh` (dev) / `build-g.sh` (fresh, dir `buildG`): V4 snapshot-9 closure (`vineest-s2/snap9`) + engine + DEGEN-VINE light
modules + gate chain + PL23-30D tensor lemmas, all in ONE `LEAN_PATH`.  Fresh rebuild: `./fresh2.sh VineEstS3.Step3Prefix` (log `logsG/EXIT.txt`).

## 1. Result (what is proved, with exact names)

`Step3Prefix.lean` (no sorry, standard axioms):
```
theorem vineestStep3 (hS : SumintMixSignedDoubled) (hG : CoherentApproximationGate30d) (hI : IncoherentDecayGate) :
    WTPrefix Step3Statement
```
* `Step3Statement P` = the bound (vineest2) of TARGET Prop `vineest` (L1742-L1752) in the no-twist case (Step 3, L1841-L1848) for
  V4's recentered kernel `clRecenteredLocalKernel` (= `\widetilde K^U_{(G)}`, `n_(1) = clLocalOrder1`, with `ε`), as a function of the output times
  `tt = (t,t',t'')` and of the boundary vector in the `sumint` convention (`sumintBoundary ζ`), norm `XNorm00Restr (2η⁸)` over the `sumint` output
  box/set `outBox D`, `outSet D L γ η` (unit balls with centres/`w̲` as parameters, `r ≠ 0`, `|r| ≤ L^{-γ+η}`, as in `sumint`):
  `≤ ofReal ((C₁√δ)^{n_(2)} · L^{-η⁸(M₀+M₁) - η² b + η⁷})`, `n_(2) = clLocalOrder2 = n_(1) + Σ sizes`, `b = |{i : ¬nor i}|`, `M₀+M₁ = D.M₀ + D.M₁`.
* Hypotheses (the three named obligations, all stated as prefix statements):
  * `SumintMixSignedDoubled` = `WTPrefixA SumintMixDoubledAt`: `sumint` with the `ε`-character mixtures at `δ' = 2δ` (DEGEN-VINE).  **Proved unconditionally in
    `degen-vine`** (`DegenVine.sumintMixSignedDoubled`, heavy env).  `validation/DischargeSumint.lean` (run `./dischargeSumint.sh`, heavy env) checks
    `example : SumintMixSignedDoubled := sumintMixSignedDoubled`, axioms `[propext, Classical.choice, Quot.sound]`.  The statement's defining modules
    `src/DegenVine/{SumintMixDoubled,ScaledSumintMix}.lean` are byte-identical (`cmp`) to degen-vine's.
  * `CoherentApproximationGate30d` = `WTPrefix CoherentGateAt`; body text-identical (whitespace-normalised, checked by script) to the 0814 pin
    `<scratch>/pl234/pinned/SpineInputs.lean.0814` (sha256 54637750...003f).  Proved by PL23-30D from the two B2.1 gates.
  * `IncoherentDecayGate` = `WTPrefix IncoherentGateAt`; body text-identical to the frozen anchor `Frozen/Theorems/IncoherentDecay.lean` (B2.2, sealed).
* The remaining hypotheses are INSIDE `Step3Statement` (typing/standing data of Section regred, TARGET L946-L951, L1724ff) — **see section 3, they are the open items**.

### Proof architecture (all in `VineEstS3/`)
1. `AssemblyClocked`: `assemblyClocked : ClockedRows (sourceSumintDatum hM9 B hG W)` (rows `K_Q^*` with clock pair = parent clocks of the two leaves, `K_T^*` with
   (parent clock of the branch, its own clock); slots from V4's `node_parent_slot`/`branch_clock_slot`); `clockedIntegrand_assembly` (= V4 integrand with `assemblyWK/WL`).
2. `EpsLabels`: V4's `ε` is DEGEN-VINE's `epsOf`: `clRegionalEpsilon_eq_epsOf` (labels by `nodeOrigin`/`originLabel`; uses `clRealizedNode_sourceOrigin`,
   `assembly_pair_momentum`, `assembly_branch_momentum`, `epsMom_latticePoint`); `|U| = n_(1)+1` (`card_U_eq`).
3. `Step3Kernel`: `outSet_exists_beta`, **`kernel_eq_clockedExprEps`**: on `outSet` the kernel is `coupling^{n₁} ζ · clockedExprEps` (V4's `vineChain_eq_sumintForm`).
4. `Step3Engine`: `clockedBoundEps_cfs` = DEGEN-VINE's `clockedBoundEps_of_restr` with the Fourier-series constant an explicit function `CfsOf d η` (needed for the
   prefix bookkeeping; proof = degen-vine's with the witness moved to the front).
5. Gate matching: `GateDefs` (verbatim copies of `timeBox, timeBoxGt, InputRemainder, regBound` from B2 Statements sha 82e42b2b... lines 36-49 = Frozen defs, and
   `SourceSeparated`), `Gate30d`, `IncoherentGate`, `ThetaMono`, `SepBound` (`rN_sourceSeparated_le`, uses PL23-30D `restr_mul_w_le`, `restr_finsetSum_le`),
   `GateRows` (**`couple_row_le`, `tree_row_le`**: `‖K*‖_{𝔛^{6η⁶,30d,·}(box)} ≤ rowB P n g = cb C₁² (2C₁²δ)ⁿ L^{-(γ₁-√η)g}`; `g ≥ 1` by B2.2, `g = 0` by the 30d gate
   + triangle + separated bound), `NativeRows` (`CoupleEligible`, `TreeEligible`, `coupleRow_le`, `treeRow_le`), `BoxFacts`, `InputsSummable`, `TreeClockOrder`,
   `Step3Data` (`step3W`, `rows_clock_mem` = engine `hclock`, `rows_continuous` = `hcont`).
6. `AdmissibleAssembly`: `admissible_source` — the param-generic `Admissible` of the source datum (V4 algebraic clauses + layer bounds + `BadClause`; clause (iii)'s `match` handled by a case split).
7. `Step3At`: **`step3At`** (engine form at fixed `P`), `Step3Facts`, `NumericCore` (`numeric_core`), `Step3Final`: **`step3Bound_le`** (the engine bound is `≤ (C* √δ)^{n_(2)} L^{...}`,
   `C* = numCstar = 3 cc c0 c · 6 c1² cf² cb² c⁵ · √2`, polynomial in `c = P.C₁`).
8. `StepMono` (`LargeConstantMonotone` of `SumintMixDoubledAt A`, `CoherentGateAt`, `IncoherentGateAt`), `Step3Prefix` (`step3_of_at`, `vineestStep3`): the final `C₁ := finalCstar d η c₀`,
   `c₀ = max` of the three prefixes' `C₁`, the three at-statements hold at `{P with C₁ := c₀}` by monotonicity.

## 2. Environment finding (important for landing)
* V4's closure (flat `MoleculeDefs`, `WaveB2Draft.ParentDefs`...) and B2-final's `WaveB2Draft.Molecules`/`Statements` (the `universe/` world, `IsBlock` repaired F57) declare the
  same `Molecule.*` names and cannot be imported together; porting V4 to `universe` is a 301-module job (`/tmp`-style count: 301 of 708 closure modules missing there,
  first failure `RegRedDraft.CurrentBlocks` uses `Molecule.DegreeBlock`).  Used instead: `build4/WaveB2Draft/{Regular,RegularDefs,DominantDefs}` = symlinks to
  universe's `Regular` and its shims (V4's `RegularDefs` is sections 1-3 of `Regular` verbatim), V4's own `ParentDefs`; B2 `Statements` is NOT importable; its four needed defs are copied (`GateDefs`).
  Flat `Words/MultiIndices/TimeBridge/SpatialBridge` are shims onto `InductNorm*` (declaration-identical, `diff` checked) so that PL23-30D and `sumint-signed-fresh` coexist.
* Consequence: notions defined only in the B2-final/universe world (`core vine`, Def `lftwist`, `molecpl` (II-e), `cohmol`) cannot be stated here; this is exactly why section 3 (b) is a hypothesis.

## 3. What is NOT discharged (hypotheses of `Step3Statement`; please rule)
(a) **Layering/standing data**: `∀ x, layer x ≤ p`, `qOut c ≤ p`, `n_ρ ≤ N_{p+1}⁴` for the regular objects, `n_(1) ≤ N₁⁴`.  (`q,q' ≤ p`, the root layers `≤ q,q'`, `q' ≤ q` and the
    lone-leaf layer `= q'` inside `CoupleEligible/TreeEligible` are derivable from `IsLayering` + `core_child_position` + `chainContextNode_lone` but not derived yet; they also need `qOut 0 ≥ layer(core a)`.)
(b) **`BadClause`**: assumptions (a)/(d) of `sumint` for every bad vine, i.e. TARGET L1846-L1847 (non-core ⇒ II-e ⇒ `t_{u4}<t_{u2}<t_{u3}`; core with `L_{u2}>min` ⇒ (a); a non-coherent
    `T_{u2}`/`Q` ⇒ (d)).  Needs `core`, `lftwist`, `molecpl (II-e)` which live in the universe world.  I stated the exact `Admissible` bad-case clause (`BadClause D`) instead.
(c) **Coherent objects**: for incoherency index 0 the eligibility `IsCoherentCoupleAt p q q' Q LG` / `IsCoherentTreeAt` (embedding into the canonical garden, TARGET L899-L951, the standing
    assumption of Props 5.1/6.1) AND `q' ≤ q`.  The orientation `q < q'` (second leaf's parent in a higher layer) needs the conjugate object (`PL234.KQstar_conj`, layerregest9) — not done; such rows are excluded by the hypothesis.
(d) **`hb1 hb2`** (V4's): the two excluded lower children are branching.  For a leaf lower child the sumint time domain `{τ_b > max(t',t'')}` differs from the actual one unless the leaf's layer is strictly below `b`'s;
    my sketch (datum with `qOut 1 := 0`, evaluate at `t' = 0`, one order-0 trace, cutoff in `t'`) needs V4's `integral_clockDomain_eq` re-proved without `hb`; NOT done.
(e) **`n_(3)`**: stated as `D.M₀ + D.M₁` (V4/`sumint` definitions: layer-mismatched `(t,s)` pairs + `Σ(g+g')`); TARGET's `n_(3)` is "the sum of the incoherency indices of the vines (cohmol) and of the regular objects".
    The identification `D.M₀ =` vine incoherency index (cohmol) is a port-time check (cohmol lives in the universe world).  `M₁ = Σ(g+g')` with `g, g'` := incoherency indices of the native objects (`LayeredGarden.incoherency`).

## 4. Checks run (exact)
* FRESH rebuild of the closure of `VineEstS3.Step3Prefix` in a new dir (`buildG`), topological order, exit codes logged: see `logsG/EXIT.txt` (result at the end of this file).
  An earlier shell filter hid some error lines during development; the fresh rebuilds (`buildF` for the closure of `Step3Final`, 105 modules rc=0 errors=0, and `buildG`) are the authoritative check.
* `#print axioms` (validation/Ax3.lean, log below): `vineestStep3, step3At, step3Bound_le, step3_of_at, kernel_eq_clockedExprEps, clRegionalEpsilon_eq_epsOf, clockedIntegrand_assembly,
  couple_row_le, tree_row_le, numeric_core, admissible_source, incoherentGate_mono, coherentGate_mono, sumintMix_mono, clockedBoundEps_cfs, rows_clock_mem, rows_continuous, rN_sourceSeparated_le`:
  all `[propext, Classical.choice, Quot.sound]`.
* Hygiene grep `sorry|admit|axiom|opaque|unsafe|maxHeartbeats|set_option` over `VineEstS3/*.lean`: no hits; max file 258 lines.  Copies in `src/` carry only `set_option autoImplicit false`.
* Text identity: Gate30d body vs 0814 pin (True), IncoherentGate body vs frozen anchor (True), DegenVine copies vs degen-vine (`cmp` same, 13 files).
* Exact-type check: there is no pinned Lean statement for `vineest` yet (the frozen anchors are `sumint` and the Prop 5.1/6.1 gates).  `Step3Statement` is the statement; the transient checks that
  `vineestStep3`'s hypotheses are literally the three named prefix statements are `example`s in `validation/Ax3.lean`'s environment (hypothesis types are the definitions above).

## 5. Source readings (TARGET `WKE-Longer_times_Final_arXiv.tex`, grep -n numbering)
Prop `vineest` L1742-L1752 (vineest2 L1748); Step 3 L1841-L1848: replace `K*` by `√δ`-expansions (L1841), `(C₁√δ)^{n_(0)}(δ/2L^{d-γ})^{n_(1)}ζ[U]·I` (L1844), `ε → 1` (L1846), bad vines (a)/(d) (L1846), `M = n_(1), n_(2) = n_(1)+n_(0), |Bad| = b, M₀+M₁ = n_(3)` (L1848).

## 6. Errata and deviations
* E4 (TARGET L1846): `ε → 1` "by trivial summation" is insufficient for large `M`; handled by DEGEN-VINE's character mixtures (mass `3^{|U|}`), no `L^{-0.1γ₀}` gain is claimed or needed.  `3^{|U|}`, `K₀ = engineConst`, `Cfs`, `cc_η`, the row constants are absorbed in `C₁` by the C₁-shift (`finalCstar`).
* δ' = 2δ: the phase is `signedPhase` at `2δ` (V4); the engine and `Step3Statement` use `2δ` inside, `δ` in the kernel.
* The statement is over the `sumint` output set (`r ≠ 0`, `|r| ≤ L^{-γ+η}`, unit balls with parameters), not over the bare unit balls of (vineest2): this is the domain of `sumint` and of the consumer.
* `GateDefs`, `Gate30d`, `IncoherentGate` restate B2 defs in the V4 world (section 2); at landing they are the frozen defs.
* `C₁` in the conclusion is the prefix `C₁` chosen large (= `finalCstar` of the max of the three component constants), as TARGET's "`C₁` denotes an arbitrary large constant".

## 7. Results of the checks (appended after the final run)
* Fresh rebuild of the closure of `VineEstS3.Step3Prefix` into the new dir `buildG`: 109 modules, every line `rc=0 errors=0`, final line `ALLDONE` (`validation/fresh-rebuild-EXIT.txt`, logs `logsG/`).
* `validation/Ax3.log`: the 18 `#print axioms` lines all read `[propext, Classical.choice, Quot.sound]` (no `sorryAx`).
* `validation/DischargeSumint.log` (heavy env): `sumintMixSignedDoubled` axioms `[propext, Classical.choice, Quot.sound]`; the `example` against `SumintMixSignedDoubled` compiles.

## 8. Exact next steps (for the orchestrator's ruling / a successor)
1. Ruling needed on (b) `BadClause` and (c) coherent-object eligibility: either accept them as named obligations of the V5 consumer (they are TARGET L1846-L1847 and the standing assumption L946-L951), or port V4 onto the `universe` world
   (then Def `lftwist`, `molecpl`, `cohmol` and LG-SPINE's embedding are available and (b),(c),(e) can be proved).
2. (a): derive `q,q' ≤ p`, root layers `≤ q,q'`, `q' ≤ q` (trees), lone layer `= q'` from `IsLayering`, `core_child_position`, `chainContextNode_lone` (make `nodeSlot`/`branchSlot` explicit `atomEquiv.symm` slots first), and add `qOut 0 ≥ layer (core a)`.
3. (d): leaf lower children — re-prove `integral_clockDomain_eq` without `hb1/hb2` using the sketch in section 3 (d).
4. Conjugate orientation `q < q'` of coherent couples via `PL234.KQstar_conj`.

## 9. SESSION 6 (R20 follow-up) -- results and STOP reasons
Fresh rebuild buildF5 of Step3Prefix: DONE 432 bad 0.  New compiled modules (sha256): ChartReindex a3ac5c60..., ChartNormalize adacbf93..., ChartNormal fe9e28cf..., DomainLayerOrder dd50660e...
(axioms propext/Classical.choice/Quot.sound; no sorry).
Step 1: chart re-indexing + adjacency proved from rung_bonds, EndRungData degree-4 rows (no contract amendment).  BUT V4 consumes `Classical.choice` of a Nonempty
(chosenVineChart, chainPieceChart), proof-irrelevant, so the normalized chart can only enter by wrapping those two defs in `normalizeChart` (V4 edit, rebuilds ~300 modules).
Step 2: null-set lemma done; the `hc` hypotheses (TreeClockOrder, Step3Data, LeafWire, Step3Kernel, LeafChild) would need weakening to subset + layer-order.
STOP reasons (steps 3/4/6):
(A) Clause (d) per vine is NOT derivable: Admissible needs j in vine i with max(g,g')>=1, but rows (i,j) carry pair/branch via clPairEnumeration/clInteriorEnumeration (Fintype.equivFin / Classical.choose depth order),
    not aligned with vines; the incoherent T_b / Q_(u23,u0) may sit in another vine's slot.  Fix needs aligned enumerations (pairs: free bijection; branches: key (vine, -depth), needs child-of-v lies in vine <= vine(v)).
(B) n_(3)=cohmol <= M0+M1 NOT derivable for normal vines: chart rung pairs are only doubled pairs; realized triples (types III-VIII) contain a doubled pair, so FullVineChart does not force chart groups = realized groups
    (works for bad types I,II: every interior atom is in a doubled chart pair and realized groups have size 2, so groups coincide).  Needs a contract field (groups_eq) or a classification.
Both need rulings (they make step 1's V4 edit moot if the contract gains an adjacency field).  Step 5 (orientation) not started; planned premise: g=0 -> (q'<=q and coherent) or (q<q' and exists conjugate coherent at (q',q)), via PL234.KQstar_conj.

## 7b. Session 7 check record
* buildF5 (uni/buildF5, log uni/drvF5.out): fresh rebuild of VineEstS3.Step3Prefix = DONE 432 bad 0.
* Session 7 R22(1): copied-V4 divergences (uni/src, originals in uni/port-orig/*.v4-pre-normalize.lean): VineEstS2/M9ChosenChart.lean (chosenVineChart := normalizeChart (choice ..), + import ChartNormalize) and VineEstS2/ChainChartIndexing.lean (chainPieceChart likewise). Rebuild `uni/run.sh VineEstS3.Step3Prefix`: DONE 434 bad 0 (no proof repair needed).

## 8.6 Fresh rebuild
`BD=buildS8 ./drv.py VineEstS3.Step3Prefix` (new dir uni/buildS8, topological order, log uni/drvS8.out): 458 modules, every line `exit 0`, final `DONE 458 bad 0`.

## Session 4b-3 addendum (Fubini, partial)
SplitTime, SplitLocal, SplitFubini compiled (exit 0, no sorry).  `clLocalKernel_split_fubini` holds under the explicit premise `AbsConv`; discharging `AbsConv` from the kernel bounds, K^T twist invariance and (tildeJ2) remain OPEN (see PROGRESS.md top).  No fresh rebuild / axiom run was done after these modules; READY is NOT claimed.

## V5-CONT EXPORT (v5-cont, READY)
Files `uni/src/VineEstS5C/Cont/{Core,Member,Class,ModKernel,ModCore,ModClass,Export}.lean` (1168 lines, namespace `WaveTurbulence.VineEstS5C.Cont`), build `uni/build5c5.sh VineEstS5C.Cont.<M>` into `uni/buildS5C5` (farm `uni/farm5c5.sh` over buildS5C4 and buildS5C). Fresh rebuild of all 7: exit 0; axioms of `twistedRecentered_continuousOn`, `twistedRecenteredModC_continuousOn`, `twistedRecenteredModC_zero`, `clRecentered_continuousOn`, `profileBound_of_snorm`: propext, Classical.choice, Quot.sound; hygiene grep clean.

**Exact statement (kind = true, `Cont/Class.lean`).**
```lean
theorem twistedRecentered_continuousOn {P : WTParams}
    (hgate : CoherentGateH P) (hinc : IncoherentGateH P)
    (hd : 1 ≤ P.d) (hη0 : 0 < P.η) (hη6 : 6 * P.η ^ 6 ≤ P.η) (hη2 : P.η ≤ 1 / 2)
    (hC : 1 ≤ P.C₁) (hδ : 0 < P.δ) (hL : 1 ≤ P.L) (hw : 0 ≤ P.gamma1 - Real.sqrt P.η)
    {p : ℕ} (hp : p < P.D) {h : ℕ → Mom P.d → ℝ} {Bh : ℕ → ℝ}
    (hB : ProfileBound P h Bh p) (hBpos : ∀ r ≤ p, 0 < Bh r)
    {G : Garden w} {U} {a b : GBranch G.tree} {R : CLRegionData G U a b} {n : ℕ}
    (hprime : IsPrimeGarden G) (hM9 : VINEPARAM) (B : CLChainAssembly G R n) (RD : ReconstructionData G)
    (hG : G.IsPlain) (layer) (hLayer : IsLayering (RD.garden hG) layer)
    (hlay : ∀ x, layer x ≤ p) (hord : (RD.garden hG).order ≤ P.N (p + 1) ^ 4)
    (centre : Fin 4 → Mom P.d) (wBar : Mom P.d)
    (H : RowCoherent hM9 B RD hG layer hLayer (step3W hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar) P.L P.γ P.δ h p) :
    ∀ E ∈ outSet (step3D hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar) P.L P.γ P.η,
      ContinuousOn (fun tt : Fin 3 → ℝ => twistedRecentered G a (canonFinset p (startState B RD hG layer hLayer) (chainStart B))
          P.L P.γ P.δ h wBar (tt 0) (tt 1) (tt 2) (sumintBoundary (G.sign a.toNode) E 0) (sumintBoundary (G.sign a.toNode) E 1)
          (sumintBoundary (G.sign a.toNode) E 2) (sumintBoundary (G.sign a.toNode) E 3))
        (cubeSet (step3D hM9 B RD hG layer hLayer (canonBadKind hM9 B RD hG layer) (qOutOf RD hG layer a b R) centre wBar).qOut)
```
`outBox ⊆ cubeSet` (`ContinuousOn.mono`). `profileBound_of_snorm (hB0 : 0 ≤ B₀) (hs : ∀ r ≤ p, SNormR (40d) (40d) (h r) ≤ ofReal B₀)` gives `ProfileBound P h (fun _ => B₀+1) p` and positivity. The gate hypotheses `hgate hinc hη6 …` are the ones of `step3AtLeafH` (available inside the prefix proof, as in `Step3PrefixH.step3Layer_of_at`); `hlay`, `hord`, `H` are binders/hypotheses of `VineEstCanonLayerC2`.

**Modulated (R58), `Cont/ModClass.lean`.** W13's definitions were not on disk (the directory `P4/W13` was empty), so the modulated kernel is defined in this namespace with the same formulas: `lowModC R lam t τ = exp(π i lam τ_b)`, `clLocalKernelModC` (modulation inside the time integral), `clRecenteredLocalKernelModC` (exp factor times it), `twistedRecenteredModC G a Z L γ δ F base lam t0 t1 t2 e f g h = exp(..) * ∑ x∈Z, clLocalKernelModC x.1.data …` (`lam : ℝ`; integer `λ` by cast). `twistedRecenteredModC_zero`: `lam = 0` is `twistedRecentered`. `twistedRecenteredModC_continuousOn` has exactly the statement above with one extra binder `(lam : ℝ)` first and `twistedRecenteredModC G a (canonFinset …) P.L P.γ P.δ h wBar lam (tt 0) …`. To instantiate with W13's `twistedRecenteredMod … (lam:ℤ)`: unfold; the two are definitionally `exp * ∑ clLocalKernelMod …` with `lowMod = lowModC` (cast of `lam`); the identification is `rfl`-level up to `((lam:ℤ):ℝ)`, to be confirmed when W13 lands (I did not compile against it).

**Approach.** Core: copy of the continuity half of `step3AtLeafH` (row decay from gates, `rows_continuousH`, `continuousOn_clockedExprEps`) plus `leafT` (continuous, cube-preserving) and `clRecenteredLocalKernel_congr`. Member: for any state reached by a batch (`kind` arbitrary), `Reach.exists_asm` gives the twisted assembly `B1`; the member datum is `step3W` of `B1` with the START output indices `q0` (needs only `hqo`: `q0 0` = layer of core `a`, and the leaf-child condition, both transported by `atomLayer`); eligibility from `Reach.rowCoherent`, `Reach.order_eq`, layers `≤ p` from `canonical_or_eq` + `CanonCriterion`. Class: `recentered_twisted` per member, finite sum. `kind = true` enters only via `mem_canonFinset` (garden-only fact, isolated in `twistedRecentered_continuousOn`; `classSum_continuousOn` takes any `Z` with `Reach p kind` members). Mod: `vineChainMod_eq_sumintForm'` (reindex with the factor, `e^{πiλτ_b} = e^{πiλ τ_slot0}` in sumint coordinates), `clockedExprEpsM`, `continuousOn_clockedExprEpsM` (bounded jointly continuous factor, so any such factor works).
**Uncertainties.** (1) Not compiled against the final W13/W2 definitions. (2) No `BadClause`/order-N1 hypotheses are used (not needed for continuity). (3) The conclusion on the cube relies on `q0 = qOutOf` of the start for members; no member-specific q is needed.


## F-QOUT (packet S-FQOUT; scratch <scratch>/vineest-s3/uni-qout/)

**Finding.** The layers can differ. `IsLayering` only demands `𝔏(child) ≤ 𝔏(parent)` and equal layers on paired leaves,
so the top `attachedNode c = (core b).child i` of the native chain at a branch child `c` and `coreBranch c` (below it in the
chain) may carry different layers (`layer (core c) ≤ layer (attached c)`; the regular rows even carry the explicit slack
"root layers ≤ q"). The skeleton clock `t_c` is the core's clock (redkg L1726; `clLocalClock` returns `t 1` at the
*branch* `c` of `G`, and `clLocalTimeDomain` retains `t 1 < τ_b` for a branch child, read as the clock of `coreBranch c`), so
V5's box `[layer(attached c), +1]` was wrong for branch children whenever the two layers differ. I did not build a Lean
counterexample; the statement quantifies over all `IsLayering`s, so no equality lemma is available.

**What V5 needs from `qOut 1`, `qOut 2`** (all uses grepped): only (i) `qOut c ≤ p`, (ii) `qOut c ≤ layer (core b)`
(`qOutOf_one_le/two_le`), (iii) the box shape. `Step3AtLeaf`/`step3W`/`step3D` etc. take `qOut` as an arbitrary function.
So fix (a) is local: only the *definition* `qOutOf` and the two lemmas change. Every other use (`Step3Prefix`,
`Step3PrefixH`, `Cont/Class`, `Cont/ModClass`, `P4/Statement`, `P4/W2/ModStatement`, `P4/Final/Core`) compiles UNCHANGED
(`hqOut` still closes by `simp only [qOutOf]; exact hlay _`).

**Patch to apply to uni/ (one file): `<scratch>/vineest-s3/uni-qout/LayerFacts.patch`** (diff -u against uni/src/VineEstS3/LayerFacts.lean,
sha256 of uni original 3c4ad8b2..., patched e9805d4b...; patched file uni-qout/src/VineEstS3/LayerFacts.lean). Content:
```lean
noncomputable def outNode (RD) (hG) (c' : GNode G.tree) : GNode (RD.forest hG) :=
  if hb : c'.1.2 ∈ (G.tree c'.1.1).branching then (RD.coreBranch hG ⟨c'.1, hb⟩).toNode else attachedNode RD hG c'
theorem layer_outNode_le ... (b : GBranch G.tree) (i : Fin 3) :
    layer (outNode RD hG (b.child i)) ≤ layer (RD.coreBranch hG b).toNode
noncomputable def qOutOf ... : Fin 3 → ℕ :=
  ![layer (RD.coreBranch hG a).toNode, layer (outNode RD hG (b.child R.positive)), layer (outNode RD hG (b.child R.negative))]
```
and `qOutOf_one_le/two_le` now `show (layer (outNode …) : ℝ) ≤ _; exact_mod_cast layer_outNode_le RD hG layer hLayer b _`.
Leaf children keep `attachedNode` (the leaf itself); branch children use the core.
Statements (`VineEstCanonLayerC2M/HalfM`, etc.) are textually unchanged; they change meaning only through `qOutOf`.
The module needs a downstream rebuild (217 modules import LayerFacts below `P4/Final/Core`); I rebuilt LayerFacts and the
7 direct users above (exit 0, in uni-qout/build, which symlinks uni's buildS5C8 tower for VineEstS3/VineEstS5C).
Not rebuilt: the intermediate modules, whose oleans stay compiled against the old `qOutOf`.

**F-LEAFCLK (new file `uni-qout/src/VineEstS3/LeafClockIndep.lean`, imports `RegRedDraft.CLLocalKernel`, sha 0c5cbc7f...):**
`clLocalClock_update_positive_leaf/negative_leaf`, `clLocalTimeDomain_update_*_leaf`, and
```lean
theorem clLocalKernel_leaf_positive_indep (D hG R)
  (hleaf : ¬ (b.child R.positive).1.2 ∈ (G.tree (b.child R.positive).1.1).branching) ... (tU tP tP' tN : ℝ) (e f g h : Mom d) :
  clLocalKernel D hG R L γ δ F layer hLayer base tU tP tN e f g h = clLocalKernel D hG R L γ δ F layer hLayer base tU tP' tN e f g h
```
and the `negative` twin. So S2 may substitute any box-valid surrogate for a leaf child's time. (The statement's kernel
`twistedRecenteredModC` composes `clLocalKernel`-type expressions; the lemma is at the `clLocalKernel` level, the
modulation `lowModC` reads only `τ_b`; I did not state the lemma at the `ModC` level.)

**Checks.** Build exit 0 for LayerFacts, LeafClockIndep and the 7 users (logs in uni-qout/logs); `#print axioms` of
`layer_outNode_le`, `qOutOf_one_le`, `qOutOf_two_le`, both leaf lemmas: propext, Classical.choice, Quot.sound; hygiene
grep (sorry/admit/axiom/opaque/unsafe/maxHeartbeats) clean on the two edited/new files. COPIED-SHA256SUMS in uni-qout.
**Uncertainty:** a full downstream rebuild is not done; exact-type `example` against a pinned statement not applicable
(statement text unchanged).

## V5 W2 CORE SESSION 5 (Sonnet; S-V5W2CORE5, after R82) -- CHECKPOINT (not READY)

Files (all `module`, no sorry, standard axioms [propext, Classical.choice, Quot.sound] via uni/scratch8/Ax5.lean; build `uni/w2b.sh VineEstS5C.P4.W2.<M>` into buildS5C8; new: ExcGeoII, OfModes, PieceAll1, PieceAll2, PieceAll3; edited in place (originals uni/scratch8/pre-s5/): Free, RowSlot, AuxRows, AuxMul, RemMulD, RemShift, RemProd, RemRowsC, PieceRep, PieceRows, PieceRowsJ, PieceRowsR; Final/ClassM, Iface (R82-authorised; Core and Prefix unchanged and rebuilt)).

Approach and findings:
1. `typeII_qb_qr` (ExcGeoII): `qbOf = R.left`, `qrOf = R.right` for any oriented end rung with `parent lower = R.left`; `endRung_right_unique` (right atom determined by the left via `EndRungData.lower_neighbor`).
2. R82 interface: `TermCertW` has `Bx ⊆ outBox` and the dictionary only on `Bx`; Final's `top_boundRBM`/`wpF_classBM` take `habs`/`TermBoundR`/`hTB` on `openTop Bx q₀` and `UniformTermCertAt` uses `openTop (outBox ..) (layer (RD.coreBranch hG a).toNode)`.  FINDING (deviation from R82's wording): NO continuity lift is needed: `XNorm00Restr` is an infimum over arbitrary extensions, so `XNorm00Restr_le_openTop` (null-set lemma, already used inside `top_boundRBM`) gives the closed-box bound from the openTop one; the V5-CONT / X7 continuity machinery is not used.
3. Row layer rewritten (R82 "every row's W is the Fourier sum"): `RowData.ofModes` (OfModes), all builders return it, `Ae` unconditional, identities conditional on the clock being in the continuity set; `PieceRep ... Bx` a.e. form; the whole `pieceRep_*` family restated with one a.e. hypothesis `hX` (slot clocks in the continuity sets AND the explicit separated form) for `tt ∈ Bx`, a.e. `τ ∈ timeDom`.  This removes the F-AUX-CONT obstruction (line `t = L4+1`, exterior clock on the faces) from the row layer: those clocks are only excluded by the a.e./openTop hypotheses.
4. Dispatch wrappers (PieceAll1-4; PieceAll4 = signs, case-M mirrors of A1/A2, `pieceRep_zero`, type-I vanishing lemmas): point-level bundle summands (`tA1 ... tTT`, mirrors `-conj` of the swapped pieces, `rA1 ... rB3` with `RemC` data) -> `PieceRep` under the Good hypothesis (indicator + identity-set + continuity-set membership of the clock pairs).
Deviations: none to the pinned sources.  Errata: none new.
NEXT (exact): see PROGRESS "STEP 2 DISPATCH WRAPPERS ... NEXT".
CHECKPOINT vineest-W2: constructor-level dispatch (`bundlePt`/`stepX` constructors x case A/M x orientation by nu, vanishing for type I, `PieceRep.smul`), then record certificate (3), `engine_rhs` (4), `uniformTermCert` (5), final checks (6).
