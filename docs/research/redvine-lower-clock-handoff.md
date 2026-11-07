# VINE-B (S2 REPRESENTS, vine case, single-state redvine factorization): STOPPED on F-LOWCLOCK

Scratch: /home/scott/wt-scratch/vine-b. No Lean was written: the factorization planned in
/home/scott/wt-scratch/represents/PLAN-VINE.md (component VINE-B) is not an identity, and no ruling covers this.
Nothing in represents, V5, regred-leaf, redsplice, lg-spine-u or the universe was edited.

## The planned statement (PLAN-VINE.md, VINE-B)
`U.toLF.valueSel(B.layered, sel_σ) = Σ_i sign_i · coupling^{n_sb} ζ(Gsb) Σ_{z ∈ GenDecoration Gsb} ε̃ Z ∫_{dom Gsb}
 phases_sb · Π_{outer slots} K*[typeProfiles h_i] · Π_j K̃^{U_j}_{(B)}[h_i(·,j₁,j₁)](t_{u1},t_{u21},t_{u22}; k-bdry_j(z))`,
with `K̃^{U_j}_{(B)}` = V5's `clRecenteredLocalKernel` / `twistedLocalKernel` (the summand of `twistedRecentered`).

## F-LOWCLOCK: the slots of the lower external children read an interior clock of the unit

Let `U_j` be a unit (`CLBlock` of `unitBlocks S_B σ`), with region data `R : CLRegionData S_B U_j a b`
(`a = u1`, `b = u2`). Let `c ∈ {b.child R.positive, b.child R.negative}` (`u21`, `u22`). Then:

1. **In the reduced skeleton integrand, the slot at `c` reads `τ_b`.** REGRED-LEAF's skeleton reduction
   (`kernelLeaves_skeleton_reduction_sel`, `LeafFamily.valueSel_skeleton_reduction`) has the integrand
   `reducedStarProductLeaves` (regred-leaf/src/RegRedLeaf/Leaves.lean L41–L63).
   - Its tree slot at a branch `c` is `treeLeaves (nativeChainLayered … c) … (parentClockWith tt τ c.toNode) (τ c) k_c`.
   - Its couple slot at a leaf `c` is `coupleLeaves (nativeCoupleLayered … p) … (parentClockWith tt τ (p.firstLeaf)) (parentClockWith tt τ (p.secondLeaf)) k`.
   - `parentClockWith tt τ x = τ (parent of x)` for a non-root `x` (regred-leaf/src/RegRedDraft/NativeParentClocks.lean
     L17–L21). The parent of `c` in `S_B` is `b`, so both slots read `τ_b`.
   - This is literal TARGET: (redkg) L1726 has `K*_{T_(m)}(t_{m^pr}, t_m, k_m)` and `K*_{Q_(l,l')}(t_{l^pr}, t_{l'^pr}, k_l)`.
   - `treeLeaves LG H t s k = kernelLeaves … LG H (fun _ => t) s …` (lg-spine-u/src/LeafwiseCoherentApp.lean L10–L12).
     Every node of the chain is constrained by `< t` (TARGET defkg (timepairtree) L682), so the slot genuinely depends
     on `t`.
2. **`τ_b` is integrated inside the unit kernel, and the slot at `c` is not part of it.**
   - `b ∈ clInteriorBranches R = U_j.erase a` (vineest-s3/uni/src/RegRedDraft/CLRegionSupport.lean L34–L35), so
     `clLocalKernel` integrates `τ_b` (`CLInternalTime R`, CLLocalTimes.lean L17–L18).
   - `clLocalStarProduct` (CLLocalFactors.lean L40–L52) contains only the chains at `clInteriorBranches R` and the
     couples at `clRegionalPairs` (internal leaves). `c ∉ U_j`, because `R.lower`/`lower_excluded` make the two bonds
     to the children other than `kept` external (CLRegionData.lean L19–L28).
   - So V5's `K^{U_j}` (and hence `twistedRecentered`) does not contain the slot at `c`. TARGET says the same: L1738
     includes only slots with `l, m ∈ G_sk[U]\{u1}`, and `u21, u22 ∉ G[B]` (block_clcn (1)(a), L1349).
3. **In `Gsb`, `c` is a child of `u1`.**
   - The splice replaces the subtree at `a` by `spliceCrown` with the three boundary subtrees as its children
     (universe/src/SpliceTrees.lean L33–L40; CLSpliceGarden.lean L51–L58, `clSplicedGardenOfSlots_tree`).
   - So the "outer slot" at `c` over `dom Gsb` is `K*(t_{u1}, …)`. That is exactly what TARGET (redvine) L1956
     writes: `Π_{m∈N_sb} K*_{T_(m)}(t_{m^pr}, t_m, k_m)` with `m^pr = u1^j`.

Hence (redvine) / the PLAN statement replaces `τ_{u2^j}` by `t_{u1^j}` in the slots at `u21^j, u22^j`. Equivalently,
the true integrand has a factor `slot_c(τ_b, …)` that couples an outer factor to a variable integrated inside
`K^{U_j}`. Then `∫ Outer · K^{U_j}` does not factor as `Outer(dom Gsb) × K̃^{U_j}(t_{u1}, t_{u21}, t_{u22}; k)`.
No choice of outer clock makes it an identity:
- with `t_{u1}` (the planned form), the domains `{chain nodes < τ_b}` and `{chain nodes < t_{u1}}` differ, since
  `τ_b < t_{u1}`;
- with `τ_b`, the outer integrand is not a function on `dom Gsb`.

**When the two clocks give the same value.**
- **The native object at `c` is trivial.** If `T_(c)` is trivial (order 0, so the slot is `1`), or `c` is a leaf
  with a trivial couple (the slot is the input profile), the slot does not depend on its first clock.
- **Every node of the `c`-side native object has layer `< L_b`.** Each such node `n` has
  `t_n < L_n + 1 ≤ L_b < τ_b < t_{u1}`, so the constraint `t_n < (clock)` is automatic for both clocks.
  - TARGET L1918 makes this observation: `J̃_Q(t, s)` is constant in `t ∈ [q, q+1]` when `q > L_r`.
  - layerreg1 (L901) shows that the nodes of a coherent regular tree may lie in layer `q = L_{n^pr} = L_b`. So layer
    separation does not hold in general.

## Explicit configuration (in the domain of `Stage1ReductionAtA`)
- `p = 0` (allowed: `p < P.D`), so every node of a garden in `𝒢_1` has layer 0 and every clock lies in `(0, 1)`.
- Take a canonical garden `G` (irreducible, proper, all layers 0; `IsCanonGC 1`) with these properties:
  - its prime skeleton `S_B` has a group `S` with a unit `U_j ∈ unitBlocks S_B σ` (σ = SG on `S`);
  - the positive lower external child `c = b.child R.positive` of `U_j` is a branching node of `S_B`;
  - the reconstruction replaces `c` by a nontrivial regular tree `T_(c)`, e.g. order 2: one chain pair `n1 → n2`,
    both in layer 0.
- Replacing a node by a regular tree keeps the garden irreducible and in `𝒢_1`, and leaves the skeleton unchanged.
  `Stage1Carries` (lg-spine-u Stage1Gate.lean L23–L26) puts no condition on the native objects.
- Then `valueSel` contains `treeLeaves(T_(c), τ_b, τ_c, k_c)`, which equals
  `coupling² ζ Σ ε ∫_{τ_c < t_{n2} < t_{n1} < τ_b, t ∈ (0,1)} (phases)(inputs)` and genuinely depends on `τ_b ∈ (0,1)`.
  The planned right-hand side has `treeLeaves(T_(c), t_{u1}, τ_c, k_c)`.
- The same happens for a leaf `c` of `S_B` paired outside `U_j`: `coupleLeaves(Q_(c,c'), τ_b, τ_{c'^pr}, k)`.
  - This factor mixes `τ_b` with an outer clock.
  - If `c'` is itself a lower external child of another unit `U_k`, it mixes `τ_{b_j}` with `τ_{b_k}`: two units'
    interiors.
- The same happens when `c` is the upper joint `u1^k` of another unit: the chain slot at `u1^k` has parent clock
  `τ_{b_j}`.

I did not evaluate a numerical instance. The non-identity rests on the structural mismatch above: the planned
right-hand side changes a constraint that bounds integrated chain times.

## Rulings checked
- R33 F-TT concerns only the root times `tt_j`. The splice preserves them: `u1`'s parent clock is the same in `S_B` and `Gsb`.
- R9, R24, R25, R28, R32, R45–R47-FINAL, R54–R57: none concerns the parent clocks of the lower external children.
- TARGET L1472 says the trees `T_(u21)`, `T_(u22)` are the "same regular tree" under LF twists (only `T_(u2)` and
  `Q_(u23,u0)` change). So the slot functions are twist-invariant, but they still read `τ_{u2}`.

## What does separate (checked by reading; these are needed under any repair)
- **Branches.** `GBranch S_B = GBranch Gsb ⊔ Σ_j (U_j.erase u1^j)`: SpMap `ob_range`, `spliceFold_cls_mem`/`notMem`.
- **Order and ζ.**
  - Order: `S_B.order = Gsb.order + Σ_j clLocalOrder1 R_j`.
  - ζ: `ζ(S_B) = ζ(Gsb) · Π_j clLocalZeta R_j`, since the splice preserves signs (`sig_eq`, `spliceLeafEquiv_sign`).
- **ε.** `epsDec S_B = (Π over Gsb branches other than the hinges `u1^j`) × Π_j clRegionalEpsilon` (the regional
  product includes `u1`, as TARGET L1957 (i) states).
- **The `u1` phase.**
  - `cl_phase_recenter` and `cl_sum_signed_resonance` (CLPhaseRecentering.lean L33–L55, CLBoundaryIdentities.lean
    L44–L60) give `Π_{v∈U_j} phase_v = e^{πiδL^{2γ} t_{u1} Γ_j} · (recentered phases)`.
  - `ζ_{u1}Ω^{sb}_{u1} = clBoundaryEnergy R_j = boundaryEnergyFromMomenta(sign u1, k_{u1}, k_{u11}, k_{u21}, k_{u22})`,
    provided the crown puts the `+`/`−` children by sign. Here `Ω^{sb}_{u1} = resFactor` of `u1`'s crown children,
    and the position-1 child carries the opposite sign.
  - So `phases_sb · K̃^{U_j} = phases_sk` holds exactly (TARGET L1957 "exactly cancels").
- **Decorations.** `Dec(S_B) ≃ Σ z : Dec(Gsb), Π_j CLLocalDecoration R_j (boundary_j z)`.
  - The ingredients are restriction (`restrictCLDecoration`) and gluing.
  - Conservation at `u1` in `Gsb` comes from the block conservation.
  - Leaves internal to a unit are completely paired; all others are retained in `Gsb`.
  - (Not built.)
- **Time domain.** `coreTimeDomainW` agrees a.e. with `splicedTimeDomain(Gsb) × Π_j clLocalTimeDomain R_j`:
  `τ_{u21} < τ_{u1}` follows from the local chain `τ_{u21} < τ_b < … < τ_{u1}`, F-TT holds by transitivity, and the
  Icc/Ioo boundaries form a null set. (Not built.)
- **Slots.**
  - Slots at internal pairs and at interior branches restrict exactly: `clLocalStarProduct_restrict`,
    CLStarConsumption.lean L29–L60.
  - The slot at `u11 = a.child excluded` reads `τ_a = t_{u1}` in both gardens.
  - Every other outer slot's parent is retained. The only external children of nodes of `U_j` are `u11` and
    `u21`/`u22`: interior atoms have degree 4 with all positions internal (`cl_child_mem_support`, CLRegionSupport.lean L73–L94).
  - **The lower children `u21^j`, `u22^j` are the only failure.**
- **P\* lemma 1.** Leaves of a unit's internal couples and interior chains have pair type `(layer, j₁, j₁)`, so
  `typeProfiles = h_i(·, j₁, j₁) ∘ layer` and `coupleLeaves`/`treeLeaves` reduce to V5's
  `KQstar`/`KTstar` with `F = h_i(·, j₁, j₁)`.
  - The template for that reduction is REGRED-LEAF `reducedStarProductLeaves_layerProfile`.
  - The leaves of `T_(u21)` are also of type `(layer, j₁, j₁)`.
  - Not built.

## Candidate repairs (for the ruling; none is adopted here)
- **(A) Lower-clock form of the unit kernel plus a modulated VINEEST.** TARGET's own machinery supports this:
  `sumint` (L1595–L1618) carries modulations `e^{πiλ t}` at every input time, with loss `[max⟨λ⟩]^{η^6}`
  (FourierboundI L1618).
  - **VINE-B♯.** State the exact identity with the lower-child slots kept at clock `τ_{b_j}`, inside a unit kernel
    that also takes the slot functions, for example
    `clLocalKernelLow R … φ := coupling^{n1} ζ Σ'κ ∫τ clLocalSummand … κ τ · φ₊(τ_b) · φ₋(τ_b)`,
    where `φ_±(t)` is the slot at `u21`/`u22` with first clock `t`.
    - For a leaf partner outside the unit, `φ` also depends on outer clocks, or on another unit's `τ_{b_k}`.
    - The integrand then does not factor over `j` before a time-Fourier split.
  - **VINE-D.** Split the lower slots by time-Fourier transform in their parent clock.
  - **VINEEST (V5).** Prove the bound for `K̃^U` with a modulation `e^{πiλτ_b}` at the lower joint, uniformly in `λ`
    with an `⟨λ⟩^{η^6}` loss.
- **(B) Restrict VINE-B to layer-separated states.** This is exact, but it is false in general (p = 0 example above),
  so it cannot discharge `Stage1ReductionAtA`.
- **(C) Erratum candidate (TARGET (redvine) L1954–L1956, with the three observations at L1946–L1951).**
  - Quoted: "`× Π_{l∈L_sb}^{(+)} K*_{Q_(l,l')}(t_{l^pr}, t_{(l')^pr}, k_l) Π_{m∈N_sb} K*_{T_(m)}(t_{m^pr}, t_m, k_m) Π_j K̃^{U_j}(…)`".
  - Why it is wrong: for `m` or `l ∈ {u21^j, u22^j}`, (redkg) L1726 has first clock `t_{u2^j}`, which K^{U_j}
    integrates (L1737). In `G_sb` the parent is `u1^j`. So (redvine) is an identity only when those slots do not
    depend on that clock. The three observations do not cover the outer slots' dependence on `t_{u2^j}`.
  - Suggested fix: keep the `u21^j`/`u22^j` slots at `t_{u2^j}` and absorb them by time Fourier with a `λ` modulation
    at `u2^j` in (sumintI1), which `sumint` permits.

## Files
- /home/scott/wt-scratch/vine-b/HANDOFF.md (this file)
- /home/scott/wt-scratch/vine-b/PROGRESS.md

## Checks run
- Read-only inspection of the files and line ranges cited above.
- No build was run: no Lean file was written, so there is nothing to rebuild and no axioms to print.

## Uncertainties
- I did not construct an explicit prime skeleton with a CL vine. I rely on the general existence of non-root CL VCs
  in V₀ whose lower joint has a branching external child. TARGET's cnblock proof (L1370) also exhibits lower children
  that are leaves paired with tree roots.
- The phase bookkeeping assumes the crown positions follow block_clcn (2) (L1352), and also needs the sign/position
  lemma for `spliceCrown`. This is unchecked in Lean.

STOPPED vine-b: F-LOWCLOCK

# VINE-B♯ EXPORT (session 3 update 1; sources src/VineB/*.lean, build with ./build.sh)

CHANGES in session 3 (newest first):
* PART I DONE (Fold1-Fold8, compiled exit 0, no sorry): `VineB.stShape hM σ : SpliceShape (unitBlk hM σ) (stSt S σ).G` with `br = (stSt S σ).M.ob`
  (`stShape_br : (stShape hM σ).br = (stSt S σ).M.ob := rfl`), `hM : S.molecule.IsMolecule`, `unitBlk hM σ j := (unitBlocks S σ).get j`
  (J = `Fin (unitBlocks S σ).length`), `unitBlk_disj hM σ : Disj (unitBlk hM σ)`, `stShape_hinges : (stShape hM σ).hinges (unitBlk_disj hM σ) = (stSt S σ).hinges`
  (= `(collectionChoices S σ).hinges`).
* G3 DONE at the level of a general `Φ : SpliceShape blk Gsb` (Src1, Src2): for `hinges` with `hmem : ∀ c, c ∈ hinges ↔ c ∈ Φ.hinges hd`, `hSb : Gsb.IsPlain`:
  `Φ.src hd hSb hinges hmem : J → Fin 4 → HingeDarts Gsb hinges ⊕ Fin w`, `Φ.src_dart`, `Φ.src_root` (statements: for ALL d, roots, decorations z:
  `bondIndex Gsb z.1 x.1 = z.1 (Φ.hmom hd j i)` resp. `z.1 (Φ.hmom hd j i) = roots r`), exactly the three AsmCtxH fields (`src`, `src_dart`, `src_root`).
  For stSt take `hinges := (stSt S σ).hinges`, `hmem := fun c => by rw [stShape_hinges]`. Structural facts: `Φ.hmom_zero : hmom j 0 = (hinge j).toNode`,
  `Φ.hmom_child : i ≠ 0 → ∃ k, hmom j i = (hinge j).child k`, `Φ.crown_exists`.

* **G2, provable part DONE (Src3, Src4)**: for a decoration `z` of `G_sb` (`hz : IsDecoration Gsb z`, e.g. `z.2.1`),
  `Φ.hmom_conservation hd j z hz : ((S.sign (blk j).upper.toNode : ℤˣ) : ℤ) • (z (hmom j 0) - z (hmom j 1)) = z (hmom j 2) - z (hmom j 3)`, and
  `Φ.hmom_outSet_core hd j L base z hz`: with `β i = base + latticePoint L (z (hmom j i))` and `v = sumintBoundary (S.sign (blk j).upper.toNode) β`,
  `(∀ c, ∃ nv, v c = base + latticePoint L nv) ∧ v 0 - v 1 = v 3 - v 2` (these are `outSet`'s coset and conservation clauses with `wBar = base`);
  `sumintBoundary_close : (∀ i, ‖β i - ctr i‖ ≤ 1) → ∀ c, ‖sumintBoundary ζ β c - sumintBoundary ζ ctr c‖ ≤ 1` (the closeness clause for
  `centre j c := sumintBoundary (S.sign a_j) (latPt ∘ c)`), and `sumintBoundary_gap_iff : (v 0 ≠ v 1 ∧ ‖v 0 - v 1‖ ≤ L^(-γ+η)) ↔ UnitGap L γ η β`
  with `UnitGap L γ η β := β 0 ≠ β 1 ∧ ‖β 0 - β 1‖ ≤ L ^ (-γ + η)`.
  **G2 is therefore `outSet` membership EXCEPT the SG-gap clause `UnitGap L γ η (fun i => base + latticePoint L (κ.1 (hmom j i)))`, which I could NOT prove.**
  Why: `selSk κ` (= `splicedGapIndicator Gsb (gapSpecification S σ) … ≠ 0`) only constrains the gap pair of the DESIGNATED atom of each group
  (`gapSpecification` is `some` only at `groupAtom`; for a hinge it is `hingeOrigPair`, a pair of the SKIPPED vine / the external pair of a whole-group
  unit, `RedSpliceGap`, `RedSpliceGapKind.hingeOrig_gapKind`). The clause for the boundary of EVERY unit `j` needs the group-level fact
  "the flow norm of each unit equals the flow norm of the designated object" for units that are runs of the chain around a skipped ingredient
  (`pair_norm_ingredient`/`flow_norm_joint` give it only for the designated pair), and it is stated for the S-decoration extending `z` by the unit interiors.
  The farm has no lemma for non-designated units. Closest provable form: G2 with the gap clause as the named input `UnitGap` per unit.
* **G1: not provable as shaped.** Provable Gsb-level content (Src5): for `τ ∈ splicedTimeDomain Gsb lay tt`:
  `Φ.hinge_clock_box`: `clockOf Gsb tt τ (hclk j 0) ∈ Icc (lay (hinge j)) (lay (hinge j) + 1)` (`lay (hinge j) = layer0 (blk j).upper` for `lay = (stSt S σ).layer layer0`);
  `Φ.child_clock`: if `nodeClk Gsb (hmom j i) = inr c` (i ≠ 0, a BRANCH boundary child), `τ c < τ (hinge j) ∧ τ c ∈ Icc (lay c) (lay c + 1)`;
  `Φ.leaf_clock`: if `nodeClk Gsb (hmom j i) = inl r` (a LEAF boundary child), then `τ (hinge j) < tt r`.
  Two obstructions to `(fun i => clockOf … (hclk j i)) ∈ outBox (unitD …)`:
  (1) LEAF lower child: its `hclk` is the root time `tt r` of its tree, which is ABOVE `τ_{u1}` (F-TT), so `max (t 1) (t 2) < t 0` of `outBox` is false (reversed),
      and `tt r` is not constrained to `[qOut, qOut+1]`. V5's kernel does not depend on that clock, so the box should not constrain it (S2/V5 must use a
      box that ignores leaf boundary clocks, or feed an in-box dummy; the identity `unitKernelM_clocks` already shows independence).
  (2) BRANCH lower child: the box needs `qOut i = layer (attachedNode RD hG (b.child pos))` (V5 `qOutOf`) to equal `lay c = layer (RD.coreBranch hG (b.child pos)).toNode`;
      but `attachedNode (b.child pos)` is the TOP of the native tree `T_(b.child pos)` (a child of the core of `b`, `core_child_position`), while `coreBranch` is the
      bottom of its lone path, so `layer (attachedNode c) ≥ layer (coreBranch c)` in general, with equality NOT proved (I expect it can fail when a nontrivial native tree spans several layers).
      For `i = 0` there is no issue: `qOut 0 = layer (coreBranch a).toNode = lay (hinge j)` (`coreLayer … = fun b => layer (D.coreBranch hS b).toNode` is `rfl`).

* **Instantiated exports for `G_sb = (stSt S σ).G`** (module `VineB.Export`, compiled): `stSrc hM σ hSb j i`, `stSrc_dart`, `stSrc_root` (G3, with
  `hinges := (stSt S σ).hinges`), and `stSt_skelVal_modal_eq_outerValM hM σ hS hSb hL γ δ base D layer hLayer h tt amp frq selSk Zw hZ hF hsum`, which is the
  per-mode identity with `Gsb := (stSt S σ).G`, layer `(stSt S σ).layer (coreLayer (layeredReconstruction D hS layer hLayer) D hS (D.garden_decodes hS))`,
  `hinges := (stSt S σ).hinges (= pi.Cs.hinges)`, `route := (stShape hM σ).route hS hSb`, `hclk := (stShape hM σ).hclk (unitBlk_disj hM σ)`,
  `hmom := (stShape hM σ).hmom (unitBlk_disj hM σ)`, `HkM := unitKernelM (unitBlk hM σ) D hS L γ δ h layer hLayer base`; units are indexed by
  `Fin (unitBlocks S σ).length`.

## (session 2 text follows)

STATUS: DONE, compiled exit 0, no sorry, axioms [propext, Classical.choice, Quot.sound]: the general-shape theorem
`SpliceShape.skelVal_modal_eq_outerValM` (Main5.lean) and all modules before it (PointA/B, Hdata, Modal, Pointwise, Meas, Unit, PiProd, Fiber1-6,
Main1-4, Main5a, Main5b, Main5). NOT STARTED: Part I (SpliceShape for `(stSt S σ).G`, `br = M.ob`), G1, G2, G3. No statement below is final until
marked DONE in PROGRESS.md.

## Names S2 consumes (all in namespace WaveTurbulence.VineB, `Φ : SpliceShape blk Gsb`)
* `Φ.route hS hSb : ReplacementSlot Gsb → Fin 2 → ClkSrc Gsb ⊕ J`, `Φ.route_natural` (= S2's `hroute`), `Φ.iota`, `Φ.node_slotNode`.
* `Φ.hclk hd j : Fin 3 → ClkSrc Gsb`, `Φ.hmom hd j : Fin 4 → GNode Gsb.tree`, `Φ.bdry_eq`, `Φ.clocks_zero`, `unitKernelM_clocks`.
* `Φ.hinges hd`.
* Per-mode identity (general shape; DONE up to the last assembly step):
  `skelVal_modal_eq_outerValM : skelVal D hS L γ δ base roots tt layer selSk (Φ.modalFn hS hSb D L γ δ (typeProfiles (layeredReconstruction D hS layer hLayer) h) layer hLayer amp frq)
     = outerValM Gsb L γ δ base roots tt (fun c => layer (D.coreBranch hS (Φ.br c)).toNode) (Φ.hinges hd) Zw hSb amp frq (Φ.route hS hSb) (Φ.hclk hd) (Φ.hmom hd) (unitKernelM blk D hS L γ δ h layer hLayer base)`
  hypotheses: `hd : Disj blk`, `hL : L ≠ 0`, `hZ : ∀ κ, (if selSk κ then 1 else 0) = Zw (Φ.resDec hS hd κ)` (selection depends on the G_sb decoration only, TARGET L1963),
  `hF : ∀ j, HF D hS L (unitProfile blk h j) layer base` (V5 source input summability, unitProfile j = h(·,j₁,j₁)),
  `hsum : Summable fun z => ampBound hSb L base amp z` (absolute summability of the outer mode amplitudes over Dec(G_sb)).
  `skelVal` with slot family `slotFn` equals REGRED-LEAF's `valueSel_skeleton_reduction` expression (`skelVal_slotFn`).
* `unitKernelM … j lam t m = clRecenteredLocalKernelModC … (t 0)(t 1)(t 2)(m 0..3)` for the profile `unitProfile blk h j`.

## Shape mismatches / flags for S2
1. `Zw`: your `fun z => if selSk z then 1 else 0` (selSk on G_sb decorations) matches; I need `hZ` linking it to the skeleton selection (stated above).
2. `HkM i j lam t k` must be `unitKernelM` (single state). `twistedRecenteredModC` (the class sum) is VINE-C's job, not mine.
3. Extra hypotheses `hF`, `hsum` above are required by Fubini; if S2 cannot supply `hsum` for its amplitudes, tell me.
4. G1/G2/G3 (`src`, `src_dart`, `src_root`, outBox/outSet membership) are not yet stated in Lean; I have not checked they are provable. Will post exact statements when Part I lands.

## VINE-B♯ session 3: final checks (run)
Files: src/VineB/*.lean (46 modules, 6012 lines, max 298/file; Fold1-8, Src1-5, Export new this session). Fresh rebuild into build-fresh in topological order
(order-fresh.txt, logs/fresh-rc.txt): all 46 rc=0 (a stale probe `Probe.lean` outside the closure was moved to logs/). Axioms (`#print axioms` of
stSt_skelVal_modal_eq_outerValM, stSrc, stSrc_dart, hmom_outSet_core, stShape): [propext, Classical.choice, Quot.sound]. Hygiene grep
(sorry/admit/axiom/opaque/unsafe/maxHeartbeats) over src/VineB: clean. Exact-type: `stSt_skelVal_modal_eq_outerValM` (Export.lean) is stated with S2's
`stSt`, `(stSt S σ).hinges`, stage1PieceOf layer, and compiles by `exact` of the general theorem.
Open (flagged above): G1 as shaped (leaf boundary clock reversed; attachedNode vs coreBranch layer), G2 SG-gap clause for non-designated units.
