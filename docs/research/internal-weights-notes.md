# research-internal: top cutoffs at nodes inside regular objects (route decision)

For wt-orch, written 2026-11-07. Main HEAD bf597bcf. Both probes were compiled against main's live lib.
TARGET means `WKE-Longer_times_Final_arXiv.tex`.

## 0. Verdict: ROUTE A (top-weighted rows), with a scope reduction and a narrower weight class

**Scope reduction (the part of C that is true).** Only one kind of regular object can carry a top factor at a
non-external momentum: an INCOHERENT object whose root-parent core layer is `p`.
- On a coherent object, the top weight is exactly one factor `g(k_ext)`, present iff `q = p > q'` (TARGET layerreg1).
  FC23 has already proved the slot form of this: `FC23Bond.slotProduct_coherent` and `nodeLabelProduct_eq_skeleton_mul`.
- On an object whose root parent lies below layer `p`, there is no top node at all.

**Faithful mechanism.**
- Weighted regular estimates: TARGET proves proplayer1 with `W` (incohproof3/5, L991–L1012). The Fourier step
  (incohproof6–8) only needs a finite Fourier `L¹` norm in `(k, x_n, y_n)`, so `W` absorbs any weight with a finite
  Fourier measure in those variables.
- Consumers use only norm bounds of the rows: vineest (L1742–L1754, proof Step 1) and the Stage-1 reduction.
- So the cutoff modifies the row kernels, and the modified rows keep proplayer1's bound up to mass.

**Weight class.** Weights must be lower-layer-blind: `topPsi p g` (`g` on every top label, `1` elsewhere). This is
needed for class-commonness when weights are read at actual nodes (§3 A-1). FC23's and C2-E-B's cutoffs are blind.

**Three exports.** All statements below compile on main (`probe/`, §6).

| Export | Owner | What it is |
|---|---|---|
| `TopIncoherentDecayGate` | C2-B (new packet C2-B-TOP) | main's leafwise incoherent gate for top-weighted kernels |
| `V5TopClassBound` | V5-SPACE-EXT | V5's class bound with every region row carrying its own top weight |
| `Stage1ReductionAtSTBLDψTop` | S2-ST | FC23's staged node-label `STBLDψN`, specialised to `g`-form |

**Cost.**
- About 9–15k lines in total, of which about 6–12k is beyond work already planned (S2-ST Phase C ≈2.4k; VineSpaceB).
- The dominant risk is threading weighted rows through V5's engine (2.5–6k). V5-SPACE-EXT should scope it first.

## 1. What exists (checked against sources)

**C2-B, first packet** (c2b/HANDOFF "C2-B EXPORT").
- Contents: `toCharMix`; `exists_weighted_regular_mass_bound`; `representsInt_external_scalar` and `_fourier`; the
  `TransferBoundary` counterexample.
- `exists_weighted_regular_mass_bound` is the spectral-mass step only. It is NOT a `KQstar`/`KTstar` norm bound.
- `representsInt_external_*` handle external scalars only.
- **No internal weight is covered at the norm level.**

**C2-B-REG** (READY; c2b/HANDOFF "C2-B-REG EXPORT").
- What it proves: the full `XNormRestr` (30d,30d) and (30d,0) bounds, with the incoherency gain kept.
- Which kernels: RAW `MomentumTreeData` source kernels only (`weightedSourceCoupleKernel`/`TreeKernel`).
- Which weights: `F.value (pairedLattice L p)` with `p : PairedMomentum d n`, i.e. the free `2n` internal momenta only
  ("These maps take no external root momentum"). Cost `F.mass`.
- **Answer to the brief.**
  - Raw incoherent kernels with weights: yes.
  - Weights at internal NODE momenta: only for weights of the form `ℓ(x,y)`.
  - A top node's momentum is `k_ext + ℓ(x,y)`. All three children of a chain node have momenta `k+x`, `k+x−y`, `k−y`.
    So a top weight is root-dependent and is NOT covered.
  - No leafwise / `LayeredGarden` / `KQstar` form exists.

**C2-B-COH** (READY, R137).
- What it bounds: the coherent ERROR `weightedCoupleLeaves − weightedCohCouple`, in leafwise form.
- Which weights: a root-independent block-product `F` on the link chart ("the root phase stays outside F").
- It covers coherent objects only. FC23's top factors do not need it, because agreement makes the factor external.
  FC23 session 11 recorded the same finding.

**Main.**
- `Spine/IncohLeafwise` (21 files, 1525 lines) generalises the raw incoherent decay to per-leaf profiles.
- `leafwise_incoherent_decay : LeafwiseIncoherentDecayGate` is proved (`Spine/SourceProviders.lean:34`).

**V5's member kernel.**
- `clLocalStarProduct` = ∏ `KQstar` over native couples × ∏ `KTstar` over native chains, with ONE layer profile `F`
  (main `RegRedDraft/CLLocalFactors.lean:41`).
- Non-exceptional rows are bounded only through two gates:
  - `CoherentGateH` and `IncoherentGateH` (uni `VineEstS5C/GateH.lean:97,122`);
  - W2's `UniformTermCertAt` takes `hinc : IncoherentGateH`.
- `RowCoherent` constrains only the rows with `g = 0` (main `VineEstS3/LayerFacts.lean:285`). Incoherent rows are
  members of V5 classes.
- The rows are concrete `KQstar κ.F`. `κ.F` appears 287× in 52 uni files; row kernels appear in 66 files.

## 2. The configurations (both occur, and the factor is not identically 1 on the support)

**In a region** (V5-SPACE-EXT's configuration).
- Shape: a core Vine (II-a) under an off-stem `u₁` of layer `p`.
  - The interior branch `u₄` carries `T(u₄)`, a dominant chain `n₁` (layer `p`) → `n₂` (layer `p−1`), link `{1,2}`.
  - `c₁` and `c₂` are children of `n₁`: lower-layer leaves (trivial attached trees), paired with children of `n₂`.
- Top nodes: `n₂`, `c₁`, `c₂`, with momenta `k_{u₄}` plus internal link variables.
- Canonicity holds: canonequiv (ii) for `(cᵢ, cᵢ')` reads `max = p−1 ≥ min(p, p−1)`.
- Def lftwist requires only `T(u₂)` and `Q(u₂₃,u₀)` to be coherent (L1468). Every other row is "the SAME regular tree
  `T(m)` … with the same layerings" (L1472). So incoherent non-exceptional rows lie in V5 classes.
- In FC23's carrier: `n₁` is an initial-tree branching node and `n₂` is the root of an attached tree.

**Outside a region.** The same row can sit anywhere in `G_sb`.

**Why the factor is genuinely there.**
- `k_{n₂} = k_{n₁} − σk_{c₁} − σk_{c₂}` is bounded only by its own cutoff.
- The other cutoffs give `|k| ≲ (#roots)·M₁`, not `≤ M₁/2`.
- One relation per attached garden (`Σ ±k_root = 0`) would need a garden-dependent choice of which root to leave
  uncut. That is impossible, because the cutoff is fixed at the level of `X` (TARGET L2283, L2294).

## 3. Refute-checks

### A (top-weighted rows): survives

**A-1. Twist invariance.**
- Non-exceptional rows are identical across a class, with the same layerings (L1472). True operations transport them
  rigidly (`decEquivR`).
- Their root-parent core layers are preserved (`LFConstruction.coreLayers`).
- Their external bond momentum is preserved (twistexplain (a),(d)).
- Exceptional rows are coherent, so each carries one factor `g(k_bond)`. That is V5-SPACE-EXT's invariant bond factor.
- **Subtlety (new).** Read at actual nodes, the coherent replacements in `𝔅` (layerreg1: `q ≥ L_{n₁} ≥ … ≥ q'`) put
  the drop below `p` at a layer `r ∈ [L_{u₂}, p)`, and `r` varies over `𝔅`.
  - A weight depending on `r` would be member-dependent and would kill the exact zero at L1907.
  - **Fix:** use only lower-layer-blind weights `topPsi p g`.
  - FC23's `fc23Psi` equals `topPsi` (`fc23Psi_eq_topPsi`). C2-E-B's `cutPhi` is `chi0(‖ρ‖/R_t)·[layer < p]`, also blind.
  - V5-SPACE-EXT's general `ψ(q,q')` remains valid only in its core-layer (skeleton) reading.

**A-2. The incoherency gain survives.**
- TARGET L995–L1035 goes through with the weight:
  - `k`-derivatives fall on `W·g(k+ℓ)`, which costs moments;
  - Sobolev in `k` (incohproof4) lets us fix `k`;
  - the Fourier expansion in `(k,x,y)` then only adds modulations `(ξ_n, ξ'_n)` and an external phase;
  - lemlayer1/2 are uniform in these;
  - the time structure (incohproof11, incohproof15) is untouched.
- In Lean:
  - integrate the presentation parameter of `g` together with the source spectral carrier (C2-B-REG's method);
  - root jets hit `e^{iξ·k}` and cost `momentMass_J`;
  - no `XNormRestr` Minkowski is needed (C2-B-COH session 9: none exists).

**A-3. Moments are finite.**
- `g_j = chi0(‖·‖/M_T)` with `M_T ≥ L` has a radial presentation with `momentMass_J ≤ C_{d,J}`.
- FC23 already has `blockMeasure_momentMassJ_ne_top` (any `J`) and `commonChartMeasure_flower_momentMassJ_le`.

### B (Fourier-expand into characters): refuted as a route, kept as an implementation option

1. **Top-node-indexed characters are not class-common.** The exchange `k_{u₂} ↔ k_{u₂₃}` (FC23 session 10) breaks
   them.
   - Slot- or bond-indexed characters are class-common, but those factors are exactly the skeleton factors, which the
     bond multiplier already carries.
2. **For internal factors of incoherent rows, per-θ characters ARE class-common** (the rows do not change).
   - A row-local expansion gives `e^{iξ·k_a} = e^{iξ·k_ext}·∏_{crossing leaves} e^{iσξ·k_ℓ}`.
   - There are at most `2·#incoherent crossing links` crossing pairs.
   - After a cos/sin split, these become REAL per-leaf profiles with `SNormR ≤ C⟨ξ⟩^{40d}`. Main's leafwise gates
     bound them with no new analysis.
   - So LayerOnlyTI *can* be replaced by "layer-only on exceptional rows, per-leaf profiles on the others". But that
     needs:
     - (a) the same V5 engine refactor as A: V5 has one `κ.F` everywhere (R125);
     - (b) bond-specific characters in V5's multiplier, which is not of `regionBondWeight`'s (layer, layer) form;
     - (c) a new leaf-identity profile class in S2-ST (`LeafFamilyTI` is label-based);
     - (d) θ-integration at every consumer's final scalar, with `4^{#crossing}` realification:
       - S2-ST's existential representation cannot be integrated over θ;
       - `SlotFam` needs countable modes;
       - there is no `rN` Minkowski.
   - Same V5 scope as A, three statement changes instead of one, and less faithful. Rejected as a route.
   - It survives only as an internal option (D′) for V5-SPACE-EXT's proof. There, Minkowski at V5's conclusion norm
     (`XNorm00Restr`) is available.

### C (configurations impossible, or factors ≡ 1): refuted

- §2 exhibits the configurations, in a region and outside one.
- Stem-style localisation fails: stems avoid vine interiors only for stem nodes (TARGET (7), L2300). The M₁ cutoff is
  on ALL initial-tree leaves, which is needed both for (7)'s separation and for the `M₁^{−80dP}` gain.
- Partial C holds and is used: coherent rows need agreement only, and rows with root-parent layer `< p` carry no top
  factor.

### D (other TARGET-supported routes): none cheaper

| Alternative | Why it fails |
|---|---|
| Trivial treatment of affected vines (item (4), `L^{20d}` per vine) | O(N) affected vines, versus an incoherency gain `L^{−(γ₁−√η)g}` per row |
| Taylor or difference splitting `g(k+ℓ) − g(k)` | still needs a weighted estimate; a crude bound loses `L^{2γ}` per link |
| Moving the cutoff (e.g. to stem siblings) | changes flowerest1's statement, and still lands inside stem rows |
| Garden-dependent cutoffs | impossible: the cutoff is fixed at the level of `X` |

## 4. Route A: exact statements, owners, cost

### 4.1 C2-B-TOP (owner C2-B): `probe/TopRowStatements.lean` (compiled)

**Definitions.**
- `topPsi`, `rowParentLayer`, `rowTopWeight p g LG qr k` = ∏_a `topPsi p g (layer a) (parent layer a) (k a)`. The
  parent layer of root `i` is `qr i`.
- `kernelKW`, `KQstarTop`, `KTstarTop`: frozen `kernelK`/`KQstar`/`KTstar` with the multiplier inside the lattice sum.
- `kernelLeavesW`, `coupleLeavesTop`, `treeLeavesTop`: the leafwise versions.
- `momentMassMom`, `GPresented J g c`.

**Proved (standard axioms).**
- `kernelKW_one`, `kernelLeavesW_one`, `rowTopWeight_one`.
- `kernelLeavesW_eq_kernelKW`: one gate serves both V5's raw rows and S2-ST's leafwise slots.

**Target.** `TopIncoherentDecayGate := WTPrefix TopIncoherentDecayAt`.
- It is main's `LeafwiseIncoherentDecayAt` with the kernels replaced by `coupleLeavesTop`/`treeLeavesTop`.
- It adds the hypotheses `g`, `1 ≤ cψ`, `GPresented (32d) g cψ`.
- Cost factor: `cψ^(4n+2)` for couples and `cψ^(4n+1)` for trees.

**Proof route.**
- Take C2-B-REG's weighted raw chain with a root-dependent multiplier: the presentation of `g` on `Mom d`, pulled back
  along the node maps `k + ℓ_a(κ)`. Root jets then cost `momentMassMom`.
- Add a multiplier copy of main's `IncohLeafwise`. The homogeneity extraction is unchanged.

**Cost:** 2–3.5k.

### 4.2 Agreement in row form (owner FC23): ports `FC23Bond.SkeletonAgreement`

- `RowTopAgreementCouple`: `IsCoherentCoupleAt p q q' Q LG`, `q' ≤ q ≤ p` imply
  `rowTopWeight p g LG ![q,q'] (coset k κ) = if q' < p ∧ q = p then g k else 1`.
- `RowTopAgreementTree`: the same statement with `IsCoherentTreeAt`.
- Both statements are in the probe. **Cost:** 0.2–0.5k.

### 4.3 V5-SPACE-EXT: `V5TopClassBound := WTPrefix V5TopClassBoundAt` (`probe/V5TopStatement.lean`, compiled)

**Statement.**
- Binders and bound are `VineEstCanonLayerHalfMXK`'s, except `(M, q0, Q)` is replaced by
  `(g : Fin w → Mom → ℂ) (cψ) (1 ≤ cψ) (∀ j, GPresented (32d) (g j) cψ)`.
- The class is `twistedRecenteredModCXTop p (g a.1.1)`, built as
  `memberMXTop` / `clLocalSummandTop` / `clLocalStarProductTop`: every regional couple and interior tree uses
  `KQstarTop`/`KTstarTop`. Root parent layers are `coreParentLayer` (core layer of the skeleton parent; `p` at a root).
- There is no skeleton multiplier.
- Mass: `cψ^(4·(|U| + clLocalOrder2))`, which is at least the number of row nodes in the region.

**Proof plan.**
- (a) Per member, rewrite coherent rows to `g(k_bond)` by agreement (4.2). Their product is `regionBondWeight`
  restricted to coherent-row darts.
  - This restriction is class-common: non-exceptional rows do not change, and exceptional rows are coherent.
  - The product then goes through VineSpaceB with a dart-dependent `ψ`.
- (b) Incoherent non-exceptional rows keep `KQstarTop`/`KTstarTop`.
  - Thread a row-kernel selector (a `KPar` field, with `if coherent then KQstar κ.F else KQstarTop …`) through the
    member kernel, the frames (`spartFrame`), the lower kernels, and the sumint rows.
  - The only analytic input for these rows is `IncoherentGateH`, which becomes `TopIncoherentDecayGate` in raw form
    via `kernelLeavesW_eq_kernelKW`.
  - Also needed: time continuity, measurability, `KQstar_const_above` and `KQstar_zero_below_root` analogues. These are
    straightforward because the weight is time-independent and bounded.
- **First do a scoping session** that lists every place where a non-exceptional row kernel is unfolded. Then choose
  between (b) and (D′): per-row superposition at `XNorm00Restr` plus a per-leaf-profile V5, which has the same engine
  scope and needs no gate.
- `V5TopClassBound` subsumes V5BondClassBound for FC23 and C2-E-B, so the VineSpaceB work is reused.

**Cost:** 3.3–7k.

### 4.4 S2-ST: `Stage1ReductionAtSTBLDψTop C₀ P`

**Statement** (text = FC23's staged `FC23STW.Stage1ReductionAtSTBLDψN`, `fc23/src/FC23STW/STBLDPsiInput.lean`).
- Replace the binders `(ψ : Fin (2R) → ℕ → ℕ → Mom → ℂ) (cψ), 1 ≤ cψ → TopSupported p ψ → SpatialPresented ψ cψ` by
  `(g : Fin (2R) → Mom P.d → ℂ) (cψ), 1 ≤ cψ → (∀ j, GPresented (32 * P.d) (g j) cψ)`.
- Conclusion: `RepresentsSTBLTφ … (cψ ^ (12 * N) * s) (psiWeight p (fun j => topPsi p (g j)) base φ) …`.
- Size: at most `3N` nonroot nodes outside regions, plus `Σ_j 4(|U_j| + order_j) ≤ 8N` inside regions.

**Producer.**
```lean
stage1STBLDψTop_of_inputs (hinc : LeafwiseIncoherentDecayGate) (hcoh : LeafwiseCoherentApproximationGate)
  (htop : TopIncoherentDecayGate) (hV : V5TopClassBound) (hM9 : VINEPARAM) :
  ∃ C₀ ≥ 2, WTPrefix (Stage1ReductionAtSTBLDψTop C₀)
```

**Internals.**
- Slot partition: port FC23's `node_inSlot`, `inSlot_unique`, `prod_eq_prod_slots`.
- Coherent slots outside regions become a `G_sb` factor (`slotProduct_coherent`). This is existing φ machinery.
- Incoherent slots outside regions:
  - `slotFnTop` (`coupleLeavesTop`/`treeLeavesTop` in main `Represents/RepNV1.slotFn`);
  - the `prod_slotFn` identity;
  - `SlotFam` from `htop`.
- Units use `V5TopClassBound`: Phase C of session 16, with `unitHkTop` in place of `unitHkψ`.
- This replaces the session-16 draft's `TwistInvariantWeightψ` clause (3). Build it in a main-based world (R138).

**Cost:** 4–4.7k, of which ≈2.4k was already planned as Phase C.

### 4.5 FC23 and C2-E-B adapters

- Restage to STBLDψTop.
  - FC23: `g j = chi0(‖·‖/fc23Scale M tail small j)` (`fc23Psi_eq_topPsi`), plus a `GPresented` adapter for the
    radial measure on `Mom d`.
  - C2-E-B: `g = chi0(‖·‖/R_t)` for `cutPhi`.
- **Cost:** 0.2–0.5k each.

### 4.6 Order of work

1. S2-ST statement switch, then FC23/C2-E-B restage. This is cheap and unblocks staging now.
2. C2-B-TOP in parallel with V5-SPACE-EXT scoping.
3. V5 (a) and (b).
4. S2-ST vine case.
5. S2-ST slots outside regions.

## 5. Findings for wt-orch

- **F1 (blind weights).** Weights read at actual nodes must be lower-layer-blind (`topPsi p g`) (§3 A-1). FC23's
  staged `STBLDψN` takes a general `ψ` with `TopSupported`; narrow it to `g`-form. FC23 loses nothing, since its `ψ` is
  already blind.
- **F2 (FINDING-STEMROW, probable, to verify).** C2-E-B's `markedPhi` cutoffs `chi0(|Ω_b|/2^j L)` at UNMARKED stem
  nodes appear to have the same gap outside regions.
  - Such a node can be a chain node of a collapsed stem regular tree: a (2,0) mini-tree on the stem, with layer-`p`
    leaf pairs.
  - Its `Ω_b = 2⟨x,y⟩` reads internal link variables. This is the coherent, root-independent case.
  - R112's argument covers vines, not collapsed rows; φ must factor through `decToStG`/collapse (clauses 2–3).
  - The gate would be C2-B-COH, which also needs the separated form of the weighted approximant.
  - So S2-ST's weighted-slot interface (4.4) should take a general slot weight, with a coherent-slot gate as well.
- **F3.** C2-B-COH is not needed for FC23's top factors (agreement). This matches FC23 session 11.
- **F4.** FINDING-INTERNAL's two halves are resolved by 4.3 (in a region) and 4.4 (outside a region). R135 (2)'s
  routing "via C2-B's weighted transfer" needs C2-B-TOP: C2-B-REG is root-independent and raw.
- **F5 (exposition gap, already noted in R132).** TARGET flowerest1 (1),(4) (L2294, L2297): the M₁ cutoff also sits
  inside incoherent regular objects. It is supported by proplayer1's `W` (L991–L1012), but stated nowhere. This is a
  candidate erratum about exposition, not a false statement.

## 6. Validation

- Compiled one at a time with `cd <repo> && nice -n 5 lake env lean <file>`, against main's
  live lib (HEAD bf597bcf). Both files: exit 0, no output.
- A deliberate-error copy of probe 2 confirmed that it elaborates.
- `#print axioms` gives `[propext, Classical.choice, Quot.sound]` for `kernelKW_one`, `kernelLeavesW_one`,
  `kernelLeavesW_eq_kernelKW` and `rowTopWeight_one`.
- No `sorry` or `admit`. Every target is stated as a `def … : Prop`, not as a theorem. The transient check files are
  deleted.
- sha256 at close:
  - `TopRowStatements.lean` fa1c000bf701724198e4bdab0488f5dedfce8fcd46e7feec5e2a795245df3567
  - `V5TopStatement.lean` 64de4bb68ab89114e9907a32d7555ee0e209336e4345d99d6c08804a308c9078
- Sources read:
  - RULINGS R63, R111, R117, R125, R130–R135, R138;
  - s2-st/HANDOFF session 16;
  - fc23/HANDOFF Opus sessions 9, 10, 11, and `FC23STW/STBLDPsiInput.lean`;
  - uni-space/HANDOFF (top section) and `VineSpaceB/Statement.lean`;
  - c2b/HANDOFF (C2-B EXPORT, C2-B-REG EXPORT, C2-B-COH sessions 9, 12, 14);
  - research-cut2/NOTES §3, §7;
  - TARGET L845–L1042, L1464–L1484, L1724–L1754, L1886–L1922, L1927–L1941, L2279–L2305;
  - main `LeafwiseAt`, `LeafwiseKernel`, `KQstar`, `KernelK`, `CoherentObjects`, `CLLocalFactors`, `CLLocalKernel`,
    `VineSpaceK/StatementDefs` and `WeightedStatements`, `Represents/RepNode1` and `RepNV1`, `VineEstS3/LayerFacts`.
