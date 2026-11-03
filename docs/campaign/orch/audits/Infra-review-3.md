# Infra review 3: statement review of the new high-stakes results (Task 10)

Auditor: `wt-orch` (Opus), refute-first. This reviews **statements**, not proofs: normalizations, hypotheses that might
not be dischargeable at the use site, junk values and exact types. Date: 2026-11-03.

## Inputs

**Repository.** `main` at `282178f`, merged into `w/orch` as `b9b46a1`.
- Main advanced by 60 commits during the review: w/bproc, w/nt-circle, w/minor-arcs, w/count, w/jr-ops, w/approxnt and
  w/wke-l2s landed.
- Everything below refers to the landed state. The 27/41 commit `ca5a6f6` was reviewed before landing;
  `VdCB/CircleCountingBridge.lean` is byte-identical on main.

**Scratch** (reviewed read-only; sha256 prefixes):
- `/home/scott/wt-scratch/main-assembly/`: `MainAssembly.lean` `3b80d6bc5037…`, `GateTypes.lean` `77e959e747f4…`,
  `GaussianData.lean` `037d88c64e47…`.
- `/home/scott/wt-scratch/main-glue2/`: the four `Ansatz*.lean` files. They are byte-identical to the main-assembly
  copies.
- `/home/scott/wt-scratch/norm-bridge/`: `SpatialBridge.lean` `c2f8b8e534ee…`, `TimeBridge.lean` `73ffd40c1d7a…`,
  `MixedBridge.lean` `3b4086401cbd…`.

**Sources (treated as data).**
- DH23 `Revision_Submit.tex`: L1013–L1036 (Lemma 6.5), L1143–L1156 (Lemma 6.7), L1012 (standing λ range),
  L2027–L2117 (Lemmas A.1–A.3).
- DH21 `Inventiones-Final_Version.tex` L944–L1075 (Def 5.2, Lemmas 5.3–5.8).
- TARGET L581–L589 (norms) and L958–L977 (Lemmas 5.2, 5.3).
- Snapshot `waveb-snap-5` (the B1 freeze candidate) and my SEAL-PLAN §B.4.

**Build (my own; one `lake env lean` at a time, `nice -n 5`; no `lake build`, no budget overrides).**
- The 47 repository modules in the main-assembly import closure that were not built in my worktree (Fourier, Gaussian,
  LinAlg, MainGlue, NLS, Probability; sources from this worktree), plus the 101-module closure of
  `WeylSums.QuadExpSum2/3`. All compiled with 0 errors.
- The main-assembly modules, recompiled **against snapshot 5** (my `waveb5` build). The handoff used snapshot 4 plus the
  SNorm guard. Its `WaveBDraft/Core.lean` copy is byte-identical to snapshot 5's, and its System copy differs only in the
  `SNorm` docstring. Result: 0 errors, 0 `sorry`.

## Verdict summary

| # | Item | Verdict |
|---|---|---|
| 1 | 27/41 circle discrepancy and annulus (VdCB, wt-ansob; Counting, wt-nt) | **PASS.** Uniform in a real centre, exact exponent `27/41`, annulus in the form (disclattice) needs |
| 1′ | wt-nt elementary annulus branch and `estcross` | **PASS** (explicit constants; scale conventions dischargeable) |
| 2 | `MainGlue.main_of_propansatz_nlsAkBridge` | **PASS, machine-checked.** The conclusion **is** the frozen `main` type and the hypotheses **are** snapshot 5's `propansatz`/`nlsAkBridge` (up to hygienic binder names and one Prop-instance proof term). No quarantined import; standard axioms |
| 2′ | MainGlue G1, G2, G4–G11 (landed and main-glue2) | **PASS** (as SEAL-PLAN §B.4, or a better form) |
| 3a | Norm bridges (`Fourier/Norm00V*`, scratch norm-bridge) | **PASS.** The direction provers need is unconditional |
| 3b | NTSP: TARGET Lemma 5.2, DH23 Lemmas 6.5 and 6.7 | **PASS**; source errata are corrected in Lean but **missing from FINDINGS** (R1) |
| 3c | ClassJR: DH21 Def 5.2, Lemmas 5.3–5.5 | **PASS**, deviations disclosed; Lemmas 5.6–5.8 not yet stated; one author question (Q1) |
| 3d | Minor arcs: lemlayer2/lemcubic (`quadExpSum2/3`), DH23 6.6 | **PASS, machine-checked.** Snapshot 5's exact `quadExpSum2`/`quadExpSum3` follow from the Foundations theorems through the cutoff and phase identities alone |
| + | `CountLemmas.atomCountLemma_bound` (landed during the review) | Text-identical to snapshot 5's `atomCountLemma`, using its own `NearLattice` with the same body |

**Nothing found affects the B1 freeze candidate.**

## 1. The 27/41 circle results (priority 1)

### 1.1 Verdict table

| Declaration | Verdict | Reason |
|---|---|---|
| `VdCB.abs_card_latticeDisc_sub_area_le (c) (hR : 1 ≤ R)` : `|#latticeDisc c R − πR²| ≤ circleDiscrepancyConstant · R^(27/41 : ℝ)` | **FAITHFUL**; this is F3's requirement e < 2/3 | Uniform in the centre: `c : EuclideanSpace ℝ (Fin 2)` is arbitrary and the constant is explicit, independent of `c`. The exponent is the literal real power `27/41`, and `ExponentCoordinates`/`ImprovedExponentAudit` prove `27/41 = (11/30+16/30)/(1+11/30) < 2/3`. **`latticeDisc` is pinned:** `Counting.mem_latticeDisc` (R ≥ 0) gives `n ∈ latticeDisc c R ↔ ‖latticePoint 1 n − c‖ ≤ R`, the closed Euclidean disc (column enumeration with `integerInterval = Icc ⌈l⌉ ⌊u⌋`). No hypotheses besides `R ≥ 1`: the endpoint estimate is discharged internally (`norm_sum_circle_endpoint_dyadic_le`, binders TYPING 4, SOURCE 3). Standard axioms per the BPROC handoff. |
| `Counting.abs_card_latticeDisc_sub_area_le_twenty_seven_forty_one` (wt-nt, landed) | **FAITHFUL** | An independent second route (localized endpoint transfer), with the same statement shape and constant `circleImprovedConstant`. |
| `VdCB.card_annulus_le s c (2 ≤ Q) (0 < ρ ≤ Q/4) (hann)` : `#s ≤ 6π Qρ + 3C·Q^(27/41)` | **FAITHFUL**; this is the first branch of (disclattice) | `s` is any finite set inside the closed annulus `|‖n − c‖ − Q| ≤ ρ` (half-width ρ; the source's "width ρ" is absorbed in constants). The centre is arbitrary real, as the use sites need: after fixing ξ = x + y the annulus is centred at ξ/2. |
| `Counting.card_annulus_le_of_circle_error_half_radius` and `card_annulus_disc_le_min_of_circle_error_half_radius` (landed) | **FAITHFUL**; this is **the full (disclattice) min with the F31 correction** | The regime is `0 < Q`, `0 < ρ ≤ Q/2`, `Qρ ≥ 1`, i.e. the source's `Q⁻¹ ≪ ρ ≪ Q` with explicit constants. This removes the `Q ≥ 2`, `ρ ≤ Q/4` restrictions of the VdCB form by an internal case split. The second branch keeps the **sum** `√(Qρ) + L(Qρ)^{3/2}/Q + L√(Qρ)Q^{−1/3}` (F31), on the closed disc of radius L about an arbitrary second centre `d`. The disc hypothesis `hdisc : ∀ R ≥ 1, |#latticeDisc c R − πR²| ≤ C R^e` is discharged by either 27/41 theorem (`C ≥ 0`, `0 ≤ e = 27/41 ≤ 1`). |
| `Counting.card_annulus_disc_le` / `_expanded` (elementary branch) | **FAITHFUL** | `640000 · (√(Qρ) + L(Qρ)^{3/2}/Q + L√(Qρ)Q^{−1/3})`; it counts any finite subset of annulus ∩ disc, uniformly in both centres. |
| `Counting.card_dense_dot_product_strips_in_balls_le` (`estcross`, L2031–L2032) | **FAITHFUL** | Dimension `D = d + 3`, matching DH23's standing `d ≥ 3` (L252, L438). The ball `A` is centred at an arbitrary `c` with radius L. Each `x ∈ s` has its own ball centre `b`, level `α` and finite `Y ⊆ B ∩ ℤ^D` with `|⟨x,y⟩ − α| ≤ ρ` and `#Y ≥ L^{D−1}/θ`; this is the source's `sup_{B,α}`. The bound `C_D (ρ^D + L^{D−2} ρ² θ² (1 + log L)²)` has an explicit log power (the source has `(log L)^C`). The scale convention `θ ≥ 1`, `16·3^{D−2} θ ≤ ρ ≤ L` fixes `1 ≲ θ ≪ ρ ≪ L`. The source's implicit constants in "`≲ ρ`" and "`≳ L^{d−1}θ⁻¹`" are absorbed by rescaling ρ and θ at the use site, as the handoff says. |
| `ImprovedExponentAudit` numerics | consistent | `27/41 ≤ 35/53`. Every `e ≤ 35/53` gives use (2)'s critical saving `63/79 = 4/5 − 1/395 < 4/5 − 10⁻⁴` (`annulus_critical_saving_of_exponent_le_thirty_five_fifty_thirds`, plus `…_eta_margin` for γ > 4/5 − 10η), and the source savings for uses (1) and (3). |

### 1.2 Remarks

- **Pending, not a defect:** DH23 Lemma A.2 (2) itself (`basiccount0` (2), the use that needs `e < 2/3`) and
  `countLemma` are not yet stated in Foundations. COUNT has proved `atomCountLemma` only.
- **The disc theorem is stated for `latticeDisc`, an enumerated `Finset`.** Its meaning rests on `mem_latticeDisc`, which
  is proved. A consumer counting `{n | ‖n − c‖ ≤ R}` uses that lemma; this is fine.

## 2. The conditional main assembly (priority 2)

### 2.1 Method

In one environment importing `MainAssembly` (rebuilt on snapshot 5) and `WaveTurbulence.Frozen.Theorems.Main` (built in
my worktree), probe `scratch/Task10-main-E1.lean` decomposes the helper's type as `∀ (h₁ : PropansatzGate.{u}) (h₂ :
NlsAkBridgeGate.{u}), B` and compares `B` with the frozen `main`'s type, after instantiating universe `u`. Probe
`Task10-main-E2.lean` prints snapshot 5's `propansatz`/`nlsAkBridge` types. I compared these with the gate bodies across
the two environments: they cannot be co-imported, because both define `WaveTurbulence.IsGaussianData`.

### 2.2 Results

| Check | Result |
|---|---|
| Binders | Exactly two extra hypotheses, `hpropansatz : PropansatzGate.{u}` and `hnlsAkBridge : NlsAkBridgeGate.{u}`. The conclusion has **no loose bound variables** (it does not depend on them). Universe parameters `[u]` = `main`'s `[u]`. |
| Conclusion vs frozen `main` | **Alpha-equivalent** (`Expr ==`: true) and **identical under `pp.all`**. `Expr.equal` is false only through binder names: the hygienic names of anonymous instance binders carry the module name. After proof erasure and hygiene canonicalization the 33,217-character `Expr` strings are **identical**. |
| `PropansatzGate` body vs snapshot 5 `propansatz` type | Identical up to hygienic instance-binder names. |
| `NlsAkBridgeGate` body vs snapshot 5 `nlsAkBridge` type | Identical up to hygienic names, except that the instance proof `Nat.AtLeastTwo 2` (a `Prop`; two occurrences, in the two `(2 : ℝ)` literals) is abstracted into `NlsAkBridgeGate._proof_1` in the abbrev. Substituting the explicit term makes the strings identical. Since `NlsAkBridgeGate._proof_1 : Nat.AtLeastTwo 2`, proof irrelevance makes this definitionally inert. |
| `IsGaussianData` (copy in `GaussianData.lean`) vs snapshot 5 | Type and value identical up to hygienic names. |
| Axioms of the helper | `[propext, Classical.choice, Quot.sound]` |
| Quarantine | The project import closure of `MainAssembly` has 85 modules and contains **no** `Provider.*`, no `Frozen.Theorems.*` (no `DRAFT_SORRY` anchor), and no sorry-carrying draft (`WaveBDraft.Statements`/`Sumint`/`Deferred`). It imports `WaveBDraft.{Core, System}` (definitions only). |

**Consequence at sealing.** The landing is one declaration per file under `Frozen/` (docs/review/WAVE-B-B1.md). The glue
then replaces its `GaussianData` copy and the `WaveBDraft` imports with the frozen definition files (`IsGaussianData` is
a definition, so it is not quarantined). The gates become the frozen anchors' types up to the inert differences above,
so `main_of_propansatz_nlsAkBridge` applies to proofs of the two gate propositions as is.

### 2.3 MainGlue G1–G11

SEAL-PLAN has no G3; the set is G1, G2 and G4–G11.

| Lemma | Verdict | Note |
|---|---|---|
| G1 `measurableSet_smoothDataSet` (0 < L, 0 < T, α = L^{−γ}) | FAITHFUL | The SEAL-PLAN premises. |
| G2 `exists_measurable_fourier_energy` / `measurable_fourierEnergyObservable` | FAITHFUL | The observable is the zero extension of the chosen solution's energy. `fourierEnergyObservable_eq` ties it to every smooth solution, so it is not a junk measurable function. |
| G4 `ansatz_event_inter_rapid_subset_solvable` | FAITHFUL | `Fev 𝔇 ∩ {IsRapidDecay} ⊆ solvableEvent`. This is the F6/T7 correction (only Fev 𝔇, never Fev p for p < 𝔇). |
| G5 `hasLaw_stdComplexGaussian` | FAITHFUL | — |
| G6 `integral_initial_mass_restrict_le` (and the general-weights version) | FAITHFUL | The Bochner integral could be junk 0 if not integrable, but the assembly proves integrability separately (handoff step 7), and G7's `summable_schwartz_lattice` removes the `tsum` junk. |
| G7 `schwartz_lattice_sum_le` | FAITHFUL | — |
| G8 `ansatz_norm_sq_le_initial_mass` | FAITHFUL | — |
| G9 `ansatz_norm_torusFourierCoeff_eq` and the selection form | FAITHFUL | Including both endpoints `t = 0, T`. |
| G10 (a) `eventually_final_exponent`, (b) `ceiling_subdivision`, (c) `induction_error_absorption(_final)` | FAITHFUL | **(c)'s threshold L₁ depends on D**, through the gap `η²⁰2^{−D}`. This is necessary, and admissible because `main` chooses L₀ after D. It corrects my SEAL-PLAN's "L₁(d, η, φin)". |
| G11 `ansatz_event_subset` | FAITHFUL | — |

## 3. Norm bridges, NTSP, ClassJR, minor arcs (priority 3)

### 3.1 Norm bridges

| Declaration | Verdict | Reason |
|---|---|---|
| `SNorm_eq_spatialNorm`, `SNormR_eq_spatialNorm`, `SNorm_restriction_eq_spatialRestrictionNorm` | **FAITHFUL, unconditional** | All orders, including order-0 discontinuous inputs (CL-19). The draft's `SNorm` body is byte-identical to snapshot 5's (Task CL-19 delta). |
| `XNorm00_eq_mixedFourierNorm00` (any `V`), `XNorm00Restr_eq_mixedRestrictionNorm00`, `XNorm00_unit_eq_timeFourierNorm`, `XNorm_zero_order_eq_mixedFourierNorm`, `XNormRestr_zero_order_eq_…` | **FAITHFUL, unconditional** | — |
| `XNorm_le_mixedFourierNorm`, `XNormRestr_le_mixedRestrictionNorm` | **FAITHFUL, unconditional**; this is the direction provers need | Landed upper bounds transfer to the draft norms. |
| `XNorm_eq_mixedFourierNorm_of_*` (positive order) | correctly conditional | Equality needs null-measurability of the bad-frequency set `{ξ | ¬ ContDiff ℝ Λ₁ (F̂ ξ ·)}` (or admissibility). **In the freeze set, positive-order `XNorm`/`XNormRestr` are used by no anchor** (FREEZE-LIST: only `XNormRestr` → `XNorm`). The only frozen 𝔛 consumer, `sumint`, uses `XNorm00Restr`, whose bridge is unconditional. B2.1 and B2.2 use `XNormRestr` only in **conclusions**, where `≤` suffices. |

### 3.2 NTSP

| Declaration | Verdict | Reason |
|---|---|---|
| `NTSP.lemlayer1` (TARGET Lemma 5.2) | **FAITHFUL** | `|s| ≤ L`, `L ≥ 1`, uniform in `a, b, ξ, ξ′`. Summability is a proved conjunct (no junk `tsum`). Bound `C/⟨s⟩^d`. `bilinearPhaseIntegral (chi0MomSchwartz)` is ∫∫χ₀(x−a)χ₀(y−b)e[…]. |
| `ntsp_one` (DH23 6.5 (1)) | **FAITHFUL** | A `lintegral` bound `C·D·λ^{2d}` for `d ≥ 2`, `λ ≥ 1`, `∀ s, NTBounds (10d) D (Φ s)`. |
| `ntsp_two`, `ntsp_two_all` (DH23 6.5 (2), (NTSPest2)) | **FAITHFUL** | `d ≥ 3`, `0 ≤ η ≤ 1/20`, `supp Φ ⊂ {|s| ≤ κL}`, `1 ≤ λ ≤ L^η`; per-`s` summability of the modes. **`λ ≤ L^η` is dischargeable:** DH23 L1012 fixes `1 ≤ λ ≤ (log L)⁴`. |
| `ntintlem_one(_gen)`, `ntintlem_two(_gen)` (DH23 6.7) | **FAITHFUL to the corrected source**; disclosed errata | The source prints `μ⁻¹∫ψ(μΩ)…` (both items) and the error `μ^{1−2η}`. Scaling forces `μ∫ψ(μΩ)…` and `μ^{−(1−2η)}`, and Lean uses those (DH21 Lemma 6.5). The Lean bound is **bilinear**: `D_Φ · ‖⟨u⟩^{1−η}ψ‖₁`. The source's single `D` for both norms is non-homogeneous; bilinear is the correct form. `deltaInner F = ∫ ‖x‖⁻¹ ∫_{x^⊥} F(x,w) dw dx` is the coarea reading of `∫∫ δ(⟨x,y⟩) F`. The proved bound pins its value, so it is not a junk 0. |
| `NTBounds N D Φ` | dischargeable; weaker than (NTphibounds) | It bounds Fréchet derivatives in each variable separately through order N. The source's mixed partial bounds `|∂_x^α ∂_y^β Φ| ≤ D` imply `NTBounds` with `D′ = C(d,N)·D`, and all conclusions are linear in `D`. |

### 3.3 ClassJR

| Declaration | Verdict | Reason |
|---|---|---|
| `ClassJ`, `ClassR`, `JSym.Bound`, `RSym.Bound`, `jker`, `rker`, `kcomp` | **FAITHFUL** with four disclosed deviations | `jker = e^{πi(ℓ(t−s)+γ₁t+γ₂s)}`; `rker = χ_∞(a+γ₃)/(a+γ₃) · jker`; `kcomp K L (t,s) = ∫_s^t K(t,z)L(z,s) dz` is Volterra composition on the triangle. Norm "≤ N" means some finite representation with `Σ cᵢ ≤ N`, the source's infimum definition. The deviations, all disclosed in `ClassDef.lean`: (1) Gevrey radius `A^k(2k)!` (F41); (2) general weight θ ∈ [0,1) (DH21 1/4, DH23 1 − η/8); (3) operator-norm derivatives (stronger); (4) `SymReg` regularity made explicit. |
| `ClassJ.comp` (5.3), `ClassJ.comp_R` / `ClassR.comp_J` (5.4), `ClassR.comp_R` (5.5, landed in this window) | **FAITHFUL** | Variable-disjoint composition (`α ∘ inl`, `α ∘ inr`; special variables tracked through `Option`) is class J with norm ≤ `C · N₁ · N₂`. |
| Lemmas 5.6–5.8 (`I_{εα} J I_{μ−εα}`, its R analogue, `I_{εα} I_{μ−εα}`) | not yet stated | — |

### 3.4 Minor arcs (machine bridge)

**Method.** `scratch/Task10-minor-bridge.lean` (sha `14539822a9e4…`) is built in one environment with snapshot 5's
`WaveBDraft.Statements` and the landed `WeylSums.QuadExpSum2/3` (104-module closure). It proves:

```lean
theorem quadExpSum2_of_foundations : type_of% @quadExpSum2   -- snapshot-5 B1.9, verbatim
theorem quadExpSum3_of_foundations : type_of% @quadExpSum3   -- snapshot-5 B1.10, verbatim
```

Each proof is a `simpa` from `WeylSums.quadExpSum2_bound` / `quadExpSum3_bound`, using only three facts:
- `chi0 = Fourier.chi0`, via `WeylSums.chi0_eq_draft_formula`;
- `chi0Vec = latticeCutoff`;
- `eZ x = WeylSums.e x` (`rfl`).

The definitions unfolded are `bilinearLatticeSum`, `cubicLatticeSum`, `cubicQuadraticForm` and `timeSquareWindow`.
**Axioms: `[propext, Classical.choice, Quot.sound]`.** So the drafted anchors' own `sorry` is not used, and the
Foundations theorems imply the frozen-candidate statements **exactly**: same quantifier order, same `Bool` convention
for Λ, same window `{L ≤ max |t| |s|, |t|, |s| ≤ T₀L^{2γ}}`, same exponents `2d − 2(d−1)(1−γ) + η` and
`3d + γ − 2 min(γ, 1−γ)` (with `log L`).

| Declaration | Verdict | Reason |
|---|---|---|
| `WeylSums.quadExpSum2_bound` (TARGET Lemma 5.3, lemlayer2) | **EXACT** (machine bridge above) | — |
| `WeylSums.quadExpSum3_bound` (TARGET lemcubic), both `sel` | **EXACT** (machine bridge above) | `d = 3` and `d ≥ 4` are handled by separate routes, which are internal. |
| `dh23_minor1_bound` (DH23 6.6 (1), (NTlem21)) | **FAITHFUL** | Support `|s| < L^{2γ}`. Bound `C·D·λ^{4d}·L^{2d}`, uniform in `a, b, ξ, ζ`, with an integrability conjunct (no junk integral). The hypotheses are joint coordinate-derivative bounds of total order ≤ 10d, implied by (NTphibounds) (`|α|, |β| ≤ 10d`), plus joint `C^{10d}` and measurability in `s`; both are implicit in the source and dischargeable. |
| `dh23_minor2_normalized_bound` (DH23 6.6 (2), (NTlem22)) | **FAITHFUL** | Weight `⟨s/(δL^{2γ})⟩^{−P}` with `P ≥ 2d` (the source has `P > η⁻²`, so Lean is stronger). `δ ∈ (0,1]`. Bound `C·D·λ^{4d}·L^{2d−2(d−1)(1−γ)+η}`. The source's support "`L ≲ |s|`" is taken as `|s| ≥ L`. This is dischargeable because the complementary NTSP Lemma 6.5 (2) (`ntsp_two`) holds for support `|s| ≤ κL` for **every** `κ > 0`, so a consumer can split at `|s| ∼ L` with any cutoff. |

## 4. REQUIRED

**R1 (ledger).** Add FINDINGS entries for the source errata that the Lean statements correct but the ledger lacks:
- **(a) DH23 L1147–L1155 (Lemma 6.7, `NTintlem`).**
  - `μ⁻¹∫ψ(μΩ)…` should be `μ∫ψ(μΩ)…` in (1) and (2).
  - The error `μ^{1−2η}` in (2) should be `μ^{−(1−2η)}` (cf. DH21 Lemma 6.5).
  - The bound is bilinear in the Φ- and ψ-norms.
  - Found by wt-ntsp; disclosed only in the `Lemma67Final.lean` docstrings.
- **(b) DH23 L2040: `#(A ∩ ℤ^d)` should be `ℤ²`.** Found by wt-nt; disclosed only in the NT-CIRCLE-v2 handoff.

No REQUIRED Lean change.

## 5. OPTIONAL

- **O1.** Export the **unconditional** (disclattice) with 27/41: `card_annulus_disc_le_min_of_circle_error_half_radius`
  instantiated with `abs_card_latticeDisc_sub_area_le_twenty_seven_forty_one`. That makes COUNT's A.2 (1)–(3)
  consumption a single citation.
- **O2.** Main-assembly handoff accuracy: `GateTypes.lean` produces 6 unused-variable linter warnings, in the handoff's
  own `build-GateTypes.log` too. The handoff says "without Lean warnings". This is harmless, since the binder names are
  kept for exact identity, but the report should say so.
- **O3.** At sealing, re-run the E1/E2 comparison against the per-declaration frozen files, with `GaussianData` and
  `WaveBDraft` imports replaced. Optionally add `example : PropansatzGate.{u} = type_of% @propansatz.{u} := rfl` once
  both are in one environment.
- **O4.** NTSP: state the (NTphibounds) ⇒ `NTBounds` implication (`D′ = C(d,N)·D`) as a lemma for the APPROXNT consumer.
- **O5.** COUNT: when `countLemma` and A.2 (2) land, state them in the drafted form, as for `atomCountLemma_bound`.

## 6. Author questions

- **Q1 (ClassJR, packet J2).** The μ[E] parameters are not modelled: "for all μ" is an outer quantifier, so the class-J
  representation may depend on μ arbitrarily, even non-measurably.
  - Does any consumer (DH21 Lemmas 5.9–5.10, Prop 5.1) integrate or differentiate in a μ variable, or turn a μ into an α
    of a later operator?
  - If so, the representation must be jointly regular in μ, and ClassJ should carry μ as a variable.
  - If not, the current form suffices.

## 7. Probes (untracked, `scratch/`)

| File | Purpose |
|---|---|
| `Task10-main-E1.lean` | Helper vs frozen `main` (`==`, `Expr.equal`, `pp.all`), gate bodies, `IsGaussianData` copy, helper axioms, `MainAssembly` import closure and quarantine scan |
| `Task10-main-E2.lean` | Snapshot 5 `propansatz`/`nlsAkBridge` types and `IsGaussianData` |
| `Task10-main-E1n.lean`, `Task10-main-E2n.lean` | The same comparisons, proofs erased |
| `Task10-minor-bridge.lean` | Snapshot 5 `quadExpSum2`/`quadExpSum3` derived from `WeylSums.quadExpSum2_bound`/`quadExpSum3_bound` |

Sha256 prefixes:
- `Task10-main-E1.lean` `647d62c22b37…`
- `Task10-main-E2.lean` `739b5d2837dd…`
- `Task10-main-E1n.lean` `61399ed2f242…`
- `Task10-main-E2n.lean` `6951517f91ea…`
- `Task10-minor-bridge.lean` `14539822a9e4…`

They run against my scratch build roots (`waveb5` for snapshot 5; `glue` for the 148 compiled repository modules, the
reused worktree oleans and the main-assembly modules).
