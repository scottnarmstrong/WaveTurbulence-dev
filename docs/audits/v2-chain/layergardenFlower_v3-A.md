# SEAL AUDIT — `layergardenFlower_v3`, KEY-A (refute-first, independent)

Anchor `WaveTurbulence.layergardenFlower_v3` (`WaveTurbulence/Frozen/Theorems/LayergardenFlowerV3.lean`), sealed by
`e8019624` "Seal layergardenFlower_v3 with its proved assembly" and `1e51bebf` "manifest: ABI hash of the sealed
layergardenFlower_v3" on origin/main (final pushed main `1987105a`; the anchor/provider closure is unchanged by the
later commits, which touch only the other three seals, the root, lakefile, manifest and docs).
Freeze `f8874a9b` (D13). Provider `WaveTurbulence/Provider/LayergardenFlowerV3.lean`, export
`WaveTurbulence.Provider.layergardenFlower_v3`. FLOWER_THM = `WaveTurbulence.Flower.Top.layergardenFlower_v3_proof` in
`WaveTurbulence.Foundations.Flower.Top.Proof` (port `14451183`, merged `c43c7b36`).
Work directory: `<scratch>/seal-audit-layergardenFlower_v3-A/` (clean `git archive 1e51bebf` in `export/`).
Toolchain: Lean 4.35.0 (eb6cafb7). All Lean processes niced 10, one heavy process at a time.

## Verdict table

| Item | Verdict | Key evidence |
|---|---|---|
| (a) Anchor bytes | **PASS** | freeze→seal diff is the one proof-body line `by sorry` → `by exact WaveTurbulence.Provider.layergardenFlower_v3`; prefix `d7203fd6…`, suffix `9f481990…` recomputed = manifest; DRAFT file `9652454c…`; guard OK, module check PASS on the clean export; manifest entry changed in exactly `state`, `abi_sha256`; 107/107 closure hashes match |
| (b) Provider | **PASS** | no anchor import (source, Lake closure); provider type `Expr.equal` anchor type; body is the bare `layergardenFlower_v3_proof`; export used only by the anchor; proof module privately imported; anchor-only probe sees 109 project modules (107 `Frozen.Defs` + anchor + provider), 0 proof-world constants, and the frozen text re-elaborates there to an `Expr.equal` type |
| (c) Axioms | **PASS** | `[propext, Classical.choice, Quot.sound]` for the anchor, provider, FLOWER_THM, the assembly `flowerest1_of_B3s_D6b_452`, its three closed inputs, `CapsStable.flower_v3_of_marked`, `Fam.layergardenFlower_v3_of_cores`, and the consumed sealed anchor `regularAsymptotics` (+ its provider) |
| (d) Hidden hypotheses / vacuity | **PASS** | FLOWER_THM's type is the constant `V2Chain.LayergardenFlowerV3Gate` (0 binders); every chain constant is a `theorem` (gate, `cθGen`, `BcMK` are defs); every named input discharged by a closed theorem (table below); budgets proved in-chain; non-vacuity witnesses compile, standard axioms only |
| (e) ABI | **PASS** | pre-seal `a4a61eea…` reproduced from my own build of the freeze bytes (two probe conventions); post-seal `33a97fdc…` reproduced; prints differ only in the value line; pp.all type byte-identical draft vs sealed (sha256 `7c8bf408…`, same Expr hash) and identical again with the whole proof world loaded |
| (f) Kernel replay | **PASS (quick mode)** | `REPLAY OK (8483s): 213961 constants, no shim, no constant turned into an axiom`; 10,465 project modules loaded (closure 11,671 project / 22,647 total modules); 0 project axioms/opaque/unsafe/partial; 0 direct `sorryAx`/`ofReduceBool`/`trustCompiler`/`ofReduceNat` users; wall 2:22:05, max RSS 6,092,732 KB; replayed oleans = seal sources (11,671/11,671 trace source hashes, 35,013/35,013 olean output hashes) |
| (g) Status fields | **PASS** | DRAFT_ANCHORS 9; UNREGISTERED_SORRIES 0; DRAFT_IMPORT_VIOLATIONS 0; SEALED_THIS_TURN `layergardenFlower_v3` (README status block is stale; see disagreements) |
| (h) Five-bin table | **PASS** | 30 rows: SOURCE 9, STANDING 11, TYPING 1, RULED 9, **EXCESS 0** (`h-binder-table.md`, written before the appendix) |

**Caveat on (f):** quick mode checks 40,618 `WaveTurbulenceVineParam` certificate theorems by statement only, namely those whose proofs use no project constant outside that library. 92,875 VineParam theorems were replayed with their proofs. Full mode was not run.

## (a) Anchor bytes
- `git show f8874a9b:…/LayergardenFlowerV3.lean` (sha256 `9652454c…74af` = brief's DRAFT hash) vs `1e51bebf` (sha256
  `14d13d64…63be`): `diff` = line 112 only. `git log f8874a9b..1e51bebf -- <file>`: `e8019624` only.
- Own region hasher (`tools/hash_regions.py`, guard convention: prefix = bytes up to the line after
  `FROZEN_ANCHOR_PROOF_BEGIN`, suffix = from the line of `FROZEN_ANCHOR_PROOF_END`): prefix `d7203fd68e46e103…b258`,
  suffix `9f48199048606af9…a8d0`, identical at freeze and seal, = manifest.
- `check_frozen_anchors.py --root export` → `FROZEN-ANCHOR GUARD OK` (5m10s); `check_lean_modules.py` → `PASS (13118
  Lean files)` (`check_frozen.out` sha256 `8b6c2e7e…`, `check_modules.out` `eac0bd96…`).
- Manifest freeze (`f8874a9b`) vs seal (`1e51bebf`) for this entry: DIFF `abi_sha256` (`a4a61eea…` → `33a97fdc…`),
  `state` (`DRAFT_SORRY` → `SEALED`), nothing else; `definition_closure` 107 entries, 0 hash mismatches on the export.
  Pre-seal (`c43c7b36`) → seal manifest: only this entry changed.

## (b) Provider
- Imports: `public import Mathlib` + the anchor's 15 `Frozen.Defs.*` (lines 8–23 identical to the anchor's) and
  `import WaveTurbulence.Foundations.Flower.Top.Proof` (private). Lake's resolved closure of the provider (20,671
  modules) does not contain `WaveTurbulence.Frozen.Theorems.LayergardenFlowerV3`; its only `Frozen.Theorems` module is
  `RegularAsymptotics` (SEALED).
- Statement text of the provider = anchor's, token for token (namespace differs: `WaveTurbulence.Provider`).
  Elaborated: replay `provider type == anchor type: true; Expr.equal: true`; same in `probes/full.out`.
- Body: replay `EXACT provider value = (some WaveTurbulence.Flower.Top.layergardenFlower_v3_proof)`; FLOWER_THM type
  `== .const V2Chain.LayergardenFlowerV3Gate []`, 0 binders (`forallTelescope` without unfolding), no level params.
- `type_of% @WaveTurbulence.layergardenFlower_v3 = V2Chain.LayergardenFlowerV3Gate := rfl` compiles. Gate text = frozen
  text token for token (whitespace only). **Gate body vs anchor type (pp.all): not syntactically equal.** They are equal
  after normalizing the `Nat.AtLeastTwo` proof argument of `instOfNatAtLeastTwo`, which the `abbrev` abstracts into
  auxiliary theorems `V2Chain.LayergardenV2Gate._proof_1/2` and `V2Chain.LayergardenFlowerV2Gate._proof_1/2/3`.
  These are Prop proofs, so the difference is proof-irrelevant. Both `Decidable` instances of `if ∀ j, pat j = .plain`
  are `Nat.decidableForallFin (2*Pm) … (fun a => instDecidableEqFixPat (pat a) FixPat.plain)` in both, not
  `Classical.propDecidable`. The kernel accepted the provider := FLOWER_THM step in the replay.
- Export use: `WaveTurbulence.Provider.layergardenFlower_v3` appears in code only in the anchor's proof body; the
  provider module is imported only by the anchor.
- Visibility (`probes/Vis.lean`, setup = Lake's anchor closure + anchor, module mode): 11,501 modules, 109 project
  modules (107 `Frozen.Defs`, anchor, provider), none outside; `env.contains` false for
  `Flower.Top.layergardenFlower_v3_proof`, `V2Chain.LayergardenFlowerV3Gate`, `CompMK.flowerest1_of_B3s_D6b_452`,
  `Fam.layergardenFlower_v3_of_cores`, `regularAsymptotics`; 0 constants under `WaveTurbulence.Flower/V2Chain/Foundations`;
  the verbatim frozen text, re-elaborated there, `Expr.equal` the anchor's type. A non-module probe of the sealed anchor
  against that closure fails (needs the provider's private imports), which confirms the closure excludes them.
- Own setup generator `tools/mksetup.py` (sha256 `e71534f7…`) from `.lake/build/ir/<M>.setup.json`. Audit of
  `scripts/abi_hash_setup.py`: it computes the same quantity as `abi_hash.py`'s probe through `import all <M>` with all
  project `.olean.private` parts added. Its failure test (`stderr` non-empty) aborts on the elan override notice (see
  disagreements). My own M2 probe with that convention reproduces both manifest hashes, and a non-module M1 probe
  reproduces the DRAFT hash.

## (c) Axioms (`probes/full.out`, sha256 `48b588a8…`; replay)
`#print axioms` = `[propext, Classical.choice, Quot.sound]` for: `WaveTurbulence.layergardenFlower_v3`,
`Provider.layergardenFlower_v3`, `Flower.Top.layergardenFlower_v3_proof`, `Flower.CompMK.flowerest1_of_B3s_D6b_452`,
`Flower.MkSlotsI.markedClassRepresentsMK_prefix`, `Flower.ProtWhole.regularComponentTargetI_of`,
`Flower.ProtPin.protBoundGate`, `Flower.CapsStable.flower_v3_of_marked`, `Flower.Fam.layergardenFlower_v3_of_cores`,
`WaveTurbulence.regularAsymptotics`, `Provider.regularAsymptotics`. Reachable `Frozen.Theorems` constants (replay):
`regularAsymptotics` (SEALED) and the anchor only. Independent check: (f).

## (d) Hidden hypotheses and vacuity
Chain (each row: conditional theorem → its named inputs → the closed term supplying each; kinds from the replay, all
`theorem` unless noted). No `AXIOM`/`OPAQUE` among the used constants of any chain value (replay `USES`).

| Theorem | Inputs and their discharge |
|---|---|
| `Flower.Top.layergardenFlower_v3_proof : LayergardenFlowerV3Gate` (0 binders) | `flowerest1_of_B3s_D6b_452 (cθ := MkSlotsG.cθGen)` with `hcθ := le_max_left 1 _` (`cθGen = max 1 (max twoLayerB (filterB chiDNS))`, def); `hB := MkSlotsI.markedClassRepresentsMK_prefix le_rfl`; `hReg := ProtWhole.regularComponentTargetI_of ProtPin.protBoundGate` |
| `MkSlotsI.markedClassRepresentsMK_prefix (hθ : cθGen ≤ cθ)` | `MkSlotsG.markedClassRepresentsMK_prefix_of_repGen hθ classRepGen_prefix`; `classRepGen_prefix := classRepGen_prefix_of MkSlotsO.genSlotObligation` (`:= genSlotObligation_of_gate ProtRT.rootTraceGate`) |
| `CompMK.flowerest1_of_B3s_D6b_452 hcθ hB hReg` | `flowerest1_of_B3s_D6b` with `0 ≤ 452`, `452 ≤ 500` (`norm_num`) |
| `CompMK.flowerest1_of_B3s_D6b` | `⟨C₀, 2 ≤ C₀, hG⟩ := Stage1MKGate.stage1ReductionAtMKFull_of_B3s cP cθ hB` (`:= stage1ReductionAtMKFull_of cP cθ hB b2eIX zeroVanish_prefix`); then `flowerest1_of_gate … ⟨C₀, by omega, hG⟩ hReg` |
| `flowerest1_of_gate` → `flowerest1_of_B4_D6b` | `flowerest1_of_inputs … hB4 (hD7 := SelRes.selSumTargetT) hReg` |
| `CompMK.flowerest1_of_inputs` | `CapsStable.flower_v3_of_marked 18000 (0 ≤ 18000) (18000 ≤ 24000) (markedComponentBoundAtI_18000 …)`; `markedComponentBoundAtI_18000 := markedComponentBoundAtI_of (nonregPrefix … (wtPrefix_sel_of_full hB4) hD7) (hReg 17999 _)` |
| `CapsStable.flower_v3_of_marked B hB0 hB hM` | `CapsComp.flower_v3_of_marked_of_stable (hst := capsTwistStable)` |
| `CapsComp.flower_v3_of_marked_of_stable hst` | `MkAsm.flower_v3_of_marked_of_caps (capsDecompF_of_stable hst) (capsDecompG_of_stable hst)` |
| `MkAsm.flower_v3_of_marked_of_caps hF hG` | `MkAsm.flower_v3_of_marked (coreFOfComponents_of_caps hF) (coreGOfComponents_of_caps hG)` |
| `MkAsm.flower_v3_of_marked hF hG` | `Fam.layergardenFlower_v3_of_cores (Bc := BcMK = 100000·d, def) BcMK_hBc (hF …) (hG …)` |
| `Fam.layergardenFlower_v3_of_cores` | `Cases.layergardenFlower_v3_of_families Cfam Ufam Cfam_pos Ufam_pos (filtFamily_explicit …) (gainFamily_of_core …)` |
| `Cases.layergardenFlower_v3_of_families` | `FlowerTop.layergardenFlower_v3_of_inputs hPlain hCut1 hCut2 hCut2Zero (hCouple := coupleHalf_of_spine (Spine.stage1ReductionGate_of_V5' VineEst.vineEstCanonLayerHalfMK) FinalCountAsm.finalCount_half)`; the four case inputs come from proved `casePlain_of_filt`, `cut1_clause_of_filt`, `cut2zero_clause_of_filt`, `cut2pos_nonplain_of_filt`, `cut2pos_plain_of_gain` |

- Budget constants are fixed inside the chain and their side conditions are proved:
  - `cP = 452` (`0 ≤ cP ≤ 500` by `norm_num`);
  - `C₀ ≥ 2`, the existential from B4, giving `1 ≤ C₀` by `omega`;
  - `cθ = cθGen ≥ 1` by `le_max_left`;
  - `B = 18000 ≤ 24000` (R175) by `norm_num`;
  - `hReg` used at `17999`;
  - `BcMK d = 10⁵d` with the proved `BcMK_hBc : BcMK d + 80d + 3 < (100d)³`.
- Universe-level and section-variable check: FLOWER_THM's elaborated type is the gate constant with no binders, so no
  `variable`/`include` adds a premise. The replay found 0 MISSING constants and 0 type-conflicting duplicate names.
- Non-vacuity (`probes/NonVac.lean`, sha256 `a2c76c3f…`, freeze environment, compiles; `nv_wke`, `nv_δD`,
  `nv_remainder`, `nv_hcut` use only the standard axioms):
  - prefix ranges: `d = 3`; `γ = 3/4` (satisfies `1/2 < γ`); every `η₀, ν₀ > 0` leaves `Ioc 0 _` non-empty;
    `φin = 0 ≥ 0` and `φ ≡ 0` satisfy `IsWKESolution 0 τ★ (fun _ => 0)` for every τ★ (`collisionOp 0 0 0 = 0`);
    every `P₀`, `L₀` leaves an upper range;
  - δ and 𝔇: for every τ★ > 0 and every prover δ₀ > 0 there exist `δ ∈ (0, δ₀]` and `D ≥ 1` with `τ★ = Dδ`;
  - body: `p = 0 < 𝔇`; `RemainderBound P 0 p` holds; `t = p + 1/2`, `s = p + 1/4`; `N = 0`; inhabitants for every
    `FlowerKind`, pattern vector and `dagger` (`none`/`some`);
  - cutoffs: `cut1 = cut2 = none` makes `hcut` vacuous, and `cut2 = some j₂` with `cut1 = some j₁` is satisfiable:
    `n ≡ m` with `m ≥ (2^{j₁}L)^{10} L` gives `(2^{j₁}L)^{10} ≤ ‖n/L‖` (`d ≥ 1`, `L > 0`);
  - couple clause: `kind = L0` with either `dt`, and `kind = tr` with `dt = true`, are both admitted.

## (e) ABI (`abi/`)
- DRAFT rebuild: the freeze-commit provider stub (sha256 `a208920d…`) and the DRAFT anchor (sha256 `9652454c…`), compiled to
  my own oleans against main's Mathlib/`Frozen.Defs` build (Lake's anchor closure, module mode); only warning: the
  single authorized `sorry`.
- `#print WaveTurbulence.layergardenFlower_v3` → sha256 of stdout:
  - DRAFT, non-module probe `import M` (`abi_hash.py` convention) **`a4a61eea…a840`**;
  - DRAFT, module probe `import all M` (`abi_hash_setup.py` convention) **`a4a61eea…a840`**;
  - sealed (main's oleans), `import all M` **`33a97fdc…5044`** = manifest.
  - `diff out-m1-draft.txt out-m2-seal.txt`: line 35 only, `sorry` → `WaveTurbulence.Provider.layergardenFlower_v3`.
- pp.all type: `ppall-draft-anchorBuild.txt` = `ppall-seal-anchorBuild.txt` = `ppall-seal-anchor.txt` (the full proof
  world loaded), all sha256 `7c8bf408…d820`. `Expr.hash` 2344925519 in both environments. No instance, coercion or
  notation drift from the new imports.

## (f) Kernel replay (`replay/`)
- Adapted from `<scratch>/seal-lg2/replay/Replay.lean` (sha256 `6c943568…`).
- Diff (`replay/Replay.diff`, sha256 `199eaebf…`):
  - root module and constant;
  - the `wanted` list (flower chain);
  - exactness checks: anchor value; provider `==`/`Expr.equal`; gate value vs anchor type; FLOWER_THM type is the gate;
  - used constants with their kinds per chain value, printed after reachability.
- Closure computation, base environment, lazy loading, stub policy and the single `Kernel.Environment.replay` are
  unchanged.
- `replay.sh` (sha256 `298df1ca…`) sets `LEAN_PATH` to main's build directly (no `lake env` in the read-only checkout).
  `Replay.lean` sha256 `56b9e79e…`; output `Replay-quick.out` sha256 `796850d1…`.
- Results:
  - closure 22,647 modules (10,976 library, 11,671 project); 245,359 project constant names indexed; reachable 223,796;
    MISSING 0;
  - project modules loaded: 10,465;
  - 1,591 same-name constants appear in two loaded modules, none with a different type or (non-theorem) value;
  - project AXIOMS / OPAQUE / UNSAFE / PARTIAL: none;
  - direct users of `sorryAx`/`ofReduceBool`/`trustCompiler`/`ofReduceNat`: none;
  - core axioms referenced directly: `Quot.sound`, `Classical.choice`, `propext`;
  - kinds reached: theorem 191,244, def 21,234, inductive 563, ctor 776, rec 144;
  - **`REPLAY OK (8483s): 213961 constants`**: elapsed 2:22:05, max RSS 6,092,732 KB.
- Source identity:
  - for all 11,671 project modules of the closure (`trace/closure-modules.txt`), the Lake `.trace` source hash
    (`Hash.ofText`, recomputed by `trace/H.lean`) equals the hash of the file in `export/` (11,671/11,671);
  - the Lake output hashes of every olean part on disk equal the trace's recorded outputs (35,013/35,013,
    `trace/H2.lean`);
  - 1,791 VineParam modules were built in the worktree `port-vp` from identical text.
- Independent source scan of the 11,671 closure files (comments and strings stripped): 0 code-level `sorry`, `admit`,
  `axiom`, `opaque`, `implemented_by`, `@[extern`, `native_decide`, `ofReduceBool`, `unsafe`, `partial def`,
  `skipKernelTC`, `set_option debug.`.

## (g) Status fields (manifest `1e51bebf`, guard on the clean export)
- DRAFT_ANCHORS: **9**:
  - `Frozen/Theorems/Main.lean`, `Fixedpoint.lean`, `Layergarden.lean`, `LayergardenFlower.lean`, `Propansatz.lean`;
  - `MainV2.lean`, `PropansatzV2.lean`, `FixedpointV2.lean`, `LayergardenFlowerV2.lean`.
- UNREGISTERED_SORRIES **0** (guard OK). DRAFT_IMPORT_VIOLATIONS **0** (guard quarantine check OK).
- SEALED_THIS_TURN **`layergardenFlower_v3`** (the only manifest entry changed by `e8019624`/`1e51bebf`). Sealed: 18
  theorems + 300 definitions.

## (h) Five-bin binder table
Full table in `h-binder-table.md` (sha256 `d73f760b…`). Source reconstruction in `h-source-reconstruction.md` (sha256
`5544233a…`) was written from the raw TeX (re-hashed `493eef6b…27cb`) and the rulings before reading the Lean docstring.
Ruling chain verified textually:
- the D7-approved text (`docs/review/WAVE-B-B1-B112.md` §1.2) = frozen v1 statement;
- v2 = v1 + `1 / 2 < P.γ →` (D10);
- v3 = v2 with `flowerSum` → `flowerSumP` (D13), and `flowerSumP` = `flowerSum` with `cutWeight1/2` → `cutWeight1P/2P`.

Counts: SOURCE 9, STANDING 11, TYPING 1, RULED 9, **EXCESS 0**.

## Disagreements with the claim appendix and the seal logs (read after my results)
1. **Binder table granularity and bins, not EXCESS.** The appendix has 23 rows (SOURCE 7, STANDING 11, TYPING 0, RULED
   5); mine has 30 (9/11/1/9). The rows I split:
   - `R` (TYPING) from `RemainderBound` (RULED);
   - `pat` from `dagger`;
   - the couple clause into 4 rows;
   - `t` from `s`.

   Bin differences, none of which involves EXCESS:
   - `Pm ≥ P₀` and `δ ∈ (0, δ₀]`: appendix STANDING, mine SOURCE (they are premises of Prop flowerest1 itself, L2279);
   - `p < P.D`: appendix SOURCE (L708, L760), mine STANDING (L610 range).

   Citations: the appendix gives C₁ as T L608, which is correct. My first draft had L606 and also L609 for the p-range
   (correct: L610); I corrected both, and no bin changed.

   Not in the appendix: the couple clause claims `t ∈ (p, p+1)` only, while T (trterm1) L2309 has `t ∈ [p, p+1]`
   (endpoints are not claimed, as approved by D7 clause (2)), and `k : Mom d` is more general than ℤ_L^d.
2. **Gate vs anchor.** The appendix and brief expect a token-for-token match, and the seal log reports
   "PROVIDER TYPE TEXT = ANCHOR TYPE TEXT (pp.all)" (provider), with the gate checked only by `rfl`. I find that the
   provider is `Expr.equal` to the anchor, but the gate's pp.all differs from the anchor's in the `Nat.AtLeastTwo` proof
   arguments (abstracted `_proof_k`). Benign: the difference is proof-irrelevant and the kernel accepted it.
3. **Chain addition.** The brief's expected chain omits the couple clause. It is discharged in
   `Cases.layergardenFlower_v3_of_families` by `coupleHalf_of_spine (Spine.stage1ReductionGate_of_V5'
   VineEst.vineEstCanonLayerHalfMK) FinalCountAsm.finalCount_half`: proved theorems of the `layergarden_v2` proof world,
   used directly rather than through the frozen `layergarden_v2` export. This is allowed (proved theorems), and the
   replay covers it.
4. **Seal logs.** The first live run (`live-20261108T191351Z`) aborted at the seal script's exact-type probe:
   `Unknown identifier WaveTurbulence.V2Chain.LayergardenFlowerV3Gate`, because its probe did not import `GateTypes`.
   This is consistent with my visibility result, and the second run added the import.
   The second run (`live-20261108T193926Z`) sealed all four anchors but ended `RESULT: ABORTED` at the final "full ABI
   check": `probe failed for WaveTurbulence.Mom`, caused by elan's override notice on stderr (`full_abi.log` has 0 OK
   lines). The brief's "full 327-anchor ABI OK" for `1987105a` is therefore **not evidenced in the seal-prep logs I
   could read**. This does not affect this anchor: I reproduced its pre- and post-seal hashes independently, and the
   guard passes.
   All of the seal log's checks for this anchor agree with mine: pre `a4a61eea…`, post `33a97fdc…`, PRINT DIFF, axioms,
   RECHECK body-only, DRAFT_SORRY 9.
5. **Brief labels.** The brief calls `1e51bebf` the "Seal commit". It is SHA2 (the ABI manifest commit); SHA1 is
   `e8019624`. Both were audited.
6. **README.** The status block (at `1e51bebf`, `1987105a` and current `e1449ba4`) still says "DRAFT_ANCHORS: 10 …
   layergardenFlower v1/v2/v3" and "SEALED: 17 theorems". It is stale: the manifest has 9 DRAFT and 18 sealed theorems
   at `1e51bebf`, and fewer DRAFT after the later seals. This is documentation lag, not a seal defect.

## Artifacts (sha256)
- Clean export: `export/` (`git archive 1e51bebf`).
- `freeze-anchor.lean` `9652454c…`; `seal-anchor.lean` `14d13d64…`.
- `probes/`: `Vis.lean` `d525e96a…` / `vis.out` `2f101ec0…`; `Full.lean` `49af354a…` / `full.out` `48b588a8…`;
  `NonVac.lean` `a2c76c3f…` / `nonvac.out` `9fd363cb…`; `PP_draft.lean` `c704eac9…`, `PP_seal.lean` `d4a6f978…`.
- `abi/`: `M1.lean` `6040f5ab…`, `M2.lean` `8b9799dc…`, outputs `a4a61eea…` (draft ×2), `33a97fdc…` (seal).
- `replay/`: `Replay.lean` `56b9e79e…`, `replay.sh` `298df1ca…`, `Replay.diff` `199eaebf…`, `Replay-quick.out`
  `796850d1…`.
- `trace/`: `H.lean` `3148a5e6…`, `H2.lean` `31193810…`, `pairs-full.txt` `c9c58eab…`, `outs-full.txt` `7e88ac51…`.
- `tools/`: `mksetup.py` `e71534f7…`, `hash_regions.py` `ef30f3b6…`, `manifest_diff.py` `340ed8e0…`.

`layergardenFlower_v3` may be recorded as PROVED (key A)
