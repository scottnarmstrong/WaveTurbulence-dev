# Seal audit: `WaveTurbulence.wkelwp` (Prop 3.2), first seal (Task 12)

Auditor: `wt-orch` (Opus), refute-first, following the lean-orchestrator seal checklist. Date: 2026-11-03.

**Subject.** Seal commit `53e73e4` on main, merged into `w/orch`. Freeze commit `8d1d2e3` (D6, "Freeze Wave A").

**Manifest entry `wkelwp_v1`.**
- export `WaveTurbulence.wkelwp`, path `WaveTurbulence/Frozen/Theorems/Wkelwp.lean`;
- implementation `WaveTurbulence.Provider.Wkelwp` / `WaveTurbulence.Provider.wkelwp`;
- source TARGET L598–L601 (TeX sha256 `493eef6b…`).

**Evidence base: my own independent build.**
- The anchor's whole project closure (196 modules; 193 compiled from this worktree's sources, which include the seal
  commit), one `lake env lean` at a time with `nice -n 5`, built with **0 errors and 0 warnings**.
- The frozen-anchor guard was run on a clean `git archive HEAD` export.
- No result from the seal commit's own logs is relied on.

## Verdict: PASS on all five items

| Item | Verdict |
|---|---|
| (a) anchor body and frozen bytes | **PASS** |
| (b) provider: no anchor import; statement equals the anchor; consumes exactly the four lemmas | **PASS** |
| (c) `#print axioms WaveTurbulence.wkelwp` | **PASS**: `[propext, Classical.choice, Quot.sound]` |
| (d) the chain under `WKEL2.wkelwp_blowup` hides no hypothesis that weakens conjunct 3 | **PASS** |
| (e) the `abi_sha256` change is only the proof term | **PASS** (both hashes reproduced) |

`wkelwp` may be recorded as `PROVED`.

## (a) Anchor bytes

- `git diff 8d1d2e3 HEAD -- WaveTurbulence/Frozen/Theorems/Wkelwp.lean` is a single changed line in the proof region:
  `  by sorry` became `  by exact WaveTurbulence.Provider.wkelwp`.
- I recomputed the prefix and suffix hashes with the checker's region convention (prefix through the
  `FROZEN_ANCHOR_PROOF_BEGIN` line, suffix from the `FROZEN_ANCHOR_PROOF_END` line). For **both** the freeze-commit
  file and the sealed file they equal the manifest: prefix `85a090253baf3c29…`, suffix `9f48199048606af9…`. There are
  no CR bytes.
- The body matches the guard's SEALED rule exactly (`by exact <implementation.export>`).
- `python3 -I scripts/check_frozen_anchors.py --root . --manifest manifest/frozen.json` on a clean `git archive HEAD`
  export prints **`FROZEN-ANCHOR GUARD OK`**. My worktree's untracked `scratch/` probes deliberately import the
  quarantined `main` anchor, hence the clean export.
- Other seal-commit changes are consistent:
  - manifest `state` is `DRAFT_SORRY → SEALED` and only `abi_sha256` was rewritten;
  - the anchor and provider left the lakefile quarantine list (`main`'s remain);
  - the root imports the anchor.
  - The provider is imported only by the anchor (`git grep`).

## (b) Provider

- **No anchor import.**
  - Source imports: Mathlib, `Frozen.Defs.{Mom, CollisionOp, IsWKESolution, WeightedL2Norm}`,
    `Foundations.WKE.{Existence, Uniqueness}`, `Foundations.WKEL2.Blowup`.
  - In the compiled environment, the provider's transitive import closure contains no `Frozen.Theorems.*` module and
    no other project provider. My filter's only hit, `Lean.Server.CodeActions.Provider`, is a Lean core module.
- **Statement equals the anchor** (`scratch/Task12-seal-probe.lean`):
  - Binders: `d` is implicit vs default; `hd` is `autoParam (3 ≤ d) _` vs `3 ≤ d`; `φin` is implicit vs default.
    Each binder type equals the anchor's after unwrapping `autoParam`.
  - The conclusions after the three binders are identical (`Expr ==` **true**, `Expr.equal` **true**). Universe
    parameters: none.
  - This is exactly the declared design (implicit `d`, `φin`; `autoParam` `hd`), so that `by exact` seals.
- **Consumption.** `set_option pp.proofs true in #print WaveTurbulence.Provider.wkelwp`
  (`scratch/Task12-provider-print.lean`) shows the project constants of the proof term are exactly:
  - `WKE.tauMax`, `WKE.tauMax_pos`, `WKE.lt_tauMax_iff`, `WKE.isWKESolution_unique`, `WKEL2.wkelwp_blowup`;
  - plus the statement's frozen definitions `Mom`, `IsWKESolution`, `weightedL2Norm`, and the provider's own
    auxiliaries (`_auto_1`, an `omega` proof `_proof_1_1`).

  There is no other lemma. The witness `τ_max = WKE.tauMax φin` is forced anyway by conjunct 2, the characterization.

## (c) Axioms

`#print axioms WaveTurbulence.wkelwp` and `#print axioms WaveTurbulence.Provider.wkelwp` both give
`[propext, Classical.choice, Quot.sound]`. This covers the whole chain, including the Theorem 7 machinery: there is
no `sorryAx` and no custom axiom.

## (d) The chain under `WKEL2.wkelwp_blowup`

- **The export itself.**
  - `wkelwp_blowup (d : ℕ) (hd : 3 ≤ d) (φin : 𝓢(Mom d, ℝ))` concludes **exactly** conjunct 3 of the anchor, with
    `WKE.tauMax φin` in place of the existential `τ_max`:
    `τmax < ⊤ → ∀ s > d/2 − 1, ∀ M, ∃ τ₀ ≥ 0, τ₀ < τmax ∧ ∀ τ★ > τ₀, τ★ < τmax → ∀ φ solution on [0,τ★], M < ‖⟨k⟩^s φ(τ★)‖_{L²}`.
  - There is no other hypothesis: no assumed trilinear estimate, existence, persistence or solution equivalence.
    `WKEL2/BLOWUP-CHECK.md` makes the same claim, and I confirmed it from the source.
- **The Theorem 7 exports**, checked against `docs/research/git20-general-d.md` Theorem 7 (d ≥ 3, s > d/2 − 1,
  measurable φᵢ with finite Z_s norms, constant depending only on (d, s)):
  - Binders of `exists_collisionTerm_bound` (`Trilinear.lean`, all `j : Fin 4`), its per-term versions (`j = 0` in
    `GainTrilinear`, `j = 1, 2, 3` in `LossOne/Two/ThreeTrilinear`) and `exists_collisionOp_bound`
    (`CollisionBound.lean`, the frozen `collisionOp`):
    - `hd : 3 ≤ d`, `hs : d/2 − 1 < s`;
    - `∃ C ≥ 0` **before** the inputs (so it depends only on d, s);
    - for all `f₁ f₂ f₃`, `Measurable fᵢ`, `MemLp (weightedFunction s fᵢ) 2`.
  - Conclusion: `MemLp` of the output **and** `‖·‖_{Z_s} ≤ C ∏ ‖fᵢ‖_{Z_s}`. The `MemLp` conjunct makes the norm
    genuine, not a junk value of `weightedL2Norm`.
  - Exactly Theorem 7's hypotheses, with "finite Z_s norm" as the honest `MemLp` condition. **No extra
    hypothesis.**
- **The strict threshold.** `s > d/2 − 1` is kept, the note's §8 shows it is sharp, and the anchor's conjunct 3 uses
  the same strict inequality.

## (e) ABI hash

`scripts/abi_hash.py` hashes the stdout of the two-line probe `import <module>` / `#print <export>`. I ran exactly
that probe (`scratch/Task12-abi-probe.lean`) on two builds:

| Build | `#print` output sha256 | Manifest |
|---|---|---|
| Freeze-commit anchor (`by sorry`), compiled in a separate root | `5e8b4769f891…` | old `abi_sha256` before `53e73e4`: `5e8b4769f891…` ✓ |
| Sealed anchor | `07e3ec1e8b0d…` | new `abi_sha256`: `07e3ec1e8b0d…` ✓ |

`diff` of the two outputs (`scratch/Task12-print-{preseal,sealed}.txt`) is one line, the proof term:

```
< fun d hd φin => sorry
---
> fun d hd φin => WaveTurbulence.Provider.wkelwp hd
```

The type text (lines 1–22) is byte-identical. So the `abi_sha256` change is due only to the proof term, as the seal
commit message states.

## Probes and evidence (untracked, `scratch/`)

| File | sha256 |
|---|---|
| `Task12-seal-probe.lean` (binders, bodies, axioms, import closure) | `ee80ba800004…` |
| `Task12-provider-print.lean` (`#print` with `pp.proofs`) | `dd600ec68e14…` |
| `Task12-abi-probe.lean` (identical to `abi_hash.py`'s probe) | `86914b0ddf34…` |
| `Task12-print-preseal.txt` / `Task12-print-sealed.txt` | `5e8b4769f891…` / `07e3ec1e8b0d…` (= the two ABI hashes) |

**Status fields:**
- DRAFT_ANCHORS: 1 (`WaveTurbulence/Frozen/Theorems/Main.lean`);
- UNREGISTERED_SORRIES: 0 in the committed tree (guard OK);
- DRAFT_IMPORT_VIOLATIONS: 0 (guard OK);
- SEALED_THIS_TURN: audited `WaveTurbulence.wkelwp`.
