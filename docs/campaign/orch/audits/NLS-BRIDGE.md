# NLS-BRIDGE audit (Task 14a): the proof of `nlsAkBridge` (B1.4)

Auditor: `wt-orch` (Opus), refute-first. Date: 2026-11-03.

## Inputs

**Scratch** (`/home/scott/wt-scratch/nls-bridge/`):
- `NlsAkBridge.lean` (`16f2a467c56f…`), `BridgeDefinitions.lean` (`fd14df951333…`), `TypeAudit.lean`
  (`256ac8b6080a…`), `HANDOFF.md`;
- `WaveBDraft/{Core,System}.lean`, which are **byte-identical** to `waveb-snap-5`.

**Landed** (main, merged into `w/orch` as `54dc078`): `Foundations/NLS/BridgeWeights.lean` (`97de70fb47c3…`),
`BridgeReduction.lean` (`498be372ad64…`), `BridgeMeasurability.lean` (`dd296b94549b…`).

**Build.** I compiled the three landed modules and the scratch `BridgeDefinitions` and `NlsAkBridge` myself, on my
snapshot-5 modules: 0 errors, 0 warnings, 0 `sorry`.

## Verdict: PASS

`WaveTurbulence.NLSBridge.nlsAkBridge` is proved at **exactly** the snapshot-5 type of `nlsAkBridge`, using only
`propext, Classical.choice, Quot.sound`. It carries no extra hypothesis.

## Checks

| Check | Result |
|---|---|
| Exact type | In one environment importing snapshot 5's `WaveBDraft.Statements` (the drafted anchor) and `NlsAkBridge` (`scratch/Task14a-nlsAkBridge-check.lean`): the types are alpha-equivalent (`Expr ==` **true**), and `example : type_of% @WaveTurbulence.nlsAkBridge.{0} := @WaveTurbulence.NLSBridge.nlsAkBridge.{0}` elaborates. `Expr.equal` is false only through hygienic instance-binder names: after canonicalizing them, the printed types are **identical** (`Task14a-nlsAkBridge-types.lean`). Universe parameters `[u]` on both. |
| Axioms | Proof: `[propext, Classical.choice, Quot.sound]`. The drafted anchor shows `sorryAx`, as expected. |
| No smuggled hypothesis | This follows from the exact type. All four conjuncts are retained verbatim, including `1 ≤ D`, item (4)'s `t ∈ Icc 0 T`, and the absence of any measurability premise on the selection `U`. |
| Quarantine | `NlsAkBridge` imports `BridgeDefinitions` (only `WaveBDraft.System`, definitions) and the three landed `Foundations/NLS/Bridge*` modules. It does **not** import `WaveBDraft.Statements` or any `sorry`-carrying draft. Statements was imported only in my comparison probe. |

## The bridges (statement level)

- **`isASolution_iff_nls`** (`Iff.rfl`). The snapshot's `IsASolution` and the landed `NLS.IsAkSolution` have the same
  body; this agrees with Task 10's `isASolution_iff_isAkSolution`.
- **`zNormOn_lt_top_iff_bound`.** `ZNormOn L s S a < ⊤ ↔ ∃ C, ∀ t ∈ S, ∀ n, ⟨n/L⟩^s |a t n| ≤ C`. This is a faithful
  unfolding of the snapshot's `ZNormOn` as a supremum.
- **`isAkBounded_iff_zNormOn`.** `NLS.IsAkBounded L T a ↔ ZNormOn L (d+1) (Icc 0 T) a < ⊤`. The landed class bounds
  `(1+|n/L|²)^{(d+1)/2}|a|` uniformly on `[0,T]`, which is `⟨n/L⟩^{d+1}` by `bridge_sqrt_rpow`.
  - The forward item (1) needs `∀ Λ, ZNormOn L Λ (Icc 0 D) a < ⊤`, **every** real Λ, which is stronger than the class.
    It is proved from uniform rapid decay of the reduced coefficients (`bridge_uniform_weight_bound`); it is not
    assumed.
- **`isRapidDecay_of_draft`.** The snapshot's backward premise (`∀ s, ∃ C, ∀ n, ⟨n/L⟩^s |c n| ≤ C`) implies the
  landed `IsRapidDecay`. This is the right direction: the draft's own hypothesis feeds the landed theorem, and no
  landed condition is added to the statement.
- **Gauge.** `bridge_reducedCoeff_eq` gives the explicit reduced coefficient with both phases
  (`e^{−iπδL^{2γ}|n/L|²t}` and `e^{−2iαMδT_kin t}`) and the mass `M = L^{−d}Σ|c_n|²`. That is exactly the snapshot's
  `let M`/`let a`, as the exact-type check confirms.
- **Measurability.** `bridge_measurableSet_solvable` and `bridge_measurable_indicator_energy` require `0 < L`,
  `0 < T`, a measurable data map and an arbitrary admissible selection. `0 < T` is derived inside the proof from
  `1 ≤ D`, `0 < δ` and `α = L^{−γ}`.

## Notes

- **Landing.** This is a proof of a frozen-candidate anchor. After the Wave B freeze it becomes `Provider.nlsAkBridge`
  (or a Foundations theorem consumed by `main`'s gate). It must not import the frozen anchor.
- **Interaction with the main assembly.** The gate `NlsAkBridgeGate` equals the drafted type up to hygiene and one
  `Prop` instance proof (Task 10). So `main_of_propansatz_nlsAkBridge _ NLSBridge.nlsAkBridge` typechecks, which the
  handoff's `TypeAudit` also checks. The handoff's binder-name note applies only to `TypeAudit`'s copy; the theorem's
  own header is verbatim.
