# Statement audit: INDUCT assembly (`propansatz_of_gates`, wt-cumul)

Auditor: `wt-orch`, refute-first. Date: 2026-11-04 (Task 29a). Findings only; nothing was edited.

**Scope.**
- `/home/scott/wt-scratch/induct`: `HANDOFF.md`, `PropansatzAssembly.lean`, `FinalAudit.lean`.
- The context and numerics modules: `InductContext`, `SmallDeltaChoice`, `AssemblySizeNumbers`.
- The prefix alignment (`PrefixAlignment`, `GateConstants`) and the base case (`AnsatzBase`, `BaseEvent`).

## Verdict

**PASS.** No statement defect. Two record-keeping findings: I-1 and I-2.
- **Exactly three gates.** `propansatz_of_gates` has exactly the type
  `LayergardenGate → FixedpointGate.{u} → WkeTaylorGate → PropansatzGate.{u}`, checked on the elaborated type.
- **The gate types are snapshot 7's.** The four types equal snapshot 7's B1.2, B1.3, B1.5 and B1.1 statements, compared
  in one environment. The 158 snapshot constants they use are identical to my own snapshot-7 build.
- **No smuggled hypothesis.** Every field of `InductContext` is discharged inside `propansatz_of_gates`, from the
  prefix data and the three gates. Each witness is chosen where the `(Π)` order allows.
- **Axioms:** [propext, Classical.choice, Quot.sound].
- **Base case.** The approved reading is inside the frozen statement and changes no level-0 expectation.

## 1. Inputs

**Pinned copy.**
- I copied the tree at 05:33 UTC: 989 files; the digest of their sha256 list is `47ee813f4c1a…`.
- I re-verified it unchanged later in the audit.

**Key files** (sha256 prefixes):

| file | sha256 |
|---|---|
| `HANDOFF.md` | `f8ec3e1406bb…` |
| `PropansatzAssembly.lean` | `38d97d41854f…` |
| `FinalAudit.lean` | `4d5640492ba2…` |
| `GateTypes.lean` | `14422e2b7d5b…` |
| `PrefixAlignment.lean` | `fb2847b8d1e0…` |
| `GateConstants.lean` | `f60851de90d8…` |
| `InductContext.lean` | `a69ca50737c1…` |
| `SmallDeltaChoice.lean` | `720fef5b6b25…` |
| `AssemblySizeNumbers.lean` | `1edb0f0d3eb4…` |
| `PrefixInduction.lean` | `24f4fde2b5db…` |
| `AnsatzBase.lean` | `fe5c932780cf…` |
| `BaseEvent.lean` | `579f4cd81db0…` |
| `WaveBDraft/Statements.lean` | `9c605bf82b41…` |

## 2. The gate types against snapshot 7

**The B1 copies.**
- `WaveBDraft/{Core,System,Lemmas}.lean` are byte-identical to snapshot 7, and to snapshot 5.
- `WaveBDraft/Statements.lean` is snapshot 7's file without its 10 theorem anchors. The anchors' orphaned docstrings
  `/--` become comments `/-`. A script compared the 218 non-blank lines: equal.
- So no draft anchor is imported, and every definition is verbatim. No local module shadows a `WaveTurbulence.*`
  module.

**One environment.** I wrote a probe in INDUCT's own environment (dev build for Wave A).
- It unfolds `GateTypes`' `…Gate`/`…Body` abbreviations.
- It elaborates snapshot 7's statement texts in the same file, with the opens of `WaveB1-Statements.lean`.
- It compares the two after instance synthesis, zeta reduction of the local `let`s, and erasing proofs.
- **All four are syntactically equal.** In raw form, `PropansatzGate` is already equal. The other three differ only
  in proof terms, and in `have` (INDUCT) against `let` (snapshot) for the local `U`/`Ntr` abbreviations.

**The theorem's type.** The type of `propansatz_of_gates` is literally the four-constant arrow above. Its only level
parameter is `[u]`.

**Closure.**
- I dumped the 158 snapshot constants reachable from the four gates: `WaveBDraft` modules and Wave A frozen
  definitions, normalized as in Task 24.
- The dump in INDUCT's environment equals the dump in my snapshot-7 build: **158/158 identical**.
- F68 does not reach INDUCT: `PatValid` and `flowerSum` are not in the closure, and INDUCT imports no Flower module.
  The handoff's "snapshot 5" result therefore holds verbatim for snapshot 7.

## 3. No hypothesis through the context or numerics modules

**`propansatz_body_of_context (H : InductContext P) : PropansatzBody P`.** The context is its only hypothesis.
`propansatz_of_gates` builds the context field by field:

| field | discharged by |
|---|---|
| `dimension`, `gamma_le_dimension` | `3 ≤ d`; `γ < 1 ≤ d` |
| `eta_pos`, `delta_pos`, `nu_nonneg` | the prefix intervals |
| `delta_le_one` | `δ ≤ δ₀ ≤ 1` |
| `C1_nonneg`, `C2_nonneg` | `1 ≤ C₁`, `1 ≤ C₂` from the gates |
| `time_range` | `τ* = Dδ` |
| `initial_nonneg`, `wke` | the prefix premises on `φin`, `φ` |
| `layergarden`, `fixedpoint`, `taylor` | the three gates at the same parameter tuple (`gates_common_prefix`) |
| `B`, `B_ge_one`, `phi_bound` | `uniform_schwartz_bracket_bound` for `φ` (a theorem) |
| `Cmom`, `Cmom_ge` | `⌈B + 4⌉₊` |
| `size` | `L ≥ L₀` |
| `small_delta` | `δ ≤ exp(−8·10⁶/ν)`, through `delta_half_power_le_of_threshold` |
| `small_taylor` | `δ ≤ e^{−1}/C₁` |

**The numerics modules state no hypotheses.**
- `AssemblySizeNumbers` defines `assemblySizeK` and `assemblySizeThreshold`. These are explicit numbers in `d`, `η`
  (through `θ₀`), `D` (through `Λ₀`), `C₁`, `C₂`, `δ`, `Cmom` and `B`. Its theorems assume only the size inequality.
- `SmallDeltaChoice` is one arithmetic theorem.
- A comment-stripped token scan of INDUCT's tree finds no `sorry`, `admit`, `axiom`, `opaque`, `extern` or budget
  option.

**The `(Π)` order.** `WTPrefix` is
`∀d,γ ∃η₀ ∀η,φin,τ*,φ ∃C₁ ∃ν₀ ∀ν ∃δ₀ ∀δ,D ∃C₂ ∃L₀ ∀L`. The witnesses:

| witness | depends on |
|---|---|
| `η₀` = min of the gates' `η₀` | `d`, `γ` |
| `C₁` = wkeTaylor's `C₁`; `ν₀` = min of the gates' `ν₀` | everything up to `φ` |
| `δ₀` = min(the gates' `δ₀`, `1`, `exp(−8·10⁶/ν)`, `e^{−1}/C₁`) | `ν`, `C₁`: after `ν`, as TARGET's `C₁ ≪ δ^{−1}` (L688) |
| `C₂` = wkeTaylor's `C₂`; `L₀` = max(the gates' `L₀`, `2`, `assemblySizeThreshold P₀ (B+1) Cmom`) | everything before `L` (`B` comes from `φ` and `Λ₀`, which depends on `D`) |

- `P₀` carries the placeholder `L = 1`, and `assemblySizeThreshold` does not read `L`: the proof's `change` from `P₀`
  to `P` checks by definitional unfolding.
- The kernel enforces this order anyway. The table is for the record.

**Aligning the gates.**
- `gates_common_prefix` takes `C₁` and `C₂` from wkeTaylor.
- `layergardenBody_update_aux` and `fixedpointBody_update_aux` prove that the layergarden and fixedpoint bodies do not
  change when `C₁, C₂` change: they read `N`, `R`, `θ`, `Λ` and `inputsF`, none of which uses `C₁, C₂`.
- So there is no shared-constants hypothesis.

## 4. The base case (`ansatz_zero`)

**TARGET.**
- Prop `propansatz` (L689–L707) does not fix `F₀`. Its item (1) asks only for `P(F_p) ≥ 1 − e^{−N_p}`, the symmetry
  and the nesting.
- The proof (L708) says "`F₀` the trivial true event".

**The frozen statement.** `AnsatzAt` at `p = 0` asks for:
- `Fev 0` measurable and symmetric, with `μ(Fev 0) ≥ 1 − e^{−N₀}`;
- classed solutions on `Fev 0`, measurability and integrability;
- clauses (2), (3), (4) with expectations over `Fev 0`.

Clause (2') and the nesting are vacuous at 0.

**INDUCT's choice.**
- `Fev 0 = initialRapidEvent`, the event that the initial coefficients decay rapidly.
- It is measurable and symmetric.
- `μ.real (Fev 0) = 1` (`measure_initialRapidEvent`) and `μ.restrict (Fev 0) = μ` (`restrict_initialRapidEvent`).
- So every level-0 expectation and cumulant is the full Gaussian one, as with TARGET's `F₀ = Ω`. The reading differs
  from L708 by a null set.

**Why the reading is needed.** The class condition is pointwise. For an arbitrary version of the Gaussian data,
outcomes whose data do not decay have no classed solution, so `Fev 0 = Ω` is not available. The reasoning is correct.

**This is a proof-level reading of L708 inside the frozen statement.** It changes no statement.

**I-1 (record).** The author's approval of this reading is recorded only in INDUCT's `WORKLOG.md` ("User explicitly
approved, twice"). It is not in `docs/DECISIONS.md` or `docs/FINDINGS.md`. Add a findings-ledger entry (a proof-level
deviation at L708, by a null set) so that it reaches `ERRATA-AND-DEVIATIONS.md`.

## 5. Other observations

**I-2 (doc).** `HANDOFF.md`, `PropansatzAssembly.lean` and `GateTypes.lean` say "snapshot 5". The result is verified
against snapshot 7 (§2). Relabel at the port.

**The S-norm guard.** The handoff mentions "the S-norm guard `Λ₁ = 0 ∨ ContDiff ℝ Λ₁ F`" in its local System copy.
It is snapshot 7's own frozen `SNorm` text (`WaveB1-System.lean` L350), not a local change.

**The port.**
- The integration port must import `Frozen.Defs`, never the anchors.
- INDUCT's local CANON, SYS and Duhamel copies are proof infrastructure, outside the statement closure. At the port,
  re-point them at the landed or sealing modules, such as `Foundations/Canon` from `w/freeze-b1`'s
  `canonicalCharacterization` seal, and diff them then.
