# Seal plans for the frozen `wkelwp` and `main` (Task 7)

Author: `wt-orch` (Opus). Date: 2026-11-03.

**Tree.** `w/orch` at the merge of main `f2c8bb6`. That includes the landed `Foundations/Probability/**`,
`NLS/{AkFlow, Backward}`, and every module named below.

**Wave B inputs.** The drafts in `/home/scott/wt-scratch/waveb-snap-2/` (Task 6b snapshot; not frozen).

**Lean checks for this plan.** All run with `lake env lean`, one process at a time, `nice -n 5`; the needed modules
were compiled with `-o`.

| Untracked scratch file | Purpose | sha256 |
|---|---|---|
| `scratch/Provider-Wkelwp-draft.lean` | the provider assembly for `wkelwp` | `45e62890…c1a556` |
| `scratch/WaveB-nlsAkBridge-D0.lean` | a probe for §B.5 | `2c4dc3af…27d7e7` |

## Part A — `wkelwp` (Frozen/Theorems/Wkelwp.lean, D6)

### A.1 Pieces

The frozen statement, for `d ≥ 3` and `φin : 𝓢(Mom d, ℝ)`, is `∃ τmax : ℝ≥0∞` with four conjuncts:

| # | Conjunct |
|---|---|
| C0 | `0 < τmax` |
| C1 | `∀ τ★ > 0, (ofReal τ★ < τmax ↔ ∃ φ, IsWKESolution φin τ★ φ)` |
| C2 | Uniqueness on `Icc 0 τ★` |
| C3 | Blow-up: `τmax < ⊤ → ∀ s > d/2 − 1, ∀ M, ∃ τ₀ ≥ 0, ofReal τ₀ < τmax ∧ ∀ τ★ > τ₀, ofReal τ★ < τmax → ∀ φ, IsWKESolution φin τ★ φ → M < weightedL2Norm s (φ τ★)` |

### A.2 Discharge table

| Piece | Landed result (module) | Exact match? | Status |
|---|---|---|---|
| witness | `WKE.tauMax φin := ⨆_{τ>0, ∃φ IsWKESolution φin τ φ} ofReal τ` (WKE/Lifespan) | — | landed |
| C0 | `WKE.tauMax_pos (hd : 2 ≤ d) φin` (WKE/Existence) | yes (d ≥ 2 ⊇ d ≥ 3) | landed |
| C1 | `WKE.lt_tauMax_iff (hd : 2 ≤ d) φin (hτ : 0 < τ★)` (WKE/Existence) | yes: same `ENNReal.ofReal τ★ < τmax ↔ ∃ φ : ℝ → 𝓢(Mom d, ℝ), IsWKESolution φin τ★ φ` | landed |
| C2 | `WKE.isWKESolution_unique (hd : 2 ≤ d) hφ hψ : ∀ τ ∈ Icc 0 T, φ τ = ψ τ` (WKE/Uniqueness) | yes | landed |
| C0–C2 together | `WKE.wkelwp_conj12` | verbatim the frozen C0–C2 (Infra-review-2) | landed |
| **C3** | none | — | **open: packet WKE-L2S**. Its HANDOFF claims no milestone. My GIT20-general-d audit lists the remaining mathematics: Theorem 7 plus the three supporting lemmas. |

**F44.** No `ContDiff` occurs anywhere in this chain. The frozen `IsWKESolution` uses `ContinuousOn` into `𝓢`.

**No junk.** `weightedL2Norm` is a Bochner integral; on Schwartz `φ τ★` the integrand is integrable, so C3 is not
junk-vacuous.

### A.3 Provider assembly (draft)

`scratch/Provider-Wkelwp-draft.lean` elaborates. Every declaration in it uses only `[propext, Classical.choice,
Quot.sound]`; it has no `sorry`, no axiom, and no added hypothesis on the provider. It contains:

1. **`WkelwpBody d φin`** — the frozen body copied verbatim. **`wkelwp_type_eq`** checks by `rfl` that
   ```lean
   (type_of% @WaveTurbulence.wkelwp) =
     ∀ (d : ℕ) (_ : 3 ≤ d) (φin : 𝓢(Mom d, ℝ)), WkelwpBody d φin
   ```
   This is a type-level check that does not depend on the frozen proof's `sorry`.
2. **Gap marker `WkelwpBlowupGap d φin : Prop`** — exactly C3 with `τmax := WKE.tauMax φin`. It is a definition
   that states what is missing. It is not assumed anywhere.
3. **`wkelwp_of_gap (d) (hd : 3 ≤ d) (φin) (h : WkelwpBlowupGap d φin) : WkelwpBody d φin`** — the assembly from
   `tauMax`, `tauMax_pos`, `lt_tauMax_iff` and `isWKESolution_unique`. These close C0–C2; only the gap is left.
4. **`wkelwpBody_iff_gap (d) (hd : 2 ≤ d) (φin) : WkelwpBody d φin ↔ WkelwpBlowupGap d φin`** — exactness.
   - C1 forces any witness to equal `tauMax φin`. The helper `eq_of_forall_ofReal_lt_iff` shows that two positive
     extended reals with the same real lower sets coincide.
   - So the frozen anchor needs **exactly** the blow-up criterion at `tauMax`: nothing weaker suffices, and nothing
     stronger is required.

**What WKE-L2S must land** (any name, in the frozen carriers):

```lean
theorem WKE.wkelwp_blowup (d : ℕ) (hd : 3 ≤ d) (φin : 𝓢(Mom d, ℝ)) :
    WKE.tauMax φin < ⊤ → ∀ s : ℝ, (d : ℝ) / 2 - 1 < s → ∀ M : ℝ,
      ∃ τ₀ : ℝ, 0 ≤ τ₀ ∧ ENNReal.ofReal τ₀ < WKE.tauMax φin ∧
        ∀ τstar > τ₀, ENNReal.ofReal τstar < WKE.tauMax φin → ∀ φ : ℝ → 𝓢(Mom d, ℝ),
          IsWKESolution φin τstar φ → M < weightedL2Norm s (φ τstar)
```

**Proof route** (GIT20-general-d audit):
1. Suppose a Z_s bound held on [0, τ_max).
2. Theorem 7 gives a uniform Z_s local existence time.
3. The three supporting lemmas lift that to Schwartz solutions: weights and the Leibniz rule for Z_{s,m};
   `IsWKESolution` ⟺ the mild formulation via the landed L^∞ bound; and 𝒮 = ⋂ Z_{s,m}.
4. Gluing (`isWKESolution_glue`) and `lt_tauMax_iff` then contradict maximality.

**Seal steps once it lands.**
1. Move the draft into `Provider/Wkelwp.lean` as
   `theorem Provider.wkelwp (d) (hd) (φin) := wkelwp_of_gap d hd φin (WKE.wkelwp_blowup d hd φin)`.
   Add imports `Foundations.WKE.Existence` and the blow-up module; the Foundations import graph has no `Provider` or
   `Theorems` node, so there is no cycle.
2. Drop the scratch-only import of `Frozen.Theorems.Wkelwp`, and keep `wkelwp_type_eq` in a test file.
3. Replace the anchor's `by sorry` with `Provider.wkelwp d hd φin`.
4. `#print axioms WaveTurbulence.wkelwp` must give the standard three axioms.
5. Run the ABI/manifest check.

## Part B — `main` (Frozen/Theorems/Main.lean, D6)

### B.1 Pieces

The frozen statement, for `d ≥ 3` and `γ ∈ (0,1)`:

`∃ θ > 0, ∀ φin ≥ 0 Schwartz, ∀ τ★ > 0, ∀ φ (IsWKESolution φin τ★ φ), ∃ L₀, ∀ L ≥ L₀, ∀ α T` with
`α = L^{−γ}` and `T = τ★·T_kin(α)`, for all probability data (Ω, P, g) that are measurable, independent, of law
`stdComplexGaussian`. It splits as follows, with F := `solvableEvent L α T φin g`:

| Piece | Content |
|---|---|
| M1 | `MeasurableSet F` |
| M2 | `1 − exp(−(log L)^{40d}) ≤ P.real F` |
| M3 | `∀ U` (selection: smooth solutions on F) `∀ t ∈ [0,T], ∀ n`: `|∫ 1_F ‖û_{Uω}(t,n)‖² dP − φ(t/T_kin, n/L)| ≤ L^{−θ}` |
| M4 | The selection device (any U as in M3) |
| M5 | The constant hierarchy: θ before the data, L₀ after them |

### B.2 How the pieces compose

1. **Choose the parameters.** Fix d, γ. B1.1 `propansatz` lives under `WTPrefix`.
   - Take η := η₀(d, γ) and **θ := η₀²⁰**.
   - Given (φin, τ★, φ): take C₁, ν := ν₀, and δ₀.
   - Choose `D := ⌈τ★/δ₀⌉ ≥ 1` and `δ := τ★/D ≤ δ₀`.
   - Take C₂ and L₀^Π. Then set **L₀ := max(L₀^Π, L₁)**, with L₁ from G10 below.
2. **Match the hypotheses.** Main's three hypotheses on g are literally `IsGaussianData P g` (snapshot-2 Statements).
   So `propansatz` yields a, F_p, R, E, Ẽ with `AnsatzAt p` for every p ≤ 𝔇.
3. **The solvable event.** Let G := {ω : initialCoeff is rapidly decaying}; P(G) = 1. Then
   F_𝔇 ∩ G ⊆ F by the backward reduction. M2 follows from AnsatzAt(𝔇)(1) and N_𝔇 ≥ (log L)^{40d}.
4. **The expectation estimate.** Write t′ := t/(δT_kin) ∈ [0,𝔇], and p := max(1, ⌈t′⌉) ≤ 𝔇, so t′ ∈ [p−1, p].
   - On F_𝔇 ∩ G, uniqueness gives ‖û_{Uω}(t,n)‖ = ‖a ω t′ n‖.
   - AnsatzAt(p)(2′) gives |∫_{F_p} ‖a t′ n‖² − φ(δt′, n/L)| ≤ 2L^{−θ_p}, and δt′ = t/T_kin.
   - The differences between F, F_𝔇 and F_p have probability ≤ e^{−N_𝔇}. On them both ‖û‖² and ‖a‖² are bounded by
     the mass Σ φin(m/L)|g_m|², which costs ≤ 2√2·e^{−N_𝔇/2}·Σ_m φin(m/L).
   - The total is ≤ 2L^{−θ_p} + C_φ L^d e^{−(log L)^{40d}/2} ≤ L^{−θ}, since θ_p > θ.
   - **F_p ⊄ F in general**: F_p only gives solvability on [0, p]. So the comparison must go through F_𝔇, which is
     contained in F_p (nesting).

### B.3 Discharge table

| Piece | Landed results (exact names, modules) | Wave B statement consumed (snap-2) | Missing glue |
|---|---|---|---|
| M5 (constants) | — | `propansatz` under `WTPrefix` (Core): the binder order d, γ → η₀ → data → C₁ → ν₀ → δ₀ → (δ, D) → C₂ → L₀ fits main's `∃θ` before the data and `∃L₀` after them | **G10**: parameter arithmetic (δ, D; N_𝔇 ≥ (log L)^{40d}; absorption) |
| hypotheses | `HasLaw` (Mathlib) from `Measurable` + `map` | `IsGaussianData` (Statements) = main's three hypotheses, literally | **G5**: `HasLaw (g n) stdComplexGaussian P` from main's hypotheses (one line) |
| M4 (selection) | `NLS.eq_of_mem_solvableEvent` (NLS/Energy): any two selections agree on `Icc 0 T`. `IsSmoothNLSSolution.eq_of_eq` (NLS/Energy). | — | none |
| M1 (measurability) | `NLS.solvableEvent_eq_preimage` (`rfl`), `smoothDataSet` (NLS/Symmetry) | **`nlsAkBridge` (4)**, first part, with `c := initialCoeff L φin g` (measurable) | **G1**, **G2**: Borel measurability of `smoothDataSet` (Infra-review-2 S5) and of the observable (route below). **Not landed**; this is the main analytic glue for M1/M3. |
| M2 (probability) | `NLS.IsAkSolution.isSmoothNLSSolution` (NLS/Backward; needs 0 < δ, **0 < 𝔇**, `IsRapidDecay c`), `Probability.ae_initialCoeff_isRapidDecay` (Probability/RandomRapidDecay; needs `HasLaw`) | `propansatz` → `AnsatzAt 𝔇` (1): `1 − e^{−N_𝔇} ≤ μ.real (Fev 𝔇)`, and the classed solution on Fev 𝔇 | **G4**: event inclusion. **G10a**: N_𝔇 ≥ (log L)^{40d} for L ≥ L₁(d). |
| M3 (estimate) | `IsSmoothNLSSolution.isAkSolution` (NLS/UniformDecay: forward reduction, with `hT : T = δ * kineticTime (L^(−γ)) * 𝔇`, which is main's T by `ring`); `NLS.IsAkSolution.eq_of_eq` (AkUnique); `NLS.norm_reducedCoeff` (Reduction); `IsSmoothNLSSolution.norm_torusFourierCoeff_sq_le` (Energy: ‖û(t,n)‖² ≤ Σ‖c_m‖²); `NLS.IsAkSolution.tsum_normSq_eq` (AkMass); `Probability.integral_norm_sq_restrict_le` (GaussianEvents: ∫_A ‖g‖² ≤ √2·√P(A)); `Probability.norm_setIntegral_le_sqrt_measure_mul` | `propansatz` → `AnsatzAt p` (1) (nesting, measurability, the classed solution) and **(2′)**, the time-parameter item F7/F27; `nlsAkBridge` (1), (3), (4) | **G2**: measurability of the integrand (otherwise the Bochner integral is junk 0). **G6**: the mass event bound. **G7**: Σ_m φin(m/L) ≤ C_φ L^d. **G8**: a-mass on F_p. **G9**: the identification ‖û‖ = ‖a‖ on F_𝔇 ∩ G. **G11**: nesting F_𝔇 ⊆ F_p. |

**F44 check for this chain.**
- Frozen `IsSmoothNLSSolution`: `ContDiffOn ℝ (⊤ : ℕ∞)` (= ∞).
- `IsSmoothNLSSolution.contDiff`: `ContDiff ℝ ∞`.
- `Probability.ae_contDiff_initial_torusSeries`: `∞`.
- Snapshot 2: no `ContDiff ℝ ⊤` remains (Task 6b).

**Binders and carriers.**
- Every landed NLS lemma uses the frozen `IsSmoothNLSSolution L α T c u` with `α = L ^ (-γ)` (`rpow`); main writes
  `α = L ^ (-γ)` too.
- `kineticTime` is the frozen one.
- `solvableEvent` and `initialCoeff` are frozen and coincide literally with the forms in Symmetry and Energy.

### B.4 Missing glue lemmas (proposed statements; none of them is a Wave B anchor)

Names are suggestions. ∀-binders follow the frozen carriers.

- **G1 (`measurableSet_smoothDataSet`).**
  ```lean
  0 < L → 0 < T → α = L^(-γ) → MeasurableSet (NLS.smoothDataSet (d := d) L α T)
  ```
  (product σ-algebra on `(Fin d → ℤ) → ℂ`).

  **Route:**
  1. With T = δT_kin𝔇, combine the forward (`isAkSolution`, `exists_uniform_decay`) and backward
     (`IsAkSolution.isSmoothNLSSolution`) reductions:
     `smoothDataSet = {c | IsRapidDecay c ∧ ∃ a, NLS.IsAkSolution L γ δ 𝔇 c a}`.
  2. `IsRapidDecay` is Borel: write it with rational constants, as countable unions and intersections of
     coordinatewise closed conditions.
  3. The existence set is Borel by the ℓ¹ flow (`NLS/AkFlow`: Lipschitz on bounded sets, so it has a continuous
     local flow and a lower-semicontinuous existence time).
  4. The map c ↦ y = (1+‖n‖)^{d+1}c into `L1 d` is measurable on {Σ(1+‖n‖)^{d+1}|c_n| < ∞}.
- **G2 (observable).**
  ```lean
  ∀ t ∈ Icc 0 T, ∀ n, ∃ Φ : ((Fin d → ℤ) → ℂ) → ℝ, Measurable Φ ∧
    ∀ c ∈ smoothDataSet L α T, ∀ u, IsSmoothNLSSolution L α T c u →
      ‖torusFourierCoeff L (u t) n‖ ^ 2 = Φ c
  ```
  Φ is the flow evaluated at time t/(δT_kin), squared; it is continuous on the existence set. Together, G1 and G2
  give `nlsAkBridge` (4) and main's M1.
- **G4 (event inclusion).**
  ```lean
  Fev 𝔇 ∩ {ω | IsRapidDecay (initialCoeff L φin g ω)} ⊆ solvableEvent L α T φin g
  ```
  This follows from `AnsatzAt 𝔇` (1) and `NLS.IsAkSolution.isSmoothNLSSolution`.
- **G5.**
  ```lean
  Measurable (g n) → P.map (g n) = stdComplexGaussian → HasLaw (g n) stdComplexGaussian P
  ```
- **G6 (mass event bound).**
  ```lean
  ∀ A, (∫ ω in A, ∑' m, φin (latticePoint L m) * ‖g m ω‖ ^ 2 ∂P) ≤
    Real.sqrt 2 * Real.sqrt (P.real A) * ∑' m, φin (latticePoint L m)
  ```
  This is `integral_norm_sq_restrict_le` termwise plus monotone convergence. The right side is finite by G7.
- **G7.**
  ```lean
  ∃ C, ∀ L ≥ 1, ∑' m, φin (latticePoint L m) ≤ C * L ^ d
  ```
  This is a lattice Riemann sum of a Schwartz function; `Probability/SchwartzLattice` has the decay input.
- **G8.** On Fev p, ‖a ω t n‖² ≤ Σ_m φin(m/L)|g_m ω|² for t ∈ [0,p]. This is `NLS.IsAkSolution.tsum_normSq_eq`
  plus `le_tsum`, with ‖c_m‖² = φin(m/L)‖g_m‖².
- **G9 (identification).**
  ```lean
  ω ∈ Fev 𝔇 ∩ G → (∀ ω ∈ F, IsSmoothNLSSolution … (U ω)) → ∀ t ∈ Icc 0 T, ∀ n,
    ‖torusFourierCoeff L (U ω t) n‖ = ‖a ω (t / (δ * kineticTime α)) n‖
  ```
  This uses `isAkSolution` (forward), `NLS.IsAkSolution.eq_of_eq` against AnsatzAt(𝔇)(1)'s `a ω`, and
  `norm_reducedCoeff`.
- **G10 (parameters).**
  - (a) N_𝔇 ≥ (log L)^{40d} once (log L)^{40d} ≥ 4. Here R_𝔇 = ⌊x⌋ ≥ x/2 and (x/2)^{40d} ≥ x.
  - (b) D := ⌈τ★/δ₀⌉, δ := τ★/D satisfy δ ∈ (0, δ₀], 1 ≤ D, τ★ = Dδ.
  - (c) Absorption: 2L^{−θ_p} + 2√2·C_φ·L^d·e^{−N_𝔇/2} ≤ L^{−θ} for L ≥ L₁(d, η, φin). This uses θ_p ≥ η²⁰(1 + 2^{−𝔇}) > θ.
- **G11 (nesting).** `∀ p ≤ 𝔇, Fev 𝔇 ⊆ Fev p`, from AnsatzAt's `Fev p ⊆ Fev (p−1)` by downward induction.

### B.5 Findings while planning (for the drafter, with D1 and S1–S8)

**T7-1 (REQUIRED for `nlsAkBridge`): item (2) is false at D = 0.**
- **The mechanism.** At T = 0 the frozen `IsSmoothNLSSolution` sees `derivWithin` on the singleton {0}, which is 0.
  So it forces −Δu(0) + α|u(0)|²u(0) = 0. Meanwhile `IsAkSolution … 0 c (fun _ => c)` holds for any data, because a
  derivative within a singleton is arbitrary.
- **The probe.** `scratch/WaveB-nlsAkBridge-D0.lean`, standard axioms:
  - `nlsAkBridge_item2_false_at_zero` refutes item (2) for d = 1, L = 1, δ = 1, the one-mode data of the constant 1,
    and α = 1;
  - `nlsAkBridge_draft_inconsistent : False` instantiates the draft anchor; its only `sorry` is the anchor's own.
- **Fix.** Add `(hD : 1 ≤ D)` to `nlsAkBridge`, or at least to item (2). The landed backward lemma already requires
  `0 < 𝔇`.
- **Impact on main.** None: main has τ★ > 0, so D ≥ 1 and T > 0.

**T7-2 (note): main consumes AnsatzAt (2′).**
- Main consumes `AnsatzAt` (2′), the F7/F27 time-parameter item that is **not** in TARGET's `propansatz`, together
  with the event comparison of B.2(4).
- (2′) is stated on Fev p with the constant 2. That is enough for main through G6–G11, so no change is needed. The
  `propansatz` prover must actually establish (2′).

**T7-3 (note): main's indirect dependency on B1.12.**
- Main depends on B1.12 indirectly: `propansatz` ⇐ `fixedpoint` ⇐ the parametrix ⇐ `layergardenFlower` (G-1).
- B1.12 is deferred (stage-3 R8), and its 𝒴/𝒲 sums are currently empty (delta-1 D1). Both must be resolved before
  the propansatz chain can be sealed. Main's own glue G1–G11 is independent of this.

### B.6 Sealing order for `main`

1. **Unfrozen glue, startable now (parallel):** G5, G6, G7, G8, G10, G11. They are elementary, and the landed
   NLS and Probability modules suffice.
2. **G1 and G2** (measurability; route via `NLS/AkFlow`) ⇒ `nlsAkBridge` (4). Items (1) and (3) are already
   landed results up to repackaging. Item (2) needs T7-1, then `NLS.IsAkSolution.isSmoothNLSSolution` plus
   `IsRapidDecay` ⟺ the draft's `jbr`-form hypothesis.
3. **G4, G9** once `propansatz`'s statement is frozen. They use only its `AnsatzAt` items (1) and (2′).
4. **`propansatz`**: the long pole. It needs B1.2, B1.3, B1.5, the unfrozen cumulant expansion T.cmattr, B1.12/X1 and
   the B2 graph.
5. **`Provider.main`** := assemble B.2 from `propansatz` + `nlsAkBridge` + G1–G11. Then replace the anchor's
   `by sorry`, check axioms, and run the ABI check.

A `Provider.main` skeleton with `propansatz`/`nlsAkBridge` as named gap Props, in the style of A.3, is possible once
the Wave B statements are frozen. Before that, its types would track drafts that are still moving.
