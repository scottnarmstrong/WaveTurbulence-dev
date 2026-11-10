# VINEEST-S3 (V5 part 1, TARGET vineest Step 3, no twist) — HANDOFF (CHECKPOINT state)

Scratch <scratch>/vineest-s3, namespace `WaveTurbulence.VineEstS3` (+ `.FS`, `.Eng`, `.Mink`).
Build: `./build.sh VineEstS3.<Mod>` (LEAN_PATH = ./build + vineest-s2/snap9 + b21-snap9/build + universe/build +
sumint-signed-fresh + WaveTurbulence-dev lake env (read-only, Foundations modules that do not import frozen B1)).
Foundations modules that import the frozen B1 (e.g. Foundations.Sumint.*) clash with the WaveBDraft draft namespace;
use the flat scratch copies instead (`MultiIndices`, `TimeBridge`, `SpatialBridge`, `SumintSigned.*`).
Order of modules: validation/order.txt. Fresh rebuild log: validation/fresh-rebuild.txt. Axioms: validation/AxEngine.lean
output (propext, Classical.choice, Quot.sound only). No sorry/axiom/opaque/unsafe/maxHeartbeats in VineEstS3/*.lean.

## What is proved (all compiled, default budgets, standard axioms)

### Items 1-2 (earlier sessions)
`Gate30d.CoherentApproximationGate30d` (0814 pin on snapshot 9, rfl-equal), `Pointwise`, `Continuity`
(`enorm_KQstar_le`, `enorm_KTstar_le`), `SumintFinal.sumintSignedDoubled` (unconditional).

### Item 3: Fourier-series route, now COMPLETE
* `FSKernel`..`FSDeriv` (earlier): period-2 Poisson identity, Peetre lattice sums, `hasSum_coeff`, `mixture_bound`.
* `FSFamily.exists_good_family`, `FSNorm.sum_SNorm_coeff_le`: for `Λ₁ ≠ 0`, `θ ≥ 0`,
  `∑'_m maxBracketPow θ (half m) * SNorm Λ₁ Λ₂ (coeff q G m) ≤ C * XNorm θ Λ₁ Λ₂ G`, C independent of `q`
  (`norm_kern_translate`, `sum_kern_weight_le_uniform`).
* `FSMain.fs_expansion`: if `f(t,k)` is continuous in `t` for `k ∈ K`, `B ⊆ cell q`, `B ⊆ closure (interior B)` and
  `XNormRestr θ Λ₁ Λ₂ B K f < b`, there are `c m : Mom d → ℂ` with `f t k = ∑_m c m k e^{πi m·t}` on `B × K`
  (`HasSum`, `fsPhase`) and `∑' maxBracketPow θ (half m) * SNorm Λ₁ Λ₂ (c m) ≤ C * b` (C uniform in q, f, b).
* `Mink.XNorm00Restr_tsum_le`: countable Minkowski for order-zero restriction norms
  (`≤ (cutoffMultiplierConstant θ (cutQ q) + 1) * ∑'`), via continuous representatives (`Regref.rep`), cutoff,
  `SumintSigned.XNorm00_count_integral_le`, repair of the null set by redefinition on `B × K`.

### THE ENGINE (new): `sumint` for clock-dependent weights  (item 4, analytic half)
`ClockedBound.clockedBound` / `ClockedBoundRestr.clockedBound_of_restr` (pointwise At-form, statement below).
Pipeline (all modules above `ClockedBoundRestr` in validation/order.txt):
1. `ClockedExpr`: `Row D = VIdx ⊕ VIdx`, `Slot D = TVar ⊕ Fin 3`, `ClockedRows` (weights `W ρ : (Fin 2 → ℝ) → Mom → ℂ` +
   `slot ρ : Fin 2 → Slot`), `clockedExpr`, `modeDatum`, `signedExpr_modeDatum`.
2. `ClockPhase` (`prod_fsPhase_clock`: ∏ρ e^{πi m_ρ·clock_ρ} = `paramFactor` · `outFactor`), `SignedParam`
   (`signedPhase_param`), `SignedBound` (continuity, |signedPhase| ≤ 1 when badKind ≠ 2), `PiProd`
   (products of series/ENNReal tsums), `DecaySum`/`DecayX` (`summable_decayWt`: ∑_x ∏ ⟨k_v(x)⟩^{-N} < ∞ via the integer
   bijection x ↦ T₁x and `NTSP.summable_lattice`), `TimeDomMeas`.
3. `ClockedExpand(2)`: `clockedExpr_hasSum` (interchange ∑_x ∫_τ ∑_m, summable majorant `S ρ m · Dec ρ k`).
4. `ScaledSumint`: `SumintDoubledAt`, `ScaledSumintAt`, `scaledSumintAt_of` (`sumint` for weights with `SNorm ≤ s_ρ`:
   factor `∏ s_ρ L^{(γ₁-√η) g_ρ}`), `OutMod` (output modulation cost), `RestrScalar`, `SNormAux`.
5. `ModeBounds(2)`: `mode_real_bound` (per-mode weight ≤ `engineConst η |Row| · maxPar D^{η⁶} · ∏ρ ⟨m_ρ/2⟩^{6η⁶}`).
6. `ClockedBound.mode_bound`, `clockedBound`:
```
XNorm00Restr (2η⁸) (outBox D) (outSet D L γ η) (fun tt E => clockedExpr cr cfs cs hI L γ (2δ) η tt E)
  ≤ (ccη η + 1) * ofReal (engineConst η |Row| * maxPar D^{η⁶} * sumintRHS0 P D * ∏ρ L^{weightExp * g_ρ}) * ∏ρ M.b ρ
```
hyps: `SumintDoubledAt A P`, `0<L`, `0<η≤1`, `0≤C₁`, `0<δ`, `1≤d`, `0<I`, `badKind ∉ {1,2}`, param-generic
`hAdm`, `M ≤ N₁⁴`, `cr : ClockedRows D`, `M : ClockedModes D (6η⁶)` (mode coefficients with
`∑_m ⟨m/2⟩^{6η⁶} SNorm(30d, N_ρ)(c ρ m) ≤ b ρ < ⊤`), `hser` (series valid for τ ∈ timeDom, tt ∈ outBox).
`clockedBound_of_restr` replaces `M, hser` by: `Bx ρ ⊆ cell (qx ρ)`, `Bx ρ ⊆ closure (interior (Bx ρ))`, `W ρ` continuous
in the clock pair, `XNormRestr (6η⁶) (30d) N_ρ (Bx ρ) univ (W ρ) < β ρ`, and `clock ∈ Bx ρ` on the time domain; the
bound then carries `∏ρ (Cfs * β ρ)`.

## Design decisions that bind the continuation
* **At-form.** Statements are pointwise at `(A, P : WTParams)` (`SumintDoubledAt A P`, `ScaledSumintAt A P`); the prefix
  wrapper is a one-line `Iff.rfl` (`sumintSignedDoubled_iff`).  Combining several prefix statements (sumint, the 30d gate,
  B2.2) needs `LargeConstantMonotone` for each At-body (LG-SPINE `PrefixConjunction.prefix_and`); the engine is monotone in `C₁`
  (RHS only).  The gate bodies' monotonicity in (C₁, C₂) is NOT proved here (the hypothesis `InputRemainder P` involves C₁).
* **`Admissible` cannot be transported between datums that differ in `param`** (a `match` in clause (iii) blocks defeq in
  the module system).  Hence `hAdm` quantifies over `param`: `∀ p a b, WeightBounds D .. a b → ({D with param := p, wK := a,
  wL := b}).Admissible ..`.  V5-proper must prove exactly this for `sourceSumintDatum hM9 B hG W` (any W): the algebraic
  clauses are `sourceSumintDatum_algebraic_hypotheses` (all W); the rest is the `q ≤ 𝔇`, bad-case (a)/(d) clauses and the
  weight bounds (= `WeightBounds`, supplied by the engine's rescaling).
* Constants: `K₀ = engineConst η |Row|`, `ccη`, `Cfs` depend only on (η, |Row|); absorbing them into `C₁` is the
  consumer's (prefix-level) job: `(K₀C₁δ^{-1/2})^M ≥ K₀^M (C₁δ^{-1/2})^M`.

## What remains for READY vineest-s3 (exact next steps)
1. **B4 bridge, clocks** (V4 files: `CLStep2Time.slot_parent_clock`, `RegRedDraft/CLLocalTimes.clLocalClock`,
   `cl_realization_parent`): prove `∃ s : Slot, ∀ t τ, parentClock (t 0) (clLocalClock R t (assemblyClockEquiv τ)) x = slotVal τ t s`
   for pair leaves (`x ∈ clRealizationNodes`, `x ≠ a.toNode`: parent is `a` ↦ `inr 0`, else an interior branch ↦ `inl s` via
   `(assemblyClockAtomEquiv).symm`); same for the branch's own clock (`clLocalClock_slot`).  Then define
   `assemblyClocked : ClockedRows (sourceSumintDatum hM9 B hG W)` with `W (inl v) = KQstar .. (s 0) (s 1)`,
   `W (inr v) = KTstar ..` and prove `clockedIntegrand = ∏ (assemblyWK ... assemblyWL ...)` (rfl after the slot lemma).
2. **Gate matching** (B4 (i)-(iii)): for each row produce `XNormRestr (6η⁶) (30d) N_ρ (timeBox q q') univ (KQstar ..) < β ρ` from
   B2.2 `incoherentDecay` (g ≥ 1, `β = (C₁δ)^n L^{-(γ₁-√η) g}`) and `CoherentApproximationGate30d` + `SourceSeparated`
   (g = 0; `β = (C₁δ)^n · C`), using `XNormRestr` triangle (`restr_add_le`) and monotonicity in θ (6η⁶ ≤ η).  Needs the
   native couple `D.couple p` hypotheses: `Q.wf`, `Q.size = 2n`, `Decodes`, layers ≤ p, `n ≤ N_{p+1}⁴`, `IsCoherentCoupleAt`
   (needs the canonical layering, TARGET L951), and `hclock` (parent clocks lie in `timeBox q q'`: from the layering and
   `assemblyTimeDomain`; `q ≥ q'` by the conjugation symmetry (layerregest9)).
3. **B5**: define `n_(2) = n_(1) + n_(0)`, `n_(3) = M₀ + M₁`, `b = |Bad|` (L1846-1853) and identify `M₀` with the vine
   incoherency index; assemble the literal bound (vineest2) from `clockedBound_of_restr` (L^{M(d-γ)} cancels against
   `(δ/2L^{d-γ})^{n_(1)}`; `∏ β ρ` gives `(C₁√δ)^{n_(0)} L^{-(γ₁-√η)M₁}`).
4. **F21 / ε (GAP).** V4's endpoint keeps `ε(x)`; `clockedExpr` has none.  TARGET (L1844-1846) replaces ε by 1 "by trivial
   summation, gaining L^{-0.1γ₀}".  As far as I can see this is NOT valid for large M: trivially summing over the
   restricted subspace gives `L^{(M-1)d}` against the required `L^{M(d-γ)}`, i.e. a loss `L^{Mγ-d}` (the oscillatory gain
   `L^{-γ}` per variable is lost) — recorded as erratum candidate (DH23 §10.5 tameness is the likely real argument).  A statement-level decision is needed
   (state Step 3 for the ε ≡ 1 kernel, or supply the degenerate-vine bound separately).
5. **Leaf lower child (hb1/hb2)**: K̃ does not depend on t' when the lower child is a leaf; apply one extra order-0 trace
   (Layered/RestrictionCalculus `restr_const_le`) — not implemented (`outBox` has `max(t',t'') < t₀`; when `u21` is a leaf the
   `t'` clock does not occur in any weight and the constraint is a.e. vacuous).
6. Final checks: fresh rebuild, exact-type check of the Step 3 statement, HANDOFF with line numbers.

## Errata / deviations recorded
* TARGET (sumintI1)/(tildeK2) phases omit the factor 2 (ζΩ = 2⟨x,y⟩): handled by `sumintSignedDoubled` (phase at 2δ).
* F21/ε removal (above).
* DH23-style combination of prefixes needs C₁-monotonicity of the gate bodies (see Design decisions).
