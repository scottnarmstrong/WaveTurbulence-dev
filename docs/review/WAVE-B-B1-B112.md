# Wave B addendum: B1.12 `layergardenFlower` (add to the B1 freeze?)

Prepared 2026-11-04. This addendum goes with the B1 freeze candidate in [`WAVE-B-B1.md`](WAVE-B-B1.md) (snapshot 5).

In snapshot 5, B1.12 was a **deferred** draft and not in the freeze set. wt-gauss-hc (packet X1 FLOWER) has
redrafted it into the exact form that the proof of `fixedpoint` (TARGET L2306–L2338) consumes. wt-orch's audit
(`docs/campaign/orch/audits/FLOWER-redraft.md`) found it faithful to TARGET `flowerest1` (L2279–L2305) and sufficient
for every use in `fixedpoint`. The audit's two edits are applied:

- F1: the time range is `t < p+1`, TARGET's range;
- F2: the per-tree choices are disclosed in the docstring.

The draft compiles on snapshot 5, and its bridges and identities use only the standard axioms. Nothing else in
snapshot 5 changes. New text: `<scratch>/flower/Flower-Gate.lean` (sha256 `768d4953bf97…`).

## Decisions for the author (with recommendations)

1. **Add B1.12 to the B1 freeze**, as the 12th theorem anchor plus its 19 new definitions (exact text in §1.2 and
   §4 below)? *Recommended: yes.* It is exactly what `fixedpoint` consumes, and in its base cases it reduces to the
   kernels already in the freeze set (`kernelK`, `truncSumC`). Bridges for both are proved.
2. **Per-order δ exponents:** `δ^{2νN}` for flower gardens (TARGET L2305 as printed) and `δ^{νN}` for couples
   (clause (2)). *Recommended: yes.* `δ^{νN}` is all the consumer needs for couples. Asking `δ^{2νN}` there would
   force `ν < 1/4`, because the restricted `ℒ₀` class contains regular-couple pieces of size about `(C₁δ)^{N/2}`.
3. **Source readings.**
   - TARGET (operatorx) omits the exponent `ζ` on `b`, which DH23 L503 has. Without it the parametrix identities
     fail, because `ℒ₁` is only ℝ-linear. *Recommended: accept as an erratum.*
   - `𝒴` and `𝒲` carry a minus sign in front of their tree sums. DH23 absorbs this sign into its notation.
     *Recommended: accept as a precision, not an erratum.*

   Neither reading changes the B1.12 statement.

Approving B1 as in `WAVE-B-B1.md` together with decision 1 freezes 12 theorem anchors in place of 11.

---

# Snapshot 6 delta: B1.12 `layergardenFlower` (packet X1, final)

**Base:** snapshot 5 (`<scratch>/waveb-snap-5/`, CL-19).
**New text:** `<scratch>/flower/Flower-Gate.lean` (sha256 `768d4953bf975d3b770b84c9e9bb219511457e09617212b136a0fc9dd82092b9`), with probes in
`Flower-Gate-probes.lean` (sha256 `6c7e469b9e5222c1bb0d21f1c6518f80c883b300d77d569e6f0dc45ed66c4ee5`).
**Audit:** wt-orch `FLOWER-redraft.md` (be8484c) found the redraft faithful and sufficient. Its edits F1 and F2 are
applied (FLOWER-DESIGN.md changelog FL-2). Kept as instructed: `δ^{2νN}` for flowers (TARGET L2305, literal) and
`δ^{νN}` for couples.

## 0. Summary

| snapshot-5 file (sha256) | snapshot 6 | Lean declarations |
|---|---|---|
| `WaveB1-Deferred.lean` (`3bfcf873027c…`) | **replaced** by `Flower-Gate.lean` (§2–§4) | B1.12 restated; 3 removed, 2 kept, 19 new (plus a derived `DecidableEq`) |
| `WaveB1-Deferred-probes.lean` (`dc4c15fbb9fb…`) | **replaced** by `Flower-Gate-probes.lean` (§5) | `finite_truncSumHζ_support` removed; finite-support probes and bridges for the new sums |
| `WaveB1-Core`, `-System`, `-Statements`, `-Sumint`, `-Lemmas`, `-Bridges` and their probes | **unchanged** | none (§6) |

- **Imports.** `Flower-Gate.lean` imports only `WaveBDraft.Statements`, like `WaveB1-Deferred.lean` (closure policy).
  Its new definitions use only `WaveBDraft.Core`, `.System` and `.Statements` declarations (§4).
- **Module name.** The scratch module is `FlowerDraft.Gate`. In the snapshot it can keep the slot `WaveBDraft.Deferred`
  (file `WaveB1-Deferred.lean`) or be renamed (say `WaveB1-Flower.lean`). Only its probes import it, so the probes'
  `import FlowerDraft.Gate` follows the choice.
- **The freeze set.** If B1.12 joins it, add the module to `frozenMods` in `FreezeList.lean` and regenerate
  `FREEZE-LIST.md`. That adds the B1.12 rows and changes no snapshot-5 row (§6).

## 1. B1.12: exact old text vs exact new text

### 1.1 Snapshot 5 (`WaveB1-Deferred.lean` L85–L104)

```lean
/-- **B1.12 `layergardenFlower` (DEFERRED draft, not for freezing; stage-3 R8, delta-1 D1)** (T Prop `flowerest1`,
deterministic core of L2279–L2305; review G-1, WAVE-B v2 §4.15). Under `(Π_P)`, for `0 ≤ p < 𝔇`,
remainders as in B1.2, `p < s < t ≤ p+1`, `k, k' ∈ ℤ_L^d`, `ζ ∈ {±}`, `N ≤ N_{p+1}^4` and every
restriction kind: the flower-garden sum of width `2P` satisfies
`|∑| ≤ ⟨k - ζk'⟩^{-4Λ_{p+1}P} L^{(100d)³P} δ^{2νN}` (one kind-independent per-order bound; for the
`𝒴`/`𝒲` kinds the gain `e^{-100N_{p+1}}` of T L2305 comes from summing over `N`, since (Y)/(W) force
`N ≥ 2P(N_{p+1} + 1)`: stage-3 O1; the time range as in the source, stage-3 O7).
Deviations: (D1) the moment expansion `𝔼_p|𝒳|^{2P} = ∑ K̃ + errors` is left to T.flowerest1 (this is
its deterministic core); (D2) the cutoff refinements (`M₁`, `M₂`) and the derivative kernels are not
drafted (R8 above); (D3) the range `N ≤ N_{p+1}^4` (T L2290 reduces to it); (D4) the prefactor
`L^{d-γ}` (F25). Open (stage-2 A1): should kind `0` exclude trivial flower trees (F39)? -/
theorem layergardenFlower : WTPrefixP fun Pm P =>
    ∀ p : ℕ, p < P.D → ∀ R : ℕ → Mom P.d → ℝ, RemainderBound P R p →
    ∀ t ∈ Ioc (p : ℝ) (p + 1), ∀ s ∈ Ioo (p : ℝ) t, ∀ n n' : Fin P.d → ℤ, ∀ ζ : ℤˣ,
    ∀ N ≤ P.N (p + 1) ^ 4, ∀ kind : Fin 3,
      ‖truncSumHζ P (inputsF P R) p N (w := 2 * Pm) kind ζ t s n n'‖ ≤
        jbr (latticePoint P.L n - (ζ : ℤ) • latticePoint P.L n') ^
            (-(4 * P.Lambda (p + 1) * Pm : ℝ)) *
          P.L ^ ((100 * P.d : ℝ) ^ 3 * Pm) * P.δ ^ (2 * P.ν * N) := by
  sorry
```

### 1.2 New (`Flower-Gate.lean` L297–L358)

```lean
open Classical in
/-- **B1.12 `layergardenFlower`** (T Prop `flowerest1`, L2279–L2305, deterministic core; T L2306–L2338 for
its uses; review G-1, stage-3 R8, WAVE-B v2 §4.15).

Setting: `(Π_P)`, `0 ≤ p < 𝔇`, remainders as in B1.2, inputs `F_q = φ(δq) + R_q`.

**(1) Flower gardens of width `2P`.** For `p < s < t < p+1` (T's range for the flower kernels, L2263),
`n, n' ∈ ℤ^d`, `ζ`, `N ≤ N_{p+1}^4`, every kind (`𝒳`, `𝒴`, `𝒲`), every pattern vector, with or without `†`
and the cutoffs:

  `|flowerSum| ≤ ⟨k − ζk'⟩^{−4Λ_{p+1}P} L^{c(100d)³P} δ^{2νN} · M₁^{−80dP} · M₂^{−P/9}`

- `c = 1` if all patterns are plain, `c = 2` otherwise.
- The `M₁` factor is present iff the `M₁` cutoff is, also for derivative patterns.
- The `M₂` factor is present iff the `M₂` cutoff is and all patterns are plain. The `M₂` cutoff requires the
  `M₁` cutoff and `|k| ≥ M₁^{10}`.

**(2) Couples.** For `p < t < p+1`, `k ∈ ℝ^d`, `N ≤ N_{p+1}^4`, kind `ℒ₀`, or kind `a^tr` with `∂_t`:

  `|coupleSum| ≤ ⟨k⟩^{−4Λ_{p+1}} L^{100d} δ^{νN}`

**Uses.**
- The `𝒴`/`𝒲` gain `e^{−100N_{p+1}}` (T L2280) comes from summing over `N ≥ 2P(N_{p+1}+1)`, the kinds'
  lower bound.
- The bounds of (1) give T (flowerest2) with its cutoff variants, and T (newnormn) with the `∂_{t,s}` terms
  of (sobolev2), T L2331.
- Those of (2) give (trterm1) for `ℒ₀`, and for `∂_t a^tr`, `∂_t ℒ₀` with an extra `L^{100d}` (T L2312).

**Deviations** (FLOWER-DESIGN.md):
- (D1) The moment expansions `𝔼_p|𝒦|^{2P} = ∑ + errors` are left to T.flowerest1 and T.fp.part1. This gate
  is their deterministic core.
- (D2) Per-order bounds with `δ^{2νN}` (flowers) and `δ^{νN}` (couples).
- (D3) Range `N ≤ N_{p+1}^4` (T L2290).
- (D4) Prefactor `L^{d−γ}` (F25).
- (D5) Kind `𝒳` excludes the trivial flower tree (F39).
- (D6) `𝒴`/`𝒲` replace the top bound (F46).
- (D7) Explicit dyadic cutoffs.
- (D8) The derivative patterns and `†` as designated nodes, removed phases and weights (R8).
- (D9) `L^{2(100d)³P}` for derivative patterns.
- (D10) The couple clause covers `ℒ₀`, which B1.2 does not.
- (D11) Per-tree choices: the `†` labels `c j` and the patterns `pat j` may differ between the trees `j` of
  the garden. The consumer uses one uniform choice, so this is more general than `fixedpoint` needs (the
  proof is per tree). -/
theorem layergardenFlower : WTPrefixP fun Pm P =>
    ∀ p : ℕ, p < P.D → ∀ R : ℕ → Mom P.d → ℝ, RemainderBound P R p →
    (∀ t ∈ Ioo (p : ℝ) (p + 1), ∀ s ∈ Ioo (p : ℝ) t, ∀ n n' : Fin P.d → ℤ, ∀ ζ : ℤˣ,
      ∀ N ≤ P.N (p + 1) ^ 4, ∀ (kind : FlowerKind) (pat : Fin (2 * Pm) → FixPat)
        (dagger : Option (Fin (2 * Pm) → Fin 3 → Mom P.d)) (cut1 cut2 : Option ℕ),
        (∀ j₂ ∈ cut2, ∃ j₁ ∈ cut1, ((2 : ℝ) ^ j₁ * P.L) ^ 10 ≤ ‖latticePoint P.L n‖) →
        ‖flowerSum P (inputsF P R) p N kind pat dagger cut1 cut2 ζ t s n n'‖ ≤
          jbr (latticePoint P.L n - (ζ : ℤ) • latticePoint P.L n') ^
              (-(4 * P.Lambda (p + 1) * Pm : ℝ)) *
            P.L ^ ((if ∀ j, pat j = .plain then 1 else 2) * (100 * P.d : ℝ) ^ 3 * Pm) *
            P.δ ^ (2 * P.ν * N) *
            (cut1.elim 1 fun j₁ => ((2 : ℝ) ^ j₁ * P.L) ^ (-(80 * P.d * Pm : ℝ))) *
            (cut2.elim 1 fun j₂ =>
              if ∀ j, pat j = .plain then ((2 : ℝ) ^ j₂ * P.L) ^ (-(Pm / 9 : ℝ)) else 1)) ∧
    (∀ t ∈ Ioo (p : ℝ) (p + 1), ∀ k : Mom P.d, ∀ N ≤ P.N (p + 1) ^ 4, ∀ (kind : TreeKind)
        (dt : Bool), (kind = .tr → dt = true) →
        ‖coupleSum P (inputsF P R) p N kind dt t k‖ ≤
          jbr k ^ (-(4 * P.Lambda (p + 1) : ℝ)) * P.L ^ (100 * P.d : ℝ) * P.δ ^ (P.ν * N)) := by
  sorry
```

### 1.3 What changed

- **Sum.** `truncSumHζ … kind ζ t s n n'` becomes
  `flowerSum P (inputsF P R) p N kind pat dagger cut1 cut2 ζ t s n n'`. The new sum has corrected kinds (F39,
  F46/D1), derivative patterns, `†` and the `M₁`/`M₂` cutoffs (R8).
- **Bound of clause (1).** The `L` exponent is now `c·(100d)³P`, with `c = 2` for derivative patterns (D9). There
  are new factors `M₁^{−80dP}` (when `cut1` is set) and `M₂^{−P/9}` (when `cut2` is set and all patterns are
  plain). `⟨k−ζk'⟩^{−4Λ_{p+1}P}` and `δ^{2νN}` are unchanged.
- **Range of clause (1).** It is now `t ∈ Ioo p (p+1)`, TARGET L2263 (audit F1); it was `Ioc`. The `M₂` cutoff
  requires `M₁` and `|k| ≥ M₁^{10}`.
- **Clause (2), new (D10).** Couple sums for `ℒ₀`, `∂_t a^tr` and `∂_t ℒ₀`, with bound
  `⟨k⟩^{−4Λ_{p+1}} L^{100d} δ^{νN}`.
- **Docstring.** It lists D1–D11. D11 is audit F2: the `†` labels and the patterns are chosen per tree, which is more
  general than `fixedpoint` needs, and the `M₁` factor is kept for derivative patterns.

Unified diff of the two texts:

```diff
--- snapshot 5
+++ new
@@ -1,20 +1,62 @@
-/-- **B1.12 `layergardenFlower` (DEFERRED draft, not for freezing; stage-3 R8, delta-1 D1)** (T Prop `flowerest1`,
-deterministic core of L2279–L2305; review G-1, WAVE-B v2 §4.15). Under `(Π_P)`, for `0 ≤ p < 𝔇`,
-remainders as in B1.2, `p < s < t ≤ p+1`, `k, k' ∈ ℤ_L^d`, `ζ ∈ {±}`, `N ≤ N_{p+1}^4` and every
-restriction kind: the flower-garden sum of width `2P` satisfies
-`|∑| ≤ ⟨k - ζk'⟩^{-4Λ_{p+1}P} L^{(100d)³P} δ^{2νN}` (one kind-independent per-order bound; for the
-`𝒴`/`𝒲` kinds the gain `e^{-100N_{p+1}}` of T L2305 comes from summing over `N`, since (Y)/(W) force
-`N ≥ 2P(N_{p+1} + 1)`: stage-3 O1; the time range as in the source, stage-3 O7).
-Deviations: (D1) the moment expansion `𝔼_p|𝒳|^{2P} = ∑ K̃ + errors` is left to T.flowerest1 (this is
-its deterministic core); (D2) the cutoff refinements (`M₁`, `M₂`) and the derivative kernels are not
-drafted (R8 above); (D3) the range `N ≤ N_{p+1}^4` (T L2290 reduces to it); (D4) the prefactor
-`L^{d-γ}` (F25). Open (stage-2 A1): should kind `0` exclude trivial flower trees (F39)? -/
+open Classical in
+/-- **B1.12 `layergardenFlower`** (T Prop `flowerest1`, L2279–L2305, deterministic core; T L2306–L2338 for
+its uses; review G-1, stage-3 R8, WAVE-B v2 §4.15).
+
+Setting: `(Π_P)`, `0 ≤ p < 𝔇`, remainders as in B1.2, inputs `F_q = φ(δq) + R_q`.
+
+**(1) Flower gardens of width `2P`.** For `p < s < t < p+1` (T's range for the flower kernels, L2263),
+`n, n' ∈ ℤ^d`, `ζ`, `N ≤ N_{p+1}^4`, every kind (`𝒳`, `𝒴`, `𝒲`), every pattern vector, with or without `†`
+and the cutoffs:
+
+  `|flowerSum| ≤ ⟨k − ζk'⟩^{−4Λ_{p+1}P} L^{c(100d)³P} δ^{2νN} · M₁^{−80dP} · M₂^{−P/9}`
+
+- `c = 1` if all patterns are plain, `c = 2` otherwise.
+- The `M₁` factor is present iff the `M₁` cutoff is, also for derivative patterns.
+- The `M₂` factor is present iff the `M₂` cutoff is and all patterns are plain. The `M₂` cutoff requires the
+  `M₁` cutoff and `|k| ≥ M₁^{10}`.
+
+**(2) Couples.** For `p < t < p+1`, `k ∈ ℝ^d`, `N ≤ N_{p+1}^4`, kind `ℒ₀`, or kind `a^tr` with `∂_t`:
+
+  `|coupleSum| ≤ ⟨k⟩^{−4Λ_{p+1}} L^{100d} δ^{νN}`
+
+**Uses.**
+- The `𝒴`/`𝒲` gain `e^{−100N_{p+1}}` (T L2280) comes from summing over `N ≥ 2P(N_{p+1}+1)`, the kinds'
+  lower bound.
+- The bounds of (1) give T (flowerest2) with its cutoff variants, and T (newnormn) with the `∂_{t,s}` terms
+  of (sobolev2), T L2331.
+- Those of (2) give (trterm1) for `ℒ₀`, and for `∂_t a^tr`, `∂_t ℒ₀` with an extra `L^{100d}` (T L2312).
+
+**Deviations** (FLOWER-DESIGN.md):
+- (D1) The moment expansions `𝔼_p|𝒦|^{2P} = ∑ + errors` are left to T.flowerest1 and T.fp.part1. This gate
+  is their deterministic core.
+- (D2) Per-order bounds with `δ^{2νN}` (flowers) and `δ^{νN}` (couples).
+- (D3) Range `N ≤ N_{p+1}^4` (T L2290).
+- (D4) Prefactor `L^{d−γ}` (F25).
+- (D5) Kind `𝒳` excludes the trivial flower tree (F39).
+- (D6) `𝒴`/`𝒲` replace the top bound (F46).
+- (D7) Explicit dyadic cutoffs.
+- (D8) The derivative patterns and `†` as designated nodes, removed phases and weights (R8).
+- (D9) `L^{2(100d)³P}` for derivative patterns.
+- (D10) The couple clause covers `ℒ₀`, which B1.2 does not.
+- (D11) Per-tree choices: the `†` labels `c j` and the patterns `pat j` may differ between the trees `j` of
+  the garden. The consumer uses one uniform choice, so this is more general than `fixedpoint` needs (the
+  proof is per tree). -/
 theorem layergardenFlower : WTPrefixP fun Pm P =>
     ∀ p : ℕ, p < P.D → ∀ R : ℕ → Mom P.d → ℝ, RemainderBound P R p →
-    ∀ t ∈ Ioc (p : ℝ) (p + 1), ∀ s ∈ Ioo (p : ℝ) t, ∀ n n' : Fin P.d → ℤ, ∀ ζ : ℤˣ,
-    ∀ N ≤ P.N (p + 1) ^ 4, ∀ kind : Fin 3,
-      ‖truncSumHζ P (inputsF P R) p N (w := 2 * Pm) kind ζ t s n n'‖ ≤
-        jbr (latticePoint P.L n - (ζ : ℤ) • latticePoint P.L n') ^
-            (-(4 * P.Lambda (p + 1) * Pm : ℝ)) *
-          P.L ^ ((100 * P.d : ℝ) ^ 3 * Pm) * P.δ ^ (2 * P.ν * N) := by
+    (∀ t ∈ Ioo (p : ℝ) (p + 1), ∀ s ∈ Ioo (p : ℝ) t, ∀ n n' : Fin P.d → ℤ, ∀ ζ : ℤˣ,
+      ∀ N ≤ P.N (p + 1) ^ 4, ∀ (kind : FlowerKind) (pat : Fin (2 * Pm) → FixPat)
+        (dagger : Option (Fin (2 * Pm) → Fin 3 → Mom P.d)) (cut1 cut2 : Option ℕ),
+        (∀ j₂ ∈ cut2, ∃ j₁ ∈ cut1, ((2 : ℝ) ^ j₁ * P.L) ^ 10 ≤ ‖latticePoint P.L n‖) →
+        ‖flowerSum P (inputsF P R) p N kind pat dagger cut1 cut2 ζ t s n n'‖ ≤
+          jbr (latticePoint P.L n - (ζ : ℤ) • latticePoint P.L n') ^
+              (-(4 * P.Lambda (p + 1) * Pm : ℝ)) *
+            P.L ^ ((if ∀ j, pat j = .plain then 1 else 2) * (100 * P.d : ℝ) ^ 3 * Pm) *
+            P.δ ^ (2 * P.ν * N) *
+            (cut1.elim 1 fun j₁ => ((2 : ℝ) ^ j₁ * P.L) ^ (-(80 * P.d * Pm : ℝ))) *
+            (cut2.elim 1 fun j₂ =>
+              if ∀ j, pat j = .plain then ((2 : ℝ) ^ j₂ * P.L) ^ (-(Pm / 9 : ℝ)) else 1)) ∧
+    (∀ t ∈ Ioo (p : ℝ) (p + 1), ∀ k : Mom P.d, ∀ N ≤ P.N (p + 1) ^ 4, ∀ (kind : TreeKind)
+        (dt : Bool), (kind = .tr → dt = true) →
+        ‖coupleSum P (inputsF P R) p N kind dt t k‖ ≤
+          jbr k ^ (-(4 * P.Lambda (p + 1) : ℝ)) * P.L ^ (100 * P.d : ℝ) * P.δ ^ (P.ν * N)) := by
   sorry
```

## 2. Declarations removed from snapshot 5

None is used by any Lean declaration in snapshot 5 or in the campaign worktrees. Outside copies of snapshots and of
`WaveB1-Deferred(-probes).lean`, the scratch trees mention them only in copies of the frozen docstrings of §6.

- **`KGflower`.** Replaced by `kernelKgen`. For flower gardens with only the flower parents designated,
  `kernelKgen = kernelK` (bridge `kernelKgen_flowerParents`), and `KGflower` was `kernelK` with root times `t`.
- **`LayeredGarden.FlowerRestr`.** Replaced by `LayeredGarden.FlowerKindOK`: `X` excludes the trivial tree (F39);
  `Y` and `W` replace the top bound instead of adding to it (F46/D1, under which `truncSumHζ` was `0` for kinds 1
  and 2).
- **`truncSumHζ`.** Replaced by `flowerSum`.

```lean
/-- **(Deferred.) The flower kernel `K̃_𝒢(t, s, k, k')`** (T (kqflower), L2266–L2268; prefactor with `L^{d-γ}`
per F25): `(k, k')`-decorations (all roots `n`, all flowers `n'`), the flower parents' times fixed to
`s`, input product over unmarked `+` leaves. -/
noncomputable def KGflower {w d : ℕ} (L γ δ : ℝ) (F : ℕ → Mom d → ℝ) (LG : LayeredGarden w)
    (t s : ℝ) (n n' : Fin d → ℤ) : ℂ :=
  kernelK L γ δ F LG (fun _ => t) s 0 (fun _ => n) n'

/-- The restrictions `(Y-1)–(Y-2)` (`kind = 1`) and `(W-1)–(W-3)` (`kind = 2`) on each flower tree of
a flower garden (T L2271–L2272, with order = number of layer-`p` branching nodes, T L2290); `kind = 0`:
no restriction (`𝒳`). -/
def LayeredGarden.FlowerRestr {w : ℕ} (LG : LayeredGarden w) (p Ntr : ℕ) (kind : Fin 3) : Prop :=
  ∀ j : Fin w,
    (kind = 1 → Ntr < LG.topOrder p j ∧ ∀ b : GBranch LG.garden.tree, b.1 = (j, []) →
      ∀ i : Fin 3, LG.topCountBelow p (b.child i) ≤ Ntr) ∧
    (kind = 2 → Ntr < LG.topOrder p j ∧ ∀ ℓ : GLeaf LG.garden.tree, ℓ.1.1 = j →
      LG.garden.IsFlower ℓ → ∀ b : GBranch LG.garden.tree, b.IsParentOf ℓ →
        (∀ i : Fin 3, (b.child i) ≠ ℓ.toNode → LG.topCountBelow p (b.child i) ≤ Ntr) ∧
        LG.topOrder p j - LG.topCountBelow p b.toNode ≤ Ntr)

/-- **`truncSumHζ p N kind ζ t s n n'`**, the one shared flower sum (T (flowerexp2), L2283–L2288;
(operatorxker); stage-3 O4, stage-2 O3: it replaces the snapshot's `truncSumH`, which lacked the
flower sign and the `𝒴`/`𝒲` restrictions): `∑ K̃_𝒢(t,s,k,k')` over `𝒢 ∈ ℋ^tr_{p+1}` of width `w`
and order `N`, with flower signs `ζ · ζ_j` (`𝒳^ζ_{kk'}`) and restriction `kind` (`0`: none). -/
noncomputable def truncSumHζ (P : WTParams) (F : ℕ → Mom P.d → ℝ) (p N : ℕ) {w : ℕ}
    (kind : Fin 3) (ζ : ℤˣ) (t s : ℝ) (n n' : Fin P.d → ℤ) : ℂ :=
  ∑ᶠ (LG : LayeredGarden w) (_ : IsCanonH (p + 1) LG ∧
      LG.IsTrunc p (P.N (p + 1)) (P.N p) ∧ LG.garden.order = N ∧
      LG.FlowerRestr p (P.N (p + 1)) kind ∧
      ∀ ℓ : GLeaf LG.garden.tree, LG.garden.IsFlower ℓ →
        LG.garden.sign ℓ.toNode = ζ * LG.garden.sig ℓ.1.1),
    KGflower P.L P.γ P.δ F LG t s n n'
```

## 3. Declarations kept, with the same name and statement

**`LayeredGarden.topCountBelow`.** Same full name, binders and body. It moves into `namespace LayeredGarden`, drops
`noncomputable` (it is computable) and gets a shorter docstring:

```diff
--- snapshot 5 (WaveB1-Deferred.lean)
+++ new (Flower-Gate.lean, inside `namespace LayeredGarden`, `variable {w : ℕ} (LG : LayeredGarden w)`)
@@ -1,4 +1,3 @@
-/-- The number of layer-`p` branching nodes below a node (the "order" of T L2290). -/
-noncomputable def LayeredGarden.topCountBelow {w : ℕ} (LG : LayeredGarden w) (p : ℕ)
-    (a : GNode LG.garden.tree) : ℕ :=
+/-- The number of layer-`p` branching nodes below `a` (the "order" of T L2290). -/
+def topCountBelow (p : ℕ) (a : GNode LG.garden.tree) : ℕ :=
   (Finset.univ.filter fun b : GBranch LG.garden.tree =>
```

**`WTPrefixP`.** Same body. Only the docstring changes: the line reference, and the wording.

```diff
--- snapshot 5 (WaveB1-Deferred.lean)
+++ new (Flower-Gate.lean)
@@ -1,3 +1,3 @@
-/-- The prefix `(Π_P)` of `flowerest1` (T L2273–L2275): as `(Π)`, with the moment order `P` chosen
-after `ν` ("large depending on `C₁`") and before `δ` ("`δ` small depending on `P`"). -/
+/-- The prefix `(Π_P)` of `flowerest1` (T L2279–L2280). It is `(Π)` with the moment order `P` chosen after `ν`
+("large depending on `C₁`") and before `δ` ("`δ` small depending on `P`"). -/
 def WTPrefixP (Q : ℕ → WTParams → Prop) : Prop :=
```

## 4. Every new definition B1.12 needs (exact text, `Flower-Gate.lean` L47–L295)

`WTPrefixP` and `topCountBelow` are included because they sit in this block (§3). The 19 new definitions are:
- **kernel:** `Garden.extendFix`, `kDomainFix`, `phaseProdOff`, `kernelKgen`;
- **patterns and cutoffs:** `FixPat`, `dyadicCut`, `LayeredGarden.IsFlowerNode`, `.IsTopLeaf`, `.fixPat`,
  `.PatValid`, `.cutWeight1`, `.cutWeight2`, `.sibWeight`;
- **kinds:** `FlowerKind`, `TreeKind`, `LayeredGarden.FlowerKindOK`, `.TreeKindOK`;
- **sums:** `flowerSum`, `coupleSum`.

They also come with the derived instance `DecidableEq FixPat`.

```lean
/-! ## §1 The general kernel -/

section General

variable {w : ℕ}

/-- Branch times from the free times: a designated node `b` (`fix b = some v`) gets the time `v`. -/
def Garden.extendFix (G : Garden w) (fix : GBranch G.tree → Option ℝ)
    (τ : {b : GBranch G.tree // fix b = none} → ℝ) : GBranch G.tree → ℝ :=
  fun b => match h : fix b with
    | some v => v
    | none => τ ⟨b, h⟩

/-- The **time domain with designated nodes**:
- every free node has `𝔏_𝔫 < t_𝔫 < 𝔏_𝔫 + 1`, `0 < t_𝔫 < up(𝔫)`;
- `t_{𝔫'} < t_𝔫` for a branching child `𝔫'` of `𝔫` whenever at least one of the two is free.

The constraints that only involve designated nodes are dropped. Their times are prescribed, and a Dirac
factor `δ(t_𝔫 − s)` sits on the boundary `t_𝔫 = t_{𝔫'}` (T L2331). With the flower parents as the
designated nodes and no lone leaves, this is `kDomain` (bridge `kDomainFix_flowerParents`, probes). -/
def kDomainFix (LG : LayeredGarden w) (up : GBranch LG.garden.tree → ℝ)
    (fix : GBranch LG.garden.tree → Option ℝ) : Set (GBranch LG.garden.tree → ℝ) :=
  {τ | ∀ b, (fix b = none → (LG.layer b.toNode : ℝ) < τ b ∧ τ b < LG.layer b.toNode + 1 ∧
      0 < τ b ∧ τ b < up b) ∧
    ∀ b' : GBranch LG.garden.tree, b'.IsChildOf b → (fix b' = none ∨ fix b = none) → τ b' < τ b}

variable (L γ δ : ℝ) {d : ℕ}

/-- The phase product with the phases at the nodes of `off` removed (`𝒥^†`, T L2327). -/
noncomputable def phaseProdOff (G : Garden w) (off : Finset (GBranch G.tree))
    (k : GNode G.tree → Mom d) (τ : GBranch G.tree → ℝ) : ℂ :=
  ∏ b : GBranch G.tree, if b ∈ off then 1 else
    Complex.exp ((Real.pi * ((G.sign b.toNode : ℤˣ) : ℤ) * δ * L ^ (2 * γ) * omegaNode G k b * τ b : ℝ) *
      Complex.I)

/-- **The general kernel** (R8): `kernelK` with designated fixed-time nodes `fix`, removed phases `off`
and a decoration weight `wt`:
`(δ/(2L^{d-γ}))^n ζ(𝒢) ∑_κ ε_κ wt(k) ∫ 1_{kDomainFix} ∏_{𝔫∉off} e^{πiζ_𝔫δL^{2γ}Ω_𝔫t_𝔫}
∏^{(+,unmarked)}_ℓ F_{𝔏_ℓ}(k_ℓ)`. The integral runs over the free times. -/
noncomputable def kernelKgen (F : ℕ → Mom d → ℝ) (LG : LayeredGarden w)
    (fix : GBranch LG.garden.tree → Option ℝ) (off : Finset (GBranch LG.garden.tree))
    (wt : (GNode LG.garden.tree → Mom d) → ℝ) (up : GBranch LG.garden.tree → ℝ) (k₀ : Mom d)
    (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ) : ℂ :=
  (coupling d L γ δ : ℂ) ^ LG.garden.order * LG.garden.zeta *
    ∑' κ : GenDecoration LG.garden d nroot nfl,
      (epsDec LG.garden κ.1 : ℂ) * (wt (cosetDecoration LG.garden L k₀ κ.1) : ℂ) *
        (∫ τ : {b : GBranch LG.garden.tree // fix b = none} → ℝ,
          (kDomainFix LG up fix).indicator
            (phaseProdOff L γ δ LG.garden off (cosetDecoration LG.garden L k₀ κ.1))
            (LG.garden.extendFix fix τ)) *
        ∏ ℓ ∈ inputLeaves LG.garden,
          (F (LG.layer ℓ.toNode) (cosetDecoration LG.garden L k₀ κ.1 ℓ.toNode) : ℂ)

end General

/-! ## §2 Flower-garden data -/

/-- The **fixed-time pattern** of one flower tree (T L2312, L2331). In every pattern the flower parent
has time `s`.
- `plain`: no other designated node.
- `dRoot`: the root also has time `t` (`∂_t`).
- `dParent`: the parent of `𝔣^pr` also has time `s` (`∂_s`).
- `dChild i`: the `i`-th child of `𝔣^pr`, a branching node, also has time `s` (`∂_s`). -/
inductive FixPat : Type
  | plain : FixPat
  | dRoot : FixPat
  | dParent : FixPat
  | dChild (i : Fin 3) : FixPat
  deriving DecidableEq

/-- The dyadic smooth cutoffs `φ_M`, `M = 2^j L`, behind "`∼₀ M` (or `≲₀ M` if `M = L`)" (T L2283–L2285):
- `φ_L(x) = χ₀(x/L)`;
- `φ_{2^jL}(x) = χ₀(x/(2^jL)) − χ₀(x/(2^{j−1}L))` for `j ≥ 1`.

They sum to `1`. `φ_M` is supported in `|x| < M`, and in `|x| > M/4` when `j ≥ 1`. -/
noncomputable def dyadicCut (L : ℝ) (j : ℕ) (x : ℝ) : ℝ :=
  if j = 0 then chi0 (x / L) else chi0 (x / (2 ^ j * L)) - chi0 (x / (2 ^ (j - 1) * L))

namespace LayeredGarden

variable {w : ℕ} (LG : LayeredGarden w)

/-- The number of layer-`p` branching nodes below `a` (the "order" of T L2290). -/
def topCountBelow (p : ℕ) (a : GNode LG.garden.tree) : ℕ :=
  (Finset.univ.filter fun b : GBranch LG.garden.tree =>
    a.IsDesc b.toNode ∧ LG.layer b.toNode = p).card

/-- `ℓ`'s node is a flower. -/
def IsFlowerNode (a : GNode LG.garden.tree) : Prop :=
  ∃ ℓ : GLeaf LG.garden.tree, LG.garden.IsFlower ℓ ∧ ℓ.toNode = a

/-- The **leaves of the initial flower trees** (T L2283, L2294). These are the non-root nodes with a
layer-`p` parent that are leaves or lie in a lower layer: the paired layer-`p` leaves, the flower, and the
roots of the attached gardens. -/
def IsTopLeaf (p : ℕ) (a : GNode LG.garden.tree) : Prop :=
  (LG.layer a < p ∨ a.1.2 ∈ (LG.garden.tree a.1.1).leaves) ∧ a.1.2 ≠ [] ∧ LG.parentLayer p a = p

open Classical in
/-- **The fixed times** of the pattern vector `pat` (T L2264, L2312, L2331): flower parents ↦ `s`,
and per tree `j`, according to `pat j`, the root ↦ `t` or a neighbour of `𝔣^pr` ↦ `s`. -/
noncomputable def fixPat (pat : Fin w → FixPat) (t s : ℝ) (b : GBranch LG.garden.tree) : Option ℝ :=
  if LG.garden.IsFlowerParent b then some s else
  match pat b.1.1 with
  | .plain => none
  | .dRoot => if b.1.2 = [] then some t else none
  | .dParent => if ∃ c : GBranch LG.garden.tree, LG.garden.IsFlowerParent c ∧ c.IsChildOf b
      then some s else none
  | .dChild i => if ∃ c : GBranch LG.garden.tree, LG.garden.IsFlowerParent c ∧ b.1.1 = c.1.1 ∧
      b.1.2 = c.1.2 ++ [i] then some s else none

/-- The pattern of tree `j` designates an existing node other than `𝔣^pr`. Without it the pattern's
boundary term does not exist. -/
def PatValid (j : Fin w) : FixPat → Prop
  | .plain => True
  | .dRoot => ∃ b : GBranch LG.garden.tree, b.1 = (j, []) ∧ ¬ LG.garden.IsFlowerParent b
  | .dParent => ∃ b c : GBranch LG.garden.tree, LG.garden.IsFlowerParent c ∧ c.1.1 = j ∧ c.IsChildOf b
  | .dChild i => ∃ b c : GBranch LG.garden.tree, LG.garden.IsFlowerParent c ∧ c.1.1 = j ∧
      b.1.1 = j ∧ b.1.2 = c.1.2 ++ [i]

variable {d : ℕ}

open Classical in
/-- The `M₁` weight (T L2283, L2294): per tree, `φ_{M₁}` of the largest `|k|` over the non-flower
leaves of the initial flower tree. -/
noncomputable def cutWeight1 (p : ℕ) (L : ℝ) (j₁ : ℕ) (k : GNode LG.garden.tree → Mom d) : ℝ :=
  ∏ j : Fin w, dyadicCut L j₁ (((Finset.univ.filter fun a : GNode LG.garden.tree =>
    a.1.1 = j ∧ LG.IsTopLeaf p a ∧ ¬ LG.IsFlowerNode a).sup fun a => ‖k a‖₊ : NNReal) : ℝ)

open Classical in
/-- The `M₂` weight (T L2285, L2299): per tree, `φ_{M₂}` of the largest `|Ω_𝔫|` over the stem branching
nodes other than `𝔣^pr`. -/
noncomputable def cutWeight2 (L : ℝ) (j₂ : ℕ) (k : GNode LG.garden.tree → Mom d) : ℝ :=
  ∏ j : Fin w, dyadicCut L j₂ (((Finset.univ.filter fun b : GBranch LG.garden.tree =>
    b.1.1 = j ∧ LG.OnStem b.toNode ∧ ¬ LG.garden.IsFlowerParent b).sup
      fun b => ‖omegaNode LG.garden k b‖₊ : NNReal) : ℝ)

open Classical in
/-- The `†` weight (T L2327): the children of each `𝔣^pr` other than the flower carry the prescribed
vectors `c j i`. -/
noncomputable def sibWeight (c : Fin w → Fin 3 → Mom d) (k : GNode LG.garden.tree → Mom d) : ℝ :=
  ∏ b : GBranch LG.garden.tree, if LG.garden.IsFlowerParent b then
    ∏ i : Fin 3, (if LG.IsFlowerNode (b.child i) then 1 else
      if k (b.child i) = c b.1.1 i then 1 else 0) else 1

end LayeredGarden

/-- The kinds of initial flower trees: `𝒳` (T (operatorxker), without the identity term), `𝒴` and `𝒲`
(T L2273). -/
inductive FlowerKind : Type
  | X : FlowerKind
  | Y : FlowerKind
  | W : FlowerKind

/-- The kinds of trees in couples: `a^tr` (T (trterm)) and `ℒ₀` (T L2312). -/
inductive TreeKind : Type
  | tr : TreeKind
  | L0 : TreeKind

namespace LayeredGarden

variable {w : ℕ} (LG : LayeredGarden w)

/-- **The kind restrictions on the initial flower trees.** "Order" means the number of layer-`p` branching
nodes (T L2290).
- `X`: `1 ≤` order `≤ N_{p+1}`. The `1 ≤` excludes the trivial flower tree, whose term is the identity of
  `𝒳 = 1 + ∑ 𝒥̃` (F39; DH23 (kernelexp)).
- `Y`: (Y-1) order `> N_{p+1}`, (Y-2) each child of the root has `≤ N_{p+1}` below it.
- `W`: (W-1) order `> N_{p+1}`, (W-2) each sibling of `𝔣` has `≤ N_{p+1}` below it, (W-3) order minus the
  count below `𝔣^pr` `≤ N_{p+1}`.

For `Y` and `W` these replace the bound `N_{p+1}` of `ℋ^tr` (F46, delta-1 D1). -/
def FlowerKindOK (p Ntr : ℕ) : FlowerKind → Prop
  | .X => ∀ j, 1 ≤ LG.topOrder p j ∧ LG.topOrder p j ≤ Ntr
  | .Y => ∀ j, Ntr < LG.topOrder p j ∧ ∀ b : GBranch LG.garden.tree, b.1 = (j, []) →
      ∀ i : Fin 3, LG.topCountBelow p (b.child i) ≤ Ntr
  | .W => ∀ j, Ntr < LG.topOrder p j ∧ ∀ b : GBranch LG.garden.tree, b.1.1 = j →
      LG.garden.IsFlowerParent b →
        (∀ i : Fin 3, ¬ LG.IsFlowerNode (b.child i) → LG.topCountBelow p (b.child i) ≤ Ntr) ∧
        LG.topOrder p j - LG.topCountBelow p b.toNode ≤ Ntr

/-- **The kind restrictions on the trees of a couple:**
- `tr`: top order `≤ N_{p+1}` (`a^tr`);
- `L0`: top order `> N_{p+1}`, and each child of the root has `≤ N_{p+1}` below it (`ℒ₀`, T L2312). -/
def TreeKindOK (p Ntr : ℕ) : TreeKind → Prop
  | .tr => ∀ j, LG.topOrder p j ≤ Ntr
  | .L0 => ∀ j, Ntr < LG.topOrder p j ∧ ∀ b : GBranch LG.garden.tree, b.1 = (j, []) →
      ∀ i : Fin 3, LG.topCountBelow p (b.child i) ≤ Ntr

end LayeredGarden

/-! ## §3 The sums -/

open Classical in
/-- **The flower sum** (corrects `truncSumHζ`; T (flowerexp2), L2287–L2290; F39, F46/D1, R8). It sums
`kernelKgen` over the layered flower gardens `𝒢` of width `w` and order `N` such that:
- `𝒢 ∈ ℋ_{p+1}` (stems in layer `p`);
- the attached gardens have order `≤ N_p`;
- the initial flower trees are of kind `kind`;
- the flower signs are `ζ · ζ_j`;
- each tree's pattern is valid.

The kernel data:
- flower parents ↦ `s`, plus the pattern's node;
- the phases at the flower parents removed if `dagger` is given;
- the weights: `M₁` cutoff (index `cut1`), `M₂` cutoff (`cut2`), sibling labels (`dagger`);
- `(n, n')`-decorations: roots `n`, flowers `n'`. -/
noncomputable def flowerSum (P : WTParams) (F : ℕ → Mom P.d → ℝ) (p N : ℕ) {w : ℕ}
    (kind : FlowerKind) (pat : Fin w → FixPat) (dagger : Option (Fin w → Fin 3 → Mom P.d))
    (cut1 cut2 : Option ℕ) (ζ : ℤˣ) (t s : ℝ) (n n' : Fin P.d → ℤ) : ℂ :=
  ∑ᶠ (LG : LayeredGarden w) (_ : IsCanonH (p + 1) LG ∧
      (∀ u ∈ LG.attachNodes p, LG.attachedOrder p u ≤ P.N p) ∧ LG.garden.order = N ∧
      LG.FlowerKindOK p (P.N (p + 1)) kind ∧
      (∀ ℓ : GLeaf LG.garden.tree, LG.garden.IsFlower ℓ →
        LG.garden.sign ℓ.toNode = ζ * LG.garden.sig ℓ.1.1) ∧
      ∀ j, LG.PatValid j (pat j)),
    kernelKgen P.L P.γ P.δ F LG (LG.fixPat pat t s)
      (if dagger.isSome then Finset.univ.filter LG.garden.IsFlowerParent else ∅)
      (fun k => (cut1.elim 1 fun j₁ => LG.cutWeight1 p P.L j₁ k) *
        (cut2.elim 1 fun j₂ => LG.cutWeight2 P.L j₂ k) * (dagger.elim 1 fun c => LG.sibWeight c k))
      (fun _ => t) 0 (fun _ => n) n'

open Classical in
/-- **The restricted couple sum** (T L2312). It sums over the couples `𝒬 ∈ 𝒞_{p+1}` of order `N`
with attached gardens of order `≤ N_p` and trees of kind `kind`. With `dt`, the roots are branching
and have time `t` (`δ(t_𝔯 − t)` of `∂_t`). The root vector is `k ∈ ℝ^d`, as in `KQ`. Without `dt`
and with kind `tr` this is `truncSumC` (bridge in the probes). -/
noncomputable def coupleSum (P : WTParams) (F : ℕ → Mom P.d → ℝ) (p N : ℕ) (kind : TreeKind)
    (dt : Bool) (t : ℝ) (k : Mom P.d) : ℂ :=
  ∑ᶠ (LG : LayeredGarden 2) (_ : IsCanonC (p + 1) LG ∧
      (∀ u ∈ LG.attachNodes p, LG.attachedOrder p u ≤ P.N p) ∧ LG.garden.order = N ∧
      LG.TreeKindOK p (P.N (p + 1)) kind ∧
      (dt = true → ∀ j : Fin 2, ∃ b : GBranch LG.garden.tree, b.1 = (j, []))),
    kernelKgen P.L P.γ P.δ F LG (fun b => if dt = true ∧ b.1.2 = [] then some t else none) ∅
      (fun _ => 1) (fun _ => t) k (fun _ => 0) 0

/-! ## §4 B1.12 -/

/-- The prefix `(Π_P)` of `flowerest1` (T L2279–L2280). It is `(Π)` with the moment order `P` chosen after `ν`
("large depending on `C₁`") and before `δ` ("`δ` small depending on `P`"). -/
def WTPrefixP (Q : ℕ → WTParams → Prop) : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 →
  ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, η ∈ Ioc 0 η₀ →
  ∀ φin : SchwartzMap (Mom d) ℝ, (∀ k, 0 ≤ φin k) →
  ∀ τstar : ℝ, 0 < τstar → ∀ φ : ℝ → SchwartzMap (Mom d) ℝ, IsWKESolution φin τstar φ →
  ∃ C₁ : ℝ, 1 ≤ C₁ ∧ ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ ν : ℝ, ν ∈ Ioc 0 ν₀ →
  ∃ P₀ : ℕ, ∀ Pm : ℕ, P₀ ≤ Pm →
  ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, δ ∈ Ioc 0 δ₀ → ∀ D : ℕ, 1 ≤ D → τstar = D * δ →
  ∃ C₂ : ℝ, 1 ≤ C₂ ∧ ∃ L₀ : ℝ, 2 ≤ L₀ ∧ ∀ L : ℝ, L₀ ≤ L →
  Q Pm ⟨d, γ, η, φin, τstar, φ, C₁, ν, δ, D, C₂, L⟩
```

**Snapshot-5 declarations used** (computed from the elaborated constants with `#print`-style traversal; all frozen):
- `WaveBDraft.Core`: `WTParams` (fields `d D L Lambda N γ δ ν`), `TTree.Path/branching/leaves/nodes`, `Garden`
  (`tree order sig sign zeta IsFlower`), `GNode` (`root IsDesc`), `GBranch` (`child toNode`), `GLeaf.toNode`,
  `GenDecoration`, `IsDecoration`, `cosetDecoration`, `epsDec`, `omegaNode`, `LayeredGarden` (`garden layer
  parentLayer topOrder OnStem attachNodes attachedOrder`), `IsCanonH`, `IsCanonC`, and the instances
  `instFintypeGBranch`, `instFintypeGNode`, `instDecidableEqGBranch`, `instDecidableIsDesc`,
  `LayeredGarden.instDecidableOnStem`;
- `WaveBDraft.System`: `chi0`, `coupling`, `inputLeaves`, `inputsF`, `jbr`, `Garden.IsFlowerParent` (with
  `instDecidableIsFlowerParent`), `GBranch.IsChildOf`;
- `WaveBDraft.Statements`: `RemainderBound`.

## 5. Probes (replacing `WaveB1-Deferred-probes.lean`)

`Flower-Gate-probes.lean` imports `FlowerDraft.Gate`, `WaveBDraft.Lemmas` and `WaveBDraft.CoreProbes`. Everything in
it is sorry-free, with axioms `[propext, Classical.choice, Quot.sound]`:
- **bridges:** `kernelKgen_flowerParents` (`= kernelK`), `kernelKgen_noFix`, `coupleSum_tr` (`= truncSumC (p+1)`);
- **finite supports:** `finite_flowerSum_support` and `finite_coupleSum_support` (new; they replace
  `finite_truncSumHζ_support`);
- **helpers:** `fixPat_plain`, `dyadicCut_zero`, `flowerParent_unique`, `not_isLoneParent`, plus local helpers.

```lean
/-! ### Finite supports -/

/-- The support of the `finsum` defining `flowerSum` is finite. -/
theorem finite_flowerSum_support (P : WTParams) (p N w : ℕ) (kind : FlowerKind) (pat : Fin w → FixPat)
    (ζ : ℤˣ) :
    {LG : LayeredGarden w | IsCanonH (p + 1) LG ∧
      (∀ u ∈ LG.attachNodes p, LG.attachedOrder p u ≤ P.N p) ∧ LG.garden.order = N ∧
      LG.FlowerKindOK p (P.N (p + 1)) kind ∧
      (∀ ℓ : GLeaf LG.garden.tree, LG.garden.IsFlower ℓ →
        LG.garden.sign ℓ.toNode = ζ * LG.garden.sig ℓ.1.1) ∧
      ∀ j, LG.PatValid j (pat j)}.Finite := by
  refine (WaveBProbes.finite_layeredGardens w N p).subset ?_
  rintro LG ⟨h, -, hN, -⟩
  exact ⟨hN.le, h.2.2.1⟩

/-- The support of the `finsum` defining `coupleSum` is finite. -/
theorem finite_coupleSum_support (P : WTParams) (p N : ℕ) (kind : TreeKind) (dt : Bool) :
    {LG : LayeredGarden 2 | IsCanonC (p + 1) LG ∧
      (∀ u ∈ LG.attachNodes p, LG.attachedOrder p u ≤ P.N p) ∧ LG.garden.order = N ∧
      LG.TreeKindOK p (P.N (p + 1)) kind ∧
      (dt = true → ∀ j : Fin 2, ∃ b : GBranch LG.garden.tree, b.1 = (j, []))}.Finite := by
  refine (WaveBProbes.finite_layeredGardens 2 N p).subset ?_
  rintro LG ⟨h, -, hN, -⟩
  exact ⟨hN.le, h.2.1⟩
```

## 6. What else in snapshot 5 changes: nothing

- **Lean declarations:** none outside `WaveB1-Deferred(-probes).lean`. In snapshot 5 only `WaveB1-Deferred-probes.lean`
  imports `WaveBDraft.Deferred`.
- **`FREEZE-LIST.md` / `FreezeList.lean`:** unchanged unless B1.12 joins the freeze set (§0); the existing rows stay
  the same either way.
- **Stale docstring mentions** in frozen files (comments only; optional refresh, which would change their checksums):
  - `WaveB1-Statements.lean` L21–L25 (module docstring): "B1.12 … is deferred … (`WTPrefixP`, `KGflower`,
    `topCountBelow`, `FlowerRestr`, `truncSumHζ`) are kept as drafts in `WaveB1-Deferred.lean`".
  - `WaveB1-System.lean` L25–L26 and L28 (module docstring): "The flower instance `K̃_𝒢` is deferred with B1.12 …
    (`WaveB1-Deferred.lean`)"; "The flower sum `truncSumHζ` is deferred (`WaveB1-Deferred.lean`)".
  - `WaveB1-System-probes.lean` L18: "(the deferred `truncSumHζ`: `WaveB1-Deferred-probes.lean`)".
  - `DESIGN.md` (B1.12 notes, CL-14 entries): to be updated by a CL entry recording this delta.

## 7. Verification (snapshot 5 roots)

- **Build:** `Flower-Gate.lean` and `Flower-Gate-probes.lean` on `../duhamel/build` (= snapshot 5, checksums
  verified).
  - Gate: one warning, `declaration uses 'sorry'` (the B1.12 anchor). Probes: clean.
  - `WaveBDraft.CoreProbes` (snapshot 5 `WaveB1-Core-probes.lean`, unchanged) was built into `../duhamel/build` for
    the finite-support probes.
- **Axioms:**
  - `layergardenFlower`: `[propext, sorryAx, Classical.choice, Quot.sound]` (the anchor);
  - `kernelKgen_flowerParents`, `kernelKgen_noFix`, `coupleSum_tr`, `finite_flowerSum_support`,
    `finite_coupleSum_support`: `[propext, Classical.choice, Quot.sound]`.
- **Imports:** `Flower-Gate.lean` imports only `WaveBDraft.Statements`.
