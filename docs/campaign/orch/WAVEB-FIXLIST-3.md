# Wave B fix list 3 (orchestrator, 2026-11-03 ~19:20) — apply in /home/scott/wt-scratch/waveb/, changelog CL-n with tags

Sources: docs/campaign/orch/audits/WaveB-delta-stage3.md (stage-3 delta: R1–R9 closed; new N1), WaveB-delta-1.md
(wt-orch: stage-1/2 closed; D1), Infra-review-2.md §S (S1–S6 integration items). All on main.

REQUIRED
1. **N1** — `nlsAkBridge`: add `(hD : 1 ≤ D)` right after `(D : ℕ)` and a deviation D3 in the docstring (the 𝔇 = 0 case
   is false: derivWithin on {0}). Replacement in the audit's `Delta3Fix.lean` (path in the audit).
2. **N-guard** (ruling from wt-anfourier's question): in the 𝔛^{θ,Λ₁,Λ₂} norm definitions require C^{Λ₁} regularity
   of k ↦ F̂(λ,k) only when Λ₁ ≥ 1; for derivative order 0 (incl. 𝔛^{θ,0,0}) impose no momentum regularity (keep the
   time-integrability guard). The source's L^∞_k needs none and k often ranges over a lattice.
3. **Freeze-set closure policy**: every definition in the freeze set must depend only on frozen definitions (Wave A)
   and Mathlib — never on Foundations definitions (the anchor checker's definition_closure must consist of manifest
   definition anchors). Keep the Wave B definitions self-contained; where a landed Foundations object is the same
   (S1 χ₀ vs `Fourier.chi0`/`chi0Tensor`; S2 a-system vs `NLS.IsAkSolution` etc.; S3 norms vs `spatialNorm`,
   `mixedFourierNorm`, `timeFourierNorm`; S4 `wkeTaylorTerm` vs `taylorU`), add a **bridge lemma** (equality /
   equivalence) in a probe file and prove it where cheap (S1, S2, S4 at least); list unproved bridges as provider
   obligations in DESIGN.md. Fix any reference that no longer resolves after the Foundations namespace moves (S2).
4. **D1**: keep `truncSumHζ`, `FlowerRestr`, `KGflower`, `layergardenFlower`, `WTPrefixP`, `topCountBelow` out of the
   freeze set (deferred to packet X1 with B1.12); mark them clearly as deferred drafts.
OPTIONAL (apply): delta-stage3 §7 O1–O5 (unused η binder in countLemma, canonicalCharacterization docstring "kind 0",
WAVE-B B2.1/B2.2 regularity via the 𝔖^{40d,40d} bound, DESIGN refresh, `IsAkSolution.mono` in the glue list).
QUESTION to check and answer in DESIGN.md: **sumint D7** — in every TARGET consumer of `sumint` (vineest, ladder bounds;
see blueprint rows citing T.sumint), do the shifts h₁, h₂ have coefficient sum 1 and no constant lattice offset? If any
needs an offset, extend the datum now.
When done: new snapshot is taken by the orchestrator; print `READY waveb-fixes4`.
