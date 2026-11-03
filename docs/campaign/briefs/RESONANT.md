# Packet N5 RESONANT — resonant measure, principal value 1/Ω, DH21 Lemma 6.3

Read `COMMON.md` first. Blueprint rows `AN.resonantMeasure`, `DH21.NTOmegainv` (packet N5) in
`/home/scott/WaveTurbulence-dev/docs/blueprint/GRAPH.md`.
Worktree `/home/scott/WaveTurbulence-worktrees/resonant`, branch `w/resonant`. Files: `WaveTurbulence/Foundations/Resonant/**`.
Build on the landed `WaveTurbulence/Foundations/WKE/{DeltaReading,Hyperplane,CollisionOp,Characterization}.lean`
(owned by wt-wke: import them, do not edit; ask the orchestrator if you need a change there).

Goals (commit after each):
1. **AN.resonantMeasure**: `resonantIntegral Ψ k := ∫_{ℓ₁} (2|ℓ₁|)⁻¹ ∫_{w ∈ ℓ₁^⊥} Ψ(k+ℓ₁, k+ℓ₁+w, k+w)` — the
   integral of Ψ(k₁,k₂,k₃) against δ(k₁−k₂+k₃−k)δ(|k₁|²−|k₂|²+|k₃|²−|k|²) in the same parametrization as the frozen
   `collisionOp` (prove `collisionOp` is the special case); bounds for Ψ with polynomial decay; smooth dependence on
   k (derivatives under the integral); the mollified-limit characterization (reuse wt-wke's
   `tendsto_mollified_collisionOp_k` route). Sources: TARGET L2502–L2505; DH21
   `/home/scott/wave-turbulence/references/src-2104.11204/Inventiones-Final_Version.tex` L1814–L1837.
2. **Principal value** p.v. 1/Ω in the same parametrization: define it as the limit with a cutoff χ_∞ (state existence
   of the limit as a theorem first; the definition then uses the proved limit), bounds.
3. **DH21.NTOmegainv** (DH21 L1305–L1367, Lemma 6.3): the principal-value limits
   `lim_{μ→∞} ∫ Ω⁻¹ χ_∞(μΩ) χ₀ χ₀ Θ e(·)` exist with uniform bounds (read the source for the exact form; use generic
   smooth compactly supported cutoffs; the frozen χ₀ comes in Wave B).
Done: `READY resonant`.
