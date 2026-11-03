# Packets N2 AN-PHASE + N3 AN-HY — Poisson summation, stationary phase, Hausdorff–Young, time-integral lemmas

Read `COMMON.md` first. Blueprint rows (packets N2, N3) in `/home/scott/WaveTurbulence-dev/docs/blueprint/GRAPH.md`:
`AN.poisson`, `AN.nonStat`, `AN.statPhase`, `AN.hausdorffYoung`, `AN.dny21`, `T.timeintlem`, `T.timeintlem2`.
Same worktree (`/home/scott/WaveTurbulence-worktrees/an-fourier`); new branch `git switch -c w/an-phase main`.
Files: `WaveTurbulence/Foundations/Fourier/**` (namespace `WaveTurbulence.Fourier`), building on your landed AN-FOURIER.

Goals (commit after each):
1. **AN.poisson** (TARGET L1035, L1541, L1575): Poisson summation on ℤ_L^d = L⁻¹ℤ^d and on products, for Schwartz /
   compactly supported smooth functions (Mathlib has `Real.tsum_eq_tsum_fourierIntegral`-type results; wrap them).
2. **AN.nonStat** (T L966, L1550): non-stationary phase |∫ χ(x−a) e(⟨w,x⟩) dx| ≲_N ⟨w⟩^{−N} uniformly in a.
3. **AN.statPhase** (T L968; DH23 L1013ff): |∫∫ χ₀(x−a) χ₀(y−b) e(⟨ξ,x⟩ + ⟨ξ′,y⟩ + s⟨x,y⟩) dx dy| ≲ ⟨s⟩^{−d} uniformly
   (bilinear phase; an exact Fourier computation, no general stationary phase needed).
4. **AN.hausdorffYoung** (T L2370): ‖F̂‖_{L^{p′}(ℝ²)} ≤ ‖F‖_{L^p(ℝ²)}, 1 ≤ p ≤ 2 (Riesz–Thorin, or Mathlib if present).
5. **AN.dny21**: DNY21 (`/home/scott/wave-turbulence/references/src-1905.04352/main.tex`, Lemma `lin` at L392 — the
   paper's Lemma 3.1; check), the kernel bound of the truncated Duhamel operator ℐ_χ:
   |K(ξ,σ,ξ′,σ′)| ≲ ⟨ξ⟩⁻¹⟨ξ−ξ′⟩⁻¹⟨σ⟩⁻¹⟨σ−σ′⟩⁻¹ (read TARGET L2365 for the exact form used).
6. **T.timeintlem** (TARGET L2353–L2379, Lemma A.2; note map Q13a: a missing log) and **T.timeintlem2** (L2380–L2420,
   Lemma A.3), in the 𝔛 norms of your AN-FOURIER packet.
Done: `READY an-phase-hy`.
