# Packet MISC-A — TARGET Lemmas A.6, A.7 (NT9 LINALG), DH21 Lemma A.4, DH21 Lemma A.5 (Hua), probability helpers

Read `COMMON.md` first. Blueprint rows `T.finitelem`, `T.lincomblem`, `DH21.combineq`, `DH21.hua`, `PROB.chebyshev`,
`PROB.condCS`, `PROB.smoothData` in `/home/scott/WaveTurbulence-dev/docs/blueprint/GRAPH.md`.
Worktree: your current one (`/home/scott/WaveTurbulence-worktrees/cumul`); new branch `git switch -c w/misc-a main`.
Files: `WaveTurbulence/Foundations/LinAlg/**`, `WaveTurbulence/Foundations/Combinatorics/**`,
`WaveTurbulence/Foundations/Probability/**`, and `WaveTurbulence/Foundations/WeylSums/Hua*.lean` (new files only; the
rest of WeylSums is wt-gausssum's).

Goals (commit after each; any order you like, but do 1–3 first):
1. **T.lincomblem** (TARGET L2449–L2457, Lemma A.7): any finite S ⊂ ℝ^d contains q ≤ d vectors spanning S with all
   coefficients bounded by 2^{d−1} (maximal-volume selection; read the source for the exact claim).
2. **T.finitelem** (TARGET L2435–L2445, Lemma A.6): the finite-representation lemma for k ∈ ℤ_L^d (systems of height
   ≤ M^{C₀}, a set 𝔑𝔢𝔭 of ≤ M^{C₀} representatives). Read it carefully; state it exactly.
3. **DH21.combineq** (DH21 `/home/scott/wave-turbulence/references/src-2104.11204/Inventiones-Final_Version.tex`
   L2814–L2822, Lemma A.4): Σ multinomial · ∏_j (2|ρ^j|)! ≤ C (2|ρ|)!.
4. **PROB.chebyshev**, **PROB.condCS** (TARGET L813–L815, L819): Markov/Chebyshev for 2P-th moments, union bounds over
   countable families; for E_p = E(1_{F_p} ·): Cauchy–Schwarz, cumulant↔moment conversions with (C₀R)! losses (use the
   landed `Foundations/Cumulant/**`), and E(1_A |g|²) ≤ √2·P(A)^{1/2} for a normalized complex Gaussian g.
5. **PROB.smoothData**: almost surely Σ_k ⟨k⟩^s √φin(k) |g_k| < ∞ for every s (Schwartz φin; uses the landed Gaussian
   API), so the random datum is smooth a.s.
6. **DH21.hua** (DH21 L2823–L2833, Lemma A.5): ‖G_h(·,r,n)‖⁴_{L⁴[0,1]} ≲ n² log(2+n), ‖G_h‖⁶_{L⁶} ≲ n⁴, uniformly in
   (r,h) — coordinate names with wt-gausssum's `WeylSums` API (import it; don't edit its files).
Done: `READY misc-a`.
