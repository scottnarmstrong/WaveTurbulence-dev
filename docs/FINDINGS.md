# Source findings ledger (candidate errata, gaps, ambiguities)

Format: F<n> — source, TeX line — quoted text — finding — evidence — status (candidate / confirmed by audit / confirmed in Lean / withdrawn).

- F1 — TARGET L795–L823 (proof of Thm `main`) — "so P(F) ≥ P(F_p) ≥ P(F_D) ≥ 1 - e^{-(log L)^{20d}}" vs. the theorem's
  "with probability ≥ 1 - e^{-(log L)^{40d}}" (L314). Harmless: Prop `propansatz`(1) gives P(F_D) ≥ 1 - e^{-N_D} with
  N_D = R_D^{40d}, R_D = ⌊(log L)^{40d}⌋, which implies the stated bound. Status: candidate (typo-level).
- F2 — TARGET L314 vs. L795–L823 — the theorem says "the expectation E is taken assuming (NLS) has a smooth solution on
  [0,T]"; the proof computes E(1_F |û|²) with F the solvability event (not the conditional expectation). Draft Lean
  statement follows the proof (indicator, unconditional). Status: reading choice, to rule.
- F3 — DH23 L2027–L2037 (Lemma `basiccount0pre`(1)) — "using the error term bound of Huxley [Hux93] for counting the
  number of lattice points inside a disc" giving `Q ρ + Q^{7/11}`. Scope risk under D1: Huxley's exponential-sum bound
  is deep. **Preliminary analysis (orchestrator, 2026-11-03):** (1) is used only in Lemma `basiccount0` (1)–(3) and
  `basiccount`(5) (L2076–L2117), each time inside a `min(Q-branch, 1/Q-branch)` that must beat a power of `L`. With the
  classical Sierpiński–van der Corput exponent 2/3 instead of 7/11: in (2) the min is ≲ L^{16/25} < L^{4/5−10^{-4}};
  in (1),(3) the gain becomes ≈ L^{-(2γ−1)/3} instead of L^{-min(10^{-3}, 2γ−1)}, which still beats the needed
  L^{-10η} because η ≪ γ − 1/2. The trivial exponent 1 would fail for 1/2 < γ ≤ 2/3. Planned route: prove the
  circle-problem bound with exponent 2/3 and adapt the constants. Status: open, route proposed; to be confirmed by the
  blueprint review.
- F4 — DH23 map (maps/DH23.md, open questions) lists candidate typos: flower-tree formulas with γ=1 normalization
  (L1996–L1999), `brprop` "Δν = 2" vs computed −2, undefined `⟨x_j,y_j⟩_β` in `approxnt`, a (Cρ)! vs (Cρ)^C slip.
  Status: candidates, to verify.
