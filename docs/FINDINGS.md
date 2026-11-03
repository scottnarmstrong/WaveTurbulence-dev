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
- F5 — TARGET L686–L688 — constant hierarchy displayed as `C_0 ≪ η^{-1} ≪ C_1 ≪ δ^{-1} ≪ C_2`; the order actually used
  is C_0 → η → 𝔆 → C_1 → ν → δ (𝔇 = τ★/δ ∈ ℤ) → C_2 → L, with δ^ν ≪_1 1 (ν omitted from the display). Status:
  candidate (exposition). Source: map T-part1 Q1.
- F6 — TARGET L818–L819 (proof of Thm `main`) — "F ⊃ F_p" is false for p < 𝔇 (F_p only gives a solution up to rescaled
  time p); route through F_𝔇. Also (log L)^{20d} vs the theorem's 40d (cf. F1) and a dropped square root of P(F_p^c).
  Easy fixes. Status: candidate. Source: T-part1 Q2.
- F7 — TARGET L821 — the theorem's sup over all t ∈ [0,T] needs `layergarden`, the WKE Taylor expansion and the whole
  inductive step at every rescaled time t′ ∈ (p, p+1], uniformly; the paper says only that this is "clear from the
  proof". Proof obligation: formalize the inductive step at general t′. Status: gap (expository). Source: T-part1 Q3.
- F8 — TARGET L314 — "smooth solution" of (NLS) is not defined; the proof produces an `a`-system solution with decay
  ⟨k⟩^{-50d}. Bridging to a C^∞ NLS solution needs inverse gauge transform, persistence of regularity, uniqueness,
  measurability of F. Proof obligations (NLS packet). Status: gap (standard). Source: T-part1 Q4.
- F9 — TARGET L712 (defjt) — leaf factor should be `a_{k_ℓ}(p)^{ζ_ℓ}` (conjugates on negative leaves), as in DH23;
  also implicit in eqnbk1.5. Status: candidate typo. Source: T-part1 Q5.
- F10 — TARGET L752–L758 — convergence of the WKE Taylor series over one step and `‖𝒰_n‖_{𝔖^{4Λ,4Λ}} ≤ C_2 (C_1 δ)^n`
  asserted "easy to see"; needs a tame estimate for 𝒦 in high norms with base independent of Λ; Appendix C works in
  L²-based norms only. Proof obligation. Status: gap. Source: T-part1 Q6.
- F11 — TARGET L1171, L1247, L957 — imported single-layer results: regref1-5 should read Σ (K*_Q)_app = 𝒰_n (as DH23
  Prop 6.2); the DH23 norm X_loc^{η,40d} → 𝔛^{η,30d,30d}(ℬ) translation is asserted; "Section 7 of DH23" should be
  Section 6. Status: candidates. Sources: T-part1 Q7, DH23 map Q1.
- F12 — TARGET L1–L1292 — several shapes defined only by figures (mini-couple/mini-tree codes, red/green/blue leaf
  pairs, vines (I)–(VIII)); uniqueness in `propstructure` not literally stated in DH21 Props 4.5–4.9; bijection
  between construction data and canonical gardens (`canonequiv`) unwritten. Needs textual definitions before freezing
  Wave B. Sources: T-part1 Q9–Q10, DH23 map Q2, DH21 map E9.
- F13 — DH21 (genericity) — DH21 Secs 6, 8, 9 are for γ = 1 / generic tori; the claimed extension to γ < 1 holds only
  near 1. Route: use DH21 Secs 4, 5, 7 (γ-free) and the DH23/TARGET versions of Secs 6, 8, 9. Source: DH21 map E2.
- F14 — DH21-2 Prop 6.3 — claims χ ≤ m − R/2 for mixed gardens; the DH21 map agent reports a width-4, scale-2
  counterexample with χ = 2 > 1 (trivial trees have no atoms). To check whether TARGET uses this (L370 uses DH21-2 for
  cumulant vanishing). Status: candidate, unverified. Source: DH21 map E5.
- F15 — DH21-2 Prop 3.8 — extends DH21 Props 6.7/6.10 from n ≤ N³ to n ≤ (log L)^{50} citing only "n ≪ L^{δ²}",
  no proof. Status: candidate gap. Source: DH21 map E6.
- F16 — TARGET `deflink` (L874–L881) attributes {x_n′, y_n′} = {±x_n, ±y_n} to DH21 Prop 4.3, which states only
  ζ_n′Ω_n′ = −ζ_nΩ_n; DH21 Prop 4.14 uniqueness step "case-by-case", not written. Status: candidate gaps. Source: DH21
  map E3, E4.
- F17 — DH21 L380 — "κ < L^{d/2}" should be κ < d/2. Typo. Source: DH21 map E1.
- F18 — TARGET Appendix C / GIT20 — GIT20 is written in d = 3; TARGET applies its trilinear estimate (Lemmas 4.1–4.3,
  Remark 2.6) for all d ≥ 3 and s > d/2 − 1. To check in GIT20. Status: open.
