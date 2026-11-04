# Source findings ledger (candidate errata, gaps, ambiguities)

Format: F<n> — source, TeX line — quoted text — finding — evidence — status (candidate / confirmed by audit / confirmed in Lean / withdrawn).

- F1 — TARGET L795–L823 (proof of Thm `main`) — "so P(F) ≥ P(F_p) ≥ P(F_D) ≥ 1 - e^{-(log L)^{20d}}" vs. the theorem's
  "with probability ≥ 1 - e^{-(log L)^{40d}}" (L314). Harmless: Prop `propansatz`(1) gives P(F_D) ≥ 1 - e^{-N_D} with
  N_D = R_D^{40d}, R_D = ⌊(log L)^{40d}⌋, which implies the stated bound. Status: candidate (typo-level).
- F2 — TARGET L314 vs. L795–L823 — the theorem says "the expectation E is taken assuming (NLS) has a smooth solution on
  [0,T]"; the proof computes E(1_F |û|²) with F the solvability event (not the conditional expectation). Draft Lean
  statement follows the proof (indicator, unconditional). Status: reading choice, to rule.
- F3 — DH23 L2027–L2037 (Lemma `basiccount0pre`(1)) — "using the error term bound of Huxley [Hux93] for counting the
  number of lattice points inside a disc" giving `Q ρ + Q^{7/11}`. Scope risk under D1 (Huxley is deep).
  **Revised 2026-11-03 (wt-nt audit, commit 3229554 on w/nt-circle, `ExponentAudit.lean`):** the orchestrator's first
  analysis (exponent 2/3 suffices everywhere) was wrong for `basiccount0`(2): it used the printed three-entry min at
  L2082, but (disclattice) is a two-branch min whose second branch is a *sum* (F31). With discrepancy exponent `e`,
  the uses (1), (3) and `basiccount`(5) work for `e = 2/3` (saving L^{-(2γ−1)/3} ≫ L^{-10η}); use (2) (γ > 4/5 − 10η)
  needs `e < 2/3` strictly (at γ = 4/5, Q = L^{6/5} the 2/3 bound gives exactly L^{4/5}); any fixed `e < 2/3` suffices
  once η is small. Exponent-pair calculus: circle error `Q^{(κ+λ)/(1+κ)}`; the A-process alone (pair (1/6,2/3)) does
  not beat 2/3; the classical pair (11/30, 16/30) (A- and B-processes) gives `e = 27/41 ≈ 0.659`. **Route:** prove a
  circle-problem bound with some `e < 2/3` by van der Corput's method (Weyl differencing + Poisson/stationary-phase
  B-process), not Huxley. Status: route set; packet NT-EXPSUM.
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
- F14 — DH21-2 Prop 6.3 — **WITHDRAWN** (wt-orch, docs/campaign/orch/figure-defs.md §9): the DH21 map's
  "counterexample" is a multi-couple (two couples), not a mixed garden; Prop 6.3 is true (one-line repair of its proof
  for trivial trees), and TARGET does not depend on it (L370 is motivational; substantive DH21-2 uses are Props
  4.4–4.6 and 6.4). Status: withdrawn.
- F15 — DH21-2 Prop 3.8 — extends DH21 Props 6.7/6.10 from n ≤ N³ to n ≤ (log L)^{50} citing only "n ≪ L^{δ²}",
  no proof. Status: candidate gap. Source: DH21 map E6.
- F16 — TARGET `deflink` (L874–L881) attributes {x_n′, y_n′} = {±x_n, ±y_n} to DH21 Prop 4.3, which states only
  ζ_n′Ω_n′ = −ζ_nΩ_n; DH21 Prop 4.14 uniqueness step "case-by-case", not written. Status: candidate gaps. Source: DH21
  map E3, E4.
- F17 — DH21 L380 — "κ < L^{d/2}" should be κ < d/2. Typo. Source: DH21 map E1.
- F18 — TARGET Appendix C / GIT20 — GIT20 is written in d = 3; TARGET applies its trilinear estimate (Lemmas 4.1–4.3,
  Remark 2.6) for all d ≥ 3 and s > d/2 − 1. To check in GIT20. Status: open.
- F19 — TARGET §7–§8 (L1326–L1530) — vines (I)–(VIII), ladders (insertion rules), vine positions and cuts are defined
  only by figures (Vines.png, Block_Mole.png, Cut.png). The T-part2 map transcribes them "[from figure]"; textual
  definitions must be fixed (and checked) before Wave B. Source: T-part2 Q1.
- F20 — TARGET §7.3–§7.4 (L1427–L1488) — twists: "exactly two options to insert u₂" (L1431) needs a full case table;
  `lftwistprop` (L1487) checks only (II-a)→(II-b); congruence being an equivalence relation is asserted. Gap.
  Source: T-part2 Q2.
- F21 — TARGET `vineest` Step 3, `subpro`(3) — degenerate decorations (k₁ = k₂ = k₃, self-loops, degree-2 atoms) are
  handled in one sentence; "non-hinge zero-gap atoms are tame" is new and unproved; DH23 §10.5 (couples) applied to
  gardens. Gap. Source: T-part2 Q3.
- F22 — TARGET L1811–L1817 — parametrizations of vines (IV)–(VIII) only called "similar". Gap. Source: T-part2 Q4.
- F23 — TARGET `sumint` — case (d) for γ > 8/9 needs an unstated second bound of `lemlin` (|r| ≥ L⁻¹); an extra
  δ^{-1/2} per bad vine silently absorbed; extension behind 𝔛(ℬ) unspecified; typos L1615, L1687. Source: T-part2 Q5.
- F24 — TARGET L2197 — "Lemma 10.2 of DH23" is Prop 10.2 (`moleprop2`), whose last clause assumes ≤ w small-gap atoms
  (unchecked here); DH23 Props 9.4–9.6 "follow from exactly the same proof" for gardens — unverified; "at most R
  imperfect components" affected by zero-gap removals (`remtame`(ii)). Gap. Source: T-part2 Q6.
- F25 — TARGET L2264–L2265 (`jtflower`, `kqflower`) — prefactor (δ/(2L^{d−1}))ⁿ should be (δ/(2L^{d−γ}))ⁿ (as in
  DH23 L1996–L1999, same slip). Typo. Sources: T-part2 Q7, DH23 map Q3.
- F26 — TARGET `flowerest1` — flower gardens: extra degree deficits, Dirac time nodes, stem-in-layer-p rule not restated
  for molecules/blocks/vines; operator identities (1−ℒ₁)𝒳 = 1+𝒴, 𝒳(1−ℒ₁) = 1+𝒲 asserted. Gap. Source: T-part2 Q8.
- F27 — TARGET `layergarden` (L761) — stated at time p+1, used at every t ∈ [p, p+1] (L821, L2309); freeze with a time
  parameter (cf. F7). The coherent-couple term (`finaltermd`) ignores the truncation of 𝒞^{tr}_{p+1} (negligible).
  Source: T-part2 Q9.
- F28 — TARGET typos with content: L1807 (ζΩ, not Ω), L1823 (u not w), L1909 (layerreg2 → sumint), L2082 (√δ → √η),
  L1523 ("Vine (V) minus two joints" false for (VII); argument survives), L1505 (omitted bond factor, harmless).
  Source: T-part2 Q10.
- F29 — External inputs not among pinned sources: DNY21 Lemma 3.1 (kernel bound in `timeintlem`), Oh–Thomann Lemma 2.6
  (replaced by our own hypercontractivity proof), quadratic Weyl sum bounds and their L^p moments (p = 3d/2). To pin.
- F30 — TARGET Lemma `propertycm` (L2343–L2346) — "there is no proper subset A ⊂ {1,…,r} such that ∪_{i∈A} S_i equals
  the union of some of the sets B ∈ 𝒫": read literally, A = ∅ always qualifies (empty union of blocks), so no
  partition would be admissible; the intended condition is "no nonempty proper subset". Also the groups S_i must be
  nonempty: for an unnormalized measure (expectations "assuming F", mass m ≠ 1), S₁ = ∅, S₂ = {j} gives
  κ(1, X_j) = (1 − m)∫X_j while the irreducible sum is empty (all TARGET uses have nonempty S_i). Found by wt-cumul;
  both adopted in the Lean statement. Status: candidate (wording).
- F31 — DH23 L2082 — "min(L^{2/5}+Q^{7/11}, L^{1/5}+L^{8/5}Q^{-1}, L^{6/5}Q^{-1/3})": the comma before the last
  term should be "+" (deduced from the two-branch (disclattice) L2029). With Huxley's 7/11 the argument still works
  (split at Q = L^{99/80}: 63/80 < 4/5 − 10^{-4}). Also L2077 "with ρ ∼ L^{2−2γ}" should be Qρ ∼ L^{2−2γ}.
  Found by wt-nt. Status: candidate typos.
- F32 — GIT20 Remark 2.6 (Kin8.tex L592–L594) — the d-dimensional trilinear estimate (s > (d−2)/2) is asserted without
  proof; GIT20 proves only d = 3, and TARGET (L2516) relies on the remark for all d ≥ 3. Confirms F18. Under D1 the
  d ≥ 4 case is new work in packet WKE. Source: wt-orch delta audit Q5. Status: gap (external).
- F33 — TARGET L949 vs DH23 L1168 — regular-couple asymptotics are used for orders up to N_{p+1}^4 = (log L)^{C(𝔇)},
  but DH21/DH23 prove them only for n ≤ N³ = (log L)^{12} (`approxnt` with λ_j ≤ (log L)^4). Same nature as F15.
  Gap: the extension must be proved. Source: blueprint GRAPH §F.2a (GAP.largeOrder). wt-orch topology review I13: a
  crude bound absorbed by δⁿ is not available (the trivial bound on K_Q loses ≈ L^γ per order), so the regular-couple
  asymptotics must genuinely be extended to orders up to N_{p+1}^4 (route R14 decided).
- F34 — Route: TARGET never uses Gaussian hypercontractivity; its large-deviation bounds (fixedest1–3) come from
  2P-th moments computed with the cumulant ansatz plus Chebyshev (L2306–L2335). Packet GAUSS-HC (DH21 Lemma A.3, done)
  is off-route; landed as infrastructure only. Source: blueprint GRAPH §F.2a, verified by the orchestrator.
- F35 — TARGET Prop `canonequiv` (L889) condition (ii) must be read for incomparable nodes (nested/equal nodes can
  never be completely paired); the Lean definition states it. Source: blueprint.
- F36 — TARGET (atomcountbd3) (L2474) is unused in L1293–L2339; `layergarden`'s proof uses the induction hypothesis
  only through R_q and (ansatz2) (L949–L951), so it can be frozen deterministically. Source: blueprint.
- F37 — TARGET L1384 vs DH23 L790 (ladders in vines) — TARGET requires every ladder to have ≥ 2 rungs while DH23
  defines length = #rungs − 1 with no lower bound; with the figure's insertion rule TARGET's literal vine family misses
  every vine in which a dashed pair carries exactly one extra rung (DH23's family includes them). Reading adopted for
  Wave B: "each dashed pair carries k ≥ 0 extra rungs" (DH23's family); "length ≥ 1" only for standalone ladders.
  Source: wt-orch figure-defs §1 (V1). Status: candidate erratum.
- F38 — TARGET §7.3 (L1427–L1434) — the unit twist is one uniform operation in all six core cases (swap the slot of
  𝔲₂ with the leaf 𝔲₀; 𝔲₂₃ keeps its position; 𝒯₁, 𝒯₂ keep root signs and swap positions); this replaces "exactly two
  options" (F20); congruence being an equivalence relation still needs three stated lemmas. Source: wt-orch
  figure-defs §3. Status: resolution of F20 (definition), lemmas to prove.
- F39 — TARGET L2271 — 𝒳's kernel uses flower trees of order ≥ 1, so (1−ℒ₁)𝒳 = 1+𝒴 needs an identity term from
  somewhere; check against DH21 §11 (part of F26). Source: wt-orch figure-defs §7. Status: open.
- F40 — Cutting at an atom with a self-loop (paired siblings) is ambiguous (TARGET L2118–L2127); encode molecules with
  half-edges. (II-a) vs (II-b) is a labelling convention only. Source: wt-orch figure-defs §2, §4. Status: design notes.
- F32 (update, wt-wke 2026-11-03) — failing step located: in GIT20 Lemma 4.2, inequality (bil7), the radial
  Cauchy–Schwarz step becomes sup_p ∫₀^∞ ⟨rθ+p⟩^{-2s} r^{d−3} dr, which grows like R^{d−3} at p = −Rθ for d ≥ 4; Lemma
  4.3(ii) transfers for 2s > d−2; Lemma 4.1 needs an unproved d-dimensional dispersive bound. Consequence: the frozen
  `wkelwp` conjunct 3 (L²_s blow-up for every s > d/2−1, d ≥ 4) has no written proof. TARGET never uses the blow-up
  criterion after Prop `wkelwp`; Theorem 1.1 (`main`) does not depend on it. Author decision pending; research agent
  investigating the general-d estimate.
- F41 — TARGET L617–L623 — "χ_0 … in Gevrey class 2 (i.e. the m-th order derivatives are bounded by (2m)!)": the
  literal bound is impossible for a cutoff equal to 1 on [−1/2,1/2] and 0 off (−1,1) (m = 1: |χ₀′| ≤ 2 forces slope
  −2 on all of (1/2,1), contradicting smoothness at 1/2). Reading adopted: |χ₀^{(m)}| ≤ C·A^m·(2m)! with absolute
  constants (Gevrey 2). Found by wt-anfourier. Status: candidate erratum (wording); also affects WAVE-B §2.6.
- F32 (update 2, 2026-11-03 ~17:15) — research note `docs/research/git20-general-d.md` (Opus research agent) claims a
  complete proof of (schappend8) for every d ≥ 3, s > d/2 − 1, j = 0..3 (Theorem 7: Tonelli, polar coordinates, one
  linear change of variables, Hölder, a weighted Schur/AM–GM step that moves the radial weight A_k(θ) onto the
  integrated variable, and the ℓ₁ ↔ ℓ₃ symmetry of the resonant measure); sharpness for s < d/2 − 1; blow-up criterion
  then follows through Appendix C unchanged; GIT20's (bil7) is true in all d ≥ 3 and only the preceding radial
  Cauchy–Schwarz step needs replacing. Status: claimed; independent refute-first audit by wt-orch pending. If it
  survives, the frozen `wkelwp` stays unchanged (no owner decision needed) and a packet formalizes Theorem 7.
- F32 (resolved on the mathematics, 2026-11-03 ~17:20) — wt-orch's refute-first audit
  (`docs/campaign/orch/audits/GIT20-general-d.md`) finds Theorem 7 of `docs/research/git20-general-d.md` CORRECT: the
  L²_s trilinear estimate holds for all d ≥ 3, s > d/2 − 1, j = 0..3; every condition reduces to 2s > d − 2; the blow-up
  passage through Appendix C goes through with three routine supporting lemmas (Leibniz/weight identities for Z_{s,m}
  inputs; equivalence of `IsWKESolution` with the Z_s mild solution; 𝒮 = ⋂ Z_{s,m}). **The frozen `wkelwp` stays
  unchanged; no owner decision needed.** Formalization: packet WKE-L2S. Erratum for the authors: GIT20 Remark 2.6 is
  unproved as written for d ≥ 4 (one radial Cauchy–Schwarz step fails; fixed by Theorem 7) and false for d = 2 (§8.3).
- F42 — TARGET Lemma A.3 (L2380–L2420, `timeintlem2`) — the printed bound ‖𝒰_χF‖_{𝔛^{1/4,0,0}} ≲ ‖∂∂F‖_{L^∞_kL¹} is false for
  arbitrary F (F ≡ 1: right side 0, while 𝒰_χF(t,0) = t²/2 on (0,1/2) for χ = χ₀); the proof uses smooth compactly
  supported F, which is the class at the use site (T.pl1.S4). Lean statement takes that hypothesis. Found by wt-anfourier.
  Status: candidate erratum (missing hypothesis).
- F43 — TARGET (atomcountbd) L2472 (Lemma `atomcountlem`) — the first bound is stated without k ≠ 0; it is false at k = 0
  with signs (+,−) and γ > 1/2 (≈ L^d solutions vs. the claimed C·L^{d+1−2γ}); DH23 Lemma A.3(1) has |k₁−k₂| ∼ R ≥ L⁻¹,
  i.e. k ≠ 0. Consumers (degenerate atoms, F21) must exclude or handle k = 0. Found by the independent Wave B stage-3
  auditor (docs/campaign/orch/audits/WaveB-stage3.md R4). Status: candidate erratum (missing hypothesis).
- F44 — Lean pitfall (not a source issue): in this Mathlib `ContDiff ℝ ⊤` means real-analytic (`ω`); C^∞ is
  `ContDiff ℝ (⊤ : ℕ∞)` / `∞`. Wave A uses `(⊤ : ℕ∞)` (correct); the Wave B drafts used `⊤` (R1). Every brief and audit
  must check this.
- F45 — DH23 L1099 — after the change to (p,q) variables the phase is written `p·ξ + y·ζ`; it must be `p·ξ + q·ζ`. Typo.
  TARGET L1567 — "|t′| ≥ L⁻¹ forces a ≠ 0": at the boundary t′ = L⁻¹, a = 0, q = 1 satisfies the weak Dirichlet error;
  harmless (null endpoint). Found by wt-gausssum (HUA). Status: candidate typos.
- F47 — TARGET L1541–L1542 (proof of `lemlin`) — after the Poisson identity with prefactor L^d, the displayed majorant
  (lemlin3) omits that factor; needed to recover (lemlin2). Typo. Found by wt-cumul (LEMLIN). Status: candidate.
- F3 (RESOLVED, 2026-11-03 ~21:30) — wt-ansob (packet NT-BPROC, `Foundations/VdCB/**`, commit ca5a6f6) proved the
  B-process for the actual circle family and the exponent pair (11/30, 16/30), giving unconditional circle-problem
  discrepancy and annulus bounds with exponent 27/41 < 2/3. Huxley's 7/11 is not needed; DH23 Lemma A.2(2) can be proved
  with 27/41 (packet COUNT).
- F48 — TARGET L2152 (`remtame`) — "some component contains exactly one atom adjacent to v" is used to conclude that all
  labels incident to a removed tame atom v are fixed; false: explicit prime 4-tree garden counterexample (two residual
  components, each with one atom adjacent to v but two opposite-oriented crossing bonds with equal labels that cancel in the
  cut identity, so the label varies over ≳ L choices). Correction adopted: replace both occurrences by "exactly one bond
  connecting the component to v" (the bridge criterion of DH21 Lemmas 9.13–9.14 and DH23 §10.5(4)); case (ii) negated
  consistently. Found by wt-ansob (DEGEN), confirmed by its independent reviewer; write-up docs/research/erratum-remtame.md;
  independent check by wt-orch pending. Status: candidate erratum (substantive; local fix).
- F49 — TARGET Appendix A.2–A.3 proofs (L2370, L2392–L2394, L2417–L2419) — (i) the convolution step at L2370 (proofichi-2)
  suppresses a logarithm (map Q13a); (ii) "a simple calculation yields" uniform low-frequency Fourier decay (weakdecay) is
  false before localization; (iii) "bounded in Schwartz class ... uniformly in ξ and k" (timeintproof2-4) is false globally
  (at Γ₁(k) = ξ the tail integral of χ² is nonzero). All three were repaired in the Lean proofs without changing the lemma
  statements (beyond F42). Found by wt-anfourier (AN-PHASE-HY). Status: candidate errata (expository).
- F48 (CONFIRMED by wt-orch, docs/campaign/orch/audits/F48-check.md): counterexample verified mechanically (valid prime
  garden, ε = −1, c_v/Γ_v fixed, k free over L/4+1 values, Δχ = −2); the bridge correction is exactly what remtame (i)/(ii),
  remtame2 and DH21 increF/cutlem need; no B1/B2 statement affected.
- F50 — DH23 L1147–L1155 (Lemma 6.7, `NTintlem`) — `μ⁻¹∫ψ(μΩ)…` should be `μ∫ψ(μΩ)…` in (1) and (2); the error
  `μ^{1−2η}` in (2) should be `μ^{−(1−2η)}` (cf. DH21 Lemma 6.5); the bound is bilinear in the Φ- and ψ-norms. Corrected
  in the Lean statements (wt-torus, NTSP). Source: wt-orch Infra-review-3 R1(a). Status: candidate errata.
- F51 — DH23 L2040 — `#(A ∩ ℤ^d)` should be `#(A ∩ ℤ²)`. Typo. Found by wt-nt (NT-CIRCLE v2). Source: Infra-review-3 R1(b).
- F52 — TARGET L1308–L1325 (decorations of molecules ↔ decorations of gardens) — the correspondence fails for gardens
  with directly paired trivial roots: e.g. four trivial trees, signs (+,−,+,−), root values (0,1,1,0) satisfy global
  conservation but admit no garden decoration, while the (empty) molecule admits one. Correction adopted: state the
  correspondence under root-pair compatibility (directly paired roots have equal prescribed values), which is exactly the
  indicator the garden sums carry. Found by wt-nt (MOLE), Lean counterexample in scratch
  (`mole/src/MoleculeDecorationEdgeCase.lean`). Status: candidate erratum (missing hypothesis; local).
- F53 — Wave B2 draft `IsLadder` (`wt-scratch/waveb2/WaveB2-Molecules.lean` L305) vs TARGET L1384–L1386 / DH23
  Def 5.1 L789–L808 (F37) — the draft requires the induced atom group of a ladder of length m to carry exactly 4m+2
  bonds; this excludes maximal source ladders with an end-to-end chord. Kernel counterexample (wt-ansob, DEGEN):
  `Degen.MaximalLadderDisjoint.chordLadder`, six atoms, eleven bonds, an actual nonsaturated molecule, whose two
  overlapping four-atom induced B2 ladders are both maximal while the six-atom selected ladder fails the count (11 vs
  10). DEGEN proved its results with the selected rung/rail reading (`SourceLadder`: double rungs, single opposite
  rails, no induced-card clause). Status: **B2 draft defect** (ours, not the source's); fix `IsLadder` before the B2
  freeze — queued for the B2 drafter after O-FK. Record: `wt-scratch/degen/ERRATUM-B2-LADDER.md`.
- F54 — DH23 L1003, L1005 (Prop 6.4, (conclusion1), (intappr)) — the inner product `⟨x_j, y_j⟩_β` is carried over from
  DH21; DH23 has no `β` (square torus). Read as `⟨·,·⟩`. Typo. Found by wt-torus (APPROXNT). Also (F33 addendum, same
  packet): DH23 Prop 6.4 assumes `n ≤ (log L)^3` (L1002) but L1168 applies it to orders up to `N^3 ≈ (log L)^{12}`; the
  landed extension holds for every fixed power of `log L`, so both F33 readings are covered.
  F53 addendum (2026-11-04): the B2 fix is B2-CL-3 (wt-gauss-hc): `IsLadder` = wt-ansob's `Degen.SourceLadder` verbatim
  (double rungs, rails of multiplicity exactly 1 and oppositely directed, no induced clause). An intermediate version
  (B2-CL-2) had dropped the single-rail requirement, which admits a length-1 ladder with a double rail (wt-orch's
  `dblRail` probe, audits/DEGEN-F53.md); B2-CL-3 restores it. Audits: NLS-BRIDGE PASS, APPROXNT PASS (η₀ ≤
  min(1/20, (d−1)(1−γ), γ) inside Π; n ≤ (log L)^A with A = A(d, 𝔇) covers F33).
- F55 — DH21 Cor 4.9 (proof; counting of regular couples) — the proof miscounts the choices for double chains; the
  corollary (≤ C₀^m regular couples of order 2m) still holds, and REG-STRUCT's proof (C₀ = 12^9, codes and actual
  couples/trees) does not use the faulty step. Found by wt-orch (Task 15, audits/REG-STRUCT-prefreeze.md R15-4).
  Status: erratum in a proof, statement unaffected. Related B2 drafting items (R15-1, R15-2): add the count
  obligation (couples and trees, tree count with the root sign fixed — it fails at m = 0 otherwise) to the B2 §4
  statements before the B2 freeze; R15-3: the general-couple skeleton uniqueness (DH21 L833, GAP.skeletonUniq) is
  packet C3's, not discharged by REG-STRUCT.
- F56 — Wave B snapshot 5 `WaveB1-Sumint.lean` `SumintDatum.phase` (L197–L215) vs TARGET (sumintI1) L1608–L1611 —
  **our statement bug**: `∏ i, (…) * ∏ i : {i // D.S.nor i = true}, …` parses as `∏ i, ((…) * ∏ i' : Nor, …)`
  (Mathlib's `∏ x, body` parses `body` at precedence 67, and `*` is 70), so the normal-block product is repeated `I`
  times. Fix: `(∏ i, (…)) * ∏ i : Nor, …`, in snapshot 6 (with B1.12). Found by wt-anfourier (SUMINT). Lesson:
  sweep every frozen candidate for big-operator scope errors (`∑`/`∏` bodies continuing past `*`, `•`, `^`); `∑`
  stops before `+` (65 < 67) but not before `*`.
- F57 — TARGET `defblock` L1328–L1331 and DH23 Def 4.10 (concatenation of blocks) — the claim that the concatenation
  of two (degree-only) blocks sharing a joint is a block/hyper-block is false: kernel counterexample
  `MoleculeBlockEdgeCase` (loops at atoms 0, 2, 4, opposite double bonds 1–2, 3–4; A = {0,1,2}, B = {0,3,4}). The
  minimal correction is internal connectedness of each block/adjoint, used throughout MOLE's overlap proof. **B2
  drafting item:** the B2 block definitions are degree-only and must add connectedness before the B2 freeze. Found by
  wt-nt (MOLE). Status: candidate erratum (missing hypothesis).
- F58 — TARGET `propcplmol` L1304–L1306 — the irreducible-garden sentence omits the qualifier "nontrivial" that the
  couple sentence has; the trivial paired roots give n = E = 0, contradicting E = 2n − R at R = 1. The B2
  characterization already assumes positive order. Found by wt-nt (MOLE). Status: minor erratum.
- F59 — Wave B2 draft (deviation ratio docstring) — identifies the deviation ratio with a least operation bound with no
  denominator condition; fails at (1, 0) (`deviation_zero_denominator_counterexample`). MOLE's cut API handles the
  zero case. **B2 drafting item** (docstring/statement precision). Found by wt-nt (MOLE).
- F60 — DH21-2 L830 (reconstruction proof) — "this does affect the result" should read "does not". Typo. Found by
  wt-nt (MOLE).
- F61 — DH21 Lemma 7.3 (L1737) vs DH21 Lemma 5.8 (proof) — Lemma 7.3 writes `+χ_∞(α)/(επiα)·I_μ`, while the proof of
  Lemma 5.8 and the landed Lean identity (`ClassJR`, JR-OPS) give `−I_μ`, and DH21 sets `ε_j = ζ_n` with no extra
  sign. Read literally, the `Z`-terms of the Prop 5.1 expansion pick up `(−1)^{|Z|}`, contradicting TARGET
  (regref1-3)'s claim that `𝒥ℬ*` does not depend on `Z` unless the per-node sign of `Ω = −2⟨k₁−k, k₃−k⟩` compensates.
  The final WKE identity is probably unaffected, but the Wave B2 per-couple bound B2.1(1) would be false with a wrong
  sign. Found by wt-orch (Task 16, audits/JR-OPS.md W2). **Status: CONFIRMED source erratum (2026-11-04).** wt-wke's
  trace (`wt-scratch/wke/F61-sign-trace.md`): the composition kernel `I_{εα}I_{μ−εα}` has `χ_∞` part
  `−χ_∞(α)/(επiα)·I_μ` (DH21 Lemma 5.8's own term II; Lean `iker_comp_decompP`; checked by hand by the orchestrator),
  so `𝒥B̃_{Q,Z} = (−1)^{|Z|}𝒥B̃_Q` (DH21 Prop 7.5 "independent of Z" is false), and the per-couple leading term of DH21
  (reducedom) / TARGET (regref1-3) L1154 needs `∏_{𝔫∈Z} (−1)/(ζ_𝔫πi)`. The Ω convention does not compensate (same
  `Ω_𝔫 = 2⟨x_𝔫,y_𝔫⟩` in (newsum1) and in `α_𝔫`). Unaffected: DH21 Props 7.8–7.10 and the main theorems (`|Z|` is
  constant on equivalence classes; the `Z ≠ ∅` classes cancel either way); TARGET (regref2-3), (regref1-5). Affected:
  TARGET's per-couple bound (regref1-1) as printed is false for dominant Q with odd |Z| terms. B2 fix (ruling,
  orchestrator): `specialWeight σ Z := ∏_{z∈Z} (−ζ_z π i)⁻¹` for couples and trees (B2-CL-11).
  F57 addendum (2026-11-04, wt-orch Task 17, audits/MOLE-prefreeze.md): the same molecule satisfies every premise of
  TARGET `disjointlem` (DH23 Lemma 4.11: connected interiors, vertex deletion) while its only applicable alternative
  (b, concatenation) fails, so Lemma 4.11's premises do not make a block connected either. B2 fix: add a
  `GroupConnected` conjunct to `IsBlock` (exact text in the audit; a one-line bridge to MOLE's definition; `IsVine`
  unchanged) and define hyper-blocks through a connected adjoint block. F59 addendum: the deviation docstring fails in
  three ℝ≥0∞ cases (a, 0), (a, ⊤), (⊤, ⊤); state operation bounds directly as `𝔄_pre ≤ ℐ · 𝔄_pos`. F58: B2's
  `propcplmol` already requires positive order; fix its docstring ("connected" is not asserted by `IsMolecule`).
- F62 — TARGET (incohproof10) L1019–L1058 (Wick factor per link) — TARGET writes a per-link factor `ε_𝔫 ∈ {1,0,−1}`,
  but `ε_ℐ` is a product over all branching nodes and the two nodes of a link carry the same `ε`, so the true per-link
  factor is `ε_𝔫² ∈ {1,0,1}` (proved: `epsDec_eq_prod_links`, LINKS scratch). Estimates unaffected; an exact
  formalization needs the square. Found by wt-torus (LINKS, E1). Status: erratum (local).
- F63 — TARGET `treelemma` (1) L2422 — "−" should be "±", and the first node has no earlier node to anchor to. Found by
  wt-torus (LINKS, E2). Status: typo/precision.
- F64 — DH23 Lemma A.4 (2) — "the interval does not depend on r" cannot hold literally; formalized as what the proof
  counts: a finite family of centres chosen per decoration and r. Found by wt-torus (LINKS, E3). Status: imprecision.
- F65 — DH21 Def 4.11 — "if 𝒬 = × then 𝒩^ch contains the root of + sign" is a slip (the trivial couple has no
  branching nodes). Found by wt-torus (LINKS, E4). Status: typo.
- F66 — Wave B2 draft `RegChain.JBtree` (`WaveB2-Regular.lean` L515–L517) vs TARGET (regref2-2) L1185 — **our statement
  bug**: the tree approximation integrates down to `s`, but `K*_𝒯(t,s,k)` does not depend on `s` once `s ≤ r` (the time
  constraint is implied by the layer bound); TARGET states (regref2-2) only for `s ∈ [r, r+1]`. So B2.1 item (2) and the
  tree half of item (3) are false when `q' < r` (Lean probe `P5.lean` on the project's own `miniTree10LG`: `K*_𝒯` constant
  in `s ≤ 1` while `app(t,s) − app(t,1) = (1−s)·c(k)` with `c(k)` independent of `L`). Fix: lower limit `max s r`
  (`X.JBchain r (max s r) t fun _ => 1`). Found by the independent B2 audit
  (`docs/campaign/orch/audits/WaveB2-independent-audit.md` F-1). Status: fix queued (B2-CL-13). The same audit reopens
  stage-2/3 R1 (self-loop halves accepted as a bond pair in the B2.3 gap hypotheses: add `x₂ ≠ M.mate x₁`) and R2
  (zero-gap tame ε-atoms, T L2183/L2152), keeps B2.3 out of the B2 freeze pending the author's ruling on DESIGN Q7, and
  requires the p.v. characterization for decaying kernels (F-5) and named instances + a B2 freeze list (F-6).
- F67 — DH23 L1924 (Prop 10.3, case (3)) — "v4 and v5 are not bridges" refers to the bonds ℓ4, ℓ5. Notation typo. Found
  by wt-ansob (MOLEPROP13). Also recorded (no erratum yet, check at the G-chain audit): DH23 Def 4.1 L633 forbids loops,
  while TARGET L1295 permits loops with a guarded large-gap convention; MOLEPROP13 proves DH23 Prop 10.1 on DH23's
  loop-free domain and claims no loop-counting extension for TARGET's use.
- F68 — Wave B snapshot 6 B1.12 `layergardenFlower`, `LayeredGarden.PatValid` (`dChild i` clause) vs TARGET L2331 —
  **our statement defect**: the clause only requires the `i`-th child of `𝔣^pr` to be a branching node, so under
  `IsCanonH (p+1)` it may be the root of an attached lower-layer garden (layer `< p`); `fixPat` then designates that
  root with time `s > p`. TARGET's `∂_s` boundary term (L2331) is taken in the single-tree kernel `𝒥^†`, where a
  non-flower child of `𝔣^pr` is a top-layer branching node or a leaf. So `flowerSum (dChild i)` contains gardens the
  moment expansion never produces, and B1.12's bound for them is not justified by TARGET. Fix (snapshot 7): add
  `LG.layer b.toNode = p` to the `dChild` clause. `dParent` is fine (the parent of `𝔣^pr` is on the stem). The
  consumer `fixedpoint` (X3) uses only `plain` and `dRoot`. Found by wt-gauss-hc (X2-HANDOFF FINDING).
- F69 — DH23 §10.4 Lemma `ylem1` (L1937–L1942) vs our B2 vine family — **open**: wt-ansob (MOLEPROP4) gives a
  kernel-checked 5-atom molecule (bonds 1→0, 1→2, 2→1, 2→0, 0→2, 0→3, 3→4, 3→4, 4→3, 4→1; 4-regular, loop-free,
  one triple bundle) whose single (Y2) step at 3, 4 gives the doubled triangle, while no vine in our B2 family has 7
  atoms (type I: 2, type II: even ≥ 6, others ≥ 9), so ylem1's conclusion fails for it
  (`/home/scott/wt-scratch/moleprop4/src/MoleProp4/ShortYCounterexample.lean`). Either our vine templates are too
  narrow (F19/F37 readings) or ylem1 misses a small case. Independent investigation commissioned
  (`/home/scott/wt-scratch/ylem1-investigation/REPORT.md`). G7 MOLEPROP4 is paused on this.
