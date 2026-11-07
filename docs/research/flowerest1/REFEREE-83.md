# Referee report 83: o83 RESOLUTION (OPEN 8.3, filtered ladders; Lemma F check; R2; R3)

Referee: independent, refute-first (wt-orch request, 2026-11-07). I did not write any of the refereed material.
Read-only elsewhere. No Lean builds, no git changes.

## 0. Pins

The draft was copied to my scratchpad at first read and hashed. I re-hashed it at the end; it had not changed.

| File | sha256 |
|---|---|
| o83/RESOLUTION.md (refereed) | `71946247…dd014` (start and end of session) |
| SUPPLEMENT-v1.md | `ddd81fe1…74d7` (matches the pin) |
| o75/RESOLUTION.md | `d7102c43…74eb8` (same as o83 cites) |
| o63/RESOLUTION.md | `a50e0f93…ebc4` (revision 2) |
| ref/REFEREE.md, ref/REFEREE-2.md | `c31ee38a…d6d`, `7ecef6b0…e45` |
| T = WKE-Longer_times_Final_arXiv.tex | `493eef6b…727cb` (matches) |
| D23 = Revision_Submit.tex | `c7e47dfa…35475` (matches) |

"T n" and "D23 n" are source lines. "R83 §x" is the refereed file.

## 1. Scope and method

I checked, line by line:
- every identity of Lemma P (R83 §4.1);
- both exponential-sum inputs (S1), (S2) against T958–977 and D23 1015–1088;
- every inequality and exponent of Lemma R, Theorem K, Lemma T and §4.6;
- the claims about o75 Lemma F (o75 §4.8), R2 (R83 §7) and R3 (R83 §8);
- the errata status of G2 and G3 against T1978–1991 and T1595–1660.

I also read the campaign's Lean ladder proof (report `Spine/`), to see whether the formalization had already run
into G2/G3.

---

## 2. Lemma P (structure of ladder decorations): correct

- **(P1).** With q₁ = p₁ − x, q₂ = p₁ − y, p₂ = p₁ − x − y, we get Γ = |x+y|² − |x|² − |y|² = 2x·y. The
  opposite-direction differences are (p₁,q₁) = x, (p₁,q₂) = y, (p₂,q₁) = −y, (p₂,q₂) = −x. Given any one momentum,
  the map is bijective. ✓
- **(P3).** I recomputed with Γ_v = Σ ζ_{v,ℓ}|k_ℓ|² (T1308) and ζ_{w_j,·} = −ζ_{v_j,·} on all four bonds. This
  sign rule is right: the double bond is reversed at its other end, and parallel rails have opposite directions
  (T1384: "each pair of two parallel single bonds must have opposite directions").
  - Adding the two conservation laws gives ζ_{c_{j−1}}r_{j−1} + ζ_{c_j}r_j = 0.
  - Adding Γ_{v_j} + Γ_{w_j} gives 2ρ_j·(c_j − c_{j−1}) + κ_j with κ_j = −(ζ_{c_j} + ζ_{c_{j−1}})|r|² ∈ {0, ±2|r|²}. ✓
- **(P4).** With both end double bonds fixed, all bonds at the four end atoms are fixed. I counted directly:
  4m+2 bonds and 2m+2 conservation laws of rank 2m+1 give 2m+1 free vectors. That equals 4 + 2(m−1) − 1, so
  there is exactly one d-dimensional constraint, (4.2).
  - For 1 ≤ j ≤ m−1, setting d_j := c_j − r_j makes conservation at w_j automatic.
  - At j = m−1 the two determinations of d_{m−1} give a condition on the end data alone. ✓
- **(P5).** ε (T556–558, `defepscoef` T646) is a sum of indicators of equalities of opposite-direction pairs. This
  follows from T1297's direction rule: children of sign ζ_n and −ζ_n lie on opposite sides.
  - At w_j the direction pattern is the exact reverse of v_j's, so the pair differences become z + θr with
    θ ∈ {0, ±1, ±2}.
  - K₀ = 9·2⁸ = 2304 is a valid bound on the coefficient mass. The constant term has coefficient ≤ 1: it is 0 as
    soon as one 𝒵 is of SG/ZG type. ✓
  - *Editorial.* "At most four 𝒵-indicators per atom" is asserted without a reason. One is available: 𝒵 encodes
    SG/LG/ZG of the vine-like objects of the collection 𝒞 (T1944, T1970). Those are disjoint atomic groups (Lemma
    `vinechainlem`), and each gap is read at one joint, so an atom carries O(1) such indicators. Only an absolute
    bound is needed for K₀.

## 3. Lemma S: correct

- **(S1)/(G5).** By Poisson summation on ℤ_L^d = (L⁻¹ℤ)^d, Σ₀ is L^{2d} times the lattice sum of `lemlayer1`
  (T958–968). That proof uses only the support radius and smoothness of the cutoff.
  - With radius 4, the case split is at 40dL, and case (ii) has ≤ (80d+1)^{2d} terms.
  - In case (ii) the integral is ≤ C⟨s⟩^{−d}: integrate in y first, which leaves x confined to a set of measure
    O(|s|^{−d}).
  - In case (i) the decay is L^{−N} ≤ ⟨s⟩^{−d} for |s| ≤ L. ✓
- **(S2)/(G4).** D23 Lemma 6.6(2) (D23 1076–1088) requires sup_{s,x,y}|∂_x^α∂_y^βΦ| ≤ D for |α|,|β| ≤ 10d
  (NTphibounds, D23 1015) and support in |s| ≳ L.
  - Φ = 1_{|s|≥L}φ(x−a)φ(y−b) qualifies with D = C_φ. The proof (D23 1092–1135) differentiates only in (u,v); s
    enters through supports.
  - λ = 8 and χ₀((x−a)/8) = 1 on supp φ(·−a) are as stated, and P_η = ⌈η^{−2}⌉ + 1 > η^{−2}.
  - The window extension with ⟨D+2⟩^{P_η} is immediate.
  - G4 is not really a gap: T's own "≲₂" at T976 already records the dependence on the window. ✓

## 4. Lemma R (one rung, arbitrary unit intervals; G1 + G2): correct

- **Step 0.** The substitution t_v = t_w − s/(δL^{2γ}) is right, and E_s = J ∩ (I + s/(δL^{2γ})).
  - (I+Δ)∖I is an interval of length ≤ min(|Δ|,|I|), so |J ∩ (I+Δ)| ≤ |J ∩ I| + |Δ|. This is (B3) for *arbitrary*
    intervals.
  - (B2): E_s = ∅ for |s| > δL^{2γ}(D+2). ✓
- **Step 1.**
  - *Region |s| ≤ L:* ∫⟨s⟩^{−d}min{1, |I∩J| + |s|/(δL^{2γ})} ≤ min{c₀, c₀|I∩J| + c₁(δL^{2γ})^{−1}}, with
    c₁ < ∞ because d ≥ 3.
  - *Region L < |s| ≤ S:* Fubini over E_s ⊂ J, then (S2) with ⟨s/(δL^{2γ})⟩^{−P_η} ≥ ⟨D+2⟩^{−P_η}.
  - *Absorption:* 2γ > 1 ≥ γ₁, and −2(d−1)(1−γ) + η ≤ −γ₁ + η < −(γ₁ − √η). Both thresholds are C₂-type. ✓
- **Step 2(a)** (only x-type balls). This is the heart of G2, and I re-derived it.
  - After the modulus is taken inside the x-sum, positivity lets all but one indicator be dropped.
  - Poisson in y gives |Σ_y| ≤ CL^d·φ̃(w_i), with φ̃(u) = Σ_g⟨Lg−u⟩^{−2}. This uses ⟨z⟩^{2d} ≥ ∏_k⟨z_k⟩².
    φ̃ is L-periodic with period integral π.
  - Any interval of length λ satisfies ∫φ̃ ≤ π(λ/L + 1): split it into ⌊λ/L⌋ full periods plus a remainder, and
    note that the remainder sits inside one period.
  - So the s-integral over J′(t_w), which has length δL^{2γ}, is ≤ π(δL^{2γ}/L + 1/|x_i|).
  - The counting bounds #B ≤ C(1+Lρ)^d and Σ_{B∖0}|x|^{−1} ≤ C(L^dρ^{d−1} + L) hold in all regimes, including
    ρ = 0 and Lρ < 1.
  - The four relative sizes are δL^{−(d−2γ)}, 2^dδL^{−1−(d−2)γ+dη}, L^{−(d−1)(γ−η)} and L^{1−d}. Each is
    O(L^{−min(1, 2γ−2η)}), and min(1, 2γ−2η) > γ₁ − √η strictly. ✓
  - *Editorial:* the text says each term is "at most L^{−min(…)}". The second term carries a 2^d, which the strict
    margin absorbs.
- **Step 2(b)** (only y-type) is the mirror image, using the phase ⟨x, ξ + sy⟩. ✓
- **Step 2(c)** (both types): the relative size δL^{−2(d−1)γ+2dη} is far below the target. ✓
- **The trivial bound** C_dL^{2d}: |W| ≤ 1, because ε ∈ {−1,0,1} and 𝒵 ∈ {0,1}. ✓

**Is Step 2 necessary?** Yes, at least as a matter of proof. A trivial count on an incoherent rung carrying an
SG ball on x costs L^d·(L^{1−γ+η})^d. Relative to the incoherent budget δ^{−1}L^{2d−2γ−(γ₁−√η)}, that is
δL^{γ₁−(d−2)γ+dη−√η}, which **exceeds 1 for d = 3 and ½ < γ < 4/5** (γ₁ = 1 for γ ≤ ¾, and γ₁ = 4(1−γ) > γ for
γ < 4/5). For ε-type point conditions the trivial count is harmless: L^d against that budget is
δL^{−(d−2γ−γ₁)+√η}, and d − 2γ > 1 ≥ γ₁.

## 5. Theorem K (box-robust core; G3): correct

- **Localization before Fourier expansion.** The bumps are inserted while the bond factors still enforce the
  support, and the Fourier inversion of 𝒦_ℓ is a pointwise identity. So the bumps survive the expansion. ✓
- **Interior bonds are affine in the rung variables, with coefficients 0, ±1.** c_j = c₀ + Σ_{i≤j}λ_i,
  d_j = c_j − r_j, and a_j, b_j come from (P1) given c_{j−1}. Counting 4m−6 interior bonds plus 8 end bonds gives
  4m+2. ✓ Also ‖𝒦̂‖₁ ≤ C_dA follows from d+1 derivatives and unit support.
- **Character average.** z := Σλ_j − (c_{m−1} − c₀) ∈ ℤ_L^d with |Lz_i| < N for N ≳ mL. Then
  N^{−d}Σ_{ζ∈[0,N)^d} e(ζ·Lz/N) = 1[z=0]. That is a mixture of linear modulations of mass exactly 1. ✓
- **Factorization.** For fixed (ν, ζ, t), each factor depends only on (x_j, y_j): the ε𝒵 weight, the bumps, the
  bilinear phase, and the linear modulations, which include −δL^{2γ}t_{w_j}⟨ρ_j, λ_j⟩.
  - The box is a product, so ∫∏_j|Σ_j| = ∏_j 𝔐_j.
  - Lemma R is uniform in the modulations, so taking the sup over (ν, ζ) inside each factor is legitimate. ✓
- **End rungs.** Every bond at v₀, w₀, v_m, w_m is end data. So their ε, 𝒵, 𝒦, filters and phases are constants
  of the interior sum. Degree-3 (root or root-paired) end atoms are only counted. ✓

## 6. Lemma T and §4.6 (filters as translations; integration): correct

- **Lemma T.** τ_v = 2ζ_𝔫ξ/(δL^{2γ}R_v) reproduces e^{2πiξζ_𝔫(−Γ_v)/R_v} exactly. The correction e^{−πiξ_vτ_v} is
  unimodular and independent of the decoration. Minkowski applies: the sum is finite and ψ̂ ∈ L¹. ✓
  - *Remark (not an error):* the restriction "Γ⁰_v = 0, interior atoms" is unnecessary. T's phase (T1968) contains
    −Γ_v + Γ⁰_v, so the translation identity holds at every atom, as o75's own Step 1 shows. o83 bounds end filters
    by ‖ψ‖_∞ instead, which is also fine.
- **§4.6.** The ξ-integral factorizes, because (4.4) is a product of rung factors each depending only on
  (ξ_{v_j}, ξ_{w_j}).
  - *Good frequencies:* |τ| ≤ ½, so the translated intervals lie in [−1, D+1]. The overlap
    |(I_v+τ_v) ∩ (I_w+τ_w)| ≤ |I_v∩I_w| + |τ_v − τ_w|.
  - *Tail:* ∫_{|ξ|>X}|ψ̂| ≤ X^{−2}𝔟, and the ratio of the tail to the incoherent rung is
    32C_dδ^{−1}L^{−2γ+γ₁−√η} ≤ 32C_dδ^{−1}L^{−(2γ−1)}.
  - Two moments are genuinely needed for R_v ≥ 1. One moment would give X^{−1}L^{2d} ≈ δ^{−1}L^{2d−2γ}, with no
    gain. So 𝔟 with (1+|ξ|)² is the right cost, and L₀ is independent of ψ. ✓
- **Assembly.** I re-checked the exponents.
  - δ-power: (2m+2) − (m−1) = m+3.
  - L-power: −(2m+2)(d−γ) + 4d + 2(m−1)(d−γ) = 4γ.
  - Losing ≤ 2 end-rung units costs L^{2(γ₁−√η)} ≤ L².
  - So (2.2) holds with C₃ = 2C₅.
  - (2.3): the ordered domain at fixed outside times is contained in 𝔅, and the normalization factor is 2L^{d−γ}/δ. ✓

## 7. Corollary 8.3.A and the budget claims: correct

- **(1) finalsbest1.** Filters at ladder atoms depend only on internal and boundary bonds of that ladder. Atoms
  outside 𝕃 have no internal bond of 𝕃. So E5's locality, fibre factorization and gluing are untouched.
  - In the gluing I checked the normalization split (2m+2 per ladder, m′ for the rest) and the trivial count of the
    rest: ≤ 4m′ + 2q′ bonds at L^d each.
  - The total is ≤ L^{20d(m′+q′)}. ✓
- **(2) finalsbest2.** Filters belong to the absolute decoration factor of (redvine5) (T2090–2097, S Lemma 9.4). ✓
- **(3) Interpolation.** θ/2 − 10ν(1−θ) = 10ν gives θ = 40ν/(1+20ν).
  - The filter factor is (∏𝔟)^θ(∏‖ψ‖_∞)^{1−θ} ≤ 𝔟_*^{θ n_sb}, so C₁ becomes C₁𝔟_*^θ.
  - Products of several filters at one atom would also be fine: 𝔟 is submultiplicative and does not increase
    under the dilations u ↦ cu, c ≤ 1. ✓
- **Incoherency gains survive.**
  - Interior incoherent rungs keep L^{−(γ₁−√η)}. The translation overlap only multiplies it by 1+|ξ_v|+|ξ_w|,
    which is integrated into 𝔟.
  - The ≤ 2 end-rung units are paid by the L² inside L^{4γ+2}. T's sketch also counts the last double bond
    trivially, so it loses at least as much.
  - In (finalsbest1) the per-ladder L² sits inside L^{80d(ρ_sb+q_sk)}, and L^{−ηg_sb} is retained in full. ✓
- **L^{4γ+2} per ladder ⊂ L^{20d}.** Yes.
  - It is < L⁶ in the core normalization, and L^{d+3γ+2} in T's 2m+1 form.
  - In (finalsbest1) it is part of L^{80d(ρ_sb+q_sk)}. After interpolation that becomes
    L^{80dθ(ρ+q)} ≪ L^{η⁶(1−θ)(ρ+q)/2} (T's choice of ν). It never enters L^{(100d)³P}.
  - For T2297(4)'s direct uses, the filter cost 𝔟_*^{2m+2} ≤ (𝔟_*⁴)^m is absorbed by enlarging C₁ by an absolute
    factor.
  - *Editorial:* R83 §5.1, last bullet, says "absorbed by (C₁δ)^m for δ small". The absorption is by an absolute
    enlargement of C₁, not by smallness of δ. The conclusion is unaffected.

## 8. §6: check of o75 Lemma F: concur (VERIFIED, given G1–G5)

- **Step 1 of Lemma F (o75 §4.8)** is exactly right, including at atoms with Γ⁰ ≠ 0. The double use of the symbol
  ξ is harmless.
- **"The box enters only through (B1)–(B3)."** True of Lemma R:
  - Step 1 uses (B1)–(B3);
  - Steps 2(a)–(c) and the end rungs use (B1) only.
- **Translation commutes with the E5 repair.** The modulus sits inside the time integral, there is no ordering, and
  locality is unchanged. ✓
- **Lemma F's own constants are fine for R_v ≥ L/2.**
  - Its good region gives |τ| ≤ 4(δL^{2γ})^{−1}.
  - Its tail uses Schwartz decay C_NL^{−N} of ϑ̂, so L₀ = L₀(ϑ). This is acceptable for the fixed ϑ.
- **Lemma F is incomplete in exactly the places R83 lists:**
  - its Step 0 inherits T's sketch for ε/𝒵 (G2) and for the last rung (G3);
  - it cites `lemlayer2` outside its window (G4);
  - its "(B3) with λ_vw" for translated boxes is not an instance of the Lean layer-box gate (G1; o75's own Audit
    note A).
- With Lemma R and Theorem K, Audit note A is discharged. The Lean `ladderL1Gate` (report
  `Spine/LadderL1Gate.lean` L15–33) is indeed stated for `timeBox` only. Its rung lemma `RungOK` (report
  `Spine/RungTotal.lean`) takes arbitrary unit intervals, but it states the gain only for disjoint intervals, not
  with the overlap term. So R83's note N1 is accurate.

## 9. R2 (frontier M₁ cutoffs on Stage-2 ladder bonds): correct

- S Lemma 3.2 expands each shell into products of χ(k_v/R), R ∈ {M, M/2}, with one factor per frontier vertex.
- Frontier vertices are indexed by original trees (S §2), so each vertex carries at most one cutoff.
- A bond of 𝕄_sb carries the momentum of one node (PC) or of two paired leaves (LP). The momentum of a regular
  object's root or lone leaf equals the bond momentum (T1235–1244). Hence there are ≤ 2 cutoffs per bond.
- Leibniz with R ≥ 1 gives the C^{30d} bound c_χ per factor, so A ≤ c_χ². Theorem 8.3 carries A^{4m+2}. ✓
- 𝒦† involves only hinge bonds (T1970), so the hypothesis of T2081 is untouched. ✓
- Cutoffs strictly inside spliced vines belong to S Lemma 5.3. They are the separately recorded erratum E37
  (report ERRATA L1921–1953) and are not R2's business.

## 10. R3 (positions of stem vertices): PASS AFTER FIX (one sentence)

- **The table is exhaustive**, and cases (a) and (c1)–(c3) are right.
- **The high-root hypothesis is verified.** The frozen clause reads
  `∀ j₂ ∈ cut2, ∃ j₁ ∈ cut1, ((2^{j₁}L))^{10} ≤ ‖n/L‖` at main `FlowerTop/CaseAssembly.lean` **L47**; R83 says
  L48, but its dependency row says L44–49. The same hypothesis appears in `Cut2EB/Target.lean` L43. So
  |k| < M₁^{10} never meets an M₂ filter. The bottom case cut2 = some 0 carries all the stem filters
  (V_{j,L} = U_{j,L}), and it is covered too. ✓
- **Case (b) needs one more sentence.**
  - The dichotomy of T2300(7) and S Lemma 9.2 is "the flower descends from 𝔲₁₁, else from 𝔲₂₁ or 𝔲₂₂". It presumes
    that the flower is not itself inside the realization 𝒢_sk[𝕌]∖{𝔲₁}.
  - That case is excluded, but by the marking, not by Lemma 9.2:
    - spliced chains are unmarked, i.e. 𝐀(𝕍) ∩ Π = ∅ (o75 Definition 2.3, Lemma 2(d));
    - Π contains 𝔣_j and 𝔣_j^pr (o75 (Π1));
    - in T's own scheme, vines containing special nodes are not spliced (T2297(4); cf. E31).
  - **Fix:** in row (b), insert "a spliced SG chain is unmarked, so its realization contains no special node, in
    particular not 𝔣_j or 𝔣_j^pr; hence, if the flower descends from 𝔲₁, it descends from one of 𝔲₁₁, 𝔲₂₁, 𝔲₂₂,
    and Lemma 9.2 excludes 𝔲₂₁, 𝔲₂₂."
  - The conclusion n = 𝔲₁ then follows. 𝔲₁₁ is outside the realization: its time does not enter 𝒦^𝕌 (T1946–1950).
- **Twist invariance.** Filters at atoms of 𝕄_sb are common to each V₀ twist class (o75 Lemma 2(d)). Corollary
  8.3.A's per-class form is therefore legitimate. ✓

## 11. Refutation attempts that failed

1. *Degenerate constraint (4.2).* For example m = 2, where λ₁(x₁,y₁) is fixed. The character average still gives
   an upper bound, losing only the L^{−d} that the constraint would have saved.
2. *Translation leaving the (S2) window.* This is handled by the good/tail split at |ξ| = δL^{2γ}/4.
3. *A ball term whose ball contains x = 0.* The x = 0 term is bounded separately by CL^d.
4. *Overlap growth on adjacent layers.* The overlap is ≤ |τ_v| + |τ_w|, which is linear in |ξ|, and the cost is
   integrable against (1+|ξ|)²|ψ̂|.
5. *End-rung indicators coupling all rungs.* In R83's parametrization they don't: both end double bonds are fixed.
   They would couple in the "one end fixed" ordering (see §12).
6. *Ordering gains lost by dropping the order.* `ladderl1new` uses no ordering gain, unlike `sumint` case (a), and
   E5 already drops the order.
7. *Dependence of L₀ on ψ, m, F or boundary data.* There is none. Every ψ-dependence is multiplicative through 𝔟.
8. *Mixed-scale products at one atom (shell differences).* 𝔟 is submultiplicative and stable under contracting
   dilations.

## 12. Errata verdict on G2 and G3 (T1989–1991 as printed)

Both are **genuine gaps in the printed sketch**. Neither is a false statement: `ladderl1new` is true as stated. I
recommend **one CANDIDATE erratum, class EXPOSITION**, "TARGET `ladderl1new` proof, L1989–1991", with two items,
cross-referenced to E4 and E5.

- **G2 (ε_v, 𝒵_v in the rung sums).**
  - K^𝕃 carries ∏_{v∈𝕃}ε_v𝒵_v (T1983). The sketch says "exactly the same thing" as `sumint` Step 2 (T1627–1660),
    whose weights are smooth with 𝔖^{30d,30d} bounds. An indicator is not such a weight; this is E4's observation.
    The sketch never mentions ε or 𝒵.
  - *ε part:* routine, either by the mass-one character mixture (E4) or by a per-rung trivial count, once the rungs
    factor.
  - *𝒵 part:* it needs a real argument, R83 Lemma R Step 2(a), **if** a ball indicator constrains an internal
    opposite pair of an incoherent interior rung. The trivial count fails for d = 3, ½ < γ < 4/5 (§4 above).
  - R83 does not show that T's 𝒵 ever lands there. In T, 𝒵 records SG/LG/ZG of the vine-like objects of 𝒞 at a
    joint (T1938–1944, T1970), and from the vine shapes I do not see a joint occurring as an interior ladder atom.
    So the erratum should say that the 𝒵 half is "needed for the general weight class; occurrence in T not
    established".
  - The campaign's Lean model allows an arbitrary gap specification at every ladder atom (report
    `Spine/SourceLocalLadder.lean` L33) and proves the rung bound for the kinds F/X/Y/Z (report
    `Spine/RungTotal.lean` L17, `Spine/Kinds.lean` L62). That is the same fill as Lemma R, and the formalization
    already needed it. It is not yet recorded in the errata file.
- **G3 (the "last remaining sum").**
  - T introduces (x_j, y_j)_{1≤j≤m} plus the last double bond, i.e. 2m+2 vector variables. A ladder with its four
    boundary momenta fixed has only 2m+1 free vectors (§2, (P4)). So one d-dimensional linear relation couples the
    rungs, and the rung-by-rung factorization of `sumint` Step 2 does not literally apply.
  - Fixing only one end double bond outermost does not cure this. The far boundary momentum still constrains, and
    the far end rung's phases and ε/𝒵 then depend on Σλ_j.
  - *Fill:* fix both end double bonds (cost L^{4d}, inside L^{20d}) and resolve the single constraint by a mass-one
    character average (R83 Theorem K step 4). The Lean proof uses the same chart, with the flux identity at report
    `Spine/FibreSum.lean` L17.
  - Sub-item: T1989's formula Γ_w = −2x·y + 2r·ζ is claimed for every indexed rung. At an end rung containing a
    degree-3 atom (T1308, (molegammav)) it can fail. This is harmless once end rungs are only counted.

## 13. Verdict table

| Item | Verdict | Fix / note |
|---|---|---|
| Theorem 8.3 ((2.2), (2.3)) | **PASS** | Editorial: Lemma T's "Γ⁰ = 0" restriction is unnecessary; "at most L^{−min(…)}" should carry the 2^d |
| Corollary 8.3.A (1)–(4) | **PASS** | Editorial (R83 §5.1): the 𝔟_*^{2m+2} cost is absorbed by an absolute enlargement of C₁, not by δ small |
| §6 check of o75 Lemma F | **PASS** (concur: VERIFIED once G1–G5 are filled) | Lemma F's Step 1 also holds at Γ⁰ ≠ 0; its R_v ≥ L/2 version needs L₀(ϑ), which is fine |
| G1 box-robust core with overlap term (Lemma R Step 0–1, Theorem K) | **PASS** | — |
| G2 gap-indicator lemma (Lemma R Step 2) | **PASS** | Editorial: justify "≤ 4 𝒵-indicators per atom" (any absolute bound suffices) |
| G3 end-rung character average (Theorem K step 4) | **PASS** | — |
| G4 enlarged `lemlayer2` window | **PASS** (trivial; T976's ≲₂ already records the window) | — |
| G5 `lemlayer1` with radius-4 bump | **PASS** (trivial) | — |
| Incoherency gains retained | **PASS** | End-rung units are paid by L², as T's sketch implicitly does |
| L^{4γ+2} per ladder absorbed in T's L^{20d} | **PASS** | Also L^{d+3γ+2} in T's normalization; inside L^{80d(ρ+q)} and never in L^{(100d)³P} |
| R2 frontier cutoffs on ladder bonds | **PASS** | — |
| R3 coverage of stem positions | **PASS AFTER FIX** | Row (b): add that spliced SG chains are unmarked (o75 Def 2.3, Lemma 2(d)), so the flower is not inside the realization; only then does T2300(7)/S Lemma 9.2 give n = 𝔲₁. Line nit: CaseAssembly hypothesis is at L47 |
| Errata: G2 | **Genuine gap in the sketch (EXPOSITION)** | ε half routine; 𝒵 half needed for the general weight class, occurrence in T not established; Lean already fills it (RungTotal kinds X/Y) |
| Errata: G3 | **Genuine gap in the sketch (EXPOSITION)** | 2m+2 variables against 2m+1 degrees of freedom; fill as in Theorem K or the Lean chart/flux |

**No FAIL.** OPEN 8.3 is closed as stated in R83 §2. The only substantive fix is the one-sentence citation in R3 (b).

STATUS: REFEREED — 0 FAIL; 1 PASS AFTER FIX (R3 row (b), citation); all other items PASS; G2/G3 are genuine EXPOSITION
errata in T1989–1991 (record as one CANDIDATE erratum, cross-reference E4/E5).
