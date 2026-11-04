<!--
DRAFT FOR SCOTT. NOT SENT. Remove this block before sending.
Sources: docs/review/ESCALATION-F69b.md; docs/research/{ylem1-investigation.md, dh23-prop96-case4.md,
dh23-prop96-referee.txt, kqmainest1-necklace.txt, vine2-m1.txt, case4-gamma-above-half.txt,
case4-gamma-above-half-referee.txt}, as on main 03666e7.
Line numbers: arXiv:2301.07063 TeX source `Revision_Submit.tex`; arXiv:2311.10082v2 TeX source
`WKE-Longer_times_Final_arXiv.tex`.
Scripts and checks can be attached on request.
-->

**To:** Yu Deng, Zaher Hani
**From:** Scott Armstrong
**Subject:** Prop. 9.6 of arXiv:2301.07063 for γ ≤ 1/2, and a few related points

Dear Yu and Zaher,

We are writing a complete Lean formalization of your long-time paper, arXiv:2311.10082 ([L] below). Its counting core
uses Proposition 9.6 of arXiv:2301.07063 ([D] below) as a black box ([L] L2192–L2197). Working through [D] §§9–10 in
detail, we ran into the points below. We would be grateful for your view, especially on the questions at the end.
Line numbers refer to the arXiv TeX sources.

**1. Lemma `ylem1` ([D] L1937) and the enumeration at L1885.** Write Q for the quadruple bond and T for the triangle
of three double bonds.
- **Omissions in `ylem1`.** If 𝕄′ (Q or T) is obtained from 𝕄 by at most two (Y) sequences, an exhaustive inverse
  enumeration finds 𝕄 outside the closures of vines (II)–(VIII) in these cases:
  - Q and T themselves (zero sequences);
  - the 5-atom T₁ = {a₁≡b₁, a₁–e, b₁–f, e–f, e=g, f=g} (one sequence of length 1, which L1929 allows);
  - two infinite families with two triple bonds, coming from the bullet at L1946 when the rail is next to the triple
    bond or next to the triangle. The smallest has 7 atoms:
    `1→0, 1→2, 2→1, 2→0, 0→2, 0→5, 5→6, 5→6, 6→5, 6→3, 3→4, 3→4, 4→3, 4→1`.
- **The lemma's use.** It is used only for Prop. 10.4(2) (L1961). There one can assume instead that no (Y)-reduction
  of 𝕄 ends in Q or T. The issue then moves to Prop. 9.6 case (4).
- **The enumeration at L1885.** "An enumeration shows that 𝕄₀ must be a vine" fails even among small blocks. A 9-atom
  example with β-atoms 7, 8 is `e=g, f=g, e–a₂, f–b₂, e–7, f–7, a₁–a₂, a₁=b₁, a₁–8, b₁–8, a₂=b₂, b₁–b₂`. It has no
  triple bond and no cut vertex, and it is not a vine.
- **What still works.** When the β-gap is large (|r| > L^{−γ+η}), your argument at L1885 goes through without using
  the vine shape. The difficulty is the small-gap components.

**2. A counterexample for 0 < γ ≤ 1/2: the necklace N_m.**
- **The molecule.** Take joints w₀, …, w_m.
  - A *T-bead* B_i between a = w_{i−1} and b = w_i has atoms e, g, f and bonds a→e, b→e, e→g (×2), g→f (×2), f→a,
    f→b.
  - An odd bead B₀ between w_m and w₀ has atoms o₁, o₂ and bonds w_m→o₁, w₀→o₁, o₁→o₂, o₂→w_m, o₂→w₀.
  - N_m has 4m+3 atoms, 8m+5 bonds and no triple bond.
  - It is the molecule of an explicit prime, non-degenerate couple. In [L] this couple is a canonical couple with all
    nodes in layer 0.
- **No vine-like objects.** The blocks of N_m are exactly the runs B_i ∪ … ∪ B_j. There are no hyper-blocks, and no
  block is a vine of any type with any number of rungs. So 𝒬_sub = 𝒬_sk.
- **The decorations.** Make every joint small-gap, with gap ±r, r = e₁/L and label R = L^{−1} (allowed by L1752).
  Make every other atom large-gap.
- **The cutting algorithm.**
  - Steps 1, 2 and 4 do nothing.
  - In every order of Step 3, the first cut is an α-cut and all later cuts are β-cuts.
  - For m ≥ 3, some T-bead is a component with V_α = 0, V_β = 2, i.e. in case (4).
- **The count.** On such a bead, γ ≤ 1/2 gives |r| = L^{−1} ≤ δ^{−1}L^{−2γ}. So both β-atom constraints hold
  automatically. Lemma A.2(1) gives no gain in this range, consistently with the remark at L579 that the triangle T
  has 𝔄 ≈ 1. A pigeonhole argument gives 𝔄₀ ≥ c_d(C⁺)^{−4}, independent of L, whereas (finalcount) (L1820) needs
  𝔄₀ ≲ L^{−η²−η⁵ρ₀}.
- **Consequences**, for 0 < γ ≤ 1/2 and η small:
  - [D] Prop. 9.6 (L1818–L1822) and its restatement [L] L2192–L2197 fail, already on N₃.
  - [D] Prop. `kqmainest2` (L1681–L1690) fails.
    - Given r the beads are independent, and 𝔠(N_m) ≥ [c δ^{−2} L^{4(d−γ)}]^m.
    - The ratio to the right side is ≳ L^{η⁶ρ − 3(d−γ)} with ρ ≥ m+3. So it fails once η⁶(m+3) > 3(d−γ).
  - [L] (finalcount1) (L2110–L2114) with R = 1 fails once 4η⁶(5m+4) > 3(d−γ). Here ρ_sb = 4m+3 and p_sb = m+1.
  - **The analytic bounds, with less certainty.** We computed the leading asymptotics of 𝒦_𝒬(t,t,k) for these couples:
    ζ(𝒬)2^{−n}δ^{2m+2−d}L^{−γ(2d−1)}(A_m + o(1)), with A_m ≠ 0 for an explicit admissible n_in. The time
    integrals give no gain per bead.
    - Hence [D] `kqmainest1` (L1632–L1640) with the ρ = ρ_sub of its proof (L1692) fails once
      η⁷(3m+3) > γ(2d−1), and [L] (finalsbest2) (L2078) fails once η⁶(4m+3) > γ(2d−1).
    - We regard this as established with high confidence, but it is not a complete proof.
    - `kqmainest1` as literally stated, existential in ρ, is not refuted.
- **What we do not claim.** These couples are few (C^n per order), and their total contribution is heuristically
  C^n L^{−γ(2d−1)}. We are not claiming that any main theorem is false. The chain of intermediate statements is what
  fails.

**3. What we can prove.**
- **Vine (II) with one double bond.** Your parametrization of vine (II) (L1421) and the remark "m ≥ 1 for vines (II)"
  (L1481) cover the 4-atom block w₁–{s=t}–w₂.
  - We checked that every vine estimate and the twist cancellation go through at m = 1:
    - all 1152 placements fall into scenarios (II-a)–(II-e);
    - Step 3 of Prop. 7.5 closes with a margin of 3η;
    - `sumintest1` (L1280) is stated for m ≥ 1.
  - With this reading, the Q-type exceptions of §1 are exactly the vines (II) with m ≥ 1.
  - Without it, necklaces of such Q-beads break the statements of §2 for all γ < 2/3. The loss is L^{(2−3γ)m}
    for 1/2 < γ < 2/3 and L^{γm} for γ ≤ 1/2.
- **Case (4) closes for 1/2 < γ < 1** (η ≪_{d,γ} 1, as at L438 and L2076).
  - **Claim.** Every case-(4) component whose closure reduces to T satisfies 𝔄₀ ≲ (C⁺)^{−4}δ^{−1}(log L)^C L^{−10η},
    uniformly in the gap.
  - **The argument.**
    1. Apply operation (c) to the first β-chain. Lemma A.3(1) costs L^{γ₀}, up to powers of δ and log L, using only |r| ≥ 1/L.
    2. Apply operation (d) to the second chain.
    3. Follow the (Y)-route to T with `ylem2`, carrying the missing bond.
    4. Remove the two now-adjacent degree-3 atoms of "T minus one bond". This is a system {(1,2,3),(1,4,5)}, which
       Lemma A.3(4) counts with the γ > 1/2 branch of Lemma A.2(3) (L2064–L2068). That branch gives
       L^{−γ₀−10η}, exactly L^{−10η} better than step 1 costs.
  - **The branch of Lemma A.2(3).** We proved the γ > 1/2 branch (sketched at L2088–L2091) from three inputs: the
    bilinear count, Lemma A.1(2), and a thin-annulus lattice bound (Lemma A.1(1); the van der Corput exponent
    suffices). The saving is κ(γ) = min((2γ−1)/3, 1−γ), up to (log L)^C, and κ(γ) ≥ 20η.
  - **Sharpness.** At γ ≤ 1/2 the same chain of bounds holds with 10η replaced by 0. The necklace shows this is sharp.
    The threshold 1/2 is exactly the branch point of Lemma A.2(3).

**4. Questions.**
1. Do you know a repair for 0 < γ ≤ 1/2? For example, small-gap chains of T-type blocks could be treated in stage 1
   like vine chains. As far as we can see, that would need a Prop. 7.6-type estimate for such blocks and a time bound
   without the log L loss per atom outside ladders.
2. Do you believe the main theorem of [L] (L314), and that of [D], hold for γ ≤ 1/2, including the case γ = 1/2
   singled out at [L] L325?
3. Was vine (II) meant to include the one-double-bond case m = 1, as your Prop. 7.5 suggests?

All of this has been checked by independent recomputation and by finite enumerations. We are happy to send the
details, scripts and figures.

With best regards,
Scott Armstrong
