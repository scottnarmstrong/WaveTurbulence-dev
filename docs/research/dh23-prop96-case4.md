# DH23 Prop 9.6, case (4): the small-gap components (F69b)

Date: 2026-11-04. Scope: FINDINGS.md F69b; investigation report `docs/research/ylem1-investigation.md`, item R3.

Sources and line numbers:
- **DH23** is `wave-turbulence/references/src-2301.07063/Revision_Submit.tex`.
- **TARGET** is `wave-turbulence/paper/source/WKE-Longer_times_Final_arXiv.tex`.

Scripts and their outputs are in this directory (Section 7). No Lean was compiled.

## 0. Summary and verdict

**Verdict: the gap cannot be closed as stated.** For 0 < γ ≤ 1/2 the estimate R3 is false.

R3 asks for 𝔄₀ ≲ L^{−η²−η⁵ρ₀} for every component 𝕄₀ with V_α = 0, V_β = 2 whose reduction 𝕄₁ is Y-exceptional. Since it fails, so do:
- DH23 Prop 9.6 (`lgmolect`, L1818–L1822);
- TARGET's restatement of it for perfect components (TARGET L2192–L2197).

The failure is not local to case (4):
- DH23 `kqmainest2` (L1681–L1690), which Prop 9.6 is used to prove (L1823–L1826), is itself false for γ ≤ 1/2, on molecules of fixed size.
- So is TARGET (finalcount1) (L2114) for R = 1.

So no rearrangement of the stage-2 bookkeeping (Steps 1–4 together with per-component bounds) can prove these statements. The missing ingredient is a new class of small-gap blocks, the **T-type blocks**:
- They are neutral for counting, exactly like the normal vines (III)–(VIII).
- They are not in DH23's vine list.
- They must be handled in stage 1, as vine chains are.

That is the extra input (Section 6).

Findings, each proved or checked below:

1. **Large gap: closed (Lemma 2.4).** If the β-gap satisfies |r| > L^{−γ+η}, the source argument works and the vine shape is never used. This includes every 𝕄₀ with a β-atom from a Step-4 cut (Lemma 2.2).
   - One printed bound must be read in its sharp form: (operc) at L1862 must be read as L^{γ−1} + δ^{−1}min(R^{−1}L^{−γ}, L^{γ}), which is the form Lemma A.3(1) gives.
   - It is closed for γ ≤ 1 − 2η. At γ = 1 (generic tori) the L^{γ−1} term gives no gain, so that endpoint is flagged.
2. **Counterexample for γ ≤ 1/2 (Prop 4.3).** The 5-atom **T-bead** is the triangle of double bonds with both copies of one double bond subdivided by the β-atoms. In parallel orientation its edges are b→e, b′→e, e⇉g, g⇉f, f→b, f→b′.
   - It occurs as a case-(4) component of 𝕄_fin for an explicit prime, non-degenerate couple (the necklace N₃). This happens in every Step-3 order.
   - With β-gap r = e₁/L its count satisfies 𝔄₀ ≥ c_d (C⁺)^{−4}, a constant independent of L.
   - Case (4) requires 𝔄₀ ≲ L^{−η²}.
3. **Global failure (Prop 4.4).** On the necklace N_m with m = ⌈(3d+1)η^{−6}⌉ T-beads and all joints small-gap:
   - the count exceeds the right side of `kqmainest2` by a factor ≳ L;
   - each T-bead contributes a factor of order 1, where `kqmainest2` needs L^{−η⁶} per bead.

   Heuristically these couples contribute O(L^{γ−d}C^n) and so do **not** refute the main theorems. What fails is the chain of intermediate statements used to prove them.
4. **Q-block.** The 4-atom Q-block is w₁–{s,t}–w₂ with s=t.
   - It violates R3 for γ < 2/3 (Lemma 4.6) unless it counts as a vine.
   - DH23's own parametrization of vine (II) covers it: Fig. VineAnnotated (A) and the proof of Prop 7.5 at L1421 have m ≥ 1 double bonds, and m = 1 is the Q-block.
   - With that reading the source argument covers it. The reading is *forced*: without it, Q-bead necklaces lose L^{(2−3γ)m}, and only the vine-(II) cancellation can absorb that.
   - Consequence: the investigation's R4 ("no change to B2") is wrong. B2's vine (II) template needs the m = 1 case.
5. **γ > 1/2.** No counterexample is known in this range.
   - Each small-gap β-constraint now gains (Section 5).
   - For the parallel T-bead, Lemma 5.1 proves 𝔄₀ ≲ δ^{−2}(C⁺)^{−4}L^{−10η} for every gap, using DH23 Lemma A.2(1) (γ > 1/2 branch).
   - A uniform proof for all T-type classes at γ > 1/2 is not done; this includes the infinite families of the investigation's R1.
6. **For the campaign.**
   - F69b is a false statement inside TARGET's black box for 0 < γ ≤ 1/2, not a missing argument. TARGET claims γ ∈ (0,1) (L314), and the physically distinguished value γ = 1/2 (TARGET L325) lies in the failing range.
   - Options:
     - (a) implement the extra input (E0)+(E1) of Section 6;
     - (b) restrict the formal target to γ ∈ (1/2, 1), take (E0), and prove R3 for all T-type classes at γ > 1/2 (the Lemma 5.1 pattern);
     - (c) escalate to the authors with the necklace example.
   - Option (c) is warranted in any case.

## 1. The setting

### 1.1 Objects

- **Molecule.** A directed multigraph without loops, with in- and out-degree ≤ 2 at each atom; V, E, F and χ = E − V + F are as at DH23 L633–L635.
- **Decoration** (L655–L658). Vectors k_ℓ ∈ ℤ_L^d with Σ_{ℓ∼v} ζ_{v,ℓ} k_ℓ = c_v, where c_v = 0 at degree-4 atoms, and Γ_v = Σ ζ_{v,ℓ}|k_ℓ|².
- **Restricted decoration** (`kqmainest2`(ii), L1686). |Γ_v − β_v| ≤ δ^{−1}L^{−2γ} and |k_ℓ − k_ℓ⁰| ≤ 1.
- **Gap** of a triple (v, ℓ₁, ℓ₂) with opposite directions: r = k_{ℓ₁} − k_{ℓ₂}. It is small gap (SG) if |r| ≤ L^{−γ+η} and large gap (LG) otherwise (L1629). An atom is LG if every opposite pair at it is LG (L1829).
- **Block, hyper-block** (L712); vines (L790–L808); vine-like objects (L792). The gap of a block is the gap at either joint (L1627).

### 1.2 Stage 1 and 𝕄(Q_sub)

- Stage 1 splices the small-gap (CL) vine chains (`stage1red`, L1643ff.).
- What remains satisfies Prop 9.1 (`subpro`, L1731–L1744) and Remark `subcondition` (L1747–L1754). Every atom not inside an SG vine-like object is fixed SG or LG. An SG atom gets a designated pair (ℓ₁,ℓ₂) and a dyadic label R_v ∈ [L^{−1}, L^{−γ+η}] with |r| ∼ R_v (L1751–L1752).
- `kqmainest2` (L1681–L1690) is the bound
  𝔠 ≤ (C⁺δ^{−1/2})^{n}L^{(d−γ)n}L^{−Δ_sub}L^{−η⁶ρ}∏𝔛_j^{−z_j},
  with ρ = q + m′ (maximal ladders plus atoms outside them).

### 1.3 Cuts and the quantity 𝔄

- **Cut** (L1757). An α-cut does not disconnect; a β-cut does.
- **𝔄** (L1767): 𝔄 := 𝔠·L^{−(d−γ)χ}(C⁺δ^{−1/2})^{−χ}∏𝔛_j^{z_j}(log L)^{Cp}.
  - 𝔠 is the supremum over the parameters (c_v, β_v, k_ℓ⁰) of the number of restricted decorations that are inherited from a decoration of 𝕄(Q_sub) satisfying Remark `subcondition` (L1765).
  - p is the number of remaining SG atoms; it is 0 in 𝕄_fin (L1819).
- **Deviation** 𝔇 (L1770): 𝔄_pre ≲ 𝔇·𝔄_pos.

### 1.4 Stage 2 (L1773–L1781)

- **Step 1** removes the SG vine-like objects of Prop 9.1(a),(e) and creates **only α-atoms** (L1775).
- **Step 2** removes triangles having two SG triples. v₃ is a β-atom; v₁, v₂ are α or β (L1777).
- **Step 3** cuts the remaining SG atoms along their designated pairs, **in arbitrary order** (L1779).
- **Step 4** performs β-cuts at the remaining atoms until none is possible (L1781). After Step 3 no SG atom is left, so every Step-4 atom is LG.
- **Prop 9.4** (`excessprop1`, L1785–L1787) is the per-operation budget.
  - A β-cut has (ΔF, ΔV_β) = (1, 2) and actual 𝔇 ≲ (log L)^C (L1788); its budget is L^{−η³}·L^{η²}.
  - An α-cut with label R has budget L^{−η³}L^{γ+3η}R².

### 1.5 The final molecule and Prop 9.6

- **Prop 9.5** (`finalmole`, L1806–L1808): ε-atoms have degree 4 and are LG, there are no triple bonds, and "any component that is a vine must be LG".
- **Prop 9.6** (`lgmolect`, L1818–L1822) is the bound
  𝔄₀ ≲ ∏_α L^{−(γ+3η)/2+κ_vη}R_v^{−1}·L^{(γ₀+2η²)V_β−(2γ₀+5η²)G}·L^{−η⁵ρ₀}.
- **Its proof** runs L1854–L1897:
  - (roughbd) L1858;
  - operation (c) L1861–L1863;
  - operation (d) L1865–L1867;
  - operation (e) and (opere) L1869–L1871;
  - case (4) L1883–L1885.

### 1.6 The needed estimate

In case (4) we have V_α = 0, V_β = 2 and G = 1, so (finalcount) reads 𝔄₀ ≲ L^{−η²−η⁵ρ₀}.

**Lemma 1.1 (interpolation).** If 𝔄₀ ≲ L^{−a} with a ≥ η² + 4C₀η³, where C₀ is the constant in (roughbd), then (finalcount) holds in case (4).

*Proof.* Use min(A, B) ≤ A^{1−θ}B^{θ} with θ = η³, together with (roughbd) 𝔄₀ ≲ L^{−η²ρ₀+3C₀}. ∎

So 𝔄₀ ≲ L^{−2η²}(log L)^C suffices. Conversely, 𝔄₀ ≥ c > 0 independent of L refutes the bound.

### 1.7 What TARGET needs

- TARGET L2192–L2197 restates Prop 9.6, and for perfect components the proof is "exactly the same as Proposition 9.6 of DH23". The extra factor L^{ηZ} equals 1 there, since Z = 0.
- TARGET's Operation 3 (L2144) is DH23's Step 3.
- TARGET (finalcount1) (L2114) is the analogue of `kqmainest2` with a stronger gain: 𝔄_sb ≤ L^{−4η⁶(ρ_sb+p_sb)}·L^{(R−1)(…)}.
- TARGET's Theorem (L314) is stated for γ ∈ (0,1) on the square torus (L285).

## 2. Structure of case (4), and the large-gap half

**Lemma 2.1 (equal gaps).** Let b₁, b₂ be the β-atoms of a case-(4) component. Then c_{b₁} = −c_{b₂}, so the two β-gaps have the same length |r|.

*Proof.* Summing (decmole1) over the atoms of 𝕄₀ gives Σ_v c_v = 0. The ε-atoms were never cut, so their degree is 4 in 𝕄(Q_sub) and their c_v is 0. A degree-2 atom carrying the pair (ℓ₁, ℓ₂) has c = ±(k_{ℓ₁} − k_{ℓ₂}). ∎

**Lemma 2.2 (provenance).** Each b_i is one piece of an atom w_i of 𝕄(Q_sub) that was cut exactly once, and w₁ ≠ w₂.
- If either w_i was cut in Step 4, then |r| > L^{−γ+η}.
- If both were cut in Steps 2–3, then |r| ≤ 2L^{−γ+η}.

*Proof.*
- A degree-2 piece is never cut again.
- The two pieces of a β-cut lie in different components forever, so w₁ ≠ w₂.
- Step 1 makes only α-atoms (L1775).
- Step-4 atoms are LG, so every opposite pair at them has a gap larger than L^{−γ+η}.
- In Step 3 the cut is along the SG designated pair, and at a degree-4 atom the other pair has the opposite gap.
- In Step 2, v₁ and v₂ are SG triples. The triangle is a closed sub-structure, so the gap at v₃ is ±r₁ ± r₂.
∎

**Lemma 2.3 (case-(4) components are blocks).** Let H be the atomic group of 𝕄(Q_sub) spanned by the ε-atoms of 𝕄₀ together with w₁ and w₂. Then:
- H is a block or a hyper-block with joints w₁, w₂ and gap ±r;
- 𝕄₀ is H, minus a possible bond w₁–w₂, with w_i replaced by b_i.

*Proof.* ε-atoms never lose bonds:
- Step 1 removes VC interiors, whose bonds stay inside the VC.
- Step 2 removes bonds between cut atoms.
- Removed components contain no atom of 𝕄₀.

So every bond at an ε-atom of 𝕄₀ lies in 𝕄₀. The joints w_i carry exactly the two bonds of b_i, and these have opposite directions. ∎

So "𝕄₀ is a vine" means "H is a vine". The source's case-(4) argument (L1885) runs: vine ⇒ LG (Prop 9.5) ⇒ operation (c). The shape of the vine enters only through "LG".

**Lemma 2.4 (large gap closes).** If |r| > L^{−γ+η}, then 𝔄₀ ≲ (log L)^C(L^{γ−1} + δ^{−1}L^{−η}). Hence (finalcount) holds in case (4) when γ ≤ 1 − 2η.

*Proof.*
- **(i) Parity.** Removing one β-chain cannot disconnect 𝕄₀. Otherwise the side A containing the endpoint v₁ would have degree sum 4(|A| − 1) + 3, plus 2 if the other β-chain lies in A, which is odd. Contradiction.
- **(ii) Operation (c) on that chain.** It has Δχ = −1. With the gap fixed, Lemma A.3(1), second part (L2101), counts the chain bonds by L^{d−1} + δ^{−1}min(R^{−1}L^{d−2γ}, L^d). So 𝔇 ≲ L^{γ−1} + δ^{−1}min(R^{−1}L^{−γ}, L^{γ}). This also holds for a chain of two β-atoms, whose second constraint is the first one shifted by |r|².
- **(iii) The rest.** What remains is a non-saturated molecule: the chain ends now have degree 3. It is LG at every atom, since the other β-chain has gap ±r. So `moleprop1` (L1832) gives 𝔄 ≲ 1.
- **Conclusion.** Put R ≥ L^{−γ+η} into (ii) and finish with Lemma 1.1.
∎

*Remark.* (operc) as printed, 1 + δ^{−1}R^{−1}L^{−γ}, yields no gain under LG. The step "𝔄₀ ≲ L^{−η/2}" at L1885 needs the sharp form in (ii). The (d)+(e) route (L1869–L1871) does not apply to T-beads, because no triple bond forms.

**What remains open after Section 2:**
- small gap (both w_i cut in Steps 2–3);
- H not a vine;
- the closure of H is Y-exceptional.

The investigation's enumeration (`ylem1-investigation/enum/out_case4.txt`) lists 25 such classes with |𝕄₁| ≤ 9: one is Q-type (the Q-block) and 24 are T-type (𝕄₁ is T or reduces to T).

## 3. The necklace molecules N_m

**Definition 3.1.** Take joints w₀, …, w_m.
- **T-beads.** For 1 ≤ i ≤ m, B_i lies between a = w_{i−1} and b = w_i, with interior atoms e_i, g_i, f_i and bonds a→e, b→e, e→g (×2), g→f (×2), f→a, f→b.
- **Odd bead.** B₀ lies between w_m and w₀, with interior atoms o₁, o₂ and bonds w_m→o₁, w₀→o₁, o₁→o₂, o₂→w_m, o₂→w₀.

N_m has n = 4m + 3 atoms and 8m + 5 = 2n − 1 bonds. It has two degree-3 atoms, o₁ with (in, out) = (2,1) and o₂ with (1,2); every other atom is (2,2). It has no triple bond. A **Q-bead** has interior atoms s, t and bonds a→s, b→s, s→t (×2), t→a, t→b; it is used in Lemma 4.6.

**Lemma 3.2 (N_m is the molecule of a prime couple).** For every m there is an explicit couple 𝒬 with 𝕄(𝒬) = N_m (directions included). 𝒬 is prime and non-degenerate in the sense of Remark `moleremark` (L682).

*Proof.* The construction works for any connected loop-free directed multigraph with in/out ≤ 2 and exactly two degree-3 atoms, one of type (2,1) and one of type (1,2), all others (2,2).
- **Forest.** Take a spanning forest of two trees rooted at the degree-3 atoms. Its edges are the PC bonds; every other bond is an LP bond, with a leaf at each end.
- **Signs.** Put ζ_v = + iff the parent bond points v → parent. A root has ζ = + iff its type is (2,1).
- **Leaves.** An LP bond u→v gives u a leaf of sign − and v a leaf of sign +.
- **Check.**
  - The child signs at each node form the multiset {ζ, ζ, −ζ} (Def `defmole`, L637–L643: out-bonds correspond to −slots, in-bonds to +slots).
  - Paired leaves have opposite signs.
  - The rules of Def `defmole` return the original directions.
- **Primality.** N_m has no triple bond. A (1,1)-mini couple or a mini tree would create one (L686–L709).
- **Mechanical check** (`necklace.py`, m ≤ 20, both bead types): 𝕄(𝒬) is rebuilt from 𝒬 and compared bond by bond, and non-degeneracy is checked (no paired sibling leaves, no sibling pair whose subtree leaves pair among themselves).
∎

**Lemma 3.3 (no vine-like objects).** The blocks of N_m (T-beads) are exactly the unions B_i ∪ … ∪ B_j with 1 ≤ i ≤ j ≤ m and joints w_{i−1}, w_j. There are no hyper-blocks. No block is isomorphic, even as an undirected graph, to a vine (I)–(VIII) with any number of rungs, or to the Q-block. Hence:
- 𝒞 = ∅ (Lemma 8.1);
- Q_sub = Q_sk = 𝒬 and 𝕄(Q_sub) = N_m;
- Δ_sub = 0 and there are no hinge atoms.

*Proof.* Let S be a block.
- **(a) {e_k, g_k, f_k} is all or nothing.** If S contains some of these atoms but not all, a double bond crosses the boundary, and its endpoint in S must be a joint. That joint's two internal bonds would then be both incoming or both outgoing. For example, if g ∈ S and e ∉ S, the internal bonds at g are g→f, g→f. This contradicts the in = out = 1 rule.
- **(b) o₁, o₂ are never in S.**
  - Their degree is 3, so neither can be interior.
  - If one of them is in S and the other is not, the joint condition fails as in (a).
  - If both are joints, every w in S is interior. Then the beads propagate around the cycle and force the excluded w into S, a contradiction.
- **(c) S is a run of beads.** So S is a union of T-bead interiors with their joints. A w_i ∈ S is interior iff both neighbouring bead interiors lie in S. Exactly two joints therefore means one run B_i, …, B_j.
- **(d) No hyper-blocks**, since the joints are pairwise non-adjacent.
- **(e) No vine.**
  - One bead has 5 atoms, and no vine has 5 atoms: (I) has 2, the Q-block 4, and (II)–(VIII) have ≥ 6.
  - A run of ≥ 2 beads has an interior cut atom, namely a shared joint.
  - No vine template has one (`vinefree.py`, checked with ≤ 2 rungs per slot). Inserting a ladder subdivides two parallel bonds and joins them by rungs, which creates no cut atom.
- **Mechanical check:** `vinefree.py` enumerates all atomic groups for m ≤ 4.
∎

**Lemma 3.4 (stage 2 on N_m).** Let 𝒟_m(r) be the class of decorations in which:
- every joint w_i is SG, with its designated pair the two bonds in bead B_{i+1} (B₀ for i = m) and gap ±r;
- every other atom is LG.

Then for every order of Step 3:
- Steps 1 and 2 do nothing, since no two joints are adjacent.
- The first Step-3 cut is an α-cut and all later Step-3 cuts are β-cuts.
- Step 4 does nothing.
- The final components are the beads. The two beads next to the first-cut joint carry one α-atom each; every other bead carries two β-atoms.
- For m ≥ 3, some T-bead component has V_α = 0 and V_β = 2, i.e. it falls in **case (4)**.

*Mechanical check* (`cuts.py`): all 24 orders for m = 3 and all 120 for m = 4 (T-beads and Q-beads). For m = 2 the conclusion fails, as expected, since then the odd bead can absorb the two β-atoms. ∎

## 4. The counterexample

Fix d ≥ 3, 0 < γ ≤ 1/2, δ ∈ (0, 1/2] and r = e₁/L. The SG label is R = L^{−1}, which is allowed (L1752). Let 𝕋 be a T-bead component:
- ε-atoms e, g, f, and β-atoms b, b′;
- bonds b→e (x), b′→e (x′), e→g (p, p′), g→f (q, q′), f→b (y), f→b′ (y′);
- c_e = c_g = c_f = 0, c_b = r, c_{b′} = −r.

Then y = x − r, y′ = x′ + r, p′ = x + x′ − p and q′ = x + x′ − q. The quantities x, x′, p, q are free, and χ(𝕋) = 8 − 5 + 1 = 4. The identities

Γ_e = 2(p−x)·(p−x′), Γ_e + Γ_g = 2(q−x)·(q−x′), Γ_b = 2x·r − |r|², Γ_{b′} = −2x′·r − |r|², ΣΓ = 0

are checked by `count_check.py`.

**Lemma 4.1 (lower bound).** For L ≥ L₀(d), 𝔄(𝕋) ≥ c_d (C⁺)^{−4}.

*Proof.*
- **Centres.** x⁰ = 0, x′⁰ = 10e₁, p⁰ = 10e₂, q⁰ = 10e₃. Draw x, x′, p, q from the radius-1/4 balls around these centres.
- **Restrictions hold automatically.**
  - Every bond vector lies within 1 of its centre.
  - Every opposite pair at e, g, f differs by ≥ 8, so LG holds for every L.
  - |Γ_b − β_b| = 2|(x − x⁰)·r| ≤ |r|/2, and likewise for b′, with β at the centre values. Since γ ≤ 1/2 and δ ≤ 1, |r| = L^{−1} ≤ λ := δ^{−1}L^{−2γ}, so the β-atom constraints of width λ hold for the whole family.
- **Pigeonhole.**
  - The family has ≥ c L^{4d} members.
  - (Γ_e, Γ_g) ranges over [−2000, 2000]².
  - Some cell of side λ contains ≥ c′λ²L^{4d} = c′δ^{−2}L^{4d−4γ} members; take β_e, β_g at its centre.
  - Γ_f = −ΣΓ_rest then lies within 2λ of a fixed value, so one more halving fixes β_f.
- **Conclusion.** 𝔠(𝕋) ≥ (c′/2)δ^{−2}L^{4(d−γ)}. Hence 𝔄(𝕋) ≥ (c′/2)δ^{−2}·(C⁺)^{−4}δ² = c_d(C⁺)^{−4}, using 𝔓 ≥ 1 and p = 0.
∎

**Lemma 4.2 (the family is inherited).** Every member of the family is the restriction to 𝕋 = B₂ of a decoration of N₃ in 𝒟₃(r). That decoration satisfies Remark `subcondition` and `kqmainest2`(i)–(ii) with fixed parameters.

*Proof.*
- **Other beads.** Fix one decoration of each other bead, using the same construction with all its vectors shifted by 100·i·e₁. A shift preserves interior vector constraints and joint differences.
- **Odd bead.** Use e.g. s = 300e₁ and s′ = 400e₁ (with t = s − r, t′ = s′ + r), and u = s + s′ + 10e₂. Then every opposite pair at o₁, o₂ differs by ≥ 8.
- **Constraints.**
  - Given r, the beads interact only through the joints.
  - Vector constraints hold because the gaps cancel.
  - Γ_{w_i} is the sum of two bead parts, each within |r|/2 of its centre value, so it is within |r| ≤ λ of β_{w_i}.
  - Interior β_v are taken from the fixed decorations.
  - The SG label is R_v = L^{−1}.
  - Non-resonance (ε ≠ 0, i.e. k₂ ∉ {k₁, k₃} at every node) holds because every opposite pair has a nonzero gap.
∎

**Proposition 4.3 (R3 and Prop 9.6 fail for γ ≤ 1/2).**
- The T-bead component of N₃ is a case-(4) component of 𝕄_fin in every Step-3 order (Lemma 3.4).
- Its 𝔄₀ is at least c_d(C⁺)^{−4} (Lemmas 4.1, 4.2).
- (finalcount) demands 𝔄₀ ≲ L^{−η²−η⁵ρ₀} with ρ₀ ≤ 5.

These are incompatible for L large. The same component is a perfect component in TARGET, so TARGET's `lgmolect` (L2193) fails as well. ∎

**Proposition 4.4 (`kqmainest2` fails for γ ≤ 1/2).** Let m ≥ (3d+1)η^{−6}. On N_m with all joints in 𝒟_m(r), the beads are independent given r. By Lemmas 4.1 and 4.2, with one fixed decoration of B₀:

𝔠(N_m) ≥ [(c′/2)δ^{−2}L^{4(d−γ)}]^m.

The right side of `kqmainest2` is (C⁺δ^{−1/2})^{4m+3}L^{(d−γ)(4m+3)}L^{−η⁶ρ}, with:
- Δ_sub = 0;
- no ladder of length ≥ 1, so ∏𝔛 = 1;
- ρ ≥ #{w_i, o₁, o₂} = m + 3.

The ratio of left side to right side is ≥ [(c′/2)(C⁺)^{−4}]^m(C⁺)^{−3}δ^{3/2}·L^{η⁶(m+3)−3(d−γ)} ≥ c(m)·L, which tends to ∞ as L → ∞ for fixed m. TARGET (finalcount1) at R = 1 fails the same way, all the more because it also asks for L^{−4η⁶p_sb} with p_sb ≥ m + 1. ∎

*Remark 4.5 (scope).* Not claimed:
- that |𝒦_𝒬| itself (time integrals included) violates DH23 (`kqmainest1`) or TARGET (finalsbest2);
- that any main theorem is false.

These couples are few (C^n of them), and their contribution is heuristically O(L^{γ−d}) per congruence class. The defect is in the proof chain.

- **Exponent bookkeeping.** In 𝕋 the β-cuts cost nothing (𝔇 ≲ (log L)^C) and are budgeted L^{−η³+η²}. The component must pay L^{−η²}, but with a small gap its β-constraints are void. Then 𝔄₀ ≈ 𝔄(𝕄₁) = 𝔄(T) ≈ 1.
- **Why the necklace defeats any repair.** The only slack in a necklace is that of the first α-cut, of size R^{d−2}L^{−3η}. A necklace with ≫ η^{−6} beads exhausts it, so no bookkeeping inside stage 2 helps.

**Lemma 4.6 (Q-bead under the literal reading).** Let 𝕢 be a Q-bead component:
- bonds b→s (x), b′→s (x′), s⇉t (u, u′), t→b, t→b′;
- χ = 3 and Γ_s = 2(u−x)·(u−x′).

With r = e₁/L:
- **γ ≤ 1/2.** Every x satisfies the β-constraint, and 𝔄(𝕢) ≳ (C⁺)^{−3}δ^{1/2}L^{γ}.
- **1/2 < γ ≤ 2/3.** The β-constraint at b confines n₁ = Lx₁ to a window of δ^{−1}L^{2−2γ} integers. Then #x, #x′ ≳ δ^{−1}L^{d+1−2γ}, a pigeonhole over Γ_s gives 𝔠 ≳ δ^{−3}L^{3d+2−6γ}, and so 𝔄(𝕢) ≳ (C⁺)^{−3}δ^{−3/2}L^{2−3γ}.

So R3 fails for γ ≤ 2/3 unless the Q-block is a vine.
- **Literal reading.** If the Q-block is not a vine, N_m(Q) (which `cuts.py` checks reaches case (4) in every order) violates `kqmainest2` by a factor ≳ L^{(2−3γ)m}.
- **Generous reading.** It *is* a vine: vine (II) with one double bond. This is the m = 1 case of DH23's parametrization (L1421, "v₁, v₂, v_{2j+1}, v_{2j+2} (1 ≤ j ≤ m)", Fig. VineAnnotated (A)). `vinefree.py` reports the Q-bead as "II(m=1)". With this reading:
  - the Q-bead is an SG vine;
  - it is removed in Step 1 or spliced in stage 1;
  - in case (4) it is LG, and Lemma 2.4 applies.
∎

## 5. Why the bound holds where it holds

### 5.1 Heuristic

- For a tiny gap, the β-constraints are void. So 𝔄₀ ≈ 𝔄(𝕄₁) with relaxed c's, by reversing operation (d) (Df ≲ (log L)^C).
- DH23 itself says (L579ff., Fig. Bad_Mol) that 𝔄(Q) ≈ L^{γ} (no good operation) and 𝔄(T) ≈ 1 (one good operation).
- For a generic small-gap block with V_H interior atoms, each bead in a tiny-gap chain contributes ≈ L^{γ(3−V_H)}, before degeneracy losses.
- So the uncovered set splits:
  - **Q-type** (the Q-block): it loses L^{γ}, like the bad vines (I) and (II).
  - **T-type** (the other 24 listed classes and the infinite families): neutral, like the normal vines.
- For γ > 1/2, every SG constraint gains: a β-constraint with |r| ≥ L^{−1} cuts the count by ≤ δ^{−1}L^{1−2γ} (Lemma A.3(1)). The T-type classes then gain about L^{−(2γ−1)} per effective β-constraint, and the Q-type ones are L^{γ}·L^{2(1−2γ)}, a gain iff γ > 2/3.

### 5.2 A proof for γ > 1/2

**Lemma 5.1 (T-bead, γ > 1/2).** Let γ > 1/2 with 0 < η ≪ γ − 1/2 (as DH23 assumes at L2076), and let L^{−1} ≤ |r| ≤ 1. The parallel T-bead component satisfies 𝔄(𝕋) ≲ δ^{−2}(C⁺)^{−4}L^{−10η}. So case (4) holds for it, with any gap.

*Proof.* Use the constraints (a) x·r ∈ I₁, (b) x′·r ∈ I₂, (c) (p−x)·(p−x′) ∈ J_e and (d) (q−x)·(q−x′) ∈ J_{eg}.
1. **Count x′ by (b).** Lemma A.3(1), second part: L^{d−1} + δ^{−1}|r|^{−1}L^{d−2γ} ≲ δ^{−1}L^{d+1−2γ}.
2. **Count (x, q) by (a) and (d).** Write X = q − x′ and Y = q − x. Then (d) is X·Y ∈ J and (a) is (X − Y)·r ∈ I₁ − x′·r. This is system (basiccount01) with ξ = X + (−Y). Lemma A.2(1), γ > 1/2 branch (L2057), gives ≲ δ^{−2}L^{2(d−γ)−10η}.
3. **Count p by (c).** The pair (p, p′) has fixed sum and fixed |p|² + |p′|². Lemma A.3(1), first part, gives δ^{−1}L^{d−γ−γ₀} = δ^{−1}L^{d−1}.
4. **Total.** δ^{−4}L^{4d−4γ−10η}. Divide by L^{4(d−γ)}(C⁺δ^{−1/2})^{4}; 𝔓 = 1. Finish with Lemma 1.1.
∎

**Status for γ > 1/2.** Still to do:
- the other orientations of the three T-beads;
- the T₁-blocks and the 9-atom block;
- the infinite families: Z_m(T_n, ℓ′) closures with β-atoms off the closure bonds, and vine closures with misplaced β-atoms.

Each needs a count of the same kind, pairing a β-constraint with a product constraint as in Lemma A.2(1). No counterexample is known in this range, and the heuristic predicts R3 holds.

## 6. The extra input required

- **(E0) Vine (II) with m ≥ 1 double bonds.** Needed for all γ < 2/3.
  - Read vine (II) as joint – (ladder of m ≥ 1 double bonds) – joint, as DH23's own Prop 7.5 parametrization does.
  - Check the (II-a)–(II-e) structure (Prop 5.3, L810ff.) at m = 1.
  - Check Steps 2–4 of Prop 7.5 (L1421–L1546) at m = 1. The twist cancellation is local to the triangle at one joint.
  - Add the m = 1 template to B2's `VineType.template` for (II). This reverses R4 of the investigation.
- **(E1) T-type blocks as normal vines.** Needed for 0 < γ ≤ 1/2. Let 𝒯 be the class of non-vine blocks whose joint-closure reduces to T by (Y)-sequences, zero sequences allowed. This includes the 5-atom T-beads, the T₁-blocks, the 9-atom block and the R1(4) families. Treat SG 𝒯-blocks, and their chains with vines, as normal vine chains. This requires:
  - **(a)** Lemma 8.1 and Prop `subsetvc` (L2128) for the enlarged family: disjointness and uniqueness of 𝒞. Lemma 4.11 (`disjointlem`, L726) applies to any blocks satisfying its (i)–(ii).
  - **(b)** A Prop 7.6-type bound for spliced 𝒯-chains, with loss ≤ L^{η⁴} per chain and no cancellation needed. Its counting core is a block-interior count of order L^{(m−2)(d−γ)}·polylog with the joint pair fixed. For the T-bead this count is δ^{−2}L^{3d−3γ−γ₀} ≤ δ^{−2}L^{3(d−γ)}.
  - **(c)** The Prop 9.1 properties (a)–(f) for the enlarged family.
  - **(d)** The Step-1 deviation. For the T-bead: 𝔇 ≲ δ^{1/2}R^dL^{2γ−γ₀} ≤ L^{−η³}R²L^{γ+3η} for γ ≤ 1 − 2η and d ≥ 3, by Lemma A.2(1) with P = 0 and Lemma A.3(1).
  - **(e)** "𝒯-component ⇒ LG" in Prop 9.5, with the same proof as for vines.

  With (E0) and (E1), a small-gap Y-exceptional H in case (4) would be an SG vine or SG 𝒯-block, which has been removed beforehand. So H is LG, and Lemma 2.4 closes case (4).
- **(E2) Alternative: restrict to γ ∈ (1/2, 1).** Take (E0), and prove R3 for all T-type classes at γ > 1/2, following Lemma 5.1. This is pure counting, but it is uniform over infinite families, and it drops γ ≤ 1/2 from the theorem, including γ = 1/2.

These are not local repairs to case (4):
- Operation choices inside case (4) cannot help, since 𝔄₀ is bounded below (Lemma 4.1).
- Choosing the Step-3 order cannot help (Lemma 3.4, every order).
- Moving the T-beads into stage-2 Step 1 alone cannot help, because a chain of SG T-beads still violates `kqmainest2` (Prop 4.4). The atoms of a chain must leave ρ, which only stage-1 splicing achieves.

## 7. Finite checks

All scripts run as `python3 -I <script>` in this directory. Checksums are in `SHA256SUMS`.

| script | what it checks | output |
|---|---|---|
| `necklace.py` | N_m (T- and Q-beads, m ≤ 20): it is a molecule with E = 2n−1 and no triple bond; the explicit couple has the right sign pattern and pairing and is non-degenerate; 𝕄(𝒬) = N_m (directed) | `out_necklace.txt` |
| `vinefree.py` | all blocks and hyper-blocks of N_m for m ≤ 4 are runs of beads; vine matches are 0 for T-beads, and Q-beads match only "II(m=1)"; vine templates have no interior cut atom | `out_vinefree.txt` |
| `cuts.py` | stage 2 in every Step-3 order (m = 3: 24, m = 4: 120): Step 4 void; a T-bead or Q-bead component with V_α = 0, V_β = 2 occurs in every order (not for m = 2) | `out_cuts.txt` |
| `count_check.py` | exact rational checks, for L = 8, 64, 10³, 10⁶, of the vector constraints, the Γ identities, the automatic β-constraints, the LG margins ≥ 8 and the unit-ball restriction for the family of Lemma 4.1 | `out_count_check.txt` |
| `graphs.py` | canonical forms (copied from `ylem1-investigation/enum`) | — |

## 8. Remaining risks

1. **Reading of 𝔠.** 𝔠 is the supremum over (c_v, β_v, k_ℓ⁰) of inherited restricted decorations (L1765; TARGET L2131), so r is a parameter. Even under a stricter reading the counterexample stands: it fixes the dyadic label R_v = L^{−1}, which Remark `subcondition`(iv) allows, and Lemma 4.2 shows inheritance.
2. **Definitions taken from the source.** LG at an atom means all opposite pairs are LG (L1629, L1829), and our margins are ≥ 8. The constants are C⁺, δ ≤ 1/2, and η small but fixed.
3. **Non-degeneracy.** Remark `moleremark` is checked mechanically. Non-resonance holds because all opposite gaps are nonzero.
4. **Lemma 3.3 for general m.** It rests on the proof in Section 3. The mechanical check covers m ≤ 4, and Prop 4.4 needs m ≈ η^{−6}.
5. **TARGET's layered gardens.** That N_m arises as 𝕄_sb with layer data has not been checked. Putting all nodes in one layer reproduces DH23's setting, but TARGET's requirements (a)–(f) (L2096–L2109) should be confirmed.
6. **(E0)** needs an author-level check that Prop 7.5's cancellation holds at m = 1.
7. **Main theorems.** Whether DH23's or TARGET's main theorems hold for γ ≤ 1/2 is not settled here. Only the intermediate statements are refuted.
8. **The γ = 1 endpoint** (generic tori) of Lemma 2.4 is not covered.

## 9. What a Lean formalization would need

- **To record the erratum** (optional, kernel-checkable). Formalize:
  - N₃ (and the T-bead component) as concrete finite directed multigraphs, with the explicit couple;
  - the decidable checks of Section 7: vine-freeness against B2 templates, and the cut simulation;
  - Lemma 4.1, which needs only lattice-point counting in balls (≥ cL^d points) and a finite pigeonhole over intervals.

  This refutes the black box `lgmolect` as stated for γ ≤ 1/2.
- **For (E0).** Add the m = 1 instance to B2's vine (II) template, and redo the affected B2 lemmas. The kernel checks of the 5-atom facts are unaffected.
- **For (E1).**
  - A new inductive class 𝒯 (via the R1 exception list or a (Y)-reduction predicate).
  - The block-interior counting lemma for 𝒯, uniform over the families. Ladder neutrality enters through the 𝔛 factors.
  - The Step-1 deviation lemma.
  - The extensions of Lemma 8.1, Prop 9.1 and Prop 9.5.
  - The stage-1 analytic bound (a Prop 7.6 analogue), which is the hardest part.
- **For (E2).**
  - A formal γ > 1/2 hypothesis in the target.
  - Lemma 5.1-type constrained counts for every T-type class, using DH23 Lemmas A.2(1) and A.3(1). Their γ > 1/2 branches need 0 < η ≪ γ − 1/2, already in the campaign's NT layer (F3).
