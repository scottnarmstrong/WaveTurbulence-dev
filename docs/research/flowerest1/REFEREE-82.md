# Referee report: o82, the resolution of OPEN 8.2 (Theorem 8.2′)

Referee: independent, refute-first (wt-orch request, 2026-11-07). I did not write any of the refereed text. Read-only on every other file. No Lean, no git.

(Written as I went. The verdict table is §1; every fix is listed in §4.)

## 0. Pins

Each file was copied to my scratchpad at first read and hashed from the copy.

| File | sha256 at first read | Note |
|---|---|---|
| o82/RESOLUTION.md | `7038cf6b5b1a2d3475171de7ab204381df4ce31b3ac19bd8caed1fb254b24e92` | unchanged at the end of the audit (re-hashed 14:11 UTC) |
| SUPPLEMENT-v1.md | `ddd81fe1…74d7` | matches its pin |
| o73/RESOLUTION.md | `eb26e89a…70b928` at first read; `f4114edb…aa0b4` later | the later version adds §§16–22; §§3, 12–13, which o82 uses, are unchanged |
| o75/RESOLUTION.md | `d7102c43…74eb8` at first read; `0007b57c…c361` later ("Rev. 1") | Rev. 1 changes the (C8.2) contract; see F1 |
| o63/RESOLUTION.md | `a50e0f93…bc4` | as refereed in REFEREE-2 |
| ref/REFEREE.md | `c31ee38a…d6d` | |

- The sources match their pins: T `493eef6b…727cb`, D21 `50d0e236…fe402`, D23 `c7e47dfa…35475`.
- Notation: "S" is the supplement; "T/D21/D23 n" is a source line; "o82 §n" is a section of the refereed file.

---

## 1. Verdict table

| # | Step (o82 section) | Verdict |
|---:|---|---|
| 1 | Prop 2.1: uniform Fourier bounds for the truncated reciprocal χ_∞ϑ/α (§2) | **PASS** |
| 2 | Prop 3.1: cutoff version of the unpinned spectral decomposition (§3) | **PASS** |
| 3 | Prop 4.1: scalar truncated discrete-to-principal-value estimate (§4) | **PASS** |
| 4 | Prop 5.1: a selected extracted coordinate (§5) | **PASS** (trivial absolute bound; not used by Thm 8.2′) |
| 5 | Exact one-pair face and pin identities (6.1), (6.3), (6.4) (§6) | **PASS** |
| 6 | Marked-coefficient interface I (§9) and its consumer Thm 13.1 (§13): the "marked-chain recursion" | **PASS as a conditional.** Its premise is never produced, and Thm 8.2′ correctly does not use it |
| 7 | Thm 10.1: many-variable discrete step in independent unit boxes, order range n ≤ H(log L)^K, simultaneous exclusions (§10) | **PASS** |
| 8 | Lemmas 11.1–11.2, Thm 11.3, time-weight interpolation (11.9): filtered principal value (§11) | **PASS** |
| 9 | Lemma 14.1 and Prop 14.2: pointwise pin/face bound with all upper filters (§14) | **PASS** |
| 10 | Prop 15.1: filtered ordinary kernels (§15) | **PASS AFTER FIX** (F3, statement level) |
| 11 | Cor 15.2: filtered terminal pin (§15) | **PASS AFTER FIX** (F2, statement level) |
| 12 | Lemma 16.1: the X^{1/4} bound (§16) | **PASS AFTER FIX** (F2: output weight; F6: citation) |
| 13 | Lemma 16.2 and Cor 16.3 (§16) | **PASS** (superseded by §18; unused) |
| 14 | Lemma 17.1 (fold extension) and Lemma 17.2 (L^∞/A^{1/4} interpolation) (§17) | **PASS** |
| 15 | Lemma 18.1 and Thm 18.2: protected-object bound, the occurrence gain M₂^{-1/18}, zero lost incoherency (§18) | **PASS** (F2 inherited) |
| 16 | Thm 8.2′, statement and proof (§19) | **PASS** |
| 17 | Sufficiency of Thm 8.2′ for Prop 10.3 / 10.3′ with o75's non-excision Thm 7.5′ (§19) | **PASS AFTER FIX** (F1, scope: already patched in o75 Rev. 1; leaves a live obligation on C7.3) |
| 18 | Loss table, exponent contract, budget (10.4) (§20) | **PASS** |
| 19 | "Zero lost incoherency units" | **PASS** |

**No FAIL.** I found no counterexample to any step that Thm 8.2′ relies on, and no hidden L^{Cn}, C₂^n or δ-dependent exponential base.

---

## 2. Sufficiency for the assembly

### 2.1 What the assembly consumes

The regular objects enter the reduction at T1725 (redkg). Stage 1 consumes them at T1959–1965:
- The leaf momenta are localized to unit balls. Summability comes from the couples' ⟨k⟩^{30d} decay.
- The regular kernels are expanded in time Fourier. Their Fourier coefficients become unit-ball amplitudes with ≤ 30d bounded output derivatives, with the time weight from the X^η norm.

So a protected regular object must supply:
- an X^{η,30d,·} bound on its local output ball, with the output supremum **inside** the Fourier integral (T582 (normX), T589 (locnorm));
- a base independent of δ;
- a numerical L-loss;
- its incoherency gain (o75 (G-ret));
- the M₂ gain at its selected occurrences.

Item 2 of Thm 8.2′, via (18.3), supplies exactly this:
- X^{η,30d,0} on a unit output ball;
- loss L^{(47d+5)r} with r = b₀ + a;
- base C_{P,χ,ϑ}^{m+1};
- full G(𝒪);
- M₂^{-a/18}.

I checked each consumption point against T.
- **Cap.** A couple carrying a stem vertex is (T′, cap) by o73 Prop 3.1, which I verified. Its output is the fixed cap momentum k′. So the T1959 summation needs no decay for it.
- **Regular trees.** Their output balls come from the tree lemma (T1960).
- **Unprotected filtered objects.** These are item 1, handled by Prop 15.1. They are consumed only through their X norms.
- **SG vines.** In the M₂ version, o75 Lemma 2(d) keeps SG vines off the stem. So no LF cancellation involves a filtered object. The filtered principal-value statement (§11) is therefore stronger than needed, but correct.

### 2.2 Non-excision geometry

Under o75 Thm 7.5′, marked vines are neither twisted nor spliced. A protected regular object attached at u₁ of an unmarked vine is a common factor of the class sum, because twist-active sets exclude u₁'s objects. So every protected regular object is an initial-skeleton object of o73 Prop 3.1 type:
- a layer-p root-to-port chain;
- arbitrary side couples;
- at most one terminal pin.

I also checked the multiplicities.
- At most one selected occurrence lies in each object (a ≤ 1). There is one selection per original tree, a regular object meets at most one stem, and selected stem vertices are chain nodes, never in side couples.
- At most one pin lies in each object (b₀ ≤ 1).
- So r ≤ 2, and Thm 18.2 covers all cases. The "repeated frequency" paragraph is vacuous in this geometry, which is harmless.

### 2.3 Scope (F1)

Thm 8.2′ gives M₂^{-1/18} only for selected occurrences **inside a regular object**. This scope is correct: S OPEN 8.2 asks for the gain only for "occurrences assigned to the object". But:
- the o75 version I pinned (d7102c43) asked (C8.2) for M₂^{-1/18} "per selected occurrence" with no restriction;
- its row 13 marked the skeleton faces "proved", although S Lemma 9.1 gives only the raw reciprocal.

**o75 Rev. 1 (0007b57c) fixes the contract.**
- (C8.2) now reads "inside a regular object".
- Skeleton selected vertices go to "S Lemma 9.1 together with the face estimates in (C7.3)".

With Rev. 1, Thm 8.2′ meets its contract exactly. The remaining obligation lies on OPEN 7.3: an estimate of the S Lemma 9.1 faces at skeleton and residual selected vertices, retaining the reciprocal (9.1). Until 7.3 closes, the third line of S (1.1) is not established.

The tracker's phrase "M₂^{-1/18} per selected occurrence" for o82 should add "inside a protected regular object".

---

## 3. Step-by-step checks

### 3.1 §2, Prop 2.1: PASS
- **ĝ near 0.** The sine-integral split at |σ|^{-1} is correct: the region 1 < α < |σ|^{-1} gives ≤ 2π, and one integration by parts handles the rest.
- **Large |σ|.** The identity (2πiσ)^r ĝ = (g^{(r)})^, with g^{(r)} ∈ L¹ for r ≥ 1, gives arbitrary decay.
- **Convolution.** ∫⟨σ⟩^r S|ϑ̂(Sσ)| ≤ ∫⟨u⟩^r|ϑ̂| for S ≥ 1, combined with Peetre's inequality, gives (2.2) uniformly in the scales.
- **(2.3) and (2.5).** (2.3) is correct. (2.5), 2 log S, correctly shows why the reciprocal must stay explicit.

### 3.2 §3, Prop 3.1: PASS
- Evenness of ϑ puts both cutoffs of a linked pair on one coordinate.
- Coordinates in Z keep their cutoffs with the reciprocal; coordinates in J are handled by S Lemma 8.1 (RR transcription fix: base C₀^n).

### 3.3 §4, Prop 4.1: PASS
- **(4.5)** is D23 L1013–1038, Lemma NTSP(2), with Φ = κ(s/L)f(s/μ). Φ is independent of (x,y) and supported in |s| ≲ L. Checked.
- **(4.6)** is D23 L1076–1086, Lemma minorarcs(2). It is stated for Φ supported on L ≲ |s| with **no upper bound**, with weight ⟨s/δL^{2γ}⟩^{-P}, P > η^{-2}. This is exactly what (4.6), (10.10) and (14.3) need. Checked.
  - T's own lemlayer2 (T972) covers only L ≤ |s| ≤ 𝒟δL^{2γ}, with a C₂ constant. Using D23's weighted version is the right choice, and its constant is δ-independent.
- **(4.9)** is D21 L1305–1323, NTOmegainv(2). It carries a factor (1+|ξ|+|η|), which D(W) in (4.1) includes. Checked.

### 3.4 §5 and §6: PASS
- (5.1) is a one-line absolute bound.
- (6.1): I re-derived K = (e^{iω(t−s)}−1)/(iω)² − (t−s)/(iω).
- (6.3) and (6.4) are correct.

### 3.5 §§9 and 13, the marked-chain recursion: PASS as a conditional; not used
- The interface I of §9 (consumed weight, ⟨α⟩^{1/4} modulation allowance, original coordinates) is never produced. o73 also did not produce it; the live o73 §16 abandons it.
- Thm 13.1 is a correct implication. I re-derived (13.4): (δ/2L^{d−γ})^{2m}L^{2de}(L^{2d}/μ)^{m−e} = (δ/4)^m μ^e.
- §19 and §21 state that Thm 8.2′ does not rely on Thm 13.1. That is accurate: §§14–18 avoid any class-J/R marked recursion.
- Consequently no document should cite o82 as having proved a marked coefficient decomposition.

### 3.6 §10, Thm 10.1: PASS
This is the many-variable step over the order range.

**Independent boxes are legitimate.** After T1002–1004 (leaf localization, then the tree lemma at cost C₀^n), every (x_𝔫, y_𝔫) lies in its own ball of radius 1/2, and smooth χ₀(x−a)χ₀(y−b) are inserted. So the triangular supports of D23 approxnt (D23 L991–993) do not occur. Fixing exceptional pairs keeps the others independent.

**Structure.** The structure matches D21 L1586–1622:
- the major/minor split (10.13);
- telescoping on the all-major term;
- the minor arc with sup_σ|f∏⟨σ_j⟩^q| ≤ BC_q^{n+1}(8qf)!.

**Inputs.**
- (10.8) and (10.9) are D23 NTSP (NTSPest2, NTSPest), with λ = 1.
- (10.10) is D23 minorarcs(2).
- (10.11) is stationary phase: |B_j(s)| ≤ CL^{2d}⟨s⟩^{-d}.
- All constants are independent of δ.

**(10.7).** For Z-coordinates, Prop 2.1 gives the weighted L^∞ bound. For J-coordinates, |σ^q Ĉ| ≤ ‖∂^q C‖₁. The total derivative order is ≤ qf.

**Order range.** n ≤ N⁴ = (log L)^{K_δ} (T612, parameters2). Then (8qf)! ≤ (8qn)^{8qf} ≤ L^{η₀f}, since 8q log(8qH(log L)^K) = o(log L).
- This is paid per minor coordinate from L^{-(a_γ−η₀)}.
- q is fixed before δ; only the L threshold depends on (δ, H, K).
- There is no L^{εm} overhead and no C₂^m.

**Exclusions (T1023–1025).**
- On {x=0 or y=0}, g_S(μx·y) = 0. Checked.
- For J-coordinates, the trace (10.16) costs one derivative. Relative to L^{2d}/μ each correction costs μL^{-d} ≤ L^{-(d−2γ)}, and d−2γ > 1 ≥ γ₁ for d ≥ 3.
- The simultaneous factorial (8(f+qh))! is absorbed as in (10.15) (verification note, §21).

**The output supremum.** The bound for each fixed ν is a product of sup_σ|f_{v,ν}| (a functional of the coefficient only) and quantities uniform in the external parameter. So it is a v-independent majorant pointwise in ν. This is what puts sup_k inside the λ-integral (used in F3).

### 3.7 §11: PASS

**Lemma 11.2.** I re-derived the bound independently. Write

ĥ(s) = ∫ψ(x−a) e(ξx) ψ̂′(ζ+sx) dx (up to signs).

Then |ĥ(s)| ≤ ‖ψ‖_∞‖ψ̂′‖₁|s|^{-d}, uniformly in (a, b, ξ, ζ). For d ≥ 3, h ∈ C¹ with ‖h′‖_∞ ≤ C. This is strictly cleaner than D21 NTOmegainv, which carries (1+|ξ|+|η|), and it is uniform in the modulations as claimed.

**(11.2), (11.7), Thm 11.3.**
- The low-frequency part is ≤ Cμ^{-1}, by symmetry and the Lipschitz bound.
- The upper-cutoff part is ≤ L^{-1}‖h‖₁.
- The J-telescoping uses a sum of single-coordinate moments, each ≤ the max-moment (D23 maincoef2.5). No product moment is claimed.
- The main term (11.5) is D23 (intappr) with the unfiltered coefficient. Checked against D23 L1000–1009: D23's "J" is o82's "Z".

**(11.8).** 2γp = 2γ − γη > 1 − η ≥ γ₁ − η, because 2γ − 1 > 0 > η(γ−1). So δ^{-p} is absorbed in the L threshold.

**(11.9).** t = (3η/4)/(1−3η/8) ≤ η for η ≤ 2/3, and (γ₁−η)(1−t) ≥ γ₁ − 2η ≥ γ₁ − √η. Hölder with the max-weights is legitimate, since max is monotone.

### 3.8 §14: PASS

**Lemma 14.1.**
- **(14.2)** follows from ϑ(u/M) = ∫ϑ̂(σ)e(σu/M)dσ. The moment bound is scale-invariant for M ≥ 1. Checked.
- **Equal layers.** r = μz + τ with |r−τ| ≤ μ.
  - The |r| ≤ L part is ≤ CL^{2d}, from lemlayer1 (T957–970) and Poisson summation.
  - The |r| ≥ L part uses D23 minorarcs(2), with ⟨r/μ⟩^q ≤ C(1+|τ|/μ)^q and μM_* ≥ 1.
  - The base constant is δ-independent, which is better than T's ≲₂ in (incohproof13).
- **Unequal layers.** ℓ_{q,q′}(z) ≤ min(1,|z|) is correct (triangle density vanishing at z = 0).
  - The |r| ≤ L part gives L^{2d}μ^{-2}∫(1+|τ|)d|ω|.
  - The |r| ≥ L part gives C_δL^{2d}μ^{-1}L^{-a_γ+η₀}.
  - Both are absorbed per unequal link into L^{-(γ₁−√η)}. That is a per-link absorption, not C₂^m.
- **Zero vectors.** On the zero-vector set the filters equal 1 (annular factors vanish there), so the cost is O(L^d).

**Prop 14.2.**
- Each surviving time belongs to exactly one non-exceptional link.
- Face substitutions only move phases onto exceptional links, which are bounded pointwise by C^eL^{2de}.
- The partition indicators define a lattice-independent D_F, and enlarging it is legitimate after absolute values.
- The normalization gives (Cδ)^m μ^e. I re-derived this.
- For original stem pins and faces every exceptional link is a layer-p chain link (o73 Prop 3.1), so g_J = g.

### 3.9 §15: Prop 15.1 PASS AFTER FIX (F3); Cor 15.2 PASS AFTER FIX (F2)

**Prop 15.1, g ≥ 1.** I re-read T981–1092 line by line. The proof uses:
- the pointwise bound |𝒮_𝔫| ≲ L^{2d};
- the pairwise integrated bounds (incohproof13)–(15);
- (incohproof18) and (incohproof25);
- for trees, the lattice expansion of the designated endpoint sums (T1084, "losing L^{4d}");
- the boundary-derivative bound (incohproof27);
- timeintlem and timeintlem2 (T2354–2379).

The upper filters are time-independent scalars of modulus ≤ 1 on each link. Lemma 14.1 replaces (13)–(15). So the replacement argument is complete at the level of T's own proof.

Two further points:
- The output derivatives and the weight ⟨k⟩^{30d} still fall on the profiles, plus the affine frontier factors (S Lemma 4.1 with the RR tree-half fix).
- The η-bookkeeping (100dη, then 200dη ≤ √η) matches (incohproof20)/(incohproof24).

**Prop 15.1, g = 0.** The coherent factorization (prooflayer1-1)/(prooflayer1-2) at T1240–1244 is an exact product of single-layer kernels with fixed or free time arguments. So the filtered single-layer estimates of §§10–11 multiply. The fix needed is F3.

**Cor 15.2.**
- It applies the o73 exact cut (13.1). I verified the cut: crossing links are excluded by legality (T849), the side couples Q₁, Q₂ of the link {a,2h} are functions of (u,s), and the chain times are ordered.
- It applies o73 Lemma 12.1. I verified the atom formula (12.3) and o73 Prop 5.1.
- The fix needed is F2.

### 3.10 §16: Lemma 16.1 PASS AFTER FIX (F2, F6)
- **Trees.** This is T (incohproof28) at T1090–1091: X^{1/4,0,0} with sup_k inside, gain γ₁ − 100dη, loss L^{4d}. Checked.
- **Couples.**
  - ‖S‖₁ ≤ A and ‖S‖_∞ ≤ AL^{2d} is (incohproof18) at T1050, not T1048 (F6).
  - Then ‖S‖₂ ≤ AL^d.
  - With (proofichi-1) at T2366, the kernel of ℐ_χ is ≲ 1/(⟨ξ⟩⟨ξ−ξ′⟩⟨σ⟩⟨σ−σ′⟩). Then ∫⟨ξ⟩^{-3/4}⟨ξ−ξ′⟩^{-1}dξ ≲ ⟨ξ′⟩^{-3/4}log(2+|ξ′|), and ⟨·⟩^{-2/3}⊗⟨·⟩^{-2/3} ∈ L²(ℝ²). So ‖ℐ_χS‖_{X^{1/4}} ≲ ‖S‖₂. I re-derived this.
- **Coherent objects.** The X^{1−η/8} bound comes from D23 (maincoef2) through Thm 10.1 (10.5) with w₁. Checked.

**Lemma 16.2.** The atom bound C⟨z⟩^{θ−1} and the two-case split are correct. **Cor 16.3:** correct, but superseded.

### 3.11 §17: PASS
**Lemma 17.1.**
- G(z) = φ(0)/(2πiz) + O(|z|^{-2}) for even φ.
- The leading reciprocals of G(ξ−a) + G(−ξ−a) cancel to φ(0)a/(πi(ξ²−a²)), so the tail is ≲ (1+|a|)|ξ|^{-2}.
- This gives the atom bound C⟨a⟩^σ log(2+|a|). The tangential tensoring is correct.
- **Numerical check (my scratchpad).** I computed ∫⟨ξ⟩^{1/4}|𝓕[φ(x)e^{2πia|x|}]| for a = 1, …, 3000. Its ratio to ⟨a⟩^{1/4}log(2+a) decreases (0.80 → 0.34), consistent with the bound.
- **Folds.** r(x) = 1 − |1 − |x|| is two folds up to isometries. Sorting is one fold across the diagonal in rotated coordinates. Five folds lose 5·(1/40) = 1/8, so A^{1/4} → A^{1/8}.
- **Extension.** The extension uses only values on D̄, and A^{1/4} functions are continuous.

**Lemma 17.2.** Cauchy–Schwarz on a ball of radius R in ℝ² gives R^{1+η}A, and the strong norm outside gives BR^{-(σ−η)}. Optimizing gives τ = (σ−η)/(1+σ) = (1−8η)/9, which is ≥ 1/18 iff η ≤ 1/16. I checked this numerically.

### 3.12 §18, Thm 18.2: PASS (F2 inherited)

**(18.4), the L^∞ bound.**
- It applies Prop 14.2 to each of the ≤ 8^a signed faces of S Lemma 9.1.
- The selected reciprocal depends only on its link variables, since Ω_{v_j} = ±2x_j·y_j for a regular object (T986, D23 L960).
- μ^{-a} ≤ 1 for L large after δ, so δ^{-a} is never separated from L^{-2γa}.
- All exceptional links are layer-p chain links, so the full g is retained.
- The stated L^{3r} is a harmless overestimate of μ^{b₀} ≤ L^{2b₀}.

**(18.5) and (18.6), the A^{1/4} bound.**
- Lemma 18.1: the annular factor D(u) = −uϑ′(u), or ϑ(u) − ϑ(2u), has scale-invariant Schwartz moments, is Gevrey-2, and vanishes at 0.
- b₀ = 0: the object is a stem regular paired tree, since a stem couple always contains f^pr. Lemma 16.1 applies.
- b₀ = 1: the four cut components have total half-order m − 1.
  - Their A^{1/4}(ℝ³) product costs ≤ 2³ times the product of the norms.
  - Lemma 12.1 at θ = 1/4 is uniform in A.
  - The exceptional pair costs Cδ²L^{2γ} ≤ L².
  - Selections inside K_pre or K_in only add an annular scalar.

**Interpolation.**
- The common factor A₀ = C^{m+1}(C₁δ)^m G(𝒪) appears to power one.
- The exponent is 3rτ + (16d+2)(1−τ) ≤ (16d+5)r for r ≥ 1.
- The gain is M₂^{-aτ} ≤ M₂^{-a/18}.
- B is independent of M₂.

**(18.3), the local extension.** Disjoint bumps ψ(L(k−k₀)) give an X(ℬ)-type extension in the sense of T (locnorm), with cost L^{30d}·L^d. Then 31d ≤ 31dr.

**Signed collection.** It is specified before absolute values: maximizer cells × {upper, lower}, with multiplicity one. Only the pointwise bound splits faces. **No face is estimated in a Fourier norm**, so the norm-only counterexample o73 (15.3) does not apply.

### 3.13 §19, Thm 8.2′: PASS; sufficiency: PASS AFTER FIX (F1)
Item by item:
- **Item 1** is Prop 15.1, with §§10–11.
- **Items 2–3** are Thm 18.2 and Cor 15.2.
- **Item 4** is (19.2).
- **Uniformity** over 𝒫(2c_χC₁): the proofs use only reality and S^{40d,40d} → S^{8d,8d} bounds (T995–1000). There is no weighted profile norm beyond S^{40d,40d} (REFEREE-2 o63-4 respected).

### 3.14 §20, budget: PASS
- c_{8.2} = 47d + 5 per protected incidence.
- Σ_𝒪(47d+5)b_𝒪 ≤ 26(47d+5)P = (1222d+130)P.
- With c_{8.2} = 47d+5:
  - (20.3) B = 10606d + 546.01 + 26c_{7.3};
  - (20.4) B + 80d + 1/9 + 3 ≤ 494,000d³ + 10686d + 549.13 < 10⁶d³.
- Derivative patterns: 570,000d³ + 12346d + 633.2 < 2·10⁶d³. Correctly labelled arithmetic only.

---

## 4. Findings and fixes

**F1 (scope of the contract; already patched in o75 Rev. 1; a live obligation on C7.3).**
- Thm 8.2′ supplies M₂^{-1/18} only at selected occurrences inside protected regular objects.
- Pinned o75 (d7102c43) asked (C8.2) for the gain at every selected occurrence, and called skeleton faces "proved" (row 13).
- o75 Rev. 1 restricts (C8.2) to "inside a regular object" and assigns skeleton selected vertices to S Lemma 9.1 + (C7.3). With Rev. 1 the contract matches.

*Fix:*
- Keep the Rev. 1 wording.
- Make (C7.3) explicitly include the Lemma 9.1 faces at skeleton and residual selected vertices, with the reciprocal (9.1) retained.
- Qualify the tracker row for 8.2: "M₂^{-1/18} per selected occurrence inside a protected regular object".

**F2 (Lemma 16.1, Cor 15.2, (18.6): summing the exceptional pair over its box centers).**
- Lemma 16.1 is stated "at fixed spatial boundary data".
- (18.6) and Cor 15.2 sum the exceptional pair over the (CL)^{2d} points of **one** pair of unit boxes, but do not say why the box centers are summable.
- In the cut, the exceptional pair (x, y) determines the outputs of the side couples Q₁, Q₂. Summability needs their output decay, or the profile if a side couple is trivial.

*Fix:* state Lemma 16.1 for couples in the weighted form X^{1/4,30d,30d}. T's step (1) at T995 and (incohproof4) at T999 give it verbatim with the same L^d. Then add one sentence to Cor 15.2 and (18.6) saying that this decay sums the exceptional box centers. No exponent changes.

**F3 (Prop 15.1, g = 0, coherent paired trees: sup_k inside the Fourier integral).**
- The X^{η,30d,0} norm (T582) puts sup_k inside the λ-integral, and coherent trees have no k-decay for the T999 Sobolev step.
- The proof of Thm 10.1/11.3 gives, for each ν, a k-independent majorant: sup_σ of the coefficient's Fourier transform, times k-uniform lattice factors. So sup_k can be taken inside.

*Fix:* say so in Prop 15.1 and Lemma 16.1. It is moot for protected objects, which use fixed output plus (18.3).

**F4 (editorial).** §1, §7.4 and §8 still read "OPEN 8.2 is not closed" and "no value of c_d … has been proved". §§9 and 21 supersede them, but a reader of §1 is misled.

*Fix:* add a header line pointing to §19 and the STATUS line.

**F5 (editorial).** In (18.4), L^{3r} can be L^{2b₀}: the stem exceptional links are same-layer, and μ^{e−a} ≤ μ^{b₀}. This is a harmless overestimate.

**F6 (citations).**
- Lemma 16.1 "T1048": the bounds ‖S‖₁, ‖S‖_∞ are (incohproof18) at T1050.
- Lemma 14.1 "T1031": A(s) is (incohproof12) at T1030.

All the other cited lines say what is claimed. Checked: T612–613, T957–976, T981–1092, T1100–1110, T1145–1174, T1234–1246, T1725, T1954–1965, T2354–2379; D21 1305–1323, 1536–1544, 1586–1622, 2684–2705; D23 436–442, 949–1009, 1012–1100, 1155–1162.

**F7 (dependency note).** Thm 8.2′ uses o73 Prop 3.1, Lemma 12.1, Prop 13.1 and (13.4). o73 is unrefereed and its STATUS is OPEN. I verified these four pieces here: PASS.
- The live o73 (§§16–22) now consumes o82's Prop 14.2, Lemma 16.1, Thm 10.1, Lemma 11.1, Prop 15.1 and Cor 15.2.
- There is no circularity: o82's proofs use only o73 §§3, 5, 12–13.
- Because o73 reuses Lemma 16.1's X^{1/4} bound for residual selected vertices, F2 matters for o73 too.
- The paired-tree half of Lemma 16.1 and of Prop 15.1 is T's own positive-endpoint argument (T1084–1091: "allowing to lose a power of at most L^{4d}", then (incohproof27)–(28)). T states it tersely. o82 inherits it with time-independent filters inserted, and adds no new gap to it; the filters do not touch the boundary-derivative step. This is a source-level dependency, the same as T's proplayer1, not an o82 defect.

---

## 5. Constants and quantifier order

- **Losses.**
  - Per protected object: L^{(16d+5)r} at fixed output and L^{(47d+5)r} locally, r ≤ 2.
  - At most 4P objects have r ≥ 1.
  - Total ≤ L^{(188d+20)P} actual and ≤ L^{(1222d+130)P} charged.
  - c = 1222d + 130 ≤ 19,000d³.
- **No per-order L-loss.**
  - Factorials are absorbed per minor coordinate.
  - L^{4d} occurs per incoherent component of a protected object only, at most four of them.
  - The exceptional-pair sums are L² per pin.
- **Bases.**
  - The base C_{P,χ,ϑ}^{m+1} uses constants ≲₁ (T's convention: depending only on C₁; T615).
  - C_δ from 𝒟 and δ^{-1} from μ^{-1} are absorbed per unequal link, or into the L threshold.
  - (C₁δ)^m, not (C₂δ)^m.
- **Order of choices.**
  - η ≤ 1/16 with 200dη ≤ √η, fixed with η (T606: η small depending only on C₀).
  - η₀ < ε/8, then q > η₀^{-2}, fixed before δ.
  - The L threshold depends on δ and on the polylog exponent K_δ of N⁴.
- **Uniformity.** The bounds are uniform in centers, modulations, layer assignments, scales M ≥ L, the output, and 𝒫(2c_χC₁).

---

## 6. Refutation attempts that did not succeed

1. A Fourier-norm estimate of an individual child face, the o73 (15.3) obstruction: not used. Only pointwise face bounds and the whole-kernel A^{1/4} bound enter.
2. A selected vertex inside a side couple, or two selections in one object from different trees: impossible, because the stem inside a regular object is its chain.
3. An exceptional link of unequal layers costing incoherency: impossible, because every stem link is in layer p.
4. Interpolation constants depending on M₂, or a lost gain: B is M₂-uniform, and G(𝒪) appears to power one in both bounds.
5. Fold extension losing the pointwise bound: Ef = χχ·f∘F_D preserves sup and agrees with f on D̄.
6. Factorials at order N⁴ ≫ (log L)³: absorbed per coordinate with a δ-dependent L threshold. No base change.
7. δ^{-a} from the selected reciprocals: absorbed by L^{-2γa}, via μ ≥ 1.
8. A weighted norm of a boundary phase: never taken. The pin modulation is consumed by Lemma 12.1.
9. Output supremum inside the integral: (18.3) uses a finite lattice sum. For item-1 coherent trees, F3.
10. A hidden C₂^m: none. The only C₂ quantities are the layer range in Lemma 14.1, absorbed per unequal link, and the L threshold.

STATUS: REFEREED — 0 FAIL. Thm 8.2′ PASS. Sufficiency PASS AFTER FIX (F1: scope "inside a regular object", matching o75 Rev. 1; skeleton-selected faces remain a C7.3 obligation). Statement-level fixes F2 (couple output weight / exceptional box summation) and F3 (sup_k majorant for coherent trees); editorial F4–F6; dependency note F7.
