# Referee report 2: resolutions o63, o102, o75 (`flowerest1`, 1/2 < γ < 1)

Referee: independent, refute-first (wt-orch request, 2026-11-07). Read-only on all other files. No Lean, no git.

(Complete. The summary table is §5; the cross-cutting notes are §4.)

## 0. Pins

Each file was copied into the scratchpad at first read (13:38 UTC) and hashed from that copy.

| File | sha256 |
|---|---|
| o63/RESOLUTION.md | `a50e0f93d68ac6fab7dfbfd59efb5808a1dc9717b391475c0d29d3cde7ddebc4` |
| o102/RESOLUTION.md | `772bac47097eb4c307b0df4993007857df23c5594a9949e5e03d6cfce4a555ab` |
| o75/RESOLUTION.md | `d7102c43c5c7f738c87d611312d584b3b6ee782e0a7c844b6ff1e9beb0b74eb8` |
| SUPPLEMENT-v1.md | `ddd81fe1…74d7` (matches the pin) |
| COMMON.md | `a165bad5…` (matches) |
| ref/REFEREE.md | `c31ee38a…d6d` |
| o83/RESOLUTION.md (cross-check only, pinned 13:54) | `7194624768921930caf73ace73bfde11c6b7e967402c1cae19aeb84d337dd014` |

At the end of the audit (about 14:00 UTC) I re-hashed the three refereed files and the supplement. No drift.

- The sources match their pins: T `493eef6b…727cb`, D21 `50d0e236…fe402`, D23 `c7e47dfa…35475`.
- o75 cites O63 as `c28aad09…2ad9`, an **earlier** revision of o63. The version refereed here is `a50e0f93…`. The parts o75 uses (Theorem 6.3′, (5.1), Prop 10.3′, the profile class 𝒫(2c_χC₁)) are present in that version in the form o75 quotes. I found no dependency on text that changed.
- Notation: "S" is the supplement, "RR" the first referee report, "T/D21/D23 n" a source line.

---

## 1. o63: Theorem 6.3′, Lemma A (one Lagrange extrapolation), Proposition 10.3′

### 1.1 What is claimed

The weighted order-n family is S_Θ[F] = Σ_𝒢 Σ_𝔇 Θ(𝔇) ∏_π F_{q_π}(k_π), one profile factor per non-cap leaf pair. Here Θ carries everything that does not depend on the profiles: normalization, signs, ε, time integrals with pins, weights and truncation labels.

The claim:
- Replace F by F·w_{ρ,z}, with w_{ρ,z} = χ(·/ρ) + z(1 − χ(·/ρ)).
- On the support, each decoration's profile product is a polynomial Π(z) of degree ≤ n with z^P | Π.
- One real Lagrange extrapolation from n+1 nodes in [0, Z] to z = 1 then gives Z^{−P} at cost 8^n.
- Z ≈ ρ^A with A = 4Λ (plus 80d in the shell case). The profiles F w_{ρ,z_r} stay in 𝒫(2c_χC₁) by Lemma B.

### 1.2 Checks performed

**(a) "At least P pairs have |k_π| ≥ 2ρ on the support" (Lemma C(iii)–(iv)): CORRECT.**
- *Leaves by tree.* Every non-flower leaf of the expanded garden belongs to exactly one original tree j. Lower-layer gardens are inserted at frontier leaves of a single original tree, and their trees are rooted there (T2261; ansatz T698).
- *One high leaf per tree.* Conservation gives k − ζk′ = Σ_{ℓ∈𝓛°_j} ±k_ℓ in every tree. Each tree has |𝓛°_j| = 2a_j ≤ 2n non-flower leaves. So:
  - in case (a), ρ = K/(4n) puts a leaf with |k_ℓ| ≥ K/(2n) = 2ρ in every tree;
  - in case (b), H_{j,M₁} ≠ 0 gives a frontier vertex with |k_v| > M₁/2 (S (3.1), χ = 1 on |x| ≤ 1). Its descendant leaves number ≤ 2n, so one has |k_ℓ| > M₁/(4n) = 2ρ.
- *Pair count.* The 2P high leaves lie in distinct trees. A pair has two leaves, so at least P distinct pairs contain them, whether or not some pair lies inside one tree. The flower–cap pairs carry the input 1 and are excluded from Pr.
- *Vanishing order.* On |u| ≥ 2ρ, χ(u/ρ) = 0 and w = z exactly. So Π(z) = z^h ∏(affine) with h ≥ P.
- *n ≥ P.* Every original tree of 𝔛_reg has order ≥ 1 (S §1, order-zero convention). The flower parent is a branching node, so n ≥ 2P.

**(b) Lemma A, the coefficient bound: CORRECT, verified independently.**
- |coefficients of ∏_{s≠r}(nx − s)| ≤ coefficients of ∏_{s≠r}(nx + s).
- Their sum is ∏_{s≠r}(n+s) ≤ (2n)!/n!.
- Dividing by r!(n−r)! gives binom(2n,n)·binom(n,r). Summing over r gives binom(2n,n)·2^n ≤ 8^n.
- For Z ≥ 1, |β_r| ≤ Z^{−P} Σ_i |[x^i]ℓ_r|.
- The identity Π(1) = Σ β_r Π(z_r) holds exactly because the coefficients c_i, i < P, vanish.

I re-ran both claims in exact rational arithmetic (script in my scratchpad):
- the bound Σ_r Σ_i |[x^i]ℓ_r| ≤ binom(2n,n)2^n for n ≤ 25 (maximum ratio to 8^n is 0.375, as o63 states);
- the identity and the Σ|β_r| ≤ 8^n Z^{−P} bound in 200 random trials (n ≤ 12, all P ≤ n, rational Z ≥ 1).

The base 8^n is absolute. It is not raised to any Λ-dependent power: there is a single extrapolation. So the R47 objection (P-1) to iterated non-central nodes does not apply.

**(c) Lemma B and Lemma D (norms): CORRECT.**
- The low part F·χ(·/ρ) costs c_χ for ρ ≥ 1.
- The high part is supported in |u| ≥ ρ, which gives the ρ^{−A}‖F‖_{S^{40d,40d+A}} factor.
- With Z = ρ^A C₁/C_♯(A), every z ≤ Z gives ‖F w_{ρ,z}‖_{S^{40d,40d}} ≤ 2c_χC₁.
- Lemma D needs 40d + A ≤ Λ_q for all q ≤ p, with A = 4Λ + 80d. We have 4Λ + 120d ≤ 40dΛ = Λ_p ≤ Λ_q since Λ ≥ 40d (T611). This holds, and ‖𝓡_q‖_{S^{Λ_q,Λ_q}} ≤ L^{−θ_q} (T695) covers the remainder part.
- The φ part is a C₂-type constant (Schwartz bound on [0, τ_*]). It enters only C_♯, hence only C_{P,δ}, never the base.

**(d) Constants and quantifier order: CORRECT.**
- The base is 16c_χ, with c_χ = c_χ(d, χ), so it is δ-independent.
- (1 + n)^{(8Λ+80d)P} is a δ-dependent polynomial. This is allowed by (6.5) and absorbed by S Lemma 10.1.
- C_{P,δ} = (C_♯/C₁)^P(40κ)^{(8Λ+80d)P} is fixed after δ and before L.
- There is no power of L, so c_d = 0.
- Homogeneity, 𝓑_Θ(2c_χC₁) = (2c_χ)^n 𝓑_Θ(C₁), is exact (n pairs, one factor each). So C₁ need not be enlarged and the choice of ν and δ is not disturbed.
- I checked every branch of (2.2a)/(2.2b) (Z ≥ 1, Z < 1, K ≥ 4nM₁). The stated constants dominate in each.

**(e) Is the extraction a forbidden regrouping? NO.**
- (2.1) is an identity of integrands, decoration by decoration, with coefficients depending only on (n, P, Z).
- Each evaluation S_Θ[F w_{ρ,z_r}] is the complete family with one common real profile tuple at every pair, which is exactly what S Lemma 5.2 and `proplayer4` permit.
- Nothing is discarded, so S Lemma 9.4's warning does not apply.
- The class form (G) holds for every partition by profile-independent data, for the same reason.

**(f) Does the downstream use any property of F beyond reality and the S^{40d,40d} bound?**

I checked every place where the profiles could enter more strongly.
- *T2069.* After T2065–2067, the main estimate uses only "F_q bounded in S^{40d,40d} by C₁". T995 weakens this further to S^{10d,10d}. T1173 asks for real inputs bounded in that regularity space.
- *T2065.* This is the only use of the heavy weight ⟨k⟩^{4Λ}F_q, and it serves exactly the external decay that 6.3′ now extracts. In the flower case no k-derivative is needed (T2067 concerns couples, R = 1, in `layergarden`).
- *`approxnt` (D23 984–1009).* It needs ‖Ŵ‖_{L¹} + ‖∂̂W‖_{L¹} ≤ (C⁺)^n for the localized amplitude. This is controlled by finitely many derivatives of the profile, which S^{40d,40d} supplies with the same C₁-type constant.
- *ansatz5 (T702).* It is used in T only for the remainder terms (T803–807), not inside the `layergarden` reductions. A profile change therefore never needs an inductive black box.
- *Coherent main term.* The approximation φ(δp) ≈ F_p (T1247, `proplayer3`) is used only for the coherent couple main term 𝒰_n of `layergarden`, which has no counterpart in the flower moment.

So (5.1) is not stronger than the unmarked estimate as T proves it. This is the interface I-6.3, correctly recorded.

**(g) Proposition 10.3′: CORRECT as a conditional.**
- Plain and bottom-first versions take (2.2a); Lemma 9.5 pays the bottom M₁ factor.
- Nonbottom versions satisfy (Hb) and take (2.2b).
- M₂ enters only through G₂ in (5.1).
- The base D′_P = 16c_χD_P is δ-independent.
- The 𝔜/𝔚 restriction n ≥ N + 1 is a property of 𝔉_n, untouched by (2.1).
- As RR noted for Prop 10.3, the OPEN 7.3/7.5/8.2 hypotheses are logically idle in this proof. The real input is (5.1).

### 1.3 Findings (none fatal)

- **o63-1 (wording; Theorem 6.3′(a)).** Part (a) is stated "no hypothesis on W". When W contains a nonbottom shell, the assembly uses (b), which is correct. When W contains A_{j,L} (bottom), the M₁ factor is paid by Lemma 9.5. The text says this in §5; the theorem statement should say it too.
- **o63-2 (citation; §1.1).** The frozen derivative and † variants (T2327, T2331) are said to "only change Θ". For † (sibling momenta fixed), Lemma C(ii)–(iv) still holds termwise, since conservation is unaffected. But this is outside `flowerest1` (RR M4) and depends on a campaign audit not checked here. Mark it as a remark, not part of the theorem.
- **o63-3 (interface to be enforced).** I-6.3 says the downstream bound must hold uniformly over real profile tuples in 𝒫(C₁), with constants depending on C₁ only. This is the single point where 6.3′ shifts weight to the downstream items. Every downstream contract (C7.3, C8.2, o83, o104) must state it. o75 does so (§2.1, §8 (C7.3)).
- **o63-4 (scope; shared with S Lemma 5.1, not specific to o63).** The modified profiles F w_{ρ,z} are bounded in S^{40d,40d} by 2c_χC₁ but **not** in S^{Λ,Λ}: their high-weight norm is ≈ Z. Any downstream argument that silently uses a weighted norm of the profile beyond S^{40d,40d} must be redone. I found none in T or S (see (f)). The owners of OPEN 7.3/8.2 should be told that "the profile is Schwartz" is no longer available.

**Verdicts.**

| Item | Verdict |
|---|---|
| Theorem 6.3′ | **PASS** (editorial o63-1, o63-2) |
| Lemma A (single Lagrange extrapolation, Σ|β_r| ≤ 8^n Z^{−P}) | **PASS** (independently verified) |
| Proposition 10.3′ | **PASS** as a conditional, subject to I-6.3 (o63-3, o63-4) |

---

## 2. o102: Theorem R (weighted remainders)

### 2.1 Checks performed

**(a) Definition of the remainders.**
- (2.3)–(2.4) match T2288/T2290 and S Lemma 2.2.
- Pairs give F_p + 𝓔_p (T693).
- Higher blocks give Σ_{n′≤N_p}𝒦_{p,n′} + 𝓔̃_p (T698, T702).
- Block sizes are ≤ 2P(6N+2) ≤ 2R_p.
- ℰ^{(1)} contains every term with at least one error factor. ℰ^{(2)} is the main part of total order n₀ + Σn′_β > N⁴.

**(b) Lemma R.1 (time integral; the M₂ gain).**
- The original-tree times all lie in (p, t). For a fixed decoration and fixed other times, t_v ranges over an interval, and the integrand depends on t_v only through e^{iω_v t_v}.
- |∫ e^{iωu} du| ≤ 2/|ω|, and the remaining volume is ≤ 1.
- The selected v may depend on the decoration. This is legitimate because the whole remainder is bounded in absolute value (S Lemma 9.4).
- No face decomposition is needed. f^pr ∉ 𝒮_j, so the selected time is never the pinned one. A pinned child time s is just one of the A_v candidates.

**(c) Lemma R.2/R.4 (pointwise extraction).**
- Per tree, ⟨K⟩ ≤ 2n_j max⟨k_ℓ⟩. Raised to the power 2Λ and multiplied over the 2P trees, this gives ⟨K⟩^{4ΛP}.
- (S1) gives a leaf with |k_ℓ| > M₁/2 in every tree, hence M₁^{80dP} ≤ 2^{80dP} ∏⟨k_ℓ⟩^{40d}.
- Each leaf is charged ≤ 2Λ + 40d. A pair variable is charged ≤ 4Λ + 80d against ⟨k⟩^{−Λ_p}.
- Λ_p − 4Λ − 80d ≥ 1600d² − 240d ≥ d + 1, because Λ = Λ_{p+1} ≥ 40d for p ≤ 𝔇 − 1.
- The decoration sum is then (C_dL^d) per free variable, at most 2n₀ free variables. Dropping the root indicators is legitimate after absolute values.

**(d) Bookkeeping.**
- Tree tuples ≤ 8^n·(2n+1) per tree.
- Partitions ≤ |B|^{|B|}.
- Error subsets ≤ 2^{|𝒫|}.
- Pair constants C_F^{|𝒫|}: C₂-type, raised to n₀ ≤ 8PN.

All of these are e^{O(PN log N)}. L^{(d+1)n₀} ≤ e^{8(d+1)PN²} with log L ≤ N.
- *ℰ^{(1)}* has e^{−N_p}, with N_p = N^{1600d²}.
- *ℰ^{(2)}* has Σn′ ≥ N⁴/2, and the composition count binom(m+h−1, h−1) ≤ 2^{m+h−1} with 2δ^ν ≤ 1/2 gives 2^h·2^{−N⁴/2}.

Both dominate (L5)/(L6). The C₂^{n₀} and L^{(d+1)n₀} factors are **not** forbidden here: n₀ ≤ 8PN is bounded, and they are paid by super-polynomially small factors. This is exactly T804/T807.

**(e) Case analysis of (R.1).**
- *M₁ = L:* the factor L^{−80dP} is paid by the margin L^{−(80d+2)P}.
- *M₂ > L:* τ_j ≤ M₂^{−1} by (L1), so ∏τ_j ≤ M₂^{−2P} ≤ M₂^{−P/9}, uniformly in arbitrarily large M₂.
- *M₂ = L:* L^{−P/9} is paid from the margin.
- The L^{−P} margin and the factor 1/4 survive.
- The 𝔜/𝔚 factor e^{−100N} is included.

### 2.2 Findings (none fatal)

- **o102-1 (wording; §6 "Quantifier order").** "C₀, η, C₁, ν, δ, then P" contradicts COMMON's "P is chosen before δ". It is harmless: Theorem R holds for every P ≥ 1, and only δ^ν ≤ 1/4 is used, which is P-independent. Fix the sentence to "Theorem R holds for every P; its only δ-condition is δ^ν ≤ 1/4."
- **o102-2 (scope).** §8.1 (absolute convergence, the bound |a_k(p)| ≤ 2⟨k⟩^{−(5/4)Λ_p}e^{3N_p} from T782/T793) is a hypothesis of S Lemma 2.2, not of Theorem R. It is correctly labelled as such. I did not re-verify the Z-norm weight in T793.
- **o102-3 (remark).** §8.4 (derivative patterns, †) is outside `flowerest1`. Its claim is plausible: one more substituted time leaves a modulus-≤1 integrand on volume ≤ 1. But it should stay a remark until o104 adopts it.

**Verdict.**

| Item | Verdict |
|---|---|
| Theorem R (and Theorem R′, Lemma R.0–R.5) | **PASS** (editorial o102-1) |

---

## 3. o75: Theorem 7.5′, Lemma F, the budget table §7, the conditional 10.3 count §8

Sources read for this section:
- T1295–1535: molecules, blocks, `block_clcn`, `cnblock`, vines, twists, LF twists, `layerlad`, `layervine`;
- T1627–1690 (`sumint` Step 2, `timeintgap`, the enlarged-interval variant T1681–1689) and T955–977 (`lemlayer1/2`);
- T1924–2256: Stage 1, `ladderl1new`, `ladderl1old`, `subpro`, Stage 2, `excessprop1`, `finalmol`, `lgmolect`, the
  proof of (finalcount1), the interpolation and the class count;
- T2257–2305 (the flower section);
- D23 1670–1676, 1731–1747 (original `subpro`) and 1784–1803 (Prop 9.4);
- errata E5, E9, E20, E21, E22, E28, E31, E35, E36.

I also read o83/RESOLUTION.md, pinned at `71946247…d014` (13:54), read-only, because it contains an independent check
of Lemma F. That file is under separate referee (REFEREE-83). I use it only as a cross-check, not as an input to my
verdicts.

### 3.1 Theorem 7.5′ (marked vines unspliced; modified `subpro`, clauses 1–9)

**What changes relative to T.**
- A vine of 𝒱 is *marked* if its twist-active set 𝐀(𝕍) meets the protected set Π (b = |Π| ≤ 26P).
- Marked vines are neither twisted nor spliced. The unmarked vines of each SG chain form *runs*, which are spliced
  into hinges.
- The unspliced members of affected chains are the *survivors* 𝒞_E (N_E ≤ 2b). Their joints form B (|B| ≤ 4b).
- Stage 2 gains an Operation 1E that removes the survivors.

**Answer to "does leaving marked vines unspliced preserve T2042–T2047?"** Not verbatim, and o75 does not claim that it
does.
- E31's configuration refutes the verbatim T2045: an unspliced special-node SG vine lies outside 𝒞₁, contains no
  hinge and has no container.
- o75 restates (4) and (6) with 𝒞₁ ∪ 𝒞_E and B, and adds (6′). That is exactly the missing structural premise E31
  identifies.
- With this restatement I checked every clause against the source. The details follow.

**(1) Connected, n_sb atoms, 2n_sb − R bonds: CORRECT.**
- Splicing any subfamily of (CL) blocks removes completely paired regions inside one tree (T1349(iii)).
- So 𝒢_sb is still an irreducible garden of width 2R, and `propcplmol` (T1304) applies verbatim. T2113's
  χ = n_sb − R + 1 is untouched.

**Bookkeeping (4.6): verified by direct computation.**
- Removing a survivor with s interior atoms (e_S = 2s + 2) with both joints ε-atoms gives ΔD = 0.
- If one joint is an already-cut degree-2 atom (a re-cut), the remnant is isolated and ΔD = +2.
- Hence F_im ≤ R′ + N_E, where R′ is T's E9-repaired bound.

**(2) Collections, hinge count, triple bonds: CORRECT.**
- 𝕄_sk has no triple bond (D23 1741(c)), so a triple bond needs a merged endpoint.
- The only triple bonds touching a survivor arise in an HVC whose last survivor is a vine (I) and whose extra bond e*
  joins the end hinge. Survivor removal deletes that triple bond.
- Hinges of m_W = 0 chains keep E22's designated-pair repair.
- *Wording fix 75-W1.* In an HVC whose image is one survivor plus e*, that survivor is an SG **HV** in 𝕄_sb, not a
  vine. Its removal is then T's HV case (ΔF = 0, T2179). Clause (2) and Lemma 3(ii) should say "SG vines, or an SG HV
  when the image of an HVC is a single survivor".

**(3) Degenerate atoms tame: CORRECT.**
- ε_v is kept at every non-hinge atom, survivors included.
- So ε ≠ 0 forces k_{𝔫₁} = k_{𝔫₂} = k_{𝔫₃}.
- Missing bonds carry k or k′.

**(4) Uncovered SG objects: CORRECT as restated.**
- (P) and (Q) are right: a vine-like object of 𝕄_sb avoiding H is one of 𝕄_sk, by internality of the block
  conditions (T1328).
- Case (d) is right: inside the image of W ∈ 𝒲_E, a connected U meeting two survivors must pass through a shared joint
  (in B) or the extra bond (endpoints in H ∪ B).

**(5) Hinge pairs: CORRECT.**
- When m_W ≥ 1, every run is adjacent to a survivor, so its designated pair can be chosen in that survivor. That pair
  is SG with the chain's gap.
- No hinge is a joint of both a 𝒞₁ object and a survivor, since objects of 𝒞 are disjoint.
- *Fix 75-F1 (missing rule).* A **non-hinge** joint J ∈ B shared by two consecutive survivors also needs a single
  designated pair (requirement (e)). The rule "choose it in the survivor removed first" is stated only for hinges.
  Extend it to every shared joint in B. Since both survivors have the same gap, requirement (f)'s single label Q_J is
  consistent.

**(6) Hinge configuration (U ∩ B = ∅): CORRECT.**
- Every hinge of a 𝒲_E chain is a survivor's joint, hence lies in B.
- So an aligned hinge of U comes from an m_W = 0 chain, and the D23 1745 replacement argument applies verbatim.

**(6′) Objects meeting B: CORRECT.** I re-derived the remaining case.
- J is an outer joint of 𝕎′ (or the end hinge), and U uses J's bonds leaving W (possibly e*).
- Replacing U's aligned hinges by their runs gives an SG vine-like object of 𝕄_sk. It contains an atom of W and an
  atom outside W.
- By Lemma `vinechainlem` it lies in a single object of 𝒞. That object must be W, a contradiction.
- If U contains an interior atom of a survivor, it contains a survivor bond in either position. So the three
  alternatives are exhaustive.
- (6′) is what makes Prop 4.8's vine-component argument work: every SG vine component of 𝕄_fin is destroyed or is
  T's own case.

**(7) Counting: CORRECT, with ledger fixes.**
- *Survivor removal (Lemma 5), ΔF = 0.* This is D23's Step-1 computation (D23 1797–1801). It is molecular, so it
  applies to (CL) survivors exactly as to the (CN)/HV objects of DH23.
- *Survivor removal, ΔF = 1.* This is T2169–2177.
- *The re-cut, a step type that exists in neither T nor DH23.* In T, Operation-1 objects are disjoint, so no
  Operation-1 removal acts on an already-cut atom. I checked the per-step bound directly:
  - at a degree-2 joint J, J's own (c_J, β_J) fixes k_{ℓ₁} − k_{ℓ₂} and confines |k_{ℓ₁}|² − |k_{ℓ₂}|²;
  - so T2174's count L^{d−γ+γ₀+η³} holds uniformly in the gap (all |r| ≥ L^{−1});
  - Δχ = −(m−1) as in T2169, so I ≲ L^{γ₀+2η³}, within (excesseqn2+).
- *Totals.* The extra p⁺_op ≤ N_E (L^{γ₀} each) and the extra imperfect components ≤ N_E (L^{2γ₀+5η²} each) give
  L^{(3γ₀+5η²)N_E} ≤ L^{2N_E}, since γ₀ = 1 − γ < 1/2. I confirm this against (together2) (T2207): the α and β label
  factors cancel exactly as in T.
- *Fix 75-F2 (ledger; E20/E21/E28).* State explicitly that:
  - the isolated half of a re-cut joint keeps the atom's α/β label;
  - its α label factor is refunded once, at the final molecule (isolated imperfect component, A = 1, admissible
    because L^{−(γ+3η)/2}Q^{−1} ≥ L^{(γ−5η)/2});
  - the re-cut step itself is bounded without a refund, as above.

  This keeps R38's "paid once, refunded at most once" (E20), E21's live-hit ι, and E28's literal isolated-half
  convention (ΔF = 1, isolated half kept), which is the convention o75 in fact uses.
- *Fix 75-F3 (R = 1 wording).* The claim that the extra imperfect components "contain no low-degree ε-atom" is not
  justified: a survivor removal with ΔF = 1 can split off the component holding a root atom of degree 3.
  - The conclusion still holds. Each extra component contains an α/β remnant, so T2197's imperfect-branch
    interpolation (A ≲ L^{−η⁴ρ+C₀η²(V_α+V_β+Z)}) applies.
  - The bounded Z ≤ 2 is absorbed by one α factor L^{γ/4} or one β factor L^{γ₀}.
  - Replace the sentence by this argument.

**E20 ghost-triangle interaction (asked for specifically): no new failure.**
- 1E runs before Operation 2. After 1E, the remnants of internal joints are isolated (degree 0) and cannot enter a
  triangle.
- The only new ghosts are the degree-2 remnants at the outer joints of 𝕎′. These are the same type as T's 𝒞₁ joint
  remnants.
- So R38's repair (γ > 1/2, 8η ≤ 2γ − 1 for two α-ghosts) covers them with no extra L-loss. Only the count of ghosts
  grows, by ≤ 2N_E, and the repair is per ghost.
- o75's Audit note B is correct.

**(8)–(9) Crude bound, interpolation, gains: CORRECT.**
- Splitting at S_split = B ∪ Π_sb (|S_split| ≤ 6b) gives q′, m′, g′ as stated. The extra factor is
  L^{(γ₁−√η)2|S|+20d|S|+40d|S|} ≤ L^{(60d+2)|S|}.
- The interpolation with θ = 40ν gives ≤ L^{(60d+2)|S|+2N_E}·C_ϑ^n, with C_ϑc_χ² δ-independent.
- The sharp form needs ν ≤ 1/(240(60d+2)). This is compatible with the quantifier order: ν may always be decreased
  before δ is chosen, and a smaller θ only helps T2220–2225.
- Runs carry L^{η⁷} each, beaten by L^{−η⁶q_sk/2} because every hinge is an SG atom outside the interiors of
  𝒞₁ ∪ 𝒞₂ ∪ 𝒞_E, so q_sk ≤ p_sb.
- Unmarked gains are retained.

**Lemmas 1 and 2 (disjointness, twist invariance): CORRECT.**
- *Lemma 1.* I checked it with D23 1673: u₁^j = u₂^{j+1} and u₁₁^j = u₂₃^{j+1}, so 𝐀(𝕍_j) lies under the free children
  of 𝕍_{j+1}.
- *Lemma 2: the cases.* I re-checked each protected type:
  - Root children: a root at u₁ marks a vine (I).
  - f^pr = u₁ forces both flower siblings into 𝐀.
  - A root child at u₁ (not in 𝐀) is correctly left unmarked: the subtree count at u₁ is preserved by T1476.
  - u₃ or u₄ protected marks the vine. This is the case that genuinely needs it, since u₂ moves between them.
  - Free-subtree swaps leave every protected datum intact.
  - In the M₂ version, 𝐀 ∩ stem = ∅ by S Lemma 9.2 (RR-corrected).
- *Lemma 2: the design.* o75's mark is finer than T2297's "vine containing a special node", and that is correct.
- *Lemma 2: E35/E36.* The congruence′ classes need no cut-label fibres for special-node vines, so that part of E35's
  R63/R64 programme is bypassed. E36 is handled by S Lemma 5.3 and RR's layer remark.

**Citations to add (75-C).**
- E31: the restated (4)/(6)/(6′) is precisely the repair E31 calls for. It is a different route from R61, which
  detaches protected subtrees as capped trees. wt-orch should record which route the formalization follows.
- E22 (hinge triple bonds).
- E28 (degree-2 cuts).
- E35 (faces remain OPEN 7.3).

**Verdict: Theorem 7.5′ PASS AFTER FIX.** The fixes are 75-W1, 75-F1, 75-F2, 75-F3 and 75-C. None changes the
statement or a number.

### 3.2 Lemma F (stem filters on ladder rungs as time translations)

**Mechanism: CORRECT.**
- By T1968 and evenness, ϑ(Ω_{𝔫(v)}/R_v) = ∫ϑ̂(ξ)e^{2πiξ(−Γ_v+Γ_v⁰)/R_v}dξ.
- Combined with the phase e^{πiδL^{2γ}(−Γ_v+Γ_v⁰)t_v}, this is the unfiltered phase at t_v + τ_v, with
  τ_v = 2ξ/(δL^{2γ}R_v). The time-modulation factor gives a unimodular constant.
- In the E5 kernel core the modulus is inside the time integral and the ordering is dropped (E5 steps 1–2). So Fubini
  and Minkowski give (4.8), and only the box moves.
- RR's T1603(iii) caution does not arise.
- The filtered core stays multiplicative over disjoint ladders, because a filter at a ladder atom depends only on
  that atom's Γ_v. So E5 steps 3–4 (gluing) are unchanged.
- In the flower setting the top-layer interval is (p, t) ⊂ [p, p+1], and the integrand is nonnegative. So
  enlargement is harmless. Pinned and face atoms lie in S_split, hence are never ladder atoms.

**Dependence on the time box (asked for specifically).**
- The rung estimates use the box only through (B1) unit length, (B2) the window |t_w − t_v| ≤ 𝔇 + 2, and (B3) the
  overlap measure.
- (B3) holds for **arbitrary** unit intervals in the form μ(v) ≤ min(1, |v|/(δL^{2γ}) + |I_v ∩ I_w|). I verified this:
  for adjacent layers translated by τ_v, τ_w, μ = max(0, 1 − |1 + τ_w − τ_v − h|) ≤ |h| + |τ_v| + |τ_w|.
- This is the same device T itself uses for enlarged overlapping intervals at T1681–1689 ("replace (timeintgap)
  with |t − q| ≤ 2L^{−β} + |t − s|"). Cite it.
- Region by region:
  - *|ξ| ≤ L:* |τ| ≤ 4/(δL^{2γ}) ≤ 1/4. The incoherent gain degrades to (δL^{2γ})^{−1}(1 + |ξ_v| + |ξ_w|), which
    is still ≤ L^{−(γ₁−√η)}·(1 + |ξ|), since 2γ > 1 ≥ γ₁. The |v| ≥ L region is unchanged (`lemlayer2`, and its
    C₂-dependence on the window is absorbed by L^{η−√η}).
  - *|ξ| > L:* the trivial rung bound times ∫_{|ξ|>L}|ϑ̂| ≤ C_N L^{−N} suffices.
- **The real dependence is the input, not the lemma's own steps.** The E5 kernel-core bound is proved (Lean
  `ladderL1Gate`) for the **layer** box only. Lemma F applies it to 𝔅 + τ(ξ), which is not an instance. This is o75's
  own Audit note A, and o83 calls it G1.
- T's `ladderl1new` is a sketch (T1989). o83 records two further gaps in it that afflict the untranslated bound too:
  - G2: the sharp 𝒵_v indicators are not admissible Poisson modulations;
  - G3: "bound the last rung trivially" does not factor the sum under global conservation.

  I checked G3's premise against T1989–1991 and agree with it: the last remaining sum is coupled to all rung variables
  through conservation. These are T-side errata candidates, not defects introduced by Lemma F.
- *Fix 75-LF.* State the input as a hypothesis:

  > **(E5′)** the kernel-core bound (redladder2) holds for every product 𝔅′ = ∏I_v of unit intervals with
  > I_v ⊂ [−1, 𝔇+1], with the incoherent factor min{1, L^{−(γ₁−√η)} + |I_v ∩ I_w|}.

  Then Lemma F is proved relative to (E5′). o83 Theorem K is a proof of (E5′) that also fills G2–G5. Its referee
  verdict, not mine, decides whether the hypothesis is discharged.
- *Minor.* R_v ≥ L/2 is more than needed (o83 relaxes it to R_v ≥ 1). The only filters met are the unselected
  telescoping factors, at scale M₂ or M₂/2 ≥ L, or L in the bottom block.
- *Scope.* Lemma F covers ladder atoms only. Covered elsewhere:
  - stem filters at non-ladder atoms: trivial bound |ϑ| ≤ 1;
  - stem filters at hinge tops: S Lemma 9.3;
  - stem filters in the count: S Lemma 9.4;
  - stem filters inside regular trees: E39, under OPEN 8.2.

  So RR's M2 is closed relative to (E5′). This duplicates o83's Theorem 8.3: wt-orch should keep one, and o83's
  version carries the proofs of G1–G5.

**Verdict: Lemma F PASS AFTER FIX (75-LF).**

### 3.3 Budget table §7

- **Arithmetic: checked.**
  - Row 9 is 4b = 104P.
  - Row 10 is (60d+2)·6b = (9360d + 312)P, or 26P in the sharp form.
  - Row 12: three exceptional variables per tree at L^{4d}, i.e. 24dP, plus the polylog (C_dρ)^{4d} with ρ ≤ Cn.
  - B = 9384d + 416.01 + 26(c₇.₃ + c₈.₂).
  - With c ≤ 19,000d³: B + 80d + 1/9 + 3 ≤ 988,000d³ + 9464d + 419.13 ≤ 10⁶d³. The last step needs
    9464d + 419.13 ≤ 12,000d³, which holds at d = 1 (9883.13) and hence for all d.
  - Derivative patterns, b ≤ 30P: 1,140,000d³ + 10,936d + 483.2 ≤ 2·10⁶d³.
- **Losses and bases.**
  - No L^{Cn} appears anywhere.
  - C₂^{22b} is n-independent, so it goes into E_{P,δ}.
  - Every exponential base (16c_χ, C_ϑ, c_χ, ‖𝓕ϑ‖₁, C^{(7.3)}, C^{(8.2)}) is δ-independent.
- **Completeness.** I looked for unlisted L-powers: the cap input, the Dirac trace (E30), the face substitutions, the
  frozen pin resonance, the Lemma 7.1 radius, and the hinge 80d·q_sk. Each is either in a row, inside the 7.3/8.2
  contracts, or absorbed exactly as in T.
- **Editorial fixes.**
  - STATUS.md says the budget "fits **iff** c₇₃, c₈₂ ≤ 19,000d³". It is "**if**": the ceilings are sufficient, not
    necessary. With the sharp row 10 the admissible ceilings are larger.
  - Row 21 (expansion errors) is now closed by o102 Theorem R, with zero B.
  - The contracts are charged per |Π| = 26P protected incidences, which is generous: 7.3's natural count is pins plus
    faces. Say so, so that the 7.3/8.2 owners know their real ceiling.

**Verdict: budget table PASS** (conditional on the contracts, as labelled).

### 3.4 The conditional 10.3 count §8

- **(i) Factorization over components: correct.**
  - Each original tree lies in one component.
  - Times, decorations, weights and labels are per tree.
  - The choices are ≤ (4P)^{4P}(n+1)^{2P}.
- **(ii)–(iii)** These are as in T2231–2235 and T2237. Regular components carry no 𝒰 subtraction, and protected
  regular objects go under the contracts.
- **(iv) Class count: correct.**
  - The garden count C₀^n(C₀ρ̄)!(C₀R)! is verbatim.
  - Survivors' layerings use `layerlad` plus C₂ per non-ladder atom, inside m_sb.
  - The lost units: L^{−νη ḡ_ret}C₂^{ḡ} = C₂^{22b}(C₂L^{−νη})^{ḡ_ret} ≤ C₂^{22b}, with no power of L.
  - L^{−νηρ̄}C₂^{ρ̄}(C₀ρ̄)! ≤ 1 by T2253.
- **(v) D_P is δ-independent,** given that the contracts' bases are.
- **(vi) Fix 75-§8 (attribution).** The M₂ gain does not come only from (C8.2).
  - For a selected vertex that is a skeleton atom, the gain (cδL^{2γ}M₂)^{−1} comes from S Lemma 9.1, and the face
    estimates are part of (C7.3). The table's row 13 already says this.
  - For a selected vertex inside a regular object, it comes from (C8.2) and (8.6).
  - Either way the count is 2P occurrences at M₂^{−1/18} ≥ M₂^{−P/9} in total, so no grouping of linked pairs is
    needed.
- **(G-ret) is a genuine new requirement on 7.3/8.2.** It is correctly flagged in Note D: at most 10 lost incoherency
  units per protected incidence. Without it D_P becomes δ-dependent, by RR's 6.3(ii) mechanism.

**Verdict: §8 PASS as a conditional** (on C7.3 with faces, C8.2, G-ret and (E5′)), after the attribution fix
75-§8.

---

## 4. Cross-cutting notes for wt-orch

1. **Assembly chain.** I find it sound as a conditional:
   - (1.1) ⇐ o63 Prop 10.3′;
   - o63 Prop 10.3′ ⇐ Theorem 6.3′ + (5.1) + o102 Theorem R;
   - (5.1) ⇐ o75 §8;
   - o75 §8 ⇐ Theorem 7.5′, Lemma F + (E5′), and the contracts C7.3 (including faces and G-ret) and C8.2.

   Everything outside those named inputs is proved.
2. **Interface I-6.3.** Every downstream contract must hold uniformly over real profile tuples in 𝒫(C₁): o73, o82,
   o83, o104, and (E5′). "Schwartz profile" is no longer available, because F w_{ρ,z} has a huge high-weight norm.
3. **E31 route choice.** o75's restated `subpro` with 𝒞_E is an alternative to ruling R61's excision. The two should
   not be mixed in supplement v2 without a ruling.
4. **o83 and Lemma F overlap.** Both close RR's M2. o83 also carries the box-robust core and the G2/G3 errata for
   T1989–1991.

---

## 5. Summary table

| Item | Verdict | Fixes |
|---|---|---|
| o63 Theorem 6.3′ | **PASS** | o63-1: state in (a) which version uses it; o63-2: † / derivative variants as a remark |
| o63 Lemma A (Lagrange extrapolation, Σ\|β_r\| ≤ 8^n Z^{−P}) | **PASS** | verified in exact arithmetic |
| o63 Proposition 10.3′ | **PASS** (conditional on (5.1)) | o63-3/4: enforce I-6.3 (profile uniformity over 𝒫(C₁); no Schwartz assumption) downstream |
| o102 Theorem R | **PASS** | o102-1: quantifier-order sentence ("for every P; only δ^ν ≤ 1/4") |
| o75 Theorem 7.5′ | **PASS AFTER FIX** | 75-W1 (HV survivor wording); 75-F1 (designated pair at shared non-hinge joints of B); 75-F2 (re-cut label ledger per E20/E21/E28); 75-F3 (R = 1 extra imperfect components: replace the "no low-degree ε-atom" claim by the α/β-remnant interpolation); 75-C (cite E31, E22, E28, E35) |
| o75 Lemma F | **PASS AFTER FIX** | 75-LF: state the box-robust kernel core (E5′) as hypothesis (Audit note A = o83 G1); cite T1681–1689; G2/G3 in T1989–1991 are T-side |
| o75 budget table §7 | **PASS** (contracts as labelled) | STATUS "iff" → "if"; row 21 now closed by o102; say that the contracts are charged per 26P |
| o75 §8 conditional 10.3 count | **PASS** (conditional) | 75-§8: M₂-gain attribution (skeleton selected vertices: S L9.1 + C7.3 faces; in-object: C8.2) |

**No FAIL.** Refutation attempts that did not succeed:
- a pair-count counterexample to "≥ P high pairs" (pairs inside one tree, lower-garden leaves, flower–cap pairs);
- a downstream use of profile decay beyond S^{40d,40d};
- a Λ-dependent exponential in the Lagrange cost;
- an L^{Cn} or C₂^n leak in Theorem R;
- a triple bond surviving 1E;
- an SG vine component of 𝕄_fin meeting B that escapes (6′);
- a re-cut step violating (excesseqn2+);
- a new ghost type in Operation 2;
- an overlap in translated incoherent boxes breaking the gain;
- an unlisted L-power in the budget.

STATUS: REFEREED — 0 FAIL; 4 PASS (6.3′, Lemma A, Prop 10.3′ conditional, Theorem R); 4 PASS AFTER FIX or
conditional (Theorem 7.5′, Lemma F, §7 table, §8 count); all fixes editorial or bookkeeping, none changes a statement
or a number. The open inputs remain C7.3 (with faces and G-ret), C8.2 and (E5′).
