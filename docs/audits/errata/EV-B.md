# EV-B: independent verification of E2d, E16, E18, E24, E26

Verifier: an independent refute-first check, run on 2026-11-10. I did not write these entries. I read the printed
sources first, reconstructed each claim from them, and tried to refute it. All computations below were redone with my
own scripts (Appendix). Nothing in the repository was edited or built.

**Sources checked.** TARGET `WKE-Longer_times_Final_arXiv.tex` (sha256 `493eef6b7dec448b…`, matches the pin); DH23
`Revision_Submit.tex` (sha256 `c7e47dfabf5a4cca…`, matches). Figures were read from the arXiv source images
(`references/src-2311.10082/vineAnnotated.png`, `Couples_CL.png`). Entries were read from
`origin/main:docs/ERRATA-AND-DEVIATIONS.md` at commit `636c5a46`. Every line number cited by the five entries was checked
and is correct.

## Verdicts

| Entry | Verdict | Class (entry → recommended) | Main corrections |
|---|---|---|---|
| E2d | CONFIRMED WITH CORRECTIONS | ERROR → MINOR | The scope is too narrow: Vine (III) (L1814, case "c, d same direction") and Vine (IV) have the same reversed sign. The signed `sumint` is the printed proof verbatim (the lemmas are symmetric under s ↦ −s). The scalar check proves only a global sign. |
| E16 | CONFIRMED | ERROR (keep) | Counterexample verified independently, including primality (item O5 of the notes). Two wording fixes. |
| E18 | CONFIRMED WITH CORRECTIONS | ERROR → MINOR | The literal claim fails for trivial objects, but the vanishing is used only for roots in layer ≥ L_{u4}+1, where no trivial object occurs. The "two other configurations" are not counterexamples to the printed text. Rewrite the Consequence. |
| E24 | CONFIRMED WITH CORRECTIONS | GAP (keep; borderline EXPOSITION) | The diagnosis is right. One sentence overstates: for the weights, an expansion over cross-tree leaf pairs never touches a vine interior. The twist-class obstruction is specific to the derivatives (L2067). The repair formula checks exactly. |
| E26 | CONFIRMED | ERROR (keep) | The identity is false as printed whenever a lower-child slot depends on its first clock. The repair is sound in outline and uses TARGET's own modulation tolerance. I did not referee the weighted flower version. |

Status line: `DONE EV-B E2d=CONFIRMED-WITH-CORRECTIONS E16=CONFIRMED E18=CONFIRMED-WITH-CORRECTIONS E24=CONFIRMED-WITH-CORRECTIONS E26=CONFIRMED`

---

## E2d: TARGET `vineest` Step 2, L1814 and L1817, the sign of the nonlinear core

### Pinned text

- L1814, (C-i), Vine (III): "If the bonds decorated by $c$ and $d$ have the same direction (which has to go from $w^i_1$
  to $w^i_3$), then we may define $(u^i_1,u^i_2,u^i_3)=(c-a,a-d,c-b)$. Then we have $\omega^i_1=2u_1^i\cdot u_2^i$, while
  $\omega_2^i$ equals $2u_1^i\cdot u_3^i$ in the first case, and equals $2u_3^i\cdot (u_1^i+u_2^i-u_3^i)$ in the second
  case. … The argument for Vine (IV) is similar, see Figure (C)."
- L1817, (C-ii), Vines (V)–(VIII): "… we have $\omega_1^i+\omega_2^i+\omega_3^i=0$ … Then we argue as above, with
  $(u_1^i,u_2^i,u_3^i)=(a-e,b-e,a-c)$ if bonds decorated by $a$ and $b$ have the same direction, and
  $(u_1^i,u_2^i,u_3^i)=(e-g_*,b-g_*,d-g_*)$ if they have opposite directions, then the same results will hold."
- L1820 (the consequence used): "their corresponding resonance factors are given by $2u_1^i\cdot u_2^i$ and
  $\Lambda^i\in\{2u_1^i\cdot u_3^i,2u_3^i\cdot (u_1^i+u_2^i-u_3^i)\}$, and $-2u_1^i\cdot u_2^i-\Lambda^i+\widetilde r\cdot\xi^i$".
- `sumint`, L1607: "$\Lambda_i\in\{\langle u_1^i,u_3^i\rangle,\langle u_3^i,u_1^i+u_2^i-u_3^i\rangle\}$". The phase in
  (sumintI1) is $(\tau_1-\tau_3)\langle u_1,u_2\rangle+(\tau_2-\tau_3)\Lambda_i+(\tau_3-t)\langle r,\xi_i\rangle$.

### Reconstruction from the source

- **The conventions.** At a degree-4 atom, $\omega_v=\zeta_{\mathfrak n}\Omega_{\mathfrak n}=-\Gamma_v$, where
  $\Gamma_v=\sum_{\ell}\zeta_{v,\ell}|k_\ell|^2$ (L1320, (molegammav); L1311, (defomegadec)). Conservation is
  out − in = 0, and $\Gamma_v$ is invariant under a common translation of the bond vectors.
- **The directions in Figure (D).** Figure (D) has a double bond (a, b) between w₁ and w₂, a double bond (c, d) between
  w₂ and w₃, a single bond e between w₁ and w₃, g_* leaving w₁ and g_* entering w₃.
  - If a and b have the same direction, both must enter w₁: w₁ already has g_* outgoing and has room for at most two
    outgoing bonds.
  - This forces e: w₁→w₃ and c, d: w₃→w₂.
- **The resonance factors.** Take g_* = 0, so e = a + b and d = a + b − c. Then

      Γ_{w1} = 2a·b,   Γ_{w2} = −2(c−a)·(c−b),   Γ_{w3} = 2c·(c−a−b),   sum = 0,

  exactly as the entry states (script `e2d.py`).

### Attempts to refute

1. **Global sign.** With the printed coordinates (u₁, u₂, u₃) = (a−e, b−e, a−c), we get 2u₁·u₂ = 2a·b = Γ_{w1}, so
   ω_{w1} = −2u₁·u₂. On its own, this is a global sign, removable by u₁ ↦ −u₁. It is not yet the error.
2. **Any choice of variables, pivot or labelling.** A form Σ M_ij⟨u_i,u_j⟩ has a symmetric 3×3 coefficient matrix M.
   - Each actual form has rank 2 and determinant 0.
   - The printed positive pair (2⟨u₁,u₂⟩, 2⟨u₃,u₁+u₂−u₃⟩) forces the third form, minus their sum, to have
     determinant −4.
   - An invertible linear substitution T multiplies determinants by det(T)² ≠ 0, and sign flips do not create a nonzero
     determinant.
   - The time phase Σω_j(τ_j − t) can be pivoted at any of the three atoms. Every choice of pivot gives a pair whose
     third form is one of the actual three, so all such pairings are excluded.
   - The linear alternative Λ = 2⟨u₁,u₃⟩ makes all three printed forms share the factor u₁. The actual factor pairs
     {a, b}, {c−a, c−b}, {c, c−a−b} share none.

   The obstruction is therefore real. In the normal form (u₁, u₂, u₃) = (a, b, c), Γ_{w1} = 2⟨u₁,u₂⟩ and
   Γ_{w3} = −2⟨u₃,u₁+u₂−u₃⟩ exactly: the relative sign is reversed.
3. **Opposite directions (the second printed case).** The three forms are 2a·e, −2e·(a−c+e) and −2e·(c−e). They share
   the factor e, and a positive pair (2⟨u₁,u₂⟩, 2⟨u₁,u₃⟩) is reached after flipping one variable. This case is correct
   up to the choice of coordinates, as the entry implies.
4. **Is the sign harmless?** Yes.
   - `sumint` uses the core only through Lemmas `lemcubic0` (L1544) and `lemcubic` (L1554), in the bound for 𝒩ⁱ (L1661).
   - Their (t, s)-domains, |s|, |t| ≤ L and L ≤ max(|t|,|s|) ≤ 𝔇δL^{2γ}, are symmetric under s ↦ −s.
   - Step 2 of `sumint` takes absolute values over regions in max(|w₁|,|w₂|) that are symmetric in w₂ ↦ −w₂.
   - So the lemmas, and `sumint`, hold for −Λ by the substitution s ↦ −s. The entry's "the proof of `sumint` does not
     use the sign" is correct, and the needed variant is the printed proof verbatim.

### Scope: the same slip occurs at L1814 and for Vine (IV) (new; scripts `e2d_vine3.py`, `e2d_vine4.py`)

- **Vine (III), Figure (B), c and d in the same direction, with the printed coordinates (c−a, a−d, c−b).**
  - Exactly, Γ_{w1} = 2⟨u₁,u₂⟩ and Γ_{w3} = −2⟨u₃,u₁+u₂−u₃⟩.
  - In terms of ω: ω_{w1} = −2⟨u₁,u₂⟩ and ω_{w3} = +2⟨u₃,u₁+u₂−u₃⟩.
  - The quadratic parts of all three Γ's, in the free variables (a, c, h_*), have determinant 0, so the printed
    positive pair is impossible here too.
  - The printed text also attaches the nonlinear form to ω₂ (atom w₂); it sits at w₃.
- **Vine (IV), Figure (C).** The external directions force a, b into w₁ and c, d into w₂. With (u₁, u₂, u₃) = (a−e, a−f,
  a−c), we get exactly Γ_{w1} = −2⟨u₁,u₂⟩ and Γ_{w2} = +2⟨u₃,u₁+u₂−u₃⟩. All three quadratic parts have determinant 0.
  TARGET prints no coordinates here, only "similar".

So every nonlinear normal-vine core (III same-direction, IV, V–VIII same-direction) has the reversed relative sign. The
project's own note (`target-vine-core-sign-check.md`) already mentions signed certificates for type-III joints.

### Verdict: CONFIRMED WITH CORRECTIONS

The mathematics of the entry is right.

**Corrections.**
1. **Scope.** Extend the entry to L1814. Suggested sentence after "What is wrong": "The same reversed relative sign
   occurs in case (C-i) for Vine (III) when the bonds c, d have the same direction (with the printed coordinates,
   Γ(w₁) = 2⟨u₁,u₂⟩ and Γ(w₃) = −2⟨u₃,u₁+u₂−u₃⟩), and for Vine (IV) ('similar', L1814): every nonlinear core of a normal
   vine has opposite relative sign. The linear (opposite-direction) cores are correct up to the choice of
   coordinates." Update the title and summary-table claim from "vines (V)–(VIII)" to "vines (III)–(VIII)", or "every
   nonlinear normal-vine core".
2. **Class.** MINOR rather than ERROR. The printed claim is false, but the needed variant of `sumint` follows from the
   printed proof by s ↦ −s in Lemmas `lemcubic0`/`lemcubic`, whose domains are symmetric. That is a small slip,
   harmless in context. If ERROR is kept, add "harmless: the printed proof of `sumint` is invariant under Λ ↦ −Λ (the
   (t, s)-domains of Lemmas `lemcubic0`, `lemcubic` are symmetric in s)". Either way, move E2d from summary item 3,
   "Other errors", to "Smaller slips" if MINOR is adopted.
3. **Wording.** The "scalar check" (−Γ(w₁) = −2 against the displayed +2) shows only a global sign of the first factor,
   which u₁ ↦ −u₁ removes. Label it "the printed coordinates give the opposite sign for ω₁" and let the determinant
   argument carry the relative-sign claim.

I did not check the Lean declarations; I confirmed only that `SumintPar.signed_of_sumintPar` and
`VineEstS2/SumintSigned.lean` exist on `origin/main`.

---

## E16: TARGET Remark `remtame`, L2152: "a ZG v₃ in Operation 2 must be tame by `subpro` (3)"

### Pinned text

- L2152: "We will also assume that no atom $v_3$ in Operation 2 or atom $v$ in Operation 4 is ZG; in fact, if any such
  atom $v$ is ZG, then it must be tame by Proposition \ref{subpro} (3), and thus can be treated by the arguments in
  Section 10.5 of [DH23]."
- `subpro` (3), L2044: "Then any degenerate/ZG atom that is **not a hinge atom** must be tame."
- `subpro` (5): for a hinge atom, the designated pair (ℓ₁, ℓ₂) "always has SG".
- Operation 2 (L2142) imposes conditions only at v₁ and v₂ (SG triples), and none at v₃.

### Reasoning

- The citation does not cover hinge atoms. Nothing in Operation 2 prevents v₃ from being a hinge.
- A hinge is **never** tame: its designated pair has SG, hence nonzero, gap, so its bonds cannot all be equal.
- So the claim fails as soon as a hinge v₃ can be ZG through its triangle pair. This needs a crossing pair (one bond
  from each original joint), whose gap the SG condition does not constrain.

### Counterexample, checked independently (script `e16.py`)

I rebuilt the couple of `remtame-hinge-notes.txt` §3.2 from TARGET's definitions: `defdec`, L641; `defcplmol`, L1297
(bond directions); `defdiff` (gaps). I used the notes' explicit decoration (L = 10⁶, γ = 3/4, η = 1/100, units 1/L).

**The couple.**
- \+ tree: P→[x, m, u1]; u1→[u11, u0, u2]; u2→[u21, u22, u23]; u21→[y1, y2, y3].
- − tree: Q→[q1, q2, Q2]; Q2→[r1, r2, r3].
- Leaf pairs: u23–u0, y1–m, x–r3, u11–q1, r2–u22, q2–y2, y3–r1.

**Results.**
- **Validity.** The signs alternate correctly and the pairs have opposite signs. The root condition holds. ε ≠ 0 at
  every node (L646).
- **M(Q_sk).** 6 atoms and 11 bonds; degrees (3, 3, 4, 4, 4, 4); in- and out-degree ≤ 2; conservation holds at every
  degree-4 atom; no self-loop; the only multiple bond is the double bond u1–u2, with opposite directions. There is no
  zero-gap pair at any atom.
- **The vine.** By `block_clcn` (1)(a), L1349, the block is (CL): G[B] = {u1, u0, u2, u23}, and u0–u23 is paired. Its
  joint degrees sum to 8 > 6, so it is non-root. Its gap is 10/L, which is SG.
- **Primality, checked directly** (this was item O5, "not separately verified", in the project notes). By `propstructure2`,
  L870, I enumerated all embedded sub-couples and sub-paired-trees. The only embedded sub-couples are (P, Q) itself and
  the seven leaf pairs; there is no embedded sub-paired-tree at all. So there is no (1,1)-mini-couple or mini tree, the
  couple is prime, and it is its own skeleton.
- **M_sb.** Splicing gives u1 children (u21, u22, u11) (Figure `Couples_CL`). Result: 5 atoms, 9 single bonds, no block.
  - At the hinge h = u1, the designated pairs are SG: (PC:u21, LP:u22) and (LP:u11, PC:u1).
  - The crossing pairs (PC:u21, PC:u1) and (LP:u11, LP:u22) are ZG.
  - h is not tame. Every other atom of M_sb is non-degenerate.
- **The triangles.** Enumerating all triangles with SG triples at v₁ and v₂ gives exactly one: (v₁, v₂, v₃) = (P, u21, h),
  with ZG pair (PC:u21, PC:u1) at h.
- **The literal cut.** Removing that triangle leaves h as a degree-2 β-atom with bonds (LP:u11 in, LP:u22 out) and zero
  gap.
- **DH23.** DH23 L1985 asserts "all the hinge atoms … will not be degenerate once they are cut according to the rules
  … any α- or β-atom will not be degenerate". DH23 Step 2 (L1777) has the same structure, so the entry's "DH23 has the
  same gap" is accurate. The related point at DH23 L1815, which assumes that the hinge is cut along (ℓ₁, ℓ₂), is
  plausible; it is correctly marked as a separate CANDIDATE.

### Verdict: CONFIRMED (class ERROR is right; the sentence at L2152 is false as printed)

**Wording corrections.**
1. Replace "The referee found this in 300 of 300 random decorations." with: "A hinge is never tame: its designated pair
   has SG, hence nonzero, gap."
2. Replace "Take decorations with D = E. Then M(Q_sk) has no zero gap" with: "Take a decoration with D = E that is
   otherwise generic (for example the explicit one in the notes, §3.2). Then M(Q_sk) has no zero-gap pair".
   D = E alone does not imply this.
3. In "Consequence", cite the property: "this breaks the non-degeneracy of α- and β-atoms asserted at DH23 L1985, on which
   the proof of DH23 Prop 9.6 relies". Add: "We do not claim that (finalcount1) itself fails for this couple." The
   skip repair makes that question moot.
4. Optional: note that primality (no embedded mini couple or mini tree) has now been checked directly.

I did not verify the (I-a) subtype label, which plays no role, nor the Lean repair.

---

## E18: TARGET L1918 (ii): "J̃_𝒬(t,s) equals 0 if t = L_r"

### Pinned text

- L1917–L1918: "(i) if $q>\Lf_{\rf}$ then $\widetilde{\Jc_\Qc}(t,s)$ is constant in $t$ for $t\in[q,q+1]$, and (ii) if
  $q=\Lf_{\rf}$ then $\widetilde{\Jc_\Qc}(t,s)$ equals $0$ if $t=\Lf_\rf$. … extending it continuously as constant (in $t$)
  functions … These extensions are consistent with the current definition for any $q\geq \Lf_\rf$, and equals $0$ for
  $t\leq \Lf_\rf$".
- The only use, L1922: "… because $t_1^p\in[\Lf_{\uf_4^p},\Lf_{\uf_4^p}+1]$, so for any $\Qc$ or $\Tc$ with root $\rf$
  satisfying $\Lf_{\rf}\geq \Lf_{\uf_4^p}+1$ we must have $\widetilde{\Jc_\Qc}(t_1^p,t_0^p)=\widetilde{\Jc_\Tc}(t_1^p,t_0^p)=0$."
- `regref2`, L1175: "for trivial couple $\Qc$ we have $\Jc\Bc_\Qc^*(t,s)=1$."

### Reasoning

1. **The literal claim is false for trivial objects.**
   - For the trivial couple, J̃ ≡ 1 by TARGET's own `regref2`. For the trivial paired tree, K* ≡ 1 (an empty product).
   - Both occur in the class 𝓑 of Def `lftwist` (L1466–L1480), and both have q = L_r when q = q′.
   - The same failure holds, equally harmlessly, for any coherent couple whose + tree is a single leaf: then J̃ does not
     depend on t.
2. **The failure is never used.**
   - The vanishing is invoked only for objects whose root lies in layer ≥ L_{u4}+1.
   - In Def `lftwist`, q′ = L_{u2} ≤ L_{u4}. By `layerreg1` (L899), a trivial or type-1 coherent object has all its nodes
     in layer q′, so its root layer is ≤ L_{u4}.
   - A root in layer > q′ therefore belongs to a type-2 object with a nonempty + chain. For such an object, (ii) holds:
     (prooflayer1-1) contains the factor K*_{T_[q]}(t, q, k) of a nontrivial tree, and (regref2-2) integrates over the
     empty range t > t₁ > s at t = s = q.
   - For trivial objects, the constant extension (≡ 1) is the right one, and the replacement s₁ᵖ → t₁ᵖ is exact for
     them.
   - So the argument for L_{u3} > L_{u4} is unaffected. The project's own handoff (`vineest-handoff.md`, line 281) says
     the same: "no trivial/type-1 case occurs for roots > L4. So R35's trivial-case repair … is not needed for hQ0".
3. **"The true kernel F·1_{t>q}" is not TARGET's object.**
   - TARGET defines K*_𝒬(t,s,k) only for t > q and s > q′ (Def `defkg`, L678), and works on 𝔅 = [q,q+1]×[q′,q′+1]
     (L951).
   - Outside that domain there is no printed "true kernel" equal to 0; the indicator is a formal convention.
4. **The "two other configurations" are not counterexamples to the printed text.**
   - "Type 1 with q′ < q": there L_r = q′ < q, so case (i) applies, and constancy in t holds there (the handoff, line
     294, agrees). Case (ii) does not apply.
   - "Type 1 with q = q′ and s < q": here s < q′ is outside 𝔅.
   - Both describe the formal approximant outside the paper's domain.

### Verdict: CONFIRMED WITH CORRECTIONS (the literal claim is false; class and consequence are overstated)

**Corrections.**
1. **Class.** ERROR → MINOR ("a reading slip harmless in context"). Main theorem: "none: the vanishing is used only for
   roots in layer ≥ L_{u4}+1 (L1922), and such objects are nontrivial type-2 objects, for which (ii) holds."
2. **Delete** the bullet list "There are also two other configurations…", or replace it with: "In the formalization, the
   approximant's values outside the domain 𝔅 of TARGET (type 1 with q′ < q off [q, q+1]; s < q′) also needed a
   convention; these are not failures of the printed claim."
3. **Replace "Consequence"** with: "For trivial objects the constant extension of L1918 is identically 1, not 0 below
   L_r. TARGET uses the vanishing only at L1922, for roots in layer ≥ L_{u4}+1, where trivial objects do not occur, so the
   argument is unaffected. The formal proof states the exact kernel for trivial objects (ruling R35)."
4. Move E18 from summary item 3, "Other errors", to the list of smaller slips.

---

## E24: TARGET §redcount0, L2065 and L2067: weights and k-derivatives on decoration-dependent leaves

### Pinned text

- L2063: the estimates involve "the weights $(\langle k_1\rangle\cdots\langle k_{2R}\rangle)^{4\Lambda_{p+1}}$ for both
  gardens and couples, and the derivatives $\partial_k^\rho$ … for couples".
- L2065: "$\langle k_j\rangle^{4\Lambda_{p+1}}\leq (3n_j)^{4\Lambda_{p+1}}\cdot\langle k_{\lf_j}\rangle^{4\Lambda_{p+1}}$
  for some leaf $\lf_j\in\Tc_j$ … if we include the extra factor $\langle k_{\lf_j}\rangle^{4\Lambda_{p+1}}$ to the input
  function $F_{\Lf_{\lf_j}}(k_{\lf_j})$ in (defkg0) … this happens for at most $R$ input factors".
- L2067: "taking any $\partial_k$ derivative is equivalent to taking exactly one $\partial_{k_\lf}$ derivative for some
  leaf $\lf\in\Gc$ … these stronger bounds will follow from same arguments below".

### Reasoning

1. **The diagnosis is right.**
   - The root momenta k_j are fixed, so the weight is a constant factor. The inequality of L2065 has a
     decoration-dependent leaf ℓ_j and is pointwise.
   - It cannot be moved inside the decoration sum, which is oscillatory, nor inside the LF-twist class sum, because
     `vineest` (L1742) cancels over that class with identical inputs and uses the realness (layerregest10) of a common
     real input.
   - Any rigorous version must be an identity.
2. **The derivatives (L2067).**
   - The Leibniz identity ∂_k K = Σ_ℓ K[∂F at ℓ] is exact.
   - Some terms put the derivative on a leaf inside T_(u₂) or 𝒬_(u₂₃,u₀) of a twisted core vine. An LF twist replaces
     these by T′, 𝒬′ with different leaf sets (Def `lftwist`, L1466–L1480), so those terms have no counterpart across
     the class.
   - "The same arguments below" therefore cannot be applied term by term. This part of the gap is genuine.
3. **The weights (L2065): one sentence of the entry overstates.**
   - By `block_clcn` (1)(a)(iii), L1349, all leaves in a (CL) realization are completely paired inside one tree.
   - Leaf pairs inside one tree cancel in k_j = Σ ±k_ℓ. Hence k_j is a signed sum over the leaves of T_j that are paired
     with leaves of *other* trees.
   - Expanding ⟨k_j⟩^{4Λ} = (1 + |Σ ±k_ℓ|²)^{2Λ} over those leaves is a decoration-independent identity. It never
     modifies a leaf inside a (CL) vine realization, hence never inside T_(u₂) or 𝒬_(u₂₃,u₀).
   - This is exactly the entry's own repair (b), "c_j … vanishes on pairs inside one tree". The entry's sentence "Those
     produce terms whose modified leaf lies inside T_(u₂) or 𝒬_(u₂₃,u₀)" is true of a naive expansion over all leaves
     and of the Leibniz distribution, but not of every rigorous replacement.
4. **Checks of the repair and the side corrections.**
   - The extraction p′(0) = Σ_{k≠M} w_k p(λ(k−M))/λ, with w_k = (−1)^{k+M+1}C(2M,k)/((k−M)C(2M,M)), is exact for
     deg p ≤ 2M. Also |w_k| ≤ 1/|k−M| and Σ|w_k| = H_M. I checked this in exact arithmetic for M ≤ 8 (script `e24.py`).
   - The degree bound n + R is right: a garden of order n and width 2R has n + R leaf pairs.
   - (3n_j) fails for a trivial tree (n_j = 0, while k_j = k_ℓ); 2n_j + 1, the number of leaves, is right.
   - "At most R" input factors should be 2R: there are 2R trees.
   - For couples the weight is ⟨k⟩^{4Λ}: (estcouple2), L776, uses S^{4Λ,4Λ}, which contradicts L2063's
     "(⟨k₁⟩⋯⟨k_{2R}⟩)^{4Λ} for both".
   - All the side corrections are correct.
5. **Class.** The printed mechanism is invalid, not merely terse. The repair needs a symmetrization idea:
   type-dependent inputs for the weights, and a symmetric family F + ε∂F for the derivatives. An equally short
   alternative for the derivatives exists: the class sum with inputs F + ε∂F is a polynomial in ε of degree ≤ n + R,
   bounded for real |ε| ≤ ε₀ by the printed argument, and Markov's inequality bounds its derivative at 0. GAP is
   defensible; EXPOSITION would also be defensible. I recommend keeping GAP and saying that the repair is short.

### Verdict: CONFIRMED WITH CORRECTIONS

**Corrections.**
1. Replace "Any rigorous replacement is a decoration-independent identity, such as a polynomial expansion of ⟨k_j⟩^{4Λ}
   over leaves or a Leibniz distribution of ∂_k over leaves. Those produce terms whose modified leaf lies inside …"
   with: "Any rigorous replacement is a decoration-independent identity. For the derivatives (L2067), the Leibniz
   distribution of ∂_k over leaves produces terms whose modified leaf lies inside the regular tree T_(u₂) or the regular
   couple 𝒬_(u₂₃,u₀) of a vine. For the weights (L2065), the defect is only that the inequality is not an identity: an
   expansion of ⟨k_j⟩^{4Λ} over the leaves of T_j paired outside T_j avoids every vine interior (repair (b) below)."
2. Mark item (iii), "Supporting facts", as formalization evidence (Lean checks, ruling R46). It is not needed to
   establish the gap in the printed text.
3. In summary item 4, "breaks the twist cancellation of `vineest` (E24)" is accurate for the derivatives. For the
   weights, say "is not an identity".

---

## E26: TARGET (redvine), L1954–L1957: lower-child slots keep the lower joint's clock

### Pinned text

- (redkg), L1726: the slots are $\Kc^*_{\Tc_{(\mf)}}(t_{\mf^{\mathrm{pr}}},t_\mf,k_\mf)$ and
  $\Kc^*_{\Qc_{(\lf,\lf')}}(t_{\lf^{\mathrm{pr}}},t_{(\lf')^{\mathrm{pr}}},k_\lf)$.
- L1737: "we only integrate over the variables $t_\nf$ for all branching nodes $\nf\in\Gc_{\mathrm{sk}}[\Ub]\backslash\{\uf_1\}$".
- L1738: the slot products in $\Kc^{\Ub}$ include only $\lf,\mf\in\Gc_{\mathrm{sk}}[\Ub]\backslash\{\uf_1\}$.
- `block_clcn` (1)(a), L1349: $\Gc[\Bb]$ consists of the descendants of u₁ that are not descendants of u₁₁, u₂₁ or u₂₂.
  So u₂ ∈ 𝒢[𝔹], but u₂₁, u₂₂ ∉ 𝒢[𝔹].
- Figure `Couples_CL`: after splicing, u₂₁ and u₂₂ are children of u₁.
- (redvine), L1956: the outer slots are $\prod_{\mf\in\Nc_{\mathrm{sb}}}\Kc^*_{\Tc_{(\mf)}}(t_{\mf^{\mathrm{pr}}},t_\mf,k_\mf)$,
  with parents taken in 𝒢_sb.

### Reasoning

1. **The mismatch.** In (redkg), the slot at m = u₂₁ is K*_{T(u21)}(t_{u2}, t_{u21}, k), and t_{u2} is integrated inside
   K^𝕌 (L1737). The slot itself is not in K^𝕌 (L1738). In (redvine), the same slot reads K*_{T(u21)}(t_{u1}, t_{u21}, k).
   The two sides agree only if the slot does not depend on its first argument between t_{u2} and t_{u1}.
2. **It does depend on it.**
   - Suppose T_(u21) is nontrivial with a node in layer L_{u2}. At p = 0 every layer is 0.
   - For order 2, the leading part of K*_T is δ·JB_T(t, s)·M(k) with JB_T(t, s) = t − s (regref2-2, with trivial
     inner couples). This is genuinely t-dependent.
   - If L_{u1} > L_{u2}, the slot (redvine) uses takes the constant value at the top of layer L_{u2}, while (redkg) has
     the varying value at t_{u2}.
   - The same holds for a leaf slot at u₂₁, whose couple slot has clocks (t_{u2}, t_{(ℓ′)^pr}).
3. **Alternative readings.**
   - Putting the lower slots inside K^𝕌 contradicts L1738 and would double-count them in (redvine).
   - Twist invariance of the slot does not make t_{u2} an exterior variable.
   - Layer separation saves the identity only when every node of the slot's object lies below layer L_{u2}.
   - No reading makes (redvine) an identity in general.
4. **The repair, in outline.** Fourier-expand the slot in its first clock and route e^{πiλt_{u2}} into the unit as a
   modulation of t₀¹ = t_{u2}.
   - `sumint` allows such modulations at a loss of [max⟨λ⟩]^{η⁶} ((FourierboundI), L1618).
   - The slots carry ⟨λ⟩^η weights (`proplayer1`, L953, 𝔛^{η,30d,0}; `proplayer2`, 𝔛^{1−η}).
   - `vineest` Step 3 absorbs modulations in exactly this way (L1848: "the η⁶ power … can be absorbed by exploiting the
     (⟨λ⟩+⟨λ′⟩)^η weight").
   - So (redvine2) survives with the same form. The repair uses only TARGET's own tools.

### Verdict: CONFIRMED (class ERROR, in an intermediate identity, is right; the conclusion (redvine2) survives)

**Wording suggestions.**
1. State the general condition alongside the p = 0 instance: "(redvine) fails as an identity whenever the slot at a lower
   external child of a spliced unit depends on its first clock on the range between t_{u2} and t_{u1}; for example, a
   nontrivial regular tree or couple there with a node in the layer of the lower joint."
2. Status: this check independently confirms the printed-source claim. The independent referee of the *weighted flower*
   repair (Theorem U-clock) is outside this check and remains pending. I did not check the Lean declarations.

---

## Appendix: scripts (Python 3, sympy 1.14; run with `python3 -I`)

Outputs quoted above were produced by these scripts, which ran in the verifier's private working directory (not
included). The essential code follows.

### e2d.py (Figure (D), same direction; determinants)

```python
import sympy as sp
a,b,c,e,d,g=sp.symbols('a b c e d g')
def gram(expr,V): return sp.Matrix(len(V),len(V),lambda i,j: sp.Rational(1,2)*sp.diff(expr,V[i],V[j]))
sub={e:a+b-g, d:a+b-c}          # a,b: w2->w1; e: w1->w3; c,d: w3->w2; g out of w1, into w3
G1=(g**2+e**2-a**2-b**2).subs(sub); G2=(a**2+b**2-c**2-d**2).subs(sub); G3=(c**2+d**2-e**2-g**2).subs(sub)
Gs=[sp.expand(G.subs(g,0)) for G in (G1,G2,G3)]          # 2ab, -2(a-c)(b-c), -2c(a+b-c); sum 0
print([gram(G,[a,b,c]).det() for G in Gs])               # [0,0,0]
u1,u2,u3=sp.symbols('u1 u2 u3'); P1=2*u1*u2
for P2 in (2*u3*(u1+u2-u3), -2*u3*(u1+u2-u3), 2*u1*u3):
    print([gram(sp.expand(P),[u1,u2,u3]).det() for P in (P1,P2,-P1-P2)])   # [0,0,-4], [0,0,0], [0,0,0]
print(sp.expand(Gs[0]-2*a*b), sp.expand(Gs[2]+2*c*(a+b-c)))                # 0 0 : signed normal form
```

### e2d_vine3.py / e2d_vine4.py (Vines (III) and (IV))

```python
# Vine (III), Figure (B), c,d: w1->w3; e out/f in at w2, g in at w1, h out at w3
a,c,g,h,e=sp.symbols('a c g h e'); d=a+g-c; b=a+g-h; f=e+a-b
G1=c**2+d**2-g**2-a**2; G2=e**2+a**2-f**2-b**2; G3=h**2+b**2-c**2-d**2
u1,u2,u3=c-a,a-d,c-b                      # printed coordinates (L1814)
assert sp.expand(G1-2*u1*u2)==0 and sp.expand(G3+2*u3*(u1+u2-u3))==0
# quadratic-part dets in free vars (a,c,h): [0,0,0]
# Vine (IV), Figure (C): e,f out of w1; g,h into w3; a,b: w2->w1; c,d: w3->w2
a,c,f,e,g=sp.symbols('a c f e g'); b=e+f-a; d=e+f-c; h=e+f-g
G1=e**2+f**2-a**2-b**2; G2=a**2+b**2-c**2-d**2; G3=c**2+d**2-g**2-h**2
U1,U2,U3=a-e,a-f,a-c
assert sp.expand(G1+2*U1*U2)==0 and sp.expand(G2-2*U3*(U1+U2-U3))==0   # signed; dets [0,0,0]
```

### e16.py (order-6 couple; M(Q_sk), M_sb, triangles, primality)

Core logic:
- The couple, leaf pairs and decoration are as in §E16. Node momenta follow k_𝔫 = k_{𝔫1} − k_{𝔫2} + k_{𝔫3}.
- **Bonds.** A PC bond n–c runs n→c if c has sign −, and c→n otherwise. An LP bond runs from the atom whose paired child
  has sign − to the atom whose paired child has sign +. The bond value is the child's or leaf's momentum.
- **Gaps.** A gap is (in-bond value) − (out-bond value). SG means 0 < |r|/L ≤ L^{−γ+η}; ZG means r = 0.
- **Splicing.** Remove u2, u0 and u23, and give u1 the children (u21, u22, u11).
- **Triangles.** Enumerate all triangles of M_sb with opposite-direction SG pairs at v₁ and v₂, and report the class of
  the pair at v₃.
- **Primality.** Enumerate every (n, n′) with n′ a proper descendant of n such that the leaves of n not below n′ are all
  paired among themselves (sub-paired-trees), and every pair of order-1 nodes whose six leaves are paired across
  (mini-couples).

Output:
```
epsilon != 0 at all nodes of Q_sk: True
[M(Q_sk)] atoms=6 bonds=11 degrees=[3, 3, 4, 4, 4, 4] in/out<=2: True
multi-bonds in M(Q_sk): {('u1', 'u2'): 2}  self-loops: []
ZG pairs anywhere in M(Q_sk): []
double bond u1-u2: [('u2','u1','PC:u2'), ('u1','u2','LP:u23-u0')]  directions opposite: True
vine gap |r|*L = 10.0  class: SG
[M_sb] atoms=5 bonds=9 degrees=[3, 3, 4, 4, 4] in/out<=2: True
M_sb multi-bonds: []
   u1 [('PC:u21','PC:u1','ZG'), ('PC:u21','LP:r2-u22','SG'), ('LP:u11-q1','PC:u1','SG'), ('LP:u11-q1','LP:r2-u22','ZG')]
   (P, u21, Q, Q2: no ZG pair)
hinge u1 tame (all bond values equal)? False
ELIGIBLE triangle v1,v2= P u21  v3= u1  gap at v3 class: ZG  pair at v3: PC:u21 PC:u1
embedded sub-couples/sub-paired-trees found: none
embedded sub-couples (any order): [('P','Q'), and the seven leaf pairs]
```

### e24.py (central-difference extraction)

```python
from fractions import Fraction as Fr; from math import comb; import random
for M in range(1,9):
    w={k:Fr((-1)**(k+M+1)*comb(2*M,k),(k-M)*comb(2*M,M)) for k in range(2*M+1) if k!=M}
    assert all(abs(v)<=Fr(1,abs(k-M)) for k,v in w.items())
    assert sum(abs(v) for v in w.values())==sum(Fr(1,j) for j in range(1,M+1))
    lam=Fr(1,3)
    for _ in range(20):
        cf=[random.randint(-9,9) for _ in range(2*M+1)]; p=lambda x: sum(ci*x**i for i,ci in enumerate(cf))
        assert sum(v*p(lam*(k-M)) for k,v in w.items())/lam==cf[1]
```
