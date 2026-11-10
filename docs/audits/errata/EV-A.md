# EV-A — refute-first verification of E2b, E2c, E11, E17, E20, E23

Verifier: independent (did not write these errata). Date 2026-11-10.
Entries read from `git show origin/main:docs/ERRATA-AND-DEVIATIONS.md` at `636c5a46` (2026-11-10 08:46 UTC).
Sources checked by sha256 against the pinned values (both match):
- TARGET `WKE-Longer_times_Final_arXiv.tex` `493eef6b7dec448b…` (2694 lines, no CR characters)
- DH23 `Revision_Submit.tex` `c7e47dfabf5a4cca…` (2387 lines)

Line numbers below are physical lines (`awk NR`) of these files. Figures were read from the PNGs in the DH23
source directory (`Vines.png`, `YOper.png`). My scripts for E2b are in
[`EV-A-scripts/`](EV-A-scripts/) (run with `python3 -I <script> <N> <dir-of-scripts>`).

## Summary of verdicts

| Entry | Verdict | Main corrections |
|---|---|---|
| E2b | CONFIRMED | optional: say in the bullet that Q is an omission only on the figure's m ≥ 2 reading of vine (II) |
| E2c | CONFIRMED WITH CORRECTIONS | class ERROR → EXPOSITION; soften the title; move it out of "Other errors" in the summary |
| E11 | CONFIRMED | optional wording: (c) is graph-level; say "(finalcount) fails for X" rather than "Prop 9.6 is false" |
| E17 | CONFIRMED WITH CORRECTIONS | heading names the wrong proposition (`finalmol` → `lgmolect`); soften "no usable bound"; C1 as drawn needs a note |
| E20 | CONFIRMED WITH CORRECTIONS | add that realizability in an actual stage-1 molecule is open; reconcile with E6; "FAILS" → "fails" |
| E23 | CONFIRMED WITH CORRECTIONS | L2122 → L2117; Example C is misdescribed; acknowledge DH23 §10.5(2),(4) on self-connecting bonds; class GAP → EXPOSITION recommended |

---

## E2b — DH23 Lemma `ylem1` (L1937–L1948) misses several molecules

### Pinned text
- DH23 L1929 defines (Y1)/(Y2) and the (Y) sequence: a (Y2) at a triple bond (v₁,v₂) with exits v₃ ≠ v₄ removes
  (v₁,v₂) and adds one bond v₃–v₄; the sequence continues only "if after (Y2) a new triple bond forms between v₃ and
  v₄". A sequence of length 1 (a single (Y2)) is therefore allowed.
- DH23 L1937 (quoted correctly in the entry): "Suppose 𝕄 is 4-regular with at most two triple bonds and 𝕄′ is formed
  from 𝕄 by (Y) sequences. If 𝕄′ is either a quadruple bond or a triangle formed by 3 double bonds, then 𝕄 is formed by
  removing the two joints of a vine and adding one new bond between the pair of atoms connected to each joint."
- L1939: "Clearly going from 𝕄 to 𝕄′ involves at most two (Y) sequences with last operation (Y2)." L1941: one (Z)
  applied to the triangle gives M̃ "which can be formed from vines (III), (IV), (V), (VII) or (VIII)". L1946: "If ℓ′ is
  a single bond inserted in the first (Z) operation, then 𝕄 is formed from (VI)."
- Use: L1961 (proof of Prop 10.4(2)): "Since 𝕄 has at most two triple bonds and is not formed from a vine, using Lemma
  ylem1, we can apply at most two (Y) sequences to reduce it to 𝕄′, which does not contain triple or quadruple bond,
  and is not a triangle formed by 3 double bonds." This use includes the case of zero sequences.
- Vines: Def `defvine` L790, Remark `remilia` L801–L807 (a ladder may be inserted at each dashed pair), Figure
  `Vines.png`. Atom counts with no ladders inserted: (I) 2, (II) 2 + 2m with m ≥ 2 rungs as drawn, (III) 9, (IV) 9,
  (V) 9, (VI) 15, (VII) 11, (VIII) 11. Each inserted rung adds 2 atoms. So closures of (II) have an even number of
  atoms, and the closures of (III)–(VIII) have at least 7.

### Checks
1. **The 5-atom T₁, by hand.** The bonds 1→0, 1→2, 2→1, 2→0, 0→2, 0→3, 3→4, 3→4, 4→3, 4→1 give in = out = 2 at every
   atom. Bonds: 0–1 single, 1=2 and 0=2 double, 0–3 and 4–1 single, 3≡4 triple. The (Y2) at (3,4) has exits 0 ≠ 1 and
   adds 0→1, which is forced by the in-degree at 0. The result is {0,1,2} with three double bonds, and no new triple
   bond forms, so the sequence stops. A vine closure with 5 atoms would need a 7-atom vine, and there is none. So T₁
   contradicts the lemma on any reading of "(Y) sequences".
2. **My own exhaustive check** (`ylem1_check.py`, `ylem1_summary.py`). I worked with undirected loopless multigraphs.
   A 4-regular one always has an Eulerian orientation with in = out = 2, and in such an orientation the two exits of a
   triple bond are one in and one out, so the direction of the (Y2) bond is consistent. I generated every connected
   𝕄 that reaches Q or T by at most two inverse (Y) sequences of any length n (a triple bond plus n − 1 double rungs
   inserted into a bond of multiplicity ≠ 3), and checked each forward in every order. I built all vine closures from
   my reading of `Vines.png` with any number of inserted rungs, and compared them by canonical form.
   - Every vine closure up to 19 atoms reduces to Q or T, which is the lemma's intended converse and a sanity check of
     my figure reading.
   - The molecules that are *not* vine closures are: Q (2 atoms; figure reading only), T (3), T₁ (5), and, with two
     triple bonds, 1, 2, 4, 5, 7, 8 and 10 molecules at 7, 9, …, 19 atoms. These fall into exactly two infinite
     families, both from the (VI) bullet (second insertion into a single bond made by the first). In family 1 the
     second structure sits on the exit bond: two triple bonds in series, smallest at 7 atoms, parameters {n₁, n₂}. In
     family 2 it sits on the rail next to the first triple bond: smallest at 9 atoms. The other single-bond positions
     with n₂ ≥ 2 give genuine (VI) closures.
   - With one triple bond, only T₁ fails. T + Zₙ for n ≥ 2 is a (V) closure.
3. **The "most generous reading"** (`ylem1_generous.py`): I let a dashed pair between two double bonds collapse the two
   rungs into one. This recovers Q (as vine (II), m = 1), T₁ (as (V) with the pair collapsed) and family 2. T and
   family 1 remain uncovered. This matches the entry's sentence exactly.

### Verdict: CONFIRMED
The lemma is false as printed (T₁ suffices). The list of omissions and the "generous reading" claim match my own
enumeration to 19 atoms. Class ERROR and "no direct effect; underlies E1" are right: the omissions break the step at
L1961, where 𝕄′ = T is not excluded.

Optional precision for the entry. The bullet "Q and T themselves, reached by zero (Y) sequences" could add: "(Q only
on the figure's reading m ≥ 2 of vine (II); with E3's m ≥ 1, Q is the closure of the m = 1 vine)". The Repair
paragraph already says this.

---

## E2c — DH23 proof of Prop 10.2, L1911–L1912: "the total number of operations is ≤ C(r₁+r₂)"

### Pinned text (quotes in the entry are accurate)
- L1911: "Now we see that the number of steps *different from* (3D3-1N) is at most C(r₁+r₂). … each chain can be as
  long as Cn, but the number of chains must be at most C(r₁+r₂) for the same reason."
- L1912: "…for operation (3D3-1N), which is the only operation whose number is not controlled by C(r₁+r₂), we do not
  have any logarithmic loss… In the same way, if E=2V−2>0, then the total number of operations is ≤ C(r₁+r₂) as shown
  above, and this total number must be positive if E>0, so we know r₁+r₂ ≥ 1 and hence 𝔄 ≲ L^{−η/3}."
- Appendix B: (3D3-1N) needs d(v₃) = d(v₄) = 4 (L2214) and removes v₁, v₂ (L2226). The loop ends only when 𝕄 has
  only isolated atoms (L2165, L2293).

### Refutation attempt
The sentence contradicts the one before it and L1911: (3D3-1N) chains can have length ≍ n. So "total number of
operations ≤ C(r₁+r₂)" is false as written. The only sensible reading is "the number of operations other than
(3D3-1N)", which is what "as shown above" points to. On that reading the bound holds, and the gap is the positivity
claim "must be positive if E>0", which needs the one-line argument the entry supplies. A (3D3-1N) leaves v₃ and v₄ of
degree 3, so it is never the last step, and a nonempty run has a non-(3D3-1N) step.

Independent check of the conclusion. I did not rely on L1906–L1911. Suppose r₁ = r₂ = 0, so the run uses only normal
operations. Use ν = 4V − 2E − 4F (ν₀ = 0 when E = 2V − 2, and ν = 0 at the end) and V₃. The increments are:
- (BR-N): Δν = −2;
- (3S3-1N): Δν = −2, ΔV₃ = +2;
- (3D3-1N): Δν = 0, ΔV₃ = 0;
- (3R-1N): Δν = +2, ΔV₃ = +2;
- (BR-N) not between two degree-3 atoms: ΔV₃ ≥ −1.

These give z₃ = z₁ + z₁′ + z₂ and −V₃₀ ≥ z₁′ + 4z₂. Hence V₃₀ = 0 and z₁′ = 0, so no normal operation applies at
the start, which contradicts E > 0. So r₁ + r₂ ≥ 1 holds, and the conclusion of Prop 10.2 is not in doubt.

(Side remark, not in the entry: Prop `brprop` at L2183 states Δν = 2, while its proof at L2185 and (increeta) use
−2. This is a typo.)

### Verdict: CONFIRMED WITH CORRECTIONS
The observation is right, but it is a misstatement plus a one-line omitted justification, not a false claim the proof
depends on. Corrections:
- Class: ERROR → **EXPOSITION**.
- Title: "…'the total number of operations is ≤ C(r₁+r₂)' should read 'the number of operations other than (3D3-1N)',
  and its positivity needs one line".
- In "What is wrong", replace "So the bound on the total, and with it the deduction of r₁ + r₂ ≥ 1, does not follow as
  written" with: "Read literally, the bound on the total is false. Read as the count of non-(3D3-1N) steps, which is
  what 'as shown above' refers to, it holds, but its positivity is not justified."
- In the summary of findings, item 3 lists E2c among "Other errors"; move it to the exposition list (item 5).

---

## E11 — TARGET Remark `remtame` case (i) (L2152, L2218)

### Pinned text (quotes in the entry are accurate)
- L2152 (`remtame`): "If (i) d(v)<4, or if some component contains exactly one atom adjacent to v, then the values of
  k_ℓ for ℓ↔v must all be fixed in the given decoration, so we always have enough gain whether the resulting α- or
  β-atoms have zero gap. We then cut at v and proceed normally."
- L2218: "In case (i) the proof is modified trivially."
- L2044 (`subpro` (3)): a tame atom has all its k_ℓ equal, and they equal a fixed value only if d(v) < 4.
- L2185 (`finalmol`): "no α- or β-atom is ZG with the assumptions in Remark remtame".
- L2203–L2204: 𝔄_fin ≤ ∏ over components of 𝔄.
- DH23 L1985 (§10.5(3)): "we shall not make any cut at non-hinge degenerate atoms". L1987 (§10.5(4)): remove a
  degenerate ε-atom; "if Δχ ≤ −2 … big gain …; if Δχ ≥ −1, then one of k_j must be a bridge".

### Checks
- **(a)** Let v be tame of degree 4 (all four values = k₀). Suppose a component C of M − v meets v only through two
  bonds to one atom u. Summing the charges over C fixes ±k₀ ± k₀; with opposite directions this is 0, so there is no
  constraint. In/out balance at v forces the other two bonds to be one in and one out. If they go to one other
  component, it is the same; if they go to two different components, both are bridges and k₀ *is* pinned. So
  "unpinned" implies c ≤ 2 components, hence Δχ = c − 4 ≤ −2, as the entry says. Confirmed (this was already
  confirmed via F48).
- **(b)** Let v be pinned by a bridge to Y₁ (the other two bonds of v are bridges to Y₁, Y₂). The β-cut along the pair
  going into X moves the zero-gap half into X, whose own charges sum to 0 and say nothing about k₀. Since 𝔄 of each
  component is a supremum over parameters (L2131), the product at L2203 does not see the pin. Confirmed.
- **(c)** In X = {a, b, c, v₁} with c→a ×2, a→b, a→v₁, v₁→b, b→c ×2, every ε-atom has in = out = 2 and v₁ is a
  degree-2 β-atom.
  - Conservation over the closed component forces c_{v₁} = 0, so gap(v₁) = 0. This is exactly the case DH23 L1874
    rules out ("the only β-atom will have gap r = 0 which is not possible").
  - χ = 7 − 4 + 1 = 4, and there are 4 free vectors. Γ_{v₁} ≡ 0, so only 2 of the 4 energy windows are independent.
    So 𝔈 ≍ L^{4d}·(δ⁻¹L^{−2γ})², and 𝔄 ≍ C₁⁻⁴. With G = 1, V_β = 1, V_α = 0, (finalcount) asks for
    L^{−γ₀−3η²−η⁵ρ}. Confirmed.
  - X arises at graph level from the configuration in (b), with Y₁ and Y₂ attached to v by bridges.

### Verdict: CONFIRMED
Class GAP is right: case (i) contains a false sub-claim, (a), which is harmless, and an argument that does not work as
written, (b) and (c). "Main theorem: repaired in Lean" was not checked by me.

Optional wording:
- (c): "Prop 9.6 (`lgmolect`) is false for a component with an unpinned zero-gap β-atom" → "(finalcount) fails for a
  component with an unpinned zero-gap β-atom. `finalmol` (L2185) excludes such atoms, but the cut of case (i) can
  create one."
- Add "(graph-level example)" after the counterexample, as E17 does.

---

## E17 — single-atom erasure and "imperfect = odd"

### Pinned text
- L2152, case (ii): "remove v without assigning any new α- or β-atoms and proceed with the rest of the molecule. The
  big gain L^{−(d−2γ−η)} is enough to cover any loss that may occur, see Remark remtame2."
- L2218: case (ii) "increases the number of imperfect components by 2".
- L2189: "…the number of imperfect components is at most R (in fact, it is exactly R if R=1)."
- L2195: "Z equals 0 if R=1". L2197: "For perfect components, or imperfect components when R=1 (which are called *odd*
  components in [DH23]), this is exactly the same as Proposition 9.6 of [DH23]".
- Remtame applies only to ZG atoms that would be cut: v₃ of Operation 2, or a β-cut atom of Operation 4.

### Checks
- **C1.** The isolated tame double bond {u, v} has χ = 1 and 𝔈 = #k₀ ≍ L^d (both energy windows are trivially
  satisfied). So 𝔄 ≍ L^d·L^{−(d−γ)} = L^γ, against (finalcount)'s L^{ηZ}. Confirmed. DH23 §10.5(4)'s dichotomy does
  not apply either: removing u gives Δχ = −1, but no bond of a double bond is a bridge.
- **C0.** An isolated atom has 𝔄 = 1, while the R = 1 imperfect bound is L^{−η⁵ρ} with ρ ≥ 1. Confirmed.
- **Caveat on C1 as drawn** (R1–e⇄u⇄v⇄f–R2). Under the *printed* split, e is in case (i): the component containing u
  meets e only at u. So the chain as drawn illustrates the erasure route of E11's repair ("unpinned, c ≤ 2 → erase"),
  not the printed case (ii). The point still holds for printed case (ii):
  - Take u⇄v tame, with each of two tame atoms p and q joined to u and v by one bond each, plus two bonds to separate
    parts Y and Z.
  - At p, a β-cut along (p–u, p–v) is possible, and no component of M − p contains exactly one neighbour of p. So
    printed case (ii) erases p, and then q in the same way.
  - The isolated tame double bond {u, v} is left (graph level).
- **Gains.** In C1, C0 and my variant, the erasure gains L^{−(d−2γ−η)} per erasure (L2152) exceed the shortfall
  (≤ L^γ). So these examples do not break (finalcount1). What is missing is any bound for such damaged components:
  `lgmolect` and 𝔄 ≲ 1 both fail for them, and L2218's "enough to cover any loss" gives no argument. GAP is a fair
  class.
- **(b).** Confirmed by reading. L2189's "exactly R if R=1" is derived without erasures. Each case-(ii) erasure of a
  degree-4 atom raises 4V − 2E − 2(V_α+V_β) by 4, which is L2218's "+2 imperfect components". So for R = 1 the
  imperfect components are not only DH23's single odd component, and L2197's identification does not hold, with
  Z = 0 removing the slack. The entry already marks (b) as graph-level and harmless.

### Verdict: CONFIRMED WITH CORRECTIONS
- Heading: "L2193/L2197 (`finalmol`, R = 1)" → "L2192–L2197 (`lgmolect` and its proof, R = 1)". `finalmol` is
  L2182–L2190; the Z = 0 convention is L2195 and the "odd" identification is L2197.
- (a), first line: "Single-atom erasure leaves components with no usable bound" → "Single-atom erasure can leave
  components for which neither (finalcount) nor 𝔄 ≲ 1 holds, and to which DH23 §10.5(4) does not apply. In the two
  examples the erasure gain covers the shortfall, but the printed proof gives no bound for such components in general."
- After C1, add: "As drawn, e falls under case (i) of the printed split. The same isolated pair arises from printed
  case-(ii) erasures, for example when two tame atoms are each joined to both u and v."
- Apply the same softening to summary item 4 ("single-atom erasure leaves components with no usable bound").

---

## E20 — ghost triangles in DH23 Prop 9.4 / TARGET Operation 2

### Pinned text (all cited lines correct)
- DH23 L1777 (Step 2): "If deg v_j ≥ 3, then we cut the molecule at each v_j … This leaves 3 atoms v_j of degree 1
  or 2." Eligibility only asks that v₁ and v₂ be SG, so v₃ may be an already-cut degree-2 atom.
- DH23 L1791: "Next consider Step 2, for which we know ΔF∈{0,1,2}, ΔV_β=ΔF+1, and Δχ=ΔF−3". This is true only if all
  three atoms are cut.
- DH23 L1813 (proof of Prop 9.5) *relies* on Step 2 removing triangles whose atoms are already α-atoms: "any triangle
  with at least two SG atoms will be removed in Step 2". So DH23 needs ghost triangles but bounds only ghost-free ones.
  This supports the entry; I suggest citing it.
- TARGET L2142 ("We then cut the molecule at each v_j", with no degree condition), L2126 (cuts at degree-2 atoms are
  allowed), L2165 ("exactly Proposition 9.4 of [DH23]"), L2189 (the invariant), (together2) L2207.

### Checks
- **The explicit configuration, recounted independently.** Take M = {v₁, v₂, g, x, y}, with l₀ = v₁→v₂, v₂→g, g→v₁,
  v₁ = x and v₂ = y double bonds, and g an α-ghost.
  - Conservation gives k(g→v₁) = u − r_x and k(v₂→g) = u + r_y, with u = k(l₀).
  - The two energy windows put u in slabs normal to r_x and r_y. With r_x ∥ r_y and |r| ≍ L⁻¹ there is one slab of
    width δ⁻¹L^{1−2γ}, so #u ≍ L^{d+1−2γ} (γ > 1/2) or L^d (γ ≤ 1/2).
  - χ(M) = 3 and χ(M′) = 2 (two bigons). The parameters of M′ vary with u only within O(W), so
    𝔄(M)/𝔄(M′) ≍ #u·L^{−(d−γ)} = L^{γ₀}.
  - With the true increments (ΔF = 1, two new β, no new α, the ghost deleted), (excesseqn2) allows only
    L^{η²−η³}. So it fails by about L^{γ₀}. Confirmed.
- **The label factor.** The ghost's creation factor L^{(γ+3η)/2−κη}Q_g ≤ 1 is paid at creation and has no counterpart
  in (finalcount), since the ghost is not in 𝕄_fin. (together2) drops it. Confirmed by reading.
- **TARGET's cut-all reading.** Cutting the ghost too gives ΔV = 0, ΔE = −3 and Δ(V_α+V_β) = +2, so
  4V − 2E − 2(V_α+V_β) rises by 2 per ghost. The remnant is an isolated β-atom of degree 0, which is an imperfect
  component, so L2189's "at most R imperfect components" fails. Confirmed.
- **Not checked by me:** the claim "every one of the 21 patterns" (I checked one pattern), and the repairs (R38 for
  γ > 1/2; the γ ≤ 1/2 cone argument, which is refereed separately). I checked that Lemma 2.1 of the γ ≤ 1/2 note is
  consistent with the older "group D is attained" example: the note restricts that example to the local model.

### Verdict: CONFIRMED WITH CORRECTIONS
Class GAP is right: the per-step proposition is stated for every operation, its proof omits ghosts, and the bound
fails in a configuration allowed by the run's rules. Corrections:
- After the explicit configuration, add: "The configuration satisfies the run's rules. Whether it arises from the
  stage-1 molecule of an actual garden has not been settled (ghost-triangle note §1b); the printed proof gives no
  exclusion, and the repair does not depend on it." Without this, a reader may take the failure as shown inside an
  actual run.
- "Under TARGET's cut-all reading … This part is an erratum (CANDIDATE)" duplicates E6, which records the same
  invariant failure as MINOR. Cross-reference E6, and give the observation one class in both places.
- "FAILS" → "fails" (tone).
- Optional: cite DH23 L1813 as evidence that ghost triangles are part of DH23's own run.

---

## E23 — the stage-1 molecule can have atoms of degree 0, 1, 2 and self-loops

### Pinned text
- **The entry's L2122 is wrong.** "The proof is essentially the same as in Sections 9--10 of \cite{DH23}, with only
  minor differences due to the fact that here we are dealing with general gardens instead of couples" is at
  **TARGET L2117**. L2122 is the caption of Figure `fig:cut`. The same wrong number is in the summary table.
- TARGET L1306: "(some  discussion is needed when some trees of 𝒢 is trivial)". Correct.
- TARGET L1297 (`defcplmol`): atoms are branching nodes, with PC and LP bonds. L1295 allows self-connecting bonds.
- TARGET L826: mini couples and mini trees are defined "with no siblings paired", so primality (L870) does not exclude
  sibling pairings. L556–L564: ε is supported where k₂ ∉ {k₁,k₃} or k₁ = k₂ = k₃.
- DH23 L682 (Remark `moleremark`): no degree-2 atom or self-connecting bond without degeneracy. L1756: cuts are defined
  for degree 3 or 4. L1806: the structure of `finalmole`. L2169: Appendix B assumes no self-connecting bonds.
- **Not mentioned in the entry:** DH23 L1983 (§10.5(2)) ends with "As for self connecting bonds, they are left for now
  and will be treated in later steps", and L1987 (§10.5(4)) treats degenerate ε-atoms in 𝕄_fin.

### Checks
- **The degree formula.** deg v = 4 − [v root] − #{children that are leaves paired with a trivial root}, with a loop
  counting 2. Confirmed from L1297.
- **Example A.** The garden is irreducible (every proper subset of trees leaves a leaf unpaired). 𝕄 is one atom with
  no bonds, n = 1 and 2n − R = 0. It is the only degree-0 case: a degree-0 atom must be a root whose three children
  are all paired with trivial roots, and irreducibility then forces R = 2. 𝔄 = 1 ≤ RHS of (finalcount1). Confirmed.
  I did not re-check the "plain/balanced" pipeline predicates.
- **Example B.** A sibling pairing is allowed by primality. ε forces k₁ = k₂ = k₃, so the loop atom is degenerate with
  four equal legs. Confirmed. Note, however, that DH23 does *claim* to handle self-connecting bonds (L1983, L1987) as
  degenerate atoms in the couple setting. In TARGET the loop atom is tame, so its handling falls under `remtame` and
  hence under E11/E17. For example, a case-(i) β-cut along the loop pair isolates a zero-gap self-loop β-atom.
- **Example C is misdescribed.** "A root whose left and right children are leaves paired with two trivial roots gives
  an atom of degree 2 with two bonds of opposite direction". By the entry's own formula this atom has degree
  4 − 1 − 2 = **1**. The intended atom is a root with **exactly one** outer child (left or right, which has the root's
  sign) paired with a trivial root.
  - Its remaining bonds go to the middle child (sign −ζ) and the other outer child (sign ζ), so they have opposite
    directions.
  - Conservation gives c_v = k_{T_j} − k_{T₀}, a difference of two root momenta, as the entry says.
  - If instead the middle child were the trivially paired one, the two bonds would have the same direction and c_v
    would be a sum.
- **Is the gap routine?**
  - Degree-2 cuts are explicitly allowed by TARGET (L2126); their bookkeeping is E28 (EXPOSITION).
  - Degree-0 and degree-1 ε-atoms are covered by the Z term and the R ≥ 2 branch of `lgmolect` (L2195, L2197). The
    𝔄 ≲ 1 argument of DH23 Prop 10.1 goes through: LG degree-2 atoms cost L^{−η/2}, degree ≤ 1 atoms cost 1, and
    tame atoms of degree < 4 have fixed values by `subpro` (3).
  - Loops are removed exactly, with a gain of L^{−(d−γ)} each, because the ε-support fixes the loop momentum.
  - The cited research note (`low-degree-cuts-handoff.md`) itself reports "No false statement of TARGET found" and
    finds that TARGET's degree-2 β-cut accounting works where erasure fails (the Example C variant).
  - The one non-routine residue, tame atoms including loop atoms, is already recorded in E11/E17.

### Verdict: CONFIRMED WITH CORRECTIONS
The substance is right: DH23's §9 run is written for atoms of degree 3–4 with no loops, and TARGET's "essentially the
same" passes over the low-degree atoms and loops that gardens with trivial trees or sibling pairings produce.
Corrections:
- **Line number:** "TARGET L2122" → "TARGET L2117", in both the summary table and the entry heading/location.
- **Example C:** replace the first sentence with: "A root exactly one of whose outer children (of the root's sign) is a
  leaf paired with a trivial root has degree 2, with two bonds of opposite direction (to its middle child and its
  other outer child)." The rest of the example is unchanged. (A root with *two* children paired to trivial roots has
  degree 1. This is the degree-1 case, which the entry lists but does not illustrate.)
- **"Why DH23's proof does not cover 𝕄_sb":** add "DH23 §10.5(2) (L1983) defers self-connecting bonds to its
  treatment of degenerate atoms (§10.5(4), L1987), in the couple setting. In TARGET such loop atoms are tame and fall
  under `remtame` (see E11, E17)."
- **Class:** recommend GAP → **EXPOSITION**. Each ingredient of the repair is a routine extension, TARGET sketches most
  of them in passing (as the entry itself lists), no example violates (finalcount1), and the non-routine parts are
  already E11, E17 and E28. If the authors of the errata keep GAP, the entry should name the step that is not routine.
- The "Main theorem" column (repaired in Lean) was not checked by me.

---

## Remarks on tone (all six entries)
The entries are factual and generally fair. Points to soften, collected from above:
- "is false" in the E2c title;
- "no usable bound" in E17 and summary item 4;
- "FAILS" in E20;
- E11(c)'s "Prop 9.6 is false for a component" (better: "(finalcount) fails for the component X").

Each of the counterexamples in E11, E17 and E20 is at graph or local-model level. The entries should say so
consistently: E17 does, E11 and E20 do not.
