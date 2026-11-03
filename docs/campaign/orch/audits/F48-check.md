# F48 check: TARGET `remtame` (L2152), adjacent-atom vs crossing-bond criterion (Task 10b)

Auditor: `wt-orch` (Opus), refute-first. Date: 2026-11-03.

## Inputs

- **Write-up:** `docs/research/erratum-remtame.md` (sha `f34794e097c2…`, on main; merged into `w/orch` as `f775a79`),
  and FINDINGS F48.
- **TARGET:**
  - L625–L660: Def `deftree`, Def `defgarden`, Def `defdec`, coefficient (defcoef0) L556;
  - L826: Def `defreg` (mini-couple, mini-tree);
  - L870: prime gardens;
  - L1295–L1325: Def `defmol`, Def `defcplmol`, Def `defdecmol`;
  - L1955–L1965: (redvine), ε̃ and 𝒵;
  - L2042–L2046: Prop `subpro` (3), the definition of tame;
  - L2152: Rem `remtame`; L2218: Rem `remtame2`.
- **DH21** L2133–L2146: Def `defbridge`, Lemma `increF`, Lemma `cutlem`.
- **DH23** L1987: §10.5 (4).

## Verdict: CONFIRMED. The erratum is real, and the proposed correction is correct and sufficient.

- **The counterexample is valid in every claimed respect.** I checked it mechanically with exact rational arithmetic in
  `scratch/Task10b-F48-check.py` (sha `5f03d148e480…`).
- **`remtame` (i) is false as printed.** "Some component contains exactly one atom adjacent to v" does not imply that
  the labels at v are fixed.
- **The correction is exactly what the downstream argument needs.** It replaces both occurrences with "exactly one bond
  connecting the component to v", i.e. the bridge criterion of DH21 `increF`/`cutlem` and DH23 §10.5 (4).
  - Under the corrected (i), the labels are fixed.
  - Under the corrected (ii), there are at most 2 residual components, so Δχ ∈ {−2, −3}. That is precisely the dichotomy
    `remtame2` accounts for.
  - No other change to the Stage-2 counting is needed.
- **No frozen or drafted statement is affected** (§4).

## 1. The counterexample, checked

I rebuilt the garden from TARGET's own rules: child signs (ζ, −ζ, ζ); opposite-sign leaf pairing; bond orientation of
Def `defcplmol`; labels `k_ℓ = k_{𝔪(v,ℓ)}`.

**The tree layout I used.** The write-up specifies the garden through its molecule, and this is one realization:
- `A = [u, a_m, a_r]`, `u = [uB, v, uv]`, `v = [vu, vw₁, vw₂]`, `B = [b_l, b_m, bu]`;
- `C = [w, c_m, c_r]`, `w = [wv₁, wv₂, wD]`, `D = [d_l, d_m, dw]`;
- roots A, B, C, D with signs (+, −, +, −).

| Claim | Check | Result |
|---|---|---|
| Garden validity | The 9 pairs partition the 18 leaves with opposite signs. No proper subset of trees is closed under pairing. | ✓ irreducible, proper (R = 2) |
| Tree orders (3,1,2,1); V = 7, E = 12 = 2V − R | computed | ✓ |
| Molecule | u→v (PC) with v→u (LP); v→w and w→v (LP); A→B and B→A; C→D and D→C; u→A (PC), B→u, w→C (PC), D→w. Degrees u, v, w = 4 and A–D = 3. In/out ≤ 2. | ✓ exactly as described |
| Nonsaturated, connected, no self-loop, no triple bond | computed | ✓ |
| **Prime** | An embedded (1,1)-mini-couple puts 3 LP bonds between its two atoms. An embedded mini-tree puts PC + 2 LP between its two atoms (Def `defreg`, no siblings paired). Both are triple bonds, and there is none. | ✓ |
| Decoration | With k = s e₂, labels as in the write-up, and node labels `k_𝔫 = k_{𝔫₁} − k_{𝔫₂} + k_{𝔫₃}`, every root equals **−e₁/8** and the signature sum is 0. | ✓ |
| Coefficients (defcoef0) | A–D: children `(k, k + e₁/4, e₁/8)` up to swapping the outer two; the middle one is not in the others, so ε = +1. u, v, w: all children are k, so ε = −1. The product is **−1 ≠ 0** for every s. | ✓ |
| ε̃ · 𝒵 ≠ 0 (`subpro`, (redvine)) | ε̃ omits only hinge atoms, and there are none (`q_sk = 0`, no SG vine chain to merge), so ε̃ = ε. 𝒵 is the indicator of the chosen SG/LG/ZG classification of the vine-like objects. The four double bonds are vines (I): u–v and v–w are ZG, A–B and C–D are LG (gap ≥ 1/4). | ✓ for that classification |
| Fixed parameters | `c_v = (e₁/8, −e₁/8, e₁/8, −e₁/8)` at A–D and 0 at u, v, w. `Γ_v = (3/64, −3/64, 3/64, −3/64)` and 0. Both are **independent of s**. All labels lie in s-independent unit balls. | ✓ |
| ≥ L/4 free choices | `s ∈ [1/4, 1/2] ∩ L⁻¹ℤ` gives L/4 + 1 values (17 at L = 64, any L ∈ 8ℤ). Each is a valid decoration with identical (c_v), (Γ_v) and centres. | ✓ |
| Gaps and tameness | v (also u, w): all four labels equal k, so it is **ZG and tame** in the sense of `subpro` (3) (d = 4, so no fixed-value requirement). A, B: squared gaps {1/16, 5/64}, LG for large L. | ✓ |
| `remtame` applies to v | v is not a hinge, and a β-cut at v along the u–v pair disconnects, so v is an Operation 4 atom. ZG and non-hinge implies tame (`subpro` (3)), which is the setting of `remtame`. Operation 4 fixes no order, so the remark must hold when v is processed first. | ✓ |
| After removing v | Components {A, B, u} and {C, D, w}. Each has **exactly one atom adjacent to v** but **two crossing bonds of net orientation 0** and equal label k. `Σ_{x ∈ U} c_x = 0` identically: the cut identity (DH21 `cutlem`) is vacuous, so k is not fixed. χ goes from 6 to 4 (Δχ = −2). | ✓ |

**Conclusion.** The hypothesis of `remtame` (i) holds and its conclusion fails: the labels at v take ≳ L values. This is
also generic: any ZG-tame atom whose unique neighbour in a residual component is joined to it by an opposite-oriented
double bond breaks (i) as printed.

## 2. What the downstream argument needs

**Setup.** Let v be ZG and tame, so all labels at v equal one vector k. For a residual component U of `M \ {v}`, DH21
`cutlem` gives `Σ_{x ∈ U} c_x = (Σ_{ℓ crossing} ζ_ℓ) · k`.

**Corrected (i): d(v) < 4, or some U is joined to v by exactly one bond.**
- If d(v) < 4, tameness itself fixes k.
- If U is joined by exactly one bond ℓ, then ℓ is a bridge and `±k = Σ_U c_x` is fixed.
- Either way all four labels are fixed, the ZG degeneracy costs nothing, and "cut at v and proceed normally" is valid.

**Corrected (ii): d(v) = 4 and every residual component is joined to v by ≥ 2 bonds.**
- The 4 bond-ends at v (a self-loop counts twice) give at most 2 components, by DH21 `increF`: h/2 with h = 4.
- Hence ΔF ≤ 1 and **Δχ = ΔE − ΔV + ΔF ∈ {−3, −2}**:
  - four distinct bonds: ΔE = −4, ΔF ∈ {0, 1};
  - one self-loop: ΔE = −3, ΔF = 0, so Δχ = −2.
- The labels at v form a single vector with ≤ L^d choices, so 𝔍 ≤ L^d · L^{−2(d−γ)} = L^{−(d−2γ)}, up to the source's
  η and δ factors. This is `remtame`'s L^{−(d−2γ−η)}.

**`remtame2`.** Its case split is exactly "ΔF = 1, Δχ = −2: two new imperfect components, loss L^{2(2γ₀+5η²)},
covered by d − 2γ − 2γ₀ ≥ 1" or "otherwise Δχ = −3".
- The correction moves only one kind of configuration from (i) to (ii): a (2,2) split where some component reaches v
  through one atom by two bonds. Those configurations have ΔF = 1 and Δχ = −2.
- So `remtame2` holds unchanged. Its case (i), "modified trivially", is valid because the labels really are fixed.
- The printed (ii) was not wrong: its own negation also forces ≥ 2 bonds per component, hence ≤ 2 components. **The
  error is only in (i)'s conclusion.** Changing both occurrences, as proposed, keeps (i) ∪ (ii) exhaustive and
  disjoint.

**Agreement with the sources.** DH23 §10.5 (4) (L1987) splits on Δχ ≤ −2 against Δχ ≥ −1 ("one of the ℓ_j must be a
bridge … uniquely fixed due to Lemma 9.14 of DH21"). That is the corrected criterion verbatim, since a component joined
by exactly one bond is a bridge (DH21 Def `defbridge`).

**Remark (optional, not needed).** A sharper valid criterion would be "some component has nonzero net crossing
orientation"; then `(net)·k` is fixed and k is fixed. Its negation still forces ≥ 2 bonds per component, so ≤ 2
components. It only enlarges (i) by (2,2) splits with same-direction pairs, which the corrected (ii) already handles
through Δχ = −2. The proposed bridge criterion is the simpler one and matches DH21/DH23, so I recommend it as adopted.

## 3. Points left unchecked

- The Lean "scratch bridge lemmas" the write-up cites (GardenLocal, DEGENERATE-TAME.md) were not re-run. The
  conclusions above rest on TARGET/DH21/DH23 and my own computation.
- `subpro` (3), the claim that ZG non-hinge atoms are tame, is outside this erratum; the write-up says it stays valid.

## 4. Consequences for the campaign

- **B1 freeze candidate: unaffected.** `remtame` belongs to the Stage-2 reduction (TARGET §10: `excessprop1`,
  `remtame2`, `finalcount`), which is proof-internal to the G packets.
- **B2.3 `rigidity` (draft): unaffected at the statement level.** It abstracts `lgmolect`, whose ZG-tame ε-atoms are
  handled by DH23 §10.5 (4), which already uses the bridge criterion.
- **Citation fix to my Task 9b audit, R2.** "Tame" is *defined* in `subpro` (3) (L2044): all labels at v equal, and
  equal to a fixed root value when d(v) < 4. `remtame` (L2152) only uses it. G8 should transcribe it from L2044.
- **Ledger.** F48 can move from "independent check by wt-orch pending" to "confirmed (wt-orch F48-check.md)". The
  Stage-2 provers (G packets) must implement the bridge form of (i)/(ii).
