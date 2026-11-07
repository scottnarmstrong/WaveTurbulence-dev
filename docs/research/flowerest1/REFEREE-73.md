# Referee report 73: o73 RESOLUTION (OPEN 7.3, Theorem 7.3′)

Referee: independent, refute-first (wt-orch request, 2026-11-07). I did not write any of the refereed material.
Read-only elsewhere. No Lean, no git changes. Written as I went; complete (the verdict table is §1 and every fix is in §3).

## 0. Pins

The refereed draft was copied to my scratchpad at first read and hashed from the copy.

| File | sha256 at first read | Note |
|---|---|---|
| o73/RESOLUTION.md (refereed) | `683351431762e5dd0ebff1b84daeb5d623b0ab45ca39807bb7fc90d39a58f7bf` | 973 lines; §§16–22 are the conclusion |
| SUPPLEMENT-v1.md | `ddd81fe1…74d7` | matches its pin |
| o63/RESOLUTION.md | `a50e0f93…bc4` | matches the hash o73 §16 records |
| o75/RESOLUTION.md | `ab0c438c…5931` | **differs** from the `d7102c43…` o73 §16 records (that was pre-Rev. 1); I referee against the live Rev. 1 contract |
| o82/RESOLUTION.md | `7038cf6b…4e92` | matches o73 §16 |
| o104/RESOLUTION.md | `21e48492…73af` | o73 §19 prints a truncated/garbled hash `21e48492cd207fb986f37c9856f4b4cf7f89e6ea9fac273af` (editorial) |
| T / D21 / D23 | `493eef6b…727cb` / `50d0e236…fe402` / `c7e47dfa…35475` | match |
| ref/REFEREE.md, REFEREE-2.md, REFEREE-82.md, REFEREE-83.md | `c31ee38a…`, `028e5595…`, `4f42eb17…`, `56f98c77…` | context |

Notation: "S" the supplement, "T/D21/D23 n" a source line, "o73 §n" a section of the refereed file.

---

## 1. Verdict table

The o73 draft did not change during the audit: its hash was the same at the start and at the end. o82 changed
mid-audit to its Revision 1; see §2.5.

| # | Step (o73 section) | Verdict |
|---:|---|---|
| 1 | Consumed-modulation operator, Lemma 12.1 (+ Prop 5.1; Lemma 12.2 unused) (§12) | **PASS** |
| 2 | Terminal pin with arbitrary ordinary layered side objects: exact cut (13.1), Prop 13.2, output extension (13.4) (§13) | **PASS AFTER FIX** (73-F2) |
| 3 | First child face, Prop 14.1 (§14; history, not consumed) | **PASS** |
| 4 | Consumer separation: unweighted time-Fourier mass suffices outside unmarked vine interiors unless a selected residual vertex consumes it (§16) | **PASS** |
| 5 | Regular-object estimates (17.1)–(17.3) and the boundary-incidence observation (§17) | **PASS AFTER FIX** (73-F2) |
| 6 | Residual coefficient with pins, endpoint faces and local suprema, Prop 18.1 (§18) | **PASS** (editorial 73-E1) |
| 7 | Root trace (19.1) and consumed child identity (19.2) (§19.1) | **PASS AFTER FIX** (73-RT) |
| 8 | Punctured-chain coefficient, Lemma 19.1 (§19.2) | **PASS AFTER FIX** (73-L19) |
| 9 | Individual faces, Prop 19.2, and F_ch (§19.3) | **PASS AFTER FIX** (73-UF, 73-P8) |
| 10 | Residual selected vertices, Prop 20.1, including cancellation of β_v by a large adjacent frequency (§20) | **PASS AFTER FIX** (73-REC, 73-F2) |
| 11 | wt-orch item, from REFEREE-82 F1: M₂^{−1/18} at skeleton and residual selected vertices; reciprocal (9.1) | **PASS as a variant.** Inside regular objects the reciprocal is kept. At residual vertices it is replaced by the valid Prop 20.1 dichotomy. Wording fixes are needed in o75 and o82 (73-W). |
| 12 | Sufficiency of Thm 7.3′ for o63 Prop 10.3′ with o75 Rev. 1 (faces, (G-ret), uniformity, row 12) (§21) | **PASS AFTER FIX** (73-PIN) |
| 13 | Numerical ledger: c_{7.3} = 400d per protected incidence, total 10400dP; doubled budget (§§21–22) | **PASS** |
| 14 | Constants and quantifier order: no L^{Cn}; bases independent of δ | **PASS** |
| 15 | Gain retention: zero final lost units; ≤ 1 intermediate unit per side-child face, repaid | **PASS** |
| 16 | Cited lines | **PASS AFTER FIX** (editorial 73-C) |

**No FAIL.** I found no counterexample to any step that Theorem 7.3′ relies on. I found no hidden L^{Cn}, C₂^n or
δ-dependent exponential base. Every fix is at the level of a statement, a citation or wording. None changes an
exponent.

**Structural observation.** The plain `flowerest1` assembly uses only rows 1, 2, 4–6, 10 and 12–15. Rows 7–9 (§19)
are used only by the derivative patterns, through o104 Theorem 10.4.

---

## 2. Work log

(sections below are appended as each step is checked)

### 2.1 Structure of what the assembly actually consumes (orientation)

Reading §§16–21 against o75 Rev. 1 §§4.6–4.9, 7, 8 and o82 Thm 18.2/8.2′:

- **Plain `flowerest1`** uses, from o73: §12 Lemma 12.1, §13 Props 13.1–13.2 (via o82 Cor 15.2), §17 (17.1)–(17.3)
  (= o82 Lemma 16.1 / Cor 15.2 / Thm 18.2 restated), §18 Prop 18.1 (residual pins/faces in the fine bound), §20
  Prop 20.1 (M₂ gain at residual = skeleton selected vertices), and the ledger §§21–22.
- **§19 (root trace, Lemma 19.1, Prop 19.2 individual faces, F_ch)** is consumed only by the derivative patterns
  (o104 Theorem 10.4, Addendum 4). In the plain assembly every selected face is handled either inside a protected
  regular kernel by the whole signed collection ((17.3) = o82 Thm 18.2) or in the residual by §20; neither uses an
  individual raw face. I confirmed this by tracing every use of "Prop 19.2"/"(19.7)" in §§20–22.
- §14 (Prop 14.1) is retained history and is not consumed; §15 contributes only the floor-face observation and the
  identity (15.2), both re-used in §19.

### 2.2 §12 — the consumed-modulation operator: PASS

- (12.3) re-derived: for H = e^{πi(ξt+λu+νs)}, ∫_s^t e^{πiA(u−s)}H du = e^{πi[ξt+(λ+ν)s]}·h_{A+λ}(t−s) exactly
  (the e^{−πiAs} is cancelled by e^{πi(A+λ)s}/e^{πiλs}). The phase is centred at the lower endpoint s, so the output
  carries **no** ⟨A⟩^θ; this is exactly the consumption the supplement demanded (S450–452).
- Prop 5.1 (uniform A^θ bound for Φ(t,s)h_z(t−s), 0≤θ≤1): large |z|: two translates of Φ̂ divided by |z|, weight
  ≤ C(1+|z|^θ)/|z|; small |z|: integral representation with bounded frequencies. Correct.
- Translation by (ξ, λ+ν) costs ≤ C max(⟨ξ⟩,⟨λ⟩,⟨ν⟩)^θ (Peetre); integrating against |Ĥ| gives (12.2). The
  extension is Φ·(smooth formula), agreeing with the kernel on the open triangle; no discontinuous zero extension.
- Domain caveat (minor, already respected downstream): (12.2) needs H defined on ℝ³ and equal to the true integrand on
  {s<u<t}. In every use the four factors are extensions of kernels whose defining domains contain {s<u<t} (the cut
  (13.1) has K_pre(t,u), K_in(u,s), Q_i(u,s)); the one place where this fails is o104's root trace, which o73 §19.1
  repairs (port lower bound; see 2.6).
- Lemma 12.2 (tensor coefficient version): correct (multi-index splitting over disjoint J_i, ∏(2|ρ_i|)! ≤ (2|ρ|)!,
  max-moment by sum of maxima), but **not used** by Theorem 7.3′.
- The §5 counterexample (J_A1 vs J_A(e^{−πiA·})) correctly identifies the forbidden shortcut; Lemma 12.1 does not
  take it.

### 2.3 §13 — terminal pin with arbitrary ordinary layered side objects: PASS AFTER FIX (inherited F2)

- **Cut (13.1).** Legal = non-crossing (T849: no a<b<c<d with {a,c},{b,d} ∈ 𝒫). With {a,2h} a pair, any
  i<a<j<2h with {i,j} ∈ 𝒫 is a crossing; so prefix 1..a−1 and interior a+1..2h−1 are each legally paired. The two
  side couples of the pair {a,2h} pair the off-chain children of n_a and n_{2h} (T855–857), so they are functions of
  (t_{n_a},t_{n_{2h}}) = (u,s). Every other side couple belongs to a pair inside one of the two sub-chains. Conditional
  on (u,s) the chain inequalities factor. The pin removes only t_{n_{2h}}. Correct; REFEREE-82 reached the same
  conclusion independently.
- **Prop 3.1 geometry** (the chain is layer p; an object containing a stem vertex is (T′,cap) or a stem-rooted paired
  tree; f^pr is the terminal chain node): re-checked against T845–846, T857, T877 and the stem-layer property. PASS.
  Consequently the exceptional link {a,2h} is same-layer and no incoherency is removed.
- **Prop 13.2.** Normalization re-derived: (δ/2L^{d−γ})²·(CL)^{2d} = Cδ²L^{2γ}, so the pin costs exactly
  μ = δL^{2γ} ≤ L², consistent with (19.8) and o82 (13.4). The output-ball extension (13.4) by disjoint bumps
  ψ(L(k−k₀)) costs L^{30d}·L^{d}. PASS.
- **Fix (inherits REFEREE-82 F2).** Summing the exceptional pair over its unit-box *centres* needs the output decay of
  the two side couples Q₁,Q₂ (their outputs are affine in (x,y)), i.e. their weighted X^{η,30d,30d} (resp.
  X^{1/4,30d,30d} for (17.2)) bounds, or the profile decay if a side couple is trivial. o73 only says "summing
  localization coefficients requires the ordinary summable profile localization". State it explicitly, and state
  (17.1) for couples in the weighted form. No exponent changes (T995/T999 give the weight at the same L^d).

### 2.4 §14 — the first child face: PASS (not consumed)

- (14.2)–(14.3) re-derived by integrating x over (max(s,u),t): top = e^{πiA(t−s)}H_β(t)H_{−β}(s); lower on u<s =
  H_β(s)H_{−β}(s); lower on u>s = e^{−πiAs}∫_s^t e^{πi(A+β)u}du·H_{−β}(s). Signs and multiplicities correct.
- Frequencies of F^child: (A+β,−A−β), (A+β,−A), (0,β), (0,0) — confirmed. (14.6) and the three-region integration
  give a bound uniform in A for θ<1; (14.5) needs p₀+θ₀<1 for the tail, satisfied by the D23 exponents
  (1−η/2)+η/4 < 1. Correct, but the result is superseded by (19.1)–(19.2) and not used by Theorem 7.3′.

> **Mid-audit change.** o82/RESOLUTION.md changed during this audit: `7038cf6b…` (the version o73 cites) →
> `d5b09e81…` (o82 Revision 1, §22, applying REFEREE-82 F1–F6). The statements o73 uses are unchanged except that
> Lemma 16.1 now **is** stated in the weighted form X^{1/4,30d,30d} (couples) / X^{1/4,30d,0} (trees), and Cor 15.2 and
> (18.6) now sum exceptional box centres explicitly. A pinned copy of the revised file is in my scratchpad.

### 2.5 §16 (consumer separation) and §17 (regular-object estimates used): PASS AFTER FIX

**§16, "unweighted time-Fourier mass suffices for protected factors outside unmarked vine interiors".** Checked against
T. The factor (max_𝔫(⟨ξ⟩+⟨ξ_𝔫⟩))^{−2η⁸} in (redvine2) (T1963) is the leftover of the vine factors' X^{2η⁸,0,0} bound
(vineest2, T1742–1760) and is never consumed: (finalsbest1) (T2081–2083) and (finalsbest2) via (redvine5) (T2091–2096)
are uniform in ξ_v; the ladderl1old coefficient (T1994–2037) is uniform in ξ (it enters only c_w, d_w at T2009–2015
and the shifts in Step 3); the count in (redvine5) depends on ξ only through (β_v) (T2096 (a)), uniformly; and
(finalproof1)/(finalproof2) (T2220–2225) contain no ξ. So a protected factor need only supply Fourier L¹ mass (with the
local output derivatives of T1965) unless a selected residual vertex consumes a moment. **Correct.**

**§17 (17.1)–(17.3).** These restate o82 Prop 15.1 + Lemma 16.1, Cor 15.2, Thm 18.2 (which REFEREE-82 passed). I
compared each display with o82: exponents, gains and uniformity match ((17.3) = o82 (18.3), L^{(47d+5)r}M₂^{−a/18};
the interpolation (17.4) with τ = (1−8η)/9 ≥ 1/18 iff η ≤ 1/16, re-derived from A^{1/8} after the fold extension).
- **Fix 73-F2 (inherited REFEREE-82 F2; now resolvable by citation).** (17.1) is stated "at fixed spatial boundary
  data". Its consumer (the moment (20.2) at a selected residual vertex) sums the adjacent couples over their T1959
  unit-ball localizations, which needs the output-weighted form. Cite revised o82 Lemma 16.1 (X^{1/4,30d,30d} for
  couples, X^{1/4,30d,0} for trees). This also makes the L^{31d} output conversion for *ordinary* adjacent factors
  unnecessary, so the 7(47d+2) charge in (20.3) is an over-count. No exponent increases.

**Boundary-incidence observation (§17, last two paragraphs).**
- "At most seven regular kernels at a residual vertex": T_(v), ≤3 trees at children, ≤3 leaf-pair couples. Correct
  (an over-count; children total ≤ 3).
- "No adjacent kernel of a selected residual vertex contains another selected stem vertex": a kernel adjacent to v lies
  in v's garden tree; one selection per original tree; a couple containing a stem vertex is (T′,cap) of that same tree
  (Prop 3.1). Correct. So (17.1)–(17.2), not (17.3), give the strong norm there.
- "No unmarked spliced vine has a selected residual boundary argument": checked through o75 Π2 (raw parent and ≤3 raw
  children of 𝔳_j are protected) and Definition 2.3 (A(𝕍) contains T_(𝔪), 𝔪 ∈ 𝒩[𝕍]∖{𝔲₁}, and the couples at
  ℒ[𝕍]). If v = 𝔲₁, the raw child toward the vine lies in A(𝕍). If v ∈ {𝔲₂₁,𝔲₂₂}, the parent 𝔲₂ is on the stem, so
  the stem would leave the SG realization through 𝔲₂₁/𝔲₂₂, which S Lemma 9.2 excludes in the M₂ version (o75
  Lemma 2(d)); o73's own wording ("its parent toward 𝔲₂ is protected") reaches the same conclusion. Correct.
- All adjacent kernels of a selected v are protected (each contains a protected raw parent/child of v), hence common
  factors of every congruence′ class; their individual kernel bounds are legitimate (no LF cancellation needed).

### 2.6 §18 — residual coefficient with pins, endpoint faces and local suprema: PASS (with remarks)

I re-ran T's four steps of `ladderl1old` (T2003–2037) with the modifications of Prop 18.1.
- **Step 1 (dephased box inequality, T2005).** Applied only in Eᶜ; E atoms carry no σ-sum (their β is frozen and
  summed in the count: o75 row 12, S Lemma 7.1). The affine rung relations (localize1) (T2013) are decoration
  identities and survive fixing β_E; every α_v ∈ 𝒮_v (≤ L^{20d} unit intervals). (18.4) by rearrangement is correct.
- **Step 2 (X variables).** Each atom lies in at most one rung of a maximal ladder; removing the orientation at E atoms
  and recipients removes ≤ 2r (o73 allows 4r) variables from X. A retained X atom keeps its Y mate and its reference
  atoms (in Y or E), so its α stays in an O(1) interval given α_Y. The "no local maximum" monotonicity (T2022–2024)
  uses only parent–child inequalities, which hold weakly on a face (a face is a piece of the closure of the original
  domain); the volume bound is unchanged for weak monotonicity. Factorial loss z!/(z−h)! ≤ (N+1)^h. Correct.
- **Step 3 (Y integration).** After contraction/pins the domain is still a rooted forest with constant lower bounds and a
  unique variable upper bound; a maximizing-child face makes the other children children of the recipient. Fixed-α
  atoms with retained time are bounded by C; frequency transfer to the parent keeps the triangular change of variables
  unimodular. Correct.
- **Step 4.** C^{N+1}(N+1)^{4r}(log L)^{4r}𝓡_N; (N+1)^{4r} ≤ C_r^{N+1} with C_r depending on r ≤ 26P only (δ-free);
  (log L)^{4r} ≤ L^{4r} is very generous. The D-power and N are the original ones, so T's final Dδ ≤ δ^{−ν} comparison
  is untouched. Correct.
- This is a genuine local-supremum estimate (the box inequality is applied before absolute values), so it fills the
  T1998 consumer the supplement required. The count side needs no change: a count with Γ_E fixed is a sub-count of the
  count with α_E in a unit box (T2096 (a)), uniformly in (β_v).
- Remark (editorial): Prop 18.1 says "at most one selected endpoint substitution per original tree"; with F_ch in the
  pattern case two atoms (m and 𝔣^pr) are pinned at s in one tree. The rooted-forest argument covers it (o73 says so
  after Prop 19.2), but the hypothesis should be worded "at most one selected substitution and a bounded number of
  pins per tree".

### 2.7 §19.1 — root trace (19.1) and the consumed child identity (19.2): PASS AFTER FIX

(o104 Prop 7.4, L543–604, read in full; T854–857, T877 for the case list.)
- o104 Prop 7.4 proves the form e^{πiεB(σ−q)}R_B with ‖R_B‖_{A^θ} ≤ C_θ∏_{i≤4}‖P_i‖_{A^θ}, uniformly in B, 0≤θ≤1, in
  all three root cases (type-2 couple/tree with mate on the same chain; type-1; type-2 with m_ε=0). The case list is
  exhaustive by T854–857/T877. The incoherency count g − ε_g is right.
- **o104 has a domain flaw that o73 repairs (record for the o104 owner).** In o104 case (a) with the mate in layer p,
  o104 integrates u from the layer floor; for a paired tree the factor K_rest(u,τ_w) is defined only for u > τ_w, so an
  A^θ extension would be integrated over (p,τ_w) where the true integrand vanishes (worst when the suffix is empty, so
  that no P_i carries the constraint). o73's convention — integrate from the port time when the port has the mate's
  layer, i.e. T′_B(σ,τ_w) — is correct and necessary; uniformity is o104 Lemma 7.1 (items 2, 3, 6).
- (19.2) re-derived: ∫_s^t e^{πiA(u−s)}e^{πiεBu}RQ₂du = e^{πiεBs}∫_s^t e^{πi(A+εB)(u−s)}RQ₂du exactly; centring at q only
  adds the unimodular e^{−πiεBq}; T_{A+εB} is uniform by Lemma 12.1. The leftover phase is a function of s only (fixed
  external time, or a translation of a residual ξ handled uniformly by Prop 18.1). This is the genuine resolution of
  the §15 norm-only obstruction (it uses the kernel's linked structure, never ∂Q bounded by ‖Q‖).
- **Fix 73-RT.** (19.1) omits Prop 7.4's hypothesis that the traced root ρ is in layer p (true in every use: a side
  root can be a maximizer only if it is in layer p; F_ch's m is layer p by the pattern validity condition). Also say
  that R_B may depend on a third boundary time (τ_w, or the port/floor), which the "…" hides.
- Note for the o104 owner (not an o73 defect): o104 (7.2), read literally, puts e^{πiA(t−s)} (P2) and e^{πiεBs}
  (P7/P8) inside an uncentred X^η norm "uniformly in the linked frequencies", which is false (it grows like ⟨A⟩^η).
  o73 §19 explicitly reads it as a centred bound plus consumption, which is correct.

### 2.8 §19.2 — Lemma 19.1, the punctured legal chain: PASS AFTER FIX

(D21 925–1160 read; spot-checked D21 957, 1046–1060, 1084–1094, 1142.)
- **κ = η/16 for 1/4.** D21's class-J/R weights are a single subadditive weight per operator (typeJ2/typeR2,
  D21 955–961); every use pays |·|^{1/4} from one denominator and keeps ⟨·⟩^{−3/4}. With κ < 1/4 the kept power is
  larger, so all displayed uniform integrals (D21 1011–1067, and "3/4-th power" at ~1140) hold with C_κ fixed before
  δ. The two-denominator Cauchy–Schwarz (powers 1−κ and 1, both > 1/2) is right. Correct.
- **Slots.** I_ω = J_{0;0,ω}; D21 957 states the J-weight "does not involve |γ₂|", and (extraid) (D21 1057) smooths the
  Dirac; when a slot is a left factor, |ω|^κ is paid by the J″ denominator as D21 does for |γ₂|^{1/4}. regchainlem7
  (D21 1084) allows any class J/R operator as X_a with X_a ≠ Id between adjacent pair members; o73 extracts a reciprocal
  only when X_a = Id. Deleting pairs keeps a legal (= non-crossing) partition. Correct.
- **Side kernels.** They enter only through their values at (t_a,t_b), i.e. as D21's λ-modulations, uniformly; the
  single non-uniform step is pole restoration, (differenceloss) at D21 1142: C log(2+|λ_a|) ≤ C_κ⟨λ_{a,1}⟩^κ⟨λ_{a,2}⟩^κ.
  The 4κ-per-endpoint, 8κ = η/2 ≤ η per side kernel charge fits the X^η weight max⟨λ_i⟩^η ≥ ⟨λ_a⟩^{η/2}⟨λ_b⟩^{η/2}.
  This is legitimate only because the chain itself is single-layer (Prop 3.1): all incoherency lives in the side
  kernels' own norms. Correct.
- **Fix 73-L19 (statement).** (19.4) integrates the side variables Λ against D(Λ) for each ρ. o82 Thm 10.1 takes a
  coefficient C_*(ν,v,α_J) at a *fixed* external parameter v with one bound B·A^{n+|ρ|+1}(8|ρ|)! and one amplitude
  W of mass D₀. The proof of Lemma 19.1 in fact gives a bound pointwise in Λ, factorized in ρ, with amplitude W_Λ of
  mass D(Λ). State (19.4) in that fixed-Λ form, apply Thm 10.1 at fixed (E,Λ), and integrate in Λ afterwards
  (Thm 10.1 is linear in (Ψ,W)). Also note that the chain's output transform is a measure on a line, so a fixed cutoff
  is needed to make it a density (as §12 says).
- (4|ρ|)! ≤ (8|ρ|)! is what Thm 10.1 / Lemma 11.1 need; upper filters on chain coordinates are ϑ(α_j/(μM)) in the
  original coordinate (T986), inserted by o82 Lemma 11.1 (J), g_S/Prop 2.1 (Z), or as bounded scalars (E). Correct.

### 2.9 §19.3 — Prop 19.2, individual faces, F_ch: PASS AFTER FIX

- **Lower faces, cell by cell: correct.** Stem-child cell: the cell condition "side roots < t_c" is exactly evaluating
  v's side couples at upper argument t_c. Side-child cell: t_v = t_ρ = u lies between the neighbouring chain times; the
  stem child is below u by chain order; the other side root is below u through Q₂(u,·). The εB phase goes to the slot
  at u, the mate is a slot, the rest stays legally paired. Recipients that are boundary times go into ℓ_E. At most two
  exceptional pairs per incidence: correct. The stem floor face is empty inside regular objects (the stem child, or the
  port, has time ≥ s > p).
- **Fix 73-UF (statement).** The rule "side couples are simply evaluated at the substituted upper argument" holds for
  the upper (top/parent) face only after **reuniting the maximizer cells** (as §14 itself does). Per cell, the upper face
  carries 1[t_ρ > t_c, t_ρ > t_{ρ₂}], an indicator coupling a side couple's *internal* root time to the chain and to the
  other side couple; that is not of the form Lemma 19.1 handles. Every consumer needs only the reunited upper face
  (o104 Lemma 6.1, L355–359, defines dRoot as the top face summed over pieces; M₂-selected faces never go through
  Prop 19.2). State in Prop 19.2 and Theorem 7.3′(1): upper faces are taken summed over the maximizer cells (a
  same-sign retained sub-collection); lower faces per cell.
- **Fix 73-P8 (editorial).** When F_ch sits in a separate object 𝒪^m ((P8)), that object's chain need not be
  single-layer, so Lemma 19.1 does not apply; its representation is (19.1) (four ordinary factors under T_B), not
  (19.3). Cost unchanged (one exceptional link, L²·L, plus L^{31d}). Prop 19.2's sentence "these expressions have a
  representation of form (19.3)–(19.4)" should exclude this case.
- **Cost (19.7).** Re-derived: (δ/2L^{d−γ})^{2m_c}L^{2de}(L^{2d}/μ)^{m_c−e} = (δ/4)^{m_c}μ^e, μ^e ≤ L^{2e}; only side
  root links can be incoherent, each restored at ≤ L^{γ₁} ≤ L; total L^{3e} ≤ L^{6r}, plus L^{31d} once per object
  ≤ L^{31dr}. Consistent with (31d+6)r.
- **F_ch.** o104 Lemma 3.1 (L166) and Lemma 6.3 (L377–392) define F_ch exactly as (19.6). In-object: (P7) is the root
  trace of Q₁ at σ = s inside the cut (13.1); (P8) a root trace of a separate object. Residual: pinning m in E of
  Prop 18.1, with the dropped inequality, keeps the rooted-forest form (two pinned atoms → two exceptional α's,
  o104 §7.4(β)). The phrase "exactly those of the flower-parent pin" is loose (at coefficient level it is the side-child
  root-trace mechanism) but harmless.
- **Scope.** Prop 19.2 is reciprocal-free and gives no M₂ gain. It is used only for the non-plain pattern faces, for
  which the frozen statement requires no M₂ factor (o104 (2.1), §2.2 L120–124, §4.3, L792). Correct.

### 2.10 §20 — selected residual (skeleton) vertices, including cancellation by a large adjacent frequency: PASS AFTER FIX

Setting checked against T1954–1974 and o75 §§2.2, 4.6–4.9. A selected skeleton atom v carries its annular factor,
|β_v| ≥ cμM₂ (S (8.1) shell telescoping; S Lemma 9.1's hypothesis). After Fourier-expanding the ≤ 7 adjacent regular
kernels (all protected, all free of other selections; §2.5), the t_v-dependence of the residual integrand is exactly
e^{πiα_v t_v}, α_v = β_v + ξ_v, times the residual order inequalities: I checked every other factor of (redvine3)
(K_(ℓ), K^†, ε̃, 𝒵, filters, shells, annuli are k-only; no unmarked vine factor sits at v; the T1963 weight is dropped
by §16; dephasing never acts on E). Fubini is legitimate (Fourier L¹ × bounded time domain).
- **H_v = {|ξ_v| ≥ |β_v|/2}.** No reciprocal; 1 ≤ C(μM₂)^{−1/18}⟨ξ_v⟩^{1/18}, and ⟨ξ_v⟩^{1/18} ≤ C₇∏⟨λ_i⟩^{1/18} is
  paid by the adjacent X^{1/4} norms (≤ 2/18 < 1/4 per kernel, since a kernel has ≤ 2 time arguments). This is exactly
  the cancellation case α_v ≈ 0: **no lower bound on |α_v| and no 1/β_v is used.** Correct.
- **L_v = {|ξ_v| < |β_v|/2}.** |α_v| ≥ |β_v|/2; integrating the single exponential over the residual interval
  (max(residual children, floor), parent/top), partitioned by the maximizer, gives upper minus lower faces with the
  exact factor (πiα_v)^{−1}, |·| ≤ C(μM₂)^{−1} ≤ CM₂^{−1/18}. The recipient's frequency is translated by α_v, and
  Prop 18.1 is uniform in that translation (dephasing is in the original α_rec; ∫_{𝒮}⟨α+c⟩^{−1} is uniform in c).
  The integrations at different selected vertices commute (distinct garden trees). Correct.
- **Both bounds, then interpolation.** For fixed (ξ,β_E) both the crude bound and the fine bound carry the same factor
  ((μM₂)^{−1/18}⟨ξ_v⟩^{1/18} ≥ 1 on H_v, |α_v|^{−1} on L_v); min(A,B) ≤ A^θB^{1−θ} with θ = 40ν (T2220) keeps
  M₂^{−a/18}; then sum β_E (o75 row 12) and integrate ξ. The crude bound needs no freezing of β_v (the dichotomy
  indicator and (πiα_v)^{−1} depend only on bonds at v, which are ladder-boundary data). Correct.
- **Fix 73-REC (statement; the argument survives).** The sentence "every selected atom and every possible recipient lies
  in the protected split set of o75. Thus none lies in the interior of a retained ladder" is **false for the upper
  (parent) recipient**. Π2 protects v's *raw* parent; when the regular tree T_(v) attached at v is nontrivial, that raw
  parent lies inside T_(v) (so the atom v ∈ Π_sb), but the residual parent v^pr — the recipient of the residual upper
  face — need not be in Π_sb and may be an interior atom of a retained ladder (stem atoms can be ladder atoms; cf.
  Lemma F). The conclusion still holds: o75's crude bound is the E5-repaired kernel core 𝔎(𝕃;𝔅) = ∫_𝔅|Σ_{k[𝕃]}…|dt
  (o75 §4.8 Step 0), with the absolute value inside the time integral and the ordering dropped. After the face, the
  extra factors on t_{v^pr} (the phase e^{πiα_v t_{v^pr}}, the indicators t_c < t_{v^pr}) are independent of k[𝕃]
  (α_v depends only on bonds at v, which are ladder-boundary bonds), so they come out of |Σ_{k[𝕃]}| with modulus ≤ 1.
  Replace the false sentence by this argument. Child recipients and floor recipients are fine as stated (a raw child
  of v protected ⇒ the residual child atom ∈ Π_sb).
- **Fix 73-F2 again.** The adjacent X^{1/4} bounds must be the output-weighted/local ones (revised o82 Lemma 16.1) so
  that the T1959 unit-ball sums of adjacent couples converge. With the revised lemma the ordinary adjacent factors cost
  L^{4d} locally; (20.3)'s 7(47d+2)a is then an over-count.

**wt-orch's extra item (REFEREE-82 F1: "M₂^{−1/18} at skeleton/residual selected vertices from S Lemma 9.1 plus the 7.3
face estimates, keeping the reciprocal (9.1)").**
- *Inside protected regular objects* the reciprocal **is** retained: (17.3) = o82 Thm 18.2 applies S Lemma 9.1 before
  absolute values, keeps all a reciprocals in the L^∞ bound (18.4), and interpolates against the whole-kernel A^{1/4}
  bound. Nothing in o73 drops it.
- *"Reciprocal-free"* (Prop 19.2, o104 reading R1) applies only to the individual dRoot/dParent/dChild pattern faces,
  which are non-plain; the frozen statement asks for M₂ only on all-plain vectors (o104 (2.1), L120–124, §4.3). So no
  M₂-selected face is estimated reciprocal-free.
- *At skeleton = residual selected vertices* o73 does **not** keep the raw reciprocal (iω_v)^{−1} = (πiβ_v)^{−1} of
  S (9.1). It replaces S Lemma 9.1 there by an exact rearrangement at the Fourier level (the residual t_v integral after
  the adjacent kernels are expanded): reciprocal (πiα_v)^{−1} of the **total** frequency on L_v, and the moment (20.4)
  on H_v. This is deliberate and, in my judgment, the correct consumption: the raw reciprocal 1/β_v *after* Fourier
  expansion would be precisely the forbidden shortcut of §5 (ignoring the incoming modulation ξ_v, which can cancel
  β_v), while applying S Lemma 9.1 in the raw garden would put faces at raw children that are roots of adjacent
  regular objects, i.e. root traces of those objects in the residual — a route o73 did not take.
- *Is this sufficient for the contract?* Yes. What o75 consumes is M₂^{−1/18} per occurrence on both bounds before
  interpolation (o75 §8(vi), §11.6: "each giving at least M₂^{−1/18}"); no row of o75 §7 uses the extra
  (cδL^{2γ})^{−1} of the raw reciprocal (row 13's B-contribution is 0; face atoms pay row 12 separately). Prop 20.1
  delivers M₂^{−1/18} per residual occurrence, repeated occurrences counted, on both bounds.
- **Wording fixes outside o73 (recommended):** o75 row 13 and §11.6 ("gain (cδL^{2γ}M₂)^{−1} … from S Lemma 9.1") and
  o82 §19/§22-F1 ("retaining reciprocal (9.1)") should read: "inside regular objects S Lemma 9.1 with the reciprocal
  retained (o82 Thm 18.2); at skeleton/residual selected vertices the o73 Prop 20.1 dichotomy, giving M₂^{−1/18} per
  occurrence". o73 itself should cite o75 **Rev. 1** (it still records the pre-Rev. 1 hash `d7102c43…`) and say
  explicitly that Prop 20.1 is what discharges Rev. 1's row 13/§11.6 obligation.

### 2.11 §21 — sufficiency of Theorem 7.3′ for the assembly (o63 Prop 10.3′ with o75 Rev. 1): PASS AFTER FIX

I matched Theorem 7.3′ against every consumption point of (C7.3) in o75 Rev. 1:
| o75 consumer | what it needs | supplied by | verdict |
|---|---|---|---|
| §4.8 (finalsbest1′): protected objects "by their 7.3/8.2 bounds"; pinned/face atoms carry no time integral | local X-norm bounds of pinned objects; faces at residual vertices | (17.2) (= o82 Cor 15.2); §20 crude part (with Fix 73-REC) | PASS |
| §4.7 (finalsbest2′): "pins and faces in the time-L¹ factor belong to OPEN 7.3" | ladderl1old with pins/faces, local suprema, frozen E | Prop 18.1 (18.3) | PASS |
| §4.6 / row 12: frozen resonances at pin/face atoms | ≤ 2 per pin, 1 per face | residual E = pins + selected atoms (+ F_ch's m in patterns); in-object exceptional pairs are summed as spatial tuples inside o73's own (19.8) | PASS |
| row 13 / §11.6: M₂ gain at skeleton selected vertices | M₂^{−1/18} per occurrence, both bounds | Prop 20.1 (variant mechanism, §2.10) | PASS (wording fix in o75/o82) |
| §8(iii): wholly regular components with a flower–cap pair | fixed-output bound, M₂ inside | o82 Thm 18.2 (18.2) | PASS |
| (G-ret) | ≤ 10 lost units per incidence | 0 lost finally; ≤ 1 intermediate unit per side-child face, repaid at L | PASS |
| uniformity; δ-independent base | (t,s,k,k′,M₁,M₂,ζ), 𝒫(2c_χC₁) | (16.1); bases C_{P,χ}, C_r, C_κ chosen before δ | PASS |
| exponent ceiling | c_{7.3} ≤ 19,000d³ per incidence | 400d | PASS |

Geometry: under o75's non-excision route every protected regular object is an initial-skeleton object of Prop 3.1
type (marked vines unspliced, nothing cut), as REFEREE-82 §2.2 also found. External decay and M₁ come from o63's
extrapolation at zero L-cost. Derivative patterns: o104 Thm 10.4 consumes Prop 19.2 (after Fixes 73-UF, 73-P8,
73-L19, 73-RT) and F_ch; the M₂ factor is not required there.

The fix needed here is bookkeeping: o73 §16 pins o75 at the pre-Rev. 1 hash `d7102c43…`; it should cite Rev. 1
(`ab0c438c…` at my read) and state that Prop 20.1 discharges Rev. 1's skeleton-selected obligation (row 13/§11.6).

### 2.12 §22 — numerical ledger: PASS

- (21.3): worst case is all incidences residual selections: 7(47d+2)+4 = 329d+18 per incidence; (329d+18)b ≤ 347db
  < 400db for d ≥ 1. With b ≤ 26P: 10400dP. Correct (very generous; with revised o82 Lemma 16.1 the true residual
  charge is ≈ 7·(16d+2)+4 per selection, and the regular-object charge (47d+6)r_reg duplicates o82's own c_{8.2} —
  both harmless over-counts).
- (22.1): 9384d+416.01+26(400d+c_{8.2}) = 19784d+416.01+26c_{8.2}. ✓. (22.2) at c_{8.2} = 19,000d³:
  494,000d³+19864d+419.12 < 10⁶d³ ⇔ 19864d+419.12 < 506,000d³, true for d ≥ 1. ✓.
- (22.3) with c_{8.2} = 47d+5: 9384+10400+1222 = 21006d; 416.01+130 = 546.01. ✓; B+80d+1/9+3 < 10⁶d³. ✓.
- Doubled (b ≤ 30P): o75's derivative rows give 10936d + 30c_{7.3} + 30c_{8.2} + 483.2; with c_{7.3} = 400d and
  c_{8.2} = 19,000d³: 570,000d³+22936d+483.2 ✓; with c_{8.2} = 47d+5 and +300d for o104: 24646d+633.2 ✓; both
  < 2·10⁶d³. o104's 300dP items (3, 31d, 8d, 20d, 80d) are already inside o73's 400d or o75's derivative rows, so
  adding them over-counts and nothing is under-counted.
- Per-incidence vs total-P conventions are kept apart correctly (c_{7.3} = 400d per incidence; 10400d per P).

### 2.13 Constants and quantifier order: PASS

- No L^{Cn}: every positive L-power is per incidence (L^{2γ} per pin, μ^e ≤ L^{2e}, L^{31d} once per object,
  L^{4r} in Prop 18.1, L^{(47d+2)} per adjacent factor at a selected residual vertex).
- Bases: C_{P,χ}^{m+1}, C_r^{N+1} with r ≤ 26P (resp. 30P), C_κ with κ = η/16, 2^a·8^a: all fixed before δ.
  (N+1)^{4r} ≤ C_r^{N+1} and factorials at order N⁴ are absorbed per coordinate (o82 Thm 10.1). No C₂^n.
- δ: an exceptional pair contributes δ² against the ordinary δ (net extra δ, not δ^{−1}); the selected reciprocal's
  δ^{−a} is never separated from L^{−2γa} (μ ≥ 1). The final comparison Dδ ≤ δ^{−ν} in Prop 18.1 uses the original D
  and N.
- η: η ≤ 1/16 (for τ ≥ 1/18) and 200dη ≤ √η, fixed with η; κ = η/16; all compatible with T606.

### 2.14 Citations

Checked and correct: T580–591 (normX, locnorm), T611–614 (γ₁ ≤ 1), T826–877 (regular objects, legal = non-crossing at
T849, links at T877), T951–956 (proplayer1), T1095–1112 (proplayer2), T1143–1166 (regref1), T1742–1760 (vineest,
X^{2η⁸} weight), T1954–1974 (redvine, redvine2/3), T1976–2037 (ladderl1new/old, Steps 1–4), T2053–2100
(finalsbest1/2, redvine5), T2214–2260 (finalproof, class count), T2259–2262 (stem layer p); D21 955–961, 1046–1060,
1084–1094, 1142; o82 Prop 14.2, 15.1, Cor 15.2, Lemma 16.1, Lemma 17.2, Lemma 18.1, Thm 18.2, Thm 10.1, Lemma 11.1,
(13.4); o104 Lemmas 3.1, 3.3, 6.1–6.3, Props 7.2–7.4, (P1)–(P8), §7.4, §8.
Editorial: the o104 hash printed in §19 is garbled (49 hex digits; the file's hash is `21e48492…f4b3ed49481a675f4b4cf7f89e6ea9fac273af`);
the o75 hash in §16 is pre-Rev. 1; the o82 hash in §16 is pre-Rev. 1 (o82 is now `d5b09e81…`). "D21 1144–1152" for
the pole correction should be D21 1142–1146 (differenceloss).

---

## 3. Fixes (complete list)

**For o73.**
- **73-F2 (statement; inherited REFEREE-82 F2).** (17.1) and the X^{1/4} use in (17.2) and §20 are stated "at fixed
  spatial boundary data". Cite revised o82 Lemma 16.1: X^{1/4,30d,30d} for couples, X^{1/4,30d,0} for trees. Add one
  sentence to Prop 13.2, (17.2) and §20: the side-couple output decay, or the profile decay for trivial sides, sums the
  exceptional and adjacent unit-box centres. No exponent changes. The ordinary adjacent factors then cost L^{4d}
  locally.
- **73-REC (statement in §20; the proof survives).** Delete "every possible recipient lies in the protected split set".
  The residual parent of a selected skeleton atom need not lie in Π_sb when T_(v) is nontrivial. Replace the sentence
  with the kernel-core argument of §2.10: the absolute value sits inside the time integral, and the added phase and
  indicators do not depend on k[𝕃].
- **73-UF (statement in Prop 19.2 and Thm 7.3′(1)).** Take top and parent faces summed over the maximizer cells. Take
  lower faces per cell. Per-cell upper faces carry an indicator that couples a side couple's internal root time to the
  chain, and Lemma 19.1 does not cover that.
- **73-P8 (editorial).** When F_ch lies in a separate object ((P8)), that object's chain need not be in one layer. Use
  (19.1), not (19.3). The cost is unchanged.
- **73-L19 (statement).** State (19.4) pointwise in the side variables Λ, with amplitude W_Λ of mass D(Λ). Apply o82
  Thm 10.1 at fixed (E,Λ), then integrate in Λ. Also note the fixed cutoff that turns the line measure of the chain's
  output into a density.
- **73-RT (statement).** Add to (19.1) the hypothesis that the traced root is in layer p. Also say that R_B may depend
  on a third boundary time.
- **73-E1 (editorial).** In Prop 18.1, replace "at most one selected endpoint substitution per original tree" with
  "at most one selected substitution and a bounded number of pins per tree". This covers F_ch with m and 𝔣^pr both
  pinned at s.
- **73-PIN (bookkeeping).** Cite o75 Rev. 1 (§16 still records `d7102c43…`) and o82 Rev. 1. State explicitly that
  Prop 20.1 discharges o75 Rev. 1 row 13/§11.6 at skeleton selected vertices.
- **73-C (editorial).** Correct the garbled o104 hash in §19 (49 hex digits). Change "D21 1144–1152" to
  D21 1142–1146 (differenceloss).

**For other packets (from this audit; for wt-orch to route).**
- **73-W (o75 row 13 and §11.6; o82 §19 and §22-F1).** The current text says "gain (cδL^{2γ}M₂)^{−1} from S Lemma 9.1"
  and "retaining reciprocal (9.1)". Replace it with: inside regular objects, S Lemma 9.1 with the reciprocal retained
  (o82 Thm 18.2); at skeleton and residual selected vertices, the o73 Prop 20.1 dichotomy, giving M₂^{−1/18} per
  occurrence on both bounds. No ledger row uses the extra (cδL^{2γ})^{−1}.
- **o104.**
  - Record that Prop 7.4(a) integrates the mate from the layer floor, so for a paired tree whose port has the mate's
    layer it integrates an extension outside the defining triangle. o73 §19.1's port convention is the correct
    repair.
  - Amend (7.2): the boundary phases e^{πiA(t−s)} and e^{πiεBs} are recorded and consumed, not bounded in an
    uncentred X^η norm.

---

## 4. Refutation attempts that did not succeed

1. Uncentred weighted norm of a pin or top-face phase. It is never taken. Lemma 12.1 consumes the pin phase, and ℓ_E
   is evaluated at external times or translates a residual ξ.
2. Raw 1/β_v at a residual selected vertex when ξ_v cancels β_v. It is not used: H_v pays with the moment.
3. A selected residual vertex adjacent to an unmarked spliced vine, whose X^{2η⁸}-only factor could not pay a moment.
   This is impossible: Π2, Definition 2.3, and S Lemma 9.2 / o75 Lemma 2(d).
4. An adjacent kernel of a selected residual vertex that contains another selection, which would need (17.3) inside a
   moment. This is impossible: there is one selection per tree, and the couple is (T′,cap) of the same tree.
5. A face recipient inside a retained ladder. It is possible for the parent recipient, but harmless (73-REC).
6. Loss of the ladder factorial in Prop 18.1 when faces remove X atoms. The loss is (N+1)^h ≤ C_r^{N+1}, with a base
   independent of δ.
7. Floor faces at selected stem vertices. They are empty inside regular objects. In the residual they are handled as a
   constant recipient.
8. Hidden C₂^n or δ-dependent bases in Lemma 19.1, Prop 18.1 or Prop 20.1. None found.
9. Interpolation destroying the M₂ gain. Both bounds carry the same factor at fixed (ξ,β_E).
10. Double use of an incoherency unit at a side-child face. One unit is moved into the exceptional link and repaid by
    L^{γ₁} ≤ L, so the final count is 0.

STATUS: REFEREED — 0 FAIL. Theorem 7.3′ PASS AFTER FIX as a sufficient variant for o63 Prop 10.3′ with o75 Rev. 1
(fixes 73-F2, 73-REC, 73-UF, 73-P8, 73-L19, 73-RT, 73-PIN, editorial 73-E1/73-C; none changes an exponent). The M₂
gain at skeleton and residual selected vertices comes from the Prop 20.1 dichotomy, a valid replacement for the raw
reciprocal (9.1); o75 row 13/§11.6 and o82 §19/§22 need a wording fix (73-W). Ledger c_{7.3} = 400d per incidence,
10400dP total, verified.
