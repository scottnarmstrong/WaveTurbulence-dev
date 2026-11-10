# The ghost step by joint removal: the two-α-ghost triangle (E20, group D) for all 0 < γ < 1

## Reader's preface

**What this note proves.** The ghost step of the stage-2 counting run (erratum E20), a triangle step whose triangle
contains two α-ghosts (atoms already cut at earlier steps), closes for every 0 < γ < 1. Two ghosts made by one removal
never meet at an eligible triangle (Lemma 2.1). Otherwise the deficit is only 4η + O(η²) (Prop 3.1), and it is paid by
classifying each critical pair of ghosts in advance as transverse or near-collinear: a cone gain at the later ghost's
creation is passed to the triangle step, and these transfers telescope exactly (Theorems 6.1 and 7.1). The run itself
is unchanged, and the ghosts of the flower estimate's Operation 1E are covered too (§8).

**How it fits the repair.** This is ingredient 3 of the γ ≤ 1/2 repair
([overview, §5](../GAMMA-LE-HALF.md#5-ingredient-3-the-ghost-step-erratum-e20)). It supports erratum E20, and E21 for
the alive cuts of Lemma 6.2, in [`../ERRATA-AND-DEVIATIONS.md`](../ERRATA-AND-DEVIATIONS.md). The counting note uses it
as its ghost lemma G (§11a), and the flower note as its ghost-step input. Two alternative approaches to the ghost step,
worked out separately and not included, reached the same conclusion.

**Where it is in Lean** (names relative to the namespace `WaveTurbulence`, files relative to the repository root).
- `GammaLow.FinalCount.Ghost.chainCoverLow'_holds` (`WaveTurbulence/Foundations/GammaLow/FinalCount/Ghost/ChainLow.lean`)
  and `GammaLow.FinalCount.Ghost.chainCoverLowL'_holds` (`WaveTurbulence/Foundations/GammaLow/FinalCount/Ghost/ChainLowL.lean`):
  the ghost bound for the two parts of the final-count run. They are stated for the whole run at once (the telescoped
  form of Theorems 6.1 and 7.1), since the per-step bound (R38) is false for γ ≤ 1/2 (Prop 3.1).
- `GammaLow.Flower.H2.Ghost.chainCoverLowLE'_holds` (`WaveTurbulence/Foundations/GammaLow/Flower/FinalMK/H2/Ghost/ChainLowLE.lean`):
  the same for the marked count inside the flower estimate.
- `GammaLow.FinalCount.Ghost.prop94_vine_all_gamma_cone` (`WaveTurbulence/Foundations/GammaLow/FinalCount/Ghost/Op1Cone4.lean`):
  the cone count at the step that creates a ghost (the cone of Theorem 6.1(e), Lemma 5.2).
- These feed `GammaLow.Close.finalCountGateLow_proved` (`WaveTurbulence/Foundations/GammaLow/Close/Halves.lean`) and
  `GammaLow.Flower.H2.finalCountGateLowMK_holds` (`WaveTurbulence/Foundations/GammaLow/Flower/FinalMK/H2/Final.lean`).
- §10 was written as instructions for the formalization. Names it proposes for new lemmas (such as `card_twoSlab`) need
  not occur in the repository.

**Status.** Accepted with repairs by an independent refute-first referee
([report](gamma-le-half-ghost-step-referee.md)). The referee's repairs are listed in the report; they were applied in
the Lean formalization and are not folded into this text.

*Provenance: written and independently refereed in November 2026.* The scripts named in the text are not included in
this repository. Lean names refer to the repository at the time of writing (this preface: commit `5c19b015`; the text:
the commit it cites, where it cites one); a later clean-up removed some unused helpers, which remain in the git history
at the commits cited.

**Abbreviations.**
- TARGET: Y. Deng, Z. Hani, *Long time justification of wave turbulence theory*, arXiv:2311.10082v2; line numbers
  (L2167, …) are lines of its TeX source.
- DH23 or D23: Y. Deng, Z. Hani, *Derivation of the wave kinetic equation: full range of scaling laws*,
  arXiv:2301.07063; line numbers as above.
- N1, N2: the first two earlier research notes on T-vines, [`gamma-le-half-repair-1-notes.md`](gamma-le-half-repair-1-notes.md)
  and [`gamma-le-half-repair-2-notes.md`](gamma-le-half-repair-2-notes.md).
- GHOST: [`ghost-triangle-notes.txt`](ghost-triangle-notes.txt) (the first analysis of the ghost step).
- SUPP: [`flowerest1/SUPPLEMENT-v2.md`](flowerest1/SUPPLEMENT-v2.md), the written completion of TARGET's flower
  estimate; O75: its resolution note [`flowerest1/o75-RESOLUTION.md`](flowerest1/o75-RESOLUTION.md).
- The counting note: [`gamma-le-half-counting-notes.md`](gamma-le-half-counting-notes.md) (DH23 Props 9.4–9.6 and
  10.4(2) at γ ≤ 1/2). The flower note: [`gamma-le-half-flower-notes.md`](gamma-le-half-flower-notes.md).
- R29, R38: rulings of the formalization project that fix readings of the sources; each is described where it is used
  and in [`../ERRATA-AND-DEVIATIONS.md`](../ERRATA-AND-DEVIATIONS.md).
- Lean file groups, all in `WaveTurbulence/Foundations/FinalCount/`: "the Lean triangle step" is `TriCount*.lean` and
  `TriDev*.lean`; "the Lean ghost step for γ > 1/2" is `Ghost*.lean`; "the Lean assembly of the final count" is
  `G3*.lean`.

Status words: **PROVED** (complete written proof here), **CHECKED** (computation; script and range given),
**SKETCH**, **OPEN**, **INPUT** (used, proved or refereed elsewhere, not re-proved here).

## 0. Result

**READY.** The two-α-ghost triangle step (group D of GHOST §3c) closes for **every 0 < γ < 1**, under `TriReal` alone
(d ≥ 3, 200η ≤ γ, 200η ≤ 1 − γ). The extra hypothesis `8η ≤ 2γ − 1` of ruling R38 (the charged per-step bound of
erratum E20) is no longer needed.

1. **The one-object configuration proposed for this route never occurs (Lemma 2.1, PROVED, CHECKED).** If both
   α-ghosts of a triangle are the two joints of *one* removed Operation-1/1E object (for example the proposed
   HV ∪ {z, w}), momentum conservation over the object forces a **zero gap at the third atom z**. Such a
   triangle is never eligible (ruling R29, the eligibility rule for triangles of errata E16/E17: nonzero gap at v₃). So
   joint removal as literally posed targets an empty case. GHOST's "group D is attained" holds only in the local model
   with free parameters. Every real group-D triangle has its two ghosts created by **two different steps** (or by one
   Op-2 step creating both).
2. **The true deficit for γ ≤ 1/2 is tiny (Prop 3.1, PROVED, CHECKED).** It is at most 4η + gη² + η³, not
   "(1 − 2γ) + 4η" as stated in the list of open steps drawn up when the extension was planned (not included; that
   formula substitutes γ₀ = 1 − γ). It occurs only when both α-ghost labels exceed L^{−γ₀−3η−…}. Pure creation-slack banking
   (an alternative approach to the ghost step, not included) is still short at d = 3, by gη² + 3η³, when both ghosts
   come from removals of double bonds (Remark 3.2).
3. **The joint count works for all γ (Lemma 4.1, PROVED).** Count the *later* ghost's creating object together
   with the triangle, as one enlarged object. The ghost's energy window then constrains the object's free joint
   momentum, and is not wasted on the triangle momentum. The resulting margin is (d−1)γ − γ₀ − (d−2)η − 2η² − η³ ≥ γ − η − O(η²).
4. **Implementation without changing the run (Theorem 6.1 and Theorem 7.1, PROVED).** Literally merging operations
   would change the run (Remark 4.3). Instead, the joint count is realized sequentially by an **angular
   specification (f′)**:
   - **Specification.** Every *critical* pair (two α-ghosts, κ = 0, both labels ≥ L^{−γ₀−4η}) is fixed as transverse
     (TR) or near-collinear (NC), relative to θ₀ = L^{−6η}.
   - **TR pairs.** The triangle step uses both energy slabs. Its margin is ≥ γ − 9η − O(η²).
   - **NC pairs.** The later ghost's creation step counts its gap in a cone of aperture θ₀, gaining ≥ L^{−12η}. It
     pays a transfer L^{−5η}, and the triangle step receives L^{+5η}.
   - **Telescoping.** The transfers cancel pair by pair, so the telescoping is exactly R38's. The run, its molecules
     and classes, subpro, Cor 1.16′, finalmol, (excessprop1)(3) and the budgets of (together2)/(together3) are all
     unchanged.
5. **Flower.** The Operation-1E ghosts (O75 L814, L900) are covered verbatim (§8).
6. **Grid.** GHOST's grid was re-run on (0, 1/2] and on the repaired scheme over (0, 1). Every margin is
   non-negative; the minima are tabulated in §9.
7. **Cross-check with the counting note (§11a).** The counting note independently finds the same deficit,
   4η + gη² + η³. This leaves the conclusion unchanged, since the scheme was built on that deficit. The counting note's
   (operc) and A.2(1) findings do not enter here. This note proves the counting note's ghost lemma G, an input that
   note takes as proved elsewhere, in its form (G-D).

## 1. Setting, notation, inputs

**Exponents.** All exponents are log_L. Write γ₀ = min(γ, 1 − γ), a = 2γ₀ + 5η², b = γ₀ + 2η², h = (γ + 3η)/2.
- **Labels.** A label is Q ∈ [L⁻¹, L^{−γ+η}] (dyadic), with q = log_L Q ∈ [−1, −γ + η]. The label factor is
  T(Q, κ) = L^{h−κη}Q, with κ ∈ {0, 50}.
- **Slab factor.** The energy window is W = δ⁻¹L^{−2γ}, and s(q) := min(0, max(−1, −2γ − q)) (GHOST §0). If
  q ≤ −γ + η and γ + η ≤ 1, then −2γ − q ≥ −γ − η ≥ −1, so s(q) = min(0, −2γ − q).

**`TriReal`** (`WaveTurbulence/Foundations/FinalCount/TriDev3.lean`, L58): d ≥ 3, 0 < γ < 1, 0 < η, 200η ≤ γ,
200η ≤ 1 − γ, L ≥ e, 0 < δ ≤ 1. In particular η ≤ γ₀/200 ≤ 1/400.

**R38's charged step bound** (GHOST §3a, §3d; ruling R38). For every step other than a component-creating
Operation 1,

  I ≤ C · L^{−η³} ∏_{new α} T(Q_v, κ_v) · ∏_{α-ghosts g} T(Q_g, κ_g)⁻¹ · L^{aΔF − bΔV_β},        (R38)

with the true increments ΔF and ΔV_β. The **margin** of a step is log_L(right-hand side) − log_L(count bound), with
δ, (log L) and constant factors dropped. They are absorbed by any margin ≥ cη² once L ≥ L₀(d, c, η, δ), exactly as in
`ghostConst` (`GhostMain1.lean`).

**Inputs** (INPUT: proved or refereed elsewhere, not re-proved here).
- **I1. GHOST's Operation-2 counting model** (GHOST §0, §3c; the `card_*` lemmas of the Lean triangle step and of the
  Lean ghost step for γ > 1/2).
  - Blocks are the post components plus one block per ghost; B − 1 block relations are independent.
  - The 3 − B free gap vectors are the new α-atoms' own gaps.
  - The triangle momentum a satisfies #a ≤ C L^{d+s(ρ)} for a fixed block gap of label ρ.
  - Δχ = m − 1 − |N|.
- **I2. The Operation-1/1E count for ΔF = 0.**
  - **Form.** count ≤ [number of joint pairs (x₀, r), r = x₀ − y₀ in the annulus |r| ~ Q] × [interior count, uniform in
    (x₀, r)]. The energies of both joints are not used: they pass to the post molecule.
  - **Vines, HV, T-vines** (DH23 L1797–L1801; N1 §3.2 row "Step-1 deviation", REFEREED): I ≲ Q^d L^{2γ}.
  - **VC of two double bonds** (DH23 L1801): I ≲ Q^d L^{3γ+s(q)}.
  - **Flower Operation 1E** (O75 Lemma 5): the same computations.
  - **κ = 50:** (QL)^d becomes (QL^{1−50η})^d (DH23 L1803).
- **I3. Run model.**
  - R29: a triangle is eligible iff it is SG at v₁, v₂, has a nonzero gap at v₃, and satisfies the hinge designation;
    Operation 5 erases tame clusters; Op 4 makes only nonzero-gap β-cuts.
  - R38/E21: ι is taken through alive cuts; κ is fixed at creation.
  - Op 1 removes one object per step. Op-1 objects are disjoint (TARGET L2167). The order is Op 1 (then 1E in the
    flower), Op 2, Op 3, Op 4, Op 5.
- **I4. Decorations** (DH23 L1766, TARGET L2131).
  - c_v = 0 at every atom of degree 4 in M_sb.
  - The counting quantity of any molecule of the run is the supremum over the current parameters (c_v, β_v, k⁰) of the
    number of current decorations inherited from M_sb-decorations that satisfy requirements (a)–(f) (TARGET L2095–L2109).

**Ghost.** A ghost is a triangle atom that is already cut: class α or β, degree 2, with its two bonds being the two
triangle bonds at it. **Group D** is a triangle step whose triangle has two α-ghosts x, y. Either g = 2 (the third atom
z is not a ghost), or g = 3 (z is a β-ghost); three α-ghosts are excluded by CompBeta. The gap of a ghost x is the gap
r_x of its triangle pair, and r_x = ±c_x from x's creation on.

## 2. The one-object configuration proposed for this route is never an eligible triangle

**Lemma 2.1 (one object, two ghosts ⇒ zero gap at z). PROVED; CHECKED (`sourceA_check.out`: 34 molecules, including the
proposed HV).**

*Statement.* Let one step of Operation 1 or 1E remove a VC U′ (an object of 𝒞₁, 𝒞₂ or 𝒞_E, or its adjoint VC) and cut
its two joints x ≠ y along the bonds of U′. Suppose that some later Operation-2 triangle (x, y, z) has both x and y as
ghosts.
- Then, in every decoration counted at that step, the two triangle bonds at z carry equal momenta. That is, the gap of
  z along its triangle pair is 0.
- Hence the triangle is not eligible (R29). In fact z can be neither v₁/v₂, which must be SG with |r| ≥ L⁻¹, nor v₃,
  which must have a nonzero gap.
- So no Operation-2 step ever has this configuration. Moreover r_x = −r_y identically.

*Proof.*
1. **Degrees.** Operations 1–4 never cut an α- or β-atom. Op-1 objects are disjoint. The flower's re-cut (O75 §4.6)
   produces a remnant of degree 0, which is never a ghost. So x is cut exactly once, at this step. Since x is a ghost
   later, its two remaining bonds are its two triangle bonds, xy and xz. Hence deg_{M_sb}(x) = 4, and x's bonds in M_sb
   are two bonds of U′, xy and xz. The same holds for y.
2. **The closed set.** Let S be the set of atoms of U′ (its interior atoms and x, y).
   - Every atom of S has degree 4 in M_sb: interior atoms of a vine-like object have all four bonds in it, and x, y by
     step 1. By I4, c_v = 0 on S.
   - The bonds of M_sb with exactly one end in S are exactly xz and yz. (Interior atoms have all their bonds in U′; the
     bond xy has both ends in S.)
3. **Conservation.** Summing the conservation law ∑_{out} k − ∑_{in} k = c_v over v ∈ S, the internal bonds cancel and
   0 = (signed flux through xz and yz).
   - At an Op-2 step, z is cut along (zx, zy), so this pair has opposite directions at z (Def `defcut`): one of the two
     bonds enters S and the other leaves it.
   - The flux identity therefore reads k(zx) = k(zy), which is a zero gap.
4. **All counted decorations.** Every decoration counted at any step is inherited from an M_sb-decoration (I4), so the
   identity holds in all of them.
5. **r_x = −r_y.** Since r_x + r_y + r_z = 0 around the triangle, r_x = −r_y. ∎

**Corollary 2.2. PROVED.**
- (a) **HV joints are never ghosts of an Operation-2 triangle.** This covers HV and HVC joints in 𝒞₁ and 𝒞₂, and the
  flower's W′ = S ∪ {e*} (O75 §11.1). After removal, a joint x keeps the HV bond xy and one other bond. A triangle
  through the ghost x therefore contains y, which is also a ghost of degree 2, so Lemma 2.1 applies.
- (b) **The proposed HV ∪ {z, w} never yields an Operation-2 step.** GHOST §3c's "group D is attained (x, y the joints of
  an SG HV …)" is a statement about the per-step lemma with free parameters c_x, c_y. It is not about a run.
- (c) **In every group-D step, the two α-ghosts were created at different steps, or both at one Operation-2 step.** The
  latter means two new α-atoms that are still joined by a second bond. An Op-1/1E step creates α-atoms only at the two
  joints of its one object, which is excluded by Lemma 2.1.

## 3. The deficit of group D

**Proposition 3.1 (R38 group-D margin, all γ). PROVED; CHECKED (`grid_low.out` part 1).**

*Statement.* Take a group-D step with α-ghost labels q_x, q_y and g ∈ {2, 3}. Let ρ be the label of GHOST's slab block,
ρ = max(q₁, q₂) ≥ max(q_x, q_y). Then:
- if ρ ≥ −2γ, the R38 margin satisfies m_D ≥ −η³ − 3η − min(q_x, q_y) − γ₀ − gη² + (κ_x + κ_y)η;
- if ρ < −2γ, then m_D ≥ 2γ − γ₀ − 3η − gη² − η³ > 0.

*Consequences.*
- m_D < 0 only if κ_x = κ_y = 0 and min(q_x, q_y) > q* := −γ₀ − 3η − gη² − η³.
- In all cases m_D ≥ −(γ₀ − γ + 4η + gη² + η³) ≥ −(4η + 3η² + η³).
- For γ ≤ 1/2 the deficit is at most 4η + gη² + η³, attained at q_x = q_y = −γ + η.

*Proof.*
1. **Right-hand side.** The right-hand side of (R38) is −η³ − (h − κ_xη + q_x) − (h − κ_yη + q_y) + aΔF − bΔV_β.
   - For g = 2: ΔF = 0 and ΔV_β = 1 (the remainder z′ is β), giving the term −b.
   - For g = 3: ΔF = ΔV_β = −1, giving the term −a + b = −γ₀ − 3η².
   - In both cases the right-hand side equals −η³ − γ − 3η − q_x − q_y − γ₀ − gη² + (κ_x + κ_y)η.
2. **Count.** By I1, Δχ = −1 and #a ≤ L^{d+s(ρ)}, so the count is I = γ + s(ρ).
3. **The case ρ ≥ −2γ.** Then s(ρ) = −2γ − ρ, and q_x + q_y − ρ ≤ min(q_x, q_y). This uses ρ ≥ max(q_x, q_y): the model
   imposes q₃ ≤ max(q₁, q₂), because r₁ + r₂ + r₃ = 0.
4. **The case ρ < −2γ.** Then s = 0 and −q_x − q_y > 4γ. ∎

The grid confirms this. The 6 group-D patterns are the only negative ones, with minimum −0.010013 = −(4η + 2η² + η³) at
γ = 1/2, η = 0.0025. Over 16 values of γ in (0, 1/2], 3 values of η, d ∈ {3, 4, 5, 8} and the κ variants, no negative
margin falls below −(4η + gη² + η³), and none occurs with min label ≤ q*.

**Correction to the planning notes for the extension (not included).** Their statement "For γ ≤ 1/2 the margin is
negative by about (1 − 2γ) + 4η" is wrong for γ < 1/2: the deficit is ≤ 4η + O(η²), uniformly in γ. The "γ > 2/5"
estimate of the creation-slack-banking approach (an alternative approach to the ghost step, not included) rests on that
formula.

**Remark 3.2 (pure creation-slack banking at d = 3). PROVED (arithmetic).**
- **Creation slack.** By I2, an Op-1 creation by a vine has R38 margin −γ + 3η + (d−2)κη − (d−2)q − η³. At d = 3 and
  q = −γ + η this is 2η − η³, shared by its two α-joints.
- **Sharpness.** For a double bond (vine (I)) the count L^d(QL)^d is the whole count, so this slack is sharp.
- **Shortfall.** A critical pair whose two ghosts are joints of two different double bonds has at most
  (2η − η³) + (2η − η³) of creation slack, against a deficit of 4η + gη² + η³. Banking R38 slack therefore falls short
  by gη² + 3η³.
- **Contrast.** Operation-2 creations have slack ≥ γ/2 − η/2 (§9), and VCs of two double bonds have ≥ 3η − η³.
- **Worst case.** If both joints of both double bonds are ghosts of group-D triangles, each ghost carries only
  η − η³/2. A triangle then has 2η − η³ against a deficit of 4η + gη² + η³, so the shortfall is about 2η.
- **Re-weighting the label factor does not help.** Replace h by h + cη, which moves slack between the creation steps
  and Prop 9.6. The deficit becomes 4η + 2cη + …, and each joint's share of creation slack becomes η + cη. In the
  worst case above a triangle then has 2η + 2cη < 4η + 2cη, for every c.
- This is recorded for the creation-slack-banking approach. Joint removal does not need it.

## 4. Joint removal: the joint count of the enlarged object

**Lemma 4.1 (enlarged object: later creation and triangle in one count). PROVED.**

*Hypotheses.* Consider an Operation-1/1E step with ΔF = 0 that removes a VC U′ with joints y, y₂, gap r, |r| ~ Q_U and
κ_U = 0, with m_U atoms (joints included). Suppose:
- y's two other bonds are yx and yz;
- x is an α-atom of M_pre of degree 2, with bonds xy and xz, label Q_x, κ_x and gap c_x;
- after the removal, (x, y, z) is an eligible group-D triangle with g = 2.

*The enlarged object.* Let E := U′ ∪ {xy, yz, zx}. Let M_pos be obtained from M_pre as follows:
- delete the bonds of E, the interior atoms of U′, and the atoms x and y;
- cut y₂ along U′, so y₂ becomes α with label Q_U;
- cut z along (zx, zy), so its remainder z′ is β.

*Conclusion.* Then ΔF = 0, ΔV_β = 1 and Δχ = −(m_U + 1). Moreover

  A_pre ≤ C δ^{−C}(log L)^C · L^{d q_U + 3γ + s(q_x) + s(q_U)} · A_pos,

and this deviation is at most L^{−η³} T(Q_U, 0) T(Q_x, κ_x)⁻¹ L^{−b}, with margin

  μ_J ≥ (d − 1)γ − γ₀ − (d − 2)η − 2η² − η³   (≥ γ − η − 2η² − η³ at d = 3; positive for every 0 < γ < 1 under `TriReal`).

So the enlarged object satisfies (excesseqn2): one new α-atom y₂, the earlier ghost x refunded, and **no label for y
at all**. There is no ghost of y and no refund of y.

*Proof.* Fix the post decoration (the supremum over post parameters). The removed variables are:
- r;
- y₀, one bond of U′ at y;
- the interior variables of U′;
- a := k(xy).

Then k(zx) = a ± c_x, and k(yz) is fixed by a and r, because c_y = 0 in M_pre (y has degree 4 there). The count uses
the following constraints.
1. **The gap r.** |r| ~ Q_U gives ≤ C(Q_U L)^d values.
2. **The energy window of x.** x is deleted, so its window Γ_x is available. Γ_x = ±(2⟨a, c_x⟩ + |c_x|²) lies in an
   interval of length W. So a lies in a slab of thickness t_x = W/(2|c_x|) ≥ 1/L inside a unit ball, which gives
   ≤ C L^{d+s(q_x)} values (Lemma 5.1 with one slab).
3. **The energy window of y.** y is deleted, so its window Γ_y is available. In the DH23 count it is not used: it would
   pass to the post molecule. Here Γ_y = ±2⟨y₀, r⟩ + (an affine function of a) + const, so given (a, r), y₀ lies in a
   slab of thickness W/(2|r|). This gives ≤ C L^{d+s(q_U)} values.
4. **The interior.** Given (y₀, r), the interior count is ≤ C δ^{−C}(log L)^C L^{(m_U−2)(d−γ)} ∏𝔛_j^{−z_j}, uniformly
   (I2).
5. **Post parameters.** Γ_{y₂} and Γ_z (the part on the deleted bonds) become post parameters. Δχ is
   −(2m_U − 2) − 3 + (m_U − 2) + 2 = −m_U − 1.

Multiplying, the exponent is d(q_U + 1) + 2d + s_x + s_U + (m_U − 2)(d − γ) − (m_U + 1)(d − γ) = d q_U + 3γ + s_x + s_U.

**The margin.** The right-hand side is −η³ + (h + q_U) − (h − κ_xη + q_x) − b. Two elementary bounds are used:
- −q_x − s_x = max(−q_x, 2γ) ≥ 2γ;
- −(d−1)q_U − s_U = −(d−2)q_U + max(−q_U, 2γ) ≥ (d−2)(γ − η) + 2γ.

Hence μ_J ≥ −η³ − γ₀ − 2η² − 3γ + 2γ + (d−2)(γ − η) + 2γ, which is the stated bound. ∎

**Why the gain is real.** The sequential bound (R38) pays for the worst case r_x ∥ r_y. There the two windows Γ_x and
Γ_y act on the same variable a, so one of them is wasted. The joint count instead assigns Γ_y to y₀, which is free in
U's count. The gain is L^{s(q_min)}, about L^{−γ−η} at the top label.
- CHECKED (`lattice_check.out` (3), d = 3, L ∈ {30, 60}, collinear worst case): joint/sequential = 1.01–1.03 × t_max,
  as predicted.

**Remark 4.2 (an object both of whose joints are later ghosts). PROVED (same computation).** Let E = U′ ∪ T ∪ T″, where
T = (x, y, z) and T″ = (x″, y₂, z″).
- Use Γ_y on y₀ only. For a vine (I), Γ_{y₂} also constrains y₀ along r and is redundant.
- The exponent is d q_U + 4γ + s_x + s_{x″} + s_U.
- The margin is ≥ dγ − 2γ₀ − (d + 2)η − 4η² − η³ ≥ γ − 5η − O(η²).

**Remark 4.3 (why the enlarged object is not run as an operation). SKETCH.** Running E as one Operation-1 step means
removing the triangle T during Operation 1, before the remaining Op-1 removals. This changes the run:
- **A later object may cut z.** Another Op-1 object U₃ may have z as a joint. In the standard run, z is cut by U₃
  before Op 2, and the triangle has a ghost at z. After a merge, z′ keeps only U₃'s bonds, and U₃'s removal re-cuts it
  to an isolated atom.
  - That removal then has ΔF = 1.
  - It is charged with (excesseqn2+), at a cost of L^{γ₀}, and p⁺_op can exceed 2R − 2.
  - The α/β classes change.
- **Group D with g = 3.** The β-ghost is necessarily created after y. Otherwise y's removal would have cut off
  {x, y, z} and y would be β. At U's time the β-ghost is not yet a ghost.
- **Operation-2 creations.** A later ghost created in Operation 2 cannot be merged into Operation 1 at all, and its
  creation slab may already be parallel to r_y.

So a literal merge would require re-proving finalmol, (excessprop1)(3) and the budget. §6 obtains the same gain with
the run unchanged.

## 5. Two lattice lemmas

TARGET works on the square torus, so ℤ^d_L = L⁻¹ℤ^d (TARGET L2446). Both lemmas hold on any lattice L⁻¹Λ with Λ fixed,
with constants depending on Λ.

**Lemma 5.1 (two slabs). PROVED; CHECKED (`lattice_check.out` (1): d = 3, L ∈ {40, 80}; N/model between 5.1 and 8.0
for every angle).**

*Statement.* Let d ≥ 2, a₀ ∈ ℝ^d, n₁, n₂ ≠ 0, c₁, c₂ ∈ ℝ and W > 0. Put t_j := W/|n_j| and assume t_j ≥ 1/L. Let θ be
the angle between the lines ℝn₁ and ℝn₂. Then

  #{a ∈ L⁻¹ℤ^d : |a − a₀| ≤ 1, |⟨a, n_j⟩ − c_j| ≤ W (j = 1, 2)} ≤ C_d L^d min(t₁, t₂, t₁t₂ / sin θ).

*Proof.*
1. **Disjoint cubes.** Write e_j = n_j/|n_j|. For each counted point p, the cube p + [0, 1/L)^d lies in
   K⁺ = {|a − a₀| ≤ 1 + √d, |⟨a, e_j⟩ − c_j/|n_j|| ≤ T_j}, with T_j := (1 + √d)t_j (this uses t_j ≥ 1/L). The cubes
   are disjoint, so # ≤ L^d vol(K⁺).
2. **Splitting the volume.** Split ℝ^d = P ⊕ P^⊥ with P = span(e₁, e₂). Then
   vol(K⁺) ≤ vol_{d−2}(B^{d−2}(1 + √d)) · area{u ∈ P : |u| ≤ 1 + √d, |⟨u, e_j⟩ − c′_j| ≤ T_j}.
3. **The area.** That area is ≤ 4T₁T₂/sin θ (a parallelogram), and ≤ 4(1 + √d)T_j (a strip inside a disc). ∎

**Lemma 5.2 (cone). PROVED; CHECKED (`lattice_check.out` (2): d = 3, L ∈ {400, 1500}; count/((QL)³θ²) ≤ 2.05 for every
θ ≥ 1/(QL)).**

*Statement.* Let e be a unit vector, 0 < θ ≤ 1 and Qθ ≥ 1/L. Then

  #{r ∈ L⁻¹ℤ^d : Q/2 ≤ |r| ≤ Q, ∠(r, ℝe) ≤ θ} ≤ C_d (QL)^d θ^{d−1}.

*Proof.* Such an r has |⟨r, e⟩| ≤ Q and |r − ⟨r, e⟩e| ≤ Q sin θ ≤ Qθ. The unit cubes attached to these points are
disjoint and lie in {|⟨r, e⟩| ≤ (1 + √d)Q, |r^⊥| ≤ (1 + √d)Qθ}, using Q ≥ Qθ ≥ 1/L. That set has volume
≤ C_d Q (Qθ)^{d−1}. ∎

## 6. The angular realization of the joint count (the deliverable)

**Definitions.**
- **Group-D pair.** For a group-D step with α-ghosts x, y, the pair is P = {x, y}, with tri(P) := that step.
  Let s(P) be the step that creates the later of x and y; if one Op-2 step creates both, it is that step.
- **Critical.** P is critical if κ_x = κ_y = 0 and min(Q_x, Q_y) ≥ L^{−γ₀−4η}.
- **Constants.** θ₀ := L^{−6η} and τ₀ := 5η.
- **Requirement (f′),** added to TARGET's (d)–(f) at L2105–L2108. For every critical pair, fix either
  - **TR:** sin∠(r_x, r_y) ≥ θ₀ (the angle between lines), or
  - **NC:** sin∠(r_x, r_y) < θ₀.
- **Why (f′) is a valid specification.** The run is determined by (d)–(f), R29's zero/nonzero specification and the ι
  choices. Hence so are its group-D steps, labels, κ's, s(P) and tri(P). Requirement (f′) enters no rule of the run,
  so it is only a partition of the decorations, into at most 2^{n_sb} classes. That loss is absorbed by C₀^{n_sb}
  (TARGET L2109). It constrains r_x, r_y, which are functions of the M_sb-decoration, just as (f) constrains gaps of
  atoms that are deleted later.
- **Counters.** ν^tri_s := #{NC critical P : tri(P) = s} ∈ {0, 1} and ν^cre_s := #{NC critical P : s(P) = s} ∈ {0, 1, 2}.

**Lemma 6.2 (the later ghost's gap is a free vector with a present centre). PROVED.** Let P be critical, and let y be
its later ghost.
- (i) s(P) is one of two kinds of step:
  - an Op-1/1E step with ΔF = 0 that removes an object U with joint y; or
  - an Op-2 step in which y is a new α-atom.
- (ii) In both cases the count at s(P) (I1, I2) is [a sum over r_y in the annulus |r_y| ~ Q_y] × [a bound uniform in
  r_y]. For a κ = 0 α-atom, the gap of y is the object's gap ±r (I2), or the new α-atom's own free gap vector (I1).
- (iii) Either x is an atom of M_pre(s(P)) with parameter c_x = ±r_x, or both x and y are new α-atoms of the same
  Op-2 step, whose two free vectors are r_x and r_y.

*Proof.*
- (i) α-atoms are created only by ΔF = 0 Op-1/1E steps (the joints of component-creating removals are β) or by Op 2.
  Op 3 runs after Op 2.
- (ii) This is I1 and I2.
- (iii) If s_x < s(P): x keeps exactly its two triangle bonds from creation on, is never re-cut, and is deleted only at
  tri(P) > s(P). So x is alive at s(P), and its parameter c_x is a current parameter. This is the alive-centre
  condition, the analogue of E21's alive cut. If s_x = s(P), Corollary 2.2(c) applies. ∎

**Theorem 6.1 (charged per-step bound, all 0 < γ < 1). PROVED (for groups A–C at γ ≤ 1/2 the R38 margins are those of §9:
closed forms PROVED, grid CHECKED).**

*Statement.* Assume `TriReal`. Every step s of Operations 1, 1E, 2, 3 and 4, except a component-creating Operation 1,
satisfies

  I_s ≤ C · L^{−η³} ∏_{new α} T(Q_v, κ_v) ∏_{α-ghosts} T(Q_g, κ_g)⁻¹ L^{aΔF − bΔV_β} · L^{τ₀(ν^tri_s − ν^cre_s)},      (★)

with the true increments and C = C(d, c, η, δ).
- Component-creating Op-1 steps keep (excesseqn2+), and have ν = 0. Op 5 is unchanged.
- **Margins of (★).**
  - Group-D steps with TR critical pairs: ≥ 2γ − γ₀ − 9η − 3η² − η³.
  - Group-D steps with NC critical pairs, and non-critical group-D steps: ≥ η − 3η² − η³.
  - Steps with ν^cre ≥ 1: ≥ 2η.
  - All other steps: their R38/DH23 margins.

*Proof.* Steps with ν = 0 that are not group-D satisfy (R38) exactly as before.
- Requirement (f′) only shrinks the counted set of M_sb-decorations.
- Every per-step bound is of the form "count of the removed variables, uniformly, × the supremum of the post count".
  This form is monotone under any requirement imposed on the M_sb-decoration, exactly as for (f).

The remaining cases are as follows.
- **(b) tri(P) for a TR critical pair.** By I1 the triangle momenta are a, a ± c_x and a ∓ c_y (g = 2), and likewise
  for g = 3.
  - Γ_x and Γ_y are windows of M_pre, since x and y are deleted. They give |⟨a, 2c_x⟩ − c| ≤ W and
    |⟨a, 2c_y⟩ − c′| ≤ W, with t_x = W/(2|c_x|) ≥ 1/L, because −2γ − q_x ≥ −γ − η ≥ −1.
  - TR gives sin∠ ≥ θ₀. Lemma 5.1 gives #a ≤ C L^d t_x t_y/θ₀ = C δ^{−2} L^{d − 4γ − q_x − q_y + 6η}.
  - With Δχ = −1 the count is −3γ − q_x − q_y + 6η, and the right-hand side is (Prop 3.1)
    −η³ − γ − 3η − q_x − q_y − γ₀ − gη².
  - So the margin is 2γ − γ₀ − 9η − gη² − η³ ≥ γ − 9η − 3η² − η³ ≥ 191η − 3η² − η³ > 0 under 200η ≤ γ.
- **(c) tri(P) for an NC critical pair.** The R38 count (one slab) gives margin ≥ −(4η + 3η² + η³) + 5η
  = η − 3η² − η³ (Prop 3.1).
- **(d) A non-critical group-D step.** It has ν = 0.
  - If κ_x = 50 or κ_y = 50, the refund is larger by L^{50η}, and the margin is ≥ 46η − 3η² − η³.
  - Otherwise min(q_x, q_y) < −γ₀ − 4η, and Prop 3.1 gives margin > η − 3η² − η³.
- **(e) s with ν^cre_s = k ≥ 1.**
  - By Lemma 6.2, each NC critical pair P with s(P) = s restricts a free vector r_y of the count at s to the double
    cone {∠(r_y, ℝc_x) < θ₀}, which is centred at a current parameter (or at the step's other free vector).
  - Lemma 5.2 applies, since κ_y = 0 and q_y − 6η ≥ −γ₀ − 10η ≥ −1/2 − 10η ≥ −1. It replaces the factor (Q_yL)^d by
    C(Q_yL)^d θ₀^{d−1}, a gain of ≥ L^{−6(d−1)η} ≤ L^{−12η}.
  - **k = 2 at an Op-1 step.** Both joints y, y₂ are later ghosts, and their common vector ±r lies in both cones. One
    cone suffices: gain 12η.
  - **k = 2 at an Op-2 step.** The two new α-atoms have the two distinct free vectors of the B = 1 pattern: gain 24η.
  - The R38 margin at s is ≥ 0 (I2 and §9). So the margin of (★) is ≥ 12η − 5ηk ≥ 2η. ∎

**Remark 6.3 (constants).** Write θ₀ = L^{−λη}. The proof needs exactly the following:
- **(b):** 2γ − γ₀ − (3 + λ)η − 3η² − η³ > 0.
- **(c):** τ₀ > 4η + 3η² + η³.
- **(e):** (d − 1)λη ≥ 2τ₀ and −γ₀ − 4η − λη ≥ −1.
- **Lemma 5.1:** γ + η ≤ 1, so that t ≥ 1/L.

The choice λ = 6, τ₀ = 5η meets all of these as soon as η ≤ γ₀/12 and η ≤ 1/20. `TriReal` gives η ≤ γ₀/200.

**Remark 6.4 (this is the joint count of §4).** Fix a dyadic angle θ between r_x and r_y. Then (★) at s(P) gains θ^{d−1},
and at tri(P) the count is ≤ min(one slab, two slabs/θ). Their product is ≤ C t_x t_y up to factors depending on θ
only. That is the joint count of Lemma 4.1. The spec (f′) is the two-class version of this dyadic split.

## 7. Telescoping, and the rest of the run

**Theorem 7.1 (telescoping). PROVED.** ∏_s L^{τ₀(ν^tri_s − ν^cre_s)} = 1. Hence the per-step bounds (★) multiply to
exactly R38's product:
- every α label factor is paid once, at creation, and refunded at most once (at M_fin through Prop 9.6, or at its own
  deletion as a ghost); an untaken refund is a gain;
- ∑ΔF = F_fin − 1 and ∑ΔV_β = V_β,fin.

(together2) follows exactly as in GHOST §3b, then (together3) and (finalcount1) (TARGET L2207–L2215) with
F_im ≤ R (the Lean assembly of the final count; R29).

*Proof.* P ↦ s(P) and P ↦ tri(P) are functions on the finite set of NC critical pairs, and both steps belong to the
run: tri(P) is an Op-2 step, and s(P) precedes it. So ∑_s ν^cre_s = #NC = ∑_s ν^tri_s. ∎

**The rest of the run is unaffected. PROVED.** By definition, (f′) enters no rule of the run. The following are
therefore literally those of R38's run:
- the operations, their order and every intermediate molecule;
- the α/β/ε classes, labels and κ's;
- ΔF, ΔV_β, the defect D, F_im, p_op, p⁺_op, Z_tot and ρ.

Consequently the following hold verbatim, with no re-verification:
- `subpro` (TARGET L2040–L2053, and its 𝒱_γ version subpro′);
- Cor 1.16′ (disjointness, location, list, removal connectivity);
- `finalmol` (L2182–L2190, with E9, E11, E16, E17, R29);
- `excessprop1`(3);
- F_im ≤ R, p⁺_op ≤ 2R − 2, Z_tot ≤ 4(R − 1), ρ_fin ≥ ρ_sb − C₀p_op, and p_sb ≤ 2p_op (E19).

The only new cost is the factor 2^{#critical pairs} ≤ 2^{n_sb} of (f′). The literal enlarged object of §4 would not
have this property (Remark 4.3).

## 8. The flower: Operation 1E (O75 L814, L900; SUPP L29, L732)

- **Outer-joint remnants.** The outer-joint remnants of 𝕎′, and the joints of the survivors S, are created by O75
  Lemma 5 with ΔF = 0 (the computation of D23 L1797–L1801). So they are α-ghosts of Op-1 type, and I2 holds for them
  (O75 Lemma 5, proof item (ii): "the gap restriction at one joint"). Lemma 2.1 covers one Lemma-5 removal. Lemma 6.2
  and case (e) apply to them verbatim.
- **The HV 𝕎′ = S ∪ {e*} (§11.1).** By Corollary 2.2(a), its joints are never ghosts.
- **Re-cut remnants (§4.6, §11.3).** These have degree 0 and are never ghosts.
- **Fresh ΔF = 1 remnants.** These are β. β-ghosts need only a nonzero gap (N1) in groups B, C, and D with g = 3.
- **Flower factors.** The pin and face freezing (O75 row 12) and the N_E budget multiply the per-step bounds unchanged.
  The transfers cancel pair by pair, so O75 §11.3's "number of ghosts grows by ≤ 2N_E, with no extra power of L" is
  still true.
- **The η choice.** SUPP L29/L732 choose 8η ≤ 2γ − 1 for the ghosts. Replace this by `TriReal`'s 200η ≤ γ₀ together
  with (f′). CHECKED: the row `op1-vine` of `scheme_check.out` is the Lemma-5 count; the Op-1E ghosts enter the
  triangle patterns as ordinary α- or β-ghosts.

## 9. The pattern grid (CHECKED)

**`grid_low.out`: GHOST's grid on γ ∈ (0, 1/2].**
- **Range.** 16 values of γ (including 0.01, 0.5 and 6 random values); η ∈ {γ₀/200, γ₀/1000, γ₀/5000};
  d ∈ {3, 4, 5, 8}; κ_new, κ_ghost ∈ {0, 50}; a 12-step label grid.
- **Part 1, charged R38 margins.** Only the 6 group-D patterns are ever negative, with minimum −(4η + 2η² + η³). No
  value lies below −(4η + gη² + η³), and none occurs outside the zone min label > q*. The minimum over groups A–C is
  1.0001η².
- **Part 2, closed forms** (γ ≤ 1/2, d = 3, κ = 0, minimum over labels; 165/165 agree with a 40-step grid). Closed
  forms for general d are PROVED by the computation of §3: insert the count of I1 and minimise over q.

| Group | Pattern | Closed form (d = 3) | General d |
|---|---|---|---|
| A | B = 1 (two new α) | γ − η − 2η² − η³ | 2(d−1)(γ−η) + 3η − γ₀ − 2γ − 2η² − η³ |
| A | B = 2 (one new α) | γ/2 − η/2 + η² − η³ | (d−1)(γ−η) − 3γ/2 + 3η/2 + η² − η³ |
| A | B = 3 | 4η² − η³ | — |
| B | B = 3 | (4 − g)η² − η³ | — |
| B | B = 2 | ≥ the A, B = 2 value (grid) | — |
| C | B = 2 | γ − 2η − 2η² − η³ | (d−1)(γ−η) − γ₀ − 2η² − η³ |
| C | B = 3 | γ/2 − 3η/2 + (2 − g)η² − η³ | — |
| D | — | −4η − gη² − η³ | — |

- **Part 3, uncharged margins.** Every one of the 21 patterns with an α-ghost is negative, as in GHOST §1.

**`scheme_check.out`: the repaired scheme of §6 over (0, 1/2] and (1/2, 1), with `TriReal` only (no
8η ≤ 2γ − 1), plus adversarial end points (γ ∈ {0.002, 0.005, 0.4999, 0.5, 0.5001, 0.502, 0.995}, η = γ₀/200, a
30-step grid).** Every margin is ≥ 0. The minima, divided by η:

| Step | Minimum margin / η |
|---|---|
| Group D, TR | ≥ 190.99 |
| Group D, NC | ≥ 0.99 |
| Group D, non-critical | ≥ 2.69 |
| Op-1 vine (= HV, T-vine, 1E), k = 0 / 1 / 2 | 2.0 / 9.0 / 4.0 |
| Op-1 VC2, k = 0 / 1 / 2 | 3.0 / 10.0 / 5.0 |
| Op-2 creations | ≥ 99.5 |
| Groups A–C | positive (≥ η² − η³ for the β-only B = 3 patterns) |

**Other checks.**
- `lattice_check.out`: Lemmas 5.1 and 5.2, and the joint/sequential ratio of Lemma 4.1 (see §4 and §5).
- `sourceA_check.out`: Lemma 2.1 holds on 34 molecules, all with r_z ≡ 0 and r_x ≡ −r_y. For two different objects,
  r_x = r_y with r_z ≠ 0 is attainable in all 16 random cases.
- GHOST's scripts, re-run: `patterns.out` and `check_charged.out` were regenerated byte-identically.

## 10. Lean-facing deliverable (the analogue of R38's `8 * η ≤ 2 * γ - 1`)

**Hypotheses.** `TriReal` only: `3 ≤ d`, `0 < γ < 1`, `0 < η`, `200 * η ≤ γ`, `200 * η ≤ 1 - γ`, `exp 1 ≤ L`,
`0 < δ ≤ 1`, `1 ≤ C₁`. **No `hH`.** The real inequalities used are:
- η ≤ 1/20;
- 9η + 3η² + η³ < γ ≤ 2γ − γ₀;
- 4η + 3η² + η³ < 5η;
- 10η ≤ 6(d − 1)η;
- γ + η ≤ 1;
- −γ₀ − 10η ≥ −1;
- for the constants, L ≥ L₀(d, c, η, δ), via `ghostConst` as now.

### 10.1 Triangle step (replaces the `hH` uses in `triangle_excess_ghost`, the Lean ghost step for γ > 1/2)

Let j₁ ≠ j₂ be two α-ghosts, `ag j₁ ∧ ag j₂`, and write g_i := gapAt (T.a j_i) (T.b j_i).
- **(T-crit-free).** If `kg j₁ = 50 ∨ kg j₂ = 50 ∨ min (Qg j₁) (Qg j₂) < L ^ (-(min γ (1-γ)) - 4*η)`, the conclusion is
  the current one, unchanged. This replaces `arith_P5_alpha2` in that case.
- **(T-TR).** If `∀ κ' ∈ Adm, L^(-12*η) * (‖g₁‖^2 * ‖g₂‖^2) ≤ ‖g₁‖^2 * ‖g₂‖^2 - ⟪g₁, g₂⟫^2`, the conclusion is the
  current one. It needs a new counting lemma, `card_twoSlab` (Lemma 5.1).
- **(T-NC).** The conclusion holds with the right-hand side multiplied by `L^(5*η)`. This needs no hypothesis at all,
  since case (c) holds for every pair.
- **Group C, B = 2 (`arith_B2_alpha`).** At γ ≤ 1/2, the existing Lean count `lhs_ba` does not suffice. Its exponent
  requires 2γ₀ − 2γ + 3η + 3η² + η³ ≤ 0, which is false. Use the ghost-label slab (`card_slabF_nu`, already in the Lean
  ghost step for γ > 1/2); the margin is then (d−1)(γ−η) − γ₀ − 2η² − η³ (§9).
- **`arith_B2_beta`.** It holds at γ ≤ 1/2 with the existing count. Re-prove it with `min γ (1-γ) ≤ γ` instead of
  `≤ 1 - γ`, and drop `hH`.

### 10.2 Creation steps (UStep1 for Op-1/1E with ΔF = 0, and UStep2 when it creates α-atoms)

- **New hypothesis.** An optional cone hypothesis for each created α-atom y with `κ_y = 0` and
  `Q_y ≥ L^(-(min γ (1-γ)) - 4*η)`:

  `hcone : ∀ κ' ∈ Adm, ‖g_y‖^2 * ‖c‖^2 - ⟪g_y, c⟫^2 < L^(-12*η) * (‖g_y‖^2 * ‖c‖^2)`.

  Here c is either the parameter c_x of a present atom of the pre-state (the alive centre), or the other free gap of
  the same Op-2 step.
- **Conclusion.** The right-hand side is multiplied by `L^(-5*η*k)`, with k ≤ 2. At an Op-1 step one cone hypothesis
  suffices for k = 2.
- **New counting lemma.** `card_cone` (Lemma 5.2), used on the annulus of the creation gap.

### 10.3 Supporting lemma and assembly

- **Lemma 2.1 in Lean.** If both triangle ghosts are the two joints of the object removed at one Op-1/1E step, then
  `gapAt z = 0` on `Adm`, which contradicts eligibility (`hnz`). This supplies Lemma 6.2(iii): the cone centre is
  present.
- **Assembly (the Lean assembly of the final count, `WTPrefix`).**
  - Add (f′) to the specification: one Bool per critical pair, enumerated with the other specification data, at a loss
    of 2^{n_sb}.
  - Add the matching maps s(P) and tri(P), and the identity ∏ L^{5η(ν^tri − ν^cre)} = 1.
  - Then the telescoping is R38's.
  - Delete `η₀ ≤ (2γ − 1)/8`.

## 11. Status of every claim, and the open remainder

| Claim | Status |
|---|---|
| Lemma 2.1, Cor 2.2 (the proposed one-object configuration is never eligible) | PROVED; CHECKED (`sourceA_check`) |
| Prop 3.1 (deficit ≤ 4η + gη² + η³ and its zone) | PROVED; CHECKED (`grid_low` part 1) |
| Closed forms of groups A–D at γ ≤ 1/2 | PROVED; CHECKED (`grid_low` part 2, 165/165) |
| Remark 3.2 (creation-slack banking is short at d = 3 for double bonds) | PROVED (arithmetic) |
| Lemma 4.1, Remark 4.2 (count of the enlarged object, all γ) | PROVED; ratio CHECKED (`lattice_check` (3)) |
| Remark 4.3 (a literal merge would change the run) | SKETCH (not needed) |
| Lemmas 5.1, 5.2 | PROVED; CHECKED (`lattice_check` (1), (2)) |
| Lemma 6.2, Theorem 6.1, Remark 6.3 | PROVED, from I1–I4 |
| Theorem 7.1 and "rest of the run unaffected" | PROVED |
| Flower §8 | PROVED, from O75 Lemma 5, §11.1 and §11.3 |
| Repaired-scheme margins over (0, 1) | CHECKED (`scheme_check`) |

**Inputs, not re-proved (INPUT).**
- I1: GHOST's Op-2 counting model, Lean-proved for γ > 1/2 (the Lean triangle step and the Lean ghost step for
  γ > 1/2). The form of its counts (free vectors
  = the new α's gaps, slabs) does not use γ > 1/2.
- I2: the Op-1 counts. For γ ≤ 1/2 these are DH23's own range; for T-vines they are N1 §3.2 and N2 §2.1 (REFEREED).
- I3: R29 and R38/E21.
- I4: DH23/TARGET decorations. Lemma 2.1 uses c_v = 0 at every degree-4 atom of M_sb, including hinge atoms and the
  flower's pinned and face atoms (pins fix times, not momenta).

**OPEN or not addressed (outside this note).**
- DH23 Prop 9.6, cases other than (4), and DH23 Prop 10.4(2) with its counting inputs, at γ ≤ 1/2: these are the
  subject of the counting note. The counting note should take Theorem 6.1 and Theorem 7.1 as its ghost input, proved
  here.
- Whether a group-D pair from two different objects actually occurs in a stage-1 molecule. This is not needed: the
  scheme covers every case.

**Referee targets (refute-first).**
1. Lemma 2.1 step 2: is c_v = 0 at every degree-4 atom of M_sb, in the TARGET garden setting and in the flower?
2. Lemma 6.2(ii): is every α-creation count of the form "free gap × uniform rest"? In particular, the counts of the
   Lean triangle step `card_βα`, `card_αβ`, and the B = 1 count.
3. Theorem 6.1(b): the window and parameter bookkeeping for g = 3. The triangle is then a whole component, and only
   Γ_x and Γ_y are used.
4. That (f′) is a legitimate refinement under the DH23 definition of the counting quantity, given that it refers to
   gaps that are later deleted.

## 11a. Cross-check against the counting note (`gamma-le-half-counting-notes.md`, READY)

**The 4η deficit.** The counting note (§3.4) finds that the group-D deficit at γ ≤ 1/2 is 4η + gη² + η³, occurring
only when both α-ghost labels lie above L^{−γ−3η−O(η²)}. This is Prop 3.1 here, derived independently: same closed form, same zone.
The conclusion of this note is **unchanged**, because the scheme of §6 was built on exactly this deficit:
- the transfer τ₀ = 5η need only exceed 4η + 3η² + η³;
- a cone of aperture L^{−6η} pays 2τ₀ at d = 3;
- the TR margin 2γ − γ₀ − 9η − … is positive.

If the deficit were (1 − 2γ) + 4η, the NC case would need τ₀ > 1 − 2γ and a cone of aperture
L^{−(1−2γ)/(d−1)−O(η)}, which a small-γ label cannot afford. So the small deficit is what makes this route cheap.

**What the 4η deficit does not do.** It does not make pure creation-slack banking work (Remark 3.2):
- double-bond removals at d = 3 give each ghost only η to 2η;
- re-weighting h cannot fix this.

The counting note's own table agrees: it records that banking "falls short by ≈ 2η–3η" for bad vines and for α-cuts. The cone gain of
§6 (e) is therefore still needed, though only at the scale O(η).

**The counting note's α-cut row is not a ghost source in TARGET's order.** Op 3 runs after Op 2 (TARGET L2148; R29: "the skipped v₁,
v₂ are cut in Op 3"), so an α-cut atom is never a ghost of an Op-2 triangle. Theorem 6.1 (e) would cover such atoms
anyway: an α-cut counts its gap r with |r| ~ Q freely, (QL)^d choices (the counting note, §3.2). Its R38 margin m_α ≥ η − η³ ≥ 0,
so the margin of (★) is ≥ m_α + 12η − 10η > 0.

**The counting note's (operc) and uncapped A.2(1) points (its Findings 1 and 2).**
- They concern Prop 9.6's final-component counts: cases (2), (4)′ and (opere). They do not concern the per-step
  triangle bounds.
- The counts used here are GHOST's slab model (I1, which is the model of the counting note, §3.3, with γ₀ = γ), the
  Op-1 counts I2 (the counting note, §3.5),
  and Lemmas 5.1–5.2, which are elementary lattice counts in the volume regime t = W/Q ≥ 1/L.
- No capped or uncapped A.2(1) bound and no (operc) enters Theorem 6.1. **No change.**

**This note proves the ghost lemma G of the counting note (§7 there; an input that note takes as proved elsewhere)
in its form (G-D).**
- **(i) The excess of the group-D steps is paid.** At an NC critical pair the triangle step carries L^{+5η}, paid by
  the cone gain at the later creation step. At a TR pair the excess is absent, since two slabs are used. Non-critical
  pairs have no excess. The telescoped product equals R38's (Theorem 7.1).
- **(ii) No triangle component with two α-atoms survives.** The run is R38/R29's run unchanged, and every eligible
  group-D triangle is still removed in Op 2. A perfect triangle with two α-atoms and a β-atom has a nonzero v₃ gap by
  N1, so it is eligible. Hence finalmol's cycle clause holds as in the Lean assembly of the final count.
- **(iii) N1, N2, `noBetaCut` and `vineLG`_γ are preserved.** The run, the classes and κ are unchanged, and (f′) only
  partitions decorations.

In the counting note's words: "the charged triangle deviation with an extra factor L^{θ_s} on group-D steps", with θ_s = 5η at NC
critical pairs. The "global bank" is the cone gain, ∑_s θ_s = ∑_s 5ην^cre_s. This bank is paid by the specific creation
steps s(P) and is cancelled exactly, not just bounded.

**The η-hypotheses are compatible.**
- The counting note's (H_η) includes dη ≤ γ/1000, i.e. η ≤ γ/3000. That implies everything §6 needs: η ≤ γ₀/12, η ≤ 1/20, γ + η ≤ 1.
- `TriReal` (200η ≤ γ₀) suffices on its own for the ghost lemma.
- The counting note's binding Prop 9.6 margin (γ − 104η) is untouched.

## 12. Files

The scripts and their outputs are not included in this repository.

| File | Content |
|---|---|
| `grid_low.py` → `grid_low.out` | GHOST grid on (0, 1/2], closed forms, uncharged margins |
| `scheme_check.py` → `scheme_check.out` | the repaired scheme of §6 on (0, 1), creation steps, adversarial ends |
| `lattice_check.py` → `lattice_check.out` | Lemmas 5.1 and 5.2, joint versus sequential count |
| `sourceA_check.py` → `sourceA_check.out` | Lemma 2.1 (conservation) and the two-object contrast |
| GHOST's scripts | re-run, see §9 |
