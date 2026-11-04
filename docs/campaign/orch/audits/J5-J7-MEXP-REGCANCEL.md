# Statement audit: wt-torus J5–J7 (MEXP, WKE-ID, REGCANCEL)

Auditor: `wt-orch`, refute-first. Date: 2026-11-04 (Task 31a). Findings only; nothing was edited.

**Scope.**
- **Landed:** `Foundations/Cancel/{TimeSplit, CollisionLin}` (main `ed94088`).
- **Scratch:** `/home/scott/wt-scratch/mexp` (`HANDOFF.md`, J5–J7) and `/home/scott/wt-scratch/cancel` (CANCEL7's
  `CancelDraft`, which the stack imports).
- **Questions:**
  - DH21 Props 7.7 and 7.8 with the F61 weight;
  - `wke_identity` and `regularAsymptotics_item4`, exactly against B2.1 item (4) of the final B2 candidate;
  - J7's statement form for DH23 Prop 6.3: is it what TARGET's consumer needs?

## Verdict

**PASS.**
- **Prop 7.7.** `prop77` is DH21 Prop 7.7. The type 1 and type 2 recursions are those of (inductm01)–(inductm05).
- **Prop 7.8.** `prop78` is DH21 Prop 7.8 with the F61 weight. On a class this is the same statement, since `|Z|`
  is constant there.
- **Item (4).** `regularAsymptotics_item4` discharges **B2.1 item (4) exactly**. In one environment, I proved B2.1
  restricted to its conjunct (4), verbatim in B2.1's binders, from it.
- **J7.** `regcancel` is exactly TARGET's use of DH23 Prop 6.3, the single-layer case of (layerregest10).
- **Findings:**
  - T-1: scope; the multi-layer case is TARGET's own extension and is not covered.
  - T-2: the interface for a garden-level consumer.
- **Axioms:** all [propext, Classical.choice, Quot.sound].

## 1. Inputs and environment

**Pins.** `mexp` was pinned at 06:53 UTC: 95 files, list digest `536e4267a560…`; its `check/SHA256SUMS` verifies.
`cancel` was pinned with 13 files, digest `d0e110464942…`. Both were unchanged at the end.

**B2 base.**
- mexp's `WaveB2Draft/Regular.lean` is byte-identical to `waveb2-snap-final`'s (`4d7f81ef…`; CL-21 did not touch
  it).
- Its `RegularDefs` is a shim that imports `Regular`.
- B1 Core and System are snapshot 7's (`0b8477d9…`, `59365906…`).
- mexp's `CancelDraft` sources equal `cancel/src` byte for byte.

**Landed Foundations.** All 23 `Foundations/Cancel` files on main equal torus-fourier's, the base of the scratch
build.

**Build consistency.**
- I checked the import closure of `MexpDraft.{WkeId, RegCancelB2, Prop78, MShape}`, resolved along the build's
  search path: 98 modules.
- No olean is older than a transitive import, and no source is newer than its olean.

**One environment.** I used the mexp stack read-only, plus my own compile of `waveb2-snap-final`'s `Molecules` and
`Statements` on top. Both compiled; Molecules' one `sorry` is the existing `isMolecule_molecule` obligation.

## 2. J5: DH21 Props 7.7 and 7.8

**`prop77`** (DH21 `multiexp`, L1814).
- **Statement.** If `Shape.Equiv (cplShape Z 𝒬 …) (cplShape Z' 𝒬' …)` for dominant `𝒬, 𝒬'`, then
  `𝒬.Mstar F Z … = 𝒬'.Mstar F Z' …`. That is "`ℳ*_𝒬` depends only on the class".
- **Classes.** A class is an ENHANCED `Shape` up to `Shape.Equiv` (C5's reading of DH21 Def 4.18; audit
  `ENHANCED-prefreeze.md`).
- **The common value `Mshape`.**
  - Trivial: `F` (`n_in`).
  - Type 1: `resIntegral` of the three factors, which is (inductm01). `mshape_type1` holds by `rfl`.
  - Type 2: `ℳ*_𝒴 · ∏_j Npair 𝙸_j 𝚌_j …`, which is (inductm02).
- **The pair factors.** `Npair` takes `𝒳_{j,1}` at `redSlot c` and `𝒳_{j,2}` at `greenSlot c`. Those slots are
  `(k₂, k₃)`, `(k₁, k₃)`, `(k₁, k₂)` for `𝚌 = 1, 2, 3`, which is (inductm03)–(inductm05). The factor is `δ(Ω)` for
  `𝙸 = 0` (`resIntegral`) and p.v. `1/Ω` for `𝙸 = 1` (`pvResonantIntegral`).
- `Mstar` is B2's frozen definition, and `mstar_eq_mshape` is proved.

**`prop78`** (DH21 `nonemptyZ`, L1838).
- **Statement.** For `r ≤ t`, every `n` and every `S` with `S.zcount ≠ 0`:
  `∑_{𝒬 ∈ domCodes n} ∑_{Z special} [cplShape Z 𝒬 ∼ S] · specialWeight ![1,-1] Z · 𝒥ℬ*_𝒬(r; t, t) = 0`.
- **It is DH21's sum over the class.** All members of a class have the same order, so the sum over `domCodes n`
  with the class indicator is the class sum, or empty.
- **Weight.** It is F61's `∏(−ζ_𝔫πi)⁻¹` in place of DH21's `∏(ζ_𝔫πi)⁻¹`. They differ by `(−1)^{|Z|}`, which is
  constant on a class, so the two statements are equivalent.
- **Domain.** `t ≥ r` generalizes DH21's `r = 0`, `t ∈ [0,1]`.
- **The object `𝒥ℬ*`.** `𝒥ℬ*` is B2's `RegCpl.JB`, not DH21's `𝒥B̃` computed from the garden. They agree through
  CANCEL7's Prop 7.5 applied to the garden-defined `B̃` (audit `BTILDE.md`).

**`prop78_mstar`.** The same with the factor `ℳ*`, constant on the class by `prop77`. This is the form item (4)
uses.

## 3. J6: `wke_identity` and B2.1 item (4)

**`wke_identity`**:
`(hd : 2 ≤ d) (F : 𝓢) (δ p) (n) (p ≤ t) (k) : ∑ᶠ 𝒬 (wf ∧ dominant ∧ size = 2n), 𝒬.app δ p F t t k =
wkeTaylorTerm F δ p n t k`. The sum and the objects are B2's own: `RegCpl.app` and the frozen B1 `wkeTaylorTerm`.

**Exactness against B2.1 item (4).**
- A script extracted B2.1 from `waveb2-snap-final/WaveB2-Statements.lean`, kept its `WTPrefix` prefix, the binders
  `p, r, R, n` and the `let F`, and kept only conjunct (4), verbatim.
- I proved this proposition (`b21_item4_only`) in the environment above:
  - the prefix witnesses are trivial (`η₀ = C₁ = ν₀ = δ₀ = C₂ = 1`, `L₀ = 2`);
  - `subst` `r = p`;
  - the term is `regularAsymptotics_item4 ⟨…⟩ (3 ≤ d ⇒ 2 ≤ d) r R n`.
- Axioms are standard. **Item (4) is discharged exactly, and unconditionally:** it uses no prefix smallness,
  `InputRemainder`, or order bound.
- The proof route (no encoded trees; DH21 7.9/7.10 merged into one recursion) does not touch the statement. It
  confirms B2's remark (D7) that the F61 weight does not affect item (4).

## 4. J7: `regcancel` against DH23 Prop 6.3 and TARGET's consumer

**DH23 Prop 6.3** (`regcpltreecancel`, L940; (realcancel)). For `0 ≤ s < t ≤ 1`, the sum over all regular couples
`𝒬` and regular trees `𝒯` of sign `+` of total order `2n` of `(K_𝒬)_app(t,s,k) · conj((K*_𝒯)_app(t,s,k))` is real.

**`regcancel`** (`δ r F n`, `r ≤ s ≤ t`, `k`):
`(∑_{(a,b) ∈ antidiagonal n} ∑_{𝒬 ∈ domCodes a} ∑_{𝒳 ∈ domTrees b} 𝒬.app δ r F t s k ·
conj(𝒳.app δ r F 1 t s k)).im = 0`.

**The objects are B2's frozen leading terms**, `RegCpl.app` and `RegChain.app` with `ζ = +1`.
- Both are `0` for non-dominant codes, by definition. So the dominant-only sum is the sum over all regular codes.
- **The order-0 terms are included.** `RegCpl.triv ∈ domCodes 0` and `RegChain.nil ∈ domTrees 0` (checked).
- **Codes against couples.** There is one term per code. That is one per regular couple or tree through the
  code–carrier correspondence: B2's reading D4, the same one B2.1 item (4) uses.

**TARGET's consumer.**
- TARGET uses DH23 Prop 6.3 once: in the proof of Prop `proplayer4`, (layerregest10) (L1121–L1123, proof L1251).
  For fixed `0 ≤ q' ≤ q ≤ p`, `(t, s) ∈ ℬ` with `t > s`, and total order `2n`, (layerregest10) says that
  `∑_{(𝒬,𝒯)} (K*_𝒬)_app · conj((K*_𝒯)_app) ∈ ℝ`, summed over coherent regular couples and `+` trees.
- L1251: "We may also assume `q > q'`, since otherwise all the nodes in `𝒬` and `𝒯` must be in the same layer, and
  the result follows from Proposition 6.3 of [DH23]".
- In B2's terms, that case is `𝒬.app δ q F_q` and `𝒳.app δ q F_q 1` on `[q, q+1]²` with `t > s`. That is
  `regcancel` with `r = q` (`q ≤ s ≤ t`), on the same input `F_q` for the couple and the tree.
- The extra clause of (layerregest10), a fixed number of layer-`p` branching nodes, is automatic in this case: the
  number is `2n` if `q = p` and `0` otherwise.
- **So `regcancel` is the right form for the case TARGET takes from DH23.** It is also more general: any real `F`
  and `δ`, `s = t` allowed, no upper time bound.

## 5. Findings

**T-1 (scope; not a defect).** TARGET's (layerregest10) for `q > q'` ("an extended version of the proof",
L1251–L1270), and its restricted form, is not covered by J7. It is TARGET's own extension, with the
`ζ̃_𝔫 = −ζ_𝔫` signs on `Z_{j,0,ι}`, `Z⁰`. It remains an obligation for whichever packet formalizes `proplayer4`.
`GJ_eq_zero`'s peeling machinery (`jsh`, `weighted_Jt_decomp`) is the natural base.

**T-2 (interface).** `regcancel` and `wke_identity` are stated over B2 codes. A consumer stated over layered
gardens, as TARGET's sums are, passes to codes through the code–carrier bijection. That is the decoding statements
O1–O4 (`existsUnique_regCpl_decodes`, `existsUnique_regChain_decodesTree` and the existence halves), which the
CL-22 ruling now makes B2 anchors. Neither J7 nor J6 needs them for its own statement.

**Readings checked and accepted.**
- R1: classes as `Shape.Equiv`.
- R2: the F61 weight.
- R4 and R8–R10: the time domains `t ≥ r` and `r ≤ s ≤ t`; DH23's `s < t` is extended to `s = t`.
- R7: `d ≥ 2` and Schwartz `F` in J6. B2.1's `P.φ` is Schwartz-valued, and `(Π)` gives `d ≥ 3`.
- R11: any real `F`.
- R12, R13: the tree sign and the statement form.
