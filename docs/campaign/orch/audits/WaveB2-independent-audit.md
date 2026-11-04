# Wave B tier B2: independent freeze audit (Task 20)

Auditor: independent (did not draft any audited text). Date: 2026-11-04. Method: `lean-statement-audit` (binders,
carriers, definition bodies, characterizations, consumption, axioms), refute-first, fail closed.

## Verdict

**FAIL (as pinned).** Two problems block the freeze.
- **B2.1 `regularAsymptotics` is false as stated.** Item (2) fails, and so does the tree half of item (3), whenever the
  lone leaf lies in a lower layer than the other nodes (`q' < r`). The definition at fault is `RegChain.JBtree` (F-1).
  The fix is one line.
- **B2.3 `rigidity` is not ready to freeze.** Three things are missing:
  - the stage-2/3 audit's R1 (self-loops) is still not fixed;
  - its R2 (ZG-tame ε-atoms) is still not fixed;
  - the author has not ruled on the abstract hypothesis set (DESIGN Q7).

Everything else I checked passes:
- the CL-11 sign fix (F61), which I re-derived independently from the B1 kernel;
- B2.2;
- the §4 obligations;
- the molecule definitions after CL-3 and CL-5;
- closure, `sorry` placement and `deriving`.

Two REQUIRED items remain: the principal-value characterization (F-5) and the instance/manifest packaging (F-6).

After F-1 and F-5/F-6 are fixed, Regular, Molecules, B2.1 and B2.2 can be re-checked as a unit. B2.3 should stay out of
this freeze.

## Inputs

**Snapshot.** `/home/scott/wt-scratch/waveb2-snap-2/`. `sha256sum -c SHA256SUMS` passes for all 8 files.
- The live `/home/scott/wt-scratch/waveb2/*.lean` and `src/WaveB2Draft/*.lean` are byte-identical to the snapshot.
- The `build/` modules were compiled from them on 2026-11-04 at 01:18–01:19.

**B1 base.** The B1 sources `Core.lean` and `System.lean` are identical to `waveb-snap-6`.

**Sources.**
- TARGET `WKE-Longer_times_Final_arXiv.tex`;
- DH21 `Inventiones-Final_Version.tex`;
- DH23 `Revision_Submit.tex`;
- FINDINGS F11, F16, F33, F37, F53, F55, F57–F59, F61;
- the handoff `WaveB2-handoff.md`;
- the prior audits `WaveB2-stage1.md`, `WaveB2-stage23.md`, `MOLE-prefreeze.md`, `DEGEN-F53.md` and
  `REG-STRUCT-prefreeze.md`.

**Probes.** All are in `/home/scott/wt-scratch/b2-audit/`. Each was run alone with `nice -n 5 lake env … lean`, on
`LEAN_PATH` = `waveb/build` + `waveb2/build`.

| Probe | Content | Result |
|---|---|---|
| `P0.lean` | the elaborated type of B2.1; axioms of `RegCpl.app`, `Garden.molecule`, `GNode.parent`, `countA` | standard axioms |
| `Closure.lean` | dependency closure of all 394 non-theorem declarations of Regular, Molecules and Statements | see item 4 |
| `P1.lean` | `KTstar_indep_of_le`, `app_chain10_affine`, the F61 weight of one `+` node | `[propext, Classical.choice, Quot.sound]` |
| `P2.lean` | the stage-2/3 self-loop probe re-run on the current definitions; axioms of `maximalLadders_pairwiseDisjoint` | standard axioms |
| `P3.lean` | `sorryAx` sweep; the proposed `JBtreeFix`; the F61 weight of one `−` node; special sets of a two-pair chain | 0 errors |
| `P4-StatementsProbes.lean` | the snapshot's Statements probes, re-elaborated | 0 errors |
| `P5.lean` | **F-1 on the project's own instance `miniTree10LG`**: `miniTree10_KTstar_const` and `chain10_app_diff` | standard axioms |

---

## Findings

### F-1. BLOCKER: `RegChain.JBtree` uses lower limit `s`, so B2.1 item (2) and the tree half of item (3) are false when `q' < r`

**Lean.**
- `WaveB2-Regular.lean` L515–517:
  ```lean
  noncomputable def RegChain.JBtree (r : ℝ) (X : RegChain) (t s : ℝ) : ℝ := X.JBchain r s t fun _ => 1
  ```
  This is the integral over `t > t₁ > ⋯ > t_m > s`.
- It is used by `RegChain.app` (L617–623), by B2.1 item (2) (`WaveB2-Statements.lean` L87–92, on the box
  `timeBoxGt r q'` with `q' ≤ r`) and by the tree half of item (3) (L100–105, the same box).

**Source.**
- TARGET (regref2-2) is stated only "for any `t,s ∈ [r,r+1]` and `t>s`" (L1185–L1188).
- The B1 kernel `K*_𝒯`, from Def `defkg` (timepairtree) (T L682–L684), uses the time domain
  `𝔏_𝔫 < t_𝔫 < 𝔏_𝔫+1`, `t_{𝔫'} < t_𝔫 < t`, `t_{ℓ_lo^pr} > s`.
- The regref1 box for trees is `([q,q+1]×[q',q'+1]) ∩ {t>s}`, with `q'` the layer of the lone leaf (T L951,
  L682). So `s ∈ [q', q'+1]` can lie below `r`.

**What is wrong.** When all branching nodes lie in layer `r` and `s ≤ r`:
- the constraint `t_{ℓ_lo^pr} > s` follows from `t_{ℓ_lo^pr} > r`;
- so `K*_𝒯(t,s,k) = K*_𝒯(t,r,k)`, and the true leading coefficient is `𝒥ℬ*_𝒯(t, max(s,r))`;
- but `JBtree r X t s` integrates down to `s`. For the mini-tree it equals `t − s` (the project probe
  `JBtree_chain10`), not `t − r`.

**Counterexample.** It is the project's own non-vacuity instance `regularAsymptotics_item2_nonvacuous`
(`WaveB2-Statements-probes.lean` L57–65): the mini-tree `10`, `X = chain10`, `r = 1`, `q' = 0`, `n = 1`.
- `P5.miniTree10_KTstar_const`: `KTstar … miniTree10LG t s k = KTstar … miniTree10LG t 1 k` for every `s ≤ 1`.
- `P5.chain10_app_diff`: `chain10.app δ r F ζ t s k − chain10.app δ r F ζ t 1 k = (1 − s) · c(k)`, where
  `c(k) = chain10.app δ r F ζ 1 0 k` does not depend on `(t, s)`.
- So on the item-(2) box `[1,2]×[0,1]`, `K*_𝒯 − app` has a slope `c(k)` in `s`. `XNorm` bounds `ess sup` on the box
  (Fourier inversion), so item (2) forces `|c(k)|/2 ≤ C₁(C₁δ)L^{-(γ₁−√η)}`.
- `c(k)` does not depend on `L`. Its real part is `−(δ/4)·resIntegral(F(k₂)F(k₃))(k)`:
  - `ζ(𝒯) = (i)(i) = −1`;
  - the `Z = {root}` term is purely imaginary.

  It is nonzero for `R = 0` and nonzero `φ(δ)`, for example a nonnegative WKE solution: the integrand is `≥ 0` and
  positive near `ℓ = w = 0`.
- Taking `L → ∞` with `√η < γ₁` gives a contradiction. The hypotheses are met: `p = r = 1`, `D ≥ 2`, `R = 0`
  satisfies `InputRemainder`, and `n = 1 ≤ N_2^4`.

**Item (3), trees.**
- With `q' = 0` and `r = p = D − 1`, `JBtree` of the mini-tree is `t − s ≥ D − 1` on the box.
- Hence `XNorm00Restr ≥ D − 1 = τ★/δ − 1`.
- `C₁` is chosen before `δ`, so `≤ C₁·C₁` fails for small `δ`.

**Fix** (exact replacement for L515–517):
```lean
/-- **`𝒥ℬ*_𝒯(t, s)`** of a dominant tree code (T (regref2-2)): `∫_{t > t₁ > ⋯ > t_{m₀} > max(s, r)}
∏_j ∏_ι 𝒥ℬ*_{𝒬_{j,0,ι}}(t_j, t_j) dt`. T states (regref2-2) for `s ∈ [r, r+1]`. For `s < r` (lone leaf in a lower
layer, the box of B2.1 item (2)) the constraint `t_{m₀} > s` is implied by `t_{m₀} > r`, so the lower limit is `r`. -/
noncomputable def RegChain.JBtree (r : ℝ) (X : RegChain) (t s : ℝ) : ℝ := X.JBchain r (max s r) t fun _ => 1
```
Also:
- update the probe `JBtree_chain10` to `= t - max s r` (checked as `P3.JBtreeFix`);
- update DESIGN §1.5 and the stage-1 table row ("Trees: the lower limit is s").

B2.1's statement text does not change. An alternative is to restrict items (2) and (3) to `q' = r`. I do not recommend
it: TARGET's consumer (prooflayer1-2) (L1243) evaluates `K*_{𝒯_[r]}(r+1, r, k)` for trees whose lone leaf lies in
layer `r − 1`.

**Consumer note (OPTIONAL).**
- When some `𝒯_[r−1]` is trivial, the lone leaf of `𝒯_[r]` lies in layer `≤ r − 2`. Then `s = r ∉ [q', q'+1]`.
- `P1.KTstar_indep_of_le` (kernel independent of `s ≤ layer`) bridges that case. It is worth landing as a helper.

**How verified.** `P5.lean` and `P1.lean` (standard axioms); `P3.lean` for the fix; the argument above.

### F-2. BLOCKER for B2.3 only: stage-2/3 R1 is still open (a self-loop counted as a gap triple)

**Lean.** `WaveB2-Statements.lean`, `DecorationHyp`:
- `epsLG` (L201–202), `alphaGap` (L205–207), `iota` (L208–210) and `abNonzero` (L211–212) quantify over darts
  `x₁, x₂` at `v` with `out x₁ ≠ out x₂`. That includes `x₂ = mate x₁`.
- `alphaGap`'s `x₁ ≠ x₂` does not exclude this.
- `Molecules.IsCutData` (L594–595) has the same issue.

**Source.** T Def `defdiff` (L1938–1941): the gap of a triple `(v, ℓ₁, ℓ₂)` is defined for **two bonds**. Def
`defcut` (L2118) and `finalmol` (L2182–2191) say the same ("if v has two bonds").

**What is wrong.** On a component with a loop at an ε-atom, `DecorationHyp` forces `¬ Adm κ` for every decoration.
B2.3 is then vacuous there, while T `lgmolect` has content.
- Re-verified on the current definitions: `P2.loopMol_decorationHyp_empty` and `P2.loopMol_finalShape`, standard
  axioms.
- CL-5's connectedness clause fixes the `IsBlockGap` part only: a connected block cannot carry a loop at a joint.

**Fix.** Add `x₂ ≠ M.mate x₁ →` after `M.atom x₂ = v →` in `epsLG`, `alphaGap`, `iota` and `abNonzero`, and the
conjunct `x₂ ≠ M.mate x₁` to `IsCutData`. For example:
```lean
  epsLG : ∀ κ, Adm κ → ∀ v ∈ M.atoms, lab v = .eps → ∀ x₁ x₂, M.atom x₁ = v → M.atom x₂ = v →
    x₂ ≠ M.mate x₁ → M.out x₁ ≠ M.out x₂ → gapKind L γ η (gapAt L w κ x₁ x₂) = .LG
```

### F-3. BLOCKER for B2.3 only: stage-2/3 R2 (DESIGN Q6) is still open (ZG-tame ε-atoms)

**Lean.** `epsLG` requires LG.

**Source.** T `finalmol` (L2183–2184): an ε-atom "must be LG or ZG, and must be tame if it is ZG". `remtame`
(L2152) and DH23 §10.5 cover tame atoms in the proof.

**What is wrong.** The consumer, the proof of (finalcount1), applies `lgmolect` to every component of `𝕄_fin`. So
`DecorationHyp` cannot be discharged on components with a ZG-tame ε-atom.

**Fix (packet G8).** Transcribe "tame" from `remtame` (L2152) and DH23 §10.5, and weaken `epsLG` to "LG, or ZG and
tame".

### F-4. BLOCKER for B2.3 only: the abstract hypothesis set has no author ruling

**Lean.** `rigidity`, `WaveB2-Statements.lean` L261–268, takes the binders `FinalShape` and `DecorationHyp`.

**Source.** T `lgmolect` (L2193) is a statement about components of `𝕄_fin` with inherited decorations.

**What is wrong.** Replacing that domain by arbitrary molecules satisfying `finalmol`'s conclusions is a
domain-generalization design item. Under the five-bin rule these two binders are **EXCESS until RULED**.
- DESIGN Q7 and `WaveB2-stage23.md` §5 both recommend keeping B2.3 unfrozen until G8.
- Nothing since then has changed that.

**Fix.** Keep B2.3 out of this freeze. When packet G8 resolves F-2 and F-3 and DESIGN §3.3 (i), obtain the author's
ruling on Q7 and re-audit.

### F-5. REQUIRED: `pvResonantIntegral` is characterized only for compactly supported kernels (stage-1 O1)

**Lean.** `WaveB2-Regular.lean` L531–540: the body is a closed form (a symmetric quotient after slicing along `ℓ`).

**Source.**
- T (regref3-3) (L1213–L1220): "p.v. 1/(|k₁|²−|k₂|²+|k₃|²−|k|²)";
- DH21 Prop 6.7 / (defintegral) (L1667): "the singularities `1/Ω_𝔫` are treated using the Cauchy principal value".

**What is wrong.** The p.v. is a limit, so the definition is characterization-defined. Its only characterization,
`tendsto_pvResonantIntegral` (from the landed `energyPrincipalValue_spec`), assumes `hs : R < ‖x‖ → kernel = 0`. The
kernels B2 actually uses, `Mr(k_x)Mg(k_y)` built from `F = φ + R`, are decaying but not compactly supported.

I checked the formula itself:
- `Ω = −2⟨ℓ,x⟩ = |k₁|²−|k₂|²+|k₃|²−|k|²`, with Jacobian 1;
- the factor `−(2|ℓ|)⁻¹ ∫ (S(t)−S(−t))/(2t)` is `p.v.∫Ψ/Ω` with the correct sign;
- for the three Factor-2 placements, `S_ℓ` is C¹ and decaying, so I expect it to agree with the joint ε-cutoff
  limit.

But this is not proved on the real carrier. Fail closed.

**Fix.** Either:
- (a) extend the characterization to decaying kernels (replace `hs` by a decay hypothesis of `DeltaKernel` type) and
  restate the probe; or
- (b) record an author ruling that, in B2, the symmetric-quotient slice form **is** the definition of the p.v.,
  listed as a deviation of B2.1.

### F-6. REQUIRED (packaging, semantics-neutral): unnamed instances and no generated B2 freeze manifest

**Lean.** Ten anonymous `instance` declarations remain in the freeze set:
- `WaveB2-Regular.lean` L68, L70, L178, L193, L298, L308, L319 and L476;
- `WaveB2-Molecules.lean` L105 and L165.

**Convention.** B1 CL-16 made every frozen instance a named `@[instance_reducible, instance] def` (B1 `DESIGN.md`
L654–663), and B1 CL-18 generated `FREEZE-LIST.md` from the compiled modules. B2-CL-12 converted the two `deriving`
clauses but not these instances. B2 also has no generated manifest, so the manifest-pinning step of the skill cannot
be carried out.

**Fix.** Name the ten instances in the B1 style, and generate a B2 freeze list with `FreezeList.lean` adapted to the
three modules (my `Closure.lean` is a starting point).

### F-7. OPTIONAL: `Garden.isMolecule_molecule` carries superfluous hypotheses

**Lean.** `WaveB2-Molecules.lean` L277–279.

**What is wrong.** `hP`, `hw` and `hn` are not needed:
- for **every** garden, each atom has at most 2 incoming and at most 2 outgoing bonds;
- each component contains a branching root, which has no parent dart and so degree `≤ 3`.

MOLE's `garden_isMolecule` proves the statement with no hypotheses. Keeping them is sound but weaker.

**Fix.** Optionally drop them. The CL-6 docstring is correct as written.

### F-8. OPTIONAL: `deviation` (the ratio) is in the freeze set but used by nothing

**Lean.** `WaveB2-Molecules.lean` L631–639. The CL-7 docstring is now correct; I checked the three cases in `ℝ≥0∞`.

**Fix.** Freeze `IsDeviation` only (T (defdev) L2135, literal), or keep `deviation` with its docstring.

### F-9. OPTIONAL: documentation drift

- The handoff (§2 CL-1 and §4 item 1) still says the `GNode.parent` inlining "has not been done yet". CL-12 did it.
  - `WaveB2-Molecules.lean` imports only `WaveB2Draft.Regular`.
  - `GNode.parent` is inlined (L183–215).
  - `Closure.lean` confirms there is no project-theorem dependency.
- The handoff's CL list stops at CL-11, although DESIGN records CL-12.
- `RegChain.JBtree`'s docstring and DESIGN §1.5 need the F-1 update.

### F-10. NOTE (no action in B2): F61 downstream in TARGET's consumer

T (regrefproof3-1) (L1253–L1265) carries `∏_{𝔫∈Z}(\widetilde{ζ_𝔫}πi)^{-1}` and so inherits the `(−1)^{|Z|}`. Its
reality argument works per fixed unordered collection of extended tuples, for which `|Z|` is fixed. The common factor
`(−1)^{|Z|}` therefore leaves (layerregest10) unaffected. The proplayer4 packet should mention this.

---

## Item 1. The change list, CL-1 to CL-12

| CL | Verdict | Evidence |
|---|---|---|
| CL-1 (import `WaveBDraft.Lemmas`) | **superseded, resolved by CL-12** | The current Molecules imports only Regular. Closure is clean (item 4). The handoff text is stale (F-9). |
| CL-2 (dart-form rails) | superseded | Not in the file. Its defect, double rails, is rejected by CL-3 (`dblRail` probes). |
| CL-3 (`IsLadder` = `SourceLadder`) | **CORRECT** | Body at L371–376, identical to DEGEN-F53 R1's text. Each clause matches its source:<br>• `1 ≤ m`: "m+1 ≥ 2 double bonds", T L1384;<br>• distinct atoms: the figure;<br>• rungs exactly 2: "double bonds"; DH23 L790 counts rungs as double bonds;<br>• rails exactly 1 and opposite: "parallel single bonds … opposite directions";<br>• no rung direction clause: DH23 `remilia` (b), L801–806;<br>• no induced clause: the figure's end stubs.<br>`maximalLadders_pairwiseDisjoint` (Ladders.lean) has standard axioms (P2). |
| CL-4 (`WaveB2-Ladders.lean`, docstring) | correct (file not for freezing) | Statement `∀ M, M.IsMolecule → (↑M.maximalLadders).PairwiseDisjoint id`, about B2's own `maximalLadders`; standard axioms. |
| CL-5 (`GroupConnected`, `IsBlock`, `eraseBond`, `IsHyperBlock`) | **CORRECT** | See the questions below. |
| CL-6 (`propcplmol` docstring) | correct | The docstring now says `IsMolecule` ≠ connected and keeps `1 ≤ order` (F58). The hypotheses are superfluous (F-7). |
| CL-7 (`IsDeviation`, `deviation` docstring) | correct | `IsDeviation` is T (defdev) L2135 literally. The three exceptional cases in the docstring are right in `ℝ≥0∞` (`⊤·0 = 0`, `a/⊤ = 0`, `⊤/⊤ = 0`). See F-8. |
| CL-8 (`regular_count_le`) | **CORRECT** | Couples of order `2m` and trees of order `2m` with fixed root sign (R15-2) each have finite count `≤ C₀^m`, with `C₀ : ℕ` existential (T L861: "at most `C₀^m`"). `∃ C₀` is fine: Π has no `C₀` field, and REG-STRUCT proves it with `12^9`. The finiteness conjuncts block the `Nat.card = 0` escape. The source-object form is right: consumers get the code form from `exists_decodes`, `existsUnique_regCpl_decodes` and `size_eq_order`. |
| CL-9, CL-10 | probe-only; correct | `dblRail` is rejected. `open Resonant` is present in the probe file. |
| CL-11 (`specialWeight` sign, F61) | **CORRECT**, independently re-derived | See item 3. |
| CL-12 (inlining, no `deriving`) | **CORRECT**, apart from the instance naming in F-6 | `GNode.parent` and `Garden.molecule` are inlined. `GapKind` and `VineType` have explicit `DecidableEq` definitions. `grep deriving` finds only comments. |

**CL-5 questions.**
1. *Is connectedness right for every consumer?* Yes.
   - T `defblock` (L1328–L1331) and DH23 Def 4.10 (L712–716) assert "σ(𝔹) = 2 iff 𝔹 is a double bond". That holds
     only for connected blocks: a degree-only block with σ = 2 can carry a separate interior component.
   - The concatenation claim and `disjointlem` (b) need it (F57; MOLE's kernel counterexample).
   - Vines, VC, HV and HVC are drawn connected.
   - (CL)/(CN) blocks in `block_clcn` are consumers that take blocks as hypotheses. A stronger hypothesis only
     weakens such statements, and any producer of blocks (vines, concatenations) produces connected ones.
2. *Is the hyper-block the source's "adjoint"?* Yes.
   - "The atomic group formed by adding one bond between the two joints of a block" cannot be an atomic group of the
     same molecule with the same atom set as its adjoint.
   - So the adjoint lives in `M` minus that bond, which is exactly `∃ e, ends e = s(j₁,j₂) ∧ (eraseBond e).IsBlock S j₁ j₂`.
   - `σ(H) = σ(B)+1` is automatic, and `∃ e` handles two parallel joint bonds.
3. *Does anything decide `IsBlock`?* No frozen declaration does: only probes use it, and `IsVine` is a `Prop`.
   `IsVine`'s meaning is unchanged, because every expanded template is connected.

## Item 2. Meaning changes with no change of statement text

**B2.1, through `specialWeight` (CL-11).** I re-derived each item against the current definitions.
- **(1) Couples.**
  - Non-dominant codes: `app = 0`, which is (regref1-1).
  - Dominant codes: `app` is (regref1-3) corrected by F61, with `𝒥ℬ*` independent of `Z`. This is now what the
    source proofs give (item 3). With the old sign it was false for odd `|Z|`.
  - Carriers, the box `[r,r+1]²` and the norm `𝔛^{η,30d,30d}` match T L951 and L1146–L1150.
  - **True as far as the source shows.**
- **(2) Trees.** The sign is correct now, but the item is **false for `q' < r`** (F-1).
- **(3)** Couples: correct. Trees: **false for `q' < r`** (F-1, unbounded `JBtree`). The `ℳ*` bounds are correct
  (regref1-4).
- **(4)** Unaffected (CL-11 auditor question 2):
  - `|Z| = |Z'|` on a class (T L1136);
  - `ζ(𝒬)` is constant on a class (T L1265);
  - `ℳ*` depends only on the class (regref3);
  - so each class sum is multiplied by the common factor `(−1)^{|Z|}`, and (regref2-3) still kills `Z ≠ ∅`.

  I checked `n = 1` explicitly:
  - the 2 type-1 codes give `δ(t−p)∫δδ φ₁φ₂φ₃`;
  - the 12 type-2 codes give `δ(t−p)∫δδ(−φφ₂φ₃+φφ₁φ₃−φφ₁φ₂)`;
  - their `Z = {ρ^±}` terms cancel in pairs, `+` chain against `−` chain, with either sign;
  - the sum is `δ(t−p)𝒦(φ,φ,φ) = 𝒰₁`.

  `∑ᶠ` parses with the sum ending before `=` (P0). The support is finite (`finite_dominant_codes`, P4).

**B2.3, through `IsLadder` (CL-3; `countA`, `rho`, `ladderScale`/`ladderGap`) and `IsBlock` (CL-5; `vineLG`).**
- With the selected-bond `IsLadder`, maximal ladders are pairwise disjoint in every molecule (Ladders.lean). That is
  how T (defcounta2) (L2132) and DH23 `kqmainest2` count them (`ρ = q + m`, `∏_j 𝔛_j^{z_j}`).
- The old induced predicate made `ρ` and the ladder product differ from the source (chordLadder). So CL-3 brings
  B2.3's meaning **closer** to T `lgmolect`.
- `ladderGap` picks the unique single rail bonds, which is well defined now.
- `vineLG`'s `IsVine` is unchanged in meaning.
- B2.3 still cannot be frozen, for F-2, F-3 and F-4. The CL changes add no new defect.

## Item 3. The F61 fix

**Independent derivation from the B1 kernel.** Take the mini-tree, a chain pair `ρ ⊃ ν` with `ν` a child of `ρ` (the
dominant case).
- The link property gives `ζ_νΩ_ν = −ζ_ρΩ_ρ`. I checked it by hand for code `10`: `k = k_lone`, `Ω_ν = −Ω_ρ`.
- So the B1 phase (`phaseProd`: `e^{πiζ_𝔫δL^{2γ}Ω_𝔫t_𝔫}`) is `e^{πiλζ_ρΩ_ρ(t_ρ−t_ν)}`, with `λ = δL^{2γ}` and
  `t_ν < t_ρ`.
- Then `∫_0^v e^{πiλζΩu}du = (e^{πiλζΩv}−1)/(πiλζΩ) → λ^{-1}[δ(Ω) − (ζπi)^{-1} p.v.(1/Ω)]`, using
  `p.v.∫e^{iax}/x = iπ` for `a > 0`.

So the per-node weight of `Z` relative to the `δ(Ω)` term is **`(−1)/(ζ_𝔫πi)`**, with `Ω = Ω_𝔫 =
|k₁|²−|k₂|²+|k₃|²−|k|²` at the chosen node `𝔫_a` (the parent). This holds for both signs; for `ζ = −1` I conjugated
the computation. It agrees with DH21 Lemma 5.8's own term II (L1076, `−χ_∞/(επiα)`), and contradicts Lemma 7.3's
`+` (L1737). **F61 is confirmed independently.** `specialWeight` is now
`∏(−ζ_zπi)^{-1} = ∏(−1)/(ζ_zπi)`; the probes `P1` and `P3` give `i/π` for `ζ = +` and `1/(πi)` for `ζ = −`.

**Sign conventions in the Lean definitions.**
- DH21 (res) (L428) and (defintegral) (L1667) use `Ω_𝔫 = Ω(k_{𝔫1},k_{𝔫2},k_{𝔫3},k_𝔫)`. (newsum1) (L1674) uses
  `2⟨x_𝔫,y_𝔫⟩` with `x = k_{𝔫1}−k_𝔫` and `y = k_𝔫−k_{𝔫3}`, which is the same quantity.
- B2's `pvResonantIntegral` and `resIntegral` use `k₁ = k+ℓ`, `k₃ = k+x`, `k₂ = k+ℓ+x`. So
  `Ω = −2⟨ℓ,x⟩ = |k₁|²−|k₂|²+|k₃|²−|k|²`, the same quantity, and the p.v. body has the right sign (F-5 checks it).
- In `RegChain.Nstar`, `(k₁,k₂,k₃)` are the children of `𝔫_a` and `k` is the chain momentum, so `Ω` is `Ω_{𝔫_a}`.
- `Z ⊆ 𝒩^ch` holds the chosen node `𝔫_a`, which is the parent, and its sign is `nodeSign σ z`.
- In a dominant chain, every `𝔫_{2j−1}` has the root's sign, because `c = M ⟺ lone = M`.
- So `RegCpl.app` (σ = (+,−)) and `RegChain.app` (σ = (ζ)) both match the corrected (regref1-3) (T L1154).
- The prefactor checks out: each pair gives `(δ/2)²L^{-2(d−γ)}·L^{2d}·λ^{-1} = δ/4`, hence `2^{-2n}δ^n`.

**CL-11 auditor question 3.** No other B2 object carries `(ζπi)^{-1}`: `grep` finds `π`/`I` only in `zetaOfTrees`
and `specialWeight`.

## Item 4. Closure, `deriving`, `sorry`

- **Closure** (`Closure.lean`). I followed all 394 non-theorem declarations of the three modules through types,
  bodies, auxiliary proofs and matchers.
  - Exactly 19 "uses" of project theorems were found. All are **structure-field projections**:
    - `Garden.pair_pair`, `pair_eq_iff`, `pair_sign`, used by `Garden.molecule`;
    - `Molecule.atom_mem`, `mate_mate`, `mate_ne`, `out_mate`, used by `eraseBond`, `cut`, `IsAlphaCut` and
      `IsHyperBlock`.
  - The policy counts projections as part of their structure. **0 genuine violations**; this confirms CL-12.
  - The non-frozen B1 module `WaveBDraft.Lemmas` is no longer in the import closure.
- **`deriving`.** None; the word appears only in comments.
- **`sorry`** (`P3`).
  - `sorryAx` occurs in no non-theorem declaration (0 of 394).
  - It occurs in exactly 10 theorems:
    - Regular §4 (6);
    - `Garden.isMolecule_molecule`;
    - B2.1–B2.3.
- **Axioms** of the key definitions (`P0`): `[propext, Classical.choice, Quot.sound]`.
- **Remaining packaging gap.** The anonymous instances (F-6).

## Item 5. Stage-1 OPTIONAL items O1–O6: needed before the freeze?

| Item | Decision |
|---|---|
| O1 (p.v. characterization for decaying kernels) | **Needed: REQUIRED (F-5)**, either the extended characterization or an author ruling that the slice form is the definition. |
| O2 (probes P1–P3 for non-trivial codes) | Not needed. REG-STRUCT's proofs of `existsUnique_regCpl_decodes` and `size_eq_order` on these exact definitions (elaborated-constant identity, REG-STRUCT S5) validate decoding far more strongly. Copying the probes is still good practice. |
| O3 (F16 link property as an obligation) | Not needed. `links` is the literal inductive rule of T `deflink` (L874–L882); the identities are proof inputs, not definitional content. OPTIONAL. |
| O4 (the equivalence `∼` of enhanced objects) | Not needed. No frozen statement quantifies over classes: item 4 sums over codes, and (regref2-3)/(regref3) are proof steps. It will be needed when those are stated. |
| O5 (document junk values) | OPTIONAL: docstrings only. |
| O6 (perfect matching / carrier uniqueness) | Not needed for freezing. REG-STRUCT proves `carrier_unique`, and `existsUnique` is about codes. A one-line obligation would pin `Decodes` inside the freeze set, which is nice to have. |

## Item 6. Further checks

**Five-bin tables (binders expanded).**

*B2.1 `regularAsymptotics`:*

| Binder | Bin | Citation |
|---|---|---|
| `WTPrefix` (Π) | STANDING | B1 snapshot 6 (audited) |
| `p < P.D` | SOURCE | T L823, L951 |
| `r ≤ p` | SOURCE | T L1145 |
| `R : Mom → ℝ` | SOURCE | T L951 ("defined for all `k`, real valued") |
| `InputRemainder P R r` | SOURCE + RULED | T L951, (ansatz2) with `40d`; D5 / O3 ruling |
| `n ≤ N_{p+1}^4` | SOURCE | T L951; D6 / F33 |
| (1) `Q`, `wf`, `size = 2n` | TYPING | D4: code = unique structure data, `existsUnique_regCpl_decodes` |
| (1) `LG`, `Decodes` | SOURCE | layered regular couple, T L1145 |
| (1) `layer = r` | SOURCE | T L1145 |
| (2) `X`, `wf`, `size`, `LG`, `DecodesTree` | TYPING / SOURCE | as above |
| (2) `q' ≤ r`, layer condition | SOURCE | Def `defkg` L682; T L1145 |
| (3) `Q`, `X` dominant; `ζ`; `q'`; `Z ∈ specialSets` | SOURCE | (regref1-4), "for any `𝒬`, `𝒯`"; Def `defencpl` |
| (4) `r = p`, `R = 0`, `t ∈ [p,p+1]`, `k` | SOURCE | (regref1-5) corrected by F11 |

Counts: SOURCE 11, STANDING 1, TYPING 2, RULED 1 (inside row 5), **EXCESS 0**. The binders are fine; the defect is
in a definition (F-1).

*B2.2 `incoherentDecay`:*

| Binder | Bin | Citation |
|---|---|---|
| Π, `p < D`, `R q` with `∀ q ≤ p` `InputRemainder`, `n ≤ N^4` | STANDING / SOURCE | T L951 |
| couples: `Q`, `wf`, `size`, `LG`, `Decodes` | TYPING / SOURCE | |
| couples: layers `≤ p`, `q, q' ≤ p`, root layers `≤ q, q'`, `g ≥ 1` | SOURCE | Def `defkg` L677–L681; `proplayer1` L953 |
| trees: the same, with root `≤ q`, lone leaf `= q'`, `q' ≤ q ≤ p` | SOURCE | T L682 |

**EXCESS 0.** Deviation D1 (arbitrary layerings when `g ≥ 1`) matches T L951, which restricts layerings only when
`g = 0`.

*B2.3 `rigidity`:*

| Binder | Bin |
|---|---|
| `V`, `D` and their instances | TYPING |
| `M`, `lab`, `w`, `prevGaps`, `Pl`, `Adm` | design-item data |
| `1 ≤ Rw` | SOURCE |
| `FinalShape` | **EXCESS-pending-RULING** |
| `DecorationHyp` | **EXCESS-pending-RULING** |

B2.3 fails the five-bin test until the Q7 ruling (F-4), and even then R1 and R2 must be fixed first (F-2, F-3).

*Obligations.*
- Regular §4: binders minimal (REG-STRUCT S1–S3 PASS; I spot-checked the five bins: 0 EXCESS).
- `regular_count_le`: no binders.
- `isMolecule_molecule`: SOURCE hypotheses, superfluous (F-7).

**Definition verdicts.**

`specialWeight`, `RegCpl.app`, `RegChain.app` (given a correct `JBtree`):
```
BODY_MATCH: OK          PUBLIC_CARRIER: OK
WELL_DEFINEDNESS: N/A_LITERAL    CHARACTERIZATION: N/A_LITERAL
CHOICE_INDEPENDENCE: N/A         DEFINITION_VERDICT: PASS (RegChain.app inherits F-1)
```

`RegChain.JBtree`:
```
BODY_MATCH: FAIL (lower limit s; source needs max(s,r) on the B2.1 box)
PUBLIC_CARRIER: OK   WELL_DEFINEDNESS: N/A_LITERAL   CHARACTERIZATION: N/A_LITERAL
CHOICE_INDEPENDENCE: N/A   DEFINITION_VERDICT: FAIL
```

`pvResonantIntegral`:
```
BODY_MATCH: OK (formula, sign)   PUBLIC_CARRIER: OK
WELL_DEFINEDNESS: N/A            CHARACTERIZATION: FAIL on the real carrier (compact support only; F-5)
CHOICE_INDEPENDENCE: N/A         DEFINITION_VERDICT: FAIL until F-5
```

`IsLadder`, `IsBlock`, `GroupConnected`, `eraseBond`, `IsHyperBlock`, `IsDeviation`, `GNode.parent`, `Garden.molecule`:
```
BODY_MATCH: OK   PUBLIC_CARRIER: OK   WELL_DEFINEDNESS: N/A_LITERAL   CHARACTERIZATION: N/A_LITERAL
CHOICE_INDEPENDENCE: N/A   DEFINITION_VERDICT: PASS
```

**Scope of big operators (F56 sweep).** Every `∑`, `∏` and `∫` in the freeze files bounds what it should:
- `zetaOfTrees`, `specialWeight`, the `Z` sum in both `app`s, `countA`'s ladder product (`^` binds inside, which is
  the intended `∏𝔛_j^{z_j}`);
- `rigidityRHS` (parenthesized), the `IsDecoration` sum (ends before `=`), `Gamma`;
- the integrals in `JB` and `JBchain`, `resIntegral`, `pvResonantIntegral`, `Nstar`;
- B2.1 item (4)'s `∑ᶠ` (P0).

No scope error.

**Off-by-one ranges and carriers.** All correct:
- `P.N (p+1) ^ 4`;
- `timeBox q q'` = `Icc q (q+1)`;
- `Fin (m+1)` with `1 ≤ m`;
- `ladderLength = |S|/2 − 1 = m`;
- `Q.size / 2 = n`;
- `2 * m` in the count;
- `ℤˣ` casts in the weight;
- the `ℝ≥0∞` deviation cases.

**Degenerate cases.** All hold:
- `n = 0`: `app_triv = F`, while `K*_{(•,•)} = F(k)` and `K*_• = app_nil = 1`; item 4 gives `F = 𝒰₀`;
- B2.2 with `n = 0` is vacuous, since `g ≥ 1` is impossible;
- `m = 0` in the count: 1 couple, and 1 tree per sign;
- empty `Z`: weight 1.

**Non-vacuity.** I re-elaborated the snapshot's Statements probes (P4); they hold. Note: item (2)'s non-vacuity
instance (`r = 1`, `q' = 0`) is exactly the F-1 counterexample.

**Stage-2/3 O3 (`k⁰` real rather than in `ℤ_L^d`), still open.** `countE` can only be marginally larger than T's `𝔈`,
which makes B2.3's conclusion slightly stronger. It is OPTIONAL now and should be revisited with F-2/F-3, since B2.3
is not in this freeze.

## Summary of BLOCKER and REQUIRED items

1. **F-1 BLOCKER.** `RegChain.JBtree` uses lower limit `s`, so B2.1 item (2) and the tree half of item (3) are false
   for `q' < r` (kernel-checked reduction on `miniTree10LG`). Fix: `X.JBchain r (max s r) t fun _ => 1`.
2. **F-2 BLOCKER (B2.3).** R1 (self-loop dart pairs in `DecorationHyp` and `IsCutData`) is still open. Fix: add
   `x₂ ≠ M.mate x₁`.
3. **F-3 BLOCKER (B2.3).** R2 (ZG-tame ε-atoms) is still open. Fix: transcribe "tame" and weaken `epsLG` (G8).
4. **F-4 BLOCKER (B2.3).** There is no author ruling on the abstract hypotheses (Q7). Keep B2.3 out of this freeze.
5. **F-5 REQUIRED.** The `pvResonantIntegral` characterization covers only compactly supported kernels. Extend it, or
   get a ruling.
6. **F-6 REQUIRED.** Ten anonymous instances need B1-style names, and B2 needs a generated freeze list.

---

## Re-check, 2026-11-04 (delta audit of B2-CL-13 to B2-CL-17; snap-3)

### Verdict for freezing Regular + Molecules + Statements without B2.3: PASS WITH REQUIRED FIXES

No BLOCKER remains in this scope. One REQUIRED item is still open: **F-5**. Its lemma statement is correct, but it is
not yet proved. B2.3 correctly stays out of the freeze: F-4, the missing author ruling on the abstract hypotheses,
is still open.

### Inputs

**Snapshot.** I copied the current `/home/scott/wt-scratch/waveb2` into `/home/scott/wt-scratch/b2-audit/snap-3/` at
2026-11-04 03:13 UTC and recorded its `SHA256SUMS`:
- `WaveB2-Regular.lean` `ce8f0a1652ba…`;
- `WaveB2-Molecules.lean` `89ff648ed5a3…`;
- `WaveB2-Statements.lean` `82e42b2bfa16…`;
- `WaveB2-Regular-probes.lean` `93b4f0bf808f…`;
- `WaveB2-Statements-probes.lean` `16099cbd4f31…`;
- `FREEZE-LIST.md` `349020959462…`;
- `FreezeList.lean` `cba281b7a004…`.

**Build match.** These are byte-identical to the sources in `waveb2/src/WaveB2Draft/`, which were built into
`waveb2/build` at 03:02–03:03 UTC.

**Change list.** Handoff addendum 2 (`w/orch` 9e10307).

**Probes.** I ran them in the dev environment: `cd /home/scott/WaveTurbulence-dev && nice -n 5 lake env …`, with
`LEAN_PATH` plus `waveb/build:waveb2/build`, one Lean process at a time.
- `Q0.lean`: the elaborated `RegChain.JBtree`.
- `Q1.lean`: the F-1 re-check.
- `Q2.lean`: closure, instances, held-out use, `sorry` sweep.
- `Q3.lean`: the F-5 statement and the relayering lemma.

All probes use standard axioms; the only `sorry` is the transient F-5 statement in `Q3`.

**Diff against snap-2.**
- B2.1 and B2.2 statement texts: **unchanged**, checked by diff.
- Regular changes only in `JBtree` (CL-13) and the ten instance headers (CL-16).
- Molecules changes only in the two instance headers, `isMolecule_molecule` (CL-17) and `IsCutData` (CL-14).
- Statements changes only in the B2.3 section: `IsTame`, `DecorationHyp` and `rigidity`.

### Per change

| CL | Verdict | Evidence |
|---|---|---|
| CL-13 (F-1) | **RESOLVED** | `JBtree r X t s = X.JBchain r (max s r) t (fun _ => 1)` (Q0). See the next section. |
| CL-14 (F-2) | **RESOLVED (B2.3 draft)** | `x₂ ≠ M.mate x₁` appears in `epsLGTame`, `alphaGap`, `iota`, `abNonzero` and `IsCutData` (T `defdiff` L1938–L1941, `defcut` L2118: two bonds). See question 2. |
| CL-15 (F-3) | **Faithful as a draft (B2.3, held out)** | `IsTame` transcribes T `subpro` (3) (L2044) exactly. See question 3. |
| CL-16 (F-6) | **RESOLVED** | Q2 and the freeze list agree. See question 4. |
| CL-17 (F-7) | **CORRECT** | `Garden.isMolecule_molecule (G : Garden w) : G.molecule.IsMolecule`. It holds for every garden (audit F-7 argument; MOLE `garden_isMolecule`). The F58 warning is kept. It is strictly stronger and has no consumer. |
| F-9 | **RESOLVED** | Handoff §2, DESIGN §1.5 and the `sorry` inventory (10) are updated. |

**Question 2 (CL-14): is the exclusion needed anywhere else?** No.
- `IsBlockGap` is used only through `IsVine`, which is a connected `IsBlock`. A connected block cannot carry a loop at
  a joint (audit F-2 / CL-5), so its two group darts at `j₁` lie on different bonds.
- `IsLadderGap`'s darts have `ends = s(u 0, u 1)` and `s(v 0, v 1)` with `u 0 ≠ u 1`, so they are not loops and lie
  on different bonds.
- `vineLG` goes through `IsBlockGap`.

**Question 3 (CL-15): is the `kFix` abstraction faithful?**
- "LG or tame" is the right per-atom reading of `finalmol`'s "LG or ZG, and tame if ZG": ZG at one triple implies
  tame, and tame forces all triples ZG.
- `kFix` with `card ≤ 2R`, universally quantified, generalizes the root momenta `(k₁,…,k_{2R})` correctly. The
  consumer takes `kFix := {k₁,…,k_{2R}}`.
- Whether DH23 §10.5 needs anything beyond "fixed" is G8's question.

**Question 4 (CL-16).** Q2 checks:
- 12 named `@[instance_reducible, instance] def` instances, all `instanceReducible`; the other 8 registered
  instances are auto-generated `_sizeOf_inst`;
- no `instance` keyword left in the three files;
- closure: the only project theorems used are the 7 structure-field projections (`Garden.pair_*`, `Molecule.*`),
  0 others;
- no listed declaration uses any of the 13 held-out B2.3 declarations;
- `sorryAx` occurs in no definition, and in exactly 10 theorems (9 in scope, plus `rigidity`).

`FREEZE-LIST.md` has 152 rows (9 theorems, 119 definitions, 3 abbrevs, 3 structures, 6 inductives, 12 instances),
which matches its header. The scope "Statements minus the B2.3 section" is the right one. The instance names are
Lean's former auto-names, consistent with B1, and can be final.

### B2.1 items (2) and (3) for trees, re-derived with the lower limit `max(s, r)`

- **`q' = r`.** On the box `s ≥ r`, so `max(s,r) = s`: this is (regref2-2) exactly (T L1185–L1188). Unchanged.
- **`q' < r`.** On the box `s ≤ q'+1 ≤ r`.
  - **Q1 proves, in general,** `KTstar(t,s) − app(t,s) = KTstar(t,r) − app(t,r)` (`B2Audit.item2_integrand_of_le`). It
    holds for every layered paired tree whose branching nodes all lie in layer `r`, every code `X` and every `s ≤ r`.
  - So item (2) on the `q' < r` box reduces to the slice `s = r`. That slice lies in the `q' = r` box, which is the
    source's regref1 claim.
  - **On the project's own instance `miniTree10LG`** (`r = 1`, `q' = 0`), `B2Audit.miniTree10_item2_const` proves
    that `K*_𝒯 − app` is constant in `s` on the item-(2) box. The slope `c(k)` of `P5.chain10_app_diff` is gone, so
    `P5` no longer refutes.
  - `Q3.KTstar_relayer` (standard axioms) adds that `K*_𝒯` with input family `fun _ => F` depends on the layering only
    through the branching nodes, so the lone leaf's layer does not enter. This covers TARGET's consumer case
    (prooflayer1-2) (L1243). There `K*_{𝒯_[r]}(r+1, r, k)` is evaluated with `s = r`, while the lone leaf may lie in
    layer `≤ r − 2`, outside `[q', q'+1]`.
  - These helpers (`KTstar_indep_of_le`, `item2_integrand_of_le`, `KTstar_relayer`) are worth landing for the
    proplayer2 packet (OPTIONAL).
- **Item (3), trees.**
  - On the `q' < r` box, `JBtree(t,s) = JBtree(t,r)` (the probe `JBtree_of_le`) is a bounded function of
    `t ∈ [r, r+1]`.
  - For the mini-tree it equals `t − 1 ∈ [0,1]` on `[1,2]×[0,1]` (Q1 `example`). The `≥ D − 1` growth is gone.
- **Conclusion.** Items (1)–(4) of B2.1 now say what T (regref1)–(regref3) (with F11 and F61) say, as far as the
  source proofs show.

### F-5: the decaying-kernel lemma statement

**Elaboration (Q3).** The drafter's `tendsto_pvResonantIntegral_of_decay` elaborates verbatim against the dev
Foundations. Its conclusion is `Tendsto (fun μ => energyInvIntegral χ μ (resonantKernel Ψ k)) atTop
(𝓝 (pvResonantIntegral Ψ k))`.
- `energyInvIntegral χ μ (resonantKernel Ψ k)` is **by `rfl`** the integral
  `∫_ℓ ∫_x Ψ(k+ℓ, k+ℓ+x, k+x)·(1 − χ(μΩ))/Ω` with `Ω = −2⟨ℓ,x⟩ = |k₁|²−|k₂|²+|k₃|²−|k|²`.
- `IsPVCutoff` requires `χ` continuous, even, compactly supported and `= 1` near 0, so `1 − χ = χ_∞`.
- So the lemma is exactly the Cauchy principal value of T (regref3-3) / DH21 (defintegral), in DH21's own cutoff
  form `χ_∞(δL²Ω)/Ω`, with a cutoff-independent limit.
- It implies the landed `tendsto_pvResonantIntegral`; the Q3 `example` drops `hR` and `hs`.

**Does it cover B2's kernels?** The `Nstar` kernels are `Ψ = M_r(k_x)·M_g(k_y)` with `|M|, |∇M| ≲ ⟨k⟩^{-a}`. The
bound `a = 30d` comes from B2.1 item (3) (`𝔖^{30d,·}`).
- Placement `(k₁,k₂)`: `A(ℓ) = C⟨k+ℓ⟩^{-a}`, `b = k+ℓ`.
- Placement `(k₁,k₃)`: `A(ℓ) = C⟨k+ℓ⟩^{-a}`, `b = k`.
- Placement `(k₂,k₃)`: by Peetre, `⟨k+x⟩^{-a}⟨k+ℓ+x⟩^{-a} ≤ C⟨ℓ⟩^{-a/2}⟨k+x⟩^{-a/2}`, so
  `A = C⟨ℓ⟩^{-a/2}`, `b = k`, `N = a/2`.

In every case `N > d` and `∫|ℓ|^{-1}A < ∞` (since `a/2 > d − 1`), so they are `DeltaKernel`s, and the gradients
likewise. The lemma therefore makes the characterization cover the decaying kernels B2 uses. The drafter's proof
sketch is sound:
- per slice, `pvQuotient(sliceInt)` is integrable: near 0 by the derivative bound (`M > d − 1`), for `|t| ≥ 1` by
  hyperplane decay (`N > d`);
- the outer domination is `|ℓ|^{-1}(A + B)`.

**Status: the statement is CORRECT. F-5 stays REQUIRED until the lemma is proved `sorry`-free with standard
axioms** and cited in `pvResonantIntegral`'s docstring. The alternative is author ruling F-5 (b). Discharging its
hypotheses for B2's kernels is a proof obligation of B2.1's provers, not a freeze item.

### Remaining items

- **REQUIRED: F-5.** Prove `tendsto_pvResonantIntegral_of_decay`, or obtain the author ruling.
- **OPTIONAL: freeze scope.** 63 listed declarations are consumed by no listed theorem. Most of them (`countA`,
  `countE`, `IsLadder`, `maximalLadders`, `IsBlock`, `IsVine`, `cut`, `IsCutData`, `AtomLabel`, …) are used only by
  the held-out B2.3, which is still being drafted: CL-14 already changed `IsCutData`. Freezing them now means any
  G8 change needs a versioned successor. With the small-frozen-surface policy, consider holding out the
  B2.3-only machinery with B2.3. This is a scope decision, not a defect.
- **OPTIONAL: helpers.** Land `KTstar_indep_of_le`, `item2_integrand_of_le` and `KTstar_relayer` (`Q1`, `Q3`) for the
  consumers.
- **B2.3 (out of scope).** F-2 and F-3 are addressed in the draft; F-4 (author ruling on Q7) is still open.

---

## Re-check 2, 2026-11-04 (CL-18 to CL-21; the final candidate `waveb2-snap-final`)

### Verdict: PASS — freeze the 59 declarations (B2.1, B2.2 and their closure)

There is no BLOCKER. There is one REQUIRED item, R2-1. It concerns the order of steps before B2.1 and B2.2 can be
sealed or counted source-faithful. It does not change any frozen text.

### Inputs

- **Snapshot.** `/home/scott/wt-scratch/waveb2-snap-final`. `sha256sum SHA256SUMS` = `d6dc5f2dd28e432a…`, the digest
  the coordinator stated. All 12 files verify. My copy is in `b2-audit/snap-final/`.
- **Build match.** The three freeze files, the probes and Ladders are byte-identical to `waveb2/src/WaveB2Draft/*`,
  which were built at 06:18–06:19 UTC.
- **Change list.** Handoff addenda 3–6; main `9a2a4da`.
- **Probes.** Run in the dev environment, one Lean process at a time, `nice -n 5`:
  - `Q4.lean`: the F-5 wrapper and its axioms;
  - `Q5.lean` with output `Q5.out`: the closure of B2.1/B2.2;
  - `Q6.lean`: a shared auxiliary proof;
  - `Q7.lean`: the vine (II) template;
  - a from-source compile of `Foundations/Resonant/PVDecay{Bounds,OneDim,Slices,}.lean`.
- **Diff against my snap-3.**
  - `WaveB2-Statements.lean` is unchanged (`82e42b2b…`), so B2.1 and B2.2 are unchanged.
  - `WaveB2-Regular.lean` changed only in the docstring of `pvResonantIntegral` (CL-19).
  - `WaveB2-Molecules.lean` changed only in `VineType.template .II` and in docstrings (CL-21).

### (1) F-5 proof: CLOSED

- **The wrapper is the exact statement.** `WaveBProbes.tendsto_pvResonantIntegral_of_decay`
  (`WaveB2-Regular-probes.lean` L295–304) is character-for-character the statement I elaborated in the first
  re-check (`Q3`). In `Q4`, an `example` with that exact type is closed by the export.
- **Proof and axioms.** The proof is `rw [pvResonantIntegral_eq_energyInv]` followed by the landed
  `Resonant.tendsto_energyInvIntegral_of_decay` (`Foundations/Resonant/PVDecay.lean` L62, commit `613a63a` on main).
  The axioms are:
  - the wrapper: `[propext, Classical.choice, Quot.sound]`;
  - `tendsto_energyInvIntegral_of_decay`: `[propext, Classical.choice, Quot.sound]`;
  - the bridge `pvResonantIntegral_eq_energyInv`: `[propext, Classical.choice, Quot.sound]`.
- **The sources are clean.**
  - The four `PVDecay*.lean` files contain no `sorry`, `admit`, `axiom`, `native_decide` or `implemented_by`.
  - They are clean in git.
  - They recompile from source in the dev environment with **no warnings**.
- **Docstring.** `pvResonantIntegral` now cites the lemma and its landed source.

### (2) The 59-declaration freeze set is exactly the closure of B2.1 and B2.2

- **Exact closure.** `Q5` computes the B2 declarations reachable from the types of `regularAsymptotics` and
  `incoherentDecay`. It follows types, bodies, constructors and auxiliary proofs and matchers, and folds auxiliary
  constants into their owners.
- **Set equality.** Compared with `FREEZE-LIST.md`'s 59 rows, the sets are equal up to three artifacts of my
  folding:
  - `RegCpl.brecOn.go` and `RegChain.brecOn.go` belong to the inductives `RegCpl` and `RegChain`.
  - `Garden.MatchesTreeCouple` is reached only through the **shared** auxiliary proof
    `Garden.MatchesTreeCouple._proof_1 : NeZero (0 + 1)`. That is the literal `(0 : Fin 1)`, which Lean shares among
    `RegChain.DecodesTree`, `treeLinks`, `app` and `MatchesPairedTree` (`Q6`). It is not a semantic dependence.
    B1's generator correctly expands shared auxiliaries instead of attributing them.
  - If the frozen declarations move to one-per-file modules, Lean regenerates the auxiliary proof, so nothing breaks.
- **Composition.**
  - 53 declarations from Regular, 6 from Statements and none from Molecules: B2.1 and B2.2 do not reach the molecule
    layer.
  - The 59 contain the single instance `instDecidableIsSpecialSet`.
  - The 59 match the `FREEZE-LIST.md` kinds: 2 theorems, 51 definitions, 2 abbrevs, 1 structure, 2 inductives,
    1 instance.
- **Closed, and no dependence on proved theorems.** The traversal reached **no** project theorem other than
  structure projections and auxiliary constants. No frozen declaration uses a held-out one (generator check; also
  implied by the closure computation).
- **Dropping the seven obligations.**
  - **Nothing in the anchors' statements, closure or (future) proofs requires them to be frozen.** Their types do
    not mention any of them, and a proof may use any proved lemma.
  - `regular_count_le` (O6) and `Garden.isMolecule_molecule` (O7) play no role in B2.1 or B2.2.
  - **Fidelity, however, does depend on five of them** (reading D4, already noted in addendum 5). B2.1 and B2.2
    quantify over well-formed codes and the carriers they decode. They say "every layered regular couple or tree of
    order `2n`" only if:
    - O1 `RegCpl.exists_decodes` and O3 `RegChain.exists_decodesTree` hold. Otherwise items (1) and (2) would also
      quantify over non-regular carriers, which is a claim beyond the source.
    - O2 `existsUnique_regCpl_decodes` and O4 `existsUnique_regChain_decodesTree` hold. Otherwise some regular
      objects would be missed.
    - O5 `RegCpl.size_eq_order` holds (order `2n` equals code size `2n`).
    - Item (4)'s sum over codes equals T's sum over dominant couples only through the bijection O1 + O2 + O5.
  - O2 and O5 are proved in scratch; **O1, O3 and O4 are open.** See R2-1.

### (3) CL-21, vine (II) from one rung: CORRECT, and it does not reach B2.1 or B2.2

- **Source.**
  - DH23 Step 2 (L1421) describes vine (II) as joints `v₁, v₂` with `2m` further atoms `v_{2j+1} = v_{2j+2}`, which
    are `m` double bonds.
  - L1481 says "`m ≥ 1` for vines (II)".
  - F72 extends B2's reading to `m = 1`.
- **New template** (`Q7 #print`): `⟨4, [(0,2),(0,3),(2,3),(2,3),(2,1),(3,1)], [((2,1),(3,1))], [[2,3]]⟩`.
  - It is the Q-block `J₁ – (a = b) – J₂`: the joints have degree 2 and the interior atoms degree 4.
  - Its slot is the rail pair `a⋯J₂`, `b⋯J₂`. Both slot bonds occur verbatim in the bond list, so
    `insertRungs`' `erase` removes them.
  - So `expand [k]` is `J₁ – (a=b) – (u₁=v₁) – ⋯ – (u_k=v_k) – J₂`: the ladder with `m = k + 1` rungs and its last
    rails at `J₂`.
  - Each rung is a group. The family is exactly DH23's `m ≥ 1`, in which the old `m ≥ 2` family appears as `k ≥ 1`.
- **Checks.**
  - My `Q7` examples (by `decide`): `expand [1]` has 6 atoms and 10 bonds (the old drawing), and both joints keep
    degree 2 for `k ≤ 3`.
  - The drafter's probes `vineII_card`, `vineII_sizes`, `vineII_family_shift` and `qBlock_vine` all use standard
    axioms or fewer. `qBlock` is a genuine molecule: the rung is antiparallel and the joint bonds are opposite.
- **Reach.** `Q5`'s closure of B2.1/B2.2 contains no declaration from Molecules. It reaches neither `VineType` nor
  `IsVine`.
  - The change reaches only held-out declarations: `expand`, `IsVine`, `DecorationHyp.vineLG` and B2.3.
  - This matches addendum 6's normalized dump: exactly one constant differs.
- **For packet G8 when B2.3 returns.** `vineLG` now also covers Q-block components. F72 section E says this is the
  source's own claim (a generic proof of DH23 Prop 9.5).

### (4) The review page's Lean matches the pinned files exactly

`docs/review/WAVE-B-B2.md` (main, last changed in `6ba59f6`):
- **Lean blocks.** It has two `lean` blocks: Regular (499 lines) and Statements (149 lines).
  - Split at its `-- [held out, not frozen: …]` markers (9 and 1), every segment is a **verbatim substring of the
    pinned file, in order**.
  - Each gap between segments contains exactly the declarations its marker names.
  - The declarations shown are **exactly the 59 frozen ones**: none missing, none extra.
- **Header hashes.** All match the snapshot:
  - Regular `4d7f81efa32b…`;
  - Molecules `5cc506118852…`;
  - Statements `82e42b2bfa16…`;
  - `FREEZE-LIST.md` `8967e57cfa83…` (also equal to `docs/review/WAVE-B-B2-FREEZE-LIST.md`);
  - `SHA256SUMS` `d6dc5f2dd28e…`.

### Remaining items

- **R2-1 REQUIRED (before B2.1 and B2.2 are sealed or reported as faithful to T, not before freezing the text).**
  1. Prove O1 `RegCpl.exists_decodes`, O3 `RegChain.exists_decodesTree` and O4 `existsUnique_regChain_decodesTree`
     in their present exact statements.
  2. Record in the freeze manifest, by hash, the statements of O1–O5 and of the 15 source-form definitions they rely
     on (`IsRegularCouple`, `IsRegularTree`, `RawRegular`, `RawCpl.*`, `Garden.MatchesTreeCouple`,
     `TTree.setAt`/`subtreeAt`, …) as **fidelity obligations of D4**.

  Editing these non-frozen lemmas or definitions can then not silently change what the frozen anchors mean.
  REG-STRUCT's order-≤ 6 diagnostics (no collisions; source range = code range) make failure unlikely.
- **OPTIONAL.** The F72 follow-ups outside B2: re-run VINES, MOLEPROP13 and `vinefree.py` with `m = 1` (addendum 6).

---

## Re-check 3, 2026-11-04 (CL-22: O1–O5 are anchors again; seal providers)

### Verdict: PASS

The 76-declaration freeze set (7 anchors) is exact and closed. The providers prove exactly O1–O5 on the snapshot's
definitions, with standard axioms; I rebuilt every module independently. The review page shows all 76 declarations
verbatim. **R2-1 is resolved.** There is no BLOCKER and no REQUIRED item.

### Inputs

- **Snapshot.** `/home/scott/wt-scratch/waveb2-snap-final`. `sha256sum SHA256SUMS` = `b605320f7676…`; all 22 entries
  verify. My copy is in `b2-audit/snap-final3/`.
- **Diff against re-check 2.** The Lean sources are byte-identical. The changes are `FREEZE-LIST.md`,
  `gen_freeze.py`, `DESIGN.md`, `README.md` and the new `providers/`.
- **Change list.** Handoff addendum 7: main `ad7cd70`. The orch worktree is the same.

### (1) The freeze set is the closure of B2.1, B2.2 and O1–O5

- **`Q8.lean`** (the Q5 traversal with seven roots, anchor types only; output `Q8.out`) reaches 78 owners. They are
  exactly the 76 rows of `FREEZE-LIST.md` plus the two recursion auxiliaries `RegCpl.brecOn.go` and
  `RegChain.brecOn.go`, which belong to their inductives.
- **No project theorem is reached** (`non-projection project theorems reached: #[]`).
- **Against the CL-20 set of 59, exactly 17 declarations were added:**
  - the 5 theorems O1–O5;
  - 12 definitions: `IsRegularCouple`, `IsRegularTree`, `RawRegular`, `RawCpl.{tree, mapTree, opA, relocate,
    orient, opB}`, `Garden.MatchesTreeCouple` (now genuinely reached, through `IsRegularTree`), `TTree.setAt` and
    `TTree.subtreeAt`.
- **The ruling's "15" is 12, as addendum 7 says.** `GNode.parent`, `GardenDart` and `Garden.molecule` are reached
  only by O7 and correctly stay out.
- **Counts.** 7 theorems, 62 definitions, 2 abbrevs, 1 structure, 3 inductives (`RegCpl`, `RegChain`,
  `RawRegular`), 1 instance (`instDecidableIsSpecialSet`). Regular 70, Statements 6, Molecules 0.
- **Fidelity.** These five anchors are exactly R2-1's fidelity obligations of reading D4, and the source-form
  definitions their statements use are now frozen with them. R2-1 is therefore resolved: the meaning of B2.1 and
  B2.2 no longer rests on editable declarations.

### (2) The providers prove exactly O1–O5

**Independent rebuild** (`b2-audit/regbuild/`, my own script `build.sh`, log `build.log`).
- Sources:
  - the 154 REG-STRUCT modules, each copied from `/home/scott/wt-scratch/reg-struct`. All 154 match
    `providers/REGSTRUCT-SHA256SUMS` and contain no `sorry`, `admit`, `axiom`, `native_decide`, `implemented_by` or
    `extern`;
  - `WaveBDraft.{Core, System}` from snapshot 6/7 (`0b8477d9…`, `59365906…`);
  - the snapshot's `WaveB2-Regular.lean` as `WaveB2Draft.Regular` (`4d7f81ef…`);
  - the shim `RegularDefs-shim.lean` as `WaveB2Draft.RegularDefs`. It contains only `public import WaveB2Draft.Regular`;
  - the five provider files, byte-for-byte.
- The build ran on dev's Mathlib and Wave A, in topological order, one `lean` at a time, `nice -n 5`, **with no other
  B1/B2 build on the path**.
- **Result: all 161 modules, 0 errors, in 1209 s.** The only warnings are the six `declaration uses 'sorry'` of
  Regular §4 itself (L373–L407).

**Seal check** (`Q9.lean`, my own, run on this build).
- Each anchor statement, copied from §4, is closed by the bare `by exact WaveTurbulence.Provider.<export>`.
- For all five: **`(seal).type == (§4 anchor).type`** (Expr equality).
- The provider types, with `autoParam` wrappers and binder annotations stripped, are `==` to the anchor types. The
  only differences are the B1 `wkelwp` pattern: implicit data binders and `by assumption` autoParams, in the same
  binder order.
- Axioms of all five seals: `[propext, Classical.choice, Quot.sound]`. There is no `sorryAx`, although the
  `sorry`'d §4 constants are in the same environment.

### (3) The review page shows all 76 verbatim

`docs/review/WAVE-B-B2.md` (main `ad7cd70`; identical in the orch worktree, `8f2f476d…`):
- **Lean blocks.** It has two `lean` blocks: Regular (600 lines, 7 held-out markers) and Statements (149 lines, 1
  marker).
  - Every segment between markers is a verbatim substring of the pinned file, in order.
  - Every marker's names are exactly the declarations in its gap.
  - The declarations shown are **exactly the 76** of `FREEZE-LIST.md`: none missing, none extra.
- **Header hashes** match the snapshot:
  - Regular `4d7f81ef…`;
  - Molecules `5cc50611…`;
  - Statements `82e42b2b…`;
  - `FREEZE-LIST.md` `61f1be74…`, also equal to `WAVE-B-B2-FREEZE-LIST.md`;
  - `SHA256SUMS` `b605320f7676…`.

### Remaining

**OPTIONAL: stale wording.** The page's L8 still says "the two theorems with body `by sorry`, as `DRAFT_SORRY`
anchors". It should say: seven theorem anchors; B2.1 and B2.2 `DRAFT_SORRY`; O1–O5 sealed on landing by their
providers.

---

## Norm measurability, 2026-11-04 (B1 snapshot 8 norms; B2 final)

### Verdict

**No frozen statement is false.** But **B2.1 items (1)–(2) and B2.2 are stated in a norm that is not TARGET's
`𝔛^{θ,Λ₁,Λ₂}(ℬ)` at `Λ₁ = 30d`.**
- The B1 definitions `XNorm` and `XNormRestr` integrate a possibly non-measurable integrand with `∫⁻`, which is a
  lower integral. So the Lean norm is `≤` TARGET's.
- Its two basic properties cannot be derived: the triangle inequality, and a.e. smoothness of the transformed
  momentum slices.
- This makes those conclusions weaker than TARGET's, and **not consumable by TARGET's own proof steps**. That is
  what wt-wke and wt-torus each hit independently.

Every other norm used by a frozen statement (`SNorm`/`SNormR`, `ZNorm`/`ZNormOn`, `XNorm00`/`XNorm00Restr`) is
measurability-robust.

**Fix (REQUIRED before the freeze): one guard in B1 `XNorm`.** Require `C^{Λ₁}` slices for almost every frequency,
exactly the landed `Fourier.MixedFourierAdmissible`. No statement text changes.

### Inputs

- B1 `/home/scott/wt-scratch/waveb-snap-8`: its `SHA256SUMS` verify. `WaveB1-System.lean` is `59365906…`, the same
  as snapshots 6 and 7; its Norms section (L327–L417) is unchanged.
- B2 `waveb2-snap-final` (`b605320f…`).
- TARGET §2.4.1 (L579–L594): (normX) L581, (normX1), (normX2) L585, (locnorm) L589, (defznorm) L594.
- wt-wke `pl234/ISSUE-XNORM.md`; wt-torus `regref/HANDOFF.md` Part 2 and `regref/OBLIGATIONS.md`.
- The landed `Foundations/Fourier/MixedNorm.lean` (`mixedFourierNorm`, `MixedFourierAdmissible`,
  `mixedRestrictionNorm`).
- Probe `N1.lean`: the fixed norm, and `XNorm ≤ XNormFix`, `XNormRestr ≤ XNormRestrFix`; standard axioms.

### What TARGET defines

- **(normX).** `‖F‖_{𝔛^{θ,Λ₁,Λ₂}} = max_{|ρ|≤Λ₁} ∫ ⟨λ⟩_max^θ ‖⟨k⟩^{Λ₂} ∂_k^ρ F̂(λ,k)‖_{L^∞_k} dλ`.
  - This is a Lebesgue integral. It presupposes that `∂_k^ρ F̂(λ,·)` exists for a.e. `λ` and that the integrand is
    measurable.
  - Otherwise the norm is not finite (the standard convention, and the one adopted by WAVE-B §2.6 and the landed
    `mixedFourierNorm`).
- **(locnorm).** The restriction norm is the infimum of `‖G‖` over extensions `G` of `F` from `ℬ × K`. TARGET treats
  it as a seminorm: (prooflayer1-1) (L1241–L1246) telescopes with the triangle inequality.
- **(normX2) and (defznorm).** Weighted suprema; no integral.

### Each Lean norm

| norm (B1 System) | used by | measurability | relation to TARGET |
|---|---|---|---|
| `SNorm`, `SNormR` (L349–357) | B1.1 `propansatz` and B1.3 `fixedpoint` (`AnsatzAt`), B1.2 `layergarden` (hyp. `RemainderBound`, concl.), B1.5 `wkeTaylor` (concl.), B1.6 `sumint` (hyp. `Admissible` weights), B1.12 `layergardenFlower` (hyp.), B2.1 (hyp. `InputRemainder`, concl. item 3) | no integral: a pointwise supremum | `≥` TARGET's: pointwise sup vs `L^∞`, and `⊤` without classical `C^{Λ₁}`. **Equal** on `C^{Λ₁}` functions. Every use has `Λ₁ ≥ 1`. Prior ruling: stage-2 O5, WAVE-B §2.6. |
| `ZNormOn`, `ZNorm`, `ZSpace` | B1.3 `fixedpoint`, B1.4 `nlsAkBridge` | supremum | **equal** to (defznorm) |
| `XNorm00`, `XNorm00Restr` (L389–402) | B1.6 `sumint` (concl.), B2.1 item 3 (`𝒥ℬ*`, concl.) | **robust.** For each `v`, `λ ↦ timeFT F λ v` is continuous (FT of an `L¹` slice), so `λ ↦ ⨆_v ‖·‖` is lower semicontinuous, hence Borel. `∫⁻` is a genuine integral, and the infimum is a seminorm. | `≥` TARGET's: pointwise sup in `v`, and the slice-integrability guard. Equal on the relevant (continuous) functions. Prior rulings. |
| `XNorm` at `Λ₁ = 0` | (through `XNormRestr`; no frozen use at order 0) | robust (lower semicontinuous, as above) | as `XNorm00` |
| **`XNorm` at `Λ₁ ≥ 1`, `XNormRestr`** (L379–398) | **B2.1 items (1), (2); B2.2 (1), (2)**, all at `Λ₁ = 30d`, all in conclusions | **not robust.** See below. | **`≤` TARGET's.** Equal for every extension whose smooth-frequency set is measurable; possibly strictly smaller otherwise. No triangle inequality is derivable. |

### The defect

**Where the integrand can fail to be measurable.** `XNorm θ Λ₁ Λ₂ G` (guard: every time slice integrable) is
`⨆_ρ ∫⁻ ⟨λ⟩^θ · g_ρ(λ)`, where `g_ρ(λ) = if ContDiff ℝ Λ₁ (Ĝ(λ,·)) then ⨆_k ⟨k⟩^{Λ₂}|∂^ρĜ(λ,k)| else ⊤`.
- On `E_G = {λ | Ĝ(λ,·) ∈ C^{Λ₁}}`, `g_ρ` agrees with a Borel function `H_ρ`: iterated difference quotients of the
  continuous `λ ↦ Ĝ(λ,k)`, with the supremum taken over a countable dense set of `k`.
- Off `E_G`, `g_ρ = ⊤`.
- `G` ranges over **arbitrary** extensions: no joint measurability, nothing tying different `k` together. So
  `E_G` is an uncountable intersection of conditions and need not be measurable.
- I did not construct an explicit `G` with non-measurable `E_G`. wt-wke asserts a Bernstein-type construction,
  which I have not verified. Nothing in the definition excludes one.

**What `∫⁻` then computes.** `∫⁻` is the supremum of integrals of measurable simple functions below `g_ρ`, so it sees
`E_Gᶜ` only through its inner measure.
- If `E_Gᶜ` has inner measure 0 but positive outer measure, then `∫⁻ g_ρ = ∫ H_ρ`. This can be finite, while
  TARGET's norm is `∞`: `∂^ρĜ(λ,·)` fails to exist on a non-null set.
- Hence `XNorm ≤ TARGET`, possibly strictly; this is wt-torus's "inner measure only".
- Lower integrals are superadditive but not subadditive. So `XNormRestr(F₁+F₂) ≤ XNormRestr F₁ + XNormRestr F₂`
  cannot be derived (wt-wke): the near-optimal extensions may have non-measurable integrands.

**When the two agree** (`N1.XNorm_le_XNormFix`). If `E_Gᶜ` is null, the integrands agree a.e., and `∫⁻` is the true
integral (`lintegral_congr_ae`). If `E_G` is measurable and `E_Gᶜ` is not null, both norms are `⊤`. So the frozen
norm differs from TARGET's only on extensions with a non-measurable smooth-frequency set. But because the infimum
ranges over all extensions, no lemma can exclude them.

### Effect on each frozen statement

| statement | norm and position | effect |
|---|---|---|
| B1.1 `propansatz`, B1.2 `layergarden`, B1.3 `fixedpoint`, B1.4 `nlsAkBridge`, B1.5 `wkeTaylor`, B1.12 `layergardenFlower` | sup norms (`SNorm`, `SNormR`, `ZNorm`), in hypotheses and conclusions | **none.** No integral is involved. The `SNorm` deviations (`≥` TARGET's; equal on `C^{Λ₁}`) are the previously ruled readings. |
| B1.6 `sumint` | `XNorm00Restr` (conclusion); `SNorm` in `Admissible` (hypothesis) | **none.** The integrand is lower semicontinuous. |
| B1.7–B1.11 | no norms | — |
| B2.1 item (3) | `XNorm00Restr` (`𝒥ℬ*`), `SNormR` (`ℳ*`), conclusions | **none** |
| B2.1 hypothesis `InputRemainder` | `SNormR` | **none** |
| **B2.1 items (1), (2); B2.2 (1), (2)** | `XNormRestr η (30d) (30d or 0)`, **conclusions** | **Weaker than TARGET**, since a smaller norm `≤` bound is a weaker claim. **They are not false:** TARGET's bound implies them, and RA2 proves B2.1 through `XNormRestr ≤ mixedRestrictionNorm`. **They are unfaithful as consumable statements:** they do not give the seminorm bound TARGET's consumers use (prooflayer1-1/1-2 L1241–L1246; the trace for `q' < r`). wt-wke cannot assemble Prop 6.1 for `q > q'` from B2.1 for this reason. |

No frozen statement has `XNorm` or `XNormRestr` in a hypothesis. So the smaller norm makes no statement stronger, and
none false.

### Fix

**The fix (REQUIRED before the freeze).** In B1 `WaveB1-System.lean` L379–384, replace `XNorm` by the following (it
elaborates; `N1.lean`, `XNormFix`):
```lean
noncomputable def XNorm {r : ℕ} (θ : ℝ) (Λ₁ Λ₂ : ℕ) (F : (Fin r → ℝ) → Mom d → ℂ) : ℝ≥0∞ :=
  if (∀ k, Integrable fun t => F t k) ∧ (Λ₁ = 0 ∨ ∀ᵐ lam, ContDiff ℝ Λ₁ (timeFT F lam)) then
    ⨆ (ρ : Fin d → ℕ) (_ : ∑ j, ρ j ≤ Λ₁), ∫⁻ lam : Fin r → ℝ, maxBracketPow θ lam *
      ⨆ k, ENNReal.ofReal (jbr k ^ Λ₂ * ‖iterPartial ρ (timeFT F lam) k‖)
  else ⊤
```
Keep the existing `open Classical in` on the definition, as `XNormFix` does with `classical`.

**What the fix changes.**
- The guard becomes TARGET's and the landed `MixedFourierAdmissible`: `C^{Λ₁}` slices for **almost every** `λ`.
- The integrand is then a.e. equal to the Borel `H_ρ`, so `∫⁻` is a genuine integral. The triangle inequality and
  differentiation under the integral become available.
- `XNormRestr`, B2.1 and B2.2 keep their text. Their meaning becomes TARGET's (normX)/(locnorm), up to the existing
  rulings: pointwise sup in `k`, integrable slices, classical derivatives.
- The fixed `XNorm` equals the landed `mixedFourierNorm`, up to multi-indices versus derivative words, which agree on
  `C^{Λ₁}`.

**Conservative.** `N1.XNormRestr_le_XNormRestrFix` (standard axioms): any bound proved in the fixed norm implies the
current one.

**Cost.**
- One B1 definition changes. No B1 theorem uses `XNorm` or `XNormRestr` (B1.6 uses `XNorm00Restr`). The B1 freeze
  list keeps its entries; `XNorm` gets a new body hash.
- B2's text and freeze set are unchanged; only the B1 base hash changes.
- Prover impact:
  - RA2 (`regref`) states `RA1Couple` in B2's `XNormRestr`; it should restate it in the fixed (equivalently, the
    landed) norm, as wt-torus already offered. `RA1Tree` is already in the landed norm.
  - `XNorm_le_mixedFourierNorm` becomes an equality.
  - PL234 gets the triangle inequality, so its weighted-order-0 workaround is no longer needed for `q > q'`.

**Why before the freeze.** After the freeze, this change needs versioned successors of `XNorm`, `XNormRestr`, B2.1 and
B2.2. Before it, the change costs one guard.

**Alternative (not recommended).** Restrict the infimum of `XNormRestr` to extensions satisfying the a.e. guard. This
has the same effect on B2, but it leaves `XNorm` non-faithful as a standalone definition.

**No action** for `SNorm`/`SNormR`, `ZNorm`/`ZNormOn`/`ZSpace` and `XNorm00`/`XNorm00Restr`.

---

## Snapshot 9, 2026-11-04 (B1 snapshot 9 = snapshot 8 + the `XNorm` fix; snapshot 8's delta; B2 rebased)

### Verdict: PASS

1. **Snapshot 8 → 9.** Exactly my `XNorm` replacement and its docstring. No other source or constant changes.
2. **Snapshot 7 → 8.** Exactly the F78 clause, with its docstring and the matching probe updates. The fix is correct
   against TARGET.
3. **B2 rebased.** The B2 Lean files are byte-identical, the freeze set is unchanged, and all seven modules compile
   on snapshot 9 with the same `sorry`s.
4. **B2.1 (1)–(2) and B2.2.** They now say what TARGET (normX)/(locnorm) says, up to the earlier rulings. The
   direction `old XNormRestr ≤ new XNormRestr` holds on the real definitions, with equality wherever TARGET's norm is
   finite.

### 1. Snapshot 8 → 9 (`/home/scott/wt-scratch/waveb-snap-9`)

**Hashes.**
- `SHA256SUMS` verifies; its digest is `30263a9921993f40…`.
- Snapshot 8's `SHA256SUMS` (`138033c99cab…`) verifies too.

**Source diff.** Of the 12 Lean files, **only `WaveB1-System.lean` differs** (`59365906…` → `cc53aad3…`). Its diff is:
- the `XNorm` docstring (L372–377);
- the guard
  `if (∀ k, Integrable fun t => F t k) ∧ (Λ₁ = 0 ∨ ∀ᵐ lam, ContDiff ℝ Λ₁ (timeFT F lam)) then`;
- the integrand `maxBracketPow θ lam * ⨆ k, ENNReal.ofReal (jbr k ^ Λ₂ * ‖iterPartial ρ (timeFT F lam) k‖)`.

This is exactly the text recommended in "Norm measurability", and `open Classical in` is kept.

**Constant diff** (`Dump.lean`, Expr hashes of every constant of `WaveBDraft.{Core, System}`).
- Snapshot 8 (`waveb/build`, compiled from System `59365906…`) has 348 constants: `dump8.txt`.
- Snapshot 9 (my build) has 349: `dump9.txt`.
- **Exactly one constant changes:** `WaveTurbulence.XNorm` (value only; its type is unchanged).
- **One constant is new:** the auxiliary `XNorm._proof_1 : OuterMeasureClass (Measure (Fin r → ℝ)) (Fin r → ℝ)`.
  This is the instance proof that the `∀ᵐ` filter needs; it is auto-generated, folds into `XNorm`, and comes from
  Mathlib.
- The other B1 modules are byte-identical. No B1 theorem uses `XNorm` or `XNormRestr`.

**Axioms.** `XNorm` and `XNormRestr`: `[propext, Classical.choice, Quot.sound]` (`Q10.lean`).

### 2. Snapshot 7 → 8 (F78)

**What changed.** Only `WaveB1-Flower.lean` and `WaveB1-Flower-probes.lean` differ.
- In `coupleSum` (B1.12's couple sum), the `dt = true` clause
  `∀ j : Fin 2, ∃ b : GBranch LG.garden.tree, b.1 = (j, [])` gains `∧ LG.layer b.toNode = p`.
- The docstring is updated.
- The two probe occurrences of the clause are updated identically.

**Source.** TARGET L2312: `∂_t a^tr` "simply contains an extra `δ(t_𝔯 − t)` factor in `𝒥_𝒯`".
- The trees of `a^tr` are top-layer trees, and `∂_t 𝒥_• = 0`. So both roots are top-layer (layer `p`) branching nodes.
- The old clause admitted a trivial top tree with a lower-layer garden attached at its root, which F78 describes
  correctly.
- `IsCanonC (p+1)` already bounds every layer by `p`, so the new clause says exactly "both top trees are nontrivial".
  It removes only the illegitimate terms. `dt = false` is unchanged.

**Correct.** Since snapshot 8, no file but `System` changed (above).

### 3. B2 rebased on snapshot 9 (`waveb2-snap-final`, `SHA256SUMS` `b3db9c4367a8…`)

**Hashes.** All entries verify. The 7 B2 Lean files, the 7 provider files and `FREEZE-LIST.md` are **byte-identical**
to my Re-check 3 copy (`snap-final3/`). So the 76-declaration freeze set is unchanged. Its closure contains no B1
definition: the B1 owners, `XNormRestr` among them, are referenced by name, and the names are unchanged.

**Independent build** (`b2-audit/s9build/`, my script; `build.log`). On dev's Mathlib and Wave A, one `lean` at a
time, I built:
- the 11 B1 modules of snapshot 9: Core, System, Statements, Lemmas, Sumint, Flower, Bridges, and the
  Core/System/Statements/Flower probes;
- the 7 B2 modules.

**All 18: 0 errors.** The `sorry`s are:
- B1: Statements 10, Sumint 1, Flower 1, which are the 12 anchors B1.1–B1.12;
- B2: Regular 6, Molecules 1, Statements 3, the same as before.

The probe files have no warnings. `regularAsymptotics` and `incoherentDecay` elaborate against the new `XNormRestr`
with their text unchanged.

### 4. What B2.1 (1)–(2) and B2.2 now say

**The direction, on the real definitions** (`N2.lean`, standard axioms; the snapshot-8 body copied as `XNormOld`):
- `XNormOld_le_XNorm`, and hence `XNormRestrOld_le_XNormRestr`: old `≤` new. **This is the direction proved in
  "Norm measurability".**
- `XNorm_eq_XNormOld_of_ae`: the two are equal whenever the slices are integrable and a.e. `C^{Λ₁}`. Nothing changes
  on extensions that TARGET's norm accepts.

**Faithfulness.** For every `G` the new `XNorm G` is TARGET's (normX) `‖G‖`.
- Either the guard fails, and the norm is `⊤`. In TARGET, the derivatives then do not exist on a non-null set, or the
  slices are not integrable (the stage-2 O1 reading for unbounded supports).
- Or `G` passes the guard. On a co-null Borel set `Ĝ(λ,·)` is then `C^{Λ₁}`, and the integrand equals the Borel
  function `sup_{k∈ℚ-dense} ⟨k⟩^{Λ₂}|∂^ρĜ(λ,k)|`. So `∫⁻` is the Lebesgue integral of TARGET's integrand.
- Hence `XNormRestr` is TARGET's (locnorm), an infimum of genuine norms over extensions, and it is subadditive.
- The remaining differences are the earlier rulings:
  - pointwise sup in `k`, which equals `L^∞_k` for continuous slices;
  - integrable time slices;
  - classical derivatives.

So **B2.1 items (1)–(2) and B2.2 now state TARGET's bounds in TARGET's norm.** They are stronger than under snapshot 8
(old norm `≤` new), and true as far as the source shows.

**OPTIONAL.** Land the triangle inequality for `XNormRestr` (the a.e.-measurability of the integrand under the new
guard) as a Foundations lemma. PL234 needs it, and it is the analogue of the landed `mixedRestrictionNorm` calculus.
RA2's bridge `XNormRestr_le_mixedRestrictionNorm` now holds as an equality up to representation, and `RA1Couple` can
be restated in either norm.
