# Audit: Wave B tier B2, stages 2–3 (molecules; B2.1–B2.3)

Auditor: `wt-orch` (Opus), refute-first. Date: 2026-11-03. Task 9b.

## Inputs

**Snapshot.** `/home/scott/wt-scratch/waveb2-snap-1/stage23/`, with its own `SHA256SUMS`. The stage-1 files of Task 8a
stay untouched in the parent directory.

| File | Lines | sha256 |
|---|---|---|
| `WaveB2-Molecules.lean` | 495 | `cfd93a08…7908b1` |
| `WaveB2-Statements.lean` | 267 | `e50aaa94…84b6f3` |
| `WaveB2-Regular.lean` (changed since stage 1) | 594 | `ad72ce4b…8c3c53` |
| probes (Molecules, Statements, Regular) | — | `d690f9de…`, `3ab2ec2b…`, `0bfef42f…` |
| `DESIGN.md` | 321 | `2d147042…96e1e0a` |

**The stage-1 delta.** The only change to `WaveB2-Regular.lean` since Task 8a is the closure policy.
- The Foundations imports are gone.
- `resIntegral`, `resSlice` and the inlined `pvResonantIntegral` repeat the landed bodies. The probe bridges
  `resIntegral_eq_resonantIntegral` and `pvResonantIntegral_eq_energyInv` both hold **by `rfl`**.
- My stage-1 OPTIONAL items O1–O6 are not yet applied (B2 is not being frozen).

**Sources.**
- TARGET:
  - Def `defmol` L1295;
  - Def `defcplmol` L1297–L1302, Prop `propcplmol`;
  - Def `defdecmol` L1308–L1325;
  - Def `defblock` L1328–L1331;
  - Def `defvine` L1384–L1390 (with my figure-defs §1);
  - Def `defdiff` L1938–L1941;
  - Def `defcut` L2117–L2127 (figure-defs §4, F40);
  - (defcounta2), (defdev) L2129–L2137;
  - Prop `ladderl1old` L1994;
  - Remarks `remiota`/`remtame` L2149–L2152;
  - Props `excessprop1`, `finalmol`, `lgmolect` L2154–L2200;
  - Props `regref1`–`regref3` L1145–L1232;
  - the standing assumptions L946–L951 and Prop `proplayer1` L953–L956.
- FINDINGS F11, F21, F33, F37, F40.

**Build.**
- Against my snapshot-3 B1 modules (Task 8b) and the landed Resonant oleans.
- `WaveB2Draft.{Regular, Molecules, Statements, RegularProbes, MoleculesProbes}` compile as modules, and the
  Statements probes elaborate.
- **0 errors.** The `sorry`s are exactly the obligations and anchors:
  - Regular: the 5 characterization obligations;
  - Molecules: `Garden.isMolecule_molecule`;
  - Statements: `regularAsymptotics`, `incoherentDecay`, `rigidity`.
- All probe files are sorry-free.

## Verdict

**Stage 2 (molecules): APPROVED as a definition set.** It is faithful to TARGET:
- half-edge molecules (F40);
- the molecule of a garden;
- decorations, Γ_v and restrictions;
- blocks and ladders (F37 for standalone ladders: m + 1 ≥ 2 rungs, opposite rails);
- the eight vine templates;
- rung insertion with k ≥ 0 (F37, DH23 family);
- the vine predicate;
- gaps, cuts (dart reading) and 𝔈/𝔄/𝔇𝔢𝔳.

I checked all eight templates bond by bond against figure-defs §1(a).

**Stage 3 (statements):**
- **B2.1 `regularAsymptotics` and B2.2 `incoherentDecay`: APPROVED as drafts.** They transcribe regref1–3 and
  proplayer1 faithfully, with F11 and F33 (order range n ≤ N_{p+1}^4) disclosed.
- **B2.3 `rigidity`: NOT APPROVED as frozen-ready. Two REQUIRED items before it can be frozen:**
  - **R1 (new):** the gap hypotheses treat the two darts of **one** self-loop as a gap triple. I prove in Lean that
    this makes the abstract theorem vacuous on components that TARGET's `lgmolect` covers.
  - **R2 (= DESIGN Q6):** ZG-tame ε-atoms are excluded. TARGET's `finalmol` allows them, and `lgmolect` covers them.
- B2.3 is not in the next freeze (it waits for packet G8), so these block nothing now.

**Priority question (findings that would change the B1 carriers): none.**
- Every B2 object is built on the B1 carriers without modification: `Garden.molecule` on `Garden`/`GBranch`/`pair`/`mark`;
  B2.1/B2.2 on `LayeredGarden`, `KQstar`, `KTstar`, `inputsF`, `XNormRestr`, `XNorm00Restr`, `SNormR` and
  `wkeTaylorTerm`.
- They need no field, layering convention or kernel argument that B1 lacks. The paired-tree convention (lone leaf
  marked `lower`, its layer free below its parent) and the couple time domains (`up = t` on 𝒯⁺, `s` on 𝒯⁻) are
  exactly what regref1 (trees, ℬ ∩ {t > s}) and proplayer1 (roots in layers ≤ q, ≤ q′) consume.
- **One forward-looking note.** The skeleton decomposition (Prop `propstructure2`) and (redkg) will need garden
  surgery: collapsing embedded regular couples and trees into leaf pairs and nodes. B1 supports it through address
  maps (B1 DESIGN §1.2); no carrier change is needed. COMB-CORE should provide those maps before B2 stage 4.

## 1. Verdict table: stage 2 (`WaveB2-Molecules.lean`)

| Decl | Verdict | TeX | Reason |
|---|---|---|---|
| `Molecule V D` (atoms, `atom`, `mate`, `out`) | FAITHFUL (F40 carrier) | Def `defmol` | A fixed-point-free bond involution with opposite orientations on the two darts. A self-loop is two darts at one atom, counting as outgoing once and incoming once, as T says. Atoms form a `Finset` of an ambient type, so cuts can add fresh atoms. |
| `dartsAt`, `deg`, `outdeg`, `indeg`, `bonds`, `ends`, `Adj`, `numComponents`, `circuitRank`, `SameComponent` | FAITHFUL | Def `defmol` | F counts the components of the undirected graph (a `Quot` of the atom subtype by `Adj`); χ = E − V + F in ℤ. |
| `IsMolecule` | FAITHFUL | Def `defmol` (i), (ii) | (i) at most 2 outgoing and 2 incoming bonds per atom. (ii) Every component has an atom of degree ≠ 4, i.e. < 4 given (i). |
| `InGroup`, `degIn`, `outIn`, `inIn`, `IsBlock`, `bondsBetween`, `sigma`, `Directed`, `groupBonds` | FAITHFUL | Def `defblock` | Joints have in- and out-degree 1 within S; interior atoms have degree 4 within S. σ = the number of joint–joint bonds. Hyper-blocks and concatenations are not drafted (proof-internal; accepted). |
| `GardenDart`, `Garden.molecule` | FAITHFUL | Def `defcplmol` | Atoms are the branching nodes. PC darts: the dart at the parent is outgoing iff the child has sign −. LP darts: one per paired leaf whose own parent and whose partner's parent both exist, outgoing iff that leaf has sign −. So the bond runs from the parent of the − leaf to the parent of the + leaf. Root leaves give no bond (T L1316 `𝔓_j`), and paired siblings give a self-loop. Checked by count against `propcplmol`: a couple of order n has n atoms and (n − 2) + (n + 1) = 2n − 1 bonds. Probe `miniCouple00_molecule_degrees`. |
| `Garden.isMolecule_molecule` (obligation) | correctly stated | Prop `propcplmol` | Plain garden, w = 2 or irreducible, order ≥ 1. I checked the delicate case of trivial trees: their root leaves carry no LP bond, but a trivial tree pairs with exactly one leaf. So if two nontrivial trees were never paired directly, the union of one of them with its trivial partners would be closed, contradicting irreducibility. The molecule is connected, and roots give degree < 4. |
| `kvec`, `dartSign`, `IsDecoration`, `Gamma`, `IsRestricted` | FAITHFUL | Def `defdecmol`, (decmole1), (defomegadec) | Labels are constant on bonds, with vectors w + n/L; a self-loop contributes k − k = 0 at its atom; the restriction is \|Γ_v − β_v\| ≤ δ⁻¹L^{−2γ} and \|k_ℓ − k_ℓ⁰\| ≤ 1. |
| `GapKind`, `gapKind`, `gapAt`, `IsBlockGap` | FAITHFUL (see R1 for the distinct-bond condition) | Def `defdiff` | ZG: r = 0. SG: 0 < \|r\| ≤ L^{−γ+η}. LG: \|r\| > L^{−γ+η}. |
| `IsLadder`, `ladderAtoms`, `IsLadderSet`, `maximalLadders`, `ladderLength`, `numLadders`, `numFree`, `rho`, `IsLadderGap` | FAITHFUL | Def `defvine` (ladder part), Prop `ladderl1old` | m ≥ 1, i.e. m + 1 ≥ 2 double bonds; distinct atoms; rails are single bonds with opposite directions per rung interval (an explicit clause, since the ends may have outside bonds); no other internal bond (4m + 2 bonds); length = m = \|S\|/2 − 1. q, m and ρ follow L2134. |
| `VineType`, `VineTemplate`, `VineType.template` | FAITHFUL (all 8 checked bond by bond) | `Vines.png`; figure-defs §1(a) | Bond counts are 2/10/16/16/16/28/20/20. Slots and their order are as in figure-defs, including the (VII) red slot **parallel** (a⋯c, b⋯d). Groups follow V5: each rung, plus the three remaining atoms, plus (VII) {c, d}. Probes: `vineTemplate_ok` (degrees: joints 2, others 4) and `vineTemplate_counts`. |
| `railBonds`, `insertRungs`, `VineType.expand` | FAITHFUL (F37: k ≥ 0, DH23 family; k = 0 is the template) | figure-defs §1(a) "expansion" | The new atoms are fresh; the slot bonds are replaced by rails, plus double rungs, plus one group per rung. Probes `vineII_one_rung` (k = 1, which is not a T ladder: F37) and `vineVI_rungs`. |
| `IsVine` | FAITHFUL (V2: no direction clause; V4: joints unordered) | Def `defvine` | A block, plus an undirected multigraph isomorphism onto `T_X(k⃗)` with {j₁, j₂} ↦ {J₁, J₂}. Probe `doubleBond_vine`. |
| `cut`, `IsCutData`, `IsAlphaCut` | FAITHFUL (F40 dart reading; see R1 for distinct bonds) | Def `defcut` and the remark after it | The incoming dart x₁ and the outgoing dart x₂ stay at v = v₁; all other darts at v move to the fresh v₂. Degree-2 cuts are allowed (the remark). α means no new component. Probe `doubleBond3_cut`. |
| `countE` (𝔈) | FAITHFUL (reading Q4) | L2131 ("supremum over the parameters") | Supremum over c (c_v = 0 at degree-4 atoms), β and k⁰ (constant on bonds) of the `encard` of restricted (c_v)-decorations with `Adm`. It is ℕ∞-valued, so there is no junk 0. Probe `finite_restricted`. See O3 for the ranges of c and k⁰. |
| `ladderWeight`, `countA` (𝔄) | FAITHFUL | (defcounta2), `ladderl1old` | 𝔈·L^{−(d−γ)χ}(C₁⁻¹δ^{1/2})^χ ∏ 𝔛_j^{z_j}, with 𝔛 = min((log L)², 1 + δL^{2γ}P). |
| `deviation` | FAITHFUL (reading Q5) | (defdev) | 𝔄_pre/𝔄_pos in ℝ≥0∞. Edge cases: x/0 = ⊤ and 0/0 = 0 are the right least ℐ. ⊤/⊤ = 0 is not, but 𝔄 is finite (O4). |
| `AtomLabel` | FAITHFUL | `finalmol`, `remiota` | α(Q, κ), β, ε. |

## 2. Verdict table: stage 3 (`WaveB2-Statements.lean`)

| Decl | Verdict | TeX | Reason |
|---|---|---|---|
| `timeBox`, `timeBoxGt`, `InputRemainder`, `regBound` | FAITHFUL | L946–L951 | ℬ = [q,q+1]×[q′,q′+1], with ∩{t > s} for trees. Rᵣ is real with ‖Rᵣ‖_{𝔖^{40d,40d}} ≤ L^{−θᵣ} ("(ansatz2) with Λ_p replaced by 40d"). The bound is C₁(C₁δ)ⁿL^{−(γ₁−√η)g}, with ≲₁ made explicit by C₁. |
| **B2.1 `regularAsymptotics`** | FAITHFUL (draft) | `regref1` (1-1)–(1-5), `regref2`, `regref3`; F11, F33 | **(1)** ‖K*_𝒬 − (K*)_app‖_{𝔛^{η,30d,30d}([r,r+1]²)} ≤ bound, for every well-formed code of size 2n and every layered carrier it decodes with all layers r. For non-dominant codes `app = 0`, so this is regref1-1, and for dominant codes it is regref1-2. **(2)** Trees: the lone leaf is in layer q′ ≤ r, ℬ ∩ {t > s}, 𝔛^{η,30d,0} (F11 D2). **(3)** ‖𝒥ℬ*‖_{𝔛^{1−η}(ℬ)} as `XNorm00Restr (V := Unit)`, and ‖ℳ*‖ in 𝔖^{30d,30d} (trees 𝔖^{30d,0}), for dominant codes and special Z (regref1-4). **(4)** Σ_{dominant, size 2n} (K*)_app(t,t,k) = 𝒰ₙ(t,k) with r = p, Rₚ = 0. This is F11's corrected regref1-5, with the finite support probed. The order range is n ≤ N_{p+1}⁴ (F33, route R14): a disclosed proof risk, not a statement defect. Quantification over (code, carrier) with `Decodes` equals quantification over regular couples, by `existsUnique_regCpl_decodes`. Probes: item-(1)/(2) hypotheses non-vacuous. |
| **B2.2 `incoherentDecay`** | FAITHFUL (draft) | `proplayer1` with L946–L951, Def `defkg` | Couples: layers ≤ p; roots ≤ q, ≤ q′ (q, q′ ≤ p); g = `incoherency Q.links` ≥ 1; ℬ = [q,q+1]×[q′,q′+1]; bound L^{−(γ₁−√η)g}. Trees: root ≤ q, lone leaf in layer q′ ≤ q ≤ p, ℬ ∩ {t > s}. Inputs: `inputsF P R` for all q ≤ p. Deviation D1 (arbitrary layerings) agrees with T's standing assumption, which imposes canonicity only for g = 0. Probe `incoherentDecay_nonvacuous` (mini-couple with g = 1). |
| `IsConnected`, `IsPerfect`, `ABLinked`, `FinalShape` | FAITHFUL to `finalmol`'s structural part | `finalmol` | No triple bond; α/β degree ≤ 2; a perfect component has a β-atom; a perfect cycle is a double bond, length ≥ 4, or a triangle with ≤ 1 α-atom; in a perfect non-cycle every α/β chain touches exactly two distinct ε-atoms. "At most R imperfect components" is global, so it is correctly not in the per-component hypothesis. Probe `doubleBond_finalShape`. |
| `DecorationHyp` | **WRONG on self-loops (R1)**; otherwise FAITHFUL up to Q6 (R2) and ∼₀ = dyadic factor 2 (D3) | `finalmol`, `excessprop1`, `remiota`, `remtame` | Correct clauses:<br>• α labels: Q ∈ [L⁻¹, L^{−γ+η}], κ ∈ {0,50};<br>• α gap ∼₀ Q;<br>• κ = 0 ⟺ ι = 0, with the earlier cut gaps given as data;<br>• no ZG α/β atom;<br>• ladder scales P ∈ {0} ∪ [L⁻¹,1] with gap 0, ∼ P, or ≳ 1;<br>• a vine component whose joints have degree 2 is LG.<br>Problems: R1 (self-loops) and R2 (ZG-tame ε excluded). |
| `numBeta`, `perfectIndicator`, `epsDefect`, `alphaFactor`, `rigidityRHS` | FAITHFUL | (finalcount) | ∏_α L^{−(γ+3η)/2+κη}Q⁻¹ · L^{(γ₀+2η²)V_β − (2γ₀+5η²)G} · L^{−η⁵ρ+ηZ}, with Z = 0 if R = 1, else the number of ε-atoms not of degree 4. |
| **B2.3 `rigidity`** | **NOT frozen-ready (R1, R2)**; the abstract design is endorsed | `lgmolect` | The abstraction ("`FinalShape` + `DecorationHyp` ⇒ 𝔄 ≤ RHS", with "(a)–(f) + Operations 1–4 ⇒ hypotheses" as a G1/G3 obligation) is the right shape. Its value depends on every hypothesis being dischargeable at the use site; R1 and R2 are the two places where it is not. |

## 3. REQUIRED (before freezing B2.3; nothing in B1 is affected)

### R1. Gap hypotheses must range over two distinct bonds, not two darts of one self-loop

**The defect.** TARGET's gap of a triple (v, ℓ₁, ℓ₂) is defined for **two bonds** ℓ₁, ℓ₂ ↔ v of opposite directions
(Def `defdiff`). The cut likewise acts along two bonds (Def `defcut`), and `finalmol`'s α condition reads "if v has
two bonds". A self-loop is **one** bond. The draft quantifies over darts x₁, x₂ at v with `out x₁ ≠ out x₂`, which
includes x₂ = mate x₁. For a bond-constant labelling that pair has gap k − k = 0, i.e. ZG. Hence:
- **`epsLG`:** an ε-atom carrying a loop can never be LG. So every admissible decoration is excluded, 𝔈 = 0, and the
  theorem is vacuous there.
- **`alphaGap`, `abNonzero`:** an α- or β-atom whose only bond is a loop gets Q ≤ 0, or gap ≠ 0 fails. Same effect.
- **`iota`:** a spurious r = 0.
- **`IsCutData`, `IsBlockGap`:** they admit the two darts of one loop. That is not a T cut or gap, though harmless.

Self-loops do occur: paired siblings give a loop, prime skeletons contain them (F21), and a cut can move a loop to v₂.

**Lean evidence.** `scratch/WaveB2-stage23-loop.lean` (sha256 `35b08829…5371502`; standard axioms only):
- `loopMol`, a single atom with one self-loop, is a molecule;
- `loopMol_finalShape` holds with the label ε;
- `loopMol_decorationHyp_empty`: `DecorationHyp … (fun _ => .eps) … Adm` forces `¬ Adm κ` for **every** decoration κ.

So B2.3 says nothing on this component, while `lgmolect` still bounds 𝔄 there (ρ = 1, and Z = 1 if R ≥ 2).

**Fix.** Add `x₂ ≠ M.mate x₁` ("distinct bonds") to the dart pairs in:
- `DecorationHyp.epsLG`, `alphaGap`, `iota` and `abNonzero`;
- `IsCutData` (T: "two bonds ℓ₁ and ℓ₂");
- `IsBlockGap`.

For degree-2 α/β atoms whose only bond is a loop, T's "if v has two bonds" makes the α condition void. With the
clause, the draft's `alphaGap` becomes void there too.

### R2. ZG-tame ε-atoms (DESIGN Q6): agree, and required before freezing

- `finalmol` says an ε-atom "must be LG or ZG, and must be tame if it is ZG". The proof of `lgmolect` covers tame
  atoms via DH23 §10.5.
- The draft's `epsLG` (LG only) makes B2.3 weaker than `lgmolect`. Its consumer, the proof of (finalcount1), must
  apply it to **every** component of 𝕄_fin, including those with ZG-tame ε-atoms. So the hypothesis is not
  dischargeable there.
- **Fix (packet G8):** transcribe "tame" from `remtame` (L2152) and DH23 §10.5, and weaken `epsLG` to "LG, or ZG and
  tame". The R1 distinct-bond clause applies here too.

## 4. OPTIONAL

- **O1. Stage-1 optional items O1–O6** (`WaveB2-stage1.md`) are still open: the p.v. characterization for decaying
  kernels, probes P1–P3, the F16 link obligation, the enhanced-couple equivalence, junk documentation, and the
  perfect-matching lemma. O4 (the equivalence ∼) is needed before regref2-3 and regref3's class-dependence can be
  stated.
- **O2. B2.1 item (4) and B2.2 depend on the B1 freeze set.** They use `wkeTaylorTerm`, `KQstar`, `KTstar`,
  `inputsF`, `XNormRestr`, `XNorm00Restr` and `SNormR`, so the stage-3 drafts must be re-elaborated against
  `waveb-snap-4` (the CL-16+ packaging). Named instances could change elaboration.
- **O3. 𝔈's parameter ranges (Q4).** T takes c_v ∈ ℤ_L^d and k_ℓ⁰ ∈ ℤ_L^d; the draft takes the supremum over real c,
  β, k⁰.
  - For c this is immaterial: only c in the right coset gives a non-empty set.
  - For k⁰, a real-centred unit ball can hold slightly more lattice points than any lattice-centred one. That makes
    `countE` ≥ T's 𝔈 and the conclusion of B2.3 marginally **stronger** than `lgmolect`.
  - Restrict k⁰ to `w + latticePoint L ·` for a literal transcription.
- **O4. `deviation` at ⊤/⊤ is 0.** Document that 𝔄 is finite (`finite_restricted`), or define 𝔇𝔢𝔳 as
  `sInf {ℐ | 𝔄_pre ≤ ℐ·𝔄_pos}`.
- **O5. B2.3's κ_v = 50 case** imposes no ι condition, so it is a weaker requirement, as T's κ_v = 50 bound allows.
  That is correct; add a sentence to the docstring.

## 5. DESIGN questions (my answers)

- **Q4 (𝔈's parameters): ACCEPT**, with O3.
- **Q5 (𝔇𝔢𝔳 = the optimal ratio): ACCEPT**, with O4.
- **Q6 (ZG-tame ε-atoms): this is REQUIRED item R2** before freezing B2.3. The reading "LG only" is not enough for
  the consumer.
- **Q7 (freeze policy): AGREE.**
  - Freeze B2.1/B2.2 only after packets C1/C2/C5 validate the codes; the structure-theorem obligations and F33 are
    the risks.
  - Keep B2.3 unfrozen until G8 resolves DESIGN §3.3 (i)–(ii), together with R1 and R2 here.
- **Q8 (orders = code sizes): ACCEPT.** This rests on `RegCpl.size_eq_order`.
- **Stage-2 carrier (half-edges, F40): ENDORSE.** With R1's distinct-bond clause, it makes cuts and gaps
  unambiguous at self-loops, as figure-defs §4 C1 recommended.

## 6. Non-vacuity probes

**Snapshot probes** (sorry-free):
- `vineTemplate_ok`, `vineTemplate_counts`, `vineII_one_rung`, `vineVI_rungs`;
- `doubleBond_block`, `doubleBond_vine`, `doubleBond3_cut`;
- `miniCouple00_molecule_degrees`;
- `finite_lattice_ball`, `finite_restricted`;
- `finite_dominant_codes`;
- `regularAsymptotics_item1/2_nonvacuous`, `incoherentDecay_nonvacuous`;
- `doubleBond_isMolecule`, `doubleBond_finalShape`;
- the Regular bridges `resIntegral_eq_resonantIntegral` and `pvResonantIntegral_eq_energyInv` (by `rfl`).

**My probe.** `scratch/WaveB2-stage23-loop.lean` (untracked): `loopMol`, `loopMol_isMolecule`, `loopMol_finalShape`,
`loopMol_gap_zero`, `loopMol_decorationHyp_empty`. Axioms: `[propext, Classical.choice, Quot.sound]`.
