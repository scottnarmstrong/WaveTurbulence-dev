# Wave B (tier B2) — freeze candidate for author approval

Snapshot `/home/scott/wt-scratch/waveb2-snap-final` · prepared 2026-11-04 (B2-CL-1 to B2-CL-22; supersedes the audited
snap-2 and snap-3).

**This is the exact Lean to be frozen**, exactly as for Wave A (D6) and as prepared for Wave B tier B1 (D7, pending):
- one declaration per file under `WaveTurbulence/Frozen/`;
- the two theorems with body `by sorry`, as `DRAFT_SORRY` anchors;
- definitions sealed.

**File hashes:**
- `WaveB2-Regular.lean` 4d7f81efa32b…;
- `WaveB2-Molecules.lean` 5cc506118852… (B2-CL-21; no frozen declaration);
- `WaveB2-Statements.lean` 82e42b2bfa16…;
- `FREEZE-LIST.md` 61f1be74590f…;
- `SHA256SUMS` b3db9c4367a8… (22 files, including `providers/`).

**B1 base:** snapshot 9, `WaveB1-Core.lean` 0b8477d9943a… and `WaveB1-System.lean` cc53aad3acd7…; once D7 lands,
these are the B1 frozen definitions. Snapshot 9 fixed B1 `XNorm`'s guard (CL-23, F80: `C^{Λ₁}` slices for almost
every frequency, TARGET's norm), so `XNormRestr` in B2.1 items (1)–(2) and B2.2 is TARGET's (locnorm); the B2 text
is unchanged.

## 1. What is frozen

**Seven theorem anchors, B2.1, B2.2 and the decoding obligations O1–O5, and the 76 declarations they reach**
(B2-CL-22):
- 7 theorems, 62 defs, 2 abbrevs, 1 structure, 3 inductives, and 1 instance-def;
- by file: Regular 70, Statements 6, Molecules none.

The full list, with source citations and dependencies, is the snapshot's `FREEZE-LIST.md`, copied to
[`WAVE-B-B2-FREEZE-LIST.md`](WAVE-B-B2-FREEZE-LIST.md). **89 further declarations stay in the files but are not
frozen** (§2 item 3). The anchor total is Wave A 2 + B1 12 + B2 7 = **21**.

| # | Lean name | TARGET / DH source | what it says | proof status |
|---|---|---|---|---|
| B2.1 | `regularAsymptotics` | Props `regref1`–`regref3` L1145–L1232 (F11, F61, F66) | (1) A layered regular couple in one layer `r`: `K*_𝒬` equals its explicit leading term `(K*_𝒬)_app` up to `C₁(C₁δ)^n L^{−(γ₁−√η)}` in `𝔛^{η,30d,30d}`. (2) The same for regular trees, lone leaf in layer `q' ≤ r`. (3) `𝒥ℬ*` and `ℳ*` are bounded by `C₁C₁^n`. (4) At `r = p`, `R = 0`, the dominant leading terms sum to the WKE Taylor term `𝒰_n^{(p)}`. | open (the main analytic anchor of B2) |
| B2.2 | `incoherentDecay` | Prop `proplayer1` L953–L956 (standing assumptions L946–L951) | Layered regular couples and trees with incoherency index `g ≥ 1` decay: `‖K*‖ ≤ C₁(C₁δ)^n L^{−(γ₁−√η)g}`. | the PL1 analytic core is proved (wt-l2s `Foundations/Incoh`, `fb174c5`; `PL1-core.md`, with P-1 open); assembly open |
| O1 | `RegCpl.exists_decodes` | Prop `propstructure` L851–L869, Def `defreg` | Decoding a well-formed couple code gives a regular couple. | **proved**; seals on landing (`providers/`) |
| O2 | `existsUnique_regCpl_decodes` | `propstructure` (a),(b); DH21 Props 4.5, 4.7, 4.8 | Every regular couple has exactly one well-formed code. | **proved**; seals on landing |
| O3 | `RegChain.exists_decodesTree` | `propstructure`, last part | Decoding a well-formed chain code gives a regular tree of either root sign. | **proved**; seals on landing |
| O4 | `existsUnique_regChain_decodesTree` | `propstructure`, last part | Every regular tree has exactly one well-formed chain code. | **proved**; seals on landing |
| O5 | `RegCpl.size_eq_order` | `propstructure` (code ↔ order) | The code size is the order of the decoded couple. | **proved**; seals on landing |

**Why O1–O5 are anchors (B2-CL-22; independent re-check 2, R2-1).** B2.1 and B2.2 quantify over well-formed codes
and the carriers they decode (reading D4). They speak about every regular couple or tree, and about nothing else,
only through O1–O5, so freezing these five also freezes what the two analytic anchors mean. The proofs are
wt-resonant's REG-STRUCT. wt-orch rebuilt them on exactly these definitions (161 modules, 0 errors) and checked each
seal: the statement verbatim, closed by `by exact WaveTurbulence.Provider.<name>`, with standard axioms.

**Non-frozen characterization lemmas (CL-20, CL-22).** These are editable targets that stay in the files. At
freeze time they move to a non-frozen module, as B1's lemmas did.

| # | Lean name | TARGET / DH source | what it says | proof status |
|---|---|---|---|---|
| O6 | `regular_count_le` | `propstructure` last sentence; DH21 Cor 4.9 (F55; R15-1, R15-2) | At most `C₀^m` regular couples of order `2m`, and the same for regular trees of each root sign, with finiteness. | **proved in scratch** in this source-object form (REG-STRUCT, `C₀ = 12^9`) |
| O7 | `Garden.isMolecule_molecule` | Prop `propcplmol` L1303–L1306 (F58) | The molecule of every garden satisfies the molecule axioms (degrees ≤ 2 in and 2 out; every component has an atom of degree `< 4`). | **proved in scratch** (MOLE `garden_isMolecule`, the same statement) |

## 2. Rulings and readings to approve

1. **F61: the sign of the special-subset weight** (B2-CL-11; B2.1 deviation D7).
   - `(K*)_app` carries `∏_{𝔫∈Z}(−ζ_𝔫πi)^{-1}`, not T (regref1-3)'s `(ζ_𝔫πi)^{-1}`.
   - DH21 Lemma 7.3 has a sign error: its `χ_∞` part is `−χ_∞(α)/(επiα)·I_μ`, as in DH21 Lemma 5.8 and the landed
     `iker_comp_decompP`.
   - The error was traced by wt-wke, CONFIRMED by the orchestrator, and re-derived independently by the independent
     auditor.
   - Item (4), the sum over equivalence classes, is unaffected, because `|Z|` is constant on a class.
2. **F66: our own statement bug, fixed** (B2-CL-13).
   - The tree coefficient `𝒥ℬ*_𝒯(t,s)` integrates down to `max(s, r)`, not `s`. TARGET states (regref2-2) only for
     `s ∈ [r, r+1]`, but item (2)'s box allows a lone leaf in a lower layer.
   - With lower limit `s`, B2.1 items (2) and (3) were **false** for `q' < r`: the independent audit gave a
     kernel-checked counterexample on the project's own `miniTree10LG`.
   - **F-5:** the principal value `pvResonantIntegral` is characterized for decaying, not compactly supported,
     kernels by `tendsto_pvResonantIntegral_of_decay`. It was proved by wt-ansob (PV-DECAY, landing as
     `Foundations/Resonant/PVDecay*`) and is cited in the docstring (B2-CL-19).
3. **Scope: the closure of the seven anchors, with B2.3 held out** (B2-CL-18, CL-20, CL-22; the orchestrator's
   rulings: small frozen surface).
   - Only declarations reachable from B2.1, B2.2 or O1–O5 are frozen.
   - **Not frozen (89):**
     - the B2.3 section (13);
     - the two characterization lemmas O6, O7 and the 3 declarations only they reach (`GNode.parent`, `GardenDart`,
       `Garden.molecule`);
     - 51 declarations used only by B2.3, such as `countA`, `IsLadder`, `IsBlock` and the `Molecule` structure;
     - 20 used by no theorem.
   - **What this means for B2.1 and B2.2 (reading D4).** They speak about well-formed codes and the carriers they
     decode.
     - TARGET's source-form definition of regular couples and trees **is frozen** (CL-22): `IsRegularCouple`,
       `IsRegularTree`, `RawRegular`, the operations A/B `RawCpl.opA`/`opB` and their helpers (12 definitions).
     - Their identification with the codes is the frozen anchors O1–O5, all proved.
     - The whole molecule layer (`Molecule`, `Garden.molecule`, …) is unfrozen as well. Neither anchor uses it; it
       returns with B2.3.
   - **B2.3 `rigidity` (T Prop `lgmolect`) stays unfrozen.**
   - **Pending author question Q7:** do you approve B2.3's *abstract* hypothesis set (`FinalShape`, the structural
     conclusions of `finalmol`; `DecorationHyp`, what the cutting process guarantees), or should B2.3 wait for
     packet G8?
     - The independent audit classifies these binders as EXCESS until you rule (F-4).
     - F-2 (self-loops are one bond) and F-3 (ZG ε-atoms that are tame, with the root momenta as a binder `kFix`,
       `#kFix ≤ 2R`; DESIGN Q6) are drafted (B2-CL-14, CL-15). G8 must still confirm the `kFix` abstraction.
4. **F57: blocks are connected** (B2-CL-5).
   - `IsBlock` requires the atomic group to be connected; hyper-blocks go through a connected adjoint block.
   - The source's degree-only wording admits disconnected "blocks", for which its concatenation and disjointness
     claims fail (MOLE's counterexample).
   - `IsBlock` itself is not frozen (B2.3 machinery). Approving the convention now keeps the CLCN and MOLE packets,
     which already use it, on the same footing.
5. **F53: ladders are the source's** (B2-CL-3).
   - Selected double-bond rungs and single opposite rails; extra end chords are allowed.
   - The earlier induced definition made maximal ladders overlap (DEGEN's counterexample). With this one, maximal
     ladders are pairwise disjoint in every molecule (`maximalLadders_pairwiseDisjoint`, proved).
   - Not frozen (B2.3 machinery), like item 4.
6. **The B2.1 and B2.2 deviations**, as stated in their docstrings:
   - **B2.1:**
     - (D1) `(K*)_app` is defined by the explicit recursions of DH21 §7 (route R4);
     - (D2) the box `ℬ` for trees as stated (F11);
     - (D3) item (4) uses `app`, not `K*` (F11);
     - (D4) regular objects are quantified as pairs (code, carrier) with `Decodes`, and the code is unique by O2;
     - (D5) the inputs have finite `𝔖^{40d,40d}` norm, not `C^∞`;
     - (D6) the order range is `n ≤ N_{p+1}^4` (F33).
   - **B2.2:** (D1) arbitrary layerings are allowed for `g ≥ 1`, since TARGET's standing assumption uses canonicity
     only for `g = 0`; packet L2 is to confirm this.
7. **Readings** (DESIGN):
   - (Q1) a regular tree of sign `−` is `(•, 𝒯)`;
   - (Q2) the `+` tree is first in a mini-couple;
   - (Q3) chain pairs are ordered by increasing `a` (pair `j` gets time `t_j`);
   - (Q8) item (4) sums over codes of size `2n`, which is the order by O5.
   - In the non-frozen lemmas: the counting lemma O6 fixes the root sign of trees (the two trivial trees would give
     `2 > C₀⁰`) and has finiteness conjuncts (R15-2).
   - O7 holds for every garden. Its earlier hypotheses were superfluous and are dropped (B2-CL-17; F58's warning
     about the bond counts is kept).
8. **The theorem-anchor count** (ruled; CL-20, CL-22). B2.1, B2.2 and O1–O5 are anchors, so the total is
   2 + 12 + 7 = **21**. O1–O5 are proved and seal on landing; O6 and O7 are non-frozen lemmas (§1).
9. **The freeze set is self-contained.**
   - The frozen declarations lie in `WaveB2-Regular.lean` and `WaveB2-Statements.lean`. These import only B1
     `WaveBDraft.System`, `Mathlib.Analysis.Calculus.DSlope` and each other.
   - No frozen definition uses a proved theorem of the project (B2-CL-12; checked by the generator and by the
     independent audit).
   - All instances are named `@[instance_reducible, instance] def`s (B2-CL-16).

## 3. Audit trail

- **Stage audits:**
  - `docs/campaign/orch/audits/WaveB2-stage1.md` (stage 1, wt-orch; its `JBtree` verdict is corrected by a dated
    note: F66);
  - `WaveB2-stage23.md` (stages 2–3, wt-orch).
- **Inputs found by audits:**
  - `DEGEN-F53.md` (F53 → CL-3);
  - `MOLE-prefreeze.md` (F57 → CL-5; F58, F59 → CL-6, CL-7);
  - `REG-STRUCT-prefreeze.md` (R15-1, R15-2 → CL-8).
- **Change list:** `WaveB2-handoff.md`, CL-1 to CL-12, with addenda 2 (CL-13 to CL-17), 3 (CL-18), 4 (CL-19),
  5 (CL-20), 6 (CL-21) and 7 (CL-22); each is also recorded in `DESIGN.md`. Authorship: CL-1 to CL-4 wt-gauss-hc;
  CL-5 to CL-22 wt-orch, as drafter.
- **CL-21 (F72):** vine (II) now includes `m = 1`, the 4-atom Q-block. It changes only held-out declarations
  (`VineType.template` and, through it, `expand`, `IsVine`, `DecorationHyp`, B2.3 `rigidity`). The frozen 59 and
  `FREEZE-LIST.md` were unchanged by it.
- **CL-22 (re-check 2, R2-1):** O1–O5 are anchors again, with the 12 source-form definitions they use. Freeze set
  76; the seal providers are in the snapshot's `providers/`.
- **Independent audit** (a fresh auditor, `WaveB2-independent-audit.md`):
  - first pass FAIL: F-1 (= F66), with F-2 to F-4 (B2.3), F-5 and F-6 REQUIRED;
  - fixes CL-13 to CL-17;
  - **Re-check: PASS WITH REQUIRED FIXES, F-5 only** (snap-3);
  - F-5 is now closed by PV-DECAY (wt-ansob; source review PASS) and CL-19;
  - **Re-check 2: PASS** (CL-18 to CL-21), with one REQUIRED item, R2-1 (the meaning of B2.1/B2.2 depends on
    O1–O5), answered by CL-22.
- **State of the snapshot:**
  - Every REQUIRED item is closed.
  - All seven modules elaborate.
  - The only `sorry`s are the 7 anchors (B2.1 and B2.2 open; O1–O5 proved in `providers/`), the 2 non-frozen
    lemmas and the held-out `rigidity`.
  - The probe files are `sorry`-free, with standard axioms.

## 4. The exact Lean code

Each file is reproduced verbatim. Each declaration that is not frozen (or run of consecutive ones) is replaced by a
marker line `-- [held out, not frozen: …]`; the B2.3 section of `WaveB2-Statements.lean` is replaced by one marker.
`WaveB2-Molecules.lean` has no frozen declarations. Everything else is the text to be frozen. The probe files, `WaveB2-Ladders.lean` and the generators are in the
snapshot.

### WaveB2-Regular.lean (70 frozen declarations)

```lean
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveBDraft.System
public import Mathlib.Analysis.Calculus.DSlope

/-!
# Wave B, tier B2 — regular couples and regular trees (DRAFT for author approval)

Drafts of WAVE-B v2 §2.7–§2.8 and §3.1–§3.5 (TARGET = arXiv:2311.10082v2, Def `defreg` L826–L829,
Def `defregchain` L848–L850, Prop `propstructure` L852–L869, Prop `deflink` L874–L882, Def `defcoh`
L885–L887, Defs `defencpl`/`defentree` L1126–L1140, Props `regref1`–`regref3` L1145–L1232). Builds on
the B1 carriers (`WaveB1-Core`, `WaveB1-System`). Self-contained (freeze-set closure policy, fix list 3
item 3): only frozen Wave A definitions, Mathlib and the B1 drafts; the resonant integral and its
principal value repeat the bodies of the landed `resonantIntegral` and `energyInvSliceLimit`
(`Foundations/Resonant/**`, packet N5), with bridges in the probe file.

* §1 Mini-couples and mini-trees: the code tables (WAVE-B §3.1–§3.2, figure-defs §5).
* §2 Regularity, source form: operations A and B on raw couple data and the inductive predicate
  `RawRegular` (T Def `defreg`); `IsRegularCouple`, `IsRegularTree` on the B1 carriers.
* §3 Structure data: the codes `RegCpl`/`RegChain` (legal partitions in Catalan form), the decoding
  into raw data, the predicates `RegCpl.Decodes`, `RegChain.DecodesTree` (WAVE-B §2.7 item 3).
* §4 Characterization obligations (statements, `sorry`): decoding lands in the regular objects, and
  every regular couple/tree has exactly one well-formed code (DH21 Props 4.5, 4.7, 4.8, Cor 4.9).
* §5 Links, `𝒩^ch`, dominant codes, special subsets `Z`, incoherency index (T L874–L887, L1126–L1140).
* §6 Time factors `𝒥ℬ*` (T (regref2-0)–(regref2-2)), the resonant integral `resIntegral` and its
  principal value `pvResonantIntegral` (WAVE-B §2.8), momentum factors `ℳ*` (T (regref3-0)–(regref3-4))
  and the leading terms `(K*)_app` (T (regref1-3)).
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

open TTree

/-! ## §1 Mini-couples and mini-trees -/

/-- The code of a `(1,1)`-mini-couple (T Def `defreg`, Figure `MiniCpl.png`; WAVE-B §3.1): `0` is code
`00` (straight: `L⁺ ↔ L⁻`, `R⁺ ↔ R⁻`), `1` is code `01` (crossed: `L⁺ ↔ R⁻`, `R⁺ ↔ L⁻`); always
`M⁺ ↔ M⁻`. Colours: red, green, blue = the pairs containing `L⁺`, `M⁺`, `R⁺` (first tree = the `+`
tree, figure-defs M1). -/
abbrev MiniCplCode := Fin 2

/-- The slot of the `-` tree paired with slot `x` of the `+` tree. -/
def MiniCplCode.partner (c : MiniCplCode) (x : Fin 3) : Fin 3 := if c = 0 then x else 2 - x

/-- The code of a mini-tree (T Def `defreg`, Figure `MiniTree.png`; WAVE-B §3.2, figure-defs §5): a
root `ρ` with a branching child `ν` at slot `c` (`0, 1, 2` = L, M, R; first code digit `c + 1`) and
second digit `b`. -/
structure MiniTreeCode where
  /-- the slot of the inner node `ν` under the root `ρ` -/
  c : Fin 3
  /-- the second code digit -/
  b : Fin 2

-- [held out, not frozen: MiniTreeCode.equiv, instDecidableEqMiniTreeCode, instFintypeMiniTreeCode]

namespace MiniTreeCode

/-- The slot of the lone leaf under `ν` (table of WAVE-B §3.2): codes `10, 11, 20, 21, 30, 31` give
`L, R, M, M, R, L`. -/
def lone (m : MiniTreeCode) : Fin 3 := (![![0, 2], ![1, 1], ![2, 0]] : Fin 3 → Fin 2 → Fin 3) m.c m.b

/-- The red pair `(ρ-slot, ν-slot)`: the pair containing the leftmost leaf child of `ρ`. -/
def red (m : MiniTreeCode) : Fin 3 × Fin 3 :=
  (![![(1, 2), (1, 0)], ![(0, 0), (0, 2)], ![(0, 1), (0, 1)]] : Fin 3 → Fin 2 → Fin 3 × Fin 3) m.c m.b

/-- The green pair `(ρ-slot, ν-slot)`: the pair containing the other leaf child of `ρ`. -/
def green (m : MiniTreeCode) : Fin 3 × Fin 3 :=
  (![![(2, 1), (2, 1)], ![(2, 2), (2, 0)], ![(1, 0), (1, 2)]] : Fin 3 → Fin 2 → Fin 3 × Fin 3) m.c m.b

end MiniTreeCode

/-- The sign of the child at slot `i` of a node of sign `ζ`: `(ζ, -ζ, ζ)` (T L627). -/
def slotSign (ζ : ℤˣ) (i : Fin 3) : ℤˣ := if i = 1 then -ζ else ζ

/-- The ternary node with children `f 0, f 1, f 2`. -/
def node3 (f : Fin 3 → TTree) : TTree := .node (f 0) (f 1) (f 2)

/-- The address `a` extended by the path `p`. -/
def addrExt {w : ℕ} (a : Fin w × Path) (p : Path) : Fin w × Path := (a.1, a.2 ++ p)

/-! ## §2 Regularity in source form: operations A and B (T Def `defreg`, L826–L829) -/

/-- Replace the subtree at path `p` by `S` (unchanged if `p` is not a node; only used at nodes). -/
def TTree.setAt : TTree → Path → TTree → TTree
  | _, [], S => S
  | .leaf, _ :: _, _ => .leaf
  | .node l m r, i :: p, S =>
    .node (if i = 0 then l.setAt p S else l) (if i = 1 then m.setAt p S else m)
      (if i = 2 then r.setAt p S else r)

/-- The subtree at path `p` (`•` if `p` is not a node; only used at nodes). -/
def TTree.subtreeAt : TTree → Path → TTree
  | T, [] => T
  | .leaf, _ :: _ => .leaf
  | .node l m r, i :: p => (![l, m, r] i).subtreeAt p

/-- **Raw couple data**: the `+` tree, the `-` tree, and the leaf pairs as `(+ leaf, - leaf)` addresses
(tree `0` = `𝒯⁺`, tree `1` = `𝒯⁻`). -/
abbrev RawCpl := (TTree × TTree) × List ((Fin 2 × Path) × (Fin 2 × Path))

namespace RawCpl

/-- The tree on side `j`. -/
def tree (R : RawCpl) (j : Fin 2) : TTree := if j = 0 then R.1.1 else R.1.2

/-- Apply `f` to the tree on side `j`. -/
def mapTree (R : RawCpl) (j : Fin 2) (f : TTree → TTree) : TTree × TTree :=
  if j = 0 then (f R.1.1, R.1.2) else (R.1.1, f R.1.2)

/-- **Operation A** at the leaf pair `(x, y)` (`x` the `+` leaf) with mini-couple code `c`: both leaves
become order-1 trees whose six leaves are paired as the mini-couple of code `c`, with `x` in the role
of the `+` root (T Def `defreg`; WAVE-B §3.3). -/
def opA (R : RawCpl) (x y : Fin 2 × Path) (c : MiniCplCode) : RawCpl :=
  let t3 : TTree := .node .leaf .leaf .leaf
  let R' : RawCpl := (R.mapTree x.1 (fun T => T.setAt x.2 t3), R.2)
  ((R'.mapTree y.1 (fun T => T.setAt y.2 t3)),
    R.2.erase (x, y) ++ [(addrExt x [0], addrExt y [c.partner 0]), (addrExt y [1], addrExt x [1]),
      (addrExt x [2], addrExt y [c.partner 2])])

/-- Relocate an address below `a` to below `a ++ [c, l]` (the old subtree is re-attached at the lone
leaf of the new mini-tree). -/
def relocate (a : Fin 2 × Path) (c l : Fin 3) (z : Fin 2 × Path) : Fin 2 × Path :=
  if z.1 = a.1 ∧ a.2 <+: z.2 then (z.1, a.2 ++ [c, l] ++ z.2.drop a.2.length) else z

/-- The oriented pair `(+ leaf, - leaf)` from a leaf `x` of sign `sx` and its partner `y`. -/
def orient (x : Fin 2 × Path) (sx : ℤˣ) (y : Fin 2 × Path) : (Fin 2 × Path) × (Fin 2 × Path) :=
  if sx = 1 then (x, y) else (y, x)

/-- **Operation B** at the node `a` with mini-tree code `m`: the subtree `S` at `a` is detached, `a`
becomes the root `ρ` of the mini-tree, `S` is re-attached at its lone leaf (keeping `a`'s sign), and
the mini-tree's red and green leaf pairs are new pairs (T Def `defreg`; WAVE-B §3.3, figure-defs §5:
B at a leaf keeps the leaf's pair). -/
def opB (R : RawCpl) (a : Fin 2 × Path) (m : MiniTreeCode) : RawCpl :=
  let S := (R.tree a.1).subtreeAt a.2
  let mini := node3 fun i => if i = m.c then node3 (fun k => if k = m.lone then S else .leaf) else .leaf
  let ζ : ℤˣ := nodeSign ![1, -1] a
  (R.mapTree a.1 (fun T => T.setAt a.2 mini),
    R.2.map (fun q => (relocate a m.c m.lone q.1, relocate a m.c m.lone q.2)) ++
      [orient (addrExt a [m.red.1]) (slotSign ζ m.red.1) (addrExt a [m.c, m.red.2]),
       orient (addrExt a [m.green.1]) (slotSign ζ m.green.1) (addrExt a [m.c, m.green.2])])

end RawCpl

/-- **Regular couples, source form** (T Def `defreg`): the raw data reachable from the trivial couple
`(•, •)` by finitely many operations A (at a leaf pair) and B (at a node). -/
inductive RawRegular : RawCpl → Prop
  | triv : RawRegular ((.leaf, .leaf), [((0, []), (1, []))])
  | opA {R : RawCpl} {x y : Fin 2 × Path} (c : MiniCplCode) :
      RawRegular R → (x, y) ∈ R.2 → RawRegular (R.opA x y c)
  | opB {R : RawCpl} {a : Fin 2 × Path} (m : MiniTreeCode) :
      RawRegular R → a.2 ∈ (R.tree a.1).nodes → RawRegular (R.opB a m)

/-- A list of pairs together with the swapped pairs (pairs read as unordered). -/
def symmPairs {α : Type*} (P : List (α × α)) : List (α × α) := P ++ P.map Prod.swap

/-- A couple carrier `G` has the trees `T = (𝒯⁺, 𝒯⁻)` and the leaf pairs of the list `P` (unordered). -/
def Garden.MatchesCouple (G : Garden 2) (T : TTree × TTree)
    (P : List ((Fin 2 × Path) × (Fin 2 × Path))) : Prop :=
  IsCouple G ∧ G.tree 0 = T.1 ∧ G.tree 1 = T.2 ∧
    ∀ ℓ : GLeaf G.tree, (ℓ.1, (G.pair ℓ).1) ∈ symmPairs P

-- [held out, not frozen: instDecidableMatchesCouple]

/-- A paired tree `G` of sign `ζ` seen as the couple `(𝒯, •)` (sign `+`) or `(•, 𝒯)` (sign `-`), with
the lone leaf paired with `•`, has the raw data `R`. -/
def Garden.MatchesTreeCouple (G : Garden 1) (R : RawCpl) : Prop :=
  let s : Fin 2 := if G.sig 0 = 1 then 0 else 1
  R.tree s = G.tree 0 ∧ R.tree (1 - s) = .leaf ∧
    ∀ ℓ : GLeaf G.tree,
      let z : Fin 2 × Path := (s, ℓ.1.2)
      let y : Fin 2 × Path := if G.IsLone ℓ then (1 - s, []) else (s, (G.pair ℓ).1.2)
      (z, y) ∈ symmPairs R.2

-- [held out, not frozen: instDecidableMatchesTreeCouple]

/-- **A regular couple** (T Def `defreg`). -/
def IsRegularCouple (G : Garden 2) : Prop := ∃ R : RawCpl, RawRegular R ∧ G.MatchesCouple R.1 R.2

/-- **A regular tree** (T Def `defreg`): a paired tree `𝒯` such that `(𝒯, •)` (sign `+`; `(•, 𝒯)` for
sign `-`) is a regular couple with the lone leaf paired with `•`. -/
def IsRegularTree (G : Garden 1) : Prop :=
  IsPairedTree G ∧ ∃ R : RawCpl, RawRegular R ∧ G.MatchesTreeCouple R

/-! ## §3 Structure data: codes of regular couples, regular chains and regular trees -/

mutual
/-- **Codes of regular couples** (the structure data of T Prop `propstructure`, recommended form of
WAVE-B §2.7 item 3): trivial; type 1 = a mini-couple of code `c` whose red, green, blue leaf pairs
are replaced by `Q₁, Q₂, Q₃`; type 2 = two regular chains `𝒳⁺`, `𝒳⁻` (with their couples) whose lone
leaves are paired and replaced by `Q_lp`. Well-formedness (`RegCpl.WF`) adds the uniqueness side
conditions of `propstructure` (b): `Q_lp` is trivial or of type 1 and `𝒬₀` is nontrivial. -/
inductive RegCpl : Type
  | triv : RegCpl
  | type1 (c : MiniCplCode) (Q₁ Q₂ Q₃ : RegCpl) : RegCpl
  | type2 (Xp Xm : RegChain) (Qlp : RegCpl) : RegCpl

/-- **Codes of regular chains with their couples** (T Def `defregchain`, `propstructure`): a legal
(non-crossing) partition of `{1,…,2m}` in Catalan form. `pair m Qr Qg inner rest` pairs the first chain
node `𝔫_a` with `𝔫_b`, where `inner` codes the chain nodes strictly between them and `rest` those after
`𝔫_b`; `m` is the mini-tree code of the rearrangement of `𝔫_a, 𝔫_b` (`m.c` = the slot of `𝔫_{a+1}` under
`𝔫_a`, `m.lone` = the slot of `𝔫_{b+1}` or of the lone leaf under `𝔫_b`), and its red and green leaf
pairs are replaced by `Qr = 𝒬_{j,ε,1}`, `Qg = 𝒬_{j,ε,2}`. Pairs are listed in increasing `a` (preorder),
as in T L855. -/
inductive RegChain : Type
  | nil : RegChain
  | pair (m : MiniTreeCode) (Qr Qg : RegCpl) (inner rest : RegChain) : RegChain
end

/-- The tree of a couple code on the side of sign `s` (`+`: `𝒯⁺`). -/
def treeOfSign (T : TTree × TTree) (s : ℤˣ) : TTree := if s = 1 then T.1 else T.2

mutual
/-- **Decoding, trees**: `Q.trees = (𝒯⁺, 𝒯⁻)`. -/
def RegCpl.trees : RegCpl → TTree × TTree
  | .triv => (.leaf, .leaf)
  | .type1 c Q₁ Q₂ Q₃ =>
    (.node Q₁.trees.1 Q₂.trees.2 Q₃.trees.1,
      if c = 0 then .node Q₁.trees.2 Q₂.trees.1 Q₃.trees.2
      else .node Q₃.trees.2 Q₂.trees.1 Q₁.trees.2)
  | .type2 Xp Xm Qlp => (Xp.plug 1 Qlp.trees.1, Xm.plug (-1) Qlp.trees.2)

/-- **Decoding, chains**: the tree of a chain whose root `𝔫_1` has sign `ζ`, with the subtree `h`
plugged at the lone-leaf position. -/
def RegChain.plug : RegChain → ℤˣ → TTree → TTree
  | .nil, _, h => h
  | .pair m Qr Qg inner rest, ζ, h =>
    node3 fun i =>
      if i = m.c then
        inner.plug (slotSign ζ m.c) (node3 fun k =>
          if k = m.lone then rest.plug (slotSign (slotSign ζ m.c) k) h
          else if k = m.red.2 then treeOfSign Qr.trees (slotSign (slotSign ζ m.c) k)
          else treeOfSign Qg.trees (slotSign (slotSign ζ m.c) k))
      else if i = m.red.1 then treeOfSign Qr.trees (slotSign ζ i)
      else treeOfSign Qg.trees (slotSign ζ i)
end

/-- The path of the lone leaf of a chain (from its root `𝔫_1`). -/
def RegChain.lonePath : RegChain → Path
  | .nil => []
  | .pair m _ _ inner rest => [m.c] ++ inner.lonePath ++ [m.lone] ++ rest.lonePath

mutual
/-- **Decoding, leaf pairs** `(+ leaf, - leaf)` of a couple code whose `+` tree is rooted at `a` and
`-` tree at `b`. -/
def RegCpl.pairsAt {w : ℕ} : RegCpl → (Fin w × Path) → (Fin w × Path) →
    List ((Fin w × Path) × (Fin w × Path))
  | .triv, a, b => [(a, b)]
  | .type1 c Q₁ Q₂ Q₃, a, b =>
    Q₁.pairsAt (addrExt a [0]) (addrExt b [c.partner 0]) ++
      Q₂.pairsAt (addrExt b [1]) (addrExt a [1]) ++
      Q₃.pairsAt (addrExt a [2]) (addrExt b [c.partner 2])
  | .type2 Xp Xm Qlp, a, b =>
    Xp.pairsAt 1 a ++ Xm.pairsAt (-1) b ++
      Qlp.pairsAt (addrExt a Xp.lonePath) (addrExt b Xm.lonePath)

/-- **Decoding, leaf pairs of a chain** rooted at `a` with root sign `ζ` (the lone leaf excluded). -/
def RegChain.pairsAt {w : ℕ} : RegChain → ℤˣ → (Fin w × Path) →
    List ((Fin w × Path) × (Fin w × Path))
  | .nil, _, _ => []
  | .pair m Qr Qg inner rest, ζ, a =>
    (if slotSign ζ m.red.1 = 1 then
        Qr.pairsAt (addrExt a [m.red.1]) (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2]))
      else Qr.pairsAt (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2])) (addrExt a [m.red.1])) ++
    (if slotSign ζ m.green.1 = 1 then
        Qg.pairsAt (addrExt a [m.green.1]) (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2]))
      else Qg.pairsAt (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2])) (addrExt a [m.green.1])) ++
    inner.pairsAt (slotSign ζ m.c) (addrExt a [m.c]) ++
    rest.pairsAt (slotSign (slotSign ζ m.c) m.lone) (addrExt a ([m.c] ++ inner.lonePath ++ [m.lone]))
end

/-- The decoded raw couple data of a code. -/
def RegCpl.raw (Q : RegCpl) : RawCpl := (Q.trees, Q.pairsAt (0, []) (1, []))

/-- `Q` is the structure data of the couple carrier `G`. -/
def RegCpl.Decodes (Q : RegCpl) (G : Garden 2) : Prop := G.MatchesCouple Q.trees Q.raw.2

-- [held out, not frozen: instDecidableDecodes]

/-- A paired-tree carrier `G` has the tree `T`, lone leaf at `lp` (marked `lower`) and the other leaf
pairs of the list `P`. -/
def Garden.MatchesPairedTree (G : Garden 1) (T : TTree) (lp : Path)
    (P : List ((Fin 1 × Path) × (Fin 1 × Path))) : Prop :=
  G.tree 0 = T ∧ (∀ ℓ : GLeaf G.tree, G.mark ℓ = if ℓ.1.2 = lp then some .lower else none) ∧
    ∀ ℓ : GLeaf G.tree, ℓ.1.2 ≠ lp → (ℓ.1, (G.pair ℓ).1) ∈ symmPairs P

-- [held out, not frozen: instDecidableMatchesPairedTree]

/-- **Codes of regular trees** (T Prop `propstructure`, last part): a regular tree is coded by its
regular chain `𝒳₀` with couples `𝒬_{j,0,ι}` (`nil` = the trivial tree `•`); the sign is that of the
carrier. `X` is the structure data of the paired-tree carrier `G`. -/
def RegChain.DecodesTree (X : RegChain) (G : Garden 1) : Prop :=
  G.MatchesPairedTree (X.plug (G.sig 0) .leaf) X.lonePath (X.pairsAt (G.sig 0) (0, []))

-- [held out, not frozen: instDecidableDecodesTree]

/-- Is the code of type 2? -/
def RegCpl.isType2 : RegCpl → Bool
  | .type2 .. => true
  | _ => false

/-- Is the chain empty? -/
def RegChain.isNil : RegChain → Bool
  | .nil => true
  | _ => false

mutual
/-- **Well-formedness** (the uniqueness side conditions of T Prop `propstructure` (b)): in a type 2
code, `Q_lp` is trivial or of type 1 and the couple `𝒬₀` of the two chains is nontrivial. -/
def RegCpl.wf : RegCpl → Bool
  | .triv => true
  | .type1 _ Q₁ Q₂ Q₃ => Q₁.wf && Q₂.wf && Q₃.wf
  | .type2 Xp Xm Qlp => Xp.wf && Xm.wf && Qlp.wf && !Qlp.isType2 && !(Xp.isNil && Xm.isNil)

/-- Well-formedness of a chain code (its couples are well formed). -/
def RegChain.wf : RegChain → Bool
  | .nil => true
  | .pair _ Qr Qg inner rest => Qr.wf && Qg.wf && inner.wf && rest.wf
end

mutual
/-- The order `n(𝒬)` of the decoded couple (number of branching nodes; characterization
`size_eq_order` in §4). -/
def RegCpl.size : RegCpl → ℕ
  | .triv => 0
  | .type1 _ Q₁ Q₂ Q₃ => Q₁.size + Q₂.size + Q₃.size + 2
  | .type2 Xp Xm Qlp => Xp.size + Xm.size + Qlp.size

/-- The number of branching nodes of a chain with its couples. -/
def RegChain.size : RegChain → ℕ
  | .nil => 0
  | .pair _ Qr Qg inner rest => Qr.size + Qg.size + inner.size + rest.size + 2
end

/-! ## §4 Characterization obligations (statements; proofs belong to packets C1, C2)

These fix what the codes mean: decoding lands in the regular objects of T Def `defreg`, and every
regular couple (tree) has exactly one well-formed code, i.e. the structure data are functions of the
couple (T Prop `propstructure`; DH21 Props 4.5, 4.7, 4.8, Cor 4.9). The last obligation is the counting
sentence of `propstructure` (B2-CL-8). No `Classical.choose` is used: consumers quantify over pairs
`(code, carrier)` with `Decodes`. -/

/-- Decoding a well-formed code gives a regular couple carrier. -/
theorem RegCpl.exists_decodes (Q : RegCpl) (hQ : Q.wf = true) :
    ∃ G : Garden 2, Q.Decodes G ∧ IsRegularCouple G := by
  sorry

/-- **Structure theorem, couples** (T Prop `propstructure` (a), (b)): every regular couple has exactly
one well-formed code. -/
theorem existsUnique_regCpl_decodes (G : Garden 2) (hG : IsRegularCouple G) :
    ∃! Q : RegCpl, Q.wf = true ∧ Q.Decodes G := by
  sorry

/-- Decoding a well-formed chain code gives a regular tree carrier of either sign. -/
theorem RegChain.exists_decodesTree (X : RegChain) (hX : X.wf = true) (ζ : ℤˣ) :
    ∃ G : Garden 1, G.sig 0 = ζ ∧ X.DecodesTree G ∧ IsRegularTree G := by
  sorry

/-- **Structure theorem, trees** (T Prop `propstructure`, last part). -/
theorem existsUnique_regChain_decodesTree (G : Garden 1) (hG : IsRegularTree G) :
    ∃! X : RegChain, X.wf = true ∧ X.DecodesTree G := by
  sorry

/-- The code size is the order of the decoded couple. -/
theorem RegCpl.size_eq_order (Q : RegCpl) {G : Garden 2} (h : Q.Decodes G) : G.order = Q.size := by
  sorry

-- [held out, not frozen: regular_count_le]

/-! ## §5 Links, `𝒩^ch`, dominant codes, special subsets, coherence -/

mutual
/-- **Links** of a couple code (T Prop `deflink`, L874–L882), as `(chosen, other)` pairs of branching
node addresses; the `+` tree is rooted at `a`, the `-` tree at `b`. Type 1: the two roots (the `+`
root chosen) and recursively; type 2: `(𝔫_a^ε, 𝔫_b^ε)` for every pair `{a,b} ∈ 𝒫^ε` (`𝔫_a` chosen) and
recursively. -/
def RegCpl.linksAt {w : ℕ} : RegCpl → (Fin w × Path) → (Fin w × Path) →
    List ((Fin w × Path) × (Fin w × Path))
  | .triv, _, _ => []
  | .type1 c Q₁ Q₂ Q₃, a, b =>
    (a, b) :: (Q₁.linksAt (addrExt a [0]) (addrExt b [c.partner 0]) ++
      Q₂.linksAt (addrExt b [1]) (addrExt a [1]) ++
      Q₃.linksAt (addrExt a [2]) (addrExt b [c.partner 2]))
  | .type2 Xp Xm Qlp, a, b =>
    Xp.linksAt 1 a ++ Xm.linksAt (-1) b ++
      Qlp.linksAt (addrExt a Xp.lonePath) (addrExt b Xm.lonePath)

/-- Links of a chain rooted at `a` with root sign `ζ` (and of its couples). -/
def RegChain.linksAt {w : ℕ} : RegChain → ℤˣ → (Fin w × Path) →
    List ((Fin w × Path) × (Fin w × Path))
  | .nil, _, _ => []
  | .pair m Qr Qg inner rest, ζ, a =>
    (a, addrExt a ([m.c] ++ inner.lonePath)) ::
    ((if slotSign ζ m.red.1 = 1 then
        Qr.linksAt (addrExt a [m.red.1]) (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2]))
      else Qr.linksAt (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2])) (addrExt a [m.red.1])) ++
    (if slotSign ζ m.green.1 = 1 then
        Qg.linksAt (addrExt a [m.green.1]) (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2]))
      else Qg.linksAt (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2])) (addrExt a [m.green.1])) ++
    inner.linksAt (slotSign ζ m.c) (addrExt a [m.c]) ++
    rest.linksAt (slotSign (slotSign ζ m.c) m.lone) (addrExt a ([m.c] ++ inner.lonePath ++ [m.lone])))
end

/-- The links of a couple code (trees rooted at `(0, [])`, `(1, [])`). -/
def RegCpl.links (Q : RegCpl) : List ((Fin 2 × Path) × (Fin 2 × Path)) := Q.linksAt (0, []) (1, [])

/-- The links of a tree code of sign `ζ`. -/
def RegChain.treeLinks (X : RegChain) (ζ : ℤˣ) : List ((Fin 1 × Path) × (Fin 1 × Path)) :=
  X.linksAt ζ (0, [])

/-- **`𝒩^ch`** (T Prop `deflink`, last paragraph; DH21 Def 4.11, review P6): one node of each link. -/
def chosenSet {w : ℕ} (links : List ((Fin w × Path) × (Fin w × Path))) : Finset (Fin w × Path) :=
  (links.map Prod.fst).toFinset

mutual
/-- **Dominant couple codes** (T Prop `propstructure`, L859–L860; DH21 Def 4.17): trivial; type 1 with
dominant `Q_j`; type 2 with dominant chains (`𝒫^ε = {{1,2},…}`) and dominant couples. -/
def RegCpl.dominant : RegCpl → Bool
  | .triv => true
  | .type1 _ Q₁ Q₂ Q₃ => Q₁.dominant && Q₂.dominant && Q₃.dominant
  | .type2 Xp Xm Qlp => Xp.dominant && Xm.dominant && Qlp.dominant

/-- Dominant chains: consecutive pairs `{2j-1, 2j}` (`inner = nil`) with dominant couples. A regular
tree is dominant iff its chain code is. -/
def RegChain.dominant : RegChain → Bool
  | .nil => true
  | .pair _ Qr Qg inner rest => inner.isNil && Qr.dominant && Qg.dominant && rest.dominant
end

/-- **Special subsets** (T Def `defencpl`, L1127): `Z ⊆ 𝒩^ch` such that for each `𝔫 ∈ Z` the node
linked with `𝔫` is a child of `𝔫`. -/
def IsSpecialSet {w : ℕ} (links : List ((Fin w × Path) × (Fin w × Path)))
    (Z : Finset (Fin w × Path)) : Prop :=
  ∀ z ∈ Z, ∃ i : Fin 3, (z, addrExt z [i]) ∈ links

@[instance_reducible, instance] def instDecidableIsSpecialSet {w : ℕ} (links : List ((Fin w × Path) × (Fin w × Path)))
    (Z : Finset (Fin w × Path)) : Decidable (IsSpecialSet links Z) := by
  unfold IsSpecialSet
  infer_instance

/-- The special subsets of `𝒩^ch` (a finite set). -/
def specialSets {w : ℕ} (links : List ((Fin w × Path) × (Fin w × Path))) :
    Finset (Finset (Fin w × Path)) :=
  (chosenSet links).powerset.filter (IsSpecialSet links)

/-- **The incoherency index** (T Def `defcoh`, L885–L887) of a layering w.r.t. a list of links: the
number of links `(𝔫, 𝔫')` with `𝔏_𝔫 ≠ 𝔏_𝔫'`. Coherent: index `0`. -/
def LayeredGarden.incoherency {w : ℕ} (LG : LayeredGarden w)
    (links : List ((Fin w × Path) × (Fin w × Path))) : ℕ :=
  ((Finset.univ : Finset (GBranch LG.garden.tree × GBranch LG.garden.tree)).filter fun bb =>
    (bb.1.1, bb.2.1) ∈ links ∧ LG.layer bb.1.toNode ≠ LG.layer bb.2.toNode).card

/-! ## §6 Time factors, the principal value, momentum factors and the leading terms -/

mutual
/-- **`𝒥ℬ*_𝒬(t, s)`** for a dominant couple code with all nodes in layer `r` (T Prop `regref2`,
(regref2-0), (regref2-1); route R4): trivial `1`; type 1 `2∫_r^{min(t,s)} ∏_j 𝒥ℬ*_{𝒬_j}(τ,τ) dτ`;
type 2 the iterated integral over `t > t₁ > ⋯ > t_{m₊} > r`, `s > s₁ > ⋯ > s_{m₋} > r` of the chain
couples' factors times `𝒥ℬ*_{𝒬_lp}(t_{m₊}, s_{m₋})` (`= 𝒥ℬ*_{𝒬_lp}(min(t_{m₊}, s_{m₋}))`, as `𝒬_lp` is
trivial or of type 1). Used for `t, s ∈ [r, r+1]`; values on non-dominant codes are not source
objects and are never used (`(K*)_app = 0` there). -/
noncomputable def RegCpl.JB (r : ℝ) : RegCpl → ℝ → ℝ → ℝ
  | .triv, _, _ => 1
  | .type1 _ Q₁ Q₂ Q₃, t, s => 2 * ∫ τ in r..min t s, Q₁.JB r τ τ * Q₂.JB r τ τ * Q₃.JB r τ τ
  | .type2 Xp Xm Qlp, t, s => Xp.JBchain r r t fun tm => Xm.JBchain r r s fun sm => Qlp.JB r tm sm

/-- Along a chain: `∫_{t > t₁ > ⋯ > t_m > lo} ∏_j ∏_ι 𝒥ℬ*_{𝒬_{j,ι}}(t_j, t_j) · G(t_m) dt` (pair `j`
of the chain gets the time `t_j`; `G(t)` for the empty chain). -/
noncomputable def RegChain.JBchain (r : ℝ) : RegChain → ℝ → ℝ → (ℝ → ℝ) → ℝ
  | .nil, _, t, G => G t
  | .pair _ Qr Qg _ rest, lo, t, G =>
    ∫ τ in lo..t, Qr.JB r τ τ * Qg.JB r τ τ * rest.JBchain r lo τ G
end

/-- **`𝒥ℬ*_𝒯(t, s)`** of a dominant tree code (T (regref2-2)): `∫_{t > t₁ > ⋯ > t_{m₀} > max(s, r)}
∏_j ∏_ι 𝒥ℬ*_{𝒬_{j,0,ι}}(t_j, t_j) dt`. T states (regref2-2) for `s ∈ [r, r+1]` (T L1185–L1188). For `s < r`
(the lone leaf in a lower layer `q' < r`: the box of B2.1 items (2) and (3)), the constraint `t_{m₀} > s` of the
kernel `K*_𝒯` (T Def `defkg`, L682–L684) is implied by `t_{m₀} > r`, so the lower limit is `r` (B2-CL-13, FINDINGS
F66: with lower limit `s`, items (2) and (3) were false for `q' < r`). -/
noncomputable def RegChain.JBtree (r : ℝ) (X : RegChain) (t s : ℝ) : ℝ := X.JBchain r (max s r) t fun _ => 1

/-- **The resonant integral** `∫ δ(k₁-k₂+k₃-k) δ(|k₁|²-|k₂|²+|k₃|²-|k|²) Ψ(k₁,k₂,k₃) dk` (T (regref3-0),
(regref3-3) with `𝙸 = 0`; WAVE-B §2.8), in the parametrization and hyperplane normalization of the
frozen `collisionOp` (`k₁ = k+ℓ`, `k₃ = k+w`, `k₂ = k+ℓ+w`, `w ⊥ ℓ`). Same body as the landed
`resonantIntegral` (bridge `resIntegral_eq_resonantIntegral`); `collisionOp` is a special case. -/
noncomputable def resIntegral {d : ℕ} (Ψ : Mom d → Mom d → Mom d → ℝ) (k : Mom d) : ℝ :=
  ∫ ℓ : Mom d, (2 * ‖ℓ‖)⁻¹ * ∫ w : ↥(ℝ ∙ ℓ)ᗮ, Ψ (k + ℓ) (k + ℓ + w) (k + w)

/-- The slice integral `S_ℓ(t) = ∫_{w ⊥ ℓ} Ψ(k+ℓ, k+ℓ+x, k+x)`, `x = t ℓ/|ℓ| + w`, of the kernel
on the hyperplanes `⟨ℓ, x⟩ = t|ℓ|`. -/
noncomputable def resSlice {d : ℕ} (Ψ : Mom d → Mom d → Mom d → ℝ) (k ℓ : Mom d) (t : ℝ) : ℝ :=
  ∫ w : ↥(ℝ ∙ ℓ)ᗮ, Ψ (k + ℓ) (k + ℓ + (t • (‖ℓ‖⁻¹ • ℓ) + w)) (k + (t • (‖ℓ‖⁻¹ • ℓ) + w))

/-- **The principal-value resonant integral** `p.v.∫ δ(k₁-k₂+k₃-k) Ψ(k₁,k₂,k₃)/Ω dk` with
`Ω = |k₁|²-|k₂|²+|k₃|²-|k|² = -2⟨ℓ, x⟩` (T (regref3-3), `𝙸 = 1`; WAVE-B §2.8) in the `collisionOp`
parametrization: the absolutely convergent symmetric-quotient form
`∫_ℓ -(2|ℓ|)^{-1} ∫_t (S_ℓ(t) - S_ℓ(-t)) / (2t) dt`. Same body as the landed
`∫ ℓ, energyInvSliceLimit (resonantKernel Ψ k) ℓ` (bridge `pvResonantIntegral_eq_energyInv`); it is
the cutoff limit `lim_{μ→∞} ∫∫ Ψ (1 - χ(μΩ))/Ω` for every admissible cutoff `χ`, for every kernel with
`DeltaKernel` decay of itself and its gradient, with no support radius: characterization
`tendsto_pvResonantIntegral_of_decay` (`WaveB2-Regular-probes.lean`; FINDINGS F66, independent audit F-5,
B2-CL-19), proved from the landed `Resonant.tendsto_energyInvIntegral_of_decay` (`Foundations/Resonant/PVDecay`,
wt-ansob). The compactly supported case is `tendsto_pvResonantIntegral`. -/
noncomputable def pvResonantIntegral {d : ℕ} (Ψ : Mom d → Mom d → Mom d → ℝ) (k : Mom d) : ℝ :=
  ∫ ℓ : Mom d, -(2 * ‖ℓ‖)⁻¹ *
    ∫ t : ℝ, 2⁻¹ * dslope (fun v => resSlice Ψ k ℓ v - resSlice Ψ k ℓ (-v)) 0 t

mutual
/-- **`ℳ*_{(𝒬,Z)}(k)[F]`** for a dominant couple code placed with its `+` tree at `a` and `-` tree at
`b` (T Prop `regref3`): trivial `F(k)`; type 1 (regref3-0) the resonant integral of
`∏_j ℳ*_{𝒬_j}(k_j)`; type 2 (regref3-1) `ℳ*_{𝒬_lp}(k) ∏_{ε,j} 𝒩*_{(j,ε)}(k)`. `Z` is a set of node
addresses (the special subset). -/
noncomputable def RegCpl.Mstar {d w : ℕ} (F : Mom d → ℝ) (Z : Finset (Fin w × Path)) :
    RegCpl → (Fin w × Path) → (Fin w × Path) → Mom d → ℝ
  | .triv, _, _ => F
  | .type1 c Q₁ Q₂ Q₃, a, b => fun k => resIntegral (fun k₁ k₂ k₃ =>
      Q₁.Mstar F Z (addrExt a [0]) (addrExt b [c.partner 0]) k₁ *
        Q₂.Mstar F Z (addrExt b [1]) (addrExt a [1]) k₂ *
        Q₃.Mstar F Z (addrExt a [2]) (addrExt b [c.partner 2]) k₃) k
  | .type2 Xp Xm Qlp, a, b => fun k =>
      Qlp.Mstar F Z (addrExt a Xp.lonePath) (addrExt b Xm.lonePath) k *
        Xp.Nstar F Z 1 a k * Xm.Nstar F Z (-1) b k

/-- **`∏_j 𝒩*_{(j,ε)}(k)`** along a chain rooted at `a` with root sign `ζ` (T (regref3-2)–(regref3-4)):
`𝒩*_{(j,ε)}(k) = ∫ δ(k₁-k₂+k₃-k)·(Factor 1)·(Factor 2)`, Factor 1 `= δ(Ω)` if `𝔫_a ∉ Z` (`𝙸 = 0`) and
`p.v. 1/Ω` if `𝔫_a ∈ Z` (`𝙸 = 1`); Factor 2 `= ℳ*_{𝒳_{j,1}}(k_x) ℳ*_{𝒳_{j,2}}(k_y)` with `x < y` the
positions of the two leaf children of `𝔫_a` in the rearranged mini-tree (red at `x`, green at `y`):
`(k₂, k₃)`, `(k₁, k₃)`, `(k₁, k₂)` for `𝚌 = 1, 2, 3` (T (regref3-4)). -/
noncomputable def RegChain.Nstar {d w : ℕ} (F : Mom d → ℝ) (Z : Finset (Fin w × Path)) :
    RegChain → ℤˣ → (Fin w × Path) → Mom d → ℝ
  | .nil, _, _ => fun _ => 1
  | .pair m Qr Qg inner rest, ζ, a => fun k =>
    let Mr : Mom d → ℝ := if slotSign ζ m.red.1 = 1 then
        Qr.Mstar F Z (addrExt a [m.red.1]) (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2]))
      else Qr.Mstar F Z (addrExt a ([m.c] ++ inner.lonePath ++ [m.red.2])) (addrExt a [m.red.1])
    let Mg : Mom d → ℝ := if slotSign ζ m.green.1 = 1 then
        Qg.Mstar F Z (addrExt a [m.green.1]) (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2]))
      else Qg.Mstar F Z (addrExt a ([m.c] ++ inner.lonePath ++ [m.green.2])) (addrExt a [m.green.1])
    let Ψ : Mom d → Mom d → Mom d → ℝ := fun k₁ k₂ k₃ =>
      Mr (![k₁, k₂, k₃] m.red.1) * Mg (![k₁, k₂, k₃] m.green.1)
    (if a ∈ Z then pvResonantIntegral Ψ k else resIntegral Ψ k) *
      inner.Nstar F Z (slotSign ζ m.c) (addrExt a [m.c]) k *
      rest.Nstar F Z (slotSign (slotSign ζ m.c) m.lone)
        (addrExt a ([m.c] ++ inner.lonePath ++ [m.lone])) k
end

/-- `ζ(𝒢) = ∏_{𝔫 ∈ 𝒩} (i ζ_𝔫)` over the branching nodes of trees `T j` with root signs `σ j`. -/
noncomputable def zetaOfTrees {w : ℕ} (σ : Fin w → ℤˣ) (T : Fin w → TTree) : ℂ :=
  ∏ j, ∏ p ∈ (T j).branching, (Complex.I * (((pathSign (σ j) p : ℤˣ) : ℤ) : ℂ))

/-- The weight `∏_{𝔫 ∈ Z} (−ζ_𝔫 π i)^{-1}` of a special subset (node signs from the root signs `σ`), for couples
and trees (F61, B2-CL-11).

TARGET (regref1-3) writes `∏_{𝔫∈Z} (ζ_𝔫 π i)^{-1}` and states that `𝒥ℬ*` does not depend on `Z`; that comes from
DH21 Lemma 7.3 (L1737). The source has a sign error there: the `χ_∞` part of `I_{εα}I_{μ−εα}` is
`−χ_∞(α)/(επiα)·I_μ`, as in DH21 Lemma 5.8's own term II and in the landed Lean `iker_comp_decompP`
(`Foundations/ClassJR/Lemma58.lean`, `T₀ = −I_μ`). DH21 sets `ε_j = ζ_𝔫`, and the `Ω` convention does not
compensate. So the `Z`-coefficient of a dominant couple is `(−1)^{|Z|}` times the `Z`-independent `𝒥ℬ*`. The
per-couple leading term therefore carries `∏_{𝔫∈Z} (−1)/(ζ_𝔫 π i)`. The sum over an equivalence class
(Prop 7.8, (regref2-3)) and the WKE identification (regref1-5) are unaffected, since `|Z|` is constant on a class.
Trace: `/home/scott/wt-scratch/wke/F61-sign-trace.md` (wt-wke). Ruling: F61 CONFIRMED (orchestrator, 2026-11-04).
Probe `specialWeight_eq_neg_one_pow_mul_old`: the new weight is `(−1)^{|Z|}` times the old one. -/
noncomputable def specialWeight {w : ℕ} (σ : Fin w → ℤˣ) (Z : Finset (Fin w × Path)) : ℂ :=
  ∏ z ∈ Z, (-((((nodeSign σ z : ℤˣ) : ℤ) : ℂ) * Real.pi * Complex.I))⁻¹

/-- **The leading term `(K*_𝒬)_app(t, s, k)`** of a couple code with all nodes in layer `r` and input
`F = F_r` (T (regref1-3); WAVE-B §2.7 item 9, route R4, deviation D1 of B2.1):
`2^{-2n} δ^n ζ(𝒬) ∑_{Z special} ∏_{𝔫 ∈ Z} (−ζ_𝔫 π i)^{-1} 𝒥ℬ*_𝒬(t,s) ℳ*_{(𝒬,Z)}(k)[F]` for dominant
codes (`2n = n(𝒬)`), and `0` for non-dominant codes (T: non-dominant couples have no leading term).
Deviation (F61, B2-CL-11): the weight is `(−ζ_𝔫 π i)^{-1}` (`specialWeight`), not T's `(ζ_𝔫 π i)^{-1}`. -/
noncomputable def RegCpl.app {d : ℕ} (δ r : ℝ) (F : Mom d → ℝ) (Q : RegCpl) (t s : ℝ)
    (k : Mom d) : ℂ :=
  if Q.dominant then
    ((2 : ℂ)⁻¹ ^ Q.size * (δ : ℂ) ^ (Q.size / 2) *
      zetaOfTrees ![1, -1] ![Q.trees.1, Q.trees.2]) *
      ∑ Z ∈ specialSets Q.links, specialWeight ![1, -1] Z * (Q.JB r t s : ℂ) *
        (Q.Mstar F Z (0, []) (1, []) k : ℂ)
  else 0

/-- **The leading term `(K*_𝒯)_app(t, s, k)`** of a tree code of sign `ζ` with all nodes except the
lone leaf in layer `r` (T (regref1-3), second line; (regref3-1-1)): `ℳ*_𝒯 = ∏_j 𝒩*_{(j,0)}`. Deviation (F61,
B2-CL-11): as for couples, the special-subset weight is `∏_{𝔫∈Z} (−ζ_𝔫 π i)^{-1}` (`specialWeight`). -/
noncomputable def RegChain.app {d : ℕ} (δ r : ℝ) (F : Mom d → ℝ) (X : RegChain) (ζ : ℤˣ)
    (t s : ℝ) (k : Mom d) : ℂ :=
  if X.dominant then
    ((2 : ℂ)⁻¹ ^ X.size * (δ : ℂ) ^ (X.size / 2) * zetaOfTrees ![ζ] ![X.plug ζ .leaf]) *
      ∑ Z ∈ specialSets (X.treeLinks ζ), specialWeight ![ζ] Z * (X.JBtree r t s : ℂ) *
        (X.Nstar F Z ζ (0, []) k : ℂ)
  else 0

end WaveTurbulence
```

### WaveB2-Molecules.lean (no frozen declarations)

Every declaration of this file is held out (CL-20, unchanged by CL-22): the molecule layer and the characterization lemma `Garden.isMolecule_molecule` are not frozen. CL-21 (vine (II) from one rung, F72) changed only this file's `VineType.template`.

### WaveB2-Statements.lean (6 frozen declarations)

```lean
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveB2Draft.Molecules

/-!
# Wave B, tier B2 — statements (DRAFT for author approval)

The tier-B2 anchors of WAVE-B v2 §4.11–§4.13. Every statement ends in `:= by sorry` (drafts); each
docstring names its source lines and lists its deviations; `DESIGN.md` §3 argues the design items.

* B2.1 `regularAsymptotics` (T Prop `regref1` with `regref2`, `regref3`; L1145–L1232; F11; order range
  up to `N_{p+1}^4`, F33 route R14).
* B2.2 `incoherentDecay` (T Prop `proplayer1`, L953–L956).
* B2.3 `rigidity` (T Prop `lgmolect`, L2192–L2200; DH23 Prop 9.6) in an **abstract** form: a connected
  labelled molecule with the structural conclusions of T Prop `finalmol` and an admissible decoration
  set with the properties the cutting process guarantees (design item, DESIGN §3.3).

Inputs: the remainders are real with `‖R_r‖_{𝔖^{40d,40d}} ≤ L^{-θ_r}` (finite smoothness, forced by the
norm; WAVE-B B2.1/B2.2 "C^∞" replaced per delta-stage-3 O3 / stage-3 R1 option B).
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

open TTree

/-- The time box `ℬ = [q, q+1] × [q', q'+1]` of pairs `(t, s)`. -/
def timeBox (q q' : ℝ) : Set (Fin 2 → ℝ) := {ts | ts 0 ∈ Icc q (q + 1) ∧ ts 1 ∈ Icc q' (q' + 1)}

/-- The time box `([q, q+1] × [q', q'+1]) ∩ {t > s}` of regular trees. -/
def timeBoxGt (q q' : ℝ) : Set (Fin 2 → ℝ) := {ts | ts ∈ timeBox q q' ∧ ts 1 < ts 0}

/-- The input-remainder hypothesis of B2.1/B2.2: `R` real with `‖R‖_{𝔖^{40d,40d}} ≤ L^{-θ_r}` (T L1033,
(ansatz2) with `Λ_p` replaced by `40d`). -/
def InputRemainder (P : WTParams) (R : Mom P.d → ℝ) (r : ℕ) : Prop :=
  SNormR (40 * P.d) (40 * P.d) R ≤ ENNReal.ofReal (P.L ^ (-P.theta r))

/-- The bound `C₁ (C₁δ)^n L^{-(γ₁ - √η) g}` of B2.1/B2.2. -/
noncomputable def regBound (P : WTParams) (n g : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (P.C₁ * (P.C₁ * P.δ) ^ n * P.L ^ (-(P.gamma1 - Real.sqrt P.η) * g))

/-! ## B2.1 `regularAsymptotics` -/

/-- **B2.1 `regularAsymptotics`** (T Props `regref1`–`regref3`, L1145–L1232; F11; WAVE-B v2 §4.11).
Under (Π), for `0 ≤ p < 𝔇`, `0 ≤ r ≤ p`, a remainder `R_r` with `‖R_r‖_{𝔖^{40d,40d}} ≤ L^{-θ_r}`, inputs
`F_r = φ(δr) + R_r` and every `n ≤ N_{p+1}^4`:
1. for every well-formed couple code `𝒬` of order `2n` and every layered couple decoded by it with all
   nodes in layer `r`: `‖K*_𝒬 - (K*_𝒬)_app‖_{𝔛^{η,30d,30d}([r,r+1]²)} ≤ C₁(C₁δ)^n L^{-(γ₁-√η)}`
   (for non-dominant `𝒬`, `(K*_𝒬)_app = 0`: this is the bound on `K*_𝒬` itself);
2. for every well-formed tree code `𝒯` of order `2n` and every layered paired tree decoded by it with all
   nodes except the lone leaf in layer `r` and the lone leaf in layer `q' ≤ r`: the same bound for
   `K*_𝒯 - (K*_𝒯)_app` in `𝔛^{η,30d,0}(([r,r+1]×[q',q'+1]) ∩ {t > s})`;
3. for dominant codes and special `Z`: `‖𝒥ℬ*‖_{𝔛^{1-η}(ℬ)} ≤ C₁C₁^n` and `‖ℳ*‖_{𝔖^{30d,30d}} ≤ C₁C₁^n`
   (trees: `𝔛^{1-η}(ℬ_𝒯)`, `𝔖^{30d,0}`); both are real valued by definition;
4. (regref1-5 corrected, F11) if `r = p` and `R_p = 0`: for `t ∈ [p, p+1]`, `k ∈ ℝ^d`,
   `∑_{𝒬 dominant, n(𝒬) = 2n} (K*_𝒬)_app(t,t,k) = 𝒰^{(p)}_n(t,k)` (a finite sum, probe
   `finite_dominant_codes`).
Deviations: (D1) `(K*)_app` is defined by the explicit recursions (route R4; `RegCpl.app`); the source's
"`𝒥ℬ*` depends only on `𝒬`" is then a definition, its agreement with DH21's construction DH21 Props 7.5,
7.7; (D2) `ℬ` for trees as stated (F11); (D3) item 4 with `app`, not `K*` (F11); (D4) regular objects are
quantified as pairs (code, carrier) with `Decodes` (structure data = the unique code,
`existsUnique_regCpl_decodes`); (D5) inputs with finite `𝔖^{40d,40d}` norm instead of `C^∞` (O3); (D6) the
order range `n ≤ N_{p+1}^4` (F33, route R14; the main proof risk); (D7) the special-subset weight of
`(K*)_app` is `∏_{𝔫∈Z} (−ζ_𝔫 π i)^{-1}`, not T (regref1-3)'s `(ζ_𝔫 π i)^{-1}` (F61, confirmed: DH21 Lemma 7.3
sign error; trace `/home/scott/wt-scratch/wke/F61-sign-trace.md`; B2-CL-11). Item 4 is unaffected, since `|Z|`
is constant on each equivalence class. -/
theorem regularAsymptotics : WTPrefix fun P =>
    ∀ p : ℕ, p < P.D → ∀ r : ℕ, r ≤ p → ∀ R : Mom P.d → ℝ, InputRemainder P R r →
    ∀ n : ℕ, n ≤ P.N (p + 1) ^ 4 →
      let F : Mom P.d → ℝ := fun k => P.φ (P.δ * r) k + R k
      -- (1) regular couples
      (∀ Q : RegCpl, Q.wf = true → Q.size = 2 * n → ∀ LG : LayeredGarden 2, Q.Decodes LG.garden →
        (∀ a, LG.layer a = r) →
        XNormRestr P.η (30 * P.d) (30 * P.d) (timeBox r r) Set.univ
          (fun ts k => KQstar P.L P.γ P.δ (fun _ => F) LG (ts 0) (ts 1) k -
            Q.app P.δ r F (ts 0) (ts 1) k) ≤ regBound P n 1) ∧
      -- (2) regular trees
      (∀ X : RegChain, X.wf = true → X.size = 2 * n → ∀ LG : LayeredGarden 1,
        X.DecodesTree LG.garden → ∀ q' : ℕ, q' ≤ r →
        (∀ a : GNode LG.garden.tree, LG.layer a = if a.1.2 = X.lonePath then q' else r) →
        XNormRestr P.η (30 * P.d) 0 (timeBoxGt r q') Set.univ
          (fun ts k => KTstar P.L P.γ P.δ (fun _ => F) LG (ts 0) (ts 1) k -
            X.app P.δ r F (LG.garden.sig 0) (ts 0) (ts 1) k) ≤ regBound P n 1) ∧
      -- (3) the factors
      (∀ Q : RegCpl, Q.wf = true → Q.dominant = true → Q.size = 2 * n →
        XNorm00Restr (V := Unit) (1 - P.η) (timeBox r r) Set.univ
            (fun ts _ => (Q.JB r (ts 0) (ts 1) : ℂ)) ≤ ENNReal.ofReal (P.C₁ * P.C₁ ^ n) ∧
          ∀ Z ∈ specialSets Q.links,
            SNormR (30 * P.d) (30 * P.d) (Q.Mstar F Z (0, []) (1, [])) ≤
              ENNReal.ofReal (P.C₁ * P.C₁ ^ n)) ∧
      (∀ X : RegChain, X.wf = true → X.dominant = true → X.size = 2 * n → ∀ ζ : ℤˣ,
        ∀ q' : ℕ, q' ≤ r →
        XNorm00Restr (V := Unit) (1 - P.η) (timeBoxGt r q') Set.univ
            (fun ts _ => (X.JBtree r (ts 0) (ts 1) : ℂ)) ≤ ENNReal.ofReal (P.C₁ * P.C₁ ^ n) ∧
          ∀ Z ∈ specialSets (X.treeLinks ζ),
            SNormR (30 * P.d) 0 (X.Nstar F Z ζ (0, [])) ≤ ENNReal.ofReal (P.C₁ * P.C₁ ^ n)) ∧
      -- (4) the WKE identity (corrected regref1-5)
      (r = p → (∀ k, R k = 0) → ∀ t ∈ Icc (p : ℝ) (p + 1), ∀ k : Mom P.d,
        ∑ᶠ (Q : RegCpl) (_ : Q.wf = true ∧ Q.dominant = true ∧ Q.size = 2 * n),
            Q.app P.δ p F t t k =
          (wkeTaylorTerm (P.φ (P.δ * p)) P.δ p n t k : ℂ)) := by
  sorry

/-! ## B2.2 `incoherentDecay` -/

/-- **B2.2 `incoherentDecay`** (T Prop `proplayer1`, L953–L956, with the standing assumptions of
L946–L951; WAVE-B v2 §4.12). Under (Π), for `0 ≤ p < 𝔇`, remainders `R_q` (`q ≤ p`) with
`‖R_q‖_{𝔖^{40d,40d}} ≤ L^{-θ_q}`, inputs `F_q = φ(δq) + R_q` and every `n ≤ N_{p+1}^4`:
1. for every well-formed couple code of order `2n` and layered couple decoded by it, with all layers
   `≤ p`, roots in layers `≤ q` and `≤ q'` (`q, q' ≤ p`, T Def `defkg`), and incoherency index `g ≥ 1`:
   `‖K*_𝒬‖_{𝔛^{η,30d,30d}([q,q+1]×[q',q'+1])} ≤ C₁(C₁δ)^n L^{-(γ₁-√η)g}`;
2. for every well-formed tree code of order `2n` and layered paired tree decoded by it, with all layers
   `≤ p`, root layer `≤ q`, lone leaf in layer `q' ≤ q ≤ p` and `g ≥ 1`: the same bound for `K*_𝒯` in
   `𝔛^{η,30d,0}(([q,q+1]×[q',q'+1]) ∩ {t > s})`.
Deviations: (D1) arbitrary layerings (TARGET's standing assumption does not use canonicity for `g ≥ 1`;
to be confirmed by packet L2); (D2) as B2.1 (D4)–(D6). -/
theorem incoherentDecay : WTPrefix fun P =>
    ∀ p : ℕ, p < P.D → ∀ R : ℕ → Mom P.d → ℝ, (∀ q ≤ p, InputRemainder P (R q) q) →
    ∀ n : ℕ, n ≤ P.N (p + 1) ^ 4 →
      -- (1) regular couples
      (∀ Q : RegCpl, Q.wf = true → Q.size = 2 * n → ∀ LG : LayeredGarden 2, Q.Decodes LG.garden →
        (∀ a, LG.layer a ≤ p) → ∀ q q' : ℕ, q ≤ p → q' ≤ p →
        LG.layer (GNode.root LG.garden.tree 0) ≤ q → LG.layer (GNode.root LG.garden.tree 1) ≤ q' →
        1 ≤ LG.incoherency Q.links →
        XNormRestr P.η (30 * P.d) (30 * P.d) (timeBox q q') Set.univ
          (fun ts k => KQstar P.L P.γ P.δ (inputsF P R) LG (ts 0) (ts 1) k) ≤
          regBound P n (LG.incoherency Q.links)) ∧
      -- (2) regular trees
      (∀ X : RegChain, X.wf = true → X.size = 2 * n → ∀ LG : LayeredGarden 1,
        X.DecodesTree LG.garden → (∀ a, LG.layer a ≤ p) → ∀ q q' : ℕ, q' ≤ q → q ≤ p →
        LG.layer (GNode.root LG.garden.tree 0) ≤ q →
        (∀ a : GNode LG.garden.tree, a.1.2 = X.lonePath → LG.layer a = q') →
        1 ≤ LG.incoherency (X.treeLinks (LG.garden.sig 0)) →
        XNormRestr P.η (30 * P.d) 0 (timeBoxGt q q') Set.univ
          (fun ts k => KTstar P.L P.γ P.δ (inputsF P R) LG (ts 0) (ts 1) k) ≤
          regBound P n (LG.incoherency (X.treeLinks (LG.garden.sig 0)))) := by
  sorry

-- [B2.3 section held out, not frozen: AtomLabel.IsAlpha, Molecule.ABLinked, Molecule.DecorationHyp, Molecule.FinalShape, Molecule.IsConnected, Molecule.IsPerfect, Molecule.IsTame, Molecule.alphaFactor, Molecule.epsDefect, Molecule.numBeta, Molecule.perfectIndicator, Molecule.rigidityRHS, rigidity]
end WaveTurbulence
```

