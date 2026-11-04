# Wave B tier B2: handoff for the independent B2 audit (Task 20)

Prepared by `wt-orch`. Date: 2026-11-04. **This is not an audit.** It lists every change to the B2 drafts since my
stage-2/3 audit (`WaveB2-stage23.md`, Task 9b), with before and after, for the independent auditor.

**Authorship.**
- B2-CL-1 to B2-CL-4: wt-gauss-hc. CL-4 is the ladder-disjointness port.
- **B2-CL-5 to B2-CL-11: wt-orch** (Tasks 19–20). wt-orch therefore must not audit CL-5 to CL-11.
- CL-2 and CL-3 (wt-gauss-hc) implement findings from my audits Task 14c and DEGEN-F53.

## 1. Baseline and current state

**Baseline.** `/home/scott/wt-scratch/waveb2-snap-1/stage23/`; its `SHA256SUMS` verify. It was audited in
`WaveB2-stage23.md`; stage 1 in `WaveB2-stage1.md`.

**Current.** `/home/scott/wt-scratch/waveb2/`, as of this file (2026-11-04, after B2-CL-12; the table was updated
for CL-12).

**B1 base.** Wave B snapshot 6 (`/home/scott/wt-scratch/waveb-snap-6`, audited in `WaveB-snapshot6.md`).

| File | Baseline sha256 | Current sha256 | Changed by |
|---|---|---|---|
| `WaveB2-Molecules.lean` | `cfd93a0842af…` | `58fe0545f105…` | CL-1 (undone by CL-12), CL-3 (via CL-2), CL-4, CL-5, CL-6, CL-7, CL-12 |
| `WaveB2-Molecules-probes.lean` | `d690f9deb83c…` | `9f8aa52a3afa…` | CL-3, CL-5, CL-7, CL-9, CL-12 |
| `WaveB2-Regular.lean` | `ad72ce4be39e…` | `6481afd99386…` | CL-8, CL-11 |
| `WaveB2-Regular-probes.lean` | `0bfef42fd8ca…` | `84a2e952c52f…` | CL-10, CL-11 |
| `WaveB2-Statements.lean` | `e50aaa9418da…` | `fcad6a08d100…` | CL-11 (docstring only) |
| `WaveB2-Statements-probes.lean` | `3ab2ec2b60e1…` | `3ab2ec2b60e1…` | unchanged |
| `WaveB2-Ladders.lean` | — | `1e5458ba0e9b…` | CL-4 (new file, not for freezing) |
| `DESIGN.md` | `2d147042…` | `3ed85d327bf3…` | changelog CL-1 to CL-12; memo lines 126, 171–174, 189–192, 217–218 |

**Complete hunk map.** `diff` of baseline → current, every hunk attributed:
- **Molecules:**
  - `8a9` → CL-1 (`import WaveBDraft.Lemmas`);
  - `118,119c119,130` · `123c134` · `125,127c136,155` → CL-5;
  - `224,226c252,259` → CL-6;
  - `293,297c326,340` · `303,304c346` → CL-3 (IsLadder; CL-2 was an intermediate state);
  - `315c357,359` → CL-4 (the `maximalLadders` docstring);
  - `484,485c528,540` → CL-7.
- **Molecules-probes:** `23c23,30` → module docstring (CL-5, CL-7, CL-9); `77c84,94` → CL-5 (`doubleBond_block`);
  `150a168,461` → CL-3 (`chordLadder`), CL-9 (`dblRail`), CL-5 (F57 + MOLE bridge), CL-7 (deviation).
- **Regular:** `364,365c364,366` · `391a393,409` → CL-8; `567c585,596` · `569c598` · `573,574c602,604` ·
  `585c615,616` → CL-11.
- **Regular-probes:** `35a36,37` → CL-10; `148a151,177` → CL-11.
- **Statements:** `72c72,75` → CL-11 (B2.1 deviation (D7), docstring).

**No hunk is unattributed.** CL-12 (§2 below) adds Molecules hunks:
- the `8a9` import hunk disappears; Molecules no longer imports `WaveBDraft.Lemmas`;
- `GNode.parent` gets its inline proof; the three helper theorems and `units_ne_one_iff_eq_neg_one` are removed;
- `Garden.molecule` gets inline facts;
- the two `deriving DecidableEq` clauses become explicit instances.

It also adds the moved theorems to Molecules-probes.

## 2. The changes, one by one

### B2-CL-1 (wt-gauss-hc): B1's lemmas moved; Molecules imports `WaveBDraft.Lemmas`

- **Before:** no such import.
- **After:** `public import WaveBDraft.Lemmas`.
- `TTree.dropLast_mem_branching`, a theorem in Molecules used by the **definition** `GNode.parent` (§3, the
  garden molecule), calls `TTree.branching_of_append_mem` from the non-frozen `WaveB1-Lemmas.lean`.
- **Auditor:** the DESIGN entry plans to inline this proof into `GNode.parent` when B2 is packaged, as B1 CL-17 did.
  **It has not been done yet.** Under B1's closure policy ("no frozen declaration uses a proved theorem of the
  project"), this is a freeze blocker for `GNode.parent` / `Garden.molecule`.

### B2-CL-2 (wt-gauss-hc), superseded by CL-3: `IsLadder` with dart-pair rails

- **Before (baseline):** the induced predicate.

  ```lean
  def IsLadder {m : ℕ} (u v : Fin (m + 1) → V) : Prop :=
    1 ≤ m ∧ Function.Injective (Sum.elim u v) ∧ (∀ j, u j ∈ M.atoms ∧ v j ∈ M.atoms) ∧
      (∀ j, M.bondsBetween (u j) (v j) = 2) ∧
      (∀ j : Fin m, M.bondsBetween (u j.castSucc) (u j.succ) = 1 ∧
        M.bondsBetween (v j.castSucc) (v j.succ) = 1 ∧
        (M.Directed (u j.castSucc) (u j.succ) ↔ M.Directed (v j.succ) (v j.castSucc))) ∧
      Multiset.card (M.groupBonds ((Finset.univ.image u) ∪ (Finset.univ.image v))) = 4 * m + 2
  ```

- **CL-2 state (intermediate):** the last two clauses were replaced by
  `∀ j : Fin m, ∃ x y : D, M.atom x = u j.castSucc ∧ M.atom (M.mate x) = u j.succ ∧ M.atom y = v j.succ ∧
  M.atom (M.mate y) = v j.castSucc ∧ M.out x = M.out y`.
  - This dropped the induced count (correct, F53), but also the rails' multiplicity 1.
  - My Task 14c kernel witness `dblRail` (a double rail) was accepted.
- **Not in the current file.**

### B2-CL-3 (wt-gauss-hc): `IsLadder` = wt-ansob's `Degen.SourceLadder` (F53)

- **After:**

  ```lean
  def IsLadder {m : ℕ} (u v : Fin (m + 1) → V) : Prop :=
    1 ≤ m ∧ Function.Injective (Sum.elim u v) ∧ (∀ j, u j ∈ M.atoms ∧ v j ∈ M.atoms) ∧
      (∀ j, M.bondsBetween (u j) (v j) = 2) ∧
      (∀ j : Fin m, M.bondsBetween (u j.castSucc) (u j.succ) = 1 ∧
        M.bondsBetween (v j.castSucc) (v j.succ) = 1 ∧
        (M.Directed (u j.castSucc) (u j.succ) ↔ M.Directed (v j.succ) (v j.castSucc)))
  ```

  That is, the baseline minus the `groupBonds` conjunct. The docstring is rewritten (selected rung and rail bonds;
  chords between end atoms allowed).
- **Meaning change.** `maximalLadders`, `numLadders`, `numFree`, `rho`, `countA`, B2.3 `rigidity` (via `countA`
  and `rho`) and the `ladderScale`/`ladderGap` clauses of `DecorationHyp` all inherit the new predicate. Their
  texts are unchanged.
- **Probes.** `chordLadder` (verbatim from wt-ansob) with `_isMolecule`, `_isLadder`, `_groupBonds`,
  `_isLadderSet_univ`, `_maximalLadders`, `_left_right_not_maximal`.
- **Evidence (mine; the independent auditor should recheck).** `DEGEN-F53.md` §re-check: the body is identical to
  `Degen.SourceLadder`. Under the old predicate the maximal ladders overlap on `chordLadder`; under the new one they
  are pairwise disjoint (wt-ansob, standard axioms).

### B2-CL-4 (wt-gauss-hc): new file `WaveB2-Ladders.lean` (not for freezing); `maximalLadders` docstring

- **Main theorem:** `Molecule.maximalLadders_pairwiseDisjoint (M) (hM : M.IsMolecule)`.
- **Provenance:** a port of wt-ansob's `MaximalLadderDisjoint.lean` and helpers, plus wt-mole's `deg_le_four` and
  friends. The source sha256 values are in the file header. I have not audited it.
- **The `maximalLadders` docstring.**
  - Before: "…not contained in the atom set of a larger ladder."
  - After: it adds the citation of the disjointness theorem.

### B2-CL-5 (wt-orch): blocks are connected; hyper-blocks through a connected adjoint (F57)

**Before (baseline):** a degree-only predicate, with a `Decidable` instance.

```lean
def IsBlock (S : Finset V) (j₁ j₂ : V) : Prop :=
  S ⊆ M.atoms ∧ j₁ ∈ S ∧ j₂ ∈ S ∧ j₁ ≠ j₂ ∧
    M.outIn S j₁ = 1 ∧ M.inIn S j₁ = 1 ∧ M.outIn S j₂ = 1 ∧ M.inIn S j₂ = 1 ∧
    ∀ v ∈ S, v ≠ j₁ → v ≠ j₂ → M.degIn S v = 4

instance (S : Finset V) (j₁ j₂ : V) : Decidable (M.IsBlock S j₁ j₂) := by
  unfold IsBlock
  infer_instance
```

**After:**

```lean
def GroupConnected (S : Finset V) : Prop :=
  ∀ u ∈ S, ∀ v ∈ S,
    Relation.EqvGen (fun a b => ∃ x, M.InGroup S x ∧ M.atom x = a ∧ M.atom (M.mate x) = b) u v

def IsBlock (S : Finset V) (j₁ j₂ : V) : Prop :=
  S ⊆ M.atoms ∧ j₁ ∈ S ∧ j₂ ∈ S ∧ j₁ ≠ j₂ ∧
    M.outIn S j₁ = 1 ∧ M.inIn S j₁ = 1 ∧ M.outIn S j₂ = 1 ∧ M.inIn S j₂ = 1 ∧
    (∀ v ∈ S, v ≠ j₁ → v ≠ j₂ → M.degIn S v = 4) ∧ M.GroupConnected S
-- (no Decidable instance)

def eraseBond (e : D) : Molecule V {x : D // x ≠ e ∧ x ≠ M.mate e} where
  atoms := M.atoms
  atom := fun x => M.atom x.1
  mate := fun x => ⟨M.mate x.1, …, …⟩   -- two inline side-condition proofs
  out := fun x => M.out x.1
  …

def IsHyperBlock (S : Finset V) (j₁ j₂ : V) : Prop :=
  ∃ e : D, M.ends e = s(j₁, j₂) ∧ (M.eraseBond e).IsBlock S j₁ j₂
```

**Why.** F57: with degree-only blocks, two blocks sharing a joint can fail to concatenate (T `defblock` L1330;
DH23 Def 4.10). The same molecule satisfies every premise of T `disjointlem` (DH23 Lemma 4.11) while its only
applicable alternative fails (`MOLE-prefreeze.md`, kernel-checked).

**Consumers.**
- `IsVine` (`M.IsBlock S j₁ j₂ ∧ …`) is unchanged in text. Its template isomorphism already forced connectedness.
- B2.3's `DecorationHyp.vineLG` uses `IsVine`.
- `IsBlockGap` does not use `IsBlock`.

**Probes.**
- `doubleBond_block`: the connectivity conjunct is proved by an explicit path, where it was `decide`.
- `disconnectedBlocks` (verbatim from MOLE) with `_isMolecule`, `_left_degrees`, `_left_not_connected`,
  `_left_not_block`.
- **The bridge to MOLE:** `moleInduced`, `moleGroupConnected`, `IsBlockDeg` (MOLE's definitions, verbatim) and
  `groupConnected_iff_mole`, `isBlock_iff_mole`, `isHyperBlock_iff_mole`.

**Auditor:**
1. Is connectedness the right reading of `defblock` for every consumer (vines, (CL)/(CN) blocks of
   `block_clcn`, splicing)?
2. Is the hyper-block definition (connected adjoint in `M` minus the joint bond) the source's "adjoint"?
3. Does anyone rely on deciding `IsBlock`? I found no one.

### B2-CL-6 (wt-orch): the `propcplmol` docstring (F58)

**Before:** "…satisfies the molecule axioms (at most two outgoing and two incoming bonds per atom; connected, with
an atom of degree `< 4`)."

**After:**
- `IsMolecule` = the degree bounds plus no saturated component, explicitly **not** connectedness.
- The counts and connectedness of `propcplmol` are separate claims.
- Any statement of them keeps `1 ≤ order` in both sentences (F58).

**Statement unchanged.** `Garden.isMolecule_molecule (G) (hP : G.IsPlain) (hw : w = 2 ∨ G.Irreducible)
(hn : 1 ≤ G.order) : G.molecule.IsMolecule`, still `sorry`.

**Auditor:** wt-nt's MOLE proves `garden_isMolecule : ∀ G, G.molecule.IsMolecule` without hypotheses. Should the
obligation drop its hypotheses, or stay as is? It is harmless either way.

### B2-CL-7 (wt-orch): operation bounds `IsDeviation`; the `deviation` docstring (F59)

**Before:**

```lean
/-- **The deviation `𝔇𝔢𝔳`** … the least `ℐ` with `𝔄_pre ≤ ℐ 𝔄_pos`, i.e. `𝔄_pre / 𝔄_pos` … -/
noncomputable def deviation (Apre Apos : ℝ≥0∞) : ℝ≥0∞ := Apre / Apos
```

**After:**
- **New `def IsDeviation (Apre Apos I : ℝ≥0∞) : Prop := Apre ≤ I * Apos`.** This is T (defdev) L2135 literally:
  T calls any such `ℐ` "the deviation".
- **`deviation` is unchanged in body.** The docstring now says it is the least `IsDeviation` bound only when
  `Apos ≠ ⊤` and (`Apos = 0 → Apre = 0`), and lists the three failing cases.

**Consumers.** None: no B2 statement uses `deviation` or `IsDeviation` yet. Per-operation bounds (T L2135ff) are to
be stated with `IsDeviation`.

**Probes:** `deviation_le_iff_of_zero_compatible`, `not_isDeviation_one_zero`, `deviation_top_top`.

### B2-CL-8 (wt-orch): the counting obligation of `propstructure` (R15-1, R15-2)

**Before:** none. §4 cited DH21 Cor 4.9 but stated no count.

**After:** a new §4 obligation (`sorry`, like its five siblings), with the §4 header updated.

```lean
theorem regular_count_le : ∃ C₀ : ℕ, ∀ m : ℕ,
    (Finite {G : Garden 2 // IsRegularCouple G ∧ G.order = 2 * m} ∧
      Nat.card {G : Garden 2 // IsRegularCouple G ∧ G.order = 2 * m} ≤ C₀ ^ m) ∧
    ∀ ζ : ℤˣ, Finite {G : Garden 1 // IsRegularTree G ∧ G.sig 0 = ζ ∧ G.order = 2 * m} ∧
      Nat.card {G : Garden 1 // IsRegularTree G ∧ G.sig 0 = ζ ∧ G.order = 2 * m} ≤ C₀ ^ m
```

- **The source.** T `propstructure`, last sentence: "the number of regular couples of order 2m is at most `C₀^m`,
  and the same holds for regular trees".
- **The tree count fixes the root sign.** Two trivial trees exist (R15-2).
- **The `Finite` conjuncts** guard against `Nat.card = 0` on an infinite type.
- **The types are REG-STRUCT's `SourceCouples`/`SourceTrees`.** wt-resonant proves the statement with `C₀ = 12^9`
  (`Reg.finite_sourceCouples`, `Reg.sourceCoupleCount_le_pow`, `Reg.finite_sourceTrees`, `Reg.sourceTreeCount_le_pow`).
- **Auditor:** `∃ C₀` (source) versus the explicit `12^9`; and the source-object form versus the code form that the
  consumers sum over. The code form follows from the §4 bijection; DESIGN CL-8 says so.

### B2-CL-9 (wt-orch): probe `dblRail` (follow-up to F53)

`dblRail` with `_isMolecule`, `_not_ladder` and `_maximalLadders = ∅` shows that a double rail is not a ladder rail.
The CL-2 state accepted it; CL-3 rejects it. Probe-only change.

### B2-CL-10 (wt-orch): probe repair, `open Resonant` in `WaveB2-Regular-probes.lean`

Main `c1a1ed9` moved `resonantIntegral`, `resonantKernel` and `energyInvSliceLimit` into `WaveTurbulence.Resonant`.
The bridge probes (`resIntegral_eq_resonantIntegral`, `pvResonantIntegral_eq_energyInv`) therefore no longer
resolved on current main. The fix is one line, `open Resonant`. The probes still hold by `rfl`.

### B2-CL-11 (wt-orch): the special-subset weight (F61, CONFIRMED by the orchestrator)

**Before:**

```lean
noncomputable def specialWeight {w : ℕ} (σ : Fin w → ℤˣ) (Z : Finset (Fin w × Path)) : ℂ :=
  ∏ z ∈ Z, ((((nodeSign σ z : ℤˣ) : ℤ) : ℂ) * Real.pi * Complex.I)⁻¹
```

**After:**

```lean
noncomputable def specialWeight {w : ℕ} (σ : Fin w → ℤˣ) (Z : Finset (Fin w × Path)) : ℂ :=
  ∏ z ∈ Z, (-((((nodeSign σ z : ℤˣ) : ℤ) : ℂ) * Real.pi * Complex.I))⁻¹
```

- **Used by both** `RegCpl.app` (couples, `σ = (+,−)`) and `RegChain.app` (trees, `σ = (ζ)`). Their texts are
  unchanged, but **their meaning changes**, and so does B2.1 `regularAsymptotics` items (1)–(2).
- **Docstrings.**
  - `specialWeight`: F61, the derivation, the trace `/home/scott/wt-scratch/wke/F61-sign-trace.md` (sha256
    `edd8025b0672…`), and the ruling.
  - `RegCpl.app` and `RegChain.app`: deviation notes.
  - B2.1: new deviation (D7).
- **Why.** DH21 Lemma 7.3 (L1737) has `+χ_∞(α)/(επiα)·I_μ`. The kernel, DH21 Lemma 5.8's term II and the landed Lean
  `iker_comp_decompP` (`T₀ = −I_μ`) give `−`. DH21 sets `ε_j = ζ_𝔫`, and the `Ω` convention does not compensate
  (wt-wke's trace). So T (regref1-3) needs `∏_{𝔫∈Z} (−1)/(ζ_𝔫 π i)`.
- **Probes:** `specialWeightT` (the old weight), `specialWeight_eq_neg_one_pow_mul_old` (new = `(−1)^{|Z|}` · old),
  `specialWeight_ne_old_of_odd`.
- **Auditor:**
  1. Verify the sign trace independently. I derived the kernel sign myself (JR-OPS W2), so I am not independent on
     it.
  2. Check the claim that B2.1 item 4 (the WKE identity, `∑ app = 𝒰_n`) is unaffected because `|Z|` is constant
     on equivalence classes.
  3. Check that no other B2 object carries T's `(ζπi)⁻¹` (I found none).

## 3. Build evidence (mine; to be redone independently)

**Setup.** My scratch root, on B1 snapshot 6 and main `b1e8a86`, one `lake env lean` at a time. Built: Regular,
Regular-probes, Molecules, Molecules-probes, Ladders, Statements, Statements-probes.

**Result.**
- 0 errors in all seven modules.
- The only warnings are `declaration uses 'sorry'`, for exactly these 10 declarations:
  - Regular §4 (6): `RegCpl.exists_decodes`, `existsUnique_regCpl_decodes`, `RegChain.exists_decodesTree`,
    `existsUnique_regChain_decodesTree`, `RegCpl.size_eq_order`, and the new `regular_count_le`;
  - Molecules (1): `Garden.isMolecule_molecule`;
  - Statements (3): B2.1 `regularAsymptotics`, B2.2 `incoherentDecay`, B2.3 `rigidity`.
- **Axioms** `[propext, Classical.choice, Quot.sound]` for every new probe: `doubleBond_block`, `doubleBond_vine`,
  `dblRail_not_ladder`, `dblRail_maximalLadders`, `disconnectedBlocks_left_not_block`, `isBlock_iff_mole`,
  `isHyperBlock_iff_mole`, `deviation_le_iff_of_zero_compatible`, `deviation_top_top`,
  `specialWeight_eq_neg_one_pow_mul_old`, `specialWeight_ne_old_of_odd`, `app_triv`.

**`/home/scott/wt-scratch/waveb2/build` was rebuilt in place** (Task 21, after CL-12), 2026-11-04 01:18–01:19 UTC.
It was built from the current sources against `/home/scott/WaveTurbulence-dev/.lake/build` and
`/home/scott/wt-scratch/waveb/build`, the `LEAN_PATH` of its readers: 0 errors, the same 10 `sorry`s. External
importers of `WaveB2Draft.*` (links, reg-struct, skeleton) use their own local copies, and moleprop13 imports
Degen/MOLE modules, not `WaveB2Draft`.

## 4. Open items for the independent auditor (beyond the per-CL questions)

1. **CL-1 closure: resolved by CL-12.** The closure check finds 0 uses of project theorems; see §2 B2-CL-12. The
   auditor should re-run such a check independently.
2. **Stage-1 OPTIONAL items O1–O6** (`WaveB2-stage1.md`): still not applied, per `WaveB2-stage23.md`. Decide whether
   any is needed for the freeze.
3. **Findings to re-check against the final text:** F53 (CL-3), F57 (CL-5), F58 (CL-6), F59 (CL-7),
   R15-1/R15-2/F55 (CL-8) and F61 (CL-11). The REG-STRUCT obligations themselves are audited in
   `REG-STRUCT-prefreeze.md`.
4. **B2.1 semantics** changed twice without a text change: through `IsLadder` (CL-3, via `countA`, in B2.3) and
   through `specialWeight` (CL-11, in B2.1). The freeze audit should re-derive B2.1 items (1)–(4) and B2.3 against
   the current definitions.
5. **MOLE, DEGEN and REG-STRUCT results** were proved against older pins of these definitions. The CL-3 change was
   re-checked for MOLE (`MOLE-prefreeze.md`: 3 exports re-proved with the new `IsLadder`). The CL-5 block change
   affects MOLE's overlap results, which are bridged by `isBlock_iff_mole` and `isHyperBlock_iff_mole`.

## Addendum: B2-CL-12 (wt-orch, Task 21): closure policy (B1 CL-17/CL-18); resolves the CL-1 blocker

**`GNode.parent`.**
- **Before:** `⟨(a.1.1, a.1.2.dropLast), TTree.dropLast_mem_branching a.2 h⟩`. The theorem `TTree.dropLast_mem_branching`
  was in Molecules and called `TTree.branching_of_append_mem` from `WaveBDraft.Lemmas`.
- **After:** the same value, `(a.1.1, a.1.2.dropLast)`, with the membership proof inline in the `by`-block. It is
  the induction of `branching_of_append_mem`, written like B1's `GBranch.child`. The probe `GNode.parent_val`
  (`rfl`) checks that the value is unchanged.

**`Garden.molecule`.**
- **Before:** it used the in-file theorems `Garden.pair_unmarked` and `Garden.pair_ne_of_unmarked`.
- **After:** the same proofs inline, from the `Garden` fields `pair_eq_iff` and `pair_pair`. The data fields are
  unchanged.

**Imports.** Molecules no longer imports `WaveBDraft.Lemmas` (the CL-1 import is removed).

**Moved to Molecules-probes,** unchanged, with the same names: `TTree.dropLast_mem_branching`,
`Garden.pair_unmarked`, `Garden.pair_ne_of_unmarked`, `units_ne_one_iff_eq_neg_one` (unused anywhere).

**`deriving DecidableEq` removed** for `Molecule.GapKind` and `VineType`.
- **Before:** `deriving DecidableEq`.
- **After:** explicit `@[instance_reducible, instance] def instDecidableEqGapKind` / `instDecidableEqVineType`, with
  the same names as the derived instances.
- They are case-by-case matches (`isTrue rfl` / `isFalse fun h => ….noConfusion h`), as for B1's `MarkTag` and
  snapshot 6b's `FixPat`.
- **Why.** The derived instances used the generated theorems `GapKind.ofNat_ctorIdx` and `VineType.ofNat_ctorIdx`,
  and CL-17/CL-18 allows no `deriving` in the freeze set (the orchestrator's FixPat ruling).

**Closure check** (`Closure.lean`, wt-orch, modelled on B1's `FreezeList.lean`).
- **Method.** For every non-theorem declaration of `WaveB2Draft.{Regular, Molecules, Statements}` (296 in all), I
  followed type, body, constructor types and auxiliary proofs and matchers transitively. Structure-field projections
  count as part of their structure.
- **First run** (mid-CL-12: after the inlining, before the `deriving` change): 16 hits.
  - 11 were structure-field projections (`Garden.pair_sign`, `pair_eq_iff`, `pair_pair`; `Molecule.mate_mate`,
    `atom_mem`, `mate_ne`, `out_mate` in `eraseBond` and `cut`).
  - 3 were `_simp` auxiliaries of `GNode.parent`'s own proof, which the refined checker expands.
  - 2 were the derived `ofNat_ctorIdx` theorems, which led to the `deriving` change.
  - The checker was not run before the inlining. The `TTree.dropLast_mem_branching` → Lemmas dependency is known from
    the source (CL-1).
- **After CL-12: 0 uses of a proved theorem of the project.**

**Checks.**
- In my scratch root: all seven modules rebuild with 0 errors and the same 10 `sorry`s.
- `waveb2/build` was rebuilt in place (see §3).

**Hashes.** `WaveB2-Molecules.lean` `58fe0545f105…`, `WaveB2-Molecules-probes.lean` `9f8aa52a3afa…`, `DESIGN.md`
`3ed85d327bf3…`. The other files are unchanged from the table.

**Auditor:**
1. Confirm that the inline proofs do not change any value: `GNode.parent_val`, and the `Garden.molecule` fields.
2. Re-run a closure check.
3. Check whether `Regular.lean` or `Statements.lean` also need the no-`deriving` sweep. Neither has `deriving`; I
   checked.
