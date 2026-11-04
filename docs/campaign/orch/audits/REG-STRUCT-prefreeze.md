# REG-STRUCT pre-freeze audit (Task 15): the regular-couple structure theorem

Auditor: `wt-orch` (Opus), refute-first. Date: 2026-11-03. **Findings only: nothing under `wt-scratch/reg-struct`
was edited.**

## Inputs

**Packet records.** The scratch has no `HANDOFF` or `WORKLOG`. Its working records are `CHECKPOINT.md`
(`28af46ace678…`) and `STRUCTURE-PROOF.md` (`0b2170dce9e5…`); the packet is still in progress.

**Statements under audit:** the B2 §4 characterization obligations in `wt-scratch/waveb2/WaveB2-Regular.lean`
(`ad72ce4be39e…`, L360–L390):
- `RegCpl.exists_decodes`;
- `existsUnique_regCpl_decodes`, the structure theorem for couples;
- `RegChain.exists_decodesTree`;
- `existsUnique_regChain_decodesTree`, the structure theorem for trees;
- `RegCpl.size_eq_order`.

These rest on the code types and decodings in §3 (`RegCpl`, `RegChain`, `trees`, `pairsAt`, `Decodes`,
`DecodesTree`, `wf`, `size`) and on the source-form regularity in §2 (`RawRegular`, `IsRegularCouple`,
`IsRegularTree`).

**REG-STRUCT's theorems.** `Reg.isRegularCouple_existsUnique_structure` (`CodeUniqueness.lean`,
`dc966c96baa6…`), `Reg.size_eq_order`, `Reg.sourceCoupleCount_le_pow`, `Reg.sourceTreeCount_le_pow` and
`Reg.coupleCodeCount_le_pow`.

**Sources.**
- DH21 `Inventiones-Final_Version.tex`. With the shared theorem counter: Prop 4.7 (L752), **Prop 4.8 `structure1`
  (L762)**, **Cor 4.9 `countcouple1` (L776)**, **Prop 4.10 `structure1.5` (L791)**, Prop 4.14 (L824–L834).
- TARGET Prop 4.4 `propstructure` (L851–L869).
- FINDINGS F12; GRAPH rows 202–206 and 216.

## Verdicts

| Item | Verdict |
|---|---|
| S1. `existsUnique_regCpl_decodes` vs TARGET 4.4 (a)/(b), DH21 4.8, 4.10 and F12 | **PASS** |
| S2. The tree statements vs TARGET 4.4's last paragraph | **PASS** (statement level; still unproved) |
| S3. `RegCpl.exists_decodes` and `size_eq_order` | **PASS** (statement level) |
| S4. REG-STRUCT closes S1 and `size_eq_order` exactly, with no hypothesis added | **PASS** (type-checked; proofs not rebuilt by me) |
| S5. Pins: REG-STRUCT's definitions = the current B2 definitions | **PASS** (elaborated constants identical) |
| S6. TARGET 4.4's counting sentence (Cor 4.9) has a B2 obligation | **GAP**: there is none (finding R15-1) |
| Brief citation "DH21 L833" for `GAP.structUniq` | **Wrong** (finding R15-3). REG-STRUCT's own clarification is correct. |

## S1. The couple structure theorem

`existsUnique_regCpl_decodes (G : Garden 2) (hG : IsRegularCouple G) : ∃! Q : RegCpl, Q.wf = true ∧ Q.Decodes G`.

**Existence (DH21 Prop 4.8).**
- Every code is trivial, type 1 (a (1,1)-mini-couple with codes `c ∈ {straight, crossed}` and `Q₁, Q₂, Q₃` on the
  red, green and blue pairs) or type 2.
- A type-2 code is two chains in Catalan form. Each chain pair carries a mini-tree code and the sub-couples
  `Q_{j,ε,1}`, `Q_{j,ε,2}`; the lone pair carries `Q_lp`.
- These are exactly 4.8's "Q₀ = mini couple or regular double chain, with leaf pairs replaced by regular couples".
  The legal-partition ↔ Catalan-form equivalence is proved (`legal_iff_catalanGenerated`, `legal_iff_enclosure`).

**Exclusive types and type-2 uniqueness (DH21 Prop 4.10, TARGET "exactly one of the two cases").**
- Both follow from `∃!`: a well-formed type-1 code and a well-formed type-2 code cannot decode the same couple.
- `wf` imposes 4.10's normalization exactly: `Q_lp` is not of type 2. It also imposes TARGET (b)'s "Q₀ nontrivial"
  (`¬(Xp = nil ∧ Xm = nil)`).
- One chain may be empty, as in TARGET (`m_ε ≥ 0`).

**Type-1 uniqueness and the red/green/blue assignment (F12).**
- TARGET 4.4 (a) asserts these; DH21 4.8–4.10 do not state them.
- Uniqueness of the code covers the mini-couple code, the colour-to-slot assignment and every sub-couple, so the
  statement contains F12's missing uniqueness.
- `STRUCTURE-PROOF.md` Steps 1–4 give the argument: property L via signed leaf sums, the stopping rule on the unique
  L-child, partner-root recovery for side couples, and strong induction.

**Design.**
- The statement quantifies over pairs (code, carrier); no `Classical.choose` is applied to a non-unique family.
- `Decodes` requires `IsCouple` (plain, signs `(+,−)`) and an exact tree match. Its pair clause is a membership
  test, but the decoded list is functional: `carrier_unique` shows a code determines its carrier.

**Refutation attempts.** None succeeded:
- extra data in the code that the source does not fix;
- the source fixing data the code omits;
- wrong normalization of `Q_lp`;
- a missing nontriviality condition;
- `Decodes` being weaker than equality of couples.

## S2–S3. Trees, range and order

**Trees.** `existsUnique_regChain_decodesTree` is TARGET's last paragraph: a unique chain `𝒳₀` with couples
`Q_{j,0,ι}`; `nil` covers the trivial tree. No `Q_lp` normalization applies, because the lone leaf ends the chain.
The decoding uses the carrier's sign `G.sig 0`.

**Range.**
- `RegCpl.exists_decodes` is the converse ("every well-formed code is a regular couple"). TARGET leaves it implicit;
  it is needed because B2.1 sums over codes.
- `RegChain.exists_decodesTree` is its tree analogue, for each sign `ζ`.

**Status.**
- Not yet proved by REG-STRUCT (`CHECKPOINT.md`): reverse range, tree existence and uniqueness, the explicit
  legal-partition ↔ chain-history equivalence, and dominant chains.
- REG-STRUCT's finite diagnostics through order 6 agree: no decoding collisions, and the source A/B range equals the
  code range. These are diagnostics, not proofs.
- At statement level all four are faithful.

## S4. REG-STRUCT closes the B2 statements

`scratch/Task15-regstruct-probe.lean` (`f7b5bf6b93a3…`) elaborates, with no extra hypothesis:
- `example (G) (hG : IsRegularCouple G) : ∃! Q : RegCpl, Q.wf = true ∧ Q.Decodes G`, from
  `Reg.isRegularCouple_existsUnique_structure` (subtype form) by a two-line repackaging;
- `example (Q) (h : Q.Decodes G) : G.order = Q.size := Reg.size_eq_order h`.

Axioms of `isRegularCouple_existsUnique_structure`, `size_eq_order`, `sourceCoupleCount_le_pow`,
`sourceTreeCount_le_pow` and `coupleCodeCount_le_pow`: `[propext, Classical.choice, Quot.sound]`.

**Caveat: I read REG-STRUCT's compiled modules; I did not rebuild them.**
- All of them are newer than their sources. The only module without a compiled file is the new
  `PartitionConstructors.lean`, which is outside the checked closure.
- Their closure imports `Frozen.Defs.{Mom, LatticePoint, IsWKESolution}` and `Foundations.NLS.AkSystem`. These are
  unchanged between their worktree's `486437a` and my HEAD.
- A from-source rebuild belongs to the seal audit.

## S5. No drift between pins

- REG-STRUCT's `WaveBDraft/Core.lean` (snapshot 4) is **byte-identical** to the snapshot-5 Core.
- Pinned B2 snapshot 1 §1–§4 is textually identical to the current `WaveB2-Regular.lean` §1–§4. Outside §1–§4, only
  the imports and §6 changed.
- REG-STRUCT's `WaveB2Draft/RegularDefs.lean` is §1–§3 verbatim, but under different imports and `open`s. So I
  compared the **elaborated** constants (`scratch/Task15-dump-consts.lean`, `23b7ae991281…`).
  - All 185 constants of `RegularDefs` occur in the current B2 `Regular`, which I compiled from source on snapshot 5.
  - Type and value are identical for all 185, after normalizing hygienic names.
- REG-STRUCT's results therefore apply to the current B2 definitions without change.

## Findings

**R15-1. Counting has no B2 obligation (pre-freeze; should be fixed before B2 freezes).**
- TARGET 4.4 ends: "the number of regular couples of order 2m is at most C₀^m, and the same holds for regular trees".
  GRAPH `T.propstructure` lists this as part of the Wave B interface.
- §4's docstring cites Cor 4.9, but §4 states no count.
- REG-STRUCT already proves:
  - code counts: `coupleCodeCount_le_pow : #{Q | wf ∧ size = 2m} ≤ (12^9)^m` and `chainCodeCount_le`;
  - source-object counts: `sourceCoupleCount_le_pow`, and `sourceTreeCount_le_pow` per root sign;
  - finiteness: `finite_coupleCodes`, `finite_sourceCouples`.
- **Recommendation:** add the count to §4 in the form consumers use. B2 consumers quantify and `∑ᶠ` over well-formed
  codes, so the natural form is the code form. Optionally add the source-object form as well.
- The constant can be explicit (`12^9`) or `∃ C₀`. Π has no `C₀` field: TARGET's absolute `C₀(d,γ)` is absorbed into
  `η₀` (snapshot-5 Core L43, L50).
- B2.1 item (4)'s `∑ᶠ` already has its finiteness probe (`finite_dominant_codes`), so nothing is vacuous now; the gap
  only affects the count consumers (`T.layerreg1`, `DH21.countcouple1` → …).

**R15-2. Trees at m = 0: fix the sign (a convention, not an erratum of substance).**
- Read literally, "the same holds for regular trees" fails at m = 0 if both root signs are counted: there are two
  trivial trees and `C₀⁰ = 1`.
- REG-STRUCT counts with a fixed sign, which gives 1. A §4 count for trees should do the same, or state `≤ 2C₀^m`.

**R15-3. The brief cites the wrong source line.**
- `briefs/REG-STRUCT.md` attributes `GAP.structUniq` to "the source's case-by-case argument, DH21 L833".
- DH21 L833 is the uniqueness half of **Prop 4.14** (general couples): "Q_int contains no nontrivial regular
  sub-couple". That is `GAP.skeletonUniq` (C3); GRAPH row 216 cites it correctly.
- `GAP.structUniq` is TARGET 4.4's uniqueness of all regular structure data, whose DH21 basis is Prop 4.10. REG-STRUCT
  flagged this itself, and its route is correct.
- **Consequence:** completing REG-STRUCT does **not** discharge the L833 case-by-case argument. C3 must still write
  it. Please correct the brief so nothing is counted twice.

**R15-4. DH21 Cor 4.9's proof miscounts double chains** (DH21 map E7; not in FINDINGS).
- The proof bounds the choices of Q₀ by the Catalan number of one partition. For a double chain the count is the
  convolution `Σ_j C_j C_{m₁−j} = C_{m₁+1}`.
- The corollary is still true with a larger constant. REG-STRUCT's prefix-code injection does not use the generating
  function, so nothing depends on the error.
- Suggest logging it as a proof erratum, statement unaffected.

**R15-5. Freeze readiness.**
- The five §4 statements are freeze-ready as statements, plus a count statement (R15-1).
- Proof status: existence-and-uniqueness for couples and `size_eq_order` are proved; the range and tree obligations
  are open.

## Probes (untracked)

- `scratch/Task15-regstruct-probe.lean`: the B2 statements closed by REG-STRUCT's theorems, and the axioms.
- `scratch/Task15-dump-consts.lean`: dumps one module's constants. I ran it once on REG-STRUCT's `RegularDefs` and
  once on my source build of the current B2 `Regular`, then compared the two dumps.
