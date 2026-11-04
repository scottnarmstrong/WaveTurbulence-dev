# Statement audit: wt-wke's B̃ bridge (BTILDE)

Auditor: `wt-orch`, refute-first. Date: 2026-11-04 (Task 31b). Findings only; nothing was edited.

**Scope.** `/home/scott/wt-scratch/btilde` (`HANDOFF.md`):
- is the garden-defined `B̃_𝒬` of DH21 (defcoefb2)/(deftildeb) equal to the code-defined one;
- does the bridge discharge wt-torus's `Cancel.BtRec` exactly?

## Verdict

**PASS.**
- **`btRec_BtJR : Cancel.BtRec BtJR`**, with no hypotheses.
- **The composition holds.** CANCEL7's `regcplcal` (DH21 Prop 7.5, corrected) and `maincancel` (Prop 7.4) apply to
  `BtJR` with the Prop 5.1 expansion `maincoef_BtJR_DH23` and nothing else.
- **Garden equals code.** `cplB_eq_BtJR` / `cplB_eq_BtJR_G` identify the garden integral of (defcoefb2) with
  `BtJR 𝒬 root root`, under (deftildeb)'s link relation, for every decoded pair.
- **Independent re-check.** I re-compiled the pinned sources in a different, consistent environment: the final B2
  Regular, main's ClassJR, and the audited `CancelDraft`. 0 errors, 0 warnings; standard axioms.
- **Finding:** B-1, the bridge's own environment was not reproducible as described.

## 1. Inputs

**Pin.** `btilde` was pinned at 06:53 UTC: 22 files, list digest `4b2ad64b0e40…`. Since then wt-wke has changed only
`build.sh`, at 06:58: the `wtroot/` symlink root is dropped, because Foundations/Cancel is on main. The sources are
unchanged.

**`BtRec`.** `cancel/src/CancelDraft/CodeDefs.lean`. Its fields are:
- `triv`: the value `1`;
- `type1`: (newexp1), with existential time swaps;
- `type2`: (newexp2) in CPS form, with pair variables the chosen chain nodes (`chainData`), signs `zetaA`, pair
  coefficients `pairF`, and existential swaps.

It is the named obligation of CANCEL7's Props 7.4 and 7.5.

## 2. Garden-defined `B̃` (DH21 (defcoefb2), (deftildeb); DH23 (defdomaine))

**`cplB G t s α = ∫ 1_{cplDom} cplPhase`.**
- **The domain `cplDom`.** Every branching node has `0 < τ_𝔟`, children earlier than their parents, and
  `τ_𝔟 < t` on tree 0 (the `+` tree, `G.sig = ![1,-1]` under `Decodes`) and `< s` on tree 1. That is DH21 (timedom)
  = DH23 (defdomaine). The time of a node whose children are all leaves is also positive, the evident reading of
  "`0 < t_𝔫' < t_𝔫`".
- **The phase.** `cplPhase = ∏_𝔟 e^{πi ζ_𝔟 α_𝔟 τ_𝔟}`, with `ζ_𝔟 = nodeSign G.sig 𝔟` (the frozen B1 sign).
- **(deftildeb).** `B̃_𝒬(α[𝒩^ch]) = B_𝒬(α[𝒩*])` with `ζ_𝔫'α_𝔫' = −ζ_𝔫α_𝔫` on each pair. In the bridge, `α` is
  defined on all addresses, and the relation is the hypothesis `LinkRel` / `LinkRelG`.
  - **Checked: `LinkRel α l` is exactly `ζ_{l.2} α_{l.2} = −ζ_{l.1} α_{l.1}`.** `LinkRelG` is the same with the
    garden's signs, and `linkRelG_iff_couple` relates them.
  - DH21's "assuming `α[𝒩*∖𝒩^ch]` is defined such that …" is exactly this hypothesis form.

**The identities.**
- `cplB_eq_BtJR (hQ : 𝒬.Decodes G) (hα : ∀ l ∈ 𝒬.links, LinkRel α l) (0 ≤ t) (0 ≤ s) :
  cplB G t s α = BtJR 𝒬 root root α t s`, where `BtJR 𝒬 a b := (toJR 𝒬).Bt a b`.
- `cplB_eq_BtJR_G`: the same, with the garden's signs.
- **Extra hypotheses.** `0 ≤ t, s` for couples, and `s < t` for the tree version `treeAstar_eq_Atilde_G` (DH21:
  "for `t > s`"). The kernel forms add layer 0 and `t, s ≤ 1`. All are within DH21's domain `t, s ∈ [0,1]`, and are
  needed only at the degenerate trivial objects.
- **`maincoef_garden_B2`.** For every regular couple `G`: `∃! 𝒬, (wf ∧ Decodes G) ∧ (garden B = BtJR under the
  link relation) ∧ MCExp …`. It takes `hstruct = existsUnique_regCpl_decodes` as a hypothesis, stated verbatim.
  wt-wke discharges it in REG-STRUCT's environment (`check/RegStructDischarge.lean`). I did not re-run that here:
  Task 32 verifies those proofs against the final B2 definitions.

## 3. `BtRec` is discharged exactly

**One environment** (mine; read-only on the others).
- **The olean root.** torus-fourier's `WaveTurbulence` oleans, plus the 20 ClassJR modules of `MCProp51`'s closure
  that only main has built, symlinked from dev. All 94 modules of that closure have identical sources in main and
  torus-fourier, and the 74 oleans present in both are byte-identical.
- **On top of it:** the mexp `build-base` (snapshot-7 B1, the final B2 Regular `4d7f81ef`, LAYERREG/REG-STRUCT/LINKS/
  ENHANCED, `CancelDraft` equal to `cancel/src`) and my compile of the pinned `src/BTilde`.
- **All 13 BTilde modules: 0 errors, 0 warnings.**

**Checked.**
- `btRec_BtJR : Cancel.BtRec BtJR`, printed type, with no hypotheses.
  - Type 1 uses the swaps `![false, true, false]`, by `rfl`.
  - Type 2 uses `swAt` and the chain lemmas.
- `check/Compose.lean` re-run here:
  - `regcplcal_BtJR_check`: for a well-formed dominant `𝒬`, special `Z` and `t, s ∈ [0,1]`, `∃ G`, the regularized
    integral is `(−1)^{|Z|} · RegCpl.JB 0 𝒬 t s`;
  - `maincancel_BtJR_check`: the non-dominant integral is `0`;
  - both are obtained by `Cancel.regcplcal btRec_BtJR …` / `Cancel.maincancel btRec_BtJR …` applied to the
    expansion of `maincoef_BtJR_DH23`, with nothing else.
- **Axioms** of `btRec_BtJR`, `cplB_eq_BtJR`, `maincoef_garden(_B2)`, `maincoef_BtJR_DH23`,
  `phaseIntegral_kDomain_eq_BtJR`, `treeAstar_eq_Atilde_G` and the two checks: [propext, Classical.choice,
  Quot.sound].

**Consequence.** B2's `RegCpl.JB` (route R4, B2.1 deviation D1) is the limit of DH21's `𝒥B̃_𝒬` computed from the
actual garden. CANCEL7's Prop 7.5 with `Z = ∅` (`regcplcal_empty`) applies to `BtJR`, and `BtJR 𝒬 root root` is
the garden integral. This closes the D1 caveat for couples: "agreement with DH21's construction".

## 4. Findings

**B-1 (environment; resolved by this re-check).**
- The handoff's environment A loaded wke's ClassJR oleans under Cancel oleans compiled against torus-fourier's.
- 29 of 97 ClassJR oleans differ between the two worktrees. Seven sources differ too (`MCT*`, wt-wke's later commit
  `cd28e4e` on `w/jr-ops`, MAINCOEF-T, 06:55).
- `wtroot/` has since been removed, so A cannot be reproduced as described.
- The bridge does not import the `MCT*` modules, and my re-check in a consistent environment (§3) passes. **No
  defect**, but the bridge must be re-compiled at the port against whatever ClassJR main then has.

**Not covered (per the handoff).** There is no tree version of Prop 5.1. `chainAtilde` is identified with the
garden `𝒜*_𝒯` (`treeAstar_eq_Atilde_G`), but it has no expansion yet.
