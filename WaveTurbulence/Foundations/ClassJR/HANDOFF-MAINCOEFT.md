# HANDOFF — MAINCOEF-T (DH21 Proposition 5.1 for regular trees; DH21 Prop 6.10)

Worker: wt-wke.
- Branch: `w/jr-ops`. Main was merged first, at `0d98524`, which includes CANCEL7.
- Commits:
  - `421785e`: rebasing; weighted and twisted symbols; one term.
  - `713ae85`: the fixed-mask expansion; `MCExpT`; the tree chain.
  - `cd28e4e`: tree codes; the constant; DH23 weights.
- Brief: the user's MAINCOEF-T message, following the B̃ bridge (`/home/scott/wt-scratch/btilde/HANDOFF.md`).
- Nothing pushed.

## Statement

Code form, in `WaveTurbulence.Foundations.ClassJR.MCProp51T`, namespace `WaveTurbulence.ClassJR`:

```lean
theorem RegChain.maincoefT_DH23 {η A : ℝ} (hη : 0 < η) (hη2 : η ≤ 2) (hA : A1 ≤ A) (X : RegChain)
    (hX : X.wf = true) (ζ : ℤˣ) (x : Addr) :
    MCExpT (1 - η / 8) (η / 4) (1 - η / 2) A (CTη η ^ (2 * X.size + 1)) nodeSgn
      (chosenSet (X.linksAt ζ x)) (X.At ζ x)
```

- `X.At ζ x` is DH21's `Ã_𝒯(t, s, α[𝒩^ch])`. It is the (newexp2) chain integral of the tree code `X`,
  with the lone-leaf condition `1{t_{2m} > s}` as continuation (`MCTMain`).
- `MCExpT` (`MCTExp`) is `MCExp` with the identity required only on `0 ≤ s < t ≤ 1`. This matches
  DH21 L1705–L1708 ("for `t > s`") and DH23 L929 ("For `0 ≤ s < t ≤ 1`").
  - The components `G_Z` are full `MCRep`s, with the same DH23 weights as for couples.
  - The strict `s < t` is needed for the trivial tree, where `Ã = 1{s < t}`.
- `RegChain.maincoefT` is the general-exponent version. The output exponents are `(θ, a, b)`. The pair
  couples are expanded with `(θ', a', b)`. The difference exponent is `δ`. The conditions are
  `δ + θ ≤ θ'`, `δ + a ≤ a'`, `δ + b ≤ 1`, plus the J3 conditions.
- DH23 instance: `θ' = 1 - η/16`, `a' = 5η/16`, `δ = η/16`.
- Constant: `C_T^{2n(𝒯)+1}` for well-formed codes (`RegChain.NtreeX_le_CT`), where `n(𝒯) = X.size`.

Garden form, in scratch `/home/scott/wt-scratch/btilde/src/BTilde/MaincoefT.lean`:
- `maincoefT_DH23_B2` is the code form on B2 codes, for `chainAtilde X ζ = (toJRc X).At ζ (rootT ζ)`
  (equal by `rfl`).
- `maincoefT_garden_DH23` gives, for every regular tree `G`, `∃! X` such that:
  - `wf ∧ DecodesTree`;
  - `𝒜*_𝒯 = Ã_𝒯` for `s < t` under the link relation;
  - `Ã_𝒯` has the `MCExpT` expansion with the DH23 weights.
- The named obligation is `existsUnique_regChain_decodesTree`. It is discharged in REG-STRUCT's
  environment (`check/RegStructDischarge.lean`: `maincoefT_garden_DH23_RS`), with standard axioms.

## Route

I used the direct route, from the chain integral with continuation `1{t′ > s}`. This is DH21's own
argument: Prop 6.10's proof analyses "the regular chain similar to Section 5.2 … for `t > s`". The
couple `(𝒯, •)` of DH21/DH23 L1175 organises the decorations and the pairing; it is not needed for the
time coefficient. The proof:

1. **Rebase at `s`** (`chainT_rebase`, `MCTShift`).
   - Since `t_{2m} > s`, every chain time is `> s`.
   - Shifting all times by `s` leaves the phases unchanged: each pair has `β_b = -β_a`.
   - The result is the chain over `(0, t - s)` with the pair coefficients at `(u + s, v + s)`.
2. **Twist the pairs.**
   - A shifted pair coefficient has symbol `e^{πi(λ₁+λ₂)s} 𝒞(λ)` (`tsym`).
   - For fixed frequencies `z`, the twists multiply to `e^{πiΛ(z)s}` (`Mz_tsym`).
   - The measure-preserving shear `λ₂ ↦ λ₂ − Λ(z)` (`shearZ`) moves this into the bottom symbol.
   - J3's `chainT_bottom_expand`, Lemma 5.10 / Lemma G and `srep_assemble` then apply unchanged
     (`treeTerm`, `MCRep.treeOne`).
3. **Pay for the shear.**
   - The weight `⟨λ₂⟩` of the sheared product costs `⟨Λ(z)⟩ ≤ ∏_j ⟨λ_j⟩`, paid by the pair symbols
     (`MzSW`, `tbound_MzSW`).
   - Gevrey bounds use the weight `θ` with no variable weight (`SRep.weighted0`). Weighted bounds use
     the weight `a` (`SRep.weighted`).
   - Pairs are therefore expanded with `θ' ≥ θ + δ`. J3's Prop 5.1 holds for every `θ' < 1`, so no
     exponent is lost.
4. **Rebase each term back** to `(t, s)` (`MCRep.sub_time`), via the shear `(λ₁, λ₂) ↦ (λ₁, λ₁ + λ₂)`.
   The `⟨max⟩` weights change by a factor at most 2. This is DH21's remark that tree weights become
   `(⟨λ₁⟩ + ⟨λ₂⟩)`.
5. **Regroup** by `Z` (`MCExpT.of_sum`, `MCExpT.chain`). This copies J3's `MCExp.chain` bookkeeping
   with an empty bottom set.

## Files (ClassJR, all `module` + `public section`)

| file | lines | content |
|---|---|---|
| MCTShift | 247 | `chainT_eq_zero_of_le`, `chainT_rebase`, `MCRep.sub_time` |
| MCTBound | 389 | `wsym`/`SRep.weighted`, `TBound.node`, `MzSW`/`tbound_MzSW`, `Λsum`, `tsym`/`Mz_tsym` |
| MCTTerm | 361 | `shearZ`, `shearM_bounds`, `twistP`, `treeTerm` |
| MCTOne | 275 | `SRep.weighted0`, `wsym_chainP`, `Ntree`, `treeOne_piece`, `MCRep.treeOne` |
| MCTExp | 373 | `MCExpT`, `MCExpT.of_sum`, `chainT_congr_pos`, `MCExpT.chain`, `MCExpT.chain'` |
| MCTMain | 177 | `RegChain.At`, `RegChain.mcexpT`, `KT`, `CT`, `RegChain.NtreeX_le_CT` |
| MCProp51T | 63 | `RegChain.maincoefT`, `CTη`, `RegChain.maincoefT_DH23` (entry module) |

Hashes:
- `MCProp51T` `d248b0f0…`
- `MCTMain` `8a63cb22…`
- `MCTExp` `21e3a00b…`
- `MCTOne` `3b6468c3…`
- `MCTTerm` `3f5eb0bf…`
- `MCTBound` `6c21bfc1…`
- `MCTShift` `12fbdda7…`

Scratch `BTilde/MaincoefT.lean` (60 lines) is hashed in `btilde/SHA256SUMS`.

## Checks

- `nice -n 5 lake build WaveTurbulence.Foundations.ClassJR.MCProp51T`: `Build completed successfully
  (3819 jobs)`, 0 warnings. Each new module was also built individually.
- `#print axioms`: `RegChain.maincoefT_DH23`, `RegChain.maincoefT`, `RegChain.mcexpT`,
  `RegChain.NtreeX_le_CT`, `MCExpT.chain(')`, `MCRep.treeOne`, `treeTerm`, `chainT_rebase` and
  `MCRep.sub_time` all give `[propext, Classical.choice, Quot.sound]`.
- `python3 /home/scott/wt-scratch/wke/dupscan.py`: `duplicate scan: OK`, `sorry scan: OK`.
- No `sorry`/`admit`/`axiom`/`set_option`. The largest new file is 389 lines.
- Scratch:
  - All 14 BTilde modules rebuild with 0 warnings in the BtRec environment and in REG-STRUCT's.
  - The symlink root is gone: CANCEL7's `Foundations/Cancel` is built in wke and is byte-identical to
    wt-torus's.
  - `check/AxAll.log`, `check/Compose.log` and `check/RegStructDischarge.log` are standard throughout.
    The exception is `linksAt_toJR`, which uses only `[propext]`.
- `WaveTurbulence.lean` (the root) is unchanged. Registering `MCProp51T` and the `MCT*` modules is the
  orchestrator's job.

## Uncertainties

- **Pair exponents.** The tree statement uses pair couples at `θ' > θ`, a slightly larger exponent than
  the output. This is internal: J3's `RegChain.mcexp_coef` holds for every `θ' < 1`. The DH23 instance
  is fixed as above.
- **Variable addresses.** The variables are ClassJR couple addresses, with the tree placed at
  `rootT ζ` (tree 0 for `ζ = +`, tree 1 for `ζ = −`). B2's own tree links (`X.treeLinks ζ`, addresses
  `Fin 1 × Path`) are related by `linksAt_rootT` (scratch `BridgeB2`), which changes the tree index.
- **Phases and the link relation.** The garden link relation and `α = δL^{2γ}Ω` are hypotheses for
  consumers, as for couples.

## Suspected errata and deviations

None new. DH21 states the tree expansion "for `t > s`" with weights `(⟨λ₁⟩+⟨λ₂⟩)^{1/4}`. The DH23
`⟨max⟩` weights are the same weights up to constants, so the tree statement has the same shape as
couples' `maincoef_DH23` apart from the identity domain.
