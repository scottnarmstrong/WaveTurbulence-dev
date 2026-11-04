# HANDOFF — J2 rest (DH21 Lemmas 5.9–5.10), branch w/jr-ops, head 0b74394

## Files (all `WaveTurbulence/Foundations/ClassJR/`, namespace `WaveTurbulence.ClassJR`)
- `Masked.lean` (657288a), `Masked2.lean` (93c64f9) — masked classes `MJ`/`MR`/`MR0`/`MJR`.
  An operator is class J/R in the variables `S ⊆ V` through an injection `ι → V`
  (`Option ι → V` for R) with range `S`. The file also has the composition (5.3–5.5) and sandwich
  (5.6–5.7) of masked operators on disjoint variable sets. This is the variable bookkeeping between
  steps: `ClassRP.reindex`, `exists_equiv_of_range_eq`, `Sum.elim`/`Option.elim` embeddings.
- `Chain.lean` (b82cbd5) — `LegalCode` (Catalan form), `chainX`, **Lemma 5.9** `chainX_spec`.
- `Lemma58.lean` (b82cbd5 + fix d027a98) — `iker_comp_decompP` now exposes `T₀ μ α = -I_μ` on the
  triangle (audit item W1). b82cbd5 alone did not build; d027a98 fixes it.
- `Chain2.lean` (14ed69c) — **Lemma 5.10**:
  - `lemma510` packages three statements: the card bound, the pointwise expansion with the explicit
    `χ_∞(α_j)/(ε_jπiα_j)` factors, and the class bounds.
  - `pchain_expand`: the pointwise expansion identity.
  - `tildeP_MJR`: `Ĩ_Z` is class J + R with norm ≤ `C510 θ ^ m`.
  - `Wv_eq`: the variables of `Ĩ_Z` are `σ '' (Ico q (q+m) \ (Z ∩ adj))`.
  - `chainX_none`: `pchain` is `chainX` with all `X_a = Id`.
- `LegalPartitions.lean` (0b74394) — REG-STRUCT copy, see the legal-partition choice below.
- `ChainPartition.lean` (0b74394) — the bridge from codes to legal partitions.

## Legal partitions: the choice (for the post-freeze move)
- **Copied:** `/home/scott/wt-scratch/reg-struct/LegalPartitions.lean`, sha256
  `91a6d0d27764c475f0951d84de60503696bd723d7319f3088622a57c08be1298` (pinned copy at
  `/home/scott/wt-scratch/wke/pins/LegalPartitions.lean.pin`). It becomes `ClassJR/LegalPartitions.lean`.
  - The definitions `PairPartition`, `PairPartition.Legal` and the three theorems are verbatim.
  - Only the namespace (`Reg` → `ClassJR`) and the imports changed: the source imports
    `WaveB2Draft.RegularDefs` but needs only Mathlib.
  - Post-freeze move: delete the copy and point `ChainPartition.lean` at the landed REG-STRUCT module
    (`ClassJR.PairPartition` → `Reg.PairPartition`).
- **Induction form:** the Lemma 5.9/5.10 inductions run on `LegalCode`, the Catalan form of
  DH21 Prop 4.5(2). This is the same shape as B2's `RegChain` (`pair m Qr Qg inner rest`, pairs in
  preorder, `/home/scott/wt-scratch/waveb2/WaveB2-Regular.lean`, sha256 `ad72ce4b…c3c53`). The
  forgetful map `RegChain → LegalCode` (`pair _ _ _ i r ↦ node i.code r.code`) is mechanical once B2 lands.
- **Bridge proved** (`ChainPartition.lean`):
  - `toPartition_legal`: the partner map of a code is a legal `PairPartition (2m)`.
  - `exists_code_of_legal`, `partner_inj`: every legal partition comes from exactly one code
    (DH21 Prop 4.5(2)).
  - `pairLeft_strictMono`, `exists_pairLeft`: the preorder index of the pairs is the increasing order
    of their smaller elements (DH21 §5.2 "the j-th pair").
  - `mem_adjSet_iff`: `adjSet` is exactly the set of adjacent pairs `{a, a+1}`.
- I did not copy `CatalanGeneration.lean` (sha256 `342c8a6a…af96d`): the bridge proves Prop 4.5(2)
  directly in partner-map form (`exists_code_of_matching`).

## Section 3 (the cutoff; my deviation 5): settled, no rework
- The `χ_∞` in every output factor is `Fourier.chiInfinity = 1 - Fourier.chi0`:
  - `chiInvR x = chiInfinity x / x`, `phiR = chiInvR/(πi)`;
  - `phiR_sign`: `Φ(εx) = χ_∞(x)/(επix)`;
  - `prod_phiQ`, and the statement of `lemma510`.
- Wave B's `chi0 = smoothTransition(2 − 2|x|)` equals `Fourier.chi0` by B1-Bridges
  `chi0_eq_fourier_chi0` (canon4 snapshot). So the factors are already the Wave B χ_∞.
- Where the cutoff enters:
  1. Def 5.2: the class R denominators `χ_∞(·)/(πi·)` (`chiInvR`).
  2. Lemma 5.8: term II's prefactor `Φ(εα₁)`, which is the output factor. The averager
     `ρ = ½·1_{[−1,1]}` (DH21's Gevrey-2 `M`) appears only inside the class R symbol of term III
     (as a function of the γ₃ integration variable, not of α) and in the class J error. It never
     reaches an output.
  3. Lemma 5.10: the factors `∏_{j∈Z} χ_∞(α_j)/(ε_jπiα_j)`.
  4. (maincoef1): the same factors, built from the 5.10 factors and from (regcplexpl)'s cutoffs (J3).
- What the consumers need from these lemmas:
  - J4 (Prop 7.4 cancellations) and J6 (7.9–7.10): the identity, the factor `χ_∞(α)/(ζπiα)` with
    Wave B's χ_∞ (true up to the bridge above), χ_∞ even (`chi0_even`), the class bounds, and
    `T₀ = −I_μ` (now exposed).
  - TARGET `regref`: the same.
  - None of them sees ρ. The orchestrator's audit (JR-OPS PASS) agrees.

## Checks
- `nice -n 5 lake build WaveTurbulence.Foundations.ClassJR.ChainPartition` → `Build completed successfully (3782 jobs).`
  This builds Chain2, Chain, Lemma58, Masked*, LegalPartitions.
- `grep -rn sorry WaveTurbulence/Foundations/ClassJR/` → 0.
- No `maxHeartbeats`/`axiom`/`opaque`/`unsafe`.
- Duplicate-name scan of the new declarations against `WaveTurbulence/`: none.
- Every file is ≤ 756 lines.

## Axioms (`#print axioms`)
- `chainX_spec`, `lemma510`, `pchain_expand`, `tildeP_congr`, `chainX_none`, `Wv_eq`, `partner_inj`,
  `pairLeft_strictMono`, `exists_pairLeft`, `mem_adjSet_iff`: `[propext, Classical.choice, Quot.sound]`.
- `toPartition_legal`, `exists_code_of_legal`: `[propext, Quot.sound]`.

## Uncertainties
- Lemma 5.10 is stated over codes with an injectivity hypothesis
  `Set.InjOn σ (Set.Ico q (q+m))`: the variables `α_j` of the pairs must be distinct.
- The parameters are `μ_j = μf j p` with `μf j` measurable (needed for Prop 5.1, where the μ_j are
  sums of integration variables).

## Suspected errata / deviations
1. **Deviation (harmless).** DH21 5.10 says each of the ≤ 2^m terms is "class J *or* class R". Our
   `Ĩ_Z` is class J **plus** class R (`MJR`), which gives ≤ 2^{|adj|+1} single-class terms. Lemma 5.9
   is likewise stated as J + R. DH21's own proof yields J + R (5.9's output).
2. **Sign (audit W2/F61): open.** Lemma 5.8 gives `𝒥_{α[ ],μ} = −I_μ`, so the Z-terms of 5.10 carry
   `∏_{j∈Z} (−χ_∞(α_j)/(ε_jπiα_j))·I_{μ_j}`. DH21 Lemma 7.3 (L1737) writes `+`. I will trace this
   through Prop 5.1 / (regchaincalref) in J3, and report the result (with a QUESTION line if it is a
   genuine source error) in the MAINCOEF handoff.
3. **Brief vs source.** DH23 (maincoef2.5) weights `max_n⟨α_n⟩^{1−η/2}`, not the brief's `α^{1/8}`
   (DH23 L955–969). J3 will follow the source.

READY jr2

---

## J3 MAINCOEF: the statement (final; for wt-torus / J4). Updated 2026-11-04, head 80bab05

All objects are committed on `w/jr-ops` under `Foundations/ClassJR/`, namespace `WaveTurbulence.ClassJR`. The entry
module is `MCProp51.lean`; it imports every other `MC*` module.

**Definitions** (`MCDefs.lean`).
- `e2 λ t s = e^{πi(λ₁t+λ₂s)}`.
- `wL a λ = (1+|λ₁|+|λ₂|)^a`, the stronger reading of DH23's `⟨max(λ₁,λ₂)⟩^a`.
- `PhiZ ζ z x = phiR (ζ z * x) = χ_∞(x)/(ζ_z πi x)` (`phiR_sign`).
- `MCRep θ a b A N S F`: on `[0,1]²`, `F α t s = ∫ 𝒞(α∘f, λ) e2 λ t s dλ`, where `f : ι ↪ V` has range `S`, and
  - `SymReg 𝒞` (audit W3);
  - (maincoef2): `∀ k, ∫∫ wL θ ‖∂^k 𝒞‖ ≤ gev N A k`, with `gev N A k = N A^k (2k)!`;
  - (maincoef2.5), per variable: `∀ i, ∫∫ wL a (1+|α_i|)^b ‖𝒞‖ ≤ N`.
- `MCExp θ a b A N ζ S F` is DH21 (maincoef3):
  `∃ G, (∀ Z ⊆ S, MCRep θ a b A N (S∖Z) (G Z)) ∧ ∀ α, ∀ t s ∈ [0,1], F α t s = Σ_{Z⊆S} (∏_{z∈Z} PhiZ ζ z (α z)) · G Z α t s`.
  `G Z` is DH21's `B̃_{Q,Z}`.

**Codes** (`MCCodes.lean`). `RegCpl`, `RegChain`, `linksAt`, `links`, `chosenSet`, `wf`, `size` and the mini codes
are copied verbatim from the B2 draft `wt-scratch/waveb2/WaveB2-Regular.lean` (sha256
`4d7f81efa32b54e5720aac452ea7d5e458cf6ee3052b9378763d37437cc5d052`).
- Variables: `Addr = Fin 2 × Path` (node addresses); node signs `nodeSgn`; `𝒩^ch = chosenSet Q.links`.
- `RegCpl.Bt Q x y` is `B̃_Q` with `+` root `x` and `-` root `y`, defined by (newexp1)/(newexp2):
  - type 1: `type1F x ![false, true, false] ![B̃_{Q₁}, B̃_{Q₂}, B̃_{Q₃}]` (the times of `Q₂` are swapped);
  - type 2: `type2F` = `+` chain (`chainT`) in `t`, `-` chain in `s`, `B̃_{Q_lp}` at the last times;
  - chain signs `ε_j = ζ_{𝔫_a}`.
- `RegCpl.Btilde Q = Q.Bt (0, []) (1, [])`.

**The theorems** (`MCProp51.lean`).
- `RegCpl.maincoef` (hθ0 : 0 ≤ θ) (hθ1 : θ < 1) (ha : 0 < a) (hb : 0 ≤ b) (hab1 : a + b < 1) (hab : a + b ≤ θ)
  (hA : A1 ≤ A) (Q) (hQ : Q.wf = true) :
  `MCExp θ a b A (C0 θ a b ^ (2 * Q.size + 1)) nodeSgn (chosenSet Q.links) Q.Btilde`.
- `RegCpl.maincoef_DH23`: the same with `θ = 1 − η/8`, `a = η/4`, `b = 1 − η/2`, for `0 < η ≤ 2`.
- `maincoef_of_structure` (IsReg) (Dec) (hstruct : ∀ G, IsReg G → ∃! Q : RegCpl, Q.wf = true ∧ Dec Q G) … (G) (hG) :
  `∃! Q, (Q.wf = true ∧ Dec Q G) ∧ MCExp … Q.Btilde`.
  With `Garden 2`, `IsRegularCouple` and `RegCpl.Decodes`, `hstruct` is REG-STRUCT's `existsUnique_regCpl_decodes`.
- The intermediate steps are also usable on their own:
  - `RegCpl.mcexp` (all codes, constant `Q.NB θ a b`);
  - `MCExp.one`, `MCExp.type1`, `MCExp.type2`, `MCExp.chain`, `MCExp.mul`, `MCExp.swapTimes`.

**F61, for J4.**
- The factor in front of `B̃_{Q,Z}` is exactly DH21 (maincoef1): `∏_{n∈Z} χ_∞(α_n)/(ζ_n π i α_n)`.
- The `−1` of Lemma 5.8's `T₀ = −I_μ` (`iker_comp_decompP`; Chain2's `T0`) is *inside* `B̃_{Q,Z}`.
- So for dominant couples `𝒥B̃_{Q,Z} = (−1)^{|Z|} · 𝒥B̃_Q`. DH21 (regchaincalref) and Lemma 7.3 miss this sign.

## HANDOFF — J3 MAINCOEF (DH21 Proposition 5.1 with the DH23 weights), branch w/jr-ops, head 80bab05

### Files
All are in `WaveTurbulence/Foundations/ClassJR/`. There are 37 J3 commits from c63e90b to 80bab05; every module
is ≤ 884 lines.

| module | what it proves |
|---|---|
| MCE | `gE` |
| MCSob | `SymReg.of_lintegral` |
| MCG, MCGR | Lemma G for class J and for class R |
| MCDefs | `MCRep`, `MCExp`, `type1F` |
| MCProd, MCK1, MCReorder, MCSRep | products, the type-1 coupling, reorderings, `SRep` |
| MCCase1, MCType1 | Case 1 |
| MCDiff | the difference loss |
| MCChainT | `chainT` |
| MCChainF | the Fubini step over the pair frequencies |
| MCGP | Lemma G for MJR |
| MCPair | `MCExp.mul`, `MCExp.swapTimes` |
| MCChainX | the mask expansion |
| MCChainM | pair symbols and their products over a code |
| MCAssemble | the shear pushforward and `srep_assemble` |
| MCChain1 | chain-term bookkeeping |
| MCChainId | the expansion identity |
| MCSum | sums of `MCRep` |
| MCChainTerm | one chain term |
| MCChainOne | fixed masks |
| MCChainExp | `MCExp.chain` |
| MCOne | the trivial couple |
| MCType2 | `MCExp.type2` |
| MCCodes | the copied B2 codes and `B̃_Q` |
| MCCodesVars | address regions and chain facts |
| MCMain | the induction |
| MCConst | `C₀^{2n+1}` |
| MCProp51 | the statements |

**Landing.** Add `public import WaveTurbulence.Foundations.ClassJR.MCProp51` to the root. I did not edit the root.

### Approach
1. Induction on the code (DH21 L944).
2. **Case 1** (`MCExp.type1`): the coupling `gE ⊗ gE`, pushed forward.
3. **Case 2** goes through one-sided chains, `chainT c R α t (G α · s)`:
   - Fubini over the pair and bottom frequencies (`chainT_fubini`, `chainT_exp_fubini`);
   - `chainT_exp`, i.e. the Volterra operator of `pchain` at `α̃ = α + ελ₁`;
   - Lemma 5.10 (`pchain_expand`, `lemma510`) over `Y ⊆ adj`;
   - `Φ(εα̃) = Φ(εα) + D` (MCDiff) over `Y' ⊆ Y`;
   - Lemma G (`MJR.lgpieces`);
   - the coefficient is the pushforward of `(∏ pair symbols with D) ⊗ 𝒞_b ⊗ H(β + shift)` along a shear (`srep_assemble`);
   - the masks are expanded (`chainT_expand`, `chainT_finsum`) and regrouped by `Z` (`MCExp.of_sum`).
     For a fixed `Z` at most `2^{m+1}` terms remain, so the factor is local.
4. **Type 2** is the `−` chain (with the times swapped), then the `+` chain with that bottom (`MCExp.type2`).
5. **Distinct variables** come from address subtrees (`RegCpl.chosen_sub`, `ChainFacts`).
6. **Constants** (`RegCpl.NB_le`): wf excludes two empty chains, and each chain pair pays `C₀²`.

### Checks
- `nice -n 5 lake build WaveTurbulence.Foundations.ClassJR.MCProp51` → `Build completed successfully (3812 jobs).`
- `python3 dupscan.py` → `duplicate scan: OK`, `sorry scan: OK`.
- `grep -rn "sorry|admit|maxHeartbeats|axiom|opaque|unsafe" ClassJR/MC*.lean` → none.
- One `set_option linter.unusedSectionVars false in` on the mutual block of MCMain. It is a linter, not a budget.

### Axioms (`#print axioms`)
`RegCpl.maincoef`, `RegCpl.maincoef_DH23`, `maincoef_of_structure`, `RegCpl.mcexp`, `RegCpl.NB_le`,
`MCExp.chain`, `MCExp.type2`, `MCExp.type1`, `MCExp.one`, `MCRep.chainOne`, `srep_assemble`:
`[propext, Classical.choice, Quot.sound]`.

### Named obligation
`existsUnique_regCpl_decodes (G : Garden 2) (hG : IsRegularCouple G) : ∃! Q : RegCpl, Q.wf = true ∧ Q.Decodes G`
(REG-STRUCT, audited PASS).
- It enters as the hypothesis `hstruct` of `maincoef_of_structure`, over an abstract carrier type.
- `Garden` (B1) is only on the unlanded `w/freeze-b1`, and `RegCpl.Decodes` and `IsRegularCouple` are only in the B2
  draft, so the library cannot name them yet.
- Instantiation is mechanical once B2 lands. The copied `RegCpl` must then be replaced by the landed one.

### Uncertainties
- **`B̃_Q` is defined on codes by (newexp1)/(newexp2)**, the same route as B2's `𝒥ℬ*`. DH21 "deduces" these
  recursions from (defcoefb2)/(deftildeb) (L923–L937). Identifying them with a garden-level `B̃` is not in this
  packet.
- **Conventions** mirror B2's `linksAt`/`pairsAt`:
  - the `+` root is the first argument;
  - only `Q₂` is time-swapped in type 1;
  - a chain couple is swapped iff `slotSign ζ red.1 ≠ 1`;
  - `Q_lp` is not swapped, because a chain's lone leaf has the root's sign (checked on all 6 mini-tree codes).
- **The type-1 phase** is `e^{πiα_x(t₁−s₁)}`, which assumes `ζ_x = +` for the `+` root, as in B2's codes.

### Suspected errata and deviations
1. **F61. QUESTION:** DH21 (regchaincalref) and Lemma 7.3 (L1732–L1746) use `+I_{μ_j}` for `j ∈ Z`, but Lemma 5.8 gives
   `−I_{μ_j}`, so `𝒥B̃_{Q,Z} = (−1)^{|Z|} 𝒥B̃_Q` (Prop 7.5 "independent of Z" is false; (reducedom) and TARGET
   (regref1-3) are off by `(−1)^{|Z|}` per term; Props 7.8–7.10 unaffected). See `wt-scratch/wke/F61-sign-trace.md`.
   In Prop 5.1 the factor is exactly (maincoef1)'s; the sign is inside `B̃_{Q,Z}`.
2. **Brief vs source:** the brief cites (maincoef2.5) weight `α^{1/8}`; DH23 L955–L969 has `max⟨α_𝔫⟩^{1−η/2}` and
   `⟨max(λ₁,λ₂)⟩^{η/4}`, (maincoef2) `⟨max⟩^{1−η/8}`. I followed the source.
3. **Trivial couple:** (maincoef1) for `Q` trivial needs `𝒞 = δ` (DH21 L937, `B̃ ≡ 1`). I use `1 = ∫∫ M₀⊗M₀ e2` on
   `[0,1]²` (integrable symbol, constant `N1 θ`). Hence the constant is `C₀^{2n(Q)+1}` (`n(Q)` = order = `2n` for scale `2n`)
   instead of `C^n`.
4. **Deviations (harmless):**
   - `⟨max(λ₁,λ₂)⟩` is read as `1+|λ₁|+|λ₂|`;
   - Gevrey bounds are `N A^k (2k)!`;
   - (maincoef2.5) is per variable, and the max costs a factor `|𝒩^ch| ≤ n`;
   - `MCRep` carries `SymReg` (W3);
   - the `λ₂` weight comes from the split (W4);
   - the difference loss `log(2+|λ|)` is replaced by `C⟨λ⟩^δ` with `δ = a` (needs `a > 0`; DH23 `a = η/4`);
   - (newexp2) is in CPS form (`chainT`);
   - each `Ĩ_Y` is class J **plus** class R (as in J2);
   - the constant needs `wf` (it excludes two empty chains); `RegCpl.mcexp` holds for all codes, with constant
     `Q.NB θ a b`.

READY maincoef
