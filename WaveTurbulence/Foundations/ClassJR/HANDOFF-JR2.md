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

## J3 MAINCOEF: the statement (in progress; for wt-torus / J4). Updated 2026-11-04, head 05f1b1a

The objects below are committed on `w/jr-ops` under `Foundations/ClassJR/` and will not change. Only the final
code-level theorem name is still open; it lands with `MCB2.lean`.

**Definitions** (`MCDefs.lean`, a0d2a72). Variables are points of a type `V` with signs `ζ : V → ℤ`. For codes,
`V = Fin 2 × Path` (node addresses).
- `e2 λ t s = e^{πi(λ₁t+λ₂s)}`.
- `wL a λ = (1+|λ₁|+|λ₂|)^a`, the stronger reading of DH23's `⟨max(λ₁,λ₂)⟩^a`.
- `PhiZ ζ z x = phiR (ζ z * x)`, which equals `χ_∞(x)/(ζ_z π i x)` (`phiR_sign`).
- `MCRep θ a b A N S F`: on `[0,1]²`, `F α t s = ∫ 𝒞(α∘f, λ) e2 λ t s dλ`, where `f : ι ↪ V` has range `S` and
  - `SymReg 𝒞` (audit W3);
  - (maincoef2): `∀ k, ∫∫ wL θ ‖∂^k 𝒞‖ ≤ gev N A k`, where `gev N A k = N A^k (2k)!` (deviation D1 of JR-OPS);
  - (maincoef2.5), per variable: `∀ i, ∫∫ wL a (1+|α_i|)^b ‖𝒞‖ ≤ N`. The max over variables follows with a
    factor `|S| ≤ n`.
- `MCExp θ a b A N ζ S F` is DH21 (maincoef3):
  `∃ G, (∀ Z ⊆ S, MCRep θ a b A N (S∖Z) (G Z)) ∧ ∀ α, ∀ t s ∈ [0,1], F α t s = Σ_{Z⊆S} (∏_{z∈Z} PhiZ ζ z (α z)) · G Z α t s`.
  `G Z` is DH21's `B̃_{Q,Z}`.
- Recursions:
  - `type1F v sw F` is (newexp1), with `swapT` for the `(t₁,s₁) ↔ (s₁,t₁)` swaps;
  - `chainT` (`MCChainT.lean`) is (newexp2) in CPS form over Catalan codes.
  - Type 2 is `fun α t s => chainT c⁺ 0 F⁺ α t (fun t' => chainT c⁻ 0 F⁻ α s (fun s' => F_lp α t' s'))`.

**Planned statement.** Prop 5.1 for `B̃_Q`, defined on B2 codes (copied under ClassJR) by (newexp1)/(newexp2):
`MCExp θ a b A (C^n) ζ (chosenSet Q.links) (B̃_Q)`, where
- `n` is the half-scale;
- `θ = 1 − η/8`, `a = η/4`, `b = 1 − η/2`; the proof only uses `0 ≤ θ < 1`, `0 ≤ a, b`, `a+b ≤ θ`, `a+b < 1`,
  `b ≤ θ`;
- `A ≥ A1`.

The garden form goes through the named obligation `existsUnique_regCpl_decodes`.

**F61, for J4.**
- The factor in front of `B̃_{Q,Z}` is exactly DH21 (maincoef1): `∏_{n∈Z} χ_∞(α_n)/(ζ_n π i α_n)`.
- The minus sign of Lemma 5.8's `T₀ = −I_μ` (`iker_comp_decompP`, conjunct `KEqOn (T₀ μ α) (−iker μ)`; Chain2's `T0`)
  sits *inside* `B̃_{Q,Z}`.
- So for dominant couples `B̃_{Q,Z} = (−1)^{|Z|} · 𝒥B̃_Q`. This sign is missing from DH21 (regchaincalref) and
  Lemma 7.3.

**Committed so far.**

| commit | module | content |
|---|---|---|
| — | MCE | gE |
| — | MCSob | SymReg from integrated bounds |
| — | MCG | Lemma G for class J |
| — | MCProd, MCK1, MCReorder, MCSRep | products, the type-1 coupling, reorderings, `SRep` |
| 0598ac3 | MCCase1 | `SRep.case1`, `integral_C1_e2` |
| 0a64ebf | MCType1 | `MCExp.type1`: Case 1 done |
| 7c20cae | MCGR | Lemma G for class R |
| 301f4ba | MCDiff | (differenceloss): `log` replaced by `⟨λ⟩^δ` |
| f706ad7, fe25d91 | MCChainT | `chainT`; `chainT_exp`: with exponential pair coefficients, `chainT` is the Volterra operator of `pchain` (DH21 kusingI) |
| 3fedef3, 6a330cd | MCChainF | frequency space `ZT c`; `chainT_fubini` (DH21 L1121–L1124: fixing the pair frequencies); `chainT_exp_fubini` |
| 30821e3 | MCGP | Lemma G for masked parametric class J + R (`MJR.lgpieces`, DH21 Cases 2.1/2.2) |
| c0ba025 | MCPair | `MCRep.mul`, `MCExp.mul` (products: the pair coefficients of (newexp2)), `MCExp.swapTimes` |
| 5fab1bd | MCChainX | `chainT_expand`: expansion of the chain integral over the pair masks (DH21 (newexp4)) |
| 36987a8, 05f1b1a | MCChainM | pair symbols (`PBound`), the pair symbol with the difference `Φ(εα+λ₁)−Φ(εα)` (`PBound.pd`), the product over a code (`tbound_MzS`) |

**Next.**
1. One-sided chain theorem (fixed masks): `(t,s) ↦ chainT c 0 R α t (t' ↦ G α t' s)` is `Σ_{Y'⊆adj} ∏_{j∈Y'} PhiZ · MCRep`.
2. Type 2 from it: the − chain first (times swapped), then the + chain with that bottom coefficient; then masks.
3. The `IsBC` induction (Prop 5.1 for the recursion).
4. MCB2: `B̃_Q` on copied B2 codes; the garden statement through `existsUnique_regCpl_decodes`.

**Shape of the type 2 statement (planned, for J4).** For a type 2 couple with chains `c⁺, c⁻` (pairs `j`, variables
`σ^± j`, signs `ε^± j`, required `ζ (σ^± j) = ε^± j`) and lone pair `lp`:
`B̃_Q α t s = chainT σ⁺ ε⁺ c⁺ 0 F⁺ α t (fun t' => chainT σ⁻ ε⁻ c⁻ 0 F⁻ α s (fun s' => F_lp α t' s'))`, where `F^±_j` are the
pair coefficients (products of the two subcouple coefficients, times swapped by the leaf signs) and the conclusion
is `MCExp θ a b A N ζ S B̃_Q`. The `PhiZ` factors of the chain variables come only from adjacent pairs (`adjSet`,
DH21 Lemma 5.10); the `T₀ = −I_μ` sign stays inside `G_Z`.
