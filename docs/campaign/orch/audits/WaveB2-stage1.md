# Audit: Wave B tier B2, stage 1 (regular couples and trees, `WaveB2-Regular.lean`)

Auditor: `wt-orch` (Opus), refute-first. Date: 2026-11-03. Task 8a.

## Inputs

**Snapshot.** I took it from `/home/scott/wt-scratch/waveb2/` into `/home/scott/wt-scratch/waveb2-snap-1/`, with
`SHA256SUMS`:

| File | Lines | sha256 |
|---|---|---|
| `WaveB2-Regular.lean` | 577 | `4558005d…a8640d` |
| `WaveB2-Regular-probes.lean` | 240 | `7519448f…69db9c3f` |
| `DESIGN.md` | 141 | `ad642e5e…badb53c15` |
| `build.sh` | — | `c804a0fb…9de172c` (read only; not run) |

**Sources.**
- TARGET §4: Def `defreg` L826–L829, Def `subobject`, Def `defregchain` L848–L850, Prop `propstructure` L852–L869,
  Prop `deflink` L874–L882, Def `defcoh` L885–L887.
- TARGET §6.2: Defs `defencpl`/`defentree` L1126–L1140, Props `regref1`–`regref3` L1145–L1232.
- DH21 §4–§7, through these citations.
- My `figure-defs.md` §5–§6 (mini codes, operations, chains, colour rule M1).
- FINDINGS F12, F16, F37–F40.

**Build.**
- Against my snapshot-2 B1 modules (`WaveBDraft.*`, Task 6b) plus the landed `Foundations/Resonant/{Integral,
  PrincipalValue}`, recompiled at `main` (`db611cd`; the WKE/Frozen/Resonant sources are unchanged since Task 7).
- `WaveB2Draft.Regular` elaborates. Its only `sorry`s are the five §4 characterization obligations (L366, L372,
  L377, L382, L387).
- The probe file elaborates with no `sorry` and no warning.

## Verdict

**APPROVED as a stage-1 definition set. No REQUIRED fix.**

I found no WRONG item:
- The mini-couple and mini-tree tables agree entry by entry with figure-defs §5. All 2 + 6 codes, the lone slots,
  and the red/green pairs match, and the colour rule "red = leftmost leaf child of ρ" holds.
- Operations A and B are the source operations, including B at a leaf (figure-defs §5).
- The code carrier (`RegCpl`/`RegChain`, legal partitions in Catalan form) and its decoding reproduce the source
  objects. My probes P1–P3 check this on non-trivial codes, by kernel `decide` against explicit source derivations
  by operations A and B. They cover a nested (non-dominant) chain, a type-2 couple with two chains (one of sign −),
  and a type-1 couple with a nested green sub-couple.
- Links, 𝒩^ch, dominance, special subsets, the incoherency index, 𝒥ℬ* (regref2-0)–(regref2-2), ℳ* (regref3-0)–(regref3-4)
  and (K*)_app (regref1-3) are literal transcriptions.

The six OPTIONAL items (§3) concern:
- the scope of the principal-value characterization;
- probes for non-trivial codes;
- the F16 link property as an obligation;
- the enhanced-object equivalence that stage 2 will need;
- small documentation points.

## 1. Verdict table

| Decl | Verdict | TeX / figure | Reason |
|---|---|---|---|
| `MiniCplCode`, `partner` | FAITHFUL | Def `defreg`, `MiniCpl.png`; figure-defs §5 | Code 00 is L↔L′, R↔R′; code 01 is L↔R′, R↔L′; M↔M′ always (`partner c x = x` or `2 − x`). Probes: `card_miniCouple_pairings = 2`, `miniCplCode_pairings`. |
| `MiniTreeCode` (`c`, `b`), `lone`, `red`, `green` | FAITHFUL | `MiniTree.png`; figure-defs §5 table | I checked each of the 6 rows: codes 10, 11, 20, 21, 30, 31 have lone ν-L, ν-R, ν-M, ν-M, ν-R, ν-L. Red is (ρ-M,ν-R), (ρ-M,ν-L), (ρ-L,ν-L), (ρ-L,ν-R), (ρ-L,ν-M), (ρ-L,ν-M). Green is (ρ-R,ν-M) twice, (ρ-R,ν-R), (ρ-R,ν-L), (ρ-M,ν-L), (ρ-M,ν-R). Probes: `card_miniTree_pairings = 6`, `miniTreeCode_legal` (signs; red leftmost), `miniTreeCode_injective`. `c : Fin 3` encodes the first digit 𝚌 − 1. |
| `slotSign`, `node3`, `addrExt`, `TTree.setAt`, `TTree.subtreeAt` | FAITHFUL (junk only off nodes, never used there) | L627 | — |
| `RawCpl`, `RawCpl.opA` | FAITHFUL | Def `defreg`, `OperAB.png` | The oriented pair (x, y) with x the + leaf is replaced by two order-1 trees with the code-c pairing. The new pairs are stored + leaf first; the "first tree" is the + tree (my M1 recommendation). |
| `RawCpl.relocate`, `orient`, `opB` | FAITHFUL | Def `defreg`, `OperAB.png`; figure-defs §5 | B at **any** node: the subtree S at a is re-attached at the lone leaf a ++ [c, lone], and pair entries below a (including a's own pair if a is a leaf) are relocated. The lone leaf has a's sign, so S keeps its signs. The new red and green pairs are oriented by `slotSign`. |
| `RawRegular` | FAITHFUL | "formed, starting from the trivial couple, by operations A and B" | An inductive closure. A acts at a listed pair; B at any node of either tree, the roots included. |
| `symmPairs`, `Garden.MatchesCouple`, `IsRegularCouple` | FAITHFUL | Def `defreg` | `IsCouple G`, equal trees, and every leaf's partner listed (unordered). This pins G because regular raw data are perfect matchings (O6). |
| `Garden.MatchesTreeCouple`, `IsRegularTree` | FAITHFUL (reading Q1, accepted) | Def `defreg` ("𝒯 forms a regular couple with •") | (𝒯, •) for sign +, (•, 𝒯) for sign −, with the lone leaf paired with •. In the couple the • leaf must pair with the unpaired leaf, so this is forced. |
| `RegCpl` (`triv`, `type1`, `type2`), `RegChain` (`nil`, `pair m Qr Qg inner rest`) | FAITHFUL as a carrier of structure data | Prop `propstructure` (a), (b); Def `defregchain` | `type1` is (a). `type2` is (b), with the chains as **legal (non-crossing) partitions in Catalan form**: the first node pairs with b, the nodes strictly inside form a non-crossing partition (`inner`), the nodes after b form another (`rest`). This form is unique, and preorder = increasing a (T L855). The mini-tree code of a pair is the rearrangement of figure-defs §6. Sign consistency: c = M ⟺ lone = M (table), so inner pairs contribute an even number of M-steps and sign(𝔫_b) = sign(𝔫_{a+1}). I re-derived this, and probe P1 confirms it. |
| `RegCpl.trees`, `RegChain.plug`, `lonePath`, `RegCpl.pairsAt`, `RegChain.pairsAt`, `RegCpl.raw` | FAITHFUL (checked on codes) | — | Type 1: L (+) gets Q₁⁺; M (−) gets Q₂⁻; R (+) gets Q₃⁺. The − tree gets Q₁⁻, Q₂⁺, Q₃⁻ in code order (00) or with Q₁ and Q₃ swapped (01). Chains: the + tree of each sub-couple goes to the + leaf of its pair. Probes: snapshot `triv`/`miniCouple00`/`miniCouple01`/`miniTree10` decodings; my P1, P2, P3. |
| `RegCpl.Decodes`, `Garden.MatchesPairedTree`, `RegChain.DecodesTree` | FAITHFUL | — | The lone leaf is marked `lower` at `lonePath`; the other marks are `none`. |
| `RegCpl.wf`, `RegChain.wf` | FAITHFUL | `propstructure` (b): "unique nontrivial 𝒬₀", "Q_lp type 1 or trivial" | `!(Xp.isNil && Xm.isNil)` and `!Qlp.isType2`. Without them decoding is not injective (`type2 nil nil triv` would decode to (•,•)). I found no further non-injectivity: in type 1, swapping Q₁ and Q₃ while toggling c changes which subtree the leaves under L pair into. |
| `RegCpl.size`, `RegChain.size` | FAITHFUL | — | +2 per type-1 node and per chain pair. Probe P3: `type1_order`. |
| §4 obligations (`RegCpl.exists_decodes`, `existsUnique_regCpl_decodes`, `RegChain.exists_decodesTree`, `existsUnique_regChain_decodesTree`, `RegCpl.size_eq_order`) | Correctly stated (DH21 Props 4.5, 4.7, 4.8, Cor 4.9) | `propstructure` | `wf` appears exactly where uniqueness needs it. `size_eq_order` needs no `wf`, which is right since size counts nodes for any code. With `Decodes` and quantification over pairs (code, carrier), the structure data are functions of the couple without `choose`. This is a good design. |
| `RegCpl.linksAt`, `RegChain.linksAt`, `links`, `treeLinks` | FAITHFUL | Prop `deflink` (inductive rule) | Type 1 links the two roots, with the + root first (chosen). Chains link (𝔫_a, 𝔫_b) with 𝔫_a chosen, and the recursion runs through all sub-couples, `inner`, `rest` and Q_lp. Probes: `miniCouple00_links`, `chain10_links`, my `type2_links_card`. |
| `chosenSet` (𝒩^ch) | FAITHFUL | `deflink` last paragraph | — |
| `RegCpl.dominant`, `RegChain.dominant` | FAITHFUL | `propstructure`, L859–L860 | A dominant chain has 𝒫 = {{1,2},…}, i.e. every `inner = nil`. Probes: `dominant_examples`, my `nested_not_dominant`. |
| `IsSpecialSet`, `specialSets` | FAITHFUL | Defs `defencpl`/`defentree` (L1127, L1137) | Z ⊆ 𝒩^ch with each z linked to some z ++ [i]. Type-1 roots are never special, because their link crosses trees; this is consistent with (unionz). Probes: `miniCouple00_specialSets = {∅}`, `chain10_specialSets_card = 2`, my `type2_specialSets_card = 4` and `type1_specialSets = {∅}` (nested type 1). |
| `LayeredGarden.incoherency` | FAITHFUL | Def `defcoh` L885–L887 | The number of links whose endpoints lie in different layers; 0 means coherent. |
| `RegCpl.JB`, `RegChain.JBchain`, `RegChain.JBtree` | FAITHFUL on dominant codes | (regref2-0), (regref2-1), (regref2-2) | Type 1 is 2∫_r^{min(t,s)}∏_j 𝒥ℬ*_{Q_j}(τ,τ). Type 2 is the nested integral over t > t₁ > ⋯ > t_{m₊} > r and s > s₁ > ⋯ > s_{m₋} > r of the chain factors, times 𝒥ℬ*_{lp}(t_{m₊}, s_{m₋}), which equals 𝒥ℬ*_{lp}(min(…)) because Q_lp is trivial or type 1. The empty chain gives t₀ = t. Trees: the lower limit is s. Probes: `JB_triv`, `JB_miniCouple` (= 2(min(t,s) − r)), `JBtree_chain10` (= t − s). Values on non-dominant codes ignore `inner`; they are unused, because (K*)_app = 0 there. |
| `pvResonantIntegral` | FAITHFUL (reading; see O1) | (regref3-3) 𝙸 = 1; WAVE-B §2.8 | `∫ ℓ, energyInvSliceLimit (resonantKernel Ψ k) ℓ` in the `collisionOp` parametrization: k₁ = k+ℓ, k₂ = k+ℓ+x, k₃ = k+x, with Jacobian 1 for δ(k₁−k₂+k₃−k), and Ω = −2⟨ℓ,x⟩. The slice factor −(2‖ℓ‖)⁻¹ and the symmetric quotient give p.v.∫Ψ/Ω with the **correct sign**. Characterization probe: `tendsto_pvResonantIntegral`. |
| `RegCpl.Mstar`, `RegChain.Nstar` | FAITHFUL on dominant codes | (regref3-0)–(regref3-4) | Trivial: F_r(k). Type 1: the landed `resonantIntegral` (δδ, the D6 normalization, the same as `collisionOp`) of ∏ℳ*_{Q_j}(k_j). Type 2: ℳ*_{lp}(k)∏𝒩*. Factor 1 is δ(Ω) or p.v. 1/Ω according to 𝔫_a ∈ Z. Factor 2 places red at `![k₁,k₂,k₃] m.red.1` and green at `… m.green.1`: (k₂,k₃), (k₁,k₃), (k₁,k₂) for 𝚌 = 1, 2, 3. This is exactly (regref3-4), and no factor sits at the 𝔫_b slot. ℳ* is defined per enhanced object (Q, Z); class-dependence is regref3's theorem. |
| `zetaOfTrees`, `specialWeight` | FAITHFUL | Def `defgarden`; (regref1-3) | ζ(𝒬) = ∏(iζ_𝔫); the weight is ∏_{𝔫∈Z}(ζ_𝔫πi)^{−1}. |
| `RegCpl.app`, `RegChain.app` | FAITHFUL (route R4 / D1, accepted) | (regref1-3) | 2^{−2n}δ^nζ(𝒬)Σ_Z ∏(ζ_𝔫πi)^{−1}𝒥ℬ*·ℳ*[F_r] for dominant codes (size = 2n), and 0 for non-dominant ones (regref1-1: those have no leading term). For trees, ℳ*_𝒯 = ∏𝒩*_{(j,0)} and the lone leaf carries no input. Probe: `app_triv = F(k)`. |
| Probes: `finite_wf_codes` | OK | — | The `finsum` over well-formed codes of bounded size is genuine. |

**F37–F40.** These findings concern vines, twists and cuts. Stage 1 defines none of them, so none applies here. F38
(the uniform slot-swap twist) and F40 (half-edge cuts) will matter when B2 reaches molecules and twists.

**F12.** The figure-only shapes (mini codes, colours) are now textual, and their probes are exhaustive. This
discharges the stage-1 part of F12.

**F16.** See O3.

## 2. REQUIRED fixes

None.

## 3. OPTIONAL suggestions

- **O1. The principal value: characterization scope and carrier.**
  - `tendsto_pvResonantIntegral` (and the landed `energyPrincipalValue_spec`) assume `hs : R < ‖x‖ → kernel = 0`,
    i.e. compact support in the second momentum.
  - The kernels that actually occur, `Mr(k_x)·Mg(k_y)` built from F_r = φ(δr) + R_r, are decaying but **not**
    compactly supported. So the characterization does not yet cover the definition's real carrier.
  - The symmetric-quotient value is still the right p.v. there: for C¹ slices with integrable decay, all standard
    regularizations agree. For a non-integrable quotient the Bochner integral gives the junk value 0, but that lies
    outside the source carrier.
  - **Recommendation:** packet N5 or B2 adds the decaying-kernel version of `tendsto_energyInvIntegral` (replace
    `hs` by a `DeltaKernel`-type decay of the kernel in x), and the probe is restated for it.
- **O2. Add probes on non-trivial codes.** My P1–P3 (`scratch/WaveB2-stage1-probes.lean`) are the only checks of
  `inner ≠ nil`, of an `𝒳⁻` chain (root sign −) and of a nested green sub-couple. The snapshot probes cover only the
  trivial couple, the mini-couples and `chain10`. Copy them into `WaveB2-Regular-probes.lean`.
- **O3. F16: state the link property as an obligation.**
  - Links are defined combinatorially, as in TARGET's inductive rule.
  - Their **use** (L1252ff, the proofs of `regref*` and `layerreg*`) is the identity ζ_{𝔫′}Ω_{𝔫′} = −ζ_𝔫Ω_𝔫 for every
    decoration, and {x_{𝔫′}, y_{𝔫′}} = {±x_𝔫, ±y_𝔫}.
  - F16 records that DH21 states only the first.
  - **Recommendation:** add both as `sorry` obligations next to §4, quantified over `Q.Decodes G` and `IsDecoration G κ`.
    They pin the semantics of `links` and expose the F16 gap to the provers.
- **O4. Stage 2 needs the enhanced-object equivalence.**
  - Defs `defencpl`/`defentree` define ∼ by recursion: for type 2, a permutation of the tuples (𝙸, 𝚌, 𝔛₁, 𝔛₂), with
    m₊ + m₋ fixed and 𝔛_lp.
  - (regref2-3), the cancellation Σ_{𝒬∈𝔛}∏(ζπi)^{−1}𝒥ℬ* = 0, and regref3's class-dependence are stated over classes.
  - The draft defines ℳ* per (Q, Z), which is right for stage 1. Any B2 statement or proof obligation that quantifies
    over a class needs ∼.
  - **Recommendation:** with computable codes, give ∼ as equality of a normal form: a sorted multiset of tuples,
    recursively.
- **O5. Document the junk values.** Document `JBchain`'s junk on non-dominant chains (`inner` ignored) and
  `pvResonantIntegral`'s junk 0 for a non-integrable quotient in the docstrings. DESIGN §1.5 already says the first.
- **O6. `MatchesCouple` relies on the decoded pair list being a perfect matching of the leaves.** For regular raw data
  and decoded codes it is. A one-line lemma, or a conjunct of `RegCpl.exists_decodes`, would make that explicit, so
  that `Decodes` cannot be met by a G with a coarser pairing.

## 4. DESIGN questions (my answers)

- **Q1 (sign of regular trees): ACCEPT** (•, 𝒯) for sign −.
  - TARGET's "forms a regular couple with •" leaves the order open. Couples are (+, −), so a − tree must come second.
  - Codes are sign-independent, and P1/P2 confirm decoding with root sign −.
- **Q2 (first tree of a mini-couple = the + tree): ACCEPT.** This is my figure-defs M1 recommendation. Values are
  symmetric; uniqueness of the tuples needs the convention.
- **Q3 (pair order = increasing a = Catalan preorder): ACCEPT.** This is T L855. For dominant chains, pair j gets
  time t_j, with t₁ the largest, as in (regref2-1).
- **Carrier choice (B) codes + decoding + `Decodes`: ENDORSE.** It avoids `choose` on unproved uniqueness and makes
  every recursive object computable. The structure theorem becomes an honest obligation.

## 5. Non-vacuity probes

**Snapshot probes.** `WaveB2-Regular-probes.lean` elaborates, sorry-free. It covers:
- the exhaustive tables;
- decoding of `triv`, `miniCouple00`, `miniCouple01` and `miniTree10`;
- `IsRegularCouple`/`IsRegularTree` examples by operations A and B;
- links and special sets;
- 𝒥ℬ* values;
- `app_triv`;
- `finite_wf_codes`;
- the p.v. characterization.

**My probes.** `scratch/WaveB2-stage1-probes.lean` (untracked, sha256 `cbc83a59…4628d8`). Each decides the decoded
carrier and proves the source predicate by an explicit operation sequence. Axioms: `[propext, Classical.choice,
Quot.sound]`.

- **P1: a non-dominant chain {1,4},{2,3}** (`.pair ⟨0,0⟩ .triv .triv chain10 .nil`).
  - `nested_decodesTree`;
  - `nested_isRegularTree`, by B at the + root (code 10) and then B at the inner node (0,[0]) (code 10);
  - `nested_not_dominant`, `nested_wf`.
- **P2: type 2 with two chains** (`.type2 chain10 chain10 .triv`).
  - `type2_decodes`;
  - `type2_isRegular`, by B at both roots;
  - `type2_links_card = 2`, `type2_specialSets_card = 4`.
- **P3: type 1 with a nested green couple** (`.type1 0 .triv (.type1 0 …) .triv`).
  - `type1_decodes`;
  - `type1_isRegular`, by A at (•,•) and then A at the green pair ((1,[1]), (0,[1]));
  - `type1_order`;
  - `type1_specialSets = {∅}`.
