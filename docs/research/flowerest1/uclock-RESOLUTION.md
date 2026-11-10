# U-clock: the native lower clock in the weighted Stage-1 reduction (erratum E26)

Packet `uclock` (FLOWER-OPEN), for wt-orch, 2026-11-07. Read-only everywhere except this file. No Lean was built and no
git state was changed.

## 0. Result

E26 is real: the printed identity (redvine) T1954–1957 is false as an identity, because the exterior slot at a lower
external child `c ∈ {u21, u22}` of a spliced unit reads the clock `τ_b = t_{u2}` that the unit integrates. Main's Lean
proof of `layergarden_v2` does **not** use (redvine). It proves a corrected identity, (redvine♯) below: the lower slots
are Fourier-expanded in their native clocks, the `τ_b` frequencies are routed into the unit as a modulation
`e^{πiλτ_b}`, and the modulated vine estimate pays `(1+|λ|)^{6η⁶}` out of the slots' time-Fourier moments. Its end
product is exactly the conclusion of the printed (redvine2). Section 2 cites the declarations.

This file proves the weighted, pinned, Stage-1′ version, **Theorem U-clock** (§4), which is the premise listed in
SUPPLEMENT-v2 §12.3. There are two new points beyond main.

1. **Weights.** Frontier cutoffs and the stem top filter are time-independent. They split into an exterior part and a
   per-unit part. The per-unit part is carried by Lemma 5.3, which still holds with a modulation (Lemma U.3).
2. **Protected lower slots.** These are the slots the supplement flags. A lower slot that contains a protected vertex
   but no pin is an ordinary regular object; protection changes only marking and twisting. The **pinned** lower slots
   are of exactly three kinds (§6.3):
   - (L2) the cap couple of an original tree, at a lower **leaf**;
   - (L3) O104 case (P6), at a lower branching child `c = φ`;
   - (L4) O104 case (P8), a couple at a lower leaf whose far tree is rooted at the `dChild`-pinned sibling `m`.

   (L2) and (L3) occur only without the second cutoff (O75 Lemma 2(d)); (L4) only for nonplain patterns. In all three,
   every explicit boundary phase is a function of the fixed flower time `s` (and of fixed layer endpoints). None
   depends on `τ_b`. After the phase is removed, the slot has a positive time weight `η` in `τ_b`, uniformly in the
   consumed modulations (O73 Lemma 12.1, Props. 13.2/17.1(b); O104 Lemma 7.1, Props. 7.4/7.6 revised). For (L2), the
   defining triangle `τ_b > s` is moved into the unit: the unit's leaf clock is set to `s` instead of the floor value of
   E14. The redundant constraint `t_{u1} > s` is recorded at the `G_sb` level. In the second-cutoff version, a lower
   couple can also be adjacent, through its far clock, to a selected residual vertex. There the slot's `X^{1/4}` bound
   pays both the unit modulation (weight `12η⁶`) and O73 Prop. 20.1's moment `⟨ξ_v⟩^{1/18}`.

No new power of `L` appears, every gain is retained, and the Section 10 budget `B = 21006d+546.01` (nonplain
`24266d+630.01`) is unchanged. The pinned lower slots cost `L^{31d+6}` each, but this is drawn from the Theorem 7.3′
allowance `L^{400d}` of their own pin incidence (§11).

---

## 1. Inputs (pinned at first read, sha256)

| Input | Path | sha256 |
|---|---|---|
| T (TARGET) | <sources>/paper/source/WKE-Longer_times_Final_arXiv.tex | `493eef6b7dec448bc5f9f1c3974c0cad7a85eca9bc428f5b35e968aad76727cb` |
| SUPPLEMENT-v2 (live; pinned copy in my session scratchpad) | <scratch>/flower-open/SUPPLEMENT-v2.md | `b1d6d780e9f08fa447d075d14d0d72242b876900ae89b260982120c6b2047511` |
| O73 | flower-open/o73/RESOLUTION.md | `2735f3321bd5cc9eab77f87037e92695083c0a70abad4562a6f8d8ab30285e23` |
| O75 | flower-open/o75/RESOLUTION.md | `47513e351d6a3e0b2dc2bef465e9278e880812f4ab3fa9ad69a6a3528587c96d` |
| O104 | flower-open/o104/RESOLUTION.md | `2d711cbdd4c38275cbc1a6b3659eab9183b414e428bd6bdc561cbd2a05b2c5f2` |
| E26 / E14 (errata) | <worktrees>/report/docs/ERRATA-AND-DEVIATIONS.md (E26 at 1420–1464, E14 at 1036–1047) | `2d77a162e123c84f13f3e6d8f765271b50d63e97da95d809b89db083aa41a140` |
| Lower-clock handoff | …/report/docs/research/redvine-lower-clock-handoff.md | `246db1920132016a7e69ba08b74454a16cd1b5613fa8a57a84d4c1ee9ea5b005` |
| RULINGS (R58 at 1427) | <worktrees>/orch/docs/campaign/orch/RULINGS.md | `3b179a5d93eb4a52450a9f0d2919d8b207e4aa848276fd7a8b957924412b61d1` |
| S-V5W SCOPE | <scratch>/flower-core/scope/S-V5W/SCOPE.md | `5ea1262f5ead9e95b710c55cdc5db02af57e5dc3846338d11fca9ebe19e37d33` |
| Main (Lean) | <repo>, HEAD `796c0f5f5d0c66a4ee92438b2e8cfcf71f0a7c2b` (seal audit of `layergarden_v2`: orch `docs/campaign/orch/audits/Seal-layergarden_v2.md`) | — |

Line numbers "T…" refer to T, "S…" to the pinned SUPPLEMENT-v2, "O73 L…" etc. to the packet files above.

---

## 2. What main's Lean proves: the unweighted U-clock

### 2.1 The chain, by declaration (all read with `git grep`; all on main, all in the sealed closure of `layergarden_v2`)

The seal audit (orch `audits/Seal-layergarden_v2.md` (d)) records the proof chain
`layergarden_v2_proof := Spine.layergarden_v2_of_V5 vineEstCanonLayerHalfMK`, with
`stage1ReductionGate_of_V5' hV := Represents.stage1ReductionGate_of_V5 vineparam leafwise_incoherent_decay
leafwise_coherent_approximation hV`. Inside that, the E26 repair (ruling R58, repair (A)) is the following.

| U-clock component (S §12.3) | Main declaration | File:line |
|---|---|---|
| Native parent clocks in the exact integrand | `WaveTurbulence.VineB.skelVal` with `slotFn` (slot times `slotTs` = native parent clocks, T (redkg) L1725–1726) | `Foundations/Vine/B/Modal.lean:38` |
| Only lower joints are interior clocks read by outer slots | `WaveTurbulence.VineB.argSrc_outer`, `…SpliceShape.argSrc_iota`, `…freqAt_inter`; routing `…SpliceShape.route` | `Vine/B/Slots.lean:144,222`; `Vine/B/SlotMap.lean:167,182` |
| The per-mode identity (one member) | `WaveTurbulence.VineB.SpliceShape.skelVal_modal_eq_outerValM` | `Vine/B/Main5.lean:40` |
| Fourier expansion of the native slots, summed over modes (one member) | `WaveTurbulence.Represents.hasSum_skelVal_outerValM` | `Stage1/Represents/RepVB8.lean:31` |
| The identity summed over the class (modulated class kernels) | `WaveTurbulence.Represents.class_sum_modes` (via `sum_tauClass_vineD_api_dep`, `VineC.sum_tauClass_vineD_api`) | `RepVD10.lean:32`; `RepVB12.lean:29`; `Vine/C/VCApi.lean:87` |
| Modulation and the modulated per-unit kernel | `modLam`, `routedPhase`, `outerValM`; `VineEstS5C.Cont.lowModC` (`e^{πiλτ_b}`), `…clLocalKernelModC`, `…twistedRecenteredModC`, `…twistedRecenteredModC_zero` | `RepOuterM.lean:34,39,46`; `VineEst/VineEstS5C/Cont/ModKernel.lean:35,43`; `Cont/ModClass.lean:32,40` |
| Modulated Lemma 5.3 (unweighted) = VINEEST(λ) | statement `WaveTurbulence.VineEstS5C.VineEstCanonLayerHalfMK` (loss `(1+|λ|)^{6η⁶}`); proof `WaveTurbulence.VineEst.vineEstCanonLayerHalfMK : WTPrefix VineEstCanonLayerHalfMK` | `VineEst/VineEstS5C/P4/W2/ModStatement.lean:154`; `VineEst/V5Proof.lean:28` |
| Slot moments (time weight `η`) | `WaveTurbulence.Represents.SlotRepM`, `slots_existM` (θ = η); producers `exists_supM`, `exists_cenSupM` (from `XNormRestr θ`) | `RepSlots2M.lean:29,52`; `RepSupM.lean:31,38,81,101` |
| Consumption of the modulations | `WaveTurbulence.Represents.tsum_modes_moment` (c = 6η⁶, 2c ≤ θ = η; `prod_modLam_le`, `prod_one_add_abs_le_maxBracketPow`) | `RepMom2.lean:26`; `RepMom1.lean:52,91` |
| Unit kernels → hinge families | `exists_hinge_data_mod` (masses `C(1+|λ_j|)^c M0_j`); leaf lower child decoupled: `exists_hinge_data_units_leaf` | `RepVN8.lean:29`; `RepLfClk2.lean:32` |
| Assembly into (redvine2) | `repIntC_vine_modes`, `representsIntA_of_vineModes` | `RepVN7.lean:33`; `RepVN10.lean:30` |
| **Conclusion** | `WaveTurbulence.Represents.VineCaseRepresents` (statement), proved by `vineCaseRepresents_of_gate` and `vineCase_prefix` | `RepS10c.lean:45`; `RepVD15.lean:76`; `RepVD16.lean:27` |

### 2.2 The main statement equivalent to the unweighted U-clock

`WaveTurbulence.Represents.VineCaseRepresents P` (RepS10c.lean:45) says the following for every vine piece π of the
Stage-1 producer. The class sum of the native leafwise kernels,
`∑ LG ∈ membersP (clsP π), U.toLF.valueSel tt base roots LG (selP … π LG)`,
satisfies `Stage1Piece.RepresentsInt` (Spine/Stage1Interface.lean:129). That is, it is an integral, against a weight of
total mass at most
`(C₁√δ)^{n−n_sb} C₁^{n_sb+2R} L^{−η⁸g_sk−(η²/2)b_sk+η⁷q_sk} s`,
of normalized spliced kernels of `G_sb` with arbitrary frequencies at the branch clocks. This is the corrected
(redvine2), with the E25 halving. It is closed on main by the term

`WaveTurbulence.Represents.vineCase_prefix Spine.leafwise_incoherent_decay Spine.leafwise_coherent_approximation
Vine.Param.vineparam VineEst.vineEstCanonLayerHalfMK : WTPrefix VineCaseRepresents`,

all four arguments being proved theorems (Spine/SourceProviders.lean:26,34; WaveTurbulenceVineParam/VineParamMain.lean:19;
VineEst/V5Proof.lean:28). The identity part alone is `Represents.class_sum_modes`. **The unweighted U-clock is therefore
proved on main.** It covers the unweighted Stage 1 with leafwise type profiles, no marks, no pins, caps, patterns or
dagger.

### 2.3 What main does not contain (the content of this packet)

- Frontier cutoffs, stem filters, the affine top amplitude (9.2), and the shell expansion.
- Stage 1′ marking. Runs are the units; marked vines stay unspliced (O75 §2.5).
- Pins, caps, derivative patterns, and dagger. In particular there is no lower slot that is a protected regular object,
  and no unit whose leaf lower child carries a constraint.

Lean counterparts in progress:
- S-V5W §1–2 pins the weighted modulated unit kernel `twistedRecenteredFW … (modW lam)` and its bound
  `V5FrontierClassBoundAt`, with T4 `WeightedClassFactorization`.
- S-STAGE1W keeps main's `RepresentsInt` as the piece conjunct.
- Both are for `Π = ∅`. The pinned lower slots of §6.3, and the capped-leaf argument `t' = s`, are new (§14).

---
## 3. Setting and notation

**The component.** Fix one irreducible component `𝒢` of a capped flower garden (S Lemma 2.1, S65–83). It is canonical,
at level `p+1`, of width `2R` and order `n ≤ N^4`. Fix the version (no cutoff, first cutoff, or both cutoffs), the
pattern vector `pat` (S §11.1), and the optional dagger data. The integrand `Θ` is that of O75 §2.1 (O63 §1.1):
- normalization `c := δ/(2L^{d−γ})` per branching node;
- `ζ` and `ε`;
- the layered time domain with the pins of S §11.1 (all pins at the external times `t, s`; parent–child inequalities
  kept whenever one node is free);
- common real profiles `G ∈ 𝒫(C)` with `C ≤ 2c_χC₁` (S §6, (6.3)).

The multiplier `W` is first expanded by S Lemma 3.2 into a signed sum of low-pass products. In each product, original
tree `j` carries its frontier product `A_{j,R_j}` (S (3.1)) and, in the second-cutoff version, a stem-filter product
`U_{j,R'_j}` (S (8.5)), with a fixed scale per tree. We work with **one** such product. All bounds are uniform, and the
signed sum costs only the order-independent `2^{O(P)}` and polynomial factors of S Lemma 10.1. Dagger indicators
(S §11.1) are part of `W`.

**Stage 1′ (O75 §2.5, O75 L124–166).**
- `Π` is the protected set (O75 §2.2), with `b = |Π| ≤ 26P`, or `≤ 30P` for patterns.
- A vine of `𝒱` is marked when its twist-active set `𝐀(𝕍)` (O75 Def. 2.3, L99) meets `Π`.
- The **units** are the runs `U_1,…,U_q` (`q = q_sk`): maximal concatenations of unmarked SG vines of one chain. Each
  run is a (CL) vine chain (T1379).
- For unit `j`:
  - `a_j = u₁^j` is its top, a hinge of `G_sb`;
  - `b_j = u₂^j` is the lower joint of its bottom vine (T1769: `(u₂,u₂₁,u₂₂) = (u₂¹,u₂₁¹,u₂₂¹)`);
  - `u₁₁^j` is the external child of `a_j`;
  - `u₂₁^j, u₂₂^j` are the external ("lower") children of `b_j`.
- `G_sb` is the result of splicing all runs. `𝒞` is a congruence′ class: LF twists at the unmarked core vines of the
  runs, with a fixed SG/LG/ZG specification.

**The exact Stage-1 integrand.** For `𝒢' ∈ 𝒞`, T (redkg) (T1725–1726), applied to the capped and pinned integrand of
S Lemma 2.2, reads

```
(U.0)  K_{𝒢'} = c^{n_sk} ζ(𝒢'_sk) Σ_{κ ∈ Dec(𝒢'_sk)} ε(κ) 𝒵(κ) W_sk(κ)
         ∫_{ℐ'_sk} Π_{𝔫 ∈ 𝒩_sk} e^{πiζ_𝔫 δL^{2γ} Ω_𝔫 t_𝔫}
             Π^{(+)}_{(𝔩,𝔩')} 𝒦*_{𝒬(𝔩,𝔩')}(t_{𝔩^pr}, t_{𝔩'^pr}, k_𝔩)  Π_{𝔪} 𝒦*_{𝒯(𝔪)}(t_{𝔪^pr}, t_𝔪, k_𝔪) dt ,
```

and `𝒦 := Σ_{𝒢'∈𝒞} K_{𝒢'}` (T1946–1952). Here:
- every slot kernel `𝒦*` is the **weighted** kernel of its regular object (frontier factors assigned by the port
  convention of S §5, S240), including any pin, cap pairing, pattern pin or dagger indicator inside it;
- `W_sk` is the part of `W` not inside any regular object (factors at skeleton nodes and bonds);
- a root's parent clock is the root time (T1728).

These are the **native parent clocks**. Nothing has been spliced yet.

**Slots.** The *regional* slots of unit `j` are:
- the couples at leaf pairs of `𝒢_sk[U_j]`;
- the trees at the branching nodes of `𝒢_sk[U_j] \ {a_j}`.

All other slots are *exterior*. Through the slot map `ι` (main `VineB.SpliceShape.iota`), they are exactly the slots
of `G_sb`. An exterior slot is a **lower slot** if one of its two native clocks is `τ_{b_j}` for some `j`. Write
`𝒮_low` for these.

**Routing.** For each exterior slot `s` and argument `i ∈ {1,2}`, `ρ(s,i)` is either a clock of `G_sb` or a unit `j`.
The value is `j` exactly when the `i`th native clock of `s` is `τ_{b_j}`. (This is main's `route`, SlotMap.lean:182.)

**The clock arguments of a unit.** The unit kernel is a function of `(t, t', t'')`, its top clock and the two
lower-child arguments. For the lower child `c = u₂₁^j` (and likewise `u₂₂^j`), the argument `σ_c` is:
- the clock `t_c` if `c` is a branching node (a clock of `G_sb`);
- the flower time `s` if `c` is a **capped leaf**, i.e. a skeleton leaf whose regular couple is the cap couple of an
  original tree (O73 Prop. 3.1, L45);
- the floor `𝔏_c` of its layer if `c` is any other leaf (E14).

**The modulated unit kernel.** For `λ ∈ ℝ`, put

```
(U.1)  𝒦̃^{U_j}_λ(t,t',t''; e,f,g,h) := e^{−πiδL^{2γ} t Γ} Σ_{𝒢' ∈ 𝒞_j} 𝒦^{U_j}_{(𝒢'),λ}(t,t',t''; e,f,g,h) .
```

Here `𝒞_j` is the set of LF twists at the vines of `U_j`, and `𝒦^{U_j}_{(𝒢'),λ}` is T's `𝒦^𝕌_{(𝒢)}` (T1730–1740) with
three changes:
- it carries the per-unit part `W_j` of the weights (frontier factors inside `𝒢_sk[U_j]` and its regional objects; in
  the second-cutoff version, the affine top amplitude (9.2), S571–575);
- it has the extra factor `e^{πiλ t_{b_j}}` in its time integrand;
- its time domain contains `t_{b_j} > max(t', t'')`, which is condition (ii) of `sumint` (T1612).

For a non-capped leaf with floor argument the last condition is vacuous a.e.: `t_{b_j} ≥ 𝔏_{b_j} ≥ 𝔏_c`. At `λ = 0` and
`(t',t'') = (σ_{u₂₁}, σ_{u₂₂})` with no capped leaf, (U.1) is T's (vineest1) with the S Lemma 5.3 weights.

**Norms.** `X^{θ,a,b}` is S (1.2), with the supremum in `k` inside the Fourier integral, and the infimum over extensions
on a time domain. The weight is `max_i⟨ω_i⟩^θ`.

---

## 4. Statement

> **Theorem U-clock.** Let `η` be small enough that `12η⁶ ≤ η` (in addition to S §1). In the setting of §3, for every
> version, pattern vector and dagger datum, uniformly over `G ∈ 𝒫(C₁)`, the frontier scales and the stem-filter scales:
>
> **(a) Routing.** A native clock of an exterior slot is either a clock of `G_sb` or a lower-joint clock `τ_{b_j}`. No
> other interior clock of a unit is read by an exterior slot.
>
> **(b) Lower slots.** Each `s ∈ 𝒮_low` has a finite complex measure `ν_s` on `ℝ²` and amplitudes `a_{s,ω}(k)`, with
> `sup_k |∂_k^ρ a_{s,ω}| ≤ 1` for `|ρ| ≤ 30d` and, for couples, support in a unit ball. On the support of the integrand,
>
> ```
> (U.2)   𝒦*_s(τ¹,τ²,k) = 1_{τ_{b} > τ*_s} ∫ a_{s,ω}(k) e^{πi(ω¹τ¹ + ω²τ²)} dν_s(ω),
>         μ_s := ∫ max(⟨ω¹⟩,⟨ω²⟩)^{θ_s} d|ν_s|(ω) < ∞ .
> ```
>
> Here:
> - `τ*_s = t_c` for a tree slot at a branching lower child `c`, `τ*_s = s` for a capped lower leaf, and the indicator
>   is absent otherwise;
> - `θ_s = 1/4` if the non-routed clock of `s` is a selected residual vertex (second-cutoff version only), and
>   `θ_s = η` otherwise;
> - every explicit boundary phase of `s` is a function of the fixed flower time `s` and is absorbed into `ν_s`.
>
> The mass `μ_s` is bounded as follows.
> - **(L1) Lower slots without a pin or cap** (possibly containing protected, unpinned vertices). `μ_s` is at most
>   twice the ordinary weighted time-Fourier bound of the object: the `X^η` bound of S Lemma 4.1 (incoherent), or
>   S Lemma 5.1 with T1145–1174 (coherent). For `θ_s = 1/4` use O73 (17.1) (O82 Lemma 16.1), at its stated cost `L^{4d}`.
> - **(L2)–(L4) Pinned lower slots.** These are the capped couple and O104 (P6), only without the second cutoff, and
>   O104 (P8), only for nonplain patterns. The bound is
>
>   `μ_s ≤ C_χ^{h+1}(1+h)^{32d} C^{m+1}(C₁δ)^m L^{31d+6} G(O),`
>
>   with `2m` the order of the object and `G(O)` its full incoherency gain.
>
> **(c) Identity (redvine♯).** With absolute convergence,
>
> ```
> (U.3)  𝒦 = ∫ Π_{s∈𝒮_low} dν_s(ω_s) · 𝒦_sb[ω],
>
>        𝒦_sb[ω] := c^{n_sb} ζ(G_sb) Σ_{z∈Dec(G_sb)} ε̃(z) 𝒵(z) W_ext(z) Π_{s∈𝒮_low} a_{s,ω_s}(k_s)
>            ∫_{ℐ_sb} Π_{𝔫∈𝒩_sb} e^{πiζ_𝔫δL^{2γ}Ω^{sb}_𝔫 t_𝔫} · Π_{ρ(s,i)∈clocks(G_sb)} e^{πiω_s^i t_{ρ(s,i)}}
>                · Π_{s ∈ ext∖𝒮_low} 𝒦*_s(native G_sb clocks) · Π_j 𝒦̃^{U_j}_{λ_j(ω)}(t_{a_j}, σ_{u₂₁^j}, σ_{u₂₂^j}; bdry_j(z)) dt ,
>
>        λ_j(ω) := Σ_{(s,i): ρ(s,i) = j} ω_s^i .
> ```
>
> Here:
> - `ε̃` omits exactly the hinges (T1957(i));
> - `𝒵` and the gap data depend only on `z` (T1950);
> - `W_ext` is `W_sk` minus the per-unit parts;
> - `ℐ_sb` is the spliced time domain with the pins.
>
> **(d) Modulated local weighted vineest (Lemma U.3 = S Lemma 5.3(λ)).** Let `M_j` be the right side of S (5.7) for
> `U_j`:
>
> `M_j = C_χ^{n_(2)+h+1}(1+n_(2)+h)^{C_d}(C₁√δ)^{n_(2)} L^{−η⁸n_(3)−η²b_j/2+η⁷}.`
>
> Then
>
> `‖1_{ℋ}𝒦̃^{U_j}_λ‖_{X^{2η⁸,0,0}(𝔅)} ≲_1 (1+|λ|)^{6η⁶} M_j,`
>
> uniformly in `λ ∈ ℝ`, in the unit balls `ℋ`, and in the box `𝔅` (any unit intervals for `(t,t',t'')`, intersected
> with `t > max(t',t'')`).
>
> **(e) Consumption and (redvine2′).**
>
> ```
> (U.4)   ∫ Π_s d|ν_s|(ω_s) Π_j (1 + |λ_j(ω)|)^{6η⁶} Π_{s ∈ 𝒮_sel} ⟨ω_s^{nr}⟩^{1/18} ≤ Π_{s∈𝒮_low} 2μ_s .
> ```
>
> Here `𝒮_sel ⊂ 𝒮_low` is the set of lower slots whose non-routed clock is a selected residual vertex, and `ω_s^{nr}`
> is the frequency at that clock. The factor `⟨ω_s^{nr}⟩^{1/18}` is the share of `s` in O73 (20.2). Thus the
> modulations are paid together with every downstream moment requirement.
>
> Consequently `𝒦 = ∫_Ξ w(ξ) 𝒦^♯_sb[ξ] dμ(ξ)`, where `𝒦^♯_sb[ξ]` is the expression `𝒦_sb[ω]` with the following
> changes:
> - each unit kernel is replaced by a hinge amplitude `𝒦†_j`, bounded by 1 and supported in the boundary unit balls,
>   together with frequencies at `(t_{a_j}, t_{u₂₁^j}, t_{u₂₂^j})` (none at a leaf argument);
> - the time domain is `ℐ^♯_sb = ℐ_sb ∩ ⋂_{j: capped} {t_{a_j} > s}`.
>
> The weight satisfies `∫|w| dμ ≤ C_h^{q} Π_j M_j · Π_{s∈𝒮_low} 2μ_s`, where `C_h` depends only on `d, η`. The other
> exterior slots are treated exactly as in O75 §4.3. The resulting (redvine2) prefactor is
>
> `(C₁√δ)^{n−n_sb} C^{n_sb+2R} L^{−η⁸ g_sk − (η²/2) b_sk + η⁷ q_sk}`,
>
> with every base independent of `δ`, every original gain retained, and no new power of `L`. Section 10's `B` is
> unchanged.

Parts (a), (c), (e) are the "resulting identity" and the "consumption" of S §12.3. Part (d) is the "modulated version of
Lemma 5.3". Part (b) is the list of "available norms", including the protected exterior slots required for patterns and
dagger. §10 explains why (redvine2′) is what Proposition 10.3′ (through O75 §4.3) consumes.

---
## 5. Lemma U.1 (routing): proof of (a)

Let `s` be an exterior slot and `i ∈ {1,2}`.

- **Port clock.** If the clock is the port clock `t_𝔪` of a tree slot `𝒯_{(𝔪)}`, then `𝔪 ∉ 𝒢_sk[U_j]∖{a_j}` for every
  `j`, since otherwise the slot would be regional. Hence `𝔪` is a node of `G_sb`, possibly a hinge.
- **Root clock.** If the clock is a root time, it is a clock of `G_sb`.
- **Parent clock.** Otherwise the clock is `t_v` with `v = 𝔵^pr`, where `𝔵` is the attachment node: `𝔪` for a tree
  slot, `𝔩` or `𝔩'` for a couple slot. Suppose `v ∈ 𝒢_sk[U_j]∖{a_j}`. Then `𝔵` is not a leaf of the realization: all
  leaf pairs at atoms of a (CL) block other than its joints are internal, so their couples are regional. Also `𝔵` is
  not a branching node of the realization, else `s` would be regional. So `𝔵` is an external child of an interior node
  of the run. A run is a (CL) block (T1379), and block_clcn (T1345–1353) gives:
  - every atom other than the two joints `a_j, b_j` has all four bonds inside the block;
  - `a_j` is not interior;
  - the bonds of `b_j` that leave the block go exactly to `u₂₁^j, u₂₂^j`.

  Hence `v = b_j`. ∎

Main proves this in Lean as `VineB.argSrc_outer` (Slots.lean:144, through `ext_child_lower`) and `VineB.freqAt_inter`
(Slots.lean:222): no interior clock other than `u₂^j` carries an outer frequency. Pins, caps and weights play no role.

Every lower slot is therefore one of the following:
- the tree slot `𝒯_{(c)}`, at a branching lower child `c`, with clocks `(τ_b, t_c)`;
- a couple slot `𝒬_{(c,c')}`, at a lower leaf `c`, with clocks `(τ_b, t_{c'^pr})`.

In the couple case, `c'^pr` may be:
- a node of `G_sb`;
- another unit's lower joint `b_k`, which gives two units' interiors, as in E26;
- the same `b_j`, which gives frequency `ω¹+ω²` routed to `j`;
- absent, when `c'` is itself a root (a cap), whose clock is a root time.

---

## 6. Lemma U.2 (lower slots): proof of (b)

### 6.1 From a weighted time-Fourier bound to (U.2)

Let `F(τ,k)` be given on a time domain `D` (a product of unit intervals, possibly intersected with `τ¹ > τ²`), with
`‖F‖_{X^{θ,30d,β}(D)} ≤ X`. By definition (S (1.2): infimum over extensions, `sup_k` inside the integral), there is an
extension `F^e` with

`∫ max_i⟨ω_i⟩^θ m(ω) dω ≤ 2X`,  where `m(ω) := max_{|ρ|≤30d} sup_k |⟨k⟩^β ∂_k^ρ F̂^e(ω,k)|`.

Put `a_ω := F̂^e(ω,·)/m(ω)` (zero where `m = 0`) and `dν := m dω`. Then:
- `F = ∫ a_ω e^{πiω·τ} dν` on `D`;
- `|∂^ρ a_ω| ≤ ⟨k⟩^{−β} ≤ 1`;
- `∫ max⟨ω⟩^θ d|ν| ≤ 2X`.

For couples (`β = 30d`), the output is localized to unit balls by the `⟨k⟩^{−30d}` decay. This is the standard
couple-centre sum (T1958–1959), whose summability uses that decay. For trees there is no output decay (T1060). The
output is localized instead by the node-centre decomposition (T1959, `treelemma`, a fixed `C₀^n`, carried as
`C₁^{n_sb}` per E15). This is unchanged from the unweighted case.

Main's discrete version is `Represents.exists_supM` / `exists_cenSupM` (RepSupM.lean:81,101). These produce `SupM θ` /
`CenSupM θ` (Fourier series `e^{πim·t}`, `m ∈ ℤ²`, weight `maxBracketPow θ (m/2)`) from `XNormRestr θ`. Main uses it
with `θ = η` for every outer slot in `slots_existM` (RepSlots2M.lean:52).

The indicator in (U.2) records the defining triangle. A tree kernel `𝒦*_𝒯(t,t_c,k)` is defined on `t > t_c`, and its
`X` norm is over that triangle (T588–591: infimum over extensions). At a branching lower child `c`, the constraint
`τ_b > t_c` is a constraint of the unit's own local domain (main `VineB.dom_iff`, TimeDomain.lean:101: "the constraint
`t_{u21} < t_{u2}` of a lower boundary child is a constraint of the local domain"). The capped case is §6.3.

### 6.2 (L1): lower slots without a pin or cap

The object `O` is an ordinary embedded regular object, with:
- its assigned frontier factors (port convention, S §5);
- no pin, no cap pairing, no face.

It may contain protected but unpinned vertices: root children, flower siblings in the plain pattern, children of a
selected vertex. Protection changes only marking and twisting (O75 §2.2–2.4), not the kernel.

There are **no upper filters** in `O`:
- without the second cutoff there are none at all;
- with it, upper filters sit only on stem vertices (S (8.5)). By O75 Lemma 2(d) (O75 L119, L288) the stem avoids
  `𝐀(𝕍)` for every vine of the run and exits a top `a_j` through `u₁₁^j`. Every lower slot hangs below `b_j`, or is a
  couple whose far tree is not on the stem (§6.3, Claim B). Hence it contains no stem vertex.

The time-Fourier bounds are therefore:
- **Incoherent `O`:** S Lemma 4.1 (S185–203): `X^{η,30d,30d}` for couples and `X^{η,30d,0}` for trees, at most
  `C_χ^{h+1}(1+h)^{32d}(C₁δ)^{m}L^{−(γ₁−√η)g}` (the `⟨λ⟩^η` weight is T's, T953–955).
- **Coherent `O`:** S Lemma 5.1 (S242–276) gives `K_{O,R} = χ(k/R)^{c(q,q')}K_O[F^{[R]}]`, with real `F^{[R]}` in
  `𝒫(C_{d,χ}C₁)` by S (5.3). `K_O[F^{[R]}]` has the coherent `X^η` bounds T1097–1110 and T1145–1164. This is what main
  uses for coherent outer slots in `slots_existM` (`IsCoherentCoupleAt` / `IsCoherentTreeAt` branches). The output
  factor `χ(k/R)^c` has `C^{30d}` norm bounded uniformly for `R ≥ 1`.
- **Trivial objects:** the trivial tree (`≡1`) and the trivial couple (the profile `G_q(k)`) are clock-independent:
  `ν_s` is a point mass at `ω = 0`.

When the non-routed clock of `s` is a selected residual vertex (second-cutoff version), O73 Prop. 17.1(a) (O73 L605–612;
O82 Lemma 16.1) gives the `X^{1/4,30d,30d}` / `X^{1/4,30d,0}` bound at cost `L^{4d}`. That cost is already charged in
O73 Prop. 20.1 (`L^{7(47d+2)a}`, at most seven strong factors per selected vertex, of which `s` is one).

### 6.3 (L2)–(L4): pinned lower slots

**Claim A (protected vertex on the `b_j` side).** Let `O` be the object of a lower slot of unit `j`. Suppose a protected
vertex `x` lies in `O` and descends from `b_j`. This covers every `x ∈ O` for a tree slot, and the near tree for a couple.
Then:
1. `b_j` is a proper ancestor of the flower parent `φ` of its tree;
2. the second cutoff is absent;
3. `O` is either the cap couple at a lower leaf (L2), or O104 (P6) at the branching lower child `c = φ` (L3).

*Proof.* Go through the elements of `Π` (O75 §2.2, O75 L78–96; S §11.1 for the pattern additions).
- **`r`.** A root has no ancestor, so `r ∉ O`.
- **Root children.** A root child's parent `r` would be in `O ∪ {b_j}`, impossible because `b_j` has a parent.
- **`f`.** The flower is a leaf paired with its cap. A regular object's non-port leaves are paired inside it, and `f`
  is not a port, being a leaf. So `f ∈ O` forces `O` to contain the cap: `O` is a couple with the cap as one tree
  (O73 Prop. 3.1, O73 L45). Then `φ ∈ O` too, since the near tree is a subtree of the original tree containing `f`.
- **`φ`.** If `φ ∈ O` then `f ∈ O`, as `φ`'s non-port children are in `O`. We are back in the previous case.
- **Siblings of `f`** (and the `dChild` vertex `m`, which is one of them). Their parent `φ` lies in `O ∪ {b_j}`. If
  `φ = b_j`, then `b_j ∈ Π ∩ 𝐀(𝕍)` and the vine is marked, contrary to assumption. So `φ ∈ O`.
- **`π = φ^pr`** (`dParent`). If `φ ∈ O`, we are in the case above. Otherwise `φ` is the port of `O` (a stem-rooted
  paired tree; O73 Prop. 3.1, O104 Prop. 7.2 (G1)(ii)). Then `O = 𝒯_{(φ)}` at the lower child `c = φ`, which is case
  (P6).
- **`Π2` vertices** (selected stem vertex, its parent, its children). In each case `b_j` is an ancestor of a stem
  vertex in `O`, or `b_j` is that stem vertex itself (which is excluded, as above). So `b_j` lies on the stem and in
  `𝐀(𝕍)`, contradicting O75 Lemma 2(d). Hence these cases occur only without the second cutoff, and there `Π2 = ∅`.

In every surviving case, `b_j` is a proper stem ancestor of `φ`. This is impossible with the second cutoff (O75 Lemma
2(d)). If `φ ∈ O`, then by O73 Prop. 3.1 `O` is the couple `(𝒯₁, cap)`. Its near tree `𝒯₁` is stem-rooted at a child
of `b_j`, with `φ` the terminal chain vertex and `f` the lone leaf. The lower child `c` is the skeleton leaf at
`𝒯₁`'s position. This is the capped leaf (L2). ∎

**Claim B (protected vertex only on the far side).** Let `O = 𝒬_{(c,c')}` be the couple at a lower leaf `c`, and
suppose the near tree contains no protected vertex but `O` does. Write `v' = c'^pr`. Then:
- the far tree contains no stem vertex;
- `v' ∈ {r, φ, v_sel}`, and the protected vertex is the far root `ρ'` (or the leaf `c'`).

If moreover `O` carries a pin, then the pattern is `dChild` with `m = ρ'` and `v' = φ`. This is O104 (P8), case (L4).

*Proof.* If the far tree contained a stem vertex, `O` would contain the cap (O73 Prop. 3.1). The cap is a trivial tree,
so it would be one of `O`'s two trees. It is not the near tree, because `c` has the parent `b_j`. So it is the far tree,
which then has no branching vertex, a contradiction.

The protected non-stem vertices are root children, siblings of `f`, children of `v_sel`, and the `dChild` vertex. Each
has its parent on the stem. That parent is not in the far tree, so the vertex is the far root `ρ'` (or the leaf `c'`
when the far side is trivial), and its parent is `v'`.

A pin inside `O` must be at a designated vertex:
- `φ` and `π` are stem vertices, so they are not in the far tree;
- `r` is never in `O`;
- the `dChild` vertex `m` can be the far root, with `v' = φ`.

That is O104 Prop. 7.2 (G1) `dChild`(ii) and Prop. 7.3 (P8). ∎

Faces occur only at selected vertices (second cutoff) and as pattern pins. In the second-cutoff version, the faces at
a selected residual vertex `v_sel` are formed at the Fourier level of the residual integral (O73 Prop. 20.1, O73
L839–870: "Once the adjacent kernels have been Fourier expanded …"). A lower couple adjacent to `v_sel` through its far
clock is therefore an ordinary Fourier-expanded factor, i.e. (L1) with `θ_s = 1/4`. No individual face is put
inside a lower slot. Pattern faces are the pins (P1)–(P8) (O104 Lemmas 6.1–6.3, 13.3), and only (P4)–(P8) can be lower
slots, by Claims A and B.

**Bounds.** Fix the exceptional spatial tuple `E` of the pinned links, at most `e ≤ 2` links. The outputs are:

- **(L2), plain.** O73 Prop. 13.1 (O73 L372–381) gives
  `O = ∫_s^{τ_b} e^{πiA(u−s)} K_pre(τ_b,u) K_in(u,s) Q₁Q₂(u,s) du` on `τ_b > s`, a terminal operator `T_A` (O73 Lemma
  12.1, O73 L325–343). Its upper time is the parent clock of `𝒯₁`'s root, which is `τ_b`.
- **(L2), patterns.** O104 Prop. 7.3: (P4) `K_pre(τ_b,s)Q₁(s,s)Q₂(s,s)`; (P5) `T_A[K_pre(τ_b,u)Q₁Q₂(u,s)(T_BG)(u,s)](τ_b,s)`;
  (P7) `e^{πiεB(s−q)}·T_A[K_pre K_in R Q₂](τ_b,s)`. In O104's notation `τ_top = τ_b`.
- **(L3).** (P6) = O73 (13.1) verbatim, with `π` terminal pinned and port `φ` at time `s`.
- **(L4).** O104 Prop. 7.4 (revised §13.1): `O^m = e^{πiεB(s−q)}R`, with `‖R‖_{A^θ} ≤ 8C_θ Π_{i≤4}‖P_i‖_{A^θ}`
  uniformly in `B`. The near tree, with upper time `τ_b`, is part of `P_4` (O104 Prop. 7.4 (a)/(c)), so `R` depends on
  `τ_b` and the norm includes that variable (O104 13.1 "R may depend on the boundary time"; O73 (19.1)).

Every explicit phase above (`e^{πiεB(s−q)}` in (P7)/(P8); none in the others) is a function of the fixed `s`. This is
O104 Prop. 7.6 revised (§13.2, O104 L962–985: "at the fixed external times t, s it is a unimodular constant, once the
exceptional spatial tuples are fixed").

The centred remainders are built from at most five ordinary components. Their `X^η` bounds are T953–955 /
T1097–1110 / T1145–1164, with frontier factors by S Lemmas 4.1/5.1, at cost `C_χ^{h+1}(1+h)^{32d}`. They are combined
by O104 Lemma 7.1 items 1–6 (O104 L428–455). Those operations are bounded on `A^θ`, `0≤θ≤1`, **uniformly in the
consumed frequencies `A, B`**. So at fixed `E` and fixed output, the centred object has an `A^η` bound in all its
boundary times, uniformly in `E`.

Restricting to fixed `s` (O104 Lemma 7.1(3), norm `≤ 1`) gives an `A^η` bound in `τ_b`. The phase `e^{πiεB(s−q)}` is
then a constant of modulus one. Summing over the at most `(CL)^{2de}` tuples `E` and restoring the `2e` branching
normalizations costs `(δ/2L^{d−γ})^{2e}(CL)^{2de} ≤ Cδ^{2e}L^{2γe}`. Restoring at most `e` lost incoherencies costs
`L^e` (O104 Prop. 7.6 proof; O73 (19.8)). In total this is `L^{(2γ+1)e} ≤ L^6`.

The local output extension by disjoint lattice bumps (O73 (13.4)) costs `L^{31d}`. In (L2) the output is the single
cap value `k'`. Hence

`μ_s ≤ C_χ^{h+1}(1+h)^{32d} C^{m+1}(C₁δ)^m L^{31d+6} G(O),`

with the full incoherency gain `G(O) = L^{−(γ₁−√η)g(O)}`. For the plain terminal pin this is O73 (13.3), with `L^{31d+2}`.

**The triangle.** In (L2) the object is defined on `τ_b > s`, and the extension supplied by Lemma 12.1 agrees with it
only there (O73 Prop. 5.1, last sentence). So on the support of the integrand,
`𝒦*_s = 1_{τ_b > s}·O^{ext}(τ_b; s)`, which is (U.2) with `τ*_s = s`. In (L3) the triangle `τ_b > τ_φ = s` is the
unit's own lower-child constraint (branching `c = φ`). In (L4) there is none: the inequality between the two pinned
vertices `m` and `φ` is dropped, and the near tree's upper bound `τ_b` is free.

**Dagger.** In a class with prescribed flower position, omitting the phase at `φ` multiplies by a unimodular constant
(S §11.1, Lemma 3.3 of O104). Sibling indicators either restrict the exceptional tuples of (L2), which are already
summed absolutely, so the bound does not increase (O104 Prop. 8.1, O73 §21), or they are functions of a `G_sb` bond
momentum, as for a far root `ρ'`. Then they belong to `W_ext`, which U-clock does not touch.

### 6.4 Why "time weight one" does not bite

S §12.3 warns that a protected exterior slot's supplied bound "may have only time weight one … with explicit boundary
phases". The time-weight-one bounds of the integrated proof are:
- O73 (19.7), consumed in `X^{0,30d,0}`, for individual faces and the coefficient-level representation (19.3);
- the uncentred reading of pure phases, which O73 §5 shows is false.

Neither enters a lower slot:
- individual faces never lie inside a lower slot (Claims A–B and the Prop. 20.1 remark);
- every explicit phase of a lower slot is in the fixed time `s`, never in the routed clock `τ_b`;
- the centred remainder has a positive weight `θ ≤ 1` uniformly in the consumed modulation. This is exactly what O73
  Lemma 12.1 asserts: "a bound for the **consumed** modulation, without a factor `⟨A⟩^θ`".

So no ordinary positive-weight estimate has been substituted for a consumed bound. The positive weight used is the
consumed-modulation estimate itself, evaluated at a fixed `s`.

---
## 7. Lemma U.3: the modulated weighted Lemma 5.3 (proof of (d))

**Statement.** This is (d) for the kernel (U.1). The leaf arguments `(t',t'')` range over the box. The native unit
kernel is the trace at `(σ_{u₂₁}, σ_{u₂₂})`.

**Proof.** The proof follows S Lemma 5.3 (S318–340), which follows T Prop. `vineest` (T1742–1923), with one extra factor
tracked through every step.

*Step 0 (what is inserted).* In T's renaming (T1829), `t_0^i := t_{u₂^i}`, so `τ_b = t_0^1`, the lower joint of the
bottom vine. Insert in every class member's integrand the factor `e^{πiλ t_0^1}` and the domain condition
`t_0^1 > max(t',t'')`.

*Step 1 (the factor is class-common).* Consider a unit LF twist at a vine `U^i` of the run (T1466–1478).
1. The skeleton node `u₂^i` and its time variable persist, in the same unit interval. T1891: "(t_0^p, s_1^p, t_1^p) =
   (t_{u₂^p}, t_{u₃^p}, t_{u₄^p}) and the unit interval that each of them belongs to does not depend on the twisting".
   T1474: the lone leaf of `𝒯'_{(u₂)}` has layer `𝔏_{u₂}`.
2. The external children `u₂₁, u₂₂` of `u₂` and their subtrees are kept. Only their positions as children are
   exchanged, and they keep their sign-labelled identity (T1431 and its footnote).
3. Every regular object except `𝒯_{(u₂^i)}` and `𝒬_{(u₂₃^i,u₀^i)}` is the same (T1472).

So `e^{πiλ t_0^1}·1_{t_0^1>max(t',t'')}` is one and the same function on every member's time domain. This is ruling
R58's "the modulation is twist-invariant". Main's V5-CONT kernel `Cont.twistedRecenteredModC` (ModClass.lean:32)
inserts `lowModC` in each member in exactly this way.

*Step 2 (T Steps 1–2, T1755–1838).* Re-parametrizing the decorations and renaming the times are pointwise operations.
The expression (tildeK2) (T1830–1838) simply carries the factor along.

*Step 3 (T Step 3, non-core, T1841–1850).*
- The slot factors are replaced by modulated combinations: `proplayer1/2`, and S Lemma 4.1 for weighted incoherent
  objects.
- The result is a (sumintI1) expression (T1601) in which the parameter `λ_0^1` is replaced by `λ_0^1+λ`, and the
  domain `𝒟` is restricted by T1612 (ii) ("all variables are less than t, and t_0^1 > max(t′,t″)") at the outputs
  `(t,t',t'')`. Hypotheses (i), (iii) and the bad-vine alternatives (a)–(d) are untouched.
- S Lemma 4.2, (4.3), costs `max(⟨λ_0^1+λ⟩, …)^{η⁶} ≤ 2^{η⁶/2}⟨λ⟩^{η⁶}·max(⟨λ_0^1⟩, …)^{η⁶}`, by
  `⟨a+b⟩ ≤ √2⟨a⟩⟨b⟩`.
- The second factor is absorbed by the slots' `⟨·⟩^η` weights, exactly as at T1848: "each λ_j^i etc. is an algebraic
  sum of these λ and λ′".

*Step 4 (T Step 4 and the additions of S Lemma 5.3).* Induct on the core twisted vines (T1852–1923). Let `U^p` be the
highest one.
- **`p ≥ 2`.** `t_0^1` is a variable of `U^{<p}`, so the factor belongs to `𝒦̃^{U^{<p}}(t_{u₂^p},t',t'',…)`. That kernel
  is extracted as a common factor (T1877–1878). By the induction hypothesis it is a combination of (sumintI1)-form
  expressions that carry the modulation and condition (ii).
- **`p = 1`.** The factor multiplies (replaceterm1) (T1886–1890) and is common to both twisted skeletons (Step 1).
  - Case (a) (ordering indicators), case (b) (difference at equal times, factor `|r|`) and case (c) (difference in the
    first argument, `t_1^p` against `s_1^p`, time-Hölder) never touch `t_0^1`, so they are unchanged.
  - Case (d): the leading term vanishes **pointwise in all times** after summation over `ℬ` (T1907; S Lemma 5.2, in
    the common-profile form). It therefore still vanishes after multiplication by the common factor.
  - Unequal upper layers (T1909–1923, with E18): the argument replaces only `s_1^p ↦ t_1^p` inside approximants, never
    `t_0^p`, and the reduction to `ℬ''` is pointwise.

The additions in S Lemma 5.3's proof (S325–338) are all spatial, or independent of the time factor:
- frontier factors through S Lemmas 4.1, 5.1, 5.2 and 3.2 (Lemma 3.2 commutators produce the `|r|` of case (b));
- the exact trivial kernel of E18;
- E25's halving, which is a class count;
- the character mixtures of E4;
- in the second-cutoff version, the affine top amplitude (9.2), which is class-common (S571–575).

*Leaf argument.* E14 traces a leaf argument at its floor. Here `t'` (or `t''`) is free in its unit interval, and the
native kernel is its trace at `σ`. For a capped leaf `σ = s ∈ [p,p+1]`. The bound (vineest2) is uniform in `𝔅`
(T1747–1749), and `sumint` allows any unit interval per output variable (T1595: "q may be different for different
variables"). Restricting the three-variable norm to `t' = s` is a trace of norm `≤ 1` (O104 Lemma 7.1(3); main's
`XNorm00Restr_trace_step`, LeafTrace.lean:51, is the same operation at the floor).

*Step 5 (conclusion).* Every resulting expression obeys (4.3) with the extra factor `2^{η⁶/2}⟨λ⟩^{η⁶}`. The
coefficients and the counting are those of S Lemma 5.3. Hence

`‖1_ℋ 𝒦̃^U_λ‖_{X^{2η⁸,0,0}(𝔅)} ≲_1 ⟨λ⟩^{η⁶}·(5.7) ≤ (1+|λ|)^{6η⁶}·(5.7)`. ∎

The unweighted, unpinned instance is main's proved `VineEstCanonLayerHalfMK` (ModStatement.lean:154;
V5Proof.lean:28), with the same loss `(1+|λ|)^{6η⁶}`; there `λ = 0` recovers the old statement
(`vineEstCanonLayerHalfK_of_MK`, ModStatement.lean:185). The weighted Lean target with the same loss is S-V5W's
`V5FrontierClassBoundAt` on `twistedRecenteredFW … (modW lam)` (S-V5W SCOPE §2.2). The leaf-argument variant
`t' = s` is not in either (§14).

---

## 8. Theorem U.4: the identity (redvine♯), proof of (c)

Fix `𝒞` and one product term of `W`.

*Step 1 (one member: product structure).* For `𝒢' ∈ 𝒞`, use the splice shape of `𝒢'_sk` over `G_sb` (main
`VineB.SpliceShape`, Shape.lean).
1. **Branches.** `𝒩_sk = 𝒩_sb ⊔ ⨆_j (𝒢_sk[U_j]∖{a_j})`. Hence `c^{n_sk} = c^{n_sb}Π_j c^{n_(1)^j}` and
   `ζ(𝒢'_sk) = ζ(G_sb)Π_j ζ[U_j]` (T1735; main `VineB.order_split`, `VineB.zeta_split`, BranchSplit.lean:98,109).
2. **Decorations.** `Dec(𝒢'_sk) ≅ Σ_{z∈Dec(G_sb)} Π_j Dec_loc(U_j; bdry_j(z))`, with
   `bdry_j(z) = (k_{a_j},k_{u₁₁^j},k_{u₂₁^j},k_{u₂₂^j})` (T1736, Remark twistexplain (d)–(e) T1452–1453; main `VineB.decSplit`,
   DecGlue.lean:141).
3. **Times.** Up to a null set, `ℐ'_sk ≅ ℐ_sb × Π_j ℐ_loc(U_j; t_{a_j}, σ_{u₂₁^j}, σ_{u₂₂^j})`. The local domain
   contains the native constraints `t_{b_j} > t_c` for branching lower children (T1737; main `VineB.timeSplit`,
   `VineB.dom_iff`, TimeEquiv.lean:36, TimeDomain.lean:101). Pinned vertices lie in `G_sb` or inside exterior objects,
   because `Π ∩ 𝐀 = ∅` for unmarked vines (O75 Lemma 2(a),(e)). Every vertex of `𝒢_sk[U_j]∖{a_j}` is free, so the
   frozen domain rules (S §11.1) keep all of its inequalities.
4. **`ε` and phases.** `ε(𝒢'_sk) = ε̃(z)Π_j ε[U_j]` (T1957(i); main `VineB.eps_split`, EpsPhase.lean:35). The phase
   product splits as `[Π_{𝔫∈𝒩_sb} e^{…}]·Π_j[e^{−πiζ_{a_j}δL^{2γ}Ω^{sb}_{a_j}t_{a_j}} Π_{𝔫∈𝒢_sk[U_j]} e^{…}]`, and
   `ζ_{a_j}Ω^{sb}_{a_j} = Γ_j` (T1957 "exactly cancels"; main `VineB.hinge_energy`, EpsPhase.lean:52).
5. **`𝒵`.** The SG/LG/ZG indicator depends on `z` only (T1950). For Stage 1′ the indicators are chain-level (O75 L310).
6. **Weights.** After the shell expansion, every factor of `W` is a function of the momenta at one vertex or bond.
   Assign the factors as follows:
   - frontier factors at vertices of `𝒢_sk[U_j]∖{a_j}` or of its regional objects go to `W_j`;
   - the top filter at `a_j` (second cutoff) depends on the momentum of `a_j`'s child inside `U_j` (S (9.2)), so it
     goes to `W_j`;
   - factors inside exterior objects belong to their slot kernels;
   - the rest are functions of `z` (including dagger indicators on `G_sb` bonds) and go to `W_ext`.

   Thus `W_sk = W_ext(z)Π_j W_j(κ_j; bdry_j(z))` (port convention, S §5; O75 Lemma 2(f)).
7. **Slots.** The regional slots of `U_j` depend only on `(κ_j, bdry_j(z), τ_j, t_{a_j})` (T1738; main
   `VineB.prod_slots`, Slots.lean:80). Exterior slots read `G_sb` clocks and the `τ_{b_j}` only (Lemma U.1).

*Step 2 (insert the lower modes).* Replace each lower slot by (U.2). Some factors depend only on the interior time
`τ_{b_j}` and on fixed data:
- each `e^{πiω_s^iτ_{b_j}}` with `ρ(s,i) = j`;
- for a capped lower leaf, `1_{τ_{b_j}>s}`.

Move these into unit `j`'s local integrand. The routed exponentials multiply to `e^{πiλ_j(ω)τ_{b_j}}`. The indicator
turns the local domain into that of (U.1) with `t' = s`. For a branching child the indicator `τ_b > t_c` is already in
`ℐ_loc`, and for any other leaf the floor condition is vacuous. What remains depends on `z` and the `G_sb` times only:
the amplitudes `a_{s,ω_s}(k_s)` and the `G_sb`-routed exponentials.

*Step 3 (Fubini, one member).* At fixed `ω`, the member integrand is a `G_sb` factor times, for each `j`, a factor in
`(κ_j, τ_j)` that depends on `(t_{a_j}, σ_{u₂₁^j}, σ_{u₂₂^j}, bdry_j(z))`. Sum `κ_j` and integrate `τ_j` first (Step 5).
This produces `𝒦^{U_j}_{(𝒢'),λ_j(ω)}(t_{a_j}, σ_{u₂₁^j}, σ_{u₂₂^j}; bdry_j(z))` (main `VineB.integrand_glue`,
Pointwise.lean:68, the fibre sum Fiber1–Fiber6, and `VineB.SpliceShape.skelVal_modal_eq_outerValM`, Main5.lean:40).

*Step 4 (class sum).* `𝒞 = Π_j 𝒞_j`: twists at distinct runs act independently (T1948, first observation; O75
Lemma 1). A twist at a vine of `U_j`:
- changes only `𝒯_{(u₂^i)}`, `𝒬_{(u₂₃^i,u₀^i)}` and the skeleton inside `𝒢_sk[U_j]` (T1466–1478);
- keeps `G_sb` (twistexplain (c)) and its inherited decoration (twistexplain (e));
- keeps every exterior slot, in particular every lower slot with its measure `ν_s` (T1472, T1431);
- keeps pins, caps and `Π` (O75 Lemma 2(a),(e)), and keeps `W_ext` (O75 Lemma 2(d),(f)).

Hence `Σ_{𝒢'∈𝒞}(member) = (G_sb factor)·Π_j Σ_{𝒢'∈𝒞_j}(unit-`j` factor)`. With Step 1.4, the hinge phase combines with
`Σ_{𝒢'∈𝒞_j}𝒦^{U_j}_{(𝒢'),λ}` into `𝒦̃^{U_j}_λ` as defined in (U.1). Main's class-sum versions are
`VineC.sum_tauClass_vineD_api` (VCApi.lean:87), `Represents.sum_tauClass_vineD_api_dep` (RepVB12.lean:29) and
`Represents.class_sum_modes` (RepVD10.lean:32).

*Step 5 (absolute convergence).*
- `|W| ≤ 1`, since `0≤χ,ϑ≤1` and the indicators are at most 1.
- `|a_{s,ω}| ≤ 1`, with unit-ball supports, and `∫d|ν_s| ≤ μ_s < ∞`.
- The unit-interior sums and integrals are absolutely convergent with bounds independent of the exterior data. This is
  main `VineEstS5C.regionAbsM` / `memberAbs` (ModStatement.lean:223,252) for the unweighted kernel; `|W_j| ≤ 1` keeps
  the same domination, and pins only remove integrations over sets of volume at most 1.
- The `G_sb` decoration sum is dominated through the unit-ball supports and profile decay (T1958–1959; main
  `tsum_ampBound_mode_le`, RepVB1, which is uniform in the modes).

So Fubini–Tonelli applies on `(ω, z, κ, t)`, and `∫dν` exchanges with the sums and integrals (main
`hasSum_skelVal_outerValM`, RepVB8.lean:31; `hasSum_tsum_interchange`, RepVB5). This gives (U.3). ∎

---

## 9. Theorem U.5: consumption and (redvine2′), proof of (e)

*Step 1 (the inequality (U.4)).* Let `c := 6η⁶ ≤ 1`. Since `1+|x+y| ≤ (1+|x|)(1+|y|)`, we have
`(1+|λ_j|)^c ≤ Π_{(s,i)→j}(1+|ω_s^i|)^c`. Each slot argument is routed to at most one unit, so

`Π_j(1+|λ_j(ω)|)^c ≤ Π_s Π_{i: ρ(s,i)∈units}(1+|ω_s^i|)^c`.

Per slot, there are three cases:
- **Two routed clocks.** `(1+|ω¹|)^c(1+|ω²|)^c ≤ (√2 max⟨ω^i⟩)^{2c} ≤ 2max⟨ω^i⟩^{2c} ≤ 2max⟨ω^i⟩^{η}`, using
  `12η⁶ ≤ η`.
- **One routed clock, other clock not selected.** `(1+|ω¹|)^c ≤ 2max⟨ω⟩^η`.
- **One routed clock, other clock at a selected residual vertex.** `(1+|ω¹|)^c⟨ω²⟩^{1/18} ≤ 2max⟨ω⟩^{c+1/18} ≤
  2max⟨ω⟩^{1/4}`.

The unit side `b_j` is never selected: selected vertices are protected and lie outside `𝐀` (O75 Lemma 2(d); O73
L650–653). So a lower slot carries at most one selected endpoint, and O73 (20.2) charges it `1/18 ≤ 2/18`.

Integrate over `Π_s d|ν_s|`, which is a product measure. This gives (U.4). Main's version, in Fourier-series form with
constant 9 instead of 2, is `Represents.tsum_modes_moment` (RepMom2.lean:26), via `prod_modLam_le` and
`prod_one_add_abs_le_maxBracketPow` (RepMom1.lean:52,91).

*Step 2 (hinge expansion).* Fix `ω` and `λ = λ_j(ω)`. By Lemma U.3 and the construction of §6.1, applied to the
`X^{2η⁸,0,0}` norm, `1_ℋ𝒦̃^{U_j}_λ` restricted to `𝔅_j` is `∫𝒦†_{j,ξ}(e,f,g,h)e^{πiξ·(t,t',t'')}dH^λ_j(ξ)`. Here
`|𝒦†| ≤ 1`, with no derivatives (as at T1965), and `‖H^λ_j‖ ≤ C_h(1+|λ|)^{6η⁶}M_j`.

The `G_sb` clocks must lie in `𝔅_j = {t > max(t',t'')} ∩` (layer box):
- **Branching lower children.** `t_{a_j} > t_c` is a parent–child constraint of `G_sb`.
- **Capped leaves.** On the support of the original integrand, `t_{a_j} > τ_{b_j} > s`, and `𝒦̃^{U_j}_λ(t,s,·) = 0` for
  `t ≤ s` (empty local domain). So inserting `1_{t_{a_j}>s}` at the `G_sb` level is exact. This is `ℐ^♯_sb`.
- **Other leaves.** The argument is the floor value (E14), and the kernel does not depend on it. This is main's
  leaf-coordinate decoupling (`HingeFam.leafWrap`, `exists_hinge_data_units_leaf`, RepLfClk1–2).
- **Layer intervals and momenta.** The layer intervals of the hinge clocks are main's G1 (`VineB` Src5). The momenta
  lie in the `sumint` output set by the SG specification of the run (main `g2_unitsN`, `unit_hinge_data`, RepVD13).

A frequency at a fixed argument (`s` or a floor) is a unimodular constant and is absorbed. Main's version is
`Represents.exists_hinge_data_mod` (RepVN8.lean:29), with masses `C(1+|λ_j|)^c M0_j`.

*Step 3 (mass).* Put `Ξ := (Π_s ℝ²) × Π_j ℝ³`, `dμ := Π_s d|ν_s| ⊗ Π_j d|H_j^{λ_j(ω)}|`, and let `w` be the
corresponding density, of modulus one. Then

```
∫|w|dμ ≤ ∫ Π_s d|ν_s|(ω_s) Π_j C_h(1+|λ_j(ω)|)^{6η⁶} M_j ≤ C_h^{q} Π_j M_j · Π_{s∈𝒮_low} 2μ_s ,
```

by (U.4). For `s ∈ 𝒮_sel`, the factor `⟨ω_s^{nr}⟩^{1/18}` is kept in the weight for O73 Prop. 20.1 (its region
`ℋ_v`). This is the version of (U.4) with that factor included. Main's assembly is `repIntC_vine_modes`,
`representsIntA_of_vineModes` (RepVN7.lean:33; RepVN10.lean:30).

*Step 4 (exponents).* Main does this bookkeeping in `exponent_order`, `gsk_bound` and `bsk_bound` (RepVB17, RepVE3).
- `n − n_sb` is the sum of the orders of all regular objects plus the `n_(1)^j`.
- `g_sk` is the sum of all regular-object incoherencies plus all run-vine incoherencies.
- `b_sk = Σ_j b_j`.

Each lower slot contributes `μ_s ≤ 2C^{m_s+1}(C₁√δ)^{2m_s}L^{−(γ₁−√η)g_s}` times its frontier constant, which is at most
`(C₁√δ)^{2m_s}L^{−η⁸g_s}` up to bases. For a pinned lower slot add the factor `L^{31d+6}` (§11). Each unit contributes
`M_j`. The remaining exterior slots enter as in O75 §4.3. The product is the (redvine2) prefactor
`(C₁√δ)^{n−n_sb}C^{n_sb+2R}L^{−η⁸g_sk−(η²/2)b_sk+η⁷q_sk}`, times:
- `2^{|𝒮_low|}C_h^{q} ≤ (4C_h)^{q}`, since `|𝒮_low| ≤ 2q`;
- the frontier bases `C_χ^{O(n)}`.

These bases depend only on `d, η, χ`. Main absorbs them into `C₁`, which is chosen after `η` (F-CONST,
`vineCaseRepresents_of_gate`: `C₁ ≥ Cchi·ballCard·(9K)²·Ch`). In the supplement they go into `D_P^n` (S Lemma 10.1).
Neither route introduces a `δ`-dependent base or a power `L^{Cn}`. ∎

---
## 10. Sufficiency for Proposition 10.3′, Theorem 10.4 and (11.1)

The only consumer of (redvine) in the integrated proof is O75 §4.3 (O75 L305–323), which feeds Theorem 7.5′ and S
Proposition 10.3′. O75 §4.3 has two steps.
- **"(redvine) holds with `q_sk` runs".** This is false as an identity (E26). Replace it by (U.3).
- **"(redvine2) follows from"** three sources: `proplayer1/2` and S Lemma 4.1 for unprotected objects, S Lemma 5.3 for
  the runs, and Theorems 7.3′/8.2′ for protected objects.
  - For the **lower** slots and the units, replace this by (e).
  - For every **non-lower** exterior slot, keep it verbatim. Its native clocks are clocks of `G_sb` (Lemma U.1), so the
    printed factorization is exact for it, and U-clock does not touch it.

The output (redvine2′) has the form the downstream consumes:
- `G_sb` with normalized edge amplitudes (unit balls, `C^{30d} ≤ 1`, as for the `𝒦_{(𝔪)}` of T1963–1964);
- hinge amplitudes `𝒦†_j` bounded by 1, without derivatives, functions of the hinge bonds (as at T1965 and T1970);
- arbitrary real frequencies at the `G_sb` clocks (the `ξ_𝔫` of T1962–1964);
- the same `ε̃` and `𝒵`;
- the same prefactor, with E25's halving.

It differs from the printed (redvine2) in three ways, none of which affects the downstream.

**(D1) Constant boundaries `t_{a_j} > s`.** These occur at a hinge whose unit has a capped lower leaf, at most one per
original tree.
- The printed (redvine) imposes the same constraint at the same place: in `G_sb` the capped leaf is a child of `a_j`,
  and the printed slot `𝒦*_O(t_{a_j}, s, k′)` is supported on its defining triangle `t_{a_j} > s`.
- So, as a time-domain structure, (redvine2′) coincides with the printed reduction. A downstream argument that is
  correct for the printed form is correct here.
- Constant boundaries at pin times are part of the residual domain in O73 Prop. 18.1 (O73 L671–700: "A pin splits a
  tree at a fixed time and introduces constant boundaries"; the `Y` integration over "a rooted forest with constant
  lower boundaries").
- The crude ladder bound drops ordering restrictions (E5; S §8.3), and hinges are split points (S Theorem 7.5′, item 8, S394–431).

**(D2) Pinned lower slots are consumed at Stage 1.**
- Their `τ_b` dependence goes into the unit.
- What remains is an amplitude of their `G_sb` bond momentum, with only constant phases in `s`. The output is the
  single cap value `k'` in (L2), and lies in a unit ball in (L3) and (L4). Their other clock is fixed: the cap's root
  time, or `τ_φ = s`, or `t_φ = s`.
- Their full gain `G(O)` is in `μ_s`, and their incoherency enters `g_sk` as in (redvine2).
- Their cost `L^{31d+6}` is drawn from the Theorem 7.3′ allowance `L^{400d}` of their own pin incidence (§11). That
  incidence then makes no further downstream claim on the allowance.
- Theorem 7.5′'s graph data (`Π`, marking, runs, survivors, the split set `H ∪ B ∪ Π_sb`) are defined on
  `𝒢_sk`/`G_sb` before any analytic estimate, and are unchanged. The adjacent hinge is already in `H`.

**(D3) Moments.** The only downstream consumer of slot moments is O73 Prop. 20.1, through (20.2) at selected residual
vertices. (U.4) includes that factor, and unit kernels never meet a selected vertex (O73 L650–653). O73 Prop. 18.1 and
the ladder core are uniform in the frequencies.

Consequently:
- the proof of S Proposition 10.3′ (S610–661) goes through verbatim, with "Theorem 7.5′ supplies the retained-vine
  reduction" now resting on Theorem U-clock rather than on the printed (redvine);
- the same holds for S Theorem 10.4 (nonplain patterns, `b ≤ 30P`, dagger), because §6.3 covers every pinned lower
  slot in those cases;
- hence for (11.1).

The sentence of S §12.3, "Proposition 10.3′ discharges … **relative to U-clock**", loses its condition.

---

## 11. Loss accounting

| Item | New `L`-power | Other factors (base independent of `δ`) | Where |
|---|---:|---|---|
| Routing; identity (U.3) | 0 | none | §5, §8 |
| Modulation losses `(1+|λ_j|)^{6η⁶}` | 0, paid by slot moments | 2 per lower slot, `C_h(d,η)` per unit: `≤ (4C_h)^{q_sk}` | (U.4), §9 |
| Lemma 5.3(λ) | 0 beyond (5.7) | `2^{η⁶/2}` | §7 |
| Leaf argument `t' = s` (trace) | 0 | trace norm `≤ 1` | §7 |
| Constant boundary `t_{a_j} > s` | 0 | none | §9, (D1) |
| (L1) ordinary lower slots, weight `η` | 0 (the `X^η` bound is T953–955 / S Lemma 4.1 / T1145–1164) | `C_χ^{h+1}(1+h)^{32d}` | §6.2 |
| (L1) at a selected vertex, weight `1/4` | `L^{4d}`, **already charged** in O73 Prop. 20.1's `L^{7(47d+2)a}` | — | §6.2 |
| (L2)–(L4) pinned lower slots | `L^{31d+6}` each, at most one per original tree, so at most `L^{(62d+12)P}` in total. Each is **drawn from** the Theorem 7.3′ allowance `L^{400d}` of its own pin incidence (S (8.1)): `31d+6 ≤ 400d` | `C^{m+1}C_χ^{h+1}(1+h)^{32d}` | §6.3, (D2) |
| **Net change to the Section 10 budget** | **0** | absorbed in `D_P^n` or `C₁` | |

The budget stays `B = 21006d + 546.01` (plain) and `B_pat = 24266d + 630.01` (nonplain), and the exact checks (10.4)
are unchanged:
- `21086d + 549 + 109/900 < 10⁶d³`;
- `24646d + 633 + 109/900 < 2·10⁶d³`.

**At most one pinned lower slot per tree.** Each pinned lower slot contains its tree's `φ`, its `π`, or its pinned
`m`. (L2) requires `φ` inside a couple, while (L3) and (L4) require `φ` to be a skeleton vertex. (L3) and (L4) need the
patterns `dParent` and `dChild` respectively, and a tree has only one pattern.

**Constants and order.**
- `θ ∈ {η, 1/4}` is fixed. The conditions `12η⁶ ≤ η` and `6η⁶ + 1/18 ≤ 1/4` are smallness conditions on `η`, imposed
  when `η` is chosen, before `C₁`.
- `C_h` depends only on `d, η` (main `hinge_units_const`, RepVC1); `C_χ` on `d, χ`.
- The factor `(4C_h)^{q_sk}C_χ^{O(n)}` is absorbed into `C₁` (chosen after `η`), as in main's F-CONST, or into the
  per-order base `D_P` of S Lemma 10.1.
- No `δ`-dependent exponential base and no `L^{Cn}` appear.

---

## 12. Gains retained

- **Lower slots.** Each lower slot retains its full incoherency gain `L^{−(γ₁−√η)g_s}`, for both ordinary and pinned
  objects (§6.2–6.3). These gains enter `g_sk` exactly as in (redvine2).
- **Units (unmarked runs).** `L^{−η⁸n_(3)−(η²/2)b_j}`, with every bad-vine gain at the E25 half rate, as in S Lemma 5.3.
  The modulation multiplies by `(1+|λ|)^{6η⁶}` and is paid by moments; it removes no gain (§7, Step 4: cases (a)–(d)
  and the unequal-layer argument are untouched).
- **Ladders.** These live in `𝕄_sb`, whose graph U-clock does not change.
- **Second-shell gains.** O73 Prop. 20.1's moments at selected residual vertices are kept by (U.4).
- **First-cutoff and decay gains.** O63 Theorem 6.3′ is applied afterwards to the uniform estimate, and U-clock is
  uniform over `𝒫(C₁)`.

---

## 13. Dependencies (by line)

- **T.**
  - (redkg) T1725–1726; `𝒦^𝕌` T1730–1740;
  - Prop. `vineest` T1742–1750, with proof T1755–1923 (renaming T1829; Step 3 T1841–1850 including T1848; Step 4
    T1852–1923 including T1877–1878, T1886–1891, T1907, T1909–1923);
  - `sumint` T1595–1620 (domain (ii) T1612, bound T1618);
  - block_clcn T1345–1353; twists T1431, Remark twistexplain T1447–1455; LF twists T1466–1478;
  - CL chains T1379; Stage 1 T1926–1957 (observations T1948–1950, (redvine) T1954–1957, "exactly cancels" T1957);
  - (redvine2) T1958–1965; regular-object norms T951–1092, T1097–1110, T1145–1174; norm conventions T581–591.
- **SUPPLEMENT-v2.**
  - Lemmas 2.1–2.2 (S65–100), 3.1–3.2 (S131–179), 4.1 (S185–203), 4.2 (S205–236), 5.1 (S242–276), 5.2 (S278–316),
    5.3 (S318–340);
  - §6 class `𝒫` (S342–348); Lemma 9.3 / (9.2) (S564–579); Lemma 10.1 (S587–594);
  - Proposition 10.3′ (S610–661); Theorem 10.4 (S682–705); §12.3 (S787–802).
- **O73.** Prop. 3.1 (L45); Lemma 12.1 (L325–343); Props. 13.1–13.2 (L372–431); Prop. 5.1 last sentence (L185);
  Prop. 17.1 (L605–648); boundary-incidence observation (L650–655); Prop. 18.1 (L671–705); Prop. 20.1 (L839–877).
- **O75.** Π (L78–96); Def. 2.3 (L99); Lemmas 1–2 (L109–122), including the proof of (d) (L288); Stage 1′ (L124–166);
  §4.3 (L305–323).
- **O104.** Lemma 7.1 (L428–455); Prop. 7.2 (L459–497); Prop. 7.3 (P1)–(P8) (L508–543); Prop. 7.4 and §13.1
  (L545–600, L932–960); Prop. 7.6 revised §13.2 (L962–985); Prop. 8.1 (L674).
- **Errata and rulings.** E14 (errata L1036–1047), E25, E26 (L1420–1464); ruling R58 (RULINGS L1427–1458).
- **Main (Lean, HEAD `796c0f5f`).** The declarations of §2.1 table, plus:
  - `VineB.order_split`, `zeta_split`, `decSplit`, `timeSplit`, `dom_iff`, `eps_split`, `hinge_energy`, `prod_slots`,
    `integrand_glue`, `fiber_sum` (Vine/B);
  - `Represents.hasSum_tsum_interchange` (RepVB5), `tsum_ampBound_mode_le` (RepVB1), `exponent_order` (RepVB17),
    `gsk_bound`, `bsk_bound` (RepVE3);
  - `VineEstS5C.regionAbsM`, `memberAbs` (ModStatement.lean:223,252); `XNorm00Restr_trace_step` (LeafTrace.lean:51).

---

## 14. Lean interface notes (for O3′ / MARKED-F; no build was run)

1. **Unweighted.** Done on main (§2): `Represents.class_sum_modes` is the identity, and `Represents.VineCaseRepresents`
   is the conclusion.
2. **Weighted, `Π = ∅`.**
   - S-V5W's `twistedRecenteredFW … (modW lam)` with `V5FrontierClassBoundAt` is Lemma U.3, carrying the S-V5W mass
     factor.
   - T4 `WeightedClassFactorization` is §8 Step 4.
   - O3′'s weighted member identity is §8 Steps 1–3 with `W_sk = W_ext Π_j W_j`.
   - A weighted `SlotRepM` producer is needed, from the `X^η` bounds of S Lemmas 4.1/5.1.
3. **New for Stage 1′ with pins** (not in main, S-V5W or S-STAGE1W):
   - (i) A unit kernel whose leaf lower child carries a prescribed time `σ`, adding the constraint `t_b > σ`. This is a
     variant of `clLocalTimeDomain` / `CLInternalTime`. It needs the trace step `XNorm00Restr_trace_step`
     generalized from the floor to any `σ` in the unit interval (same proof).
   - (ii) A `G_sb` domain with constant lower bounds at hinges (cf. FlowerTop/Port `SplicedKernelDataST`).
   - (iii) `SupM η` producers for pinned objects, from O73 Prop. 13.2 and O104 Props. 7.4/7.6.
   - (iv) A joint-moment version of `tsum_modes_moment` carrying the `⟨ω^{nr}⟩^{1/18}` factor for `𝒮_sel`.

---

## 15. Remaining items

**No OPEN sub-item of U-clock remains.** Two items are for the referee to confirm. Neither changes an exponent.

- **(R1)** Item (D1): the downstream (O75 count, O73 Prop. 18.1, O83 box core) must accept the constant lower boundary
  `t_{a_j} > s` at a hinge adjacent to a capped lower leaf. This is the same constraint that the printed reduction
  imposes through `𝒦*_O(t_{a_j}, s, k′)`. U-clock introduces nothing new here, but the supplement never states the
  point explicitly for hinges.
- **(R2)** §6.3 uses O104 Prop. 7.6 (revised) and O73 Prop. 13.2 at fixed `s`, after the restriction of O104 Lemma
  7.1(3). For (L2) the output is fixed at the cap momentum `k'`, so the local output extension (O73 (13.4)) is applied
  to a single lattice value.

**Alternative route (not used, not proved here).** One could remove (L2)–(L4) altogether by enlarging the marking: also
mark a vine whose lower-child slot carries a pin. This needs
- re-checking O75 Lemmas 1–2 for the enlarged twist-active sets (at most `3b` marked vines);
- an extra crude-split cost of about `L^{(480d+24)b}`, which still fits (10.4).

Because the analytic route above closes the configuration, this alternative is recorded only as a fallback.

STATUS: CLOSED WITH VARIANT (see §4, §10). The variant: the false identity (redvine) T1954–1957 is replaced by the exact identity (redvine♯) (U.3). In it, the lower slots are expanded in their native clock `τ_b`, the `τ_b` frequencies go into the units as `e^{πiλτ_b}`, and S Lemma 5.3 holds with the factor `(1+|λ|)^{6η⁶}`, which slot moments pay through (U.4). The resulting (redvine2′) adds the hinge constraints `t_{a_j}>s` that the printed form already imposes, and consumes the pinned lower slots (cap couple, O104 (P6)/(P8)) at Stage 1 through their centred `X^η` bounds, whose explicit phases are only in `s`. The `L`-cost is zero and `B` is unchanged.
