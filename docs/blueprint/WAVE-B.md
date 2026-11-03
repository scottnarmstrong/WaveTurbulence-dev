# Wave B: proposed second wave of frozen statements (the "constitutional surface")

Target: Deng–Hani arXiv:2311.10082v2 (TARGET), Theorem 1.1 for 0<γ<1, square torus, d≥3 (D1, D2). Companion of
`GRAPH.md` (node IDs `T.*`, `DH23.*`, … refer to its §A). Written 2026-11-03. Sources are cited as `T Lxxx` (TARGET
TeX), `DH23 L…`, `DH21 L…`, `DH212 L…`; figures are the PNG files in `~/wave-turbulence/references/src-*/`.

Contents
- §0 Summary, counting policy, tiers.
- §1 Shared conventions: lattice, signs, the parameter prefix (Π) encoding the constant hierarchy (F5).
- §2 Definitions needed by the Wave B statements (precise textual definitions and Lean shapes).
- §3 Definitions given only by figure or incompletely (F12, F19, F20, F26): proposed textual definitions, the
  figure each is derived from, and what must be checked.
- §4 The Wave B statements (exact mathematical form, quantifiers, constant dependence, source lines, needed
  definitions, deviations).
- §5 Junk-value hazards and audit checklist.
- §6 Open items for the author / orchestrator.

---------------------------------------------------------------------------------------------------------------

## 0. Summary

### 0.1 Counting policy

Wave A (draft `~/WaveTurbulence-dev/scratch/Draft.lean`) already has 2 theorem anchors (`main`, `wkelwp`) and 13
supporting definitions (`Mom`, `latticePoint`, `collisionOp`, `IsWKESolution`, `partialDeriv`, `normLaplacian`,
`torusFourierCoeff`, `IsSmoothNLSSolution`, `stdComplexGaussian`, `initialCoeff`, `solvableEvent`, `kineticTime`,
`weightedL2Norm`). A surface of "at most ~20 declarations including definitions" therefore cannot contain any of
the induction gates: stating `propansatz` faithfully needs trees, gardens, decorations, layerings, canonical layered
gardens, `K_G`, the `a`-system, cumulants, norms and the parameter hierarchy (≈15 further definitions).

Proposal: **count theorem anchors** against the ~20 budget (as in the memory note "freeze ~20 statements (roots +
major interfaces)"), and freeze every definition that a frozen statement mentions, each with a characterization
lemma that the statement audit checks (lean-statement-audit "characterization" items). Under this policy:

| tier | theorem anchors | count | cumulative (with Wave A) |
|---|---|---|---|
| Wave A | `main`, `wkelwp` | 2 | 2 |
| **B1 (freeze now)** | `propansatz`, `layergarden`, `fixedpoint`, `nlsAkBridge`, `wkeTaylor`, `sumint`, `countLemma`, `atomCountLemma`, `quadExpSum2` (lemlayer2), `quadExpSum3` (lemcubic) | 10 | 12 |
| **B2 (freeze once its definitions are validated by packets C1, C5, M1, M4)** | `regularAsymptotics` (regref1), `incoherentDecay` (proplayer1), `rigidity` (lgmolect), `canonicalCharacterization` (canonequiv + construction) | 4 | 16 |
| optional | `trilinearZs` (GIT20), `leonovShiryaev` (propertycm) | 2 | 18 |

New definition anchors: ≈24 for tier B1 (§2.1–§2.6, bundled into structures where possible) and ≈14 more for tier
B2 (§2.7–§2.9). If the author prefers to count definitions too, the fallback is: freeze only the def-light B1
interfaces (`nlsAkBridge`, `wkeTaylor`, `sumint`, `countLemma`, `atomCountLemma`, `quadExpSum2`, `quadExpSum3`) and
keep the gates as unfrozen targets — not recommended, because the gates are where statement drift is most likely.

### 0.2 Why these statements

- The three **induction gates** are the hinges of the proof (GRAPH §D: on the critical path). `layergarden` is
  stated as a **deterministic** statement (its proof uses the induction hypothesis only through the remainders
  R_q and their bounds (ansatz2), T L949–L951), which removes the probabilistic data from it. Both `layergarden`
  and the two-point part of `propansatz` carry a **time parameter** (F7, F27).
- `nlsAkBridge` isolates the NLS/PDE content (F8) from the Fourier-side induction.
- `wkeTaylor` isolates the WKE time-analyticity (F10; running packet WKE).
- `sumint`, `countLemma`, `atomCountLemma`, `quadExpSum2`, `quadExpSum3` are the analytic/number-theoretic
  interfaces with the highest fan-out (GRAPH §A.6, §A.11) and need no combinatorial definitions: provers in the NT
  and V packets can work against them immediately.
- Tier B2: `regularAsymptotics` is the import boundary from DH21 §4–§7 / DH23 §6 (the longest chain of the
  campaign); `rigidity` is the import boundary from DH23 §9–§10 / App B; `incoherentDecay` is TARGET's main new
  estimate on regular objects; `canonicalCharacterization` certifies the frozen definition of 𝒢_p against Def 3.7.

---------------------------------------------------------------------------------------------------------------

## 1. Shared conventions

### 1.1 Carriers (as in Wave A)

- Momentum space `Mom d = EuclideanSpace ℝ (Fin d)`, ⟨k,ℓ⟩ Euclidean, ⟨k⟩ := (1+∣k∣²)^{1/2}.
- Lattice ℤ_L^d = (L^{−1}ℤ)^d: points indexed by `n : Fin d → ℤ`, `latticePoint L n = n/L` (Wave A). For couples and
  paired trees, decorations may live in the coset k + ℤ_L^d, k∈ℝ^d (T L643).
- Signs `ζ ∈ {+,−}` (Lean: `Bool` or `SignType` restricted to ±1); z^+ = z, z^− = z̄.
- e(z) := e^{2πiz}. Time Fourier transform F̂(λ) = ∫F(t)e^{−2πiλt}dt (T L579).
- χ_0: the fixed cutoff of T L617–L623 (frozen definition `chi0`, §2.6).

### 1.2 The parameter prefix (Π) (encodes F5)

TARGET fixes, in this order (T L605–L615): C_0(d,γ); η small depending on C_0; φ_in, τ*, φ and 𝔆 =
sup_{[0,τ*]}∥φ∥_{𝔖^{40d,40d}}; C_1 depending on (τ*, η, 𝔆); ν small depending on C_1; δ small depending on ν with
𝔇 = τ*/δ ∈ ℤ (and δ^ν ≪_1 1); C_2 depending on (𝔇, δ, φ_in); L large depending on C_2. "Arbitrary constants" C_j are
encoded as existentially quantified numbers placed right after the quantities they may depend on:

```
(Π)  ∀ d ≥ 3, ∀ γ ∈ (0,1), ∃ η₀ > 0, ∀ η ∈ (0, η₀],                         -- C₀ absorbed into η₀
     ∀ φin : 𝓢(Mom d, ℝ), (∀ k, 0 ≤ φin k) → ∀ τ* > 0, ∀ φ, IsWKESolution φin τ* φ →
     ∃ C₁ ≥ 1, ∃ ν₀ > 0, ∀ ν ∈ (0, ν₀],                                     -- C₁ = C₁(d,γ,η,τ*,𝔆)
     ∃ δ₀ > 0, ∀ δ ∈ (0, δ₀], ∀ 𝔇 : ℕ, 1 ≤ 𝔇 → τ* = 𝔇 · δ →               -- δ small given ν (and C₁)
     ∃ C₂ ≥ 1, ∃ L₀, ∀ L ≥ L₀,                                              -- C₂ = C₂(…,𝔇,δ,φin)
     <statement>
```

Conventions inside `<statement>`: `X ≲_1 Y` ⇝ `X ≤ C₁·Y`, `(C_1δ)^n` ⇝ `(C₁δ)^n` (one constant C₁ suffices: take
the maximum); `X ≲_2 Y` ⇝ `X ≤ C₂·Y`; `≲_0` ⇝ a constant fixed after (d,γ) (here: absorbed into C₁, which is
allowed since C₁ ≥ C₀). Statements whose conclusions have explicit constants (the gates) do not use C₁, C₂; the
existentials are then omitted. The composition of frozen statements is possible because every statement is
"eventually true" along the same ordered sequence of choices (a gate's proof takes C₁ := max of the C₁'s of the
lemmas it uses, then ν₀ := min of their ν₀'s, etc.). For Theorem 1.1, η := η₀(d,γ) and θ := η₀^{20} (T L612).

Derived parameters (frozen definitions `WTParam.*`, §2.1), all functions of (d, η, 𝔇, L) and the integer p:
θ_p := η^{20}(1+2^{−p}); Λ_p := (40d)^{𝔇−p+1}; R_𝔇 := ⌊(log L)^{40d}⌋, N_p := R_p^{40d} (0≤p≤𝔇),
R_{p−1} := N_p^{40d} (1≤p≤𝔇); γ_0 := min(γ,1−γ); γ_1 := min(2γ,1,2(d−1)(1−γ)) (T L611–L613).

---------------------------------------------------------------------------------------------------------------

## 2. Definitions needed by the Wave B statements

Each item: name (proposed Lean name), source, precise definition, Lean shape, audit/characterization lemma. "B1"
items are needed by tier B1 statements, "B2" items only by tier B2.

### 2.1 Parameters (B1)

- `WTParam.theta (η) (p : ℕ) : ℝ := η^20 * (1 + 2^(-p))` (T L611).
- `WTParam.Lambda (d 𝔇 p : ℕ) : ℕ := (40*d)^(𝔇 - p + 1)` for p ≤ 𝔇 (T L611).
- `WTParam.R (d 𝔇 : ℕ) (L : ℝ) : ℕ → ℕ` and `WTParam.N` by downward recursion from p=𝔇: R_𝔇 = ⌊(log L)^{40d}⌋,
  N_p = R_p^{40d}, R_{p−1} = N_p^{40d} (T L612). Lean: define `RN : ℕ → ℕ × ℕ` on k = 𝔇 − p by recursion on k.
- `WTParam.gamma0 γ := min γ (1-γ)`, `WTParam.gamma1 d γ := min (2γ) (min 1 (2(d-1)(1-γ)))` (T L613).
- Audit lemmas: θ_{p+1} < (4θ_{p+1}+θ_p)/5 < θ_p; Λ_p = 40d·Λ_{p+1}; R_𝔇 < N_𝔇 < R_{𝔇−1} < … ; N_0 ≤ L^{ε} for
  L ≥ L_0(𝔇, ε).

### 2.2 Trees, gardens, decorations, layerings, canonical gardens (B1)

1. **Ternary trees** (T L625–L631; DH21 Def 2.1). `inductive TTree | leaf | node (l m r : TTree)`. Nodes are
   addressed by paths `List (Fin 3)` (0=left, 1=mid, 2=right); `TTree.nodes`, `leaves`, `branching : Finset (List
   (Fin 3))`; order n(𝒯) = #branching; ∣leaves∣ = 2n+1 (lemma). Sign of the node at path π in a tree of sign ζ:
   ζ·(−1)^{#(1's in π)} (children of a node of sign ζ have signs (ζ,−ζ,ζ)). ζ(𝒯) := ∏_{𝔫 branching} (i·ζ_𝔫) ∈ ℂ.
2. **Gardens** (T L632–L638; DH212 Def 4.1). For m ≥ 1 (width 2m): `structure Garden (m : ℕ)` with `sig : Fin (2m) →
   Sign` (exactly m plus signs), `tree : Fin (2m) → TTree`, and `pair : Equiv.Perm (Leaf G)` on the leaf type
   `Leaf G := Σ j, (tree j).leaves`, an involution without fixed points such that paired leaves have opposite signs
   (the sign of a leaf is its node sign in its tree of sign `sig j`). Couple: m=1, sig=(+,−). Order n(G) = Σ n(𝒯_j).
   **Irreducible**: no A ⊂ Fin (2m), A ≠ ∅, A ≠ univ, with `pair` mapping leaves of {𝒯_j : j∈A} into themselves.
   Proper: m ≥ 2. A trivial tree's root is a leaf (it may be paired).
   **Paired tree** (B2): a tree with a fixed-point-free sign-reversing involution on all leaves but one (the lone leaf).
3. **Decorations** (T L639–L648). For a garden G and n⃗ : Fin (2m) → ℤ^d (lattice indices; vectors n/L): a
   (n⃗)-decoration is κ : Node G → ℤ^d with κ(𝔫) = κ(𝔫1) − κ(𝔫2) + κ(𝔫3) at every branching node (children
   left/mid/right), κ(ℓ) = κ(pair ℓ) for leaves, κ(root j) = n_j. For couples, decorations of root vector k ∈ ℝ^d are
   k + κ/L with κ an integer decoration of root value 0 (T L643: k_𝔫 − k ∈ ℤ_L^d). Coefficients:
   ε_{k1k2k3} := 1 if k2 ∉ {k1,k3}; −1 if k1 = k2 = k3; 0 otherwise (T L556–L561);
   Ω_𝔫 := ∣k_{𝔫1}∣² − ∣k_{𝔫2}∣² + ∣k_{𝔫3}∣² − ∣k_𝔫∣² (T L647, on vectors k = κ/L or k+κ/L); ε_ℐ := ∏_𝔫 ε_{k_{𝔫1}k_{𝔫2}k_{𝔫3}}.
   Audit lemma: a decoration is determined by its leaf values; Ω_𝔫 = 2⟨k_{𝔫1}−k_𝔫, k_𝔫−k_{𝔫3}⟩; translation invariance.
4. **Layerings** (T L649–L656). 𝔏 : Node G → ℕ with 𝔏(child) ≤ 𝔏(parent) and 𝔏(ℓ) = 𝔏(pair ℓ). `LayeredGarden m`
   := Σ G, layerings of G.
5. **Canonical layered gardens** (T L657–L668, criterion form per route R12; T L888–L897). For q ≥ 1:
   `IsCanonG q (G,𝔏)` :⇔ G irreducible and proper, all 𝔏 ≤ q−1, and for any two **incomparable** nodes 𝔫, 𝔫′
   (neither a descendant of the other) such that `pair` maps the leaves below 𝔫 or 𝔫′ onto themselves:
   max(𝔏_𝔫, 𝔏_𝔫′) ≥ min(𝔏_{𝔫^pr}, 𝔏_{𝔫′^pr}), where the parent layer of a root is read as q−1.
   `IsCanonC q (Q,𝔏)` (couples, 𝒞_q): same with m = 1 (irreducibility vacuous). 𝒢_0 = ∅ (`IsCanonG 0` false).
   Remark: "incomparable" is implicit in the source (a subtree has an odd number of leaves, so nested or equal
   nodes can never be completely paired); stating it avoids a vacuous reading.
   Characterization (tier B2 anchor `canonicalCharacterization`): equivalence with the inductive construction of
   Def 3.7 and uniqueness of the construction data.
6. **Truncation** (T L731–L732, rewritten without construction data; agrees with L1483). For (G,𝔏) with
   `IsCanonG (p+1)` (or `IsCanonC (p+1)`): let 𝒰 := {𝔫 : 𝔏_𝔫 < p and (𝔫 is a root or 𝔏_{𝔫^pr} = p)}. The **top
   tree** of 𝒯_j consists of the nodes all of whose strict ancestors have layer p; its order is
   #{branching 𝔫 ∈ 𝒯_j : 𝔏_𝔫 = p}. The **attached gardens** are the irreducible components of the garden formed by
   the subtrees rooted at 𝒰 (with the restricted pairing). `IsTrunc p (G,𝔏)` :⇔ every top tree has order ≤ N_{p+1}
   and every attached garden has order ≤ N_p. Audit lemma (in D3): these coincide with the data of Def 3.7.

### 2.3 The a-system and cumulants (B1)

1. **Nonlinearity** (T L553–L564): for f,g,h : ℤ^d → ℂ, ζ ∈ {±}, t ∈ ℝ:
   𝒞_ζ(f,g,h)_n(t) := (δ/(2L^{d−γ}))·(iζ)·Σ_{n1−n2+n3=n} ε_{k1k2k3} e^{ζπiδL^{2γ}Ω(k1,k2,k3,k)t} f_{n1}g_{n2}h_{n3},
   k_j = n_j/L (`tsum`; summability is a lemma for f,g,h in Z^{Λ}, Λ>d).
2. **Solutions** (T L545–L551; class per Q16): `IsASolution (a₀ : ℤ^d → ℂ) (T : ℝ) (a : ℝ → ℤ^d → ℂ)` :⇔
   a 0 = a₀; sup_{t∈[0,T]} sup_n ⟨n/L⟩^{d+1}∣a_n(t)∣ < ∞; and for every n, t ↦ a_n(t) has derivative
   𝒞_+(a(t), conj a(t), a(t))_n(t) within [0,T] at every t ∈ [0,T].
3. **Cumulants** (T L570–L577): CUMUL DRAFT `cumulant μ X s` (partition formula against a measure μ;
   μ = P.restrict F for "assuming F"). Characterization: inversion formula (eqncm2) (running packet CUMUL).
4. **Symmetric events** (T L567–L569): `IsSymmetricEvent g F` :⇔ ∃ A ⊆ (ℤ^d → ℂ) measurable with F = g⁻¹(A) and A
   invariant under c ↦ (e^{iθ}c_n)_n and c ↦ (e^{−2πi⟨n/L,x₀⟩}c_n)_n for all θ ∈ ℝ, x₀ ∈ ℝ^d.

### 2.4 The quantities K_G, K*_Q, K*_T and the order-n sums (B1)

1. **K_G** (T L669–L677). For a layered garden (G,𝔏) of width 2m with all 𝔏 ≤ p, inputs F : ℕ → Mom d → ℝ, lattice
   roots n⃗ with Σζ_jn_j = 0, and t ∈ ℝ:
   K_G(t, n⃗) := (δ/(2L^{d−γ}))^{n(G)} ζ(G) Σ_{κ (n⃗)-decoration} ε_κ ∫_{ℐ(t)} ∏_{𝔫∈𝒩} e^{πiζ_𝔫δL^{2γ}Ω_𝔫t_𝔫} dt_𝔫
   · ∏_{ℓ∈ℒ, ζ_ℓ=+} F_{𝔏_ℓ}(κ(ℓ)/L),
   ℐ(t) := {t[𝒩] : 𝔏_𝔫 < t_𝔫 < 𝔏_𝔫+1 for all 𝔫; t_𝔫 < t for all 𝔫; t_{𝔫′} < t_𝔫 whenever 𝔫′ is a branching child of 𝔫}
   (reading of (timegarden): the constraint t_𝔫 < t applies to every branching node). Sum = `tsum`; integral over a
   bounded polytope in ℝ^{𝒩}.
2. **K*_Q, K*_T** (T L678–L684): same expression with root vector k ∈ ℝ^d (decorations in k + ℤ_L^d) and domains
   ℐ* (t_𝔫 < t on 𝒯^+, t_𝔫 < s on 𝒯^−) resp. 𝒟* (t_𝔫 < t, child constraints, t_{(ℓ_lo)^pr} > s; product over +
   leaves other than the lone leaf). K_Q(t,k) := K*_Q(t,t,k).
3. **Order-n sums** (T L762, L703): for a balanced signature ζ⃗ of width 2m,
   𝒦^tr_{p+1,n}(t; ζ⃗, n⃗) := Σ_{(G,𝔏): IsCanonG (p+1), IsTrunc p, sig = ζ⃗, n(G) = n} K_G(t, n⃗) for m ≥ 2, and the same
   with `IsCanonC (p+1)` for m = 1 (then also for k ∈ ℝ^d via K*_Q(t,t,k)); 𝒦_{p,n}(ζ⃗, n⃗) := Σ_{IsCanonG p,
   sig = ζ⃗, n(G) = n} K_G(p, n⃗). Lean: `finsum` over `LayeredGarden m`, with a finiteness lemma (the set of layered
   gardens of given width, order and maximal layer is finite) — audit item (otherwise `finsum` is 0).

### 2.5 Duhamel objects and the remainder space (B1; for `fixedpoint`)

1. **Tree terms** (T L708–L716 with F9): for a tree 𝒯 of sign +, t > p and data a(p):
   (𝒥_𝒯)_n(t) := (δ/(2L^{d−γ}))^{n(𝒯)} ζ(𝒯) Σ_{κ n-decoration} ε_κ ∫_{p<t_{𝔫′}<t_𝔫<t} ∏ e^{πiζ_𝔫δL^{2γ}Ω_𝔫t_𝔫}dt_𝔫 ·
   ∏_{ℓ∈ℒ} a_{κ(ℓ)}(p)^{ζ_ℓ}  (conjugate on − leaves: F9);  𝒥_N := Σ_{n(𝒯)=N, sign +} 𝒥_𝒯; a^tr := Σ_{N≤N_{p+1}} 𝒥_N.
2. **ℒ_0,…,ℒ_3** (T L717–L725): (ℒ_j(b,…,b))_n(t) := Σ_{(j)} ∫_p^t 𝒞_+(u, conj v, w)_n(s) ds over (u,v,w) ∈
   {b, 𝒥_0, …, 𝒥_{N_{p+1}}}³ with exactly j entries equal to b, and for j = 0 the restriction n1+n2+n3 ≥ N_{p+1}
   (conjugate in the middle slot made explicit). ℝ-multilinear.
3. **Z space** (T L594, L787): Z := {b : [p,p+1] → ℤ^d → ℂ : every t ↦ b_n(t) continuous, ∥b∥_Z :=
   sup_{t,n}⟨n/L⟩^{(5/4)Λ_{p+1}}∣b_n(t)∣ < ∞} (Banach; continuity is our choice, Q16 — needed for the time integrals).

### 2.6 Norms, cutoff, WKE Taylor terms, ansatz predicate (B1)

1. **𝔖^{Λ1,Λ2}** (T L585): for F : Mom d → ℂ, ∥F∥_{𝔖^{Λ1,Λ2}} := max_{∣ρ∣≤Λ1} sup_k ⟨k⟩^{Λ2}∣∂^ρF(k)∣ ∈ [0,∞], ∂^ρ
   coordinate partial derivatives; := ∞ if F ∉ C^{Λ1} (ENNReal-valued; no junk zero).
2. **𝔛^{θ,Λ1,Λ2}** (T L581): for F : ℝ^r × Mom d → ℂ, ∥F∥ := max_{∣ρ∣≤Λ1} ∫_{ℝ^r} max_j⟨λ_j⟩^θ · sup_k
   ⟨k⟩^{Λ2}∣∂^ρ_kF̂(λ,k)∣ dλ (time Fourier transform in t ∈ ℝ^r); := ∞ unless t ↦ F(t,k) is integrable for every k and
   k ↦ F̂(λ,k) is C^{Λ1} for a.e. λ. Variant `𝔛^{θ,0,0}` with several vector variables (sup over all of them).
3. **Restriction norms** (T L589): ∥F∥_{𝔛^{θ,Λ1,Λ2}(ℬ)} := ⨅ {∥G∥_{𝔛^{θ,Λ1,Λ2}} : G = F on ℬ × K}, K the set of vector
   arguments where F is defined (lattice coset or ℝ^d); same for 𝔛^θ(ℬ).
4. **Z^Λ(ℬ)** (T L594): sup_{t∈ℬ} sup_n ⟨n/L⟩^Λ∣a_n(t)∣.
5. **Cutoff** `chi0` (T L617–L623): a fixed even C^∞ function ℝ → [0,1], = 1 on [−1/2,1/2], = 0 off (−1,1), with
   ∣χ_0^{(m)}∣ ≤ (2m)! (Gevrey 2); on ℝ^d the tensor product. Freeze one explicit formula (e.g. built from
   exp(−1/x)); the Gevrey bound is a lemma (packet N1). Statements B1.9–B1.10 depend on this choice only through
   these properties.
6. **WKE Taylor terms** (T L753–L755): for p ∈ ℕ and t ∈ [p,p+1]: 𝒰^{(p)}_0(t) := φ(pδ);
   𝒰^{(p)}_n(t) := δ Σ_{n1+n2+n3=n−1} ∫_p^t `collisionOp`(𝒰^{(p)}_{n1}(t′), 𝒰^{(p)}_{n2}(t′), 𝒰^{(p)}_{n3}(t′)) dt′.
7. **Ansatz predicate** `AnsatzAt p (a, F, R, E, Ẽ)`: the conjunction of statements (1), (2), (3), (4) of B1.1 at
   level p (used as the hypothesis of `fixedpoint`, with "for all q ≤ p").

### 2.7 Regular couples and their leading terms (B2; for `regularAsymptotics`, `incoherentDecay`)

1. Mini-couples, mini-trees, operations A and B, regular couples, regular trees: textual definitions in §3.1–§3.3.
2. Legal partitions, regular chains, dominant chains (T L848–L850): text is complete (non-crossing pair partitions
   of {1..2m}; chain n_1…n_{2m} with n_{j+1} a child of n_j; for {a,b} ∈ 𝒫 the four remaining children of n_a, n_b
   are paired across as in a mini-tree, §3.4).
3. Structure data (T L851–L869): type 1 data (Q_1, Q_2, Q_3) and type 2 data (𝒳^±, Q_{j,ε,ι}, Q_lp) as **functions
   of the couple** (well defined by the uniqueness theorem; in Lean: define via `Classical.choose` on the frozen
   uniqueness statement, or as inductive "regular couple codes" with a decoding map — recommendation: an inductive
   type `RegCode` of structure data and a map `RegCode → Couple`, injective, whose range is the regular couples).
4. Links and 𝒩^ch (T L874–L882), defined recursively on `RegCode`.
5. Dominant couples/trees (T L859–L860, DH21 Def 4.17): recursive on `RegCode`.
6. Special subsets Z ⊂ 𝒩^ch (T L1126–L1137; DH21 Def 4.18): Z = Z_1 ∪ Z_2 ∪ Z_3 (type 1, root ∉ Z); type 2: (unionz)
   with Z^ε ⊂ {1..m_ε} selecting the nodes n^ε_{2j−1}; recursive.
7. Time factors 𝒥ℬ*_Q(t,s), 𝒥ℬ*_T(t,s) (T L1175–L1196, route R4): 𝒥ℬ*_× := 1; type 1: 2∫_r^{min(t,s)}
   ∏_{j=1}^3 𝒥ℬ*_{Q_j}(τ,τ)dτ; type 2: (regref2-1); dominant tree: (regref2-2). Defined for dominant objects (0
   otherwise).
8. Momentum factors ℳ*_{(Q,Z)}(k)[F] (T L1197–L1232): trivial: F(k); type 1: ∫∏ℳ*_{𝒳_j}(k_j) δ(k_1−k_2+k_3−k)
   δ(Ω)dk via the resonant measure of `collisionOp` (§2.8); type 2: ℳ*_{𝒳_lp}∏𝒩*_{(j,ε)} with Factor 1 = δ(Ω)
   (𝙸 = 0) or p.v.1/Ω (𝙸 = 1) and Factor 2 selected by the code digit 𝚌 ∈ {1,2,3}; tree: ∏𝒩*_{(j,0)}.
9. Leading terms (K*_Q)_app := 2^{−2n}δ^nζ(Q)Σ_{Z special}∏_{𝔫∈Z}(ζ_𝔫πi)^{−1}𝒥ℬ*_Q(t,s)ℳ*_{(Q,Z)}(k)[F_r], and
   the tree analogue; := 0 for non-dominant objects.
10. Coherence and incoherency index (T L885–L887): g := #{links (𝔫,𝔫′) : 𝔏_𝔫 ≠ 𝔏_𝔫′}.

### 2.8 Resonant measure and principal value (B2)

`resonantIntegral (Ψ : Mom d × Mom d × Mom d → ℂ) (k) := ∫_{ℓ_1} (2∣ℓ_1∣)^{−1} ∫_{w∈ℓ_1^⊥} Ψ(k+ℓ_1, k+ℓ_1+w, k+w)`
— the integral against δ(k_1−k_2+k_3−k)δ(∣k_1∣²−∣k_2∣²+∣k_3∣²−∣k∣²), with the same parametrization as Wave A
`collisionOp` (so that `collisionOp` is a special case: audit lemma). Principal value: `pvResonant Ψ k :=
lim_{ε→0} ∫∫ Ψ(k+ℓ_1,k+ℓ_1+ℓ_3,k+ℓ_3) χ_∞(Ω/ε)/Ω dℓ_1dℓ_3` with Ω = −2⟨ℓ_1,ℓ_3⟩ (the DH21 [G]∫ Gaussian
regularization is an equivalent alternative; to be fixed by packet N5 with a characterization lemma).

### 2.9 Molecules and counting (B2; for `rigidity`)

Molecules (T L1295–L1296), molecules of gardens (L1297–L1302), (c_v)-decorations and restricted decorations
(L1308–L1325), blocks (L1328–L1331), vines and ladders (§3.6–§3.7), gaps SG/LG/ZG (L1938–L1941), cuts (§3.10),
α/β/ε atoms, maximal ladders and 𝔛_j = min((log L)², 1+δL^{2γ}P_j), ρ = q+m, 𝔈 and 𝔄 = 𝔈L^{−(d−γ)χ}(C₁^{−1}δ^{1/2})^χ
∏𝔛_j^{z_j} (T L2129–L2137). The abstract hypotheses of `rigidity` are an open design item (§4.12, §6).

---------------------------------------------------------------------------------------------------------------

## 3. Definitions given only by figure or incompletely: proposed textual definitions

Notation: in a tree of sign ζ the children of a node of sign ζ′ have signs (ζ′, −ζ′, ζ′) (left, mid, right).
"Paired" = paired as leaves. Every proposal below was derived by reading the cited PNG; each ends with **Check**
items that a second, independent reader must confirm before the definition is frozen (F12, F19, F20).

### 3.1 (1,1)-mini-couples, codes 00 and 01 (T L826; DH21 Def 4.1 L697; figure `src-2311.10082/MiniCpl.png`)

A (1,1)-mini-couple is a couple (𝒯^+, 𝒯^−) in which both trees have order 1 (a root with three leaf children).
Leaves: 𝒯^+ has (L^+, M^+, R^+) with signs (+,−,+); 𝒯^− has (L^−, M^−, R^−) with signs (−,+,−). The pairing must be
sign-reversing with no siblings paired; hence M^+ ↔ M^− always, and either
- **code 00**: L^+ ↔ L^−, R^+ ↔ R^− ("straight"), or
- **code 01**: L^+ ↔ R^−, R^+ ↔ L^− ("crossed").
**Red, green, blue pairs**: the pairs containing L^+, M^+, R^+ respectively (colours of the left tree in the figure;
DH21 Def 4.11 L798: "red, green, blue, left to right in the tree whose root has + sign").
**Check**: (i) these are the only two sign-reversing pairings without sibling pairs (6 matchings, 4 excluded);
(ii) the figure's right column (code 01) shows the − tree as (blue, green, red) = crossed. Confirmed by this reader.

### 3.2 Mini-trees, codes 10, 11, 20, 21, 30, 31 (T L827; DH21 Def 4.1; figure `MiniTree.png`)

A mini-tree is a paired tree of order 2 with no siblings paired: a root u of sign ζ with children (c_1,c_2,c_3); the
child c_c (c ∈ {1,2,3} = first code digit) is a branching node u′ with children (d_1,d_2,d_3); the other two
children of u and two of the children of u′ are paired across (root-child ↔ u′-child), the remaining child of u′ is
the lone leaf. Sign constraints force the following six cases (lone leaf always has sign ζ):

| code | u′ = | pairs (red; green) | lone leaf |
|---|---|---|---|
| 10 | c_1 (left, sign ζ) | red: c_2 ↔ d_3; green: c_3 ↔ d_2 | d_1 |
| 11 | c_1 | red: c_2 ↔ d_1; green: c_3 ↔ d_2 | d_3 |
| 20 | c_2 (mid, sign −ζ) | red: c_1 ↔ d_1; green: c_3 ↔ d_3 | d_2 |
| 21 | c_2 | red: c_1 ↔ d_3; green: c_3 ↔ d_1 | d_2 |
| 30 | c_3 (right, sign ζ) | red: c_1 ↔ d_2; green: c_2 ↔ d_1 | d_3 |
| 31 | c_3 | red: c_1 ↔ d_2; green: c_2 ↔ d_3 | d_1 |

**Red pair** = the pair containing the leftmost leaf child of u; **green pair** = the pair containing the other
leaf child of u. Second digit: for c ∈ {1,3}, 0 means the lone leaf is on the same side as u′ (outer), 1 the
opposite side; for c = 2, 0 = straight, 1 = crossed.
**Check**: (i) six = all sign-compatible no-sibling pairings (for c=1: c_3 must pair with d_2; c_2 with d_1 or
d_3); (ii) colours in MiniTree.png row by row; (iii) consistency with RegChain.png (a type 2 dominant couple whose
+ chain uses code 10: Q_{1,+,1} red = root-mid ↔ inner-right; confirmed by this reader); (iv) agreement with the
use of 𝚌 in (regref3-4) (𝚌 = which of (k_1,k_2,k_3) is *not* an argument of ℳ*_{𝒳_1}ℳ*_{𝒳_2}, i.e. the position
of u′) and DH21 Prop 7.9's codes 1–3 — to be checked in packet C5.

### 3.3 Operations A and B (T L828; DH21 Def 4.2; figure `OperAB.png`, DH21 `Reg_Cpl_Cstr_1/2.png`)

- **Operation A** at a leaf pair (ℓ, ℓ′) (ℓ of sign +, ℓ′ of sign −; any two paired leaves, same tree or not): ℓ and
  ℓ′ become branching nodes, each with three new leaf children, and the six new leaves are paired as a (1,1)-mini-
  couple of code 00 or 01 with ℓ in the role of the + root. Everything else unchanged.
- **Operation B** at a node 𝔫 (branching node or leaf, including a root or the lone leaf): the subtree rooted at 𝔫 is
  detached; 𝔫 becomes the root u of a mini-tree of some code (signs follow from 𝔫's sign); the detached subtree is
  re-attached at the lone-leaf position of the mini-tree (it keeps 𝔫's sign); the mini-tree's two leaf pairs are new
  pairs. Everything else unchanged.
- A couple is **regular** if obtained from the trivial couple (•,•) by finitely many operations A and B; a paired
  tree 𝒯 is a **regular tree** if (𝒯, •) is a regular couple (with its lone leaf paired with •).
**Check**: OperAB.png draws B with the mini-tree of code 10 and the lower part (Y) at the lone leaf; confirm that B
"at a leaf" yields a mini-tree whose lone leaf is that leaf (so the pair of the leaf is preserved). Lean shape:
operations on `TTree` at a path, and on the pairing by relabelling; regularity as an inductive predicate or via
`RegCode` (§2.7.3).

### 3.4 Regular chains: the "rearrangement into a mini-tree" (T L849, L855; DH21 Prop 4.7; figures `RegChain.png`)

For a regular chain with nodes n_1,…,n_{2m} (n_{j+1} a child of n_j, the lone leaf a child of n_{2m}) and
{a,b} ∈ 𝒫 (a<b): write ch(n_a) for the position of n_{a+1} among the children of n_a and lp(n_b) for the position of
n_{b+1} (or of the lone leaf if b = 2m) among the children of n_b. The condition is: the two children of n_a other
than n_{a+1} are paired with the two children of n_b other than n_{b+1} (lone leaf), sign-reversingly, with no siblings
paired; the **code** of the pair is the mini-tree code with u = n_a, c = ch(n_a), u′ = n_b, lone position lp(n_b)
and the same pairing; its **red/green** pairs are those of §3.2. **Check**: the code is well defined (the table in
§3.2 shows that (c, lone position, pairing) determines exactly one code, and that every sign-compatible pairing is one
of the six); this is the content of DH21 Prop 4.7 to be re-proved in packet D4.

### 3.5 Links: the (x,y) relation (T L878–L879; DH21 Prop 4.3, figures `src-2104.11204/BranPair.png`, `BranPair2.png`)

Text of Prop 4.6 is complete; the missing proof (F16) reduces, by induction on the structure theorem, to the two
basic pieces, which this reader computed from BranPair.png with (x_𝔫,y_𝔫) = (k_{𝔫1}−k_𝔫, k_𝔫−k_{𝔫3}):
- (1,1)-mini-couple (linked roots, both decorated k): code 00: (x′,y′) = (x,y); code 01: (x′,y′) = (−y,−x).
- mini-tree code 10 (root u with children decorated (a,b,c), inner node u′ = c_1 with children (k,c,b)):
  (x_{u′}, y_{u′}) = (k−a, a−b) = (−x_u, y_u) using a−b+c = k.
**Check**: the remaining codes 11, 20, 21, 30, 31 by the same computation (packet C2, GAP.linkXY); the claim is
{x′,y′} = {±x, ±y} as sets of vectors (one sign each), which is what Prop 5.1's change of variables uses.

### 3.6 Vines (I)–(VIII) (T L1384–L1394; DH23 Def 5.1, Rem 5.2; figure `src-2311.10082/Vines.png`, same as `src-2301.07063/Vines.png`)

A **vine** is a block (T L1328–L1331: interior atoms of degree 4 inside, two joints J1, J2 each with exactly one
outgoing and one incoming bond inside) whose underlying undirected multigraph is isomorphic, by a map sending
{J1,J2} to {J1,J2}, to one of the following templates **after ladder insertion** (§3.7) at its slots. Notation: `x=y`
double bond, `x−y` single bond, `x⋯y` single bond forming one half of a **slot** (a pair of parallel single bonds at
which a ladder may be inserted; slots are listed with their colour in the figure).

| type | atoms (no insertion) | bonds | slots | # atoms / bonds |
|---|---|---|---|---|
| (I) bad | J1, J2 | J1=J2 | — | 2 / 2 |
| (II) bad | J1,a,b,c,d,J2 | J1−a, J1−b, a=b, c=d, J2−c, J2−d | red {a⋯c, b⋯d} | 6 / 10 |
| (III) | J1,a,b,c,g,h,e,f,J2 | J1−a, J1−b, a=b; c−g, c−h, g=h; e=f, e−J2, f−J2 | red {a⋯c, b⋯g}, green {c⋯e, h⋯f} | 9 / 16 |
| (IV) | J1,a,b,c,m,e,f,g,J2 | J1−a, J1−b, a=b; c=m, m=e; f=g, f−J2, g−J2 | red {a⋯c, b⋯e}, green {c⋯f, e⋯g} | 9 / 16 |
| (V) | J1,J2,a,b,c,d,e,f,g | J1−J2, J1−a, J2−b, a=b; c=d, c−e, d−f, e−f, e=g, f=g | cyan {a⋯c, b⋯d} | 9 / 16 |
| (VI) | J1,a,b,c,d,e,f,g1,g2,J2,h,i,j,k,m | J1−a, J1−b, a=b; c=d, c−e, d−h; e=f, f−i; g1=g2, g1−J2, g2−J2; h=i; j−k, j=m, k=m | red {a⋯c, b⋯d}, green {e⋯g1, f⋯g2}, cyan {h⋯j, i⋯k} | 15 / 28 |
| (VII) | J1,a,b,p,q,r,c,d,e,f,J2 | J1−a, J1−b, a=b; p=q, p=r, q−r; c−d; e=f, e−J2, f−J2 | red {a⋯c, b⋯d}, cyan {q⋯c, r⋯d}, green {c⋯e, d⋯f} | 11 / 20 |
| (VIII) | J1,a,b,p,q,J2,e,f,g,h,i | J1−a, J1−e, a=b; p=q, p−J2, q−J2; b−f; e=f; g−h, g=i, h=i | red {a⋯p, b⋯q}, cyan {e⋯g, f⋯h} | 11 / 20 |

Bad vines: (I), (II); normal: (III)–(VIII). σ(𝕍) (#bonds between the joints) = 2 for (I), 1 for (V), 0 otherwise.
In every template each non-joint atom has degree 4 and each joint degree 2 (checked: 2E = 4(V−2)+4 in each row).
**Directions**: the template is undirected except that, as for every block, at each joint the two vine bonds have
opposite directions (one in, one out); every interior atom has in-degree 2 and out-degree 2 (molecule condition).
**Check** (packet M4, GAP.vineDef): (i) the reading of every row against Vines.png (this reader's transcription;
the T-part2 map's independent transcription agrees on all rows except the (VII) red slot, see (ii)); (ii) in (VII) the red slot is drawn crossed; the two
readings {a⋯c, b⋯d} and {a⋯d, b⋯c} give isomorphic templates (swap a,b), so the choice is immaterial; (iii) atom
counts match T L1513 (bad: 2m+2, normal: 2m+5, m = number of double-bond rungs outside the special triangle/3-atom
group, e.g. (VI): m = 5) and the parametrization counts n_i = 2m_i+1 (bad), 2m_i+4 (normal) of T L1753–L1825;
(iv) whether the opposite-direction condition on every slot (§3.7) is implied by the degree condition (it is for
(II): a forced computation) — if not, add it to the definition explicitly; (v) completeness of the list relative to
DH23 Lemma ylem1 (DH23 map Q8: (VIII) never appears in that enumeration) — not needed for soundness of the
definition, but needed for DH23 Prop 10.4 (packet G7).

### 3.7 Ladders and ladder insertion (T L1385–L1386; figure `Vines.png`, bottom right)

A **ladder of length m ≥ 1** is the atomic group with atoms u_0,…,u_m, v_0,…,v_m, double bonds ("rungs") u_j = v_j,
and single bonds ("rails") u_j − u_{j+1}, v_j − v_{j+1} (0 ≤ j < m), such that for each j the two rails between rung
j and rung j+1 have **opposite directions** (one from rung j to rung j+1, the other from rung j+1 to rung j).
**Insertion** of k ≥ 0 rungs at a slot {x⋯y, x′⋯y′}: replace the two bonds by x − w_1, x′ − w′_1, w_1 = w′_1,
w_i − w_{i+1}, w′_i − w′_{i+1}, w_i = w′_i (i<k), w_k − y, w′_k − y′; each pair of parallel single bonds of the
resulting chain from {x,x′} to {y,y′} has opposite directions. k = 0 leaves the slot as drawn (so the drawn
configuration is itself a vine; T-part2 Q1). Each slot receives one (possibly empty) inserted ladder.
**Check**: (i) "inserted between each same-coloured pair of dashed parallel bonds" (DH23 Rem 5.2) = one insertion
per slot (a second insertion at the same slot is the same as a longer one); (ii) the rails of an inserted ladder
connect to the slot's end atoms as above (x to the w-side, x′ to the w′-side) — both choices give isomorphic results.

### 3.8 Groups of a vine, coherence (T L1489–L1499; derived from the templates)

Groups (partition of the non-joint atoms): (I) none; (II) {a,b}, {c,d}; (III) {c,g,h} (the triangle without joint),
{a,b}, {e,f}; (IV) {c,m,e} (the 3-atom set with two double bonds), {a,b}, {f,g}; (V) {e,f,g}, {a,b}, {c,d};
(VI) {j,k,m}, {a,b}, {c,d}, {e,f}, {g1,g2}, {h,i}; (VII) {p,q,r}, {a,b}, {e,f}, {c,d}; (VIII) {g,h,i}, {a,b}, {p,q},
{e,f}; plus one group {w_i, w′_i} per inserted rung. A vine is coherent if each group lies in one layer; the
incoherency index is the number of groups meeting two layers. **Check**: T L1491–L1497 wording "the unique triangle
that contains no joint" holds in (III), (V)–(VIII) (verified on the templates); for (VII) the leftover pair {c,d}
(single bond) is one group, as stated at L1495.

### 3.9 Positions of (CL) vines in gardens: (I-a), (I-b), (II-a)–(II-e) (T L1396–L1424; DH23 Prop 5.3; figure `Block_Mole.png`)

The text of T L1398–L1422 is complete for the defining conditions; the figure adds the bond labels used later:
(I-a)/(I-b): the double bond between v_1 = 𝔫^{−1}(u_1) and v_2 consists of one PC bond (P at v_1, C at v_2) and one LP
bond (u_23 ↔ u_0); (II-a), (II-b): the double bond v_3 = v_4 consists of two LP bonds, and v_2 is joined to v_3, v_4
by one PC bond (u_2 a child of u_4, resp. u_3) and one LP bond (u_23 ↔ u_0); (II-c), (II-d): the double bond
consists of one PC bond (P at v_3, C at v_4) and one LP bond, and v_2 is again joined by one PC and one LP bond;
(II-e): v_3 = v_4 are two LP bonds and both bonds at v_2 are PC (C at v_2 towards v_3, P at v_2 towards v_4, since
u_4 = u_23). Free children
(white in the figure): u_21, u_22 (subtrees 𝒯_1, 𝒯_2) and the child of u_1 (I) or of u_4 ((II-c), (II-d)) carrying 𝒯_3.
**Check**: the label pattern for (II-e) (top right of Block_Mole.png), read by this reader as stated above.

### 3.10 Unit twist (T L1429–L1434; DH23 Def 5.5; figures `Block_Mole.png`, `twist_dec.png`) — case table (F20)

For a core (CL) vine (bad, not (II-e)) with nodes (u_1,u_11,u_2,u_21,u_22,u_23,u_0[,u_3,u_4]), the **unit twist**
𝒢 ↦ 𝒢′ is: (1) **exchange the positions of u_2 (with its whole subtree) and of the leaf u_0** — in (I) both are
children of u_1; in (II-a)/(II-b) u_2 is a child of u_4 and u_0 of u_3 (or vice versa); in (II-c)/(II-d) one of them
is a child of u_3 and the other of u_4; (2) inside the moved u_2, which now has the opposite sign, **keep the
position of u_23**, and place u_21 (the child of sign +, with 𝒯_1) and u_22 (sign −, with 𝒯_2) in the two other
positions as dictated by the sign rule; (3) everything else (all other nodes, positions, pairings, in particular
u_23 ↔ u_0) is unchanged. Resulting case table: (I-a) ↔ (I-b), (II-a) ↔ (II-b), (II-c) ↔ (II-d); the map is an
involution; decorations correspond with k_{u_2} and k_{u_23} exchanged (twistexplain (d)).
Verified by this reader on twist_dec.png ((II-c): a = u_3 with children (u_4 = b, c, y = u_0), u_2 = x the mid child
of b with children (e, f, y = u_23); (II-d): u_2 = y the right child of a with children (f, e, x = u_23), u_0 = x the
mid child of b) and on Block_Mole.png ((I-a)/(I-b), (II-a)/(II-b)).
**Check**: (i) step (2) when u_23 is not the right child (the figures always draw it on the right; positions "may
vary", DH23 L849–L857); (ii) that rule (1)–(3) coincides with DH23 Def 5.5's "exactly two ways to insert u_2" in
every case, including (I) with u_2 at the left vs right of u_1; (iii) the LF-twist version (T L1466–L1480) replaces
the attached 𝒯_(u_2), 𝒬_(u_23,u_0) as stated there — no further figure input.

### 3.11 Cutting (T L2118–L2127; DH23 Def 9.3; figure `Cut.png`)

Given an atom v and two bonds ℓ_1, ℓ_2 at v of opposite directions (one into v, one out of v): replace v by two atoms
v_1, v_2; ℓ_1 and ℓ_2 get endpoint v_1 instead of v, all other bonds at v get endpoint v_2. α-cut if the number of
connected components does not increase, β-cut otherwise; gap r := k_{ℓ_1} − k_{ℓ_2}. For deg v = 2 the cut produces
an isolated atom v_2. The figure (in-bond ℓ_1, out-bond ℓ_2 moved to v_1) agrees. No further check needed.

### 3.12 Flower trees and flower gardens (T L2259–L2265; DH21 Def 11.1; figure `Flowertree.png`) (F25, F26)

Text: a flower tree is a tree with a distinguished leaf 𝔣 (the flower); the stem is the root-to-flower path. A flower
garden of width 2P: 2P flower trees with root signs alternating (+,−,…), all non-flower leaves completely paired,
flowers unpaired. Layering: as T Def 3.6, plus all stem nodes (root, …, 𝔣^pr, 𝔣) in layer p. (k,k′)-decoration:
k_𝔯 = k and k_𝔣 = k′ in every tree. Kernels with δ(t_{𝔣^pr} − s) meaning "t_{𝔣^pr} := s, not integrated";
prefactor (δ/(2L^{d−γ}))^n (F25: TARGET L2264–L2265 print L^{d−1}). The figure only illustrates the stem; no
additional definition is figure-only. **Check**: the sign of 𝔣 (ζ) and the conjugation convention in (operatorx)
(ζ = − acts on b̄), and the canonical class ℋ_{p+1} ("canonequiv holds for ℋ_{p+1}, same proof") — packet X1.

### 3.13 Not proposed here (figure-only, outside Wave B)

- DH23 App B operation groups (3S3, 3S3New, 3D3, 3D3New, 3D4, 3S2, 3R; figures in `src-2301.07063/*.png`) and the
  (Y)/(Z) sequences (YOper.png): needed by packets G4, G7 before they start (marked "frozen def first" in GRAPH §E);
  transcription task for the G4 prover with an independent check.
- DH21 §10.1 Case 1/Case 2 module pictures (`figCase1.png`, `FigCase2AB.png`): used by DH21 Prop 10.1, which TARGET
  replaces by T.ladderl1old (route R8); not needed.

---------------------------------------------------------------------------------------------------------------

## 4. The Wave B statements

Format per statement: proposed Lean name; GRAPH node; source lines; exact statement (prefix (Π) of §1.2 written
`(Π)` and truncated where indicated); constant dependence; definitions needed (§2/§3 numbers); deviations from the
source (each to be disclosed in the anchor docstring and approved by the author); consumers.

Throughout, for a lattice index n ∈ ℤ^d write k = n/L and ⟨n⟩_L := ⟨n/L⟩; "balanced ζ⃗ of width 2m" = ζ⃗ : Fin (2m)
→ {±} with exactly m plus signs. The probability data are: a probability space (Ω,P), g : ℤ^d → Ω → ℂ measurable,
iid with law `stdComplexGaussian` (exactly the Wave A hypotheses), and a_n(0) := `initialCoeff` = √φ_in(n/L)·g_n.

### 4.1 B1.1 `propansatz` — GRAPH T.propansatz — T L689–L707 (+ time parameter, F7/F27; + L951)

(Π) truncated after `∀ L ≥ L₀` (no C₁, C₂ appear). Then: for all probability data (Ω,P,g) there exist
- a : Ω → ℝ → ℤ^d → ℂ (the solution), F : ℕ → Set Ω (events), R : ℕ → Mom d → ℝ, E : ℕ → ℤ^d → ℝ,
  Ẽ : ℕ → (m : ℕ) → (Fin (2m) → {±}) → (Fin (2m) → ℤ^d) → ℂ,

such that for every integer 0 ≤ p ≤ 𝔇:
1. (event, solution) F p is measurable and `IsSymmetricEvent g (F p)`; F (p+1) ⊆ F p if p < 𝔇;
   P(F p) ≥ 1 − e^{−N_p}; for every ω ∈ F p, `IsASolution (a_·(0)(ω)) p (a ω)` and every `IsASolution` b with the
   same initial datum on [0,p] equals a ω on [0,p]; for t ∈ [0,p] and n, ω ↦ a ω t n is a.e.-strongly measurable
   for P restricted to F p.
2. (two-point function at integer time) R p is C^∞ and real, ∥R p∥_{𝔖^{Λ_p,Λ_p}} ≤ L^{−θ_p};
   ∣E p n∣ ≤ ⟨n⟩_L^{−Λ_p}e^{−N_p}; and for all n, n′: ∫_{F p} a_n(p)·conj(a_{n′}(p)) dP = 1_{n=n′}(φ(δp, n/L) +
   R p (n/L) + E p n).
2′. (two-point function at intermediate times; F7, F27) if p ≥ 1: for all t ∈ [p−1, p] and n:
   ∣∫_{F p} ∣a_n(t)∣² dP − φ(δt, n/L)∣ ≤ 2L^{−θ_p}.
3. (higher cumulants) for 2 ≤ m ≤ R_p, balanced ζ⃗ of width 2m and n⃗ : Fin (2m) → ℤ^d:
   `cumulant (P.restrict (F p)) (j ↦ a_{n_j}(p)^{ζ_j}) univ` = Σ_{(G,𝔏) : IsCanonG p, sig = ζ⃗, n(G) ≤ N_p} K_G(p, n⃗)
   + Ẽ p m ζ⃗ n⃗, with K_G computed from the inputs F_q := φ(δq) + R q (q ≤ p−1); Ẽ p m ζ⃗ n⃗ = 0 unless
   Σ_j ζ_jn_j = 0; ∣Ẽ p m ζ⃗ n⃗∣ ≤ (∏_j⟨n_j⟩_L)^{−Λ_p}e^{−N_p}.
4. (order-n bound) for the same (m, ζ⃗, n⃗) and every N ≤ N_p:
   ∣Σ_{(G,𝔏): IsCanonG p, sig = ζ⃗, n(G) = N} K_G(p, n⃗)∣ ≤ (∏_j⟨n_j⟩_L)^{−Λ_p} L^{−(m−1)/6} δ^{νN}.

Constant dependence: none hidden (all bounds explicit); the thresholds η₀(d,γ), ν₀(d,γ,η,τ*,φ), δ₀(…,ν),
L₀(…,δ,𝔇) are existential in (Π).
Definitions: §2.1; §2.2 (1–5); §2.3 (1,2,3,4); §2.4 (1,3); §2.6 (1,7); Wave A (`stdComplexGaussian`,
`initialCoeff`, `IsWKESolution`, `latticePoint`).
Deviations: (D1) R p is required to be a smooth real function on ℝ^d with the 𝔖-norm of ℝ^d (TARGET: lattice
function with the infimum norm (locnorm), but L951 and L810 use the ℝ^d extension) — a strengthening that the proof
provides; (D2) ansatz1's cumulant 𝕂_p(a_k, ā_ℓ) is replaced by the moment (they agree since first moments vanish on
symmetric events, T L567–L576); (D3) item 2′ is new (non-integer times, F7) and the constant 2 absorbs ∥R∥_∞ +
∣E∣; (D4) uniqueness is stated in the class of §2.3.2 (Q16); (D5) the measurability conjunct is added (needed for
the integrals). Consumers: T.proofmain (main), T.fixedpoint (as hypothesis via `AnsatzAt`).

### 4.2 B1.2 `layergarden` — GRAPH T.layergarden — T L761–L779 (deterministic; time parameter, F27)

(Π) truncated after `∀ L ≥ L₀`. Then for every integer 0 ≤ p < 𝔇 and every R : ℕ → Mom d → ℝ such that for all
q ≤ p, R q is C^∞ and real with ∥R q∥_{𝔖^{Λ_q,Λ_q}} ≤ L^{−θ_q}, with inputs F_q := φ(δq) + R q:
for all t ∈ (p, p+1], 1 ≤ m ≤ 10R_{p+1} and N ≤ N_{p+1}^4:
1. if m ≥ 2: for all balanced ζ⃗ of width 2m and n⃗ : Fin (2m) → ℤ^d,
   ∣𝒦^tr_{p+1,N}(t; ζ⃗, n⃗)∣ ≤ (∏_j⟨n_j⟩_L)^{−4Λ_{p+1}} L^{−(m−1)/4} δ^{2νN};
2. if m = 1: (a) 𝒦^tr_{p+1,N}(t; (+,−), (n_1,n_2)) = 0 for n_1 ≠ n_2; (b) the function on ℝ^d
   k ↦ 𝒦^tr_{p+1,N}(t; k) − [N even]·𝒰^{(p)}_{N/2}(t, k) (couple sum with real root vector k, §2.4.3) is C^∞ and
   its 𝔖^{4Λ_{p+1},4Λ_{p+1}} norm is ≤ L^{−(4θ_{p+1}+θ_p)/5} δ^{2νN}.

Constant dependence: none hidden. Definitions: §2.1, §2.2 (1–6), §2.3.1, §2.4, §2.6 (1, 6). Deviations: (D1) the
induction hypothesis is replaced by exactly what the proof uses (smooth real remainders with (ansatz2) bounds;
T L949–L951, L2065–L2067); (D2) time t ∈ (p,p+1] instead of t = p+1 (F27; used at L821, L2309); (D3) (2)(b) merges
(estcouple) and (estcouple2) by naming R_{p+1,N} explicitly. Consumers: T.step.S5, T.step.S6, T.fp.part1.

### 4.3 B1.3 `fixedpoint` — GRAPH T.fixedpoint — T L780–L794

(Π) truncated after `∀ L ≥ L₀`. Then for all probability data (Ω,P,g), every integer 0 ≤ p < 𝔇 and all
(a, F, R, E, Ẽ) with `AnsatzAt q (a,F,R,E,Ẽ)` for every q ≤ p, letting 𝒥_N, a^tr, ℒ_0,…,ℒ_3 be built from a(p) on
F p (§2.5) and Z = Z^{(5/4)Λ_{p+1}}([p,p+1]) (§2.5.3), there is F′ ⊆ F p with F′ measurable,
`IsSymmetricEvent g F′`, P(F p ∖ F′) ≤ e^{−4N_{p+1}}, such that for every ω ∈ F′:
1. ∣a^tr_n(t)∣ ≤ ⟨n⟩_L^{−(3/2)Λ_{p+1}}e^{3N_{p+1}} for all n and t ∈ [p,p+1];
2. ∣(ℒ_0)_n(t)∣ ≤ ⟨n⟩_L^{−(3/2)Λ_{p+1}}e^{−20N_{p+1}} for all n and t ∈ [p,p+1];
3. 1 − ℒ_1 is a bijection of Z (ℝ-linear) whose inverse satisfies ∥(1−ℒ_1)^{−1}b∥_Z ≤ e^{3N_{p+1}}∥b∥_Z;
4. Φ(b) := (1−ℒ_1)^{−1}(ℒ_0 + ℒ_2(b,b) + ℒ_3(b,b,b)) maps B := {b ∈ Z : ∥b∥_Z ≤ e^{−10N_{p+1}}} into B and
   ∥Φ(b)−Φ(b′)∥_Z ≤ ½∥b−b′∥_Z on B.

Definitions: as B1.1 plus §2.5. Deviations: (D1) Lipschitz constant ½ made explicit ("contraction"); (D2) Z
requires continuity in t (§2.5.3); (D3) F9 (conjugate leaves in 𝒥_𝒯) and the explicit conjugate middle slot in ℒ_j.
Consumers: T.step.S1, T.step.S6, T.step.S7.

### 4.4 B1.4 `nlsAkBridge` — GRAPH NLS.akReduction, NLS.inverse, NLS.uniqueSmooth, NLS.measurable — T L540–L566, L817–L819 (F8)

For d ≥ 1, L > 0, γ ∈ ℝ, α = L^{−γ}, δ > 0, 𝔇 ∈ ℕ, T := 𝔇·δ·T_kin(α) (`kineticTime`), and c : ℤ^d → ℂ:
1. (forward) if `IsSmoothNLSSolution L α T c u` then, with M := L^{−d}Σ_n∣c_n∣² and
   a_n(t) := exp(−πiδL^{2γ}∣n/L∣²t)·exp(−2iαM·δT_kin t)·`torusFourierCoeff L (u (δT_kin t)) n`, we have
   `IsASolution c 𝔇 a`, a ∈ Z^Λ([0,𝔇]) for every Λ, and ∣a_n(t)∣ = ∣û(δT_kin t, n)∣.
2. (backward) if sup_n⟨n⟩^s∣c_n∣ < ∞ for every s and `IsASolution c 𝔇 a`, then there is u with
   `IsSmoothNLSSolution L α T c u` and ∣`torusFourierCoeff L (u t) n`∣ = ∣a_n(t/(δT_kin))∣ for t ∈ [0,T].
3. (uniqueness) two smooth solutions on [0,T] with the same data c coincide on [0,T].
4. (measurability) for every measurable space Ω and measurable c : Ω → (ℤ^d → ℂ), the set {ω : ∃u,
   `IsSmoothNLSSolution L α T (c ω) u`} is measurable, and for every U with U ω a solution on that set, ω ↦
   1_{set}(ω)·∣`torusFourierCoeff L (U ω t) n`∣² is measurable for each (t,n).

Definitions: Wave A (`IsSmoothNLSSolution`, `torusFourierCoeff`, `kineticTime`), §2.3.1–2. Deviations: (D1) item 4
is the precise form of F8's "measurability of F"; (D2) the data in item 2 must be rapidly decreasing (otherwise
u_in is not smooth; on the event F_𝔇 this holds almost surely: PROB.smoothData). Consumers: T.proofmain.

### 4.5 B1.5 `wkeTaylor` — GRAPH T.wketaylor, T.taylorbound — T L752–L758 (F10)

(Π) truncated after `∃ C₂ ≥ 1` (no L). Then for every integer 0 ≤ p < 𝔇:
1. for all t ∈ [p,p+1] and k ∈ ℝ^d: Σ_N ∣𝒰^{(p)}_N(t,k)∣ < ∞ and Σ_N 𝒰^{(p)}_N(t,k) = φ(δt, k);
2. for all N and t ∈ [p,p+1]: ∥𝒰^{(p)}_N(t)∥_{𝔖^{4Λ_{p+1},4Λ_{p+1}}} ≤ C₂·(C₁δ)^N.

Constant dependence: C₁ = C₁(d,γ,η,τ*,𝔆) (the base must not depend on 𝔇), C₂ may depend on 𝔇, δ, φ_in.
Definitions: §2.1, §2.6 (1, 6), Wave A (`collisionOp`, `IsWKESolution`). Deviation: item 1 for all t (time
parameter). Consumers: T.step.S5, T.fp.part1, DH21.wkeTaylorId. (Running packet WKE, goal 5.)

### 4.6 B1.6 `sumint` — GRAPH T.sumint — T L1595–L1722

(Π) with one extra parameter A ≥ 1 quantified right after η (the bound ∏Λ_j^i ≤ A^M of hypothesis (ii)); C₁ may
depend on A. Truncated after `∀ L ≥ L₀`. Then for every datum D consisting of:
- I ≥ 1, a partition {1..I} = Nor ⊔ Bad, integers m_i ≥ 0, n_i := 2m_i + 1 + 3·1_{Nor}(i), M := Σn_i;
- output time intervals [q,q+1], [q′,q′+1], [q″,q″+1] ⊆ [0,𝔇] (q,q′,q″ ∈ ℤ) and ℬ := {(t,t′,t″) in their product :
  t > max(t′,t″)}; unit balls B_e, B_f, B_g, B_h ⊂ ℝ^d; w̲ ∈ ℝ^d;
- integer matrices T_1, T_2 (entries in {0,±1}, T_1 invertible with T_1^{−1} also with entries in {0,±1}) and affine
  maps h_1, h_2 of (e,f,g,h) such that, writing 𝐱 = (x_0^i, x_j^i, y_j^i, u_1^i, u_2^i, u_3^i) ∈ (ℤ_L^d)^M,
  𝐤 = T_1𝐱 + h_1, ℓ = T_2𝐱 + h_2: (ii) for each (i,j) there is (i′,j′) <_lex (i,j) with ℓ_j^i − ℓ_{j′}^{i′} a signed
  sum of at most Λ_j^i distinct entries of (𝐤, e,f,g,h), ∏Λ_j^i ≤ A^M; (iii) every input vector is the difference of
  two entries of (𝐤, ℓ, e,f,g,h);
- weights 𝒦_j^i, ℒ_j^i : Mom d → ℂ (1 ≤ j ≤ n_i) and integers g_{ij}, g′_{ij} ≥ 0 with
  ∥𝒦_j^i∥_{𝔖^{30d,30d}} ≤ L^{−(γ_1−√η)g_{ij}}, ∥ℒ_j^i∥_{𝔖^{30d,0}} ≤ L^{−(γ_1−√η)g′_{ij}};
- coefficient choices ζ_j^i = a_j^ix_j^i + b_j^iy_j^i + c_j^ir (a,b,c ∈ {0,±1}, j ≥ 1), ζ_0^i = x_0^i,
  Λ_i ∈ {⟨u_1^i,u_3^i⟩, ⟨u_3^i, u_1^i+u_2^i−u_3^i⟩}, ξ_i = a_iu_1^i+b_iu_2^i+c_iu_3^i+d_ir (coefficients in {0,±1});
- real parameters λ_j^i, μ_j^i, σ_j^i; for every input time variable a unit interval [q_v, q_v+1] ⊆ [0,𝔇]; a finite
  set of order constraints v < w between input time variables; 𝒟(t,t′,t″) := the set of input times in their
  intervals, all < t, with t_0^1 > max(t′,t″) and the order constraints;
- for each i ∈ Bad one of: (a) the constraints contain s_1^i < t_0^i < t_1^i or t_1^i < t_0^i < s_1^i; (b) an extra
  factor ∣r∣ in the summand; (c) an extra factor ∣t_1^i − s_1^i∣^{1−3η}; (d) max_j max(g_{ij}, g′_{ij}) ≥ 1;

and for (e,f,g,h) ∈ (w̲+ℤ_L^d)^4 in the unit balls with e − f = h − g =: r ≠ 0, ∣r∣ ≤ L^{−γ+η}, the expression
ℐ_D(t,t′,t″,e,f,g,h) of (sumintI1) (T L1608–L1611), with M_0 := #{(i,j): t_j^i, s_j^i in different unit intervals}
+ #{i ∈ Nor : τ_1^i, τ_2^i, τ_3^i not in one unit interval} and M_1 := Σ(g_{ij}+g′_{ij}):

∥ℐ_D∥_{𝔛^{2η^8,0,0}(ℬ)} ≤ C₁·[max_{(i,j)}(⟨λ_j^i⟩,⟨μ_j^i⟩,⟨σ_j^i⟩)]^{η^6}·(C₁δ^{−1/2})^M·L^{M(d−γ) − η²(∣Bad∣+M_1) − η^8M_0 + η^7},

the norm taken in (t,t′,t″) with (e,f,g,h) as vector variables (sup inside), restricted to ℬ × (balls).
Definitions: §2.1, §2.6 (1–3), lattice. Deviations: (D1) weights are functions on ℝ^d with the ℝ^d 𝔖-norm (T:
lattice functions, inf norm); (D2) A explicit (T: C_0^M); (D3) unit intervals inside [0,𝔇] (implicit in T; needed by
lemlayer2's range); (D4) typo fixes (L1615 "A" = Nor; L1687 index j); (D5) F23: the proof must use the second bound
of lemlin for γ > 8/9. Open: whether the proof needs M ≤ (log L)^C (check in packet V2). Consumers: T.vineest.S3,
T.vineest.S4, T.ladderl1new (Step 2 lemmas).

### 4.7 B1.7 `countLemma` — GRAPH T.countlem — T L2459–L2466 (DH23 Lemma A.2, L2048–L2096; route F3)

∀ d ≥ 3, ∀ γ ∈ (0,1), ∀ c₀ ≥ 1, ∃ C, ∃ L₀, ∀ L ≥ L₀, ∀ δ ∈ (0,1], ∀ α, β ∈ ℝ, ∀ r, v ∈ ℤ_L^d, ∀ P ∈ [L^{−1},1] ∪ {0}
with (P = 0 → r = 0), (0 < P < 1 → c₀^{−1}P ≤ ∣r∣ ≤ c₀P), (P = 1 → ∣r∣ ≥ c₀^{−1}), ∀ centres a_x, a_y, a_z ∈ ℝ^d,
∀ ξ ∈ {x, y, x+y}, ∀ ζ ∈ {x−v, x+y−v, x+y−v−z} (as linear forms), with 𝔛 := min((log L)², 1 + δL^{2γ}P):
1. #{(x,y) ∈ (ℤ_L^d)² : ∣x−a_x∣,∣y−a_y∣ ≤ 1, ∣⟨x,y⟩−α∣ ≤ δ^{−1}L^{−2γ}, ∣⟨r,ξ⟩−β∣ ≤ δ^{−1}L^{−2γ}} ≤ C·δ^{−1}L^{2(d−γ)}𝔛^{−1};
2. #{(x,y,z) ∈ (ℤ_L^d)³ : ∣x−a_x∣,∣y−a_y∣,∣z−a_z∣ ≤ 1, ∣⟨x,y⟩−α∣ ≤ δ^{−1}L^{−2γ}, ∣⟨ζ,z⟩−β∣ ≤ δ^{−1}L^{−2γ}} ≤ C·δ^{−2}L^{3(d−γ)−γ_0}.

Constant dependence: C = C(d,γ,c₀) — stronger than T's "≲_1" (the counting involves no φ); if the 2/3-exponent
proof needs η-dependence, weaken to C(d,γ,η,c₀). Definitions: lattice only. Deviation: "∣r∣ ∼_0 P" made explicit with
c₀. Consumers: T.excessprop1 (via DH23.excessprop1 also DH23.basiccount0).

### 4.8 B1.8 `atomCountLemma` — GRAPH T.atomcountlem — T L2467–L2478 (DH23 Lemma A.3 (1),(2); Q8b)

∀ d ≥ 3, γ ∈ (0,1), η ∈ (0, min(γ,1−γ)/2], ∃ C, L₀, ∀ L ≥ L₀, δ ∈ (0,1], β ∈ ℝ, k ∈ ℤ_L^d, centres a_1, a_2, a_3:
1. for ε ∈ {(+,+), (+,−)}: #{(k_1,k_2) : ∣k_j−a_j∣ ≤ 1, ε_1k_1+ε_2k_2 = k, ∣ε_1∣k_1∣²+ε_2∣k_2∣²−β∣ ≤ δ^{−1}L^{−2γ}}
   ≤ C·δ^{−1}min(L^d, L^{d+1−2γ});
2. for ε = (+,−) and ∣k∣ ≥ L^{−γ+η} (here k = k_1 − k_2; this is the reading of "∣r∣ ≥ L^{−γ+η}", Q8b): the same count
   ≤ C·δ^{−1}L^{d−γ−η};
3. #{(k_1,k_2,k_3) : ∣k_j−a_j∣ ≤ 1, k_1−k_2+k_3 = k, ∣∣k_1∣²−∣k_2∣²+∣k_3∣²−β∣ ≤ δ^{−1}L^{−2γ}} ≤ C·δ^{−1}L^{2(d−γ)}.

Not included: the 4-vector bound (atomcountbd3, T L2474), which is not used in T L1293–L2339 (T-part2 map §0.2).
Definitions: lattice only. Deviations: Q8b reading; signs for r = 3 fixed to (+,−,+) (the only pattern arising from
decorations). Consumers: T.excessprop1.

### 4.9 B1.9 `quadExpSum2` (lemlayer2) — GRAPH T.lemlayer2 — T L970–L977 (DH23 Lemma 6.6(2))

∀ d ≥ 3, γ ∈ (0,1), η > 0, T₀ > 0, ∃ C, L₀, ∀ L ≥ L₀, ∀ a, b, ξ, ξ′ ∈ ℝ^d:
∫_{L ≤ ∣s∣ ≤ T₀L^{2γ}} ∣Σ_{x,y∈ℤ_L^d} χ_0(x−a)χ_0(y−b) e(⟨x,ξ⟩+⟨y,ξ′⟩+s⟨x,y⟩)∣ ds ≤ C·L^{2d−2(d−1)(1−γ)+η}.
Constant: C = C(d,γ,η,T₀) (T: ≲_2 with T₀ = 𝔇δ = τ*). Definitions: `chi0`. Consumers: T.pl1.S3, T.sumint.S2.

### 4.10 B1.10 `quadExpSum3` (lemcubic) — GRAPH T.lemcubic — T L1554–L1593

∀ d ≥ 3, γ ∈ (0,1), T₀ > 0, ∃ C, L₀, ∀ L ≥ L₀, ∀ Λ ∈ {(x,y,z) ↦ ⟨x,z⟩, (x,y,z) ↦ ⟨z, x+y−z⟩}, ∀ a,b,c,ξ,ξ′,ξ″ ∈ ℝ^d:
∫∫_{L ≤ max(∣t∣,∣s∣), ∣t∣,∣s∣ ≤ T₀L^{2γ}} ∣Σ_{x,y,z∈ℤ_L^d} χ_0(x−a)χ_0(y−b)χ_0(z−c) e(t⟨x,y⟩+sΛ(x,y,z)+⟨ξ,x⟩+⟨ξ′,y⟩+⟨ξ″,z⟩)∣ dt ds
≤ C·L^{3d+γ−2γ_0}·log L.
Constant C = C(d,γ,T₀). Definitions: `chi0`. Consumers: T.sumint.S2.

### 4.11 B2.1 `regularAsymptotics` (regref1) — GRAPH T.regref1 — T L1145–L1174 (+ F11 corrections)

(Π) truncated after `∀ L ≥ L₀`. Then for every integer 0 ≤ p < 𝔇, every 0 ≤ r ≤ p and every C^∞ real R_r with
∥R_r∥_{𝔖^{40d,40d}} ≤ L^{−θ_r}, inputs F_r := φ(δr) + R_r, every n ≤ N_{p+1}^4:
1. for every regular couple Q of order 2n with all nodes in layer r, with ℬ_Q := [r,r+1]²: if Q is not dominant,
   ∥K*_Q∥_{𝔛^{η,30d,30d}(ℬ_Q)} ≤ C₁(C₁δ)^nL^{−(γ_1−√η)}; if Q is dominant, ∥K*_Q − (K*_Q)_app∥_{𝔛^{η,30d,30d}(ℬ_Q)}
   ≤ C₁(C₁δ)^nL^{−(γ_1−√η)};
2. for every regular tree 𝒯 of order 2n with all nodes except the lone leaf in layer r and lone leaf in layer
   q′ ≤ r, with ℬ_𝒯 := ([r,r+1]×[q′,q′+1]) ∩ {t>s}: the same two bounds with 𝔛^{η,30d,0}(ℬ_𝒯);
3. for dominant Q (resp. 𝒯) and special Z: 𝒥ℬ*, ℳ* are real valued, ∥𝒥ℬ*_Q∥_{𝔛^{1−η}(ℬ_Q)} ≤ C₁C₁^n,
   ∥ℳ*_{(Q,Z)}[F_r]∥_{𝔖^{30d,30d}} ≤ C₁C₁^n (trees: 𝔛^{1−η}(ℬ_𝒯), 𝔖^{30d,0});
4. (corrected regref1-5, F11) if r = p and R_p := 0: for all t ∈ [p,p+1], k ∈ ℝ^d:
   Σ_{Q dominant, n(Q)=2n, all nodes in layer p} (K*_Q)_app(t,t,k) = 𝒰^{(p)}_n(t,k).

Definitions: §2.1, §2.2, §2.4.2, §2.6 (1–3, 6), §2.7 (all), §2.8, §3.1–§3.5. Deviations: (D1) (K*)_app defined by
the explicit recursions (route R4) — the source's "(regref1-3) where 𝒥ℬ* depends only on Q" is then a definition, and
its agreement with DH21's construction is DH21 Props 7.5, 7.7; (D2) ℬ for trees as stated (T leaves ℬ implicit for
the single-layer case; check, F11); (D3) item 4 corrected (app, not K*). Range n ≤ N_{p+1}^4: see GAP.largeOrder
(route R14) — **the main proof risk of this anchor**. Consumers: T.proplayer2, T.proplayer3, T.proplayer4.

### 4.12 B2.2 `incoherentDecay` (proplayer1) — GRAPH T.proplayer1 — T L953–L956

(Π) truncated after `∀ L ≥ L₀`. For every integer 0 ≤ p < 𝔇, remainders R_q (q ≤ p) as in B2.1 (40d norms), every
n ≤ N_{p+1}^4, integers 0 ≤ q′ ≤ q ≤ p (for couples any q, q′ ≤ p):
1. for every regular couple Q of order 2n with a layering (all layers ≤ p, roots in layers ≤ q resp. ≤ q′) of
   incoherency index g ≥ 1: ∥K*_Q∥_{𝔛^{η,30d,30d}([q,q+1]×[q′,q′+1])} ≤ C₁(C₁δ)^nL^{−(γ_1−√η)g};
2. for every regular tree 𝒯 of order 2n with root layer ≤ q, lone leaf layer q′ and incoherency index g ≥ 1:
   ∥K*_𝒯∥_{𝔛^{η,30d,0}(([q,q+1]×[q′,q′+1])∩{t>s})} ≤ C₁(C₁δ)^nL^{−(γ_1−√η)g}.
Definitions: as B2.1 (§2.7.1–4, 10). Deviation: stated for arbitrary layerings (TARGET's standing assumption does not
use canonicity for g ≥ 1; confirm in packet L2). Consumers: T.vineest.S3, T.redsplice, T.plg.c.

### 4.13 B2.3 `rigidity` (lgmolect) — GRAPH T.lgmolect — T L2192–L2200 (DH23 Prop 9.6, L1818–L1827)

Source statement: for each connected component 𝕄 of 𝕄_fin, with (𝔄, 𝔈) and (ρ, q, m) of (defcounta2) and α-labels
Q_v: 𝔄 ≤ ∏_{α-atoms}L^{−(γ+3η)/2+κ_vη}Q_v^{−1} · L^{(γ_0+2η²)V_β−(2γ_0+5η²)G} · L^{−η^5ρ+ηZ}
(G = 1 perfect / 0 imperfect; Z = 0 if R = 1, else #ε-atoms of degree ≠ 4).
Proposed frozen form (design item for packet G8, to be approved before freezing): an **abstract** version quantified
over (i) a connected (pseudo)molecule 𝕄 with an atom labelling α/β/ε, α-labels Q_v ∈ [L^{−1},L^{−γ+η}] (dyadic)
and κ_v ∈ {0,50}, satisfying the structural conclusions of `finalmol` (no triple bond; degree pattern; chains of
α/β-atoms between distinct ε-atoms; perfect cycles as listed); (ii) a set 𝒮 of restricted (c_v)-decorations
(∣k_ℓ−k_ℓ^0∣ ≤ 1, ∣Γ_v−β_v∣ ≤ δ^{−1}L^{−2γ}) such that every ε-atom is LG or ZG-tame, every two-bond α-atom has
∣k_{ℓ1}−k_{ℓ2}∣ ∈ [c^{−1}Q_v, cQ_v], κ_v = 50 only if the given near-coincidence condition holds, and maximal ladders
have gaps ∼ P_j; conclusion: 𝔄(𝒮) ≤ RHS with constants ≤ C₁. The inheritance requirements (a)–(f) of T L2101–L2107
must be shown to imply (ii) (packet F1/G3). Definitions: §2.9. Deviation: abstraction of "inherited decorations".

### 4.14 B2.4 `canonicalCharacterization` (optional) — GRAPH T.canonequiv, GAP.cmattrBij — T L657–L668, L888–L897

For q ≥ 0: `IsCanonG (q+1) (G,𝔏)` ⇔ (G,𝔏) is produced by the inductive construction of Def 3.7 from top trees in
layer q, a partition (B_i) of their leaves with the irreducibility condition, pairs for ∣B_i∣ = 2 and gardens of
`IsCanonG q` for ∣B_i∣ ≥ 4; and the construction data are unique (the top trees, the partition and the attached
gardens are determined by (G,𝔏) as in §2.2.6). Same for `IsCanonC (q+1)`. Purpose: certifies the frozen criterion
definition against the source definition (route R12). Consumers: T.cmattr, T.defgtr.

---------------------------------------------------------------------------------------------------------------

## 5. Junk-value hazards and audit checklist

| hazard | where | mitigation |
|---|---|---|
| `tsum` of a non-summable family is 0 | K_G, K*_Q, K*_T (lattice sums), 𝒞_ζ | frozen together with a summability theorem for inputs with 𝔖^{40d,40d} decay (T.defkg.sum) and for Z^{d+1} data; the audit checks that every frozen use satisfies its hypotheses |
| `finsum` over an infinite support is 0 | 𝒦^tr_{p+1,N}, 𝒦_{p,N}, the sums in propansatz (3), (4) | finiteness lemma for layered gardens of given width, order and maximal layer (packet D3); audit item |
| Bochner integral of a non-integrable function is 0 | `collisionOp` (Wave A), 𝒰^{(p)}_N, cumulants under P.restrict F_p, ∫_{F p} a ā | Wave A audit (WKE.deltaChar); propansatz should also assert integrability of all products of a_n(t) on F p (they are bounded by powers of Σ_k φ_in(k)∣g_k∣², which has all moments) — recommended extra conjunct (1′) |
| norms defined as real-valued sups/integrals can be 0 by junk | 𝔖, 𝔛, restriction norms, Z | ENNReal-valued with ⊤ for non-smooth/non-integrable inputs (§2.6) |
| `Real.log`, `rpow` for L ≤ 1 | N_p, R_p, L^{−θ}, (log L)² | all statements have L ≥ L₀ and every L₀ is ≥ 2 by choice (state `2 ≤ L₀`) |
| existential witnesses chosen trivially | propansatz (∃ F, R, E, Ẽ) | P(F p) ≥ 1−e^{−N_p} and the moment identities with bounds on R, E pin the content; Ẽ is a defined difference with a bound |
| vacuous hypotheses | fixedpoint (`AnsatzAt` for all q ≤ p), layergarden (remainder bounds) | non-vacuity probes: R ≡ 0 satisfies layergarden's hypotheses; `AnsatzAt 0` holds for the Gaussian data (T.ansatzBase) |

Audit unit tests (cheap, decide/norm_num level): (i) exactly 2 mini-couples and 6 mini-trees (§3.1–§3.2);
(ii) every vine template has interior degree 4 and joint degree 2 and the stated atom/bond counts (§3.6);
(iii) the worked example T L733–L750 (Figure CanonGarden): the displayed formula equals K_G(3,k_1,…,k_4) for the
layered garden of the figure, and that garden satisfies `IsCanonG 3` (with the typo L749 F_2(K_15) → F_2(k_15));
(iv) the unit twist of §3.10 is an involution on the four drawn configurations; (v) `IsCanonG 1` = irreducible proper
gardens with all layers 0, `IsCanonC 1` = all couples with all layers 0 (T L664).

## 6. Open items for the author / orchestrator

1. **Counting policy** (§0.1): approve "≤ 20 theorem anchors; definitions frozen with their statements", or choose
   the def-light fallback.
2. **Tier B2 timing**: freeze `regularAsymptotics` / `incoherentDecay` (import boundary DH21 §4–§7, DH23 §6) only after
   packets C1, C2, C5 have validated the structure data and links; freeze `rigidity` only after the abstract
   hypothesis set of §4.13 is designed (packet G8) — or decide to keep `rigidity` unfrozen.
3. **GAP.largeOrder** (new finding, cf. F15): TARGET needs regular-couple asymptotics for orders up to
   N_{p+1}^4 = (log L)^{C(𝔇)}, DH21/DH23 prove them for n ≤ N³ = (log L)^{12}. Choose route R14 (re-check vs crude bound).
   Proposed FINDINGS entry F30.
4. **Gaussian hypercontractivity is not used by TARGET** (route R6): its large deviations come from 2P-th moments via
   the cumulant ansatz and Chebyshev (T L2306–L2335). The running packet GAUSS-HC (DH21 Lemma A.3) can be
   deprioritized. Proposed FINDINGS entry F31.
5. **Solution class (Q16)**: Z^{d+1} on [0,p] for the a-system (§2.3.2) and continuity in time for Z (§2.5.3): approve.
6. **layergarden as a deterministic statement** (§4.2 D1): approve (it removes the probabilistic hypothesis).
7. **Two-point function at intermediate times** (§4.1 item 2′): approve the form ∣∫_{F p}∣a_n(t)∣² − φ(δt)∣ ≤
   2L^{−θ_p} for t ∈ [p−1,p] (sufficient for `main`).
8. **Canonical gardens in criterion form** (route R12) with the "incomparable nodes" reading (§2.2.5): approve; the
   characterization theorem B2.4 is then the audit link to Def 3.7.
9. **Figure transcriptions** (§3.1–§3.10): a second independent reading of MiniCpl.png, MiniTree.png, OperAB.png,
   Vines.png, Block_Mole.png, twist_dec.png before freezing; in particular the unit-twist rule (§3.10 check (i)) and
   the direction conditions on vine slots (§3.6 check (iv)).
10. **sumint**: whether M (number of input vectors) must be bounded by a power of log L (check in packet V2), and the
    explicit extension behind 𝔛(ℬ) (F23).
11. **countLemma / atomCountLemma constants**: the proposal uses C(d,γ,c₀) (no φ dependence); confirm with the NT
    packets after GAP.circle23.
12. **Unpinned sources** (F29): DNY21 Lemma 3.1 (used by T.timeintlem) and DH19 Prop 2.3 (DH21 Lemma 10.2's proof
    source; DH19 TeX is pinned but the label must be located, candidate region DH19 L347–L407).
13. **atomcountbd3** (T L2474) is not used anywhere in T L1293–L2339; it is left out of `atomCountLemma`.
