# Wave B (tier B1) — freeze candidate for author approval

Snapshot `/home/scott/wt-scratch/waveb-snap-9` · prepared 2026-11-04 (supersedes snapshots 5–8: FINDINGS F56, B1.12, F68, F78, F80 fixes). **This is the exact Lean to be frozen** (one declaration per file under
`WaveTurbulence/Frozen/`, theorems with body `by sorry` as `DRAFT_SORRY` anchors, definitions sealed), exactly as for
Wave A (D6). File hashes: `WaveB1-Core.lean` 0b8477d9943a…, `WaveB1-System.lean` cc53aad3acd7…, `WaveB1-Statements.lean` e72e32df7fa0…, `WaveB1-Sumint.lean` 9750d760d676…, `WaveB1-Flower.lean` fd2b5e501d04….

## 1. What is frozen

12 theorem anchors and their definitions (167 defs, 4 abbrevs, 5 structures, 5 inductives, 33 instance-defs; full list
with source lines and dependencies: `FREEZE-LIST.md` of the snapshot, copied to `docs/review/WAVE-B-B1-FREEZE-LIST.md`).

| # | Lean name | TARGET source | what it says |
|---|---|---|---|
| B1.1 | `propansatz` | Prop `propansatz` L689–L707 (+ time parameter, F7/F27) | the inductive ansatz: events F_p, the two-point function = φ(δp,k) + R_p + E_p with ‖R_p‖_{𝔖^{Λ_p,Λ_p}} ≤ L^{−θ_p}, |E_p| ≤ ⟨k⟩^{−Λ_p}e^{−N_p}; higher cumulants = Σ over canonical layered gardens of K_G + small error; order-n decay |𝒦_{p,n}| ≤ ⟨k⟩^{−Λ_p}L^{−(R−1)/6}δ^{νn}; at every p ≤ 𝔇 and every rescaled time in [p,p+1] |
| B1.2 | `layergarden` | Prop `layergarden` L761–L779 (deterministic, time parameter) | the garden sums 𝒦^tr_{p+1,n}: (1) R ≥ 2 decay with L^{−(R−1)/4}δ^{2νn}; (2) R = 1: couple sums = WKE Taylor term 𝒰_n + R_{p+1,n}, with the stated bound |
| B1.3 | `fixedpoint` | Prop `fixedpoint` L780–L794 | the event F_{p+1} ⊆ F_p with P(F_p∖F_{p+1}) ≤ e^{−4N_{p+1}} and the bounds on a^tr, ℒ₀, (1−ℒ₁)^{−1}, contraction |
| B1.4 | `nlsAkBridge` | L540–L566, L817–L819 (F8) | NLS smooth solutions ↔ classed a-system solutions on [0,𝔇] (needs 1 ≤ 𝔇, deviation D3); measurability on [0,T] |
| B1.5 | `wkeTaylor` | (wketaylor)–(taylorbound) L752–L758 (F10) | WKE Taylor expansion over one step, with ‖𝒰_N‖_{𝔖^{4Λ,4Λ}} ≤ C₂(C₁δ)^N, C₁ independent of 𝔇 and Λ |
| B1.6 | `sumint` | Prop `sumint` L1595–L1722 | the general exponential-sum / oscillatory-integral estimate for vine chains (size hypothesis M ≤ N₁⁴, all Λ_v ≥ 1; shifts per Q9) |
| B1.7 | `countLemma` | `countlem` L2459–L2466 (DH23 A.2 (1),(3)) | lattice counting bounds (constant C before δ, L₀ after δ; exponent 2/3 suffices for these items, F3) |
| B1.8 | `atomCountLemma` | `atomcountlem` L2467–L2478 (DH23 A.3 (1),(2)) | two-vector counts; k ≠ 0 for ε = (+,−) (erratum F43) |
| B1.9 | `quadExpSum2` | `lemlayer2` L970–L977 (DH23 6.6(2)) | ∫_{L≤|s|≤T₀L^{2γ}} |Σ_{x,y} χ₀χ₀ e(…)| ds ≤ C L^{2d−2(d−1)(1−γ)+η} |
| B1.10 | `quadExpSum3` | `lemcubic` L1554–L1593 | the three-vector analogue ≤ C L^{3d+γ−2γ₀} log L |
| B1.11 | `canonicalCharacterization` | `canonequiv` L888–L897, Def 3.7 L657–L668 | the criterion form of canonical layered gardens ⇔ the inductive construction, with uniqueness of the construction data — **already proved in scratch** (wt-gauss-hc, 1447 lines, standard axioms) |
| B1.12 | `layergardenFlower` | Prop `flowerest1` L2279–L2305 (deterministic core; uses L2306–L2338) | flower-garden sums of width 2P (kinds 𝒳, 𝒴, 𝒲, derivative patterns, †, M₁/M₂ cutoffs) ≤ ⟨k−ζk'⟩^{−4Λ_{p+1}P} L^{c(100d)³P} δ^{2νN}·(cutoff gains), and couple sums (ℒ₀, ∂_t a^tr) ≤ ⟨k⟩^{−4Λ_{p+1}} L^{100d} δ^{νN} — **new in snapshot 6**; decisions in [`WAVE-B-B1-B112.md`](WAVE-B-B1-B112.md) |

## 2. Rulings and readings to approve

1. **Remainders R_q in finite smoothness** (C^{Λ_q}, forced by the 𝔖 norm), not C^∞ (stage-3 R1; F44: `ContDiff ℝ ⊤` is
   real-analytic in this Mathlib).
2. **`layergardenFlower` (B1.12) is now included** (packet X1 redraft, audited `FLOWER-redraft.md`; edits F1/F2 applied); its three decisions are in [`WAVE-B-B1-B112.md`](WAVE-B-B1-B112.md).
3. **`cumulantExpansion` stays unfrozen** (proof target T.cmattr) (stage-3 R9).
4. **`nlsAkBridge` gets `1 ≤ 𝔇`** (deviation D3: at 𝔇 = 0 the statement is false; `main` supplies 𝔇 ≥ 1).
5. **Count theorem anchors against the ~20 budget** (Wave A 2 + Wave B 12 = 14; deferred: B2.1–B2.3).
6. Readings (DESIGN Q1–Q9): layers in ℕ (Q1); 𝒞₀ empty (Q2); prefix composition lemma left to provers (Q3); arbitrary
   garden width (Q4); **symmetric events = preimages of invariant sets of initial data** (Q5, the literal source notion);
   χ₀ Gevrey 2 with a constant (Q6, F41); `sumint` shifts with coefficient sum 1, no offset (Q9).
7. The constant hierarchy is the parameter prefix (Π): d, γ → η₀ → data → C₁ → ν₀ → δ₀ → (δ, 𝔇) → C₂ → L₀ (F5).
8. Freeze-set definitions are self-contained (depend only on frozen Wave A definitions and Mathlib); bridges to the
   landed Foundations objects (χ₀, the a-system, the Taylor terms) are proved; norm bridges are provider obligations.
9. **Snapshot 6 fix (F56):** in `SumintDatum.phase` the normal-block product was inside the block product (Mathlib parses a `∏` body at precedence 67, `*` is 70); it is now `(∏ i, …) * ∏ i : Nor, …` as in TARGET (sumintI1). A sweep of every file found no other scope error (wt-gauss-hc; independently re-swept by wt-orch).
10. **Snapshot 7 fix (F68):** B1.12's `PatValid` `dChild` clause now requires the designated child of `𝔣^pr` to be a layer-`p` branching node (`LG.layer b.toNode = p`); otherwise `flowerSum (dChild i)` contained gardens TARGET's bound (L2331) does not cover. `PatValid` takes `p` as an argument; the text of B1.12 itself is unchanged; `fixedpoint` uses only the `plain` and `dRoot` patterns.
11. **Snapshot 8 fix (F78):** in B1.12's `coupleSum`, the `∂_t` clause requires both roots to be layer-`p` branching nodes (equivalently: both top trees nontrivial), matching TARGET L2312; it removes couples whose ∂_t contribution is zero in the source.
12. **Snapshot 9 fix (F80):** `XNorm`'s guard is TARGET's (normX): integrable time slices and `C^{Λ₁}` slices for almost every frequency (the landed `MixedFourierAdmissible`), instead of a per-frequency `⊤`; so `XNorm` and `XNormRestr` are TARGET's (normX)/(locnorm), with the triangle inequality. No B1 theorem uses them; B2.1 items (1)–(2) and B2.2 become exactly TARGET's statements (independently audited, `WaveB2-independent-audit.md` §Snapshot 9).

## 3. Audit trail

Stage audits: `docs/campaign/orch/audits/WaveB-stage1.md` (core definitions, wt-orch), `WaveB-stage2.md` (system objects,
wt-orch), `WaveB-stage3.md` (statements, independent Opus auditor: 9 REQUIRED); deltas `WaveB-delta-1.md`,
`WaveB-delta-stage3.md` (all closed; N1); `WaveB-final-check.md` (PASS); `WaveB-packaging-check.md` (packaging only).
Snapshot 6: `FLOWER-redraft.md` (B1.12), `WaveB-snapshot6.md` (delta audit: B1.12, F56, sweep), `WaveB-snapshot7.md` (F68 delta, PASS), independent audit §Snapshot 9 (F78, F80 deltas, PASS). Every REQUIRED item is closed; all files elaborate; the only `sorry`s are the 12 anchors.

## 4. The exact Lean code

### WaveB1-Core.lean

```lean
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Frozen.Defs.Mom
public import WaveTurbulence.Frozen.Defs.LatticePoint
public import WaveTurbulence.Frozen.Defs.IsWKESolution

/-!
# Wave B, tier B1 — core carriers (DRAFT for author approval)

Drafts of the source-facing definitions of WAVE-B §1.2 and §2.1–§2.2 (TARGET = Deng–Hani,
arXiv:2311.10082v2, `WKE-Longer_times_Final_arXiv.tex`). Not landed; see `DESIGN.md` for the carrier
choices and the deviations from the TeX.

* §1 Parameters: the parameter bundle `WTParams` and the quantifier prefix `WTPrefix` (WAVE-B (Π),
  T L605–L615), and the derived parameters `θ_p, Λ_p, R_p, N_p, γ₀, γ₁` (T L611–L613).
* §2 Ternary trees (T Def `deftree`, L625–L631), node addresses, node signs, `ζ(𝒯)`.
* §3 Gardens of width `w` with marked leaves (T Def `defgarden`, L632–L638; paired trees L637;
  flower gardens L2259–L2263; WAVE-B v2 §2.2.2): signature, partial pairing, marks, order,
  irreducibility; couples, paired trees, flower gardens.
* §4 Decorations (T Def `defdec`, L639–L648): integer (lattice) decorations, coset decorations of
  couples, `ε` and `ε_ℐ` (T L556–L561), `Ω_𝔫` (T (res), (defomega)). Self-contained: imports only
  frozen Wave A definitions and Mathlib (freeze-set closure policy).
* §5 Layerings (T Def `deflayer`, L649–L656).
* §6 Canonical layered gardens in criterion form (T Prop `canonequiv`, L888–L897; Def `defcanon`,
  L657–L668), with incomparable nodes (FINDINGS F35).
* §7 Truncation (T Def `defgtr`, L731–L732), stated without construction data.
-/

@[expose] public section

open Finset Set

namespace WaveTurbulence

/-! ## §1 Parameters (WAVE-B §1.2, T L605–L615) -/

/-- The parameters fixed in T §2.4.2 (L605–L615), in the order in which TARGET chooses them:
`d, γ` (and the absolute constant `C₀(d,γ)`), `η`, the data `φin, τ★, φ`, `C₁`, `ν`, `δ`
(with `𝔇 = τ★/δ ∈ ℤ`), `C₂`, `L`. The constraints between them are imposed by `WTPrefix`. -/
structure WTParams where
  /-- dimension -/
  d : ℕ
  /-- the exponent `γ ∈ (0,1)` of `α = L^{-γ}` -/
  γ : ℝ
  /-- the small parameter `η` (depends only on `C₀(d,γ)`) -/
  η : ℝ
  /-- the initial data of (WKE) -/
  φin : SchwartzMap (Mom d) ℝ
  /-- the final kinetic time `τ★` -/
  τstar : ℝ
  /-- the solution of (WKE) on `[0, τ★]` -/
  φ : ℝ → SchwartzMap (Mom d) ℝ
  /-- the constant `C₁ = C₁(d,γ,η,τ★,𝔆)` -/
  C₁ : ℝ
  /-- the small parameter `ν` (depends on `C₁`) -/
  ν : ℝ
  /-- the step `δ` (depends on `ν`), with `τ★ = 𝔇 δ` -/
  δ : ℝ
  /-- the number of steps `𝔇 = τ★ / δ ∈ ℤ` -/
  D : ℕ
  /-- the constant `C₂ = C₂(𝔇, δ, φin)` -/
  C₂ : ℝ
  /-- the size `L` of the torus (large depending on `C₂`) -/
  L : ℝ

/-- **The parameter prefix (Π)** (WAVE-B §1.2; T L605–L615 and FINDINGS F5): `P` holds for all
parameters chosen in TARGET's order `d, γ → η → φin, τ★, φ → C₁ → ν → δ, 𝔇 → C₂ → L`, each
"small" or "large" choice being eventual (`∃` threshold, `∀` beyond it) and each constant `Cⱼ`
existential right after the quantities it may depend on. -/
def WTPrefix (P : WTParams → Prop) : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 →
  ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, η ∈ Ioc 0 η₀ →
  ∀ φin : SchwartzMap (Mom d) ℝ, (∀ k, 0 ≤ φin k) →
  ∀ τstar : ℝ, 0 < τstar → ∀ φ : ℝ → SchwartzMap (Mom d) ℝ, IsWKESolution φin τstar φ →
  ∃ C₁ : ℝ, 1 ≤ C₁ ∧ ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ ν : ℝ, ν ∈ Ioc 0 ν₀ →
  ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, δ ∈ Ioc 0 δ₀ → ∀ D : ℕ, 1 ≤ D → τstar = D * δ →
  ∃ C₂ : ℝ, 1 ≤ C₂ ∧ ∃ L₀ : ℝ, 2 ≤ L₀ ∧ ∀ L : ℝ, L₀ ≤ L →
  P ⟨d, γ, η, φin, τstar, φ, C₁, ν, δ, D, C₂, L⟩

namespace WTParams

variable (P : WTParams)

/-- `θ_p := η^{20} (1 + 2^{-p})` (T (parameters), L611). -/
noncomputable def theta (p : ℕ) : ℝ := P.η ^ 20 * (1 + (2 : ℝ)⁻¹ ^ p)

/-- `Λ_p := (40d)^{𝔇-p+1}` (T (parameters), L611), for `0 ≤ p ≤ 𝔇 + 1`; written with exponent
`𝔇 + 1 - p`, which equals `𝔇 - p + 1` in that range (every use has `p ≤ 𝔇 + 1`). Junk range
(stage-1 O2): `Lambda p = 1` for `p > 𝔇 + 1`; no consumer reaches it. -/
def Lambda (p : ℕ) : ℕ := (40 * P.d) ^ (P.D + 1 - p)

/-- `R_{𝔇-k}` by downward recursion (T (parameters2), L612): `R_𝔇 = ⌊(log L)^{40d}⌋` and
`R_{p-1} = N_p^{40d} = (R_p^{40d})^{40d}`. -/
noncomputable def Rdown : ℕ → ℕ
  | 0 => ⌊Real.log P.L ^ (40 * P.d)⌋₊
  | k + 1 => (Rdown k ^ (40 * P.d)) ^ (40 * P.d)

/-- `R_p` for `0 ≤ p ≤ 𝔇` (T (parameters2)). Junk range (stage-1 O2): `R p = R_𝔇` for `p > 𝔇`
(truncated subtraction); statements quantify `p ≤ 𝔇` and use `q = p + 1 ≤ 𝔇`. -/
noncomputable def R (p : ℕ) : ℕ := P.Rdown (P.D - p)

/-- `N_p = R_p^{40d}` for `0 ≤ p ≤ 𝔇` (T (parameters2)). -/
noncomputable def N (p : ℕ) : ℕ := P.R p ^ (40 * P.d)

/-- `γ₀ := min(γ, 1-γ)` (T (defgamma1), L613). -/
noncomputable def gamma0 : ℝ := min P.γ (1 - P.γ)

/-- `γ₁ := min(2γ, 1, 2(d-1)(1-γ))` (T (defgamma1), L613). -/
noncomputable def gamma1 : ℝ := min (2 * P.γ) (min 1 (2 * ((P.d : ℝ) - 1) * (1 - P.γ)))

end WTParams

/-! ## §2 Ternary trees (T Def `deftree`, L625–L631) -/

/-- A ternary tree: a leaf, or a branching node with left, mid and right subtrees
(T Def `deftree`; DH21 Def 2.1). The trivial tree `•` is `leaf`. -/
inductive TTree : Type
  | leaf : TTree
  | node (l m r : TTree) : TTree

/-- Decidable equality of ternary trees (structural recursion). -/
def TTree.decEq : (a b : TTree) → Decidable (a = b)
  | .leaf, .leaf => isTrue rfl
  | .leaf, .node .. => isFalse fun h => TTree.noConfusion h
  | .node .., .leaf => isFalse fun h => TTree.noConfusion h
  | .node l m r, .node l' m' r' =>
    match TTree.decEq l l', TTree.decEq m m', TTree.decEq r r' with
    | isTrue h₁, isTrue h₂, isTrue h₃ => isTrue (by rw [h₁, h₂, h₃])
    | isFalse h, _, _ => isFalse fun e => h (TTree.node.inj e).1
    | isTrue _, isFalse h, _ => isFalse fun e => h (TTree.node.inj e).2.1
    | isTrue _, isTrue _, isFalse h => isFalse fun e => h (TTree.node.inj e).2.2

@[instance_reducible, instance] def instDecidableEqTTree : DecidableEq TTree := TTree.decEq

namespace TTree

/-- Node addresses: the path from the root, `0, 1, 2` = left, mid, right child. The children of
the node at `p` are `p ++ [0], p ++ [1], p ++ [2]`; the parent of `p ≠ []` is `p.dropLast`. -/
abbrev Path := List (Fin 3)

/-- The order `n(𝒯) = |𝒩|`, the number of branching nodes. -/
def order : TTree → ℕ
  | leaf => 0
  | node l m r => l.order + m.order + r.order + 1

/-- Prefix every path of a set by a first step `i`. -/
def pre (i : Fin 3) (S : Finset Path) : Finset Path := S.image (List.cons i)

/-- All node addresses. -/
def nodes : TTree → Finset Path
  | leaf => {[]}
  | node l m r => insert [] (pre 0 l.nodes ∪ pre 1 m.nodes ∪ pre 2 r.nodes)

/-- Addresses of the leaves `ℒ` (the root of `•` is a leaf). -/
def leaves : TTree → Finset Path
  | leaf => {[]}
  | node l m r => pre 0 l.leaves ∪ pre 1 m.leaves ∪ pre 2 r.leaves

/-- Addresses of the branching nodes `𝒩`. -/
def branching : TTree → Finset Path
  | leaf => ∅
  | node l m r => insert [] (pre 0 l.branching ∪ pre 1 m.branching ∪ pre 2 r.branching)

/-- The sign `ζ_𝔫` of the node at path `p` in a tree of sign `ζ`: children of a node of sign `ζ'`
have signs `(ζ', -ζ', ζ')`, so `ζ_𝔫 = ζ (-1)^{#mid steps}`. -/
def pathSign (ζ : ℤˣ) (p : Path) : ℤˣ := ζ * (-1) ^ (p.count 1)

end TTree

/-! ## §3 Gardens and couples (T Def `defgarden`, L632–L638) -/

section Forest

open TTree

variable {w : ℕ} (tree : Fin w → TTree)

/-- The set of global addresses `(j, p)` (tree index, path) with `p ∈ f (tree j)`. -/
def forestSet (f : TTree → Finset Path) : Finset (Fin w × Path) :=
  Finset.univ.biUnion fun j => (f (tree j)).image (Prod.mk j)

/-- The nodes of a forest `(𝒯_j)`, as global addresses. -/
def GNode : Type := {a : Fin w × Path // a.2 ∈ (tree a.1).nodes}

/-- The leaves `ℒ = ℒ₁ ∪ ⋯ ∪ ℒ_w` of a forest. -/
def GLeaf : Type := {a : Fin w × Path // a.2 ∈ (tree a.1).leaves}

/-- The branching nodes `𝒩 = 𝒩₁ ∪ ⋯ ∪ 𝒩_w` of a forest. -/
def GBranch : Type := {a : Fin w × Path // a.2 ∈ (tree a.1).branching}

@[instance_reducible, instance] def instDecidableEqGNode : DecidableEq (GNode tree) :=
  inferInstanceAs (DecidableEq (Subtype _))
@[instance_reducible, instance] def instDecidableEqGLeaf : DecidableEq (GLeaf tree) :=
  inferInstanceAs (DecidableEq (Subtype _))
@[instance_reducible, instance] def instDecidableEqGBranch : DecidableEq (GBranch tree) :=
  inferInstanceAs (DecidableEq (Subtype _))

@[instance_reducible, instance] def instFintypeGNode : Fintype (GNode tree) :=
  Fintype.subtype (forestSet tree TTree.nodes) fun a => by
    simp only [forestSet, Finset.mem_biUnion, Finset.mem_univ, Finset.mem_image, true_and]
    constructor
    · rintro ⟨j, q, hq, rfl⟩
      exact hq
    · intro h
      exact ⟨a.1, a.2, h, rfl⟩
@[instance_reducible, instance] def instFintypeGLeaf : Fintype (GLeaf tree) :=
  Fintype.subtype (forestSet tree TTree.leaves) fun a => by
    simp only [forestSet, Finset.mem_biUnion, Finset.mem_univ, Finset.mem_image, true_and]
    constructor
    · rintro ⟨j, q, hq, rfl⟩
      exact hq
    · intro h
      exact ⟨a.1, a.2, h, rfl⟩
@[instance_reducible, instance] def instFintypeGBranch : Fintype (GBranch tree) :=
  Fintype.subtype (forestSet tree TTree.branching) fun a => by
    simp only [forestSet, Finset.mem_biUnion, Finset.mem_univ, Finset.mem_image, true_and]
    constructor
    · rintro ⟨j, q, hq, rfl⟩
      exact hq
    · intro h
      exact ⟨a.1, a.2, h, rfl⟩

variable {tree}

/-- A leaf as a node. -/
def GLeaf.toNode (ℓ : GLeaf tree) : GNode tree :=
  ⟨ℓ.1, by
    have key : ∀ (t : TTree) (p : TTree.Path), p ∈ t.leaves → p ∈ t.nodes := by
      intro t
      induction t with
      | leaf => exact fun p hp => by simpa [TTree.leaves, TTree.nodes] using hp
      | node l m r ihl ihm ihr =>
        intro p hp
        simp only [TTree.leaves, TTree.pre, Finset.mem_union, Finset.mem_image] at hp
        simp only [TTree.nodes, TTree.pre, Finset.mem_insert, Finset.mem_union, Finset.mem_image]
        rcases hp with (⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩) | ⟨q, hq, rfl⟩
        · exact Or.inr (Or.inl (Or.inl ⟨q, ihl q hq, rfl⟩))
        · exact Or.inr (Or.inl (Or.inr ⟨q, ihm q hq, rfl⟩))
        · exact Or.inr (Or.inr ⟨q, ihr q hq, rfl⟩)
    exact key _ _ ℓ.2⟩

/-- A branching node as a node. -/
def GBranch.toNode (b : GBranch tree) : GNode tree :=
  ⟨b.1, by
    have key : ∀ (t : TTree) (p : TTree.Path), p ∈ t.branching → p ∈ t.nodes := by
      intro t
      induction t with
      | leaf => exact fun p hp => by simp [TTree.branching] at hp
      | node l m r ihl ihm ihr =>
        intro p hp
        simp only [TTree.branching, TTree.pre, Finset.mem_insert, Finset.mem_union,
          Finset.mem_image] at hp
        simp only [TTree.nodes, TTree.pre, Finset.mem_insert, Finset.mem_union, Finset.mem_image]
        rcases hp with rfl | (⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩) | ⟨q, hq, rfl⟩
        · exact Or.inl rfl
        · exact Or.inr (Or.inl (Or.inl ⟨q, ihl q hq, rfl⟩))
        · exact Or.inr (Or.inl (Or.inr ⟨q, ihm q hq, rfl⟩))
        · exact Or.inr (Or.inr ⟨q, ihr q hq, rfl⟩)
    exact key _ _ b.2⟩

/-- The `i`-th child (`0, 1, 2` = left, mid, right) of a branching node. -/
def GBranch.child (b : GBranch tree) (i : Fin 3) : GNode tree :=
  ⟨(b.1.1, b.1.2 ++ [i]), by
    have cons_mem : ∀ (i j : Fin 3) (S : Finset TTree.Path) (q : TTree.Path),
        j :: q ∈ TTree.pre i S ↔ i = j ∧ q ∈ S := by
      intro i j S q
      simp only [TTree.pre, Finset.mem_image, List.cons.injEq]
      constructor
      · rintro ⟨q', hq', rfl, rfl⟩
        exact ⟨rfl, hq'⟩
      · rintro ⟨rfl, hq⟩
        exact ⟨q, hq, rfl, rfl⟩
    have key : ∀ (t : TTree) (p : TTree.Path), p ∈ t.branching → ∀ i : Fin 3,
        p ++ [i] ∈ t.nodes := by
      intro t
      induction t with
      | leaf => exact fun p hp => by simp [TTree.branching] at hp
      | node l m r ihl ihm ihr =>
        intro p hp i
        rcases p with _ | ⟨j, p⟩
        · have hnil : ∀ s : TTree, ([] : TTree.Path) ∈ s.nodes := fun s => by
            cases s <;> simp [TTree.nodes]
          simp only [List.nil_append, TTree.nodes, Finset.mem_insert, Finset.mem_union, cons_mem]
          fin_cases i <;> simp [hnil]
        · simp only [TTree.branching, Finset.mem_insert, Finset.mem_union, cons_mem, reduceCtorEq,
            false_or] at hp
          simp only [List.cons_append, TTree.nodes, Finset.mem_insert, Finset.mem_union, cons_mem,
            reduceCtorEq, false_or]
          rcases hp with (⟨rfl, h⟩ | ⟨rfl, h⟩) | ⟨rfl, h⟩
          · exact Or.inl (Or.inl ⟨rfl, ihl p h i⟩)
          · exact Or.inl (Or.inr ⟨rfl, ihm p h i⟩)
          · exact Or.inr ⟨rfl, ihr p h i⟩
    exact key _ _ b.2 i⟩

variable (tree) in
/-- The root `𝔯_j` of the `j`-th tree. -/
def GNode.root (j : Fin w) : GNode tree :=
  ⟨(j, []), by
    show ([] : TTree.Path) ∈ (tree j).nodes
    rcases tree j with _ | ⟨l, m, r⟩ <;> simp [TTree.nodes]⟩

/-- `IsDesc a a'`: the node `a'` is a descendant of `a` (`a' = a` allowed, T L627). -/
def GNode.IsDesc (a a' : GNode tree) : Prop := a.1.1 = a'.1.1 ∧ a.1.2 <+: a'.1.2

@[instance_reducible, instance] def instDecidableIsDesc (a a' : GNode tree) : Decidable (a.IsDesc a') :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- Two nodes are incomparable if neither is a descendant of the other. -/
def GNode.Incomparable (a a' : GNode tree) : Prop := ¬ a.IsDesc a' ∧ ¬ a'.IsDesc a

@[instance_reducible, instance] def instDecidableIncomparable (a a' : GNode tree) :
    Decidable (a.Incomparable a') :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The leaves of the subtree rooted at `a`. -/
def GNode.leavesBelow (a : GNode tree) : Finset (GLeaf tree) :=
  Finset.univ.filter fun ℓ => a.IsDesc ℓ.toNode

/-- The number of branching nodes of the subtree rooted at `a` (its order). -/
def GNode.orderBelow (a : GNode tree) : ℕ :=
  (Finset.univ.filter fun b : GBranch tree => a.IsDesc b.toNode).card

/-- The sign `ζ_𝔫` of the node at global address `a` when the trees have signs `sig`. -/
def nodeSign (sig : Fin w → ℤˣ) (a : Fin w × Path) : ℤˣ := TTree.pathSign (sig a.1) a.2

end Forest

/-- The tag of a marked (unpaired) leaf (WAVE-B v2 §2.2.2): `lower` for the lone leaf of a paired
tree (domain constraint `t_{ℓ_lo^pr} > s`, T (timepairtree)), `equal` for a flower (`t_{𝔣^pr} := s`,
T (kqflower)). -/
inductive MarkTag : Type
  | lower : MarkTag
  | equal : MarkTag

@[instance_reducible, instance] def instDecidableEqMarkTag : DecidableEq MarkTag := fun a b =>
  match a, b with
  | .lower, .lower => isTrue rfl
  | .lower, .equal => isFalse fun h => MarkTag.noConfusion h
  | .equal, .lower => isFalse fun h => MarkTag.noConfusion h
  | .equal, .equal => isTrue rfl

@[instance_reducible, instance] def instFintypeMarkTag : Fintype MarkTag :=
  ⟨{MarkTag.lower, MarkTag.equal}, fun x => by cases x <;> simp⟩

/-- A **garden of width `w` with marked leaves** (T Def `defgarden`, L632–L638; DH21-2 Def 4.1;
paired trees L637; flower gardens Def `defflower`, L2259–L2263; WAVE-B v2 §2.2.2 and topology review
G-1): trees `𝒯_j` of signs `ζ_j` (`j < w`), a set of **marked** leaves with tags, and a pairing of the
unmarked leaves into pairs of opposite signs. The pairing is encoded as an involution `pair` of all
leaves whose fixed points are exactly the marked leaves. Instances: ordinary gardens (`IsPlain`,
width `2m`), couples (`IsCouple`), paired trees (`IsPairedTree`, width 1), flower gardens
(`IsFlowerGarden`). Irreducibility and balance of the signature are predicates. -/
structure Garden (w : ℕ) where
  /-- the signature `(ζ₁,…,ζ_w)` -/
  sig : Fin w → ℤˣ
  /-- the trees `𝒯₁,…,𝒯_w` -/
  tree : Fin w → TTree
  /-- the pairing involution (fixed points = marked leaves) -/
  pair : GLeaf tree → GLeaf tree
  /-- the marks: `none` for paired leaves, `some tag` for marked (unpaired) leaves -/
  mark : GLeaf tree → Option MarkTag
  pair_pair : ∀ ℓ, pair (pair ℓ) = ℓ
  pair_eq_iff : ∀ ℓ, pair ℓ = ℓ ↔ mark ℓ ≠ none
  /-- paired leaves have opposite signs -/
  pair_sign : ∀ ℓ, pair ℓ ≠ ℓ → nodeSign sig (pair ℓ).1 = -nodeSign sig ℓ.1

namespace Garden

variable {w : ℕ} (G : Garden w)

/-- `ℓ` is a flower (marked with tag `equal`). -/
def IsFlower (ℓ : GLeaf G.tree) : Prop := G.mark ℓ = some MarkTag.equal

/-- `ℓ` is a lone leaf (marked with tag `lower`). -/
def IsLone (ℓ : GLeaf G.tree) : Prop := G.mark ℓ = some MarkTag.lower

@[instance_reducible, instance] def instDecidableIsFlower (ℓ : GLeaf G.tree) : Decidable (G.IsFlower ℓ) :=
  inferInstanceAs (Decidable (_ = _))
@[instance_reducible, instance] def instDecidableIsLone (ℓ : GLeaf G.tree) : Decidable (G.IsLone ℓ) :=
  inferInstanceAs (Decidable (_ = _))

/-- An ordinary garden (T Def `defgarden`): no marked leaves, all leaves paired. -/
def IsPlain : Prop := ∀ ℓ, G.mark ℓ = none

@[instance_reducible, instance] def instDecidableIsPlain : Decidable G.IsPlain := by
  unfold IsPlain
  infer_instance

/-- Exactly half of the signs are `+` (automatic for plain gardens). -/
def IsBalanced : Prop := ∑ j, ((G.sig j : ℤˣ) : ℤ) = 0

@[instance_reducible, instance] def instDecidableIsBalanced : Decidable G.IsBalanced :=
  inferInstanceAs (Decidable (_ = _))

/-- A **flower garden** (T Def `defflower`): every tree has exactly one marked leaf, it is a flower,
and the root signs alternate `(+,-,…,+,-)`. TARGET's flower gardens have even width `2P`; the
predicate allows any `w`, and the width is fixed by the consumer (`w := 2 * Pm`; stage-1 O1). -/
def IsFlowerGarden : Prop :=
  (∀ j : Fin w, (Finset.univ.filter fun ℓ : GLeaf G.tree => ℓ.1.1 = j ∧ G.mark ℓ ≠ none).card = 1)
    ∧ (∀ ℓ, G.mark ℓ ≠ none → G.IsFlower ℓ) ∧ ∀ j : Fin w, G.sig j = (-1) ^ (j : ℕ)

@[instance_reducible, instance] def instDecidableIsFlowerGarden : Decidable G.IsFlowerGarden := by
  unfold IsFlowerGarden
  infer_instance

/-- The order `n(𝒢) = ∑_j n(𝒯_j) = |𝒩|`. -/
def order : ℕ := ∑ j, (G.tree j).order

/-- The sign of a node. -/
def sign (a : GNode G.tree) : ℤˣ := nodeSign G.sig a.1

/-- `ζ(𝒢) = ∏_{𝔫 ∈ 𝒩} (i ζ_𝔫)` (T Def `defgarden`). -/
noncomputable def zeta : ℂ :=
  ∏ b : GBranch G.tree, (Complex.I * (((G.sign b.toNode : ℤˣ) : ℤ) : ℂ))

/-- A set of leaves is **completely paired** if it contains no marked leaf and the pairing maps it
into itself. -/
def CompletelyPaired (S : Finset (GLeaf G.tree)) : Prop := ∀ ℓ ∈ S, G.pair ℓ ≠ ℓ ∧ G.pair ℓ ∈ S

@[instance_reducible, instance] def instDecidableCompletelyPaired (S : Finset (GLeaf G.tree)) :
    Decidable (G.CompletelyPaired S) := by
  unfold CompletelyPaired
  infer_instance

/-- The leaves of the trees `𝒯_j, j ∈ A`. -/
def leavesOf (A : Finset (Fin w)) : Finset (GLeaf G.tree) :=
  Finset.univ.filter fun ℓ => ℓ.1.1 ∈ A

/-- **Irreducible** (T L636): there is no `A ⊆ {1,…,w}` with `A ≠ ∅`, `A ≠` everything, such that
the leaves of the trees `𝒯_j, j ∈ A`, are all paired with each other. -/
def Irreducible : Prop :=
  ∀ A : Finset (Fin w), A.Nonempty → A ≠ Finset.univ → ¬ G.CompletelyPaired (G.leavesOf A)

@[instance_reducible, instance] def instDecidableIrreducible : Decidable G.Irreducible := by
  unfold Irreducible
  infer_instance

end Garden

/-- A **couple** (T L634–L635): a plain garden of width `2` with signature `(+,-)`; its trees are
`𝒯⁺ = tree 0` and `𝒯⁻ = tree 1`. -/
def IsCouple (G : Garden 2) : Prop := G.IsPlain ∧ G.sig = ![1, -1]

@[instance_reducible, instance] def instDecidableIsCouple (G : Garden 2) : Decidable (IsCouple G) := by
  unfold IsCouple
  infer_instance

/-- A **paired tree** (T L637): one tree whose leaves are paired except one, the lone leaf (marked
`lower`). -/
def IsPairedTree (G : Garden 1) : Prop :=
  (Finset.univ.filter fun ℓ : GLeaf G.tree => G.mark ℓ ≠ none).card = 1 ∧
    ∀ ℓ, G.mark ℓ ≠ none → G.IsLone ℓ

@[instance_reducible, instance] def instDecidableIsPairedTree (G : Garden 1) :
    Decidable (IsPairedTree G) := by
  unfold IsPairedTree
  infer_instance

/-! ## §4 Decorations, `ε` and `Ω` (T Def `defdec`, L639–L648; (defcoef0), (res)) -/

section Decorations

variable {w : ℕ} (G : Garden w)

/-- `κ : 𝒢 → V` is a **decoration** (T Def `defdec`): `κ_𝔫 = κ_{𝔫₁} - κ_{𝔫₂} + κ_{𝔫₃}` at every
branching node (children left, mid, right) and `κ_ℓ = κ_{ℓ'}` for paired leaves. Used with
`V = (Fin d → ℤ)` (lattice indices `n`, vectors `n/L`) and `V = Mom d`. -/
def IsDecoration {V : Type*} [AddCommGroup V] (κ : GNode G.tree → V) : Prop :=
  (∀ b : GBranch G.tree, κ b.toNode = κ (b.child 0) - κ (b.child 1) + κ (b.child 2)) ∧
    ∀ ℓ : GLeaf G.tree, κ ℓ.toNode = κ (G.pair ℓ).toNode

/-- The **integer `(n₁,…,n_w)`-decorations** (T Def `defdec`): decorations by lattice indices
`κ_𝔫 ∈ ℤ^d` (the vector of node `𝔫` is `κ_𝔫 / L`, `latticePoint L κ_𝔫`) with root values
`κ_{𝔯_j} = n_j`. -/
def IntDecoration (d : ℕ) (n : Fin w → (Fin d → ℤ)) : Type :=
  {κ : GNode G.tree → (Fin d → ℤ) // IsDecoration G κ ∧ ∀ j, κ (GNode.root G.tree j) = n j}

/-- The **general integer decorations** used by the one kernel `kernelK`: root values `n_j` and,
at every flower, the value `n'` (T Def `defflower`: `(k, k')`-decorations). For plain gardens and
paired trees the flower condition is void. -/
def GenDecoration (d : ℕ) (n : Fin w → (Fin d → ℤ)) (n' : Fin d → ℤ) : Type :=
  {κ : GNode G.tree → (Fin d → ℤ) // IsDecoration G κ ∧ (∀ j, κ (GNode.root G.tree j) = n j) ∧
    ∀ ℓ : GLeaf G.tree, G.IsFlower ℓ → κ ℓ.toNode = n'}

/-- The vectors of a coset decoration `k_𝔫 = k₀ + z_𝔫 / L` (T L643: for couples and paired trees
with root vector `k₀ ∈ ℝ^d`, `k_𝔫 - k₀ ∈ ℤ_L^d`; `k₀ = 0` gives lattice decorations). As `z` ranges
over the integer decorations with root values `0`, this ranges bijectively over the
`k₀`-decorations (`L ≠ 0`). -/
noncomputable def cosetDecoration {d : ℕ} (L : ℝ) (k : Mom d) (z : GNode G.tree → (Fin d → ℤ)) :
    GNode G.tree → Mom d :=
  fun a => k + latticePoint L (z a)

/-- `ε_{k₁k₂k₃}` (T (defcoef0), L556–L561) on lattice indices `kᵢ = nᵢ/L`: `+1` if `k₂ ∉ {k₁, k₃}`,
`-1` if `k₁ = k₂ = k₃`, `0` otherwise. Self-contained (freeze-set closure policy, fix list 3 item 3);
it is the landed `NLS.epsCoef` (bridge `epsCoef_eq_nls`, `WaveB1-Bridges.lean`). -/
def epsCoef {d : ℕ} (n₁ n₂ n₃ : Fin d → ℤ) : ℝ :=
  if n₂ ≠ n₁ ∧ n₂ ≠ n₃ then 1 else if n₁ = n₂ ∧ n₂ = n₃ then -1 else 0

/-- `ε_ℐ = ∏_{𝔫 ∈ 𝒩} ε_{k_{𝔫₁} k_{𝔫₂} k_{𝔫₃}}` (T (defepscoef)), with `ε = epsCoef` (T (defcoef0))
evaluated on the integer labels of a decoration (for
coset decorations `k + z/L` this gives the same value, `z ↦ k + z/L` being injective). -/
def epsDec {d : ℕ} (κ : GNode G.tree → (Fin d → ℤ)) : ℝ :=
  ∏ b : GBranch G.tree, epsCoef (κ (b.child 0)) (κ (b.child 1)) (κ (b.child 2))

/-- The resonance factor `Ω(k₁,k₂,k₃,k) = |k₁|² - |k₂|² + |k₃|² - |k|²` (T (res)). -/
noncomputable def resFactor {d : ℕ} (k₁ k₂ k₃ k : Mom d) : ℝ :=
  ‖k₁‖ ^ 2 - ‖k₂‖ ^ 2 + ‖k₃‖ ^ 2 - ‖k‖ ^ 2

/-- `Ω_𝔫` of a branching node for a vector decoration `k` (T (defomega)). -/
noncomputable def omegaNode {d : ℕ} (k : GNode G.tree → Mom d) (b : GBranch G.tree) : ℝ :=
  resFactor (k (b.child 0)) (k (b.child 1)) (k (b.child 2)) (k b.toNode)

end Decorations

/-! ## §5 Layerings (T Def `deflayer`, L649–L656) -/

/-- A **layering** `𝔏 : 𝒢 → ℕ` (T Def `deflayer`): `𝔏_{𝔫'} ≤ 𝔏_𝔫` whenever `𝔫'` is a child of
`𝔫`, and `𝔏_ℓ = 𝔏_{ℓ'}` for paired leaves. (`0 ≤ 𝔏` is built into `ℕ`; DESIGN Q1.) -/
def IsLayering {w : ℕ} (G : Garden w) (𝔏 : GNode G.tree → ℕ) : Prop :=
  (∀ b : GBranch G.tree, ∀ i : Fin 3, 𝔏 (b.child i) ≤ 𝔏 b.toNode) ∧
    ∀ ℓ : GLeaf G.tree, 𝔏 ℓ.toNode = 𝔏 (G.pair ℓ).toNode

@[instance_reducible, instance] def instDecidableIsLayering {w : ℕ} (G : Garden w) (𝔏 : GNode G.tree → ℕ) :
    Decidable (IsLayering G 𝔏) := by
  unfold IsLayering
  infer_instance

/-- A **layered garden** of width `w`. -/
structure LayeredGarden (w : ℕ) where
  /-- the garden -/
  garden : Garden w
  /-- the layers `𝔏_𝔫` -/
  layer : GNode garden.tree → ℕ
  isLayering : IsLayering garden layer

/-! ## §6 Canonical layered gardens (criterion form; T Prop `canonequiv`, L888–L897) -/

namespace LayeredGarden

variable {w : ℕ} (LG : LayeredGarden w)

/-- The layer of the parent of `a`, the parent layer of a root being read as `top`
(T Prop `canonequiv`: "replaced by `p`"). -/
def parentLayer (top : ℕ) (a : GNode LG.garden.tree) : ℕ :=
  if a.1.2 = [] then top
  else LG.layer ⟨(a.1.1, a.1.2.dropLast), by
    have cons_mem : ∀ (i j : Fin 3) (S : Finset TTree.Path) (q : TTree.Path),
        j :: q ∈ TTree.pre i S ↔ i = j ∧ q ∈ S := by
      intro i j S q
      simp only [TTree.pre, Finset.mem_image, List.cons.injEq]
      constructor
      · rintro ⟨q', hq', rfl, rfl⟩
        exact ⟨rfl, hq'⟩
      · rintro ⟨rfl, hq⟩
        exact ⟨q, hq, rfl, rfl⟩
    have key : ∀ (t : TTree) (p : TTree.Path), p ∈ t.nodes → p.dropLast ∈ t.nodes := by
      intro t
      induction t with
      | leaf =>
        intro p h
        simp only [TTree.nodes, Finset.mem_singleton] at h
        subst h
        simp [TTree.nodes]
      | node l m r ihl ihm ihr =>
        intro p h
        rcases p with _ | ⟨j, p⟩
        · simp [TTree.nodes]
        · simp only [TTree.nodes, Finset.mem_insert, Finset.mem_union, cons_mem, reduceCtorEq,
            false_or] at h
          rcases p with _ | ⟨c, p⟩
          · simp [TTree.nodes]
          · rw [List.dropLast_cons_cons]
            simp only [TTree.nodes, Finset.mem_insert, Finset.mem_union, cons_mem, reduceCtorEq,
              false_or]
            rcases h with (⟨rfl, h⟩ | ⟨rfl, h⟩) | ⟨rfl, h⟩
            · exact Or.inl (Or.inl ⟨rfl, by simpa using ihl _ h⟩)
            · exact Or.inl (Or.inr ⟨rfl, by simpa using ihm _ h⟩)
            · exact Or.inr ⟨rfl, by simpa using ihr _ h⟩
    exact key _ _ a.2⟩

/-- **Canonicity criterion at depth `p + 1`** (T Prop `canonequiv` (i)–(ii), L889): (i) every node
is in layer `≤ p`; (ii) for any two incomparable nodes `𝔫, 𝔫'` (FINDINGS F35) whose subtrees have
completely paired leaves, `max(𝔏_𝔫, 𝔏_{𝔫'}) ≥ min(𝔏_{𝔫^pr}, 𝔏_{𝔫'^pr})`, a root's parent layer
being read as `p`. -/
def CanonCriterion (p : ℕ) : Prop :=
  (∀ a, LG.layer a ≤ p) ∧
    ∀ a a' : GNode LG.garden.tree, a.Incomparable a' →
      LG.garden.CompletelyPaired (a.leavesBelow ∪ a'.leavesBelow) →
        min (LG.parentLayer p a) (LG.parentLayer p a') ≤ max (LG.layer a) (LG.layer a')

@[instance_reducible, instance] def instDecidableCanonCriterion (p : ℕ) :
    Decidable (LG.CanonCriterion p) := by
  unfold CanonCriterion
  infer_instance

/-- The **stem** of a flower tree: the ancestors of a flower (T Def `defflower`). -/
def OnStem (a : GNode LG.garden.tree) : Prop :=
  ∃ ℓ : GLeaf LG.garden.tree, LG.garden.IsFlower ℓ ∧ a.IsDesc ℓ.toNode

@[instance_reducible, instance] def instDecidableOnStem (a : GNode LG.garden.tree) :
    Decidable (LG.OnStem a) := by
  unfold OnStem
  infer_instance

end LayeredGarden

/-- **Canonical layered gardens `𝒢_q`** (T Def `defcanon`, L657–L668, in the equivalent criterion
form of T Prop `canonequiv`, L889; route R12): `𝒢₀ = ∅`, and `LG ∈ 𝒢_{p+1}` iff the garden is plain,
proper (width `≥ 4`), irreducible and satisfies `CanonCriterion p`. The agreement with the inductive
construction of Def `defcanon` is the B1 anchor `canonicalCharacterization` (B1.11, review G-2). -/
def IsCanonG {w : ℕ} : ℕ → LayeredGarden w → Prop
  | 0, _ => False
  | p + 1, LG => 4 ≤ w ∧ LG.garden.IsPlain ∧ LG.garden.Irreducible ∧ LG.CanonCriterion p

/-- **Canonical layered couples `𝒞_q`** (T Def `defcanon`, last paragraph; criterion form by T Prop
`canonequiv`): `LG ∈ 𝒞_{p+1}` iff `LG` is a couple satisfying `CanonCriterion p` (irreducibility is
automatic for couples). `𝒞₀` is not defined in TARGET; we set it empty (DESIGN Q2). -/
def IsCanonC : ℕ → LayeredGarden 2 → Prop
  | 0, _ => False
  | p + 1, LG => IsCouple LG.garden ∧ LG.CanonCriterion p

/-- **Canonical layered flower gardens `ℋ_q`** (T Def `defflower`, last paragraph; criterion form:
"Proposition `canonequiv` also holds for `ℋ_{p+1}`"): a flower garden with all stem nodes in layer
`p`, satisfying `CanonCriterion p` (no irreducibility, no properness). -/
def IsCanonH {w : ℕ} : ℕ → LayeredGarden w → Prop
  | 0, _ => False
  | p + 1, LG => LG.garden.IsFlowerGarden ∧ (∀ a, LG.OnStem a → LG.layer a = p) ∧
      LG.CanonCriterion p

@[instance_reducible, instance] def instDecidableIsCanonG {w : ℕ} (q : ℕ) (LG : LayeredGarden w) :
    Decidable (IsCanonG q LG) :=
  match q with
  | 0 => isFalse fun h => h
  | p + 1 => inferInstanceAs
    (Decidable (4 ≤ w ∧ LG.garden.IsPlain ∧ LG.garden.Irreducible ∧ LG.CanonCriterion p))

@[instance_reducible, instance] def instDecidableIsCanonC (q : ℕ) (LG : LayeredGarden 2) :
    Decidable (IsCanonC q LG) :=
  match q with
  | 0 => isFalse fun h => h
  | p + 1 => inferInstanceAs (Decidable (IsCouple LG.garden ∧ LG.CanonCriterion p))

@[instance_reducible, instance] def instDecidableIsCanonH {w : ℕ} (q : ℕ) (LG : LayeredGarden w) :
    Decidable (IsCanonH q LG) :=
  match q with
  | 0 => isFalse fun h => h
  | p + 1 => inferInstanceAs (Decidable (LG.garden.IsFlowerGarden ∧
      (∀ a, LG.OnStem a → LG.layer a = p) ∧ LG.CanonCriterion p))

/-! ## §7 Truncation (T Def `defgtr`, L731–L732) -/

namespace LayeredGarden

variable {w : ℕ} (LG : LayeredGarden w)

/-- The nodes `𝒰` at which the gardens of `𝒢_p` are attached in the construction of a garden of
`𝒢_{p+1}` (T Prop `canonequiv`, proof): `𝔏_𝔫 < p` and `𝔏_{𝔫^pr} = p` (roots: parent layer `p`). -/
def attachNodes (p : ℕ) : Finset (GNode LG.garden.tree) :=
  Finset.univ.filter fun a => LG.layer a < p ∧ LG.parentLayer p a = p

/-- The order of the top tree `𝒯_j^p`: the number of branching nodes of `𝒯_j` in layer `p`. -/
def topOrder (p : ℕ) (j : Fin w) : ℕ :=
  (Finset.univ.filter fun b : GBranch LG.garden.tree => b.1.1 = j ∧ LG.layer b.toNode = p).card

/-- Two nodes are linked if some leaf below the first is paired with a leaf below the second. -/
def AttachLinked (u u' : GNode LG.garden.tree) : Prop :=
  ∃ ℓ ∈ u.leavesBelow, LG.garden.pair ℓ ∈ u'.leavesBelow

/-- `AttachLinked` restricted to the attachment nodes `𝒰 = attachNodes p`. The attached gardens are
the classes of the equivalence relation on `𝒰` generated by this (T Prop `canonequiv`, proof: the
irreducible components of the garden formed by the trees rooted at `𝒰`). Generating on all nodes
would merge distinct attached gardens through a common ancestor (stage-1 audit R1). -/
def AttachLinkedOn (p : ℕ) (u u' : GNode LG.garden.tree) : Prop :=
  u ∈ LG.attachNodes p ∧ u' ∈ LG.attachNodes p ∧ LG.AttachLinked u u'

/-- The order of the attached garden containing `u`: the total order of the subtrees rooted at the
attachment nodes `AttachLinkedOn`-equivalent to `u`. -/
noncomputable def attachedOrder (p : ℕ) (u : GNode LG.garden.tree) : ℕ := by
  classical
  exact ∑ u' ∈ (LG.attachNodes p).filter (fun u' => Relation.EqvGen (LG.AttachLinkedOn p) u u'),
    u'.orderBelow

/-- **Truncation** (T Def `defgtr`, L731–L732, without construction data; the flower version
`ℋ^tr`, T L2288, is the same predicate): every top tree has order `≤ Ntop` and every attached garden
has order `≤ Natt`. TARGET uses `Ntop = N_{p+1}`, `Natt = N_p`. -/
def IsTrunc (p Ntop Natt : ℕ) : Prop :=
  (∀ j, LG.topOrder p j ≤ Ntop) ∧ ∀ u ∈ LG.attachNodes p, LG.attachedOrder p u ≤ Natt

end LayeredGarden

end WaveTurbulence

```

### WaveB1-System.lean

```lean
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveBDraft.Core
public import WaveTurbulence.Frozen.Defs.CollisionOp
public import WaveTurbulence.Frozen.Defs.InitialCoeff

/-!
# Wave B, tier B1 — system objects (DRAFT for author approval)

Drafts of WAVE-B §2.3–§2.6 (TARGET = arXiv:2311.10082v2). Builds on `WaveB1-Core`. **Self-contained**
(freeze-set closure policy, fix list 3 item 3): imports only frozen Wave A definitions and Mathlib.
Where a landed Foundations object is the same (the `a`-system of `Foundations/NLS/AkSystem`, the
`cumulant` of `Foundations/Cumulant/Basic`, `Fourier.chi0`, `WKE.taylorU`, the Foundations norms), the
bridge lemma is in `WaveB1-Bridges.lean` (or listed as a provider obligation in DESIGN.md).

* §A The `a`-system nonlinearity `aNonlin`, the classed solution `IsASolution` (T L545–L564; WAVE-B
  §2.3.2, Q16, review C1), the cumulant `jointCumulant` (T Def `defcm`), `z^ζ`.
* §B Symmetric events (T L567–L569).
* §C Time domains, phase integrals, the one kernel `kernelK` and its instances `K_𝒢`, `K*_𝒬`, `K_𝒬`,
  `K*_𝒯` (T Def `defkg`, L669–L684; WAVE-B v2 §2.4.1). The flower instance `K̃_𝒢` is deferred with
  B1.12 to packet X1 (`WaveB1-Deferred.lean`).
* §D The shared truncated order-`N` sums `truncSum`, `truncSumC` (T (ansatz3)–(ansatz5), (expgarden);
  WAVE-B v2 §2.4.3, review G-3). The flower sum `truncSumHζ` is deferred (`WaveB1-Deferred.lean`).
* §E Duhamel tree terms `𝒥_𝒯, 𝒥_N, a^tr` (T (defjt)–(defbk) with F9) and `ℒ₀,…,ℒ₃` (T (eqnbk1.5)).
* §F Norms: `𝔖^{Λ₁,Λ₂}`, `𝔛^{θ,Λ₁,Λ₂}`, `𝔛^{θ,0,0}` with vector variables, restriction norms,
  `Z^Λ(ℬ)`, the space `Z` (T L579–L594, L787); all `ℝ≥0∞`-valued with `⊤` for inadmissible inputs.
* §G The cutoff `χ₀` (T L617–L623), one explicit formula.
* §H WKE Taylor terms `𝒰^{(p)}_n` (T (wketaylor2)).
* §I The ansatz predicate `AnsatzAt` (T Prop `propansatz` (1)–(4) at level `p`).
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

/-- The Japanese bracket `⟨k⟩ = (1 + |k|²)^{1/2}`. -/
noncomputable def jbr {d : ℕ} (k : Mom d) : ℝ := Real.sqrt (1 + ‖k‖ ^ 2)

/-- `z^ζ`: `z^+ = z`, `z^- = z̄` (T §2.4.3 notations). -/
noncomputable def zpowSign (ζ : ℤˣ) (z : ℂ) : ℂ := if ζ = 1 then z else (starRingEnd ℂ) z

/-- The coupling constant `δ / (2 L^{d-γ})`. -/
noncomputable def coupling (d : ℕ) (L γ δ : ℝ) : ℝ := δ / (2 * L ^ ((d : ℝ) - γ))

/-! ## §A The `a`-system, its classed solutions, and cumulants -/

/-- **The nonlinearity `𝒞_ζ(f,g,h)_k(t)`** of (akeqn2) (T L553–L564), `ζ = ±1`:
`δ/(2L^{d-γ}) · (iζ) ∑_{k₁-k₂+k₃=k} ε_{k₁k₂k₃} e^{ζπiδL^{2γ}Ω t} f_{k₁} g_{k₂} h_{k₃}` (`tsum` over the
resonant set; absolutely convergent in the solution class). Same body as the landed `NLS.aNonlin`
(bridge `aNonlin_eq_nls`). -/
noncomputable def aNonlin {d : ℕ} (L γ δ : ℝ) (ζ : ℤ) (t : ℝ) (f g h : (Fin d → ℤ) → ℂ)
    (n : Fin d → ℤ) : ℂ :=
  ((δ / (2 * L ^ ((d : ℝ) - γ)) : ℝ) : ℂ) * (Complex.I * ζ) *
    ∑' p : {p : (Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ) // p.1 - p.2.1 + p.2.2 = n},
      (epsCoef p.1.1 p.1.2.1 p.1.2.2 : ℂ) *
        Complex.exp (((ζ * Real.pi * δ * L ^ (2 * γ) *
          resFactor (latticePoint L p.1.1) (latticePoint L p.1.2.1) (latticePoint L p.1.2.2)
            (latticePoint L n) * t : ℝ) : ℂ) * Complex.I) * f p.1.1 * g p.1.2.1 * h p.1.2.2

/-- **Classed solutions of the `a`-system** (T (akeqn)–(akeqn2), L545–L564; WAVE-B §2.3.2 with Q16
and review C1): `a(0) = c`, the class `sup_{t ∈ [0,T]} sup_n ⟨n/L⟩^{d+1} |a_n(t)| < ∞` (in which the
sums of `𝒞₊` converge absolutely and uniqueness holds), and `∂ₜ a_n = 𝒞₊(a, ā, a)_n(t)` within
`[0, T]` at every `t ∈ [0, T]`. Same body as the landed `NLS.IsAkSolution` (bridge
`isASolution_iff_nls`). -/
def IsASolution {d : ℕ} (L γ δ T : ℝ) (c : (Fin d → ℤ) → ℂ) (a : ℝ → (Fin d → ℤ) → ℂ) : Prop :=
  a 0 = c ∧
    (∃ C, ∀ t ∈ Icc 0 T, ∀ n, (1 + ‖latticePoint L n‖ ^ 2) ^ (((d : ℝ) + 1) / 2) * ‖a t n‖ ≤ C) ∧
    ∀ t ∈ Icc 0 T, ∀ n, HasDerivWithinAt (fun s => a s n)
      (aNonlin L γ δ 1 t (a t) (fun m => (starRingEnd ℂ) (a t m)) (a t) n) (Icc 0 T) t

/-- **The joint cumulant** `𝕂((X_j)_{j ∈ s})` of T Def `defcm` (eqncm), expectations against a measure
`μ` (`μ = P.restrict F` for "assuming `F`"): the sum over all partitions `𝒫` of `s` of
`(-1)^{|𝒫|-1} (|𝒫|-1)! ∏_{A ∈ 𝒫} 𝔼 ∏_{j ∈ A} X_j`. Same body as the landed `cumulant` (CUMUL packet;
bridge `jointCumulant_eq_cumulant`). -/
noncomputable def jointCumulant {Ω ι : Type*} [MeasurableSpace Ω] [DecidableEq ι] (μ : Measure Ω)
    (X : ι → Ω → ℂ) (s : Finset ι) : ℂ :=
  ∑ P : Finpartition s, (-1 : ℂ) ^ (P.parts.card - 1) * ((P.parts.card - 1).factorial : ℂ) *
    ∏ A ∈ P.parts, ∫ ω, ∏ j ∈ A, X j ω ∂μ

/-! ## §B Symmetric events -/

/-- **Gauge and space-translation symmetric events** (T L567–L569): `F` is the set of `ω` whose
initial data `(û_in(k))_k = (√φin(k) g_k(ω))_k` lie in a measurable set `A` of coefficient arrays that
is invariant under `c ↦ e^{iθ} c` (gauge) and `c ↦ (e^{-2πi⟨k,x₀⟩} c_k)_k` (translation
`u ↦ u(· - x₀)`). (WAVE-B §2.3.4 uses the preimage under `g` instead of the initial data; TARGET
says "any event can be interpreted as a subset of initial data". See DESIGN Q5.) -/
def IsSymmetricEvent {d : ℕ} {Ω : Type*} (L : ℝ) (φin : Mom d → ℝ)
    (g : (Fin d → ℤ) → Ω → ℂ) (F : Set Ω) : Prop :=
  ∃ A : Set ((Fin d → ℤ) → ℂ), MeasurableSet A ∧ F = initialCoeff L φin g ⁻¹' A ∧
    (∀ θ : ℝ, ∀ c ∈ A, (fun n => Complex.exp ((θ : ℂ) * Complex.I) * c n) ∈ A) ∧
    ∀ x₀ : Mom d, ∀ c ∈ A, (fun n => Complex.exp
      (-(2 * Real.pi * inner ℝ (latticePoint L n) x₀ : ℝ) * Complex.I) * c n) ∈ A

/-! ## §C Time domains, phase integrals and the one kernel `kernelK` -/

section Kernels

variable {w : ℕ}

/-- `b'` is a (branching) child of the branching node `b`. -/
def GBranch.IsChildOf {w : ℕ} {tree : Fin w → TTree} (b' b : GBranch tree) : Prop :=
  b'.1.1 = b.1.1 ∧ ∃ i : Fin 3, b'.1.2 = b.1.2 ++ [i]

/-- `b` is the parent of the leaf `ℓ`. -/
def GBranch.IsParentOf {w : ℕ} {tree : Fin w → TTree} (b : GBranch tree) (ℓ : GLeaf tree) : Prop :=
  ℓ.1.1 = b.1.1 ∧ ∃ i : Fin 3, ℓ.1.2 = b.1.2 ++ [i]

@[instance_reducible, instance] def instDecidableIsParentOf {w : ℕ} {tree : Fin w → TTree}
    (b : GBranch tree) (ℓ : GLeaf tree) : Decidable (b.IsParentOf ℓ) := by
  unfold GBranch.IsParentOf
  infer_instance

/-- The parent `𝔣^pr` of a flower: its time is fixed (`δ(t_{𝔣^pr} - s)`, T (kqflower)). -/
def Garden.IsFlowerParent (G : Garden w) (b : GBranch G.tree) : Prop :=
  ∃ ℓ : GLeaf G.tree, G.IsFlower ℓ ∧ b.IsParentOf ℓ

/-- The parent `ℓ_lo^pr` of a lone leaf: its time is `> s` (T (timepairtree)). -/
def Garden.IsLoneParent (G : Garden w) (b : GBranch G.tree) : Prop :=
  ∃ ℓ : GLeaf G.tree, G.IsLone ℓ ∧ b.IsParentOf ℓ

@[instance_reducible, instance] def instDecidableIsFlowerParent (G : Garden w) (b : GBranch G.tree) :
    Decidable (G.IsFlowerParent b) := by
  unfold Garden.IsFlowerParent
  infer_instance

/-- The branching nodes whose time variable is integrated (all but the flower parents). -/
def Garden.FreeBranch (G : Garden w) : Type := {b : GBranch G.tree // ¬ G.IsFlowerParent b}

@[instance_reducible, instance] noncomputable def instFintypeFreeBranch (G : Garden w) :
    Fintype G.FreeBranch := by
  unfold Garden.FreeBranch
  infer_instance

/-- Times of all branching nodes from the free times, the flower parents getting the time `s`. -/
def Garden.extendTime (G : Garden w) (s : ℝ) (τ : G.FreeBranch → ℝ) : GBranch G.tree → ℝ :=
  fun b => if h : G.IsFlowerParent b then s else τ ⟨b, h⟩

variable (L γ δ : ℝ) {d : ℕ}

/-- The phase `∏_{𝔫 ∈ 𝒩} e^{πi ζ_𝔫 δ L^{2γ} Ω_𝔫 t_𝔫}` of a vector decoration `k` at times `τ`. -/
noncomputable def phaseProd (G : Garden w) (k : GNode G.tree → Mom d) (τ : GBranch G.tree → ℝ) :
    ℂ :=
  ∏ b : GBranch G.tree, Complex.exp ((Real.pi * ((G.sign b.toNode : ℤˣ) : ℤ) * δ *
    L ^ (2 * γ) * omegaNode G k b * τ b : ℝ) * Complex.I)

/-- The **phase integral** `∫_D ∏ e^{πi ζ_𝔫 δ L^{2γ} Ω_𝔫 t_𝔫} dt` over a time domain
`D ⊆ ℝ^{𝒩}`, integrating the free nodes and setting the flower parents to `s` (without flowers an
ordinary integral over `ℝ^{𝒩}`). -/
noncomputable def phaseIntegral (G : Garden w) (D : Set (GBranch G.tree → ℝ)) (s : ℝ)
    (k : GNode G.tree → Mom d) : ℂ :=
  ∫ τ : G.FreeBranch → ℝ, D.indicator (phaseProd L γ δ G k) (G.extendTime s τ)

/-- The **time domain** of the kernels: `𝔏_𝔫 < t_𝔫 < 𝔏_𝔫 + 1`, `0 < t_𝔫 < up(𝔫)`,
`t_{𝔫'} < t_𝔫` for `𝔫'` a branching child of `𝔫`, and `t_{ℓ_lo^pr} > s` at the parent of a lone
leaf. With `up ≡ t`: (timegarden) (T L674), read with `t_𝔫 < t` for every branching node (the literal
"whenever `𝔫'` is a child of `𝔫`" leaves nodes with only leaf children unconstrained; cf. (timetree)
for a tree of order 1); with `up = t` on `𝒯⁺` and `s` on `𝒯⁻`: (timecouple); with a lone leaf:
(timepairtree). -/
def kDomain (LG : LayeredGarden w) (up : GBranch LG.garden.tree → ℝ) (s : ℝ) :
    Set (GBranch LG.garden.tree → ℝ) :=
  {τ | ∀ b, (LG.layer b.toNode : ℝ) < τ b ∧ τ b < LG.layer b.toNode + 1 ∧ 0 < τ b ∧
    τ b < up b ∧ (∀ b' : GBranch LG.garden.tree, b'.IsChildOf b → τ b' < τ b) ∧
    (LG.garden.IsLoneParent b → s < τ b)}

/-- The leaves carrying an input factor: sign `+`, not marked (T (defkg0); L682; (kqflower)). -/
def inputLeaves (G : Garden w) : Finset (GLeaf G.tree) :=
  Finset.univ.filter fun ℓ => G.sign ℓ.toNode = 1 ∧ G.mark ℓ = none

/-- **The one kernel** (WAVE-B v2 §2.4.1; T Def `defkg`, (defkg0), (timecouple), (timepairtree),
(kqflower)): for a layered garden with marked leaves, inputs `F_q`, node upper times `up`, the time
`s` (flower parents fixed to `s`, lone-leaf parents `> s`), a base vector `k₀` (vectors
`k_𝔫 = k₀ + κ_𝔫/L`), root labels `n_j` and flower label `n'`:
`(δ/(2L^{d-γ}))^n ζ(𝒢) ∑_κ ε_κ ∫ ∏ e^{πiζ_𝔫 δL^{2γ}Ω_𝔫 t_𝔫} dt ∏^{(+, unmarked)}_ℓ F_{𝔏_ℓ}(k_ℓ)`.
The `tsum` converges absolutely when every tree has at most one lone-marked leaf (all TARGET
carriers) and the inputs have summable lattice values (`summable_kernelK_summand`, T.defkg.sum). On
gardens with two or more lone leaves in one tree (not TARGET objects) the decorations have a free
direction and the `tsum` is the junk value `0` (stage-2 audit R2, O7). -/
noncomputable def kernelK (F : ℕ → Mom d → ℝ) (LG : LayeredGarden w)
    (up : GBranch LG.garden.tree → ℝ) (s : ℝ) (k₀ : Mom d) (nroot : Fin w → (Fin d → ℤ))
    (nfl : Fin d → ℤ) : ℂ :=
  (coupling d L γ δ : ℂ) ^ LG.garden.order * LG.garden.zeta *
    ∑' κ : GenDecoration LG.garden d nroot nfl,
      (epsDec LG.garden κ.1 : ℂ) *
        phaseIntegral L γ δ LG.garden (kDomain LG up s) s (cosetDecoration LG.garden L k₀ κ.1) *
        ∏ ℓ ∈ inputLeaves LG.garden,
          (F (LG.layer ℓ.toNode) (cosetDecoration LG.garden L k₀ κ.1 ℓ.toNode) : ℂ)

/-- **`K_𝒢(t, n₁,…,n_w)`** (T (defkg0), L671–L674): lattice decorations with root labels `n_j`. -/
noncomputable def KG (F : ℕ → Mom d → ℝ) (LG : LayeredGarden w) (t : ℝ)
    (n : Fin w → (Fin d → ℤ)) : ℂ :=
  kernelK L γ δ F LG (fun _ => t) 0 0 n 0

/-- **`K*_𝒬(t, s, k)`** (T (timecouple), L678–L680) for a layered couple and `k ∈ ℝ^d`: coset
`k`-decorations, `𝒯⁺` times `< t`, `𝒯⁻` times `< s`. -/
noncomputable def KQstar (F : ℕ → Mom d → ℝ) (LG : LayeredGarden 2) (t s : ℝ) (k : Mom d) : ℂ :=
  kernelK L γ δ F LG (fun b => if b.1.1 = 0 then t else s) 0 k (fun _ => 0) 0

/-- `K_𝒬(t, k) := K*_𝒬(t, t, k)` (T L678). -/
noncomputable def KQ (F : ℕ → Mom d → ℝ) (LG : LayeredGarden 2) (t : ℝ) (k : Mom d) : ℂ :=
  KQstar L γ δ F LG t t k

/-- **`K*_𝒯(t, s, k)`** (T (timepairtree), L681–L684) for a layered paired tree (`IsPairedTree`):
coset `k`-decorations (`k_𝔯 = k_{ℓ_lo} = k`), all times `< t`, the parent of the lone leaf `> s`, the
input product over `+` leaves other than the lone leaf. -/
noncomputable def KTstar (F : ℕ → Mom d → ℝ) (LG : LayeredGarden 1) (t s : ℝ) (k : Mom d) : ℂ :=
  kernelK L γ δ F LG (fun _ => t) s k (fun _ => 0) 0

end Kernels

/-! ## §D The shared truncated order-`N` sums (WAVE-B v2 §2.4.3; review G-3) -/

/-- `𝒢_q ∪ 𝒞_q` as one predicate on layered gardens of any width: width `≥ 4`: `IsCanonG`; width
`2`: a couple of `𝒞_q` (probes `isCanonGC_iff_G`, `isCanonGC_iff_C`). -/
def IsCanonGC {w : ℕ} : ℕ → LayeredGarden w → Prop
  | 0, _ => False
  | p + 1, LG => LG.garden.IsPlain ∧
      ((4 ≤ w ∧ LG.garden.Irreducible) ∨ (w = 2 ∧ ∀ j, LG.garden.sig j = (-1) ^ (j : ℕ))) ∧
      LG.CanonCriterion p

/-- The input functions `F_q = φ(δq) + R_q` (T (ansatz3), L703). -/
noncomputable def inputsF (P : WTParams) (R : ℕ → Mom P.d → ℝ) : ℕ → Mom P.d → ℝ :=
  fun q k => P.φ (P.δ * q) k + R q k

/-- **`truncSum q N t ζ⃗ n⃗`** (T (expgarden), L762, at time `t`; T (ansatz3)–(ansatz5) at `t = p`;
WAVE-B v2 §2.4.3): the sum of `K_𝒢(t, n⃗)` over `𝒢 ∈ 𝒢^tr_q` (width `≥ 4`) or `𝒬 ∈ 𝒞^tr_q`
(width 2) of signature `ζ⃗` and order `N`, truncation `(N_q, N_{q-1})` (T Def `defgtr`). A finite sum
(`finite_layeredGardens`). Then `𝒦^tr_{p+1,N}(t) = truncSum (p+1) N t`, and for `N ≤ N_p` the sums of
(ansatz3)–(ansatz5) are `truncSum p N p` (the truncation is void: audit lemma `truncSum_untruncated`). -/
noncomputable def truncSum (P : WTParams) (F : ℕ → Mom P.d → ℝ) (q N : ℕ) {w : ℕ} (t : ℝ)
    (ζ : Fin w → ℤˣ) (n : Fin w → (Fin P.d → ℤ)) : ℂ :=
  ∑ᶠ (LG : LayeredGarden w) (_ : IsCanonGC q LG ∧ LG.IsTrunc (q - 1) (P.N q) (P.N (q - 1)) ∧
      LG.garden.sig = ζ ∧ LG.garden.order = N),
    KG P.L P.γ P.δ F LG t n

/-- **`truncSumC q N t k`**: the couple sum with real root vector `k` (T L678 with (expgarden), used
in (estcouple)): `∑ K_𝒬(t, k)` over `𝒬 ∈ 𝒞^tr_q` of order `N`. -/
noncomputable def truncSumC (P : WTParams) (F : ℕ → Mom P.d → ℝ) (q N : ℕ) (t : ℝ)
    (k : Mom P.d) : ℂ :=
  ∑ᶠ (LG : LayeredGarden 2) (_ : IsCanonC q LG ∧ LG.IsTrunc (q - 1) (P.N q) (P.N (q - 1)) ∧
      LG.garden.order = N),
    KQ P.L P.γ P.δ F LG t k

/-! ## §E Duhamel tree terms and the operators `ℒ_j` -/

section Duhamel

variable (L γ δ : ℝ) {d : ℕ}

/-- The forest consisting of one tree. -/
def single (T : TTree) : Fin 1 → TTree := fun _ => T

/-- Branch-consistent labels on a forest: `κ_𝔫 = κ_{𝔫₁} - κ_{𝔫₂} + κ_{𝔫₃}`. -/
def IsBranchConsistent {w : ℕ} {tree : Fin w → TTree} {V : Type*} [AddCommGroup V]
    (κ : GNode tree → V) : Prop :=
  ∀ b : GBranch tree, κ b.toNode = κ (b.child 0) - κ (b.child 1) + κ (b.child 2)

/-- The `n`-decorations of a tree (T Def `defdec`, first paragraph). -/
def TreeDecoration (T : TTree) (d : ℕ) (n : Fin d → ℤ) : Type :=
  {κ : GNode (single T) → (Fin d → ℤ) // IsBranchConsistent κ ∧ κ (GNode.root _ 0) = n}

/-- Node signs in a tree of sign `+`. -/
def treeSign (T : TTree) (a : GNode (single T)) : ℤˣ := nodeSign (fun _ => 1) a.1

/-- The duration domain (timetree) `{p < t_{𝔫'} < t_𝔫 < t}` (T L714), read with `p < t_𝔫 < t` for all
branching nodes. -/
def treeTimeDomain (T : TTree) (p t : ℝ) : Set (GBranch (single T) → ℝ) :=
  {τ | ∀ b, p < τ b ∧ τ b < t ∧ ∀ b' : GBranch (single T), b'.IsChildOf b → τ b' < τ b}

/-- **The tree term `(𝒥_𝒯)_n(t)`** (T (defjt), L710–L714, with F9: the leaf factor is
`a_{k_ℓ}(p)^{ζ_ℓ}`) for a tree of sign `+`, data `b = a(p)` and `t > p`. -/
noncomputable def treeTerm (p : ℕ) (T : TTree) (b : (Fin d → ℤ) → ℂ) (t : ℝ) (n : Fin d → ℤ) : ℂ :=
  (coupling d L γ δ : ℂ) ^ T.order *
    (∏ c : GBranch (single T), (Complex.I * (((treeSign T c.toNode : ℤˣ) : ℤ) : ℂ))) *
    ∑' κ : TreeDecoration T d n,
      (∏ c : GBranch (single T),
          (epsCoef (κ.1 (c.child 0)) (κ.1 (c.child 1)) (κ.1 (c.child 2)) : ℂ)) *
        (∫ τ : GBranch (single T) → ℝ, (treeTimeDomain T p t).indicator
          (fun τ => ∏ c : GBranch (single T), Complex.exp ((Real.pi *
            ((treeSign T c.toNode : ℤˣ) : ℤ) * δ * L ^ (2 * γ) *
            resFactor (latticePoint L (κ.1 (c.child 0))) (latticePoint L (κ.1 (c.child 1)))
              (latticePoint L (κ.1 (c.child 2))) (latticePoint L (κ.1 c.toNode)) *
            τ c : ℝ) * Complex.I)) τ) *
        ∏ ℓ : GLeaf (single T), zpowSign (treeSign T ℓ.toNode) (b (κ.1 ℓ.toNode))

/-- `𝒥_N = ∑_{n(𝒯) = N} 𝒥_𝒯` over trees of sign `+` (T (defjn)); a finite sum. -/
noncomputable def treeTermN (p N : ℕ) (b : (Fin d → ℤ) → ℂ) (t : ℝ) (n : Fin d → ℤ) : ℂ :=
  ∑ᶠ (T : TTree) (_ : T.order = N), treeTerm L γ δ p T b t n

/-- `a^tr = ∑_{N ≤ Ntr} 𝒥_N` (T (defbk); `Ntr = N_{p+1}`). -/
noncomputable def aTr (p Ntr : ℕ) (b : (Fin d → ℤ) → ℂ) (t : ℝ) (n : Fin d → ℤ) : ℂ :=
  ∑ N ∈ Finset.range (Ntr + 1), treeTermN L γ δ p N b t n

/-- An input slot of the trilinear form: `none` is the unknown `b`, `some N` is `𝒥_N`. -/
abbrev Slot (Ntr : ℕ) := Option (Fin (Ntr + 1))

/-- Number of `b`-slots and total order of the `𝒥`-slots. -/
def slotCountB {Ntr : ℕ} (x : Slot Ntr × Slot Ntr × Slot Ntr) : ℕ :=
  [x.1, x.2.1, x.2.2].count none

def slotOrder {Ntr : ℕ} (x : Slot Ntr × Slot Ntr × Slot Ntr) : ℕ :=
  ([x.1, x.2.1, x.2.2].map fun o => o.elim 0 (fun N => (N : ℕ))).sum

/-- **The operators `ℒ_j`** (T (eqnbk1.5), L717–L725; WAVE-B §2.5.2): `(ℒ_j b)_n(t) =
∑_{(j)} ∫_p^t 𝒞₊(u, v̄, w)_n(s) ds` over `(u,v,w) ∈ {b, 𝒥₀, …, 𝒥_{Ntr}}³` with exactly `j` entries
equal to `b`, and for `j = 0` the restriction `n₁ + n₂ + n₃ ≥ Ntr`; the conjugate in the middle slot
is explicit (F9). `b` is a function on `[p, p+1]`, extended to `ℝ` by `Set.IccExtend` (only its values
on `[p, t]` are used). -/
noncomputable def Lop (p Ntr : ℕ) (aP : (Fin d → ℤ) → ℂ) (j : ℕ)
    (b : Icc (p : ℝ) (p + 1) → (Fin d → ℤ) → ℂ) (t : ℝ) (n : Fin d → ℤ) : ℂ :=
  let val : Slot Ntr → ℝ → (Fin d → ℤ) → ℂ := fun o s => match o with
    | none => Set.IccExtend (by linarith : (p : ℝ) ≤ p + 1) b s
    | some N => treeTermN L γ δ p N aP s
  ∑ x ∈ (Finset.univ : Finset (Slot Ntr × Slot Ntr × Slot Ntr)).filter
      (fun x => slotCountB x = j ∧ (j = 0 → Ntr ≤ slotOrder x)),
    ∫ s in (p : ℝ)..t, aNonlin L γ δ 1 s (val x.1 s)
      (fun m => (starRingEnd ℂ) (val x.2.1 s m)) (val x.2.2 s) n

end Duhamel

/-! ## §F Norms (all `ℝ≥0∞`-valued; `⊤` for inadmissible inputs) -/

section Norms

variable {d : ℕ}

/-- The coordinate partial derivative `∂_{k^j} F` on `ℝ^d`. -/
noncomputable def partialMom (j : Fin d) (F : Mom d → ℂ) : Mom d → ℂ :=
  fun k => fderiv ℝ F k (EuclideanSpace.single j 1)

/-- `∂^ρ F` for a multi-index `ρ : Fin d → ℕ`. -/
noncomputable def iterPartial (ρ : Fin d → ℕ) (F : Mom d → ℂ) : Mom d → ℂ :=
  (List.finRange d).foldr (fun j G => (partialMom j)^[ρ j] G) F

open Classical in
/-- The weighted `C^{Λ₁}` sup quantity `max_{|ρ| ≤ Λ₁} sup_k ⟨k⟩^{Λ₂} |∂^ρ F(k)|`, `⊤` unless
`Λ₁ = 0` or `F` is `C^{Λ₁}`. For `Λ₁ = 0` it is `sup_k ⟨k⟩^{Λ₂} |F(k)|` with no regularity, as in the
source (normX2) and the landed `spatialNorm` (fix 5; as for `XNorm`, CL-13). Reading for `Λ₁ ≥ 1`
(stage-2 O5): classical derivatives; a function with bounded but discontinuous top-order partials has
a finite source norm but `⊤` here. All consumers have `Λ₁ ≥ 1` and supply `C^{Λ₁}` functions, and for
`Λ₁ ≠ 0` a finite value forces `C^{Λ₁}` (`contDiff_of_SNormR_lt_top`). -/
noncomputable def SNorm (Λ₁ Λ₂ : ℕ) (F : Mom d → ℂ) : ℝ≥0∞ :=
  if Λ₁ = 0 ∨ ContDiff ℝ Λ₁ F then
    ⨆ (ρ : Fin d → ℕ) (_ : ∑ j, ρ j ≤ Λ₁) (k : Mom d),
      ENNReal.ofReal (jbr k ^ Λ₂ * ‖iterPartial ρ F k‖)
  else ⊤

/-- **`‖F‖_{𝔖^{Λ₁,Λ₂}}`** of a real function on `ℝ^d` (T (normX2), L585). -/
noncomputable def SNormR (Λ₁ Λ₂ : ℕ) (F : Mom d → ℝ) : ℝ≥0∞ :=
  SNorm Λ₁ Λ₂ (fun k => (F k : ℂ))

/-- The time Fourier transform `F̂(λ, v) = ∫ F(t, v) e^{-2πi⟨λ,t⟩} dt` in `r` time variables. -/
noncomputable def timeFT {r : ℕ} {V : Type*} (F : (Fin r → ℝ) → V → ℂ) (lam : Fin r → ℝ) (v : V) :
    ℂ :=
  ∫ t : Fin r → ℝ, F t v * Complex.exp (-(2 * Real.pi * ∑ i, lam i * t i : ℝ) * Complex.I)

/-- `(max_i ⟨λ_i⟩)^θ` (T (normX)); `1` for `r = 0`. Correct for every `θ ∈ ℝ`: `max_i (⟨λ_i⟩^θ)`
would take the minimum bracket when `θ < 0` (stage-2 audit R3). Since `⟨λ⟩ ≥ 1`, the `⊔ 1` changes
nothing for `r ≥ 1`. -/
noncomputable def maxBracketPow {r : ℕ} (θ : ℝ) (lam : Fin r → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (((⨆ i, Real.sqrt (1 + lam i ^ 2)) ⊔ 1) ^ θ)

open Classical in
/-- **`‖F‖_{𝔛^{θ,Λ₁,Λ₂}}`** (T (normX), L581) for `F(t₁,…,t_r, k)`: `max_{|ρ| ≤ Λ₁} ∫ max_i⟨λ_i⟩^θ
‖⟨k⟩^{Λ₂} ∂_k^ρ F̂(λ, k)‖_{L^∞_k} dλ`; `⊤` unless every `t ↦ F(t,k)` is integrable and, for `Λ₁ ≥ 1`,
`k ↦ F̂(λ,k)` is `C^{Λ₁}` for almost every `λ` (F80). This is the guard of TARGET's norm and of the landed
`Fourier.MixedFourierAdmissible`. A per-frequency `⊤` inside the integral would make `∫⁻` a lower integral of a
possibly non-measurable integrand: the norm could be smaller than TARGET's and would have no triangle inequality.
With the a.e. guard the integrand is a.e. equal to a Borel function, so `∫⁻` is a genuine integral. For `Λ₁ = 0`
no momentum regularity is imposed (the source's `L^∞_k` needs none, and `k` often ranges over a lattice:
orchestrator ruling, fix list 3 item 2). Reading (stage-2 O1): the integrability
guard makes the unrestricted norm `⊤` for some functions with finite source norm (e.g. `sinc`);
the restricted norms over bounded `ℬ`, the only use, agree with TARGET's up to an absolute factor
(multiply by a cutoff equal to `1` on `ℬ`; Peetre). -/
noncomputable def XNorm {r : ℕ} (θ : ℝ) (Λ₁ Λ₂ : ℕ) (F : (Fin r → ℝ) → Mom d → ℂ) : ℝ≥0∞ :=
  if (∀ k, Integrable fun t => F t k) ∧ (Λ₁ = 0 ∨ ∀ᵐ lam, ContDiff ℝ Λ₁ (timeFT F lam)) then
    ⨆ (ρ : Fin d → ℕ) (_ : ∑ j, ρ j ≤ Λ₁), ∫⁻ lam : Fin r → ℝ, maxBracketPow θ lam *
      ⨆ k, ENNReal.ofReal (jbr k ^ Λ₂ * ‖iterPartial ρ (timeFT F lam) k‖)
  else ⊤

open Classical in
/-- **`‖F‖_{𝔛^{θ,0,0}}`** with an arbitrary type `V` of vector variables (T L589, last sentence):
`∫ max_i⟨λ_i⟩^θ sup_v |F̂(λ, v)| dλ`; `⊤` unless every `t ↦ F(t, v)` is integrable. -/
noncomputable def XNorm00 {r : ℕ} {V : Type*} (θ : ℝ) (F : (Fin r → ℝ) → V → ℂ) : ℝ≥0∞ :=
  if ∀ v, Integrable fun t => F t v then
    ∫⁻ lam : Fin r → ℝ, maxBracketPow θ lam * ⨆ v, ‖timeFT F lam v‖ₑ
  else ⊤

/-- **Restriction norms** (T (locnorm), L589): the infimum of the norms of all `G` agreeing with `F`
on `ℬ × K` (`⊤` if there is none). -/
noncomputable def XNormRestr {r : ℕ} (θ : ℝ) (Λ₁ Λ₂ : ℕ) (B : Set (Fin r → ℝ)) (K : Set (Mom d))
    (F : (Fin r → ℝ) → Mom d → ℂ) : ℝ≥0∞ :=
  ⨅ (G : (Fin r → ℝ) → Mom d → ℂ) (_ : ∀ t ∈ B, ∀ k ∈ K, G t k = F t k), XNorm θ Λ₁ Λ₂ G

noncomputable def XNorm00Restr {r : ℕ} {V : Type*} (θ : ℝ) (B : Set (Fin r → ℝ)) (K : Set V)
    (F : (Fin r → ℝ) → V → ℂ) : ℝ≥0∞ :=
  ⨅ (G : (Fin r → ℝ) → V → ℂ) (_ : ∀ t ∈ B, ∀ v ∈ K, G t v = F t v), XNorm00 θ G

/-- **`‖a‖_{Z^Λ(ℬ)}`** (T (defznorm), L594) of a lattice array depending on time. -/
noncomputable def ZNormOn (L : ℝ) (Λ : ℝ) (B : Set ℝ) (a : ℝ → (Fin d → ℤ) → ℂ) : ℝ≥0∞ :=
  ⨆ (t ∈ B) (n : Fin d → ℤ), ENNReal.ofReal (jbr (latticePoint L n) ^ Λ * ‖a t n‖)

/-- `‖b‖_Z` for `b` on `[p, p+1]`, `Z = Z^Λ([p,p+1])` (T L787). -/
noncomputable def ZNorm (L : ℝ) (Λ : ℝ) {p : ℕ} (b : Icc (p : ℝ) (p + 1) → (Fin d → ℤ) → ℂ) :
    ℝ≥0∞ :=
  ⨆ (t : Icc (p : ℝ) (p + 1)) (n : Fin d → ℤ), ENNReal.ofReal (jbr (latticePoint L n) ^ Λ * ‖b t n‖)

/-- **The space `Z`** (T L787; WAVE-B §2.5.3 with Q16): arrays on `[p, p+1]`, continuous in time for
each `n`, with finite `Z^Λ` norm. -/
def ZSpace (L : ℝ) (Λ : ℝ) (p : ℕ) : Set (Icc (p : ℝ) (p + 1) → (Fin d → ℤ) → ℂ) :=
  {b | (∀ n, Continuous fun t => b t n) ∧ ZNorm L Λ b < ⊤}

end Norms

/-! ## §G The cutoff `χ₀` -/

/-- **The cutoff `χ₀`** (T L617–L623), one explicit formula: `χ₀(x) = ψ(2 - 2|x|)` with `ψ` Mathlib's
`Real.smoothTransition` (built from `e^{-1/x}`): even, `C^∞`, `[0,1]`-valued, `= 1` on `[-1/2, 1/2]`,
`= 0` off `(-1, 1)`. -/
noncomputable def chi0 (x : ℝ) : ℝ := Real.smoothTransition (2 - 2 * |x|)

/-- `χ₀` on `ℝ^d`: `χ₀(x) = ∏_j χ₀(x^j)`. -/
noncomputable def chi0Vec {d : ℕ} (x : Mom d) : ℝ := ∏ j, chi0 (x j)

/-! ## §H WKE Taylor terms -/

/-- **`𝒰^{(p)}_n(t, k)`** (T (wketaylor2), L753–L755): `𝒰₀ = φ(pδ)` and
`𝒰_{n+1}(t) = δ ∑_{n₁+n₂+n₃ = n} ∫_p^t 𝒦(𝒰_{n₁}(t'), 𝒰_{n₂}(t'), 𝒰_{n₃}(t')) dt'`. -/
noncomputable def wkeTaylorTerm {d : ℕ} (φp : Mom d → ℝ) (δ : ℝ) (p : ℝ) :
    ℕ → ℝ → Mom d → ℝ
  | 0 => fun _ => φp
  | n + 1 => fun t k => δ * ∑ x ∈ (Finset.Nat.antidiagonalTuple 3 n).attach,
      ∫ t' in p..t, collisionOp
        (wkeTaylorTerm φp δ p (x.1 0) t')
        (wkeTaylorTerm φp δ p (x.1 1) t')
        (wkeTaylorTerm φp δ p (x.1 2) t') k
  decreasing_by
    all_goals
      have h := (Finset.Nat.mem_antidiagonalTuple.1 x.2)
      have h2 : ∀ i, x.1 i ≤ n := fun i => by
        have := Finset.single_le_sum (f := x.1) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
        rw [h] at this
        exact this
      exact Nat.lt_succ_of_le (h2 _)

/-! ## §I The ansatz predicate -/

/-- **The ansatz at level `p`** (T Prop `propansatz` (1)–(4); WAVE-B §2.6.7 and §4.1), for the
probability data `(Ω, μ, g)`, the solution `a`, events `Fev`, the two-point corrections `R, E` and
the cumulant remainders `Et`. Items:
1. `Fev p` is measurable and symmetric, `Fev p ⊆ Fev (p-1)`, `P(Fev p) ≥ 1 - e^{-N_p}`; on `Fev p`
   the classed solution exists on `[0, p]` with data `û_in` and is unique in the class; every
   `a_n(t)` (`t ∈ [0,p]`) is measurable (review C1) and every product of them is integrable on `Fev p`
   (WAVE-B §5);
2. `R p` is real with `‖R p‖_{𝔖^{Λ_p,Λ_p}} ≤ L^{-θ_p}` (hence `C^{Λ_p}`, the regularity TARGET
   tracks; no separate smoothness conjunct: `ContDiff ℝ ⊤` would be real-analyticity, stage-3 R1,
   stage-2 R4), `|E p n| ≤ ⟨n/L⟩^{-Λ_p} e^{-N_p}`,
   and `𝔼_p(a_n(p) ā_{n'}(p)) = 1_{n=n'} (φ(δp, n/L) + R_p(n/L) + E_p(n))`;
2'. (time parameter, F7/F27) for `p ≥ 1`, `t ∈ [p-1, p]`: `|𝔼_p|a_n(t)|² - φ(δt, n/L)| ≤ 2L^{-θ_p}`;
3. for `2 ≤ m ≤ R_p`, balanced `ζ⃗`, `n⃗`: `𝕂_p(a_{n_j}(p)^{ζ_j}) = ∑_{N ≤ N_p} truncSum p N p ζ⃗ n⃗
   + Ẽ_p` (= `∑_{𝒢 ∈ 𝒢_p, n(𝒢) ≤ N_p} K_𝒢(p, n⃗) + Ẽ_p`: truncation void for `N ≤ N_p`), with
   `Ẽ_p = 0` unless `∑ ζ_j n_j = 0`, `|Ẽ_p| ≤ (∏⟨n_j/L⟩)^{-Λ_p} e^{-N_p}`;
4. for the same data and `N ≤ N_p`: `|𝒦_{p,N}| = |truncSum p N p| ≤ (∏⟨n_j/L⟩)^{-Λ_p}
   L^{-(m-1)/6} δ^{νN}`. -/
def AnsatzAt (P : WTParams) {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (g : (Fin P.d → ℤ) → Ω → ℂ) (a : Ω → ℝ → (Fin P.d → ℤ) → ℂ) (Fev : ℕ → Set Ω)
    (R : ℕ → Mom P.d → ℝ) (E : ℕ → (Fin P.d → ℤ) → ℝ)
    (Et : ℕ → (m : ℕ) → (Fin (2 * m) → ℤˣ) → (Fin (2 * m) → (Fin P.d → ℤ)) → ℂ) (p : ℕ) :
    Prop :=
  -- (1) event and solution
  (MeasurableSet (Fev p) ∧ IsSymmetricEvent P.L P.φin g (Fev p) ∧
    (1 ≤ p → Fev p ⊆ Fev (p - 1)) ∧
    1 - Real.exp (-(P.N p : ℝ)) ≤ μ.real (Fev p) ∧
    (∀ ω ∈ Fev p, IsASolution P.L P.γ P.δ p (initialCoeff P.L P.φin g ω) (a ω) ∧
      ∀ b, IsASolution P.L P.γ P.δ p (initialCoeff P.L P.φin g ω) b →
        ∀ t ∈ Icc (0 : ℝ) p, b t = a ω t) ∧
    (∀ t ∈ Icc (0 : ℝ) p, ∀ n, Measurable fun ω => a ω t n) ∧
    ∀ (r : ℕ) (t : Fin r → Icc (0 : ℝ) p) (n : Fin r → (Fin P.d → ℤ)) (ζ : Fin r → ℤˣ),
      Integrable (fun ω => ∏ j, zpowSign (ζ j) (a ω (t j) (n j))) (μ.restrict (Fev p))) ∧
  -- (2) two-point function at time p
  (SNormR (P.Lambda p) (P.Lambda p) (R p) ≤
      ENNReal.ofReal (P.L ^ (-P.theta p)) ∧
    (∀ n, |E p n| ≤ jbr (latticePoint P.L n) ^ (-(P.Lambda p : ℝ)) * Real.exp (-(P.N p : ℝ))) ∧
    ∀ n n', ∫ ω in Fev p, a ω p n * (starRingEnd ℂ) (a ω p n') ∂μ =
      if n = n' then ((P.φ (P.δ * p) (latticePoint P.L n) + R p (latticePoint P.L n) + E p n : ℝ)
        : ℂ) else 0) ∧
  -- (2') two-point function at intermediate times
  (1 ≤ p → ∀ t ∈ Icc ((p : ℝ) - 1) p, ∀ n,
    |(∫ ω in Fev p, ‖a ω t n‖ ^ 2 ∂μ) - P.φ (P.δ * t) (latticePoint P.L n)| ≤
      2 * P.L ^ (-P.theta p)) ∧
  -- (3) higher cumulants
  (∀ m : ℕ, 2 ≤ m → m ≤ P.R p → ∀ ζ : Fin (2 * m) → ℤˣ, ∑ j, ((ζ j : ℤˣ) : ℤ) = 0 →
    ∀ n : Fin (2 * m) → (Fin P.d → ℤ),
      jointCumulant (μ.restrict (Fev p)) (fun j ω => zpowSign (ζ j) (a ω p (n j))) Finset.univ =
        (∑ N ∈ Finset.range (P.N p + 1), truncSum P (inputsF P R) p N (p : ℝ) ζ n) +
          Et p m ζ n ∧
      (∑ j, ((ζ j : ℤˣ) : ℤ) • n j ≠ 0 → Et p m ζ n = 0) ∧
      ‖Et p m ζ n‖ ≤ (∏ j, jbr (latticePoint P.L (n j))) ^ (-(P.Lambda p : ℝ)) *
        Real.exp (-(P.N p : ℝ))) ∧
  -- (4) order-N bound
  (∀ m : ℕ, 2 ≤ m → m ≤ P.R p → ∀ ζ : Fin (2 * m) → ℤˣ, ∑ j, ((ζ j : ℤˣ) : ℤ) = 0 →
    ∀ n : Fin (2 * m) → (Fin P.d → ℤ), ∀ N ≤ P.N p,
      ‖truncSum P (inputsF P R) p N (p : ℝ) ζ n‖ ≤
        (∏ j, jbr (latticePoint P.L (n j))) ^ (-(P.Lambda p : ℝ)) *
          P.L ^ (-((m : ℝ) - 1) / 6) * P.δ ^ (P.ν * N))

end WaveTurbulence

```

### WaveB1-Statements.lean

```lean
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveBDraft.System
public import WaveTurbulence.Frozen.Defs.IsSmoothNLSSolution
public import WaveTurbulence.Frozen.Defs.TorusFourierCoeff
public import WaveTurbulence.Frozen.Defs.KineticTime
public import WaveTurbulence.Frozen.Defs.StdComplexGaussian

/-!
# Wave B, tier B1 — statements (DRAFT for author approval)

The tier-B1 anchors of WAVE-B v2 §4 (B1.1–B1.5, B1.7–B1.11; B1.6 `sumint` is in
`WaveB1-Sumint.lean`). Every statement ends in `:= by sorry` (drafts). Each docstring names its
source lines and lists its deviations; DESIGN.md §6 records the disagreements with WAVE-B.

**Freeze set (after the stage-3 audit):** B1.1–B1.11. **B1.12 `layergardenFlower` is deferred**
(stage-3 R8: not sufficient for `fixedpoint`'s proof; it waits for packet X1, which fixes the cutoffs
and the designated fixed-time nodes); it and its definitions (`WTPrefixP`, `KGflower`,
`topCountBelow`, `FlowerRestr`, `truncSumHζ`) are kept as drafts in `WaveB1-Deferred.lean`, outside
the freeze set (fix list 3 item 4, delta-1 D1). The optional `cumulantExpansion` is dropped from the
freeze set (stage-3 R9); it remains the unfrozen target T.cmattr (DESIGN records the corrected order
range). Self-contained: imports only frozen Wave A definitions, Mathlib and the B1 drafts.

Auxiliary definitions introduced here: `IsGaussianData` (the Wave A probability hypotheses),
`LayeredGarden.CanonInd`, `TopDecompWith`, `TopDecomp` (the inductive construction of T Def
`defcanon` as a decomposition predicate, for B1.11).
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Finset Set
open scoped ENNReal

universe u

namespace WaveTurbulence

/-- The probability data of Wave A (`main`): `g_n` measurable, independent, each of law
`stdComplexGaussian`. -/
def IsGaussianData {d : ℕ} {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (g : (Fin d → ℤ) → Ω → ℂ) : Prop :=
  (∀ n, Measurable (g n)) ∧ iIndepFun g μ ∧ ∀ n, μ.map (g n) = stdComplexGaussian

/-- A balanced signature of width `2m`: exactly `m` plus signs. -/
def IsBalancedSig {w : ℕ} (ζ : Fin w → ℤˣ) : Prop := ∑ j, ((ζ j : ℤˣ) : ℤ) = 0

/-- `∏_j ⟨n_j/L⟩`. -/
noncomputable def jbrProd {w d : ℕ} (L : ℝ) (n : Fin w → (Fin d → ℤ)) : ℝ :=
  ∏ j, jbr (latticePoint L (n j))

/-! ## B1.1 `propansatz` -/

/-- **B1.1 `propansatz`** (T Prop `propansatz`, L689–L707; + time parameter F7/F27; + L951).
Under (Π), for all probability data of Wave A there are a solution `a`, events `Fev`, two-point
corrections `R, E` and cumulant remainders `Ẽ` such that `AnsatzAt p` holds for every `0 ≤ p ≤ 𝔇`.
Deviations (WAVE-B v2 §4.1): (D1) `R p` is a real `C^{Λ_p}` function on `ℝ^d` with the `ℝ^d` 𝔖-norm
(regularity from the norm bound for `Λ_p ≠ 0`, `contDiff_of_SNormR_lt_top`; stage-3 R1, option B);
(D2) the cumulant of (ansatz1) is written as the moment; (D3) item (2') (intermediate times) is
new, constant `2`; (D4) uniqueness in the classed solution notion (Q16, C1); (D5) measurability
(`Measurable`, C1) and integrability conjuncts added; (D6) the sums of (3)–(4) are the shared
`truncSum` (equal to the source's untruncated sums: `truncSum_untruncated`); (D7, DESIGN Q5)
symmetric events are preimages of invariant sets of initial data.
Beyond the frozen anchors, `main` needs three unfrozen glue lemmas (stage-3 O8): mass conservation for
smooth NLS solutions (T L819), the almost-sure rapid decay of `initialCoeff` (PROB.smoothData), and the
Gaussian moments of the mass `∑ φin(n/L)|g_n|²`. -/
theorem propansatz : WTPrefix fun P =>
    ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (g : (Fin P.d → ℤ) → Ω → ℂ), IsGaussianData μ g →
    ∃ (a : Ω → ℝ → (Fin P.d → ℤ) → ℂ) (Fev : ℕ → Set Ω) (R : ℕ → Mom P.d → ℝ)
      (E : ℕ → (Fin P.d → ℤ) → ℝ)
      (Et : ℕ → (m : ℕ) → (Fin (2 * m) → ℤˣ) → (Fin (2 * m) → (Fin P.d → ℤ)) → ℂ),
      ∀ p ≤ P.D, AnsatzAt P μ g a Fev R E Et p := by
  sorry

/-! ## B1.2 `layergarden` -/

/-- The remainder hypothesis of `layergarden`: for `q ≤ p`, `R q` is real with
`‖R q‖_{𝔖^{Λ_q,Λ_q}} ≤ L^{-θ_q}` (T (ansatz2), as used at L949–L951). The bound forces `R q ∈ C^{Λ_q}`
(`contDiff_of_SNormR_lt_top`, as `Λ_q = (40d)^{𝔇+1-q} ≥ 1`), which is all TARGET tracks; there is no
smoothness conjunct (`ContDiff ℝ ⊤` is real-analyticity in this Mathlib; stage-3 R1, option B). -/
def RemainderBound (P : WTParams) (R : ℕ → Mom P.d → ℝ) (p : ℕ) : Prop :=
  ∀ q ≤ p, SNormR (P.Lambda q) (P.Lambda q) (R q) ≤ ENNReal.ofReal (P.L ^ (-P.theta q))

/-- The couple remainder of (estcouple): `k ↦ 𝒦^tr_{p+1,N}(t; k) - [N even] 𝒰^{(p)}_{N/2}(t, k)`. -/
noncomputable def coupleRemainder (P : WTParams) (R : ℕ → Mom P.d → ℝ) (p N : ℕ) (t : ℝ) :
    Mom P.d → ℂ := fun k =>
  truncSumC P (inputsF P R) (p + 1) N t k -
    (if Even N then (wkeTaylorTerm (P.φ (P.δ * p)) P.δ p (N / 2) t k : ℂ) else 0)

/-- **B1.2 `layergarden`** (T Prop `layergarden`, L761–L779; deterministic, F36; time parameter
F27). For `0 ≤ p < 𝔇`, remainders with (ansatz2) bounds, inputs `F_q = φ(δq) + R_q`, every
`t ∈ (p, p+1]` and `N ≤ N_{p+1}^4`: (1) for `2 ≤ m ≤ 10 R_{p+1}` the truncated garden sum is
`≤ (∏⟨n_j⟩)^{-4Λ_{p+1}} L^{-(m-1)/4} δ^{2νN}`; (2)(a) the lattice couple sum vanishes off the diagonal;
(2)(b) `k ↦ 𝒦^tr_{p+1,N}(t;k) - [N even] 𝒰^{(p)}_{N/2}(t,k)` has
`𝔖^{4Λ_{p+1},4Λ_{p+1}}` norm `≤ L^{-(4θ_{p+1}+θ_p)/5} δ^{2νN}` (so it is `C^{4Λ_{p+1}}`; TARGET L776
claims no more: a smoothness conjunct was false, stage-3 R2).
Deviations (WAVE-B v2 §4.2): (D1) the induction hypothesis is replaced by `RemainderBound`;
(D2) `t ∈ (p, p+1]`; (D3) (estcouple)+(estcouple2) merged; (D4) shared sums; (D5) general carriers.
Note T L762: for `N ≤ N_{p+1}^4` the attached-garden truncation is void. -/
theorem layergarden : WTPrefix fun P =>
    ∀ p : ℕ, p < P.D → ∀ R : ℕ → Mom P.d → ℝ, RemainderBound P R p →
    ∀ t ∈ Ioc (p : ℝ) (p + 1), ∀ N ≤ P.N (p + 1) ^ 4,
      (∀ m : ℕ, 2 ≤ m → m ≤ 10 * P.R (p + 1) → ∀ ζ : Fin (2 * m) → ℤˣ, IsBalancedSig ζ →
        ∀ n : Fin (2 * m) → (Fin P.d → ℤ),
          ‖truncSum P (inputsF P R) (p + 1) N t ζ n‖ ≤
            jbrProd P.L n ^ (-(4 * P.Lambda (p + 1) : ℝ)) * P.L ^ (-((m : ℝ) - 1) / 4) *
              P.δ ^ (2 * P.ν * N)) ∧
      (∀ n : Fin 2 → (Fin P.d → ℤ), n 0 ≠ n 1 →
        truncSum P (inputsF P R) (p + 1) N t ![1, -1] n = 0) ∧
      SNorm (4 * P.Lambda (p + 1)) (4 * P.Lambda (p + 1)) (coupleRemainder P R p N t) ≤
        ENNReal.ofReal (P.L ^ (-(4 * P.theta (p + 1) + P.theta p) / 5) * P.δ ^ (2 * P.ν * N)) := by
  sorry

/-! ## B1.3 `fixedpoint` -/

/-- **B1.3 `fixedpoint`** (T Prop `fixedpoint`, L780–L794). For probability data, `0 ≤ p < 𝔇` and
ansatz data with `AnsatzAt q` for all `q ≤ p`, with `𝒥_N, a^tr, ℒ_j` built from `a(p)` and
`Z = Z^{(5/4)Λ_{p+1}}([p,p+1])`, there is a measurable symmetric `F' ⊆ F_p` with
`P(F_p ∖ F') ≤ e^{-4N_{p+1}}` on which: (1) `|a^tr_n(t)| ≤ ⟨n⟩^{-(3/2)Λ_{p+1}} e^{3N_{p+1}}`;
(2) `|(ℒ₀)_n(t)| ≤ ⟨n⟩^{-(3/2)Λ_{p+1}} e^{-20N_{p+1}}`; (3) `1 - ℒ₁` maps `Z` into `Z`, is a bijection
of `Z`, and `‖b‖_Z ≤ e^{3N_{p+1}} ‖(1-ℒ₁)b‖_Z`; (4) for `b, b'` in the ball `B` of radius
`e^{-10N_{p+1}}`, the solution `Φ(b) ∈ Z` of `(1-ℒ₁)Φ(b) = ℒ₀ + ℒ₂(b,b) + ℒ₃(b,b,b)` lies in `B`, and
`‖Φ(b) - Φ(b')‖_Z ≤ ½‖b - b'‖_Z`. Deviations (WAVE-B v2 §4.3): (D1) contraction constant `½`;
(D2) continuity in `Z`; (D3) F9 conjugations; (D4) `(1-ℒ₁)^{-1}` expressed through unique
solvability. -/
theorem fixedpoint : WTPrefix fun P =>
    ∀ (Ω : Type u) [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      (g : (Fin P.d → ℤ) → Ω → ℂ), IsGaussianData μ g →
    ∀ p : ℕ, p < P.D →
    ∀ (a : Ω → ℝ → (Fin P.d → ℤ) → ℂ) (Fev : ℕ → Set Ω) (R : ℕ → Mom P.d → ℝ)
      (E : ℕ → (Fin P.d → ℤ) → ℝ)
      (Et : ℕ → (m : ℕ) → (Fin (2 * m) → ℤˣ) → (Fin (2 * m) → (Fin P.d → ℤ)) → ℂ),
      (∀ q ≤ p, AnsatzAt P μ g a Fev R E Et q) →
    ∃ F' : Set Ω, F' ⊆ Fev p ∧ MeasurableSet F' ∧ IsSymmetricEvent P.L P.φin g F' ∧
      μ.real (Fev p \ F') ≤ Real.exp (-(4 * P.N (p + 1) : ℝ)) ∧
      ∀ ω ∈ F',
        let Ntr := P.N (p + 1)
        let Λ : ℝ := 5 / 4 * P.Lambda (p + 1)
        let ℒ : ℕ → (Icc (p : ℝ) (p + 1) → (Fin P.d → ℤ) → ℂ) →
            Icc (p : ℝ) (p + 1) → (Fin P.d → ℤ) → ℂ :=
          fun j b t n => Lop P.L P.γ P.δ p Ntr (a ω p) j b t n
        let Zs := ZSpace (d := P.d) P.L Λ p
        (∀ t ∈ Icc (p : ℝ) (p + 1), ∀ n,
          ‖aTr P.L P.γ P.δ p Ntr (a ω p) t n‖ ≤
            jbr (latticePoint P.L n) ^ (-(3 / 2 * P.Lambda (p + 1) : ℝ)) *
              Real.exp (3 * Ntr)) ∧
        (∀ (b : Icc (p : ℝ) (p + 1) → (Fin P.d → ℤ) → ℂ) (t : Icc (p : ℝ) (p + 1)) (n),
          ‖ℒ 0 b t n‖ ≤ jbr (latticePoint P.L n) ^ (-(3 / 2 * P.Lambda (p + 1) : ℝ)) *
            Real.exp (-(20 * Ntr : ℝ))) ∧
        (∀ b ∈ Zs, b - ℒ 1 b ∈ Zs) ∧
        (∀ c ∈ Zs, ∃! b, b ∈ Zs ∧ b - ℒ 1 b = c) ∧
        (∀ b ∈ Zs, ZNorm P.L Λ b ≤ ENNReal.ofReal (Real.exp (3 * Ntr)) * ZNorm P.L Λ (b - ℒ 1 b)) ∧
        (∀ b ∈ Zs, ZNorm P.L Λ b ≤ ENNReal.ofReal (Real.exp (-(10 * Ntr : ℝ))) →
          ∃ c ∈ Zs, c - ℒ 1 c = ℒ 0 b + ℒ 2 b + ℒ 3 b ∧
            ZNorm P.L Λ c ≤ ENNReal.ofReal (Real.exp (-(10 * Ntr : ℝ)))) ∧
        (∀ b ∈ Zs, ∀ b' ∈ Zs, ∀ c ∈ Zs, ∀ c' ∈ Zs,
          ZNorm P.L Λ b ≤ ENNReal.ofReal (Real.exp (-(10 * Ntr : ℝ))) →
          ZNorm P.L Λ b' ≤ ENNReal.ofReal (Real.exp (-(10 * Ntr : ℝ))) →
          c - ℒ 1 c = ℒ 0 b + ℒ 2 b + ℒ 3 b → c' - ℒ 1 c' = ℒ 0 b' + ℒ 2 b' + ℒ 3 b' →
          ZNorm P.L Λ (c - c') ≤ 2⁻¹ * ZNorm P.L Λ (b - b')) := by
  sorry

/-! ## B1.4 `nlsAkBridge` -/

/-- **B1.4 `nlsAkBridge`** (T L540–L566, L817–L819; F8). For `L > 0`, `α = L^{-γ}`, `δ > 0`,
`T = 𝔇 δ T_kin(α)`: (1) a smooth NLS solution with data `c` gives, through (reducedcoef), a classed
solution of the `a`-system on `[0, 𝔇]` with `|a_n(t)| = |û(δT_kin t, n)|`, in every `Z^Λ([0,𝔇])`;
(2) conversely, a classed `a`-system solution with rapidly decreasing data gives a smooth NLS
solution with `|û(t, n)| = |a_n(t/(δT_kin))|`; (3) smooth solutions are unique; (4) the solvable
event is measurable and so are the truncated observables at times `t ∈ [0, T]` (a smooth solution is
constrained only on `[0, T]`; for all `t ∈ ℝ` the item was false, stage-3 R3). Deviations (WAVE-B v2
§4.4): (D1) item 4 is the precise form of F8's measurability; (D2) rapidly decreasing data in item 2.
(D3, delta-stage-3 N1) `1 ≤ 𝔇`: at `𝔇 = 0` the `a`-system on `[0,0]` is void (a derivative within a
singleton is arbitrary) while a smooth solution on `[0,0]` must be stationary, so item (2) is false
there; every consumer has `1 ≤ 𝔇` from the prefix. The classed `a`-system solution is
`IsASolution`. The phase
conventions (`e^{-πiδL^{2γ}|k|²t}`, `e^{-2iαMδT_kin t}`) follow (reducedcoef) with the normalized
Laplacian of Wave A; to be checked by the NLS packet. -/
theorem nlsAkBridge {d : ℕ} (hd : 1 ≤ d) (L γ δ : ℝ) (hL : 0 < L) (hδ : 0 < δ) (D : ℕ)
    (hD : 1 ≤ D) (α T : ℝ) (hα : α = L ^ (-γ)) (hT : T = D * δ * kineticTime α) :
    -- (1) forward
    (∀ (c : (Fin d → ℤ) → ℂ) (u : ℝ → (Fin d → ℝ) → ℂ), IsSmoothNLSSolution L α T c u →
      let M : ℝ := (L ^ d)⁻¹ * ∑' n, ‖c n‖ ^ 2
      let a : ℝ → (Fin d → ℤ) → ℂ := fun t n =>
        Complex.exp (-(Real.pi * δ * L ^ (2 * γ) * ‖latticePoint L n‖ ^ 2 * t : ℝ) *
          Complex.I) *
        Complex.exp (-(2 * α * M * δ * kineticTime α * t : ℝ) * Complex.I) *
        torusFourierCoeff L (u (δ * kineticTime α * t)) n
      IsASolution L γ δ D c a ∧ (∀ Λ : ℝ, ZNormOn L Λ (Icc 0 D) a < ⊤) ∧
        ∀ t ∈ Icc (0 : ℝ) D, ∀ n,
          ‖a t n‖ = ‖torusFourierCoeff L (u (δ * kineticTime α * t)) n‖) ∧
    -- (2) backward
    (∀ (c : (Fin d → ℤ) → ℂ) (a : ℝ → (Fin d → ℤ) → ℂ),
      (∀ s : ℝ, ∃ C, ∀ n, jbr (latticePoint L n) ^ s * ‖c n‖ ≤ C) →
      IsASolution L γ δ D c a →
      ∃ u : ℝ → (Fin d → ℝ) → ℂ, IsSmoothNLSSolution L α T c u ∧
        ∀ t ∈ Icc 0 T, ∀ n, ‖torusFourierCoeff L (u t) n‖ = ‖a (t / (δ * kineticTime α)) n‖) ∧
    -- (3) uniqueness
    (∀ (c : (Fin d → ℤ) → ℂ) (u u' : ℝ → (Fin d → ℝ) → ℂ),
      IsSmoothNLSSolution L α T c u → IsSmoothNLSSolution L α T c u' → ∀ t ∈ Icc 0 T, u t = u' t) ∧
    -- (4) measurability
    (∀ (Ω : Type u) [MeasurableSpace Ω] (c : Ω → (Fin d → ℤ) → ℂ), Measurable c →
      MeasurableSet {ω | ∃ v, IsSmoothNLSSolution L α T (c ω) v} ∧
      ∀ U : Ω → ℝ → (Fin d → ℝ) → ℂ,
        (∀ ω, (∃ v, IsSmoothNLSSolution L α T (c ω) v) → IsSmoothNLSSolution L α T (c ω) (U ω)) →
        ∀ t ∈ Icc 0 T, ∀ n, Measurable fun ω =>
          {ω | ∃ v, IsSmoothNLSSolution L α T (c ω) v}.indicator
            (fun ω => ‖torusFourierCoeff L (U ω t) n‖ ^ 2) ω) := by
  sorry

/-! ## B1.5 `wkeTaylor` -/

/-- **B1.5 `wkeTaylor`** (T (wketaylor)–(taylorbound), L752–L758; F10). Under (Π) (statement
independent of `L`), for `0 ≤ p < 𝔇`: (0) the `t'`-integrands of (wketaylor2) are interval integrable
(no junk integrals, WAVE-B §5); (1) for `t ∈ [p,p+1]`, `k ∈ ℝ^d`: `∑_N |𝒰_N(t,k)| < ∞` and
`∑_N 𝒰_N(t,k) = φ(δt, k)`; (2) `‖𝒰_N(t)‖_{𝔖^{4Λ_{p+1},4Λ_{p+1}}} ≤ C₂ (C₁δ)^N`. Constants: `C₁` must
not depend on `𝔇` (it is chosen before `δ, 𝔇` in (Π)); `C₂` may. Deviations: item (1) for all `t`
(time parameter); item (0) added. -/
theorem wkeTaylor : WTPrefix fun P =>
    ∀ p : ℕ, p < P.D →
      let U := wkeTaylorTerm (P.φ (P.δ * p)) P.δ p
      (∀ N, ∀ t ∈ Icc (p : ℝ) (p + 1), ∀ k, ∀ x ∈ Finset.Nat.antidiagonalTuple 3 N,
        IntervalIntegrable (fun t' => collisionOp (U (x 0) t') (U (x 1) t') (U (x 2) t') k)
          volume p t) ∧
      (∀ t ∈ Icc (p : ℝ) (p + 1), ∀ k, Summable (fun N => |U N t k|) ∧
        ∑' N, U N t k = P.φ (P.δ * t) k) ∧
      ∀ N, ∀ t ∈ Icc (p : ℝ) (p + 1),
        SNormR (4 * P.Lambda (p + 1)) (4 * P.Lambda (p + 1)) (U N t) ≤
          ENNReal.ofReal (P.C₂ * (P.C₁ * P.δ) ^ N) := by
  sorry

/-! ## B1.7 `countLemma`, B1.8 `atomCountLemma` -/

/-- The lattice vectors `x = n/L` within distance `1` of a centre `a`. -/
def NearLattice {d : ℕ} (L : ℝ) (a : Mom d) (n : Fin d → ℤ) : Prop := ‖latticePoint L n - a‖ ≤ 1

/-- **B1.7 `countLemma`** (T Lemma `countlem`, L2459–L2466; DH23 Lemma A.2 (1), (3); F3 revised,
G-5). For `x, y, z ∈ ℤ_L^d` in unit balls, `|r| ∼ P` (constant `c₀`), `ξ ∈ {x, y, x+y}`,
`ζ ∈ {x-v, x+y-v, x+y-v-z}`, `𝔛 = min((log L)², 1 + δL^{2γ}P)`: (1) the pairs with
`|⟨x,y⟩-α|, |⟨r,ξ⟩-β| ≤ δ^{-1}L^{-2γ}` number `≤ C δ^{-1} L^{2(d-γ)} 𝔛^{-1}`; (2) the triples with
`|⟨x,y⟩-α|, |⟨ζ,z⟩-β| ≤ δ^{-1}L^{-2γ}` number `≤ C δ^{-2} L^{3(d-γ)-γ₀}`. The counted sets are finite
(stated, against junk `ncard`). Constants `C(d,γ,η,c₀)` uniform in `δ`, `η ≤ η₀(d,γ)`, and
`L ≥ L₀(δ)`: DH23's bound (countc1-1) needs `δ^{-1}L^{-10η} ≤ (log L)^{-2}` (stage-3 R5; consumers fix
`δ` before `L`). The binder `η ∈ (0, η₀]` does not occur in the bound; it is kept so that `C` may
depend on `η` as in the source (delta-stage-3 O1). Deviations: `|r| ∼₀ P` made explicit with `c₀`; for `P = 1` also `|r| ≤ c₀` (DH23's
dyadic setting; in every use `r` is a difference of vectors in unit balls; stage-3 O2). -/
theorem countLemma :
    ∀ d : ℕ, 3 ≤ d → ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 → ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η ∈ Ioc 0 η₀,
    ∀ c₀ : ℝ, 1 ≤ c₀ → ∃ C : ℝ, ∀ δ ∈ Ioc (0 : ℝ) 1, ∃ L₀ : ℝ, ∀ L ≥ L₀, ∀ α β : ℝ,
    ∀ (nr nv : Fin d → ℤ) (Pr : ℝ), (Pr = 0 ∨ Pr ∈ Icc L⁻¹ 1) →
      (Pr = 0 → nr = 0) →
      (0 < Pr → Pr < 1 → c₀⁻¹ * Pr ≤ ‖latticePoint L nr‖ ∧ ‖latticePoint L nr‖ ≤ c₀ * Pr) →
      (Pr = 1 → c₀⁻¹ ≤ ‖latticePoint L nr‖ ∧ ‖latticePoint L nr‖ ≤ c₀) →
    ∀ ax ay az : Mom d, ∀ ξsel : Fin 3, ∀ ζsel : Fin 3,
      let r := latticePoint L nr
      let v := latticePoint L nv
      let 𝔛 := min (Real.log L ^ 2) (1 + δ * L ^ (2 * γ) * Pr)
      let tol := δ⁻¹ * L ^ (-2 * γ)
      let S₁ : Set ((Fin d → ℤ) × (Fin d → ℤ)) := {q | NearLattice L ax q.1 ∧ NearLattice L ay q.2 ∧
        |inner ℝ (latticePoint L q.1) (latticePoint L q.2) - α| ≤ tol ∧
        |inner ℝ r (![latticePoint L q.1, latticePoint L q.2,
            latticePoint L q.1 + latticePoint L q.2] ξsel) - β| ≤ tol}
      let S₂ : Set ((Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ)) := {q | NearLattice L ax q.1 ∧
        NearLattice L ay q.2.1 ∧ NearLattice L az q.2.2 ∧
        |inner ℝ (latticePoint L q.1) (latticePoint L q.2.1) - α| ≤ tol ∧
        |inner ℝ (![latticePoint L q.1 - v, latticePoint L q.1 + latticePoint L q.2.1 - v,
            latticePoint L q.1 + latticePoint L q.2.1 - v - latticePoint L q.2.2] ζsel)
          (latticePoint L q.2.2) - β| ≤ tol}
      (S₁.Finite ∧ (S₁.ncard : ℝ) ≤ C * δ⁻¹ * L ^ (2 * ((d : ℝ) - γ)) * 𝔛⁻¹) ∧
      (S₂.Finite ∧ (S₂.ncard : ℝ) ≤
        C * δ⁻¹ ^ 2 * L ^ (3 * ((d : ℝ) - γ) - min γ (1 - γ))) := by
  sorry

/-- **B1.8 `atomCountLemma`** (T Lemma `atomcountlem`, L2467–L2478; DH23 Lemma A.3 (1), (2)).
For `k_j ∈ ℤ_L^d` in unit balls: (1) for `ε ∈ {(+,+), (+,-)}` the solutions of `ε₁k₁ + ε₂k₂ = k`,
`|ε₁|k₁|² + ε₂|k₂|² - β| ≤ δ^{-1}L^{-2γ}` number `≤ C δ^{-1} min(L^d, L^{d+1-2γ})`, for `ε = (+,-)` only
when `k ≠ 0` (DH23 A.3(1) assumes `|k₁ - k₂| ∼ R ≥ L^{-1}`; at `k = 0`, `γ > 1/2` the bound is false,
and so is TARGET's literal (atomcountbd), T L2472: stage-3 R4, new finding); (2) for `ε = (+,-)` and
`|k| ≥ L^{-γ+η}` (reading Q8b of "`|r| ≥ L^{-γ+η}`") they number `≤ C δ^{-1} L^{d-γ-η}`; (3) the solutions
of `k₁ - k₂ + k₃ = k`, `||k₁|² - |k₂|² + |k₃|² - β| ≤ δ^{-1}L^{-2γ}` number `≤ C δ^{-1} L^{2(d-γ)}`.
(atomcountbd3) is omitted (unused in T L1293–L2339). Deviations: Q8b reading; signs `(+,-,+)` for
`r = 3`. The counted sets are finite (stated). -/
theorem atomCountLemma :
    ∀ d : ℕ, 3 ≤ d → ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 → ∀ η : ℝ, 0 < η → η ≤ min γ (1 - γ) / 2 →
    ∃ C L₀ : ℝ, ∀ L ≥ L₀, ∀ δ ∈ Ioc (0 : ℝ) 1, ∀ β : ℝ, ∀ nk : Fin d → ℤ, ∀ a₁ a₂ a₃ : Mom d,
      let k := latticePoint L nk
      let tol := δ⁻¹ * L ^ (-2 * γ)
      let S₂ (ε : ℤˣ) : Set ((Fin d → ℤ) × (Fin d → ℤ)) := {q | NearLattice L a₁ q.1 ∧
        NearLattice L a₂ q.2 ∧ q.1 + (ε : ℤ) • q.2 = nk ∧
        |‖latticePoint L q.1‖ ^ 2 + (ε : ℤ) * ‖latticePoint L q.2‖ ^ 2 - β| ≤ tol}
      let S₃ : Set ((Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ)) := {q | NearLattice L a₁ q.1 ∧
        NearLattice L a₂ q.2.1 ∧ NearLattice L a₃ q.2.2 ∧ q.1 - q.2.1 + q.2.2 = nk ∧
        |‖latticePoint L q.1‖ ^ 2 - ‖latticePoint L q.2.1‖ ^ 2 + ‖latticePoint L q.2.2‖ ^ 2 - β| ≤
          tol}
      (∀ ε : ℤˣ, (S₂ ε).Finite) ∧
      (∀ ε : ℤˣ, (ε = -1 → nk ≠ 0) →
        ((S₂ ε).ncard : ℝ) ≤ C * δ⁻¹ * min (L ^ d) (L ^ ((d : ℝ) + 1 - 2 * γ))) ∧
      (L ^ (-γ + η) ≤ ‖k‖ → ((S₂ (-1)).ncard : ℝ) ≤ C * δ⁻¹ * L ^ ((d : ℝ) - γ - η)) ∧
      (S₃.Finite ∧ (S₃.ncard : ℝ) ≤ C * δ⁻¹ * L ^ (2 * ((d : ℝ) - γ))) := by
  sorry

/-! ## B1.9 `quadExpSum2`, B1.10 `quadExpSum3` -/

/-- `e(z) = e^{2πiz}`. -/
noncomputable def eZ (z : ℝ) : ℂ := Complex.exp ((2 * Real.pi * z : ℝ) * Complex.I)

/-- **B1.9 `quadExpSum2`** (T Lemma `lemlayer2`, L970–L977; DH23 Lemma 6.6(2)). Uniformly in
`a, b, ξ, ξ' ∈ ℝ^d`: `∫_{L ≤ |s| ≤ T₀L^{2γ}} |∑_{x,y ∈ ℤ_L^d} χ₀(x-a)χ₀(y-b) e(⟨x,ξ⟩+⟨y,ξ'⟩+s⟨x,y⟩)| ds
≤ C L^{2d-2(d-1)(1-γ)+η}`, `C = C(d,γ,η,T₀)` (T: `≲₂` with `T₀ = 𝔇δ`). The lattice sum has finitely many
nonzero terms (`χ₀` has compact support). -/
theorem quadExpSum2 :
    ∀ d : ℕ, 3 ≤ d → ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 → ∀ η : ℝ, 0 < η → ∀ T₀ : ℝ, 0 < T₀ →
    ∃ C L₀ : ℝ, ∀ L ≥ L₀, ∀ a b ξ ξ' : Mom d,
      ∫ s in {s : ℝ | L ≤ |s| ∧ |s| ≤ T₀ * L ^ (2 * γ)},
          ‖∑' q : (Fin d → ℤ) × (Fin d → ℤ),
            ((chi0Vec (latticePoint L q.1 - a) * chi0Vec (latticePoint L q.2 - b) : ℝ) : ℂ) *
              eZ (inner ℝ (latticePoint L q.1) ξ + inner ℝ (latticePoint L q.2) ξ' +
                s * inner ℝ (latticePoint L q.1) (latticePoint L q.2))‖ ≤
        C * L ^ (2 * (d : ℝ) - 2 * ((d : ℝ) - 1) * (1 - γ) + η) := by
  sorry

/-- **B1.10 `quadExpSum3`** (T Lemma `lemcubic`, L1554–L1593). For
`Λ ∈ {⟨x,z⟩, ⟨z, x+y-z⟩}`, uniformly in `a, b, c, ξ, ξ', ξ''`:
`∫∫_{L ≤ max(|t|,|s|), |t|,|s| ≤ T₀L^{2γ}} |∑_{x,y,z} χ₀(x-a)χ₀(y-b)χ₀(z-c)
e(t⟨x,y⟩ + sΛ + ⟨ξ,x⟩ + ⟨ξ',y⟩ + ⟨ξ'',z⟩)| dt ds ≤ C L^{3d+γ-2γ₀} log L`, `C = C(d,γ,T₀)`. -/
theorem quadExpSum3 :
    ∀ d : ℕ, 3 ≤ d → ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 → ∀ T₀ : ℝ, 0 < T₀ →
    ∃ C L₀ : ℝ, ∀ L ≥ L₀, ∀ Λsel : Bool, ∀ a b c ξ ξ' ξ'' : Mom d,
      let Λf : Mom d → Mom d → Mom d → ℝ := fun x y z =>
        if Λsel then inner ℝ x z else inner ℝ z (x + y - z)
      ∫ ts in {ts : ℝ × ℝ | L ≤ max |ts.1| |ts.2| ∧ |ts.1| ≤ T₀ * L ^ (2 * γ) ∧
          |ts.2| ≤ T₀ * L ^ (2 * γ)},
          ‖∑' q : (Fin d → ℤ) × (Fin d → ℤ) × (Fin d → ℤ),
            ((chi0Vec (latticePoint L q.1 - a) * chi0Vec (latticePoint L q.2.1 - b) *
                chi0Vec (latticePoint L q.2.2 - c) : ℝ) : ℂ) *
              eZ (ts.1 * inner ℝ (latticePoint L q.1) (latticePoint L q.2.1) +
                ts.2 * Λf (latticePoint L q.1) (latticePoint L q.2.1) (latticePoint L q.2.2) +
                inner ℝ ξ (latticePoint L q.1) + inner ℝ ξ' (latticePoint L q.2.1) +
                inner ℝ ξ'' (latticePoint L q.2.2))‖ ≤
        C * L ^ (3 * (d : ℝ) + γ - 2 * min γ (1 - γ)) * Real.log L := by
  sorry

/-! ## B1.11 `canonicalCharacterization` -/

namespace LayeredGarden

variable {w : ℕ} (LG : LayeredGarden w)

/-- The nodes below some node of `S`. -/
def BelowSet (S : Finset (GNode LG.garden.tree)) (a : GNode LG.garden.tree) : Prop :=
  ∃ s ∈ S, s.IsDesc a

@[instance_reducible, instance] def instDecidableBelowSet (S : Finset (GNode LG.garden.tree))
    (a : GNode LG.garden.tree) : Decidable (LG.BelowSet S a) := by
  unfold BelowSet
  infer_instance

/-- The leaves below the nodes of `S`. -/
def leavesBelowSet (S : Finset (GNode LG.garden.tree)) : Finset (GLeaf LG.garden.tree) :=
  Finset.univ.filter fun ℓ => LG.BelowSet S ℓ.toNode

/-- The top region of the subtrees rooted at `S` with attachment nodes `U`: the nodes below `S`
having no strict ancestor in `U` (T Def `defcanon`: the trees `𝒯_j^p` with the leaves `U`). -/
def TopRegion (S U : Finset (GNode LG.garden.tree)) (a : GNode LG.garden.tree) : Prop :=
  LG.BelowSet S a ∧ ∀ u ∈ U, u.IsDesc a → u = a

/-- **The decomposition of T Def `defcanon` at one level with given data `(U, Bp)`**, relative to root
nodes `S` and depth `p + 1`, with a predicate `sub` for "the sub-garden rooted at a block is in
`𝒢_p`": attachment nodes `U` in the top region, a partition of `U` into blocks of size `≥ 4` satisfying `sub`, every other node
of the top region in layer `p`, and every leaf of the top region outside `U` either paired with a
leaf of the top region outside `U` (`B_i` of size 2) or, if `flowers`, a flower (`ℋ`). -/
def TopDecompWith (flowers : Bool) (p : ℕ) (sub : Finset (GNode LG.garden.tree) → Prop)
    (S U : Finset (GNode LG.garden.tree)) (Bp : Finpartition U) : Prop :=
  (∀ u ∈ U, LG.TopRegion S U u) ∧
  (∀ a, LG.TopRegion S U a → a ∉ U → LG.layer a = p) ∧
  (∀ ℓ : GLeaf LG.garden.tree, LG.TopRegion S U ℓ.toNode → ℓ.toNode ∉ U →
    (LG.garden.pair ℓ ≠ ℓ ∧ LG.TopRegion S U (LG.garden.pair ℓ).toNode ∧
      (LG.garden.pair ℓ).toNode ∉ U) ∨ (flowers = true ∧ LG.garden.IsFlower ℓ)) ∧
  ∀ B ∈ Bp.parts, 4 ≤ B.card ∧ sub B

/-- `TopDecompWith` for some construction data `(U, Bp)`. -/
def TopDecomp (flowers : Bool) (p : ℕ) (sub : Finset (GNode LG.garden.tree) → Prop)
    (S : Finset (GNode LG.garden.tree)) : Prop :=
  ∃ U : Finset (GNode LG.garden.tree), ∃ Bp : Finpartition U, LG.TopDecompWith flowers p sub S U Bp

/-- The sub-garden rooted at `S` is irreducible: no nonempty proper `A ⊂ S` has completely paired
leaves (T Def `defcanon`: "no proper subset `A` such that the leaves of `𝒯_j^p, j ∈ A`, equal a union
of some `B_i`"). -/
def IrreducibleAt (S : Finset (GNode LG.garden.tree)) : Prop :=
  ∀ A ∈ S.powerset, A.Nonempty → A ≠ S → ¬ LG.garden.CompletelyPaired (LG.leavesBelowSet A)

@[instance_reducible, instance] def instDecidableIrreducibleAt (S : Finset (GNode LG.garden.tree)) :
    Decidable (LG.IrreducibleAt S) := by
  unfold IrreducibleAt
  infer_instance

@[instance_reducible, instance] def instDecidableTopRegion (S U : Finset (GNode LG.garden.tree))
    (a : GNode LG.garden.tree) : Decidable (LG.TopRegion S U a) := by
  unfold TopRegion
  infer_instance

/-- **The inductive class of T Def `defcanon`, read as a decomposition** (B1.11):
`CanonInd p S` means that the layered sub-garden rooted at the (incomparable) nodes `S` belongs to
`𝒢_p` as defined inductively in Def `defcanon`: `𝒢₀ = ∅`; at depth `p+1`, `|S| ≥ 4`, the leaves below
`S` are completely paired, the sub-garden is irreducible, and it decomposes as in `TopDecomp` with
blocks in `𝒢_p`. -/
def CanonInd : ℕ → Finset (GNode LG.garden.tree) → Prop
  | 0, _ => False
  | p + 1, S => 4 ≤ S.card ∧ (∀ s ∈ S, ∀ s' ∈ S, s ≠ s' → s.Incomparable s') ∧
      LG.garden.CompletelyPaired (LG.leavesBelowSet S) ∧ LG.IrreducibleAt S ∧
      LG.TopDecomp false p (CanonInd p) S

/-- The roots of all trees. -/
def roots : Finset (GNode LG.garden.tree) := Finset.univ.image (GNode.root LG.garden.tree)

end LayeredGarden

/-- **B1.11 `canonicalCharacterization`** (T Def `defcanon`, L657–L668; Prop `canonequiv`,
L888–L897; Def `defflower`, L2262; review G-2, mandatory with B1). (1) The criterion `IsCanonG (p+1)`
coincides with the inductive construction of Def `defcanon` (read as `CanonInd` on the roots, plain
garden); (2) **uniqueness of the construction data**, for gardens, couples and flower gardens alike
(`IsCanonGC` covers `𝒢` and `𝒞`; stage-3 R7): any top-level decomposition `(U, Bp)` has
`U = attachNodes p` and blocks the classes of the relation `AttachLinkedOn p` generated on `𝒰`
(stage-1 R1), hence `IsTrunc`, defined through these data, is T Def `defgtr` (and `ℋ^tr`, T L2288,
for the restriction kind `0`, i.e. `𝒳`; the `𝒴`/`𝒲` reading is packet X1's, delta-1 D1);
for flower gardens with `flowers = false` the hypothesis is unsatisfiable, so the clause is vacuous
there; (3) the same as (1) for couples (`IsCanonC`, no properness/irreducibility) and (4) for flower
gardens (`IsCanonH`, flowers allowed in the top region, stems in layer `p`, no irreducibility).
Deviation: Def `defcanon` builds gardens from data; we state the equivalent decomposition of a given
garden (the construction is a bijection onto its image, which is (2)). -/
theorem canonicalCharacterization {w : ℕ} (p : ℕ) (LG : LayeredGarden w) :
    (IsCanonG (p + 1) LG ↔ LG.garden.IsPlain ∧ LG.CanonInd (p + 1) LG.roots) ∧
    ((IsCanonGC (p + 1) LG ∨ IsCanonH (p + 1) LG) →
      ∀ (flowers : Bool) (U : Finset (GNode LG.garden.tree)) (Bp : Finpartition U),
        LG.TopDecompWith flowers p (LG.CanonInd p) LG.roots U Bp →
        U = LG.attachNodes p ∧
          ∀ B ∈ Bp.parts, ∀ u ∈ B, ∀ u' ∈ U,
            (u' ∈ B ↔ Relation.EqvGen (LG.AttachLinkedOn p) u u')) ∧
    (∀ LG2 : LayeredGarden 2, IsCanonC (p + 1) LG2 ↔ IsCouple LG2.garden ∧
      (∀ s ∈ LG2.roots, ∀ s' ∈ LG2.roots, s ≠ s' → s.Incomparable s') ∧
      LG2.TopDecomp false p (LG2.CanonInd p) LG2.roots) ∧
    (IsCanonH (p + 1) LG ↔ LG.garden.IsFlowerGarden ∧
      LG.TopDecomp true p (LG.CanonInd p) LG.roots) := by
  sorry

end WaveTurbulence

```

### WaveB1-Sumint.lean

```lean
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveBDraft.System

/-!
# Wave B, tier B1 — B1.6 `sumint` (DRAFT for author approval)

T Prop `sumint`, L1595–L1640 (statement), with the WAVE-B v2 §4.6 additions: the explicit constant
`A` of hypothesis (ii), unit intervals inside `[0, 𝔇]`, typo fixes (L1615 `A` = Nor; L1687 index
`j`), and the size hypothesis `M ≤ N_1^4` (review G-4). The datum of the proposition is bundled in
`SumintDatum`; the expression `ℐ` of (sumintI1) is `SumintDatum.expr`.

Encoding of the input vector variables of block `i` (`n_i = 2m_i + 1 + 3·1_Nor(i)` slots, `Fin n_i`):
slot `0` is `x₀ⁱ`, slots `1,…,m_i` are `x_jⁱ`, slots `m_i+1,…,2m_i` are `y_jⁱ`, and for `i ∈ Nor` slots
`2m_i+1, 2m_i+2, 2m_i+3` are `u₁ⁱ, u₂ⁱ, u₃ⁱ`. Input time variables: `t_jⁱ` (`0 ≤ j ≤ m_i`),
`s_jⁱ` (`1 ≤ j ≤ m_i`), `τ_jⁱ` (`i ∈ Nor`, `j = 1,2,3`).
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

/-- The combinatorial shape: `I` blocks, lengths `m_i`, and the partition `Nor ⊔ Bad`. -/
structure SumintShape where
  I : ℕ
  m : Fin I → ℕ
  nor : Fin I → Bool

namespace SumintShape

variable (S : SumintShape)

/-- `n_i = 2m_i + 1 + 3·1_Nor(i)`. -/
def n (i : Fin S.I) : ℕ := 2 * S.m i + 1 + if S.nor i then 3 else 0

/-- The input vector variables `x = (x₀ⁱ, x_jⁱ, y_jⁱ, u_jⁱ)` (and the alternative variables
`k_jⁱ, ℓ_jⁱ`, indexed the same way). -/
abbrev VIdx : Type := Σ i : Fin S.I, Fin (S.n i)

/-- `M = ∑ n_i`. -/
def M : ℕ := ∑ i, S.n i

/-- Lexicographic order on `VIdx`. -/
def LexLt (v w : S.VIdx) : Prop := v.1 < w.1 ∨ (v.1 = w.1 ∧ (v.2 : ℕ) < w.2)

/-- The input time variables: `t_jⁱ` (`j ≤ m_i`), `s_jⁱ` (`1 ≤ j ≤ m_i`, stored as `j - 1`),
`τ_jⁱ` (`i ∈ Nor`). -/
abbrev TVar : Type :=
  (Σ i : Fin S.I, Fin (S.m i + 1)) ⊕ (Σ i : Fin S.I, Fin (S.m i)) ⊕
    (Σ _ : {i : Fin S.I // S.nor i = true}, Fin 3)

/-- The slot of `x_jⁱ` (`1 ≤ j ≤ m_i`, given as `j - 1 : Fin m_i`). -/
def xSlot (i : Fin S.I) (j : Fin (S.m i)) : S.VIdx := ⟨i, ⟨j + 1, by unfold n; omega⟩⟩

/-- The slot of `y_jⁱ`. -/
def ySlot (i : Fin S.I) (j : Fin (S.m i)) : S.VIdx := ⟨i, ⟨S.m i + 1 + j, by unfold n; omega⟩⟩

/-- The slot of `x₀ⁱ`. -/
def x0Slot (i : Fin S.I) : S.VIdx := ⟨i, ⟨0, by unfold n; omega⟩⟩

/-- The slot of `u_cⁱ` (`i ∈ Nor`, `c = 0,1,2` for `u₁, u₂, u₃`). -/
def uSlot (i : Fin S.I) (h : S.nor i = true) (c : Fin 3) : S.VIdx :=
  ⟨i, ⟨2 * S.m i + 1 + c, by unfold n; simp only [h, ite_true]; omega⟩⟩

end SumintShape

/-- A coefficient in `{0, ±1}`. -/
def IsUnitCoeff (a : ℤ) : Prop := a = 0 ∨ a = 1 ∨ a = -1

/-- **The datum of `sumint`** (T L1595–L1625). The affine maps `k = T₁x + h₁`, `ℓ = T₂x + h₂` have
integer matrices and shifts that are integer combinations of `(e,f,g,h)` (WAVE-B v2: "affine maps
`h₁, h₂` of `(e,f,g,h)`"). -/
structure SumintDatum (d : ℕ) where
  S : SumintShape
  /-- `T₁`, its inverse, and `T₂`, with entries in `{0, ±1}` -/
  T₁ : Matrix S.VIdx S.VIdx ℤ
  T₁inv : Matrix S.VIdx S.VIdx ℤ
  T₂ : Matrix S.VIdx S.VIdx ℤ
  T₁_mul : T₁ * T₁inv = 1
  T₁inv_mul : T₁inv * T₁ = 1
  T_unit : ∀ v v', IsUnitCoeff (T₁ v v') ∧ IsUnitCoeff (T₁inv v v') ∧ IsUnitCoeff (T₂ v v')
  /-- the shifts `h₁, h₂` as coefficients of `(e, f, g, h)` -/
  H₁ : S.VIdx → Fin 4 → ℤ
  H₂ : S.VIdx → Fin 4 → ℤ
  /-- all of `k, ℓ, e, f, g, h` lie in `w̲ + ℤ_L^d` -/
  H_coset : ∀ v, ∑ c, H₁ v c = 1 ∧ ∑ c, H₂ v c = 1
  /-- hypothesis (ii): the predecessors and the numbers `Λ_jⁱ`. Reading (stage-3 O3):
  `prev v = none` means that `ℓ_v` itself is a signed sum (otherwise (ii) would be impossible for the
  lex-first index). -/
  Λ : S.VIdx → ℕ
  prev : S.VIdx → Option S.VIdx
  /-- the signed sums of (ii): coefficients of `k` and of `(e,f,g,h)` -/
  σk : S.VIdx → S.VIdx → ℤ
  σe : S.VIdx → Fin 4 → ℤ
  /-- weights `𝒦_jⁱ, ℒ_jⁱ` and the integers `g_{ij}, g'_{ij}` -/
  wK : S.VIdx → Mom d → ℂ
  wL : S.VIdx → Mom d → ℂ
  g : S.VIdx → ℕ
  g' : S.VIdx → ℕ
  /-- `ζ_jⁱ = a x_j + b y_j + c r` (`j ≥ 1`) -/
  ζc : (i : Fin S.I) → Fin (S.m i) → Fin 3 → ℤ
  /-- `Λ_i` choice (`true`: `⟨u₁,u₃⟩`, `false`: `⟨u₃, u₁+u₂-u₃⟩`) and `ξ_i = a u₁ + b u₂ + c u₃ + d r` -/
  Λsel : Fin S.I → Bool
  ξc : Fin S.I → Fin 4 → ℤ
  /-- parameters `λ_jⁱ` (on `t`), `μ_jⁱ` (on `s`), `σ_jⁱ` (on `τ`) -/
  param : S.TVar → ℝ
  /-- unit intervals `[q_v, q_v+1]` of the input times and the order constraints `v < w` -/
  q : S.TVar → ℕ
  constraints : Finset (S.TVar × S.TVar)
  /-- for `i ∈ Bad`, which of (a)–(d) holds (`0`–`3`) -/
  badKind : Fin S.I → Fin 4
  /-- output unit intervals for `(t, t', t'')`, unit-ball centres for `(e,f,g,h)`, and `w̲` -/
  qOut : Fin 3 → ℕ
  centre : Fin 4 → Mom d
  wBar : Mom d

namespace SumintDatum

variable {d : ℕ} (D : SumintDatum d)

/-- `k(x; e,f,g,h)` and `ℓ(x; e,f,g,h)` for lattice indices `x` (input vectors `x_v / L`). -/
noncomputable def kVec (L : ℝ) (x : D.S.VIdx → (Fin d → ℤ)) (efgh : Fin 4 → Mom d) (v : D.S.VIdx) :
    Mom d :=
  ∑ v', (D.T₁ v v' : ℝ) • latticePoint L (x v') + ∑ c, (D.H₁ v c : ℝ) • efgh c

noncomputable def ℓVec (L : ℝ) (x : D.S.VIdx → (Fin d → ℤ)) (efgh : Fin 4 → Mom d) (v : D.S.VIdx) :
    Mom d :=
  ∑ v', (D.T₂ v v' : ℝ) • latticePoint L (x v') + ∑ c, (D.H₂ v c : ℝ) • efgh c

/-- **Hypotheses (ii), (iii) and the weight bounds** of `sumint` (T L1603–L1622), with `A` the
constant of (ii) and the bad-case conditions (a), (d). Every `Λ_v ≥ 1` ("at most `Λ` terms" with
`∏ Λ ≤ C₀^M` a genuine count): a zero factor would make `∏ Λ_v ≤ A^M` vacuous and leave the other
`Λ_v` unconstrained (stage-3 R6). -/
def Admissible (A : ℝ) (L γ η : ℝ) (Dsteps : ℕ) : Prop :=
  -- (ii) as identities of affine forms: `ℓ_v - ℓ_{prev v} = ∑ σk k + ∑ σe (e,f,g,h)`
  (∀ v, (∀ v', IsUnitCoeff (D.σk v v')) ∧ (∀ c, IsUnitCoeff (D.σe v c)) ∧
    ((Finset.univ.filter fun v' => D.σk v v' ≠ 0).card +
      (Finset.univ.filter fun c => D.σe v c ≠ 0).card ≤ D.Λ v) ∧
    (∀ w, D.prev v = some w → D.S.LexLt w v) ∧
    (∀ v'', D.T₂ v v'' - (D.prev v).elim 0 (fun w => D.T₂ w v'') =
      ∑ v', D.σk v v' * D.T₁ v' v'') ∧
    ∀ c, D.H₂ v c - (D.prev v).elim 0 (fun w => D.H₂ w c) =
      ∑ v', D.σk v v' * D.H₁ v' c + D.σe v c) ∧
  (∀ v, 1 ≤ D.Λ v) ∧ ((∏ v, (D.Λ v : ℝ)) ≤ A ^ D.S.M) ∧
  -- (iii): every input variable is the difference of two of `(k, ℓ, e, f, g, h)` (as affine forms)
  (∀ v, ∃ a b : D.S.VIdx ⊕ D.S.VIdx ⊕ Fin 4,
    let rowT : D.S.VIdx ⊕ D.S.VIdx ⊕ Fin 4 → D.S.VIdx → ℤ := fun z => match z with
      | .inl w => D.T₁ w | .inr (.inl w) => D.T₂ w | .inr (.inr _) => 0
    let rowH : D.S.VIdx ⊕ D.S.VIdx ⊕ Fin 4 → Fin 4 → ℤ := fun z => match z with
      | .inl w => D.H₁ w | .inr (.inl w) => D.H₂ w | .inr (.inr c) => Pi.single c 1
    (∀ v', rowT a v' - rowT b v' = if v' = v then 1 else 0) ∧ ∀ c, rowH a c - rowH b c = 0) ∧
  -- the weight bounds (propertyKj)
  (∀ v, SNorm (30 * d) (30 * d) (D.wK v) ≤ ENNReal.ofReal (L ^ (-(min (2 * γ)
      (min 1 (2 * ((d : ℝ) - 1) * (1 - γ))) - Real.sqrt η) * D.g v)) ∧
    SNorm (30 * d) 0 (D.wL v) ≤ ENNReal.ofReal (L ^ (-(min (2 * γ)
      (min 1 (2 * ((d : ℝ) - 1) * (1 - γ))) - Real.sqrt η) * D.g' v))) ∧
  -- coefficients in `{0, ±1}`
  (∀ i j c, IsUnitCoeff (D.ζc i j c)) ∧ (∀ i c, IsUnitCoeff (D.ξc i c)) ∧
  -- unit intervals inside `[0, 𝔇]`
  (∀ v, D.q v + 1 ≤ Dsteps) ∧ (∀ c, D.qOut c + 1 ≤ Dsteps) ∧
  -- the bad cases (a) and (d)
  (∀ i, D.S.nor i = false →
    (D.badKind i = 0 → ∃ h : 0 < D.S.m i,
      let t0 : D.S.TVar := .inl ⟨i, 0⟩
      let t1 : D.S.TVar := .inl ⟨i, ⟨1, by omega⟩⟩
      let s1 : D.S.TVar := .inr (.inl ⟨i, ⟨0, h⟩⟩)
      ((s1, t0) ∈ D.constraints ∧ (t0, t1) ∈ D.constraints) ∨
        ((t1, t0) ∈ D.constraints ∧ (t0, s1) ∈ D.constraints)) ∧
    (D.badKind i = 2 → 0 < D.S.m i) ∧
    (D.badKind i = 3 → ∃ j : Fin (D.S.n i), 1 ≤ max (D.g ⟨i, j⟩) (D.g' ⟨i, j⟩)))

/-- The input time domain `𝒟(t, t', t'')` (T L1612–L1613): unit intervals, all `< t`, `t₀¹ >
max(t', t'')`, and the order constraints. Requires `I ≥ 1`. -/
def timeDom (hI : 0 < D.S.I) (t t' t'' : ℝ) : Set (D.S.TVar → ℝ) :=
  {τ | (∀ v, (D.q v : ℝ) ≤ τ v ∧ τ v ≤ D.q v + 1 ∧ τ v < t) ∧
    max t' t'' < τ (.inl ⟨⟨0, hI⟩, 0⟩) ∧ ∀ c ∈ D.constraints, τ c.1 < τ c.2}

/-- The phase of (sumintI1) at input vectors `x` and input times `τ`, including the extra factors
`|t₁ⁱ - s₁ⁱ|^{1-3η}` of the bad case (c). -/
noncomputable def phase (L γ δ η : ℝ) (x : D.S.VIdx → (Fin d → ℤ)) (r : Mom d) (t : ℝ)
    (τ : D.S.TVar → ℝ) : ℂ :=
  let c := δ * L ^ (2 * γ)
  let X : D.S.VIdx → Mom d := fun v => latticePoint L (x v)
  let e (θ : ℝ) : ℂ := Complex.exp ((Real.pi * θ : ℝ) * Complex.I)
  (∏ i, ((∏ j : Fin (D.S.m i), e (c * (τ (.inl ⟨i, j.succ⟩) - τ (.inr (.inl ⟨i, j⟩))) *
        inner ℝ (X (D.S.xSlot i j)) (X (D.S.ySlot i j)))) *
      e (c * (τ (.inl ⟨i, 0⟩) - t) * inner ℝ r (X (D.S.x0Slot i))) *
      (∏ j : Fin (D.S.m i), e (c * (τ (.inl ⟨i, j.succ⟩) - t) * inner ℝ r
        ((D.ζc i j 0 : ℝ) • X (D.S.xSlot i j) + (D.ζc i j 1 : ℝ) • X (D.S.ySlot i j) +
          (D.ζc i j 2 : ℝ) • r))) *
      (∏ j : Fin (D.S.m i + 1), e (D.param (.inl ⟨i, j⟩) * τ (.inl ⟨i, j⟩))) *
      (∏ j : Fin (D.S.m i), e (D.param (.inr (.inl ⟨i, j⟩)) * τ (.inr (.inl ⟨i, j⟩)))) *
      (if h : D.S.nor i = false ∧ D.badKind i = 2 ∧ 0 < D.S.m i then
        ((|τ (.inl ⟨i, ⟨1, by omega⟩⟩) - τ (.inr (.inl ⟨i, ⟨0, h.2.2⟩⟩))| ^ (1 - 3 * η) : ℝ) : ℂ)
      else 1))) *
  ∏ i : {i : Fin D.S.I // D.S.nor i = true},
    let u (c' : Fin 3) := X (D.S.uSlot i.1 i.2 c')
    let τ' (c' : Fin 3) := τ (.inr (.inr ⟨i, c'⟩))
    e (c * (τ' 0 - τ' 2) * inner ℝ (u 0) (u 1)) *
      e (c * (τ' 1 - τ' 2) *
        (if D.Λsel i.1 then inner ℝ (u 0) (u 2) else inner ℝ (u 2) (u 0 + u 1 - u 2))) *
      e (c * (τ' 2 - t) * inner ℝ r ((D.ξc i.1 0 : ℝ) • u 0 + (D.ξc i.1 1 : ℝ) • u 1 +
        (D.ξc i.1 2 : ℝ) • u 2 + (D.ξc i.1 3 : ℝ) • r)) *
      ∏ c', e (D.param (.inr (.inr ⟨i, c'⟩)) * τ' c')

/-- **The expression `ℐ(t, t', t'', e, f, g, h)`** of (sumintI1) (T L1608–L1611), with the extra
factor `|r|` for each bad block of case (b). -/
noncomputable def expr (hI : 0 < D.S.I) (L γ δ η : ℝ) (tt : Fin 3 → ℝ) (efgh : Fin 4 → Mom d) :
    ℂ :=
  let r := efgh 0 - efgh 1
  ((‖r‖ ^ (Finset.univ.filter fun i => D.S.nor i = false ∧ D.badKind i = 1).card : ℝ) : ℂ) *
  ∑' x : D.S.VIdx → (Fin d → ℤ),
    (∏ v, D.wK v (D.kVec L x efgh v) * D.wL v (D.ℓVec L x efgh v)) *
      ∫ τ in D.timeDom hI (tt 0) (tt 1) (tt 2), D.phase L γ δ η x r (tt 0) τ

/-- `M₀`: the number of pairs `(t_jⁱ, s_jⁱ)` in different unit intervals, plus the number of `i ∈ Nor`
whose `τ₁ⁱ, τ₂ⁱ, τ₃ⁱ` are not in one unit interval (T L1622–L1623, "`i ∈ A`" read as `i ∈ Nor`). -/
def M₀ : ℕ :=
  (Finset.univ.filter fun p : Σ i : Fin D.S.I, Fin (D.S.m i) =>
      D.q (.inl ⟨p.1, p.2.succ⟩) ≠ D.q (.inr (.inl ⟨p.1, p.2⟩))).card +
    (Finset.univ.filter fun i : {i : Fin D.S.I // D.S.nor i = true} =>
      ¬ (D.q (.inr (.inr ⟨i, 0⟩)) = D.q (.inr (.inr ⟨i, 1⟩)) ∧
        D.q (.inr (.inr ⟨i, 1⟩)) = D.q (.inr (.inr ⟨i, 2⟩)))).card

/-- `M₁ = ∑ (g_{ij} + g'_{ij})`. -/
def M₁ : ℕ := ∑ v, (D.g v + D.g' v)

end SumintDatum

/-- The prefix `(Π)` with the constant `A ≥ 1` of `sumint` (ii) quantified right after `η`
(WAVE-B v2 §4.6). -/
def WTPrefixA (Q : ℝ → WTParams → Prop) : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 →
  ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, η ∈ Ioc 0 η₀ → ∀ A : ℝ, 1 ≤ A →
  ∀ φin : SchwartzMap (Mom d) ℝ, (∀ k, 0 ≤ φin k) →
  ∀ τstar : ℝ, 0 < τstar → ∀ φ : ℝ → SchwartzMap (Mom d) ℝ, IsWKESolution φin τstar φ →
  ∃ C₁ : ℝ, 1 ≤ C₁ ∧ ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ ν : ℝ, ν ∈ Ioc 0 ν₀ →
  ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, δ ∈ Ioc 0 δ₀ → ∀ D : ℕ, 1 ≤ D → τstar = D * δ →
  ∃ C₂ : ℝ, 1 ≤ C₂ ∧ ∃ L₀ : ℝ, 2 ≤ L₀ ∧ ∀ L : ℝ, L₀ ≤ L →
  Q A ⟨d, γ, η, φin, τstar, φ, C₁, ν, δ, D, C₂, L⟩

/-- **B1.6 `sumint`** (T Prop `sumint`, L1595–L1640; WAVE-B v2 §4.6). For every admissible datum
with `I ≥ 1` and `M ≤ N_1^4`: with `ℬ = {(t,t',t'') ∈ ∏ [q,q+1] : t > max(t',t'')}` and `K` the set of
`(e,f,g,h) ∈ (w̲ + ℤ_L^d)^4` in the unit balls with `e - f = h - g = r ≠ 0`, `|r| ≤ L^{-γ+η}`,
`‖ℐ‖_{𝔛^{2η^8,0,0}(ℬ)} ≤ C₁ [max ⟨λ,μ,σ⟩]^{η^6} (C₁δ^{-1/2})^M L^{M(d-γ) - η²(|Bad| + M₁) - η^8 M₀ + η^7}`.
Deviations (WAVE-B v2 §4.6): (D1) weights on `ℝ^d` with the `ℝ^d` 𝔖-norm; (D2) `A` explicit (T: `C₀^M`);
(D3) unit intervals inside `[0, 𝔇]`; (D4) typo fixes (L1615 `A` = Nor; L1687 `j`); (D5) F23 (proof
obligation, not in the statement); (D6, G-4) the size hypothesis `M ≤ N_1^4`; (D7) the shifts
`h₁, h₂` are integer combinations of `(e,f,g,h)` with coefficient sum `1` and no constant lattice
offset (T: "vectors depending only on `(e,f,g,h)`"; if a consumer needs an offset, the datum gets
`c₁ c₂ : S.VIdx → (Fin d → ℤ)`, stage-3 O3 and question 3); (D8, stage-3 R6) every `Λ_v ≥ 1`. -/
theorem sumint : WTPrefixA fun A P =>
    ∀ (D : SumintDatum P.d) (hI : 0 < D.S.I), D.Admissible A P.L P.γ P.η P.D →
      D.S.M ≤ P.N 1 ^ 4 →
      let B : Set (Fin 3 → ℝ) := {tt | (∀ c, (D.qOut c : ℝ) ≤ tt c ∧ tt c ≤ D.qOut c + 1) ∧
        max (tt 1) (tt 2) < tt 0}
      let K : Set (Fin 4 → Mom P.d) := {v | (∀ c, (∃ nv : Fin P.d → ℤ, v c = D.wBar +
          latticePoint P.L nv) ∧ ‖v c - D.centre c‖ ≤ 1) ∧ v 0 - v 1 = v 3 - v 2 ∧ v 0 ≠ v 1 ∧
        ‖v 0 - v 1‖ ≤ P.L ^ (-P.γ + P.η)}
      let maxPar : ℝ := ⨆ v, jbr (d := 1) (WithLp.toLp 2 fun _ => D.param v)
      XNorm00Restr (2 * P.η ^ 8) B K (fun tt v => D.expr hI P.L P.γ P.δ P.η tt v) ≤
        ENNReal.ofReal (P.C₁ * maxPar ^ (P.η ^ 6) * (P.C₁ * P.δ ^ (-(1 : ℝ) / 2)) ^ D.S.M *
          P.L ^ ((D.S.M : ℝ) * (P.d - P.γ) -
            P.η ^ 2 * ((Finset.univ.filter fun i => D.S.nor i = false).card + D.M₁) -
            P.η ^ 8 * D.M₀ + P.η ^ 7)) := by
  sorry

end WaveTurbulence

```

### WaveB1-Flower.lean

```lean
/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveBDraft.Statements

/-!
# B1.12 `layergardenFlower`, redraft (packet X1; frozen candidate)

The deterministic flower-garden gate. This redraft is meant to suffice for `fixedpoint`'s proof (stage-3 R8;
FLOWER-DESIGN.md §3). It replaces the deferred draft of `WaveB1-Deferred.lean`. Like the freeze set, it imports
only the frozen B1 files (closure policy, fix list 3 item 3).

* **§1 The general kernel `kernelKgen`.** It is `kernelK` with three generalizations (R8: "a set of designated
  branching nodes with prescribed times, plus a cutoff-function parameter"):
  - designated **fixed-time nodes** `fix b = some v`, whose times are not integrated;
  - a set `off` of nodes whose phase factor is removed (the `𝒥^†` of T L2327);
  - a **weight** on the decoration (the smooth cutoffs of T L2283–L2285, and the sibling labels of T L2327).

  Its time domain `kDomainFix` keeps the layer and upper-time constraints for free nodes, and the order
  constraint `t_{𝔫'} < t_𝔫` whenever at least one of the two nodes is free. A Dirac factor `δ(t_𝔫 − s)` at
  the boundary of `t_𝔫 < t_{𝔫^pr}` turns that constraint into an equality (T L2331).
* **§2 Flower-garden data.**
  - the fixed-time patterns `FixPat`: plain, `∂_t` (root ↦ `t`), `∂_s` (the parent, or a non-flower branching
    child, of `𝔣^pr` ↦ `s`), each with `𝔣^pr ↦ s`;
  - the dyadic cutoffs `dyadicCut` and the weights for `M₁` (top leaves), `M₂` (stem resonances) and `†`
    (sibling labels);
  - the kinds of initial flower trees: `𝒳` (`1 ≤` top order `≤ N_{p+1}`, F39); `𝒴`, `𝒲` ((Y-1)–(Y-2),
    (W-1)–(W-3), which **replace** the top bound: F46, delta-1 D1);
  - the kinds of trees in couples: `a^tr` (top order `≤ N_{p+1}`) and `ℒ₀` (top order `> N_{p+1}`, root
    children `≤ N_{p+1}`).
* **§3 The sums.** `flowerSum` corrects `truncSumHζ`; `coupleSum` gives the second moments of `ℒ₀`,
  `∂_t a^tr` and `∂_t ℒ₀`.
* **§4 B1.12.**
-/

@[expose] public section

open MeasureTheory Finset Set
open scoped ENNReal

namespace WaveTurbulence

/-! ## §1 The general kernel -/

section General

variable {w : ℕ}

/-- Branch times from the free times: a designated node `b` (`fix b = some v`) gets the time `v`. -/
def Garden.extendFix (G : Garden w) (fix : GBranch G.tree → Option ℝ)
    (τ : {b : GBranch G.tree // fix b = none} → ℝ) : GBranch G.tree → ℝ :=
  fun b => match h : fix b with
    | some v => v
    | none => τ ⟨b, h⟩

/-- The **time domain with designated nodes**:
- every free node has `𝔏_𝔫 < t_𝔫 < 𝔏_𝔫 + 1`, `0 < t_𝔫 < up(𝔫)`;
- `t_{𝔫'} < t_𝔫` for a branching child `𝔫'` of `𝔫` whenever at least one of the two is free.

The constraints that only involve designated nodes are dropped. Their times are prescribed, and a Dirac
factor `δ(t_𝔫 − s)` sits on the boundary `t_𝔫 = t_{𝔫'}` (T L2331). With the flower parents as the
designated nodes and no lone leaves, this is `kDomain` (bridge `kDomainFix_flowerParents`, probes). -/
def kDomainFix (LG : LayeredGarden w) (up : GBranch LG.garden.tree → ℝ)
    (fix : GBranch LG.garden.tree → Option ℝ) : Set (GBranch LG.garden.tree → ℝ) :=
  {τ | ∀ b, (fix b = none → (LG.layer b.toNode : ℝ) < τ b ∧ τ b < LG.layer b.toNode + 1 ∧
      0 < τ b ∧ τ b < up b) ∧
    ∀ b' : GBranch LG.garden.tree, b'.IsChildOf b → (fix b' = none ∨ fix b = none) → τ b' < τ b}

variable (L γ δ : ℝ) {d : ℕ}

/-- The phase product with the phases at the nodes of `off` removed (`𝒥^†`, T L2327). -/
noncomputable def phaseProdOff (G : Garden w) (off : Finset (GBranch G.tree))
    (k : GNode G.tree → Mom d) (τ : GBranch G.tree → ℝ) : ℂ :=
  ∏ b : GBranch G.tree, if b ∈ off then 1 else
    Complex.exp ((Real.pi * ((G.sign b.toNode : ℤˣ) : ℤ) * δ * L ^ (2 * γ) * omegaNode G k b * τ b : ℝ) *
      Complex.I)

/-- **The general kernel** (R8): `kernelK` with designated fixed-time nodes `fix`, removed phases `off`
and a decoration weight `wt`:
`(δ/(2L^{d-γ}))^n ζ(𝒢) ∑_κ ε_κ wt(k) ∫ 1_{kDomainFix} ∏_{𝔫∉off} e^{πiζ_𝔫δL^{2γ}Ω_𝔫t_𝔫}
∏^{(+,unmarked)}_ℓ F_{𝔏_ℓ}(k_ℓ)`. The integral runs over the free times. -/
noncomputable def kernelKgen (F : ℕ → Mom d → ℝ) (LG : LayeredGarden w)
    (fix : GBranch LG.garden.tree → Option ℝ) (off : Finset (GBranch LG.garden.tree))
    (wt : (GNode LG.garden.tree → Mom d) → ℝ) (up : GBranch LG.garden.tree → ℝ) (k₀ : Mom d)
    (nroot : Fin w → (Fin d → ℤ)) (nfl : Fin d → ℤ) : ℂ :=
  (coupling d L γ δ : ℂ) ^ LG.garden.order * LG.garden.zeta *
    ∑' κ : GenDecoration LG.garden d nroot nfl,
      (epsDec LG.garden κ.1 : ℂ) * (wt (cosetDecoration LG.garden L k₀ κ.1) : ℂ) *
        (∫ τ : {b : GBranch LG.garden.tree // fix b = none} → ℝ,
          (kDomainFix LG up fix).indicator
            (phaseProdOff L γ δ LG.garden off (cosetDecoration LG.garden L k₀ κ.1))
            (LG.garden.extendFix fix τ)) *
        ∏ ℓ ∈ inputLeaves LG.garden,
          (F (LG.layer ℓ.toNode) (cosetDecoration LG.garden L k₀ κ.1 ℓ.toNode) : ℂ)

end General

/-! ## §2 Flower-garden data -/

/-- The **fixed-time pattern** of one flower tree (T L2312, L2331). In every pattern the flower parent
has time `s`.
- `plain`: no other designated node.
- `dRoot`: the root also has time `t` (`∂_t`).
- `dParent`: the parent of `𝔣^pr` also has time `s` (`∂_s`).
- `dChild i`: the `i`-th child of `𝔣^pr`, a branching node, also has time `s` (`∂_s`). -/
inductive FixPat : Type
  | plain : FixPat
  | dRoot : FixPat
  | dParent : FixPat
  | dChild (i : Fin 3) : FixPat

/-- Decidable equality of patterns, written out as for `TTree` and `MarkTag` (CL-17/CL-18: no `deriving` in the
freeze set). -/
def FixPat.decEq : (a b : FixPat) → Decidable (a = b)
  | .plain, .plain => isTrue rfl
  | .plain, .dRoot => isFalse fun h => FixPat.noConfusion h
  | .plain, .dParent => isFalse fun h => FixPat.noConfusion h
  | .plain, .dChild _ => isFalse fun h => FixPat.noConfusion h
  | .dRoot, .plain => isFalse fun h => FixPat.noConfusion h
  | .dRoot, .dRoot => isTrue rfl
  | .dRoot, .dParent => isFalse fun h => FixPat.noConfusion h
  | .dRoot, .dChild _ => isFalse fun h => FixPat.noConfusion h
  | .dParent, .plain => isFalse fun h => FixPat.noConfusion h
  | .dParent, .dRoot => isFalse fun h => FixPat.noConfusion h
  | .dParent, .dParent => isTrue rfl
  | .dParent, .dChild _ => isFalse fun h => FixPat.noConfusion h
  | .dChild _, .plain => isFalse fun h => FixPat.noConfusion h
  | .dChild _, .dRoot => isFalse fun h => FixPat.noConfusion h
  | .dChild _, .dParent => isFalse fun h => FixPat.noConfusion h
  | .dChild i, .dChild j =>
    if h : i = j then isTrue (h ▸ rfl) else isFalse fun e => h (FixPat.dChild.inj e)

@[instance_reducible, instance] def instDecidableEqFixPat : DecidableEq FixPat := FixPat.decEq

/-- The dyadic smooth cutoffs `φ_M`, `M = 2^j L`, behind "`∼₀ M` (or `≲₀ M` if `M = L`)" (T L2283–L2285):
- `φ_L(x) = χ₀(x/L)`;
- `φ_{2^jL}(x) = χ₀(x/(2^jL)) − χ₀(x/(2^{j−1}L))` for `j ≥ 1`.

They sum to `1`. `φ_M` is supported in `|x| < M`, and in `|x| > M/4` when `j ≥ 1`. -/
noncomputable def dyadicCut (L : ℝ) (j : ℕ) (x : ℝ) : ℝ :=
  if j = 0 then chi0 (x / L) else chi0 (x / (2 ^ j * L)) - chi0 (x / (2 ^ (j - 1) * L))

namespace LayeredGarden

variable {w : ℕ} (LG : LayeredGarden w)

/-- The number of layer-`p` branching nodes below `a` (the "order" of T L2290). -/
def topCountBelow (p : ℕ) (a : GNode LG.garden.tree) : ℕ :=
  (Finset.univ.filter fun b : GBranch LG.garden.tree =>
    a.IsDesc b.toNode ∧ LG.layer b.toNode = p).card

/-- `ℓ`'s node is a flower. -/
def IsFlowerNode (a : GNode LG.garden.tree) : Prop :=
  ∃ ℓ : GLeaf LG.garden.tree, LG.garden.IsFlower ℓ ∧ ℓ.toNode = a

/-- The **leaves of the initial flower trees** (T L2283, L2294). These are the non-root nodes with a
layer-`p` parent that are leaves or lie in a lower layer: the paired layer-`p` leaves, the flower, and the
roots of the attached gardens. -/
def IsTopLeaf (p : ℕ) (a : GNode LG.garden.tree) : Prop :=
  (LG.layer a < p ∨ a.1.2 ∈ (LG.garden.tree a.1.1).leaves) ∧ a.1.2 ≠ [] ∧ LG.parentLayer p a = p

open Classical in
/-- **The fixed times** of the pattern vector `pat` (T L2264, L2312, L2331): flower parents ↦ `s`,
and per tree `j`, according to `pat j`, the root ↦ `t` or a neighbour of `𝔣^pr` ↦ `s`. -/
noncomputable def fixPat (pat : Fin w → FixPat) (t s : ℝ) (b : GBranch LG.garden.tree) : Option ℝ :=
  if LG.garden.IsFlowerParent b then some s else
  match pat b.1.1 with
  | .plain => none
  | .dRoot => if b.1.2 = [] then some t else none
  | .dParent => if ∃ c : GBranch LG.garden.tree, LG.garden.IsFlowerParent c ∧ c.IsChildOf b
      then some s else none
  | .dChild i => if ∃ c : GBranch LG.garden.tree, LG.garden.IsFlowerParent c ∧ b.1.1 = c.1.1 ∧
      b.1.2 = c.1.2 ++ [i] then some s else none

/-- The pattern of tree `j` designates an existing node other than `𝔣^pr`. Without it the pattern's
boundary term does not exist.

For `dChild i` the designated child of `𝔣^pr` is in layer `p` (F68). The boundary term `δ(t_𝔫 − s)` of `∂_s`
(T L2331) is taken in the single-tree kernel `𝒥^†`, where a non-flower child of `𝔣^pr` is a top-layer branching
node or a leaf. So the root of an attached lower-layer garden is excluded. -/
def PatValid (p : ℕ) (j : Fin w) : FixPat → Prop
  | .plain => True
  | .dRoot => ∃ b : GBranch LG.garden.tree, b.1 = (j, []) ∧ ¬ LG.garden.IsFlowerParent b
  | .dParent => ∃ b c : GBranch LG.garden.tree, LG.garden.IsFlowerParent c ∧ c.1.1 = j ∧ c.IsChildOf b
  | .dChild i => ∃ b c : GBranch LG.garden.tree, LG.garden.IsFlowerParent c ∧ c.1.1 = j ∧
      b.1.1 = j ∧ b.1.2 = c.1.2 ++ [i] ∧ LG.layer b.toNode = p

variable {d : ℕ}

open Classical in
/-- The `M₁` weight (T L2283, L2294): per tree, `φ_{M₁}` of the largest `|k|` over the non-flower
leaves of the initial flower tree. -/
noncomputable def cutWeight1 (p : ℕ) (L : ℝ) (j₁ : ℕ) (k : GNode LG.garden.tree → Mom d) : ℝ :=
  ∏ j : Fin w, dyadicCut L j₁ (((Finset.univ.filter fun a : GNode LG.garden.tree =>
    a.1.1 = j ∧ LG.IsTopLeaf p a ∧ ¬ LG.IsFlowerNode a).sup fun a => ‖k a‖₊ : NNReal) : ℝ)

open Classical in
/-- The `M₂` weight (T L2285, L2299): per tree, `φ_{M₂}` of the largest `|Ω_𝔫|` over the stem branching
nodes other than `𝔣^pr`. -/
noncomputable def cutWeight2 (L : ℝ) (j₂ : ℕ) (k : GNode LG.garden.tree → Mom d) : ℝ :=
  ∏ j : Fin w, dyadicCut L j₂ (((Finset.univ.filter fun b : GBranch LG.garden.tree =>
    b.1.1 = j ∧ LG.OnStem b.toNode ∧ ¬ LG.garden.IsFlowerParent b).sup
      fun b => ‖omegaNode LG.garden k b‖₊ : NNReal) : ℝ)

open Classical in
/-- The `†` weight (T L2327): the children of each `𝔣^pr` other than the flower carry the prescribed
vectors `c j i`. -/
noncomputable def sibWeight (c : Fin w → Fin 3 → Mom d) (k : GNode LG.garden.tree → Mom d) : ℝ :=
  ∏ b : GBranch LG.garden.tree, if LG.garden.IsFlowerParent b then
    ∏ i : Fin 3, (if LG.IsFlowerNode (b.child i) then 1 else
      if k (b.child i) = c b.1.1 i then 1 else 0) else 1

end LayeredGarden

/-- The kinds of initial flower trees: `𝒳` (T (operatorxker), without the identity term), `𝒴` and `𝒲`
(T L2273). -/
inductive FlowerKind : Type
  | X : FlowerKind
  | Y : FlowerKind
  | W : FlowerKind

/-- The kinds of trees in couples: `a^tr` (T (trterm)) and `ℒ₀` (T L2312). -/
inductive TreeKind : Type
  | tr : TreeKind
  | L0 : TreeKind

namespace LayeredGarden

variable {w : ℕ} (LG : LayeredGarden w)

/-- **The kind restrictions on the initial flower trees.** "Order" means the number of layer-`p` branching
nodes (T L2290).
- `X`: `1 ≤` order `≤ N_{p+1}`. The `1 ≤` excludes the trivial flower tree, whose term is the identity of
  `𝒳 = 1 + ∑ 𝒥̃` (F39; DH23 (kernelexp)).
- `Y`: (Y-1) order `> N_{p+1}`, (Y-2) each child of the root has `≤ N_{p+1}` below it.
- `W`: (W-1) order `> N_{p+1}`, (W-2) each sibling of `𝔣` has `≤ N_{p+1}` below it, (W-3) order minus the
  count below `𝔣^pr` `≤ N_{p+1}`.

For `Y` and `W` these replace the bound `N_{p+1}` of `ℋ^tr` (F46, delta-1 D1). -/
def FlowerKindOK (p Ntr : ℕ) : FlowerKind → Prop
  | .X => ∀ j, 1 ≤ LG.topOrder p j ∧ LG.topOrder p j ≤ Ntr
  | .Y => ∀ j, Ntr < LG.topOrder p j ∧ ∀ b : GBranch LG.garden.tree, b.1 = (j, []) →
      ∀ i : Fin 3, LG.topCountBelow p (b.child i) ≤ Ntr
  | .W => ∀ j, Ntr < LG.topOrder p j ∧ ∀ b : GBranch LG.garden.tree, b.1.1 = j →
      LG.garden.IsFlowerParent b →
        (∀ i : Fin 3, ¬ LG.IsFlowerNode (b.child i) → LG.topCountBelow p (b.child i) ≤ Ntr) ∧
        LG.topOrder p j - LG.topCountBelow p b.toNode ≤ Ntr

/-- **The kind restrictions on the trees of a couple:**
- `tr`: top order `≤ N_{p+1}` (`a^tr`);
- `L0`: top order `> N_{p+1}`, and each child of the root has `≤ N_{p+1}` below it (`ℒ₀`, T L2312). -/
def TreeKindOK (p Ntr : ℕ) : TreeKind → Prop
  | .tr => ∀ j, LG.topOrder p j ≤ Ntr
  | .L0 => ∀ j, Ntr < LG.topOrder p j ∧ ∀ b : GBranch LG.garden.tree, b.1 = (j, []) →
      ∀ i : Fin 3, LG.topCountBelow p (b.child i) ≤ Ntr

end LayeredGarden

/-! ## §3 The sums -/

open Classical in
/-- **The flower sum** (corrects `truncSumHζ`; T (flowerexp2), L2287–L2290; F39, F46/D1, R8). It sums
`kernelKgen` over the layered flower gardens `𝒢` of width `w` and order `N` such that:
- `𝒢 ∈ ℋ_{p+1}` (stems in layer `p`);
- the attached gardens have order `≤ N_p`;
- the initial flower trees are of kind `kind`;
- the flower signs are `ζ · ζ_j`;
- each tree's pattern is valid.

The kernel data:
- flower parents ↦ `s`, plus the pattern's node;
- the phases at the flower parents removed if `dagger` is given;
- the weights: `M₁` cutoff (index `cut1`), `M₂` cutoff (`cut2`), sibling labels (`dagger`);
- `(n, n')`-decorations: roots `n`, flowers `n'`. -/
noncomputable def flowerSum (P : WTParams) (F : ℕ → Mom P.d → ℝ) (p N : ℕ) {w : ℕ}
    (kind : FlowerKind) (pat : Fin w → FixPat) (dagger : Option (Fin w → Fin 3 → Mom P.d))
    (cut1 cut2 : Option ℕ) (ζ : ℤˣ) (t s : ℝ) (n n' : Fin P.d → ℤ) : ℂ :=
  ∑ᶠ (LG : LayeredGarden w) (_ : IsCanonH (p + 1) LG ∧
      (∀ u ∈ LG.attachNodes p, LG.attachedOrder p u ≤ P.N p) ∧ LG.garden.order = N ∧
      LG.FlowerKindOK p (P.N (p + 1)) kind ∧
      (∀ ℓ : GLeaf LG.garden.tree, LG.garden.IsFlower ℓ →
        LG.garden.sign ℓ.toNode = ζ * LG.garden.sig ℓ.1.1) ∧
      ∀ j, LG.PatValid p j (pat j)),
    kernelKgen P.L P.γ P.δ F LG (LG.fixPat pat t s)
      (if dagger.isSome then Finset.univ.filter LG.garden.IsFlowerParent else ∅)
      (fun k => (cut1.elim 1 fun j₁ => LG.cutWeight1 p P.L j₁ k) *
        (cut2.elim 1 fun j₂ => LG.cutWeight2 P.L j₂ k) * (dagger.elim 1 fun c => LG.sibWeight c k))
      (fun _ => t) 0 (fun _ => n) n'

open Classical in
/-- **The restricted couple sum** (T L2312). It sums over the couples `𝒬 ∈ 𝒞_{p+1}` of order `N`
with attached gardens of order `≤ N_p` and trees of kind `kind`. With `dt`, the roots are layer-`p`
branching nodes and have time `t` (`δ(t_𝔯 − t)` of `∂_t`). The root vector is `k ∈ ℝ^d`, as in `KQ`.
Without `dt` and with kind `tr` this is `truncSumC` (bridge in the probes).

The roots must be in layer `p` (F78). The term `δ(t_𝔯 − t)` comes from `∂_t` of the tree expansion, whose roots
are top-layer branching nodes; `∂_t 𝒥_• = 0`. So a couple whose top tree is trivial, with a lower-layer garden
attached at its root, is excluded. -/
noncomputable def coupleSum (P : WTParams) (F : ℕ → Mom P.d → ℝ) (p N : ℕ) (kind : TreeKind)
    (dt : Bool) (t : ℝ) (k : Mom P.d) : ℂ :=
  ∑ᶠ (LG : LayeredGarden 2) (_ : IsCanonC (p + 1) LG ∧
      (∀ u ∈ LG.attachNodes p, LG.attachedOrder p u ≤ P.N p) ∧ LG.garden.order = N ∧
      LG.TreeKindOK p (P.N (p + 1)) kind ∧
      (dt = true → ∀ j : Fin 2, ∃ b : GBranch LG.garden.tree, b.1 = (j, []) ∧ LG.layer b.toNode = p)),
    kernelKgen P.L P.γ P.δ F LG (fun b => if dt = true ∧ b.1.2 = [] then some t else none) ∅
      (fun _ => 1) (fun _ => t) k (fun _ => 0) 0

/-! ## §4 B1.12 -/

/-- The prefix `(Π_P)` of `flowerest1` (T L2279–L2280). It is `(Π)` with the moment order `P` chosen after `ν`
("large depending on `C₁`") and before `δ` ("`δ` small depending on `P`"). -/
def WTPrefixP (Q : ℕ → WTParams → Prop) : Prop :=
  ∀ d : ℕ, 3 ≤ d → ∀ γ : ℝ, γ ∈ Ioo (0 : ℝ) 1 →
  ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, η ∈ Ioc 0 η₀ →
  ∀ φin : SchwartzMap (Mom d) ℝ, (∀ k, 0 ≤ φin k) →
  ∀ τstar : ℝ, 0 < τstar → ∀ φ : ℝ → SchwartzMap (Mom d) ℝ, IsWKESolution φin τstar φ →
  ∃ C₁ : ℝ, 1 ≤ C₁ ∧ ∃ ν₀ : ℝ, 0 < ν₀ ∧ ∀ ν : ℝ, ν ∈ Ioc 0 ν₀ →
  ∃ P₀ : ℕ, ∀ Pm : ℕ, P₀ ≤ Pm →
  ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, δ ∈ Ioc 0 δ₀ → ∀ D : ℕ, 1 ≤ D → τstar = D * δ →
  ∃ C₂ : ℝ, 1 ≤ C₂ ∧ ∃ L₀ : ℝ, 2 ≤ L₀ ∧ ∀ L : ℝ, L₀ ≤ L →
  Q Pm ⟨d, γ, η, φin, τstar, φ, C₁, ν, δ, D, C₂, L⟩

open Classical in
/-- **B1.12 `layergardenFlower`** (T Prop `flowerest1`, L2279–L2305, deterministic core; T L2306–L2338 for
its uses; review G-1, stage-3 R8, WAVE-B v2 §4.15).

Setting: `(Π_P)`, `0 ≤ p < 𝔇`, remainders as in B1.2, inputs `F_q = φ(δq) + R_q`.

**(1) Flower gardens of width `2P`.** For `p < s < t < p+1` (T's range for the flower kernels, L2263),
`n, n' ∈ ℤ^d`, `ζ`, `N ≤ N_{p+1}^4`, every kind (`𝒳`, `𝒴`, `𝒲`), every pattern vector, with or without `†`
and the cutoffs:

  `|flowerSum| ≤ ⟨k − ζk'⟩^{−4Λ_{p+1}P} L^{c(100d)³P} δ^{2νN} · M₁^{−80dP} · M₂^{−P/9}`

- `c = 1` if all patterns are plain, `c = 2` otherwise.
- The `M₁` factor is present iff the `M₁` cutoff is, also for derivative patterns.
- The `M₂` factor is present iff the `M₂` cutoff is and all patterns are plain. The `M₂` cutoff requires the
  `M₁` cutoff and `|k| ≥ M₁^{10}`.

**(2) Couples.** For `p < t < p+1`, `k ∈ ℝ^d`, `N ≤ N_{p+1}^4`, kind `ℒ₀`, or kind `a^tr` with `∂_t`:

  `|coupleSum| ≤ ⟨k⟩^{−4Λ_{p+1}} L^{100d} δ^{νN}`

**Uses.**
- The `𝒴`/`𝒲` gain `e^{−100N_{p+1}}` (T L2280) comes from summing over `N ≥ 2P(N_{p+1}+1)`, the kinds'
  lower bound.
- The bounds of (1) give T (flowerest2) with its cutoff variants, and T (newnormn) with the `∂_{t,s}` terms
  of (sobolev2), T L2331.
- Those of (2) give (trterm1) for `ℒ₀`, and for `∂_t a^tr`, `∂_t ℒ₀` with an extra `L^{100d}` (T L2312).

**Deviations** (FLOWER-DESIGN.md):
- (D1) The moment expansions `𝔼_p|𝒦|^{2P} = ∑ + errors` are left to T.flowerest1 and T.fp.part1. This gate
  is their deterministic core.
- (D2) Per-order bounds with `δ^{2νN}` (flowers) and `δ^{νN}` (couples).
- (D3) Range `N ≤ N_{p+1}^4` (T L2290).
- (D4) Prefactor `L^{d−γ}` (F25).
- (D5) Kind `𝒳` excludes the trivial flower tree (F39).
- (D6) `𝒴`/`𝒲` replace the top bound (F46).
- (D7) Explicit dyadic cutoffs.
- (D8) The derivative patterns and `†` as designated nodes, removed phases and weights (R8).
- (D9) `L^{2(100d)³P}` for derivative patterns.
- (D10) The couple clause covers `ℒ₀`, which B1.2 does not.
- (D11) Per-tree choices: the `†` labels `c j` and the patterns `pat j` may differ between the trees `j` of
  the garden. The consumer uses one uniform choice, so this is more general than `fixedpoint` needs (the
  proof is per tree). -/
theorem layergardenFlower : WTPrefixP fun Pm P =>
    ∀ p : ℕ, p < P.D → ∀ R : ℕ → Mom P.d → ℝ, RemainderBound P R p →
    (∀ t ∈ Ioo (p : ℝ) (p + 1), ∀ s ∈ Ioo (p : ℝ) t, ∀ n n' : Fin P.d → ℤ, ∀ ζ : ℤˣ,
      ∀ N ≤ P.N (p + 1) ^ 4, ∀ (kind : FlowerKind) (pat : Fin (2 * Pm) → FixPat)
        (dagger : Option (Fin (2 * Pm) → Fin 3 → Mom P.d)) (cut1 cut2 : Option ℕ),
        (∀ j₂ ∈ cut2, ∃ j₁ ∈ cut1, ((2 : ℝ) ^ j₁ * P.L) ^ 10 ≤ ‖latticePoint P.L n‖) →
        ‖flowerSum P (inputsF P R) p N kind pat dagger cut1 cut2 ζ t s n n'‖ ≤
          jbr (latticePoint P.L n - (ζ : ℤ) • latticePoint P.L n') ^
              (-(4 * P.Lambda (p + 1) * Pm : ℝ)) *
            P.L ^ ((if ∀ j, pat j = .plain then 1 else 2) * (100 * P.d : ℝ) ^ 3 * Pm) *
            P.δ ^ (2 * P.ν * N) *
            (cut1.elim 1 fun j₁ => ((2 : ℝ) ^ j₁ * P.L) ^ (-(80 * P.d * Pm : ℝ))) *
            (cut2.elim 1 fun j₂ =>
              if ∀ j, pat j = .plain then ((2 : ℝ) ^ j₂ * P.L) ^ (-(Pm / 9 : ℝ)) else 1)) ∧
    (∀ t ∈ Ioo (p : ℝ) (p + 1), ∀ k : Mom P.d, ∀ N ≤ P.N (p + 1) ^ 4, ∀ (kind : TreeKind)
        (dt : Bool), (kind = .tr → dt = true) →
        ‖coupleSum P (inputsF P R) p N kind dt t k‖ ≤
          jbr k ^ (-(4 * P.Lambda (p + 1) : ℝ)) * P.L ^ (100 * P.d : ℝ) * P.δ ^ (P.ν * N)) := by
  sorry

end WaveTurbulence

```
