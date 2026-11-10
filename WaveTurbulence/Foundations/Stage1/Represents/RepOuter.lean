/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Stage1.Represents.RepAsm2

/-!
# S2 REPRESENTS: the outer form of a vine piece (interface VINE-B/C → VINE-D)

TARGET (redvine), L1954-L1963: after the skeleton reduction (REGRED-LEAF) and the splitting of the decorations and times
of `G_sk` at the units `U_j` of `𝒱₀`, a σ-restricted class sum is
`(δ/2L^{d-γ})^{n_sb} ζ(G_sb) Σ_{I_sb} ε̃ Z ∫_{I_sb} Π_n e^{πiζΩt} · Π K*_Q · Π K*_T · Π_j K̃^{U_j}(t_{u1}, t_{u21}, t_{u22}; k_{u1}, k_{u11}, k_{u21}, k_{u22})`.

`outerVal` is this expression on the spliced garden `G = G_sb`, with
* `Zw z` the selection weight (`Z`, the SG/LG/ZG indicator, a function of the `G_sb` decoration only, L1963);
* `splicedEpsilon G hinges` (`ε̃`: the epsilon factors of all non-hinge branches, L1962 (i));
* the FULL phase product `phaseProd` of `G_sb` (the phase at a hinge `u1^j` is cancelled by the recentering factor of
  `K̃^{U_j}`, L1963 "exactly cancels"), over `splicedTimeDomain G layer tt` (unit layer boxes, parent order, root
  truncation F-TT);
* the outer slot kernels `Fn s` at the replacement slots of `G_sb` (regular couples at pairs, regular trees at branches,
  including the tree `T_(u1)` at a hinge), at the slot clocks `slotTs` and the slot momentum `slotNode`;
* for each unit `j : J`, the vine factor `Hk j` at the three clocks `hclk j` (`t_{u1}`, `t_{u21}`, `t_{u22}`; a leaf
  boundary child gets any clock, it is unused) and the four node momenta `hmom j` (`k_{u1}, k_{u11}, k_{u21}, k_{u22}`, in
  the order of `RegRed.clBoundaryNodes`).

The vine piece of a τ-class `T` with prescription `σ` is (VINE-C):
`Σ_{LG ∈ T} U.toLF.valueSel tt base roots LG (sel LG) = Σ_i U.sign i · outerVal … (Fn_i) … (Hk_i)` with
`Fn_i s = slotFn D hS L γ δ (typeProfiles LG₀ (U.h i)) layer hLayer (ι s)` (`ι` the slot embedding `G_sb → G_sk`) and
`Hk_i j = twistedRecentered S (u_j.upper) (canonFinsetK p kind (startState B_j D hS layer hLayer) (chainStart B_j))
  L γ δ (fun q => U.h i q j₁ j₁) base`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.Represents
open Finset TTree Reg Reg.Skeleton WaveTurbulence WaveTurbulence.LGSpine MeasureTheory

variable {w d : ℕ}

/-- **The outer form of a vine piece** (TARGET (redvine), L1954-L1963; interface VINE-B/C → VINE-D). -/
noncomputable def outerVal (G : Garden w) (hS : G.IsPlain) (L γ δ : ℝ) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) (tt : Fin w → ℝ) (layer : GBranch G.tree → ℕ)
    (hinges : Finset (GBranch G.tree)) (Zw : GenDecoration G d roots 0 → ℝ)
    (Fn : ReplacementSlot G → (Fin 2 → ℝ) → Mom d → ℂ)
    {J : Type} [Fintype J] (hclk : J → Fin 3 → ClkSrc G) (hmom : J → Fin 4 → GNode G.tree)
    (Hk : J → (Fin 3 → ℝ) → (Fin 4 → Mom d) → ℂ) : ℂ :=
  (coupling d L γ δ : ℂ) ^ G.order * G.zeta *
    ∑' z : GenDecoration G d roots 0, (splicedEpsilon G hinges z.1 : ℂ) * (Zw z : ℂ) *
      ∫ τ : GBranch G.tree → ℝ, (splicedTimeDomain G layer tt).indicator (fun τ =>
        phaseProd L γ δ G (cosetDecoration G L base z.1) τ *
          (∏ s, Fn s (slotTs hS tt τ s) (base + latticePoint L (z.1 (slotNode hS s)))) *
          ∏ j, Hk j (fun c => clockOf G tt τ (hclk j c)) (fun c => base + latticePoint L (z.1 (hmom j c)))) τ

end WaveTurbulence.Represents
