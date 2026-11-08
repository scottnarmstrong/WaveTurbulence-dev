/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Flower.MkDefs.Stage1MK
public import WaveTurbulence.Foundations.Flower.LadFilt.Defs
public import WaveTurbulence.Foundations.FlowerTop.Port.SplicedKernelST

/-! # C2 FINALMK-CRUDE: statements

Probe `FinalMKProbe.lean` (current on-disk version, R158) lines 573-662, copied by source (sha256 in
`COPIED-SHA256SUMS`); only namespace and open lines differ. `filterB` is C3's `LadFilt.filterB`; the B0 vocabulary
(`SplicedKernelDataMK`, `splicedKernelMK`) is imported from `MkDefs.Stage1MK`. -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.Induct Set Finset MeasureTheory
open scoped Classical ENNReal

namespace WaveTurbulence.Flower.FinalMKDefs
open WaveTurbulence.LGSpine.SourceVine
open WaveTurbulence.Flower.MkDefs (SplicedKernelDataMK splicedKernelMK splicedTimeIntegralMK)
open WaveTurbulence.Flower.LadFilt (LadderL1AtFilt filterB)

/-- Admissible atom weights (S-MARKED `AtomOK`, `lb` gone): filters only at non-hinge atoms, scale `≥ 1`, `|ψ| ≤ 1`,
`𝔟 ψ ≤ cθ`; indicators in `[0,1]` depending only on the bonds at the atoms of `prot`. -/
def AtomOK {w d : ℕ} {G : Garden w} (D : SplicedKernelDataMK G d)
    (prot : Finset (GBranch G.tree)) (cθ : ℝ) : Prop :=
  (∀ a q, D.filt a = some q → a ∉ D.hinges ∧ 1 ≤ q.1 ∧ (∀ u, ‖q.2 u‖ ≤ 1) ∧ filterB ⇑q.2 ≤ cθ) ∧
  (∀ k, 0 ≤ D.ind k ∧ D.ind k ≤ 1) ∧
  ∀ k k', (∀ a ∈ prot, ∀ i : Fin 3, k (a.child i) = k' (a.child i) ∧ k a.toNode = k' a.toNode) → D.ind k = D.ind k'

/-- The world's piece filters use `MkDefs.filterB`, C3's gate `LadFilt.filterB`: the same definition [proved]. -/
theorem filterB_eq_ladFilt : MkDefs.filterB = WaveTurbulence.Flower.LadFilt.filterB := rfl

/-! ### C2: the crude bound (finalsbest1′, o75 Theorem 7.5′(8)) -/

/-- The geometric premises that main's coarse proof actually uses (`coarse_fixed` reads only these four fields of
`SplicedSourcePremises`; no subpro support, so survivors do not enter the crude bound). -/
structure SplicedGeomPremises {R : ℕ} (G : Garden (2 * R)) : Prop where
  molecule : G.molecule.IsMolecule
  connected : G.molecule.IsConnected
  atom_count : G.molecule.atoms.card = G.order
  bond_count : G.molecule.bonds.card + R = 2 * G.order

theorem SplicedSourcePremises.toGeom {R : ℕ} {P : WTParams} {G : Garden (2 * R)} {D : SplicedKernelData G P.d}
    {base : Mom P.d} {roots : Fin (2 * R) → (Fin P.d → ℤ)} (h : SplicedSourcePremises P G D base roots) :
    SplicedGeomPremises G := ⟨h.molecule, h.connected, h.atom_count, h.bond_count⟩

/-- **C2 target `CoarseSplicedAtMK`** (o75 (finalsbest1′)): pins `fix` at any times, Schwartz filters (C3's
`filterB ≤ cθ`), dagger indicators local at `split`; maximal ladders split at `hinges ∪ split` (`split ⊇` pins; the
consumer takes `split = B ∪ Π_sb`). Cost `cθ` per atom, `80d` per split atom (o75: `60d+2`). -/
abbrev CoarseSplicedAtMK (P : WTParams) : Prop :=
  ∀ p : ℕ, p < P.D → ∀ R : ℕ, 1 ≤ R → R ≤ 10 * P.R (p + 1) →
  ∀ G : Garden (2 * R), G.IsPlain → G.Irreducible → IsBalancedSig G.sig →
    1 ≤ G.order → G.order ≤ P.N (p + 1) ^ 4 →
  ∀ (D : SplicedKernelDataMK G P.d) (split : Finset (GBranch G.tree)) (cθ : ℝ), 1 ≤ cθ →
    SplicedAmplitudeBounds G D.toSplicedKernelData → (∀ v, D.layer v ≤ p) → AtomOK D split cθ →
    (∀ b, (D.fix b).isSome → b ∈ split) →
  ∀ (A : SourceMaximalLadderData G) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)),
    SplicedGeomPremises G →
    ‖splicedKernelMK G D P.L P.γ P.η P.δ base roots‖ ≤
      P.C₂ * (cθ * P.C₁ * Real.sqrt P.δ) ^ G.order *
        P.L ^ (-P.η * A.totalIncoherency D.layer + 80 * P.d * (G.molecule.rho + (D.hinges ∪ split).card))

/-- **The C2 deliverable**, from C3's `ladderL1GateFilt : WTPrefix LadderL1AtFilt`. -/
abbrev CoarseSplicedGateMK : Prop := WTPrefix CoarseSplicedAtMK

/-- Unmarked data as marked data (no pins, no filters, indicator `1`, no lower bounds). -/
def toMKData {w d : ℕ} {G : Garden w} (D : SplicedKernelData G d) : SplicedKernelDataMK G d :=
  { D with fix := fun _ => none, filt := fun _ => none, ind := fun _ => 1 }

theorem splicedTimeIntegralMK_toMK {w d : ℕ} {G : Garden w} (D : SplicedKernelData G d) (L γ δ : ℝ) (base : Mom d)
    (z : GNode G.tree → (Fin d → ℤ)) :
    splicedTimeIntegralMK G (toMKData D) L γ δ base z = splicedTimeIntegral G D L γ δ base z := by
  rw [MkDefs.splicedTimeIntegralMK_lb_none G (toMKData D) rfl]
  unfold splicedTimeIntegral
  have hfix : ∀ b, (toMKData D).fix b = none := fun _ => rfl
  have hdom : splicedTimeDomainFix G (toMKData D).layer (toMKData D).rootTime (toMKData D).fix =
      splicedTimeDomain G D.layer D.rootTime := by
    ext t
    simp only [splicedTimeDomainFix, splicedTimeDomain, toMKData, true_or, forall_const, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨fun v => (h1 v).1, h2, fun v => (h1 v).2⟩
    · rintro ⟨h1, h2, h3⟩
      exact ⟨fun v => ⟨h1 v, h3 v⟩, h2⟩
  have key := integral_pi_subtype_univ (Q := fun b : GBranch G.tree => (toMKData D).fix b = none) hfix
    (fun t => (splicedTimeDomain G D.layer D.rootTime).indicator
      (fun t => phaseProd L γ δ G (cosetDecoration G L base z) t *
        ∏ v : GBranch G.tree, Complex.exp ((Real.pi * D.frequency v * t v : ℝ) * Complex.I)) t)
  rw [← key]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun τ => ?_)
  simp only
  rw [extendFix_of_none G _ hfix τ, hdom]
  rfl

theorem splicedKernelMK_toMK {w d : ℕ} {G : Garden w} (D : SplicedKernelData G d) (L γ η δ : ℝ) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) :
    splicedKernelMK G (toMKData D) L γ η δ base roots = splicedKernel G D L γ η δ base roots := by
  unfold splicedKernelMK splicedKernel
  congr 1
  refine tsum_congr fun z => ?_
  rw [splicedTimeIntegralMK_toMK]
  simp [SplicedKernelDataMK.atomW, toMKData]

/-- **Non-vacuity bridge (proved)**: `CoarseSplicedAtMK` gives main's `CoarseSplicedAt`. -/
theorem coarseSplicedAt_of_MK (P : WTParams) (h : CoarseSplicedAtMK P) : CoarseSplicedAt P := by
  intro p hp R hR hRmax G hpl hir hbal hn hnmax D hD hlay A base roots hprem
  have hok : AtomOK (toMKData D) ∅ 1 :=
    ⟨fun a q hq => by simp [toMKData] at hq, fun k => by simp [toMKData], fun k k' _ => rfl⟩
  have := h p hp R hR hRmax G hpl hir hbal hn hnmax (toMKData D) ∅ 1 le_rfl hD hlay hok
    (fun b hb => by simp [toMKData] at hb) A base roots (SplicedSourcePremises.toGeom hprem)
  rw [splicedKernelMK_toMK] at this
  simpa [toMKData] using this

end WaveTurbulence.Flower.FinalMKDefs
