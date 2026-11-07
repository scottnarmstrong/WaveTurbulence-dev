/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS4.SplitSummand
public import WaveTurbulence.Foundations.VineEst.VineEstS4.Tw11Data

/-! # V5 Step 4d-B: the S-part with the two exceptional rows split off

`spart = spartFrame * spartExc`, where `spartExc` is the time condition `u b < parentClock (u a) u b`
together with the exceptional rows (the couple row at the pair `p0` of the retained leaf and the tree row at the
lower joint `b`), and `spartFrame` is everything else (TARGET `(tildeJ2)`: the factors that are common to all LF
twists at `p*`).  `qRow`, `tRow` are the individual starred-kernel rows of `starProd`.
-/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5B
open WaveTurbulence WaveTurbulence.VineEstS2 WaveTurbulence.VineEstS4 WaveTurbulence.RegRed
  WaveTurbulence.Reg.Skeleton TTree MeasureTheory

variable {w d : ℕ} {G : Garden w}

section Rows
variable (D : ReconstructionData G) (hG : G.IsPlain) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
  (layer : GNode (D.forest hG) → ℕ) (hLayer : IsLayering (D.garden hG) layer) (base : Mom d)

/-- The starred couple row of a regional pair. -/
@[expose] noncomputable def qRow (top : ℝ) (x : GNode G.tree → (Fin d → ℤ)) (u : GBranch G.tree → ℝ)
    (p : SourcePair G) : ℂ :=
  KQstar L γ δ F (nativeCoupleLayered D hG layer hLayer p)
    (parentClock top u (p.firstLeaf hG).toNode) (parentClock top u (p.secondLeaf hG).toNode)
    (cosetDecoration G L base x (p.firstLeaf hG).toNode)

/-- The starred tree row of an interior branch. -/
@[expose] noncomputable def tRow (top : ℝ) (x : GNode G.tree → (Fin d → ℤ)) (u : GBranch G.tree → ℝ)
    (v : GBranch G.tree) : ℂ :=
  KTstar L γ δ F (nativeChainLayered D hG layer hLayer v)
    (parentClock top u v.toNode) (u v) (cosetDecoration G L base x v.toNode)

theorem starProd_eq_rows (V : Finset (GBranch G.tree)) (a : GBranch G.tree) (top : ℝ)
    (x : GNode G.tree → (Fin d → ℤ)) (u : GBranch G.tree → ℝ) :
    starProd D hG L γ δ F layer hLayer base V a top x u =
      (∏ p ∈ clRegionalPairs hG V, qRow D hG L γ δ F layer hLayer base top x u p) *
        ∏ v ∈ V.erase a, tRow D hG L γ δ F layer hLayer base top x u v := rfl

end Rows

/-- The frame time condition: the windows and the parent-clock conditions of all interior branches, except the
parent-clock condition at `b`. -/
@[expose] def DomF (lay : GBranch G.tree → ℕ) (S : Finset (GBranch G.tree)) (a b : GBranch G.tree)
    (u : GBranch G.tree → ℝ) : Prop :=
  ∀ v ∈ S.erase a, (lay v : ℝ) < u v ∧ u v < lay v + 1 ∧ 0 < u v ∧
    (v ≠ b → u v < parentClock (u a) u v.toNode)

section Split
variable (D : ReconstructionData G) (hG : G.IsPlain) (L γ δ : ℝ) (F : ℕ → Mom d → ℝ)
  (layer : GNode (D.forest hG) → ℕ) (hLayer : IsLayering (D.garden hG) layer) (base : Mom d)

/-- The common frame of the S-part: all rows except the couple row at `p0` and the tree row at `b`. -/
@[expose] noncomputable def spartFrame (S : Finset (GBranch G.tree)) (a b : GBranch G.tree) (p0 : SourcePair G)
    (x : GNode G.tree → (Fin d → ℤ)) (u : GBranch G.tree → ℝ) : ℂ :=
  open Classical in
  (if DomF (fun v => layer (D.coreBranch hG v).toNode) S a b u then 1 else 0) *
    ((clRegionalEpsilon G (S.erase b) x : ℂ) *
      (clRegionalPhase G (S.erase b) L γ δ (cosetDecoration G L base x) u *
        ((∏ p ∈ (clRegionalPairs hG S).erase p0, qRow D hG L γ δ F layer hLayer base (u a) x u p) *
          ∏ v ∈ (S.erase a).erase b, tRow D hG L γ δ F layer hLayer base (u a) x u v)))

/-- The exceptional factor: the parent-clock condition at `b` and the two exceptional rows. -/
@[expose] noncomputable def spartExc (S : Finset (GBranch G.tree)) (a b : GBranch G.tree) (p0 : SourcePair G)
    (x : GNode G.tree → (Fin d → ℤ)) (u : GBranch G.tree → ℝ) : ℂ :=
  open Classical in
  (if u b < parentClock (u a) u b.toNode then 1 else 0) *
    (qRow D hG L γ δ F layer hLayer base (u a) x u p0 * tRow D hG L γ δ F layer hLayer base (u a) x u b)

theorem spart_eq_frame_mul_exc (S : Finset (GBranch G.tree)) (a b : GBranch G.tree) (p0 : SourcePair G)
    (hb : b ∈ S.erase a) (hp0 : p0 ∈ clRegionalPairs hG S)
    (x : GNode G.tree → (Fin d → ℤ)) (u : GBranch G.tree → ℝ) :
    spart D hG L γ δ F layer hLayer base S a b x u =
      spartFrame D hG L γ δ F layer hLayer base S a b p0 x u *
        spartExc D hG L γ δ F layer hLayer base S a b p0 x u := by
  classical
  unfold spart spartFrame spartExc
  rw [starProd_eq_rows, ← Finset.mul_prod_erase _ _ hp0, ← Finset.mul_prod_erase _ _ hb]
  have hdom : DomS (fun v => layer (D.coreBranch hG v).toNode) S a u ↔
      DomF (fun v => layer (D.coreBranch hG v).toNode) S a b u ∧ u b < parentClock (u a) u b.toNode := by
    unfold DomS DomF
    constructor
    · intro h
      exact ⟨fun v hv => ⟨(h v hv).1, (h v hv).2.1, (h v hv).2.2.1, fun _ => (h v hv).2.2.2⟩, (h b hb).2.2.2⟩
    · rintro ⟨h, hbb⟩ v hv
      by_cases hvb : v = b
      · subst hvb
        exact ⟨(h v hv).1, (h v hv).2.1, (h v hv).2.2.1, hbb⟩
      · exact ⟨(h v hv).1, (h v hv).2.1, (h v hv).2.2.1, (h v hv).2.2.2 hvb⟩
  by_cases h1 : DomF (fun v => layer (D.coreBranch hG v).toNode) S a b u <;>
    by_cases h2 : u b < parentClock (u a) u b.toNode
  · have : DomS (fun v => layer (D.coreBranch hG v).toNode) S a u := hdom.mpr ⟨h1, h2⟩
    simp only [if_pos this, if_pos h1, if_pos h2]
    ring
  · have : ¬ DomS (fun v => layer (D.coreBranch hG v).toNode) S a u := fun h => h2 (hdom.mp h).2
    simp only [if_neg this, if_pos h1, if_neg h2]
    ring
  · have : ¬ DomS (fun v => layer (D.coreBranch hG v).toNode) S a u := fun h => h1 (hdom.mp h).1
    simp only [if_neg this, if_neg h1]
    ring
  · have : ¬ DomS (fun v => layer (D.coreBranch hG v).toNode) S a u := fun h => h1 (hdom.mp h).1
    simp only [if_neg this, if_neg h1]
    ring

end Split

end WaveTurbulence.VineEstS5B
