/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.IncohInst.CoupleRoot
public import WaveTurbulence.Foundations.IncohInst.TreeCarrier
public import WaveTurbulence.Foundations.WaveB.FrozenB1

/-! # Exact lattice-decoration equivalences for B2's original kernels -/

public section
noncomputable section
namespace WaveTurbulence.IncohInst
open Incoh Links

/-- Plain source couples have no flower constraint, so the actual kernel subtype is C2's `DecR`. -/
@[expose] def coupleGenDecorationEquiv {G : Garden 2} (hG : IsCouple G) (d : ℕ) :
    GenDecoration G d (fun _ => 0) 0 ≃ DecR G (Fin d → ℤ) 0 where
  toFun κ := ⟨κ.1, κ.2.1, κ.2.2.1⟩
  invFun κ := ⟨κ.1, κ.2.1, κ.2.2, fun ℓ hℓ => by
    have h := hG.1 ℓ
    exact False.elim (by simp [Garden.IsFlower, h] at hℓ)⟩
  left_inv κ := Subtype.ext rfl
  right_inv κ := Subtype.ext rfl

/-- For decoded paired trees there are no flowers either; the only fixed root is C2's root. -/
@[expose] def treeGenDecorationEquiv {G : Garden 1} {X : RegChain} (hX : X.DecodesTree G) (d : ℕ) :
    GenDecoration G d (fun _ => 0) 0 ≃ DecRT G (Fin d → ℤ) 0 where
  toFun κ := ⟨κ.1, κ.2.1, κ.2.2.1 0⟩
  invFun κ := ⟨κ.1, κ.2.1, fun j => by
    have hj : j = 0 := Subsingleton.elim _ _
    simpa only [hj] using κ.2.2, fun ℓ hℓ => by
      have h := hX.2.1 ℓ
      exact False.elim (by
        rw [Garden.IsFlower, h] at hℓ
        split_ifs at hℓ; cases hℓ)⟩
  left_inv κ := Subtype.ext rfl
  right_inv κ := Subtype.ext rfl

/-- Reindexing B2's original integer decorations by precisely its two link coordinates. -/
@[expose] def coupleLatticeEquiv {G : Garden 2} {Q : RegCpl} (hQ : Q.Decodes G) (d : ℕ) :
    GenDecoration G d (fun _ => 0) 0 ≃ (Fin Q.links.length × Fin 2 → Fin d → ℤ) :=
  (coupleGenDecorationEquiv hQ.1 d).trans ((decEquiv hQ hQ.1 0).trans
    { toFun := fun θ j => if j.2 = 0 then (θ j.1).1 else (θ j.1).2
      invFun := fun p j => (p (j, 0), p (j, 1))
      left_inv := by intro θ; funext j; rfl
      right_inv := by intro p; funext j; rcases j with ⟨j, b⟩; fin_cases b <;> rfl })

/-- The analogous exact reindexing for B2's original tree kernel. -/
@[expose] def treeLatticeEquiv {G : Garden 1} {X : RegChain} (hX : X.DecodesTree G) (d : ℕ) :
    GenDecoration G d (fun _ => 0) 0 ≃ (Fin (X.treeLinks (G.sig 0)).length × Fin 2 → Fin d → ℤ) :=
  (treeGenDecorationEquiv hX d).trans ((treeDecEquiv hX 0).trans
    { toFun := fun θ j => if j.2 = 0 then (θ j.1).1 else (θ j.1).2
      invFun := fun p j => (p (j, 0), p (j, 1))
      left_inv := by intro θ; funext j; rfl
      right_inv := by intro p; funext j; rcases j with ⟨j, b⟩; fin_cases b <;> rfl })

end WaveTurbulence.IncohInst
