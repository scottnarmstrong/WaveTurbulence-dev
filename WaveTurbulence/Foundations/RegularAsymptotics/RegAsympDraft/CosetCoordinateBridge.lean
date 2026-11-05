/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.PhaseCoordinates
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.SourceMomentumBridge

/-! # Actual coset lattice decorations equal the continuous C2 coordinates -/

@[expose] public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open Links

/-- Translate the actual root-zero integer decoration into its real coset. -/
def cosetDecR {G : Garden 2} {Q : RegCpl} (hQ : Q.Decodes G) (hG : IsCouple G)
    (d : ℕ) (θ : Fin Q.links.length → (Fin d → ℤ) × (Fin d → ℤ)) (L : ℝ) (k : Mom d) :
    DecR G (Mom d) k :=
  let κ := ((integerLinkEquiv hQ hG d).symm θ)
  ⟨cosetDecoration G L k κ.val,isDecoration_coset κ.property.1 L k,fun i => by
    change k+latticePoint L (κ.val (GNode.root G.tree i)) = k
    rw [κ.property.2.1 i]
    have hz : latticePoint L (0 : Fin d → ℤ) = 0 := by ext j; simp [latticePoint]
    rw [hz,add_zero]⟩

/-- The physical free parameters are exactly the scaled independent integers. -/
theorem decParams_cosetDecR {G : Garden 2} {Q : RegCpl} (hQ : Q.Decodes G) (hG : IsCouple G)
    (d : ℕ) (θ : Fin Q.links.length → (Fin d → ℤ) × (Fin d → ℤ)) (L : ℝ) (k : Mom d) :
    decParams hQ (cosetDecR hQ hG d θ L k) =
      fun j => (latticePoint L (θ j).1,latticePoint L (θ j).2) := by
  funext j
  let κ := ((integerLinkEquiv hQ hG d).symm θ)
  have hp := congrFun (integerLinkEquiv_symm_params hQ hG d θ) j
  apply Prod.ext
  · change xv (extend (cosetDecoration G L k κ.val)) (chosenBranch hQ j).val = _
    rw [xv_extend]
    rw [xNode_coset]
    have hx := congrArg Prod.fst hp
    change xv (extend κ.val) (chosenBranch hQ j).val = (θ j).1 at hx
    rw [xv_extend] at hx
    exact congrArg (latticePoint L) hx
  · change yv (extend (cosetDecoration G L k κ.val)) (chosenBranch hQ j).val = _
    rw [yv_extend]
    rw [yNode_coset]
    have hy := congrArg Prod.snd hp
    change yv (extend κ.val) (chosenBranch hQ j).val = (θ j).2 at hy
    rw [yv_extend] at hy
    exact congrArg (latticePoint L) hy

/-- The lattice-kernel leaves and the real-coordinate localization leaves
are literally the same decoration, by the proved C2 equivalence. -/
theorem cosetDecoration_integerLinkEquiv_eq_decOfParams {G : Garden 2} {Q : RegCpl}
    (hQ : Q.Decodes G) (hG : IsCouple G) (d : ℕ)
    (θ : Fin Q.links.length → (Fin d → ℤ) × (Fin d → ℤ)) (L : ℝ) (k : Mom d) :
    cosetDecoration G L k ((integerLinkEquiv hQ hG d).symm θ).val =
      (decOfParams hQ k (fun j => (latticePoint L (θ j).1,latticePoint L (θ j).2))).val := by
  have hh : cosetDecR hQ hG d θ L k =
      decOfParams hQ k (fun j => (latticePoint L (θ j).1,latticePoint L (θ j).2)) := by
    apply (decEquiv hQ hG k).injective
    exact (decParams_cosetDecR hQ hG d θ L k).trans
      (decParams_decOfParams hQ hG k _).symm
  exact congrArg Subtype.val hh

end WaveTurbulence.RegAsymp
