/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.ZpSurj.Coherent1

/-! # ZP-SURJ: conjugation is an involution (codes and layered gardens) -/

@[expose] public section
variable {rowSelU : Unit} [rowSel : WaveTurbulence.VineEst.RowSel rowSelU]
set_option autoImplicit false
open WaveTurbulence.Induct
namespace WaveTurbulence.ZpSurj
open TTree WaveTurbulence.Reg WaveTurbulence.Links WaveTurbulence.LGSpine WaveTurbulence.ConjCoh WaveTurbulence.Stage1

mutual
theorem conjCpl_conjCpl : ∀ Q : RegCpl, conjCpl (conjCpl Q) = Q
  | .triv => rfl
  | .type1 c Q₁ Q₂ Q₃ => by
    by_cases hc : c = 0
    · simp [conjCpl, hc, conjCpl_conjCpl]
    · simp [conjCpl, hc, conjCpl_conjCpl]
  | .type2 Xp Xm Qlp => by
    simp [conjCpl, conjChain_conjChain, conjCpl_conjCpl]
termination_by structural Q => Q

theorem conjChain_conjChain : ∀ X : RegChain, conjChain (conjChain X) = X
  | .nil => rfl
  | .pair m Qr Qg inner rest => by
    simp [conjChain, conjCpl_conjCpl, conjChain_conjChain]
termination_by structural X => X
end

theorem conjGarden_refl_refl {w : ℕ} (G : Garden w) :
    conjGarden (conjGarden G (Equiv.refl (Fin w))) (Equiv.refl (Fin w)) = G := by
  cases G with
  | mk sig tree pair mark pp pe ps =>
    simp only [conjGarden, Garden.mk.injEq]
    refine ⟨funext fun j => neg_neg _, rfl, ?_, ?_⟩
    · exact heq_of_eq (funext fun ℓ => rfl)
    · exact heq_of_eq (funext fun ℓ => rfl)

theorem conjLayered_refl_refl {w : ℕ} (L : LayeredGarden w) :
    conjLayered (conjLayered L (Equiv.refl (Fin w))) (Equiv.refl (Fin w)) = L := by
  refine layered_ext (conjGarden_refl_refl L.garden) (fun x => ?_)
  have h1 := layerAt_conj (conjLayered_isConjugateBy (conjLayered L (Equiv.refl (Fin w))) (Equiv.refl (Fin w))) x
  have h2 := layerAt_conj (conjLayered_isConjugateBy L (Equiv.refl (Fin w))) x
  exact h1.trans h2

end WaveTurbulence.ZpSurj
