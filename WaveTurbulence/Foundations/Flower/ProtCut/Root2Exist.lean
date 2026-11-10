/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtCut.Root2Ker
public import WaveTurbulence.Foundations.Flower.ProtCut.CheckNil
public import WaveTurbulence.Foundations.Spine.PL234Draft.SliceAlgebra

/-! # D2c-3 PROT-CUT: the pieces of o104 Prop 7.4 (a) for couples exist; branch-local multipliers factor

* **`Root2Data.exists_of_decodes`**: a well-formed `type2 (pair m Qr Qg inner rest) Xm Qlp` decoding a layered couple
  `LG` has its closing pair `LGZ` and rest couple `LGB` with the layers of `LG`; `PairOnly.exists_of_wf` then gives
  the pieces of the closing pair.
* **`Root2Data.multFactors_local`**: `K ↦ ∏_b f b (bstar K b)` satisfies the hypotheses `hMg` (glue) and `hMZ`
  (`PairOnly.MultFactors`) of `kernelProt_root2`, with explicit factors. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset

namespace WaveTurbulence.Flower.ProtCut

open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234
open WaveTurbulence.Flower.ProtDefs

namespace Root2Data

variable {LG : LayeredGarden 2} {m : MiniTreeCode} {Qr Qg : RegCpl} {inner : RegChain}
  {LGZ : LayeredGarden 1} {LGB : LayeredGarden 2} (D : Root2Data LG m Qr Qg inner LGZ LGB)
  {LGi : LayeredGarden 1} {LGr LGg : LayeredGarden 2} (P : PairOnly LGZ m Qr Qg inner LGi LGr LGg)
include D P

/-- **A branch-local multiplier satisfies the hypotheses of `kernelProt_root2`.** -/
theorem multFactors_local {d : ℕ} (f : GBranch LG.garden.tree → (Fin 4 → Mom d) → ℂ) :
    (∀ K, (∏ b, f b (bstar K b)) = (fun K' => ∏ x, f (D.gd.ofSum (.inl x)) (bstar K' x)) (K ∘ D.gd.ι₁) *
        (fun K' => ∏ y, f (D.gd.ofSum (.inr y)) (bstar K' y)) (K ∘ D.gd.ι₂)) ∧
      P.MultFactors (fun K' => ∏ x, f (D.gd.ofSum (.inl x)) (bstar K' x))
        (fun A B => f (D.gd.ofSum (.inl P.hp.rootB)) A * f (D.gd.ofSum (.inl P.hp.bB)) B)
        (fun K => ∏ x, f (D.gd.ofSum (.inl (P.hp.βi x))) (bstar K x))
        (fun K => ∏ y, f (D.gd.ofSum (.inl (P.hp.βr y))) (bstar K y))
        (fun K => ∏ y, f (D.gd.ofSum (.inl (P.hp.βg y))) (bstar K y)) := by
  refine ⟨fun K => ?_, P.multFactors_local (fun x => f (D.gd.ofSum (.inl x)))⟩
  rw [D.gd.prod_branch]
  have hl : ∀ x, bstar K (D.gd.ofSum (.inl x)) = bstar (K ∘ D.gd.ι₁) x := by
    intro x; funext i
    refine Fin.cases rfl (fun j => ?_) i
    show K ((D.gd.ofSum (.inl x)).child j) = K (D.gd.ι₁ (x.child j))
    rw [D.gd.ofSum_inl_child]
  have hr : ∀ y, bstar K (D.gd.ofSum (.inr y)) = bstar (K ∘ D.gd.ι₂) y := by
    intro y; funext i
    refine Fin.cases rfl (fun j => ?_) i
    show K ((D.gd.ofSum (.inr y)).child j) = K (D.gd.ι₂ (y.child j))
    rw [D.gd.ofSum_inr_child]
  simp only [hl, hr]

end Root2Data

end WaveTurbulence.Flower.ProtCut
