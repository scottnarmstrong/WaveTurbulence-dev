/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.CapsGlue.Select
/-! # A3a CAPS-GLUE: stem filters and selected-face weights of a glue are products over the components -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.CapsGlue
open TTree Finset WaveTurbulence WaveTurbulence.FlowerP7 WaveTurbulence.Flower.MkDefs

variable {m w d : ℕ} {a : Fin m → ℕ}

/-- Restriction of a decoration of the glue to component `c`. -/
def resK (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (TA : ∀ c, Fin (a c) → TTree)
    (k : GNode (gT σ TA) → Mom d) (c : Fin m) : GNode (TA c) → Mom d :=
  fun x => k (glueNodeN σ TA ⟨c, x⟩)

theorem omega_glueN_any (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (LA : ∀ c, LayeredGarden (a c))
    (k : GNode (glueL σ LA).garden.tree → Mom d) (c : Fin m) (x : GBranch (LA c).garden.tree) :
    omegaNode (glueL σ LA).garden k (glueBranchN σ (fun c => (LA c).garden.tree) ⟨c, x⟩) =
      omegaNode (LA c).garden (resK σ (fun c => (LA c).garden.tree) k c) x := by
  unfold omegaNode resK
  rw [glueBranchN_child, glueBranchN_child, glueBranchN_child, glueBranchN_toNode]

theorem omega_glueN_any' (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (LA : ∀ c, LayeredGarden (a c))
    (k : GNode (glueL σ LA).garden.tree → Mom d) (c : Fin m) (x : GBranch (LA c).garden.tree) :
    omegaNode (glueGardenN σ fun c => (LA c).garden) k
      (glueBranchN σ (fun c => (LA c).garden.tree) ⟨c, x⟩) =
      omegaNode (LA c).garden (resK σ (fun c => (LA c).garden.tree) k c) x :=
  omega_glueN_any σ LA k c x

theorem prodDyadicCut_map {ι ι' : Type*} (L : ℝ) (j : ℕ) (e : ι ↪ ι') (s : Finset ι) (y : ι' → ℝ) :
    prodDyadicCut L j (s.map e) y = prodDyadicCut L j s (fun x => y (e x)) := by
  unfold prodDyadicCut
  split_ifs <;> simp [Finset.prod_map]

theorem stemFilterCap_glueN (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (LA : ∀ c, LayeredGarden (a c))
    (J : Finset (Fin w)) (L : ℝ) (sg : Fin w → Option ℕ) (k : GNode (glueL σ LA).garden.tree → Mom d) :
    stemFilterCap (glueL σ LA) J L sg k =
      ∏ c, stemFilterCap (LA c) (resJ σ J c) L (resF σ sg c) (resK σ (fun c => (LA c).garden.tree) k c) := by
  unfold stemFilterCap
  rw [← σ.prod_comp, Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun c _ => Finset.prod_congr rfl fun i _ => ?_
  rcases hs : sg (σ ⟨c, i⟩) with _ | n
  · simp [resF, hs]
  · simp only [resF, hs, Option.elim_some]
    rw [stemSetCap_glueN, prodDyadicCut_map]
    simp only [embBr_apply, omega_glueN_any']

theorem selWeightCap_glueN (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (LA : ∀ c, LayeredGarden (a c))
    (J : Finset (Fin w)) (kSel : Fin w → Option ℕ) (Rs : Fin w → ℝ)
    (k : GNode (glueL σ LA).garden.tree → Mom d) :
    selWeightCap (glueL σ LA) J (selCap (glueL σ LA) J kSel) Rs k =
      ∏ c, selWeightCap (LA c) (resJ σ J c) (selCap (LA c) (resJ σ J c) (resF σ kSel c)) (resF σ Rs c)
        (resK σ (fun c => (LA c).garden.tree) k c) := by
  unfold selWeightCap
  rw [← σ.prod_comp, Fintype.prod_sigma]
  refine Finset.prod_congr rfl fun c _ => Finset.prod_congr rfl fun i _ => ?_
  rw [selCap_glueN]
  rcases hv : selCap (LA c) (resJ σ J c) (resF σ kSel c) i with _ | u
  · rfl
  · simp only [Option.map_some, Option.elim_some, resF]
    rw [stemSetCap_glueN, ← Finset.map_erase, Finset.prod_map]
    simp only [embBr_apply, omega_glueN_any']

end WaveTurbulence.Flower.CapsGlue
