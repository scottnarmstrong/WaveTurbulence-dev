/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Flower.CapsGlue.Weights3
/-! # A3a CAPS-GLUE: `compValue` of a glue of capped components is the product of the component values

The data `fixCap`, `offCap`, `selOK · markedWeight` of the glued garden are product-shaped over the components (each
reads only its own tree's nodes), so the generic identity `kernelKgen_glueN` applies. -/
@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
namespace WaveTurbulence.Flower.CapsGlue
open TTree Finset WaveTurbulence WaveTurbulence.LGSpine WaveTurbulence.FlowerP7 WaveTurbulence.Flower.MkDefs

variable {m w d : ℕ} {a : Fin m → ℕ}

/-- The decoration weight `selOK · markedWeight` of a (capped) component, as in `CompData.val`. -/
def capWt {w d : ℕ} (LG : LayeredGarden w) (J : Finset (Fin w)) (p : ℕ) (L : ℝ) (kSel : Fin w → Option ℕ)
    (Rf : Fin w → Option ℝ) (sg : Fin w → Option ℕ) (Rs : Fin w → ℝ) (h : ℕ → Fin w → Fin w → Mom d → ℝ)
    (dag : Option (Fin w → Fin 3 → Mom d)) : (GNode LG.garden.tree → Mom d) → ℝ :=
  fun k => selOK LG J kSel * markedWeight LG J p L Rf sg (selCap LG J kSel) Rs h dag k

theorem capWt_glueN (σ : (Σ c : Fin m, Fin (a c)) ≃ Fin w) (LA : ∀ c, LayeredGarden (a c))
    (J : Finset (Fin w)) (p : ℕ) (L : ℝ) (kSel : Fin w → Option ℕ) (Rf : Fin w → Option ℝ)
    (sg : Fin w → Option ℕ) (Rs : Fin w → ℝ) (h : ℕ → Fin w → Fin w → Mom d → ℝ)
    (dag : Option (Fin w → Fin 3 → Mom d)) :
    capWt (glueL σ LA) J p L kSel Rf sg Rs h dag =
      gWt σ (fun c => (LA c).garden.tree) fun c =>
        capWt (LA c) (resJ σ J c) p L (resF σ kSel c) (resF σ Rf c) (resF σ sg c) (resF σ Rs c) (resH σ h c)
          (resDag σ dag c) := by
  funext k
  unfold capWt gWt markedWeight
  rw [selOK_glueN, frontierW_glueN, stemFilterCap_glueN, selWeightCap_glueN, leafProdCap_glueN]
  have hd : (dag.elim 1 fun e => sibWeightCap (glueL σ LA) J e k) =
      ∏ c, (resDag σ dag c).elim 1 fun e => sibWeightCap (LA c) (resJ σ J c) e
        (resK σ (fun c => (LA c).garden.tree) k c) := by
    cases dag with
    | none => simp [resDag]
    | some e => simp [resDag, sibWeightCap_glueN]
  rw [hd]
  simp only [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun c _ => by unfold resK; ring

/-- **The glue identity for `compValue`.** -/
theorem compValue_glueN (P : WTParams) {R0 m : ℕ} {R : Fin m → ℕ}
    (σ : (Σ c : Fin m, Fin (2 * R c)) ≃ Fin (2 * R0)) (LA : ∀ c, LayeredGarden (2 * R c))
    (J : Finset (Fin (2 * R0))) (pat : Fin (2 * R0) → FixPat) (t s : ℝ) (kSel : Fin (2 * R0) → Option ℕ)
    (p : ℕ) (Rf : Fin (2 * R0) → Option ℝ) (sg : Fin (2 * R0) → Option ℕ) (Rs : Fin (2 * R0) → ℝ)
    (h : ℕ → Fin (2 * R0) → Fin (2 * R0) → Mom P.d → ℝ) (dag : Option (Fin (2 * R0) → Fin 3 → Mom P.d))
    (roots : Fin (2 * R0) → (Fin P.d → ℤ))
    (hs : ∀ c, Summable fun κ : GenDecoration (LA c).garden P.d (resF σ roots c) 0 =>
      kgTerm P.L P.γ P.δ (fun _ _ => 1) (LA c) (fixCap (LA c) (resJ σ J c) (resF σ pat c) t s)
        (offCap (LA c) (resJ σ J c) dag.isSome)
        (capWt (LA c) (resJ σ J c) p P.L (resF σ kSel c) (resF σ Rf c) (resF σ sg c) (resF σ Rs c)
          (resH σ h c) (resDag σ dag c)) (fun _ => t) 0 κ.1) :
    compValue P (glueL σ LA) (fixCap (glueL σ LA) J pat t s) (offCap (glueL σ LA) J dag.isSome)
      (capWt (glueL σ LA) J p P.L kSel Rf sg Rs h dag) t roots =
    ∏ c, compValue P (LA c) (fixCap (LA c) (resJ σ J c) (resF σ pat c) t s)
      (offCap (LA c) (resJ σ J c) dag.isSome)
      (capWt (LA c) (resJ σ J c) p P.L (resF σ kSel c) (resF σ Rf c) (resF σ sg c) (resF σ Rs c)
        (resH σ h c) (resDag σ dag c)) t (resF σ roots c) := by
  unfold compValue
  have hfix : fixCap (glueL σ LA) J pat t s =
      gBr σ (fun c => (LA c).garden.tree) fun c => fixCap (LA c) (resJ σ J c) (resF σ pat c) t s := by
    funext b
    obtain ⟨⟨c, x⟩, rfl⟩ := (glueBranchN σ fun c => (LA c).garden.tree).surjective b
    rw [fixCap_glueN, gBr_apply]
  have hroots : roots = gRootN σ (fun c => resF σ roots c) := by
    funext x
    obtain ⟨⟨c, i⟩, rfl⟩ := σ.surjective x
    simp [resF]
  have hup : (fun _ : GBranch (glueL σ LA).garden.tree => t) =
      gBr σ (fun c => (LA c).garden.tree) fun c _ => t := rfl
  rw [hfix, offCap_glueN, capWt_glueN, hup]
  conv_lhs => rw [hroots]
  exact kernelKgen_glueN P.L P.γ P.δ (fun _ _ => 1) σ LA _ _ _ (fun _ _ => t) 0 _ 0 hs

end WaveTurbulence.Flower.CapsGlue
