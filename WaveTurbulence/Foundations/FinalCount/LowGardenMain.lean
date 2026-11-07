/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.LowGardenClass
public import WaveTurbulence.Foundations.FinalCount.LowGardenOne
public import WaveTurbulence.Foundations.FinalCount.AsmGReg2
/-! **FINALCOUNT-ASSEMBLY (LOW-GARDEN): the garden-level LOW bound for one-atom and loop-free gardens.**

`lowGardenNoLoop_of_molecule`: `LowMoleculeBound d γ η` gives the statement of `LowGardenBound d γ η` for every garden that has one
atom (loops allowed: `lowGarden_single_atom`) or at least two atoms and no loop (`lowClassHyps_loopfree`).  The remaining gardens
(at least two atoms and a loop) are NOT covered: see HANDOFF-LOWGARDEN.md (the unlooped molecule has degree-2 atoms that are
degenerate but not tame, so `LowClassHyps.degen` fails on it). -/
@[expose] public section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open Set (Ioo Ioc)
open scoped ENNReal
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine
  WaveTurbulence.AtomTransport WaveTurbulence.MoleProp WaveTurbulence.Mole WaveTurbulence.VineCount

/-- `LowGardenBound` restricted to the gardens with one atom or without loops (conditional helper, distinct name). -/
def LowGardenBoundNoLoop (d : ℕ) (γ η : ℝ) : Prop :=
  ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ m c : ℕ, ∀ C1 ≥ 4 * Cstar, ∀ δ ∈ Ioc (0 : ℝ) 1, ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ L ≥ R₀,
    ∀ {R : ℕ} (G : Garden (2 * R)), G.IsPlain → G.Irreducible → IsBalancedSig G.sig → 1 ≤ G.order →
      1 ≤ R → (R : ℝ) ≤ (1 + Real.log L) ^ c → ((2 * G.order : ℕ) : ℝ) ≤ (1 + Real.log L) ^ m →
    ∀ (D : SplicedKernelData G d) (C : CountingChoices G d), D.hinges = C.subpro.hinges → CountingGeometry G C →
      ¬ RegGeom G → (2 ≤ G.molecule.atoms.card → ∀ x, G.molecule.atom x ≠ G.molecule.atom (G.molecule.mate x)) →
    ∀ (base : Mom d) (roots : Fin (2 * R) → (Fin d → ℤ)) (Adm : (GardenDart G → (Fin d → ℤ)) → Prop),
      (∀ κ, Adm κ → splicedCountingAdmissible G D C L γ η base roots κ) →
      G.molecule.countA L γ δ C1 base Adm C.ladderScale ≤
        ENNReal.ofReal (L ^ (-4 * η ^ 6 * (G.molecule.rho + C.numCriticalSG)) *
          L ^ (((R : ℝ) - 1) * ((d : ℝ) - γ - 1 / 4 - 1 / 40)))

theorem lowGardenNoLoop_of_molecule {d : ℕ} (hd : 3 ≤ d) {γ η : ℝ} (hγ : γ ∈ Ioo (1 / 2 : ℝ) 1) (hη : 0 < η)
    (hη40 : η ≤ 1 / 40) (hLM : LowMoleculeBound d γ η) : LowGardenBoundNoLoop d γ η := by
  obtain ⟨Cs, hCs, hmol⟩ := hLM
  refine ⟨Cs, hCs, fun m c C1 hC1 δ hδ => ?_⟩
  obtain ⟨R₀, hR₀, hb⟩ := hmol m c C1 hC1 δ hδ
  refine ⟨R₀, hR₀, fun L hL R G hp hirr hbal hord hR hRc hordm D C hD hg hnreg hnl base roots Adm hA => ?_⟩
  have hL1 : 1 ≤ L := le_trans hR₀ hL
  have hL0 : 0 < L := by linarith
  have hC1' : 1 ≤ C1 := by linarith
  have hcnt : 1 ≤ G.molecule.atoms.card := by rw [hg.atom_count]; exact hord
  by_cases h2a : 2 ≤ G.molecule.atoms.card
  swap
  · exact lowGarden_single_atom hd hγ.2 hη hη40 G hp hR D C hD hg (by omega) hL1 hC1' hδ.1 hδ.2 base roots Adm hA
  have hnl' := hnl h2a
  by_cases hne : ∃ κ, Adm κ
  swap
  · push Not at hne
    have h0 := countA_union_le G.molecule L γ δ C1 base (∅ : Finset Bool) (Adm := Adm) (fun _ _ => True)
      (fun κ hκ => absurd hκ (hne κ)) C.ladderScale
    simp only [Finset.sum_empty] at h0
    exact h0.trans bot_le
  obtain ⟨κ0, hκ0⟩ := hne
  have hSG : SubHypL R G.molecule := subHypL_of_geometry hg hR h2a hnl'
  have hS : SubHypL R (inlMol G.molecule) := subHypL_mapAtoms (inlEmb _) hSG
  have hk : (kFix0 C base).card ≤ 2 * R := Finset.card_image_le.trans hg.fixedRoots_card
  have hmateAll : ∀ κ, Adm κ → ∀ x, κ ((inlMol G.molecule).mate x) = κ x := by
    intro κ hκ x
    obtain ⟨c, hc, -⟩ := gdec hp hL0.ne' (hA κ hκ)
    exact hc.1 x
  have hcard' : ((2 * (inlMol G.molecule).atoms.card : ℕ) : ℝ) ≤ (1 + Real.log L) ^ m := by
    rw [inlMol_atoms, Finset.card_map, hg.atom_count]; exact hordm
  have hP0 : ∀ S ∈ (inlMol G.molecule).maximalLadders, 0 ≤ scaleMap (inlEmb _) C.ladderScale S := by
    intro S hS'
    have hgaps : SourceLadderGaps (inlMol G.molecule) L base (scaleMap (inlEmb _) C.ladderScale) κ0 :=
      (ladderGaps_mapAtoms (inlEmb _) C L γ η base κ0).2 (hA κ0 hκ0).2.2.2.2.2.2.2.2.2
    rcases (hgaps S hS').1 with h | ⟨-, h, -⟩
    · rw [h]
    · exact le_trans (inv_nonneg.2 hL0.le) h
  have hC10 : 0 ≤ C1 := by linarith
  have hmol := hb L hL (M₀ := inlMol G.molecule) (Rn := R)
    (P := heredScale' (inlMol G.molecule) (scaleMap (inlEmb _) C.ladderScale)) (Adm := Adm) (C := C0 C)
    (Un := Un0 C L γ η) (Fst := Fst0 C) (crit := critMap (inlEmb _) C) (kFix0 C base) hS hk hRc hmateAll
    (fun lab _ hne' => lowClassHyps_loopfree hp hR hg hnl' h2a hL0 hA lab hne' m hcard')
  rw [rho_inl, ← numCriticalSG_eq (inlEmb _) C] at hmol
  calc G.molecule.countA L γ δ C1 base Adm C.ladderScale
      = G.molecule.countA L γ δ C1 0 Adm C.ladderScale := countA_base_eq_of_molecule G.molecule hg.molecule L γ δ C1 base 0 Adm _
    _ = (inlMol G.molecule).countA L γ δ C1 0 Adm (scaleMap (inlEmb _) C.ladderScale) :=
        (countA_inl_scale G.molecule L γ δ C1 0 Adm C.ladderScale).symm
    _ ≤ (inlMol G.molecule).countA L γ δ C1 0 Adm (heredScale' (inlMol G.molecule) (scaleMap (inlEmb _) C.ladderScale)) :=
        countA_le_hered _ L γ δ C1 0 Adm hL0 hδ.1.le hC10 hP0
    _ ≤ _ := hmol

end WaveTurbulence.FinalCountAsm
