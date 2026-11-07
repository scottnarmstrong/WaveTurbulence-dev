/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.LowGardenSplit3
public import WaveTurbulence.Foundations.FinalCount.LowGardenLoopData
public import WaveTurbulence.Foundations.FinalCount.LowGardenLoopMain
public import WaveTurbulence.Foundations.FinalCount.LowGardenMain
/-! **LOW-GARDEN (session 3): `LowGardenBound` from `LowLoopClassBound` (R79, treatment A).**

* `lowGardenGE2_of_loopMolecule`: the gardens with at least two atoms (loops allowed, `k ≥ 0`) from `LowLoopMoleculeBound`.
* `lowGarden_of_loopClassBound`: `LowLoopClassBound d γ η → LowGardenBound d γ η` (`3 ≤ d`, `γ ∈ (1/2,1)`, `0 < η ≤ 1/40`); the one-atom
  gardens by `lowGarden_single_atom`.
* `lowGardenBoundAll_of_loopClassBound`: the smallness form for LOW-GLUE (conditional on `LowLoopClassBound`; distinct helper). -/
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

/-- `LowGardenBound` restricted to the gardens with at least two atoms (loops allowed; conditional helper, distinct name). -/
def LowGardenBoundGE2 (d : ℕ) (γ η : ℝ) : Prop :=
  ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ m c : ℕ, ∀ C1 ≥ 4 * Cstar, ∀ δ ∈ Ioc (0 : ℝ) 1, ∃ R₀ : ℝ, 1 ≤ R₀ ∧ ∀ L ≥ R₀,
    ∀ {R : ℕ} (G : Garden (2 * R)), G.IsPlain → G.Irreducible → IsBalancedSig G.sig → 1 ≤ G.order →
      1 ≤ R → (R : ℝ) ≤ (1 + Real.log L) ^ c → ((2 * G.order : ℕ) : ℝ) ≤ (1 + Real.log L) ^ m →
    ∀ (D : SplicedKernelData G d) (C : CountingChoices G d), D.hinges = C.subpro.hinges → CountingGeometry G C →
      ¬ RegGeom G → 2 ≤ G.molecule.atoms.card →
    ∀ (base : Mom d) (roots : Fin (2 * R) → (Fin d → ℤ)) (Adm : (GardenDart G → (Fin d → ℤ)) → Prop),
      (∀ κ, Adm κ → splicedCountingAdmissible G D C L γ η base roots κ) →
      G.molecule.countA L γ δ C1 base Adm C.ladderScale ≤
        ENNReal.ofReal (L ^ (-4 * η ^ 6 * (G.molecule.rho + C.numCriticalSG)) *
          L ^ (((R : ℝ) - 1) * ((d : ℝ) - γ - 1 / 4 - 1 / 40)))

theorem lowGardenGE2_of_loopMolecule {d : ℕ} {γ η : ℝ} (hLM : LowLoopMoleculeBound d γ η) : LowGardenBoundGE2 d γ η := by
  obtain ⟨Cs, hCs, hmol⟩ := hLM
  refine ⟨Cs, hCs, fun m c C1 hC1 δ hδ => ?_⟩
  obtain ⟨R₁, hR₁, hb⟩ := hmol m c C1 hC1 δ hδ
  refine ⟨R₁, hR₁, fun L hL R G hp hirr hbal hord hR hRc hordm D C hD hg hnreg h2a base roots Adm hA => ?_⟩
  have hL1 : 1 ≤ L := le_trans hR₁ hL
  have hL0 : 0 < L := by linarith
  by_cases hne : ∃ κ, Adm κ
  swap
  · push Not at hne
    have h0 := countA_union_le G.molecule L γ δ C1 base (∅ : Finset Bool) (Adm := Adm) (fun _ _ => True)
      (fun κ hκ => absurd hκ (hne κ)) C.ladderScale
    simp only [Finset.sum_empty] at h0
    exact h0.trans bot_le
  obtain ⟨κ0, hκ0⟩ := hne
  set M := inlMol G.molecule with hMdef
  have hS : SubHypLoop R M := subHypLoop_mapAtoms (inlEmb _) (subHypLoop_of_geometry hg hR h2a)
  have hdet := inl_loop_det hp hg hD hA
  have hcard : ((2 * M.atoms.card : ℕ) : ℝ) ≤ (1 + Real.log L) ^ m := by
    rw [hMdef, inlMol_atoms, Finset.card_map, hg.atom_count]; exact hordm
  have hD0 := lowLoopData_garden hp hR hD hg h2a hL0 hA ⟨κ0, hκ0⟩ m hcard
  let Un' : (NonLoop M → Fin d → ℤ) → Set (Object M.unloop) := fun κ' =>
    if h : ∃ κ, Adm κ ∧ κ' = fun y : NonLoop M => κ y.1 then unloopSet M (Un0 C L γ η (Classical.choose h)) else ∅
  have hUn' : ∀ κ, Adm κ → Un' (fun y : NonLoop M => κ y.1) = unloopSet M (Un0 C L γ η κ) := by
    intro κ hκ
    have h : ∃ κ₂, Adm κ₂ ∧ (fun y : NonLoop M => κ y.1) = fun y : NonLoop M => κ₂ y.1 := ⟨κ, hκ, rfl⟩
    have hch : Classical.choose h = κ := by
      obtain ⟨h1, h2⟩ := Classical.choose_spec h
      exact hdet _ _ h1 hκ (fun x hx => (congrFun h2 ⟨x, hx⟩).symm)
    simp only [Un', h, ↓reduceDIte, hch]
  have hkF : (kFix0 C base).card ≤ 2 * R := Finset.card_image_le.trans hg.fixedRoots_card
  have hkle : ((M.loopBonds.card : ℕ) : ℝ) ≤ (1 + Real.log L) ^ m := by
    have h1 : M.loopBonds.card ≤ M.bonds.card := Finset.card_le_card (Finset.filter_subset _ _)
    have h2 := hS.count
    have h3 : M.loopBonds.card ≤ 2 * M.atoms.card := by omega
    refine le_trans ?_ hcard
    exact_mod_cast h3
  have hclass : ∀ lab ∈ labelSet M (kFix0 C base),
      (∃ κ, Adm κ ∧ InClass M L (0 : Mom d) (kFix0 C base) lab.1 lab.2 κ) →
      LowLoopClassHyps (d := d) M R (heredScale' M.unloop (scaleMap (inlEmb _) C.ladderScale))
        {κ' | unloopAdm M (fun κ => Adm κ ∧ InClass M L (0 : Mom d) (kFix0 C base) lab.1 lab.2 κ) κ'} (C0 C).unloop Un'
        (unloopSet M (Fst0 C)) (critMap (inlEmb _) C) (fun v => v ∈ lab.1) L γ η m :=
    fun lab _ hne' => lowLoopClassHyps_unloop hD0 hL0.ne' hkle hUn' lab hne'
  have hres := hb L hL (M := M) (R := R) (P0 := scaleMap (inlEmb _) C.ladderScale) (Adm := Adm) (C := (C0 C).unloop)
    (Un := Un') (Fst := unloopSet M (Fst0 C)) (crit := critMap (inlEmb _) C) (kFix0 C base) hS hkF hRc hD0.hmate hdet
    hD0.hP0 hclass
  have ecrit : (M.unloop.atoms.filter (critMap (inlEmb _) C)).card = C.numCriticalSG := (numCriticalSG_eq (inlEmb _) C).symm
  have erho : M.rho = G.molecule.rho := rho_inl G.molecule
  rw [unloop_rho, erho, ecrit] at hres
  calc G.molecule.countA L γ δ C1 base Adm C.ladderScale
      = G.molecule.countA L γ δ C1 0 Adm C.ladderScale := countA_base_eq_of_molecule G.molecule hg.molecule L γ δ C1 base 0 Adm _
    _ = M.countA L γ δ C1 0 Adm (scaleMap (inlEmb _) C.ladderScale) := (countA_inl_scale G.molecule L γ δ C1 0 Adm C.ladderScale).symm
    _ ≤ _ := hres

/-- **LOW-GARDEN target (treatment A):** `LowGardenBound` from the weighted class bound `LowLoopClassBound`. -/
theorem lowGarden_of_loopClassBound {d : ℕ} (hd : 3 ≤ d) {γ η : ℝ} (hγ : γ ∈ Ioo (1 / 2 : ℝ) 1) (hη : 0 < η)
    (hη40 : η ≤ 1 / 40) (hcl : LowLoopClassBound d γ η) : LowGardenBound d γ η := by
  obtain ⟨Cs, hCs, hmol⟩ := lowGardenGE2_of_loopMolecule (lowLoop_molecule_bound_of hη hη40 hcl)
  refine ⟨Cs, hCs, fun m c C1 hC1 δ hδ => ?_⟩
  obtain ⟨R₀, hR₀, hb⟩ := hmol m c C1 hC1 δ hδ
  refine ⟨R₀, hR₀, fun L hL R G hp hirr hbal hord hR hRc hordm D C hD hg hnreg base roots Adm hA => ?_⟩
  have hL1 : 1 ≤ L := le_trans hR₀ hL
  have hC1' : 1 ≤ C1 := by
    have := hCs; linarith [hC1]
  have hcnt : 1 ≤ G.molecule.atoms.card := by rw [hg.atom_count]; exact hord
  by_cases h2a : 2 ≤ G.molecule.atoms.card
  · exact hb L hL G hp hirr hbal hord hR hRc hordm D C hD hg hnreg h2a base roots Adm hA
  · exact lowGarden_single_atom hd hγ.2 hη hη40 G hp hR D C hD hg (by omega) hL1 hC1' hδ.1 hδ.2 base roots Adm hA

/-- **The smallness form for LOW-GLUE**, conditional on `LowLoopClassBound` (distinct helper; feeds `finalCount_half_of_lowGarden`). -/
theorem lowGardenBoundAll_of_loopClassBound
    (hcl : ∀ d : ℕ, 3 ≤ d → ∀ γ : ℝ, 1 / 2 < γ → γ < 1 →
      ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η : ℝ, 0 < η → η ≤ η₀ → LowLoopClassBound d γ η) :
    LowGardenBoundAll := by
  intro d hd γ hγ1 hγ2
  obtain ⟨η₀, hη₀, h⟩ := hcl d hd γ hγ1 hγ2
  refine ⟨min η₀ (1 / 40), lt_min hη₀ (by norm_num), fun η hη hηle => ?_⟩
  exact lowGarden_of_loopClassBound hd ⟨hγ1, hγ2⟩ hη (le_trans hηle (min_le_right _ _))
    (h η hη (le_trans hηle (min_le_left _ _)))

end WaveTurbulence.FinalCountAsm
