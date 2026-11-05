/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.BTilde.MaincoefT
public import WaveTurbulence.Foundations.RegularAsymptotics.BTilde.BridgeB2
public import WaveTurbulence.Foundations.IncohInst.Links.TreeLinks

/-! # The actual regular-tree phase integral consumes the landed tree coefficient expansion -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open TTree Links ClassJR MainCoef Set

/-- Conservation supplies the tree link energy relation with the original source signs. -/
theorem tree_linkRel_alphaOmega_of_decoration {d : ℕ} {G : Garden 1} {X : RegChain}
    (hX : X.DecodesTree G) (L γ δ : ℝ) {k : GNode G.tree → Mom d} (hk : IsDecoration G k)
    {l : (Fin 1 × TTree.Path) × (Fin 1 × TTree.Path)} (hl : l ∈ X.treeLinks (G.sig 0)) :
    LinkRelG G (alphaOmegaT L γ δ G k) l := by
  have hb := (tree_mem_pairEndpoints_links_iff hX l.1).mp
    ((Reg.mem_pairEndpoints_iff _ _).mpr ⟨l, hl, Or.inl rfl⟩)
  have hb' := (tree_mem_pairEndpoints_links_iff hX l.2).mp
    ((Reg.mem_pairEndpoints_iff _ _).mpr ⟨l, hl, Or.inr rfl⟩)
  let b : GBranch G.tree := ⟨l.1, hb⟩
  let b' : GBranch G.tree := ⟨l.2, hb'⟩
  have he := tree_zeta_omega_link hX hk hl b b' rfl rfl
  simp only [LinkRelG, alphaOmegaT, dite_eq_left hb, dite_eq_left hb']
  change ((G.sign b'.toNode : ℤ) : ℝ) * (δ * L ^ (2 * γ) * omegaNode G k b') =
    -(((G.sign b.toNode : ℤ) : ℝ) * (δ * L ^ (2 * γ) * omegaNode G k b))
  calc
    _ = (δ * L ^ (2 * γ)) * (((G.sign b'.toNode : ℤ) : ℝ) * omegaNode G k b') := by ring
    _ = (δ * L ^ (2 * γ)) * (-(((G.sign b.toNode : ℤ) : ℝ) * omegaNode G k b)) := by rw [he]
    _ = _ := by ring

/-- The literal layer-zero tree phase integral equals the landed code coefficient; its link
relation is proved from source conservation rather than assumed as an additional input. -/
theorem actual_tree_phaseIntegral_eq_Atilde {d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden 1)
    (h0 : ∀ a, LG.layer a = 0) {X : RegChain} (hX : X.DecodesTree LG.garden)
    {k : GNode LG.garden.tree → Mom d} (hk : IsDecoration LG.garden k)
    {t s : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) (hst : s < t) (s' : ℝ) :
    phaseIntegral L γ δ LG.garden (kDomain LG (fun _ => t) s) s' k =
      chainAtilde X (LG.garden.sig 0) (liftT (alphaOmegaT L γ δ LG.garden k)) t s := by
  apply phaseIntegral_kDomain_eq_Atilde L γ δ LG h0 hX k _ ht hst s'
  intro l hl
  rw [linksAt_rootT, List.mem_map] at hl
  obtain ⟨l', hl', rfl⟩ := hl
  exact (linkRelG_iff_tree LG.garden _ l').mp (tree_linkRel_alphaOmega_of_decoration hX L γ δ hk hl')

/-- DH23 (maincoef1)–(maincoef2.5) for the literal source tree phase integral.
One coefficient family is chosen before the decoration, torus scale and root momentum. -/
theorem actual_tree_time_expansion {η A : ℝ}
    (hη : 0 < η) (hη2 : η ≤ 2) (hA : ClassJR.A1 ≤ A)
    (X : RegChain) (hwf : X.wf = true) (ζ : ℤˣ) :
    ∃ G : Finset ClassJR.Addr → (ClassJR.Addr → ℝ) → ℝ → ℝ → ℂ,
      (∀ Z ⊆ ClassJR.chosenSet ((toJRc X).linksAt ζ (rootT ζ)),
        MCRep (1 - η / 8) (η / 4) (1 - η / 2) A
          (CTη η ^ (2 * X.size + 1))
          (ClassJR.chosenSet ((toJRc X).linksAt ζ (rootT ζ)) \ Z : Finset ClassJR.Addr) (G Z)) ∧
      ∀ (d : ℕ) (L γ δ : ℝ) (LG : LayeredGarden 1),
        LG.garden.sig 0 = ζ → (∀ a, LG.layer a = 0) → X.DecodesTree LG.garden →
      ∀ k : GNode LG.garden.tree → Mom d, IsDecoration LG.garden k →
      ∀ t s : ℝ, 0 ≤ s → s < t → t ≤ 1 → ∀ s' : ℝ,
        phaseIntegral L γ δ LG.garden (kDomain LG (fun _ => t) s) s' k =
          ∑ Z ∈ (ClassJR.chosenSet ((toJRc X).linksAt ζ (rootT ζ))).powerset,
            (∏ z ∈ Z, PhiZ nodeSgn z (liftT (alphaOmegaT L γ δ LG.garden k) z)) *
              G Z (liftT (alphaOmegaT L γ δ LG.garden k)) t s := by
  obtain ⟨G, hG, hF⟩ := maincoefT_DH23_B2 hη hη2 hA X hwf ζ
  refine ⟨G, hG, ?_⟩
  intro d L γ δ LG hζ h0 hX k hk t s hs hst ht s'
  rw [actual_tree_phaseIntegral_eq_Atilde L γ δ LG h0 hX hk ⟨hs.trans hst.le, ht⟩ hst s', hζ]
  exact hF _ t s hs hst ht

end WaveTurbulence.RegAsymp
