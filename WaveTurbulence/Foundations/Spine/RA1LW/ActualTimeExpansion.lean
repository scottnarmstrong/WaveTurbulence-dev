/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.RA1LW.CoefficientClassification
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.PhaseCoordinates
public import WaveTurbulence.Foundations.RegularAsymptotics.BTilde.BridgeB2

/-! # The J3 expansion and J4 coefficients for the literal garden phase integral -/

public section
noncomputable section
namespace WaveTurbulence.RA1Leafwise
open WaveTurbulence.RegAsymp
open TTree Reg Links ClassJR Cancel MainCoef Set

/-- The actual garden energies satisfy the source link relation. -/
theorem linkRel_alphaOmega_of_decoration {d : ℕ} {G : Garden 2} {Q : RegCpl}
    (hQ : Q.Decodes G) (L γ δ : ℝ) {k : GNode G.tree → Mom d} (hk : IsDecoration G k)
    {l : Cancel.Addr × Cancel.Addr} (hl : l ∈ Q.links) : MainCoef.LinkRel (alphaOmega L γ δ G k) l := by
  obtain ⟨hl1,hl2,-⟩ := link_branching hQ hl
  let b : GBranch G.tree := ⟨l.1,hl1⟩
  let b' : GBranch G.tree := ⟨l.2,hl2⟩
  have hΩ := zeta_omega_link hQ hQ.1 hk hl b b' rfl rfl
  have hsign (v : GBranch G.tree) :
      ((G.sign v.toNode : ℤ):ℝ) = (nodeSgn v.val : ℝ) := by
    rw [← zetaA_eq_nodeSgn]
    simp only [Garden.sign,hQ.1.2,zetaA]
    rfl
  rw [hsign b,hsign b'] at hΩ
  simp only [MainCoef.LinkRel,MainCoef.alphaOmega,dite_eq_left hl1,dite_eq_left hl2]
  change (nodeSgn l.2 : ℝ)*(δ*L^(2*γ)*omegaNode G k b') =
    -((nodeSgn l.1 : ℝ)*(δ*L^(2*γ)*omegaNode G k b))
  calc
    _ = (δ*L^(2*γ))*((nodeSgn l.2 : ℝ)*omegaNode G k b') := by ring
    _ = (δ*L^(2*γ))*(-((nodeSgn l.1 : ℝ)*omegaNode G k b)) := by rw [hΩ]
    _ = _ := by ring

/-- The phase integral of the actual layer-zero couple is the code time
coefficient, with its link hypothesis discharged by source conservation. -/
theorem actual_phaseIntegral_eq_BtJR {d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden 2)
    (h0 : ∀ a, LG.layer a = 0) {Q : RegCpl} (hQ : Q.Decodes LG.garden)
    {k : GNode LG.garden.tree → Mom d} (hk : IsDecoration LG.garden k)
    {t s : ℝ} (ht : t ∈ Icc (0:ℝ) 1) (hs : s ∈ Icc (0:ℝ) 1) (s₁ s₂ : ℝ) :
    phaseIntegral L γ δ LG.garden (kDomain LG (fun b => if b.1.1=0 then t else s) s₁) s₂ k =
      BtJR Q (0,[]) (1,[]) (alphaOmega L γ δ LG.garden k) t s :=
  phaseIntegral_kDomain_eq_BtJR L γ δ LG h0 hQ k
    (fun _ hl => linkRel_alphaOmega_of_decoration hQ L γ δ hk hl) ht hs s₁ s₂

/-- The actual code expansion, with every limiting coefficient identified.
The Gevrey constant A here is the fixed J3 parameter, not the order exponent. -/
theorem couple_time_expansion_classified {η A : ℝ}
    (hη : 0 < η) (hη2 : η ≤ 2) (hA : ClassJR.A1 ≤ A)
    (Q : RegCpl) (hwf : Q.wf = true) :
    ∃ G : Finset Cancel.Addr → TCoef,
      (∀ Z ⊆ chosenSet Q.links, MCRep (1-η/8) (η/4) (1-η/2) A
        (C0 (1-η/8) (η/4) (1-η/2)^(2*Q.size+1)) (↑(chosenSet Q.links \ Z)) (G Z)) ∧
      (∀ α t s, t ∈ Icc (0:ℝ) 1 → s ∈ Icc (0:ℝ) 1 →
        BtJR Q (0,[]) (1,[]) α t s =
          ∑ Z ∈ (chosenSet Q.links).powerset, (∏ z ∈ Z, PhiZ zetaA z (α z))*G Z α t s) ∧
      ∀ Z ⊆ chosenSet Q.links, ∀ t ∈ Icc (0:ℝ) 1, ∀ s ∈ Icc (0:ℝ) 1, ∀ α₀ : Cancel.Addr → ℝ,
        mint (chosenSet Q.links \ Z) (fun α => G Z α t s) α₀ =
          if Q.dominant = true ∧ IsSpecialSet Q.links Z then
            (-1:ℂ)^Z.card*(Q.JB 0 t s : ℂ) else 0 := by
  obtain ⟨G,hG,hF⟩ := maincoef_BtJR_DH23 hη hη2 hA Q hwf
  refine ⟨G,hG,hF,?_⟩
  intro Z hZ t ht s hs α₀
  rw [mint_eq_of_MCExp (by linarith : 0 ≤ 1-η/8) zetaA_pm hZ
    (regCoef_root btRec_BtJR hwf Z) hG hF ht hs α₀]
  exact cplJ_eq_if_special Q Z hZ t ht s hs

end WaveTurbulence.RA1Leafwise
