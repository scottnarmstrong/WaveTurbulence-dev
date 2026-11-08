/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.MkMark.NearStep
public import WaveTurbulence.Foundations.Stage1.Shared.S1VInvEquiv

/-! # B2b MK-MARK: one LF step transports the coarse marking (Lemma 2⁺, `markI0`, one step)

`mark_step`: for a twist site `Z` (a vine of `𝒱` with its core placement) and either LF choice `ε`, if no vertex of
`Π₀(LG)` lies in the near region of the lower joint, then the marked sets `markedVinesRaw … Π₀` of the source and of
the output reconstruction correspond along `chosenMolIso`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical
open WaveTurbulence WaveTurbulence.Flower.MkDefs WaveTurbulence.Reg WaveTurbulence.Reg.Skeleton
  WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.Stage1

namespace WaveTurbulence.Flower.MkMark

variable {w : ℕ}

theorem pair_retained_tree' {S : Garden w} (P : CorePlacement S) {A : Finset (GBranch S.tree)} {a : GBranch S.tree}
    (hB : S.molecule.IsBlock A a P.lower) (hCL : Mole.CLParentPattern S A a P.lower)
    (hP : IsPlacementAt S A P.lower P) : (S.pair P.retained).1.1 = P.lower.1.1 := by
  have hr := placement_pair_in_realization S P hB hP
  have h1 := (Mole.cl_leaf_realization_iff S hB hCL _).mp ((Mole.leaf_incidence_realization_iff S A _).mp hr)
  have h2 := (Mole.cl_branch_realization_iff S hB hCL P.lower).mp hB.2.2.1
  exact h1.1.1.symm.trans h2.1.1

theorem mem_markedVinesRaw {S : Garden w} (X : GBranch S.tree → RegChain) {T : Fin w → TTree}
    (Pi : Finset (GNode T)) (c : CLVine S) :
    c ∈ markedVinesRaw S X Pi ↔ c ∈ vinesV S ∧ ∃ b ∈ c.atoms, b ≠ c.upper ∧ MarkedBranch S X Pi b := Iff.rfl

section Step
variable {S : Garden w} (hS : S.IsPlain) (Z : TwistGroupSite S) (D : ReconstructionData S)
  (X : RegChain) (Q : RegCpl) (hX : X.wf = true) (hQ : Q.wf = true)

/-- **One LF step transports the coarse marking.** -/
theorem mark_step (ε : Bool) {LG LG' : LayeredGarden w} (hd : D.Decodes hS LG.garden)
    (hd' : (lfReconstructionChoice S Z.P hS D ε X Q hX hQ).Decodes (chosenSkeleton_plain S Z.P hS ε) LG'.garden)
    {J : Finset (Fin w)} {pat : Fin w → FixPat} (t s : ℝ)
    (hn : ∀ a ∈ protI0 LG J pat t s, a.1 ∉ nearRegion S D.tree Z.P.lower) :
    MarkTransported (VineA.chosenMolIso S Z.P ε) (markedVinesRaw S D.tree (protI0 LG J pat t s))
      (markedVinesRaw (chosenSkeleton S Z.P ε) (lfReconstructionChoice S Z.P hS D ε X Q hX hQ).tree
        (protI0 LG' J pat t s)) := by
  have hsame := pair_retained_tree' Z.P Z.hB Z.hCL Z.hP
  have hp := noProt_of_near hS Z.P D hd t s hn
  cases ε with
  | false =>
    set C := idCoord hS Z.P D X Q hX hQ
    have hst := C.step_prot (idPair hS Z.P D X Q hX hQ) hd hd' (replaced_nonroot Z.P) (replaced_pairTree Z.P hsame)
      (replaced_nonroot Z.P) (replaced_pairTree Z.P hsame) hp
    have hMB := C.markedBranch_transport hd hd' t s id (fun o _ b => Iff.rfl) hp hst.1 hst.2
    intro c c' hc'
    have hcc : c' = c := by
      apply VineA.clVine_eq_of_atoms
      rw [hc']
      exact Finset.image_id
    subst hcc
    exact ⟨fun ⟨hv, b, hb, hbu, hm⟩ => ⟨hv, b, hb, hbu, (hMB b).mp hm⟩,
      fun ⟨hv, b, hb, hbu, hm⟩ => ⟨hv, b, hb, hbu, (hMB b).mpr hm⟩⟩
  | true =>
    set C := twistCoord hS Z.P D X Q hX hQ hsame
    obtain ⟨hp', hiff⟩ := twist_step_prot hS Z.P D X Q hX hQ hsame hd hd' t s hn
    have hMB := C.markedBranch_transport hd hd' t s (coreBranchEquiv S Z.P)
      (fun o ho b => twist_nearRel hS Z.P D X Q hX hQ hsame o ho b) hp hp' hiff
    intro c c' hc'
    rw [mem_markedVinesRaw, mem_markedVinesRaw]
    constructor
    · rintro ⟨hv, b, hb, hbu, hm⟩
      obtain ⟨c'', hc''V, hc''a, hc''u, -⟩ := Z.vinesV_image hv
      have e : c'' = c' := VineA.clVine_eq_of_atoms (hc''a.trans hc'.symm)
      subst e
      refine ⟨hc''V, coreBranchEquiv S Z.P b, ?_, ?_, (hMB b).mp hm⟩
      · rw [hc''a]
        exact (VineA.chosenMolIso S Z.P true).mem_img _ b |>.mpr hb
      · rw [hc''u]
        exact fun h => hbu ((coreBranchEquiv S Z.P).injective h)
    · rintro ⟨hv', b', hb', hbu', hm'⟩
      obtain ⟨c₀, hc₀V, hc₀a, hc₀u, -⟩ := Z.vinesV_preimage hv'
      have hae : c₀.atoms = c.atoms := (VineA.chosenMolIso S Z.P true).img_injective (hc₀a.trans hc')
      have e : c₀ = c := VineA.clVine_eq_of_atoms hae
      subst e
      set b := (coreBranchEquiv S Z.P).symm b'
      have hbb : coreBranchEquiv S Z.P b = b' := Equiv.apply_symm_apply _ _
      refine ⟨hc₀V, b, ?_, ?_, ?_⟩
      · apply ((VineA.chosenMolIso S Z.P true).mem_img c₀.atoms b).mp
        have h1 : (VineA.chosenMolIso S Z.P true).img c₀.atoms = c'.atoms := hc₀a
        have h2 : (VineA.chosenMolIso S Z.P true).e b = b' := hbb
        rw [h1, h2]
        exact hb'
      · intro h
        apply hbu'
        rw [← hbb, h, hc₀u]
      · rw [hMB b, hbb]
        exact hm'

end Step

end WaveTurbulence.Flower.MkMark
