/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.Stage1WNoVine.Core2
public import WaveTurbulence.Foundations.Flower.Stage1W.Bridge
public import WaveTurbulence.Foundations.Stage1.Represents.RepPr9
public import WaveTurbulence.Foundations.Stage1.Represents.RepS10c

/-! # STAGE1W-O4: `NoVineRepresentsFW` (row O4d, part 3)

The class level: a vine-free tau class has the single member `repPt π`.layered, so its weighted class sum is the
weighted value of the representative (`noVine_members_sumW`); the representative is a reconstruction of its prime
data, so `NoVineRepresentsAtNW` gives its `RepresentsInt` at size `cψ^(3N) s ≤ cψ^(16N) s`
(`noVineRepresentsFW_of_atNW`).  With the prefix `noVine_prefixNW` this is **`noVineRepresentsFW`**. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.Flower.Stage1WNoVine
open Finset WaveTurbulence TTree WaveTurbulence.LGSpine WaveTurbulence.RedSplice WaveTurbulence.Reg
  WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed Set WaveTurbulence.VineA WaveTurbulence.LFTwist
  WaveTurbulence.VineA.PrescribedPrimeGarden WaveTurbulence.Represents WaveTurbulence.Flower.Stage1W
  WaveTurbulence.ClassCount

open scoped Classical in
theorem noVineN_atW (P : WTParams) (hP : NoVineRepresentsAtNW P) {R : ℕ} {S : Garden (2 * R)}
    (D : ReconstructionData S) (hS : S.IsPlain) (LG : LayeredGarden (2 * R)) (hd : D.Decodes hS LG.garden)
    (hg : D.garden hS = LG.garden) (σ : Prescription S) (hnv : unitBlocks S σ = [])
    {p N : ℕ} (hp : p < P.D) (hNb : N ≤ P.N (p + 1) ^ 4) (hord : LG.garden.order = N)
    (hcan : IsCanonGC (p + 1) LG)
    (tt : Fin (2 * R) → ℝ) (htt : ∀ j, tt j ∈ Icc (p : ℝ) (p + 1))
    (F : LeafFamily P (2 * R)) (hF : F.Controlled LG)
    (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)) (s : ℝ) (hs : F.size LG ≤ s)
    (g : Fin (2 * R) → Mom P.d → ℂ) (cψ : ℝ) (hc : 1 ≤ cψ) (hgp : ∀ j, GPresented (32 * P.d) (g j) cψ) :
    Stage1Piece.RepresentsInt (P := P) (NormalizedSplice.stage1PieceOf P.d hS LG hd σ) N tt base roots
      (cψ ^ (3 * N) * s)
      (valueSelW F tt base roots LG (fun κ =>
        NormalizedSplice.selOf (NormalizedSplice.GroupPrescription.ofPrescription σ) P.L P.γ P.η base
          (collapseGenDecoration D hS (hg ▸ κ)).1) (fwWeight p g base LG)) := by
  obtain ⟨layer, hLayer, he⟩ := layered_eq_reconstruction D hS LG hd
  subst he
  have hsz := D.decoded_order hS hd
  have h := hP R S D hS layer hLayer p hp (by omega) hcan tt htt F hF base roots σ hnv
    (Mole.garden_isMolecule _) N s hs (by omega) g cψ hc hgp
  have ho : (D.garden hS).order = N := hord
  rw [ho] at h
  exact h

open scoped Classical in
theorem noVine_representsIntAW (P : WTParams) (hP : NoVineRepresentsAtNW P) {R : ℕ}
    (b : PrescribedPrimeGarden (2 * R)) (hnv : unitBlocks b.prime.skeleton b.totalSigma = [])
    {p N : ℕ} (hp : p < P.D) (hNb : N ≤ P.N (p + 1) ^ 4) (hord : b.layered.garden.order = N)
    (hcan : IsCanonGC (p + 1) b.layered)
    (tt : Fin (2 * R) → ℝ) (htt : ∀ j, tt j ∈ Icc (p : ℝ) (p + 1))
    (F : LeafFamily P (2 * R)) (hF : F.Controlled b.layered)
    (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)) (s : ℝ) (hs : F.size b.layered ≤ s)
    (g : Fin (2 * R) → Mom P.d → ℂ) (cψ : ℝ) (hc : 1 ≤ cψ) (hgp : ∀ j, GPresented (32 * P.d) (g j) cψ) :
    Stage1Piece.RepresentsInt (P := P) (b.normalizedPiece P.d) N tt base roots (cψ ^ (3 * N) * s)
      (valueSelW F tt base roots b.layered (fun κ => selAt P base b.prime b.sigma κ) (fwWeight p g base b.layered)) := by
  have h := noVineN_atW P hP b.prime.data b.prime.prime.1 b.layered b.prime.decodes b.prime.gardenEq
    b.totalSigma hnv hp hNb hord hcan tt htt F hF base roots s hs g cψ hc hgp
  have e : NormalizedSplice.GroupPrescription.ofPrescription b.totalSigma = b.sigma :=
    of_extendGroupPrescription b.sigma
  rw [e] at h
  exact h

variable {R : ℕ} {p : ℕ} {kind : Bool} {A : Finset (LayeredGarden (2 * R))}

open scoped Classical in
/-- The weighted class sum of a vine-free class is the weighted value of its representative. -/
theorem noVine_members_sumW (P : WTParams) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (tt : Fin (2 * R) → ℝ) (F : LeafFamily P (2 * R)) (π : PcA R p kind A)
    (hnv : unitBlocks (repPt π).prime.skeleton (repPt π).totalSigma = [])
    (wt : ∀ LG : LayeredGarden (2 * R), GenDecoration LG.garden P.d roots 0 → ℂ) :
    ∑ LG ∈ membersP (clsP π), valueSelW F tt base roots LG (selP p kind A P base roots π LG) (wt LG) =
      valueSelW F tt base roots (repPt π).layered (fun κ => selAt P base (repPt π).prime (repPt π).sigma κ)
        (wt (repPt π).layered) := by
  have hmem : (repPt π).layered ∈ membersP (clsP π) := by
    refine Finset.mem_filter.2 ⟨repPt_layered_mem π, ?_⟩
    show (repPt π).layered ∈ coarseOf p kind (repPt π)
    rw [coarseOf_empty]
    exact (repPt π).prime.mem_coarse_outputs_self
  rw [Finset.sum_eq_single (repPt π).layered]
  · congr 1
    funext κ
    exact propext ((selP_noVine P base roots π hnv _ κ).trans ⟨fun ⟨h, hs⟩ => hs, fun hs => ⟨rfl, hs⟩⟩)
  · intro LG _ hne
    have hnone : ∀ κ : GenDecoration LG.garden P.d roots 0, ¬ selP p kind A P base roots π LG κ := by
      intro κ hκ
      obtain ⟨h, -⟩ := (selP_noVine P base roots π hnv LG κ).1 hκ
      exact hne h.symm
    simp [valueSelW, kernelLeavesSelW, hnone]
  · intro h; exact absurd hmem h

/-- **O4′ at one parameter record**: the weighted vine-free successor pieces give `NoVineRepresentsFW`. -/
theorem noVineRepresentsFW_of_atNW (P : WTParams) (hC : 1 ≤ P.C₁) (hL : 1 ≤ P.L) (h : NoVineRepresentsAtNW P) :
    NoVineRepresentsFW P := by
  intro p hp R hR hRmax N hN1 hN A hA hcl tt htt base roots g cψ hc1 hg hreal U s hs0 hb hsize π hv
  have hctrl := controlled_of_bounded hA U hb
  have hc := hA _ (repPt_layered_mem π)
  have h1 := noVine_representsIntAW P h (repPt π) hv hp hN hc.2.2.1 hc.1 tt htt U.toLF
    (hctrl _ (repPt_layered_mem π)) base roots s (hsize _ (repPt_layered_mem π)) g cψ hc1 hg
  rw [noVine_members_sumW P base roots tt U.toLF π hv (fwWeight p g base)]
  refine representsInt_mono_size (by linarith) (by linarith) h1 ?_
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hc1 (by omega)) hs0.le

/-- **`NoVineRepresentsFW` on the prefix** (O4′, the vine-free pieces of the weighted Stage-1 gate). -/
theorem noVineRepresentsFW : WTPrefix NoVineRepresentsFW := by
  intro d hd γ hγ
  obtain ⟨η₀, hη₀, h⟩ := noVine_prefixNW d hd γ hγ
  refine ⟨η₀, hη₀, fun η hη φin hφin τ hτ φ hsol => ?_⟩
  obtain ⟨C₁, hC₁, ν₀, hν₀, h2⟩ := h η hη φin hφin τ hτ φ hsol
  refine ⟨C₁, hC₁, ν₀, hν₀, fun ν hν => ?_⟩
  obtain ⟨δ₀, hδ₀, h3⟩ := h2 ν hν
  refine ⟨δ₀, hδ₀, fun δ hδ D hD htime => ?_⟩
  obtain ⟨C₂, hC₂, L₀, hL₀, h4⟩ := h3 δ hδ D hD htime
  refine ⟨C₂, hC₂, L₀, hL₀, fun L hL => ?_⟩
  exact noVineRepresentsFW_of_atNW _ hC₁ (by show (1 : ℝ) ≤ L; linarith) (h4 L hL)

end WaveTurbulence.Flower.Stage1WNoVine
