/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.MkUnits.Defs
public import WaveTurbulence.Foundations.Flower.Stage1WNoVine.Class
public import WaveTurbulence.Foundations.Vine.A.VineMarkedGapMK4

/-! # MK-UNITS: O4′ at a marking — the vine-free fine′ pieces

A fine′ piece with no unit at the fine marking (`unitBlocks … (mkF (repPt π).prime) = []`) has the single member
`(repPt π).layered` (main's `selP_noVineMk`, `related_eq_of_unitBlocks_nil`), and its producer piece has `G_sb = S`,
no hinges, `b_sk = 0` and `g_sk = g_reg` at the marking (main's `…Mk` twins in `RepNoVine*`).  Its gap indicator is
the σ-restriction by B2c's `splicedGapIndicator_eq_selOfMk`.  Stage1WNoVine's generic core
`represents_noVine_coreW` (any piece with these fields) then gives `RepresentsInt` at size `cψ^(3N) s ≤ cψ^(16N) s`.

Adapted from `Flower/Stage1WNoVine/Core2.lean`, `Class.lean` and main's `Stage1/Represents/RepPr5.lean` (see
`COPIED-SHA256SUMS`).
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.Flower.MkUnits
open Finset WaveTurbulence TTree WaveTurbulence.LGSpine WaveTurbulence.RedSplice WaveTurbulence.Reg
  WaveTurbulence.Reg.Skeleton WaveTurbulence.RegRed Set WaveTurbulence.VineA WaveTurbulence.LFTwist
  WaveTurbulence.VineA.PrescribedPrimeGarden WaveTurbulence.Represents WaveTurbulence.Flower.Stage1W
  WaveTurbulence.ClassCount WaveTurbulence.Flower.Stage1WNoVine

section Gap
variable {w : ℕ} {S : Garden w}

/-- The gap specification of the vine-free piece at a marking, on `S` (main's `gsCastN` at a marking). -/
noncomputable def gsCastNMk (σ : Prescription S) {Mk : Set (Stage1.CLVine S)} (h : unitBlocks S σ Mk = []) :
    (v : GBranch S.tree) → Option (LocalGapSpecification S v) :=
  (stSt_G_eq_of_unitBlocks_emptyMk σ h) ▸ NormalizedSplice.gapSpecificationMk S σ Mk

theorem heq_gapSpecNMk (σ : Prescription S) {Mk : Set (Stage1.CLVine S)} (h : unitBlocks S σ Mk = []) :
    HEq (NormalizedSplice.gapSpecificationMk S σ Mk) (gsCastNMk σ h) :=
  heq_cast_gapSpec (stSt S σ Mk).G (stSt_G_eq_of_unitBlocks_emptyMk σ h) _

open scoped Classical in
theorem gapIndicator_noVineNMk (hM : S.molecule.IsMolecule) (hp : S.IsPlain) (σ : Prescription S)
    {Mk : Set (Stage1.CLVine S)} (h : unitBlocks S σ Mk = []) {d : ℕ} {L : ℝ} (hL : L ≠ 0) (γ η : ℝ) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) (zS : GenDecoration S d roots 0)
    (D : SplicedKernelData (stSt S σ Mk).G d)
    (hD : D.gapSpecification = NormalizedSplice.gapSpecificationMk S σ Mk) :
    splicedGapIndicator (stSt S σ Mk).G D L γ η base (fun n => zS.1 (nodeCast σ h n)) =
      if NormalizedSplice.selOf (NormalizedSplice.GroupPrescription.ofPrescription σ) L γ η base zS.1 then 1 else 0 :=
  NormalizedSplice.splicedGapIndicator_eq_selOfMk hM σ L γ η base _ zS.1
    (spliced_molecule_decoration S hp hL base roots zS)
    (fun v _ hv => gardenSource_eq_zero_of_deg_four S hp _ v hv) _
    (bondIndex_nodeCastMk σ h zS.1) D hD

open scoped Classical in
/-- The `hgsp` input of the vine-free core at a marking (main's `hgsp_noVineN` at a marking). -/
theorem hgsp_noVineNMk (hM : S.molecule.IsMolecule) (hp : S.IsPlain) (σ : Prescription S)
    {Mk : Set (Stage1.CLVine S)} (h : unitBlocks S σ Mk = []) {d : ℕ} {L : ℝ} (hL : L ≠ 0) (γ η : ℝ) (base : Mom d)
    (roots : Fin w → (Fin d → ℤ)) :
    ∀ D' : SplicedKernelData S d, D'.gapSpecification = gsCastNMk σ h → ∀ z : GenDecoration S d roots 0,
      splicedGapIndicator S D' L γ η base z.1 =
        if NormalizedSplice.selOf (NormalizedSplice.GroupPrescription.ofPrescription σ) L γ η base z.1
          then 1 else 0 := by
  intro D' hD' z
  have e := stSt_G_eq_of_unitBlocks_emptyMk σ h
  rw [transport_gapIndicator (stSt S σ Mk).G e D']
  have hD'' := transport_gapSpec (stSt S σ Mk).G e (NormalizedSplice.gapSpecificationMk S σ Mk) D' hD'
  have := gapIndicator_noVineNMk hM hp σ h hL γ η base roots z (e.symm ▸ D') hD''
  convert this using 2
  funext n
  exact congrArg (fun x => z.1 x) (cast_node_eq (stSt S σ Mk).G e n)

end Gap

/-! ## The vine-free pieces at a marking -/

open scoped Classical in
/-- `RepresentsInt` of every vine-free successor piece at a marking, for the frontier-weighted value (Stage1WNoVine's
`NoVineRepresentsAtNW` at a marking). -/
def NoVineRepresentsAtNWMk (P : WTParams) : Prop :=
  ∀ (R : ℕ) (S : Garden (2 * R)) (D : ReconstructionData S) (hS : S.IsPlain)
    (layer : GNode (D.forest hS) → ℕ) (hLayer : IsLayering (D.garden hS) layer) (p : ℕ),
    p < P.D → D.size ≤ P.N (p + 1) ^ 4 →
    IsCanonGC (p + 1) (RegRed.layeredReconstruction D hS layer hLayer) →
    ∀ (tt : Fin (2 * R) → ℝ), (∀ j, tt j ∈ Set.Icc (p : ℝ) (p + 1)) →
    ∀ (F : LeafFamily P (2 * R)), F.Controlled (RegRed.layeredReconstruction D hS layer hLayer) →
    ∀ (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)) (σ : Prescription S) (Mk : Set (Stage1.CLVine S)),
    unitBlocks S σ Mk = [] → S.molecule.IsMolecule →
    ∀ (n : ℕ) (s : ℝ), F.size (RegRed.layeredReconstruction D hS layer hLayer) ≤ s →
    n - S.order = D.size →
    ∀ (g : Fin (2 * R) → Mom P.d → ℂ) (cψ : ℝ), 1 ≤ cψ → (∀ j, GPresented (32 * P.d) (g j) cψ) →
    Stage1Piece.RepresentsInt (P := P)
      (NormalizedSplice.stage1PieceOf P.d hS (RegRed.layeredReconstruction D hS layer hLayer)
        (D.garden_decodes hS) σ Mk)
      n tt base roots (cψ ^ (3 * (D.garden hS).order) * s)
      (valueSelW F tt base roots (RegRed.layeredReconstruction D hS layer hLayer)
        (fun κ => NormalizedSplice.selOf (NormalizedSplice.GroupPrescription.ofPrescription σ) P.L P.γ P.η base
          (collapseGenDecoration D hS κ).1)
        (fwWeight p g base (RegRed.layeredReconstruction D hS layer hLayer)))

theorem noVineRepresentsAtNWMk_of_gate (Pg : WTParams) (E : GateEnv Pg) (hinc : TopIncoherentDecayAtR Pg) (C : ℝ)
    (hC : CminFW Pg.d Pg.η Pg.C₁ ≤ C) : NoVineRepresentsAtNWMk { Pg with C₁ := C } := by
  obtain ⟨Cmin, hC1, hCe, hcore⟩ := represents_noVine_coreW Pg E hinc
  intro R S D hS layer hLayer p hp hN hcan tt htt F hctrl base roots σ Mk hσ hM n s hs hnrest g cψ hc1 hg
  rw [N_bumpC1] at hN
  have hL : Pg.L ≠ 0 := by have := E.hL1; positivity
  refine hcore C (hCe ▸ hC) D hS layer hLayer p hp hN hcan tt htt F hctrl base roots (gsCastNMk σ hσ)
    (fun z => NormalizedSplice.selOf (NormalizedSplice.GroupPrescription.ofPrescription σ) Pg.L Pg.γ Pg.η base z.1)
    (hgsp_noVineNMk hM hS σ hσ hL Pg.γ Pg.η base roots)
    (NormalizedSplice.stage1PieceOf Pg.d hS (RegRed.layeredReconstruction D hS layer hLayer)
      (D.garden_decodes hS) σ Mk)
    (stSt_G_eq_of_unitBlocks_emptyMk σ hσ)
    (stSt_hinges_eq_emptyMk σ hσ) ?_ (heq_gapSpecNMk σ hσ) ?_ ?_ n s hs hnrest g cψ hc1 hg
  · have e : RegRed.coreLayer (RegRed.layeredReconstruction D hS layer hLayer) D hS (D.garden_decodes hS) =
        fun b => layer (D.coreBranch hS b).toNode := rfl
    show HEq ((stSt S σ Mk).layer (RegRed.coreLayer (RegRed.layeredReconstruction D hS layer hLayer) D hS
      (D.garden_decodes hS))) _
    rw [e]
    exact heq_layerMk σ hσ _
  · exact bskOf_noVineMk σ hσ
  · show gskOf _ S σ _ Mk = _
    rw [gskOf_noVineMk _ σ hσ, gregOf_eq_sum_slotIncoh D hS layer hLayer]

/-- The weighted vine-free successor pieces at a marking on the prefix (Stage1WNoVine's `noVine_prefixNW`). -/
theorem noVine_prefixNWMk : WTPrefix NoVineRepresentsAtNWMk := by
  have hall : WTPrefix (fun P => (LeafwiseIncoherentDecayAt P ∧ LeafwiseCoherentApproximationAt P) ∧
      TopIncoherentDecayAtR P) :=
    prefix_and (prefix_and Spine.leafwise_incoherent_decay Spine.leafwise_coherent_approximation
      leafwiseIncoherentDecay_largeConstantMonotone leafwiseCoherentApproximation30_largeConstantMonotone)
      IncTop.topIncoherentDecayGateR
      (leafwiseIncoherentDecay_largeConstantMonotone.and leafwiseCoherentApproximation30_largeConstantMonotone)
      topIncoherentDecayAtR_largeConstantMonotone
  intro d hd γ hγ
  obtain ⟨η₀, hη₀, hη⟩ := hall d hd γ hγ
  set g1 : ℝ := min (2 * γ) (min 1 (2 * ((d : ℝ) - 1) * (1 - γ))) with hg1
  have hd' : (3 : ℝ) ≤ d := by exact_mod_cast hd
  have hg : 0 < g1 := by
    rw [hg1]
    refine lt_min (by linarith [hγ.1]) (lt_min one_pos ?_)
    have : 0 < 1 - γ := by linarith [hγ.2]
    nlinarith
  refine ⟨min η₀ (min (1 / 2) ((g1 / 2) ^ 2)), lt_min hη₀ (lt_min (by norm_num) (by positivity)), ?_⟩
  intro η hηm φin hφin τ hτ φ hsol
  have hη0 : η ≤ η₀ := hηm.2.trans (min_le_left _ _)
  have hη2 : η ≤ 1 / 2 := hηm.2.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hη3 : η ≤ (g1 / 2) ^ 2 := hηm.2.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨C₁g, hC₁g, ν₀, hν₀, hrest⟩ := hη η ⟨hηm.1, hη0⟩ φin hφin τ hτ φ hsol
  refine ⟨max C₁g (CminFW d η C₁g), hC₁g.trans (le_max_left _ _), ν₀, hν₀, ?_⟩
  intro ν hν
  obtain ⟨δ₀, hδ₀, hrest2⟩ := hrest ν hν
  refine ⟨δ₀, hδ₀, ?_⟩
  intro δ hδ D hD htime
  obtain ⟨C₂, hC₂, L₀, hL₀, hrest3⟩ := hrest2 δ hδ D hD htime
  refine ⟨C₂, hC₂, L₀, hL₀, ?_⟩
  intro L hL
  obtain ⟨⟨hincP, hcohP⟩, htopP⟩ := hrest3 L hL
  let Pg : WTParams := ⟨d, γ, η, φin, τ, φ, C₁g, ν, δ, D, C₂, L⟩
  have E : GateEnv Pg :=
    { hd1 := by show 1 ≤ d; omega
      hL1 := by show 1 ≤ L; linarith [hL₀.trans hL]
      hη0 := hηm.1.le
      hη := hη2
      hC1 := hC₁g
      hδ0 := hδ.1.le
      hκ := Represents.eta_pow_leN g1 η hg hηm.1 hη3 hη2
      hinc := hincP
      hcoh := hcohP }
  exact noVineRepresentsAtNWMk_of_gate Pg E htopP (max C₁g (CminFW d η C₁g)) (le_max_right _ _)

open scoped Classical in
theorem noVineN_atWMk (P : WTParams) (hP : NoVineRepresentsAtNWMk P) {R : ℕ} {S : Garden (2 * R)}
    (D : ReconstructionData S) (hS : S.IsPlain) (LG : LayeredGarden (2 * R)) (hd : D.Decodes hS LG.garden)
    (hg : D.garden hS = LG.garden) (σ : Prescription S) (Mk : Set (Stage1.CLVine S)) (hnv : unitBlocks S σ Mk = [])
    {p N : ℕ} (hp : p < P.D) (hNb : N ≤ P.N (p + 1) ^ 4) (hord : LG.garden.order = N)
    (hcan : IsCanonGC (p + 1) LG)
    (tt : Fin (2 * R) → ℝ) (htt : ∀ j, tt j ∈ Icc (p : ℝ) (p + 1))
    (F : LeafFamily P (2 * R)) (hF : F.Controlled LG)
    (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)) (s : ℝ) (hs : F.size LG ≤ s)
    (g : Fin (2 * R) → Mom P.d → ℂ) (cψ : ℝ) (hc : 1 ≤ cψ) (hgp : ∀ j, GPresented (32 * P.d) (g j) cψ) :
    Stage1Piece.RepresentsInt (P := P) (NormalizedSplice.stage1PieceOf P.d hS LG hd σ Mk) N tt base roots
      (cψ ^ (3 * N) * s)
      (valueSelW F tt base roots LG (fun κ =>
        NormalizedSplice.selOf (NormalizedSplice.GroupPrescription.ofPrescription σ) P.L P.γ P.η base
          (collapseGenDecoration D hS (hg ▸ κ)).1) (fwWeight p g base LG)) := by
  obtain ⟨layer, hLayer, he⟩ := layered_eq_reconstruction D hS LG hd
  subst he
  have hsz := D.decoded_order hS hd
  have h := hP R S D hS layer hLayer p hp (by omega) hcan tt htt F hF base roots σ Mk hnv
    (Mole.garden_isMolecule _) N s hs (by omega) g cψ hc hgp
  have ho : (D.garden hS).order = N := hord
  rw [ho] at h
  exact h

open scoped Classical in
theorem noVine_representsIntAWMk (P : WTParams) (hP : NoVineRepresentsAtNWMk P) {R : ℕ}
    (b : PrescribedPrimeGarden (2 * R)) (Mk : Set (Stage1.CLVine b.prime.skeleton))
    (hnv : unitBlocks b.prime.skeleton b.totalSigma Mk = [])
    {p N : ℕ} (hp : p < P.D) (hNb : N ≤ P.N (p + 1) ^ 4) (hord : b.layered.garden.order = N)
    (hcan : IsCanonGC (p + 1) b.layered)
    (tt : Fin (2 * R) → ℝ) (htt : ∀ j, tt j ∈ Icc (p : ℝ) (p + 1))
    (F : LeafFamily P (2 * R)) (hF : F.Controlled b.layered)
    (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ)) (s : ℝ) (hs : F.size b.layered ≤ s)
    (g : Fin (2 * R) → Mom P.d → ℂ) (cψ : ℝ) (hc : 1 ≤ cψ) (hgp : ∀ j, GPresented (32 * P.d) (g j) cψ) :
    Stage1Piece.RepresentsInt (P := P) (b.normalizedPiece P.d Mk) N tt base roots (cψ ^ (3 * N) * s)
      (valueSelW F tt base roots b.layered (fun κ => selAt P base b.prime b.sigma κ)
        (fwWeight p g base b.layered)) := by
  have h := noVineN_atWMk P hP b.prime.data b.prime.prime.1 b.layered b.prime.decodes b.prime.gardenEq
    b.totalSigma Mk hnv hp hNb hord hcan tt htt F hF base roots s hs g cψ hc hgp
  have e : NormalizedSplice.GroupPrescription.ofPrescription b.totalSigma = b.sigma :=
    of_extendGroupPrescription b.sigma
  rw [e] at h
  exact h

/-! ## The class level -/

variable {R : ℕ} {p : ℕ} {kind : Bool} {A : Finset (LayeredGarden (2 * R))}

open scoped Classical in
/-- The weighted coarse′ class sum of a unit-free fine′ piece is the weighted value of its representative (main's
`noVine_members_sumMk` with a weight). -/
theorem noVine_members_sumWMk (P : WTParams) (base : Mom P.d) (roots : Fin (2 * R) → (Fin P.d → ℤ))
    (tt : Fin (2 * R) → ℝ) (F : LeafFamily P (2 * R)) {mkF : Stage1Mk.MarkFn (2 * R)} (mkC : Stage1Mk.MarkFn (2 * R))
    (hT : ∀ c : PrescribedPrimeGarden (2 * R), c.FineTransportedAt mkF) (π : PcA R p kind A mkF)
    (hnv : unitBlocks (repPt π).prime.skeleton (repPt π).totalSigma (mkF (repPt π).prime) = [])
    (wt : ∀ LG : LayeredGarden (2 * R), GenDecoration LG.garden P.d roots 0 → ℂ) :
    ∑ LG ∈ membersP (clsPMk mkC π), valueSelW F tt base roots LG (selPMk p kind A P base roots mkF π LG) (wt LG) =
      valueSelW F tt base roots (repPt π).layered (fun κ => selAt P base (repPt π).prime (repPt π).sigma κ)
        (wt (repPt π).layered) := by
  have hmem : (repPt π).layered ∈ membersP (clsPMk mkC π) :=
    Finset.mem_filter.2 ⟨repPt_layered_memMk π, (repPt π).prime.mem_coarse_outputs_selfMk (mkC (repPt π).prime)⟩
  rw [Finset.sum_eq_single (repPt π).layered]
  · congr 1
    funext κ
    exact propext ((selP_noVineMk P base roots hT π hnv _ κ).trans ⟨fun ⟨h, hs⟩ => hs, fun hs => ⟨rfl, hs⟩⟩)
  · intro LG _ hne
    have hnone : ∀ κ : GenDecoration LG.garden P.d roots 0, ¬ selPMk p kind A P base roots mkF π LG κ := by
      intro κ hκ
      obtain ⟨h, -⟩ := (selP_noVineMk P base roots hT π hnv LG κ).1 hκ
      exact hne h.symm
    simp [valueSelW, kernelLeavesSelW, hnone]
  · intro h; exact absurd hmem h

/-- **O4′ at one parameter record**: the vine-free fine′ pieces give `NoVineRepresentsFWMk`. -/
theorem noVineRepresentsFWMk_of_atNWMk (P : WTParams) (hC : 1 ≤ P.C₁) (hL : 1 ≤ P.L)
    (h : NoVineRepresentsAtNWMk P) : NoVineRepresentsFWMk P := by
  intro p hp R hR hRmax N hN1 hN A hA mkF mkC hok tt htt base roots g cψ hc1 hg U s hs0 hb hsize π hv
  have hctrl := controlled_of_boundedW hA U hb
  have hc := hA _ (repPt_layered_memMk π)
  have h1 := noVine_representsIntAWMk P h (repPt π) (mkAt mkF (repPt π)) hv hp hN hc.2.1 hc.1 tt htt U.toLF
    (hctrl _ (repPt_layered_memMk π)) base roots s (hsize _ (repPt_layered_memMk π)) g cψ hc1 hg
  rw [noVine_members_sumWMk P base roots tt U.toLF mkC hok.fine π ((unitBlocks_mkAt_nil_iff mkF (repPt π)).mp hv)
    (fwWeight p g base)]
  refine representsInt_mono_size (by linarith) (by linarith) h1 ?_
  exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hc1 (by omega)) hs0.le

/-- **`NoVineRepresentsFWMk` on the prefix** (O4′ at a marking). -/
theorem noVineRepresentsFWMk : WTPrefix NoVineRepresentsFWMk := by
  intro d hd γ hγ
  obtain ⟨η₀, hη₀, h⟩ := noVine_prefixNWMk d hd γ hγ
  refine ⟨η₀, hη₀, fun η hη φin hφin τ hτ φ hsol => ?_⟩
  obtain ⟨C₁, hC₁, ν₀, hν₀, h2⟩ := h η hη φin hφin τ hτ φ hsol
  refine ⟨C₁, hC₁, ν₀, hν₀, fun ν hν => ?_⟩
  obtain ⟨δ₀, hδ₀, h3⟩ := h2 ν hν
  refine ⟨δ₀, hδ₀, fun δ hδ D hD htime => ?_⟩
  obtain ⟨C₂, hC₂, L₀, hL₀, h4⟩ := h3 δ hδ D hD htime
  refine ⟨C₂, hC₂, L₀, hL₀, fun L hL => ?_⟩
  exact noVineRepresentsFWMk_of_atNWMk _ hC₁ (by show (1 : ℝ) ≤ L; linarith) (h4 L hL)

end WaveTurbulence.Flower.MkUnits
