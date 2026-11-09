/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.Famc.Coarse.Gate
public import WaveTurbulence.Foundations.GammaLow.Famc.Cover.Gate
public import WaveTurbulence.Foundations.GammaLow.Fama.Gate
/-! # Glue to L5a's Stage 1 pieces (packet L5c; for L7)

Main's `LGSpine.stage1_piece_bound_int` (Spine/Stage1PieceBound.lean) uses, for one Stage 1 piece, the coarse spliced
estimate (`hcoarse … hprem`) and the fine spliced estimate (`Cover.fine_spliced_of_subpro_choices … hconc`), with the
premises built from `Stage1Piece.Sound`. Over `𝒱_γ` the piece is L5a's `Fama.Stage1PieceG` and its `Sound`; this module
gives the two premises and the two bounds, for every choice of the analytic data of the piece. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.Famc
open WaveTurbulence.Induct WaveTurbulence.LGSpine

variable {P : WTParams} {R : ℕ}

/-- `Sound` gives the `𝒱_γ` premises of finalsbest1 (main: `hprem` in `stage1_piece_bound_int`). -/
theorem splicedSourcePremisesGamma_of_sound (π : Fama.Stage1PieceG P R) {p : ℕ} {base : Mom P.d}
    {roots : Fin (2 * R) → (Fin P.d → ℤ)} (hπ : π.Sound p base roots) (tt : Fin (2 * R) → ℝ)
    (ctr : GardenDart π.Gsb → Mom P.d) (edge : GardenDart π.Gsb → Mom P.d → ℂ)
    (hinge : (HingeDarts π.Gsb π.Cs.hinges → Mom P.d) → ℂ) (freq : GBranch π.Gsb.tree → ℝ) :
    SplicedSourcePremisesGamma P π.Gsb (π.data tt ctr edge hinge freq) base roots :=
  ⟨hπ.molecule, hπ.connected, hπ.atom_count, hπ.bond_count,
    ⟨π.Cs, hπ.structural, rfl, fun z he hg => hπ.support z he hg⟩⟩

/-- `Sound` gives the decorated subpro conclusions of the counting cover (main: `hconc`). -/
theorem subproConclusionsGamma_of_sound (π : Fama.Stage1PieceG P R) {p : ℕ} {base : Mom P.d}
    {roots : Fin (2 * R) → (Fin P.d → ℤ)} (hπ : π.Sound p base roots) (tt : Fin (2 * R) → ℝ)
    (ctr : GardenDart π.Gsb → Mom P.d) (edge : GardenDart π.Gsb → Mom P.d → ℂ)
    (hinge : (HingeDarts π.Gsb π.Cs.hinges → Mom P.d) → ℂ) (freq : GBranch π.Gsb.tree → ℝ) :
    SubproConclusionsGamma P.γ π.Gsb (π.data tt ctr edge hinge freq) π.Cs P.L P.γ P.η base roots :=
  ⟨hπ.structural, rfl, fun z he hg => hπ.support z he hg, hπ.hingeOutsideFirst, hπ.tripleDesignated,
    hπ.hingeNoLoop⟩

/-- **finalsbest1 for a `𝒱_γ` Stage 1 piece.** -/
theorem stage1Piece_coarse_gamma (hcoarse : CoarseSplicedGammaAt P) (π : Fama.Stage1PieceG P R) {p : ℕ}
    (hp : p < P.D) (hR : 1 ≤ R) (hRmax : R ≤ 10 * P.R (p + 1)) {base : Mom P.d}
    {roots : Fin (2 * R) → (Fin P.d → ℤ)} (hπ : π.Sound p base roots) (tt : Fin (2 * R) → ℝ)
    (ctr : GardenDart π.Gsb → Mom P.d) (edge : GardenDart π.Gsb → Mom P.d → ℂ)
    (hinge : (HingeDarts π.Gsb π.Cs.hinges → Mom P.d) → ℂ) (freq : GBranch π.Gsb.tree → ℝ)
    (hD : SplicedAmplitudeBounds π.Gsb (π.data tt ctr edge hinge freq)) :
    ‖splicedKernel π.Gsb (π.data tt ctr edge hinge freq) P.L P.γ P.η P.δ base roots‖ ≤
      P.C₂ * (P.C₁ * Real.sqrt P.δ) ^ π.Gsb.order *
        P.L ^ (-P.η * π.ladders.totalIncoherency (π.data tt ctr edge hinge freq).layer +
          80 * P.d * (π.Gsb.molecule.rho + (π.data tt ctr edge hinge freq).hinges.card)) :=
  hcoarse p hp R hR hRmax π.Gsb hπ.plain hπ.irreducible hπ.balanced hπ.order_pos hπ.order_le _ hD
    hπ.layer_le π.ladders base roots (splicedSourcePremisesGamma_of_sound π hπ tt ctr edge hinge freq)

/-- **finalsbest2 for a `𝒱_γ` Stage 1 piece** (via the counting cover over `𝒱_γ` and L6's finalcount1). -/
theorem stage1Piece_fine_gamma (hSO : SubObjectsInput) (hfourier : LadderFourierAt P)
    (hcount : FinalCount.FinalCountGammaAt P) (hs : CoverSmall P) (π : Fama.Stage1PieceG P R) {p : ℕ}
    (hp : p < P.D) (hR : 1 ≤ R) (hRmax : R ≤ 10 * P.R (p + 1)) {base : Mom P.d}
    {roots : Fin (2 * R) → (Fin P.d → ℤ)} (hπ : π.Sound p base roots) (tt : Fin (2 * R) → ℝ)
    (ctr : GardenDart π.Gsb → Mom P.d) (edge : GardenDart π.Gsb → Mom P.d → ℂ)
    (hinge : (HingeDarts π.Gsb π.Cs.hinges → Mom P.d) → ℂ) (freq : GBranch π.Gsb.tree → ℝ)
    (hD : SplicedAmplitudeBounds π.Gsb (π.data tt ctr edge hinge freq)) :
    ‖splicedKernel π.Gsb (π.data tt ctr edge hinge freq) P.L P.γ P.η P.δ base roots‖ ≤
      P.C₁ * (P.C₁ * P.δ ^ (-10 * P.ν)) ^ π.Gsb.order *
        P.L ^ (-P.η ^ 6 * (π.Gsb.molecule.rho + (π.data tt ctr edge hinge freq).hinges.card)) *
          P.L ^ (-((R : ℝ) - 1) * (1 / 4 + 1 / 50)) :=
  fineSplicedChoicesGamma hSO P hfourier hcount hs hp hR hRmax π.Gsb hπ.plain hπ.irreducible hπ.balanced
    hπ.order_pos hπ.order_le _ hD hπ.layer_le hπ.molecule hπ.connected hπ.atom_count hπ.bond_count π.Cs base roots
    (subproConclusionsGamma_of_sound π hπ tt ctr edge hinge freq)

end WaveTurbulence.GammaLow.Famc
