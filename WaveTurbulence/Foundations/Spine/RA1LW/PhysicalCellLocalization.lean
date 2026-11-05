/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.RA1LW.LeafFam
public import WaveTurbulence.Foundations.Spine.RA1LW.PhysicalLatticeArray
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.CoupleCellCover

/-! # Exact absolute cell localization of the original physical couple kernel -/

public section
noncomputable section
namespace WaveTurbulence.RA1Leafwise
open WaveTurbulence.RegAsymp
open Links Incoh

/-- The ORIGINAL KQstar lattice sum equals the absolutely rearranged
sum of its literal source cells. Its bounded time/Wick coefficient is
proved from the actual unit phase bound, not assumed as a representation. -/
theorem coupleLeaves_eq_sourceCell_lattice {d K M : ℕ} {L : ℝ} (hL : 1 ≤ L) (γ δ : ℝ)
    (LG : LayeredGarden 2) (h0 : ∀ a, LG.layer a = 0) {Q : RegCpl} (hQ : Q.Decodes LG.garden)
    {H : LGSpine.LeafProfiles 2 d} {B : ℝ} (hK : d+1 ≤ K) (hM : 2*d ≤ M) (hB : 0 ≤ B)
    (hF : ∀ a, Fourier.spatialNorm K M (leafFam hQ hQ.1 H a) ≤ ENNReal.ofReal B)
    (S : (Fin (2*Q.links.length+1) → Fin d → ℤ) →
      Finset ((Fin Q.links.length × Fin 2) → Fin d → ℤ)) {Ccover : ℝ}
    (hS : ∀ c, ((S c).card:ℝ) ≤ Ccover^Q.links.length)
    {t s : ℝ} (ht : t ≤ 1) (hs : s ≤ 1) (k : Mom d)
    (hcover : ∀ c x, (coupleMomentumData hQ hQ.1).inputCellWeight c k x ≠ 0 →
      ∀ z, halfCellArrayWeight z (fun p : Fin Q.links.length × Fin 2 => x p.1 p.2) ≠ 0 → z ∈ S c) :
    LGSpine.coupleLeaves L γ δ LG H t s k =
      (coupling d L γ δ:ℂ)^LG.garden.order*LG.garden.zeta *
      ∑' u : SourceCellIndex S, ∑' p : (Fin Q.links.length × Fin 2) → Fin d → ℤ,
        coupleLatticeTimeCoefficient L γ δ LG hQ t s k p *
          (coupleMomentumData hQ hQ.1).sourceCellWeight (leafFam hQ hQ.1 H) S k
            (fun i j => latticePoint L (p (i,j))) u := by
  rw [coupleLeaves_latticeArray L γ δ H LG hQ t s k]
  apply congrArg (fun v : ℂ => (coupling d L γ δ:ℂ)^LG.garden.order*LG.garden.zeta*v)
  exact source_lattice_eq_tsum_cells (coupleMomentumData hQ hQ.1)
    (leafFam hQ hQ.1 H) S k hcover hS hL hK hM hB hF
    (coupleLatticeTimeCoefficient L γ δ LG hQ t s k)
    (fun p => norm_coupleLatticeTimeCoefficient_le_one L γ δ LG h0 hQ ht hs k p)

end WaveTurbulence.RA1Leafwise
