/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPtw.TreeBound
public import WaveTurbulence.Foundations.Flower.ProtCut.CapKer
public import WaveTurbulence.Foundations.Flower.ProtCut.MultLocal
public import WaveTurbulence.Foundations.Incoh.MixedSpatialEnvelope
public import WaveTurbulence.Foundations.Incoh.SpatialCenterDecay

/-! # D6a PROT-PTW: cap couples

A cap couple is the input of its lone leaf times the paired tree of its chain (ProtCut `CapData.kernelProt_cap`).
The D6 multiplier transports: the filters and the dagger read only tree `0` (`βc`, `termChild_cap`); the star weights
become a star factor presented by the star root measure with the transported rows `treeRow ∘ ρ`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open MeasureTheory Set
open scoped ENNReal

namespace WaveTurbulence.Flower.ProtPtw
open WaveTurbulence.Incoh WaveTurbulence.IncohInst WaveTurbulence.IncohLeafwise WaveTurbulence.LGSpine
open WaveTurbulence.Flower.FiltLink WaveTurbulence.Flower.IncTop WaveTurbulence.Cut2A
open WaveTurbulence.Flower.ProtCut WaveTurbulence.Flower.ProtDefs WaveTurbulence.Links

variable {d : ℕ} {X : RegChain} {LG : LayeredGarden 2} {LG1 : LayeredGarden 1}

theorem omegaNode_cap (D : CapData X LG LG1) (K : GNode LG1.garden.tree → Mom d) (b : GBranch LG1.garden.tree) :
    omegaNode LG.garden (fun a => K (D.ρ a)) (D.βc b) = omegaNode LG1.garden K b := by
  unfold omegaNode
  simp only [D.βc_child, D.βc_toNode, D.ρ_ι]

theorem filtWeight_cap (D : CapData X LG LG1) (F : Finset (GBranch LG.garden.tree))
    (ann : GBranch LG.garden.tree → Bool) (M : GBranch LG.garden.tree → ℝ) (K : GNode LG1.garden.tree → Mom d) :
    filtWeight F ann M (fun a => K (D.ρ a)) =
      filtWeight (F.map D.βc.symm.toEmbedding) (fun b => ann (D.βc b)) (fun b => M (D.βc b)) K := by
  unfold filtWeight
  rw [Finset.prod_map]
  refine Finset.prod_congr rfl fun b _ => ?_
  simp only [Equiv.coe_toEmbedding, Equiv.apply_symm_apply]
  rw [← omegaNode_cap D K (D.βc.symm b), Equiv.apply_symm_apply]

/-- The transported star factor. -/
def capStar (D : CapData X LG LG1) (S : Finset (GNode LG.garden.tree)) (ω : GNode LG.garden.tree → Star d → ℂ) :
    (GNode LG1.garden.tree → Mom d) → ℂ :=
  fun K => starWeight S ω (fun a => K (D.ρ a))

theorem capStar_eq_value (D : CapData X LG LG1) (J : ℕ) (S : Finset (GNode LG.garden.tree))
    (ω : GNode LG.garden.tree → Star d → ℂ) (c : GNode LG.garden.tree → ℝ) (h : ∀ a ∈ S, StarPresented J (ω a) (c a))
    (L : ℝ) (k : Mom d) (p : Fin (X.treeLinks (LG1.garden.sig 0)).length × Fin 2 → Fin d → ℤ) :
    capStar D S ω (cosetDecoration LG1.garden L k
        (treeDecOfParams D.dec1 (0 : Fin d → ℤ) (fun j => (p (j, 0), p (j, 1)))).1) =
      ((starRootMeasure J S ω c h (fun a => treeRow D.dec1 (D.ρ a))).at k).value (pairedLattice L p) := by
  unfold capStar
  rw [starRootMeasure_value]
  refine Finset.prod_congr rfl fun a _ => ?_
  congr 1
  unfold starMomenta rowStar
  congr 1
  funext s
  exact tree_coset_eq_row D.dec1 L k p (D.ρ (starNode a s))

/-- **The D6 multiplier of a cap couple is a D6 multiplier of its paired tree.** -/
theorem capM_protMult (D : CapData X LG LG1) (S : Finset (GNode LG.garden.tree))
    (ω : GNode LG.garden.tree → Star d → ℂ) (F : Finset (GBranch LG.garden.tree)) (M : GBranch LG.garden.tree → ℝ)
    (Sel : Finset (GBranch LG.garden.tree)) (M₂ : ℝ) (Fu : Finset (GBranch LG.garden.tree))
    (Mu : GBranch LG.garden.tree → ℝ) (ind : (GNode LG.garden.tree → Mom d) → ℝ) :
    D.capM (fun κ => starWeight S ω κ *
        filtWeight (F ∪ Sel) (fun b => decide (b ∈ Sel)) (fun b => if b ∈ Sel then M₂ else M b) κ *
        filtWeight Fu (fun _ => false) Mu κ * (ind κ : ℂ)) =
      protMultG (capStar D S ω) (F.map D.βc.symm.toEmbedding) (fun b => M (D.βc b))
        (Sel.map D.βc.symm.toEmbedding) M₂ (Fu.map D.βc.symm.toEmbedding) (fun b => Mu (D.βc b))
        (fun K => ind (fun a => K (D.ρ a))) := by
  funext K
  unfold CapData.capM protMultG capStar
  simp only
  rw [filtWeight_cap D, filtWeight_cap D, Finset.map_union]
  have hmem (b : GBranch LG1.garden.tree) : (b ∈ Sel.map D.βc.symm.toEmbedding) ↔ D.βc b ∈ Sel := by
    rw [Finset.mem_map_equiv]; simp
  simp only [hmem]

theorem capStar_mass_le (D : CapData X LG LG1) (S : Finset (GNode LG.garden.tree))
    (ω : GNode LG.garden.tree → Star d → ℂ) (cω : GNode LG.garden.tree → ℝ)
    (hω : ∀ a ∈ S, StarPresented (30 * d) (ω a) (cω a)) (k : Mom d) :
    ENNReal.ofReal ((starRootMeasure (30 * d) S ω cω hω (fun a => treeRow D.dec1 (D.ρ a))).at k).mass ≤
      ∏ a ∈ S, ENNReal.ofReal (cω a) := by
  refine le_trans ?_ (starRootMeasure_momentMass_le (30 * d) S ω cω hω (fun a => treeRow D.dec1 (D.ρ a)))
  rw [RootMeasure.at_mass, SpatialMeasure.mass,
    ofReal_integral_norm_eq_lintegral_enorm (starRootMeasure (30 * d) S ω cω hω _).base.amplitude_integrable,
    RootMeasure.momentMass]
  apply lintegral_mono
  intro a
  have : (1 : ℝ≥0∞) ≤ ENNReal.ofReal ((1 + ‖(starRootMeasure (30 * d) S ω cω hω
      (fun a => treeRow D.dec1 (D.ρ a))).root a‖) ^ (30 * d)) := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal (one_le_pow₀ (by linarith [norm_nonneg ((starRootMeasure (30 * d) S ω cω hω
      (fun a => treeRow D.dec1 (D.ρ a))).root a)]))
  calc ‖(starRootMeasure (30 * d) S ω cω hω (fun a => treeRow D.dec1 (D.ρ a))).base.amplitude a‖ₑ =
      1 * ‖(starRootMeasure (30 * d) S ω cω hω (fun a => treeRow D.dec1 (D.ρ a))).base.amplitude a‖ₑ :=
        (one_mul _).symm
    _ ≤ _ := mul_le_mul' this le_rfl

/-- A leaf profile with normalized spatial norm is bounded by one. -/
theorem enorm_le_of_spatialNorm {f : Mom d → ℂ} {K M : ℕ} (h : Fourier.spatialNorm K M f ≤ ENNReal.ofReal 1)
    (k : Mom d) : ‖f k‖ₑ ≤ 1 := by
  have h0 := momentumSupNorm_derivative_le_spatialNorm (N := K) (M := M) f (Nat.zero_le K) (Fin.elim0)
  rw [Fourier.momentumDerivative_zero] at h0
  have h1 : ‖f k‖ₑ ≤ Fourier.momentumSupNorm M f := by
    unfold Fourier.momentumSupNorm
    refine le_trans ?_ (le_iSup _ k)
    calc ‖f k‖ₑ = 1 * ‖f k‖ₑ := (one_mul _).symm
      _ ≤ _ := by
          gcongr
          rw [← ENNReal.ofReal_one]
          exact ENNReal.ofReal_le_ofReal (one_le_pow₀ (one_le_momentumBracket k))
  exact (h1.trans (h0.trans h)).trans_eq ENNReal.ofReal_one

end WaveTurbulence.Flower.ProtPtw
