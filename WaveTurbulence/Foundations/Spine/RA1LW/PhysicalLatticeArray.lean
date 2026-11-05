/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.RA1LW.LeafFam
public import WaveTurbulence.Foundations.Spine.RA1LW.SourcePhaseBound
public import WaveTurbulence.Foundations.Spine.RA1LW.ActualLeafSpectrum
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.WickSupport
public import WaveTurbulence.Foundations.RegAsymp.SourceLatticeLocalization

/-! # Literal physical couple kernel on the original two-coordinate lattice array -/

@[expose] public section
noncomputable section
namespace WaveTurbulence.RA1Leafwise
open WaveTurbulence.RegAsymp
open Links Incoh

/-- Repackage the original pair per link as its literal two-entry array. -/
def linkPairArrayEquiv (n : ℕ) (V : Type*) :
    (Fin n → V × V) ≃ ((Fin n × Fin 2) → V) where
  toFun θ p := if p.2=0 then (θ p.1).1 else (θ p.1).2
  invFun p j := (p (j,0),p (j,1))
  left_inv θ := by funext j; simp
  right_inv p := by
    funext z
    obtain ⟨j,i⟩ := z
    fin_cases i <;> simp

/-- The original squared Wick factor times the original physical phase
integral, with the original decoration equivalence retained literally. -/
def coupleLatticeTimeCoefficient {d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden 2)
    {Q : RegCpl} (hQ : Q.Decodes LG.garden) (t s : ℝ) (k : Mom d)
    (p : (Fin Q.links.length × Fin 2) → Fin d → ℤ) : ℂ :=
  ((∏ j, epsXY (p (j,0)) (p (j,1))^2:ℝ):ℂ) *
    phaseIntegral L γ δ LG.garden
      (kDomain LG (fun b => if b.1.1=0 then t else s) 0) 0
      (cosetDecoration LG.garden L k
        ((integerLinkEquiv hQ hQ.1 d).symm (fun j => (p (j,0),p (j,1)))).val)

/-- The source time/Wick coefficient is uniformly bounded before any
Fourier representation or source lattice/cell exchange. -/
theorem norm_coupleLatticeTimeCoefficient_le_one {d : ℕ} (L γ δ : ℝ) (LG : LayeredGarden 2)
    (h0 : ∀ a, LG.layer a = 0) {Q : RegCpl} (hQ : Q.Decodes LG.garden)
    {t s : ℝ} (ht : t ≤ 1) (hs : s ≤ 1) (k : Mom d)
    (p : (Fin Q.links.length × Fin 2) → Fin d → ℤ) :
    ‖coupleLatticeTimeCoefficient L γ δ LG hQ t s k p‖ ≤ 1 := by
  rcases prod_epsXY_sq_cases (fun j => (p (j,0),p (j,1))) with hp | hp
  · simp only [coupleLatticeTimeCoefficient,hp,Complex.ofReal_zero,zero_mul,norm_zero,zero_le_one]
  · simp only [coupleLatticeTimeCoefficient,hp,Complex.ofReal_one,one_mul]
    exact norm_phaseIntegral_layer_zero_le_one L γ δ LG h0 hQ.1.1 ht hs 0 0 _

/-- Exact reindexing of the ORIGINAL physical kernel, with its original
input product expressed by the actual source momentum data. -/
theorem coupleLeaves_latticeArray {d : ℕ} (L γ δ : ℝ) (H : LGSpine.LeafProfiles 2 d)
    (LG : LayeredGarden 2) {Q : RegCpl} (hQ : Q.Decodes LG.garden)
    (t s : ℝ) (k : Mom d) :
    LGSpine.coupleLeaves L γ δ LG H t s k =
      (coupling d L γ δ:ℂ)^LG.garden.order*LG.garden.zeta *
      ∑' p : (Fin Q.links.length × Fin 2) → Fin d → ℤ,
        coupleLatticeTimeCoefficient L γ δ LG hQ t s k p *
          (coupleMomentumData hQ hQ.1).sourceLeafWeight (leafFam hQ hQ.1 H) k
            (fun i j => latticePoint L (p (i,j))) := by
  rw [coupleLeaves_integerLinkEquiv L γ δ H LG hQ hQ.1 t s k]
  apply congrArg (fun v : ℂ => (coupling d L γ δ:ℂ)^LG.garden.order*LG.garden.zeta*v)
  rw [← (linkPairArrayEquiv Q.links.length (Fin d → ℤ)).symm.tsum_eq]
  apply tsum_congr
  intro p
  dsimp only [linkPairArrayEquiv,Equiv.coe_fn_symm_mk]
  rw [actual_coset_leafProduct_eq hQ hQ.1 _ L k H]
  have he : (fun i j => if j=0 then latticePoint L (p (i,0)) else latticePoint L (p (i,1))) =
      (fun i j => latticePoint L (p (i,j))) := by
    funext i j
    fin_cases j <;> simp
  rw [he]
  rfl

end WaveTurbulence.RA1Leafwise
