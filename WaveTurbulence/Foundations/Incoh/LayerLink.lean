/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Incoh.LinkFactor
public import WaveTurbulence.Foundations.Incoh.BoxProduct

/-!
# Layered link data and the actual product time integral

TARGET (incohproof9)–(incohproof16). Link data contain only the two integer
layers, orientation, centers and Fourier shifts. The time-order domain is
an actual measurable set supplied by the later tree/couple construction.
-/

public section

noncomputable section

open MeasureTheory Set

namespace WaveTurbulence.Incoh

variable {d n : ℕ}

/-- Source data of one linked pair of branching nodes; there are no estimate fields. -/
structure LayerLink (d : ℕ) extends LinkParameters d where
  leftLayer : ℤ
  rightLayer : ℤ
  orientation : ℤˣ

/-- The unit time box belonging to a link, TARGET (incohproof11). -/
@[expose] def linkBox (Q : LayerLink d) : Set (Fin 2 → ℝ) :=
  Icc ![(Q.leftLayer : ℝ), (Q.rightLayer : ℝ)]
    ![(Q.leftLayer : ℝ) + 1, (Q.rightLayer : ℝ) + 1]

/-- The incoherent flag is determined by inequality of the actual integer layers. -/
@[expose] def LayerLink.IsIncoherent (Q : LayerLink d) : Prop := Q.leftLayer ≠ Q.rightLayer

/-- Number of incoherent links, not an assumed upper bound for the kernel. -/
@[expose] def incoherenceCount (Q : Fin n → LayerLink d) : ℕ :=
  by
    classical
    exact (Finset.univ.filter fun i => (Q i).IsIncoherent).card

/-- The literal time-dependent lattice factor in TARGET (incohproof10). -/
@[expose] def linkTimeFactor (L γ δ : ℝ) (Q : LayerLink d) (t : Fin 2 → ℝ) : ℂ :=
  linkLatticeSum L (((Q.orientation : ℤ) : ℝ) * δ * L ^ (2 * γ) * (t 0 - t 1)) Q.toLinkParameters

/-- Continuity follows from the proved finite support of the literal lattice amplitude. -/
theorem continuous_linkTimeFactor {L : ℝ} (hL : 0 < L) (γ δ : ℝ) (Q : LayerLink d) :
    Continuous (linkTimeFactor L γ δ Q) :=
  (continuous_linkLatticeSum hL Q.toLinkParameters).comp (by fun_prop)

/-- Each actual link factor is integrable on its own unit time box. -/
theorem integrableOn_linkTimeFactor {L : ℝ} (hL : 0 < L) (γ δ : ℝ) (Q : LayerLink d) :
    IntegrableOn (linkTimeFactor L γ δ Q) (linkBox Q) :=
  (continuous_linkTimeFactor hL γ δ Q).integrableOn_Icc

/-- The coupling-normalized product integral in TARGET (incohproof9). -/
@[expose] def normalizedLinkIntegral (L γ δ : ℝ) (Q : Fin n → LayerLink d)
    (I : Set (Fin n → Fin 2 → ℝ)) : ℂ :=
  ((δ / (2 * L ^ ((d : ℝ) - γ))) ^ (2 * n) : ℝ) *
    ∫ t in I, ∏ i, linkTimeFactor L γ δ (Q i) (t i)

/-- The actual product integrand is integrable on every source subdomain of the link boxes. -/
theorem integrableOn_linkProduct {L : ℝ} (hL : 0 < L) (γ δ : ℝ) (Q : Fin n → LayerLink d)
    {I : Set (Fin n → Fin 2 → ℝ)} (hI : I ⊆ univ.pi (fun i => linkBox (Q i))) :
    IntegrableOn (fun t => ∏ i, linkTimeFactor L γ δ (Q i) (t i)) I :=
  (integrableOn_pi_product (fun i => integrableOn_linkTimeFactor hL γ δ (Q i))).mono_set hI

/-- Product domination for the literal source factors, before their one-link estimates are inserted. -/
theorem norm_linkProduct_integral_le {L : ℝ} (hL : 0 < L) (γ δ : ℝ) (Q : Fin n → LayerLink d)
    {I : Set (Fin n → Fin 2 → ℝ)} (hI : I ⊆ univ.pi (fun i => linkBox (Q i))) :
    ‖∫ t in I, ∏ i, linkTimeFactor L γ δ (Q i) (t i)‖ ≤
      ∏ i, ∫ t in linkBox (Q i), ‖linkTimeFactor L γ δ (Q i) t‖ :=
  norm_setIntegral_pi_product_le hI (fun i => integrableOn_linkTimeFactor hL γ δ (Q i))

end WaveTurbulence.Incoh
