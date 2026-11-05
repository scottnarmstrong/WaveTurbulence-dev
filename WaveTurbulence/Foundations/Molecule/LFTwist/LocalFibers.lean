/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Molecule.LFTwist.IdentityConstruction
public import WaveTurbulence.Foundations.Molecule.LFTwist.FiniteCandidates
public import WaveTurbulence.Foundations.Molecule.CanonDraft.Finite

/-! # The exact two admissible local LF fibers

Each fiber is the range of actual literal LF constructions inside a finite
coordinate space. The two fibers may differ. They are never identified or
paired by an assumed bijection. This is the combinatorial interface used by
V5 before its separate analytic leading-term cancellation.
-/

public section
namespace WaveTurbulence.LFTwist
open TTree Reg Reg.Skeleton Twist Links RegRed

namespace LFSource
variable {w p : ℕ} {kind : Bool} {LG : LayeredGarden w} (s : LFSource p kind LG)

@[expose] def fiberOutputs (ε : Bool) : Set (LayeredGarden w) :=
  {LH | ∃ h : LFConstruction s ε, h.output = LH}

theorem fiberOutputs_finite (ε : Bool) : (s.fiberOutputs ε).Finite := by
  apply (Canon.finite_layeredGardens w LG.garden.order p).subset
  intro LH hL
  obtain ⟨h,rfl⟩ := hL
  exact ⟨h.order.le,h.canonical.criterion.1⟩

theorem mem_false_fiber : LG ∈ s.fiberOutputs false := s.identity_construction

end LFSource
namespace LFConstruction
variable {w p : ℕ} {kind : Bool} {LG : LayeredGarden w} {s : LFSource p kind LG} {ε : Bool}
    (h : LFConstruction s ε)

theorem data_size_le : h.data.size ≤ LG.garden.order := by
  have ho : h.output.garden.order = (s.chosen ε).order + h.data.size := h.data.forest_order (s.chosen_plain ε)
  rw [h.order] at ho
  omega

/-- The full final code and layering, with genuine finite bounds derived from
canonical output and exact order preservation. -/
@[expose] noncomputable def coordinate :
    ReconstructionLayerFamily (s.chosen ε) (s.chosen_plain ε) LG.garden.order p :=
  ⟨⟨h.data,h.data_size_le⟩,⟨h.outLayer,h.out_isLayering,h.canonical.criterion.1⟩⟩

theorem coordinate_garden : reconstructionFamilyGarden h.coordinate = h.output := rfl

end LFConstruction
namespace LFSource
variable {w p : ℕ} {kind : Bool} {LG : LayeredGarden w} (s : LFSource p kind LG)

/-- Exact admissible final coordinates for one skeleton choice, with no
unrealized candidates admitted. Different witnesses of the same final
coordinate do not add multiplicity. -/
@[expose] def AdmissibleCoordinate (ε : Bool) :=
  {c : ReconstructionLayerFamily (s.chosen ε) (s.chosen_plain ε) LG.garden.order p //
    ∃ h : LFConstruction s ε, h.coordinate = c}

instance (ε : Bool) : Finite (s.AdmissibleCoordinate ε) := by
  unfold AdmissibleCoordinate
  infer_instance

noncomputable instance (ε : Bool) : Fintype (s.AdmissibleCoordinate ε) := Fintype.ofFinite _

@[expose] noncomputable def coordinateGarden {ε : Bool} (c : s.AdmissibleCoordinate ε) : LayeredGarden w :=
  reconstructionFamilyGarden c.1

/-- Every admissible coordinate and every actual local construction have
exactly the asserted actual garden correspondence. -/
theorem coordinateGarden_mem {ε : Bool} (c : s.AdmissibleCoordinate ε) :
    s.coordinateGarden c ∈ s.fiberOutputs ε := by
  obtain ⟨h,he⟩ := c.2
  exact ⟨h,congrArg reconstructionFamilyGarden he⟩

theorem fiberOutputs_eq_coordinate_range (ε : Bool) :
    s.fiberOutputs ε = Set.range (s.coordinateGarden (ε := ε)) := by
  ext LH
  constructor
  · rintro ⟨h,rfl⟩
    exact ⟨⟨h.coordinate,h,rfl⟩,rfl⟩
  · rintro ⟨c,rfl⟩
    exact s.coordinateGarden_mem c

/-- Both skeleton choices with their own, possibly different, admissible fibers. -/
@[expose] def LocalCoordinates := Σ ε : Bool, s.AdmissibleCoordinate ε

noncomputable instance : Fintype s.LocalCoordinates :=
  inferInstanceAs (Fintype (Σ ε : Bool, s.AdmissibleCoordinate ε))

/-- Finite-sum decomposition into the actual two fibers, without an equal-fiber
assumption. Terms may later be estimates or actual regional kernel weights. -/
theorem sum_localCoordinates {M : Type*} [AddCommMonoid M] (f : s.LocalCoordinates → M) :
    (∑ c, f c) = (∑ c : s.AdmissibleCoordinate false, f ⟨false,c⟩) +
      ∑ c : s.AdmissibleCoordinate true, f ⟨true,c⟩ := by
  have h := Fintype.sum_sigma (fun c : (Σ ε : Bool, s.AdmissibleCoordinate ε) => f c)
  simp only [Fintype.sum_bool] at h
  exact h.trans (add_comm _ _)

end LFSource
end WaveTurbulence.LFTwist
