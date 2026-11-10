/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Vine.A.VineSelectedTransport
public import WaveTurbulence.Foundations.Vine.A.VineUnitCover
/-! VINE-A2: actual splice units are good atom sets for a selected unit twist.
Their molecular block and CL orientation transport with the source atom map. -/
@[expose] public section
open WaveTurbulence.Induct
set_option autoImplicit false
namespace WaveTurbulence.VineA
open Finset WaveTurbulence.Stage1 WaveTurbulence.RedSplice WaveTurbulence.Twist
open WaveTurbulence.LGSpine.SourceVine
variable {w : ℕ} {G : Garden w}

private theorem disjoint_members (l : List (CLBlock G))
    (hl : l.Pairwise (fun u v => Disjoint u.atoms v.atoms))
    {u v : CLBlock G} (hu : u ∈ l) (hv : v ∈ l) (hne : u ≠ v) : Disjoint u.atoms v.atoms := by
  induction l generalizing u v with
  | nil => simp only [List.not_mem_nil] at hu
  | cons a l ih =>
    obtain ⟨ha, ht⟩ := List.pairwise_cons.mp hl
    rcases List.mem_cons.mp hu with rfl | hut
    · exact ha v ((List.mem_cons.mp hv).resolve_left (Ne.symm hne))
    · rcases List.mem_cons.mp hv with rfl | hvt
      · exact (ha u hut).symm
      · exact ih ht hut hvt hne

/-- Pairwise disjoint units that share an atom are the same unit. -/
theorem units_eq_of_mem_inter (l : List (CLBlock G))
    (hl : l.Pairwise (fun u v => Disjoint u.atoms v.atoms))
    {u v : CLBlock G} (hu : u ∈ l) (hv : v ∈ l)
    {z : GBranch G.tree} (hz : z ∈ u.atoms) (hz' : z ∈ v.atoms) : u = v := by
  by_contra hne
  exact (disjoint_left.mp (disjoint_members l hl hu hv hne) hz) hz'

/-- The CL orientation fixes both ordered joints of a block with a given atom set. -/
theorem clBlock_eq_of_atoms {u v : CLBlock G} (h : u.atoms = v.atoms) : u = v := by
  have hj := Vine.block_joints_unique G.molecule (h ▸ u.isBlock) v.isBlock
  have hu : u.upper = v.upper := by
    rcases Mole.finset_pair_eq_pair_iff.mp hj with ⟨ha, _⟩ | ⟨ha, _⟩
    · exact ha
    · exact (u.cl.1 (by rw [h, ha]; exact v.cl.2)).elim
  have hv : u.lower = v.lower := by
    rcases Mole.finset_pair_eq_pair_iff.mp hj with ⟨_, hb⟩ | ⟨ha, hb⟩
    · exact hb
    · exact (u.isBlock.2.2.2.1 (hu.trans hb.symm)).elim
  cases u
  cases v
  cases h
  cases hu
  cases hv
  rfl

/-- B1b (Mk-general form of `unitBlocks_good`). -/
theorem unitBlocks_goodMk (Z : TwistGroupSite G) (σ : Prescription G)
    {Mk : Set (Stage1.CLVine _)} (hsel : ∃ c ∈ vinesV0 (Mk := Mk) G σ, c.atoms = Z.S0) {u : CLBlock G} (hu : u ∈ unitBlocks (Mk := Mk) G σ) :
    Z.Good u.atoms := by
  obtain ⟨c, hc, hat⟩ := hsel
  obtain ⟨_, v, hv, hcv⟩ := (vinesV0_iff_unit_cover_diffMk (Mk := Mk) G σ c).mp hc
  by_cases huv : u = v
  · subst v
    exact Or.inl (hat ▸ hcv)
  · right
    intro x hx hxu
    exact ((disjoint_left.mp (disjoint_members (unitBlocks (Mk := Mk) G σ)
      (unitBlocks_pairwiseMk (Mk := Mk) (Mole.garden_isMolecule G) σ) hu hv huv) hxu)
      (hcv (hat.symm ▸ hx))).elim

/-- The transported actual unit, with its CL property derived from source geometry. -/
noncomputable def unitImage (Z : TwistGroupSite G) (u : CLBlock G) (hgood : Z.Good u.atoms) :
    CLBlock Z.target where
  atoms := Z.iso.img u.atoms
  upper := Z.iso.e u.upper
  lower := Z.iso.e u.lower
  isBlock := Z.iso.isBlock_img u.isBlock
  cl := ⟨fun h => u.cl.1 ((Z.ip_map hgood u.isBlock.2.1).mp h),
    (Z.ip_map hgood u.isBlock.2.2.1).mpr u.cl.2⟩

end WaveTurbulence.VineA
