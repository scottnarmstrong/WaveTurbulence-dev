/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.RA1LW.LeafFam
public import WaveTurbulence.Foundations.Spine.RA1LW.Base
public import WaveTurbulence.Foundations.Spine.RA1LW.PhysicalZeroOrder

/-! # Literal kernel-minus-app vanishes at order zero -/

public section
noncomputable section
namespace WaveTurbulence.RA1Leafwise
open WaveTurbulence.RegAsymp
open Links Set

/-- The trivial recursive leading term is the original input. -/
theorem triv_app {d : ℕ} (δ : ℝ) (H : LGSpine.LeafProfiles 2 d) (t s : ℝ) (k : Mom d) :
    LGSpine.LeafApp.couple δ 0 H RegCpl.triv t s k = (H (0,[]) k:ℂ) := by
  have hz : zetaOfTrees ![1,-1] ![RegCpl.triv.trees.1,RegCpl.triv.trees.2] = 1 := by
    unfold zetaOfTrees
    apply Finset.prod_eq_one
    intro j _
    fin_cases j <;> rfl
  simp only [LGSpine.LeafApp.couple,RegCpl.dominant,ite_true,RegCpl.size,pow_zero,Nat.zero_div,one_mul,hz,
    RegCpl.links,RegCpl.linksAt,chosenSet,List.map_nil,List.toFinset_nil,specialSets,
    Finset.powerset_empty,Finset.filter_singleton,IsSpecialSet,Finset.forall_mem_empty_iff,ite_true,Finset.sum_singleton,specialWeight,Finset.prod_empty,RegCpl.JB,
    Complex.ofReal_one,LGSpine.LeafApp.cplMstar]

/-- The normalized zero-order physical error is exactly zero; it needs
neither a positive-order NT estimate nor a spatial norm hypothesis. -/
theorem coupleLeaves_eq_app_of_size_zero {d : ℕ} (L γ δ : ℝ) (H : LGSpine.LeafProfiles 2 d)
    (LG : LayeredGarden 2) (h0 : ∀ a, LG.layer a = 0)
    {Q : RegCpl} (hwf : Q.wf = true) (hsize : Q.size = 0) (hQ : Q.Decodes LG.garden)
    {t s : ℝ} (ht : t ∈ Icc (0:ℝ) 1) (hs : s ∈ Icc (0:ℝ) 1) (k : Mom d) :
    LGSpine.coupleLeaves L γ δ LG H t s k = LGSpine.LeafApp.couple δ 0 H Q t s k := by
  obtain rfl := regCpl_eq_triv_of_wf_size_zero Q hwf hsize
  rw [coupleLeaves_triv L γ δ H LG h0 hQ ht hs k,triv_app]

end WaveTurbulence.RA1Leafwise
