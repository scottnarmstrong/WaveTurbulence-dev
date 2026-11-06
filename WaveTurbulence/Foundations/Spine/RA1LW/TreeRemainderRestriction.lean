/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Spine.RA1LW.TreeFam
public import WaveTurbulence.Foundations.Spine.RA1LW.Base
public import WaveTurbulence.Foundations.Spine.RA1LW.TreeRemainderExtension
public import WaveTurbulence.Foundations.Spine.RA1LW.TreeZeroRemainder
public import WaveTurbulence.Foundations.RegAsymp.TreeMixedZero
public import WaveTurbulence.Foundations.Spine.RA1LW.LeafFam
public import WaveTurbulence.Foundations.WaveB.MoleculeStatements
public import WaveTurbulence.Foundations.RegularAsymptotics.RegAsympDraft.CoupleParameters

/-! # The exact causal restriction-norm tree remainder with uniform source constants -/

public section
noncomputable section
namespace WaveTurbulence.RA1Leafwise
open WaveTurbulence.RegAsymp
open MeasureTheory Incoh Links IncohInst ClassJR ApproxNT MainCoef Set

/-- The original tree remainder has the exact source rate and parameter order:
C before delta and the logarithmic order exponent, including empty order. -/
theorem exists_tree_remainder_restriction_bound {d : ℕ} (hd : 3 ≤ d) {γ η B : ℝ}
    (hγ : γ ∈ Ioo (0:ℝ) 1) (hη0 : 0 < η) (hη : η ≤ 1/20)
    (hηγ : η ≤ ((d:ℝ)-1)*(1-γ)) (hηγ' : η ≤ γ) (hB : 0 ≤ B)
    (hηsqrt : 2*η ≤ Real.sqrt η) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ δ ∈ Ioc (0:ℝ) (1/2), ∀ A : ℝ, ∃ L₀ : ℝ,
      ∀ L : ℝ, L₀ ≤ L → ∀ H : LGSpine.LeafProfiles 1 d,
      (∀ z, Fourier.spatialNorm (40*d) (40*d) (addrFam H z) ≤ ENNReal.ofReal B) →
      ∀ n : ℕ, (n:ℝ) ≤ Real.log L^A →
      ∀ X : RegChain, X.wf=true → X.size=2*n → ∀ LG : LayeredGarden 1,
      X.DecodesTree LG.garden → (∀ a, LG.layer a=0) →
      Fourier.mixedRestrictionNorm η (30*d) 0 (timeBoxGt 0 0) Set.univ
        (fun ts k => LGSpine.treeLeaves L γ δ LG H (ts.val 0) (ts.val 1) k.val -
          LGSpine.LeafApp.tree δ 0 H X (LG.garden.sig 0) (ts.val 0) (ts.val 1) k.val) ≤
        ENNReal.ofReal (C*(C*δ)^n*L^(-(gam1L d γ-Real.sqrt η))) := by
  obtain ⟨C,hC,hExt⟩ := exists_tree_remainder_extension_bound hd hγ hη0 hη hηγ hηγ' hB
  refine ⟨C,hC,?_⟩
  intro δ hδ A
  obtain ⟨Le,hLe⟩ := hExt A
  obtain ⟨Ld,hLd⟩ := exists_physical_delta_threshold hη0 hδ.1
  refine ⟨max Le (max Ld 2),?_⟩
  intro L hL H hF n hnlog X hwf hsize LG hX h0
  have hL1 : 1 ≤ L := by linarith [(le_max_right Ld 2).trans ((le_max_right Le _).trans hL)]
  have hδlower := hLd L ((le_max_left Ld 2).trans ((le_max_right Le _).trans hL))
  have hbox (t : timeBoxGt 0 0) :
      ((t.val 0∈Icc (0:ℝ) 1) ∧ (t.val 1∈Icc (0:ℝ) 1)) ∧ t.val 1<t.val 0 := by
    simpa only [timeBoxGt,timeBox,Set.mem_ofPred_eq,zero_add] using t.property
  by_cases hn0 : n=0
  · have hEq (t : timeBoxGt 0 0) (k : (Set.univ : Set (Mom d))) :
        (0:ℂ)=LGSpine.treeLeaves L γ δ LG H (t.val 0) (t.val 1) k.val -
          LGSpine.LeafApp.tree δ 0 H X (LG.garden.sig 0) (t.val 0) (t.val 1) k.val := by
      rw [KTstar_eq_app_of_tree_size_zero hd hwf (by omega) LG hX h0 hL1 δ γ hδ.1.ne'
        hB hF (hbox t).1.2.1 (hbox t).2 (hbox t).1.1.2 k.val,sub_self]
    have hh := Fourier.mixedRestrictionNorm_le_extension (θ := η) (Λ₁ := 30*d) (Λ₂ := 0)
      (fun _ _ => (0:ℂ)) hEq
    rw [tree_mixedFourierNorm_zero] at hh
    exact hh.trans bot_le
  · have hlen : (X.treeLinks (LG.garden.sig 0)).length=n := by
      have hh := chain_linksAt_length X (LG.garden.sig 0) ((0:Fin 1),[])
      change (X.treeLinks (LG.garden.sig 0)).length*2=X.size at hh
      omega
    obtain ⟨E,hE,hEnorm⟩ := hLe L ((le_max_left _ _).trans hL) δ hδlower hδ.2 H hF X hwf LG hX h0
      (by omega) (by simpa only [hlen] using hnlog)
    have hEq (t : timeBoxGt 0 0) (k : (Set.univ : Set (Mom d))) :
        E t.val k.val=LGSpine.treeLeaves L γ δ LG H (t.val 0) (t.val 1) k.val -
          LGSpine.LeafApp.tree δ 0 H X (LG.garden.sig 0) (t.val 0) (t.val 1) k.val := by
      have ht : (![t.val 0,t.val 1] : Fin 2 → ℝ)=t.val := by funext i; fin_cases i <;> rfl
      rw [← ht]
      exact hE _ _ (hbox t).1.2.1 (hbox t).2 (hbox t).1.1.2 k.val
    apply (Fourier.mixedRestrictionNorm_le_extension E hEq).trans
    apply hEnorm.trans
    rw [hlen]
    apply ENNReal.ofReal_le_ofReal
    apply mul_le_mul_of_nonneg_left _ (mul_nonneg (zero_le_one.trans hC)
      (pow_nonneg (mul_nonneg (zero_le_one.trans hC) hδ.1.le) n))
    apply Real.rpow_le_rpow_of_exponent_le hL1
    change -gamma1 d γ+2*η ≤ -(gam1L d γ-Real.sqrt η)
    have hg : gamma1 d γ = gam1L d γ := rfl
    rw [hg]
    linarith only [hηsqrt]

end WaveTurbulence.RA1Leafwise
