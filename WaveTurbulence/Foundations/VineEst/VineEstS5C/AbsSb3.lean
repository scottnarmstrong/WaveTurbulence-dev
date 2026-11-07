/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.VineEst.VineEstS5C.AbsSb2

/-! # `SAbs` of the bundle kernel of a TRUE-choice (twisted) output (V5 Step 4d part C, `hAbs`, leaf `sb`)

The bundle kernel of a twisted state is the native S-part of the twisted garden at `(extEquiv x, tEquivS σ)`; the sums and integrals of the norms are
transported along the bijection of the decorations and the measure-preserving change of the times. -/

@[expose] public section
set_option autoImplicit false
open WaveTurbulence.VineParamContract
namespace WaveTurbulence.VineEstS5C
open WaveTurbulence WaveTurbulence.Twist WaveTurbulence.LFTwist WaveTurbulence.Links WaveTurbulence.VineEstS4 WaveTurbulence.VineEstS5B
  WaveTurbulence.RegRed WaveTurbulence.Reg.Skeleton TTree MeasureTheory

theorem tsum_integral_norm_transport {X Y α β : Type*} [MeasurableSpace α] [MeasurableSpace β] {μ : Measure α} {ν : Measure β}
    (e : X ≃ Y) (m : α ≃ᵐ β) (hm : MeasurePreserving m μ ν) (f : X → α → ℂ) (g : Y → β → ℂ)
    (hfg : ∀ x a, g (e x) (m a) = f x a) :
    (∀ y, Integrable (g y) ν) → (∀ x, Integrable (f x) μ) ∧
      (∀ x, ∫ a, ‖f x a‖ ∂μ = ∫ b, ‖g (e x) b‖ ∂ν) ∧
      ∑' x, ∫ a, ‖f x a‖ ∂μ = ∑' y, ∫ b, ‖g y b‖ ∂ν := by
  intro hg
  have h1 : ∀ x, ∫ a, ‖f x a‖ ∂μ = ∫ b, ‖g (e x) b‖ ∂ν := by
    intro x
    have := hm.integral_comp' (g := fun b => ‖g (e x) b‖)
    rw [← this]
    exact integral_congr_ae (Filter.Eventually.of_forall fun a => by simp only [hfg])
  refine ⟨fun x => ?_, h1, ?_⟩
  · have : f x = g (e x) ∘ m := funext fun a => (hfg x a).symm
    rw [this]
    exact (hm.integrable_comp_emb m.measurableEmbedding).mpr (hg (e x))
  · simp_rw [h1]
    exact e.tsum_eq (fun y => ∫ b, ‖g y b‖ ∂ν)

section Tw
variable {w d : ℕ} {G G' : Garden w} {S S' : Finset (GBranch G.tree)} {S'' : Finset (GBranch G'.tree)} {a b : GBranch G.tree}
  {a' b' : GBranch G'.tree}

theorem sAbs_transport (RS : CLRegionData G S a b) (RS' : CLRegionData G' S'' a' b') (L : ℝ) (base : Mom d)
    (E : ∀ e f : Mom d, ExtS RS L base e f ≃ ExtS RS' L base e f)
    (m : CLInternalTime RS ≃ᵐ CLInternalTime RS') (hm : MeasurePreserving m volume volume)
    (Ψ : (GNode G.tree → (Fin d → ℤ)) → (GBranch G.tree → ℝ) → ℂ)
    (Ψ' : (GNode G'.tree → (Fin d → ℤ)) → (GBranch G'.tree → ℝ) → ℂ) {C : ℝ}
    (hΨ : ∀ (t : Fin 3 → ℝ) (e f : Mom d) (x : ExtS RS L base e f) (σ : CLInternalTime RS),
      Ψ' (E e f x).1 (clLocalClock RS' t (m σ)) = Ψ x.1 (clLocalClock RS t σ))
    (h : SAbs RS' L base Ψ' C) : SAbs RS L base Ψ C := by
  intro t e f
  obtain ⟨h1, h2, h3⟩ := h t e f
  obtain ⟨hI, hN, hS⟩ := tsum_integral_norm_transport (E e f) m hm
    (fun (x : ExtS RS L base e f) (σ : CLInternalTime RS) => Ψ x.1 (clLocalClock RS t σ))
    (fun (y : ExtS RS' L base e f) (σ' : CLInternalTime RS') => Ψ' y.1 (clLocalClock RS' t σ'))
    (fun x σ => hΨ t e f x σ) h1
  refine ⟨hI, ?_, ?_⟩
  · have : (fun x : ExtS RS L base e f => ∫ σ : CLInternalTime RS, ‖Ψ x.1 (clLocalClock RS t σ)‖) =
        (fun y : ExtS RS' L base e f => ∫ σ' : CLInternalTime RS', ‖Ψ' y.1 (clLocalClock RS' t σ')‖) ∘ (E e f) :=
      funext fun x => hN x
    rw [this]
    exact ((E e f).summable_iff (f := fun y : ExtS RS' L base e f =>
      ∫ σ' : CLInternalTime RS', ‖Ψ' y.1 (clLocalClock RS' t σ')‖)).mpr h2
  · rw [hS]; exact h3

end Tw


section Ops
variable {w : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ℕ} {pstar : ι} {J : Set ι} {d : ℕ} {kind : Bool}
variable (κ : KPar d) (A : FamilyReconstruction w ι) (sp : SplitAt A.skeleton A.family pstar J)
  (hcan : CanonicalObject p kind A.layered)
  (hel : SourceLayerEligible A.layered A.data A.plain A.decodes (A.family.placement pstar) (A.family.kind pstar)
    (A.family.atoms pstar) (A.family.upper pstar))
  (htc : CohOn A.layered ((A.data.tree (A.family.placement pstar).lower).linksAt
    (nodeSign A.skeleton.sig (A.family.placement pstar).lower.1)
    (inflatedPosition A.skeleton A.data.tree (A.family.placement pstar).lower.toNode)))
  (hcc : CohOn A.layered ((A.data.couple (pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained)).linksAt
    (inflatedPosition A.skeleton A.data.tree
      ((pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained).firstLeaf A.plain).toNode)
    (inflatedPosition A.skeleton A.data.tree
      ((pairOfLeaf A.skeleton A.plain (A.family.placement pstar).retained).secondLeaf A.plain).toNode)))

theorem bundleKernel_true_eq (con : LFConstruction (A.source pstar hcan hel htc hcc) true)
    (x : ExtS sp.RS κ.L κ.base κ.e κ.f) (σ : CLInternalTime sp.RS) :
    spart con.data (unitTwistGarden_plain A.skeleton (A.family.placement pstar) A.plain) κ.L κ.γ κ.δ κ.F
        (stateLayer (opOut A pstar hcan hel htc hcc con)) (stateLayer_isLayering (opOut A pstar hcan hel htc hcc con)) κ.base
        (SplitAt.nextA A sp pstar true).sb.U (SplitAt.nextA A sp pstar true).sb.a (SplitAt.nextA A sp pstar true).sb.b
        ((stw_true A sp).extEquiv κ.L κ.base κ.e κ.f x).1
        (clLocalClock (SplitAt.nextA A sp pstar true).RS ![κ.t0, κ.t1, κ.t2]
          (tEquivS (A.family.placement pstar) sp.RS (SplitAt.nextA A sp pstar true).RS σ)) =
      bundleKernel κ A sp true (nuOf (opOut A pstar hcan hel htc hcc con) pstar)
        (rowQ κ (opOut A pstar hcan hel htc hcc con) pstar) (rowT κ (opOut A pstar hcan hel htc hcc con) pstar) x.1
        (clLocalClock sp.RS ![κ.t0, κ.t1, κ.t2] σ) := by
  have hS := SplitAt.slow sp
  have hT := stw_true A sp
  have h1 := bundleInt_eq_kernel κ A sp (fun _ _ _ => (1 : ℂ)) true
    (nuOf (opOut A pstar hcan hel htc hcc con) pstar) (rowQ κ (opOut A pstar hcan hel htc hcc con) pstar)
    (rowT κ (opOut A pstar hcan hel htc hcc con) pstar) x σ
  have h2 : sInt (SplitAt.nextA A sp pstar true).RS con.data (unitTwistGarden_plain A.skeleton (A.family.placement pstar) A.plain)
      κ.L κ.γ κ.δ κ.F (stateLayer (opOut A pstar hcan hel htc hcc con))
      (stateLayer_isLayering (opOut A pstar hcan hel htc hcc con)) κ.base κ.t0 κ.t1 κ.t2 κ.e κ.f
      (eB (A.family.placement pstar) sp.sb.b).toNode
      ((eB (A.family.placement pstar) sp.sb.b).child (SplitAt.nextA A sp pstar true).RS.kept) (fun _ _ _ => (1 : ℂ))
      ((stw_true A sp).extEquiv κ.L κ.base κ.e κ.f x)
      (tEquivS (A.family.placement pstar) sp.RS (SplitAt.nextA A sp pstar true).RS σ) =
      bundleInt κ A sp (fun t E Fr => (fun _ _ _ => (1 : ℂ)) t Fr E) true
        (nuOf (opOut A pstar hcan hel htc hcc con) pstar)
        (rowQ κ (opOut A pstar hcan hel htc hcc con) pstar) (rowT κ (opOut A pstar hcan hel htc hcc con) pstar) x σ := by
    rw [← twInt_true_eq κ A sp hcan hel htc hcc con (fun _ _ _ => (1 : ℂ)) x σ]
    exact sInt_tw hT A.plain A.data con.data κ.L κ.γ κ.δ κ.F (stateLayer A) (stateLayer_isLayering A)
      (stateLayer (opOut A pstar hcan hel htc hcc con)) (stateLayer_isLayering (opOut A pstar hcan hel htc hcc con))
      κ.base κ.t0 κ.t1 κ.t2 κ.e κ.f (fun _ _ _ => (1 : ℂ))
      (fun q _ hq => native_couple_eq con (stateLayer A) (stateLayer_isLayering A) (stateLayer_spec A)
        (stateLayer (opOut A pstar hcan hel htc hcc con)) (stateLayer_isLayering (opOut A pstar hcan hel htc hcc con))
        (stateLayer_spec (opOut A pstar hcan hel htc hcc con)) q hq)
      (fun v _ hv => native_tree_eq con (stateLayer A) (stateLayer_isLayering A) (stateLayer_spec A)
        (stateLayer (opOut A pstar hcan hel htc hcc con)) (stateLayer_isLayering (opOut A pstar hcan hel htc hcc con))
        (stateLayer_spec (opOut A pstar hcan hel htc hcc con)) v (hS.lower ▸ hv))
      (fun v _ => coreLayer_eq con (stateLayer A) (stateLayer_isLayering A) (stateLayer_spec A)
        (stateLayer (opOut A pstar hcan hel htc hcc con)) (stateLayer_isLayering (opOut A pstar hcan hel htc hcc con))
        (stateLayer_spec (opOut A pstar hcan hel htc hcc con)) v) x σ
  rw [h1] at h2
  unfold sInt at h2
  simp only [mul_one] at h2
  exact h2

/-- **`SAbs` of the bundle kernel of a TRUE-choice (twisted) output.** -/
theorem sAbs_bundle_true (con : LFConstruction (A.source pstar hcan hel htc hcc) true)
    (hL : κ.L ≠ 0) (hF : ∀ k : ℕ, Summable fun n : Fin d → ℤ => |κ.F k (κ.base + latticePoint κ.L n)|) :
    SAbs sp.RS κ.L κ.base (fun x u => bundleKernel κ A sp true (nuOf (opOut A pstar hcan hel htc hcc con) pstar)
        (rowQ κ (opOut A pstar hcan hel htc hcc con) pstar) (rowT κ (opOut A pstar hcan hel htc hcc con) pstar) x u)
      (baseConst con.data (unitTwistGarden_plain A.skeleton (A.family.placement pstar) A.plain) κ.L κ.γ κ.δ κ.F
        (stateLayer (opOut A pstar hcan hel htc hcc con)) (stateLayer_isLayering (opOut A pstar hcan hel htc hcc con))
        κ.base (SplitAt.nextA A sp pstar true).RS) := by
  have hHF := HF_of_all con.data (unitTwistGarden_plain A.skeleton (A.family.placement pstar) A.plain) κ.L κ.F
    (stateLayer (opOut A pstar hcan hel htc hcc con)) κ.base hF
  have key := sAbs_spart (hLayer := stateLayer_isLayering (opOut A pstar hcan hel htc hcc con)) (γ := κ.γ) (δ := κ.δ)
    (SplitAt.nextA A sp pstar true).sb.block (SplitAt.nextA A sp pstar true).RS hHF hL
  refine sAbs_transport sp.RS (SplitAt.nextA A sp pstar true).RS κ.L κ.base
    (fun e f => (stw_true A sp).extEquiv κ.L κ.base e f)
    (tEquivS (A.family.placement pstar) sp.RS (SplitAt.nextA A sp pstar true).RS)
    (tEquivS_measurePreserving (A.family.placement pstar) sp.RS (SplitAt.nextA A sp pstar true).RS) _ _ ?_ key
  intro t e f x σ
  obtain ⟨t0, t1, t2, rfl⟩ : ∃ t0 t1 t2 : ℝ, t = ![t0, t1, t2] := ⟨t 0, t 1, t 2, vec3_eta t⟩
  exact bundleKernel_true_eq (kparWithExt κ ![t0, t1, t2] e f) A sp hcan hel htc hcc con x σ

end Ops

end WaveTurbulence.VineEstS5C
