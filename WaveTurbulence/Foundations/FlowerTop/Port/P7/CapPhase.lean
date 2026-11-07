/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FlowerTop.Port.P7.CapBook
public import WaveTurbulence.Foundations.WaveB.FrozenB1
/-! FLOWER-P7: phases and time domains of the cap with both roots pinned at time `t`. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.FlowerP7
open TTree Finset MeasureTheory

variable {d : ℕ}

/-- Integrals over function spaces on equivalent finite index types agree. -/
theorem integral_equiv_pi {ι ι' : Type*} [Fintype ι] [Fintype ι'] (e : ι ≃ ι') (Φ : (ι' → ℝ) → ℂ) :
    ∫ τ : ι' → ℝ, Φ τ = ∫ σ : ι → ℝ, Φ (fun i' => σ (e.symm i')) := by
  have hmp := measurePreserving_piCongrLeft (fun _ : ι' => (volume : Measure ℝ)) e
  have := hmp.integral_comp' (f := MeasurableEquiv.piCongrLeft (fun _ : ι' => ℝ) e) Φ
  have hfun : ∀ σ : ι → ℝ, MeasurableEquiv.piCongrLeft (fun _ : ι' => ℝ) e σ = fun i' => σ (e.symm i') := by
    intro σ
    funext b'
    obtain ⟨a, rfl⟩ := e.surjective b'
    simp [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
  simp only [hfun] at this
  exact this.symm

/-- The coset labels of the cap are the coset labels of the six trees at lifted nodes. -/
theorem coset_cap_lift (G : Garden (2 * 3)) (hsig : ∀ c, G.sig c = childSig c) (L : ℝ) (k : Mom d)
    (κ' : GNode G.tree → (Fin d → ℤ)) (a : GNode G.tree) :
    cosetDecoration (capGarden G hsig) L k (upperDec (T := G.tree) κ') (liftNode a) =
      cosetDecoration G L k κ' a := by
  simp [cosetDecoration, upperDec_lift]

theorem coset_cap_root (G : Garden (2 * 3)) (hsig : ∀ c, G.sig c = childSig c) (L : ℝ) (k : Mom d)
    (κ' : GNode G.tree → (Fin d → ℤ)) (j : Fin 2) :
    cosetDecoration (capGarden G hsig) L k (upperDec (T := G.tree) κ') (rootBranch G.tree j).toNode =
      k + latticePoint L 0 := by
  simp [cosetDecoration, upperDec_root]

theorem omega_cap_lift (G : Garden (2 * 3)) (hsig : ∀ c, G.sig c = childSig c) (L : ℝ) (k : Mom d)
    (κ' : GNode G.tree → (Fin d → ℤ)) (a : GBranch G.tree) :
    omegaNode (capGarden G hsig) (cosetDecoration (capGarden G hsig) L k (upperDec (T := G.tree) κ'))
      (liftBranch a) = omegaNode G (cosetDecoration G L k κ') a := by
  unfold omegaNode
  show resFactor (cosetDecoration (capGarden G hsig) L k (upperDec κ') ((liftBranch a).child 0)) _ _ _ = _
  rw [liftBranch_child, liftBranch_child, liftBranch_child, liftBranch_toNode, coset_cap_lift, coset_cap_lift,
    coset_cap_lift, coset_cap_lift]

/-- The resonance factor at the root `j`, as a function of the three outer labels. -/
noncomputable def rootOmega (L : ℝ) (k : Mom d) (a b c : Fin d → ℤ) : ℝ :=
  resFactor (k + latticePoint L a) (k + latticePoint L b) (k + latticePoint L c) (k + latticePoint L 0)

theorem omega_cap_root (G : Garden (2 * 3)) (hsig : ∀ c, G.sig c = childSig c) (L : ℝ) (k : Mom d)
    (κ' : GNode G.tree → (Fin d → ℤ)) (j : Fin 2) :
    omegaNode (capGarden G hsig) (cosetDecoration (capGarden G hsig) L k (upperDec (T := G.tree) κ'))
      (rootBranch G.tree j) =
      rootOmega L k (κ' (GNode.root G.tree (idx j 0))) (κ' (GNode.root G.tree (idx j 1)))
        (κ' (GNode.root G.tree (idx j 2))) := by
  unfold omegaNode rootOmega
  show resFactor (cosetDecoration (capGarden G hsig) L k (upperDec κ') ((rootBranch G.tree j).child 0)) _ _ _ = _
  rw [rootBranch_child, rootBranch_child, rootBranch_child, coset_cap_lift, coset_cap_lift, coset_cap_lift,
    coset_cap_root]
  rfl

/-- The pinned phase of the two roots at time `t`. -/
noncomputable def rootPhase (L γ δ : ℝ) (k : Mom d) (t : ℝ) (n : Fin (2 * 3) → (Fin d → ℤ)) : ℂ :=
  ∏ j : Fin 2, Complex.exp ((Real.pi * (((![1, -1] : Fin 2 → ℤˣ) j : ℤˣ) : ℤ) * δ * L ^ (2 * γ) *
    rootOmega L k (n (idx j 0)) (n (idx j 1)) (n (idx j 2)) * t : ℝ) * Complex.I)

/-- The times of the cap: both roots at `t`, the other branching nodes from `σ`. -/
noncomputable def extendCap (T : Fin (2 * 3) → TTree) (t : ℝ) (σ : GBranch T → ℝ) : GBranch (capTree T) → ℝ :=
  fun b => ((capBranchEquiv T).symm b).elim (fun _ => t) σ

theorem extendCap_root (T : Fin (2 * 3) → TTree) (t : ℝ) (σ : GBranch T → ℝ) (j : Fin 2) :
    extendCap T t σ (rootBranch T j) = t := by
  unfold extendCap
  have : (capBranchEquiv T).symm (rootBranch T j) = Sum.inl j := by
    rw [Equiv.symm_apply_eq]; rfl
  rw [this]; rfl

theorem extendCap_lift (T : Fin (2 * 3) → TTree) (t : ℝ) (σ : GBranch T → ℝ) (a : GBranch T) :
    extendCap T t σ (liftBranch a) = σ a := by
  unfold extendCap
  have : (capBranchEquiv T).symm (liftBranch a) = Sum.inr a := by
    rw [Equiv.symm_apply_eq]; rfl
  rw [this]; rfl

/-- The phase product of the cap factors into the root phase and the phase product of the six trees. -/
theorem phaseProd_cap (L γ δ : ℝ) (G : Garden (2 * 3)) (hsig : ∀ c, G.sig c = childSig c) (k : Mom d)
    (t : ℝ) (κ' : GNode G.tree → (Fin d → ℤ)) (σ : GBranch G.tree → ℝ) :
    phaseProdOff L γ δ (capGarden G hsig) ∅
        (cosetDecoration (capGarden G hsig) L k (upperDec (T := G.tree) κ')) (extendCap G.tree t σ) =
      rootPhase L γ δ k t (fun c => κ' (GNode.root G.tree c)) *
        phaseProdOff L γ δ G ∅ (cosetDecoration G L k κ') σ := by
  unfold phaseProdOff
  simp only [Finset.notMem_empty, if_false]
  rw [prod_cap_branch]
  congr 1
  · refine Finset.prod_congr rfl fun j _ => ?_
    rw [extendCap_root, sign_cap_root, omega_cap_root]
  · refine Finset.prod_congr rfl fun a _ => ?_
    rw [extendCap_lift, liftBranch_toNode, sign_cap_lift, omega_cap_lift]

end WaveTurbulence.FlowerP7
