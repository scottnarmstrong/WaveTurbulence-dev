/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.BTilde.TreeFlat
public import WaveTurbulence.Foundations.RegularAsymptotics.BTilde.TreeIntL
public import WaveTurbulence.Foundations.WaveB.FrozenB1

/-!
# The time coefficient `B_Q` of a couple garden

DH21 (defcoefb2), DH23 (defcoefb2) (L951–L954):
`B_Q(t, s, α[𝒩]) = ∫_ℰ ∏_{𝔫 ∈ 𝒩} e^{ζ_𝔫 πi α_𝔫 t_𝔫} dt`, with ℰ (DH23 (defdomaine), L474):
`0 < t_{𝔫'} < t_𝔫` for a child `𝔫'` of `𝔫`, `t_𝔫 < t` on `𝒩⁺` and `t_𝔫 < s` on `𝒩⁻` (`cplB`, `cplDom`).

* `cplB_eq`: `B_Q(t, s) = A_{𝒯⁺}(t) A_{𝒯⁻}(s)`, the product of the tree integrals.
* `kDomain_eq_cplDom`, `phaseIntegral_eq_cplB`: for a couple with all layers `0` and `t, s ∈ [0, 1]`,
  Wave B's `kDomain` is ℰ and `phaseIntegral` is `B_Q` at `α = δL^{2γ}Ω` (the form in which
  `kernelK`, hence `KQstar`, contains it).
-/

@[expose] public section

namespace WaveTurbulence.MainCoef

open TTree MeasureTheory Complex Set
open scoped Real

section Couple

variable (G : Garden 2)

/-- The branching nodes of a couple, tree by tree. -/
def gbEquiv : GBranch G.tree ≃ TB (G.tree 0) ⊕ TB (G.tree 1) where
  toFun b := if h : b.1.1 = 0 then .inl ⟨b.1.2, h ▸ b.2⟩ else
    .inr ⟨b.1.2, by
      have h1 : b.1.1 = 1 := by omega
      exact h1 ▸ b.2⟩
  invFun x := match x with
    | .inl p => ⟨(0, p.1), p.2⟩
    | .inr p => ⟨(1, p.1), p.2⟩
  left_inv b := by
    rcases b with ⟨⟨j, p⟩, hp⟩
    fin_cases j <;> rfl
  right_inv x := by
    rcases x with p | p <;> rfl

theorem gbEquiv_zero {p : TTree.Path} (h : p ∈ (G.tree 0).branching) :
    gbEquiv G ⟨(0, p), h⟩ = .inl ⟨p, h⟩ := by
  simp [gbEquiv]

theorem gbEquiv_one {p : TTree.Path} (h : p ∈ (G.tree 1).branching) :
    gbEquiv G ⟨(1, p), h⟩ = .inr ⟨p, h⟩ := by
  simp [gbEquiv]

/-- **The time domain ℰ of a couple** (DH23 (defdomaine), L474): `0 < t_𝔫`, `t_{𝔫'} < t_𝔫` for a
branching child `𝔫'`, `t_𝔫 < t` on `𝒯⁺` and `t_𝔫 < s` on `𝒯⁻`. -/
def cplDom (t s : ℝ) : Set (GBranch G.tree → ℝ) :=
  {τ | ∀ b, 0 < τ b ∧ τ b < (if b.1.1 = 0 then t else s) ∧
    ∀ b' : GBranch G.tree, b'.IsChildOf b → τ b' < τ b}

/-- The phase `∏_𝔫 e^{πiζ_𝔫α_𝔫t_𝔫}`, with `ζ_𝔫 = nodeSign G.sig 𝔫`. -/
noncomputable def cplPhase (α : Fin 2 × TTree.Path → ℝ) (τ : GBranch G.tree → ℝ) : ℂ :=
  ∏ b : GBranch G.tree, cexp (π * I * (((nodeSign G.sig b.1 : ℤˣ) : ℤ) * α b.1 * τ b))

/-- **The time coefficient of a couple** (DH21/DH23 (defcoefb2)). -/
noncomputable def cplB (t s : ℝ) (α : Fin 2 × TTree.Path → ℝ) : ℂ :=
  ∫ τ : GBranch G.tree → ℝ, (cplDom G t s).indicator (cplPhase G α) τ

/-- The phases of tree `j`. -/
def treeBeta (α : Fin 2 × TTree.Path → ℝ) (j : Fin 2) (p : TTree.Path) : ℝ :=
  ((nodeSign G.sig (j, p) : ℤˣ) : ℤ) * α (j, p)

theorem cplDom_reindex (t s : ℝ) (σ : TB (G.tree 0) ⊕ TB (G.tree 1) → ℝ) :
    (fun b => σ (gbEquiv G b)) ∈ cplDom G t s ↔
      (fun p => σ (.inl p)) ∈ treeDomF (G.tree 0) t ∧ (fun p => σ (.inr p)) ∈ treeDomF (G.tree 1) s := by
  constructor
  · intro h
    refine ⟨fun p => ?_, fun p => ?_⟩
    · have := h ⟨(0, p.1), p.2⟩
      simp only [gbEquiv_zero] at this
      refine ⟨this.1, by simpa using this.2.1, fun q ⟨i, hi⟩ => ?_⟩
      have h2 := this.2.2 ⟨(0, q.1), q.2⟩ ⟨rfl, i, hi⟩
      simpa [gbEquiv_zero] using h2
    · have := h ⟨(1, p.1), p.2⟩
      simp only [gbEquiv_one] at this
      refine ⟨this.1, by simpa using this.2.1, fun q ⟨i, hi⟩ => ?_⟩
      have h2 := this.2.2 ⟨(1, q.1), q.2⟩ ⟨rfl, i, hi⟩
      simpa [gbEquiv_one] using h2
  · rintro ⟨h0, h1⟩ ⟨⟨j, p⟩, hp⟩
    fin_cases j
    · have := h0 ⟨p, hp⟩
      simp only [Fin.zero_eta, gbEquiv_zero]
      refine ⟨this.1, by simpa using this.2.1, fun ⟨⟨j', q⟩, hq⟩ ⟨hj, i, hi⟩ => ?_⟩
      simp only at hj hi
      subst hj
      simpa [gbEquiv_zero] using this.2.2 ⟨q, hq⟩ ⟨i, hi⟩
    · have := h1 ⟨p, hp⟩
      simp only [Fin.mk_one, gbEquiv_one]
      refine ⟨this.1, by simpa using this.2.1, fun ⟨⟨j', q⟩, hq⟩ ⟨hj, i, hi⟩ => ?_⟩
      simp only at hj hi
      subst hj
      simpa [gbEquiv_one] using this.2.2 ⟨q, hq⟩ ⟨i, hi⟩

theorem cplPhase_reindex (α : Fin 2 × TTree.Path → ℝ) (σ : TB (G.tree 0) ⊕ TB (G.tree 1) → ℝ) :
    cplPhase G α (fun b => σ (gbEquiv G b)) =
      treePhase (G.tree 0) (treeBeta G α 0) (fun p => σ (.inl p)) *
        treePhase (G.tree 1) (treeBeta G α 1) (fun p => σ (.inr p)) := by
  unfold cplPhase treePhase treeBeta
  rw [← (gbEquiv G).symm.prod_comp, Fintype.prod_sum_type]
  simp only [Equiv.apply_symm_apply]
  push_cast
  rfl

/-- **`B_Q(t, s) = A_{𝒯⁺}(t) A_{𝒯⁻}(s)`**: Fubini over the two trees. -/
theorem cplB_eq {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) (α : Fin 2 × TTree.Path → ℝ) :
    cplB G t s α = treeInt (G.tree 0) (treeBeta G α 0) t * treeInt (G.tree 1) (treeBeta G α 1) s := by
  unfold cplB
  rw [← integral_reindex_pi (gbEquiv G)]
  have e : ∀ σ : TB (G.tree 0) ⊕ TB (G.tree 1) → ℝ,
      (cplDom G t s).indicator (cplPhase G α) (fun b => σ (gbEquiv G b)) =
        (treeDomF (G.tree 0) t).indicator (treePhase (G.tree 0) (treeBeta G α 0)) (fun p => σ (.inl p)) *
        (treeDomF (G.tree 1) s).indicator (treePhase (G.tree 1) (treeBeta G α 1))
          (fun p => σ (.inr p)) := by
    intro σ
    by_cases h0 : (fun p => σ (.inl p)) ∈ treeDomF (G.tree 0) t
    · by_cases h1 : (fun p => σ (.inr p)) ∈ treeDomF (G.tree 1) s
      · rw [Set.indicator_of_mem ((cplDom_reindex G t s σ).2 ⟨h0, h1⟩), Set.indicator_of_mem h0,
          Set.indicator_of_mem h1, cplPhase_reindex]
      · rw [Set.indicator_of_notMem (fun h => h1 ((cplDom_reindex G t s σ).1 h).2),
          Set.indicator_of_notMem h1, mul_zero]
    · rw [Set.indicator_of_notMem (fun h => h0 ((cplDom_reindex G t s σ).1 h).1),
        Set.indicator_of_notMem h0, zero_mul]
  simp_rw [e]
  rw [integral_sum_pi_mul (fun x => (treeDomF (G.tree 0) t).indicator
      (treePhase (G.tree 0) (treeBeta G α 0)) x)
    (fun y => (treeDomF (G.tree 1) s).indicator (treePhase (G.tree 1) (treeBeta G α 1)) y),
    treeDomF_eq, treeDomF_eq, integral_treeDomR _ _ _ ht, integral_treeDomR _ _ _ hs]

end Couple

section Kernel

/-- `α_𝔫 = δL^{2γ}Ω_𝔫` on the branching nodes (`0` elsewhere): the frequencies of `phaseProd`. -/
noncomputable def alphaOmega {d : ℕ} (L γ δ : ℝ) (G : Garden 2) (k : GNode G.tree → Mom d)
    (a : Fin 2 × TTree.Path) : ℝ :=
  if h : a.2 ∈ (G.tree a.1).branching then δ * L ^ (2 * γ) * omegaNode G k ⟨a, h⟩ else 0

theorem not_isLoneParent_of_plain {G : Garden 2} (hG : G.IsPlain) (b : GBranch G.tree) :
    ¬ G.IsLoneParent b := by
  rintro ⟨ℓ, hℓ, -⟩
  have := (hG ℓ).symm.trans hℓ
  cases this

theorem not_isFlowerParent_of_plain {G : Garden 2} (hG : G.IsPlain) (b : GBranch G.tree) :
    ¬ G.IsFlowerParent b := by
  rintro ⟨ℓ, hℓ, -⟩
  have := (hG ℓ).symm.trans hℓ
  cases this

/-- **Wave B's time domain is ℰ** for a couple in layer `0` with `t, s ≤ 1`. -/
theorem kDomain_eq_cplDom (LG : LayeredGarden 2) (h0 : ∀ a, LG.layer a = 0)
    (hplain : LG.garden.IsPlain) {t s : ℝ} (ht1 : t ≤ 1) (hs1 : s ≤ 1) (s' : ℝ) :
    kDomain LG (fun b => if b.1.1 = 0 then t else s) s' = cplDom LG.garden t s := by
  ext τ
  simp only [kDomain, cplDom, Set.mem_ofPred_eq, h0, Nat.cast_zero, zero_add]
  constructor
  · intro h b
    exact ⟨(h b).2.2.1, (h b).2.2.2.1, (h b).2.2.2.2.1⟩
  · intro h b
    have hb := h b
    have hup : τ b < 1 := hb.2.1.trans_le (by split_ifs <;> assumption)
    exact ⟨hb.1, hup, hb.1, hb.2.1, hb.2.2, fun hl => absurd hl (not_isLoneParent_of_plain hplain b)⟩

/-- **Wave B's phase integral is `B_Q`** at `α = δL^{2γ}Ω` (DH23 L951: `B_Q(t, s, δL^{2γ}Ω[𝒩])`). -/
theorem phaseIntegral_eq {d : ℕ} (L γ δ : ℝ) {G : Garden 2} (hG : G.IsPlain)
    (D : Set (GBranch G.tree → ℝ)) (s' : ℝ) (k : GNode G.tree → Mom d) :
    phaseIntegral L γ δ G D s' k =
      ∫ τ : GBranch G.tree → ℝ, D.indicator (cplPhase G (alphaOmega L γ δ G k)) τ := by
  have hfp := not_isFlowerParent_of_plain hG
  have hph : phaseProd L γ δ G k = cplPhase G (alphaOmega L γ δ G k) := by
    funext τ
    unfold phaseProd cplPhase alphaOmega
    refine Finset.prod_congr rfl fun b _ => ?_
    rw [dite_eq_left b.2, show (⟨b.1, b.2⟩ : GBranch G.tree) = b from rfl]
    congr 1
    push_cast
    simp only [Garden.sign, GBranch.toNode]
    ring
  unfold phaseIntegral
  rw [hph]
  have e : ∀ τ : G.FreeBranch → ℝ, G.extendTime s' τ = fun b => τ ((Equiv.subtypeUnivEquiv hfp).symm b) := by
    intro τ
    funext b
    simp only [Garden.extendTime, hfp b, dite_false]
    rfl
  simp_rw [e]
  exact integral_reindex_pi (Equiv.subtypeUnivEquiv hfp).symm
    (fun τ => D.indicator (cplPhase G (alphaOmega L γ δ G k)) τ)

/-- `phaseIntegral` over ℰ is `B_Q(t, s, δL^{2γ}Ω)`. -/
theorem phaseIntegral_cplDom_eq {d : ℕ} (L γ δ : ℝ) {G : Garden 2} (hG : G.IsPlain) (t s s' : ℝ)
    (k : GNode G.tree → Mom d) :
    phaseIntegral L γ δ G (cplDom G t s) s' k = cplB G t s (alphaOmega L γ δ G k) :=
  phaseIntegral_eq L γ δ hG _ s' k

end Kernel

end WaveTurbulence.MainCoef
