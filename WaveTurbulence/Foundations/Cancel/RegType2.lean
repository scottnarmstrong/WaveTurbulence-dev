/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.Cancel.RegChainT

/-!
# The type 2 closure (DH21 (newexp2), (recurtype2))

A type 2 coefficient is `type2 α t s = chainT⁺ t (t' ↦ chainT⁻ s (s' ↦ F_lp(α, t', s')))`. The two chains
carry pair coefficients `F^±_j` (DH21 (newexp2)) and the lone pair carries `F_lp`. If all of these have
regularized limits, so does the type 2 coefficient (`regCoef_type2`). Its limit is
`chainL⁺ t (t' ↦ chainL⁻ s (s' ↦ J_lp(t', s')))`. An adjacent pair `j` contributes
`sg(σ j ∈ Z) J_j(τ, τ)`: the factor is `-1` for `σ j ∈ Z` (F61). A non-adjacent pair contributes `0`.
-/

public section

open MeasureTheory Set Filter Complex intervalIntegral Function
open scoped Real Topology

namespace WaveTurbulence.Cancel

open WaveTurbulence.ClassJR

theorem chainL_congr {D D' : ℕ → ℝ → ℂ} :
    ∀ (c : LegalCode) (q : ℕ),
      (∀ j, q ≤ j → j < q + c.size → ∀ τ ∈ Icc (0 : ℝ) 1, D j τ = D' j τ) →
      ∀ {g g' : ℝ → ℂ}, (∀ x ∈ Icc (0 : ℝ) 1, g x = g' x) → ∀ t ∈ Icc (0 : ℝ) 1,
        chainL D c q t g = chainL D' c q t g'
  | .nil, _, _, _, _, hg, t, ht => hg t ht
  | .node .nil r, q, hD, g, g', hg, t, ht => by
    have hsz : (LegalCode.node .nil r).size = r.size + 1 := by simp [LegalCode.size]
    simp only [chainL]
    refine intervalIntegral.integral_congr fun τ hτ => ?_
    rw [uIcc_of_le ht.1] at hτ
    have hτ' : τ ∈ Icc (0 : ℝ) 1 := ⟨hτ.1, hτ.2.trans ht.2⟩
    rw [hD q le_rfl (by omega) τ hτ',
      chainL_congr r (q + 1) (fun j h1 h2 => hD j (by omega) (by omega)) hg τ hτ']
  | .node (.node _ _) _, _, _, _, _, _, _, _ => rfl

theorem RegLim2.congr_lim {R : ℝ → ℝ → ℝ → ℂ} {J J' : ℝ → ℝ → ℂ} (h : RegLim2 R J)
    (he : ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, J t s = J' t s) : RegLim2 R J' :=
  ⟨h.bound, h.lip, fun t ht s hs => he t ht s hs ▸ h.lim t ht s hs⟩

theorem KFam.single {R : ℝ → ℝ → ℝ → ℂ} {J : ℝ → ℝ → ℂ} (h : RegLim2 R J) :
    KFam (fun _ θ t s => R θ (clamp01 t) (clamp01 s)) (fun _ => J) := by
  have h' := KFam.ofFinset {0} (R := fun _ => R) (R₀ := fun _ => J) fun _ _ => h
  obtain ⟨M, hM⟩ := h'.bound
  obtain ⟨L, hL⟩ := h'.lip
  refine ⟨⟨M, hM.mono fun θ hθ j t s => by simpa using hθ 0 t s⟩,
    ⟨L, hL.mono fun θ hθ j t s t' s' => by simpa using hθ 0 t s t' s'⟩,
    fun j t ht s hs => by simpa using h'.lim 0 t ht s hs⟩

variable {V : Type} [DecidableEq V]

/-- The regularized pair kernels of a chain. -/
@[expose] noncomputable def regPK (θ : ℝ) (ζ : V → ℤ) (Z : Finset V) (σ : ℕ → V)
    (SF : ℕ → Finset V) (F : ℕ → (V → ℝ) → ℝ → ℝ → ℂ) (j : ℕ) (ta tb : ℝ) : ℂ :=
  (kk (decide (σ j ∈ Z)) θ (ta - tb) : ℂ) * RI θ ζ Z (SF j) (F j) ta tb

/-- **The type 2 recursion under regularization** (Fubini). -/
theorem RI_type2 {θ : ℝ} (hθ : 0 < θ) (ζ : V → ℤ) (hζ : ∀ v, ζ v = 1 ∨ ζ v = -1) (Z : Finset V)
    {σp σm : ℕ → V} {εp εm : ℕ → ℤ} (hεp : ∀ j, εp j = ζ (σp j)) (hεm : ∀ j, εm j = ζ (σm j))
    {Fp Fm : ℕ → (V → ℝ) → ℝ → ℝ → ℂ} {SFp SFm : ℕ → Finset V}
    (hFp : ∀ j, NiceCoef (SFp j) (Fp j)) (hFm : ∀ j, NiceCoef (SFm j) (Fm j)) {BF : ℝ} (hBF0 : 0 ≤ BF)
    (hBFp : ∀ j α, ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, ‖Fp j α t s‖ ≤ BF)
    (hBFm : ∀ j α, ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, ‖Fm j α t s‖ ≤ BF)
    {Flp : (V → ℝ) → ℝ → ℝ → ℂ} {Slp : Finset V} (hlp : NiceCoef Slp Flp)
    (cp cm : LegalCode) (hdp : ChainDisjF σp SFp cp 0) (hdm : ChainDisjF σm SFm cm 0)
    (hpm : Disjoint (chainVarsF σp SFp cp 0) (chainVarsF σm SFm cm 0 ∪ Slp))
    (hml : Disjoint (chainVarsF σm SFm cm 0) Slp) {t s : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hs : s ∈ Icc (0 : ℝ) 1) :
    RI θ ζ Z (chainVarsF σp SFp cp 0 ∪ (chainVarsF σm SFm cm 0 ∪ Slp))
        (fun α t s => chainT σp εp cp 0 Fp α t (fun t' => chainT σm εm cm 0 Fm α s
          (fun s' => Flp α t' s'))) t s =
      chainK (regPK θ ζ Z σp SFp Fp) cp 0 t (fun t' => chainK (regPK θ ζ Z σm SFm Fm) cm 0 s
        (fun s' => RI θ ζ Z Slp Flp t' s')) := by
  obtain ⟨Bl, hBl⟩ := hlp.bdd
  have hBl0 : 0 ≤ max Bl 0 := le_max_right _ _
  have hPcm := fun j => continuous_phaseK (σ := σm) (ε := εm) (fun j => (hFm j).cont) j
  have hmm := mass_phaseK (σ := σm) (ε := εm) hBF0 hBFm
  -- the inner chain, as a function of `(α, t')`
  set g : (V → ℝ) → ℝ → ℂ := fun α t' => chainK (phaseK σm εm Fm α) cm 0 s (fun s' => Flp α t' s')
    with hg
  have hgc : Continuous (Function.uncurry g) := by
    have h := continuous_chainK_param (X := (V → ℝ) × ℝ) (P := fun x => phaseK σm εm Fm x.1)
      (fun j => (hPcm j).comp (f := fun p : ((V → ℝ) × ℝ) × ℝ × ℝ => (p.1.1, p.2)) (by fun_prop))
      cm 0 (g := fun x s' => Flp x.1 x.2 s')
      (hlp.cont.comp (f := fun p : ((V → ℝ) × ℝ) × ℝ => (p.1.1, p.1.2, p.2)) (by fun_prop))
    exact h.comp (f := fun p : (V → ℝ) × ℝ => (p, s)) (by fun_prop)
  have hgb : ∀ α, ∀ x ∈ Icc (0 : ℝ) 1, ‖g α x‖ ≤ BF ^ cm.size * max Bl 0 := fun α x hx =>
    norm_chainK_le hBF0 (hmm α) cm 0 hBl0 (fun y hy => (hBl α x hx y hy).trans (le_max_left _ _)) s hs
  have hgd : ∀ x, DependsOn (fun α => g α x) ↑(chainVarsF σm SFm cm 0 ∪ Slp) := by
    intro x α α' h
    exact chainK_phaseK_congr (fun j => (hFm j).dep) cm 0
      (fun w hw => h w (Finset.mem_coe.2 (Finset.mem_union_left _ hw)))
      (fun y => hlp.dep x y fun w hw => h w (Finset.mem_coe.2 (Finset.mem_union_right _
        (Finset.mem_coe.1 hw)))) s
  have e : (fun α (t s : ℝ) => chainT σp εp cp 0 Fp α t (fun t' => chainT σm εm cm 0 Fm α s
      (fun s' => Flp α t' s'))) = fun α t s => chainK (phaseK σp εp Fp α) cp 0 t
        (fun t' => chainK (phaseK σm εm Fm α) cm 0 s (fun s' => Flp α t' s')) := by
    funext α t s
    rw [chainT_eq_chainK]
    congr 1
    funext t'
    rw [chainT_eq_chainK]
  rw [e]
  unfold RI
  rw [mint_chain hθ ζ hζ Z hεp hFp hBF0 hBFp cp 0 hdp hpm (g := g) hgd hgc (by positivity) hgb t ht]
  refine chainK_congr cp 0 (fun _ _ _ _ _ _ _ => rfl) (fun x hx => ?_) t ht
  simp only [hg]
  exact mint_chain hθ ζ hζ Z hεm hFm hBF0 hBFm cm 0 hdm hml (g := fun α s' => Flp α x s')
    (fun y => hlp.dep x y) (hlp.cont.comp (f := fun p : (V → ℝ) × ℝ => (p.1, x, p.2)) (by fun_prop))
    hBl0 (fun α y hy => (hBl α x hx y hy).trans (le_max_left _ _)) s hs

/-- **The type 2 step** (DH21 (newexp2), (recurtype2)). -/
theorem regCoef_type2 {ζ : V → ℤ} (hζ : ∀ v, ζ v = 1 ∨ ζ v = -1) {Z : Finset V}
    {σp σm : ℕ → V} {εp εm : ℕ → ℤ} (hεp : ∀ j, εp j = ζ (σp j)) (hεm : ∀ j, εm j = ζ (σm j))
    {Fp Fm : ℕ → (V → ℝ) → ℝ → ℝ → ℂ} {SFp SFm : ℕ → Finset V}
    (hFp : ∀ j, NiceCoef (SFp j) (Fp j)) (hFm : ∀ j, NiceCoef (SFm j) (Fm j)) {BF : ℝ} (hBF0 : 0 ≤ BF)
    (hBFp : ∀ j α, ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, ‖Fp j α t s‖ ≤ BF)
    (hBFm : ∀ j α, ∀ t ∈ Icc (0 : ℝ) 1, ∀ s ∈ Icc (0 : ℝ) 1, ‖Fm j α t s‖ ≤ BF)
    {Jp Jm : ℕ → ℝ → ℝ → ℂ} (cp cm : LegalCode)
    (hRp : ∀ j < cp.size, RegLim2 (fun θ t s => RI θ ζ Z (SFp j) (Fp j) t s) (Jp j))
    (hRm : ∀ j < cm.size, RegLim2 (fun θ t s => RI θ ζ Z (SFm j) (Fm j) t s) (Jm j))
    {Flp : (V → ℝ) → ℝ → ℝ → ℂ} {Slp : Finset V} {Jlp : ℝ → ℝ → ℂ} (hlp : RegCoef ζ Z Slp Flp Jlp)
    (hdp : ChainDisjF σp SFp cp 0) (hdm : ChainDisjF σm SFm cm 0)
    (hpm : Disjoint (chainVarsF σp SFp cp 0) (chainVarsF σm SFm cm 0 ∪ Slp))
    (hml : Disjoint (chainVarsF σm SFm cm 0) Slp) :
    RegCoef ζ Z (chainVarsF σp SFp cp 0 ∪ (chainVarsF σm SFm cm 0 ∪ Slp))
      (fun α t s => chainT σp εp cp 0 Fp α t (fun t' => chainT σm εm cm 0 Fm α s
        (fun s' => Flp α t' s')))
      (fun t s => chainL (kD (fun j => decide (σp j ∈ Z)) (fun j τ _ => Jp j τ τ)) cp 0 t
        (fun t' => chainL (kD (fun j => decide (σm j ∈ Z)) (fun j τ _ => Jm j τ τ)) cm 0 s
          (fun s' => Jlp t' s'))) := by
  obtain ⟨Bl, hBl⟩ := hlp.nice.bdd
  have hBl0 : 0 ≤ max Bl 0 := le_max_right _ _
  have hPcp := fun j => continuous_phaseK (σ := σp) (ε := εp) (fun j => (hFp j).cont) j
  have hPcm := fun j => continuous_phaseK (σ := σm) (ε := εm) (fun j => (hFm j).cont) j
  have hmp := mass_phaseK (σ := σp) (ε := εp) hBF0 hBFp
  have hmm := mass_phaseK (σ := σm) (ε := εm) hBF0 hBFm
  have e : (fun α (t s : ℝ) => chainT σp εp cp 0 Fp α t (fun t' => chainT σm εm cm 0 Fm α s
      (fun s' => Flp α t' s'))) = fun α t s => chainK (phaseK σp εp Fp α) cp 0 t
        (fun t' => chainK (phaseK σm εm Fm α) cm 0 s (fun s' => Flp α t' s')) := by
    funext α t s
    rw [chainT_eq_chainK]
    congr 1
    funext t'
    rw [chainT_eq_chainK]
  have e' : ∀ α t s, chainT σp εp cp 0 Fp α t (fun t' => chainT σm εm cm 0 Fm α s
      (fun s' => Flp α t' s')) = chainK (phaseK σp εp Fp α) cp 0 t
        (fun t' => chainK (phaseK σm εm Fm α) cm 0 s (fun s' => Flp α t' s')) :=
    fun α t s => congrFun (congrFun (congrFun e α) t) s
  -- the inner chain as a function of `((α, t'), s)`
  have hinc : Continuous fun p : ((V → ℝ) × ℝ) × ℝ =>
      chainK (phaseK σm εm Fm p.1.1) cm 0 p.2 (fun s' => Flp p.1.1 p.1.2 s') :=
    continuous_chainK_param (X := (V → ℝ) × ℝ) (P := fun x => phaseK σm εm Fm x.1)
      (fun j => (hPcm j).comp (f := fun p : ((V → ℝ) × ℝ) × ℝ × ℝ => (p.1.1, p.2)) (by fun_prop))
      cm 0 (g := fun x s' => Flp x.1 x.2 s')
      (hlp.nice.cont.comp (f := fun p : ((V → ℝ) × ℝ) × ℝ => (p.1.1, p.1.2, p.2)) (by fun_prop))
  refine ⟨⟨fun t s => ?_, ?_, ⟨BF ^ cp.size * (BF ^ cm.size * max Bl 0), fun α t ht s hs => ?_⟩⟩, ?_⟩
  · -- dependence
    simp only [e']
    intro α α' h
    exact chainK_phaseK_congr (fun j => (hFp j).dep) cp 0
      (fun w hw => h w (Finset.mem_coe.2 (Finset.mem_union_left _ hw)))
      (fun t' => chainK_phaseK_congr (fun j => (hFm j).dep) cm 0
        (fun w hw => h w (Finset.mem_coe.2 (Finset.mem_union_right _ (Finset.mem_union_left _ hw))))
        (fun s' => hlp.nice.dep t' s' fun w hw => h w (Finset.mem_coe.2 (Finset.mem_union_right _
          (Finset.mem_union_right _ (Finset.mem_coe.1 hw))))) s) t
  · -- continuity
    simp only [e']
    have h := continuous_chainK_param (X := (V → ℝ) × ℝ) (P := fun x => phaseK σp εp Fp x.1)
      (fun j => (hPcp j).comp (f := fun p : ((V → ℝ) × ℝ) × ℝ × ℝ => (p.1.1, p.2)) (by fun_prop))
      cp 0 (g := fun x t' => chainK (phaseK σm εm Fm x.1) cm 0 x.2 (fun s' => Flp x.1 t' s'))
      (hinc.comp (f := fun p : ((V → ℝ) × ℝ) × ℝ => ((p.1.1, p.2), p.1.2)) (by fun_prop))
    exact h.comp (f := fun p : (V → ℝ) × ℝ × ℝ => ((p.1, p.2.2), p.2.1)) (by fun_prop)
  · -- the bound
    simp only [e']
    refine norm_chainK_le hBF0 (hmp α) cp 0 (by positivity) (fun x hx => ?_) t ht
    exact norm_chainK_le hBF0 (hmm α) cm 0 hBl0 (fun y hy => (hBl α x hx y hy).trans
      (le_max_left _ _)) s hs
  · -- the limit
    have hKp := KFam.ofFinset (Finset.range cp.size) (R := fun j θ t s => RI θ ζ Z (SFp j) (Fp j) t s)
      (R₀ := Jp) fun j hj => hRp j (Finset.mem_range.1 hj)
    have hKm := KFam.ofFinset (Finset.range cm.size) (R := fun j θ t s => RI θ ζ Z (SFm j) (Fm j) t s)
      (R₀ := Jm) fun j hj => hRm j (Finset.mem_range.1 hj)
    have hKl := KFam.single hlp.lim
    have h := regLim2_type2 (bbp := fun j => decide (σp j ∈ Z)) (bbm := fun j => decide (σm j ∈ Z))
      hKp hKm hKl cp cm
    refine (h.congr_lim fun t ht s hs => ?_).congr ?_
    · refine chainL_congr cp 0 (fun j _ hj τ _ => ?_) (fun x hx => ?_) t ht
      · simp [kD, Finset.mem_range.2 (by simpa using hj)]
      · refine chainL_congr cm 0 (fun j _ hj τ _ => ?_) (fun y _ => rfl) s hs
        simp [kD, Finset.mem_range.2 (by simpa using hj)]
    · filter_upwards [eventually_pos_nhdsGT] with θ hθ t ht s hs
      rw [RI_type2 hθ ζ hζ Z hεp hεm hFp hFm hBF0 hBFp hBFm hlp.nice cp cm hdp hdm hpm hml ht hs]
      refine chainK_congr cp 0 (fun j _ hj ta hta tb htb => ?_) (fun x hx => ?_) t ht
      · simp [regPK, kP, Finset.mem_range.2 (by simpa using hj), clamp01_eq hta, clamp01_eq htb]
      · refine chainK_congr cm 0 (fun j _ hj ta hta tb htb => ?_) (fun y hy => ?_) s hs
        · simp [regPK, kP, Finset.mem_range.2 (by simpa using hj), clamp01_eq hta, clamp01_eq htb]
        · simp [clamp01_eq hx, clamp01_eq hy]

end WaveTurbulence.Cancel
