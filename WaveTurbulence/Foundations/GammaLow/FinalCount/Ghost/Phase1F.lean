/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Ghost.Phase1E
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmPhase1c
/-! **Ghost assembly, Phase 1 (F): the triple-cut node with the bank** (design: `CHAIN-DESIGN.md`).

`nodeT_bank`: for a triple node `t` (H's `NodeT`: a cut of `v` along two of `≥ 3` bonds to one atom `u`; post state
`h.cut3Post v v₂ x₁ x₂ R kp`, an α-cut) of a class `A` with bank `≤ b` and a split index `σ`, the split class
`B = tripSplit … σ` (`split1` with the new atoms `v`, `v₂` and the cut gap) satisfies `Inv1` at the post state,
`epsCount` drops, and for `k = k1Of σ`: the child's bank is `≤ b + k` and
`QS h B ≤ 3·5^d·max cα cβ·stepRHS·L^{-5ηk} · QS h' B`. The class `k = 0` uses H's `nodeT_facts`; a cone class uses
`cut_excess_cone` with `k = 2` and `cutCone_of_crit`. The new atoms `v`, `v₂` are not adjacent (the darts `x₁`, `x₂`
left at `v` go to `u ≠ v₂`). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.GammaLow.FinalCount.Ghost
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.FinalCountAsm
open WaveTurbulence.VineCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

/-- A dart at `v` after the cut of `v` is one of the two cut darts. -/
theorem cut_atom_eq_v {D : Type*} [Fintype D] [DecidableEq D] {M : Molecule V D} {v v₂ : V} {x₁ x₂ : D}
    (hcd : M.IsCutData v v₂ x₁ x₂) {x : D} (hx : (M.cut v v₂ x₁ x₂).atom x = v) : x = x₁ ∨ x = x₂ := by
  change (if M.atom x = v ∧ x ≠ x₁ ∧ x ≠ x₂ then v₂ else M.atom x) = v at hx
  have hvf : v ≠ v₂ := fun e => hcd.2.1 (e ▸ hcd.1)
  split_ifs at hx with hcnd
  · exact absurd hx.symm hvf
  · by_contra hn
    push Not at hn
    exact hcnd ⟨hx, hn.1, hn.2⟩

section trip
variable [Infinite V] {M₀ : Molecule V D₀} {C : H.CollData M₀} {L γ η : ℝ} {h : HSt V D₀} {t : T3 h}

/-- **The split class `σ` of a triple node.** -/
noncomputable def tripSplit (Un : (D₀ → (Fin d → ℤ)) → Set (Src.Object Src.γL M₀)) (w : Mom d)
    (A : Set (D₀ → (Fin d → ℤ))) (t : T3 h) (σ : Sig1) : Set (D₀ → (Fin d → ℤ)) :=
  split1 L γ η w h (post3 h t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1)
    (cutSurv h t.1 (fresh h) t.2.1 t.2.2.1 ((2 : ℝ) ^ t.2.2.2.1) (if t.2.2.2.2.1 then 50 else 0))
    ![t.1, fresh h] (fun k0 => pgap L w k0 (h.s.pr t.2.1 t.2.2.1))
    (cls3 L γ η w h (H.Atrip C Un L γ η w h A) t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1 t.2.2.2.2.2.1 t.2.2.2.2.2.2) σ

/-- The two new atoms of a triple cut are not adjacent. -/
theorem trip_not_adj (hn : H.NodeT C L γ η h t) :
    ¬ (post3 h t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1).s.M.Adj t.1 (fresh h) := by
  obtain ⟨hc, -⟩ := hn.1
  obtain ⟨-, -, u, hu, -, hm₁, hm₂⟩ := hn.2
  rintro ⟨x, hx, hy⟩
  change (h.s.M.cut t.1 (fresh h) t.2.1 t.2.2.1).atom x = t.1 at hx
  change (h.s.M.cut t.1 (fresh h) t.2.1 t.2.2.1).atom (h.s.M.mate x) = fresh h at hy
  have hxv : x = t.2.1 ∨ x = t.2.2.1 := cut_atom_eq_v hc hx
  have huM : u ∈ h.s.M.atoms := hm₁ ▸ h.s.M.atom_mem _
  have hun : u ≠ fresh h := fun e => hc.2.1 (e ▸ huM)
  have hat : ∀ y, h.s.M.atom y = u → (h.s.M.cut t.1 (fresh h) t.2.1 t.2.2.1).atom y = u := by
    intro y hy'
    change (if h.s.M.atom y = t.1 ∧ y ≠ t.2.1 ∧ y ≠ t.2.2.1 then fresh h else h.s.M.atom y) = u
    rw [ite_eq_right (fun hc' => hu (hy'.symm.trans hc'.1))]; exact hy'
  rcases hxv with rfl | rfl
  · exact hun ((hat _ hm₁).symm.trans hy)
  · exact hun ((hat _ hm₂).symm.trans hy)

/-- **The triple-cut node with the bank.** -/
theorem nodeT_bank {Rn : ℕ} {Un : (D₀ → (Fin d → ℤ)) → Set (Src.Object Src.γL M₀)} {Fst : Set (Src.Object Src.γL M₀)}
    {δ C₁ : ℝ} {w : Mom d} {P : Finset V → ℝ} {A0 A : Set (D₀ → (Fin d → ℤ))}
    (HR : TriReal d L γ η δ C₁) (hS : SubHyp Rn M₀)
    (hp0 : PinnedM0 (fun k => k ∈ A0) L w M₀) (hP : LadderHered M₀ P) (hP0 : ∀ S, 0 ≤ P S) (c : ℕ)
    (hnc : ((2 * M₀.atoms.card : ℕ) : ℝ) ≤ Real.log L ^ c)
    (h0 : ∀ κ ∈ A0, ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0)
    (hA : H.Inv1 M₀ Rn C Un Fst L γ η w A0 A h) (hn : H.NodeT C L γ η h t) {b : ℕ}
    (hbank : bank L γ η w h A ≤ b) (σ : Sig1) :
    H.Inv1 M₀ Rn C Un Fst L γ η w A0 (tripSplit (C := C) (L := L) (γ := γ) (η := η) Un w A t σ) (post3 h t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1) ∧
    epsCount (post3 h t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1).s < epsCount h.s ∧
    bank L γ η w (post3 h t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1) (tripSplit (C := C) (L := L) (γ := γ) (η := η) Un w A t σ) ≤ b + k1Of σ ∧
    QS L γ δ C₁ w P h (tripSplit (C := C) (L := L) (γ := γ) (η := η) Un w A t σ) ≤
      ENNReal.ofReal (3 * 5 ^ d * max (cAlpha d γ η) (cBeta η c) *
        stepRHS L γ η h (post3 h t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1) * L ^ (-5 * η * ((k1Of σ : ℕ) : ℝ))) *
        QS L γ δ C₁ w P (post3 h t.1 t.2.1 t.2.2.1 t.2.2.2.1 t.2.2.2.2.1) (tripSplit (C := C) (L := L) (γ := γ) (η := η) Un w A t σ) := by
  set v := t.1 with hvdef
  set x₁ := t.2.1 with hx1def
  set x₂ := t.2.2.1 with hx2def
  set z := t.2.2.2.1 with hzdef
  set bb := t.2.2.2.2.1 with hbbdef
  set a := t.2.2.2.2.2.1 with hadef
  set sg := t.2.2.2.2.2.2 with hsgdef
  set R : ℝ := (2 : ℝ) ^ z with hRdef
  set kp : ℕ := if bb then 50 else 0 with hkpdef
  set v₂ := fresh h with hv₂def
  set h' := post3 h v x₁ x₂ z bb with hh'
  set B0 := cls3 L γ η w h (H.Atrip C Un L γ η w h A) x₁ x₂ z bb a sg with hB0
  set B := tripSplit (C := C) (L := L) (γ := γ) (η := η) Un w A t σ with hBdef
  set n : Fin 2 → V := ![v, v₂] with hndef
  set g : (D₀ → (Fin d → ℤ)) → Mom d := fun k0 => pgap L w k0 (h.s.pr x₁ x₂) with hgdef
  have hpost : h' = h.cut3Post v v₂ x₁ x₂ R kp := rfl
  obtain ⟨hcd, hε, h3, hR, ha, hb⟩ := hn.1
  have hBB0 : B ⊆ B0 := fun k hk => hk.1
  have hBA : B ⊆ A := fun k hk => (hBB0 hk).1.1
  have hself : cls3 L γ η w h B x₁ x₂ z bb a sg = B := by
    ext k; exact ⟨fun hk => hk.1, fun hk => ⟨hk, (hBB0 hk).2⟩⟩
  obtain ⟨hinv, hlt, hdevTR⟩ := H.nodeT_facts HR hS hp0 hP hP0 c hnc (hA.mono hBA)
    (fun k hk => ((hBB0 hk).1).2) hn
  rw [hself] at hinv hdevTR
  refine ⟨hinv, hlt, ?_⟩
  by_cases hBe : B = ∅
  · refine ⟨?_, ?_⟩
    · rw [hBe, bank_empty]; omega
    · rw [hBe, QS_empty]; exact bot_le
  rcases hA.2 with he | ⟨hc, hap, hr⟩
  · exact absurd (Set.eq_empty_of_subset_empty (he ▸ hBA)) hBe
  obtain ⟨κ, hκ⟩ := Set.nonempty_iff_ne_empty.2 hBe
  have hI : Inv Rn h.s := hc.good.1
  have hL : 0 < L := lt_of_lt_of_le (Real.exp_pos 1) HR.hL
  have hIE := H.invE_of_reach hS (h0 κ (hA.1 (hBA hκ))) (H.Reach1.toAny (hr κ (hBA hκ)))
  have hBal : BalS h.s := hIE.bal
  have hRI : ∀ k0 ∈ B, HInv L γ η w k0 h ∧ HGap L w k0 h := fun k0 hk0 => by
    have := H.runInv_of_reach hS (h0 k0 (hA.1 (hBA hk0))) (H.Reach1.toAny (hr k0 (hBA hk0)))
    exact ⟨this.hrec, this.gap⟩
  have hv₂ : v₂ ∉ h.s.M.atoms := hcd.2.1
  have hvv : v ≠ v₂ := fun e => hv₂ (e ▸ hcd.1)
  have hsurv := cutSurvMap h v v₂ x₁ x₂ R kp hv₂
  have hgv : ∀ k0 ∈ B, ∀ j, IsCritA L γ η h' (n j) →
      gvec h' L w k0 (n j) = g k0 ∨ gvec h' L w k0 (n j) = -g k0 := by
    intro k0 _ j _
    left
    fin_cases j
    · exact gvec_cut_v h v v₂ x₁ x₂ R kp hvv L w k0
    · exact gvec_cut_v₂ h v v₂ x₁ x₂ R kp L w k0
  have hnew : ∀ x, IsCritA L γ η h' x → x ∉ cutSurv h v v₂ x₁ x₂ R kp → ∃ j, x = n j := by
    intro x hx hX
    rcases cut_critA_cases h v v₂ x₁ x₂ R kp hx hX with e | e
    · exact ⟨0, e⟩
    · exact ⟨1, e⟩
  have hpair : NCEdge L γ η w h' B (n 0) (n 1) → n 0 ∈ cov1Of n σ ∨ n 1 ∈ cov1Of n σ := by
    intro hE
    exact absurd hE.2.2.2.1 (trip_not_adj hn)
  have hbk : bank L γ η w h' B ≤ bank L γ η w h A + (cov1Of n σ).card := by
    refine bank_step hsurv hBA (critSet L γ η h) (cov1Of n σ) ?_ ?_
    · intro x y hE hx hy
      exact Or.inl ⟨mem_critSet.2 (hsurv.critA hx hE.2.1), mem_critSet.2 (hsurv.critA hy hE.2.2.1)⟩
    · exact edge_cover1 n g hsurv (B0 := B0) subset_rfl hnew hgv hpair
  have hcov := card_cov1Of_le n σ
  refine ⟨by omega, ?_⟩
  have hX0 : 0 ≤ stepRHS L γ η h h' := by
    have hc'' := (hinv.2.resolve_left hBe)
    unfold stepRHS
    have h1 := apProd_pos (L := L) (γ := γ) (η := η) hL hap
    have h2 := apProd_pos (L := L) (γ := γ) (η := η) hL hc''.2.1
    positivity
  by_cases hz : ∀ j, sOf σ j = 0
  · -- the TR class
    rw [k1Of_eq_zero hz]
    refine hdevTR.trans (mul_le_mul' ?_ le_rfl)
    have : (1 : ℝ) ≤ 5 ^ d := one_le_pow₀ (by norm_num)
    have h1 := ofReal_le_mul_rpow_zero (L := L) (η := η) (a := 3 * 5 ^ d)
      (X := max (cAlpha d γ η) (cBeta η c) * stepRHS L γ η h h') (by linarith)
    refine h1.trans (le_of_eq (congrArg ENNReal.ofReal ?_))
    ring
  · -- a cone class: `cut_excess_cone` with `k = 2`
    push Not at hz
    obtain ⟨j, hsj⟩ := hz
    rw [k1Of_eq_two ⟨j, hsj⟩]
    obtain ⟨hcj, y, hyX, hyc, hcone⟩ := stat1_cone n g hsurv (B0 := B0) subset_rfl ⟨κ, hκ⟩ j hsj
    have hclsn : (h.cut3Post v v₂ x₁ x₂ R kp).s.cls (n j) = if h.s.M.IsAlphaCut v v₂ x₁ x₂ then .alpha R kp else .beta := by
      fin_cases j
      · show Function.update (Function.update h.s.cls v _) v₂ _ v = _
        rw [Function.update_of_ne hvv, Function.update_self]
      · show Function.update (Function.update h.s.cls v _) v₂ _ v₂ = _
        rw [Function.update_self]
    obtain ⟨R₀, hR₀, hcrit⟩ := hcj.2.2
    rw [hclsn] at hR₀
    have hα : h.s.M.IsAlphaCut v v₂ x₁ x₂ := by
      by_contra hn'
      rw [ite_eq_right hn'] at hR₀
      cases hR₀
    rw [ite_eq_left hα] at hR₀
    obtain ⟨hRR, hkp0⟩ := Cls.alpha.inj hR₀
    have hc' := hinv.2.resolve_left hBe
    have hLC := LCtx.of_inv hI ⟨h.anc, hc.anc⟩ hc.rel
    have hLC' : LCtx M₀ (h.s.cutSt v v₂ x₁ x₂ (.alpha R kp) (.alpha R kp)) :=
      LCtx.cutSt hLC hcd (.alpha R kp) (.alpha R kp) (fun e => by cases e) (fun e => by cases e)
    have hPinh := LCtx.hPinh (s := h.s) (s' := h.s.cutSt v v₂ x₁ x₂ (.alpha R kp) (.alpha R kp)) hP hLC hLC'
    have hcone' : CutCone h.s.M x₁ x₂ L γ δ (L ^ (-6 * η)) w (AdmS (fun k => k ∈ B) h.s) :=
      cutCone_of_crit (by have := HR.hd; omega) hBal hRI hyc x₁ x₂ hcone
    have hcrit' : Crit L γ η R := by rw [hRR]; exact hcrit
    have hdev := cut_excess_cone (Adm0 := fun k => k ∈ B) HR hI P hP0 hcd hPinh R hR
      hcrit' (fun k0 hk0 => (hBB0 hk0).2.2.1) hα hcone' 2 le_rfl
    have hs' : h'.s = h.s.cutSt v v₂ x₁ x₂ (.alpha R kp) (.alpha R kp) := by
      show h.s.cutSt v v₂ x₁ x₂ (if h.s.M.IsAlphaCut v v₂ x₁ x₂ then .alpha R kp else .beta)
        (if h.s.M.IsAlphaCut v v₂ x₁ x₂ then .alpha R kp else .beta) = _
      rw [ite_eq_left hα]
    have hF : h'.s.M.numComponents = h.s.M.numComponents :=
      numComponents_cut_of_same h.s.M hcd ((isAlphaCut_iff h.s.M hcd).1 hα)
    have hBv : vBeta h'.s = vBeta h.s := by rw [hs']; exact vBeta_cutSt_alpha h.s hcd hε R kp
    have hAp : apProd L γ η h'.s = apProd L γ η h.s * apFactor L γ η (.alpha R kp) ^ 2 := by
      rw [hs']; exact apProd_cutSt_alpha h.s L γ η hcd hε R kp
    have hst := stepRHS_alpha hL (apProd_pos hL hap) hF hBv hAp
    have hEx : 0 ≤ excessRHS L γ η [(R, 0), (R, 0)] 0 0 := by rw [excessRHS_alpha]; positivity
    refine hdev.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal ?_) le_rfl)
    rw [hst, hkp0]
    have hLp : 0 ≤ L ^ (-5 * η * ((2 : ℕ) : ℝ)) := Real.rpow_nonneg hL.le _
    have h5 : (0 : ℝ) ≤ 3 * 5 ^ d := by positivity
    have hle := le_max_left (cAlpha d γ η) (cBeta η c)
    calc 3 * 5 ^ d * cAlpha d γ η * L ^ (-5 * η * ((2 : ℕ) : ℝ)) * excessRHS L γ η [(R, 0), (R, 0)] 0 0
        = (3 * 5 ^ d) * (L ^ (-5 * η * ((2 : ℕ) : ℝ)) * excessRHS L γ η [(R, 0), (R, 0)] 0 0) *
            cAlpha d γ η := by ring
      _ ≤ (3 * 5 ^ d) * (L ^ (-5 * η * ((2 : ℕ) : ℝ)) * excessRHS L γ η [(R, 0), (R, 0)] 0 0) *
            max (cAlpha d γ η) (cBeta η c) := mul_le_mul_of_nonneg_left hle (mul_nonneg h5 (mul_nonneg hLp hEx))
      _ = 3 * 5 ^ d * max (cAlpha d γ η) (cBeta η c) * excessRHS L γ η [(R, 0), (R, 0)] 0 0 *
            L ^ (-5 * η * ((2 : ℕ) : ℝ)) := by ring

end trip

end WaveTurbulence.GammaLow.FinalCount.Ghost
