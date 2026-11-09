/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Ghost.Step2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Ghost.Cone8
/-! **L6E GHOST, part 19: `UStep2.excess_cone`** — M1-R2 Theorem 6.1 (e) at a uniform Op-2 creation step.

Main's `FinalCountG3.UStep2.excess` (R38(2)) for a triangle step that creates `α`-atoms carrying the cone hypotheses of
the (f′) class NC (`CreationCone`, `k ∈ {1, 2}` NC critical pairs with `s(P)` this step): the right-hand side
`C · excessRHS(αnew, ΔF, ΔV_β) / ∏_{α-ghosts} T(Q_g, κ_g)` holds with the factor `9·25^d · L^{-5ηk}`
(`TriReal` only). Copy of main's proof (sha256 in COPIED-SHA256SUMS). -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.GammaLow.FinalCount.Ghost
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}
variable {L γ η : ℝ} {w : Mom d} {Adm0 : (D₀ → (Fin d → ℤ)) → Prop} {M₀ : Molecule V D₀}

/-- **`UStep2.excess_cone`**: a uniform Step 2 `h → h'` creating `α`-atoms with `k` creation cones has the charged
deviation times `9·25^d · L^{-5ηk}` (Theorem 6.1 (e); `TriReal` only). -/
theorem UStep2.excess_cone {δ C₁ : ℝ} {c : ℕ} (H : TriReal d L γ η δ C₁) {h h' : HSt V D₀}
    (hs : UStep2 L γ η w Adm0 h h') (hc : LCtx M₀ h.s) (hCl : Clean h.s) (hCB : CompBeta h.s)
    (hAR : AtomRelU Adm0 L w h) (P : Finset V → ℝ)
    (hP0 : ∀ S, 0 ≤ P S) (hPh : LadderHered M₀ P) (hn : (h.s.M.atoms.card : ℝ) ≤ Real.log L ^ c)
    (hne : ∃ k0, Adm0 k0) (hRI : ∀ k0, Adm0 k0 → HInv L γ η w k0 h ∧ HGap L w k0 h)
    (k : ℕ)
    (hcone : ∀ (T : TriData h.s.M) (Q : Fin 2 → ℝ) (kp : Fin 2 → ℕ) (hcl : PClosed T.kept (triKeep h.s T)),
      h' = h.triPost T Q kp hcl → CreationCone T L γ δ η w (AdmS Adm0 h.s) (Q 0) (Q 1)
        (if h.s.cls (T.t 0) = .eps then kp 0 else 0) (if h.s.cls (T.t 1) = .eps then kp 1 else 0) k) :
    ∃ (T : TriData h.s.M) (Q : Fin 2 → ℝ) (kp : Fin 2 → ℕ) (hcl : PClosed T.kept (triKeep h.s T)),
      h' = h.triPost T Q kp hcl ∧
      IsDeviation (h.s.M.countA L γ δ C₁ w (AdmS Adm0 h.s) P)
        (h'.s.M.countA L γ δ C₁ w (AdmS Adm0 h'.s) P)
        (ENNReal.ofReal (9 * 25 ^ d * L ^ (-5 * η * (k : ℝ)) * (ghostConstLow d c η δ *
          (excessRHS L γ η (triAlphaNew h T Q kp) ((h'.s.M.numComponents : ℤ) - h.s.M.numComponents)
            (betaCount h'.s - betaCount h.s) / labelProd L γ η (alphaGhostList h T))))) := by
  cases hs with
  | tri T Q kp hQ hkp hsg hsim hcl hnz hι₀ hι₀' hι₁ hι₁' h3 =>
    refine ⟨T, Q, kp, hcl, rfl, ?_⟩
    have hL0 : 0 < L := lt_of_lt_of_le (Real.exp_pos 1) H.hL
    have hC0 : 0 < C₁ := by linarith [H.hC]
    have hgd : ∀ j, h.s.cls (T.t j) ≠ .eps → h.s.M.deg (T.t j) ≤ 2 := by
      intro j hj
      by_contra hcon
      exact hj (hc.eps _ (T.t_mem j) (by omega))
    obtain ⟨k1, hk1⟩ := hne
    have hG : ∀ j R k, h.s.cls (T.t j) = .alpha R k → IsLabel L γ η R ∧ (k = 0 ∨ k = 50) ∧
        ∀ k0, Adm0 k0 → GapSim L w (k0 ∘ h.s.down) (T.a j) (T.b j) R := by
      intro j R k hj
      obtain ⟨hI1, hG1⟩ := hRI k1 hk1
      have h1 := ghost_alpha_gap hI1 hG1 (T.t_mem j) hj (T.atom_a j) (T.atom_b j) (T.out_a j) (T.out_b j)
      refine ⟨h1.1, h1.2.1, fun k0 hk0 => ?_⟩
      obtain ⟨hI, hG⟩ := hRI k0 hk0
      exact (ghost_alpha_gap hI hG (T.t_mem j) hj (T.atom_a j) (T.atom_b j) (T.out_a j) (T.out_b j)).2.2
    have hnz' : ∀ κ, AdmS Adm0 h.s κ → ∀ j, Molecule.gapAt L w κ (T.a j) (T.b j) ≠ 0 := by
      rintro _ ⟨k0, hk0, rfl⟩ j
      fin_cases j
      · exact gapKind_SG_ne_zero (hsg k0 hk0 0)
      · exact gapKind_SG_ne_zero (hsg k0 hk0 1)
      · exact hnz k0 hk0
    have hctx1 := hc.cutSt (T.cd1) .beta (if h.s.cls (T.t 0) = .eps then .beta else .ghost) (by simp)
      (by split_ifs <;> simp)
    have hctx2 := hctx1.cutSt (T.cd2) .beta (if h.s.cls (T.t 1) = .eps then .beta else .ghost) (by simp)
      (by split_ifs <;> simp)
    have hctx3 := hctx2.cutSt (T.cd3) .beta (if h.s.cls (T.t 2) = .eps then .beta else .ghost) (by simp)
      (by split_ifs <;> simp)
    have hAdm' : ∀ κ, AdmS Adm0 h.s κ → AdmS Adm0 ((triCuts h.s T).delSt T.TP T.pclosed) (fun x => κ x.1) :=
      fun κ hκ => AdmS.delSt (s := triCuts h.s T) T.TP T.pclosed hκ
    have key := Tri.triangle_excess_cone T H (fun a ha => hc.d4 a ha) c hn w (AdmS Adm0 h.s)
      (AdmS Adm0 ((triCuts h.s T).delSt T.TP T.pclosed)) hAdm' P hP0
      (fun S' hS' S hS => hc.hPinh hPh hctx1 S' hS' S hS)
      (fun S' hS' S hS => hctx1.hPinh hPh hctx2 S' hS' S hS)
      (fun S' hS' S hS => hctx2.hPinh hPh hctx3 S' hS' S hS)
      hnz'
      (Q 0) (Q 1) (if h.s.cls (T.t 0) = .eps then kp 0 else 0) (if h.s.cls (T.t 1) = .eps then kp 1 else 0)
      (by split_ifs
          · exact hkp 0
          · exact Or.inl rfl)
      (by split_ifs
          · exact hkp 1
          · exact Or.inl rfl)
      (hQ 0).2.1 (hQ 0).2.2 (hQ 1).2.1 (hQ 1).2.2
      (by rintro _ ⟨k0, hk0, rfl⟩; exact (hsim k0 hk0 0).2)
      (by
        intro h50
        have e0 : h.s.cls (T.t 0) = .eps := by
          by_contra e; rw [if_neg e] at h50; omega
        rw [if_pos e0] at h50
        exact (hι₀ e0 h50).ball hAR)
      (by rintro _ ⟨k0, hk0, rfl⟩; exact (hsim k0 hk0 1).2)
      (by
        intro h50
        have e1 : h.s.cls (T.t 1) = .eps := by
          by_contra e; rw [if_neg e] at h50; omega
        rw [if_pos e1] at h50
        exact (hι₁ e1 h50).imp (fun hu => hu.ball hAR) (fun hs => sibU_reading hs.2))
      (fun j => h.s.cls (T.t j) ≠ .eps) (fun j => ∃ R k, h.s.cls (T.t j) = .alpha R k)
      (by rintro j ⟨R, k, hj⟩; rw [hj]; simp) hgd (ghostQ h T) (ghostK h T)
      (by rintro j ⟨R, k, hj⟩; rw [ghostQ_eq hj]; exact (hG j R k hj).1.2.1)
      (by rintro j ⟨R, k, hj⟩; rw [ghostQ_eq hj]; exact (hG j R k hj).1.2.2)
      (by
        rintro j ⟨R, k, hj⟩ _ ⟨k0, hk0, rfl⟩
        rw [ghostQ_eq hj]; exact ((hG j R k hj).2.2 k0 hk0).1)
      k (hcone T Q kp hcl rfl)
    have hno := triKeep_dartless T hgd
    have hghost := countA_restrict_dartless T.kept (triKeep h.s T) hcl hno L γ δ C₁ w hL0 H.hδ0 hC0
      (AdmS Adm0 ((triCuts h.s T).delSt T.TP T.pclosed))
      (AdmS Adm0 (h.triPost T Q kp hcl).s)
      (fun κ hκ => AdmS.delSt (s := (((triCuts h.s T).delSt T.TP T.pclosed).withCls (triCls h.s T Q kp)))
        (triKeep h.s T) hcl hκ) P
      (fun S => zero_le_one.trans (ladderWeight_ge_one L γ δ (P S) H.hL H.hδ0.le (hP0 S)))
    have htr := isDeviation_trans' key hghost
    rw [mul_one] at htr
    unfold triRHSCone triRHS0 at htr
    have hN := triSt_numComponents_ghost T Q kp hcl hgd
    have hB := betaCount_incr h T Q kp hcl hgd
    have hset : (Finset.univ.filter fun j => h.s.cls (T.t j) ≠ .eps ∧ ¬ ∃ R k, h.s.cls (T.t j) = .alpha R k) =
        Finset.univ.filter fun j => h.s.cls (T.t j) = .beta := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hne', hna⟩
        have hg := hCl (T.t j) (T.t_mem j)
        rcases hc : h.s.cls (T.t j) with _ | ⟨R, k⟩ | _ | _
        · exact absurd hc hne'
        · exact absurd ⟨R, k, hc⟩ hna
        · rfl
        · exact absurd hc hg
      · intro hb; rw [hb]; simp
    have e1 : (((h.triPost T Q kp hcl).s.M.numComponents : ℕ) : ℤ) - (h.s.M.numComponents : ℤ) =
        (T.kept.numComponents : ℤ) - h.s.M.numComponents -
          ((Finset.univ.filter fun j => h.s.cls (T.t j) ≠ .eps).card : ℤ) := by
      have : (((h.triPost T Q kp hcl).s.M.numComponents : ℕ) : ℤ) +
          ((Finset.univ.filter fun j => h.s.cls (T.t j) ≠ .eps).card : ℤ) = (T.kept.numComponents : ℤ) := by
        exact_mod_cast hN
      linarith
    rw [← mul_div_assoc] at htr ⊢
    rw [e1, hB, ← alphaLabels_eq_triAlphaNew h T Q kp hgd, labelProd_eq_ghostCharge, ← hset]
    exact htr

end WaveTurbulence.GammaLow.FinalCount.Ghost
