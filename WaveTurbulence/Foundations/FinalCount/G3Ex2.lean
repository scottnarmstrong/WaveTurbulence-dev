/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3Ex34
public import WaveTurbulence.Foundations.FinalCount.G3Ctx
public import WaveTurbulence.Foundations.FinalCount.G3Ghost
public import WaveTurbulence.Foundations.FinalCount.G3URun
public import WaveTurbulence.Foundations.FinalCount.G3HRun
public import WaveTurbulence.Foundations.FinalCount.TriSib3
/-! **FINALCOUNT-G3: excessprop1 (1) for Step 2 (triangles)** (DH23 Prop 9.4, Step 2, L1793--L1796, glued to
FINALCOUNT-G2-SIBLING `triangle_excess_sibling`).

The three cuts are G2's `T.m1, T.m2, T.m3`, the removal of the triangle is `T.kept`; the ghost deletion of
`triSt` (reading R-T1: an already cut triangle atom leaves an isolated remainder) is a dartless restriction
(`countA_restrict_dartless`: `𝔄` is unchanged).  The `κ = 50` of the second cut comes from an older cut still carried by a
present atom (`IotaUnif`), or from the first cut of the same triangle (`SibUnif`, the sibling count). -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}
variable {L γ η : ℝ} {w : Mom d} {Adm0 : (D₀ → (Fin d → ℤ)) → Prop} {M₀ : Molecule V D₀}

theorem isDeviation_trans' {a b c I J : ℝ≥0∞} (h1 : IsDeviation a b I) (h2 : IsDeviation b c J) :
    IsDeviation a c (I * J) := by
  unfold IsDeviation at *
  calc a ≤ I * b := h1
    _ ≤ I * (J * c) := by gcongr
    _ = I * J * c := by ring

theorem gapKind_SG_ne_zero {r : Mom d} (h : Molecule.gapKind L γ η r = .SG) : r ≠ 0 := by
  intro e; subst e; simp [Molecule.gapKind] at h

theorem sibU_reading {h : HSt V D₀} {T : TriData h.s.M} {R : ℝ}
    (hS : SibUnif Adm0 L η w (h.s.pr (T.a 0) (T.b 0)) (h.s.pr (T.a 1) (T.b 1)) R) :
    T.SiblingReading L w (AdmS Adm0 h.s) (L ^ (-50 * η) * R) := by
  obtain ⟨sg, hsg, hb⟩ := hS
  rcases hsg with rfl | rfl
  · refine ⟨-1, Or.inr rfl, ?_⟩
    rintro _ ⟨k0, hk0, rfl⟩
    have := (hb k0 hk0).2
    have e : Molecule.gapAt L w (k0 ∘ h.s.down) (T.a 1) (T.b 1) - ((-1 : ℤ) : ℝ) • Molecule.gapAt L w (k0 ∘ h.s.down) (T.a 0) (T.b 0) =
        pgap L w k0 (h.s.pr (T.a 1) (T.b 1)) + (1 : ℝ) • pgap L w k0 (h.s.pr (T.a 0) (T.b 0)) := by
      simp [pgap, St.pr]; rfl
    rw [e]; exact this
  · refine ⟨1, Or.inl rfl, ?_⟩
    rintro _ ⟨k0, hk0, rfl⟩
    have := (hb k0 hk0).2
    have e : Molecule.gapAt L w (k0 ∘ h.s.down) (T.a 1) (T.b 1) - ((1 : ℤ) : ℝ) • Molecule.gapAt L w (k0 ∘ h.s.down) (T.a 0) (T.b 0) =
        pgap L w k0 (h.s.pr (T.a 1) (T.b 1)) + (-1 : ℝ) • pgap L w k0 (h.s.pr (T.a 0) (T.b 0)) := by
      simp [pgap, St.pr]; rfl
    rw [e]; exact this

theorem kept_deg_f_zero {s : St.{u} V D₀} (T : TriData s.M) (j : Fin 3) (hd : s.M.deg (T.t j) ≤ 2) :
    T.kept.deg (T.f j) = 0 := by
  have hP : T.TP (T.f j) := fun i e => T.f_ne_t j i e
  have h5 := tri_deg_f T j
  have h6 : T.kept.deg (T.f j) = T.m3.deg (T.f j) := restrictP_deg T.m3 T.TP T.pclosed hP
  have := tri_deg_ge_two T j
  omega

/-- **excessprop1 (1), Step 2** (DH23 Prop 9.4, L1793--L1796): the triangle removal of `UStep2`, with the bookkeeping of G2
(`ΔF = F(T.kept) - F(pre)`, `ΔV_β = 3 - #α`; a ghost of `triSt` is a component of `T.kept` that the ghost deletion removes
without changing `𝔄`). -/
theorem tri_excess {δ C₁ : ℝ} (H : TriReal d L γ η δ C₁) {h : HSt V D₀} (hc : LCtx M₀ h.s)
    (hAR : AtomRelU Adm0 L w h) (P : Finset V → ℝ) (hP0 : ∀ S, 0 ≤ P S) (hPh : LadderHered M₀ P) (c : ℕ)
    (hn : (h.s.M.atoms.card : ℝ) ≤ Real.log L ^ c) (T : TriData h.s.M) (Q : Fin 2 → ℝ) (kp : Fin 2 → ℕ)
    (hQ : ∀ j : Fin 2, IsLabel L γ η (Q j)) (hkp : ∀ j : Fin 2, kp j = 0 ∨ kp j = 50)
    (hsg : ∀ k0, Adm0 k0 → ∀ j : Fin 2, Molecule.gapKind L γ η
      (Molecule.gapAt L w (k0 ∘ h.s.down) (T.a j.castSucc) (T.b j.castSucc)) = .SG)
    (hsim : ∀ k0, Adm0 k0 → ∀ j : Fin 2, GapSim L w (k0 ∘ h.s.down) (T.a j.castSucc) (T.b j.castSucc) (Q j))
    (hcl : PClosed T.kept (triKeep h.s T))
    (hnz : ∀ k0, Adm0 k0 → pgap L w k0 (h.s.pr (T.a 2) (T.b 2)) ≠ 0)
    (hι₀ : kp 0 = 50 → IotaUnif Adm0 L η w h (h.s.pr (T.a 0) (T.b 0)) (Q 0))
    (hι₁ : kp 1 = 50 → IotaUnif Adm0 L η w h (h.s.pr (T.a 1) (T.b 1)) (Q 1) ∨
      SibUnif Adm0 L η w (h.s.pr (T.a 0) (T.b 0)) (h.s.pr (T.a 1) (T.b 1)) (Q 1)) :
    IsDeviation (h.s.M.countA L γ δ C₁ w (AdmS Adm0 h.s) P)
      ((h.triPost T Q kp hcl).s.M.countA L γ δ C₁ w (AdmS Adm0 (h.triPost T Q kp hcl).s) P)
      (ENNReal.ofReal (triConst d c η δ *
        excessRHS L γ η (T.alphaLabels (Q 0) (Q 1) (kp 0) (kp 1)) ((T.kept.numComponents : ℤ) - h.s.M.numComponents)
          (3 - ((T.alphaLabels (Q 0) (Q 1) (kp 0) (kp 1)).length : ℤ)))) := by
  have hL0 : 0 < L := lt_of_lt_of_le (Real.exp_pos 1) H.hL
  have hC0 : 0 < C₁ := by linarith [H.hC]
  have hctx1 := hc.cutSt (T.cd1) .beta (if h.s.cls (T.t 0) = .eps then .beta else .ghost) (by simp)
    (by split_ifs <;> simp)
  have hctx2 := hctx1.cutSt (T.cd2) .beta (if h.s.cls (T.t 1) = .eps then .beta else .ghost) (by simp)
    (by split_ifs <;> simp)
  have hctx3 := hctx2.cutSt (T.cd3) .beta (if h.s.cls (T.t 2) = .eps then .beta else .ghost) (by simp)
    (by split_ifs <;> simp)
  have hAdm' : ∀ κ, AdmS Adm0 h.s κ → AdmS Adm0 ((triCuts h.s T).delSt T.TP T.pclosed) (fun x => κ x.1) :=
    fun κ hκ => AdmS.delSt (s := triCuts h.s T) T.TP T.pclosed hκ
  have key := T.triangle_excess_sibling H (fun a ha => hc.d4 a ha) c hn w (AdmS Adm0 h.s)
    (AdmS Adm0 ((triCuts h.s T).delSt T.TP T.pclosed)) hAdm' P hP0
    (fun S' hS' S hS => hc.hPinh hPh hctx1 S' hS' S hS)
    (fun S' hS' S hS => hctx1.hPinh hPh hctx2 S' hS' S hS)
    (fun S' hS' S hS => hctx2.hPinh hPh hctx3 S' hS' S hS)
    (by
      rintro _ ⟨k0, hk0, rfl⟩ j
      fin_cases j
      · exact gapKind_SG_ne_zero (hsg k0 hk0 0)
      · exact gapKind_SG_ne_zero (hsg k0 hk0 1)
      · exact hnz k0 hk0)
    (Q 0) (Q 1) (kp 0) (kp 1) (hkp 0) (hkp 1) (hQ 0).2.1 (hQ 0).2.2 (hQ 1).2.1 (hQ 1).2.2
    (by rintro _ ⟨k0, hk0, rfl⟩; exact (hsim k0 hk0 0).2)
    (fun h50 => (hι₀ h50).ball hAR)
    (by rintro _ ⟨k0, hk0, rfl⟩; exact (hsim k0 hk0 1).2)
    (fun h50 => (hι₁ h50).imp (fun hu => hu.ball hAR) (fun hs => sibU_reading hs))
  have hno : ∀ x : PDart T.m3 T.TP, triKeep h.s T (T.kept.atom x) := by
    intro x j hj hxj
    have hd : h.s.M.deg (T.t j) ≤ 2 := by
      by_contra hcon
      exact hj (hc.eps _ (T.t_mem j) (by omega))
    have h0 := kept_deg_f_zero T j hd
    have hmem : x ∈ T.kept.dartsAt (T.f j) := (mem_dartsAt T.kept _ x).2 hxj
    have : 0 < T.kept.deg (T.f j) := Finset.card_pos.2 ⟨x, hmem⟩
    omega
  have hghost := countA_restrict_dartless T.kept (triKeep h.s T) hcl hno L γ δ C₁ w hL0 H.hδ0 hC0
    (AdmS Adm0 ((triCuts h.s T).delSt T.TP T.pclosed))
    (AdmS Adm0 (h.triPost T Q kp hcl).s) (fun κ hκ => AdmS.delSt (s := (((triCuts h.s T).delSt T.TP T.pclosed).withCls (triCls h.s T Q kp))) (triKeep h.s T) hcl hκ) P
    (fun S => zero_le_one.trans (ladderWeight_ge_one L γ δ (P S) H.hL H.hδ0.le (hP0 S)))
  have := isDeviation_trans' key hghost
  rw [mul_one] at this
  exact this

/-! ### R38(2): the charged triangle bound with the TRUE increments -/

/-- The `α`-ghosts of a triangle: the already-cut `α` atoms `t j`, with their stored labels `(Q_g, κ_g)`. -/
noncomputable def alphaGhostList (h : HSt V D₀) (T : TriData h.s.M) : List (ℝ × ℕ) :=
  (List.finRange 3).filterMap fun j => match h.s.cls (T.t j) with
    | .alpha R k => some (R, k)
    | _ => none

/-- The new `α`-atoms (labels) of a triangle step: the non-ghost `f_j`, `j ∈ {0,1}`, that `triCls` makes `α`. -/
noncomputable def triAlphaNew (h : HSt V D₀) (T : TriData h.s.M) (Q : Fin 2 → ℝ) (kp : Fin 2 → ℕ) : List (ℝ × ℕ) :=
  (List.finRange 2).filterMap fun j => if h.s.cls (T.t j.castSucc) = .eps then
    (match triCls h.s T Q kp (T.f j.castSucc) with | .alpha R k => some (R, k) | _ => none) else none

/-- The number of `β`-atoms of a state. -/
noncomputable def betaCount (s : St.{u} V D₀) : ℤ := ((s.M.atoms.filter fun a => s.cls a = .beta).card : ℤ)

/-- The refund factor `∏ T(Q_g, κ_g)` of a list of labels, `T(Q,κ) = L^{(γ+3η)/2 - κη} Q`. -/
noncomputable def labelProd (L γ η : ℝ) (l : List (ℝ × ℕ)) : ℝ :=
  (l.map fun p => L ^ ((γ + 3 * η) / 2 - (p.2 : ℝ) * η) * p.1).prod

/-- The label of an already-cut `α`/`β` atom of degree `2` on the triangle darts, from the run invariants. -/
theorem ghost_alpha_gap {h : HSt V D₀} {κ : D₀ → (Fin d → ℤ)} (hI : HInv L γ η w κ h) (hG : HGap L w κ h)
    {a : V} (ha : a ∈ h.s.M.atoms) {R : ℝ} {k : ℕ} (hc : h.s.cls a = .alpha R k) {x y : h.s.D}
    (hx : h.s.M.atom x = a) (hy : h.s.M.atom y = a) (ho1 : h.s.M.out x = false) (ho2 : h.s.M.out y = true) :
    IsLabel L γ η R ∧ (k = 0 ∨ k = 50) ∧ GapSim L w (κ ∘ h.s.down) x y R := by
  obtain ⟨hl, p, vis, hr, hp, hk, -, -⟩ := (hI.ok a ha).1 R k hc
  obtain ⟨p', vis', hr', hn⟩ := hG.dg a ha (by rw [hc]; simp) x y hx hy ho1 ho2
  rw [hr] at hr'; simp only [Option.some.injEq, Prod.mk.injEq] at hr'
  obtain ⟨rfl, -⟩ := hr'
  have := norm_gap_of_pm hn
  exact ⟨hl, hk, by unfold GapSim; rw [this]; exact hp⟩

theorem ghost_beta_gap {h : HSt V D₀} {κ : D₀ → (Fin d → ℤ)} (hI : HInv L γ η w κ h) (hG : HGap L w κ h)
    {a : V} (ha : a ∈ h.s.M.atoms) (hc : h.s.cls a = .beta) {x y : h.s.D}
    (hx : h.s.M.atom x = a) (hy : h.s.M.atom y = a) (ho1 : h.s.M.out x = false) (ho2 : h.s.M.out y = true) :
    Molecule.gapAt L w (κ ∘ h.s.down) x y ≠ 0 := by
  obtain ⟨p, vis, hr, hnz⟩ := (hI.ok a ha).2 hc
  obtain ⟨p', vis', hr', hn⟩ := hG.dg a ha (by rw [hc]; simp) x y hx hy ho1 ho2
  rw [hr] at hr'; simp only [Option.some.injEq, Prod.mk.injEq] at hr'
  obtain ⟨rfl, -⟩ := hr'
  intro e; rw [e] at hn
  rcases hn with hn | hn
  · exact hnz hn.symm
  · exact hnz (neg_eq_zero.1 hn.symm)

end WaveTurbulence.FinalCountG3
