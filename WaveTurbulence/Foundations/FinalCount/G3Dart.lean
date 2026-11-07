/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3HInv
public import WaveTurbulence.Foundations.FinalCount.G3Run
/-! **FINALCOUNT-G3: dart-level gaps of the cut atoms.**  For a decoration with charge `0` at the degree-`4` atoms of
`M_sub` (`(c_v)`-decorations with `c_v = 0` at degree-`4` atoms, `Molecule.countE`), the two remaining darts of a
cut degree-`4` atom `v₂` have gap `-(gap of the cut)`.  `HGap` records this for every `α`/`β`-atom of degree `2`:
`‖gap(x,y)‖ = ‖gap of the recorded cut‖`. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}
variable {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)}

/-- Charge `0` at every `ε`-atom of degree `4`. -/
def ChgS (L : ℝ) (w : Mom d) (κ : D₀ → (Fin d → ℤ)) (s : St.{u} V D₀) : Prop :=
  ∀ a ∈ s.M.atoms, s.cls a = .eps → s.M.deg a = 4 →
    ∑ x ∈ s.M.dartsAt a, s.M.dartSign x • Molecule.kvec L w (κ ∘ s.down) x = 0

/-- Dart gaps of the cut atoms. -/
def DGS (L : ℝ) (w : Mom d) (κ : D₀ → (Fin d → ℤ)) (h : HSt V D₀) : Prop :=
  ∀ a ∈ h.s.M.atoms, h.s.cls a ≠ .eps → ∀ x y : h.s.D, h.s.M.atom x = a → h.s.M.atom y = a →
    h.s.M.out x = false → h.s.M.out y = true →
    ∃ p vis, h.crec a = some (p, vis) ∧
      (Molecule.gapAt L w (κ ∘ h.s.down) x y = pgap L w κ p ∨ Molecule.gapAt L w (κ ∘ h.s.down) x y = -pgap L w κ p)

theorem norm_gap_of_pm {r p : Mom d} (h : r = p ∨ r = -p) : ‖r‖ = ‖p‖ := by
  rcases h with rfl | rfl
  · rfl
  · exact norm_neg _

structure HGap (L : ℝ) (w : Mom d) (κ : D₀ → (Fin d → ℤ)) (h : HSt V D₀) : Prop where
  chg : ChgS L w κ h.s
  dg : DGS L w κ h

theorem HGap.init {M₀ : Molecule V D₀}
    (h0 : ∀ a ∈ M₀.atoms, M₀.deg a = 4 → ∑ x ∈ M₀.dartsAt a, M₀.dartSign x • Molecule.kvec L w κ x = 0) :
    HGap L w κ (HSt.init M₀) where
  chg := fun a ha _ h4 => h0 a ha h4
  dg := fun a _ hc => absurd rfl hc

theorem HGap.delSt {h : HSt V D₀} (hG : HGap L w κ h) (P : V → Prop) [DecidablePred P] (hP : PClosed h.s.M P) :
    HGap L w κ ⟨h.s.delSt P hP, h.hist, h.crec, h.anc⟩ where
  chg := by
    intro a ha hc h4
    have haP : a ∈ h.s.M.atoms ∧ P a := Finset.mem_filter.1 ha
    have hdeg : h.s.M.deg a = 4 := by
      have := restrictP_deg h.s.M P hP haP.2
      exact this ▸ h4
    have e := restrictP_sum h.s.M P hP haP.2 (fun y => h.s.M.dartSign y • Molecule.kvec L w (κ ∘ h.s.down) y)
    exact e.trans (hG.chg a haP.1 hc hdeg)
  dg := by
    intro a ha hc x y hx hy hox hoy
    obtain ⟨p, vis, hr, hn⟩ := hG.dg a (Finset.mem_filter.1 ha).1 hc x.1 y.1 hx hy hox hoy
    exact ⟨p, vis, hr, hn⟩


theorem dartSign_of_out_false {D : Type*} (M : Molecule V D) {x : D} (h : M.out x = false) :
    M.dartSign x = -1 := by
  unfold Molecule.dartSign; rw [h]; simp

theorem dartSign_of_out_true {D : Type*} (M : Molecule V D) {x : D} (h : M.out x = true) :
    M.dartSign x = 1 := by
  unfold Molecule.dartSign; rw [h]; simp

/-- **The remaining darts of a cut degree-`4` atom**: `gap(x,y) = -gap(x₁,x₂)`. -/
theorem cut_v2_gap {h : HSt V D₀} (hG : HGap L w κ h) {v v₂ : V} {x₁ x₂ : h.s.D}
    (hcd : h.s.M.IsCutData v v₂ x₁ x₂) (hε : h.s.cls v = .eps) (h3 : 3 ≤ h.s.M.deg v) (h4 : h.s.M.deg v ≤ 4)
    {x y : h.s.D} (hx : (h.s.M.cut v v₂ x₁ x₂).atom x = v₂) (hy : (h.s.M.cut v v₂ x₁ x₂).atom y = v₂)
    (hox : h.s.M.out x = false) (hoy : h.s.M.out y = true) :
    Molecule.gapAt L w (κ ∘ h.s.down) x y = -Molecule.gapAt L w (κ ∘ h.s.down) x₁ x₂ := by
  set M := h.s.M with hM
  have hxy : x ≠ y := fun e => by rw [e] at hox; rw [hox] at hoy; exact Bool.false_ne_true hoy
  have hxS : x ∈ (M.cut v v₂ x₁ x₂).dartsAt v₂ := (mem_dartsAt _ _ _).2 hx
  have hyS : y ∈ (M.cut v v₂ x₁ x₂).dartsAt v₂ := (mem_dartsAt _ _ _).2 hy
  have hdeg := cut_deg_v₂ hcd
  have hcard : ((M.cut v v₂ x₁ x₂).dartsAt v₂).card + 2 = M.deg v := hdeg
  have h4' : M.deg v = 4 := by
    by_contra hne
    have h3' : M.deg v = 3 := by omega
    have : ((M.cut v v₂ x₁ x₂).dartsAt v₂).card = 1 := by omega
    have := Finset.one_lt_card.2 ⟨x, hxS, y, hyS, hxy⟩
    omega
  have hS : (M.cut v v₂ x₁ x₂).dartsAt v₂ = {x, y} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz; rcases hz with rfl | rfl <;> assumption
    · rw [Finset.card_pair hxy]; omega
  have hsplit := cut_sum_split M hcd (fun z => M.dartSign z • Molecule.kvec L w (κ ∘ h.s.down) z)
  rw [hG.chg v hcd.1 hε h4', hS, Finset.sum_pair hxy] at hsplit
  have hcv := cut_c_v M hcd L w (κ ∘ h.s.down)
  rw [show (∑ z ∈ (M.cut v v₂ x₁ x₂).dartsAt v, M.dartSign z • Molecule.kvec L w (κ ∘ h.s.down) z) =
    ∑ z ∈ (M.cut v v₂ x₁ x₂).dartsAt v, (M.cut v v₂ x₁ x₂).dartSign z • Molecule.kvec L w (κ ∘ h.s.down) z from rfl,
    hcv, dartSign_of_out_false M hox, dartSign_of_out_true M hoy] at hsplit
  have : Molecule.gapAt L w (κ ∘ h.s.down) x y = -Molecule.gapAt L w (κ ∘ h.s.down) x₁ x₂ := by
    unfold Molecule.gapAt
    simp only [neg_smul, one_smul] at hsplit
    have h2 : (Molecule.kvec L w (κ ∘ h.s.down) x - Molecule.kvec L w (κ ∘ h.s.down) y) +
        (Molecule.kvec L w (κ ∘ h.s.down) x₁ - Molecule.kvec L w (κ ∘ h.s.down) x₂) = 0 := by
      have e : (Molecule.kvec L w (κ ∘ h.s.down) x - Molecule.kvec L w (κ ∘ h.s.down) y) +
          (Molecule.kvec L w (κ ∘ h.s.down) x₁ - Molecule.kvec L w (κ ∘ h.s.down) x₂) =
          -(-(Molecule.kvec L w (κ ∘ h.s.down) x₁ - Molecule.kvec L w (κ ∘ h.s.down) x₂) +
            (-Molecule.kvec L w (κ ∘ h.s.down) x + Molecule.kvec L w (κ ∘ h.s.down) y)) := by abel
      rw [e, ← hsplit]; simp
    exact eq_neg_of_add_eq_zero_left h2
  exact this


theorem HGap.cut_gen {h : HSt V D₀} (hG : HGap L w κ h) {v v₂ : V} {x₁ x₂ : h.s.D}
    (hcd : h.s.M.IsCutData v v₂ x₁ x₂) (hε : h.s.cls v = .eps) (h3 : 3 ≤ h.s.M.deg v) (h4 : h.s.M.deg v ≤ 4)
    (c₁ c₂ : Cls) (hc1 : c₁ ≠ .eps) (hc2 : c₂ ≠ .eps) (vis nh : List (D₀ × D₀)) {na : V → V} :
    HGap L w κ ⟨h.s.cutSt v v₂ x₁ x₂ c₁ c₂, nh,
      Function.update (Function.update h.crec v (some (h.s.pr x₁ x₂, vis))) v₂
        (some (h.s.pr x₁ x₂, vis)), na⟩ where
  chg := by
    intro a ha hae h4'
    have ha' : a ∈ insert v₂ h.s.M.atoms := ha
    have hne : v₂ ≠ v := fun e => hcd.2.1 (e ▸ hcd.1)
    have e2 : a ≠ v₂ := by
      rintro rfl; rw [cutSt_cls_v₂] at hae; exact hc2 hae
    have e1 : a ≠ v := by
      rintro rfl; rw [cutSt_cls_v _ _ hne] at hae; exact hc1 hae
    rw [cutSt_cls_other _ _ e1 e2] at hae
    have hD : (h.s.cutSt v v₂ x₁ x₂ c₁ c₂).M.dartsAt a = h.s.M.dartsAt a := cut_dartsAt_other h.s.M hcd e1 e2
    have hdeg : h.s.M.deg a = 4 := by
      have h44 : (h.s.cutSt v v₂ x₁ x₂ c₁ c₂).M.deg a = 4 := h4'
      have : (h.s.cutSt v v₂ x₁ x₂ c₁ c₂).M.deg a = h.s.M.deg a := congrArg Finset.card hD
      omega
    have := hG.chg a ((Finset.mem_insert.1 ha').resolve_left e2) hae hdeg
    show ∑ x ∈ (h.s.cutSt v v₂ x₁ x₂ c₁ c₂).M.dartsAt a, h.s.M.dartSign x • Molecule.kvec L w (κ ∘ h.s.down) x = 0
    rw [hD]; exact this
  dg := by
    intro a ha hac x y hx hy hox0 hoy0
    have hox : h.s.M.out x = false := hox0
    have hoy : h.s.M.out y = true := hoy0
    have ha' : a ∈ insert v₂ h.s.M.atoms := ha
    have hne : v₂ ≠ v := fun e => hcd.2.1 (e ▸ hcd.1)
    by_cases e2 : a = v₂
    · subst e2
      refine ⟨h.s.pr x₁ x₂, vis, by simp, Or.inr ?_⟩
      exact cut_v2_gap hG hcd hε h3 h4 hx hy hox hoy
    · by_cases e1 : a = v
      · subst e1
        refine ⟨h.s.pr x₁ x₂, vis, by simp [Function.update_of_ne e2], Or.inl ?_⟩
        have hx' : x ∈ (h.s.M.cut a v₂ x₁ x₂).dartsAt a := (mem_dartsAt _ _ _).2 hx
        have hy' : y ∈ (h.s.M.cut a v₂ x₁ x₂).dartsAt a := (mem_dartsAt _ _ _).2 hy
        rw [cut_dartsAt_v_eq h.s.M hcd] at hx' hy'
        have hx'' : x = x₁ ∨ x = x₂ := (Finset.mem_insert.1 hx').imp id Finset.mem_singleton.1
        have hy'' : y = x₁ ∨ y = x₂ := (Finset.mem_insert.1 hy').imp id Finset.mem_singleton.1
        have o1 := hcd.2.2.2.2.2.1
        have o2 := hcd.2.2.2.2.2.2
        have hx1 : x = x₁ := by
          rcases hx'' with h' | h'
          · exact h'
          · have := o2; rw [← h', hox] at this; exact absurd this (by simp)
        have hy2 : y = x₂ := by
          rcases hy'' with h' | h'
          · have := o1; rw [← h', hoy] at this; exact absurd this (by simp)
          · exact h'
        show Molecule.gapAt L w (κ ∘ h.s.down) x y = pgap L w κ (h.s.pr x₁ x₂)
        rw [hx1, hy2]
        rfl
      · rw [cutSt_cls_other _ _ e1 e2] at hac
        obtain ⟨p, vis', hr, hn⟩ := hG.dg a ((Finset.mem_insert.1 ha').resolve_left e2) hac x y
          ((cut_atom_eq_iff h.s.M (v := v) (v₂ := v₂) (x₁ := x₁) (x₂ := x₂) x e1 e2).1 hx)
          ((cut_atom_eq_iff h.s.M (v := v) (v₂ := v₂) (x₁ := x₁) (x₂ := x₂) y e1 e2).1 hy) hox hoy
        exact ⟨p, vis', by simp [Function.update_of_ne e2, Function.update_of_ne e1, hr], hn⟩


variable {R : ℕ}

theorem HStep3.gap {h h' : HSt V D₀} (hs : HStep3 L γ η w κ h h') (hG : HGap L w κ h) (hI : Inv R h.s) :
    HGap L w κ h' := by
  cases hs with
  | cut v v₂ x₁ x₂ hc R' kp hR hkp hε hsg hsim hι h3 =>
    have hab : (if h.s.M.IsAlphaCut v v₂ x₁ x₂ then Cls.alpha R' kp else Cls.beta).IsAB := by
      split_ifs <;> trivial
    exact hG.cut_gen hc hε h3 (deg_le_four _ (hI.bounds v hc.1)) _ _
      (Cls.ne_eps_of_isAB hab) (Cls.ne_eps_of_isAB hab) _ _

theorem HStep4.gap {h h' : HSt V D₀} (hs : HStep4 L w κ h h') (hG : HGap L w κ h) (hI : Inv R h.s) :
    HGap L w κ h' := by
  cases hs with
  | cut v v₂ x₁ x₂ hc hε hβ hnz h3 =>
    exact hG.cut_gen hc hε h3 (deg_le_four _ (hI.bounds v hc.1)) _ _ (by simp) (by simp) _ _

theorem HStep1.gap {h h' : HSt V D₀} (hs : HStep1 L γ η w κ h h') (hG : HGap L w κ h) (hI : Inv R h.s) :
    HGap L w κ h' := by
  cases hs with
  | vine K R' kp hR hkp hu hl ga gb htwin hι₁ hι₂ hsg h3a h3b =>
    have hab := alphaOrBeta_isAB K.post.numComponents h.s.M.numComponents R' kp
    have hne := Cls.ne_eps_of_isAB hab
    have g1 := hG.cut_gen (na := Function.update h.anc K.fa (h.anc K.C.upper)) K.cut_a hu h3a (deg_le_four _ (hI.bounds _ K.cut_a.1)) _ _ hne hne
      h.alive (h.s.pr K.x₁ K.x₂ :: h.hist)
    have hlo : K.C.lower ∈ h.s.M.atoms := objectAtoms_sub K.C K.b_mem
    have hlne : K.C.lower ≠ K.C.upper := K.ab_ne.symm
    have hlfa : K.C.lower ≠ K.fa := fun e => K.fa_fresh (e ▸ hlo)
    have hcl : (h.s.cutSt K.C.upper K.fa K.x₁ K.x₂ (alphaOrBeta K.post.numComponents h.s.M.numComponents R' kp)
        (alphaOrBeta K.post.numComponents h.s.M.numComponents R' kp)).cls K.C.lower = .eps := by
      rw [cutSt_cls_other _ _ hlne hlfa]; exact hl
    have hD : (h.s.M.cut K.C.upper K.fa K.x₁ K.x₂).dartsAt K.C.lower = h.s.M.dartsAt K.C.lower :=
      cut_dartsAt_other h.s.M K.cut_a hlne hlfa
    have hdeg : (h.s.M.cut K.C.upper K.fa K.x₁ K.x₂).deg K.C.lower = h.s.M.deg K.C.lower :=
      congrArg Finset.card hD
    have h3 := h3b
    have h4 := deg_le_four _ (hI.bounds _ hlo)
    have g2 := g1.cut_gen (na := Function.update (Function.update h.anc K.fa (h.anc K.C.upper)) K.fb (h.anc K.C.lower)) K.cut_b hcl (by show 3 ≤ (h.s.M.cut _ _ _ _).deg _; omega)
      (by show (h.s.M.cut _ _ _ _).deg _ ≤ 4; omega) _ _ hne hne (h.s.pr K.x₁ K.x₂ :: h.alive)
      (h.s.pr K.y₁ K.y₂ :: h.s.pr K.x₁ K.x₂ :: h.hist)
    exact g2.delSt _ K.closed


section tri
variable {s : St.{u} V D₀} (T : TriData s.M)

/-- Dart sums over the triangle-removed state. -/
theorem triSt_sum (Q : Fin 2 → ℝ) (kp : Fin 2 → ℕ) (hcl : PClosed T.kept (triKeep s T)) {E : Type*}
    [AddCommMonoid E] {a : V} (ha : a ∈ (triSt s T Q kp hcl).M.atoms) (g : s.D → E) :
    ∑ x ∈ (triSt s T Q kp hcl).M.dartsAt a, g x.1.1 = ∑ x ∈ T.m3.dartsAt a, g x := by
  have ha' : a ∈ T.kept.atoms ∧ triKeep s T a := Finset.mem_filter.1 ha
  have hTP : T.TP a := (Finset.mem_filter.1 ha'.1).2
  have e1 := restrictP_sum T.kept (triKeep s T) hcl ha'.2 (fun y => g y.1)
  exact e1.trans (T.kept_sum hTP g)

theorem tri_f_gap {R : ℕ} {h : HSt V D₀} (hG : HGap L w κ h) (hI : Inv R h.s) (T : TriData h.s.M) (j : Fin 3)
    (hj : h.s.cls (T.t j) = .eps) (hdeg3 : 3 ≤ h.s.M.deg (T.t j)) {x y : h.s.D} (hx : T.m3.atom x = T.f j) (hy : T.m3.atom y = T.f j)
    (hox : h.s.M.out x = false) (hoy : h.s.M.out y = true) :
    Molecule.gapAt L w (κ ∘ h.s.down) x y = -Molecule.gapAt L w (κ ∘ h.s.down) (T.a j) (T.b j) := by
  have hxy : x ≠ y := fun e => by rw [e] at hox; rw [hox] at hoy; exact Bool.false_ne_true hoy
  have hxS : x ∈ T.m3.dartsAt (T.f j) := (mem_dartsAt _ _ _).2 hx
  have hyS : y ∈ T.m3.dartsAt (T.f j) := (mem_dartsAt _ _ _).2 hy
  have hdf := tri_deg_f T j
  have hdeg4 := deg_le_four _ (hI.bounds _ (T.t_mem j))
  have hcard : (T.m3.dartsAt (T.f j)).card + 2 = h.s.M.deg (T.t j) := hdf.symm
  have h4 : h.s.M.deg (T.t j) = 4 := by
    by_contra hne
    have : (T.m3.dartsAt (T.f j)).card = 1 := by omega
    have := Finset.one_lt_card.2 ⟨x, hxS, y, hyS, hxy⟩
    omega
  have hS : T.m3.dartsAt (T.f j) = {x, y} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro z hz; simp only [Finset.mem_insert, Finset.mem_singleton] at hz; rcases hz with rfl | rfl <;> assumption
    · rw [Finset.card_pair hxy]; omega
  have hsum := T.sum_t j (fun z => h.s.M.dartSign z • Molecule.kvec L w (κ ∘ h.s.down) z)
  rw [hG.chg _ (T.t_mem j) hj h4, hS, Finset.sum_pair hxy, dartSign_of_out_false h.s.M hox,
    dartSign_of_out_true h.s.M hoy, dartSign_of_out_false h.s.M (T.out_a j),
    dartSign_of_out_true h.s.M (T.out_b j)] at hsum
  have : Molecule.gapAt L w (κ ∘ h.s.down) x y = -Molecule.gapAt L w (κ ∘ h.s.down) (T.a j) (T.b j) := by
    unfold Molecule.gapAt
    simp only [neg_smul, one_smul] at hsum
    have h2 : (Molecule.kvec L w (κ ∘ h.s.down) x - Molecule.kvec L w (κ ∘ h.s.down) y) +
        (Molecule.kvec L w (κ ∘ h.s.down) (T.a j) - Molecule.kvec L w (κ ∘ h.s.down) (T.b j)) = 0 := by
      have e : (Molecule.kvec L w (κ ∘ h.s.down) x - Molecule.kvec L w (κ ∘ h.s.down) y) +
          (Molecule.kvec L w (κ ∘ h.s.down) (T.a j) - Molecule.kvec L w (κ ∘ h.s.down) (T.b j)) =
          -((-Molecule.kvec L w (κ ∘ h.s.down) x + Molecule.kvec L w (κ ∘ h.s.down) y) +
            (-Molecule.kvec L w (κ ∘ h.s.down) (T.a j) + Molecule.kvec L w (κ ∘ h.s.down) (T.b j))) := by abel
      rw [e, ← hsum]; simp
    exact eq_neg_of_add_eq_zero_left h2
  exact this

end tri

theorem HStep2.gap {R : ℕ} {h h' : HSt V D₀} (hs : HStep2 L γ η w κ h h') (hG : HGap L w κ h) (hI : Inv R h.s) :
    HGap L w κ h' := by
  cases hs with
  | tri T Q kp hQ hkp hsg hsim hcl hnz hι₀ hι₁ h3 =>
    have f01 : T.f 0 ≠ T.f 1 := T.f_ne (by decide)
    have f02 : T.f 0 ≠ T.f 2 := T.f_ne (by decide)
    have f12 : T.f 1 ≠ T.f 2 := T.f_ne (by decide)
    refine ⟨?_, ?_⟩
    · intro a ha hae h4'
      have ha' : a ∈ T.m3.atoms.filter T.TP := (Finset.mem_filter.1 ha).1
      have ha3 : a ∈ T.m3.atoms := (Finset.mem_filter.1 ha').1
      have hTP : T.TP a := (Finset.mem_filter.1 ha').2
      have hcl' : (triSt h.s T Q kp hcl).cls a = triCls h.s T Q kp a := rfl
      rw [TriData.m3_atoms] at ha3
      simp only [Finset.mem_insert] at ha3
      rcases ha3 with e | e | e | e
      · subst e; rw [hcl', triCls_f2] at hae; split_ifs at hae <;> simp at hae
      · subst e; rw [hcl', triCls_f1] at hae; split_ifs at hae <;> simp at hae
      · subst e; rw [hcl', triCls_f0] at hae; split_ifs at hae <;> simp at hae
      · have hf : ∀ j, a ≠ T.f j := fun j e' => T.f_fresh j (e' ▸ e)
        rw [hcl', triCls_other T Q kp hf] at hae
        have hdeg : h.s.M.deg a = 4 := by
          have h1 := triSt_sum T Q kp hcl ha (fun _ => (1 : ℕ))
          simp only [Finset.sum_const, smul_eq_mul, mul_one] at h1
          have h2 : (triSt h.s T Q kp hcl).M.deg a = 4 := h4'
          unfold Molecule.deg at h2 ⊢
          rw [← T.m3_dartsAt_other e hTP] ; omega
        have := hG.chg a e hae hdeg
        have e2 := triSt_sum T Q kp hcl ha (fun z => h.s.M.dartSign z • Molecule.kvec L w (κ ∘ h.s.down) z)
        rw [T.m3_dartsAt_other e hTP] at e2
        exact e2.trans this
    · intro a ha hac x y hx hy hox0 hoy0
      have hox : h.s.M.out x.1.1 = false := hox0
      have hoy : h.s.M.out y.1.1 = true := hoy0
      have ha' : a ∈ T.m3.atoms.filter T.TP := (Finset.mem_filter.1 ha).1
      have ha3 : a ∈ T.m3.atoms := (Finset.mem_filter.1 ha').1
      have hTP : T.TP a := (Finset.mem_filter.1 ha').2
      have hkeep : triKeep h.s T a := (Finset.mem_filter.1 ha).2
      have hcl' : (triSt h.s T Q kp hcl).cls a = triCls h.s T Q kp a := rfl
      have hxa : T.m3.atom x.1.1 = a := hx
      have hya : T.m3.atom y.1.1 = a := hy
      have fgap : ∀ j : Fin 3, a = T.f j → Molecule.gapAt L w (κ ∘ (triSt h.s T Q kp hcl).down) x y =
          -Molecule.gapAt L w (κ ∘ h.s.down) (T.a j) (T.b j) := by
        intro j hj
        have hε : h.s.cls (T.t j) = .eps := by
          by_contra hne
          exact hkeep j hne hj
        exact tri_f_gap hG hI T j hε (h3 j hε) (hj ▸ hxa) (hj ▸ hya) hox hoy
      rw [TriData.m3_atoms] at ha3
      simp only [Finset.mem_insert] at ha3
      rcases ha3 with e | e | e | e
      · refine ⟨h.s.pr (T.a 2) (T.b 2), h.triVis2 T,
          by rw [e]; simp, ?_⟩
        exact Or.inr (fgap 2 e)
      · refine ⟨h.s.pr (T.a 1) (T.b 1), h.triVis1 T,
          by rw [e]; simp [f12], ?_⟩
        exact Or.inr (fgap 1 e)
      · refine ⟨h.s.pr (T.a 0) (T.b 0), h.alive, by rw [e]; simp [f02, f01], ?_⟩
        exact Or.inr (fgap 0 e)
      · have hf : ∀ j, a ≠ T.f j := fun j e' => T.f_fresh j (e' ▸ e)
        rw [hcl', triCls_other T Q kp hf] at hac
        have hx0 : h.s.M.atom x.1.1 = a := by
          have : x.1.1 ∈ T.m3.dartsAt a := (mem_dartsAt _ _ _).2 hxa
          rw [T.m3_dartsAt_other e hTP] at this
          exact (mem_dartsAt _ _ _).1 this
        have hy0 : h.s.M.atom y.1.1 = a := by
          have : y.1.1 ∈ T.m3.dartsAt a := (mem_dartsAt _ _ _).2 hya
          rw [T.m3_dartsAt_other e hTP] at this
          exact (mem_dartsAt _ _ _).1 this
        obtain ⟨p, vis, hr, hn⟩ := hG.dg a e hac x.1.1 y.1.1 hx0 hy0 hox hoy
        exact ⟨p, vis, by simp [Function.update_of_ne (hf 2), Function.update_of_ne (hf 1),
          Function.update_of_ne (hf 0), hr], hn⟩

end WaveTurbulence.FinalCountG3
