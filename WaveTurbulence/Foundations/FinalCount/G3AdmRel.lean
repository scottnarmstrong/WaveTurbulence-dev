/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3Iota
public import WaveTurbulence.Foundations.FinalCount.G3CutDeg
/-! **FINALCOUNT-G3: the charge relation of the cut atoms is preserved** (excessprop1 (1), `ι`-glue).

Charges of a cut (`chargeAt_cut_*`), and the preservation of `AtomRelX` (the exempted form of `AtomRelU`) by one cut
with record, and by a deletion `delSt`. -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

universe u

section charge
variable {V : Type*} [DecidableEq V] {D : Type*} [Fintype D] [DecidableEq D] {d : ℕ}
variable (M : Molecule V D) {v v₂ : V} {x₁ x₂ : D}

theorem chargeAt_cut_other (hcd : M.IsCutData v v₂ x₁ x₂) {a : V} (h1 : a ≠ v) (h2 : a ≠ v₂) (L : ℝ) (w : Mom d)
    (κ : D → (Fin d → ℤ)) : chargeAt (M.cut v v₂ x₁ x₂) L w κ a = chargeAt M L w κ a := by
  unfold chargeAt
  rw [cut_dartsAt_other M hcd h1 h2]; rfl

theorem chargeAt_cut_v (hcd : M.IsCutData v v₂ x₁ x₂) (L : ℝ) (w : Mom d) (κ : D → (Fin d → ℤ)) :
    chargeAt (M.cut v v₂ x₁ x₂) L w κ v = -Molecule.gapAt L w κ x₁ x₂ := by
  unfold chargeAt Molecule.gapAt
  exact cut_c_v M hcd L w κ

theorem chargeAt_cut_v₂ (hcd : M.IsCutData v v₂ x₁ x₂) (L : ℝ) (w : Mom d) (κ : D → (Fin d → ℤ)) :
    chargeAt (M.cut v v₂ x₁ x₂) L w κ v₂ = chargeAt M L w κ v + Molecule.gapAt L w κ x₁ x₂ := by
  have h := cut_sum_split M hcd (fun x => M.dartSign x • Molecule.kvec L w κ x)
  have h1 := chargeAt_cut_v M hcd L w κ
  unfold chargeAt at h1 ⊢
  rw [h]
  have : ∑ x ∈ (M.cut v v₂ x₁ x₂).dartsAt v, M.dartSign x • Molecule.kvec L w κ x =
      -Molecule.gapAt L w κ x₁ x₂ := h1
  rw [this]; abel

end charge

variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}
variable {Adm0 : (D₀ → (Fin d → ℤ)) → Prop} {L : ℝ} {w : Mom d}

/-- `AtomRelU` except at the exempted atoms. -/
def AtomRelX (ex : V → Prop) (Adm0 : (D₀ → (Fin d → ℤ)) → Prop) (L : ℝ) (w : Mom d) (h : HSt V D₀) : Prop :=
  ∀ a ∈ h.s.M.atoms, ¬ ex a → ∀ q vis, h.crec a = some (q, vis) →
    ∃ sgn : ℝ, (sgn = 1 ∨ sgn = -1) ∧ ∃ c₀ : Mom d, ∀ k0, Adm0 k0 →
      chargeAt h.s.M L w (k0 ∘ h.s.down) a = sgn • pgap L w k0 q + c₀

theorem AtomRelU.toX {ex : V → Prop} {h : HSt V D₀} (hR : AtomRelU Adm0 L w h) : AtomRelX ex Adm0 L w h :=
  fun a ha _ => hR a ha

theorem AtomRelX.toU {h : HSt V D₀} (hR : AtomRelX (fun _ => False) Adm0 L w h) : AtomRelU Adm0 L w h :=
  fun a ha => hR a ha (fun h => h)

theorem AtomRelX.init (ex : V → Prop) (M₀ : Molecule V D₀) : AtomRelX ex Adm0 L w (HSt.init M₀) :=
  fun a _ _ q vis h => by simp [HSt.init] at h

theorem AtomRelX.mono {ex ex' : V → Prop} (hex : ∀ a, ex' a → ex a) {h : HSt V D₀} (hR : AtomRelX ex' Adm0 L w h) :
    AtomRelX ex Adm0 L w h := fun a ha hna => hR a ha (fun h' => hna (hex a h'))

/-- One cut with record; the fresh half `v₂` is exempted unless the charge of the cut atom is pinned. -/
theorem AtomRelX.cut {ex : V → Prop} {h : HSt V D₀} (hR : AtomRelX ex Adm0 L w h) {v v₂ : V} {x₁ x₂ : h.s.D}
    (hcd : h.s.M.IsCutData v v₂ x₁ x₂) (c₁ c₂ : Cls) (nh : List (D₀ × D₀)) (na : V → V)
    (vis : List (D₀ × D₀)) :
    AtomRelX (fun a => (ex a ∧ a ≠ v ∧ a ≠ v₂) ∨ (a = v₂ ∧ ¬ ∃ c : Mom d, ∀ k0, Adm0 k0 →
        chargeAt h.s.M L w (k0 ∘ h.s.down) v = c)) Adm0 L w
      ⟨h.s.cutSt v v₂ x₁ x₂ c₁ c₂, nh,
        Function.update (Function.update h.crec v (some (h.s.pr x₁ x₂, vis))) v₂ (some (h.s.pr x₁ x₂, vis)), na⟩ := by
  have hne : v₂ ≠ v := fun e => hcd.2.1 (e ▸ hcd.1)
  intro a ha hna q vis' hq
  have ha' : a ∈ insert v₂ h.s.M.atoms := ha
  by_cases e2 : a = v₂
  · rw [e2] at hq hna ⊢
    have hpin : ∃ c : Mom d, ∀ k0, Adm0 k0 → chargeAt h.s.M L w (k0 ∘ h.s.down) v = c := by
      by_contra hc; exact hna (Or.inr ⟨rfl, hc⟩)
    obtain ⟨c, hc⟩ := hpin
    simp only [Function.update_self] at hq
    obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj hq)
    refine ⟨1, Or.inl rfl, c, fun k0 hk0 => ?_⟩
    show chargeAt (h.s.M.cut v v₂ x₁ x₂) L w (k0 ∘ h.s.down) v₂ = _
    rw [chargeAt_cut_v₂ h.s.M hcd, hc k0 hk0]
    rw [one_smul, add_comm]; rfl
  · by_cases e1 : a = v
    · rw [e1] at hq ⊢
      simp only [Function.update_of_ne hne.symm, Function.update_self] at hq
      obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj hq)
      refine ⟨-1, Or.inr rfl, 0, fun k0 hk0 => ?_⟩
      show chargeAt (h.s.M.cut v v₂ x₁ x₂) L w (k0 ∘ h.s.down) v = _
      rw [chargeAt_cut_v h.s.M hcd]
      simp only [neg_smul, one_smul, add_zero]; rfl
    · have haM : a ∈ h.s.M.atoms := (Finset.mem_insert.1 ha').resolve_left e2
      simp only [Function.update_of_ne e2, Function.update_of_ne e1] at hq
      have hna' : ¬ ex a := fun h' => hna (Or.inl ⟨h', e1, e2⟩)
      obtain ⟨sgn, hs, c₀, hrel⟩ := hR a haM hna' q vis' hq
      refine ⟨sgn, hs, c₀, fun k0 hk0 => ?_⟩
      show chargeAt (h.s.M.cut v v₂ x₁ x₂) L w (k0 ∘ h.s.down) a = _
      rw [chargeAt_cut_other h.s.M hcd e1 e2]
      exact hrel k0 hk0

/-- Deletion of a union of components that contains no exempted atom. -/
theorem AtomRelX.del {ex : V → Prop} {h : HSt V D₀} (hR : AtomRelX ex Adm0 L w h) (P : V → Prop) [DecidablePred P]
    (hP : PClosed h.s.M P) (hex : ∀ a ∈ h.s.M.atoms, P a → ¬ ex a) (nh : List (D₀ × D₀)) (na : V → V) :
    AtomRelX (fun _ => False) Adm0 L w ⟨h.s.delSt P hP, nh, h.crec, na⟩ := by
  intro a ha _ q vis hq
  have ha' : a ∈ h.s.M.atoms.filter P := ha
  rw [Finset.mem_filter] at ha'
  obtain ⟨sgn, hs, c₀, hrel⟩ := hR a ha'.1 (hex a ha'.1 ha'.2) q vis hq
  refine ⟨sgn, hs, c₀, fun k0 hk0 => ?_⟩
  have e := restrictP_sum h.s.M P hP ha'.2 (fun y => h.s.M.dartSign y • Molecule.kvec L w (k0 ∘ h.s.down) y)
  show ∑ x ∈ (restrictP h.s.M P hP).dartsAt a, (restrictP h.s.M P hP).dartSign x •
      Molecule.kvec L w (fun x : PDart h.s.M P => k0 (h.s.down x.1)) x = _
  have e' : ∑ x ∈ (restrictP h.s.M P hP).dartsAt a, (restrictP h.s.M P hP).dartSign x •
      Molecule.kvec L w (fun x : PDart h.s.M P => k0 (h.s.down x.1)) x =
      ∑ x ∈ (restrictP h.s.M P hP).dartsAt a, h.s.M.dartSign x.1 • Molecule.kvec L w (k0 ∘ h.s.down) x.1 := rfl
  rw [e', e]
  exact hrel k0 hk0

/-- Deletion keeps the exemption (the atoms that remain are among those of the old state). -/
theorem AtomRelX.del' {ex : V → Prop} {h : HSt V D₀} (hR : AtomRelX ex Adm0 L w h) (P : V → Prop) [DecidablePred P]
    (hP : PClosed h.s.M P) (nh : List (D₀ × D₀)) (na : V → V) :
    AtomRelX ex Adm0 L w ⟨h.s.delSt P hP, nh, h.crec, na⟩ := by
  intro a ha hna q vis hq
  have ha' : a ∈ h.s.M.atoms.filter P := ha
  rw [Finset.mem_filter] at ha'
  obtain ⟨sgn, hs, c₀, hrel⟩ := hR a ha'.1 hna q vis hq
  refine ⟨sgn, hs, c₀, fun k0 hk0 => ?_⟩
  have e := restrictP_sum h.s.M P hP ha'.2 (fun y => h.s.M.dartSign y • Molecule.kvec L w (k0 ∘ h.s.down) y)
  have e' : chargeAt (restrictP h.s.M P hP) L w (fun x : PDart h.s.M P => k0 (h.s.down x.1)) a =
      ∑ x ∈ (restrictP h.s.M P hP).dartsAt a, h.s.M.dartSign x.1 • Molecule.kvec L w (k0 ∘ h.s.down) x.1 := rfl
  show chargeAt (restrictP h.s.M P hP) L w (fun x : PDart h.s.M P => k0 (h.s.down x.1)) a = _
  rw [e', e]
  exact hrel k0 hk0

theorem AtomRelX.withCls {ex : V → Prop} {h : HSt V D₀} (hR : AtomRelX ex Adm0 L w h) (c : V → Cls) :
    AtomRelX ex Adm0 L w ⟨h.s.withCls c, h.hist, h.crec, h.anc⟩ := hR

/-- Only the states `s` and the values of `crec` at the atoms that matter count. -/
theorem AtomRelX.crec_congr {ex : V → Prop} {h h' : HSt V D₀} (hR : AtomRelX ex Adm0 L w h) (hs : h'.s = h.s)
    (hc : ∀ a ∈ h.s.M.atoms, h'.crec a = h.crec a) : AtomRelX ex Adm0 L w h' := by
  obtain ⟨s', hist', crec', anc'⟩ := h'
  simp only at hs hc
  subst hs
  intro a ha hna q vis hq
  exact hR a ha hna q vis (by rw [← hc a ha]; exact hq)

end WaveTurbulence.FinalCountG3
