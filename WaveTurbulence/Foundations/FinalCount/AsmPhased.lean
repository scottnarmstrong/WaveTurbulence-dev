/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmPhase1d
public import WaveTurbulence.Foundations.FinalCount.AsmPhase2d
public import WaveTurbulence.Foundations.FinalCount.AsmPhase3d
public import WaveTurbulence.Foundations.FinalCount.AsmPhase4b
/-! **FINALCOUNT-ASSEMBLY: the phased reach relations.**  `Reach2/3/4` record the whole run `HRunNC` (phase boundaries and stop conditions) of a
decoration, with the designated-pair steps `HStep2C`, `HStep3C`.  Extension lemmas (`hext2`, `hext3`, `hext4`) for the cover theorems, and the
transitions between phases. -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.VineCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

theorem rtg_mono' {α : Type*} {r p : α → α → Prop} (hrp : ∀ a b, r a b → p a b) {a b : α}
    (h : Relation.ReflTransGen r a b) : Relation.ReflTransGen p a b := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hs ih => exact ih.tail (hrp _ _ hs)

section defs
variable {M₀ : Molecule V D₀} (C : CollData M₀) (Un : (D₀ → (Fin d → ℤ)) → Set (Object M₀)) (Fst : Set (Object M₀)) (L γ η : ℝ) (w : Mom d)

def Reach2 (κ : D₀ → (Fin d → ℤ)) (h : HSt V D₀) : Prop :=
  ∃ h₁, Reach1 C Un Fst L γ η w κ h₁ ∧ Stuck1 C L γ η w Un κ h₁ ∧ Relation.ReflTransGen (HStep2C C L γ η w κ) h₁ h

def Reach3 (κ : D₀ → (Fin d → ℤ)) (h : HSt V D₀) : Prop :=
  ∃ h₁ h₂, Reach1 C Un Fst L γ η w κ h₁ ∧ Stuck1 C L γ η w Un κ h₁ ∧ Relation.ReflTransGen (HStep2C C L γ η w κ) h₁ h₂ ∧
    NoEligibleTriangle C L γ η w κ h₂ ∧ Relation.ReflTransGen (HStep3C C L γ η w κ) h₂ h

def Reach4 (κ : D₀ → (Fin d → ℤ)) (h : HSt V D₀) : Prop :=
  ∃ h₁ h₂ h₃, Reach1 C Un Fst L γ η w κ h₁ ∧ Stuck1 C L γ η w Un κ h₁ ∧ Relation.ReflTransGen (HStep2C C L γ η w κ) h₁ h₂ ∧
    NoEligibleTriangle C L γ η w κ h₂ ∧ Relation.ReflTransGen (HStep3C C L γ η w κ) h₂ h₃ ∧
    NoSGLeft L γ η w κ (HSt.init M₀).s h₃.s ∧ Relation.ReflTransGen (HStep4 L w κ) h₃ h

variable {C Un Fst L γ η w}

theorem Reach2.ext {κ} {h h' : HSt V D₀} (hr : Reach2 C Un Fst L γ η w κ h) (hs : HStep2C C L γ η w κ h h') :
    Reach2 C Un Fst L γ η w κ h' := by
  obtain ⟨h₁, a, b, c⟩ := hr; exact ⟨h₁, a, b, c.tail hs⟩

theorem Reach3.ext {κ} {h h' : HSt V D₀} (hr : Reach3 C Un Fst L γ η w κ h) (hs : HStep3C C L γ η w κ h h') :
    Reach3 C Un Fst L γ η w κ h' := by
  obtain ⟨h₁, h₂, a, b, c, d', e⟩ := hr; exact ⟨h₁, h₂, a, b, c, d', e.tail hs⟩

theorem Reach4.ext {κ} {h h' : HSt V D₀} (hr : Reach4 C Un Fst L γ η w κ h) (hs : HStep4 L w κ h h') :
    Reach4 C Un Fst L γ η w κ h' := by
  obtain ⟨h₁, h₂, h₃, a, b, c, d', e, f, g⟩ := hr; exact ⟨h₁, h₂, h₃, a, b, c, d', e, f, g.tail hs⟩

theorem Reach1.to2 {κ} {h : HSt V D₀} (hr : Reach1 C Un Fst L γ η w κ h) (hs : Stuck1 C L γ η w Un κ h) :
    Reach2 C Un Fst L γ η w κ h := ⟨h, hr, hs, Relation.ReflTransGen.refl⟩

theorem Reach2.to3 {κ} {h : HSt V D₀} (hr : Reach2 C Un Fst L γ η w κ h) (hs : NoEligibleTriangle C L γ η w κ h) :
    Reach3 C Un Fst L γ η w κ h := by
  obtain ⟨h₁, a, b, c⟩ := hr; exact ⟨h₁, h, a, b, c, hs, Relation.ReflTransGen.refl⟩

theorem Reach3.to4 {κ} {h : HSt V D₀} (hr : Reach3 C Un Fst L γ η w κ h) (hs : NoSGLeft L γ η w κ (HSt.init M₀).s h.s) :
    Reach4 C Un Fst L γ η w κ h := by
  obtain ⟨h₁, h₂, a, b, c, d', e⟩ := hr; exact ⟨h₁, h₂, h, a, b, c, d', e, hs, Relation.ReflTransGen.refl⟩

theorem Reach2.toAny {κ} {h : HSt V D₀} (hr : Reach2 C Un Fst L γ η w κ h) :
    Relation.ReflTransGen (HAny L γ η w κ) (HSt.init M₀) h := by
  obtain ⟨h₁, a, -, c⟩ := hr
  exact (Reach1.toAny a).trans (rtg_mono' (p := HAny L γ η w κ) (fun x y hs => Or.inr (Or.inl hs.toHStep2)) c)

theorem Reach3.toAny {κ} {h : HSt V D₀} (hr : Reach3 C Un Fst L γ η w κ h) :
    Relation.ReflTransGen (HAny L γ η w κ) (HSt.init M₀) h := by
  obtain ⟨h₁, h₂, a, -, c, -, e⟩ := hr
  exact ((Reach1.toAny a).trans (rtg_mono' (p := HAny L γ η w κ) (fun x y hs => Or.inr (Or.inl hs.toHStep2)) c)).trans
    (rtg_mono' (p := HAny L γ η w κ) (fun x y hs => Or.inr (Or.inr (Or.inl hs.toHStep3))) e)

theorem Reach4.toAny {κ} {h : HSt V D₀} (hr : Reach4 C Un Fst L γ η w κ h) :
    Relation.ReflTransGen (HAny L γ η w κ) (HSt.init M₀) h := by
  obtain ⟨h₁, h₂, h₃, a, -, c, -, e, -, g⟩ := hr
  exact (((Reach1.toAny a).trans (rtg_mono' (p := HAny L γ η w κ) (fun x y hs => Or.inr (Or.inl hs.toHStep2)) c)).trans
    (rtg_mono' (p := HAny L γ η w κ) (fun x y hs => Or.inr (Or.inr (Or.inl hs.toHStep3))) e)).trans
    (rtg_mono' (p := HAny L γ η w κ) (fun x y hs => Or.inr (Or.inr (Or.inr hs))) g)

/-- The run `HRunNC` from `Reach4` at a state where Step 4 stops. -/
theorem Reach4.toRunNC {κ} {h : HSt V D₀} (hr : Reach4 C Un Fst L γ η w κ h) (hn : NoBetaCut L w κ h.s) :
    HRunNC L γ η w κ M₀ h C (Un κ) := by
  obtain ⟨h₁, h₂, h₃, a, ⟨b1, b2⟩, c, d', e, f, g⟩ := hr
  exact ⟨h₁, h₂, h₃, a.toC, b1, c, d', e, f, g, hn, b2⟩

end defs

section ext
variable {M₀ : Molecule V D₀} {C : CollData M₀} {Un : (D₀ → (Fin d → ℤ)) → Set (Object M₀)} {Fst : Set (Object M₀)} {L γ η : ℝ} {w : Mom d}

theorem hext4 [Infinite V] {A : Set (D₀ → (Fin d → ℤ))} {h : HSt V D₀} {v : V} {x₁ x₂ : h.s.D} (hn : Node4 h v x₁ x₂)
    (k : D₀ → (Fin d → ℤ)) (hk : k ∈ cls4 L w h A x₁ x₂) (hr : Reach4 C Un Fst L γ η w k h) :
    Reach4 C Un Fst L γ η w k (post4 h v x₁ x₂) :=
  hr.ext (UStep4.hstep (uStep4_node (L := L) (w := w) (A := A) hn) hk)

theorem hstep3C_node [Infinite V] {A : Set (D₀ → (Fin d → ℤ))} {h : HSt V D₀} {v : V} {x₁ x₂ : h.s.D} {z : ℤ} {b : Bool} {a : V}
    {sg : Bool} (hn : Node3 L γ η h v x₁ x₂ z b a sg) (hdes : Desig C (h.anc v) (h.s.pr x₁ x₂)) {κ : D₀ → (Fin d → ℤ)}
    (hk : κ ∈ cls3 L γ η w h A x₁ x₂ z b a sg) : HStep3C C L γ η w κ h (post3 h v x₁ x₂ z b) := by
  obtain ⟨hc, hε, h3, hR, ha, hb⟩ := hn
  obtain ⟨-, hsg, hsim, hb1, hb0⟩ := hk
  have hkp : (if b then 50 else 0) = 0 ∨ (if b then 50 else 0) = 50 := by cases b <;> simp
  have hI : (if b then 50 else 0) = 50 ↔ IotaHit L η w κ h.alive (h.s.pr x₁ x₂) ((2 : ℝ) ^ z) := by
    constructor
    · intro h50
      have hb' : b = true := by cases b <;> simp_all
      obtain ⟨q, vis, hcr, hq⟩ := hb hb'
      have := hb1 hb'
      have hq' : qOf h a (h.s.pr x₁ x₂) = q := by simp [qOf, hcr]
      rw [hq'] at this
      exact ⟨q, HSt.mem_alive.2 ⟨hq, ⟨a, ha, vis, hcr⟩⟩, if sg then 1 else -1, by cases sg <;> simp, this.1, this.2⟩
    · intro hit
      by_contra hne
      have hb' : b = false := by cases b <;> simp_all
      exact hb0 hb' hit
  exact HStep3C.cut h v (fresh h) x₁ x₂ hc ((2 : ℝ) ^ z) (if b then 50 else 0) hR hkp hε hsg hsim hI h3 hdes

theorem hext3 [Infinite V] {A : Set (D₀ → (Fin d → ℤ))} {h : HSt V D₀} {v : V} {x₁ x₂ : h.s.D} {z : ℤ} {b : Bool} {a : V}
    {sg : Bool} (hn : Node3 L γ η h v x₁ x₂ z b a sg) (hdes : Desig C (h.anc v) (h.s.pr x₁ x₂))
    (k : D₀ → (Fin d → ℤ)) (hk : k ∈ cls3 L γ η w h A x₁ x₂ z b a sg) (hr : Reach3 C Un Fst L γ η w k h) :
    Reach3 C Un Fst L γ η w k (post3 h v x₁ x₂ z b) :=
  hr.ext (hstep3C_node hn hdes hk)

theorem hext2 [Infinite V] {A : Set (D₀ → (Fin d → ℤ))} {h : HSt V D₀} {n : T2 h} (hn : Node2 L γ η h n)
    (hdes : ∀ j : Fin 3, Desig C (h.anc (n.1 j)) (h.s.pr (n.2.1 j) (n.2.2.1 j)))
    (k : D₀ → (Fin d → ℤ)) (hk : k ∈ cls2 L γ η w h A n) (hr : Reach2 C Un Fst L γ η w k h) :
    Reach2 C Un Fst L γ η w k (post2 L γ η h n) := by
  obtain ⟨hcl0, ht, ha, hb, hf, -⟩ := Classical.choose_spec hn
  change (triOf hn).t = _ at ht
  change (triOf hn).a = _ at ha
  change (triOf hn).b = _ at hb
  have hel : Eligible C L γ η w k h (triOf hn) := by
    refine ⟨fun j => ?_, ?_, fun j => ?_⟩
    · rw [ha, hb]; exact hk.2.1 j
    · rw [ha, hb]; exact hk.2.2.2.1
    · rw [ht, ha, hb]; exact hdes j
  have hs2 : HStep2 L γ η w k h (post2 L γ η h n) := by
    have := UStep2.hstep (uStep2_node (L := L) (γ := γ) (η := η) (w := w) (A := A) hn) hk
    exact this
  refine hr.ext (HStep2C.mk (triOf hn) hel hs2 ⟨Q2 n, kp2 n, triOf_cl hn, ?_⟩)
  rw [post2_eq hn]; rfl

end ext

end WaveTurbulence.FinalCountAsm
