/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3Ladder
public import WaveTurbulence.Foundations.FinalCount.G3Tri
/-! **FINALCOUNT-G3: the ladder context of a state** (`LCtx`): ancestors, dart relation, `deg ≥ 3 ⇒ ε`, degree `≤ 4`.
It is preserved by cuts and deletions, and gives the heredity `hPinh` of the cut estimates for every pair of states. -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}
variable {M₀ : Molecule V D₀}

/-- The ladder context of a state. -/
structure LCtx (M₀ : Molecule V D₀) (s : St.{u} V D₀) : Prop where
  anc : ∃ a, AncRel M₀ s a
  rel : DartRel M₀ s
  eps : ∀ b ∈ s.M.atoms, 3 ≤ s.M.deg b → s.cls b = .eps
  d4 : ∀ b ∈ s.M.atoms, s.M.deg b ≤ 4

theorem LCtx.cutSt {s : St.{u} V D₀} (hc : LCtx M₀ s) {v v₂ : V} {x₁ x₂ : s.D} (hcd : s.M.IsCutData v v₂ x₁ x₂)
    (c₁ c₂ : Cls) (h₁ : c₁ ≠ .eps) (h₂ : c₂ ≠ .eps) : LCtx M₀ (s.cutSt v v₂ x₁ x₂ c₁ c₂) := by
  obtain ⟨a, ha⟩ := hc.anc
  have hv : v ∈ s.M.atoms := hcd.1
  have hv₂ : v₂ ∉ s.M.atoms := hcd.2.1
  have hne : v₂ ≠ v := fun e => hv₂ (e ▸ hv)
  have hdv := hc.d4 v hv
  have hd2 := cut_deg_v₂ hcd
  have hdvv : (s.M.cut v v₂ x₁ x₂).deg v = 2 := cut_deg_v s.M hcd
  refine ⟨⟨_, ha.cutSt v v₂ x₁ x₂ c₁ c₂ h₁ h₂ hcd _ (fun b => rfl)⟩, hc.rel.cutSt v v₂ x₁ x₂ c₁ c₂ h₁ h₂ hv₂, ?_, ?_⟩
  · intro b hb h3
    change 3 ≤ (s.M.cut v v₂ x₁ x₂).deg b at h3
    have hb' : b ∈ insert v₂ s.M.atoms := hb
    by_cases e2 : b = v₂
    · subst e2; omega
    by_cases e1 : b = v
    · subst e1; exact absurd hdvv (by omega)
    have hbm : b ∈ s.M.atoms := (Finset.mem_insert.1 hb').resolve_left e2
    have := hc.eps b hbm (by rw [← cut_deg_other hcd e1 e2]; exact h3)
    show Function.update (Function.update s.cls v c₁) v₂ c₂ b = .eps
    rw [Function.update_of_ne e2, Function.update_of_ne e1]; exact this
  · intro b hb
    show (s.M.cut v v₂ x₁ x₂).deg b ≤ 4
    have hb' : b ∈ insert v₂ s.M.atoms := hb
    by_cases e2 : b = v₂
    · subst e2; omega
    by_cases e1 : b = v
    · subst e1; omega
    have hbm : b ∈ s.M.atoms := (Finset.mem_insert.1 hb').resolve_left e2
    rw [cut_deg_other hcd e1 e2]; exact hc.d4 b hbm

theorem LCtx.delSt {s : St.{u} V D₀} (hc : LCtx M₀ s) (P : V → Prop) [DecidablePred P] (hP : PClosed s.M P) :
    LCtx M₀ (s.delSt P hP) := by
  obtain ⟨a, ha⟩ := hc.anc
  refine ⟨⟨a, ha.delSt P hP⟩, hc.rel.delSt P hP, ?_, ?_⟩
  · intro b hb h3
    have hb' := Finset.mem_filter.1 hb
    have := hc.eps b hb'.1 (by rw [← restrictP_deg s.M P hP hb'.2]; exact h3)
    exact this
  · intro b hb
    have hb' := Finset.mem_filter.1 hb
    show (restrictP s.M P hP).deg b ≤ 4
    rw [restrictP_deg s.M P hP hb'.2]; exact hc.d4 b hb'.1

theorem LCtx.withCls {s : St.{u} V D₀} (hc : LCtx M₀ s) (c : V → Cls)
    (hcc : ∀ b ∈ s.M.atoms, (c b = .eps ↔ s.cls b = .eps)) : LCtx M₀ (s.withCls c) := by
  obtain ⟨a, ha⟩ := hc.anc
  refine ⟨⟨a, ha.withCls c hcc⟩, hc.rel.withCls c hcc, fun b hb h3 => ?_, hc.d4⟩
  exact (hcc b hb).2 (hc.eps b hb h3)

/-- Heredity of the ladder scale between two states. -/
theorem LCtx.hPinh {P : Finset V → ℝ} (hP : LadderHered M₀ P) {s s' : St.{u} V D₀} (hc : LCtx M₀ s)
    (hc' : LCtx M₀ s') :
    ∀ S' ∈ s'.M.maximalLadders, ∀ S ∈ s.M.maximalLadders, S' ⊆ S → P S' = P S := by
  obtain ⟨a, ha⟩ := hc.anc
  obtain ⟨a', ha'⟩ := hc'.anc
  exact hPinh_of_hered ha hc.rel hc.eps hP ha' hc'.rel hc'.eps

theorem LCtx.of_inv {R : ℕ} {s : St.{u} V D₀} (hI : Inv R s) (hA : ∃ a, AncRel M₀ s a) (hD : DartRel M₀ s) :
    LCtx M₀ s :=
  ⟨hA, hD, fun b hb h3 => by
    by_contra hne
    have := (hI.ab b hb hne).1
    omega, fun b hb => deg_le_four _ (hI.bounds b hb)⟩

end WaveTurbulence.FinalCountG3
