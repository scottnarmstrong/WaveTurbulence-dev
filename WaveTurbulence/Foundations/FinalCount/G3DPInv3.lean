/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.G3DPInv2
/-! **FINALCOUNT-G3: `DPInv` for Step 2 (the triangle removal) and for whole runs.** -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}
variable {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {M₀ : Molecule V D₀}

theorem DPInv.congr {s : St.{u} V D₀} {hist hist' : List (D₀ × D₀)} {c c' : V → Option ((D₀ × D₀) × List (D₀ × D₀))}
    {a a' : V → V} (hI : DPInv ⟨s, hist, c, a⟩) (h : ∀ j ∈ s.M.atoms, c' j = c j) : DPInv ⟨s, hist', c', a'⟩ where
  ok := fun j hj p vis hp => hI.ok j hj p vis (by show c j = _; rw [← h j hj]; exact hp)

theorem DPInv.withCls {s : St.{u} V D₀} {hist : List (D₀ × D₀)} {c : V → Option ((D₀ × D₀) × List (D₀ × D₀))}
    {a : V → V} (hI : DPInv ⟨s, hist, c, a⟩) (cl : V → Cls) : DPInv ⟨s.withCls cl, hist, c, a⟩ :=
  ⟨fun j hj p vis hp => hI.ok j hj p vis hp⟩

theorem HStep2.dp {h h' : HSt V D₀} (hs : HStep2 L γ η w κ h h') (hI : DPInv h)
    (hinj : Function.Injective h.s.down) : DPInv h' := by
  cases hs with
  | tri T Q kp hQ hkp hsg hsim hcl hnz hι₀ hι₁ h3 =>
    set p0 := h.s.pr (T.a 0) (T.b 0)
    set p1 := h.s.pr (T.a 1) (T.b 1)
    set p2 := h.s.pr (T.a 2) (T.b 2)
    have mk : ∀ (q : D₀ × D₀) (vis : List (D₀ × D₀)) (x y : h.s.D), q = h.s.pr x y →
        ∀ p vis', (some (q, vis) : Option ((D₀ × D₀) × List (D₀ × D₀))) = some (p, vis') → p = h.s.pr x y :=
      fun q vis x y hq p vis' e => by
        simp only [Option.some.injEq, Prod.mk.injEq] at e; rw [← e.1]; exact hq
    have g1 := hI.cut_gen hinj T.cd1 .beta (if h.s.cls (T.t 0) = .eps then .beta else .ghost)
      (h.s.pr (T.a 2) (T.b 2) :: h.s.pr (T.a 1) (T.b 1) :: h.s.pr (T.a 0) (T.b 0) :: h.hist)
      (na := h.anc) (some (p0, h.alive)) (some (p0, h.alive)) (mk _ _ _ _ rfl) (mk _ _ _ _ rfl)
    have g2 := g1.cut_gen (hinj) T.cd2 .beta (if h.s.cls (T.t 1) = .eps then .beta else .ghost)
      (h.s.pr (T.a 2) (T.b 2) :: h.s.pr (T.a 1) (T.b 1) :: h.s.pr (T.a 0) (T.b 0) :: h.hist)
      (na := h.anc) (some (p1, h.triVis1 T)) (some (p1, h.triVis1 T)) (mk _ _ _ _ rfl) (mk _ _ _ _ rfl)
    have g3 := g2.cut_gen (hinj) T.cd3 .beta (if h.s.cls (T.t 2) = .eps then .beta else .ghost)
      (h.s.pr (T.a 2) (T.b 2) :: h.s.pr (T.a 1) (T.b 1) :: h.s.pr (T.a 0) (T.b 0) :: h.hist)
      (na := h.anc) (some (p2, h.triVis2 T)) (some (p2, h.triVis2 T)) (mk _ _ _ _ rfl) (mk _ _ _ _ rfl)
    have g4 := g3.delSt T.TP T.pclosed
    have g5 := (g4.congr (hist' := h.s.pr (T.a 2) (T.b 2) :: h.s.pr (T.a 1) (T.b 1) :: h.s.pr (T.a 0) (T.b 0) :: h.hist)
      (c' := Function.update (Function.update (Function.update h.crec (T.f 0) (some (p0, h.alive)))
           (T.f 1) (some (p1, h.triVis1 T))) (T.f 2) (some (p2, h.triVis2 T)))
      (a' := Function.update (Function.update (Function.update h.anc (T.f 0) (h.anc (T.t 0))) (T.f 1) (h.anc (T.t 1)))
           (T.f 2) (h.anc (T.t 2))) (fun j hj => by
        have hj' := (Finset.mem_filter.1 hj).2
        have n0 : j ≠ T.t 0 := hj' 0
        have n1 : j ≠ T.t 1 := hj' 1
        have n2 : j ≠ T.t 2 := hj' 2
        simp only [Function.update_apply, n0, n1, n2, ite_false])).withCls (triCls h.s T Q kp)
    exact g5.delSt _ hcl

end WaveTurbulence.FinalCountG3
