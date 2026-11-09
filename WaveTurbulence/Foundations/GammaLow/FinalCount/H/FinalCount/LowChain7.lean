/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.LowChain7
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowChain4
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.LowChain7`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT LOW-CHAIN, LC-2 (3): Step 2/3 existence in the LOW run.**  `exists_step2C_L`/`exists_step3C_L` are `exists_step2C`/`exists_step3C`
with `InvL` and the hypothesis `3 ≤ deg` of the `ε` atoms (the REG proofs get it from `Flat`).  In the LOW run the degree bound follows from `NoD3`:
an `ε`-atom of degree `2` carrying a nonzero designated pair gap would still allow Step D3 (`noD3_transfer`, `deg_three_of_sg`,
`deg_three_of_eligible`). -/
@[expose] public section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
open scoped ENNReal
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3
open WaveTurbulence.LGSpine.SourceVine WaveTurbulence.VineCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}
variable {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {M₀ : Molecule V D₀} {R : ℕ}

/-- `NoD3` at an earlier state controls the degree-`2` `ε`-atoms of a later state (same `ε`-atom, same darts of `M₀`). -/
theorem noD3_transfer {C : CollData M₀} {h₂ h : HSt V D₀} (hA₂ : AncRel M₀ h₂.s h₂.anc) (hD₂ : DartRel M₀ h₂.s)
    (hA : AncRel M₀ h.s h.anc) (hD : DartRel M₀ h.s) (hE : EpsLe h₂.s h.s) (hN : NoD3 C L w κ h₂)
    {v : V} {x₁ x₂ : h.s.D} (hd : D3Data h v x₁ x₂) :
    pgap L w κ (h.s.pr x₁ x₂) = 0 ∨ ¬ Desig C (h.anc v) (h.s.pr x₁ x₂) := by
  obtain ⟨⟨hv₂, hε₂⟩, -, -⟩ := hE v hd.hv v hd.hv hd.hε hd.hε
  have e1 : M₀.atom (h.s.down x₁) = v := by rw [hD.eps x₁ (by rw [hd.hx₁]; exact hd.hε), hd.hx₁]
  have e2 : M₀.atom (h.s.down x₂) = v := by rw [hD.eps x₂ (by rw [hd.hx₂]; exact hd.hε), hd.hx₂]
  obtain ⟨y₁, hy₁d, hy₁a, hy₁o⟩ := eps_lift hA₂ hD₂ hv₂ hε₂ e1
  obtain ⟨y₂, hy₂d, hy₂a, hy₂o⟩ := eps_lift hA₂ hD₂ hv₂ hε₂ e2
  have hdeg : h₂.s.M.deg v = 2 := by
    rw [deg_eps_eq hA₂ hv₂ hε₂, ← deg_eps_eq hA hd.hv hd.hε]; exact hd.hd
  have hD3 : D3Data h₂ v y₁ y₂ :=
    { hv := hv₂, hε := hε₂, hd := hdeg, hx₁ := hy₁a, hx₂ := hy₂a
      hne := by
        intro e
        apply hd.hne
        apply hA.inj
        rw [← hy₂d, e, ← hD₂.mate, hy₁d, hD.mate]
      ho₁ := by rw [hy₁o, hD.out]; exact hd.ho₁
      ho₂ := by rw [hy₂o, hD.out]; exact hd.ho₂ }
  have key := hN v y₁ y₂ hD3
  have hpr : h₂.s.pr y₁ y₂ = h.s.pr x₁ x₂ := by simp [St.pr, hy₁d, hy₂d]
  have hanc : h₂.anc v = h.anc v := by rw [hA₂.eps v hv₂ hε₂, hA.eps v hd.hv hd.hε]
  rw [hpr, hanc] at key
  exact key

/-- A pair of darts at an SG `ε`-atom of `M₀` that is designated at a hinge. -/
theorem pair_of_sg {C : CollData M₀} (obl : SubproOblG C L γ η w κ) {v : V} (hSG : SGat M₀ L γ η w κ v) :
    ∃ x y : D₀, M₀.atom x = v ∧ M₀.atom y = v ∧ y ≠ M₀.mate x ∧ M₀.out x = false ∧ M₀.out y = true ∧
      Molecule.gapKind L γ η (Molecule.gapAt L w κ x y) = .SG ∧ Desig C v (x, y) := by
  by_cases hh : v ∈ C.hinges
  · obtain ⟨f, s, x, y, h1, h2, hx, hy, hne, ho1, ho2, hsg, hset⟩ := hinge_oriented obl hh
    exact ⟨x, y, hx, hy, hne, ho1, ho2, hsg, fun _ => ⟨f, s, h1, h2, Or.inl hset⟩⟩
  · obtain ⟨x, y, hx, hy, ho1, ho2, hne, hsg⟩ := hSG
    exact ⟨x, y, hx, hy, hne, ho1, ho2, hsg, fun h' => absurd h' hh⟩

/-- **The degree of an SG `ε`-atom after Step D3 is complete.** -/
theorem deg_three_of_sg {C : CollData M₀} (obl : SubproOblG C L γ η w κ) {h₂ h : HSt V D₀}
    (hA₂ : AncRel M₀ h₂.s h₂.anc) (hD₂ : DartRel M₀ h₂.s) (hA : AncRel M₀ h.s h.anc) (hD : DartRel M₀ h.s)
    (hE : EpsLe h₂.s h.s) (hN : NoD3 C L w κ h₂) {v : V} (hv : v ∈ h.s.M.atoms) (hε : h.s.cls v = .eps)
    (hSG : SGat M₀ L γ η w κ v) : 3 ≤ h.s.M.deg v := by
  by_contra hlt
  obtain ⟨x, y, hx, hy, hne, hxo, hyo, hsg, hdes⟩ := pair_of_sg obl hSG
  obtain ⟨x₁, hx₁d, hx₁a, hx₁o⟩ := eps_lift hA hD hv hε hx
  obtain ⟨x₂, hx₂d, hx₂a, hx₂o⟩ := eps_lift hA hD hv hε hy
  have hne' : x₂ ≠ h.s.M.mate x₁ := by
    intro e
    apply hne
    rw [← hx₂d, e, ← hD.mate, hx₁d]
  have hne12 : x₁ ≠ x₂ := by
    intro e; rw [e] at hx₁o; rw [hxo] at hx₁o; rw [hx₂o, hyo] at hx₁o; exact absurd hx₁o (by simp)
  have h2 := two_le_deg hx₁a hx₂a hne12
  have hD3 : D3Data h v x₁ x₂ :=
    { hv := hv, hε := hε, hd := by omega, hx₁ := hx₁a, hx₂ := hx₂a, hne := hne'
      ho₁ := by rw [hx₁o, hxo], ho₂ := by rw [hx₂o, hyo] }
  have key := noD3_transfer hA₂ hD₂ hA hD hE hN hD3
  have hpr : h.s.pr x₁ x₂ = (x, y) := by simp [St.pr, hx₁d, hx₂d]
  have hnz : pgap L w κ (h.s.pr x₁ x₂) ≠ 0 := by
    rw [hpr]; exact gap_ne_zero_of_SG hsg
  rw [hA.eps v hv hε, hpr] at key
  rcases key with k | k
  · exact hnz (by rw [hpr]; exact k)
  · exact k hdes

/-- **The degree of the `ε`-atoms of an eligible triangle after Step D3 is complete.** -/
theorem deg_three_of_eligible {C : CollData M₀} {h₂ h : HSt V D₀}
    (hA₂ : AncRel M₀ h₂.s h₂.anc) (hD₂ : DartRel M₀ h₂.s) (hA : AncRel M₀ h.s h.anc) (hD : DartRel M₀ h.s)
    (hE : EpsLe h₂.s h.s) (hN : NoD3 C L w κ h₂) (T : TriData h.s.M) (hel : Eligible C L γ η w κ h T) :
    ∀ j, h.s.cls (T.t j) = .eps → 3 ≤ h.s.M.deg (T.t j) := by
  intro j hε
  by_contra hlt
  have hne12 : T.a j ≠ T.b j := fun e => by
    have := T.out_a j; rw [e, T.out_b j] at this; exact absurd this (by simp)
  have h2 := two_le_deg (T.atom_a j) (T.atom_b j) hne12
  have hD3 : D3Data h (T.t j) (T.a j) (T.b j) :=
    { hv := T.t_mem j, hε := hε, hd := by omega, hx₁ := T.atom_a j, hx₂ := T.atom_b j
      hne := (T.b_ne_mate_a j), ho₁ := T.out_a j, ho₂ := T.out_b j }
  have key := noD3_transfer hA₂ hD₂ hA hD hE hN hD3
  have hnz : pgap L w κ (h.s.pr (T.a j) (T.b j)) ≠ 0 := by
    fin_cases j
    · exact gap_ne_zero_of_SG (hel.1 0)
    · exact gap_ne_zero_of_SG (hel.1 1)
    · exact hel.2.1
  rcases key with k | k
  · exact hnz k
  · exact k (hel.2.2 j)

/-- **Step-2 existence in the LOW run**: an eligible triangle whose `ε`-atoms have degree `≥ 3` has a step. -/
theorem exists_step2C_L {C : CollData M₀} (hL : 0 < L) (h2 : 2 / L ≤ L ^ (-γ + η)) {h : HSt V D₀}
    (hI : InvL M₀ R L γ η w κ h) (T : TriData h.s.M) (hel : Eligible C L γ η w κ h T)
    (h3 : ∀ j, h.s.cls (T.t j) = .eps → 3 ≤ h.s.M.deg (T.t j)) :
    ∃ h', HStep2C C L γ η w κ h h' := by
  have hInv := hI.good.1
  have hcl : PClosed T.kept (triKeep h.s T) := tri_keep_closed hInv T
  have hlab : ∀ j : Fin 2, ∃ R', IsLabel L γ η R' ∧
      GapSim L w (κ ∘ h.s.down) (T.a j.castSucc) (T.b j.castSucc) R' :=
    fun j => exists_label_of_SG w (κ ∘ h.s.down) _ _ hL h2 (hel.1 j)
  choose Q hQ hsim using hlab
  let kp0 : ℕ := if IotaHit L η w κ h.alive (h.s.pr (T.a 0) (T.b 0)) (Q 0) then 50 else 0
  let kp1 : ℕ := if IotaHit L η w κ (h.triVis1 T) (h.s.pr (T.a 1) (T.b 1)) (Q 1)
    then 50 else 0
  let kp : Fin 2 → ℕ := ![kp0, kp1]
  have hkp : ∀ j : Fin 2, kp j = 0 ∨ kp j = 50 := by
    intro j; fin_cases j
    · show kp0 = 0 ∨ kp0 = 50
      by_cases hh : IotaHit L η w κ h.alive (h.s.pr (T.a 0) (T.b 0)) (Q 0) <;> simp [kp0, hh]
    · show kp1 = 0 ∨ kp1 = 50
      by_cases hh : IotaHit L η w κ (h.triVis1 T) (h.s.pr (T.a 1) (T.b 1)) (Q 1) <;>
        simp [kp1, hh]
  have hι₀ : kp 0 = 50 ↔ IotaHit L η w κ h.alive (h.s.pr (T.a 0) (T.b 0)) (Q 0) := by
    show kp0 = 50 ↔ _
    by_cases hh : IotaHit L η w κ h.alive (h.s.pr (T.a 0) (T.b 0)) (Q 0) <;> simp [kp0, hh]
  have hι₁ : kp 1 = 50 ↔
      IotaHit L η w κ (h.triVis1 T) (h.s.pr (T.a 1) (T.b 1)) (Q 1) := by
    show kp1 = 50 ↔ _
    by_cases hh : IotaHit L η w κ (h.triVis1 T) (h.s.pr (T.a 1) (T.b 1)) (Q 1) <;>
      simp [kp1, hh]
  have hs := HStep2.tri h T Q kp hQ hkp hel.1 hsim hcl hel.2.1 (fun _ => hι₀) (fun _ => hι₁) h3
  exact ⟨_, HStep2C.mk T hel hs ⟨Q, kp, hcl, rfl⟩⟩

/-- **Step-3 existence in the LOW run** (an `ε` SG atom of degree `≥ 3`). -/
theorem exists_step3C_L [Infinite V] {C : CollData M₀} (obl : SubproOblG C L γ η w κ) (hL : 0 < L)
    (h2 : 2 / L ≤ L ^ (-γ + η)) {h : HSt V D₀} (hI : InvL M₀ R L γ η w κ h) (hA : AncRel M₀ h.s h.anc)
    {v : V} (hv : v ∈ h.s.M.atoms) (hε : h.s.cls v = .eps) (hSG : SGat M₀ L γ η w κ v)
    (h3 : 3 ≤ h.s.M.deg v) : ∃ h', HStep3C C L γ η w κ h h' := by
  have hD : DartRel M₀ h.s := hI.rel
  have hanc : h.anc v = v := hA.eps v hv hε
  obtain ⟨v₂, hv₂⟩ := Infinite.exists_notMem_finset h.s.M.atoms
  obtain ⟨x, y, hxv, hyv, hne, hxo, hyo, hsgxy, hdes⟩ : ∃ x y : D₀, M₀.atom x = v ∧ M₀.atom y = v ∧ y ≠ M₀.mate x ∧
      M₀.out x = false ∧ M₀.out y = true ∧ Molecule.gapKind L γ η (Molecule.gapAt L w κ x y) = .SG ∧
      (v ∈ C.hinges → ∃ f s, C.first v = some f ∧ C.second v = some s ∧ ({x, y} : Set D₀) = {f, s}) := by
    by_cases hh : v ∈ C.hinges
    · obtain ⟨f, s, x, y, h1, h2, hx, hy, hne, ho1, ho2, hsg, hset⟩ := hinge_oriented obl hh
      exact ⟨x, y, hx, hy, hne, ho1, ho2, hsg, fun _ => ⟨f, s, h1, h2, hset⟩⟩
    · obtain ⟨x, y, hx, hy, ho1, ho2, hne, hsg⟩ := hSG
      exact ⟨x, y, hx, hy, hne, ho1, ho2, hsg, fun h' => absurd h' hh⟩
  obtain ⟨x₁, hx₁d, hx₁a, hx₁o⟩ := eps_lift hA hD hv hε hxv
  obtain ⟨x₂, hx₂d, hx₂a, hx₂o⟩ := eps_lift hA hD hv hε hyv
  have hne' : x₂ ≠ h.s.M.mate x₁ := by
    intro e
    apply hne
    rw [← hx₂d, e, ← hD.mate, hx₁d]
  have hc : h.s.M.IsCutData v v₂ x₁ x₂ := ⟨hv, hv₂, hx₁a, hx₂a, hne', by simp [hx₁o, hxo], by simp [hx₂o, hyo]⟩
  have hsg' : Molecule.gapKind L γ η (Molecule.gapAt L w (κ ∘ h.s.down) x₁ x₂) = .SG := by
    have : Molecule.gapAt L w (κ ∘ h.s.down) x₁ x₂ = Molecule.gapAt L w κ x y := by
      unfold Molecule.gapAt Molecule.kvec; simp [hx₁d, hx₂d]
    rw [this]; exact hsgxy
  obtain ⟨R', hR', hsim⟩ := exists_label_of_SG w (κ ∘ h.s.down) x₁ x₂ hL h2 hsg'
  by_cases hIo : IotaHit L η w κ h.alive (h.s.pr x₁ x₂) R'
  · refine ⟨_, HStep3C.cut h v v₂ x₁ x₂ hc R' 50 hR' (Or.inr rfl) hε hsg' hsim (by simp [hIo]) h3 ?_⟩
    intro hh
    rw [hanc] at hh
    obtain ⟨f, s, h1, h2', hset⟩ := hdes hh
    rw [hanc]
    refine ⟨f, s, h1, h2', Or.inl ?_⟩
    simpa [St.pr, hx₁d, hx₂d] using hset
  · refine ⟨_, HStep3C.cut h v v₂ x₁ x₂ hc R' 0 hR' (Or.inl rfl) hε hsg' hsim (by simp [hIo]) h3 ?_⟩
    intro hh
    rw [hanc] at hh
    obtain ⟨f, s, h1, h2', hset⟩ := hdes hh
    rw [hanc]
    refine ⟨f, s, h1, h2', Or.inl ?_⟩
    simpa [St.pr, hx₁d, hx₂d] using hset

end WaveTurbulence.GammaLow.FinalCount.H
