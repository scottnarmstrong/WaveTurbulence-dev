/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.GL1
public import WaveTurbulence.Foundations.FinalCount.G3URun
public import WaveTurbulence.Foundations.FinalCount.G3Ctx
/-! **G3-LOWDEG (R48), part 2**: the degree-`2` cut `HStepD3` (TARGET Remark after `defcut`: "after the cut `v₂` becomes an
isolated atom ... forming a single connected component by itself"; the isolated half is deleted) and its invariants. -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount
universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}
variable {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {R : ℕ} {M₀ : Molecule V D₀}

/-- The darts of a degree-`2` atom with two distinct darts `x₁, x₂` are exactly `x₁, x₂`. -/
theorem dart_of_deg_two {D : Type*} [Fintype D] [DecidableEq D] (M : Molecule V D) {v : V} {x₁ x₂ : D}
    (hd : M.deg v = 2) (h1 : M.atom x₁ = v) (h2 : M.atom x₂ = v) (hne : x₁ ≠ x₂) :
    ∀ x, M.atom x = v → x = x₁ ∨ x = x₂ := by
  intro x hx
  have hsub : ({x₁, x₂} : Finset D) ⊆ M.dartsAt v := by
    intro z hz
    simp only [Finset.mem_insert, Finset.mem_singleton] at hz
    rcases hz with rfl | rfl <;> simp [Molecule.dartsAt, *]
  have hcard : (M.dartsAt v).card ≤ ({x₁, x₂} : Finset D).card := by
    rw [Finset.card_pair hne]; exact hd.le
  have := Finset.eq_of_subset_of_card_le hsub hcard
  have hx' : x ∈ M.dartsAt v := by simp [Molecule.dartsAt, hx]
  rw [← this] at hx'
  simpa using hx'

/-- The state with history after the degree-`2` cut. -/
noncomputable def HSt.betaPost (h : HSt V D₀) (v : V) (x₁ x₂ : h.s.D) : HSt V D₀ :=
  ⟨h.s.betaSt v, h.s.pr x₁ x₂ :: h.hist, Function.update h.crec v (some (h.s.pr x₁ x₂, h.alive)), h.anc⟩

/-- **Step D3** (R48 item 3; TARGET Remark after `defcut`, Operations 3/4): the cut of an `ε`-atom `v` of degree `2` along both
of its bonds `(x₁, x₂)` (opposite directions, different bonds) with NONZERO gap (SG: Operation 3; LG: Operation 4, a `β`-cut);
the isolated half is deleted (equivalently `v` becomes a `β`-atom). `Desig` as in `HStep3C`. Performed before Step 2, so that
triangles never contain an `ε`-atom of degree `2` with nonzero pair gap. -/
inductive HStepD3 (C : CollData M₀) (L γ η : ℝ) (w : Mom d) (κ : D₀ → (Fin d → ℤ)) : HSt V D₀ → HSt V D₀ → Prop
  | cut (h : HSt V D₀) (v : V) (x₁ x₂ : h.s.D) (hv : v ∈ h.s.M.atoms) (hε : h.s.cls v = .eps)
      (hd : h.s.M.deg v = 2) (hx₁ : h.s.M.atom x₁ = v) (hx₂ : h.s.M.atom x₂ = v)
      (hne : x₂ ≠ h.s.M.mate x₁) (ho₁ : h.s.M.out x₁ = false) (ho₂ : h.s.M.out x₂ = true)
      (hnz : pgap L w κ (h.s.pr x₁ x₂) ≠ 0)
      (hdes : Desig C (h.anc v) (h.s.pr x₁ x₂)) :
      HStepD3 C L γ η w κ h (h.betaPost v x₁ x₂)

section inv
variable {h : HSt V D₀} {v : V} {x₁ x₂ : h.s.D}

theorem HInv.betaPost (hI : HInv L γ η w κ h) (hv : v ∈ h.s.M.atoms)
    (hnz : pgap L w κ (h.s.pr x₁ x₂) ≠ 0) :
    HInv L γ η w κ (h.betaPost v x₁ x₂) where
  mem := by
    intro a ha p vis hp
    show p ∈ h.s.pr x₁ x₂ :: h.hist
    by_cases e : a = v
    · subst e
      have : (Function.update h.crec a (some (h.s.pr x₁ x₂, h.alive))) a = some (h.s.pr x₁ x₂, h.alive) :=
        Function.update_self ..
      change Function.update h.crec a (some (h.s.pr x₁ x₂, h.alive)) a = some (p, vis) at hp
      rw [this] at hp
      simp only [Option.some.injEq, Prod.mk.injEq] at hp
      rw [← hp.1]; exact List.mem_cons_self
    · change Function.update h.crec v (some (h.s.pr x₁ x₂, h.alive)) a = some (p, vis) at hp
      rw [Function.update_of_ne e] at hp
      exact List.mem_cons_of_mem _ (hI.mem a ha p vis hp)
  cmp := by
    intro a ha a' ha' p vis p' vis' e e'
    change Function.update h.crec v (some (h.s.pr x₁ x₂, h.alive)) a = some (p, vis) at e
    change Function.update h.crec v (some (h.s.pr x₁ x₂, h.alive)) a' = some (p', vis') at e'
    have hal : ∀ b, b ∈ h.s.M.atoms → ∀ q vis, h.crec b = some (q, vis) → q ∈ h.alive :=
      fun b hb q vis hq => HSt.mem_alive.2 ⟨hI.mem b hb q vis hq, b, hb, vis, hq⟩
    by_cases e1 : a = v <;> by_cases e2 : a' = v
    · subst e1; subst e2
      rw [Function.update_self] at e e'
      simp only [Option.some.injEq, Prod.mk.injEq] at e e'
      left; rw [← e.1, ← e'.1]
    · subst e1
      rw [Function.update_self] at e
      rw [Function.update_of_ne e2] at e'
      simp only [Option.some.injEq, Prod.mk.injEq] at e
      right; right
      rw [← e.2]
      exact hal a' ha' p' vis' e'
    · subst e2
      rw [Function.update_self] at e'
      rw [Function.update_of_ne e1] at e
      simp only [Option.some.injEq, Prod.mk.injEq] at e'
      right; left
      rw [← e'.2]
      exact hal a ha p vis e
    · rw [Function.update_of_ne e1] at e
      rw [Function.update_of_ne e2] at e'
      exact hI.cmp a ha a' ha' p vis p' vis' e e'
  ok := by
    intro a ha
    change AtomOK L γ η w κ (Function.update h.s.cls v .beta a) (Function.update h.crec v (some (h.s.pr x₁ x₂, h.alive)) a)
    by_cases e : a = v
    · subst e
      rw [Function.update_self, Function.update_self]
      exact AtomOK.beta hnz
    · rw [Function.update_of_ne e, Function.update_of_ne e]
      exact hI.ok a ha

/-- The data of Step D3 at the state `h` (used by all invariant lemmas). -/
structure D3Data (h : HSt V D₀) (v : V) (x₁ x₂ : h.s.D) : Prop where
  hv : v ∈ h.s.M.atoms
  hε : h.s.cls v = .eps
  hd : h.s.M.deg v = 2
  hx₁ : h.s.M.atom x₁ = v
  hx₂ : h.s.M.atom x₂ = v
  hne : x₂ ≠ h.s.M.mate x₁
  ho₁ : h.s.M.out x₁ = false
  ho₂ : h.s.M.out x₂ = true

theorem D3Data.ne {h : HSt V D₀} {v : V} {x₁ x₂ : h.s.D} (hD : D3Data h v x₁ x₂) : x₁ ≠ x₂ := by
  intro e; have := hD.ho₁; rw [e, hD.ho₂] at this; exact absurd this (by simp)

theorem D3Data.darts {h : HSt V D₀} {v : V} {x₁ x₂ : h.s.D} (hD : D3Data h v x₁ x₂) :
    ∀ x, h.s.M.atom x = v → x = x₁ ∨ x = x₂ := dart_of_deg_two h.s.M hD.hd hD.hx₁ hD.hx₂ hD.ne

theorem HGap.betaPost (hG : HGap L w κ h) (hD : D3Data h v x₁ x₂) : HGap L w κ (h.betaPost v x₁ x₂) where
  chg := by
    intro a ha hae h4
    have hae' : Function.update h.s.cls v .beta a = .eps := hae
    by_cases e : a = v
    · rw [e, Function.update_self] at hae'; exact absurd hae' (by simp)
    · rw [Function.update_of_ne e] at hae'
      exact hG.chg a ha hae' h4
  dg := by
    intro a ha hac x y hx hy hox hoy
    have hcl : (h.betaPost v x₁ x₂).s.cls a = Function.update h.s.cls v .beta a := rfl
    by_cases e : a = v
    · subst e
      refine ⟨h.s.pr x₁ x₂, h.alive, by
        show Function.update h.crec a (some (h.s.pr x₁ x₂, h.alive)) a = _
        rw [Function.update_self], Or.inl ?_⟩
      have hx' : x = x₁ ∨ x = x₂ := hD.darts x hx
      have hy' : y = x₁ ∨ y = x₂ := hD.darts y hy
      have hox' : h.s.M.out x = false := hox
      have hoy' : h.s.M.out y = true := hoy
      have hxe : x = x₁ := by
        rcases hx' with h1 | h1
        · exact h1
        · rw [h1, hD.ho₂] at hox'; exact absurd hox' (by simp)
      have hye : y = x₂ := by
        rcases hy' with h1 | h1
        · rw [h1, hD.ho₁] at hoy'; exact absurd hoy' (by simp)
        · exact h1
      rw [hxe, hye]; rfl
    · rw [hcl, Function.update_of_ne e] at hac
      obtain ⟨p, vis, hp, hn⟩ := hG.dg a ha hac x y hx hy hox hoy
      exact ⟨p, vis, by
        show Function.update h.crec v (some (h.s.pr x₁ x₂, h.alive)) a = _
        rw [Function.update_of_ne e]; exact hp, hn⟩

theorem CompBeta.betaSt {s : St.{u} V D₀} (hC : CompBeta s) {v : V} (hε : s.cls v = .eps) :
    CompBeta (s.betaSt v) := by
  intro a ha hag
  have hcl : ∀ b, (s.betaSt v).cls b = Function.update s.cls v .beta b := fun b => rfl
  have hag' : s.cls a ≠ .ghost := by
    by_cases e : a = v
    · rw [e, hε]; simp
    · rw [hcl, Function.update_of_ne e] at hag; exact hag
  obtain ⟨b, hb, hab, hprop⟩ := hC a ha hag'
  refine ⟨b, hb, hab, ?_⟩
  by_cases e : b = v
  · left; rw [hcl, e, Function.update_self]
  · rcases hprop with hp | hp
    · left; rw [hcl, Function.update_of_ne e]; exact hp
    · right
      have : contrib (s.betaSt v) b = contrib s b := by
        unfold contrib
        rw [hcl, Function.update_of_ne e]; rfl
      rw [this]; exact hp

theorem outdeg_pos_of {D : Type*} [Fintype D] [DecidableEq D] (M : Molecule V D) {v : V} {x : D}
    (h1 : M.atom x = v) (h2 : M.out x = true) : 0 < M.outdeg v := by
  unfold Molecule.outdeg
  exact Finset.card_pos.2 ⟨x, by simp [Molecule.dartsAt, h1, h2]⟩

theorem indeg_pos_of {D : Type*} [Fintype D] [DecidableEq D] (M : Molecule V D) {v : V} {x : D}
    (h1 : M.atom x = v) (h2 : M.out x = false) : 0 < M.indeg v := by
  unfold Molecule.indeg
  exact Finset.card_pos.2 ⟨x, by simp [Molecule.dartsAt, h1, h2]⟩

theorem BalS.betaSt {s : St.{u} V D₀} (hB : BalS s) {v : V} {x₁ x₂ : s.D} (hd : s.M.deg v = 2)
    (h1 : s.M.atom x₁ = v) (h2 : s.M.atom x₂ = v) (ho₁ : s.M.out x₁ = false) (ho₂ : s.M.out x₂ = true) :
    BalS (s.betaSt v) := by
  refine ⟨hB.1, fun a ha he hda => ?_⟩
  by_cases e : a = v
  · subst e
    have a1 := outdeg_pos_of s.M h2 ho₂
    have a2 := indeg_pos_of s.M h1 ho₁
    have a3 := deg_eq s.M a
    exact ⟨by show s.M.outdeg a = 1; omega, by show s.M.indeg a = 1; omega⟩
  · have he' : s.cls a ≠ .eps := by
      have : (s.betaSt v).cls a = s.cls a := Function.update_of_ne e _ _
      rw [← this]; exact he
    exact hB.2 a ha he' hda

theorem DartRel.betaSt {s : St.{u} V D₀} (hR : DartRel M₀ s) (v : V) : DartRel M₀ (s.betaSt v) where
  mate := hR.mate
  out := hR.out
  eps := fun x hx => by
    have : s.cls ((s.betaSt v).M.atom x) = .eps := by
      by_contra hne
      apply absurd hx
      show Function.update s.cls v .beta _ ≠ .eps
      by_cases e : (s.betaSt v).M.atom x = v
      · rw [e, Function.update_self]; simp
      · rw [Function.update_of_ne e]; exact hne
    exact hR.eps x this

theorem AncRel.betaSt {s : St.{u} V D₀} {a : V → V} (hA : AncRel M₀ s a) (v : V) : AncRel M₀ (s.betaSt v) a where
  atom := hA.atom
  mem := hA.mem
  eps := fun b hb hcl => by
    have : s.cls b = .eps := by
      by_contra hne
      apply absurd hcl
      show Function.update s.cls v .beta b ≠ .eps
      by_cases e : b = v
      · rw [e, Function.update_self]; simp
      · rw [Function.update_of_ne e]; exact hne
    exact hA.eps b hb this
  uniq := fun c hc b hb hcl hca => by
    have : s.cls b = .eps := by
      by_contra hne
      apply absurd hcl
      show Function.update s.cls v .beta b ≠ .eps
      by_cases e : b = v
      · rw [e, Function.update_self]; simp
      · rw [Function.update_of_ne e]; exact hne
    exact hA.uniq c hc b hb this hca
  inj := hA.inj
  surj := fun b hb hcl z hz => by
    have : s.cls b = .eps := by
      by_contra hne
      apply absurd hcl
      show Function.update s.cls v .beta b ≠ .eps
      by_cases e : b = v
      · rw [e, Function.update_self]; simp
      · rw [Function.update_of_ne e]; exact hne
    exact hA.surj b hb this z hz

theorem DPInv.betaPost (hI : DPInv h) (hD : D3Data h v x₁ x₂) : DPInv (h.betaPost v x₁ x₂) where
  ok := by
    intro j hj p vis hp
    change Function.update h.crec v (some (h.s.pr x₁ x₂, h.alive)) j = some (p, vis) at hp
    by_cases e : j = v
    · subst e
      rw [Function.update_self] at hp
      simp only [Option.some.injEq, Prod.mk.injEq] at hp
      obtain ⟨rfl, -⟩ := hp
      left
      ext z
      simp only [DSet, Set.mem_setOf_eq, St.pr, Set.mem_insert_iff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨x, hx, hxz⟩
        rcases hD.darts x hx with h1 | h1
        · exact Or.inl (by rw [← hxz, h1]; rfl)
        · exact Or.inr (by rw [← hxz, h1]; rfl)
      · rintro (h1 | h1)
        · exact ⟨x₁, hD.hx₁, h1.symm⟩
        · exact ⟨x₂, hD.hx₂, h1.symm⟩
    · rw [Function.update_of_ne e] at hp
      exact hI.ok j hj p vis hp

theorem EpsLe.betaSt {s : St.{u} V D₀} (v : V) : EpsLe s (s.betaSt v) := by
  intro a ha b hb hca hcb
  have key : ∀ c, (s.betaSt v).cls c = .eps → s.cls c = .eps := by
    intro c hc
    by_cases e : c = v
    · rw [e] at hc; exact absurd hc (by simp [St.betaSt_cls])
    · simpa [St.betaSt_cls, Function.update_of_ne e] using hc
  exact ⟨⟨ha, key a hca⟩, ⟨hb, key b hcb⟩, le_rfl⟩

theorem AtomRelU.betaPost {Adm0 : (D₀ → (Fin d → ℤ)) → Prop} (hR : AtomRelU Adm0 L w h) (hD : D3Data h v x₁ x₂) :
    AtomRelU Adm0 L w (h.betaPost v x₁ x₂) := by
  intro a ha q vis hq
  change Function.update h.crec v (some (h.s.pr x₁ x₂, h.alive)) a = some (q, vis) at hq
  by_cases e : a = v
  · subst e
    rw [Function.update_self] at hq
    simp only [Option.some.injEq, Prod.mk.injEq] at hq
    obtain ⟨rfl, -⟩ := hq
    refine ⟨-1, Or.inr rfl, 0, fun k0 hk0 => ?_⟩
    show chargeAt h.s.M L w (k0 ∘ h.s.down) a = _
    unfold chargeAt
    have hset : h.s.M.dartsAt a = {x₁, x₂} := by
      ext x
      simp only [Molecule.dartsAt, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
        Finset.mem_singleton]
      constructor
      · intro hx; exact hD.darts x hx
      · rintro (rfl | rfl)
        · exact hD.hx₁
        · exact hD.hx₂
    rw [hset, Finset.sum_pair hD.ne]
    have s1 : h.s.M.dartSign x₁ = -1 := by simp [Molecule.dartSign, hD.ho₁]
    have s2 : h.s.M.dartSign x₂ = 1 := by simp [Molecule.dartSign, hD.ho₂]
    rw [s1, s2]
    show _ = (-1 : ℝ) • (Molecule.kvec L w (k0 ∘ h.s.down) x₁ - Molecule.kvec L w (k0 ∘ h.s.down) x₂) + 0
    simp only [neg_smul, one_smul, add_zero]; abel
  · rw [Function.update_of_ne e] at hq
    exact hR a ha q vis hq
end inv
end WaveTurbulence.FinalCountG3
