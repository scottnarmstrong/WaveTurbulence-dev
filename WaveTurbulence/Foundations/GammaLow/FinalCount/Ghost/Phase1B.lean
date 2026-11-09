/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Ghost.Phase1A
public import WaveTurbulence.Foundations.GammaLow.FinalCount.Ghost.Closed
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmP1Basic
public import WaveTurbulence.Foundations.FinalCount.G3CutDeg
/-! **Ghost assembly, Phase 1 (B): the twins of an Operation-1 step are locked** (M1-R2 Lemma 2.1; design:
`CHAIN-DESIGN.md`).

After `h' = h.vinePostL K R kp`, if the fresh joints `fa`, `fb` both have degree `2` and are adjacent (a hyper object:
the added bond), the removed object `S = K.C.atoms` has exactly two boundary darts in `h.s.M`, the outer darts `p` at the
upper and `q` at the lower joint. Its atoms are `ε` of degree `4`, hence of charge `0` (`ChgS`), and the flux through
the boundary vanishes: an outside atom holding `mate p`, `mate q` sees gap `0` (`vine_twin_locked`). -/
@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.GammaLow.FinalCount.Ghost
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.FinalCountAsm

universe u
variable {V : Type*} [DecidableEq V] {d : ℕ}

/-- **Flux, charge form.** A set `S` of atoms of charge `0` (for a mate-symmetric labelling) whose only boundary darts
are `p ≠ q` of opposite orientations: the two labels agree. -/
theorem boundary_kvec_eq {D : Type*} [Fintype D] [DecidableEq D] (M : Molecule V D) {L : ℝ} {w : Mom d}
    {κ : D → (Fin d → ℤ)} (hk : ∀ x, κ (M.mate x) = κ x) (S : Finset V)
    (hc : ∀ a ∈ S, ∑ x ∈ M.dartsAt a, M.dartSign x • Molecule.kvec L w κ x = 0) (p q : D)
    (hpq : p ≠ q) (hp : M.atom p ∈ S ∧ M.atom (M.mate p) ∉ S) (hq : M.atom q ∈ S ∧ M.atom (M.mate q) ∉ S)
    (hbd : ∀ x, M.atom x ∈ S → M.atom (M.mate x) ∉ S → x = p ∨ x = q) (hdir : M.out p ≠ M.out q) :
    Molecule.kvec L w κ p = Molecule.kvec L w κ q := by
  have hflux := sum_darts_boundary M S (fun x => M.dartSign x • Molecule.kvec L w κ x) (by
    intro x
    have h1 : Molecule.kvec L w κ (M.mate x) = Molecule.kvec L w κ x := by
      unfold Molecule.kvec; rw [hk x]
    simp only [Molecule.dartSign, M.out_mate, h1]
    cases M.out x <;> simp)
  have hzero : ∑ a ∈ S, ∑ x ∈ M.dartsAt a, M.dartSign x • Molecule.kvec L w κ x = 0 :=
    Finset.sum_eq_zero fun a ha => hc a ha
  have hbset : Finset.univ.filter (fun x => M.atom x ∈ S ∧ M.atom (M.mate x) ∉ S) = {p, q} := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨h1, h2⟩; exact hbd x h1 h2
    · rintro (rfl | rfl)
      · exact hp
      · exact hq
  rw [hzero, hbset, Finset.sum_pair hpq] at hflux
  have hsq : M.dartSign q = -M.dartSign p := by
    unfold Molecule.dartSign
    rcases hP : M.out p <;> rcases hQ : M.out q <;> simp_all
  rw [hsq, neg_smul] at hflux
  have hs0 : M.dartSign p ≠ 0 := by unfold Molecule.dartSign; split_ifs <;> norm_num
  have h2 : M.dartSign p • (Molecule.kvec L w κ p - Molecule.kvec L w κ q) = 0 := by
    rw [smul_sub, sub_eq_add_neg]; exact hflux.symm
  rcases smul_eq_zero.1 h2 with h | h
  · exact absurd h hs0
  · exact sub_eq_zero.1 h

variable {D₀ : Type u} [Fintype D₀] [DecidableEq D₀]

section vine
variable (h : HSt V D₀) (K : Step1.VineCut Src.γL h.s.M) (R : ℝ) (kp : ℕ)

theorem fa_notMem_C : K.fa ∉ K.C.atoms := fun hm => fa_notMem h K (Step1.objectAtoms_sub K.C hm)
theorem fb_notMem_C : K.fb ∉ K.C.atoms := fun hm => fb_notMem h K (Step1.objectAtoms_sub K.C hm)

/-- A dart of the cut molecule at `fa` was at the upper joint. -/
theorem atom_of_cut_fa {y : h.s.D} (hy : K.cutMol.atom y = K.fa) : h.s.M.atom y = K.C.upper := by
  have e0 : K.cutMol.atom y = (h.s.M.cut K.C.upper K.fa K.x₁ K.x₂).atom y :=
    cut_atom_of_ne y (by change K.cutMol.atom y ≠ K.fb; rw [hy]; exact fa_ne_fb h K)
  have e1 : (h.s.M.cut K.C.upper K.fa K.x₁ K.x₂).atom y = K.fa := e0.symm.trans hy
  exact cut_atom_eq_new y (fa_notMem h K) e1

/-- A dart of the cut molecule at `fb` was at the lower joint. -/
theorem atom_of_cut_fb {y : h.s.D} (hy : K.cutMol.atom y = K.fb) : h.s.M.atom y = K.C.lower := by
  have e1 : (h.s.M.cut K.C.upper K.fa K.x₁ K.x₂).atom y = K.C.lower := cut_atom_eq_new y K.cut_b.2.1 hy
  rw [← e1]
  exact (cut_atom_of_ne y (by rw [e1]; exact fa_ne_atom h K (lower_mem h K))).symm

/-- A dart of the cut molecule not at `fa`, `fb` sits where it sat. -/
theorem atom_cut_of_mem_C {y : h.s.D} (hy : h.s.M.atom y ∈ K.C.atoms) (hy' : K.cutMol.atom y ∉ K.C.atoms) :
    K.cutMol.atom y = K.fa ∨ K.cutMol.atom y = K.fb := by
  by_contra hn
  push Not at hn
  exact hy' (by rw [vine_atom_of_ne h K y hn.1 hn.2]; exact hy)

theorem deg_upper_of_fa (hfa : K.cutMol.deg K.fa = 2) : h.s.M.deg K.C.upper = 4 := by
  have e2 : K.cutMol.deg K.fa = (h.s.M.cut K.C.upper K.fa K.x₁ K.x₂).deg K.fa :=
    cut_deg_other K.cut_b (fa_ne_atom h K (lower_mem h K)).symm (fa_ne_fb h K)
  have e3 := cut_deg_v₂ K.cut_a
  omega

theorem deg_lower_of_fb (hfb : K.cutMol.deg K.fb = 2) : h.s.M.deg K.C.lower = 4 := by
  have e3 := cut_deg_v₂ K.cut_b
  have e2 : (h.s.M.cut K.C.upper K.fa K.x₁ K.x₂).deg K.C.lower = h.s.M.deg K.C.lower :=
    cut_deg_other K.cut_a K.ab_ne.symm (fa_ne_atom h K (lower_mem h K))
  have e1' : ((h.s.M.cut K.C.upper K.fa K.x₁ K.x₂).cut K.C.lower K.fb K.y₁ K.y₂).deg K.fb = 2 := hfb
  omega

/-- Two darts of a degree-`2` atom, distinct: every dart of the atom is one of them. -/
theorem dart_eq_of_deg2 {D : Type*} [Fintype D] [DecidableEq D] (M : Molecule V D) {v : V} (hv : M.deg v = 2)
    {e₁ e₂ x : D} (h1 : M.atom e₁ = v) (h2 : M.atom e₂ = v) (hne : e₁ ≠ e₂) (hx : M.atom x = v) :
    x = e₁ ∨ x = e₂ := by
  have hsub : ({e₁, e₂} : Finset D) ⊆ M.dartsAt v := by
    intro y hy
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy
    simp only [Molecule.dartsAt, Finset.mem_filter, Finset.mem_univ, true_and]
    rcases hy with rfl | rfl
    · exact h1
    · exact h2
  have hcard : (M.dartsAt v).card ≤ ({e₁, e₂} : Finset D).card := by
    rw [Finset.card_pair hne]; unfold Molecule.deg at hv; omega
  have heq := Finset.eq_of_subset_of_card_le hsub hcard
  have hxm : x ∈ M.dartsAt v := by simp [Molecule.dartsAt, hx]
  rw [← heq] at hxm
  simpa using hxm

/-- **The twin gap vanishes** (the dart-level core of `vine_twin_locked`): darts `a₁`, `b₁` of opposite directions at
a common atom `z` outside the object, pointing to `fa` and `fb`, which are adjacent and of degree `2`. -/
theorem vine_twin_gap_zero {Rn : ℕ} {L : ℝ} {w : Mom d} (hI : Inv Rn h.s) (hu : h.s.cls K.C.upper = .eps)
    (hl : h.s.cls K.C.lower = .eps) (k0 : D₀ → (Fin d → ℤ)) (hchg : ChgS L w k0 h.s)
    (hmate : ∀ x, k0 (h.s.down (h.s.M.mate x)) = k0 (h.s.down x))
    (hfa : K.cutMol.deg K.fa = 2) (hfb : K.cutMol.deg K.fb = 2)
    (e₀ : h.s.D) (he1 : K.cutMol.atom e₀ = K.fa) (he2 : K.cutMol.atom (h.s.M.mate e₀) = K.fb)
    (a₁ b₁ : h.s.D) (hzS : K.cutMol.atom a₁ ∉ K.C.atoms) (hzab : K.cutMol.atom a₁ = K.cutMol.atom b₁)
    (hdir : h.s.M.out a₁ ≠ h.s.M.out b₁) (hpa : K.cutMol.atom (h.s.M.mate a₁) = K.fa)
    (hqb : K.cutMol.atom (h.s.M.mate b₁) = K.fb) :
    Molecule.gapAt L w (k0 ∘ h.s.down) a₁ b₁ = 0 := by
  have hP : h.s.M.atom (h.s.M.mate a₁) = K.C.upper := atom_of_cut_fa h K hpa
  have hQ : h.s.M.atom (h.s.M.mate b₁) = K.C.lower := atom_of_cut_fb h K hqb
  have hzfa : K.cutMol.atom a₁ ≠ K.fa := by
    intro e
    exact hI.noloop a₁ ((atom_of_cut_fa h K e).trans hP.symm)
  have hzfb : K.cutMol.atom a₁ ≠ K.fb := by
    intro e
    exact hI.noloop b₁ ((atom_of_cut_fb h K (hzab ▸ e)).trans hQ.symm)
  have hA : h.s.M.atom a₁ = K.cutMol.atom a₁ := (vine_atom_of_ne h K a₁ hzfa hzfb).symm
  have hB : h.s.M.atom b₁ = K.cutMol.atom a₁ := by
    rw [hzab] at hzfa hzfb ⊢; exact (vine_atom_of_ne h K b₁ hzfa hzfb).symm
  have mma : h.s.M.mate (h.s.M.mate a₁) = a₁ := h.s.M.mate_mate a₁
  have mmb : h.s.M.mate (h.s.M.mate b₁) = b₁ := h.s.M.mate_mate b₁
  have mme : h.s.M.mate (h.s.M.mate e₀) = e₀ := h.s.M.mate_mate e₀
  have hpS : h.s.M.atom (h.s.M.mate a₁) ∈ K.C.atoms ∧ h.s.M.atom (h.s.M.mate (h.s.M.mate a₁)) ∉ K.C.atoms := by
    rw [mma, hP, hA]; exact ⟨K.a_mem, hzS⟩
  have hqS : h.s.M.atom (h.s.M.mate b₁) ∈ K.C.atoms ∧ h.s.M.atom (h.s.M.mate (h.s.M.mate b₁)) ∉ K.C.atoms := by
    rw [mmb, hQ, hB]; exact ⟨K.b_mem, hzS⟩
  have hbd : ∀ x, h.s.M.atom x ∈ K.C.atoms → h.s.M.atom (h.s.M.mate x) ∉ K.C.atoms →
      x = h.s.M.mate a₁ ∨ x = h.s.M.mate b₁ := by
    intro x hx hmx
    have hxc : K.cutMol.atom x ∉ K.C.atoms := by
      intro hin
      by_cases hm : K.cutMol.atom (h.s.M.mate x) = K.fa ∨ K.cutMol.atom (h.s.M.mate x) = K.fb
      · rcases hm with hm | hm
        · exact hmx ((atom_of_cut_fa h K hm).symm ▸ K.a_mem)
        · exact hmx ((atom_of_cut_fb h K hm).symm ▸ K.b_mem)
      · push Not at hm
        have e := vine_atom_of_ne h K (h.s.M.mate x) hm.1 hm.2
        have hcl : K.cutMol.atom (h.s.M.mate (h.s.M.mate x)) ∉ K.C.atoms :=
          K.closed (h.s.M.mate x) (by show K.cutMol.atom (h.s.M.mate x) ∉ K.C.atoms; rw [e]; exact hmx)
        rw [h.s.M.mate_mate] at hcl
        exact hcl hin
    rcases atom_cut_of_mem_C h K hx hxc with hxa | hxb
    · have hne : h.s.M.mate a₁ ≠ e₀ := by
        intro ee
        have : K.cutMol.atom (h.s.M.mate (h.s.M.mate a₁)) = K.fb := by rw [ee]; exact he2
        rw [mma] at this
        exact hzfb this
      rcases dart_eq_of_deg2 K.cutMol hfa hpa he1 hne hxa with hx1 | hx2
      · exact Or.inl hx1
      · exfalso
        apply hmx
        rw [hx2, atom_of_cut_fb h K he2]; exact K.b_mem
    · have hne : h.s.M.mate b₁ ≠ h.s.M.mate e₀ := by
        intro ee
        have h2 : b₁ = e₀ := by
          have := congrArg h.s.M.mate ee; rwa [mmb, mme] at this
        exact hzfa (hzab.trans (h2 ▸ he1))
      rcases dart_eq_of_deg2 K.cutMol hfb hqb he2 hne hxb with hx1 | hx2
      · exact Or.inr hx1
      · exfalso
        apply hmx
        rw [hx2, mme, atom_of_cut_fa h K he1]; exact K.a_mem
  have hc : ∀ v ∈ K.C.atoms, ∑ x ∈ h.s.M.dartsAt v, h.s.M.dartSign x • Molecule.kvec L w (k0 ∘ h.s.down) x = 0 := by
    intro v hv
    have hvM : v ∈ h.s.M.atoms := Step1.objectAtoms_sub K.C hv
    have heps := GammaLow.FinalCount.H.vine_atoms_eps hI K hu hl v hv
    have h4 : h.s.M.deg v = 4 := by
      by_cases h1 : v = K.C.upper
      · rw [h1]; exact deg_upper_of_fa h K hfa
      by_cases h2 : v = K.C.lower
      · rw [h2]; exact deg_lower_of_fb h K hfb
      exact GammaLow.FinalCount.H.vine_interior_deg K hI.bounds hv h1 h2
    exact hchg v hvM heps h4
  have hpq : h.s.M.mate a₁ ≠ h.s.M.mate b₁ := by
    intro e; rw [e] at hP; rw [hP] at hQ; exact K.ab_ne hQ
  have hdir' : h.s.M.out (h.s.M.mate a₁) ≠ h.s.M.out (h.s.M.mate b₁) := by
    rw [h.s.M.out_mate, h.s.M.out_mate]
    intro e; apply hdir
    simpa using e
  have hkv := boundary_kvec_eq h.s.M (κ := k0 ∘ h.s.down) (L := L) (w := w) hmate K.C.atoms hc
    (h.s.M.mate a₁) (h.s.M.mate b₁) hpq hpS hqS hbd hdir'
  have e1 : Molecule.kvec L w (k0 ∘ h.s.down) (h.s.M.mate a₁) = Molecule.kvec L w (k0 ∘ h.s.down) a₁ := by
    unfold Molecule.kvec; simp only [Function.comp]; rw [hmate]
  have e2 : Molecule.kvec L w (k0 ∘ h.s.down) (h.s.M.mate b₁) = Molecule.kvec L w (k0 ∘ h.s.down) b₁ := by
    unfold Molecule.kvec; simp only [Function.comp]; rw [hmate]
  unfold Molecule.gapAt
  rw [← e1, ← e2, hkv, sub_self]

/-- **The twins of an Operation-1 step are locked** (M1-R2 Lemma 2.1 at the creation step). -/
theorem vine_twin_locked {Rn : ℕ} {L : ℝ} {w : Mom d} (hI : Inv Rn h.s) (hu : h.s.cls K.C.upper = .eps)
    (hl : h.s.cls K.C.lower = .eps) {B : Set (D₀ → (Fin d → ℤ))}
    (hchg : ∀ k0 ∈ B, ChgS L w k0 h.s) (hmate : ∀ k0 ∈ B, ∀ x, k0 (h.s.down (h.s.M.mate x)) = k0 (h.s.down x))
    (hfa : (h.vinePostL K R kp).s.M.deg K.fa = 2) (hfb : (h.vinePostL K R kp).s.M.deg K.fb = 2)
    (hadj : (h.vinePostL K R kp).s.M.Adj K.fa K.fb) :
    Locked L w (h.vinePostL K R kp) B K.fa K.fb := by
  intro a b hab hdir ha hb k0 hk0
  have hfa' : K.cutMol.deg K.fa = 2 :=
    (restrictP_deg K.cutMol (fun a => a ∉ K.C.atoms) K.closed (fa_notMem_C h K)).symm.trans hfa
  have hfb' : K.cutMol.deg K.fb = 2 :=
    (restrictP_deg K.cutMol (fun a => a ∉ K.C.atoms) K.closed (fb_notMem_C h K)).symm.trans hfb
  obtain ⟨e, he, he'⟩ := hadj
  exact vine_twin_gap_zero h K hI hu hl k0 (hchg k0 hk0) (hmate k0 hk0) hfa' hfb' e.1 he he' a.1 b.1 a.2 hab hdir ha hb

end vine

end WaveTurbulence.GammaLow.FinalCount.Ghost
