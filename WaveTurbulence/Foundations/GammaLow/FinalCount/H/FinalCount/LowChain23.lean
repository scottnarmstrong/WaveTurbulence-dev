/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.LowChain23
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.LowChain22
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.LowChain23`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT LOW-CHAIN, session 5 (1): the removal bookkeeping for `HendAtL` (`ConnExtraL`, `ConnDataL2`).**
`ConnExtraL` adds to `ConnDataL` the fields needed to compare the state with `remMol M₀ ps`: present darts are not killed (`he1`),
no state atom is the ancestor of an interior atom of a piece (`he3`), the first-stage order (`hfo`), and the weakened `he2'`: an atom of `M₀`
that is interior to no piece is an ancestor of a state atom OR has all its darts killed (the degree-`2` joints deleted by Step D1).
`connExtraL_vine`/`connExtraL_vineG` carry it along the old vine step and Step D1. -/
@[expose] public section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine
  WaveTurbulence.VineCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

def ConnExtraL (M₀ : Molecule V D₀) (Fst : Set (Src.Object Src.γL M₀)) (h : HSt V D₀) (ps : List (Src.Object Src.γL M₀ × Quad D₀)) : Prop :=
  (∀ x : h.s.D, ∀ p ∈ ps, h.s.down x ∉ PieceKill p.1 p.2) ∧
  (∀ v ∈ M₀.atoms, (∀ p ∈ ps, ¬ PieceInt p.1 v) →
    (∃ c ∈ h.s.M.atoms, h.anc c = v) ∨ (∀ z, M₀.atom z = v → z ∈ KillS ps)) ∧
  (∀ c ∈ h.s.M.atoms, ∀ p ∈ ps, ¬ PieceInt p.1 (h.anc c)) ∧
  ((∃ p ∈ ps, p.1 ∉ Fst) → ∀ U ∈ Fst, Dartless U h)

def ConnDataL2 (M₀ : Molecule V D₀) (C : CollData M₀) (Un : (D₀ → (Fin d → ℤ)) → Set (Src.Object Src.γL M₀)) (Fst : Set (Src.Object Src.γL M₀))
    (L γ η : ℝ) (w : Mom d) (κ : D₀ → (Fin d → ℤ)) (h : HSt V D₀) (ps : List (Src.Object Src.γL M₀ × Quad D₀)) : Prop :=
  ConnDataL M₀ C Un Fst L γ η w κ h ps ∧ ConnExtraL M₀ Fst h ps

theorem connExtraL_init (M₀ : Molecule V D₀) (Fst : Set (Src.Object Src.γL M₀)) : ConnExtraL M₀ Fst (HSt.init M₀) [] := by
  refine ⟨by simp, ?_, by simp, by simp⟩
  intro v hv _
  exact Or.inl ⟨v, hv, rfl⟩

theorem connDataL2_init (M₀ : Molecule V D₀) (C : CollData M₀) (Un : (D₀ → (Fin d → ℤ)) → Set (Src.Object Src.γL M₀)) (Fst : Set (Src.Object Src.γL M₀))
    (L γ η : ℝ) (w : Mom d) (κ : D₀ → (Fin d → ℤ)) : ConnDataL2 M₀ C Un Fst L γ η w κ (HSt.init M₀) [] :=
  ⟨connDataL_init M₀ C Un Fst L γ η w κ, connExtraL_init M₀ Fst⟩

theorem vineCut_x_ne {D : Type*} [Fintype D] [DecidableEq D] {M : Molecule V D} (K : Step1.VineCut Src.γL M) : K.x₁ ≠ K.x₂ := by
  intro e; have h1 := K.cut_a.2.2.2.2.2.1; have h2 := K.cut_a.2.2.2.2.2.2; rw [e] at h1; simp_all

theorem vineCut_y_ne {D : Type*} [Fintype D] [DecidableEq D] {M : Molecule V D} (K : Step1.VineCut Src.γL M) : K.y₁ ≠ K.y₂ := by
  intro e; have h1 := K.cut_b.2.2.2.2.2.1; have h2 := K.cut_b.2.2.2.2.2.2; rw [e] at h1; simp_all

/-- At a degree-`2` joint of a cut object, every dart of `M₀` at the joint is killed by the new piece or by an earlier one. -/
theorem joint_killed_of_deg2 {M₀ : Molecule V D₀} {b : HSt V D₀} (hA : AncRel M₀ b.s b.anc)
    {ps : List (Src.Object Src.γL M₀ × Quad D₀)}
    (hinj : ∀ c ∈ b.s.M.atoms, ∀ e ∈ b.s.M.atoms, b.anc c = b.anc e → c = e)
    (hpres : ∀ z : D₀, (∀ x : b.s.D, b.s.down x ≠ z) → ∃ p ∈ ps, z ∈ PieceKill p.1 p.2)
    (U : Src.Object Src.γL M₀) (N : Quad D₀) {j : V} (hj : j ∈ b.s.M.atoms) (hjanc : b.anc j = j) (hd : b.s.M.deg j = 2)
    {p₁ p₂ : b.s.D} (h1 : b.s.M.atom p₁ = j) (h2 : b.s.M.atom p₂ = j) (hne : p₁ ≠ p₂)
    (k1 : b.s.down p₁ ∈ PieceKill U N) (k2 : b.s.down p₂ ∈ PieceKill U N) :
    ∀ z, M₀.atom z = j → z ∈ KillS ((U, N) :: ps) := by
  intro z hz
  by_cases hx : ∃ x : b.s.D, b.s.down x = z
  · obtain ⟨x, rfl⟩ := hx
    have e1 : M₀.atom (b.s.down x) = b.anc (b.s.M.atom x) := hA.atom x
    have e2 : b.s.M.atom x = j := hinj _ (b.s.M.atom_mem x) _ hj (by rw [← e1, hz, hjanc])
    rcases dart_of_deg_two b.s.M hd h1 h2 hne x e2 with rfl | rfl
    · exact ⟨(U, N), List.mem_cons_self, k1⟩
    · exact ⟨(U, N), List.mem_cons_self, k2⟩
  · push Not at hx
    obtain ⟨p, hp, hk⟩ := hpres z hx
    exact ⟨p, List.mem_cons_of_mem _ hp, hk⟩

theorem connExtraL_vine [Infinite V] {M₀ : Molecule V D₀} {C : CollData M₀} {Un : (D₀ → (Fin d → ℤ)) → Set (Src.Object Src.γL M₀)}
    {Fst : Set (Src.Object Src.γL M₀)} {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {b : HSt V D₀} (hA : AncRel M₀ b.s b.anc)
    {ps : List (Src.Object Src.γL M₀ × Quad D₀)} (hI : ConnDataL2 M₀ C Un Fst L γ η w κ b ps) (K : Step1.VineCut Src.γL b.s.M) (R : ℝ) (kp : ℕ) (U : Src.Object Src.γL M₀)
    (hUK : U.atoms = K.C.atoms)
    (hUJ : (M₀.atom (b.s.down K.x₁) = U.upper ∧ M₀.atom (b.s.down K.y₁) = U.lower) ∨
      (M₀.atom (b.s.down K.x₁) = U.lower ∧ M₀.atom (b.s.down K.y₁) = U.upper))
    (hord : U ∈ Fst ∨ ∀ U' ∈ Fst, Dartless U' b)
    (hint : UIntact U b) : ConnExtraL M₀ Fst (b.vinePostL K R kp)
      ((U, (b.s.down K.x₁, b.s.down K.x₂, b.s.down K.y₁, b.s.down K.y₂)) :: ps) := by
  obtain ⟨⟨hinj, hps, hpw, hrem, hpres⟩, he1, he2, he3, hfo⟩ := hI
  have hUe : ∀ v ∈ K.C.atoms, b.anc v = v := fun v hv => by
    have hv' : v ∈ U.atoms := by rw [hUK]; exact hv
    exact hA.eps v (hint v hv').1 (hint v hv').2
  have hpost : (b.vinePostL K R kp).s.M.atoms = (insert K.fb (insert K.fa b.s.M.atoms)).filter (fun a => a ∉ K.C.atoms) := rfl
  have hup : M₀.atom (b.s.down K.x₁) = K.C.upper := by
    rw [hA.atom, K.cut_a.2.2.1, hUe _ K.a_mem]
  have hlow : M₀.atom (b.s.down K.y₁) = K.C.lower := by
    rw [hA.atom, K.My₁, hUe _ K.b_mem]
  have hJ : (K.C.upper = U.upper ∧ K.C.lower = U.lower) ∨ (K.C.upper = U.lower ∧ K.C.lower = U.upper) := by
    rcases hUJ with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · exact Or.inl ⟨hup ▸ e1, hlow ▸ e2⟩
    · exact Or.inr ⟨hup ▸ e1, hlow ▸ e2⟩
  have hJ' : ∀ v, (v = K.C.upper ∨ v = K.C.lower) → (v = U.upper ∨ v = U.lower) := by
    intro v hv
    rcases hJ with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rcases hv with rfl | rfl
    · exact Or.inl e1
    · exact Or.inr e2
    · exact Or.inr e1
    · exact Or.inl e2
  have hback : ∀ c ∈ b.s.M.atoms, b.anc c ∈ U.atoms → c = b.anc c := fun c hc hu =>
    hA.uniq c hc (b.anc c) (hint _ hu).1 (hint _ hu).2 rfl
  have hold : ∀ c ∈ b.s.M.atoms, c ∉ K.C.atoms → b.anc c ∉ U.atoms := by
    intro c hc hcC hu
    exact hcC (by rw [← hUK, hback c hc hu]; exact hu)
  have hanc : (b.vinePostL K R kp).anc = Function.update (Function.update b.anc K.fa (b.anc K.C.upper)) K.fb (b.anc K.C.lower) := rfl
  have hev : ∀ c, c ∈ b.s.M.atoms → (b.vinePostL K R kp).anc c = b.anc c := by
    intro c hc
    rw [hanc, Function.update_of_ne (fun e => K.fb_fresh (by rw [← e]; exact hc)),
      Function.update_of_ne (fun e => K.fa_fresh (by rw [← e]; exact hc))]
  have hfaE : (b.vinePostL K R kp).anc K.fa = K.C.upper := by
    rw [hanc, Function.update_of_ne K.fa_ne_fb, Function.update_self, hUe _ K.a_mem]
  have hfbE : (b.vinePostL K R kp).anc K.fb = K.C.lower := by
    rw [hanc, Function.update_self, hUe _ K.b_mem]
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- present darts are not killed
    intro x p hp
    rcases List.mem_cons.1 hp with rfl | hp
    · intro hk
      have hat : M₀.atom (b.s.down x.1) ∈ U.atoms := hk.1
      have himp : (M₀.atom (b.s.down x.1) = U.upper ∨ M₀.atom (b.s.down x.1) = U.lower) →
          (b.s.down x.1 = b.s.down K.x₁ ∨ b.s.down x.1 = b.s.down K.x₂ ∨ b.s.down x.1 = b.s.down K.y₁ ∨
            b.s.down x.1 = b.s.down K.y₂) := hk.2
      have hy : K.cutMol.atom x.1 ∉ K.C.atoms := x.2
      have hz1 : M₀.atom (b.s.down x.1) = b.anc (b.s.M.atom x.1) := hA.atom x.1
      have hu : b.anc (b.s.M.atom x.1) ∈ U.atoms := hz1 ▸ hat
      have hMx : b.s.M.atom x.1 = b.anc (b.s.M.atom x.1) := hback _ (b.s.M.atom_mem x.1) hu
      have hMxC : b.s.M.atom x.1 ∈ K.C.atoms := by
        have h1 : b.anc (b.s.M.atom x.1) ∈ K.C.atoms := (Finset.ext_iff.1 hUK _).1 hu
        rw [hMx]; exact h1
      have hmv := cutMol_atom_moved K hMxC hy
      have hzj : M₀.atom (b.s.down x.1) = b.s.M.atom x.1 := by rw [hz1, ← hMx]
      have hmj : M₀.atom (b.s.down x.1) = U.upper ∨ M₀.atom (b.s.down x.1) = U.lower := by
        rcases hmv with ⟨e, -, -⟩ | ⟨e, -, -⟩
        · exact hJ' _ (Or.inl (hzj.trans e))
        · exact hJ' _ (Or.inr (hzj.trans e))
      have hN := himp hmj
      have hinjd := hA.inj
      rcases hmv with ⟨e, n1, n2⟩ | ⟨e, n1, n2⟩
      · rcases hN with e' | e' | e' | e'
        · exact n1 (hinjd e')
        · exact n2 (hinjd e')
        · have := hinjd e'; rw [this] at e; exact K.ab_ne (e.symm.trans K.My₁)
        · have := hinjd e'; rw [this] at e; exact K.ab_ne (e.symm.trans K.My₂)
      · rcases hN with e' | e' | e' | e'
        · have := hinjd e'; rw [this] at e; exact K.ab_ne (K.Mx₁.symm.trans e)
        · have := hinjd e'; rw [this] at e; exact K.ab_ne (K.Mx₂.symm.trans e)
        · exact n1 (hinjd e')
        · exact n2 (hinjd e')
    · exact he1 x.1 p hp
  · -- atoms: ancestor of a state atom, or all darts killed
    intro v hv hvn
    have hvn' : ∀ p ∈ ps, ¬ PieceInt p.1 v := fun p hp => hvn p (List.mem_cons_of_mem _ hp)
    have hnU : ¬ PieceInt U v := hvn _ List.mem_cons_self
    rcases he2 v hv hvn' with ⟨c, hc, hcv⟩ | hk
    · left
      by_cases hcC : c ∈ K.C.atoms
      · have hvU : v ∈ U.atoms := by rw [hUK, ← hcv, hUe _ hcC]; exact hcC
        have hvj : v = U.upper ∨ v = U.lower := by
          by_contra hcon
          push Not at hcon
          exact hnU ⟨hvU, hcon.1, hcon.2⟩
        rcases hJ with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · rcases hvj with rfl | rfl
          · refine ⟨K.fa, ?_, ?_⟩
            · rw [hpost, Finset.mem_filter]
              exact ⟨Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), fun h => K.fa_fresh (Step1.objectAtoms_sub K.C h)⟩
            · rw [hfaE, e1]
          · refine ⟨K.fb, ?_, ?_⟩
            · rw [hpost, Finset.mem_filter]
              exact ⟨Finset.mem_insert_self _ _, fun h => K.fb_fresh (Step1.objectAtoms_sub K.C h)⟩
            · rw [hfbE, e2]
        · rcases hvj with rfl | rfl
          · refine ⟨K.fb, ?_, ?_⟩
            · rw [hpost, Finset.mem_filter]
              exact ⟨Finset.mem_insert_self _ _, fun h => K.fb_fresh (Step1.objectAtoms_sub K.C h)⟩
            · rw [hfbE, e2]
          · refine ⟨K.fa, ?_, ?_⟩
            · rw [hpost, Finset.mem_filter]
              exact ⟨Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), fun h => K.fa_fresh (Step1.objectAtoms_sub K.C h)⟩
            · rw [hfaE, e1]
      · refine ⟨c, ?_, ?_⟩
        · rw [hpost, Finset.mem_filter]
          exact ⟨Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hc), hcC⟩
        · rw [hev c hc, hcv]
    · right
      intro z hz
      obtain ⟨p, hp, hkz⟩ := hk z hz
      exact ⟨p, List.mem_cons_of_mem _ hp, hkz⟩
  · -- no state atom is the ancestor of an interior atom of a removed piece
    intro c hc p hp
    rw [hpost, Finset.mem_filter, Finset.mem_insert, Finset.mem_insert] at hc
    obtain ⟨hc1, hc2⟩ := hc
    rcases List.mem_cons.1 hp with rfl | hp
    · rintro ⟨hat, hn1, hn2⟩
      rcases hc1 with rfl | rfl | hc1
      · rw [hfbE] at hat hn1 hn2
        rcases hJ with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · exact hn2 e2
        · exact hn1 e2
      · rw [hfaE] at hat hn1 hn2
        rcases hJ with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · exact hn1 e1
        · exact hn2 e1
      · rw [hev c hc1] at hat
        exact hold c hc1 hc2 hat
    · rcases hc1 with rfl | rfl | hc1
      · rw [hfbE]
        intro hpi
        have := he3 K.C.lower (Step1.objectAtoms_sub K.C K.b_mem) p hp
        rw [hUe _ K.b_mem] at this
        exact this hpi
      · rw [hfaE]
        intro hpi
        have := he3 K.C.upper (Step1.objectAtoms_sub K.C K.a_mem) p hp
        rw [hUe _ K.a_mem] at this
        exact this hpi
      · rw [hev c hc1]
        exact he3 c hc1 p hp
  · -- first-stage order
    intro ⟨p, hp, hpF⟩ U' hU'
    have hshr : ∀ U'' ∈ Fst, Dartless U'' b := by
      rcases List.mem_cons.1 hp with rfl | hp
      · rcases hord with h1 | h1
        · exact absurd h1 hpF
        · exact h1
      · exact hfo ⟨p, hp, hpF⟩
    intro x hx
    exact hshr U' hU' x.1 hx

theorem connExtraL_vineG [Infinite V] {M₀ : Molecule V D₀} {C : CollData M₀} {Un : (D₀ → (Fin d → ℤ)) → Set (Src.Object Src.γL M₀)}
    {Fst : Set (Src.Object Src.γL M₀)} {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {b : HSt V D₀} (hA : AncRel M₀ b.s b.anc)
    {ps : List (Src.Object Src.γL M₀ × Quad D₀)} (hI : ConnDataL2 M₀ C Un Fst L γ η w κ b ps) (K : Step1.VineCut Src.γL b.s.M) (U : Src.Object Src.γL M₀)
    (hUK : U.atoms = K.C.atoms)
    (hUJ : (M₀.atom (b.s.down K.x₁) = U.upper ∧ M₀.atom (b.s.down K.y₁) = U.lower) ∨
      (M₀.atom (b.s.down K.x₁) = U.lower ∧ M₀.atom (b.s.down K.y₁) = U.upper))
    (hord : U ∈ Fst ∨ ∀ U' ∈ Fst, Dartless U' b)
    (hint : UIntact U b) : ConnExtraL M₀ Fst (b.vinePostGL K)
      ((U, (b.s.down K.x₁, b.s.down K.x₂, b.s.down K.y₁, b.s.down K.y₂)) :: ps) := by
  obtain ⟨⟨hinj, hps, hpw, hrem, hpres⟩, he1, he2, he3, hfo⟩ := hI
  have hUe : ∀ v ∈ K.C.atoms, b.anc v = v := fun v hv => by
    have hv' : v ∈ U.atoms := by rw [hUK]; exact hv
    exact hA.eps v (hint v hv').1 (hint v hv').2
  have hpost : (b.vinePostGL K).s.M.atoms = (insert K.fb (insert K.fa b.s.M.atoms)).filter (VineKeep K) := rfl
  have hup : M₀.atom (b.s.down K.x₁) = K.C.upper := by
    rw [hA.atom, K.cut_a.2.2.1, hUe _ K.a_mem]
  have hlow : M₀.atom (b.s.down K.y₁) = K.C.lower := by
    rw [hA.atom, K.My₁, hUe _ K.b_mem]
  have hup2 : M₀.atom (b.s.down K.x₂) = K.C.upper := by rw [hA.atom, K.Mx₂, hUe _ K.a_mem]
  have hlow2 : M₀.atom (b.s.down K.y₂) = K.C.lower := by rw [hA.atom, K.My₂, hUe _ K.b_mem]
  have hJ : (K.C.upper = U.upper ∧ K.C.lower = U.lower) ∨ (K.C.upper = U.lower ∧ K.C.lower = U.upper) := by
    rcases hUJ with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · exact Or.inl ⟨hup ▸ e1, hlow ▸ e2⟩
    · exact Or.inr ⟨hup ▸ e1, hlow ▸ e2⟩
  have hJ' : ∀ v, (v = K.C.upper ∨ v = K.C.lower) → (v = U.upper ∨ v = U.lower) := by
    intro v hv
    rcases hJ with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rcases hv with rfl | rfl
    · exact Or.inl e1
    · exact Or.inr e2
    · exact Or.inr e1
    · exact Or.inl e2
  have hJr : ∀ v, (v = U.upper ∨ v = U.lower) → (v = K.C.upper ∨ v = K.C.lower) := by
    intro v hv
    rcases hJ with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rcases hv with rfl | rfl
    · exact Or.inl e1.symm
    · exact Or.inr e2.symm
    · exact Or.inr e2.symm
    · exact Or.inl e1.symm
  have hback : ∀ c ∈ b.s.M.atoms, b.anc c ∈ U.atoms → c = b.anc c := fun c hc hu =>
    hA.uniq c hc (b.anc c) (hint _ hu).1 (hint _ hu).2 rfl
  have hold : ∀ c ∈ b.s.M.atoms, c ∉ K.C.atoms → b.anc c ∉ U.atoms := by
    intro c hc hcC hu
    exact hcC (by rw [← hUK, hback c hc hu]; exact hu)
  have hanc : (b.vinePostGL K).anc = Function.update (Function.update b.anc K.fa (b.anc K.C.upper)) K.fb (b.anc K.C.lower) := rfl
  have hev : ∀ c, c ∈ b.s.M.atoms → (b.vinePostGL K).anc c = b.anc c := by
    intro c hc
    rw [hanc, Function.update_of_ne (fun e => K.fb_fresh (by rw [← e]; exact hc)),
      Function.update_of_ne (fun e => K.fa_fresh (by rw [← e]; exact hc))]
  have hfaE : (b.vinePostGL K).anc K.fa = K.C.upper := by
    rw [hanc, Function.update_of_ne K.fa_ne_fb, Function.update_self, hUe _ K.a_mem]
  have hfbE : (b.vinePostGL K).anc K.fb = K.C.lower := by
    rw [hanc, Function.update_self, hUe _ K.b_mem]
  have hat : ∀ v ∈ K.C.atoms, v ∈ U.atoms := fun v hv => by rw [hUK]; exact hv
  set N : Quad D₀ := (b.s.down K.x₁, b.s.down K.x₂, b.s.down K.y₁, b.s.down K.y₂) with hN
  have hk1 : b.s.down K.x₁ ∈ PieceKill U N := ⟨hup ▸ hat _ K.a_mem, fun _ => Or.inl rfl⟩
  have hk2 : b.s.down K.x₂ ∈ PieceKill U N := ⟨hup2 ▸ hat _ K.a_mem, fun _ => Or.inr (Or.inl rfl)⟩
  have hk3 : b.s.down K.y₁ ∈ PieceKill U N := ⟨hlow ▸ hat _ K.b_mem, fun _ => Or.inr (Or.inr (Or.inl rfl))⟩
  have hk4 : b.s.down K.y₂ ∈ PieceKill U N := ⟨hlow2 ▸ hat _ K.b_mem, fun _ => Or.inr (Or.inr (Or.inr rfl))⟩
  have hKu : b.s.M.deg K.C.upper = 2 → ∀ z, M₀.atom z = K.C.upper → z ∈ KillS ((U, N) :: ps) := fun hd =>
    joint_killed_of_deg2 hA hinj hpres U N (Step1.objectAtoms_sub K.C K.a_mem) (hUe _ K.a_mem) hd K.cut_a.2.2.1 K.Mx₂
      (vineCut_x_ne K) hk1 hk2
  have hKl : b.s.M.deg K.C.lower = 2 → ∀ z, M₀.atom z = K.C.lower → z ∈ KillS ((U, N) :: ps) := fun hd =>
    joint_killed_of_deg2 hA hinj hpres U N (Step1.objectAtoms_sub K.C K.b_mem) (hUe _ K.b_mem) hd K.My₁ K.My₂
      (vineCut_y_ne K) hk3 hk4
  have hfa_mem : b.s.M.deg K.C.upper ≠ 2 → K.fa ∈ (b.vinePostGL K).s.M.atoms := fun hd => by
    rw [hpost, Finset.mem_filter]
    exact ⟨Finset.mem_insert_of_mem (Finset.mem_insert_self _ _),
      fun h => K.fa_fresh (Step1.objectAtoms_sub K.C h), fun ⟨_, h⟩ => hd h, fun ⟨e, _⟩ => K.fa_ne_fb e⟩
  have hfb_mem : b.s.M.deg K.C.lower ≠ 2 → K.fb ∈ (b.vinePostGL K).s.M.atoms := fun hd => by
    rw [hpost, Finset.mem_filter]
    exact ⟨Finset.mem_insert_self _ _,
      fun h => K.fb_fresh (Step1.objectAtoms_sub K.C h), fun ⟨e, _⟩ => K.fa_ne_fb e.symm, fun ⟨_, h⟩ => hd h⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- present darts are not killed
    intro x p hp
    rcases List.mem_cons.1 hp with rfl | hp
    · intro hk
      have hat' : M₀.atom (b.s.down x.1) ∈ U.atoms := hk.1
      have himp : (M₀.atom (b.s.down x.1) = U.upper ∨ M₀.atom (b.s.down x.1) = U.lower) →
          (b.s.down x.1 = b.s.down K.x₁ ∨ b.s.down x.1 = b.s.down K.x₂ ∨ b.s.down x.1 = b.s.down K.y₁ ∨
            b.s.down x.1 = b.s.down K.y₂) := hk.2
      have hy : K.cutMol.atom x.1 ∉ K.C.atoms := x.2.1
      have hz1 : M₀.atom (b.s.down x.1) = b.anc (b.s.M.atom x.1) := hA.atom x.1
      have hu : b.anc (b.s.M.atom x.1) ∈ U.atoms := hz1 ▸ hat'
      have hMx : b.s.M.atom x.1 = b.anc (b.s.M.atom x.1) := hback _ (b.s.M.atom_mem x.1) hu
      have hMxC : b.s.M.atom x.1 ∈ K.C.atoms := by
        have h1 : b.anc (b.s.M.atom x.1) ∈ K.C.atoms := (Finset.ext_iff.1 hUK _).1 hu
        rw [hMx]; exact h1
      have hmv := cutMol_atom_moved K hMxC hy
      have hzj : M₀.atom (b.s.down x.1) = b.s.M.atom x.1 := by rw [hz1, ← hMx]
      have hmj : M₀.atom (b.s.down x.1) = U.upper ∨ M₀.atom (b.s.down x.1) = U.lower := by
        rcases hmv with ⟨e, -, -⟩ | ⟨e, -, -⟩
        · exact hJ' _ (Or.inl (hzj.trans e))
        · exact hJ' _ (Or.inr (hzj.trans e))
      have hN' := himp hmj
      have hinjd := hA.inj
      rcases hmv with ⟨e, n1, n2⟩ | ⟨e, n1, n2⟩
      · rcases hN' with e' | e' | e' | e'
        · exact n1 (hinjd e')
        · exact n2 (hinjd e')
        · have := hinjd e'; rw [this] at e; exact K.ab_ne (e.symm.trans K.My₁)
        · have := hinjd e'; rw [this] at e; exact K.ab_ne (e.symm.trans K.My₂)
      · rcases hN' with e' | e' | e' | e'
        · have := hinjd e'; rw [this] at e; exact K.ab_ne (K.Mx₁.symm.trans e)
        · have := hinjd e'; rw [this] at e; exact K.ab_ne (K.Mx₂.symm.trans e)
        · exact n1 (hinjd e')
        · exact n2 (hinjd e')
    · exact he1 x.1 p hp
  · -- atoms: ancestor of a state atom, or all darts killed
    intro v hv hvn
    have hvn' : ∀ p ∈ ps, ¬ PieceInt p.1 v := fun p hp => hvn p (List.mem_cons_of_mem _ hp)
    have hnU : ¬ PieceInt U v := hvn _ List.mem_cons_self
    rcases he2 v hv hvn' with ⟨c, hc, hcv⟩ | hk
    · by_cases hcC : c ∈ K.C.atoms
      · have hvU : v ∈ U.atoms := by rw [hUK, ← hcv, hUe _ hcC]; exact hcC
        have hvj : v = U.upper ∨ v = U.lower := by
          by_contra hcon
          push Not at hcon
          exact hnU ⟨hvU, hcon.1, hcon.2⟩
        rcases hJr v hvj with hvu | hvl
        · by_cases hd : b.s.M.deg K.C.upper = 2
          · right; rw [hvu]; exact hKu hd
          · left; exact ⟨K.fa, hfa_mem hd, by rw [hfaE, hvu]⟩
        · by_cases hd : b.s.M.deg K.C.lower = 2
          · right; rw [hvl]; exact hKl hd
          · left; exact ⟨K.fb, hfb_mem hd, by rw [hfbE, hvl]⟩
      · left
        refine ⟨c, ?_, ?_⟩
        · rw [hpost, Finset.mem_filter]
          exact ⟨Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hc), hcC,
            by rintro ⟨e, -⟩; exact K.fa_fresh (e ▸ hc), by rintro ⟨e, -⟩; exact K.fb_fresh (e ▸ hc)⟩
        · rw [hev c hc, hcv]
    · right
      intro z hz
      obtain ⟨p, hp, hkz⟩ := hk z hz
      exact ⟨p, List.mem_cons_of_mem _ hp, hkz⟩
  · -- no state atom is the ancestor of an interior atom of a removed piece
    intro c hc p hp
    rw [hpost, Finset.mem_filter, Finset.mem_insert, Finset.mem_insert] at hc
    obtain ⟨hc1, hc2⟩ := hc
    rcases List.mem_cons.1 hp with rfl | hp
    · rintro ⟨hat', hn1, hn2⟩
      rcases hc1 with rfl | rfl | hc1
      · rw [hfbE] at hat' hn1 hn2
        rcases hJ with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · exact hn2 e2
        · exact hn1 e2
      · rw [hfaE] at hat' hn1 hn2
        rcases hJ with ⟨e1, e2⟩ | ⟨e1, e2⟩
        · exact hn1 e1
        · exact hn2 e1
      · rw [hev c hc1] at hat'
        exact hold c hc1 hc2.1 hat'
    · rcases hc1 with rfl | rfl | hc1
      · rw [hfbE]
        intro hpi
        have := he3 K.C.lower (Step1.objectAtoms_sub K.C K.b_mem) p hp
        rw [hUe _ K.b_mem] at this
        exact this hpi
      · rw [hfaE]
        intro hpi
        have := he3 K.C.upper (Step1.objectAtoms_sub K.C K.a_mem) p hp
        rw [hUe _ K.a_mem] at this
        exact this hpi
      · rw [hev c hc1]
        exact he3 c hc1 p hp
  · -- first-stage order
    intro ⟨p, hp, hpF⟩ U' hU'
    have hshr : ∀ U'' ∈ Fst, Dartless U'' b := by
      rcases List.mem_cons.1 hp with rfl | hp
      · rcases hord with h1 | h1
        · exact absurd h1 hpF
        · exact h1
      · exact hfo ⟨p, hp, hpF⟩
    intro x hx
    exact hshr U' hU' x.1 hx

theorem connDataL2_vine [Infinite V] {M₀ : Molecule V D₀} {C : CollData M₀} {Un : (D₀ → (Fin d → ℤ)) → Set (Src.Object Src.γL M₀)}
    {Fst : Set (Src.Object Src.γL M₀)} {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {b : HSt V D₀} (hA : AncRel M₀ b.s b.anc)
    {ps : List (Src.Object Src.γL M₀ × Quad D₀)} (hI : ConnDataL2 M₀ C Un Fst L γ η w κ b ps) (K : Step1.VineCut Src.γL b.s.M) (R : ℝ) (kp : ℕ) (U : Src.Object Src.γL M₀)
    (hU : Collected C (Un κ) L γ η w κ U) (hUK : U.atoms = K.C.atoms)
    (hUD : U.ContainsDart (b.s.down K.x₁) ∧ U.ContainsDart (b.s.down K.x₂) ∧ U.ContainsDart (b.s.down K.y₁) ∧
      U.ContainsDart (b.s.down K.y₂))
    (hUJ : (M₀.atom (b.s.down K.x₁) = U.upper ∧ M₀.atom (b.s.down K.y₁) = U.lower) ∨
      (M₀.atom (b.s.down K.x₁) = U.lower ∧ M₀.atom (b.s.down K.y₁) = U.upper))
    (hord : U ∈ Fst ∨ ∀ U' ∈ Fst, Dartless U' b)
    (hint : UIntact U b) : ConnDataL2 M₀ C Un Fst L γ η w κ (b.vinePostL K R kp)
      ((U, (b.s.down K.x₁, b.s.down K.x₂, b.s.down K.y₁, b.s.down K.y₂)) :: ps) :=
  ⟨connDataL_vine hA hI.1 K R kp U hU hUK hUD hUJ hord hint, connExtraL_vine hA hI K R kp U hUK hUJ hord hint⟩

theorem connDataL2_vineG [Infinite V] {M₀ : Molecule V D₀} {C : CollData M₀} {Un : (D₀ → (Fin d → ℤ)) → Set (Src.Object Src.γL M₀)}
    {Fst : Set (Src.Object Src.γL M₀)} {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {b : HSt V D₀} (hA : AncRel M₀ b.s b.anc)
    {ps : List (Src.Object Src.γL M₀ × Quad D₀)} (hI : ConnDataL2 M₀ C Un Fst L γ η w κ b ps) (K : Step1.VineCut Src.γL b.s.M) (U : Src.Object Src.γL M₀)
    (hU : Collected C (Un κ) L γ η w κ U) (hUK : U.atoms = K.C.atoms)
    (hUD : U.ContainsDart (b.s.down K.x₁) ∧ U.ContainsDart (b.s.down K.x₂) ∧ U.ContainsDart (b.s.down K.y₁) ∧
      U.ContainsDart (b.s.down K.y₂))
    (hUJ : (M₀.atom (b.s.down K.x₁) = U.upper ∧ M₀.atom (b.s.down K.y₁) = U.lower) ∨
      (M₀.atom (b.s.down K.x₁) = U.lower ∧ M₀.atom (b.s.down K.y₁) = U.upper))
    (hord : U ∈ Fst ∨ ∀ U' ∈ Fst, Dartless U' b)
    (hint : UIntact U b) : ConnDataL2 M₀ C Un Fst L γ η w κ (b.vinePostGL K)
      ((U, (b.s.down K.x₁, b.s.down K.x₂, b.s.down K.y₁, b.s.down K.y₂)) :: ps) :=
  ⟨connDataL_vineG hA hI.1 K U hU hUK hUD hUJ hord hint, connExtraL_vineG hA hI K U hUK hUJ hord hint⟩

end WaveTurbulence.GammaLow.FinalCount.H
