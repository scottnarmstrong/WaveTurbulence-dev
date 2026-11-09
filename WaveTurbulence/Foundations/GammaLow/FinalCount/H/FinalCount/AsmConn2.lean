/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.AsmConn2
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmConn1
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.FinalCount.AsmVN15
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.Api
/-! **L6-H port of main `WaveTurbulence.Foundations.FinalCount.AsmConn2`** (sha256 in H/COPIED-SHA256SUMS): only the declarations that
depend on the vine-family carrier, re-stated over the low family `Src … Src.γL` (and L6-STEP1's
`Step1.VineCut Src.γL`); everything else is main's, by import.

 **FINALCOUNT-ASSEMBLY (hconn0, part 2): lifting the M₀-level host connectivity to the state.**
`hconn0_of_hostConn`: for an intact collected three-atom object, every `DoubleShape` cut `K'` over its atoms has the joints joined
outside the group darts (`VineOutsideConn`).  The M₀ chain of `HostConn` (named input of S4-SHAPE) avoids the killed darts of the
removed pieces (`ConnInv`), so all its bonds are present in the state, and `anc` is injective on the state atoms. -/
@[expose] public section
open WaveTurbulence.Induct
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.GammaLow.FinalCount.H
open WaveTurbulence.FinalCountAsm
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.LGSpine WaveTurbulence.LGSpine.SourceVine

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}

theorem hconn0_of_hostConn [Infinite V] {M₀ : Molecule V D₀} {C : CollData M₀} {Un : (D₀ → (Fin d → ℤ)) → Set (Src.Object Src.γL M₀)}
    {Fst : Set (Src.Object Src.γL M₀)} {L γ η : ℝ} {w : Mom d} {A0 : Set (D₀ → (Fin d → ℤ))} {κ : D₀ → (Fin d → ℤ)} (hHC : HostConn M₀ C Un L γ η w A0) (hκ : κ ∈ A0)
    {h : HSt V D₀} (hA : AncRel M₀ h.s h.anc) (hD : DartRel M₀ h.s) (hI : ConnInv M₀ C Un Fst L γ η w κ h)
    {U : Src.Object Src.γL M₀} (hUc : Collected C (Un κ) L γ η w κ U) (hint : UIntact U h) {K : Step1.VineCut Src.γL h.s.M}
    (hKat : K.C.atoms = U.atoms) :
    ∀ K' : Step1.VineCut Src.γL h.s.M, K'.C.atoms = K.C.atoms → Nonempty (Step1.DoubleShape K') →
      ∃ G : Finset h.s.D, (∀ z ∈ ({K'.x₁, K'.x₂, K'.y₁, K'.y₂} : Finset h.s.D), z ∈ G) ∧ VineOutsideConn K' G := by
  intro K' hK'at ⟨S⟩
  refine ⟨{K'.x₁, K'.x₂, K'.y₁, K'.y₂}, fun z hz => hz, ?_⟩
  obtain ⟨ps, hinj, hps, hpw, hrem, hpres, -, -, -, -⟩ := hI
  set a := K'.C.upper with ha
  set b := K'.C.lower with hb
  set x := S.x with hx
  have hUat : U.atoms = {a, x, b} := by rw [← hKat, ← hK'at]; exact S.atoms_eq
  have hax : a ≠ x := S.x_ne_a.symm
  have hxb : x ≠ b := S.x_ne_b
  have hab : a ≠ b := K'.ab_ne
  have hmem : ∀ v ∈ ({a, x, b} : Finset V), v ∈ h.s.M.atoms ∧ h.s.cls v = .eps := fun v hv => hint v (hUat ▸ hv)
  have hancε : ∀ v ∈ ({a, x, b} : Finset V), h.anc v = v := fun v hv => hA.eps v (hmem v hv).1 (hmem v hv).2
  have haM : a ∈ ({a, x, b} : Finset V) := by simp
  have hxM : x ∈ ({a, x, b} : Finset V) := by simp
  have hbM : b ∈ ({a, x, b} : Finset V) := by simp
  -- closure of the darts at x
  have hclos : ∀ z, M₀.atom z = x → M₀.atom (M₀.mate z) = a ∨ M₀.atom (M₀.mate z) = b := by
    intro z hz
    obtain ⟨x', hx'⟩ := hA.surj x (hmem x hxM).1 (hmem x hxM).2 z hz
    have h1 : h.anc (h.s.M.atom x') = x := by rw [← hA.atom x', hx', hz]
    have h2 : h.s.M.atom x' = x := hA.uniq _ (h.s.M.atom_mem x') x (hmem x hxM).1 (hmem x hxM).2 h1
    have h3 : x' ∈ h.s.M.dartsAt x := (Mole.mem_dartsAt _ _ _).2 h2
    rw [S.darts_x] at h3
    have hm : M₀.atom (M₀.mate z) = h.anc (h.s.M.atom (h.s.M.mate x')) := by
      rw [← hx', hD.mate, hA.atom]
    simp only [Finset.mem_insert, Finset.mem_singleton] at h3
    rcases h3 with e | e | e | e <;> rw [e, h.s.M.mate_mate] at hm
    · left; rw [hm, K'.Mx₁, hancε a haM]
    · left; rw [hm, K'.Mx₂, hancε a haM]
    · right; rw [hm, K'.My₁, hancε b hbM]
    · right; rw [hm, K'.My₂, hancε b hbM]
  have hdis : ∀ p ∈ ps, Disjoint p.1.atoms U.atoms := fun p hp =>
    Finset.disjoint_left.2 fun v hv hvU => hrem p hp v hv (hint v hvU)
  have hconn := hHC κ hκ ps U a x b hps hpw hdis hUc hUat hax hxb hab hclos
  -- the lift
  let σ : V → V := fun s => if hs : ∃ c ∈ h.s.M.atoms, h.anc c = s then Classical.choose hs else s
  have hσ : ∀ c ∈ h.s.M.atoms, σ (h.anc c) = c := by
    intro c hc
    have hs : ∃ c' ∈ h.s.M.atoms, h.anc c' = h.anc c := ⟨c, hc, rfl⟩
    simp only [σ, dif_pos hs]
    exact hinj _ (Classical.choose_spec hs).1 _ hc (Classical.choose_spec hs).2
  have hint' : ∀ c ∈ vineInterior K', c = x := by
    intro c hc
    simp only [vineInterior, Finset.mem_sdiff, Finset.mem_insert, Finset.mem_singleton, not_or] at hc
    rw [S.atoms_eq] at hc
    simp only [Finset.mem_insert, Finset.mem_singleton] at hc
    rcases hc with ⟨hc | hc | hc, h1, h2⟩
    · exact absurd hc h1
    · exact hc
    · exact absurd hc h2
  have hxint : x ∈ vineInterior K' := by
    unfold vineInterior
    rw [S.atoms_eq]
    refine Finset.mem_sdiff.2 ⟨Finset.mem_insert_of_mem (Finset.mem_insert_self _ _), ?_⟩
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hax.symm, hxb⟩
  -- mate darts at x
  have hxd : ∀ y : h.s.D, y ∈ ({K'.x₁, K'.x₂, K'.y₁, K'.y₂} : Finset h.s.D) → h.s.M.atom (h.s.M.mate y) = x := by
    intro y hy
    have : h.s.M.mate y ∈ h.s.M.dartsAt x := by
      rw [S.darts_x]
      simp only [Finset.mem_insert, Finset.mem_singleton] at hy ⊢
      rcases hy with e | e | e | e <;> simp [e]
    exact (Mole.mem_dartsAt _ _ _).1 this
  have hxd' : ∀ y : h.s.D, h.s.M.mate y ∈ ({K'.x₁, K'.x₂, K'.y₁, K'.y₂} : Finset h.s.D) → h.s.M.atom y = x := by
    intro y hy
    have := hxd _ hy
    rwa [h.s.M.mate_mate] at this
  have hstep : ∀ s t, Relation.EqvGen (fun s t : V => ∃ z, M₀.atom z = s ∧ M₀.atom (M₀.mate z) = t ∧
      z ∉ ((⋃ p ∈ ps, PieceKill p.1 p.2) ∪ {z | M₀.atom z = x}) ∧
      M₀.mate z ∉ ((⋃ p ∈ ps, PieceKill p.1 p.2) ∪ {z | M₀.atom z = x})) s t →
      Relation.EqvGen (fun s t : V => s ∉ vineInterior K' ∧ t ∉ vineInterior K' ∧
        ∃ z, h.s.M.atom z = s ∧ h.s.M.atom (h.s.M.mate z) = t ∧ z ∉ ({K'.x₁, K'.x₂, K'.y₁, K'.y₂} : Finset h.s.D) ∧
          h.s.M.mate z ∉ ({K'.x₁, K'.x₂, K'.y₁, K'.y₂} : Finset h.s.D)) (σ s) (σ t) := by
    intro s t hst
    induction hst with
    | rel s t hr =>
      obtain ⟨z, hs, ht, hz, hmz⟩ := hr
      have hpr : ∀ z' : D₀, z' ∉ ((⋃ p ∈ ps, PieceKill p.1 p.2) ∪ {z | M₀.atom z = x}) → ∃ x₀ : h.s.D, h.s.down x₀ = z' := by
        intro z' hz'
        by_contra hno
        push Not at hno
        obtain ⟨p, hp, hk⟩ := hpres z' hno
        exact hz' (Or.inl (Set.mem_iUnion₂.2 ⟨p, hp, hk⟩))
      obtain ⟨x₀, hx₀⟩ := hpr z hz
      have hz1 : M₀.atom z ≠ x := fun e => hz (Or.inr e)
      have hz2 : M₀.atom (M₀.mate z) ≠ x := fun e => hmz (Or.inr e)
      have hc1 : h.anc (h.s.M.atom x₀) = s := by rw [← hs, ← hx₀, hA.atom]
      have hc2 : h.anc (h.s.M.atom (h.s.M.mate x₀)) = t := by rw [← ht, ← hx₀, hD.mate, hA.atom]
      have hs1 : σ s = h.s.M.atom x₀ := by rw [← hc1]; exact hσ _ (h.s.M.atom_mem x₀)
      have ht1 : σ t = h.s.M.atom (h.s.M.mate x₀) := by rw [← hc2]; exact hσ _ (h.s.M.atom_mem _)
      rw [hs1, ht1]
      have hne : ∀ c ∈ h.s.M.atoms, h.anc c ≠ x → c ∈ h.s.M.atoms → c ∈ vineInterior K' → False := by
        intro c _ hcx _ hci
        have := hint' c hci
        subst this
        exact hcx (hancε _ hxM)
      refine Relation.EqvGen.rel _ _ ⟨fun hci => hne _ (h.s.M.atom_mem _) (by rw [hc1]; exact fun e => hz1 (hs.trans e)) (h.s.M.atom_mem _) hci,
        fun hci => hne _ (h.s.M.atom_mem _) (by rw [hc2]; exact fun e => hz2 (ht.trans e)) (h.s.M.atom_mem _) hci, x₀, rfl, rfl, ?_, ?_⟩
      · intro hG
        apply hne _ (h.s.M.atom_mem (h.s.M.mate x₀)) (by rw [hc2]; exact fun e => hz2 (ht.trans e)) (h.s.M.atom_mem _)
        rw [hxd x₀ hG]; exact hxint
      · intro hG
        apply hne _ (h.s.M.atom_mem x₀) (by rw [hc1]; exact fun e => hz1 (hs.trans e)) (h.s.M.atom_mem _)
        rw [hxd' x₀ hG]; exact hxint
    | refl s => exact Relation.EqvGen.refl _
    | symm s t _ ih => exact Relation.EqvGen.symm _ _ ih
    | trans s t u _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2
  have := hstep a b hconn
  have e1 : σ a = a := by have := hσ a (hmem a haM).1; rwa [hancε a haM] at this
  have e2 : σ b = b := by have := hσ b (hmem b hbM).1; rwa [hancε b hbM] at this
  rw [e1, e2] at this
  exact this

end WaveTurbulence.GammaLow.FinalCount.H
