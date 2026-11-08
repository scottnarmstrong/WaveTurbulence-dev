/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.FinalMKPhase1.Rel
public import WaveTurbulence.Foundations.FinalCount.LowChain26

/-! # C1b1 MK-PHASE1 (6): the removal bookkeeping for ancestor-matched cuts (`GeomBook`)

Main's LOW bookkeeping (`ConnDataL` LowChain20, `ConnExtraL` LowChain23) records the removed pieces and is carried
along a vine step at an **intact** collected object (`connDataL_vine(G)`, `connExtraL_vine(G)`: `U.atoms = K.C.atoms`,
`anc = id` on `U`). A survivor with a pending re-cut joint is not intact: its joint at the earlier survivor is the
fresh remnant of that cut (`anc r = v`, class `α/β`). Here the bookkeeping is stated for one list of all removed pieces
(collected and survivor) and carried along an **ancestor-matched** removal `RemA` (`U.atoms = K.C.atoms.image anc`,
the node darts of `U` at its joints; `SurvCut` is exactly `RemA` for `U = E i`). The proofs are main's, with
`anc K.C.upper` in place of `K.C.upper`; injectivity of `anc` on the present atoms replaces intactness.

`GeomBook` = main's `ConnDataL ∧ ConnExtraL` without the collected-piece clauses (`PieceData`, pairwise disjointness,
first-stage order), plus `neps`: every non-`ε` atom descends from an atom of a removed piece (it is a cut remnant).
`dartless_vinePostGA`/`dartless_vinePostA`: the removed object is dartless afterwards (main's `dartless_vineSt_key`
with ancestors). -/

@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.Flower.FinalMKPhase1
open WaveTurbulence WaveTurbulence.FinalCount WaveTurbulence.FinalCountG3 WaveTurbulence.FinalCountAsm
open WaveTurbulence.VineCount WaveTurbulence.Flower.FinalMKDefs WaveTurbulence.Flower.FinalMKStep
open WaveTurbulence.LGSpine.SourceVine

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀]

section book
variable {M₀ : Molecule V D₀}

/-- The node darts of a cut, as darts of `M₀`. -/
abbrev quadK (b : HSt V D₀) (K : VineCut b.s.M) : Quad D₀ :=
  (b.s.down K.x₁, b.s.down K.x₂, b.s.down K.y₁, b.s.down K.y₂)

/-- **Ancestor-matched removal** of the object `U` of `M₀` by the cut `K` (the three clauses of `SurvCut`). -/
def RemA (M₀ : Molecule V D₀) (b : HSt V D₀) (K : VineCut b.s.M) (U : Object M₀) : Prop :=
  U.atoms = K.C.atoms.image b.anc ∧
  (U.ContainsDart (b.s.down K.x₁) ∧ U.ContainsDart (b.s.down K.x₂) ∧ U.ContainsDart (b.s.down K.y₁) ∧
    U.ContainsDart (b.s.down K.y₂)) ∧
  ((M₀.atom (b.s.down K.x₁) = U.upper ∧ M₀.atom (b.s.down K.y₁) = U.lower) ∨
    (M₀.atom (b.s.down K.x₁) = U.lower ∧ M₀.atom (b.s.down K.y₁) = U.upper))

theorem remA_of_survCut {m : ℕ} {E : Fin m → Object M₀} {i : Fin m} {b : HSt V D₀} {K : VineCut b.s.M}
    (hc : SurvCut E i b K) : RemA M₀ b K (E i) := hc

/-- An intact object cut along its own atoms is an ancestor-matched removal. -/
theorem remA_of_intact {b : HSt V D₀} (hA : AncRel M₀ b.s b.anc) (K : VineCut b.s.M) (U : Object M₀)
    (hUK : U.atoms = K.C.atoms) (hint : UIntact U b)
    (hUD : U.ContainsDart (b.s.down K.x₁) ∧ U.ContainsDart (b.s.down K.x₂) ∧ U.ContainsDart (b.s.down K.y₁) ∧
      U.ContainsDart (b.s.down K.y₂))
    (hUJ : (M₀.atom (b.s.down K.x₁) = U.upper ∧ M₀.atom (b.s.down K.y₁) = U.lower) ∨
      (M₀.atom (b.s.down K.x₁) = U.lower ∧ M₀.atom (b.s.down K.y₁) = U.upper)) : RemA M₀ b K U := by
  have hUe : ∀ v ∈ K.C.atoms, b.anc v = v := fun v hv => by
    have hv' : v ∈ U.atoms := by rw [hUK]; exact hv
    exact hA.eps v (hint v hv').1 (hint v hv').2
  refine ⟨?_, hUD, hUJ⟩
  rw [hUK]
  ext a
  rw [Finset.mem_image]
  constructor
  · intro ha; exact ⟨a, ha, hUe a ha⟩
  · rintro ⟨c, hc, rfl⟩; rw [hUe c hc]; exact hc

/-- **The geometric removal bookkeeping** for the list `rs` of all removed pieces. -/
structure GeomBook (M₀ : Molecule V D₀) (h : HSt V D₀) (rs : List (Object M₀ × Quad D₀)) : Prop where
  inj : ∀ c ∈ h.s.M.atoms, ∀ e ∈ h.s.M.atoms, h.anc c = h.anc e → c = e
  rem : ∀ p ∈ rs, ∀ a ∈ p.1.atoms, ¬ (a ∈ h.s.M.atoms ∧ h.s.cls a = .eps)
  pres : ∀ z : D₀, (∀ x : h.s.D, h.s.down x ≠ z) → ∃ p ∈ rs, z ∈ PieceKill p.1 p.2
  live : ∀ x : h.s.D, ∀ p ∈ rs, h.s.down x ∉ PieceKill p.1 p.2
  cov : ∀ v ∈ M₀.atoms, (∀ p ∈ rs, ¬ PieceInt p.1 v) →
    (∃ c ∈ h.s.M.atoms, h.anc c = v) ∨ (∀ z, M₀.atom z = v → z ∈ KillS rs)
  noint : ∀ c ∈ h.s.M.atoms, ∀ p ∈ rs, ¬ PieceInt p.1 (h.anc c)
  neps : ∀ c ∈ h.s.M.atoms, h.s.cls c ≠ .eps → ∃ p ∈ rs, h.anc c ∈ p.1.atoms

theorem geomBook_init (M₀ : Molecule V D₀) : GeomBook M₀ (HSt.init M₀) [] where
  inj := fun _ _ _ _ e => e
  rem := by simp
  pres := fun z hz => absurd rfl (hz z)
  live := by simp
  cov := fun v hv _ => Or.inl ⟨v, hv, rfl⟩
  noint := by simp
  neps := fun _ _ hc => absurd rfl hc

/-- The bookkeeping depends on the list of pieces only through its members. -/
theorem GeomBook.congr {h : HSt V D₀} {rs rs' : List (Object M₀ × Quad D₀)} (hm : ∀ p, p ∈ rs ↔ p ∈ rs')
    (hG : GeomBook M₀ h rs) : GeomBook M₀ h rs' where
  inj := hG.inj
  rem := fun p hp => hG.rem p ((hm p).2 hp)
  pres := fun z hz => by obtain ⟨p, hp, hk⟩ := hG.pres z hz; exact ⟨p, (hm p).1 hp, hk⟩
  live := fun x p hp => hG.live x p ((hm p).2 hp)
  cov := fun v hv hn => by
    rcases hG.cov v hv (fun p hp => hn p ((hm p).1 hp)) with h1 | h2
    · exact Or.inl h1
    · right; intro z hz; obtain ⟨p, hp, hk⟩ := h2 z hz; exact ⟨p, (hm p).1 hp, hk⟩
  noint := fun c hc p hp => hG.noint c hc p ((hm p).2 hp)
  neps := fun c hc hne => by obtain ⟨p, hp, hk⟩ := hG.neps c hc hne; exact ⟨p, (hm p).1 hp, hk⟩

/-- At a degree-`2` joint `j` of a cut object, every dart of `M₀` at `anc j` is killed (main's `joint_killed_of_deg2`
with ancestors). -/
theorem joint_killed_of_deg2A {b : HSt V D₀} (hA : AncRel M₀ b.s b.anc) {rs : List (Object M₀ × Quad D₀)}
    (hinj : ∀ c ∈ b.s.M.atoms, ∀ e ∈ b.s.M.atoms, b.anc c = b.anc e → c = e)
    (hpres : ∀ z : D₀, (∀ x : b.s.D, b.s.down x ≠ z) → ∃ p ∈ rs, z ∈ PieceKill p.1 p.2)
    (U : Object M₀) (N : Quad D₀) {j : V} (hj : j ∈ b.s.M.atoms) (hd : b.s.M.deg j = 2)
    {p₁ p₂ : b.s.D} (h1 : b.s.M.atom p₁ = j) (h2 : b.s.M.atom p₂ = j) (hne : p₁ ≠ p₂)
    (k1 : b.s.down p₁ ∈ PieceKill U N) (k2 : b.s.down p₂ ∈ PieceKill U N) :
    ∀ z, M₀.atom z = b.anc j → z ∈ KillS ((U, N) :: rs) := by
  intro z hz
  by_cases hx : ∃ x : b.s.D, b.s.down x = z
  · obtain ⟨x, rfl⟩ := hx
    have e1 : M₀.atom (b.s.down x) = b.anc (b.s.M.atom x) := hA.atom x
    have e2 : b.s.M.atom x = j := hinj _ (b.s.M.atom_mem x) _ hj (by rw [← e1, hz])
    rcases dart_of_deg_two b.s.M hd h1 h2 hne x e2 with rfl | rfl
    · exact ⟨(U, N), List.mem_cons_self, k1⟩
    · exact ⟨(U, N), List.mem_cons_self, k2⟩
  · push Not at hx
    obtain ⟨p, hp, hk⟩ := hpres z hx
    exact ⟨p, List.mem_cons_of_mem _ hp, hk⟩

/-- The common facts of an ancestor-matched removal, used by both step lemmas. -/
theorem RemA.facts {b : HSt V D₀} (hA : AncRel M₀ b.s b.anc)
    (hinj : ∀ c ∈ b.s.M.atoms, ∀ e ∈ b.s.M.atoms, b.anc c = b.anc e → c = e)
    {K : VineCut b.s.M} {U : Object M₀} (hR : RemA M₀ b K U) :
    (M₀.atom (b.s.down K.x₁) = b.anc K.C.upper ∧ M₀.atom (b.s.down K.x₂) = b.anc K.C.upper ∧
      M₀.atom (b.s.down K.y₁) = b.anc K.C.lower ∧ M₀.atom (b.s.down K.y₂) = b.anc K.C.lower) ∧
    ((b.anc K.C.upper = U.upper ∧ b.anc K.C.lower = U.lower) ∨
      (b.anc K.C.upper = U.lower ∧ b.anc K.C.lower = U.upper)) ∧
    (∀ c ∈ b.s.M.atoms, b.anc c ∈ U.atoms → c ∈ K.C.atoms) ∧
    (∀ c ∈ K.C.atoms, b.anc c ∈ U.atoms) := by
  obtain ⟨hUK, -, hUJ⟩ := hR
  have hup : M₀.atom (b.s.down K.x₁) = b.anc K.C.upper := by rw [hA.atom, K.Mx₁]
  have hlow : M₀.atom (b.s.down K.y₁) = b.anc K.C.lower := by rw [hA.atom, K.My₁]
  refine ⟨⟨hup, by rw [hA.atom, K.Mx₂], hlow, by rw [hA.atom, K.My₂]⟩, ?_, ?_, ?_⟩
  · rcases hUJ with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · exact Or.inl ⟨hup ▸ e1, hlow ▸ e2⟩
    · exact Or.inr ⟨hup ▸ e1, hlow ▸ e2⟩
  · intro c hc hu
    rw [hUK, Finset.mem_image] at hu
    obtain ⟨c', hc', e⟩ := hu
    rw [← hinj c' (objectAtoms_sub K.C hc') c hc e]; exact hc'
  · intro c hc; rw [hUK]; exact Finset.mem_image_of_mem _ hc

/-- **The removed object is dartless afterwards** (main's `dartless_vineSt_key` with ancestors). -/
theorem dartlessA_key {s : St.{u} V D₀} {a : V → V} (hA : AncRel M₀ s a) (hD : DartRel M₀ s)
    (hinj : ∀ c ∈ s.M.atoms, ∀ e ∈ s.M.atoms, a c = a e → c = e)
    (K : VineCut s.M) (U : Object M₀) (hUat : U.atoms = K.C.atoms.image a)
    (hdx : U.ContainsDart (s.down K.x₁) ∧ U.ContainsDart (s.down K.x₂) ∧ U.ContainsDart (s.down K.y₁) ∧
      U.ContainsDart (s.down K.y₂))
    (hUJ : (M₀.atom (s.down K.x₁) = U.upper ∧ M₀.atom (s.down K.y₁) = U.lower) ∨
      (M₀.atom (s.down K.x₁) = U.lower ∧ M₀.atom (s.down K.y₁) = U.upper))
    (y : s.D) (hP : K.cutMol.atom y ∉ K.C.atoms) (hx : U.ContainsDart (s.down y)) : False := by
  have hG := containsDart_inGroup U hx
  have hn : s.M.atom y ∈ K.C.atoms := by
    have hu : a (s.M.atom y) ∈ U.atoms := by rw [← hA.atom y]; exact hG.1
    rw [hUat, Finset.mem_image] at hu
    obtain ⟨c', hc', e⟩ := hu
    rw [← hinj c' (objectAtoms_sub K.C hc') _ (s.M.atom_mem y) e]; exact hc'
  have hup : M₀.atom (s.down K.x₁) = a K.C.upper := by rw [hA.atom, K.cut_a.2.2.1]
  have hy1a : s.M.atom K.y₁ = K.C.lower := m1_atom_of_ne K K.fa_ne_b.symm K.cut_b.2.2.1
  have hy2a : s.M.atom K.y₂ = K.C.lower := m1_atom_of_ne K K.fa_ne_b.symm K.cut_b.2.2.2.1
  have hlow : M₀.atom (s.down K.y₁) = a K.C.lower := by rw [hA.atom, hy1a]
  rcases cutMol_atom_moved K hn hP with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · have hv : a K.C.upper = U.upper ∨ a K.C.upper = U.lower := by
      rcases hUJ with ⟨e, -⟩ | ⟨e, -⟩
      · exact Or.inl (hup ▸ e)
      · exact Or.inr (hup ▸ e)
    have hza : M₀.atom (s.down y) = a K.C.upper := by rw [hA.atom, h1]
    have := cd_at_joint_eq U hv (p := s.down K.x₂) (q := s.down K.x₁) (z := s.down y)
      (by rw [hA.atom, K.cut_a.2.2.2.1]) hup hdx.2.1 hdx.1
      (by rw [hD.out]; exact K.cut_a.2.2.2.2.2.2) (by rw [hD.out]; exact K.cut_a.2.2.2.2.2.1) hza hx
    rcases this with e | e
    · exact h3 (hA.inj e)
    · exact h2 (hA.inj e)
  · have hv : a K.C.lower = U.upper ∨ a K.C.lower = U.lower := by
      rcases hUJ with ⟨-, e⟩ | ⟨-, e⟩
      · exact Or.inr (hlow ▸ e)
      · exact Or.inl (hlow ▸ e)
    have hza : M₀.atom (s.down y) = a K.C.lower := by rw [hA.atom, h1]
    have := cd_at_joint_eq U hv (p := s.down K.y₂) (q := s.down K.y₁) (z := s.down y)
      (by rw [hA.atom, hy2a]) hlow hdx.2.2.2 hdx.2.2.1
      (by rw [hD.out]; exact K.cut_b.2.2.2.2.2.2) (by rw [hD.out]; exact K.cut_b.2.2.2.2.2.1) hza hx
    rcases this with e | e
    · exact h3 (hA.inj e)
    · exact h2 (hA.inj e)

theorem dartless_vinePostGA {b : HSt V D₀} (hA : AncRel M₀ b.s b.anc) (hD : DartRel M₀ b.s)
    (hinj : ∀ c ∈ b.s.M.atoms, ∀ e ∈ b.s.M.atoms, b.anc c = b.anc e → c = e) (K : VineCut b.s.M) {U : Object M₀}
    (hR : RemA M₀ b K U) : Dartless U (b.vinePostG K) :=
  fun x hx => dartlessA_key hA hD hinj K U hR.1 hR.2.1 hR.2.2 x.1 x.2.1 hx

theorem dartless_vinePostA {b : HSt V D₀} (hA : AncRel M₀ b.s b.anc) (hD : DartRel M₀ b.s)
    (hinj : ∀ c ∈ b.s.M.atoms, ∀ e ∈ b.s.M.atoms, b.anc c = b.anc e → c = e) (K : VineCut b.s.M) (R : ℝ) (kp : ℕ)
    {U : Object M₀} (hR : RemA M₀ b K U) : Dartless U (b.vinePost K R kp) :=
  fun x hx => dartlessA_key hA hD hinj K U hR.1 hR.2.1 hR.2.2 x.1 x.2 hx

/-- The node darts of an ancestor-matched removal are killed by the new piece. -/
theorem RemA.kill {b : HSt V D₀} (hA : AncRel M₀ b.s b.anc)
    (hinj : ∀ c ∈ b.s.M.atoms, ∀ e ∈ b.s.M.atoms, b.anc c = b.anc e → c = e)
    {K : VineCut b.s.M} {U : Object M₀} (hR : RemA M₀ b K U) :
    b.s.down K.x₁ ∈ PieceKill U (quadK b K) ∧ b.s.down K.x₂ ∈ PieceKill U (quadK b K) ∧
      b.s.down K.y₁ ∈ PieceKill U (quadK b K) ∧ b.s.down K.y₂ ∈ PieceKill U (quadK b K) := by
  obtain ⟨⟨hup, hup2, hlow, hlow2⟩, -, -, hat⟩ := hR.facts hA hinj
  refine ⟨⟨by rw [hup]; exact hat _ K.a_mem, fun _ => Or.inl rfl⟩, ⟨by rw [hup2]; exact hat _ K.a_mem,
    fun _ => Or.inr (Or.inl rfl)⟩, ⟨by rw [hlow]; exact hat _ K.b_mem, fun _ => Or.inr (Or.inr (Or.inl rfl))⟩,
    ⟨by rw [hlow2]; exact hat _ K.b_mem, fun _ => Or.inr (Or.inr (Or.inr rfl))⟩⟩

end book

end WaveTurbulence.Flower.FinalMKPhase1
