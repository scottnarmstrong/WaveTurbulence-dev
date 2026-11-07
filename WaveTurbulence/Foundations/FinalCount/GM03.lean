/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.GM02
public import WaveTurbulence.Foundations.FinalCount.G3ChainEnds
/-! **FINALCOUNT-G3: `FinalShape` for a component** (third part: cycles and chains), and the assembly
`finalShape_compL`. -/
@[expose] public section
open WaveTurbulence.VineParamContract
set_option autoImplicit false
set_option linter.unusedSectionVars false
open Finset Classical
namespace WaveTurbulence.FinalCountG3
open WaveTurbulence WaveTurbulence.FinalCount

universe u
variable {V : Type*} [DecidableEq V] {D₀ : Type u} [Fintype D₀] [DecidableEq D₀] {d : ℕ}
variable {L γ η : ℝ} {w : Mom d} {κ : D₀ → (Fin d → ℤ)} {R : ℕ} {Tm : V → Prop} {hf : HSt V D₀}

section shape3
variable (hC : Prop95ConclAtL L γ η w κ R hf Tm) {a₀ : V} (ha₀ : a₀ ∈ hf.s.M.atoms)
include hC ha₀

theorem shape_cycleL (hE : LowFree hf a₀) : (∀ a ∈ (compMol hf.s.M a₀).atoms, (compMol hf.s.M a₀).deg a = 2) →
    (compMol hf.s.M a₀).atoms.card = 2 ∨ 4 ≤ (compMol hf.s.M a₀).atoms.card ∨
      ((compMol hf.s.M a₀).atoms.card = 3 ∧
        (G8Copy.alphaAtoms (compMol hf.s.M a₀).atoms (fun a => toCls (hf.s.cls a))).card ≤ 1) := by
  intro h2
  have hev : EvenComp hf.s.M a₀ := by
    intro b hb hsc
    have hm : b ∈ (compMol hf.s.M a₀).atoms := (mem_compMol _ _).2 ⟨hb, hsc⟩
    have := h2 b hm
    rw [compMol_deg _ _ hsc] at this
    rw [this]; exact even_two
  have hne : ∀ b ∈ compAtoms hf.s.M a₀, hf.s.cls b ≠ .eps := by
    intro b hb hc
    have hm : b ∈ (compMol hf.s.M a₀).atoms := hb
    have h := (mem_compMol _ _).1 hm
    have := h2 b hm
    rw [compMol_deg _ _ h.2] at this
    have := hE b (Finset.mem_filter.2 h) hc
    omega
  have hcy := hC.cycles a₀ ha₀ hev hne
  unfold CycleShape at hcy
  have hal : G8Copy.alphaAtoms (compMol hf.s.M a₀).atoms (fun a => toCls (hf.s.cls a)) =
      (compAtoms hf.s.M a₀).filter fun c => ∃ ρ kp, hf.s.cls c = .alpha ρ kp := by
    unfold G8Copy.alphaAtoms
    rw [compMol_atoms]
    exact Finset.filter_congr fun c _ => toCls_isAlpha
  rw [hal, compMol_atoms]
  exact hcy

theorem chainOf_eqL {K : Finset V} (hK : G8Copy.IsChainSet (compMol hf.s.M a₀) (fun a => toCls (hf.s.cls a)) K)
    {a : V} (ha : a ∈ K) : chainOf hf.s a = K := by
  obtain ⟨-, hKC, hne, hcl, hcon⟩ := hK
  have hnE : ∀ v ∈ K, hf.s.cls v ≠ .eps := fun v hv h => hne v hv (toCls_isEps.2 h)
  ext c
  rw [mem_chainOf]
  constructor
  · rintro ⟨hcm, hcne, hr⟩
    have : ∀ y, Relation.ReflTransGen (fun x y => hf.s.M.Adj x y ∧ hf.s.cls y ≠ .eps) a y → y ∈ K := by
      intro y hy
      induction hy with
      | refl => exact ha
      | @tail b y' hab hs ih =>
        have hbK := ih
        have hbC := (mem_compMol _ _).1 (hKC hbK)
        obtain ⟨z, hz1, hz2⟩ := hs.1
        have hAdj : (compMol hf.s.M a₀).Adj b y' := by
          refine ⟨⟨z, ?_⟩, hz1, hz2⟩
          show hf.s.M.SameComponent a₀ (hf.s.M.atom z)
          rw [hz1]; exact hbC.2
        exact hcl b hbK y' hAdj (fun h => hs.2 (toCls_isEps.1 h))
    exact this c hr
  · intro hc
    have hcC := (mem_compMol _ _).1 (hKC hc)
    refine ⟨hcC.1, hnE c hc, ?_⟩
    have key : ∀ u v, Relation.EqvGen (fun a b => a ∈ K ∧ b ∈ K ∧ (compMol hf.s.M a₀).Adj a b) u v →
        Relation.ReflTransGen (fun x y => x ∈ K ∧ y ∈ K ∧ hf.s.M.Adj x y) u v := by
      have hsym : ∀ x y, (x ∈ K ∧ y ∈ K ∧ hf.s.M.Adj x y) → (y ∈ K ∧ x ∈ K ∧ hf.s.M.Adj y x) := by
        rintro x y ⟨hx, hy, z, hz1, hz2⟩
        exact ⟨hy, hx, hf.s.M.mate z, hz2, by rw [hf.s.M.mate_mate]; exact hz1⟩
      haveI : Std.Symm (fun x y => x ∈ K ∧ y ∈ K ∧ hf.s.M.Adj x y) := ⟨fun x y h => hsym x y h⟩
      intro u v h
      induction h with
      | rel x y hxy =>
        obtain ⟨hx, hy, ⟨z, hz1, hz2⟩⟩ := hxy
        exact Relation.ReflTransGen.single ⟨hx, hy, z.1, hz1, hz2⟩
      | refl x => exact Relation.ReflTransGen.refl
      | symm x y _ ih => exact Relation.ReflTransGen.stdSymm.symm _ _ ih
      | trans x y z _ _ ih1 ih2 => exact ih1.trans ih2
    have := key a c (hcon a ha c hc)
    have goal : ∀ y, Relation.ReflTransGen (fun x y => x ∈ K ∧ y ∈ K ∧ hf.s.M.Adj x y) a y →
        Relation.ReflTransGen (fun x y => hf.s.M.Adj x y ∧ hf.s.cls y ≠ .eps) a y := by
      intro y hy
      induction hy with
      | refl => exact Relation.ReflTransGen.refl
      | tail _ h ih => exact ih.tail ⟨h.2.2, hnE _ h.2.1⟩
    exact goal c this

theorem shape_chainsL (hT : TameFree hf Tm a₀) (hE : LowFree hf a₀) (hn : ¬ CompOddL hf a₀) : (¬ ∀ a ∈ (compMol hf.s.M a₀).atoms, (compMol hf.s.M a₀).deg a = 2) →
    ∀ K, G8Copy.IsChainSet (compMol hf.s.M a₀) (fun a => toCls (hf.s.cls a)) K →
    ∃ y₁ y₂, G8Copy.crossDarts (compMol hf.s.M a₀) K = {y₁, y₂} ∧ y₁ ≠ y₂ ∧
      (toCls (hf.s.cls ((compMol hf.s.M a₀).atom ((compMol hf.s.M a₀).mate y₁)))).IsEps ∧
      (toCls (hf.s.cls ((compMol hf.s.M a₀).atom ((compMol hf.s.M a₀).mate y₂)))).IsEps ∧
      (compMol hf.s.M a₀).atom ((compMol hf.s.M a₀).mate y₁) ≠ (compMol hf.s.M a₀).atom ((compMol hf.s.M a₀).mate y₂) := by
  intro hnot K hK
  obtain ⟨⟨a, haK⟩, hKC, hne, hcl, hcon⟩ := hK
  have hK' := (⟨⟨a, haK⟩, hKC, hne, hcl, hcon⟩ : G8Copy.IsChainSet (compMol hf.s.M a₀) (fun a => toCls (hf.s.cls a)) K)
  have haC := (mem_compMol _ _).1 (hKC haK)
  have hnE : hf.s.cls a ≠ .eps := fun h => hne a haK (toCls_isEps.2 h)
  have hev : EvenComp hf.s.M a := by
    intro b hb hsc
    have hm : b ∈ (compMol hf.s.M a₀).atoms :=
      (mem_compMol _ _).2 ⟨hb, Relation.EqvGen.trans _ _ _ haC.2 hsc⟩
    have := shape_evenDegL hC ha₀ hn b hm
    rw [compMol_deg _ _ ((mem_compMol _ _).1 hm).2] at this
    rcases this with e | e <;> rw [e] <;> decide
  have hex : ∃ b ∈ compAtoms hf.s.M a, hf.s.cls b = .eps := by
    push_neg at hnot
    obtain ⟨b, hb, hb2⟩ := hnot
    have hbm := (mem_compMol _ _).1 hb
    have h4 := shape_evenDegL hC ha₀ hn b hb
    have hc := (shape_classesL hC ha₀ hE b hb)
    refine ⟨b, ?_, ?_⟩
    · exact (Finset.mem_filter.2 ⟨hbm.1, Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ haC.2) hbm.2⟩)
    · by_contra hcn
      have : ¬ (toCls (hf.s.cls b)).IsEps := fun h => hcn (toCls_isEps.1 h)
      have := hc.2 this
      omega
  obtain ⟨d₁, d₂, h12, hd1, hd2, he1, he2, hdist, hall⟩ := hC.chains a haC.1 hev hnE hex (hT.of_sc haC.2)
    (fun e he hce => hE e (Finset.mem_filter.2 ⟨(Finset.mem_filter.1 he).1,
      Relation.EqvGen.trans _ _ _ haC.2 (Finset.mem_filter.1 he).2⟩) hce)
  rw [chainOf_eqL hC ha₀ hK' haK] at hd1 hd2 hall
  have hP1 : compP hf.s.M a₀ (hf.s.M.atom d₁) := (mem_compMol _ _).1 (hKC hd1) |>.2
  have hP2 : compP hf.s.M a₀ (hf.s.M.atom d₂) := (mem_compMol _ _).1 (hKC hd2) |>.2
  have hout : ∀ e, hf.s.cls (hf.s.M.atom (hf.s.M.mate e)) = .eps → hf.s.M.atom (hf.s.M.mate e) ∉ K :=
    fun e he hm => hne _ hm (toCls_isEps.2 he)
  refine ⟨⟨d₁, hP1⟩, ⟨d₂, hP2⟩, ?_, ?_, toCls_isEps.2 he1, toCls_isEps.2 he2, hdist⟩
  · ext z
    simp only [G8Copy.crossDarts, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert,
      Finset.mem_singleton]
    constructor
    · rintro ⟨hz1, hz2⟩
      rcases hall z.1 hz1 hz2 with e | e
      · left; exact Subtype.ext e
      · right; exact Subtype.ext e
    · rintro (rfl | rfl)
      · exact ⟨hd1, hout _ he1⟩
      · exact ⟨hd2, hout _ he2⟩
  · intro h; exact h12 (congrArg Subtype.val h)

/-- **`FinalShape` for every component of the final molecule** (the `R = 1` case of Prop 9.5, as in G8's Prop 9.6). -/
theorem finalShape_compL (hR : CompOddL hf a₀ → R = 1) (hT : TameFree hf Tm a₀) (hE : LowFree hf a₀) :
    G8Copy.FinalShape (compMol hf.s.M a₀) (fun a => toCls (hf.s.cls a)) (CompOddL hf a₀) where
  nonempty := shape_nonemptyL hC ha₀
  caps := shape_capsL hC ha₀
  noLoop := shape_noLoopL hC ha₀
  conn := shape_connL hC ha₀
  degPos := shape_degPosL hC ha₀
  classes := shape_classesL hC ha₀ hE
  dir2 := shape_dir2L hC ha₀ hE
  oddDeg := fun hod => shape_oddDegL hC ha₀ (hR hod) hod
  evenDeg := shape_evenDegL hC ha₀
  noTriple := shape_noTripleL hC ha₀
  evenBeta := shape_evenBetaL hC ha₀ hE
  cycle := shape_cycleL hC ha₀ hE
  chains := shape_chainsL hC ha₀ hT hE

end shape3

end WaveTurbulence.FinalCountG3
