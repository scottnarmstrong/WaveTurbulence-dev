/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.FinalCount.GL20
public import WaveTurbulence.Foundations.GammaLow.FinalCount.H.TV.Invariance
public import WaveTurbulence.Foundations.FinalCount.AtMapVine
/-! # H-DS: T-vine transport along main's group embeddings `GEmb` (packet L6-HDS; hand-written)

Main's `FinalCountG3.GEmb.isVine_iff` transports a vine of a drawn type along a group embedding (used for the loop-free
restriction `unloop`); the T-vine form is L6-HTV's `isTVine_iff_of_groupBonds_eq` with `GEmb.groupBonds_eq` and
`GEmb.isBlock_iff`. -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.GammaLow.FinalCount.H.DS
open WaveTurbulence.FinalCountG3

variable {V : Type*} [DecidableEq V] {D1 D2 : Type*} [Fintype D1] [DecidableEq D1] [Fintype D2] [DecidableEq D2]

/-- T-vine form of `GEmb.isVine_iff`. -/
theorem gEmb_isTVine_iff {M1 : Molecule V D1} {M2 : Molecule V D2} {ι : D1 → D2} {S : Finset V}
    (G : GEmb M1 M2 ι S) (hat : M1.atoms = M2.atoms) {j₁ j₂ : V} : M2.IsTVine S j₁ j₂ ↔ M1.IsTVine S j₁ j₂ :=
  TV.isTVine_iff_of_groupBonds_eq G.groupBonds_eq (G.isBlock_iff hat)

section mapAtoms
open WaveTurbulence.AtomTransport WaveTurbulence.MoleProp
variable {V W D : Type*} [DecidableEq V] [DecidableEq W] [Fintype D] [DecidableEq D]

/-- T-vine form of main's `mapAtoms_isVine` (relabelling the atoms by an embedding). -/
theorem mapAtoms_isTVine (M : Molecule V D) (ι : V ↪ W) (S : Finset V) (j₁ j₂ : V) :
    (mapAtoms M ι).IsTVine (S.map ι) (ι j₁) (ι j₂) ↔ M.IsTVine S j₁ j₂ := by
  classical
  constructor
  · intro h
    let g : W → V := Function.extend ι id (fun _ => j₁)
    have hg : ∀ v, g (ι v) = v := fun v => ι.injective.extend_apply id _ v
    have hinj : Set.InjOn g ↑(S.map ι) := by
      intro x hx y hy hxy
      obtain ⟨u, -, rfl⟩ := Finset.mem_map.mp hx
      obtain ⟨v, -, rfl⟩ := Finset.mem_map.mp hy
      rw [hg, hg] at hxy
      rw [hxy]
    have himg : S = (S.map ι).image g := by
      ext v
      simp [Finset.mem_image, hg]
    have hgb : M.groupBonds S = ((mapAtoms M ι).groupBonds (S.map ι)).map (Sym2.map g) := by
      rw [mapAtoms_groupBonds, Multiset.map_map]
      have : (Sym2.map g ∘ Sym2.map ι) = id := by
        funext e
        simp only [Function.comp_apply, Sym2.map_map, id, hg]
        exact congrFun Sym2.map_id' e
      rw [this, Multiset.map_id]
    have hB : M.IsBlock S (g (ι j₁)) (g (ι j₂)) := by
      rw [hg, hg]; exact (mapAtoms_isBlock M ι S j₁ j₂).mp h.1
    have := TV.isTVine_map_of_groupBonds hinj himg hgb hB h
    rwa [hg, hg] at this
  · intro h
    exact TV.isTVine_map_of_groupBonds ι.injective.injOn (Finset.map_eq_image ι S) (mapAtoms_groupBonds M ι S)
      ((mapAtoms_isBlock M ι S j₁ j₂).mpr h.1) h

/-- The enlarged family is invariant under relabelling the atoms. -/
theorem mapAtoms_isVineEnl (M : Molecule V D) (ι : V ↪ W) (S : Finset V) (j₁ j₂ : V) :
    (mapAtoms M ι).IsVineEnl (S.map ι) (ι j₁) (ι j₂) ↔ M.IsVineEnl S j₁ j₂ := by
  unfold Molecule.IsVineEnl
  rw [mapAtoms_isVine M ι .I, mapAtoms_isVine M ι .II, mapAtoms_isTVine M ι]

end mapAtoms

end WaveTurbulence.GammaLow.FinalCount.H.DS
