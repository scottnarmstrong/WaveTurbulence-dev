/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module
public import WaveTurbulence.Foundations.Spine.SourceLocalLadder
public import WaveTurbulence.Foundations.Spine.GardenLatticeCorrespondence
public import WaveTurbulence.Foundations.Spine.GardenEnergyCorrespondence
public import WaveTurbulence.Foundations.Molecule.GardenMoleculeAxioms
public import WaveTurbulence.Foundations.Molecule.GardenIncidence
/-! # Garden decorations versus dart labellings (S3b LADDER-DECAY) -/
@[expose] public section
set_option autoImplicit false
namespace WaveTurbulence.LadderDecay
open WaveTurbulence WaveTurbulence.LGSpine

variable {w d : ℕ} (G : Garden w)

lemma bondIndex_eq_restrict {d : ℕ} (z : GNode G.tree → (Fin d → ℤ)) :
    bondIndex G z = Mole.restrictLabels G z := by
  funext x
  rcases x with ⟨c, b⟩ | l <;> rfl


lemma latticePoint_comb {d : ℕ} (L : ℝ) (a b c : Fin d → ℤ) :
    latticePoint L (a - b + c) = latticePoint L a - latticePoint L b + latticePoint L c := by
  ext j
  simp [latticePoint, add_div, sub_div]

lemma latticePoint_injective {d : ℕ} {L : ℝ} (hL : L ≠ 0) : Function.Injective (latticePoint (d := d) L) := by
  intro a b h
  funext j
  have := congrArg (fun v : Mom d => v j) h
  simp only [latticePoint] at this
  exact_mod_cast (div_left_inj' hL).mp this

variable (L : ℝ) (base : Mom d) (roots : Fin w → (Fin d → ℤ))

/-- The root vectors `base + n_i / L`. -/
noncomputable def rootVec : Fin w → Mom d := fun i => base + latticePoint L (roots i)

variable {G}
/-- Integer decorations of the molecule with the garden's root boundary. -/
abbrev DecLab (hP : G.IsPlain) :=
  {k : GardenDart G → (Fin d → ℤ) //
    G.molecule.IsDecoration L base (Mole.gardenSource G hP (rootVec L base roots)) k}


lemma isDecoration_coset {z : GNode G.tree → (Fin d → ℤ)} (hz : IsDecoration G z) :
    IsDecoration G (fun a => base + latticePoint L (z a)) := by
  refine ⟨fun b => ?_, fun l => ?_⟩
  · have := hz.1 b
    simp only [this, latticePoint_comb]
    abel
  · simp only [hz.2 l]

variable (hP : G.IsPlain)

/-- Integer node labels of the extension of a dart labelling. -/
noncomputable def zOfLab (k : GardenDart G → (Fin d → ℤ)) (a : GNode G.tree) : Fin d → ℤ :=
  Classical.choose (Mole.extendLabels_mem_affineLattice G hP L base (rootVec L base roots)
      (Molecule.kvec L base k) (fun i => ⟨roots i, rfl⟩) (fun x => ⟨k x, rfl⟩) a)

lemma zOfLab_spec (k : GardenDart G → (Fin d → ℤ)) (a : GNode G.tree) :
    Mole.extendLabels G hP (rootVec L base roots) (Molecule.kvec L base k) a =
      base + latticePoint L (zOfLab L base roots hP k a) :=
  Classical.choose_spec (Mole.extendLabels_mem_affineLattice G hP L base (rootVec L base roots)
      (Molecule.kvec L base k) (fun i => ⟨roots i, rfl⟩) (fun x => ⟨k x, rfl⟩) a)

lemma zOfLab_decoration (hL : L ≠ 0) (hn : Mole.RootPairCompatible G (rootVec L base roots))
    (k : DecLab L base roots hP) : IsDecoration G (zOfLab L base roots hP k.1) ∧
      ∀ j, zOfLab L base roots hP k.1 (GNode.root G.tree j) = roots j := by
  have hk := Mole.gardenDecoration_of_molecule G hP (rootVec L base roots) hn L base k.1 k.2
  have sp := zOfLab_spec L base roots hP k.1
  have inj := latticePoint_injective (d := d) hL
  refine ⟨⟨fun b => ?_, fun l => ?_⟩, fun j => ?_⟩
  · have h := hk.1.1 b
    rw [sp, sp, sp, sp] at h
    apply inj
    rw [latticePoint_comb]
    have h2 : latticePoint L (zOfLab L base roots hP k.1 b.toNode) =
        latticePoint L (zOfLab L base roots hP k.1 (b.child 0)) -
        latticePoint L (zOfLab L base roots hP k.1 (b.child 1)) +
        latticePoint L (zOfLab L base roots hP k.1 (b.child 2)) := by
      have := congrArg (fun v => v - base) h
      calc _ = (base + latticePoint L (zOfLab L base roots hP k.1 b.toNode)) - base := by abel
        _ = _ := by rw [this]; abel
    exact h2
  · have h := hk.1.2 l
    rw [sp, sp] at h
    exact inj (add_left_cancel h)
  · have h := hk.2.1 j
    rw [sp] at h
    exact inj (add_left_cancel h)

/-- Garden decorations with fixed roots correspond to molecule decorations with the root
boundary vector (F52 root-pair compatibility assumed). -/
noncomputable def decEquiv (hL : L ≠ 0) (hn : Mole.RootPairCompatible G (rootVec L base roots)) :
    GenDecoration G d roots 0 ≃ DecLab L base roots hP where
  toFun z := ⟨bondIndex G z.1, by
    rw [bondIndex_eq_restrict]
    exact Mole.moleculeDecoration_of_garden G hP (rootVec L base roots) hL base z.1
      (isDecoration_coset L base z.2.1) (fun i => by rw [z.2.2.1 i]; rfl)⟩
  invFun k := ⟨zOfLab L base roots hP k.1, (zOfLab_decoration L base roots hP hL hn k).1,
    (zOfLab_decoration L base roots hP hL hn k).2,
    fun l hl => absurd hl (by unfold Garden.IsFlower; rw [hP l]; simp)⟩
  left_inv z := by
    apply Subtype.ext
    funext a
    have inj := latticePoint_injective (d := d) hL
    have sp := zOfLab_spec L base roots hP (bondIndex G z.1) a
    have hrest : Mole.restrictLabels G (fun a => base + latticePoint L (z.1 a)) =
        Molecule.kvec L base (bondIndex G z.1) := by
      funext x
      rw [bondIndex_eq_restrict]; rfl
    have hext := Mole.extend_restrictLabels G hP (rootVec L base roots)
      (fun a => base + latticePoint L (z.1 a)) (fun i => by rw [z.2.2.1 i]; rfl)
      (fun l => by simp only [z.2.1.2 l])
    rw [hrest] at hext
    rw [hext] at sp
    exact (inj (add_left_cancel sp)).symm
  right_inv k := by
    apply Subtype.ext
    funext x
    have inj := latticePoint_injective (d := d) hL
    have sp := zOfLab_spec L base roots hP k.1 (Mole.dartNode G x)
    have hr := Mole.restrict_extendLabels G hP (rootVec L base roots) (Molecule.kvec L base k.1)
      (fun y => by simp only [Molecule.kvec, k.2.1 y])
    have hx := congrFun hr x
    change Mole.extendLabels G hP (rootVec L base roots) (Molecule.kvec L base k.1)
      (Mole.dartNode G x) = Molecule.kvec L base k.1 x at hx
    rw [hx] at sp
    show bondIndex G (zOfLab L base roots hP k.1) x = k.1 x
    rw [bondIndex_eq_restrict]
    change zOfLab L base roots hP k.1 (Mole.dartNode G x) = k.1 x
    exact (inj (add_left_cancel sp)).symm

end WaveTurbulence.LadderDecay
