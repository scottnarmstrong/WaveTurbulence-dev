/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtCut.CutTermTime
public import WaveTurbulence.Foundations.Flower.ProtCut.PairLeaves
public import WaveTurbulence.Foundations.Flower.ProtCut.CutSum

/-! # D2c PROT-CUT: the terminal pin, one decoration at a time

* Exceptional data at the cut: the star momenta `starA`, `starB` of `𝔫_a`, `𝔫_b`, the linked frequency `cutFreq`,
  the `ε` factor `cutEps`.
* The direct node maps `ιP`, `ιI`, `ιR`, `ιG` of the four pieces into the protected tree, the piece profiles
  `Hp`, `Hi`, `Hr`, `Hg`, and the node-local factorization hypothesis `MultFactors` of the decoration multiplier.
* `CutTermData.Φ`: decorations of the protected tree ≃ prefix × (exceptional data × interior × red × green).
* **`summand_eq`**: the summand of `kernelProt` at a decoration is
  `c_e · ∫_{cutU} e^{πi A_e (u - s)} · S_pre(u) · S_in(u) · S_r(u) · S_g(u) du` (o73 (13.1) at one decoration). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory

namespace WaveTurbulence.Flower.ProtCut

open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234
open WaveTurbulence.Flower.ProtDefs

/-- Addresses of the star of `𝔫_a` (the node, then its three children). -/
def aAddr (Xp : RegChain) : Fin 4 → Fin 1 × Path :=
  Fin.cases ((0 : Fin 1), Xp.lonePath) fun i => ((0 : Fin 1), Xp.lonePath ++ [i])

/-- Addresses of the star of `𝔫_b`. -/
def bAddr (Xp : RegChain) (m : MiniTreeCode) (inner : RegChain) : Fin 4 → Fin 1 × Path :=
  Fin.cases ((0 : Fin 1), Xp.lonePath ++ bPath m inner) fun i => ((0 : Fin 1), Xp.lonePath ++ (bPath m inner ++ [i]))

/-- The star momenta of `𝔫_a` for the exceptional data `e` (output `k`). -/
def starA (m : MiniTreeCode) (L : ℝ) {d : ℕ} (k : Mom d) (e : PairE m d) : Fin 4 → Mom d :=
  Fin.cases k fun i => k + latticePoint L (pairA m e.1.1 e.1.2.1 e.1.2.2 i)

/-- The star momenta of `𝔫_b`. -/
def starB (m : MiniTreeCode) (L : ℝ) {d : ℕ} (k : Mom d) (e : PairE m d) : Fin 4 → Mom d :=
  Fin.cases (k + latticePoint L e.1.1) fun i => k + latticePoint L (pairB m e.1.2.1 e.1.2.2 i)

/-- **The linked frequency** `A_e = ζ δ L^{2γ} Ω_{𝔫_a}`. -/
def cutFreq (m : MiniTreeCode) (ζ : ℤˣ) (L γ δ : ℝ) {d : ℕ} (k : Mom d) (e : PairE m d) : ℝ :=
  (((ζ : ℤˣ) : ℤ) : ℝ) * δ * L ^ (2 * γ) *
    resFactor (starA m L k e 1) (starA m L k e 2) (starA m L k e 3) (starA m L k e 0)

/-- The `ε` factors of `𝔫_a` and `𝔫_b`. -/
def cutEps (m : MiniTreeCode) {d : ℕ} (e : PairE m d) : ℝ :=
  epsCoef (pairA m e.1.1 e.1.2.1 e.1.2.2 0) (pairA m e.1.1 e.1.2.1 e.1.2.2 1) (pairA m e.1.1 e.1.2.1 e.1.2.2 2) *
    epsCoef (pairB m e.1.2.1 e.1.2.2 0) (pairB m e.1.2.1 e.1.2.2 1) (pairB m e.1.2.1 e.1.2.2 2)

/-- The modulation `e^{πi A_e (u - s)}`. -/
def cutPh (m : MiniTreeCode) (ζ : ℤˣ) (L γ δ : ℝ) {d : ℕ} (k : Mom d) (s : ℝ) (e : PairE m d) (u : ℝ) : ℂ :=
  Complex.exp (((Real.pi * cutFreq m ζ L γ δ k e * (u - s) : ℝ) : ℂ) * Complex.I)

/-- The prefix profiles. -/
def cutHp {d : ℕ} (H : LeafProfiles 1 d) : LeafProfiles 1 d := fun a => H ((0 : Fin 1), a.2)

/-- The interior profiles. -/
def cutHi (Xp : RegChain) (m : MiniTreeCode) {d : ℕ} (H : LeafProfiles 1 d) : LeafProfiles 1 d :=
  fun a => H ((0 : Fin 1), Xp.lonePath ++ m.c :: a.2)

/-- The red couple profiles. -/
def cutHr (Xp : RegChain) (m : MiniTreeCode) (inner : RegChain) (ζ : ℤˣ) {d : ℕ} (H : LeafProfiles 1 d) :
    LeafProfiles 2 d :=
  fun a => H ((0 : Fin 1), Xp.lonePath ++ (rBase m inner ζ a.1 ++ a.2))

/-- The green couple profiles. -/
def cutHg (Xp : RegChain) (m : MiniTreeCode) (inner : RegChain) (ζ : ℤˣ) {d : ℕ} (H : LeafProfiles 1 d) :
    LeafProfiles 2 d :=
  fun a => H ((0 : Fin 1), Xp.lonePath ++ (gBase m inner ζ a.1 ++ a.2))

namespace CutTermData

variable {LG LGp LGi : LayeredGarden 1} {LGr LGg : LayeredGarden 2} {Xp : RegChain} {m : MiniTreeCode}
  {Qr Qg : RegCpl} {inner : RegChain}
variable (D : CutTermData LG Xp m Qr Qg inner LGp LGi LGr LGg)
include D

theorem exists_GZ : ∃ GZ : Garden 1, GZ.sig 0 = LG.garden.sig 0 ∧ (cpair m Qr Qg inner).DecodesTree GZ := by
  obtain ⟨G, h1, h2, -⟩ := Reg.wf_chain_exists_regular_decodesTree _ D.wfZ (LG.garden.sig 0)
  exact ⟨G, h1, h2⟩

/-! ### The pieces, placed in the protected tree -/

/-- The prefix, in the protected tree. -/
def ιP (z : GNode LGp.garden.tree) : GNode LG.garden.tree :=
  ⟨((0 : Fin 1), z.1.2), by
    obtain ⟨GZ, hs, hZ⟩ := D.exists_GZ
    exact ((D.gd hZ hs).ι₁ z).2⟩

/-- The interior, in the protected tree. -/
def ιI (z : GNode LGi.garden.tree) : GNode LG.garden.tree :=
  ⟨((0 : Fin 1), Xp.lonePath ++ m.c :: z.1.2), by
    obtain ⟨GZ, hs, hZ⟩ := D.exists_GZ
    have := ((D.gd hZ hs).ι₂ ((D.hp hZ hs).ιi z)).2
    simpa [GlueData.ι₂, botAddr, PairData.ιi] using this⟩

/-- The red couple, in the protected tree. -/
def ιR (z : GNode LGr.garden.tree) : GNode LG.garden.tree :=
  ⟨((0 : Fin 1), Xp.lonePath ++ (rBase m inner (LG.garden.sig 0) z.1.1 ++ z.1.2)), by
    obtain ⟨GZ, hs, hZ⟩ := D.exists_GZ
    have := ((D.gd hZ hs).ι₂ ((D.hp hZ hs).ιr z)).2
    simpa [GlueData.ι₂, botAddr, PairData.ιr, hs] using this⟩

/-- The green couple, in the protected tree. -/
def ιG (z : GNode LGg.garden.tree) : GNode LG.garden.tree :=
  ⟨((0 : Fin 1), Xp.lonePath ++ (gBase m inner (LG.garden.sig 0) z.1.1 ++ z.1.2)), by
    obtain ⟨GZ, hs, hZ⟩ := D.exists_GZ
    have := ((D.gd hZ hs).ι₂ ((D.hp hZ hs).ιg z)).2
    simpa [GlueData.ι₂, botAddr, PairData.ιg, hs] using this⟩

/-- **The decoration multiplier is node-local and factors** at the cut: `M = M_cut(star_a, star_b) · M_pre · M_in ·
M_r · M_g`, the pieces reading the momenta of their own nodes. -/
def MultFactors {d : ℕ} (M : (GNode LG.garden.tree → Mom d) → ℂ) (Mc : (Fin 4 → Mom d) → (Fin 4 → Mom d) → ℂ)
    (Mp : (GNode LGp.garden.tree → Mom d) → ℂ) (Mi : (GNode LGi.garden.tree → Mom d) → ℂ)
    (Mr : (GNode LGr.garden.tree → Mom d) → ℂ) (Mg : (GNode LGg.garden.tree → Mom d) → ℂ) : Prop :=
  ∀ K : GNode LG.garden.tree → Mom d,
    M K = Mc (fun i => extend K (aAddr Xp i)) (fun i => extend K (bAddr Xp m inner i)) *
      (Mp (K ∘ D.ιP) * (Mi (K ∘ D.ιI) * (Mr (K ∘ D.ιR) * Mg (K ∘ D.ιG))))

/-! ### The decoration bijection and the summand identity -/

section Summand

variable {GZ : Garden 1} (hZ : (cpair m Qr Qg inner).DecodesTree GZ) (hsZ : GZ.sig 0 = LG.garden.sig 0)
include hZ hsZ

theorem ιI_eq (z : GNode LGi.garden.tree) : D.ιI z = (D.gd hZ hsZ).ι₂ ((D.hp hZ hsZ).ιi z) :=
  Subtype.ext (by simp [ιI, GlueData.ι₂, botAddr, PairData.ιi])

theorem ιR_eq (z : GNode LGr.garden.tree) : D.ιR z = (D.gd hZ hsZ).ι₂ ((D.hp hZ hsZ).ιr z) :=
  Subtype.ext (by simp [ιR, GlueData.ι₂, botAddr, PairData.ιr, hsZ])

theorem ιG_eq (z : GNode LGg.garden.tree) : D.ιG z = (D.gd hZ hsZ).ι₂ ((D.hp hZ hsZ).ιg z) :=
  Subtype.ext (by simp [ιG, GlueData.ι₂, botAddr, PairData.ιg, hsZ])

theorem ι₂_val (w : GNode GZ.tree) : ((D.gd hZ hsZ).ι₂ w).1 = ((0 : Fin 1), Xp.lonePath ++ w.1.2) := by
  obtain ⟨⟨j, p⟩, _⟩ := w
  have hj : j = 0 := Subsingleton.elim _ _
  subst hj
  show botAddr Xp.lonePath ((0 : Fin 1), p) = _
  simp [botAddr]

/-- **Decorations of the protected tree**: prefix × (exceptional data × interior × red × green). -/
def Φ (d : ℕ) : GenDecoration LG.garden d (fun _ => 0) 0 ≃
    GenDecoration LGp.garden d (fun _ => 0) 0 × (PairE m d × (GenDecoration LGi.garden d (fun _ => 0) 0 ×
      (GenDecoration LGr.garden d (fun _ => 0) 0 × GenDecoration LGg.garden d (fun _ => 0) 0))) :=
  ((D.gd hZ hsZ).decEquiv (decSplit_tree D.dec D.decP D.sigP hZ hsZ)
      (decGlue_tree D.dec D.decP D.sigP hZ hsZ) (not_flower_of_decodesTree D.dec)
      (not_flower_of_decodesTree D.decP) (not_flower_of_decodesTree hZ)).trans
    ((Equiv.refl _).prodCongr ((D.hp hZ hsZ).decEquiv d))

variable {d : ℕ} (κ : GenDecoration LG.garden d (fun _ => 0) 0)

theorem isDec_Z : IsDecoration GZ (κ.1 ∘ (D.gd hZ hsZ).ι₂) :=
  ((decSplit_tree D.dec D.decP D.sigP hZ hsZ (V := Fin d → ℤ)) κ.1 κ.2.1).2

theorem Z_root : (κ.1 ∘ (D.gd hZ hsZ).ι₂) (GNode.root GZ.tree 0) = 0 :=
  (((D.gd hZ hsZ).decEquiv (decSplit_tree D.dec D.decP D.sigP hZ hsZ)
      (decGlue_tree D.dec D.decP D.sigP hZ hsZ) (not_flower_of_decodesTree D.dec)
      (not_flower_of_decodesTree D.decP) (not_flower_of_decodesTree hZ)) κ).2.2.2.1 0

theorem Z_extend0 : extend (κ.1 ∘ (D.gd hZ hsZ).ι₂) ((0 : Fin 1), []) = 0 := by
  rw [show ((0 : Fin 1), ([] : Path)) = (GNode.root GZ.tree 0).1 from rfl, extend_node]
  exact D.Z_root hZ hsZ κ

theorem Φ_e : (D.Φ hZ hsZ d κ).2.1.1 = (extend (κ.1 ∘ (D.gd hZ hsZ).ι₂) ((0 : Fin 1), [m.c]),
    extend (κ.1 ∘ (D.gd hZ hsZ).ι₂) ((0 : Fin 1), rBase m inner (GZ.sig 0) 0),
    extend (κ.1 ∘ (D.gd hZ hsZ).ι₂) ((0 : Fin 1), gBase m inner (GZ.sig 0) 0)) := rfl

theorem Φ_i : ((D.Φ hZ hsZ d κ).2.2.1).1 = fun z =>
    κ.1 ((D.gd hZ hsZ).ι₂ ((D.hp hZ hsZ).ιi z)) - extend (κ.1 ∘ (D.gd hZ hsZ).ι₂) ((0 : Fin 1), [m.c]) := rfl

theorem Φ_r : ((D.Φ hZ hsZ d κ).2.2.2.1).1 = fun z =>
    κ.1 ((D.gd hZ hsZ).ι₂ ((D.hp hZ hsZ).ιr z)) -
      extend (κ.1 ∘ (D.gd hZ hsZ).ι₂) ((0 : Fin 1), rBase m inner (GZ.sig 0) 0) := rfl

theorem Φ_g : ((D.Φ hZ hsZ d κ).2.2.2.2).1 = fun z =>
    κ.1 ((D.gd hZ hsZ).ι₂ ((D.hp hZ hsZ).ιg z)) -
      extend (κ.1 ∘ (D.gd hZ hsZ).ι₂) ((0 : Fin 1), gBase m inner (GZ.sig 0) 0) := rfl

end Summand

/-! ### Momenta at the cut and on the pieces -/

section Momenta

variable {GZ : Garden 1} (hZ : (cpair m Qr Qg inner).DecodesTree GZ) (hsZ : GZ.sig 0 = LG.garden.sig 0)
include hZ hsZ
variable (L : ℝ) {d : ℕ} (k : Mom d) (κ : GenDecoration LG.garden d (fun _ => 0) 0)

/-- Momenta of a decoration of the protected tree at the nodes of the closing pair. -/
theorem coset_ι₂ (w : GNode GZ.tree) :
    cosetDecoration LG.garden L k κ.1 ((D.gd hZ hsZ).ι₂ w) = k + latticePoint L ((κ.1 ∘ (D.gd hZ hsZ).ι₂) w) := rfl

theorem extend_coset (w : GNode GZ.tree) (a : Fin 1 × Path) (ha : a = ((0 : Fin 1), Xp.lonePath ++ w.1.2)) :
    extend (cosetDecoration LG.garden L k κ.1) a = k + latticePoint L ((κ.1 ∘ (D.gd hZ hsZ).ι₂) w) := by
  rw [ha, ← D.ι₂_val hZ hsZ w, extend_node]
  rfl

theorem κZ_slot (j : Fin 3) : (κ.1 ∘ (D.gd hZ hsZ).ι₂) ((D.hp hZ hsZ).rootB.child j) =
    pairA m (D.Φ hZ hsZ d κ).2.1.1.1 (D.Φ hZ hsZ d κ).2.1.1.2.1 (D.Φ hZ hsZ d κ).2.1.1.2.2 j := by
  rw [D.Φ_e hZ hsZ κ, ← extend_node (κ.1 ∘ (D.gd hZ hsZ).ι₂)]
  have := (D.hp hZ hsZ).extend_slot (D.isDec_Z hZ hsZ κ) j
  convert this using 2
  simp [PairData.rootB, GBranch.child]

theorem κZ_bslot (j : Fin 3) : (κ.1 ∘ (D.gd hZ hsZ).ι₂) ((D.hp hZ hsZ).bB.child j) =
    pairB m (D.Φ hZ hsZ d κ).2.1.1.2.1 (D.Φ hZ hsZ d κ).2.1.1.2.2 j := by
  rw [D.Φ_e hZ hsZ κ, ← extend_node (κ.1 ∘ (D.gd hZ hsZ).ι₂)]
  exact (D.hp hZ hsZ).extend_bslot (D.isDec_Z hZ hsZ κ) (D.Z_extend0 hZ hsZ κ) j

theorem κZ_bB : (κ.1 ∘ (D.gd hZ hsZ).ι₂) (D.hp hZ hsZ).bB.toNode = (D.Φ hZ hsZ d κ).2.1.1.1 := by
  rw [D.Φ_e hZ hsZ κ, ← extend_node (κ.1 ∘ (D.gd hZ hsZ).ι₂)]
  exact (D.hp hZ hsZ).extend_bPath (D.isDec_Z hZ hsZ κ)

theorem κZ_rootB : (κ.1 ∘ (D.gd hZ hsZ).ι₂) (D.hp hZ hsZ).rootB.toNode = 0 :=
  D.Z_root hZ hsZ κ

theorem starA_eq : (fun i => extend (cosetDecoration LG.garden L k κ.1) (aAddr Xp i)) =
    starA m L k (D.Φ hZ hsZ d κ).2.1 := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [show aAddr Xp 0 = ((0 : Fin 1), Xp.lonePath ++ (D.hp hZ hsZ).rootB.toNode.1.2) by
      simp [aAddr, PairData.rootB, GBranch.toNode]]
    rw [D.extend_coset hZ hsZ L k κ _ _ rfl, D.κZ_rootB hZ hsZ κ, latticePoint_zero, add_zero]
    rfl
  · rw [show aAddr Xp j.succ = ((0 : Fin 1), Xp.lonePath ++ ((D.hp hZ hsZ).rootB.child j).1.2) by
      simp [aAddr, PairData.rootB, GBranch.child]]
    rw [D.extend_coset hZ hsZ L k κ _ _ rfl, D.κZ_slot hZ hsZ κ]
    rfl

theorem starB_eq : (fun i => extend (cosetDecoration LG.garden L k κ.1) (bAddr Xp m inner i)) =
    starB m L k (D.Φ hZ hsZ d κ).2.1 := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · rw [show bAddr Xp m inner 0 = ((0 : Fin 1), Xp.lonePath ++ (D.hp hZ hsZ).bB.toNode.1.2) by
      simp [bAddr, PairData.bB, GBranch.toNode]]
    rw [D.extend_coset hZ hsZ L k κ _ _ rfl, D.κZ_bB hZ hsZ κ]
    rfl
  · rw [show bAddr Xp m inner j.succ = ((0 : Fin 1), Xp.lonePath ++ ((D.hp hZ hsZ).bB.child j).1.2) by
      simp [bAddr, PairData.bB, GBranch.child]]
    rw [D.extend_coset hZ hsZ L k κ _ _ rfl, D.κZ_bslot hZ hsZ κ]
    rfl

theorem coset_P : cosetDecoration LG.garden L k κ.1 ∘ D.ιP =
    cosetDecoration LGp.garden L k ((D.Φ hZ hsZ d κ).1).1 := rfl

theorem coset_I : cosetDecoration LG.garden L k κ.1 ∘ D.ιI =
    cosetDecoration LGi.garden L (k + latticePoint L (D.Φ hZ hsZ d κ).2.1.1.1) ((D.Φ hZ hsZ d κ).2.2.1).1 := by
  rw [← cosetDecoration_add_const, D.Φ_i hZ hsZ κ, D.Φ_e hZ hsZ κ]
  funext z
  simp only [Function.comp_apply, sub_add_cancel]
  rw [D.ιI_eq hZ hsZ z]
  rfl

theorem coset_R : cosetDecoration LG.garden L k κ.1 ∘ D.ιR =
    cosetDecoration LGr.garden L (k + latticePoint L (D.Φ hZ hsZ d κ).2.1.1.2.1) ((D.Φ hZ hsZ d κ).2.2.2.1).1 := by
  rw [← cosetDecoration_add_const, D.Φ_r hZ hsZ κ, D.Φ_e hZ hsZ κ]
  funext z
  simp only [Function.comp_apply, sub_add_cancel]
  rw [D.ιR_eq hZ hsZ z]
  rfl

theorem coset_G : cosetDecoration LG.garden L k κ.1 ∘ D.ιG =
    cosetDecoration LGg.garden L (k + latticePoint L (D.Φ hZ hsZ d κ).2.1.1.2.2) ((D.Φ hZ hsZ d κ).2.2.2.2).1 := by
  rw [← cosetDecoration_add_const, D.Φ_g hZ hsZ κ, D.Φ_e hZ hsZ κ]
  funext z
  simp only [Function.comp_apply, sub_add_cancel]
  rw [D.ιG_eq hZ hsZ z]
  rfl

end Momenta

/-! ### `ε`, input leaves and phases at the cut -/

section Factors

variable {GZ : Garden 1} (hZ : (cpair m Qr Qg inner).DecodesTree GZ) (hsZ : GZ.sig 0 = LG.garden.sig 0)
include hZ hsZ
variable {d : ℕ} (κ : GenDecoration LG.garden d (fun _ => 0) 0)

theorem epsDec_cut : epsDec LG.garden κ.1 = epsDec LGp.garden ((D.Φ hZ hsZ d κ).1).1 *
    (cutEps m (D.Φ hZ hsZ d κ).2.1 * (epsDec LGi.garden ((D.Φ hZ hsZ d κ).2.2.1).1 *
      (epsDec LGr.garden ((D.Φ hZ hsZ d κ).2.2.2.1).1 * epsDec LGg.garden ((D.Φ hZ hsZ d κ).2.2.2.2).1))) := by
  rw [(D.gd hZ hsZ).epsDec_glue κ.1, (D.hp hZ hsZ).epsDec_pair]
  have hi : epsDec LGi.garden ((κ.1 ∘ (D.gd hZ hsZ).ι₂) ∘ (D.hp hZ hsZ).ιi) =
      epsDec LGi.garden ((D.Φ hZ hsZ d κ).2.2.1).1 := by
    rw [D.Φ_i hZ hsZ κ]
    symm
    rw [← epsDec_add_const LGi.garden _ (extend (κ.1 ∘ (D.gd hZ hsZ).ι₂) ((0 : Fin 1), [m.c]))]
    congr 1
    funext z
    simp
  have hr : epsDec LGr.garden ((κ.1 ∘ (D.gd hZ hsZ).ι₂) ∘ (D.hp hZ hsZ).ιr) =
      epsDec LGr.garden ((D.Φ hZ hsZ d κ).2.2.2.1).1 := by
    rw [D.Φ_r hZ hsZ κ]
    symm
    rw [← epsDec_add_const LGr.garden _
      (extend (κ.1 ∘ (D.gd hZ hsZ).ι₂) ((0 : Fin 1), rBase m inner (GZ.sig 0) 0))]
    congr 1
    funext z
    simp
  have hg : epsDec LGg.garden ((κ.1 ∘ (D.gd hZ hsZ).ι₂) ∘ (D.hp hZ hsZ).ιg) =
      epsDec LGg.garden ((D.Φ hZ hsZ d κ).2.2.2.2).1 := by
    rw [D.Φ_g hZ hsZ κ]
    symm
    rw [← epsDec_add_const LGg.garden _
      (extend (κ.1 ∘ (D.gd hZ hsZ).ι₂) ((0 : Fin 1), gBase m inner (GZ.sig 0) 0))]
    congr 1
    funext z
    simp
  rw [hi, hr, hg, D.κZ_slot hZ hsZ κ 0, D.κZ_slot hZ hsZ κ 1, D.κZ_slot hZ hsZ κ 2, D.κZ_bslot hZ hsZ κ 0,
    D.κZ_bslot hZ hsZ κ 1, D.κZ_bslot hZ hsZ κ 2]
  unfold cutEps
  rfl

theorem hmtop : ∀ ℓ : GLeaf LG.garden.tree, (ℓ.1.1 = 0 ∧ ¬ Xp.lonePath <+: ℓ.1.2) → LG.garden.mark ℓ = none := by
  intro ℓ hℓ
  rw [D.dec.2.1 ℓ, appendChain_lonePath]
  refine ite_eq_right fun he => hℓ.2 ?_
  rw [he]
  exact List.prefix_append _ _

theorem hmbot : ∀ (ℓ₂ : GLeaf GZ.tree) (ℓ : GLeaf LG.garden.tree), ℓ.1 = botAddr Xp.lonePath ℓ₂.1 →
    LG.garden.mark ℓ = GZ.mark ℓ₂ := by
  intro ℓ₂ ℓ he
  rw [D.dec.2.1 ℓ, hZ.2.1 ℓ₂, appendChain_lonePath]
  have hp : ℓ.1.2 = Xp.lonePath ++ ℓ₂.1.2 := by
    rw [he]
    have hj : ℓ₂.1.1 = 0 := Subsingleton.elim _ _
    simp [botAddr, hj]
  rw [hp]
  simp only [List.append_cancel_left_eq]

theorem prodH_cut (L : ℝ) (H : LeafProfiles 1 d) (k : Mom d) :
    ∏ ℓ ∈ inputLeaves LG.garden, (H ℓ.1 (cosetDecoration LG.garden L k κ.1 ℓ.toNode) : ℂ) =
      (∏ ℓ ∈ inputLeaves LGp.garden, (cutHp H ℓ.1 (cosetDecoration LGp.garden L k ((D.Φ hZ hsZ d κ).1).1 ℓ.toNode) : ℂ)) *
      ((∏ ℓ ∈ inputLeaves LGi.garden, (cutHi Xp m H ℓ.1 (cosetDecoration LGi.garden L
          (k + latticePoint L (D.Φ hZ hsZ d κ).2.1.1.1) ((D.Φ hZ hsZ d κ).2.2.1).1 ℓ.toNode) : ℂ)) *
        ((∏ ℓ ∈ inputLeaves LGr.garden, (cutHr Xp m inner (LG.garden.sig 0) H ℓ.1 (cosetDecoration LGr.garden L
            (k + latticePoint L (D.Φ hZ hsZ d κ).2.1.1.2.1) ((D.Φ hZ hsZ d κ).2.2.2.1).1 ℓ.toNode) : ℂ)) *
          ∏ ℓ ∈ inputLeaves LGg.garden, (cutHg Xp m inner (LG.garden.sig 0) H ℓ.1 (cosetDecoration LGg.garden L
            (k + latticePoint L (D.Φ hZ hsZ d κ).2.1.1.2.2) ((D.Φ hZ hsZ d κ).2.2.2.2).1 ℓ.toNode) : ℂ))) := by
  set f : Fin 1 × Path → ℂ := fun z => (H z (k + latticePoint L (extend κ.1 z)) : ℂ) with hf
  have e0 : ∏ ℓ ∈ inputLeaves LG.garden, (H ℓ.1 (cosetDecoration LG.garden L k κ.1 ℓ.toNode) : ℂ) =
      ∏ ℓ ∈ inputLeaves LG.garden, f ℓ.1 := by
    refine Finset.prod_congr rfl fun ℓ _ => ?_
    rw [hf]
    simp only
    rw [show ℓ.1 = ℓ.toNode.1 from rfl, extend_node]
    rfl
  rw [e0, (D.gd hZ hsZ).prod_inputLeaves_glue D.decP.2.1 (D.hmtop hZ hsZ) (D.hmbot hZ hsZ) f,
    (D.hp hZ hsZ).prod_inputLeaves_pair (fun z => f (botAddr Xp.lonePath z))]
  have hc := D.coset_I hZ hsZ L k κ
  have hcr := D.coset_R hZ hsZ L k κ
  have hcg := D.coset_G hZ hsZ L k κ
  congr 1
  · refine Finset.prod_congr rfl fun ℓ _ => ?_
    rw [hf]
    simp only [cutHp]
    rw [show extend κ.1 (topAddr ℓ.1) = κ.1 ((D.gd hZ hsZ).ι₁ ℓ.toNode) from
      extend_node κ.1 ((D.gd hZ hsZ).ι₁ ℓ.toNode)]
    rfl
  congr 1
  · refine Finset.prod_congr rfl fun ℓ _ => ?_
    have e1 : botAddr Xp.lonePath (pφi m ℓ.1) = (D.ιI ℓ.toNode).1 := by
      rw [D.ιI_eq hZ hsZ, D.ι₂_val hZ hsZ]; rfl
    rw [hf]
    simp only
    rw [e1, extend_node, ← congrFun hc ℓ.toNode]
    rfl
  congr 1
  · refine Finset.prod_congr rfl fun ℓ _ => ?_
    have e1 : botAddr Xp.lonePath (pφr m inner (GZ.sig 0) ℓ.1) = (D.ιR ℓ.toNode).1 := by
      rw [D.ιR_eq hZ hsZ, D.ι₂_val hZ hsZ]; rfl
    rw [hf]
    simp only
    rw [e1, extend_node, ← congrFun hcr ℓ.toNode]
    simp only [cutHr, ιR, Function.comp_apply]
    rfl
  · refine Finset.prod_congr rfl fun ℓ _ => ?_
    have e1 : botAddr Xp.lonePath (pφg m inner (GZ.sig 0) ℓ.1) = (D.ιG ℓ.toNode).1 := by
      rw [D.ιG_eq hZ hsZ, D.ι₂_val hZ hsZ]; rfl
    rw [hf]
    simp only
    rw [e1, extend_node, ← congrFun hcg ℓ.toNode]
    simp only [cutHg, ιG, Function.comp_apply]
    rfl

end Factors

/-! ### The linked phase and the summand identity -/

section SummandEq

variable {GZ : Garden 1} (hZ : (cpair m Qr Qg inner).DecodesTree GZ) (hsZ : GZ.sig 0 = LG.garden.sig 0)
include hZ hsZ
variable {d : ℕ} (κ : GenDecoration LG.garden d (fun _ => 0) 0)

omit D hZ hsZ in
theorem coset_cA (L : ℝ) (k : Mom d) (x yr yg : Fin d → ℤ) (j : Fin 3) :
    k + latticePoint L (pairA m x yr yg j) =
      cA m (k + latticePoint L x) (k + latticePoint L yr) (k + latticePoint L yg) j := by
  unfold pairA cA; split_ifs <;> rfl

omit D hZ hsZ in
theorem coset_cB (L : ℝ) (k : Mom d) (yr yg : Fin d → ℤ) (j : Fin 3) :
    k + latticePoint L (pairB m yr yg j) = cB m k (k + latticePoint L yr) (k + latticePoint L yg) j := by
  unfold pairB cB; split_ifs <;> simp [latticePoint_zero]

theorem phase_cut (L γ δ : ℝ) (k : Mom d) (s u : ℝ) :
    Complex.exp ((Real.pi * ((GZ.sign (D.hp hZ hsZ).rootB.toNode : ℤˣ) : ℤ) * δ * L ^ (2 * γ) *
        omegaNode GZ (cosetDecoration LG.garden L k κ.1 ∘ (D.gd hZ hsZ).ι₂) (D.hp hZ hsZ).rootB * u : ℝ) *
          Complex.I) *
      Complex.exp ((Real.pi * ((GZ.sign (D.hp hZ hsZ).bB.toNode : ℤˣ) : ℤ) * δ * L ^ (2 * γ) *
        omegaNode GZ (cosetDecoration LG.garden L k κ.1 ∘ (D.gd hZ hsZ).ι₂) (D.hp hZ hsZ).bB * s : ℝ) *
          Complex.I) =
      cutPh m (LG.garden.sig 0) L γ δ k s (D.Φ hZ hsZ d κ).2.1 u := by
  set e := (D.Φ hZ hsZ d κ).2.1
  set P0 := k
  set Px := k + latticePoint L e.1.1
  set Pr := k + latticePoint L e.1.2.1
  set Pg := k + latticePoint L e.1.2.2
  have sa : GZ.sign (D.hp hZ hsZ).rootB.toNode = LG.garden.sig 0 := by
    show pathSign (GZ.sig 0) [] = _
    simp [pathSign, hsZ]
  have sb : GZ.sign (D.hp hZ hsZ).bB.toNode = slotSign (LG.garden.sig 0) m.c := by
    show pathSign (GZ.sig 0) (bPath m inner) = _
    rw [bPath, Comb.pathSign_append, pathSign_singleton, lonePath_sign, hsZ]
  have oa : omegaNode GZ (cosetDecoration LG.garden L k κ.1 ∘ (D.gd hZ hsZ).ι₂) (D.hp hZ hsZ).rootB =
      resFactor (cA m Px Pr Pg 0) (cA m Px Pr Pg 1) (cA m Px Pr Pg 2) P0 := by
    have hc : ∀ j, cosetDecoration LG.garden L k κ.1 ((D.gd hZ hsZ).ι₂ ((D.hp hZ hsZ).rootB.child j)) =
        cA m Px Pr Pg j := fun j => by
      rw [D.coset_ι₂ hZ hsZ L k κ, D.κZ_slot hZ hsZ κ j, coset_cA]
    have h0 : cosetDecoration LG.garden L k κ.1 ((D.gd hZ hsZ).ι₂ (D.hp hZ hsZ).rootB.toNode) = P0 := by
      rw [D.coset_ι₂ hZ hsZ L k κ, D.κZ_rootB hZ hsZ κ, latticePoint_zero, add_zero]
    unfold omegaNode
    simp only [Function.comp_apply]
    rw [hc 0, hc 1, hc 2, h0]
  have ob : omegaNode GZ (cosetDecoration LG.garden L k κ.1 ∘ (D.gd hZ hsZ).ι₂) (D.hp hZ hsZ).bB =
      resFactor (cB m P0 Pr Pg 0) (cB m P0 Pr Pg 1) (cB m P0 Pr Pg 2) Px := by
    have hc : ∀ j, cosetDecoration LG.garden L k κ.1 ((D.gd hZ hsZ).ι₂ ((D.hp hZ hsZ).bB.child j)) =
        cB m P0 Pr Pg j := fun j => by
      rw [D.coset_ι₂ hZ hsZ L k κ, D.κZ_bslot hZ hsZ κ j, coset_cB]
    have h0 : cosetDecoration LG.garden L k κ.1 ((D.gd hZ hsZ).ι₂ (D.hp hZ hsZ).bB.toNode) = Px := by
      rw [D.coset_ι₂ hZ hsZ L k κ, D.κZ_bB hZ hsZ κ]
    unfold omegaNode
    simp only [Function.comp_apply]
    rw [hc 0, hc 1, hc 2, h0]
  have hfreq : cutFreq m (LG.garden.sig 0) L γ δ k e =
      (((LG.garden.sig 0 : ℤˣ) : ℤ) : ℝ) * δ * L ^ (2 * γ) *
        resFactor (cA m Px Pr Pg 0) (cA m Px Pr Pg 1) (cA m Px Pr Pg 2) P0 := by
    unfold cutFreq
    rw [show starA m L k e 1 = k + latticePoint L (pairA m e.1.1 e.1.2.1 e.1.2.2 0) from rfl,
      show starA m L k e 2 = k + latticePoint L (pairA m e.1.1 e.1.2.1 e.1.2.2 1) from rfl,
      show starA m L k e 3 = k + latticePoint L (pairA m e.1.1 e.1.2.1 e.1.2.2 2) from rfl,
      show starA m L k e 0 = k from rfl, coset_cA, coset_cA, coset_cA]
  have key := link_cancel m (LG.garden.sig 0) P0 Px Pr Pg
  unfold cutPh
  rw [sa, sb, oa, ob, hfreq, ← Complex.exp_add, ← add_mul, ← Complex.ofReal_add]
  congr 3
  linear_combination (Real.pi * δ * L ^ (2 * γ) * s) * key

/-- **The terminal pin at one decoration** (o73 (13.1), summand level). -/
theorem summand_eq (L γ δ : ℝ) (H : LeafProfiles 1 d) (M : (GNode LG.garden.tree → Mom d) → ℂ)
    (Mc : (Fin 4 → Mom d) → (Fin 4 → Mom d) → ℂ) (Mp : (GNode LGp.garden.tree → Mom d) → ℂ)
    (Mi : (GNode LGi.garden.tree → Mom d) → ℂ) (Mr : (GNode LGr.garden.tree → Mom d) → ℂ)
    (Mg : (GNode LGg.garden.tree → Mom d) → ℂ) (hM : D.MultFactors M Mc Mp Mi Mr Mg) (T s s' : ℝ) (k : Mom d) :
    protSummand L γ δ LG H M (fun _ => T) s' (termFix Xp m inner s) k κ =
      (Mc (starA m L k (D.Φ hZ hsZ d κ).2.1) (starB m L k (D.Φ hZ hsZ d κ).2.1) *
          (cutEps m (D.Φ hZ hsZ d κ).2.1 : ℂ)) *
        ∫ u in cutU LG Xp T s, cutPh m (LG.garden.sig 0) L γ δ k s (D.Φ hZ hsZ d κ).2.1 u *
          (protSummand L γ δ LGp (cutHp H) Mp (fun _ => T) u (fun _ => none) k (D.Φ hZ hsZ d κ).1 *
            (protSummand L γ δ LGi (cutHi Xp m H) Mi (fun _ => u) s (fun _ => none)
                (k + latticePoint L (D.Φ hZ hsZ d κ).2.1.1.1) (D.Φ hZ hsZ d κ).2.2.1 *
              (protSummand L γ δ LGr (cutHr Xp m inner (LG.garden.sig 0) H) Mr
                  (fun y => cupR m inner (LG.garden.sig 0) u s y.1.1) 0 (fun _ => none)
                  (k + latticePoint L (D.Φ hZ hsZ d κ).2.1.1.2.1) (D.Φ hZ hsZ d κ).2.2.2.1 *
                protSummand L γ δ LGg (cutHg Xp m inner (LG.garden.sig 0) H) Mg
                  (fun y => cupG m inner (LG.garden.sig 0) u s y.1.1) 0 (fun _ => none)
                  (k + latticePoint L (D.Φ hZ hsZ d κ).2.1.1.2.2) (D.Φ hZ hsZ d κ).2.2.2.2))) := by
  have hI : cosetDecoration LG.garden L k κ.1 ∘ ((D.gd hZ hsZ).ι₂ ∘ (D.hp hZ hsZ).ιi) =
      cosetDecoration LGi.garden L (k + latticePoint L (D.Φ hZ hsZ d κ).2.1.1.1) ((D.Φ hZ hsZ d κ).2.2.1).1 := by
    rw [← D.coset_I hZ hsZ L k κ]
    funext z
    simp [D.ιI_eq hZ hsZ]
  have hR : cosetDecoration LG.garden L k κ.1 ∘ ((D.gd hZ hsZ).ι₂ ∘ (D.hp hZ hsZ).ιr) =
      cosetDecoration LGr.garden L (k + latticePoint L (D.Φ hZ hsZ d κ).2.1.1.2.1)
        ((D.Φ hZ hsZ d κ).2.2.2.1).1 := by
    rw [← D.coset_R hZ hsZ L k κ]
    funext z
    simp [D.ιR_eq hZ hsZ]
  have hG : cosetDecoration LG.garden L k κ.1 ∘ ((D.gd hZ hsZ).ι₂ ∘ (D.hp hZ hsZ).ιg) =
      cosetDecoration LGg.garden L (k + latticePoint L (D.Φ hZ hsZ d κ).2.1.1.2.2)
        ((D.Φ hZ hsZ d κ).2.2.2.2).1 := by
    rw [← D.coset_G hZ hsZ L k κ]
    funext z
    simp [D.ιG_eq hZ hsZ]
  have hP : cosetDecoration LG.garden L k κ.1 ∘ (D.gd hZ hsZ).ι₁ =
      cosetDecoration LGp.garden L k ((D.Φ hZ hsZ d κ).1).1 := rfl
  have hphase := D.phase_cut hZ hsZ κ L γ δ k s
  unfold protSummand
  rw [hM, D.starA_eq hZ hsZ L k κ, D.starB_eq hZ hsZ L k κ, D.coset_P hZ hsZ L k κ, D.coset_I hZ hsZ L k κ,
    D.coset_R hZ hsZ L k κ, D.coset_G hZ hsZ L k κ, D.epsDec_cut hZ hsZ κ,
    D.protTime_cutTerm hZ hsZ L γ δ T s s' (cosetDecoration LG.garden L k κ.1), D.prodH_cut hZ hsZ κ L H k]
  simp only [hI, hR, hG, hP, hphase]
  rw [hsZ]
  rw [show ∀ (a b c J : ℂ), a * (b * J * c) = (a * b * c) * J from fun a b c J => by ring]
  conv_lhs => rw [← integral_const_mul]
  conv_rhs => rw [← integral_const_mul]
  congr 1
  funext u
  push_cast
  ring

end SummandEq

end CutTermData

end WaveTurbulence.Flower.ProtCut
