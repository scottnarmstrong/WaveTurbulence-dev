/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtCut.Root2Exist
public import WaveTurbulence.Foundations.Flower.ProtCut.Relabel

/-! # D2c-3 PROT-CUT: a chain on tree `1` of a type-2 couple, glued after relabelling

Main's `GlueData` glues a chain on tree `0`. For a couple decoded by `type2 X₂ (appendChain X Y) Qlp` (the chain `X` at
the top of tree `1`) the trees are swapped (`swLG`, `Relabel.lean`): `SwGlueData.gd` glues `X` (sign `-1`) on the
relabelled rest couple `swLG LGB`, `LGB` decoded by `closeCouple X₂ Y Qlp`. The decoration split and glue
(`SwGlueData.hs`, `SwGlueData.hg`) are proved from the code of `LG` through the relabelling (`cplDec_G_iff`,
`cplDec_B_iff`: the code of `LG` and of the rest couple, pulled back along `top1`, `phiB`).

Instances: o104 Prop 7.4 (a) with `ε = -` (`X` the closing pair of the `-` chain, `Root2Sw.lean`) and (c) with
`ε = +` (`X = X⁻`, `Y = nil`, `X₂ = nil`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset

namespace WaveTurbulence.Flower.ProtCut

open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234
open WaveTurbulence.Flower.ProtDefs

theorem layerAt_sw (LG : LayeredGarden 2) (x : Fin 2 × Path) : layerAt (swLG LG) x = layerAt LG (t1sw x.1, x.2) :=
  rfl

/-- The address map of the rest couple `closeCouple Xp rest Qlp` into the couple: tree `0` (the chain `X⁺`) in
place, tree `1` (the suffix) below the closing pair. -/
def phiB (lp : Path) (x : Fin 2 × Path) : Fin 2 × Path := if x.1 = 0 then (0, x.2) else (1, lp ++ x.2)

theorem phiB_hom (lp : Path) : ∀ x q, phiB lp (addrExt x q) = addrExt (phiB lp x) q := by
  intro x q
  obtain ⟨t, p⟩ := x
  unfold phiB addrExt
  split_ifs <;> simp [List.append_assoc]

/-- The address map of the closing pair into tree `1`. -/
def top1 (x : Fin 1 × Path) : Fin 2 × Path := ((1 : Fin 2), x.2)

theorem top1_hom : ∀ x q, top1 (addrExt x q) = addrExt (top1 x) q := fun _ _ => rfl

theorem phiB_sw (lp : Path) (x : Fin 2 × Path) :
    phiB lp (t1sw x.1, x.2) = (t1sw (botAddr lp x).1, (botAddr lp x).2) := by
  obtain ⟨t, p⟩ := x
  fin_cases t <;> simp [phiB, botAddr, t1sw]

theorem t1sw_eq_one_iff (t : Fin 2) : t1sw t = 1 ↔ t = 0 := by fin_cases t <;> simp [t1sw]

theorem trFix_brB (σ : ℝ) {T : Fin 2 → TTree} (b : GBranch (swT T)) : trFix 1 σ (brB b) = trFix 0 σ b := by
  unfold trFix
  simp only [brB, t1sw_eq_one_iff]

/-- Clocks of the rest couple in the original labelling: its tree `1` (below `n⁻_b`) at `u`, its tree `0` at `U 0`. -/
def bClock1 (U : Fin 2 → ℝ) (u : ℝ) (t : Fin 2) : ℝ := if t = 1 then u else U t

theorem extend_ndF {T : Fin 2 → TTree} {V : Type*} [AddCommGroup V] (κ : GNode (swT T) → V) (x : Fin 2 × Path) :
    extend (κ ∘ ndF) x = extend κ (t1sw x.1, x.2) := by
  obtain ⟨t, p⟩ := x
  unfold extend
  by_cases h : p ∈ (T t).nodes
  · have h' : p ∈ (swT T (t1sw t)).nodes := by show p ∈ (T (t1sw (t1sw t))).nodes; rw [t1sw_t1sw]; exact h
    rw [dif_pos h, dif_pos h']
    rfl
  · have h' : p ∉ (swT T (t1sw t)).nodes := by show p ∉ (T (t1sw (t1sw t))).nodes; rw [t1sw_t1sw]; exact h
    rw [dif_neg h, dif_neg h']

/-- **A type-2 couple with a chain on tree `1` glued, relabelled**: `LG` decoded by `type2 X₂ (appendChain X Y) Qlp`;
`X` (sign `-1`, a paired tree `LGX`) is the top of tree `1`, and `LGB` is the couple `closeCouple X₂ Y Qlp` (the rest),
with the layers of `LG` (`top1`, `phiB`). After relabelling (`swLG`), `X` is glued on `swLG LGB` at tree `0`. -/
structure SwGlueData (LG : LayeredGarden 2) (X₂ X Y : RegChain) (Qlp : RegCpl) (LGX : LayeredGarden 1)
    (LGB : LayeredGarden 2) : Prop where
  dec : (RegCpl.type2 X₂ (appendChain X Y) Qlp).Decodes LG.garden
  decX : X.DecodesTree LGX.garden
  sigX : LGX.garden.sig 0 = -1
  decB : (SourceApp.closeCouple X₂ Y Qlp).Decodes LGB.garden
  layX : ∀ z : GNode LGX.garden.tree, LGX.layer z = layerAt LG (top1 z.1)
  layB : ∀ z : GNode LGB.garden.tree, LGB.layer z = layerAt LG (phiB X.lonePath z.1)

/-- The gluing of `X` on the relabelled rest couple, at the level of gardens. -/
theorem glueSw {G GB : Garden 2} {GZ : Garden 1} {X₂ X Y : RegChain} {Qlp : RegCpl} (hd : (RegCpl.type2 X₂ (appendChain X Y) Qlp).Decodes G)
    (hdZ : X.DecodesTree GZ) (hsZ : GZ.sig 0 = -1)
    (hdB : (SourceApp.closeCouple X₂ Y Qlp).Decodes GB) :
    GlueData (swGarden G) GZ (swGarden GB) X := by
  have hsG : G.sig = ![1, -1] := hd.1.2
  have hsB : GB.sig = ![1, -1] := hdB.1.2
  have t2 := closeCouple_trees X₂ Y Qlp
  refine ⟨?_, ?_, ?_, ?_, hdZ⟩
  · show G.tree (t1sw 0) = X.plug (G.sig (t1sw 0)) (GB.tree (t1sw 0))
    rw [show t1sw 0 = 1 from rfl, hd.2.2.1, hdB.2.2.1, t2, hsG]
    simp only [RegCpl.trees, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_zero]
    rw [appendChain_plug]
  · intro j hj
    have hj1 : j = 1 := by fin_cases j <;> simp_all
    subst hj1
    show G.tree (t1sw 1) = GB.tree (t1sw 1)
    rw [show t1sw 1 = 0 from rfl, hd.2.1, hdB.2.1, t2]
    rfl
  · funext j
    show G.sig (t1sw j) = GB.sig (t1sw j)
    rw [hsG, hsB]
  · rw [hsZ]
    show (-1 : ℤˣ) = G.sig (t1sw 0)
    rw [hsG]
    simp [t1sw]

namespace SwGlueData

variable {LG : LayeredGarden 2} {X₂ X Y : RegChain} {Qlp : RegCpl} {LGX : LayeredGarden 1} {LGB : LayeredGarden 2}
  (D : SwGlueData LG X₂ X Y Qlp LGX LGB)
include D

theorem gd : GlueData (swLG LG).garden LGX.garden (swLG LGB).garden X :=
  glueSw D.dec D.decX D.sigX D.decB

/-! ### The codes, split -/

omit D in
theorem cplDec_G_iff {V : Type*} [AddCommGroup V] (F : Fin 2 × Path → V) :
    CplDec F (RegCpl.type2 X₂ (appendChain X Y) Qlp) (0, []) (1, []) ↔
      ChainDec F X₂ 1 (0, []) ∧ (ChainDec F X (-1) (1, []) ∧
        ChainDec F Y (-1) (1, X.lonePath)) ∧
      CplDec F Qlp (0, X₂.lonePath) (1, X.lonePath ++ Y.lonePath) := by
  have e1 : addrExt ((1 : Fin 2), ([] : Path)) X.lonePath =
      (1, X.lonePath) := by simp [addrExt]
  have e2 : addrExt ((0 : Fin 2), ([] : Path)) X₂.lonePath = (0, X₂.lonePath) := by simp [addrExt]
  have e3 : addrExt ((1 : Fin 2), ([] : Path)) (X.lonePath ++ Y.lonePath) =
      (1, X.lonePath ++ Y.lonePath) := by simp [addrExt]
  simp only [CplDec, chainDec_append, appendChain_lonePath, e1, e2, e3]

omit D in
theorem cplDec_B_iff {V : Type*} [AddCommGroup V] (F : Fin 2 × Path → V) :
    CplDec (F ∘ phiB X.lonePath) (SourceApp.closeCouple X₂ Y Qlp) (0, []) (1, []) ↔
      ChainDec F X₂ 1 (0, []) ∧ ChainDec F Y (-1) (1, X.lonePath) ∧
        CplDec F Qlp (0, X₂.lonePath) (1, X.lonePath ++ Y.lonePath) := by
  set lp := X.lonePath
  rw [cplDec_closeCouple]
  simp only [CplDec]
  rw [chainDec_comp (phiB_hom lp), chainDec_comp (phiB_hom lp), cplDec_comp (phiB_hom lp)]
  have e0 : phiB lp ((0 : Fin 2), ([] : Path)) = (0, []) := by simp [phiB]
  have e1 : phiB lp ((1 : Fin 2), ([] : Path)) = (1, lp) := by simp [phiB]
  have e2 : phiB lp (addrExt ((0 : Fin 2), ([] : Path)) X₂.lonePath) = (0, X₂.lonePath) := by
    simp [phiB, addrExt]
  have e3 : phiB lp (addrExt ((1 : Fin 2), ([] : Path)) Y.lonePath) = (1, lp ++ Y.lonePath) := by
    simp [phiB, addrExt]
  rw [e0, e1, e2, e3]

/-! ### The decoration split and glue of the relabelled couple -/

theorem hs (d : ℕ) : D.gd.DecSplit (Fin d → ℤ) := by
  intro κ' hκ'
  set κ : GNode LG.garden.tree → (Fin d → ℤ) := κ' ∘ ndF with hκdef
  have hκ'eq : ∀ x, κ' x = κ (ndB x) := fun x => by rw [hκdef]; simp only [Function.comp_apply, ndF_ndB]
  have hκ : IsDecoration LG.garden κ := isDecoration_of_sw (by
    have : κ ∘ ndB = κ' := funext fun x => (hκ'eq x).symm
    rw [this]; exact hκ')
  obtain ⟨hXp, ⟨hZ, hR⟩, hQ⟩ := (cplDec_G_iff (extend κ)).mp (cplDec_of_decoration D.dec hκ)
  constructor
  · have h1 : ChainDec (extend κ ∘ top1) X (LGX.garden.sig 0) ((0 : Fin 1), []) := by
      rw [D.sigX, chainDec_comp top1_hom]; exact hZ
    have h2 := PL234.isDecoration_of_chainDec D.decX h1
    convert h2 using 1
    funext x
    show κ' (D.gd.ι₁ x) = extend κ (top1 x.1)
    rw [hκ'eq, ← extend_node κ (ndB (D.gd.ι₁ x))]
    rfl
  · have h2 : CplDec (extend κ ∘ phiB X.lonePath) (SourceApp.closeCouple X₂ Y Qlp)
        (0, []) (1, []) := (cplDec_B_iff (extend κ)).mpr ⟨hXp, hR, hQ⟩
    have hb := isDecoration_sw (isDecoration_of_cplDec D.decB h2)
    convert hb using 1
    funext y
    show κ' (D.gd.ι₂ y) = extend κ (phiB X.lonePath (ndB y).1)
    rw [hκ'eq, ← extend_node κ (ndB (D.gd.ι₂ y))]
    exact congrArg (extend κ) (phiB_sw _ y.1).symm

theorem hg (d : ℕ) : GlueData.DecGlue (G := (swLG LG).garden) (G₁ := LGX.garden) (G₂ := (swLG LGB).garden)
    (X := X) (Fin d → ℤ) := by
  intro κ₁ κ₂ hκ₁ hκ₂ h0₁ h0₂
  classical
  let F : Fin 2 × Path → (Fin d → ℤ) := fun a =>
    GlueData.glueAddr (w := 2) (X := X) κ₁ κ₂ (t1sw a.1, a.2)
  have hF : GlueData.glue (G := (swLG LG).garden) (G₁ := LGX.garden) (G₂ := (swLG LGB).garden)
      (X := X) κ₁ κ₂ = (fun a : GNode LG.garden.tree => F a.1) ∘ ndB := by
    funext z
    show GlueData.glueAddr (X := X) κ₁ κ₂ z.1 =
      GlueData.glueAddr (X := X) κ₁ κ₂ (t1sw (t1sw z.1.1), z.1.2)
    rw [t1sw_t1sw]
  rw [hF]
  have hκ₂' : IsDecoration LGB.garden (κ₂ ∘ ndF) := isDecoration_of_sw (by
    have : (κ₂ ∘ ndF) ∘ ndB = κ₂ := funext fun x => congrArg κ₂ (ndF_ndB x)
    rw [this]; exact hκ₂)
  have hFB : F ∘ phiB X.lonePath = extend (κ₂ ∘ ndF) := by
    funext x
    obtain ⟨t, p⟩ := x
    rw [extend_ndF]
    fin_cases t
    · simp [F, phiB, GlueData.glueAddr, GlueData.unbot, t1sw]
    · simp [F, phiB, GlueData.glueAddr, GlueData.unbot, t1sw]
  obtain ⟨hXp, hR, hQ⟩ := (cplDec_B_iff F).mp (by rw [hFB]; exact cplDec_of_decoration D.decB hκ₂')
  refine isDecoration_sw (isDecoration_of_cplDec D.dec ((cplDec_G_iff F).mpr ⟨hXp, ⟨?_, hR⟩, hQ⟩))
  have hd₁ := chainDec_of_decoration D.decX hκ₁
  rw [D.sigX] at hd₁
  have hcong : ∀ q ∈ (X.plug (-1) .leaf).nodes,
      (F ∘ top1) (addrExt ((0 : Fin 1), ([] : Path)) q) = extend κ₁ (addrExt ((0 : Fin 1), ([] : Path)) q) := by
    intro q hq
    simp only [Function.comp_apply, top1, addrExt, List.nil_append]
    by_cases hpre : X.lonePath <+: q
    · have hq' := plug_leaf_prefix X (-1) hq hpre
      subst hq'
      have hu : GlueData.unbot X.lonePath ((0 : Fin 2), X.lonePath) = (GNode.root (swLG LGB).garden.tree 0).1 := by
        simp [GlueData.unbot, GNode.root]
      have e1 : F ((1 : Fin 2), X.lonePath) = extend κ₂ (GlueData.unbot X.lonePath ((0 : Fin 2), X.lonePath)) := by
        simp [F, GlueData.glueAddr, t1sw]
      rw [e1, hu, extend_node, h0₂]
      have hl : ((0 : Fin 1), X.lonePath) = D.gd.lone.1 := rfl
      rw [hl, extend_node, D.gd.lone_eq_root hκ₁, h0₁]
    · simp [F, GlueData.glueAddr, hpre, t1sw]
  have hc : ChainDec (F ∘ top1) X (-1) ((0 : Fin 1), ([] : Path)) :=
    (chainDec_congr X (-1) ((0 : Fin 1), ([] : Path)) hcong).mpr hd₁
  exact (chainDec_comp top1_hom F X (-1) ((0 : Fin 1), ([] : Path))).mp hc


end SwGlueData

/-- A kernel of the relabelled couple read in the original labelling (no designation). -/
theorem kernelProt_sw_back {LG' : LayeredGarden 2} (hp : LG'.garden.IsPlain) (L γ δ : ℝ) {d : ℕ}
    (H' : LeafProfiles 2 d) (M' : (GNode (swLG LG').garden.tree → Mom d) → ℂ)
    (up' : GBranch (swLG LG').garden.tree → ℝ) (s : ℝ) (k : Mom d) :
    kernelProt L γ δ (swLG LG') H' M' up' s (fun _ => none) k (fun _ => 0) 0 =
      kernelProt L γ δ LG' (fun a => H' (t1sw a.1, a.2)) (fun K => M' (K ∘ ndB)) (fun b => up' (brF b)) s
        (fun _ => none) k (fun _ => 0) 0 := by
  rw [← kernelProt_sw hp L γ δ (fun a => H' (t1sw a.1, a.2)) (fun K => M' (K ∘ ndB)) (fun b => up' (brF b)) s
    (fun _ => none) k]
  have e1 : swH (fun a => H' (t1sw a.1, a.2)) = H' := by
    funext a
    simp only [swH, t1sw_t1sw]
  have e2 : swM (fun K => M' (K ∘ ndB)) = M' := by
    funext K
    show M' ((K ∘ ndF) ∘ ndB) = M' K
    congr 1
    funext x
    exact congrArg K (ndF_ndB x)
  have e3 : (fun b => (fun b => up' (brF b)) (brB b) : GBranch (swLG LG').garden.tree → ℝ) = up' := by
    funext b
    simp only [brF_brB]
  rw [e1, e2, e3]

theorem lfB_input {G : Garden 2} (ℓ : GLeaf (swGarden G).tree) (hℓ : ℓ ∈ inputLeaves (swGarden G)) :
    lfB ℓ ∈ inputLeaves G := by
  rw [mem_inputLeaves] at hℓ ⊢
  exact hℓ

theorem hH_sw {LG : LayeredGarden 2} {d : ℕ} (L : ℝ) (H : LeafProfiles 2 d)
    (hH : ∀ ℓ ∈ inputLeaves LG.garden, ∀ k' : Mom d, Summable fun n : Fin d → ℤ => |H ℓ.1 (k' + latticePoint L n)|) :
    ∀ ℓ ∈ inputLeaves (swLG LG).garden, ∀ k' : Mom d,
      Summable fun n : Fin d → ℤ => |swH H ℓ.1 (k' + latticePoint L n)| :=
  fun ℓ hℓ k' => hH (lfB ℓ) (lfB_input ℓ hℓ) k'

end WaveTurbulence.Flower.ProtCut
