/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtPin.TChild2ACoh
public import WaveTurbulence.Foundations.Flower.ProtPin.TChild2AMult
public import WaveTurbulence.Foundations.Flower.ProtPin.TChildMixT
public import WaveTurbulence.Foundations.Flower.ProtPin.TChildIvl
public import WaveTurbulence.Foundations.VineEst.VineEstS3.Mink

/-! # D3-HELPER (P7), shape (a+): preparations of the root trace

* root layers of the pieces (`tc2a_rootB0_le`, `tc2a_rootI_le`, `tc2a_rootR_le`, `tc2a_rootG_le`) and the lone layer of
  the interior (`tc2a_loneI`);
* the side-couple clocks lie in the boxes of their parent layers (`tc2a_cupR_mem`, `tc2a_cupG_mem`);
* the rest-couple clocks (`tc2a_bClock_eq`), the constant of main's countable Minkowski (`tc2a_cmc_eq`), the modulus of
  the closing-pair coefficient (`tc2a_norm_Izeta`). -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory WaveTurbulence.Fourier
open scoped ENNReal NNReal

namespace WaveTurbulence.Flower.ProtPin

open WaveTurbulence.Flower.ProtDefs WaveTurbulence.Flower.ProtCut
open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234

/-- The constant of main's countable Minkowski on a unit cell (the worker's `tc_cmc_eq`, restated). -/
theorem tc2a_cmc_eq (θ : ℝ) {r : ℕ} (q : Fin r → ℝ) :
    cutoffMultiplierConstant θ (VineEstS3.FS.cutQ q) = ENNReal.ofReal (2 ^ |θ|) * cutNormR |θ| r := by
  unfold cutoffMultiplierConstant
  congr 1
  have e : VineEstS3.FS.cutQ q = fun t => coordinateCutoff (r := r) Layered.chiUnit (t + -q) := by
    funext t
    simp only [VineEstS3.FS.cutQ, sub_eq_add_neg]
  rw [e, timeFourierNorm_translate]
  rfl

theorem tc2a_norm_Izeta (u : ℤˣ) : ‖Complex.I * (((u : ℤ) : ℂ))‖ = 1 := by
  rcases Int.units_eq_one_or u with rfl | rfl <;> simp

theorem tc2a_bClock_eq (s y u : ℝ) (t : Fin 2) :
    bClock (fun t' : Fin 2 => if t' = 0 then s else y) u t = (![u, y] : Fin 2 → ℝ) t := by
  fin_cases t <;> simp [bClock]

theorem tc2a_cupR_mem {m : MiniTreeCode} {inner : RegChain} {ζ : ℤˣ} {p q : ℕ} {s u : ℝ}
    (hs : s ∈ Icc (p : ℝ) (p + 1)) (hu : u ∈ Icc (q : ℝ) (q + 1)) :
    (fun t => cupR m inner ζ s u t) ∈ timeBox ((tc2aQR m inner ζ p q 0 : ℕ) : ℝ) (tc2aQR m inner ζ p q 1) := by
  refine ⟨?_, ?_⟩ <;> simp only [cupR, tc2aQR] <;> split_ifs <;> assumption

theorem tc2a_cupG_mem {m : MiniTreeCode} {inner : RegChain} {ζ : ℤˣ} {p q : ℕ} {s u : ℝ}
    (hs : s ∈ Icc (p : ℝ) (p + 1)) (hu : u ∈ Icc (q : ℝ) (q + 1)) :
    (fun t => cupG m inner ζ s u t) ∈ timeBox ((tc2aQG m inner ζ p q 0 : ℕ) : ℝ) (tc2aQG m inner ζ p q 1) := by
  refine ⟨?_, ?_⟩ <;> simp only [cupG, tc2aQG] <;> split_ifs <;> assumption

theorem tc2a_cupR_cont (m : MiniTreeCode) (inner : RegChain) (ζ : ℤˣ) (s : ℝ) :
    Continuous fun u : ℝ => (fun t : Fin 2 => cupR m inner ζ s u t) :=
  continuous_pi fun t => by unfold cupR; split_ifs <;> fun_prop

theorem tc2a_cupG_cont (m : MiniTreeCode) (inner : RegChain) (ζ : ℤˣ) (s : ℝ) :
    Continuous fun u : ℝ => (fun t : Fin 2 => cupG m inner ζ s u t) :=
  continuous_pi fun t => by unfold cupG; split_ifs <;> fun_prop

theorem tc2a_bPath_ne (m : MiniTreeCode) (inner : RegChain) (i j : Fin 3) : bPath m inner ++ [i] ≠ [j] := by
  intro h
  have := congrArg List.length h
  simp [bPath] at this

section Data

variable {LG : LayeredGarden 2} {m : MiniTreeCode} {Qr Qg : RegCpl} {inner : RegChain}
  {LGZ : LayeredGarden 1} {LGB : LayeredGarden 2} (D : Root2Data LG m Qr Qg inner LGZ LGB)
  {LGi : LayeredGarden 1} {LGr LGg : LayeredGarden 2} (P : PairOnly LGZ m Qr Qg inner LGi LGr LGg)
include D P

theorem tc2a_rootB0_le {p : ℕ} (hle : ∀ a, LG.layer a ≤ p) :
    LGB.layer (GNode.root LGB.garden.tree 0) ≤ layerAt LG ((0 : Fin 2), bPath m inner) := by
  have hm := (D.gd.ι₂ (GNode.root LGB.garden.tree 0)).2
  have e : (D.gd.ι₂ (GNode.root LGB.garden.tree 0)).1 = addrExt ((0 : Fin 2), bPath m inner) [m.lone] := by
    show botAddr (cpair m Qr Qg inner).lonePath (GNode.root LGB.garden.tree 0).1 = _
    simp [botAddr, GNode.root, addrExt, tc2a_lone_path D P, bPath]
  rw [D.layB, show botAddr (cpair m Qr Qg inner).lonePath (GNode.root LGB.garden.tree 0).1 =
    (D.gd.ι₂ (GNode.root LGB.garden.tree 0)).1 from rfl, e]
  rw [e] at hm
  exact tc2a_child_le LG hle _ m.lone hm

theorem tc2a_rootI_le {p : ℕ} (hle : ∀ a, LG.layer a ≤ p) (hj : layerAt LG ((0 : Fin 2), []) = p) :
    LGi.layer (GNode.root LGi.garden.tree 0) ≤ p := by
  have hm : (addrExt ((0 : Fin 2), ([] : TTree.Path)) [m.c]).2 ∈
      (LG.garden.tree (addrExt ((0 : Fin 2), ([] : TTree.Path)) [m.c]).1).nodes :=
    (D.gd.ι₁ (P.hp.ιi (GNode.root LGi.garden.tree 0))).2
  rw [← layerAt_node, tc2a_layI D P _ (GNode.root LGi.garden.tree 0).2, ← hj]
  exact tc2a_child_le LG hle _ m.c hm

theorem tc2a_loneI : ∀ a : GNode LGi.garden.tree, a.1.2 = inner.lonePath →
    LGi.layer a = layerAt LG ((0 : Fin 2), bPath m inner) := by
  intro a ha
  rw [← layerAt_node, tc2a_layI D P a.1 a.2, ha]
  rfl

theorem tc2a_rootR_le {p : ℕ} (hle : ∀ a, LG.layer a ≤ p) (hj : layerAt LG ((0 : Fin 2), []) = p) (t : Fin 2) :
    LGr.layer (GNode.root LGr.garden.tree t) ≤
      tc2aQR m inner (LGZ.garden.sig 0) p (layerAt LG ((0 : Fin 2), bPath m inner)) t := by
  have hm : rBase m inner (LGZ.garden.sig 0) t ++ [] ∈ (LG.garden.tree 0).nodes :=
    (D.gd.ι₁ (P.hp.ιr (GNode.root LGr.garden.tree t))).2
  rw [List.append_nil] at hm
  rw [← layerAt_node, tc2a_layR D P _ (GNode.root LGr.garden.tree t).2]
  show layerAt LG ((0 : Fin 2), rBase m inner (LGZ.garden.sig 0) t ++ []) ≤ _
  rw [List.append_nil]
  unfold tc2aQR
  rcases rBase_cases m inner (LGZ.garden.sig 0) t with h | h
  · rw [if_pos h, ← hj]
    rw [h] at hm ⊢
    exact tc2a_child_le LG hle ((0 : Fin 2), []) m.red.1 hm
  · rw [if_neg (by rw [h]; exact tc2a_bPath_ne m inner _ _)]
    rw [h] at hm ⊢
    have e : ((0 : Fin 2), bPath m inner ++ [m.red.2]) = addrExt ((0 : Fin 2), bPath m inner) [m.red.2] := by
      simp [addrExt]
    rw [e]
    exact tc2a_child_le LG hle _ m.red.2 (by rw [← e]; exact hm)

theorem tc2a_rootG_le {p : ℕ} (hle : ∀ a, LG.layer a ≤ p) (hj : layerAt LG ((0 : Fin 2), []) = p) (t : Fin 2) :
    LGg.layer (GNode.root LGg.garden.tree t) ≤
      tc2aQG m inner (LGZ.garden.sig 0) p (layerAt LG ((0 : Fin 2), bPath m inner)) t := by
  have hm : gBase m inner (LGZ.garden.sig 0) t ++ [] ∈ (LG.garden.tree 0).nodes :=
    (D.gd.ι₁ (P.hp.ιg (GNode.root LGg.garden.tree t))).2
  rw [List.append_nil] at hm
  rw [← layerAt_node, tc2a_layG D P _ (GNode.root LGg.garden.tree t).2]
  show layerAt LG ((0 : Fin 2), gBase m inner (LGZ.garden.sig 0) t ++ []) ≤ _
  rw [List.append_nil]
  unfold tc2aQG
  have hg : gBase m inner (LGZ.garden.sig 0) t = [m.green.1] ∨
      gBase m inner (LGZ.garden.sig 0) t = bPath m inner ++ [m.green.2] := by
    unfold gBase; split_ifs <;> simp
  rcases hg with h | h
  · rw [if_pos h, ← hj]
    rw [h] at hm ⊢
    exact tc2a_child_le LG hle ((0 : Fin 2), []) m.green.1 hm
  · rw [if_neg (by rw [h]; exact tc2a_bPath_ne m inner _ _)]
    rw [h] at hm ⊢
    have e : ((0 : Fin 2), bPath m inner ++ [m.green.2]) = addrExt ((0 : Fin 2), bPath m inner) [m.green.2] := by
      simp [addrExt]
    rw [e]
    exact tc2a_child_le LG hle _ m.green.2 (by rw [← e]; exact hm)

theorem tc2a_qR_le {p : ℕ} (hle : ∀ a, LG.layer a ≤ p) (t : Fin 2) :
    tc2aQR m inner (LGZ.garden.sig 0) p (layerAt LG ((0 : Fin 2), bPath m inner)) t ≤ p := by
  unfold tc2aQR; split_ifs
  · exact le_rfl
  · exact layerAt_le_of_forall_layer_le hle _

theorem tc2a_qG_le {p : ℕ} (hle : ∀ a, LG.layer a ≤ p) (t : Fin 2) :
    tc2aQG m inner (LGZ.garden.sig 0) p (layerAt LG ((0 : Fin 2), bPath m inner)) t ≤ p := by
  unfold tc2aQG; split_ifs
  · exact le_rfl
  · exact layerAt_le_of_forall_layer_le hle _

end Data

end WaveTurbulence.Flower.ProtPin
