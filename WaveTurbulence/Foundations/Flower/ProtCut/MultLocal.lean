/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.Flower.ProtCut.CapCut

/-! # D2c PROT-CUT: branch-local multipliers factor at the cut

* `bstar K b`: the star `(K b, K b0, K b1, K b2)` of a branching node; `starFilt_local`: for star nodes on branching
  nodes, `starWeight · filtWeight · filtWeight` is a product over branches of a function of their stars (`fD3`).
* **`CutTermData.multFactors_local`**: `K ↦ (∏_b f b (bstar K b)) · g (bstar K 𝔫_b)` satisfies `MultFactors`, with
  explicit factors; `multFactors_local_bound` bounds them.
* **`CutTermData.multFactors_D3`**: D3's multiplier `starWeight S ω · filtWeight F ann M · filtWeight Fu false Mu · ind`
  (`S` on branching nodes, `ind` a `TermChildIndicator`) satisfies `MultFactors`.
* `CapData.capM_local`, `CapData.termChild_cap`: the same for a cap couple through `CapData.capM`. -/

@[expose] public section
set_option autoImplicit false
noncomputable section
open WaveTurbulence WaveTurbulence.LGSpine Set Finset MeasureTheory
open WaveTurbulence.Flower.FlShell (chiD)

namespace WaveTurbulence.Flower.ProtCut

open TTree WaveTurbulence.Links WaveTurbulence.Reg WaveTurbulence.PL234
open WaveTurbulence.Flower.ProtDefs

variable {w d : ℕ}

/-! ### Stars of branching nodes -/

/-- The star `(K b, K b0, K b1, K b2)` of a branching node. -/
def bstar {T : Fin w → TTree} (K : GNode T → Mom d) (b : GBranch T) : Fin 4 → Mom d :=
  Fin.cases (K b.toNode) fun i => K (b.child i)

theorem starNode_branch {T : Fin w → TTree} (b : GBranch T) (s : Fin 4) :
    IncTop.starNode b.toNode s = Fin.cases b.toNode (fun i => b.child i) s := by
  unfold IncTop.starNode
  split_ifs with h
  · rfl
  · exact absurd b.2 h

theorem starMomenta_branch {T : Fin w → TTree} (K : GNode T → Mom d) (b : GBranch T) :
    IncTop.starMomenta K b.toNode = WithLp.toLp 2 (bstar K b) := by
  unfold IncTop.starMomenta
  congr 1
  funext s
  rw [starNode_branch]
  refine Fin.cases rfl (fun j => rfl) s

/-- One branch's factor of `starWeight S ω · filtWeight F ann M · filtWeight Fu false Mu`. -/
def fD3 {G : Garden w} (S : Finset (GNode G.tree)) (ω : GNode G.tree → IncTop.Star d → ℂ)
    (F : Finset (GBranch G.tree)) (ann : GBranch G.tree → Bool) (M : GBranch G.tree → ℝ)
    (Fu : Finset (GBranch G.tree)) (Mu : GBranch G.tree → ℝ) (b : GBranch G.tree) (ξ : Fin 4 → Mom d) : ℂ :=
  (if b.toNode ∈ S then ω b.toNode (WithLp.toLp 2 ξ) else 1) *
    ((if b ∈ F then (((if ann b then chiD else chi0) (|resFactor (ξ 1) (ξ 2) (ξ 3) (ξ 0)| / M b) : ℝ) : ℂ)
      else 1) *
     (if b ∈ Fu then (((if (fun _ : GBranch G.tree => false) b then chiD else chi0)
        (|resFactor (ξ 1) (ξ 2) (ξ 3) (ξ 0)| / Mu b) : ℝ) : ℂ) else 1))

theorem prod_branchNodes {G : Garden w} {α : Type*} [CommMonoid α] (S : Finset (GNode G.tree))
    (hS : ∀ a ∈ S, a.1.2 ∈ (G.tree a.1.1).branching) (φ : GNode G.tree → α) :
    ∏ a ∈ S, φ a = ∏ b : GBranch G.tree, if b.toNode ∈ S then φ b.toNode else 1 := by
  rw [← Finset.prod_filter]
  let e : GBranch G.tree ↪ GNode G.tree :=
    ⟨GBranch.toNode, fun b b' h => Subtype.ext (by have := congrArg (fun a : GNode G.tree => a.1) h; exact this)⟩
  have hS' : S = (Finset.univ.filter fun b : GBranch G.tree => b.toNode ∈ S).map e := by
    ext a
    simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · intro ha
      exact ⟨⟨a.1, hS a ha⟩, ha, rfl⟩
    · rintro ⟨b, hb, rfl⟩
      exact hb
  have h := Finset.prod_map (Finset.univ.filter fun b : GBranch G.tree => b.toNode ∈ S) e φ
  rw [← hS'] at h
  exact h

theorem prod_finsetBranch {G : Garden w} {α : Type*} [CommMonoid α] (F : Finset (GBranch G.tree))
    (φ : GBranch G.tree → α) : ∏ b ∈ F, φ b = ∏ b : GBranch G.tree, if b ∈ F then φ b else 1 := by
  rw [← Finset.prod_filter]
  congr 1
  ext b
  simp

/-- **`starWeight · filtWeight · filtWeight` is branch-local** (star nodes on branching nodes). -/
theorem starFilt_local {G : Garden w} (S : Finset (GNode G.tree)) (hS : ∀ a ∈ S, a.1.2 ∈ (G.tree a.1.1).branching)
    (ω : GNode G.tree → IncTop.Star d → ℂ) (F : Finset (GBranch G.tree)) (ann : GBranch G.tree → Bool)
    (M : GBranch G.tree → ℝ) (Fu : Finset (GBranch G.tree)) (Mu : GBranch G.tree → ℝ) (K : GNode G.tree → Mom d) :
    IncTop.starWeight S ω K * filtWeight F ann M K * filtWeight Fu (fun _ => false) Mu K =
      ∏ b : GBranch G.tree, fD3 S ω F ann M Fu Mu b (bstar K b) := by
  unfold IncTop.starWeight filtWeight fD3
  rw [prod_branchNodes S hS, prod_finsetBranch F, prod_finsetBranch Fu, ← Finset.prod_mul_distrib,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun b _ => ?_
  rw [starMomenta_branch, mul_assoc]
  rfl

/-- A terminal-child indicator read on a star of the terminal node. -/
def indB {T : Fin w → TTree} (ind : (GNode T → Mom d) → ℝ) (B : Fin 4 → Mom d) : ℝ :=
  ind fun a => if h : a.1.2 ≠ [] then B (a.1.2.getLast h).succ else 0

/-! ### The cut of a branch-local multiplier -/

namespace CutTermData

variable {LG LGp LGi : LayeredGarden 1} {LGr LGg : LayeredGarden 2} {Xp : RegChain} {m : MiniTreeCode}
  {Qr Qg : RegCpl} {inner : RegChain} (D : CutTermData LG Xp m Qr Qg inner LGp LGi LGr LGg)
include D

/-- The linked node `𝔫_a`. -/
def aBr : GBranch LG.garden.tree :=
  ⟨((0 : Fin 1), Xp.lonePath), by
    obtain ⟨GZ, hs, hZ⟩ := D.exists_GZ
    have h := ((D.gd hZ hs).ofSum (.inr (D.hp hZ hs).rootB)).2
    rw [glue_ofSum_inr_path] at h
    simpa [PairData.rootB] using h⟩

/-- The terminal node `𝔫_b`. -/
def bBr : GBranch LG.garden.tree :=
  ⟨((0 : Fin 1), Xp.lonePath ++ bPath m inner), by
    obtain ⟨GZ, hs, hZ⟩ := D.exists_GZ
    have h := ((D.gd hZ hs).ofSum (.inr (D.hp hZ hs).bB)).2
    rw [glue_ofSum_inr_path] at h
    simpa [PairData.bB] using h⟩

/-- The branches of the prefix in the protected tree. -/
def βP (x : GBranch LGp.garden.tree) : GBranch LG.garden.tree :=
  ⟨((0 : Fin 1), x.1.2), by
    obtain ⟨GZ, hs, hZ⟩ := D.exists_GZ
    exact ((D.gd hZ hs).ofSum (.inl x)).2⟩

/-- The branches of the interior in the protected tree. -/
def βI (x : GBranch LGi.garden.tree) : GBranch LG.garden.tree :=
  ⟨((0 : Fin 1), Xp.lonePath ++ m.c :: x.1.2), by
    obtain ⟨GZ, hs, hZ⟩ := D.exists_GZ
    have h := ((D.gd hZ hs).ofSum (.inr ((D.hp hZ hs).βi x))).2
    rw [glue_ofSum_inr_path] at h
    simpa [PairData.βi] using h⟩

/-- The branches of the red side couple in the protected tree. -/
def βR (y : GBranch LGr.garden.tree) : GBranch LG.garden.tree :=
  ⟨((0 : Fin 1), Xp.lonePath ++ (rBase m inner (LG.garden.sig 0) y.1.1 ++ y.1.2)), by
    obtain ⟨GZ, hs, hZ⟩ := D.exists_GZ
    have h := ((D.gd hZ hs).ofSum (.inr ((D.hp hZ hs).βr y))).2
    rw [glue_ofSum_inr_path] at h
    simpa [PairData.βr, hs] using h⟩

/-- The branches of the green side couple in the protected tree. -/
def βG (y : GBranch LGg.garden.tree) : GBranch LG.garden.tree :=
  ⟨((0 : Fin 1), Xp.lonePath ++ (gBase m inner (LG.garden.sig 0) y.1.1 ++ y.1.2)), by
    obtain ⟨GZ, hs, hZ⟩ := D.exists_GZ
    have h := ((D.gd hZ hs).ofSum (.inr ((D.hp hZ hs).βg y))).2
    rw [glue_ofSum_inr_path] at h
    simpa [PairData.βg, hs] using h⟩

theorem bstar_aBr (K : GNode LG.garden.tree → Mom d) :
    (fun i => extend K (aAddr Xp i)) = bstar K D.aBr := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact extend_node K D.aBr.toNode
  · exact extend_node K (D.aBr.child j)

theorem bstar_bBr (K : GNode LG.garden.tree → Mom d) :
    (fun i => extend K (bAddr Xp m inner i)) = bstar K D.bBr := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact extend_node K D.bBr.toNode
  · rw [show bAddr Xp m inner j.succ = (D.bBr.child j).1 by simp [bAddr, bBr, GBranch.child]]
    exact extend_node K (D.bBr.child j)

theorem bstar_βP (K : GNode LG.garden.tree → Mom d) (x : GBranch LGp.garden.tree) :
    bstar K (D.βP x) = bstar (K ∘ D.ιP) x := by
  funext i
  exact Fin.cases rfl (fun j => rfl) i

theorem bstar_βI (K : GNode LG.garden.tree → Mom d) (x : GBranch LGi.garden.tree) :
    bstar K (D.βI x) = bstar (K ∘ D.ιI) x := by
  funext i
  refine Fin.cases rfl (fun j => ?_) i
  exact congrArg K (Subtype.ext (by simp [βI, ιI, GBranch.child, GBranch.toNode]))

theorem bstar_βR (K : GNode LG.garden.tree → Mom d) (y : GBranch LGr.garden.tree) :
    bstar K (D.βR y) = bstar (K ∘ D.ιR) y := by
  funext i
  refine Fin.cases rfl (fun j => ?_) i
  exact congrArg K (Subtype.ext (by simp [βR, ιR, GBranch.child, GBranch.toNode]))

theorem bstar_βG (K : GNode LG.garden.tree → Mom d) (y : GBranch LGg.garden.tree) :
    bstar K (D.βG y) = bstar (K ∘ D.ιG) y := by
  funext i
  refine Fin.cases rfl (fun j => ?_) i
  exact congrArg K (Subtype.ext (by simp [βG, ιG, GBranch.child, GBranch.toNode]))

section Split

variable {GZ : Garden 1} (hZ : (cpair m Qr Qg inner).DecodesTree GZ) (hsZ : GZ.sig 0 = LG.garden.sig 0)
include hZ hsZ

theorem ofSum_P (x : GBranch LGp.garden.tree) : (D.gd hZ hsZ).ofSum (.inl x) = D.βP x := rfl

theorem ofSum_I (x : GBranch LGi.garden.tree) : (D.gd hZ hsZ).ofSum (.inr ((D.hp hZ hsZ).βi x)) = D.βI x :=
  Subtype.ext (by rw [glue_ofSum_inr_path]; simp [βI, PairData.βi])

theorem ofSum_R (y : GBranch LGr.garden.tree) : (D.gd hZ hsZ).ofSum (.inr ((D.hp hZ hsZ).βr y)) = D.βR y :=
  Subtype.ext (by rw [glue_ofSum_inr_path]; simp [βR, PairData.βr, hsZ])

theorem ofSum_G (y : GBranch LGg.garden.tree) : (D.gd hZ hsZ).ofSum (.inr ((D.hp hZ hsZ).βg y)) = D.βG y :=
  Subtype.ext (by rw [glue_ofSum_inr_path]; simp [βG, PairData.βg, hsZ])

theorem ofSum_a : (D.gd hZ hsZ).ofSum (.inr (D.hp hZ hsZ).rootB) = D.aBr :=
  Subtype.ext (by rw [glue_ofSum_inr_path]; simp [aBr, PairData.rootB])

theorem ofSum_b : (D.gd hZ hsZ).ofSum (.inr (D.hp hZ hsZ).bB) = D.bBr :=
  Subtype.ext (by rw [glue_ofSum_inr_path]; simp [bBr, PairData.bB])

/-- Products over the branches of the protected tree split at the cut. -/
theorem prod_branch_cut {α : Type*} [CommMonoid α] (φ : GBranch LG.garden.tree → α) :
    ∏ b, φ b = φ D.aBr * φ D.bBr * ((∏ x, φ (D.βP x)) * ((∏ x, φ (D.βI x)) * ((∏ y, φ (D.βR y)) *
      ∏ y, φ (D.βG y)))) := by
  rw [(D.gd hZ hsZ).prod_branch, (D.hp hZ hsZ).prod_pairBranch]
  simp only [D.ofSum_P hZ hsZ, D.ofSum_I hZ hsZ, D.ofSum_R hZ hsZ, D.ofSum_G hZ hsZ, D.ofSum_a hZ hsZ,
    D.ofSum_b hZ hsZ]
  exact mul_left_comm _ _ _

end Split

/-- **A branch-local multiplier factors at the cut.** -/
theorem multFactors_local (f : GBranch LG.garden.tree → (Fin 4 → Mom d) → ℂ) (g : (Fin 4 → Mom d) → ℂ) :
    D.MultFactors (fun K => (∏ b, f b (bstar K b)) * g (bstar K D.bBr))
      (fun A B => f D.aBr A * f D.bBr B * g B)
      (fun K => ∏ x, f (D.βP x) (bstar K x)) (fun K => ∏ x, f (D.βI x) (bstar K x))
      (fun K => ∏ y, f (D.βR y) (bstar K y)) (fun K => ∏ y, f (D.βG y) (bstar K y)) := by
  intro K
  obtain ⟨GZ, hs, hZ⟩ := D.exists_GZ
  simp only
  rw [D.bstar_aBr K, D.bstar_bBr K, D.prod_branch_cut hZ hs]
  simp only [D.bstar_βP, D.bstar_βI, D.bstar_βR, D.bstar_βG]
  ring

/-- Bounds for the factors of a branch-local multiplier. -/
theorem multFactors_local_bound (f : GBranch LG.garden.tree → (Fin 4 → Mom d) → ℂ) (g : (Fin 4 → Mom d) → ℂ)
    (Cf : GBranch LG.garden.tree → ℝ) (hf : ∀ b ξ, ‖f b ξ‖ ≤ Cf b) (hC : ∀ b, 1 ≤ Cf b) (Cg : ℝ)
    (hg : ∀ ξ, ‖g ξ‖ ≤ Cg) (hCg : 1 ≤ Cg) :
    (∀ A B, ‖f D.aBr A * f D.bBr B * g B‖ ≤ Cg * ∏ b, Cf b) ∧
    (∀ K, ‖∏ x, f (D.βP x) (bstar K x)‖ ≤ Cg * ∏ b, Cf b) ∧
    (∀ K, ‖∏ x, f (D.βI x) (bstar K x)‖ ≤ Cg * ∏ b, Cf b) ∧
    (∀ K, ‖∏ y, f (D.βR y) (bstar K y)‖ ≤ Cg * ∏ b, Cf b) ∧
    (∀ K, ‖∏ y, f (D.βG y) (bstar K y)‖ ≤ Cg * ∏ b, Cf b) := by
  obtain ⟨GZ, hs, hZ⟩ := D.exists_GZ
  have h0 : ∀ b, 0 ≤ Cf b := fun b => zero_le_one.trans (hC b)
  have one_le : ∀ {ι : Type _} [Fintype ι] (φ : ι → GBranch LG.garden.tree), 1 ≤ ∏ x, Cf (φ x) := by
    intro ι _ φ
    calc (1 : ℝ) = ∏ _x : ι, (1 : ℝ) := Finset.prod_const_one.symm
      _ ≤ ∏ x, Cf (φ x) := Finset.prod_le_prod₀ (fun _ _ => zero_le_one) (fun x _ => hC (φ x))
  have hnorm : ∀ {ι : Type _} [Fintype ι] (φ : ι → GBranch LG.garden.tree) (K' : ι → Fin 4 → Mom d),
      ‖∏ x, f (φ x) (K' x)‖ ≤ ∏ x, Cf (φ x) := by
    intro ι _ φ K'
    rw [norm_prod]
    exact Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun x _ => hf _ _)
  have htot := D.prod_branch_cut hZ hs Cf
  set P := ∏ x, Cf (D.βP x)
  set I := ∏ x, Cf (D.βI x)
  set R := ∏ y, Cf (D.βR y)
  set G := ∏ y, Cf (D.βG y)
  have hP : 1 ≤ P := one_le _
  have hI : 1 ≤ I := one_le _
  have hR : 1 ≤ R := one_le _
  have hG : 1 ≤ G := one_le _
  have ha := hC D.aBr
  have hb := hC D.bBr
  have key : ∀ x : ℝ, 0 ≤ x → x ≤ P ∨ x ≤ I ∨ x ≤ R ∨ x ≤ G ∨ x ≤ Cf D.aBr * Cf D.bBr * Cg →
      x ≤ Cg * ∏ b, Cf b := by
    intro x hx hcase
    rw [htot]
    have e1 : 1 ≤ Cf D.aBr * Cf D.bBr := one_le_mul_of_one_le_of_one_le ha hb
    have e2 : 1 ≤ I * (R * G) := one_le_mul_of_one_le_of_one_le hI (one_le_mul_of_one_le_of_one_le hR hG)
    have e3 : 1 ≤ R * G := one_le_mul_of_one_le_of_one_le hR hG
    have hP0 : 0 ≤ P := zero_le_one.trans hP
    have hI0 : 0 ≤ I := zero_le_one.trans hI
    have hR0 : 0 ≤ R := zero_le_one.trans hR
    have hG0 : 0 ≤ G := zero_le_one.trans hG
    have hCg0 : 0 ≤ Cg := zero_le_one.trans hCg
    have hab0 : 0 ≤ Cf D.aBr * Cf D.bBr := zero_le_one.trans e1
    rcases hcase with h | h | h | h | h
    · calc x ≤ P := h
        _ ≤ (Cg * (Cf D.aBr * Cf D.bBr) * (I * (R * G))) * P :=
          le_mul_of_one_le_left hP0 (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hCg e1) e2)
        _ = _ := by ring
    · calc x ≤ I := h
        _ ≤ (Cg * (Cf D.aBr * Cf D.bBr) * P * (R * G)) * I :=
          le_mul_of_one_le_left hI0 (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
              (one_le_mul_of_one_le_of_one_le hCg e1) hP) e3)
        _ = _ := by ring
    · calc x ≤ R := h
        _ ≤ (Cg * (Cf D.aBr * Cf D.bBr) * P * (I * G)) * R :=
          le_mul_of_one_le_left hR0 (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
              (one_le_mul_of_one_le_of_one_le hCg e1) hP) (one_le_mul_of_one_le_of_one_le hI hG))
        _ = _ := by ring
    · calc x ≤ G := h
        _ ≤ (Cg * (Cf D.aBr * Cf D.bBr) * P * (I * R)) * G :=
          le_mul_of_one_le_left hG0 (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
              (one_le_mul_of_one_le_of_one_le hCg e1) hP) (one_le_mul_of_one_le_of_one_le hI hR))
        _ = _ := by ring
    · calc x ≤ Cf D.aBr * Cf D.bBr * Cg := h
        _ ≤ (P * (I * (R * G))) * (Cf D.aBr * Cf D.bBr * Cg) :=
          le_mul_of_one_le_left (mul_nonneg hab0 hCg0) (one_le_mul_of_one_le_of_one_le hP e2)
        _ = _ := by ring
  refine ⟨fun A B => key _ (norm_nonneg _) (Or.inr (Or.inr (Or.inr (Or.inr ?_)))),
    fun K => key _ (norm_nonneg _) (Or.inl (hnorm _ _)),
    fun K => key _ (norm_nonneg _) (Or.inr (Or.inl (hnorm _ _))),
    fun K => key _ (norm_nonneg _) (Or.inr (Or.inr (Or.inl (hnorm _ _)))),
    fun K => key _ (norm_nonneg _) (Or.inr (Or.inr (Or.inr (Or.inl (hnorm _ _)))))⟩
  rw [norm_mul, norm_mul]
  exact mul_le_mul (mul_le_mul (hf _ _) (hf _ _) (norm_nonneg _) (h0 _)) (hg _) (norm_nonneg _)
    (mul_nonneg (h0 _) (h0 _))

/-! ### The terminal indicator -/

theorem ind_eq (ind : (GNode LG.garden.tree → Mom d) → ℝ)
    (hind : TermChildIndicator (appendChain Xp (cpair m Qr Qg inner)) ind) (K : GNode LG.garden.tree → Mom d) :
    ind K = indB ind (bstar K D.bBr) := by
  unfold indB
  refine hind.2 _ _ fun a _ hne hd => ?_
  rw [dif_pos hne]
  show K a = K (D.bBr.child (a.1.2.getLast hne))
  refine congrArg K (Subtype.ext (Prod.ext (Subsingleton.elim _ _) ?_))
  show a.1.2 = Xp.lonePath ++ bPath m inner ++ [a.1.2.getLast hne]
  rw [← lonePath_dropLast_cutTerm, ← hd, List.dropLast_append_getLast]

/-- **D3's multiplier factors at the cut** (star nodes on branching nodes, `ind` a terminal-child indicator). -/
theorem multFactors_D3 (S : Finset (GNode LG.garden.tree)) (hS : ∀ a ∈ S, a.1.2 ∈ (LG.garden.tree a.1.1).branching)
    (ω : GNode LG.garden.tree → IncTop.Star d → ℂ) (F : Finset (GBranch LG.garden.tree))
    (ann : GBranch LG.garden.tree → Bool) (M : GBranch LG.garden.tree → ℝ) (Fu : Finset (GBranch LG.garden.tree))
    (Mu : GBranch LG.garden.tree → ℝ) (ind : (GNode LG.garden.tree → Mom d) → ℝ)
    (hind : TermChildIndicator (appendChain Xp (cpair m Qr Qg inner)) ind) :
    D.MultFactors
      (fun κ => IncTop.starWeight S ω κ * filtWeight F ann M κ * filtWeight Fu (fun _ => false) Mu κ * (ind κ : ℂ))
      (fun A B => fD3 S ω F ann M Fu Mu D.aBr A * fD3 S ω F ann M Fu Mu D.bBr B * ((indB ind B : ℝ) : ℂ))
      (fun K => ∏ x, fD3 S ω F ann M Fu Mu (D.βP x) (bstar K x))
      (fun K => ∏ x, fD3 S ω F ann M Fu Mu (D.βI x) (bstar K x))
      (fun K => ∏ y, fD3 S ω F ann M Fu Mu (D.βR y) (bstar K y))
      (fun K => ∏ y, fD3 S ω F ann M Fu Mu (D.βG y) (bstar K y)) := by
  intro K
  have h := D.multFactors_local (fD3 S ω F ann M Fu Mu) (fun B => ((indB ind B : ℝ) : ℂ)) K
  simp only at h ⊢
  rw [starFilt_local S hS, D.ind_eq ind hind K]
  exact h

end CutTermData

/-! ### Cap couples -/

namespace CapData

variable {X : RegChain} {LG : LayeredGarden 2} {LG1 : LayeredGarden 1} (D : CapData X LG LG1)
include D

theorem bstar_cap (K : GNode LG1.garden.tree → Mom d) (b : GBranch LG1.garden.tree) :
    bstar (fun a => K (D.ρ a)) (D.βc b) = bstar K b := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact congrArg K (D.ρ_ι b.toNode)
  · exact congrArg K (D.ρ_ι (b.child j))

/-- **A branch-local multiplier of the cap couple is branch-local on the paired tree.** -/
theorem capM_local (f : GBranch LG.garden.tree → (Fin 4 → Mom d) → ℂ) (h : (GNode LG.garden.tree → Mom d) → ℂ)
    (K : GNode LG1.garden.tree → Mom d) :
    D.capM (fun K' => (∏ b, f b (bstar K' b)) * h K') K =
      (∏ b, f (D.βc b) (bstar K b)) * h (fun a => K (D.ρ a)) := by
  unfold capM
  simp only
  rw [← D.βc.prod_comp]
  simp only [D.bstar_cap]

/-- The terminal-child indicator of the paired tree. -/
theorem termChild_cap (ind : (GNode LG.garden.tree → Mom d) → ℝ) (hind : TermChildIndicator X ind) :
    TermChildIndicator X (fun K : GNode LG1.garden.tree → Mom d => ind fun a => K (D.ρ a)) := by
  refine ⟨fun K => hind.1 _, fun K K' hKK => hind.2 _ _ fun a ha hne hd => ?_⟩
  have e := D.ρ_val a ((Fin.val_eq_zero_iff).1 ha)
  refine hKK (D.ρ a) (by simp) ?_ ?_
  · rw [e]; exact hne
  · rw [e]; exact hd

omit D in
/-- **D3's multiplier of a cap couple factors at the cut of its paired tree.** -/
theorem multFactors_D3_cap {LG : LayeredGarden 2} {LG1 LGp LGi : LayeredGarden 1} {LGr LGg : LayeredGarden 2}
    {Xp : RegChain} {m : MiniTreeCode} {Qr Qg : RegCpl} {inner : RegChain}
    (D : CapData (appendChain Xp (cpair m Qr Qg inner)) LG LG1)
    (C : CutTermData LG1 Xp m Qr Qg inner LGp LGi LGr LGg)
    (S : Finset (GNode LG.garden.tree)) (hS : ∀ a ∈ S, a.1.2 ∈ (LG.garden.tree a.1.1).branching)
    (ω : GNode LG.garden.tree → IncTop.Star d → ℂ) (F : Finset (GBranch LG.garden.tree))
    (ann : GBranch LG.garden.tree → Bool) (M : GBranch LG.garden.tree → ℝ) (Fu : Finset (GBranch LG.garden.tree))
    (Mu : GBranch LG.garden.tree → ℝ) (ind : (GNode LG.garden.tree → Mom d) → ℝ)
    (hind : TermChildIndicator (appendChain Xp (cpair m Qr Qg inner)) ind) :
    C.MultFactors
      (D.capM fun κ =>
        IncTop.starWeight S ω κ * filtWeight F ann M κ * filtWeight Fu (fun _ => false) Mu κ * (ind κ : ℂ))
      (fun A B => fD3 S ω F ann M Fu Mu (D.βc C.aBr) A * fD3 S ω F ann M Fu Mu (D.βc C.bBr) B *
        ((indB (fun K1 : GNode LG1.garden.tree → Mom d => ind fun a => K1 (D.ρ a)) B : ℝ) : ℂ))
      (fun K => ∏ x, fD3 S ω F ann M Fu Mu (D.βc (C.βP x)) (bstar K x))
      (fun K => ∏ x, fD3 S ω F ann M Fu Mu (D.βc (C.βI x)) (bstar K x))
      (fun K => ∏ y, fD3 S ω F ann M Fu Mu (D.βc (C.βR y)) (bstar K y))
      (fun K => ∏ y, fD3 S ω F ann M Fu Mu (D.βc (C.βG y)) (bstar K y)) := by
  intro K
  have h := C.multFactors_local (fun b => fD3 S ω F ann M Fu Mu (D.βc b))
    (fun B => ((indB (fun K1 : GNode LG1.garden.tree → Mom d => ind fun a => K1 (D.ρ a)) B : ℝ) : ℂ)) K
  simp only at h ⊢
  have e : D.capM (fun κ => IncTop.starWeight S ω κ * filtWeight F ann M κ *
      filtWeight Fu (fun _ => false) Mu κ * (ind κ : ℂ)) K =
      D.capM (fun K' => (∏ b, fD3 S ω F ann M Fu Mu b (bstar K' b)) * (ind K' : ℂ)) K := by
    unfold capM
    simp only
    rw [starFilt_local S hS]
  have hi := C.ind_eq _ (D.termChild_cap ind hind) K
  rw [e, D.capM_local]
  rw [show (ind fun a => K (D.ρ a)) = indB (fun K1 : GNode LG1.garden.tree → Mom d => ind fun a => K1 (D.ρ a))
    (bstar K C.bBr) from hi]
  exact h

end CapData

end WaveTurbulence.Flower.ProtCut
