/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import WaveTurbulence.Foundations.XChain.X2EDraft.FlowerConds

/-!
# X2E-3, step 10: the flower garden sum

`FlIdx`: `2P`-tuples of flower trees of the kernel family, partitions of their leaves containing the pair blocks,
and lower data on every block. `flIdxGraft`: the flower graft of an index.

**Statements.**
- `flIdxGraft_injective`, `range_flIdxGraft`: the flower graft is a bijection onto the layered gardens of `ℋ_{p+1}` with
  attached orders `≤ N_att`, of kind `kind`, flower signs `ζ ζ_j` and valid pattern (`GateCond`).
- `sum_flIdx_eq_finsum`: sums over the indices are the corresponding `finsum`s over gardens.
- **`sum_flowerKer_eq_finsum_gate`**: X2E-1's main term `∑_{(F_j)} ∑_Q ∑'_κ flowerKerIntegrand` is the gate's garden sum
  `∑ᶠ_{𝒢 ∈ GateCond} gateSummand 𝒢`, given the identification of the cutoff weights (void without cutoffs).
-/

@[expose] public section

namespace WaveTurbulence.X2E

open Finset Induct SysAPI
open scoped Classical

variable {Pm p : ℕ} (Natt Ntr : ℕ) (pat : FixPat) (kind : FlowerKind) (ζ : ℤˣ)

/-- **The indices**: flower trees of the kernel family, a partition with the pair blocks, lower data. -/
abbrev FlIdx (Pm p : ℕ) :=
  Σ tops : Fin (2 * Pm) → ↥(kernelTrees pat Ntr kind ζ),
    Σ P : {P : Finpartition (univ : Finset (GLeaf (ftop (fun j => (tops j).1)))) //
      ∀ j, pbF (fun j => (tops j).1) j ∈ P.parts},
      (B : P.1.parts) → LowerGraftData (sigP (fun j => (tops j).1) P.1 B) p Natt

theorem kernelTrees_sign {F : FTree} (h : F ∈ kernelTrees pat Ntr kind ζ) : F.sign = ζ := (mem_filter.mp h).2.1

/-- The flower graft of an index. -/
noncomputable def flIdxGraft (x : FlIdx Natt Ntr pat kind ζ Pm p) : LayeredGarden (2 * Pm) :=
  ((mkFlowerAt x.2.1.1 x.2.1.2 x.2.2).toData (fun j => kernelTrees_sign Ntr pat kind ζ (x.1 j).2)).flowerGraft

/-- **The gate's conditions** (`flowerSum` without the order). -/
def GateCond (LG : LayeredGarden (2 * Pm)) : Prop :=
  IsCanonH (p + 1) LG ∧ (∀ u ∈ LG.attachNodes p, LG.attachedOrder p u ≤ Natt) ∧
    LG.FlowerKindOK p Ntr kind ∧ (∀ ℓ : GLeaf LG.garden.tree, LG.garden.IsFlower ℓ →
      LG.garden.sign ℓ.toNode = ζ * LG.garden.sig ℓ.1.1) ∧ ∀ j, LG.PatValid p j pat

theorem flIdxGraft_injective : Function.Injective (flIdxGraft (Pm := Pm) (p := p) Natt Ntr pat kind ζ) := by
  rintro ⟨tops₁, ⟨P₁, hP₁⟩, fam₁⟩ ⟨tops₂, ⟨P₂, hP₂⟩, fam₂⟩ h
  have hD := FlowerGraftData.flowerGraft_injective h
  have hfl := congrArg FlowerGraftData.fl hD
  have hb := congrArg FlowerGraftData.base hD
  have htop := congrArg PlainGraftData.top hb
  have ht : tops₁ = tops₂ := funext fun j => Subtype.ext
    (eq_of_toTree_flowerPath (congrFun htop j) (congrFun hfl j))
  subst ht
  injection hb with h1 h2 h3
  cases h2
  have hfam : fam₁ = fam₂ := funext fun B => LowerGraftData.low_injective (congrFun (eq_of_heq h3) B)
  subst hfam
  rfl

theorem gateCond_flIdxGraft (x : FlIdx Natt Ntr pat kind ζ Pm p) (hpat : pat = .plain ∨ pat = .dRoot) :
    GateCond Natt Ntr pat kind ζ (p := p) (flIdxGraft Natt Ntr pat kind ζ x) := by
  obtain ⟨tops, ⟨P, hP⟩, fam⟩ := x
  have hF : ∀ j, (tops j).1 ≠ FTree.flower := fun j => ne_flower_of_mem_kernelTrees pat (tops j).2
  have hsign : ∀ j, ((tops j).1).sign = ζ := fun j => kernelTrees_sign Ntr pat kind ζ (tops j).2
  refine ⟨((mkFlowerAt P hP fam).toData hsign).flowerGraft_isCanonH,
    (attach_iff (mkFlowerAt P hP fam) hsign Natt).mpr fun B => (fam B).order_le,
    (flowerKindOK_iff (mkFlowerAt P hP fam) hsign hF Ntr kind).mpr fun j => (mem_filter.mp (tops j).2).1,
    ((mkFlowerAt P hP fam).toData hsign).flowerGraft_flower_sign,
    (patValid_iff (mkFlowerAt P hP fam) hsign hF pat hpat).mpr fun j => ?_⟩
  obtain ⟨-, -, hF', hv⟩ := mem_filter.mp (tops j).2
  exact hv

/-- The flower signs give the signs of the flower trees. -/
theorem sign_of_flSign {σ ζ' : ℤˣ} {q : TTree.Path} (h : TTree.pathSign σ q = ζ' * σ) : TTree.pathSign 1 q = ζ' := by
  unfold TTree.pathSign at h ⊢
  rw [one_mul]
  rw [mul_comm ζ' σ] at h
  exact mul_left_cancel h

theorem exists_flIdx (D : FlowerGraftData Pm p ζ) (hatt : ∀ u ∈ D.flowerGraft.attachNodes p,
    D.flowerGraft.attachedOrder p u ≤ Natt) (hkind : D.flowerGraft.FlowerKindOK p Ntr kind)
    (hpatv : ∀ j, D.flowerGraft.PatValid p j pat) (hpat : pat = .plain ∨ pat = .dRoot) :
    ∃ x : FlIdx Natt Ntr pat kind ζ Pm p, flIdxGraft Natt Ntr pat kind ζ x = D.flowerGraft := by
  obtain ⟨⟨top, part, low, plain, sign, comp⟩, fl, fl_mem, fl_sign, pair_mem⟩ := D
  obtain ⟨tops, htops⟩ : ∃ tops : Fin (2 * Pm) → FTree, tops = fun j => ofPath (top j) (fl j) := ⟨_, rfl⟩
  have htop : ftop tops = top := by
    rw [htops]
    exact funext fun j => ofPath_toTree (fl_mem j)
  have hfl : ∀ j, (tops j).flowerPath = fl j := fun j => by
    rw [htops]
    exact ofPath_flowerPath (fl_mem j)
  clear htops
  subst htop
  have hfl' : fl = fun j => (tops j).flowerPath := funext fun j => (hfl j).symm
  subst hfl'
  let x0 : FlowerAt Pm p tops := ⟨part, low, plain, sign, comp, pair_mem⟩
  have hsign : ∀ j, (tops j).sign = ζ := fun j => by
    rw [sign_eq_pathSign]
    exact sign_of_flSign (fl_sign j)
  have hpos : ∀ j, 1 ≤ (tops j).order := fun j => by
    rw [← topOrder_toData x0 hsign j]
    cases kind with
    | X => exact (hkind j).1
    | Y => exact Nat.lt_of_le_of_lt (Nat.zero_le _) (hkind j).1
    | W => exact Nat.lt_of_le_of_lt (Nat.zero_le _) (hkind j).1
  have hF : ∀ j, tops j ≠ FTree.flower := fun j h => by
    have := hpos j
    rw [h] at this
    simp [FTree.order] at this
  have hkind' := (flowerKindOK_iff x0 hsign hF Ntr kind).mp hkind
  have hpat' := (patValid_iff x0 hsign hF pat hpat).mp hpatv
  have hatt' := (attach_iff x0 hsign Natt).mp hatt
  have hmem : ∀ j, tops j ∈ kernelTrees pat Ntr kind ζ := fun j =>
    mem_filter.mpr ⟨hkind' j, hsign j, hF j, hpat' j⟩
  refine ⟨⟨fun j => ⟨tops j, hmem j⟩, ⟨part, pair_mem⟩, fun B =>
    ⟨low B, funext (sign B), plain B, comp B, hatt' B⟩⟩, rfl⟩

theorem range_flIdxGraft (hpat : pat = .plain ∨ pat = .dRoot) :
    Set.range (flIdxGraft (Pm := Pm) (p := p) Natt Ntr pat kind ζ) =
      {LG | GateCond Natt Ntr pat kind ζ (p := p) LG} := by
  ext LG
  constructor
  · rintro ⟨x, rfl⟩
    exact gateCond_flIdxGraft Natt Ntr pat kind ζ x hpat
  · rintro ⟨hH, hatt, hkind, hfl, hpatv⟩
    obtain ⟨D, hD⟩ := (flowerGraftEquiv Pm p ζ).surjective ⟨LG, hH, hfl⟩
    have hDLG : D.flowerGraft = LG := congrArg Subtype.val hD
    subst hDLG
    exact exists_flIdx Natt Ntr pat kind ζ D hatt hkind hpatv hpat

/-- **Sums over the indices are garden `finsum`s.** -/
theorem sum_flIdx_eq_finsum (hpat : pat = .plain ∨ pat = .dRoot) (f : LayeredGarden (2 * Pm) → ℂ) :
    ∑ x : FlIdx Natt Ntr pat kind ζ Pm p, f (flIdxGraft Natt Ntr pat kind ζ x) =
      ∑ᶠ (LG : LayeredGarden (2 * Pm)) (_ : GateCond Natt Ntr pat kind ζ (p := p) LG), f LG := by
  have h := finsum_mem_range (f := f) (flIdxGraft_injective (Pm := Pm) (p := p) Natt Ntr pat kind ζ)
  rw [range_flIdxGraft Natt Ntr pat kind ζ hpat,
    finsum_eq_sum_of_fintype (fun x : FlIdx Natt Ntr pat kind ζ Pm p => f (flIdxGraft Natt Ntr pat kind ζ x))] at h
  exact h.symm

/-! ## Assembly -/

section Assembly

variable (L γ δ : ℝ) {d : ℕ}

/-- **X2E-1's main term is the gate's garden sum** (given the identification of the cutoff weights). -/
theorem sum_flowerKer_eq_finsum_gate (F : ℕ → Mom d → ℝ)
    (hFs : ∀ q, Summable fun m : Fin d → ℤ => |F q (latticePoint L m)|) (hpat : pat = .plain ∨ pat = .dRoot)
    (dagger : Option (Fin 3 → Mom d)) (cut1 cut2 : Option ℕ)
    (hcut : ∀ x : FlIdx Natt Ntr pat kind ζ Pm p, CutWeightsOK L (d := d)
      (fun j => ne_flower_of_mem_kernelTrees pat (x.1 j).2) (mkFlowerAt x.2.1.1 x.2.1.2 x.2.2)
      (fun j => kernelTrees_sign Ntr pat kind ζ (x.1 j).2) cut1 cut2)
    {t s : ℝ} (hpt : (p : ℝ) ≤ t) (hps : (p : ℝ) ≤ s) (n n' : Fin d → ℤ) :
    ∑ tops : Fin (2 * Pm) → ↥(kernelTrees pat Ntr kind ζ), ∑ Q : Finpartition (nfLeaves (fun j => (tops j).1)),
      ∑' κ : FlowerForestDec (fun j => (tops j).1) d (fun _ => n) (fun _ => n'),
        flowerKerIntegrand L γ δ F (altFlowerSig Pm) (fun j => (tops j).1)
          (fun j => fkCoef L γ δ p pat dagger cut1 cut2 t s (tops j).1) Q p Natt κ =
      ∑ᶠ (LG : LayeredGarden (2 * Pm)) (_ : GateCond Natt Ntr pat kind ζ (p := p) LG),
        gateSummand L γ δ F p pat dagger cut1 cut2 t s n n' LG := by
  rw [← sum_flIdx_eq_finsum Natt Ntr pat kind ζ hpat, Fintype.sum_sigma]
  refine sum_congr rfl fun tops _ => ?_
  rw [Fintype.sum_sigma]
  exact sum_flowerKer_eq_sum_gate L γ δ Natt (fun j => ne_flower_of_mem_kernelTrees pat (tops j).2)
    (fun j => kernelTrees_sign Ntr pat kind ζ (tops j).2) F hFs pat hpat dagger cut1 cut2
    (fun P hP fam => hcut ⟨tops, ⟨P, hP⟩, fam⟩) hpt hps n n'

end Assembly

end WaveTurbulence.X2E
