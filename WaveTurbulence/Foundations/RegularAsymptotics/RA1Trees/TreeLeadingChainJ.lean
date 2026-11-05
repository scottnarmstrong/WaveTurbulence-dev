/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.RegularAsymptotics.RA1Trees.TreeActualRegularizedLimit
public import WaveTurbulence.Foundations.RegAsymp.TreeLimitRebase

/-! # The actual tree limiting integral is the original cancellation chain with its lone-leaf cut -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open MeasureTheory Set ClassJR Cancel MainCoef Links

/-- The actual Gaussian leading coefficient is exactly the landed chainJ recursion,
with the original lone-leaf lower-time indicator kept as its continuation. -/
theorem treeRegularizedLeading_eq_chainJ (Z : Finset Cancel.Addr) (X : RegChain) (ζ : ℤˣ)
    {t s : ℝ} (hs : 0 ≤ s) (hst : s < t) (ht : t ≤ 1) :
    treeRegularizedLeading Z X ζ t s =
      chainJ Z X ζ (rootT ζ) t (fun u => if s < u then 1 else 0) := by
  let L := treePairData X ζ
  let D := kD (fun j => decide (chainSig L j ∈ Z)) (fun j τ _ => pairJ Z (L.getD j dfltP) τ)
  let Dc := fun j τ => D j (clamp01 τ)
  have hag : ChainAgr L X ζ (rootT ζ) 0 := fun k _ => by rw [zero_add]; rfl
  have hD : kD (fun j => decide (chainSig (treePairData X ζ) j ∈ Z))
      (fun j u v => treePairLimit Z X ζ j (clamp01 (u+s)) (clamp01 (v+s))) =
        fun j u => Dc j (u+s) := by
    funext j u
    simp only [kD,treePairLimit,pairJsw_diag,Dc,D,L]
  unfold treeRegularizedLeading
  rw [hD]
  symm
  calc
    _ = chainL D (chainCode X) 0 t (fun u => if s < u then 1 else 0) :=
      (chainL_eq_chainJ Z L X ζ (rootT ζ) 0 hag t _).symm
    _ = chainL Dc (chainCode X) 0 t (fun u => if s < u then 1 else 0) := by
      apply chainL_congr (chainCode X) 0 _ (fun _ _ => rfl) t ⟨hs.trans hst.le,ht⟩
      intro j _ _ u hu
      dsimp only [Dc]
      rw [clamp01_eq hu]
    _ = chainL (fun j u => Dc j (u+s)) (chainCode X) 0 (t-s)
        (fun u => if s < u+s then 1 else 0) :=
      tree_chainL_rebase Dc (chainCode X) 0 hs (fun u hu => by simp [not_lt.mpr hu]) hst.le
    _ = _ := tree_chainL_congr_pos _ (chainCode X) 0
      (fun u hu => by simp [hu]) (by linarith : 0 < t-s)

end WaveTurbulence.RegAsymp
