/- Copyright (c) 2026 Scott Armstrong. All rights reserved. -/
module

public import WaveTurbulence.Foundations.ApproxNT.AppRep
public import Mathlib.Data.Fin.Tuple.Basic

/-! # Exact root recursion of the original backwards singular integration -/

public section
noncomputable section
namespace WaveTurbulence.RegAsymp
open ApproxNT Function

variable {d n : ℕ}

/-- Fixing the root leaves precisely the original backwards integration
on the tail coordinates, at every intermediate stage. -/
theorem appIter_cons_root (J : Finset (Fin (n+1)))
    (W : (Fin (n+1) → Mom d) → (Fin (n+1) → Mom d) → ℂ)
    (k : ℕ) (hk : k ≤ n) (a b : Mom d) (x y : Fin n → Mom d) :
    appIter J W k (Fin.cons a x) (Fin.cons b y) =
      appIter (J.preimage Fin.succ (Fin.succ_injective n).injOn)
        (fun x y => W (Fin.cons a x) (Fin.cons b y)) k x y := by
  induction k generalizing x y with
  | zero => rfl
  | succ k ih =>
    have hkn : k < n := by omega
    have hkn' : k < n+1 := by omega
    have he : (⟨n+1-1-k,by omega⟩ : Fin (n+1)) = (⟨n-1-k,by omega⟩ : Fin n).succ := by
      apply Fin.ext
      dsimp only [Fin.val_mk,Fin.val_succ]
      omega
    simp only [appIter,hkn,hkn',dite_true,he,appStep,Finset.mem_preimage]
    have hfun : (fun a' b' => appIter J W k
        (update (Fin.cons a x) (⟨n-1-k,by omega⟩ : Fin n).succ a')
        (update (Fin.cons b y) (⟨n-1-k,by omega⟩ : Fin n).succ b')) =
        (fun a' b' => appIter (J.preimage Fin.succ (Fin.succ_injective n).injOn)
          (fun x y => W (Fin.cons a x) (Fin.cons b y)) k
          (update x ⟨n-1-k,by omega⟩ a') (update y ⟨n-1-k,by omega⟩ b')) := by
      funext a' b'
      rw [← Fin.cons_update,← Fin.cons_update]
      exact ih (by omega) _ _
    rw [hfun]

/-- The singular integral follows its literal root-first recursion;
all child pairs are integrated first, as in DH21's backwards convention. -/
theorem singInt_root_recursion (J : Finset (Fin (n+1)))
    (W : (Fin (n+1) → Mom d) → (Fin (n+1) → Mom d) → ℂ) :
    singInt J W =
      if (0:Fin (n+1)) ∈ J then
        pvOp (fun a b => singInt (J.preimage Fin.succ (Fin.succ_injective n).injOn)
          (fun x y => W (Fin.cons a x) (Fin.cons b y)))
      else NTSP.deltaInner (fun a b => singInt (J.preimage Fin.succ (Fin.succ_injective n).injOn)
          (fun x y => W (Fin.cons a x) (Fin.cons b y))) := by
  have he : (⟨n+1-1-n,by omega⟩ : Fin (n+1)) = 0 := by apply Fin.ext; dsimp; omega
  rw [singInt,appIter]
  simp only [show n < n+1 by omega,dite_true,he,appStep]
  have hfun : (fun a b => appIter J W n (update 0 0 a) (update 0 0 b)) =
      (fun a b => singInt (J.preimage Fin.succ (Fin.succ_injective n).injOn)
        (fun x y => W (Fin.cons a x) (Fin.cons b y))) := by
    funext a b
    have hu (a : Mom d) : update (0:Fin (n+1) → Mom d) 0 a = Fin.cons a 0 := by
      funext j
      cases j using Fin.cases <;> simp
    rw [hu,hu,appIter_cons_root J W n le_rfl]
    rfl
  rw [hfun]

/-- With one pair the defined singular integral is exactly its original
local delta/PV operator, without a hidden change of variables. -/
theorem singInt_one_pair (J : Finset (Fin 1)) (F : Mom d → Mom d → ℂ) :
    singInt J (fun x y => F (x 0) (y 0)) =
      if (0:Fin 1) ∈ J then pvOp F else NTSP.deltaInner F := by
  rw [singInt_root_recursion]
  have he (a b : Mom d) :
      singInt (J.preimage Fin.succ (Fin.succ_injective 0).injOn)
        (fun (x y : Fin 0 → Mom d) => F (Fin.cons (α := fun _ : Fin 1 => Mom d) a x 0)
          (Fin.cons (α := fun _ : Fin 1 => Mom d) b y 0)) = F a b := by
    simp only [singInt,appIter,Fin.cons_zero]
  simp_rw [he]

end WaveTurbulence.RegAsymp
