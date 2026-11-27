module

public import Mathlib

public section

#click_suggestions

-- structure Tiesze1 where
--   X : Type
--   Y : Type
--   R : Set (FreeGroup X)
--   S : Set (FreeGroup Y)
--   X_eq_Y : X = Y
--   s : FreeGroup Y
--   s_in_Y : s ∈ S
--   R_eq_S_insert_s : R = S ∪ {s}

structure Tiesze1 where
  X : Type
  R : Set (FreeGroup X)
  S : Set (FreeGroup X)
  s : FreeGroup X
  s_in_NR : s ∈ Subgroup.normalClosure R
  S_eq_Rus : S = R ∪ {s}

#check PresentedGroup

def Tiesze1' {α : Type*} {X: Set α} (R S : Set (FreeGroup X)) (s : FreeGroup X) {t : Set (FreeGroup X)} (s_in_NR : s ∈ Subgroup.normalClosure R) (S_eq_Rus : S = R ∪ {s}):=
  have hst : S.MapsTo (MonoidHom.id (FreeGroup X)) (Subgroup.normalClosure R) := by
    unfold Set.MapsTo
    intro x hx
    simp
    rw [S_eq_Rus] at hx
    apply Set.mem_or_mem_of_mem_union at hx
    sorry
  PresentedGroup.map (MonoidHom.id (FreeGroup X)) hst


#check Tiesze1'

#check PresentedGroup.map (MonoidHom.id (FreeGroup X))

def Tiesze1'' {α : Type*} {X: Set α} (R : Set (FreeGroup X)) (s : FreeGroup X) (hs : s ∈ Subgroup.normalClosure R) : (PresentedGroup (R ∪ {s})) ≃* (PresentedGroup R) := by
  apply QuotientGroup.quotientMulEquivOfEq
  apply le_antisymm
  · apply Subgroup.normalClosure_le_normal
    rintro x (hx | rfl)
    · exact Subgroup.subset_normalClosure hx
    · exact hs
  · exact Subgroup.normalClosure_mono Set.subset_union_left

def Tiesze2'' {α : Type*} {X: Set α} (R : Set (FreeGroup X)) (y : α) (ξ : FreeGroup X) : (PresentedGroup (R ∪ {y * ξ⁻¹})) ≃* (PresentedGroup R) := by


#check QuotientGroup.coe_mk'


def toyInv (G : Type*) [CommGroup G] : G ≃* G where
  toFun x := x⁻¹
  invFun x := x⁻¹
  left_inv := inv_inv
  right_inv := inv_inv
  map_mul' x y := by simp [mul_comm]
