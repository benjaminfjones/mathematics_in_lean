import MIL.Common
import Mathlib.Topology.MetricSpace.Basic

section
variable {α : Type*} [PartialOrder α]
variable (x y z : α)

#check x ≤ y
#check (le_refl x : x ≤ x)
#check (le_trans : x ≤ y → y ≤ z → x ≤ z)
#check (le_antisymm : x ≤ y → y ≤ x → x = y)


#check x < y
#check (lt_irrefl x : ¬x < x)
#check (lt_trans : x < y → y < z → x < z)
#check (lt_of_le_of_lt : x ≤ y → y < z → x < z)
#check (lt_of_lt_of_le : x < y → y ≤ z → x < z)

example : x < y ↔ x ≤ y ∧ x ≠ y :=
  lt_iff_le_and_ne

end

section
variable {α : Type*} [Lattice α]
variable (x y z : α)

#check x ⊓ y
#check (inf_le_left : x ⊓ y ≤ x)
#check (inf_le_right : x ⊓ y ≤ y)
#check (le_inf : z ≤ x → z ≤ y → z ≤ x ⊓ y)
#check x ⊔ y
#check (le_sup_left : x ≤ x ⊔ y)
#check (le_sup_right : y ≤ x ⊔ y)
#check (sup_le : x ≤ z → y ≤ z → x ⊔ y ≤ z)

example : x ⊓ y = y ⊓ x := by
  have h : ∀ a b : α , a ⊓ b ≤ b ⊓ a := by
    intros
    apply le_inf
    apply inf_le_right
    apply inf_le_left
  exact le_antisymm (h x y) (h y x)

example : x ⊓ y ⊓ z = x ⊓ (y ⊓ z) := by
  apply le_antisymm
  . show x ⊓ y ⊓ z ≤ x ⊓ (y ⊓ z)
    have hx  : (x ⊓ y) ⊓ z ≤ x := le_trans (inf_le_left) (inf_le_left)
    have hy  : (x ⊓ y) ⊓ z ≤ y := le_trans (inf_le_left) (inf_le_right)
    have hz  : (x ⊓ y) ⊓ z ≤ z := inf_le_right
    have hyz : (x ⊓ y) ⊓ z ≤ y ⊓ z := le_inf hy hz
    exact le_inf hx hyz

  . show x ⊓ (y ⊓ z) ≤ x ⊓ y ⊓ z
    have hx  : x ⊓ (y ⊓ z) ≤ x := inf_le_left
    have hy  : x ⊓ (y ⊓ z) ≤ y := le_trans (inf_le_right) (inf_le_left)
    have hz  : x ⊓ (y ⊓ z) ≤ z := le_trans (inf_le_right) (inf_le_right)
    have hxy : x ⊓ (y ⊓ z) ≤ x ⊓ y := le_inf hx hy
    exact le_inf hxy hz

example : x ⊔ y = y ⊔ x := by
  have h : ∀ a b : α , a ⊔ b ≤ b ⊔ a := by
    intros
    apply sup_le
    . apply le_sup_right
    . apply le_sup_left
  exact le_antisymm (h x y) (h y x)

-- same proof structure as for infimum, but flipped left/right and le/ge
example : x ⊔ y ⊔ z = x ⊔ (y ⊔ z) := by
  apply le_antisymm
  . show x ⊔ y ⊔ z ≤ x ⊔ (y ⊔ z)
    have hx  :     x ≤ x ⊔ (y ⊔ z) := le_sup_left
    have hy  :     y ≤ x ⊔ (y ⊔ z) := le_trans (le_sup_left) (le_sup_right)
    have hz  :     z ≤ x ⊔ (y ⊔ z) := le_trans (le_sup_right) (le_sup_right)
    have hxy : x ⊔ y ≤ x ⊔ (y ⊔ z) := sup_le hx hy
    exact sup_le hxy hz

  . show x ⊔ (y ⊔ z) ≤ (x ⊔ y) ⊔ z
    have hx  :     x ≤ (x ⊔ y) ⊔ z := le_trans (le_sup_left) (le_sup_left)
    have hy  :     y ≤ (x ⊔ y) ⊔ z := le_trans (le_sup_right) (le_sup_left)
    have hz  :     z ≤ (x ⊔ y) ⊔ z := le_sup_right
    have hyz : y ⊔ z ≤ (x ⊔ y) ⊔ z := sup_le hy hz
    exact sup_le hx hyz

theorem absorb1 : x ⊓ (x ⊔ y) = x := by
  apply le_antisymm
  . show x ⊓ (x ⊔ y) ≤ x
    apply inf_le_left
  . show x ≤ x ⊓ (x ⊔ y)
    apply le_inf
    . apply le_refl
    . apply le_sup_left

theorem absorb2 : x ⊔ x ⊓ y = x := by
  apply le_antisymm
  . show x ⊔ x ⊓ y ≤ x
    apply sup_le
    . apply le_refl
    . apply inf_le_left
  . show x ≤ x ⊔ x ⊓ y
    apply le_sup_left

end

section
variable {α : Type*} [DistribLattice α]
variable (x y z : α)

#check (inf_sup_left x y z : x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z)
#check (inf_sup_right x y z : (x ⊔ y) ⊓ z = x ⊓ z ⊔ y ⊓ z)
#check (sup_inf_left x y z : x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z))
#check (sup_inf_right x y z : x ⊓ y ⊔ z = (x ⊔ z) ⊓ (y ⊔ z))
end

section
variable {α : Type*} [Lattice α]
variable (a b c : α)

example (h : ∀ x y z : α, x ⊓ (y ⊔ z) = x ⊓ y ⊔ x ⊓ z) : a ⊔ b ⊓ c = (a ⊔ b) ⊓ (a ⊔ c) := by
  sorry

example (h : ∀ x y z : α, x ⊔ y ⊓ z = (x ⊔ y) ⊓ (x ⊔ z)) : a ⊓ (b ⊔ c) = a ⊓ b ⊔ a ⊓ c := by
  sorry

end

section
variable {R : Type*} [StrictOrderedRing R]
variable (a b c : R)

#check (add_le_add_left : a ≤ b → ∀ c, c + a ≤ c + b)
#check (mul_pos : 0 < a → 0 < b → 0 < a * b)

#check (mul_nonneg : 0 ≤ a → 0 ≤ b → 0 ≤ a * b)

example (h : a ≤ b) : 0 ≤ b - a := by
  sorry

example (h: 0 ≤ b - a) : a ≤ b := by
  sorry

example (h : a ≤ b) (h' : 0 ≤ c) : a * c ≤ b * c := by
  sorry

end

section
variable {X : Type*} [MetricSpace X]
variable (x y z : X)

#check (dist_self x : dist x x = 0)
#check (dist_comm x y : dist x y = dist y x)
#check (dist_triangle x y z : dist x z ≤ dist x y + dist y z)

example (x y : X) : 0 ≤ dist x y := by
  sorry

end
