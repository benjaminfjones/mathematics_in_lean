import Mathlib.Algebra.Ring.Defs
import Mathlib.Data.Real.Basic
import MIL.Common

section
variable (R : Type*) [Ring R]

#check (add_assoc : ∀ a b c : R, a + b + c = a + (b + c))
#check (add_comm : ∀ a b : R, a + b = b + a)
#check (zero_add : ∀ a : R, 0 + a = a)
#check (add_left_neg : ∀ a : R, -a + a = 0)
#check (mul_assoc : ∀ a b c : R, a * b * c = a * (b * c))
#check (mul_one : ∀ a : R, a * 1 = a)
#check (one_mul : ∀ a : R, 1 * a = a)
#check (mul_add : ∀ a b c : R, a * (b + c) = a * b + a * c)
#check (add_mul : ∀ a b c : R, (a + b) * c = a * c + b * c)

end

section
variable (R : Type*) [CommRing R]
variable (a b c d : R)

example : c * b * a = b * (a * c) := by ring

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by ring

example : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by ring

example (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp, hyp']
  ring

end

namespace MyRing
variable {R : Type*} [Ring R]

theorem add_zero (a : R) : a + 0 = a := by rw [add_comm, zero_add]

theorem add_right_neg (a : R) : a + -a = 0 := by rw [add_comm, add_left_neg]

#check MyRing.add_zero
#check add_zero

end MyRing

namespace MyRing
variable {R : Type*} [Ring R]

theorem neg_add_cancel_left (a b : R) : -a + (a + b) = b := by
  rw [← add_assoc, add_left_neg, zero_add]

-- Prove these:
theorem add_neg_cancel_right (a b : R) : a + b + -b = a := by
  rw [add_assoc, add_comm b _, add_left_neg, add_zero]

theorem add_left_cancel {a b c : R} (h : a + b = a + c) : b = c := by
  rw [← zero_add b, ← add_left_neg a, add_assoc]
  rw [h]
  rw [neg_add_cancel_left]

theorem add_right_cancel {a b c : R} (h : a + b = c + b) : a = c := by
  rw [← add_zero a, ← add_left_neg b, add_comm (-b) _, ← add_assoc]
  rw [h]
  rw [add_neg_cancel_right]

theorem mul_zero (a : R) : a * 0 = 0 := by
  have h : a * 0 + a * 0 = a * 0 + 0 := by
    rw [← mul_add, add_zero, add_zero]
  rw [add_left_cancel h]

theorem zero_mul (a : R) : 0 * a = 0 := by
  have h : 0 * a + 0 * a = 0 * a + 0 := by
    rw [← add_mul, add_zero, add_zero]
  apply add_left_cancel h

theorem neg_eq_of_add_eq_zero {a b : R} (h : a + b = 0) : -a = b := by
  have ha : -a + a = 0 := add_left_neg a
  rw [← h, add_comm (-a) a] at ha
  exact add_left_cancel ha

theorem eq_neg_of_add_eq_zero {a b : R} (h : a + b = 0) : a = -b := by
  have hb : -b + b = 0 := add_left_neg b
  rw [← hb, ] at h
  exact add_right_cancel h

theorem neg_zero : (-0 : R) = 0 := by
  apply neg_eq_of_add_eq_zero
  rw [add_zero]

theorem neg_neg (a : R) : - -a = a := by
  apply neg_eq_of_add_eq_zero
  exact add_left_neg a

end MyRing

-- Examples.
section
variable {R : Type*} [Ring R]

example (a b : R) : a - b = a + -b :=
  sub_eq_add_neg a b

end

example (a b : ℝ) : a - b = a + -b :=
  rfl

example (a b : ℝ) : a - b = a + -b := by
  rfl

namespace MyRing
variable {R : Type*} [Ring R]

theorem self_sub (a : R) : a - a = 0 := by
  sorry

theorem one_add_one_eq_two : 1 + 1 = (2 : R) := by
  norm_num

theorem two_mul (a : R) : 2 * a = a + a := by
  sorry

end MyRing

section
variable (A : Type*) [AddGroup A]

#check (add_assoc : ∀ a b c : A, a + b + c = a + (b + c))
#check (zero_add : ∀ a : A, 0 + a = a)
#check (add_left_neg : ∀ a : A, -a + a = 0)

end

section
variable {G : Type*} [Group G]

#check (mul_assoc : ∀ a b c : G, a * b * c = a * (b * c))
#check (one_mul : ∀ a : G, 1 * a = a)
#check (mul_left_inv : ∀ a : G, a⁻¹ * a = 1)

namespace MyGroup

-- helper, didn't end up needing this
theorem inv_mul_cancel_left (a b : G) : a⁻¹ * (a * b) = b := by
  rw [← mul_assoc, mul_left_inv, one_mul]

-- helper
theorem mul_left_cancel {a b c : G} (h : a * b = a * c) : b = c := by
  rw [← one_mul b, ← mul_left_inv a, mul_assoc]
  rw [h]
  rw [← mul_assoc, mul_left_inv, one_mul]

-- helper for `mul_one`
theorem eq_of_inv_mul_eq_one (a b : G) (h : a⁻¹ * b = 1) : a = b := by
  have h1 : a⁻¹ * a = 1 := mul_left_inv a
  rw [← h] at h1
  exact mul_left_cancel h1

-- Exercise 2
theorem mul_one (a : G) : a * 1 = a := by
  have h1 : (1 : G) * 1 = 1 := one_mul 1
  nth_rw 1 [← mul_left_inv a] at h1
  rw [mul_assoc] at h1
  have h2 : a = a * 1 := eq_of_inv_mul_eq_one a (a * 1) h1
  rw [← h2]

-- Exercise 1
theorem mul_right_inv (a : G) : a * a⁻¹ = 1 := by
  have h : 1 * a⁻¹ = a⁻¹ := by rw [one_mul]
  rw [← mul_left_inv a, mul_assoc] at h
  nth_rw 3 [← mul_one a⁻¹] at h
  exact mul_left_cancel h

-- helper
theorem eq_inv_of_mul_one (a b : G) (h : a * b = 1) : a = b⁻¹ :=
  calc
    a = a * 1 := Eq.symm (mul_one a)
    _ = a * (b * b⁻¹) := by rw [← mul_right_inv b]
    _ = (a * b) * b⁻¹ := by rw [← mul_assoc]
    _ = 1 * b⁻¹ := by rw [h]
    _ = b⁻¹ := by rw [one_mul]

-- Exercise 3
theorem mul_inv_rev (a b : G) : (a * b)⁻¹ = b⁻¹ * a⁻¹ := by
  -- apply that x * g = 1 => x = g⁻¹
  have h : (b⁻¹ * a⁻¹) * (a * b) = 1 := by
    calc
      (b⁻¹ * a⁻¹) * (a * b) = ((b⁻¹ * a⁻¹) * a) * b := by rw [← mul_assoc]
      _                     = (b⁻¹ * (a⁻¹ * a)) * b := by rw [mul_assoc b⁻¹ _ _]
      _                     = (b⁻¹ * 1) * b         := by rw [mul_left_inv]
      _                     = b⁻¹ * b               := by rw [mul_one]
      _                     = 1                     := by rw [mul_left_inv]
  exact Eq.symm (eq_inv_of_mul_one (b⁻¹ * a⁻¹) (a * b) h)

end MyGroup

end

