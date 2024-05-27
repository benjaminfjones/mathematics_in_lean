import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S05

section

variable {x y : ℝ}

example (h : y > x ^ 2) : y > 0 ∨ y < -1 := by
  left
  linarith [pow_two_nonneg x]

example (h : -y > x ^ 2 + 1) : y > 0 ∨ y < -1 := by
  right
  linarith [pow_two_nonneg x]

example (h : y > 0) : y > 0 ∨ y < -1 :=
  Or.inl h

example (h : y < -1) : y > 0 ∨ y < -1 :=
  Or.inr h

example : x < |y| → x < y ∨ x < -y := by
  rcases le_or_gt 0 y with h | h
  · rw [abs_of_nonneg h]
    intro h; left; exact h
  . rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  case inl h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  case inr h =>
    rw [abs_of_neg h]
    intro h; right; exact h

example : x < |y| → x < y ∨ x < -y := by
  cases le_or_gt 0 y
  next h =>
    rw [abs_of_nonneg h]
    intro h; left; exact h
  next h =>
    rw [abs_of_neg h]
    intro h; right; exact h


example : x < |y| → x < y ∨ x < -y := by
  match le_or_gt 0 y with
    | Or.inl h =>
      rw [abs_of_nonneg h]
      intro h; left; exact h
    | Or.inr h =>
      rw [abs_of_neg h]
      intro h; right; exact h

namespace MyAbs

theorem le_abs_self (x : ℝ) : x ≤ |x| := by
  unfold abs
  rw [le_sup_iff]
  left
  apply le_refl

theorem neg_le_abs_self (x : ℝ) : -x ≤ |x| := by
  unfold abs
  rw [le_sup_iff]
  right
  apply le_refl

theorem abs_add (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  by_contra h
  have h0 : abs x + abs y < abs (x + y) := lt_of_not_le h

  -- In `h1` and `h2`, it's not clear if using `linarith` is circular
  have h1 : x + y < abs (x + y) := by  -- linarith [le_abs_self x, le_abs_self y]
    calc abs (x + y) > abs x + abs y := h0
         _           ≥ x + abs y := by apply add_le_add_right; exact le_abs_self x
         _           ≥ x + y := by apply add_le_add_left; exact le_abs_self y

  have h2 : -(x + y) < abs (x + y) := by  -- linarith [neg_le_abs_self x, neg_le_abs_self y]
    calc abs (x + y) > abs x + abs y := h0
         _           ≥ -x + abs y := by apply add_le_add_right; exact neg_le_abs_self x
         _           ≥ -x + -y := by apply add_le_add_left; exact neg_le_abs_self y
         _           ≥ -(x + y) := by rw [neg_add]

  rcases le_or_gt 0 (x+y) with h | h
  . rw [abs_of_nonneg h] at h1
    linarith
  . rw [abs_of_neg h] at h2
    linarith
  -- Alternate route:
  --
  -- suffices abs (x+y) - abs y ≤ abs x by linarith
  -- suffices abs (x+y) - abs y ≤ x ∨ abs (x+y) - abs y ≤ -x by {
  --   rcases this with h | h
  --   . exact le_trans h (le_abs_self _)
  --   . exact le_trans h (neg_le_abs_self _)
  -- }
  -- rcases le_or_gt 0 x with hx | hx
  -- . sorry
  -- . sorry


theorem lt_abs : x < |y| ↔ x < y ∨ x < -y := by
  constructor
  . intro h
    rcases le_or_gt 0 y with i | i
    . left; rw [abs_of_nonneg i] at h; assumption
    . right; rw [abs_of_neg i] at h; assumption
  . intro hxy
    rcases hxy with h | h
    . exact lt_of_lt_of_le h (le_abs_self y)
    . exact lt_of_lt_of_le h (neg_le_abs_self y)

theorem abs_lt : |x| < y ↔ -y < x ∧ x < y := by
  constructor
  . intro h
    rcases le_or_gt 0 x with i | i
    . rw [abs_of_nonneg i] at h
      have h0 : -x ≤ x := by exact neg_le_self i
      have h1 : -y < x := by
        calc -y < -x := by exact neg_lt_neg h
             _  ≤ x := h0
      exact ⟨ h1, h ⟩
    . rw [abs_of_neg i] at h
      have h0 : -y < x := by rw [← neg_neg y] at h; exact lt_of_neg_lt_neg h
      have hnxp : 0 ≤ -x := by apply le_of_neg_le_neg; simp only [neg_neg, neg_zero]; exact le_of_lt i
      have h1 : x < y := by
        -- some contortion here in the name of using only short theorems
        calc y > -x := h
             _ ≥ x := by
               show x ≤ -x
               nth_rw 1 [← neg_neg x]
               apply neg_le_self hnxp
      exact ⟨ h0, h1 ⟩
  . rintro ⟨ h0, h1 ⟩
    rcases le_or_gt 0 x with h | h
    . rw [abs_of_nonneg h]; assumption
    . rw [abs_of_neg h]; apply lt_of_neg_lt_neg; rw [neg_neg]; assumption

end MyAbs

end

example {x : ℝ} (h : x ≠ 0) : x < 0 ∨ x > 0 := by
  rcases lt_trichotomy x 0 with xlt | xeq | xgt
  · left
    exact xlt
  · contradiction
  . right; exact xgt

example {m n k : ℕ} (h : m ∣ n ∨ m ∣ k) : m ∣ n * k := by
  rcases h with ⟨a, rfl⟩ | ⟨b, rfl⟩
  · rw [mul_assoc]
    apply dvd_mul_right
  . rw [mul_comm, mul_assoc]
    apply dvd_mul_right

example {z : ℝ} (h : ∃ x y, z = x ^ 2 + y ^ 2 ∨ z = x ^ 2 + y ^ 2 + 1) : z ≥ 0 := by
  sorry

example {x : ℝ} (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  sorry

example {x y : ℝ} (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  sorry

section
variable {R : Type*} [CommRing R] [IsDomain R]
variable (x y : R)

example (h : x ^ 2 = 1) : x = 1 ∨ x = -1 := by
  sorry

example (h : x ^ 2 = y ^ 2) : x = y ∨ x = -y := by
  sorry

end

example (P : Prop) : ¬¬P → P := by
  intro h
  cases em P
  · assumption
  . contradiction

example (P : Prop) : ¬¬P → P := by
  intro h
  by_cases h' : P
  · assumption
  contradiction

example (P Q : Prop) : P → Q ↔ ¬P ∨ Q := by
  sorry
