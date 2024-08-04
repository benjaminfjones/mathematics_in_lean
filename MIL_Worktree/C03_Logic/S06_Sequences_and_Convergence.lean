import MIL.Common
import Mathlib.Data.Real.Basic

namespace C03S06

def ConvergesTo (s : ℕ → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

-- Extensionality
example : (fun x y : ℝ ↦ (x + y) ^ 2) = fun x y : ℝ ↦ x ^ 2 + 2 * x * y + y ^ 2 := by
  ext x y  -- name the function inputs explicitly to make the goal nicer
  ring

-- Congruence
example (a b : ℝ) : |a| = |a - b + b| := by
  congr
  ring

-- `convert` applies a theorem conclusion and congruence to some depth and then produces
-- new goals for the differences
example {a : ℝ} (h : 1 < a) : a < a * a := by
  -- convert: b < c → b * a < c * a
  convert (mul_lt_mul_right _).2 h
  -- goals:
  -- 1. 1 = 1 * a
  -- 2. 0 < a
  · rw [one_mul]
  exact lt_trans zero_lt_one h

theorem convergesTo_const (a : ℝ) : ConvergesTo (fun _ : ℕ ↦ a) a := by
  intro ε εpos
  use 0
  intro n _nge
  dsimp  -- unfold the fun so we have: ⊢ |a - a| < ε
  rw [sub_self, abs_zero]
  apply εpos

theorem convergesTo_add {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n + t n) (a + b) := by
  intro ε εpos
  dsimp  -- this line is not needed but cleans up the goal a bit.
  have ε2pos : 0 < ε / 2 := by linarith
  -- apply main hypotheses to our chosen neighborhood
  rcases cs (ε / 2) ε2pos with ⟨Ns, hs⟩
  rcases ct (ε / 2) ε2pos with ⟨Nt, ht⟩
  use max Ns Nt
  intro n hn
  have hs' : abs (s n - a) < ε / 2 := hs n (le_trans (le_max_left _ _) hn)
  have ht' : abs (t n - b) < ε / 2 := ht n (le_trans (le_max_right _ _) hn)
  calc
    abs (s n + t n - (a + b)) = abs ((s n - a) + (t n - b)) := by congr; ring
    _                         ≤ abs (s n - a) + abs (t n - b) := by apply abs_add
    _                         < ε / 2 + abs (t n - b) := by apply add_lt_add_right hs'
    _                         < ε / 2 + ε / 2 := by apply add_lt_add_left ht'
    _                         ≤ ε := by norm_num

-- ∀ ε > 0, ∃ N, ∀ n ≥ N, |c*s n - c*s| < ε
theorem convergesTo_mul_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (cs : ConvergesTo s a) :
    ConvergesTo (fun n ↦ c * s n) (c * a) := by
  by_cases h : c = 0
  . convert convergesTo_const 0
    <;> (rw [h]; ring)
  . intro ε εpos
    let εc := ε / abs c  -- convergence neighborhood, scaled by (abs c)
    have acpos : 0 < |c| := abs_pos.mpr h
    have εcpos : 0 < εc := div_pos εpos acpos

    rcases cs εc εcpos with ⟨ N, hc ⟩
    use N
    dsimp
    intro n hngtN
    rw [← mul_sub, abs_mul c _, mul_comm]
    apply (lt_div_iff acpos).mp
    exact hc n hngtN

theorem exists_abs_le_of_convergesTo {s : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) :
    ∃ N b, ∀ n, N ≤ n → |s n| < b := by
  rcases cs 1 zero_lt_one with ⟨N, h⟩
  use N, |a| + 1
  intro n hn
  calc
    abs (s n) = abs ((s n - a) + a) := by congr; ring
    _         ≤ abs (s n - a) + abs a:= by apply abs_add
    _         < 1 + abs a := by apply add_lt_add_right (h n hn)
    _         = abs a + 1 := by rw [add_comm]

theorem aux {s t : ℕ → ℝ} {a : ℝ} (cs : ConvergesTo s a) (ct : ConvergesTo t 0) :
    ConvergesTo (fun n ↦ s n * t n) 0 := by
  intro ε εpos
  dsimp
  -- eventual abs upper bound on (s n) implies (s n) * (t n) → 0
  rcases exists_abs_le_of_convergesTo cs with ⟨N₀, B, h₀⟩
  have Bpos : 0 < B := lt_of_le_of_lt (abs_nonneg _) (h₀ N₀ (le_refl _))
  have Bnonzero : B ≠ 0 := by exact Ne.symm (ne_of_lt Bpos)
  have pos₀ : ε / B > 0 := div_pos εpos Bpos
  rcases ct (ε / B) pos₀ with ⟨N₁, h₁⟩
  use max N₀ N₁
  intro n hn
  let h₁' : abs (t n - 0) < ε / B := h₁ n (le_of_max_le_right hn)
  rw [sub_zero] at *
  -- using `mul_lt_mul''` somewhat simplifies the calc below
  calc
    abs (s n * t n) = abs (s n) * abs (t n) := by rw [abs_mul]
    _                   ≤ B * abs (t n)     := by apply mul_le_mul_of_nonneg_right
                                                  . exact le_of_lt (h₀ n (le_of_max_le_left hn))
                                                  . apply abs_nonneg
    _                   < B * (ε / B)       := by apply (mul_lt_mul_left _).mpr h₁'
                                                  exact Bpos
    _                   = ε                 := by rw [mul_div_cancel₀ ε Bnonzero]

theorem convergesTo_mul {s t : ℕ → ℝ} {a b : ℝ}
      (cs : ConvergesTo s a) (ct : ConvergesTo t b) :
    ConvergesTo (fun n ↦ s n * t n) (a * b) := by
  have h₁ : ConvergesTo (fun n ↦ s n * (t n + -b)) 0 := by
    apply aux cs
    convert convergesTo_add ct (convergesTo_const (-b))
    ring
  have := convergesTo_add h₁ (convergesTo_mul_const b cs)
  convert convergesTo_add h₁ (convergesTo_mul_const b cs) using 1
  · ext; ring
  ring

theorem convergesTo_unique {s : ℕ → ℝ} {a b : ℝ}
      (sa : ConvergesTo s a) (sb : ConvergesTo s b) :
    a = b := by
  by_contra abne
  have : |a - b| > 0 := by
    apply abs_pos.mpr
    intro amb
    have : a = b := by apply eq_of_sub_eq_zero amb
    exact abne this
  let ε := |a - b| / 2
  have εpos : ε > 0 := by
    change |a - b| / 2 > 0
    linarith
  rcases sa ε εpos with ⟨Na, hNa⟩
  rcases sb ε εpos with ⟨Nb, hNb⟩
  let N := max Na Nb
  have absa : |s N - a| < ε := hNa N (le_max_left Na Nb)
  have absb : |s N - b| < ε := hNb N (le_max_right Na Nb)
  have : |a - b| < |a - b| := by
    calc
      abs (a - b) = abs ((s N - b) + (-(s N - a))) := by congr 1; ring
      _           ≤ abs (s N - b) + abs (-(s N - a)) := by apply abs_add
      _           = abs (s N - b) + abs (s N - a) := by rw [abs_neg]
      _           < ε + abs (s N - a) := by apply add_lt_add_right absb  -- add_lt_add
      _           < ε + ε := by apply add_lt_add_left absa
      _           = abs (a - b) := by exact add_halves |a - b|  -- `norm_num [ε]` also works
  exact lt_irrefl _ this

section
variable {α : Type*} [LinearOrder α]

def ConvergesTo' (s : α → ℝ) (a : ℝ) :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |s n - a| < ε

end
