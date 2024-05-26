import Mathlib.Data.Finset.Basic

namespace Mark
open Finset
def Address := Finset.range 1024

example : 0 ∈ Address := by
  unfold Address
  rw [mem_range]
  norm_num

end Mark

namespace Sean

#check beq_iff_eq

variable (α : Type)
example (e f: α) [BEq α] [LawfulBEq α]: (e == f) = true ↔ e = f := by
  exact beq_iff_eq e f

end Sean

