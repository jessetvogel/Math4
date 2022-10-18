import Math.Algebra.CommRing.Basic

open Algebra.CommRing

namespace Algebra

class Field (α : Type u) extends CommRing α, Inv α where
  mul_inv_cancel : ∀ {x : α}, x ≠ 0 → x * x⁻¹ = 1

namespace Field

variable [Field α]

def inv_mul_cancel (x : α) (hx : x ≠ 0) : x⁻¹ * x = 1 := by rw [mul_comm]; exact mul_inv_cancel hx

end Field

end Algebra
