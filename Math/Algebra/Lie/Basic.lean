import Math.Algebra.Field.Basic
import Math.Algebra.Module.Basic

namespace Algebra

variable (α : Type u) [Field α]

class Lie (β : Type v) extends Module α β, Bracket β where
  bilinear : ∀ (a b : α) (x y z : β), ⁅a • x + b • y, z⁆ = a • ⁅x, z⁆ + b • ⁅y, z⁆
  alt : ∀ (x : β), ⁅x, x⁆ = 0
  jacobi : ∀ (x y z : β), ⁅x, ⁅y, z⁆⁆ + ⁅z, ⁅x, y⁆⁆ + ⁅y, ⁅z, x⁆⁆ = 0

end Algebra
