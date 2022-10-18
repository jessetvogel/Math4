import Math.Algebra.Ring.Basic

namespace Algebra

class CommRing (α : Type u) extends Ring α where
  mul_comm : ∀ (x y : α), x * y = y * x

end Algebra
