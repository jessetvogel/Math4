import Math.Algebra.Monoid.Basic
import Math.Algebra.Abelian.Basic
import Math.Algebra.Group.Basic

open Algebra.Monoid

namespace Algebra

class Ring (α : Type u) extends Abelian α, Monoid α where
  distrib_left : ∀ (x y z : α), x * (y + z) = x * y + x * z
  distrib_right : ∀ (x y z : α), (x + y) * z = x * z + y * z

attribute [simp] Ring.distrib_left Ring.distrib_right

end Algebra
