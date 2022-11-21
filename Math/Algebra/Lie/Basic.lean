import Math.Algebra.Field.Basic
import Math.Algebra.Module.Basic
import Math.SetTheory.Basic

open SetTheory

namespace Algebra

variable (k : Type _) [Field k]

class Lie (V : Type _) extends Module k V, Bracket V where
  bilinear : ∀ (a b : k) (x y z : V), ⁅a • x + b • y, z⁆ = a • ⁅x, z⁆ + b • ⁅y, z⁆
  alt : ∀ (x : V), ⁅x, x⁆ = 0
  jacobi : ∀ (x y z : V), ⁅x, ⁅y, z⁆⁆ + ⁅z, ⁅x, y⁆⁆ + ⁅y, ⁅z, x⁆⁆ = 0

structure Lie.Ideal (V : Type _) [Lie k V] where
  set : Set V
  has_lie : ∀ (x y : V), x ∈ set → ⁅x, y⁆ ∈ set
  -- TODO ...

end Algebra
