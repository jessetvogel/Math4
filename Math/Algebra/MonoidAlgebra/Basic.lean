import Math.Algebra.Group.Basic
import Math.Algebra.Ring.Basic

namespace Algebra

def MonoidAlgebra (k : Type _) [Ring k] (G : Type _) [Group G] : Type := sorry

instance [Ring k] [Group G] : Ring (MonoidAlgebra k G) := by sorry

namespace MonoidAlgebra

-- TODO: universal property
-- `lift` and `lift_unique`

end MonoidAlgebra

end Algebra
