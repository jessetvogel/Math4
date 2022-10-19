import Math.Algebra.Abelian.Basic
import Math.Algebra.Group.Basic
import Math.Algebra.Ring.Basic

namespace Algebra

class Module (α : Type u) [Ring α] (β : Type v) extends Abelian β, SMul α β where
  smul_add : ∀ (x : α) (m m' : β), x • (m + m') = x • m + x • m'
  add_smul : ∀ (x y : α) (m : β), (x + y) • m = x • m + y • m
  mul_smul : ∀ (x y : α) (m : β), (x * y) • m = x • (y • m)
  one_smul : ∀ (m : β), (1 : α) • m = m

-- Every abelian group is an Int-module
-- instance [A : AddGroup α] : Module Int α := {
--   smul := A.zmul,
--   smul_add := sorry,
--   add_smul := sorry,
--   mul_smul := sorry,
--   one_smul := sorry,
-- }

end Algebra
