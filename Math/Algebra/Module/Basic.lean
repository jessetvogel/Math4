import Math.Algebra.Abelian.Basic
import Math.Algebra.Group.Basic
import Math.Algebra.Ring.Basic

namespace Algebra

structure Module (R : Ring) extends Abelian where
  smul : R.set → set → set
  smul_add : ∀ (x : R.set) (m m' : set), smul x (add m m') = add (smul x m) (smul x m')
  add_smul : ∀ (x y : R.set) (m : set), smul (R.add x y) m = add (smul x m) (smul y m)
  mul_smul : ∀ (x y : R.set) (m : set), smul (R.mul x y) m = smul x (smul y m)
  one_smul : ∀ (m : set), smul R.one m = m

-- Every abelian group is an Int-module
-- instance [A : AddGroup α] : Module Int α := {
--   smul := A.zmul,
--   smul_add := sorry,
--   add_smul := sorry,
--   mul_smul := sorry,
--   one_smul := sorry,
-- }

end Algebra
