import Math.Algebra.AddGroup.Basic
import Math.Algebra.Group.Basic
import Math.Algebra.Ring.Basic

namespace Algebra

variable (R : Type _) [Ring R]

class Module (M : Type _) extends AddGroup M, SMul R M where
  smul_add : ∀ (x : R) (m m' : M), x • (m + m') = x • m + x • m'
  add_smul : ∀ (x y : R) (m : M), (x + y) • m = x • m + y • m
  mul_smul : ∀ (x y : R) (m : M), (x * y) • m = x • (y • m)
  one_smul : ∀ (m : M), (1 : R) • m = m

class abbrev ModuleHom (f : M → M') [Module R M] [Module R M'] : Prop := AddGroupHom f, SMulHom R f

end Algebra
