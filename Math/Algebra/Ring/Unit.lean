import Math.Algebra.Ring.Basic
import Math.Algebra.Monoid.Unit

namespace Algebra
namespace Ring

instance [Ring α] : Group (Unit α) where
  mul_inv u := by {
    unfold HMul.hMul, instHMul, Mul.mul, Monoid.toMul, instMonoidUnit;
    simp;
    unfold instMulUnit;
    simp;
    congr;
    exact u.val_inv;
    exact u.val_inv;
  }

end Ring
end Algebra
