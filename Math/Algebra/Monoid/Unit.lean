import Math.Algebra.Monoid.Basic

namespace Algebra
namespace Monoid

structure Unit (α : Type u) [Monoid α] where
  val : α
  inv : α
  val_inv : val * inv = 1
  inv_val : inv * val = 1

variable [Monoid α]

instance : Mul (Unit α) where mul u v := {
  val := u.val * v.val,
  inv := v.inv * u.inv,
  val_inv := by rw [mul_assoc, ← mul_assoc u.val, v.val_inv, mul_one, u.val_inv],
  inv_val := by rw [mul_assoc, ← mul_assoc v.inv, u.inv_val, mul_one, v.inv_val],
}

instance : One (Unit α) where one := {
  val := 1,
  inv := 1,
  val_inv := mul_one 1,
  inv_val := mul_one 1,
}

instance : Inv (Unit α) where inv u := {
  val := u.inv,
  inv := u.val,
  val_inv := u.inv_val,
  inv_val := u.val_inv
}

instance : Monoid (Unit α) where
  mul_assoc u v w := by unfold HMul.hMul, instHMul, Mul.mul, instMulUnit; simp; -- TODO: is it possible to avoid unfolding these ugly things?
  mul_one u := by {
    unfold HMul.hMul, instHMul, Mul.mul, instMulUnit;
    simp;
    congr;
    exact mul_one _;
    exact one_mul _;
  }
  one_mul u := by {
    unfold HMul.hMul, instHMul, Mul.mul, instMulUnit;
    simp;
    congr;
    exact one_mul _;
    exact mul_one _;
  }

end Monoid
end Algebra
