import Math.Algebra.Monoid.Basic

open Algebra.Monoid

namespace Algebra
 
class Group (α : Type u) extends Monoid α, Inv α where
  mul_inv : ∀ (x : α), x * x⁻¹ = 1

attribute [simp] Group.mul_inv

@[simp]
def Group.inv_mul (α : Type u) [Group α] : ∀ (x : α), x⁻¹ * x = 1 :=
  λ x => by rw [← mul_inv x⁻¹, ← Monoid.left_inv_eq_right_inv (mul_inv x) (mul_inv x⁻¹)]

namespace Group

variable [Group α]

def eq_of_mul_left (x : α) {y z : α} (h : y = z) : x * y = x * z := by rw [h];
def eq_of_mul_right (x : α) {y z : α} (h : y = z) : y * x = z * x := by rw [h];
def cancel_left (x : α) {y z : α} (h : x * y = x * z) : y = z := by {
  have q := eq_of_mul_left (x⁻¹) h;
  simp at q;
  exact q;
}

def cancel_right (x : α) {y z : α} (h : y * x = z * x) : y = z := by {
  have q := eq_of_mul_right (x⁻¹) h;
  rw [← mul_assoc, mul_inv, mul_one, ← mul_assoc, mul_inv, mul_one] at q;
  exact q;
}

@[simp] def inv_inv (x : α) : x⁻¹⁻¹ = x := by apply cancel_left x⁻¹; simp;
@[simp] def mul_mul_inv (x y : α) : x * y * y⁻¹ = x := by simp [← mul_assoc];
@[simp] def mul_inv_mul (x y : α) : x * y⁻¹ * y = x := by simp [← mul_assoc];
@[simp] def inv_of_mul (x y : α) : (x * y)⁻¹ = y⁻¹ * x⁻¹ := by {
  apply cancel_left (x * y);
  simp;
}

def zpow (x : α) : Int → α
| Int.ofNat n => x ^ n
| Int.negSucc n => (x ^ n.succ)⁻¹

instance : Pow α Int where pow := zpow

@[simp]
def zpow_add (x : α) (m n : Int) : x ^ (n + m) = (x ^ n) * (x ^ m) := by {
  sorry;
}

def zpow_neg (x : α) (n : Int) : x ^ (-n) = (x⁻¹) ^ n := by {
  sorry;
}

def zpow_sub (x : α) (m n : Int) : x ^ (m - n) = (x ^ m) * (x⁻¹) ^ n := by {
  sorry;
}

@[simp]
def inv_zpow (x : α) (n : Int) : (x ^ n)⁻¹ = x ^ (-n) := by {
  sorry;
}

@[simp]
def zpow_inv (x : α) (n : Int) : (x⁻¹) ^ n = x ^ (-n) := by {
  sorry;
}

end Group

class GroupHom (f : α → β) [Group α] [Group β] extends MulHom f

/-- Every group morphism sends 1 to 1. -/
instance (f : α → β) [Group α] [Group β] [hf : GroupHom f] : OneHom f := {
  map_one := by {
    apply Group.cancel_right (f 1);
    rw [← hf.map_mul, one_mul, one_mul];
  }
}

end Algebra
