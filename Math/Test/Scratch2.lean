namespace Test

structure Monoid where
  type : Type u
  mul : type → type → type
  one : type
  mul_one : ∀ (x : type), mul x one = x
  one_mul : ∀ (x : type), mul one x = x
  mul_assoc : ∀ (x y z : type), mul (mul x y) z = mul x (mul y z)

structure Group extends Monoid where
  inv : type → type
  mul_inv : ∀ (x : type), mul x (inv x) = one
  inv_mul : ∀ (x : type), mul (inv x) x = one

def toType (M : Monoid) := M.type

variable (G : Group)

instance : Coe Group Monoid where
  coe G := G.toMonoid

#check toType G

end Test

