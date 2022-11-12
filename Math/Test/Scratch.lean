namespace Test

structure Monoid where
  type : Type u
  mul : type → type → type
  one : type
  mul_one : ∀ x, mul x one = one
  one_mul : ∀ x, mul one x = one

infixl:60 " * " => Monoid.mul _

@[appUnexpander Monoid.mul]
def unexpandMonoidMul : Lean.PrettyPrinter.Unexpander
| `($_ $_ $x $y) => `($x * $y)
| _ => throw ()

structure Group extends Monoid where
  inv : type → type
  mul_inv : ∀ x, mul x (inv x) = one
  inv_mul : ∀ x, mul (inv x) x = one

postfix:max " ⁻¹ " => Group.inv _

@[appUnexpander Group.inv]
def unexpandGroupInv : Lean.PrettyPrinter.Unexpander
| `($_ $_ $x) => `($x⁻¹)
| _ => throw ()

@[appUnexpander Group.toMonoid]
def unexpandGroupToMonoid : Lean.PrettyPrinter.Unexpander
| `($_) => `(TEST)
-- | _ => throw ()

example {G : Group} (x y : G.type) : x * y = y * x := by {
  
}

end Test
