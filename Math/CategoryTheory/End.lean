import Math.CategoryTheory.Basic
import Math.Algebra.Monoid.Basic

open Algebra

namespace CategoryTheory

variable [C : Category α]

/-- An endomorphism of `X`. -/
def End (X : α) := C.hom X X

instance (X : α) : Monoid (End X) where
  mul := C.comp
  one := C.id X
  mul_assoc _ _ _ := Eq.symm (C.comp_assoc _ _ _)
  mul_one := C.comp_id
  one_mul := C.id_comp

end CategoryTheory
