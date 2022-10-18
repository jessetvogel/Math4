import Math.CategoryTheory.Basic

namespace CategoryTheory
namespace Category

variable (α : Sort u) [C : Category α]

def op := α

postfix:max " ᵒᵖ " => op

instance : Category (op α) where
  hom X Y := C.hom Y X
  id X := C.id X
  comp g f := C.comp f g
  comp_id := C.id_comp
  id_comp := C.comp_id
  comp_assoc h g f := Eq.symm (C.comp_assoc f g h)

end Category
end CategoryTheory
