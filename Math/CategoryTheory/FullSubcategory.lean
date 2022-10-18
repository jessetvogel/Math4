import Math.CategoryTheory.Basic

namespace CategoryTheory

def Category.FullSubcategory (C : Category) (P : C.obj → Prop) : Category := {
  obj := Σ' (X : C.obj), P X
  hom := λ X Y => C.hom X.fst Y.fst
  id := λ X => C.id X.fst,
  comp := C.comp,
  comp_id := λ f => by simp,
  id_comp := λ f => by simp,
  assoc := λ h g f => by simp,
}

end CategoryTheory
