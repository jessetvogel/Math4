import Math.Algebra.Group.Basic
import Math.CategoryTheory.Category

open CategoryTheory

namespace Algebra

def CatGroup : Category := {
  obj := Group,
  hom := GroupHom,
  id := GroupHom.id,
  comp := GroupHom.comp,
  comp_id := λ _ => by rfl,
  id_comp := λ _ => by rfl,
  comp_assoc := λ _ _ _ => by rfl,
}

end Algebra
