import Math.Algebra.Abelian.Basic
import Math.Algebra.Group.Category
import Math.CategoryTheory.Category

open CategoryTheory

namespace Algebra

def CatAbelian : Category := {
  obj := Abelian,
  hom := λ A B => GroupHom A.toGroup B.toGroup,
  id := λ A => GroupHom.id A.toGroup,
  comp := GroupHom.comp,
  comp_id := CatGroup.comp_id,
  id_comp := CatGroup.id_comp,
  comp_assoc := CatGroup.comp_assoc,
}

end Algebra
