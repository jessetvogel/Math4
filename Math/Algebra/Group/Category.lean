import Math.Algebra.Group.Basic
import Math.CategoryTheory.Bundled.Basic

open CategoryTheory

namespace Algebra

instance : BundledHom Algebra.GroupHom where
  id _ := inferInstance
  comp {_ _ _ _ _ _ _ _} _ _ := inferInstance

def CatGroup := CatBundled Algebra.Group Algebra.GroupHom

end Algebra
