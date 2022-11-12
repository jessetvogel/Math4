import Math.Algebra.AddGroup.Basic
import Math.CategoryTheory.Bundled.Basic

open CategoryTheory

namespace Algebra

instance : BundledHom AddGroupHom where
  id _ := inferInstance
  comp {_ _ _ _ _ _ _ _} _ _ := inferInstance

def CatAddGroup := CatBundled AddGroup AddGroupHom

end Algebra
