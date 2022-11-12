import Math.Algebra.AddMonoid.Basic
import Math.CategoryTheory.Bundled.Basic

open CategoryTheory

namespace Algebra

instance : BundledHom AddMonoidHom where
  id _ := inferInstance
  comp {_ _ _ _ _ _ _ _} _ _ := inferInstance

def CatAddMonoid := CatBundled AddMonoid AddMonoidHom

end Algebra
