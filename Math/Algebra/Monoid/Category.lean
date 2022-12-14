import Math.Algebra.Monoid.Basic
import Math.CategoryTheory.Bundled.Basic

open CategoryTheory

namespace Algebra

instance : BundledHom MonoidHom where
  id _ := inferInstance
  comp {_ _ _ _ _ _ _ _} _ _ := inferInstance

def CatMonoid := CatBundled Monoid MonoidHom

end Algebra
