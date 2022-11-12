import Math.Algebra.Ring.Basic
import Math.CategoryTheory.Bundled.Basic

open CategoryTheory

namespace Algebra

instance : BundledHom RingHom where
  id _ := inferInstance
  comp {_ _ _ _ _ _ _ _} _ _ := inferInstance

def CatGroup := CatBundled Ring RingHom

end Algebra
