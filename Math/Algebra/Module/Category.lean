import Math.Algebra.Module.Basic
import Math.CategoryTheory.Bundled.Basic

open CategoryTheory

namespace Algebra

variable (α : Type u) [Ring α]

instance : BundledHom (ModuleHom α) where
  id _ := inferInstance
  comp {_ _ _ _ _ _ _ _} _ _ := inferInstance

instance CatModule : Category (Bundled (Module α)) := CatBundled (Module α) (ModuleHom α)

end Algebra
