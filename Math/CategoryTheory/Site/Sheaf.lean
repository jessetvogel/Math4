import Math.CategoryTheory.Presheaf
import Math.CategoryTheory.Site.Basic

namespace CategoryTheory

structure Sheaf {C : Category} (J : GrothendieckTopology C) (A : Category) where
  F : Presheaf C A
  sheaf : True -- TODO

end CategoryTheory
