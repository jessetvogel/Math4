import Math.Algebra.Field.Basic
import Math.CategoryTheory.Bundled.Basic
import Math.Algebra.Ring.Category

open CategoryTheory

namespace Algebra

class abbrev FieldHom (f : α → β) [Field α] [Field β] : Prop := RingHom f

instance : BundledHom FieldHom where
  id _ := inferInstance
  comp {_ _ _ _ _ _ _ _} _ _ := inferInstance

def CatField := CatBundled Field FieldHom

end Algebra
