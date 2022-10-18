import Math.CategoryTheory.Basic

namespace CategoryTheory

open Category

class Groupoid (α : Sort u) [Category α] where
  inv : ∀ {X Y : α}, hom X Y → hom Y X
  inv_comp : ∀ {X Y : α} (f : hom X Y), inv f ∘ f = 𝟙 X
  comp_inv : ∀ {X Y : α} (f : hom X Y), f ∘ inv f = 𝟙 Y

end CategoryTheory
