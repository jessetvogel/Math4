import Math.CategoryTheory.Category
import Math.CategoryTheory.Functor

namespace CategoryTheory

structure Comma (F : Functor C E) (G : Functor D E) :=
  left : C.obj
  right : D.obj
  hom : E.hom (F.obj left) (G.obj right)

structure CommaHom {F : Functor C E} {G : Functor D E} (X Y : Comma F G) :=
  left : C.hom X.left Y.left
  right : D.hom X.right Y.right
  comm : Y.hom ∘ (F.hom left) = (G.hom right) ∘ X.hom

def CommaId {F : Functor C E} {G : Functor D E} (X : Comma F G) : CommaHom X X := {
  left := C.id X.left,
  right := D.id X.right,
  comm := by rw [F.map_id, E.comp_id, G.map_id, E.id_comp];
}

def CommaHom.comp (g : CommaHom Y Z) (f : CommaHom X Y) : CommaHom X Z := {
  left := g.left ∘ f.left,
  right := g.right ∘ f.right,
  comm := by rw [Functor.map_comp, ← Category.assoc, g.comm, Functor.map_comp, Category.assoc, f.comm, Category.assoc],
}

def CatComma (F : Functor C E) (G : Functor D E) : Category := {
  obj := Comma F G,
  hom := CommaHom,
  id := CommaId,
  comp := CommaHom.comp,
  comp_id := λ f => by dsimp; unfold CommaHom.comp, CommaId; congr; dsimp; rw [C.comp_id]; rw [D.comp_id],
  id_comp := λ f => by dsimp; unfold CommaHom.comp, CommaId; congr; dsimp; rw [C.id_comp]; rw [D.id_comp],
  assoc := λ h g f => by dsimp; unfold CommaHom.comp; congr; rw [Category.assoc]; rw [Category.assoc],
}

-- Arrow categories
def Arrow (C : Category) := Comma (Functor.id C) (Functor.id C)
def CatArrow (C : Category) := CatComma (Functor.id C) (Functor.id C)

-- Arrow categories
def Slice (C : Category) (X : C.obj) := Comma (Functor.id C) (Functor.const C X)
def CatSlice (C : Category) (X : C.obj) := CatComma (Functor.id C) (Functor.const C X)

end CategoryTheory
