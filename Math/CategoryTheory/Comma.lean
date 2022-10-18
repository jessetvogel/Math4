import Math.CategoryTheory.Basic
import Math.CategoryTheory.Functor

namespace CategoryTheory

open Category

variable [Category α] [Category β] [Category γ]

structure Comma (F : Functor α γ) (G : Functor β γ) where
  left : α
  right : β
  hom : hom (F.obj left) (G.obj right)

variable {F : Functor α γ} {G : Functor β γ}

structure CommaHom (X Y : Comma F G) where
  left : hom X.left Y.left
  right : hom X.right Y.right
  comm : Y.hom ∘ (F.map left) = (G.map right) ∘ X.hom

def CommaHom.id (X : Comma F G) : CommaHom X X := {
  left := 𝟙 X.left,
  right := 𝟙 X.right,
  comm := by rw [F.map_id, comp_id, G.map_id, id_comp]
}

def CommaHom.comp {X Y Z : Comma F G} (g : CommaHom Y Z) (f : CommaHom X Y) : CommaHom X Z := {
  left := g.left ∘ f.left,
  right := g.right ∘ f.right,
  comm := by rw [Functor.map_comp, ← comp_assoc, g.comm, Functor.map_comp, comp_assoc, f.comm, comp_assoc],
}

instance CatComma (F : Functor α γ) (G : Functor β γ) : Category (Comma F G) where
  hom := CommaHom
  id := CommaHom.id
  comp := CommaHom.comp
  comp_id f := by dsimp; unfold CommaHom.comp, CommaHom.id; congr; rw [comp_id]; rw [comp_id]
  id_comp f := by dsimp; unfold CommaHom.comp, CommaHom.id; congr; rw [id_comp]; rw [id_comp]
  comp_assoc h g f := by dsimp; unfold CommaHom.comp; congr; rw [comp_assoc]; rw [comp_assoc]

variable (α : Sort u) [Category α]

-- Arrow categories
def Arrow := Comma (Functor.id α) (Functor.id α)
def CatArrow := CatComma (Functor.id α) (Functor.id α)

-- Slice categories
def Slice (X : α) := Comma (Functor.id α) (Functor.const α X)
def CatSlice (X : α) := CatComma (Functor.id α) (Functor.const α X)

-- Coslice categories
def Coslice (X : α) := Comma (Functor.const α X) (Functor.id α)
def CatCoslice (X : α) := CatComma (Functor.const α X) (Functor.id α)

end CategoryTheory
