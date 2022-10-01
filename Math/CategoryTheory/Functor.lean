import Math.CategoryTheory.Category

namespace CategoryTheory

structure Functor (C D : Category) where
  obj      : C.obj → D.obj
  hom      : ∀ {X Y} (_ : C.hom X Y), D.hom (obj X) (obj Y)
  map_id   : ∀ X, hom (C.id X) = D.id (obj X) := by simp
  map_comp : ∀ {X Y Z} (g : C.hom Y Z) (f : C.hom X Y), hom (g ∘ f) = (hom g) ∘ (hom f) := by simp

attribute [simp] Functor.map_id Functor.map_comp

namespace Functor

variable {C D E : Category}

class full (F : Functor C D) : Prop :=
  intro : ∀ {X Y} (g : D.hom (F.obj X) (F.obj Y)), ∃ (f : C.hom X Y), F.hom f = g

class faithful (F : Functor C D) : Prop :=
  cancel : ∀ {X Y} {f g : C.hom X Y} (_ : F.hom f = F.hom g), f = g

-- The identity functor
def id (C : Category) : Functor C C := {
  obj := λ X => X,
  hom := λ f => f,
}

-- Composition of functors
def comp (G : Functor D E) (F : Functor C D) : Functor C E := {
  obj := λ X => G.obj (F.obj X),
  hom := λ f => G.hom (F.hom f),
}

-- infixr:80 " ∘ " => Functor.comp

-- Constant functor
def const (C : Category) (Y : D.obj) : Functor C D := {
  obj := λ _ => Y,
  hom := λ _ => D.id Y,
}

end Functor

-- TODO: move elsewhere ?
def CatCategory : Category := {
  obj := Category,
  hom := Functor,
  id := Functor.id,
  comp := Functor.comp,
  comp_id := λ F => by trivial,
  id_comp := λ F => by trivial,
  assoc := λ H G F => by trivial,
}

end CategoryTheory
