import Math.CategoryTheory.Basic

open CategoryTheory.Category

namespace CategoryTheory

structure Functor (α : Sort u) (β : Sort v) [Category α] [Category β] where
  obj : α → β
  map : ∀ {X Y : α}, hom X Y → hom (obj X) (obj Y)
  map_id : ∀ (X : α), map (𝟙 X) = 𝟙 (obj X) := by simp
  map_comp : ∀ {X Y Z : α} (g : hom Y Z) (f : hom X Y), map (g ∘ f) = map g ∘ map f := by simp

attribute [simp] Functor.map_id Functor.map_comp

namespace Functor

variable [Category α] [Category β] [Category γ]

class full (F : Functor α β) : Prop :=
  intro : ∀ {X Y : α} (g : hom (F.obj X) (F.obj Y)), ∃ (f : hom X Y), F.map f = g

class faithful (F : Functor α β) : Prop :=
  cancel : ∀ {X Y} {f g : hom X Y} (_ : F.map f = F.map g), f = g

/-- The identity functor. -/
def id (α : Sort u) [Category α] : Functor α α := {
  obj := λ X => X,
  map := λ f => f,
}

/-- Composition of functors. -/
def comp (G : Functor β γ) (F : Functor α β) : Functor α γ := {
  obj := G.obj ∘ F.obj,
  map := G.map ∘ F.map,
}

/-- Constant functor `Δ_X : α → β` . -/
def const (α : Sort u) [Category α] (X : β) : Functor α β where
  obj _ := X
  map _ := 𝟙 X

end Functor

-- TODO: move elsewhere ? (NEED BUNDLED FOR THIS)
-- def CatCategory : Category := {
--   obj := Category,
--   hom := Functor,
--   id := Functor.id,
--   comp := Functor.comp,
--   comp_id := λ F => by trivial,
--   id_comp := λ F => by trivial,
--   assoc := λ H G F => by trivial,
-- }

end CategoryTheory
