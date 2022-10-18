import Math.CategoryTheory.Limits.Basic

namespace CategoryTheory

namespace EqualizerDiagram

inductive obj
| A : obj
| B : obj

inductive hom : obj → obj → Type v
| id : ∀ X, hom X X
| f : hom obj.A obj.B
| g : hom obj.A obj.B

def hom.comp {X Y Z : obj} (g : hom Y Z) (f : hom X Y) : hom X Z :=
  match X, Y, Z, g, f with
  | _, _, _, g, (hom.id _) => g
  | _, _, _, (hom.id _), hom.f => hom.f
  | _, _, _, (hom.id _), hom.g => hom.g
  
end EqualizerDiagram

def EqualizerDiagram : Category := {
  obj := EqualizerDiagram.obj
  hom := EqualizerDiagram.hom,
  id := EqualizerDiagram.hom.id,
  comp := EqualizerDiagram.hom.comp,
  comp_id := λ f => by cases f; repeat { rfl },
  id_comp := λ f => by cases f; repeat { rfl },
  assoc := λ h g f => by cases f; repeat { cases g; repeat { cases h; repeat { rfl } } },
}

def EqualizerFunctor {C : Category} {X Y : C.obj} (f g : C.hom X Y) : Functor EqualizerDiagram C := {
  obj := λ obj => match obj with
    | EqualizerDiagram.obj.A => X
    | EqualizerDiagram.obj.B => Y,
  hom := λ f' => match f' with
    | (EqualizerDiagram.hom.id (EqualizerDiagram.obj.A)) => C.id X
    | (EqualizerDiagram.hom.id (EqualizerDiagram.obj.B)) => C.id Y
    | EqualizerDiagram.hom.f => f
    | EqualizerDiagram.hom.g => g,
  map_id := λ f' => by cases f'; repeat { rfl },
  map_comp := λ {X' Y' Z'} g' f' => by sorry,
    -- cases g';
    -- cases f';
    -- cases X';
    -- {
    --   dsimp;
    --   have comp_id : ∀ X'' Y'' (h : EqualizerDiagram.hom X'' Y''), EqualizerDiagram.comp h (EqualizerDiagram.hom.id X'') = h := λ Z h => by apply EqualizerDiagram.comp_id;
    --   have id_comp : ∀ X'' Y'' (h : EqualizerDiagram.hom X'' Y''), EqualizerDiagram.comp (EqualizerDiagram.hom.id Y'') h = h := λ Z h => by {
    --     intros h;
    --     apply EqualizerDiagram.id_comp;
    --   }; 
      
    --   simp [comp_id, id_comp];
    -- };
  -- },
}

def stupid (C : Category) {X Y : C.obj} (f g : C.hom X Y) : Functor EqualizerDiagram C := sorry

def Equalizer {C : Category} {X Y : C.obj} (f g : C.hom X Y) := (EqualizerFunctor f g)
-- def Equalizer' {C : Category} {X Y : C.obj} (f g : C.hom X Y) := Limit (stupid C f g)






------------- TEST --------------

structure Category' where
  obj     : Sort u
  hom     : obj → obj → Sort v

structure Functor' (C D : Category') where
  x : Nat

structure Limit' {C D : Category'} (F : Functor' C D) where
  x : Nat

def MyCategory' : Category' := {
  obj := EqualizerDiagram.obj,
  hom := λ X Y => EqualizerDiagram.hom X Y, -- EqualizerDiagram.hom,
}

def stupid' (C : Category') {X Y : C.obj} (f g : C.hom X Y) : Functor' MyCategory' C := sorry

def Equalizer' {C : Category'} {X Y : C.obj} (f g : C.hom X Y) := Limit' (stupid' C f g)

end CategoryTheory
