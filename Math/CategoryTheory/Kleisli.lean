import Math.CategoryTheory.Monad.Basic
import Math.CategoryTheory.Adjunction.Basic

namespace CategoryTheory
namespace Monad

open Category

variable [C : Category α]

def Kleisli (_ : Monad α) := α

instance CatKleisli (M : Monad α) : Category M.Kleisli where
  hom X Y := C.hom X (M.T.obj Y)
  id X := M.η.app X
  comp g f := M.μ.app _ ∘ M.T.map g ∘ f
  comp_id f := by {
    dsimp;
    rw [← M.η.natural f];
    unfold Functor.id;
    simp;
    rw [← comp_assoc, M.mul_one, id_comp];
  }
  id_comp f := by {
    dsimp;
    rw [← comp_assoc, M.one_mul];
    simp;
  }
  comp_assoc {W X Y Z} h g f := by {
    simp;
    rw [← comp_assoc, M.assoc];
    simp;
    congr;
    suffices s : (M.μ.app (M.T.obj Z)) ∘ (M.T.map (M.T.map h)) = (M.T.map h) ∘ (M.μ.app Y) by rw [← comp_assoc, s, comp_assoc];
    exact M.μ.natural h;
  }

def Kleisli.free (M : Monad α) : Functor α M.Kleisli where
  obj X := X
  map f := C.comp (M.η.app _) f
  map_id X := by simp; rfl
  map_comp {X Y Z} g f := by {
    show M.η.app Z ∘ g ∘ f = M.μ.app Z ∘ M.T.map (M.η.app Z ∘ g) ∘ M.η.app Y ∘ f;
    rw [M.T.map_comp, C.comp_assoc, ← C.comp_assoc (M.μ.app Z), M.one_mul];
    have q₁ := M.η.natural f; unfold Functor.id at q₁; dsimp at q₁;
    have q₂ := M.η.natural (g ∘ f); unfold Functor.id at q₂; dsimp at q₂;
    rw [q₁, ← C.comp_assoc (M.T.map g), ← M.T.map_comp];
    rw [← q₂];
    rw [C.id_comp (M.η.app Z ∘  _)];
  }

def Kleisli.forget (M : Monad α) : Functor M.Kleisli α where
  obj X := M.T.obj X
  map f := C.comp (M.μ.app _) (M.T.map f)
  map_id X := by show M.μ.app X ∘ M.T.map (M.η.app X) = 𝟙 (M.T.obj X); simp
  map_comp := λ {X Y Z} g f => by {
    show M.μ.app Z ∘ M.T.map (M.μ.app _ ∘ M.T.map g ∘ f) = (M.μ.app Z ∘ M.T.map g) ∘ M.μ.app Y ∘ M.T.map f;
    sorry;
  }

def Kleisli.adjunction (M : Monad α) : Kleisli.free M ⊣ Kleisli.forget M where
  equiv X Y := {
    map := λ f => f,
    inv := λ f => f,
    map_inv := by simp,
    inv_map := by simp,
  }
  natural {X X' Y Y'} f g h := by {
    unfold Kleisli, Kleisli.free, Kleisli.forget;
    simp;
    congr;
    
    let t := M.η.app X' ∘ f;
    have q : h ∘ t = M.μ.app _ ∘ M.T.map h ∘ (M.η.app X' ∘ f) := by rfl;
    rw [q];

    -- Get rid of f
    rw [← C.comp_assoc, ← C.comp_assoc]; congr;
    simp;
    -- Use Kleisli.comp_id h
    have q := comp_id h;
    unfold Kleisli, Kleisli.free at q;
    simp at q;
    
    sorry;
  }

end Monad
end CategoryTheory
