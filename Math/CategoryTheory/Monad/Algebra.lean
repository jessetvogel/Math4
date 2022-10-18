import Math.CategoryTheory.Monad.Basic
import Math.CategoryTheory.Adjunction.Basic

namespace CategoryTheory.Monad

open Category

variable [Category α]

structure Algebra (M : Monad α) where
  A : α
  eval : hom (M.T.obj A) A
  unit : eval ∘ M.η.app A = 𝟙 A := by simp
  assoc : eval ∘ M.T.map eval = eval ∘ M.μ.app A := by simp

attribute [simp] Algebra.unit Algebra.assoc

@[simp]
theorem Algebra.ev_T_η (M : Monad α) (alg : Algebra M) (f : hom X alg.A) : alg.eval ∘ M.T.map f ∘ M.η.app X = f :=
  by rw [← M.η.natural, ← comp_assoc]; unfold Functor.id; simp;

structure AlgebraHom {M : Monad α} (alg₁ alg₂ : Algebra M) where
  map : hom alg₁.A alg₂.A
  comm : map ∘ alg₁.eval = alg₂.eval ∘ M.T.map map := by simp

attribute [simp] AlgebraHom.comm

instance CatAlgebra (M : Monad α) : Category M.Algebra where
  hom := AlgebraHom
  id _ := { map := 𝟙 _ }
  comp g f := {
    map := g.map ∘ f.map,
    comm := by simp; rw [← comp_assoc, g.comm]; simp
  }
  comp_id _ := by simp
  id_comp _ := by simp
  comp_assoc _ _ _:= by simp

def free (M : Monad α) : Functor α M.Algebra where
  obj X := { A := M.T.obj X, eval := M.μ.app X }
  map f := { map := M.T.map f }
  map_id f := by simp; rfl
  map_comp g f := by simp; rfl

def forget (M : Monad α) : Functor M.Algebra α where
  obj alg := alg.A
  map f := f.map
  map_id f := by rfl
  map_comp g f := by rfl

def adjunction (M : Monad α) : M.free ⊣ M.forget where
  equiv X Y := {
    map := λ f => f.map ∘ M.η.app X,
    inv := λ g => {
      map := Y.eval ∘ M.T.map g,
      comm := by {
        unfold free;
        simp;
        congr;
        rw [← M.μ.natural];
        -- rw [← M.T.map_comp];
        unfold Functor.comp;
        dsimp;
        congr; -- probably not the way to go ..
        simp;
        sorry;
      },
    },
    map_inv := λ _ => by simp
    inv_map := λ f => by sorry
  }
  natural f g h := by {
    simp [forget, free];
    sorry;
  }

end CategoryTheory.Monad
