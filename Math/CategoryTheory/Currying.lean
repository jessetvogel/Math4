import Math.CategoryTheory.NaturalTransformation
import Math.CategoryTheory.Equivalence

namespace CategoryTheory

def Functor.uncurry (F : Functor C (CatFunctor D E)) : Functor (C.product D) E := {
  obj := λ X => (F.obj X.1).obj X.2,
  hom := λ {X Y} f => (F.obj Y.1).hom f.2 ∘ (F.hom f.1).map X.2,
  map_id := λ X => by simp [Category.product, CatFunctor, NaturalTransformation.id],
  map_comp := λ g f => by {
    simp[Category.product, CatFunctor, NaturalTransformation.comp];
    congr;
    rw [← Category.assoc, ← Category.assoc, NaturalTransformation.natural];
  }
}

def Functor.curry (F : Functor (C.product D) E) : Functor C (CatFunctor D E) := {
  obj := λ X => {
    obj := λ Y => F.obj ⟨X, Y⟩,
    hom := λ f => F.hom ⟨C.id X, f⟩,
    map_id := λ Y => by {
      let q : ⟨C.id X, D.id Y⟩ = (C.product D).id ⟨X, Y⟩ := by simp[Category.product];
      simp [q];
    },
    map_comp := λ g f => by rw [← F.map_comp]; simp [Category.product],
  },
  hom := λ {X Y} f => {
    map := λ Z => F.hom ⟨f, D.id Z⟩,
    natural := λ {A B} g => by dsimp; rw [← Functor.map_comp, ← Functor.map_comp]; simp [Category.product],
  },
  map_id := λ X => by {
    dsimp;
    congr;
    funext _;
    simp [CatFunctor, NaturalTransformation.id];
    exact F.map_id _;
  },
  map_comp := λ g f => by {
    dsimp [CatFunctor];
    congr;
    funext _;
    simp [NaturalTransformation.comp];
    rw [← F.map_comp];
    simp [Category.product];
  },
}

def currying : Equivalence (CatFunctor C (CatFunctor D E)) (CatFunctor (C.product D) E) := {
  F := {
    obj := Functor.uncurry,
    hom := λ μ => {
      map := λ X => by {
        simp [Functor.uncurry];
        simp [CatFunctor] at μ;
        sorry;
      },
      natural := sorry,
    },
    map_id := sorry,
    map_comp := sorry
  }
  G := {
    obj := Functor.curry,
    hom := sorry,
    map_id := sorry,
    map_comp := sorry
  },
  μ := sorry,
  ν := sorry,
}

end CategoryTheory
