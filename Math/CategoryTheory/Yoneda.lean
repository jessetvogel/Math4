import Math.CategoryTheory.NaturalTransformation

namespace CategoryTheory

def Yoneda (C : Category) : Functor C (CatFunctor C.op CatType) := {
  obj := λ X => {
    obj := λ Y => C.hom Y X,
    hom := λ f g => g ∘ f,
    map_id := λ _ => by unfold Category.op, CatType; simp,
    map_comp := λ _ _ => by unfold Category.op, CatType; simp,
  },
  hom := λ f => {
    map := λ _ g => f ∘ g,
    natural := λ _ => by unfold CatType; simp,
  },
  map_id := λ _ => by dsimp; congr; simp; rfl,
  map_comp := λ _ _ => by dsimp; congr; simp; rfl,
}

def CoYoneda (C : Category) : Functor C.op (CatFunctor C CatType) := {
  obj := λ X => {
    obj := λ Y => C.hom X Y,
    hom := λ f g => f ∘ g,
    map_id := λ _ => by unfold CatType; simp,
    map_comp := λ _ _ => by unfold CatType; simp,
  },
  hom := λ f => {
    map := λ _ g => g ∘ f,
    natural := λ _ => by unfold CatType; simp,
  },
  map_id := λ _ => by unfold Category.op; dsimp; congr; simp; rfl,
  map_comp := λ g f => by unfold Category.op, CatFunctor, CatType, NaturalTransformation.comp; simp,
}

instance Yoneda.full (C : Category) : (Yoneda C).full := ⟨
  λ {X Y} μ => by {
    -- use f = μ.map X (C.id X)
    apply Exists.intro (μ.map X (C.id X));
    unfold Yoneda; simp;
    congr;
    funext (Z : C.obj) g;
    -- use naturality of μ on g
    have q := congrFun (μ.natural g) (C.id X);
    unfold CatType, Yoneda at q;
    simp at q;
    exact Eq.symm q;
  }
⟩

instance Yoneda.faithful (C : Category) : (Yoneda C).faithful := ⟨
  λ {X Y f g} h => by {
    have h' : ((Yoneda C).hom f).map X (C.id X) = ((Yoneda C).hom g).map X (C.id X) := by rw [h];
    unfold Yoneda at h';
    simp at h';
    exact h';
  }
⟩

-- Note: it doesn't even need Yoneda's lemma
def Yoneda.ext {C : Category} {X Y : C.obj}
  (p : ∀ {Z}, C.hom Z X → C.hom Z Y)
  (q : ∀ {Z}, C.hom Z Y → C.hom Z X)
  (h₁ : ∀ {Z} (f : C.hom Z X), q (p f) = f)
  (h₂ : ∀ {Z} (f : C.hom Z Y), p (q f) = f)
  (n : ∀ {Z Z'} (f : C.hom Z' Z) (g : C.hom Z X), p (g ∘ f) = (p g) ∘ f)
  : X ≅ Y := {
  f := p (C.id X),
  g := q (C.id Y),
  comp_gf := by rw [← h₁ (q (C.id Y) ∘ p (C.id X)), n, h₂, C.id_comp, h₁],
  comp_fg := by rw [← n, C.id_comp, h₂],
}

end CategoryTheory
