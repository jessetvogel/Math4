import Math.CategoryTheory.NatTrans
import Math.CategoryTheory.Opposite

namespace CategoryTheory

open Category

variable (α : Sort u) [C : Category α]

def Yoneda : Functor α (Functor αᵒᵖ (Sort v)) := {
  obj := λ X => {
    obj := λ Y => C.hom Y X,
    map := λ f g => g ∘ f,
    map_id := λ Y => by {
      have q : 𝟙 Y = C.id Y := by rfl;
      simp[q]; rfl;
    },
    map_comp := λ g f => by {
      funext h;
      exact Eq.symm (C.comp_assoc _ _ _);
    }
  },
  map := λ f => {
    app := λ _ g => f ∘ g,
    natural := λ g => by {
      funext h;
      exact Eq.symm (C.comp_assoc _ _ _);
    },
  },
  map_id := λ _ => by dsimp; congr; simp; rfl,
  map_comp := λ _ _ => by dsimp; congr; simp; rfl,
}

def CoYoneda : Functor αᵒᵖ (Functor α (Sort v)) := {
  obj := λ X => {
    obj := λ Y => C.hom X Y,
    map := λ f g => C.comp f g,
    map_id := λ Y => by {
      have q : 𝟙 Y = C.id Y := by rfl;
      simp[q]; rfl;
    },
    map_comp := λ _ _ => by {
      funext h;
      apply C.comp_assoc;
    }
  },
  map := λ f => {
    app := λ Z g => C.comp g f,
    natural := λ _ => by {
      funext h;
      apply C.comp_assoc;
    }
  },
  map_id := λ Y => by {
    have q : 𝟙 Y = C.id Y := by rfl;
    simp [q]; rfl;
  },
  map_comp := λ g f => by {
    dsimp;
    congr;
    funext _ _;
    exact Eq.symm (C.comp_assoc _ _ _);
  }
}

instance Yoneda.full : (Yoneda α).full := ⟨
  λ {X Y} μ => by {
    -- use f = μ.map X (C.id X)
    apply Exists.intro (μ.app X (C.id X));
    unfold Yoneda; simp;
    congr;
    funext (Z : α) g;
    -- use naturality of μ on g
    have q : C.comp (μ.app X (C.id X)) g = μ.app Z (C.comp (C.id X) g) := Eq.symm $ congrFun (μ.natural g) (C.id X);
    simp at q;
    exact q;
  }
⟩

instance Yoneda.faithful : (Yoneda α).faithful := ⟨
  λ {X Y f g} h => by {
    have h' : ((Yoneda α).map f).app X (C.id X) = ((Yoneda α).map g).app X (C.id X) := by rw [h];
    unfold Yoneda at h';
    simp at h';
    exact h';
  }
⟩

-- Note: it doesn't even need Yoneda's lemma (TODO)
-- def Yoneda.ext {C : Category} {X Y : C.obj}
--   (p : ∀ {Z}, C.hom Z X → C.hom Z Y)
--   (q : ∀ {Z}, C.hom Z Y → C.hom Z X)
--   (h₁ : ∀ {Z} (f : C.hom Z X), q (p f) = f)
--   (h₂ : ∀ {Z} (f : C.hom Z Y), p (q f) = f)
--   (n : ∀ {Z Z'} (f : C.hom Z' Z) (g : C.hom Z X), p (g ∘ f) = (p g) ∘ f)
--   : X ≅ Y := {
--   f := p (C.id X),
--   g := q (C.id Y),
--   comp_gf := by rw [← h₁ (q (C.id Y) ∘ p (C.id X)), n, h₂, C.id_comp, h₁],
--   comp_fg := by rw [← n, C.id_comp, h₂],
-- }

end CategoryTheory
